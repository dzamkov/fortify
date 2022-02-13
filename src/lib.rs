#![warn(missing_docs)]
//! This crate provides the [`Fortify`] wrapper type. When used with a borrowing type (i.e. a type
//! with a lifetime parameter) it allows values of that type to reference arbitrary data owned by
//! the `Fortify` itself.
//!
//! # Example
//! ```
//! use fortify::*;
//!
//! // Define a borrowing type.
//! #[derive(WithLifetime)]
//! struct Example<'a> {
//!    a: &'a i32,
//!    b: &'a mut i32,
//! }
//!
//! // Construct a fortified value that makes an "external" reference to `a` and an "internal"
//! // reference to `b`, which is owned by the Fortify.
//! let a = 1;
//! let mut example: Fortify<Example> = fortify! {
//!     let mut b = 1;
//!     b += 1;
//!     yield Example {
//!         a: &a,
//!         b: &mut b
//!     };
//! };
//!
//! // Use `with_mut` for general mutable access to the wrapped value. Note that the reference
//! // to `b` is still valid even though `b` is not in scope in this block.
//! example.with_mut(|example| {
//!     assert_eq!(*example.a, 1);
//!     assert_eq!(*example.b, 2);
//!     *example.b += 1;
//!     assert_eq!(*example.b, 3);
//! });
//! ```
extern crate self as fortify;
pub use fortify_derive::*;
use std::future::Future;
use std::marker::PhantomData;
use std::mem::{transmute, transmute_copy, ManuallyDrop, MaybeUninit};
use std::pin::Pin;
use std::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};

/// Wraps a value of type `T` and allows it to reference arbitrary supplementary data owned by the
/// [`Fortify`]. This can be used to effectively convert a borrowing type into an owning type.
///
/// # Example
/// ```
/// use fortify::*;
/// let example: Fortify<&'static str> = fortify! {
///     let mut str = String::new();
///     str.push_str("Foo");
///     str.push_str("Bar");
///     yield str.as_str();
/// };
/// example.with_ref(|s| assert_eq!(s, &"FooBar"));
/// assert_eq!(example.borrow(), &"FooBar");
/// ```
pub struct Fortify<T> {
    value: ManuallyDrop<T>,
    data_raw: *mut (),
    data_drop_fn: unsafe fn(*mut ()),
}

impl<'a, T: WithLifetime<'a, Target = T>> Fortify<T> {
    /// Directly constructs a [`Fortify`] wrapper over the given value.
    pub fn new(value: T) -> Self {
        Self {
            value: ManuallyDrop::new(value),
            data_raw: 0 as *mut (),
            data_drop_fn: drop_nop,
        }
    }

    /// Creates a [`Fortify`] by explicitly providing its owned data and constructing its value
    /// from that using a closure. Note that for technical reasons, the constructed value must be
    /// wrapped in a [`FortifySource`] wrapper.
    ///
    /// # Example
    /// ```
    /// use fortify::{Fortify, FortifySource};
    /// let mut str = String::new();
    /// str.push_str("Hello");
    /// let fortified: Fortify<&str> = Fortify::new_dep(str, |s| FortifySource::new(s.as_str()));
    /// assert_eq!(fortified.borrow(), &"Hello");
    /// ```
    pub fn new_dep<O: 'a, C>(owned: O, cons: C) -> Self
    where
        C: 'a + for<'b> FnOnce(&'b mut O) -> FortifySource<'b, 'a, T>,
    {
        Self::new_box_dep(Box::new(owned), cons)
    }

    /// Creates a [`Fortify`] by explicitly providing its owned data (as a [`Box`]) and
    /// constructing its value from that using a closure. Note that for technical reasons, the
    /// constructed value must be wrapped in a [`FortifySource`] wrapper.
    pub fn new_box_dep<O: 'a, C>(owned: Box<O>, cons: C) -> Self
    where
        C: 'a + for<'b> FnOnce(&'b mut O) -> FortifySource<'b, 'a, T>,
    {
        let owned = Box::into_raw(owned);
        let value = cons(unsafe { &mut *owned });
        Self {
            value: ManuallyDrop::new(value.into_inner()),
            data_raw: owned as *mut (),
            data_drop_fn: drop_box_from_raw::<O>,
        }
    }

    /// Creates a [`Fortify`] by using a [`Future`] to construct the `Fortify`'s value. As soon
    /// as the `Future` "yields" a value, it will be suspended and become the supplementary data
    /// for the `Fortify`. This allows the inner value to reference locals defined by the `Future`.
    ///
    /// The `Future` must await on [`FortifyYielder::yield_`] and nothing else. Code following the
    /// await may or may not be executed.
    ///
    /// This is a hacky way of taking advantage of rust's code generation for async in order to
    /// suspend an executing block of code. In the future, when 'generators' is stabilized, this
    /// would be unnecessary. Therefore, it is recommended to use the [`fortify!`] macro instead.
    ///
    /// # Example
    /// ```
    /// use fortify::Fortify;
    /// let external = 1;
    /// let mut fortified: Fortify<(&i32, &i32)> = Fortify::new_async(|y| async {
    ///     let internal = 2;
    ///     y.yield_((&external, &internal)).await;
    /// });
    /// let (external_ref, internal_ref) = *fortified.borrow();
    /// assert_eq!(*external_ref, 1);
    /// assert_eq!(*internal_ref, 2);
    /// ```
    pub fn new_async<C, F>(cons: C) -> Self
    where
        C: 'a + FnOnce(FortifyYielder<'a, T>) -> F,
        F: 'a + Future<Output = ()>,
    {
        let mut context = FortifyYielderContext {
            value: MaybeUninit::uninit(),
            yielder_future_ptr: std::ptr::null_mut(),
        };
        let future = Box::into_raw(Box::new(cons(FortifyYielder {
            context_ptr: &mut context,
            marker: PhantomData,
        })));
        let waker = nop_waker();
        let mut cx = Context::from_waker(&waker);
        match Future::poll(unsafe { Pin::new_unchecked(&mut *future) }, &mut cx) {
            Poll::Ready(_) => {
                unsafe { drop_box_from_raw::<F>(future as *mut ()) };
                panic!("Future must await on FortifyYielder::yield_")
            }
            Poll::Pending => {
                if !context.yielder_future_ptr.is_null() {
                    unsafe {
                        // Set `yielder_future_ptr` to null to prevent `context` from being
                        // accessed after this call returns.
                        (*context.yielder_future_ptr).0 = std::ptr::null_mut();
                    }
                    Fortify {
                        value: ManuallyDrop::new(unsafe { context.value.assume_init() }),
                        data_raw: future as *mut (),
                        data_drop_fn: drop_box_from_raw::<F>,
                    }
                } else {
                    unsafe { drop_box_from_raw::<F>(future as *mut ()) };
                    panic!("Future may only await on FortifyYielder::yield_")
                }
            }
        }
    }

    /// Immutably borrows the value inside a [`Fortify`]. In practice, this can only be called when
    /// `T` is covariant in its lifetime parameter, since the lifetime must be shortened to match
    /// that of the `Fortify`. This is also the reason why there isn't a mutable version of this
    /// function.
    ///
    /// For more general access to the wrapped value, see [`Fortify::with_ref`] and
    /// [`Fortify::with_mut`].
    pub fn borrow(&'a self) -> &'a T {
        &self.value
    }
}

// NOTE: this implementation doesn't verify the "identical runtime representation" condition for
// `WithLifetime`, but that's okay because the condition is verified at the time the `Fortify` is
// created. In order to keep things safe, all methods in this block must always use a pre-existing
// `Fortify`.
impl<T: for<'a> WithLifetime<'a>> Fortify<T> {
    /// Executes a closure using an immutable reference to the value stored inside this [`Fortify`].
    pub fn with_ref<'a, F, R>(&'a self, f: F) -> R
    where
        F: for<'b> FnOnce(&'a <T as WithLifetime<'b>>::Target) -> R,
    {
        let value = &*self.value;
        f(unsafe { transmute(value) })
    }

    /// Executes a closure using a mutable reference to the value stored inside this [`Fortify`].
    pub fn with_mut<'a, F, R>(&'a mut self, f: F) -> R
    where
        F: for<'b> FnOnce(&'a mut <T as WithLifetime<'b>>::Target) -> R,
    {
        let value = &mut *self.value;
        f(unsafe { transmute(value) })
    }
}

impl<'a, T> Fortify<&'a T> {
    /// Creates a [`Fortify`] by taking ownership of a [`Box`] and wrapping a reference to
    /// the value inside it.
    ///
    /// # Example
    /// ```
    /// use fortify::Fortify;
    /// let value = Box::new(123);
    /// let mut fortified: Fortify<&i32> = Fortify::new_box_ref(value);
    /// assert_eq!(**fortified.borrow(), 123);
    /// ```
    pub fn new_box_ref(value: Box<T>) -> Self {
        Fortify::new_box_dep(value, |inner| FortifySource::new(&*inner))
    }
}

impl<'a, T> Fortify<&'a mut T> {
    /// Creates a [`Fortify`] by taking ownership of a [`Box`] and wrapping a mutable reference to
    /// the value inside it.
    ///
    /// # Example
    /// ```
    /// use fortify::Fortify;
    /// let value = Box::new(123);
    /// let mut fortified: Fortify<&mut i32> = Fortify::new_box_mut(value);
    /// fortified.with_mut(|v| **v *= 2);
    /// assert_eq!(**fortified.borrow(), 246);
    /// ```
    pub fn new_box_mut(value: Box<T>) -> Self {
        Fortify::new_box_dep(value, |inner| FortifySource::new(inner))
    }
}

impl<'a, T: WithLifetime<'a, Target = T>> From<T> for Fortify<T> {
    fn from(value: T) -> Self {
        Fortify::new(value)
    }
}

impl<'a, T> From<Box<T>> for Fortify<&'a T> {
    fn from(value: Box<T>) -> Self {
        Fortify::new_box_ref(value)
    }
}

impl<'a, T> From<Box<T>> for Fortify<&'a mut T> {
    fn from(value: Box<T>) -> Self {
        Fortify::new_box_mut(value)
    }
}

impl<'a, T: Default + WithLifetime<'a, Target = T>> Default for Fortify<T> {
    fn default() -> Self {
        Fortify::new(T::default())
    }
}

impl<T> std::fmt::Debug for Fortify<T>
where
    for<'a> T: WithLifetime<'a>,
    for<'a> <T as WithLifetime<'a>>::Target: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.with_ref(|inner| inner.fmt(f))
    }
}

impl<T> std::fmt::Display for Fortify<T>
where
    for<'a> T: WithLifetime<'a>,
    for<'a> <T as WithLifetime<'a>>::Target: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.with_ref(|inner| inner.fmt(f))
    }
}

impl<T> Drop for Fortify<T> {
    fn drop(&mut self) {
        unsafe {
            // Value must be dropped before data
            ManuallyDrop::drop(&mut self.value);
            (self.data_drop_fn)(self.data_raw);
        }
    }
}

/// Does nothing.
unsafe fn drop_nop(_: *mut ()) {
    // Nothing to do here
}

/// Constructs a box from its raw pointer and then drops it.
unsafe fn drop_box_from_raw<T>(raw: *mut ()) {
    // NOTE: It may seem easier to convert to a box and drop it here, but that may trigger UB if
    // the box contains self-references (which is common with futures). Instead, we'll use the
    // destruction pattern from https://doc.rust-lang.org/std/boxed/struct.Box.html#method.into_raw
    std::ptr::drop_in_place(raw as *mut T);
    let layout = std::alloc::Layout::new::<T>();
    if layout.size() > 0 {
        std::alloc::dealloc(raw as *mut u8, layout);
    }
}

/// A [`Waker`] that does nothing when waked.
fn nop_waker() -> Waker {
    const VTABLE: &RawWakerVTable = &RawWakerVTable::new(clone, nop, nop, nop);
    unsafe fn clone(data: *const ()) -> RawWaker {
        RawWaker::new(data, VTABLE)
    }
    unsafe fn nop(_: *const ()) {}
    unsafe { Waker::from_raw(RawWaker::new(0 as *const (), VTABLE)) }
}

/// Wraps a value of type `T` and allows it to reference arbitrary supplementary data in the `'a`
/// lifetime. This is isomorphic to `<T as WithLifetime<'a>>::Target`, but necessary to work around
/// some [issues](https://stackoverflow.com/questions/60459609/how-do-i-return-an-associated-type-from-a-higher-ranked-trait-bound-trait)
/// with type checking.
pub struct FortifySource<'a, 'b, T> {
    value: T,
    marker: PhantomData<fn(&'a (), &'b ()) -> (&'a (), &'b ())>,
}

impl<'a, 'b, T> FortifySource<'a, 'b, T> {
    /// Constructs a [`FortifySource`] from its wrapped value.
    pub fn new<O>(value: O) -> Self
    where
        T: WithLifetime<'a, Target = O>,
        O: WithLifetime<'b, Target = T>,
    {
        let value = unsafe { transmute_copy(&*ManuallyDrop::new(value)) };
        FortifySource {
            value,
            marker: PhantomData,
        }
    }

    /// Unpacks this [`FortifySource`] wrapper.
    pub fn into_inner(self) -> <T as WithLifetime<'a>>::Target
    where
        T: WithLifetime<'a>,
    {
        unsafe { transmute_copy(&*ManuallyDrop::new(self.value)) }
    }
}

/// A helper interface used by the [`Fortify::new_async`] constructor.
pub struct FortifyYielder<'a, T> {
    context_ptr: *mut FortifyYielderContext<T>,
    marker: PhantomData<&'a ()>,
}

impl<'a, T> FortifyYielder<'a, T> {
    /// Provides the [`Fortify`] value to this [`FortifyYielder`] and returns a [`Future`] that may
    /// be awaited to suspend execution.
    pub fn yield_<'b, O>(self, value: O) -> impl Future<Output = ()> + 'b
    where
        T: WithLifetime<'b, Target = O>,
        O: WithLifetime<'a, Target = T>,
    {
        unsafe {
            let target = &mut *(self.context_ptr as *mut FortifyYielderContext<O>);
            target.value.write(value);
            FortifyYielderFuture(&mut target.yielder_future_ptr)
        }
    }
}

struct FortifyYielderContext<T> {
    value: MaybeUninit<T>,
    yielder_future_ptr: *mut FortifyYielderFuture,
}

struct FortifyYielderFuture(*mut *mut FortifyYielderFuture);

impl Future for FortifyYielderFuture {
    type Output = ();

    fn poll(self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<Self::Output> {
        if !self.0.is_null() {
            unsafe {
                // Inform the context that the yield future has been created and pinned. This is a
                // necessary precondition to using the yielded value.
                let self_mut = Pin::into_inner_unchecked(self);
                *self_mut.0 = &mut *self_mut;
            }
        }
        Poll::Pending
    }
}

impl Drop for FortifyYielderFuture {
    fn drop(&mut self) {
        if !self.0.is_null() {
            unsafe {
                // Inform the context that the yielder future has been dropped. This indicates
                // that it is no longer safe to use the yielded value.
                *self.0 = std::ptr::null_mut();
            }
        }
    }
}

/// Indicates that a type has a "primary" lifetime parameter and that parameter can be
/// replaced with another lifetime (`'a`) to produce the type `WithLifetime<'a>::Target`. This
/// trait can be automatically derived. When doing so, the first lifetime parameter in the
/// parameters list will be treated as the "primary" lifetime parameter.
///
/// ## Safety Note
/// For any value of `'a`, `Target` needs to be a type that has an identical runtime representation
/// to `Self`. Rather than being asserted by the implementor, this condition is checked at the
/// point of usage. This typically involves the constraint `T: WithLifetime<'a, Target = T>`. Due
/// to parametericity of lifetime parameters, if `Target` has an identical runtime representation
/// for some lifetime `'a`, it must have an identical runtime representation for all lifetimes.
pub trait WithLifetime<'a> {
    /// The type resulting from replacing the "primary" lifetime of `Self` with `'a`.
    type Target: WithLifetime<'a, Target = Self::Target>;
}

impl<'a, 'b, T: 'b + ?Sized> WithLifetime<'b> for &'a T {
    type Target = &'b T;
}

impl<'a, 'b, T: 'b + ?Sized> WithLifetime<'b> for &'a mut T {
    type Target = &'b mut T;
}

impl<'a, T: WithLifetime<'a> + ?Sized> WithLifetime<'a> for Box<T> {
    type Target = Box<<T as WithLifetime<'a>>::Target>;
}

impl<'a, T: WithLifetime<'a>, const N: usize> WithLifetime<'a> for [T; N] {
    type Target = [<T as WithLifetime<'a>>::Target; N];
}

impl<'a, T: WithLifetime<'a>> WithLifetime<'a> for Fortify<T> {
    type Target = Fortify<<T as WithLifetime<'a>>::Target>;
}

impl<'a, A: WithLifetime<'a>, B: WithLifetime<'a>> WithLifetime<'a> for (A, B) {
    type Target = (
        <A as WithLifetime<'a>>::Target,
        <B as WithLifetime<'a>>::Target,
    );
}

impl<'a, A: WithLifetime<'a>, B: WithLifetime<'a>, C: WithLifetime<'a>> WithLifetime<'a>
    for (A, B, C)
{
    type Target = (
        <A as WithLifetime<'a>>::Target,
        <B as WithLifetime<'a>>::Target,
        <C as WithLifetime<'a>>::Target,
    );
}

impl<'a, A: WithLifetime<'a>, B: WithLifetime<'a>, C: WithLifetime<'a>, D: WithLifetime<'a>>
    WithLifetime<'a> for (A, B, C, D)
{
    type Target = (
        <A as WithLifetime<'a>>::Target,
        <B as WithLifetime<'a>>::Target,
        <C as WithLifetime<'a>>::Target,
        <D as WithLifetime<'a>>::Target,
    );
}

/// A helper macro for creating a `Fortify` using generator-like syntax. The macro takes a block of
/// statements that ends with a `yield` of some expression. The block will be executed up to the
/// `yield` statement, at which point the value of expression will be bundled with the suspended
/// scope of the block and returned as a `Fortify`ied value. Local variables defined in the block
/// may be accessed through references in the wrapped value.
///
/// # Example
/// ```
/// use fortify::*;
/// let external = 1;
/// let mut fortified: Fortify<(&i32, &i32)> = fortify! {
///     let internal = 2;
///     yield (&external, &internal);
/// };
/// let (external_ref, internal_ref) = *fortified.borrow();
/// assert_eq!(*external_ref, 1);
/// assert_eq!(*internal_ref, 2);
/// ```
#[macro_export]
macro_rules! fortify {
    (@INNER $y:ident , yield $res:expr ;) => {
        $y.yield_($res).await
    };
    (@INNER $y:ident , $st:stmt ; $($t:tt)*) => {
        { $st fortify!(@INNER $y , $($t)*) }
    };
    ($($t:tt)*) => {
        $crate::Fortify::new_async(|y| async {
            fortify!(@INNER y , $($t)*)
        })
    };
}

#[cfg(test)]
mod tests;
