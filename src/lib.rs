#![warn(missing_docs)]
//! This crate provides the [`Fortify`] wrapper type. When used with a borrowing type (i.e. a type
//! with a lifetime parameter) it allows values of that type to reference arbitrary data owned by
//! the `Fortify` itself.
//!
//! # Example
//! ```
//! use fortify::*;
//!
//! // Define a borrowing type. The `Lower` trait specifies that it is covariant in its first
//! // lifetime parameter.
//! #[derive(Lower)]
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
mod lower;

pub use fortify_derive::*;
pub use lower::*;
use std::future::Future;
use std::mem::{transmute_copy, ManuallyDrop, MaybeUninit};
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

impl<T> Fortify<T> {
    /// Directly constructs a [`Fortify`] wrapper over the given value.
    pub fn new(value: T) -> Self {
        Self {
            value: ManuallyDrop::new(value),
            data_raw: std::ptr::null_mut(),
            data_drop_fn: drop_nop,
        }
    }
}

impl<'a, T: Refers<'a>> Fortify<T> {
    /// Creates a [`Fortify`] by explicitly providing its owned data and constructing its value
    /// from that using a closure. Note that for technical reasons, the constructed value must be
    /// wrapped in a [`Lowered`] wrapper.
    ///
    /// # Example
    /// ```
    /// use fortify::{Fortify, Lowered};
    /// let mut str = String::new();
    /// str.push_str("Hello");
    /// let fortified: Fortify<&str> = Fortify::new_dep(str, |s| Lowered::new(s.as_str()));
    /// assert_eq!(fortified.borrow(), &"Hello");
    /// ```
    pub fn new_dep<O: 'a, C>(owned: O, cons: C) -> Self
    where
        C: 'a + for<'b> FnOnce(&'b mut O) -> Lowered<'b, T>,
    {
        Self::new_box_dep(Box::new(owned), cons)
    }

    /// Creates a [`Fortify`] by explicitly providing its owned data (as a [`Box`]) and
    /// constructing its value from that using a closure. Note that for technical reasons, the
    /// constructed value must be wrapped in a [`Lowered`] wrapper.
    pub fn new_box_dep<O: 'a, C>(owned: Box<O>, cons: C) -> Self
    where
        C: 'a + for<'b> FnOnce(&'b mut O) -> Lowered<'b, T>,
    {
        let owned = Box::into_raw(owned);
        let value = cons(unsafe { &mut *owned });
        Self {
            value: ManuallyDrop::new(value.value),
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
    /// use fortify::{Fortify, Lowered};
    /// let external = 1;
    /// let mut fortified: Fortify<(&i32, &i32)> = Fortify::new_async(|y| async {
    ///     let internal = 2;
    ///     y.yield_(Lowered::new((&external, &internal))).await;
    /// });
    /// let (external_ref, internal_ref) = *fortified.borrow();
    /// assert_eq!(*external_ref, 1);
    /// assert_eq!(*internal_ref, 2);
    /// ```
    pub fn new_async<C, F>(cons: C) -> Self
    where
        C: 'a + FnOnce(FortifyYielder<T>) -> F,
        F: 'a + Future<Output = ()>,
    {
        let waker = nop_waker();
        let mut cx = Context::from_waker(&waker);
        let mut data = FortifyYielderData {
            value: MaybeUninit::uninit(),
            tracker: FortifyYielderTracker {
                cx_ptr: &cx as *const Context as *const (),
                has_awaited: false,
            },
        };
        let future = Box::into_raw(Box::new(cons(FortifyYielder(&mut data))));
        match Future::poll(unsafe { Pin::new_unchecked(&mut *future) }, &mut cx) {
            Poll::Ready(_) => {
                unsafe { drop_box_from_raw::<F>(future as *mut ()) };
                panic!("Future must await on FortifyYielder::yield_")
            }
            Poll::Pending => {
                if data.tracker.has_awaited {
                    Self {
                        value: ManuallyDrop::new(unsafe {
                            transmute_copy(data.value.assume_init_ref())
                        }),
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
}

impl<'a, T: Lower<'a, Target = T>> Fortify<&'a T>
{
    /// Creates a [`Fortify`] by taking ownership of a [`Box`] and wrapping a reference to
    /// the value inside it.
    ///
    /// # Example
    /// ```
    /// use fortify::Fortify;
    /// let value = Box::new(123);
    /// let mut fortified: Fortify<&i32> = Fortify::new_box_ref(value);
    /// assert_eq!(**fortified.borrow(), 123);
    /// assert_eq!(fortified.with_inner(|x| *x), 123);
    /// ```
    pub fn new_box_ref(value: Box<T>) -> Self {
        Self::new_box_dep(value, |inner| Lowered::new(&*inner))
    }
}

impl<'a, T: 'a> Fortify<&'a mut T> {
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
        Self::new_box_dep(value, |inner| Lowered::new(inner))
    }
}

impl<'a, T: Lower<'a>> Fortify<T> {
    /// Immutably borrows the value inside a [`Fortify`]. For more general access to the wrapped
    /// value, see [`Fortify::with_ref`] and [`Fortify::with_mut`].
    #[allow(clippy::should_implement_trait)]
    // We would like to implement `std::borrow::Borrow`, but it's not possible to specify the
    // lifetime correctly.
    pub fn borrow(&'a self) -> &'a <T as Lower<'a>>::Target {
        let value = &*self.value;
        unsafe { transmute_copy(&value) }
    }
}

impl<T: for<'a> Lower<'a>> Fortify<T> {
    /// Executes a closure using an immutable reference to the value stored inside this [`Fortify`].
    ///
    /// Calls to `with_ref` can typically be replaced with and simplified using `borrow`. This
    /// method is retained for consistency with `with_mut` and possible support for non-covariant
    /// types (which can't use `borrow`) in the future.
    pub fn with_ref<'a, F, R>(&'a self, f: F) -> R
    where
        F: for<'b> FnOnce(&'a <T as Lower<'b>>::Target) -> R,
    {
        let value = &*self.value;
        f(unsafe { transmute_copy(&value) })
    }

    /// Executes a closure using a mutable reference to the value stored inside this [`Fortify`].
    pub fn with_mut<'a, F, R>(&'a mut self, f: F) -> R
    where
        F: for<'b> FnOnce(&'a mut <T as Lower<'b>>::Target) -> R,
    {
        let value = &mut *self.value;
        f(unsafe { transmute_copy(&value) })
    }

    /// Executes a closure with the value stored inside this [`Fortify`], effectively destructing
    /// the wrapper.
    pub fn with_inner<F, R>(self, f: F) -> R
    where
        for<'a> <T as Lower<'a>>::Target: Sized,
        F: for<'a> FnOnce(<T as Lower<'a>>::Target) -> R,
    {
        self.split(|inner| (Lowered::new(()), f(Lowered::unwrap(inner))))
            .1
    }
}

impl<'a, T: 'a> Fortify<T> {
    /// Maps and splits this [`Fortify`] wrapper into a component that references its owned
    /// data, and a component that doesn't. This is a generalization of both [`Fortify::map`] and
    /// [`Fortify::with_inner`].
    ///
    /// # Example
    /// ```
    /// use fortify::*;
    /// let fortified: Fortify<(&i32, i32)> = fortify! {
    ///     let x = 12;
    ///     yield (&x, 15);
    /// };
    /// let (x, y) = fortified.split(|inner| (Lowered::new(inner.0), inner.1));
    /// assert_eq!(**x.borrow(), 12);
    /// assert_eq!(y, 15);
    /// ```
    pub fn split<F, N, R>(mut self, f: F) -> (Fortify<N>, R)
    where
        N: Refers<'a>,
        F: 'a + for<'b> FnOnce(Lowered<'b, T>) -> (Lowered<'b, N>, R),
    {
        let value = unsafe { ManuallyDrop::take(&mut self.value) };
        let data_raw = self.data_raw;
        let data_drop_fn = self.data_drop_fn;
        std::mem::forget(self);
        let (value, res) = f(Lowered {
            value,
            marker: std::marker::PhantomData,
        });
        (
            Fortify {
                value: ManuallyDrop::new(value.value),
                data_raw,
                data_drop_fn,
            },
            res,
        )
    }

    /// Constructs a new [`Fortify`] wrapper by applying a mapping function to the value stored
    /// in this wrapper. The resulting [`Fortify`] will carry the exact same owned data as this
    /// does.
    pub fn map<F, N>(self, f: F) -> Fortify<N>
    where
        N: Refers<'a>,
        F: 'a + for<'b> FnOnce(Lowered<'b, T>) -> Lowered<'b, N>,
    {
        self.split(|inner| (f(inner), ())).0
    }
}

/// Indicates that, if this type has a non-trivial implementation of [`Lower`], it references
/// the lifetime `'a`. Thus, the bound `T: Refers<'a>` can be thought of as the inverse of `T: 'a`.
/// 
/// This is used by various [`Fortify`]-constructing functions to ensure that the resulting
/// wrapper does not outlive the external references it contains. This will be automatically
/// implemented for any type that correctly implements [`Lower`].
pub trait Refers<'a> { }

impl<'a, T: Lower<'a, Target = T>> Refers<'a> for T { }

impl<T> From<T> for Fortify<T> {
    fn from(value: T) -> Self {
        Fortify::new(value)
    }
}

impl<'a, T: Lower<'a, Target = T>> From<Box<T>> for Fortify<&'a T>
{
    fn from(value: Box<T>) -> Self {
        Fortify::new_box_ref(value)
    }
}

impl<'a, T> From<Box<T>> for Fortify<&'a mut T> {
    fn from(value: Box<T>) -> Self {
        Fortify::new_box_mut(value)
    }
}

impl<T: Default> Default for Fortify<T> {
    fn default() -> Self {
        Fortify::new(T::default())
    }
}

impl<T> std::fmt::Debug for Fortify<T>
where
    for<'a> T: Lower<'a>,
    for<'a> <T as Lower<'a>>::Target: std::fmt::Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.borrow().fmt(f)
    }
}

impl<T> std::fmt::Display for Fortify<T>
where
    for<'a> T: Lower<'a>,
    for<'a> <T as Lower<'a>>::Target: std::fmt::Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.borrow().fmt(f)
    }
}

unsafe impl<'a, T: Lower<'a>> Lower<'a> for Fortify<T>
where
    T::Target: Sized,
{
    type Target = Fortify<T::Target>;
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
    unsafe { Waker::from_raw(RawWaker::new(std::ptr::null(), VTABLE)) }
}

/// A helper interface used by the [`Fortify::new_async`] constructor.
pub struct FortifyYielder<T>(*mut FortifyYielderData<T>);

impl<T> FortifyYielder<T> {
    /// Provides the [`Fortify`] value to this [`FortifyYielder`] and returns a [`Future`] that may
    /// be awaited to suspend execution.
    pub fn yield_(self, value: Lowered<T>) -> impl Future<Output = ()> + '_ {
        unsafe {
            let target = &mut *self.0;
            target.value.write(value.value);
            FortifyYielderFuture(&mut target.tracker)
        }
    }
}

struct FortifyYielderData<T> {
    value: MaybeUninit<T>,
    tracker: FortifyYielderTracker,
}

struct FortifyYielderTracker {
    cx_ptr: *const (),
    has_awaited: bool,
}

struct FortifyYielderFuture(*mut FortifyYielderTracker);

impl Future for FortifyYielderFuture {
    type Output = ();

    fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        unsafe {
            // Verify the context to ensure that this future is being polled by `new_async` rather
            // than by the user.
            let tracker = &mut *self.as_ref().0;
            if tracker.cx_ptr == (cx as *const Context as *const ()) {
                // Inform `new_async` that the future has been awaited. This enables the value
                // written to `FortifyYielderData` to be used.
                tracker.has_awaited = true;
            }
        }
        Poll::Pending
    }
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
        $y.yield_(Lowered::new($res)).await
    };
    (@INNER $y:ident , $st:stmt ; $($t:tt)*) => {
        { $st fortify!(@INNER $y , $($t)*) }
    };
    ($($t:tt)*) => {
        $crate::Fortify::new_async(move |y| async move {
            fortify!(@INNER y , $($t)*)
        })
    };
}

#[cfg(test)]
mod tests;
