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
use std::intrinsics::transmute;
use std::marker::PhantomData;
use std::mem::ManuallyDrop;
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
            data_raw: 0 as *mut (),
            data_drop_fn: drop_nop,
        }
    }

    /// Creates a [`Fortify`] by explicitly providing its owned data and constructing its value
    /// from that using a closure. The closure must call [`FortifyBuilder::provide`] to provide the
    /// value of the `Fortify`.
    ///
    /// # Example
    /// ```
    /// use fortify::Fortify;
    /// let mut str = String::new();
    /// str.push_str("Hello");
    /// let fortified: Fortify<&str> = Fortify::new_dep(str, |b, s| b.provide(s.as_str()));
    /// assert_eq!(fortified.borrow(), &"Hello");
    /// ```
    pub fn new_dep<'a, O: 'a, C>(owned: O, cons: C) -> Self
    where
        T: for<'b> WithLifetime<'b>,
        C: 'a + for<'b> FnOnce(FortifyBuilder<'a, T>, &'b mut O),
    {
        Self::new_box_dep(Box::new(owned), cons)
    }

    /// Creates a [`Fortify`] by explicitly providing its owned data (as a [`Box`]) and
    /// constructing its value from that using a closure. The closure must call
    /// [`FortifyBuilder::provide`] to provide the value of the `Fortify`.
    pub fn new_box_dep<'a, O: 'a, C>(mut owned: Box<O>, cons: C) -> Self
    where
        T: for<'b> WithLifetime<'b>,
        C: 'a + for<'b> FnOnce(FortifyBuilder<'a, T>, &'b mut O),
    {
        let mut value = None;
        cons(
            FortifyBuilder {
                ptr: &mut value,
                marker: PhantomData,
            },
            &mut *owned,
        );
        match value {
            Some(value) => Self {
                value: ManuallyDrop::new(value),
                data_raw: Box::into_raw(owned) as *mut (),
                data_drop_fn: drop_box_from_raw::<O>,
            },
            None => panic!("FortifyBuilder::provide must be called to provide a value"),
        }
    }

    /// Creates a [`Fortify`] by using a [`Future`] to construct the `Fortify`'s value. As soon
    /// as the `Future` "yields" a value, it will be suspended and become the supplementary data
    /// for the `Fortify`. This allows the inner value to reference locals defined by the `Future`.
    ///
    /// The `Future` must await on [`FortifyBuilder::yield_`] and nothing else. Code following the
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
    /// let mut fortified: Fortify<(&i32, &i32)> = Fortify::new_async(|b| async {
    ///     let internal = 2;
    ///     b.yield_((&external, &internal)).await;
    /// });
    /// let (external_ref, internal_ref) = *fortified.borrow();
    /// assert_eq!(*external_ref, 1);
    /// assert_eq!(*internal_ref, 2);
    /// ```
    pub fn new_async<'a, C, F>(cons: C) -> Self
    where
        T: WithLifetime<'a, Target = T>,
        C: 'a + FnOnce(FortifyBuilder<'a, T>) -> F,
        F: 'a + Future<Output = ()>,
    {
        let mut value = None;
        let mut future = Box::pin(cons(FortifyBuilder {
            ptr: &mut value,
            marker: PhantomData,
        }));
        let waker = nop_waker();
        let mut cx = Context::from_waker(&waker);
        match Future::poll(future.as_mut(), &mut cx) {
            Poll::Ready(_) => panic!("Future must await on FortifyBuilder::yield_"),
            Poll::Pending => match value {
                Some(value) => unsafe {
                    let data = Pin::into_inner_unchecked(future);
                    return Fortify {
                        value: ManuallyDrop::new(value),
                        data_raw: Box::into_raw(data) as *mut (),
                        data_drop_fn: drop_box_from_raw::<F>,
                    };
                },
                None => panic!("Future may only await on FortifyBuilder::yield_"),
            },
        }
    }

    /// Immutably borrows the value inside a [`Fortify`]. In practice, this can only be called when
    /// `T` is covariant in its lifetime parameter, since the lifetime must be shortened to match
    /// that of the `Fortify`. This is also the reason why there isn't a mutable version of this
    /// function.
    ///
    /// For more general access to the wrapped value, see [`Fortify::with_ref`] and
    /// [`Fortify::with_mut`].
    pub fn borrow<'a>(&'a self) -> &'a T
    where
        T: WithLifetime<'a, Target = T>,
    {
        &self.value
    }

    /// Executes a closure using an immutable reference to the value stored inside this [`Fortify`].
    pub fn with_ref<'a, F, R>(&'a self, f: F) -> R
    where
        T: for<'b> WithLifetime<'b>,
        F: for<'b> FnOnce(&'a <T as WithLifetime<'b>>::Target) -> R,
    {
        let value = &*self.value;
        f(unsafe { transmute(value) })
    }

    /// Executes a closure using a mutable reference to the value stored inside this [`Fortify`].
    pub fn with_mut<'a, F, R>(&'a mut self, f: F) -> R
    where
        T: for<'b> WithLifetime<'b>,
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
        let data_raw = Box::into_raw(value);
        Self {
            value: ManuallyDrop::new(unsafe { &*data_raw }),
            data_raw: data_raw as *mut (),
            data_drop_fn: drop_nop,
        }
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
        let data_raw = Box::into_raw(value);
        Self {
            value: ManuallyDrop::new(unsafe { &mut *data_raw }),
            data_raw: data_raw as *mut (),
            data_drop_fn: drop_nop,
        }
    }
}

impl<T> From<T> for Fortify<T> {
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

impl<T: Default> Default for Fortify<T> {
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
    drop(Box::from_raw(raw as *mut T))
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

/// A helper interface used by [`Fortify`] constructors.
pub struct FortifyBuilder<'a, T> {
    ptr: *mut Option<T>,
    marker: PhantomData<&'a ()>,
}

impl<'a, T> FortifyBuilder<'a, T> {
    /// Provides the [`Fortify`] value to this [`FortifyBuilder`].
    pub fn provide<'b, O>(self, value: O)
    where
        T: WithLifetime<'b, Target = O>,
        O: WithLifetime<'a, Target = T>,
    {
        unsafe { *(self.ptr as *mut Option<O>) = Some(value) };
    }

    /// Provides the [`Fortify`] value to this [`FortifyBuilder`] and returns a [`Future`] that may
    /// be awaited to suspend execution.
    pub fn yield_<'b, O>(self, value: O) -> impl Future<Output = ()>
    where
        T: WithLifetime<'b, Target = O>,
        O: WithLifetime<'a, Target = T>,
    {
        unsafe { *(self.ptr as *mut Option<O>) = Some(value) };
        FortifyBuilderFuture
    }
}

struct FortifyBuilderFuture;

impl Future for FortifyBuilderFuture {
    type Output = ();

    fn poll(self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<Self::Output> {
        Poll::Pending
    }
}

/// Indicates that a type has a "primary" lifetime parameter and that parameter can be
/// replaced with another lifetime (`'a`) to produce the type [`WithLifetime<'a>::Target`]. This
/// trait can be automatically derived. When doing so, the first lifetime parameter in the
/// parameters list will be treated as the "primary" lifetime parameter.
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
