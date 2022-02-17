use std::mem::transmute_copy;

/// Indicates that a type [covariantly](https://doc.rust-lang.org/nomicon/subtyping.html)
/// references a set of lifetime parameters, and when these parameters are all replaced with `'a`,
/// the resulting type is `Target`. Consequentially, if the type outlives `'a`, it can be directly
/// coerced to `Target` by applying covariance.
/// 
/// This trait can be trivially implemented for any type by setting `Target` to be `Self`. However,
/// in order to maximize its usefulness, it should operate on as many lifetime parameters as
/// possible.
/// 
/// This trait can be automatically derived. When deriving on a type with no lifetime parameters,
/// the trivial implementation will be used (i.e. `Target = Self`). Otherwise, it will operate
/// on the first lifetime parameter in the generic parameters list. Deriving will fail if the
/// type is not covariant in this parameter.
pub unsafe trait Lower<'a> {
    /// The type resulting from substituting the covariant lifetime parameters in `Self` for `'a`.
    type Target: Lower<'a, Target = Self::Target> + ?Sized + 'a;

    /// Applies convariance in order to shorten the internal lifetime parameters in a reference.
    fn lower_ref<'b>(&'b self) -> &'b Self::Target
    where
        Self: 'a,
        'a: 'b,
    {
        // SAFETY: The implementor of the trait is responsible for ensuring that `Target` is
        // a covariant specialization of `Self`. Assuming this, we can directly coerce `Self` to
        // `Target`.
        unsafe { transmute_copy(&self) }
    }
}

unsafe impl<'a, 'b, T: Lower<'b> + ?Sized> Lower<'b> for &'a T {
    type Target = &'b <T as Lower<'b>>::Target;
}

unsafe impl<'a, 'b, T: 'b + ?Sized> Lower<'b> for &'a mut T {
    type Target = &'b mut T;
    fn lower_ref<'c>(&'c self) -> &'c Self::Target
    where
        'a: 'b,
        'b: 'c,
    {
        self
    }
}

unsafe impl<'a, T: Lower<'a> + ?Sized> Lower<'a> for Box<T> {
    type Target = Box<<T as Lower<'a>>::Target>;
}

unsafe impl<'a, T: Lower<'a>> Lower<'a> for [T]
where
    <T as Lower<'a>>::Target: Sized,
{
    type Target = [<T as Lower<'a>>::Target];
}

unsafe impl<'a, T: Lower<'a>, const N: usize> Lower<'a> for [T; N]
where
    <T as Lower<'a>>::Target: Sized,
{
    type Target = [<T as Lower<'a>>::Target; N];
}

unsafe impl<'a, A: Lower<'a>, B: Lower<'a> + ?Sized> Lower<'a> for (A, B)
where
    <A as Lower<'a>>::Target: Sized,
{
    type Target = (<A as Lower<'a>>::Target, <B as Lower<'a>>::Target);
}

unsafe impl<'a, A: Lower<'a>, B: Lower<'a>, C: Lower<'a> + ?Sized> Lower<'a> for (A, B, C)
where
    <A as Lower<'a>>::Target: Sized,
    <B as Lower<'a>>::Target: Sized,
{
    type Target = (
        <A as Lower<'a>>::Target,
        <B as Lower<'a>>::Target,
        <C as Lower<'a>>::Target,
    );
}

unsafe impl<'a, A: Lower<'a>, B: Lower<'a>, C: Lower<'a>, D: Lower<'a> + ?Sized> Lower<'a>
    for (A, B, C, D)
where
    <A as Lower<'a>>::Target: Sized,
    <B as Lower<'a>>::Target: Sized,
    <C as Lower<'a>>::Target: Sized,
{
    type Target = (
        <A as Lower<'a>>::Target,
        <B as Lower<'a>>::Target,
        <C as Lower<'a>>::Target,
        <D as Lower<'a>>::Target,
    );
}

macro_rules! impl_trivial_lower {
    ($t:ty) => {
        unsafe impl<'a> Lower<'a> for $t {
            type Target = $t;
            fn lower_ref<'b>(&'b self) -> &'b Self::Target
            where
                Self: 'a,
                'a: 'b,
            {
                self
            }
        }
    };
}

impl_trivial_lower!(());
impl_trivial_lower!(bool);
impl_trivial_lower!(char);
impl_trivial_lower!(f32);
impl_trivial_lower!(f64);
impl_trivial_lower!(i8);
impl_trivial_lower!(i16);
impl_trivial_lower!(i32);
impl_trivial_lower!(i64);
impl_trivial_lower!(i128);
impl_trivial_lower!(isize);
impl_trivial_lower!(u8);
impl_trivial_lower!(u16);
impl_trivial_lower!(u32);
impl_trivial_lower!(u64);
impl_trivial_lower!(u128);
impl_trivial_lower!(usize);
impl_trivial_lower!(std::num::NonZeroI8);
impl_trivial_lower!(std::num::NonZeroI16);
impl_trivial_lower!(std::num::NonZeroI32);
impl_trivial_lower!(std::num::NonZeroI64);
impl_trivial_lower!(std::num::NonZeroI128);
impl_trivial_lower!(std::num::NonZeroIsize);
impl_trivial_lower!(std::num::NonZeroU8);
impl_trivial_lower!(std::num::NonZeroU16);
impl_trivial_lower!(std::num::NonZeroU32);
impl_trivial_lower!(std::num::NonZeroU64);
impl_trivial_lower!(std::num::NonZeroU128);
impl_trivial_lower!(std::num::NonZeroUsize);
impl_trivial_lower!(std::sync::atomic::AtomicI8);
impl_trivial_lower!(std::sync::atomic::AtomicI16);
impl_trivial_lower!(std::sync::atomic::AtomicI32);
impl_trivial_lower!(std::sync::atomic::AtomicI64);
impl_trivial_lower!(std::sync::atomic::AtomicIsize);
impl_trivial_lower!(std::sync::atomic::AtomicU8);
impl_trivial_lower!(std::sync::atomic::AtomicU16);
impl_trivial_lower!(std::sync::atomic::AtomicU32);
impl_trivial_lower!(std::sync::atomic::AtomicU64);
impl_trivial_lower!(std::sync::atomic::AtomicUsize);
impl_trivial_lower!(str);
impl_trivial_lower!(String);
impl_trivial_lower!(std::ffi::CStr);
impl_trivial_lower!(std::ffi::CString);
impl_trivial_lower!(std::ffi::OsStr);
impl_trivial_lower!(std::ffi::OsString);