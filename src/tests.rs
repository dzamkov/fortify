use crate::*;
use std::cell::Cell;

#[test]
fn test_complex() {
    let counter = &Cell::new(0);
    let fortified = fortify! {
        let a = Box::new([1, 1, 2, 3, 5, 8]);
        let b = 100;
        let c = fortify! {
            let d = 10000;
            let e = 500;
            let f = DropChecker::new(counter);
            yield (&b, &d, [&b, &d, &e], &f);
        };
        let d = DropChecker::new(counter);
        yield (&a, Box::new(&a[1..3]), &c, d);
    };
    fortified.with_ref(|inner| {
        assert_eq!(&**inner.0, &[1, 1, 2, 3, 5, 8]);
        assert_eq!(&*inner.1, &[1, 2]);
        inner.2.with_ref(|inner| {
            assert_eq!(*inner.0, 100);
            assert_eq!(*inner.1, 10000);
            assert_eq!(*inner.2[0], 100);
            assert_eq!(*inner.2[1], 10000);
            assert_eq!(*inner.2[2], 500);
        });
    });
    drop(fortified);
    assert_eq!(counter.get(), 0);
}

#[test]
fn test_zst() {
    let _: Fortify<&'static ()> = Fortify::new_dep((), |r| Lowered::new(&*r));
}

#[test]
fn test_no_lifetime() {
    #[allow(dead_code)]
    #[derive(Lower)]
    struct Test<T>
    where
        T: std::fmt::Display,
    {
        a: T,
        b: bool,
    }
    let fortified = fortify! {
        yield Test { a: 'x', b: true };
    };
    assert_eq!(fortified.borrow().a, 'x');
    assert_eq!(fortified.borrow().b, true);
}

#[test]
fn test_move() {
    // See https://github.com/dzamkov/fortify/issues/1
    #[derive(Lower)]
    pub struct I32<'a> {
        foo: &'a i32,
    }
    fn create(foo: i32) -> Fortify<I32<'static>> {
        fortify! {
            let foo = foo;
            yield I32 { foo: &foo };
        }
    }
    assert_eq!(*create(15).borrow().foo, 15);
}

#[test]
fn test_debug() {
    #[allow(dead_code)]
    #[derive(Lower, Debug)]
    struct Test<'a> {
        a: &'a i32,
        b: &'a str,
    }
    let fortified = fortify! {
        let a = 13;
        let b = "Foo";
        yield Test { a: &a, b: &b };
    };
    assert_eq!(format!("{:?}", fortified), "Test { a: 13, b: \"Foo\" }");
}

/// A helper for testing that a value is dropped.
#[derive(Lower)]
struct DropChecker<'a>(&'a Cell<u32>);

impl<'a> DropChecker<'a> {
    fn new(counter: &'a Cell<u32>) -> Self {
        counter.set(counter.get() + 1);
        Self(counter)
    }
}

impl<'a> Drop for DropChecker<'a> {
    fn drop(&mut self) {
        let old_count = self.0.get();
        assert!(old_count > 0);
        self.0.set(old_count - 1);
    }
}

#[test]
fn test_drop_new() {
    let counter = Cell::new(0);
    drop(Fortify::new(DropChecker::new(&counter)));
    assert_eq!(counter.get(), 0);
}

#[test]
fn test_drop_new_box_ref() {
    let counter = Cell::new(0);
    drop(Fortify::new_box_ref(Box::new(DropChecker::new(&counter))));
    assert_eq!(counter.get(), 0);
}

#[test]
fn test_drop_new_box_mut() {
    let counter = Cell::new(0);
    drop(Fortify::new_box_mut(Box::new(DropChecker::new(&counter))));
    assert_eq!(counter.get(), 0);
}

#[test]
#[should_panic]
#[allow(unused_must_use)]
fn test_new_async_no_await() {
    let _ = Fortify::new_async(|y| async {
        let x = 42;
        y.yield_(Lowered::new(&x));
    });
}

struct NopFuture;
impl Future for NopFuture {
    type Output = ();

    fn poll(self: Pin<&mut Self>, _: &mut Context<'_>) -> Poll<Self::Output> {
        Poll::Pending
    }
}

#[test]
#[should_panic]
#[allow(unused_must_use)]
fn test_new_async_bad_await() {
    let _ = Fortify::new_async(|y| async {
        let x = 42;
        let future = y.yield_(Lowered::new(&x));

        // Try tricking `new_async` into thinking the future was awaited by polling on it
        let waker = nop_waker();
        let mut fake_cx = Context::from_waker(&waker);
        Box::pin(future).as_mut().poll(&mut fake_cx);

        // .. but await a different future instead
        NopFuture.await;
    });
}
