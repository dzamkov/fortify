use crate::*;

#[test]
fn test_complex() {
    let fortified = fortify! {
        let a = Box::new([1, 1, 2, 3, 5, 8]);
        let b = 100;
        let c = fortify! {
            let d = 10000;
            let e = 500;
            yield (&b, &d, [&b, &d, &e]);
        };
        yield (&a, Box::new(&a[1..3]), c);
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
}

#[test]
fn test_debug() {
    #[derive(WithLifetime, Debug)]
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
