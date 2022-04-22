use fortify::*;

fn main() {
    let x = Box::new(123);
    let obj = 456;
    let fortified = Fortify::new_dep(obj, |_| Lowered::new(&*x));
    drop(x);
    assert_eq!(**fortified.borrow(), 123);
}