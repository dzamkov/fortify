use fortify::*;

fn main() {
    let x = Box::new(123);
    let obj = &*x;
    let fortified = Fortify::new_dep(obj, |val| Lowered::new(*val));
    drop(x);
    assert_eq!(**fortified.borrow(), 123);
}