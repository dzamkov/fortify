use fortify::*;

fn main() {
    let fortified = Fortify::new(456);
    let x = Box::new(123);
    let fortified = fortified.map(|_| Lowered::new(&*x));
    drop(x);
    assert_eq!(**fortified.borrow(), 123);
}