A simple and convenient way to bundle owned data with a borrowing type.

## Example
```rust
use fortify::*;

// Define a borrowing type. The `Lower` trait specifies that it is covariant in its first
// lifetime parameter.
#[derive(Lower)]
struct Example<'a> {
   a: &'a i32,
   b: &'a mut i32,
}

// Construct a fortified value that makes an "external" reference to `a` and an "internal"
// reference to `b`, which is owned by the Fortify.
let a = 1;
let mut example: Fortify<Example> = fortify! {
    let mut b = 1;
    b += 1;
    yield Example {
        a: &a,
        b: &mut b
    };
};

// Use `with_mut` for general mutable access to the wrapped value. Note that the reference
// to `b` is still valid even though `b` is not in scope in this block.
example.with_mut(|example| {
    assert_eq!(*example.a, 1);
    assert_eq!(*example.b, 2);
    *example.b += 1;
    assert_eq!(*example.b, 3);
});
```

## The Problem

One of the main selling points of Rust is its borrow checker, which allows you to define types
that make references to outside data while ensuring that the data will remain valid for as long
the type is using it. In theory, this is the ideal memory management scheme: it costs nothing to
"drop" a reference, we're not putting off any work for a deferred garbage collection and we're
completely protected from use after free errors.

However, many Rust programmers feel uneasy putting this technique into practice, often resorting
to simpler methods such as reference counting. A key reason for this is the infectious nature of
lifetimes: storing a reference in a type requires you to specify a lifetime, and with the rare
exception of `'static` data, this requires you to have a lifetime parameter on the type. Then, to
use the type in another type, you need to specify a lifetime parameter for that type, and so on.
The chain only ends when you finally introduce the value as a local variable, allowing new unique
lifetimes to be created for it.

But this isn't always possible. Sometimes you need a value to be allocated at a higher stack level
than you have access to. It's difficult to identify these situations ahead of time,
and when you do, your whole design collapses. No wonder Rust programmers are hesitant about using
references.

There's a few existing solutions to mitigate this problem, but all of them have their issues:
* Using an arena allocator such as [bumpalo](https://crates.io/crates/bumpalo) or
[typed-arena](https://crates.io/crates/typed-arena), you can allocate data with a particular
lifetime from a lower level in the stack. However, the memory can't be freed until the allocator
is dropped, so there is a practical limit to how long the allocator can be kept alive.
* The [owning_ref](https://crates.io/crates/owning_ref) crate allows you to avoid specifying the
lifetime for a reference by bundling it with the data it is referencing. However, it has
[numerous](https://github.com/Kimundi/owning-ref-rs/issues/49)
[soundness](https://github.com/Kimundi/owning-ref-rs/issues/61)
[issues](https://github.com/Kimundi/owning-ref-rs/issues/77) and is no longer being maintained.
* There have been proposals for allowing self-referential structs. In lieu of language support,
the [rental](https://crates.io/crates/rental) and [ouroboros](https://crates.io/crates/ouroboros)
crates enable a limited form of this. However, the implementation of self-referential structs is
not as simple or intuitive as one would expect. There are limitations to what may be stored in
the struct and access to struct fields must be restricted in order to adhere to Rust's aliasing
rules.

This crate introduces yet another solution to problem, with the goal of being flexible and
convenient enough to enable fearless use of references and borrowing types.

## The Solution

The `Fortify<T>` wrapper allows a wrapped value to make references to hidden, supplementary
data owned by the wrapper itself. For example, a `Fortify<&'static str>` can be a regular
`&'static str`, or it can be a reference to a string stored inside the `Fortify`. `T` isn't limited
to being a reference, it can be any type that has a lifetime parameter, with similar
effect. The implication here is that you can turn any borrowing type (i.e. a type with a lifetime
parameter) into an owning type by setting its lifetime to `'static` and putting it in a `Fortify`
wrapper.

**How is this okay? Doesn't a `&'static str` always have to reference something in the `'static`
lifetime?**

The key insight is that you can never get a `&'static str` from a `Fortify<&'static str>`. Instead,
you can get a `&'a str` where `'a` is tied to lifetime of the `Fortify`. The wrapper has a complex
relationship with its wrapped type that can't normally be expressed in Rust (hence the need for
this crate). It's implementation requires being able to manipulate the lifetime parameter of
the enclosed type.

**So if I use a type with multiple lifetime parameters, how does the wrapper know which lifetime
it "works" on?**

All wrapped types must implement the `Lower<'a>` trait, which specifies how to substitute the
covariant lifetime parameters in the type. This trait can be automatically derived, in which
case it will only operate on the first lifetime parameter in the parameter list.

**How do I create a `Fortify<T>`?**

There are many ways to create an instance of the wrapper, with the simplest being a direct
conversion from `T`. However, the preferred and most general method is the `fortify!` macro:

```rust
let example: Fortify<&'static str> = fortify! {
     let mut str = String::new();
     str.push_str("Foo");
     str.push_str("Bar");
     yield str.as_str();
};
```

This captures all of the local variables in a block of code and stores them inside the `Fortify`
wrapper. The final `yield` statement provides the wrapped value that is exposed to the outside.
Note that it may make references to the local variables.

**How do I use it?**

You can use `borrow` to get an immutable reference to the wrapped value with appropriately
shortened lifetime. Mutable access is a bit more complicated, and requires the
use of `with_mut`.

```rust
assert_eq!(example.borrow(), &"FooBar");
// or
example.with_mut(|s| assert_eq!(s, &"FooBar"));
```

**Can I use `Fortify<T>` with a non-`'static` lifetime?**

Of course! The `Fortify` wrapper merely introduces an additional option for references (pointing to
owned data inside the wrapper). It is always possible to forgo this option and construct a
`Fortify<T>` directly from a `T`. You can even have a mixed value which makes some references to
external data and some references to owned data, as in the first example.