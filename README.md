A simple and convenient way to bundle owned data with a borrowing type.

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
lifetime for a reference by bundling it with the data it is referencing. Although it has some
support for wrapping other dependent objects through
[`OwningHandle`](http://kimundi.github.io/owning-ref-rs/owning_ref/struct.OwningHandle.html), it is
inflexible and tricky to use.
* There have been proposals for allowing self-referential structs. In lieu of language support,
the [rental](https://crates.io/crates/rental) crate enables a limited form of this. However, it is
no longer being maintained.

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

All wrapped types must implement the `WithLifetime<'a>` trait, which asserts that a type has a
lifetime parameter *and* allows that parameter to be swapped for something else. This trait can be
automatically derived, in which case it will operate on the first lifetime parameter in the
parameter list.

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

In most cases, you will need to use `with_ref` or `with_mut`. These execute a caller-provided
closure with the properly-typed inner value. There is one case where you don't need to use a 
closure: if the wrapped value is covariant in its lifetime parameter, you can use `borrow` to get
an immutable reference to it (with appropriately-shortened lifetime).

```rust
example.with_ref(|s| assert_eq!(s, &"FooBar"));
// or
assert_eq!(example.borrow(), &"FooBar");
```

**Can I use `Fortify<T>` with a non-`'static` lifetime?**

Of course! The `Fortify` wrapper merely introduces an additional option for references (pointing to
owned data inside the wrapper). It is always possible to forgo this option and construct a
`Fortify<T>` directly from a `T`. You can even have a mixed value which makes some references to
external data and some references to owned data.

```rust
let external = 1;
let mut mixed: Fortify<(&i32, &i32)> = fortify! {
    let internal = 2;
    yield (&external, &internal);
};
let (external_ref, internal_ref) = *mixed.borrow();
assert_eq!(*external_ref, 1);
assert_eq!(*internal_ref, 2);
```

[**Worked Example**](https://github.com/dzamkov/fortify/tree/master/tests/game.md)