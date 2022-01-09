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

## Worked Example

Say we want to make a simple 2D game. The (imaginary) framework we're using provides the
following API:

```rust
/// An interactive application drawn on a two-dimensional surface.
pub trait Application {
    /// Draws the UI for the application.
    fn draw(&self);

    /// Updates the state of the application in response to the passage of time.
    fn update(&mut self, step: f32);
}

/// Runs an [`Application`].
pub fn run_app(mut app: impl Application + 'static);

/// An interface to a graphics device used for drawing and managing textures.
pub struct Device { ... };

impl Device {
    /// Creates a new [`Device`].
    pub fn new() -> Self;

    /// Loads a texture by name.
    pub fn load_texture(&self, name: &'static str) -> u32;

    /// Unloads a texture.
    pub fn unload_texture(&self, id: u32);

    /// Draws a rectangular section of a [`Texture`] to the screen.
    pub fn draw_texture<'a>(
        &self,
        id: u32,
        uv_min: (u32, u32),
        uv_max: (u32, u32),
        pos: (f32, f32),
    );
}
```

We will need to create an implementation of `Application` which manages the state for the game.
This state includes a set of entities where each entity has a position, velocity and sprite used
for drawing. A sprite is a rectangular section of a texture (sprites are packed together in the
same texture for [performance reasons](https://en.wikipedia.org/wiki/Texture_atlas)).

Feeling adventurous, we will model this with liberal use of references:

```rust
/// Identifies a texture resource owned by a [`Device`].
pub struct Texture<'a> {
    device: &'a Device,
    id: u32
}

impl<'a> Texture<'a> {
    /// Loads a texture by name.
    pub fn load(device: &'a Device, name: &'static str) -> Self {
        Self {
            device: &device,
            id: device.load_texture(name)
        }
    }
}

impl<'a> Drop for Texture<'a> {
    fn drop(&mut self) {
        self.device.unload_texture(self.id)
    }
}

/// Identifies a rectangular section of a [`Texture`] used as an individual sprite.
#[derive(Clone, Copy)]
pub struct Sprite<'a> {
    texture: &'a Texture<'a>,
    uv_min: (u32, u32),
    uv_max: (u32, u32),
}

/// A game entity, drawn using a single [`Sprite`].
pub struct Entity<'a> {
    sprite: Sprite<'a>,
    pos: (f32, f32),
    vel: (f32, f32),
}

/// Encapsulates the game state at a particular moment.
pub struct Game<'a> {
    device: &'a Device,
    background: &'a Texture<'a>,
    entities: Vec<Entity<'a>>,
}

impl<'a> Application for Game<'a> {
    ...
}
```

Now, let's just create an instance of `Game` and pass it to `run_app`:

```rust
fn main() {
    let device = Device::new();
    let background = Texture::load(&device, "background.png");
    let atlas = Texture::load(&device, "atlas.png");
    let player_sprite = Sprite {
        texture: &atlas,
        uv_min: (0, 0),
        uv_max: (64, 64)
    };
    let goombler_sprite = Sprite {
        texture: &atlas,
        uv_min: (64, 0),
        uv_max: (128, 64)
    };
    run_app(Game {
        device: &device,
        background: &background,
        entities: vec![
            Entity {
                sprite: player_sprite,
                pos: (0.0, 0.0),
                vel: (10.0, 0.0)
            },
            Entity {
                sprite: goombler_sprite,
                pos: (200.0, 0.0),
                vel: (-10.0, 0.0)
            },
            Entity {
                sprite: goombler_sprite,
                pos: (400.0, 0.0),
                vel: (-10.0, 0.0)
            }
        ]
    });
}
```

Just compile and we should be good to go!

...

...

...

Uh oh

```
error[E0597]: `device` does not live long enough
error[E0597]: `device` does not live long enough
error[E0597]: `atlas` does not live long enough
error[E0597]: `atlas` does not live long enough
error[E0597]: `device` does not live long enough
error[E0597]: `background` does not live long enough
```

Looks like we missed the `'static` bound on `run_app`. This is actually a pretty big problem. On
some platforms (e.g. web), the event loop doesn't start until after the main entry point
returns. That means we can't have any stack-allocated data persisting between events.

This calls our entire reference-based design into question. In times not long ago, we would
be reaching for [`Arc`](https://doc.rust-lang.org/std/sync/struct.Arc.html) or
[`Box::leak`](https://doc.rust-lang.org/std/boxed/struct.Box.html#method.leak). But now we have a
new tool at our disposal: Fortify!

Instead of passing `run_app` a `Game<'a>`, we can pass it a `Fortify<Game<'static>>`. Let's assume
the application framework was kind enough to provide the following implementation:

```rust
impl<T> Application for Fortify<T>
where
    for<'a> T: WithLifetime<'a>,
    for<'a> <T as WithLifetime<'a>>::Target: Application,
{
    fn draw(&self) {
        self.with_ref(|app| app.draw())
    }

    fn update(&mut self, step: f32) {
        self.with_mut(|app| app.update(step))
    }
}
```

*(It's okay if it doesn't. It just saves us the trouble of creating a wrapper type and doing it
ourselves)*

Now, lets bundle up all of our game's resources using the `fortify!` macro and try again:

```rust
fn main() {
    run_app(fortify! {
        let device = Device::new();
        let background = Texture::load(&device, "background.png");
        let atlas = Texture::load(&device, "atlas.png");
        let player_sprite = Sprite {
            texture: &atlas,
            uv_min: (0, 0),
            uv_max: (64, 64)
        };
        let goombler_sprite = Sprite {
            texture: &atlas,
            uv_min: (64, 0),
            uv_max: (128, 64)
        };
        yield Game {
            device: &device,
            background: &background,
            entities: vec![
                Entity {
                    sprite: player_sprite,
                    pos: (0.0, 0.0),
                    vel: (10.0, 0.0)
                },
                Entity {
                    sprite: goombler_sprite,
                    pos: (200.0, 0.0),
                    vel: (-10.0, 0.0)
                },
                Entity {
                    sprite: goombler_sprite,
                    pos: (400.0, 0.0),
                    vel: (-10.0, 0.0)
                }
            ]
        };
    });
}
```

Success! With a minor reorganization of the setup code, we were able to promote stack-allocated
variables into long-lived resources.