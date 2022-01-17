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
variables into long-lived resources. Check out the full code for this example
[here](https://github.com/dzamkov/fortify/blob/master/tests/game.rs).