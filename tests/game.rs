#![allow(unused_must_use)]
use fortify::*;
use std::cell::Cell;
use std::fmt::Write;
use std::sync::{Arc, Mutex};

/// An interface to a graphics device used for drawing and managing textures.
pub struct Device {
    log: Arc<Mutex<dyn Write>>,
    next_texture_id: Cell<u32>,
}

impl Device {
    /// Creates a new [`Device`].
    pub fn new(log: Arc<Mutex<dyn Write>>) -> Self {
        writeln!(log.lock().unwrap(), "Initializing device");
        Device {
            log,
            next_texture_id: Cell::new(0),
        }
    }

    /// Loads a texture by name.
    pub fn load_texture(&self, name: &'static str) -> u32 {
        let id = self.next_texture_id.get();
        self.next_texture_id.set(id + 1);
        writeln!(self.log.lock().unwrap(), "Loading \"{}\" as texture {}", name, id);
        id
    }

    /// Unloads a texture.
    pub fn unload_texture(&self, id: u32) {
        writeln!(self.log.lock().unwrap(), "Unloading texture {}", id);
    }

    /// Draws a rectangular section of a [`Texture`] to the screen.
    pub fn draw_texture<'a>(
        &self,
        id: u32,
        uv_min: (u32, u32),
        uv_max: (u32, u32),
        pos: (f32, f32),
    ) {
        writeln!(
            self.log.lock().unwrap(),
            "Drawing texture {} from {:?} to {:?} at {:?}",
            id,
            uv_min,
            uv_max,
            pos
        );
    }
}

impl Drop for Device {
    fn drop(&mut self) {
        writeln!(self.log.lock().unwrap(), "Destroying device");
    }
}

/// Identifies a texture resource owned by a [`Device`].
pub struct Texture<'a> {
    device: &'a Device,
    id: u32
}

impl<'a> Texture<'a> {
    /// Loads a texture by name.
    pub fn load(device: &'a Device, name: &'static str) -> Self {
        Self {
            device,
            id: device.load_texture(name)
        }
    }
}

impl<'a> Drop for Texture<'a> {
    fn drop(&mut self) {
        self.device.unload_texture(self.id)
    }
}

/// Identifies a rectangular section of a [`Texture`] used as an individual sprite (multiple
/// sprites are typically packed into the same texture to improve performance).
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
#[derive(Lower)]
pub struct Game<'a> {
    device: &'a Device,
    background: &'a Texture<'a>,
    entities: Vec<Entity<'a>>,
}

/// An interactive application drawn on a two-dimensional surface.
pub trait Application {
    /// Draws the UI for the application.
    fn draw(&self);

    /// Updates the state of the application in response to the passage of time.
    fn update(&mut self, step: f32);
}

impl<'a> Application for Game<'a> {
    fn draw(&self) {
        self.device
            .draw_texture(self.background.id, (0, 0), (1024, 1024), (0.0, 0.0));
        for entity in self.entities.iter() {
            let sprite = &entity.sprite;
            self.device
                .draw_texture(sprite.texture.id, sprite.uv_min, sprite.uv_max, entity.pos);
        }
    }

    fn update(&mut self, step: f32) {
        for entity in self.entities.iter_mut() {
            let (pos_x, pos_y) = &mut entity.pos;
            let (vel_x, vel_y) = entity.vel;
            *pos_x += vel_x * step;
            *pos_y += vel_y * step;
        }
    }
}

// This implementation allows a "fortified" application to be used as an application itself.
impl<T> Application for Fortify<T>
where
    for<'a> T: Lower<'a>,
    for<'a> <T as Lower<'a>>::Target: Application,
{
    fn draw(&self) {
        self.borrow().draw()
    }

    fn update(&mut self, step: f32) {
        self.with_mut(|app| app.update(step))
    }
}

/// Runs an [`Application`].
pub fn run_app(mut app: impl Application + 'static) {
    for _ in 0..5 {
        app.draw();
        app.update(1.0);
    }
}

fn run(log: Arc<Mutex<dyn Write>>) {
    run_app(fortify! {
        let device = Device::new(log);
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

#[test]
fn test() {
    // Run program while logging output
    let log = Arc::new(Mutex::new(String::new()));
    run(log.clone());
    let output = log.lock().unwrap();

    // Prepare expected output
    let mut e = String::new();
    writeln!(&mut e, "Initializing device");
    writeln!(&mut e, "Loading \"background.png\" as texture 0");
    writeln!(&mut e, "Loading \"atlas.png\" as texture 1");
    writeln!(&mut e, "Drawing texture 0 from (0, 0) to (1024, 1024) at (0.0, 0.0)");
    writeln!(&mut e, "Drawing texture 1 from (0, 0) to (64, 64) at (0.0, 0.0)");
    writeln!(&mut e, "Drawing texture 1 from (64, 0) to (128, 64) at (200.0, 0.0)");
    writeln!(&mut e, "Drawing texture 1 from (64, 0) to (128, 64) at (400.0, 0.0)");
    writeln!(&mut e, "Drawing texture 0 from (0, 0) to (1024, 1024) at (0.0, 0.0)");
    writeln!(&mut e, "Drawing texture 1 from (0, 0) to (64, 64) at (10.0, 0.0)");
    writeln!(&mut e, "Drawing texture 1 from (64, 0) to (128, 64) at (190.0, 0.0)");
    writeln!(&mut e, "Drawing texture 1 from (64, 0) to (128, 64) at (390.0, 0.0)");
    writeln!(&mut e, "Drawing texture 0 from (0, 0) to (1024, 1024) at (0.0, 0.0)");
    writeln!(&mut e, "Drawing texture 1 from (0, 0) to (64, 64) at (20.0, 0.0)");
    writeln!(&mut e, "Drawing texture 1 from (64, 0) to (128, 64) at (180.0, 0.0)");
    writeln!(&mut e, "Drawing texture 1 from (64, 0) to (128, 64) at (380.0, 0.0)");
    writeln!(&mut e, "Drawing texture 0 from (0, 0) to (1024, 1024) at (0.0, 0.0)");
    writeln!(&mut e, "Drawing texture 1 from (0, 0) to (64, 64) at (30.0, 0.0)");
    writeln!(&mut e, "Drawing texture 1 from (64, 0) to (128, 64) at (170.0, 0.0)");
    writeln!(&mut e, "Drawing texture 1 from (64, 0) to (128, 64) at (370.0, 0.0)");
    writeln!(&mut e, "Drawing texture 0 from (0, 0) to (1024, 1024) at (0.0, 0.0)");
    writeln!(&mut e, "Drawing texture 1 from (0, 0) to (64, 64) at (40.0, 0.0)");
    writeln!(&mut e, "Drawing texture 1 from (64, 0) to (128, 64) at (160.0, 0.0)");
    writeln!(&mut e, "Drawing texture 1 from (64, 0) to (128, 64) at (360.0, 0.0)");
    writeln!(&mut e, "Unloading texture 1");
    writeln!(&mut e, "Unloading texture 0");
    writeln!(&mut e, "Destroying device");

    // Compare
    assert_eq!(output.as_str(), e.as_str());
}
