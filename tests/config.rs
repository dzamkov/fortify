#![allow(dead_code)]
use fortify::*;
use std::collections::HashMap;

pub struct User {
    pub name: String,
    pub data: u32,
    // ...
}

pub struct Config(Fortify<ConfigInner<'static>>);

#[derive(WithLifetime)]
struct ConfigInner<'a> {
    pub users: &'a Vec<User>,
    pub map: HashMap<&'a str, &'a User>,
}

impl Config {
    pub fn new(users: Vec<User>) -> Self {
        fn build_map<'a>(users: &'a Vec<User>) -> HashMap<&'a str, &'a User> {
            let mut map = HashMap::new();
            for user in users.iter() {
                map.insert(user.name.as_str(), user);
            }
            map
        }
        Config(fortify! {
            let users = users;
            yield ConfigInner {
                users: &users,
                map: build_map(&users)
            };
        })
    }

    pub fn get_user_by_name(&self, name: &str) -> Option<&User> {
        self.0.borrow().map.get(name).copied()
    }
}

#[test]
fn test() {
    let config = Config::new(vec![
        User {
            name: "Alice".to_string(),
            data: 24,
        },
        User {
            name: "Bob".to_string(),
            data: 30,
        },
    ]);
    assert!(config.get_user_by_name("Alice").unwrap().data == 24);
    assert!(config.get_user_by_name("Bob").unwrap().data == 30);
    assert!(config.get_user_by_name("Charlie").is_none());
}
