// Copyright 2018 Sergey Sherkunov <leinlawun@leinlawun.org>
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![feature(plugin)]
#![plugin(sig)]
#![sig]

use std::rc::Rc;

macro_rules! connect {
    ($object:expr, $signal:ident, $slot:expr) => {
        $object.$signal.push(Rc::new($slot))
    }
}

struct Hello {}

impl Hello {
    #[sig]
    pub fn hello(&self) {
        println!("Hello, ");
    }

    #[sig]
    pub fn hello_person(&self, name: &str) {
        println!("Hello, ");
    }

    pub fn hello_galaxy(&self) {
        println!("Galaxy!");
    }
}

fn world() {
    println!("World!");
}

fn universe() {
    println!("Universe!");
}

fn person(name: &str) {
    println!("{}", name);
}

fn main() {
    let mut hello1 = Hello {
        hello: vec![],
        hello_person: vec![],
    };
    let hello2 = Hello {
        hello: vec![],
        hello_person: vec![],
    };

    connect!(hello1, hello, world);
    connect!(hello1, hello, move || hello2.hello_galaxy());
    connect!(hello1, hello, universe);
    connect!(hello1, hello_person, person);

    hello1.hello();
    hello1.hello_person("Number 5");
}
