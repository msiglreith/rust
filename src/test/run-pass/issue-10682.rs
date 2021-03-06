// Copyright 2014 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Regression test for issue #10682
// Nested `proc` usage can't use outer owned data


fn work(_: Box<int>) {}
fn foo(_: proc()) {}

pub fn main() {
  let a = box 1;
  foo(proc() { foo(proc() { work(a) }) })
}
