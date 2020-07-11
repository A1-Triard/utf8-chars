![travis](https://travis-ci.org/A1-Triard/utf8-chars.svg?branch=master)

# utf8-chars

Char-per-char iterator and `read_char` method for `BufRead`.

```rust
use std::io::{stdin};
use utf8_chars::{BufReadCharsExt};

fn main() {
    for c in stdin().lock().chars().map(|x| x.unwrap()) {
        println!("{}", c);
    }
}
```
