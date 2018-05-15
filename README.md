ip_network_table
========

IPv4 and IPv6 network fast lookup table.

[![Build Status](https://travis-ci.org/JakubOnderka/ip_network_table.svg?branch=master)](https://travis-ci.org/JakubOnderka/ip_network_table)
[![Coverage Status](https://coveralls.io/repos/github/JakubOnderka/ip_network_table/badge.svg?branch=master)](https://coveralls.io/github/JakubOnderka/ip_network_table?branch=master)
[![Crates.io](https://img.shields.io/crates/v/ip_network_table.svg)](https://crates.io/crates/ip_network_table)

- [Documentation](https://docs.rs/ip_network_table)

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
ip_network = "0.2"
ip_network_table = "0.1"
```

this to your crate root:

```rust
extern crate ip_network;
extern crate ip_network_table;
```

and then you can use it like this:

```rust
use std::net::{IpAddr, Ipv6Addr};
use ip_network::{IpNetwork, Ipv6Network};
use ip_network_table::Table;

let mut table: Table<&str> = Table::new();
let network = IpNetwork::from(Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0), 64).unwrap();
let ip_address = Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0x1);

assert_eq!(table.insert(network.clone(), "foo"), None);
// Get value for network from table
assert_eq!(table.longest_match(ip_address), Some((network, &"foo")));
```

Minimal required version of Rust compiler is 1.26 (because of `ip_network` crate). 
