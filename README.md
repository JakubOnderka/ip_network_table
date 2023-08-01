ipnet-trie
========

IPv4 and IPv6 network fast lookup prefix trie.

[![Rust](https://github.com/bgpkit/ipnet-trie/actions/workflows/rust.yml/badge.svg)](https://github.com/bgpkit/ipnet-trie/actions/workflows/rust.yml)
[![Documentation](https://docs.rs/ipnet-trie/badge.svg)](https://docs.rs/ipnet-trie)
[![Crates.io](https://img.shields.io/crates/v/ipnet-trie.svg)](https://crates.io/crates/ipnet-trie)
[![License](https://img.shields.io/crates/l/ipnet-trie)](https://raw.githubusercontent.com/bgpkit/ipnet-trie/master/LICENSE)

## Description


This crate provides storage and retrieval of IPv4 and IPv6 network prefixes.

Currently, it uses [`ipnet`](https://docs.rs/ipnet/latest/ipnet/) crate as IP network data structure and fork of
 [`treebitmap`](https://github.com/hroi/treebitmap) ([fork](https://github.com/JakubOnderka/treebitmap)) as backend, 
that provides fast lookup times, and a small memory footprint. Backend can be changed in future releases.

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
ipnet = "2.8"
ipnet-trie = "0.0.1"
```

and then you can use it like this:

```rust
use std::net::{IpAddr, Ipv6Addr};
use ipnet::{IpNet, Ipv6Net};
use ipnet_trie::IpnetTrie;

let mut table = IpnetTrie::new();
let network = IpNet::from(Ipv6Net::new(Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0), 64).unwrap());
let ip_address = Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0x1);

assert_eq!(table.insert(network, "foo"), None);
// Get value for network from table
assert_eq!(table.longest_match(ip_address), Some((network, &"foo")));
```
