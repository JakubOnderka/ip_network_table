//! This crate provides storage and retrieval of IPv4 and IPv6 network prefixes.
//!
//! Currently, it uses `ip_network` crate, that provides IP network data structure and
//! `treebitmap` as backend, that provides fast lookup times, and a small memory footprint.
//! Backend can be changed in future releases.
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
use ip_network::{IpNetwork, Ipv4Network, Ipv6Network};
use treebitmap::IpLookupTable;

/// Table holding IPv4 and IPv6 network prefixes.
pub struct Table<T> {
    ipv4: IpLookupTable<Ipv4Addr, T>,
    ipv6: IpLookupTable<Ipv6Addr, T>,
}

impl<T> Table<T> {
    /// Constructs a new, empty `Table<T>`.
    pub fn new() -> Self {
        Self::with_capacity(0, 0)
    }

    /// Constructs a new, empty `Table<T>` with the specified capacity.
    pub fn with_capacity(ipv4_size: usize, ipv6_size: usize) -> Self {
        Self {
            ipv4: IpLookupTable::with_capacity(ipv4_size),
            ipv6: IpLookupTable::with_capacity(ipv6_size),
        }
    }

    /// Returns the number of elements in the table.
    pub fn len(&self) -> (usize, usize) {
        (self.ipv4.len(), self.ipv6.len())
    }

    /// Insert a value for the IpNetwork. If prefix existed previously, the old value is returned.
    ///
    /// # Example
    ///
    /// ```
    /// extern crate ip_network;
    /// extern crate ip_network_table;
    ///
    /// use ip_network_table::Table;
    /// use ip_network::Ipv6Network;
    /// use std::net::Ipv6Addr;
    ///
    /// # fn main() {
    /// let mut table: Table<&str> = Table::new();
    /// let network = Ipv6Network::from(Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0), 64).unwrap();
    ///
    /// assert_eq!(table.insert(network.clone(), "foo"), None);
    /// // Insert duplicate
    /// assert_eq!(table.insert(network.clone(), "bar"), Some("foo"));
    /// // Value is replaced
    /// assert_eq!(table.insert(network, "null"), Some("bar"));
    /// # }
    /// ```
    pub fn insert<N: Into<IpNetwork>>(&mut self, network: N, data: T) -> Option<T> {
        match network.into() {
            IpNetwork::V4(ipv4_network) => self.insert_ipv4(ipv4_network, data),
            IpNetwork::V6(ipv6_network) => self.insert_ipv6(ipv6_network, data),
        }
    }

    /// Specific version of `insert` for IPv4 network.
    pub fn insert_ipv4(&mut self, network: Ipv4Network, data: T) -> Option<T> {
        self.ipv4.insert(
            network.network_address(),
            network.netmask() as u32,
            data,
        )
    }

    /// Specific version of `insert` for IPv6 network.
    pub fn insert_ipv6(&mut self, network: Ipv6Network, data: T) -> Option<T> {
        self.ipv6.insert(
            network.network_address(),
            network.netmask() as u32,
            data,
        )
    }

    /// Insert a value for the IpNetwork. If prefix existed previously, the old value is returned.
    ///
    /// # Example
    ///
    /// ```
    /// extern crate ip_network;
    /// extern crate ip_network_table;
    ///
    /// use ip_network_table::Table;
    /// use ip_network::Ipv6Network;
    /// use std::net::Ipv6Addr;
    ///
    /// # fn main() {
    /// let mut table: Table<&str> = Table::new();
    /// let network = Ipv6Network::from(Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0), 64).unwrap();
    ///
    /// assert_eq!(table.insert(network.clone(), "foo"), None);
    /// // Remove network from table
    /// assert_eq!(table.remove(network.clone()), Some("foo"));
    /// // Network is removed
    /// assert_eq!(table.exact_match(network), None);
    /// # }
    /// ```
    pub fn remove<N: Into<IpNetwork>>(&mut self, network: N) -> Option<T> {
        match network.into() {
            IpNetwork::V4(ipv4_network) => self.remove_ipv4(ipv4_network),
            IpNetwork::V6(ipv6_network) => self.remove_ipv6(ipv6_network),
        }
    }

    /// Specific version of `remove` for IPv4 network.
    pub fn remove_ipv4(&mut self, network: Ipv4Network) -> Option<T> {
        self.ipv4.remove(
            network.network_address(),
            network.netmask() as u32,
        )
    }

    /// Specific version of `remove` for IPv6 network.
    pub fn remove_ipv6(&mut self, network: Ipv6Network) -> Option<T> {
        self.ipv6.remove(
            network.network_address(),
            network.netmask() as u32,
        )
    }

    /// Get pointer to value from table based on exact network match.
    /// If network is not in table, `None` is returned.
    ///
    /// # Example
    ///
    /// ```
    /// extern crate ip_network;
    /// extern crate ip_network_table;
    ///
    /// use ip_network_table::Table;
    /// use ip_network::Ipv6Network;
    /// use std::net::Ipv6Addr;
    ///
    /// # fn main() {
    /// let mut table: Table<&str> = Table::new();
    /// let network_a = Ipv6Network::from(Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0), 64).unwrap();
    /// let network_b = Ipv6Network::from(Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0), 128).unwrap();
    ///
    /// assert_eq!(table.insert(network_a.clone(), "foo"), None);
    /// // Get value for network from table
    /// assert_eq!(table.exact_match(network_a.clone()), Some(&"foo"));
    /// // Network B doesnt exists in table
    /// assert_eq!(table.exact_match(network_b), None);
    /// # }
    /// ```
    pub fn exact_match<N: Into<IpNetwork>>(&self, network: N) -> Option<&T> {
        match network.into() {
            IpNetwork::V4(ipv4_network) => self.exact_match_ipv4(ipv4_network),
            IpNetwork::V6(ipv6_network) => self.exact_match_ipv6(ipv6_network),
        }
    }

    /// Specific version of `exact_match` for IPv4.
    pub fn exact_match_ipv4(&self, network: Ipv4Network) -> Option<&T> {
        self.ipv4.exact_match(
            network.network_address(),
            network.netmask() as u32,
        )
    }

    /// Specific version of `exact_match` for IPv6.
    pub fn exact_match_ipv6(&self, network: Ipv6Network) -> Option<&T> {
        self.ipv6.exact_match(
            network.network_address(),
            network.netmask() as u32,
        )
    }

    /// Find most specific IP network in table that contains given IP address. If no network in table contains
    /// given IP address, `None` is returned.
    ///
    /// # Example
    ///
    /// ```
    /// extern crate ip_network;
    /// extern crate ip_network_table;
    ///
    /// use ip_network_table::Table;
    /// use ip_network::{IpNetwork, Ipv6Network};
    /// use std::net::{IpAddr, Ipv6Addr};
    ///
    /// # fn main() {
    /// let mut table: Table<&str> = Table::new();
    /// let network = IpNetwork::from(Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0), 64).unwrap();
    /// let ip_address = Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0x1);
    ///
    /// assert_eq!(table.insert(network.clone(), "foo"), None);
    /// // Get value for network from table
    /// assert_eq!(table.longest_match(ip_address), Some((network, &"foo")));
    /// # }
    /// ```
    pub fn longest_match<A: Into<IpAddr>>(&self, ip: A) -> Option<(IpNetwork, &T)> {
        match ip.into() {
            IpAddr::V4(ipv4) => self.longest_match_ipv4(ipv4)
                .map(|(n, t)| (IpNetwork::V4(n), t)),
            IpAddr::V6(ipv6) => self.longest_match_ipv6(ipv6)
                .map(|(n, t)| (IpNetwork::V6(n), t)),
        }
    }

    /// Specific version of `longest_match` for IPv4 address.
    #[inline]
    pub fn longest_match_ipv4(&self, ip: Ipv4Addr) -> Option<(Ipv4Network, &T)> {
        match self.ipv4.longest_match(ip) {
            Some((addr, mask, data)) => Some((Ipv4Network::from(addr, mask as u8).unwrap(), data)),
            None => None,
        }
    }

    /// Specific version of `longest_match` for IPv6 address.
    #[inline]
    pub fn longest_match_ipv6(&self, ip: Ipv6Addr) -> Option<(Ipv6Network, &T)> {
        match self.ipv6.longest_match(ip) {
            Some((addr, mask, data)) => Some((Ipv6Network::from(addr, mask as u8).unwrap(), data)),
            None => None,
        }
    }

    /// Iterator for all networks in table, first are iterated IPv4 and then IPv6 networks. Order is not guaranteed.
    ///
    /// # Example
    ///
    /// ```
    /// extern crate ip_network;
    /// extern crate ip_network_table;
    ///
    /// use ip_network_table::Table;
    /// use ip_network::{IpNetwork, Ipv4Network, Ipv6Network};
    /// use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
    ///
    /// # fn main() {
    /// let mut table: Table<&str> = Table::new();
    /// let network_a = Ipv4Network::from(Ipv4Addr::new(192, 168, 0, 0), 24).unwrap();
    /// assert_eq!(table.insert(network_a.clone(), "foo"), None);
    /// let network_b = Ipv6Network::from(Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0), 64).unwrap();
    /// assert_eq!(table.insert(network_b.clone(), "foo"), None);
    ///
    /// let mut iterator = table.iter();
    /// assert_eq!(iterator.next(), Some((IpNetwork::V4(network_a), &"foo")));
    /// assert_eq!(iterator.next(), Some((IpNetwork::V6(network_b), &"foo")));
    /// assert_eq!(iterator.next(), None);
    /// # }
    /// ```
    pub fn iter(&self) -> Iter<T> {
        Iter {
            ipv4: self.ipv4.iter(),
            ipv6: self.ipv6.iter(),
        }
    }
}

/// Table iterator.
pub struct Iter<'a, T: 'a> {
    ipv4: treebitmap::Iter<'a, Ipv4Addr, T>,
    ipv6: treebitmap::Iter<'a, Ipv6Addr, T>,
}

impl<'a, T> Iterator for Iter<'a, T> {
    type Item = (IpNetwork, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        match self.ipv4.next() {
            Some((addr, mask, data)) => Some((
                IpNetwork::V4(Ipv4Network::from(addr, mask as u8).unwrap()),
                data,
            )),
            None => match self.ipv6.next() {
                Some((addr, mask, data)) => Some((
                    IpNetwork::V6(Ipv6Network::from(addr, mask as u8).unwrap()),
                    data,
                )),
                None => None,
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::Table;
    use std::net::{Ipv4Addr, Ipv6Addr};
    use ip_network::{Ipv4Network, Ipv6Network};

    #[test]
    fn insert_ipv4_ipv6() {
        let mut table: Table<u32> = Table::new();
        table.insert(
            Ipv4Network::from(Ipv4Addr::new(127, 0, 0, 0), 16).unwrap(),
            1,
        );
        table.insert(
            Ipv6Network::from(Ipv6Addr::new(1, 2, 3, 4, 5, 6, 7, 8), 128).unwrap(),
            1,
        );
    }
}
