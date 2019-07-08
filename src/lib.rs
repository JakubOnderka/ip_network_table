//! This crate provides storage and retrieval of IPv4 and IPv6 network prefixes.
//!
//! Currently, it uses `ip_network` crate, that provides IP network data structure and
//! `treebitmap` as backend, that provides fast lookup times, and a small memory footprint.
//! Backend can be changed in future releases.
//!
//! ## Examples
//!
//! ```rust
//! use std::net::{IpAddr, Ipv6Addr};
//! use ip_network::{IpNetwork, Ipv6Network};
//! use ip_network_table::IpNetworkTable;
//!
//! let mut table = IpNetworkTable::new();
//! let network = IpNetwork::new(Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0), 64).unwrap();
//! let ip_address = Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0x1);
//!
//! assert_eq!(table.insert(network.clone(), "foo"), None);
//! // Get value for network from table
//! assert_eq!(table.longest_match(ip_address), Some((network, &"foo")));
//! ```

use ip_network::{IpNetwork, Ipv4Network, Ipv6Network};
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
use treebitmap::IpLookupTable;

/// Table holding IPv4 and IPv6 network prefixes with value.
#[derive(Default)]
pub struct IpNetworkTable<T> {
    ipv4: IpLookupTable<Ipv4Addr, T>,
    ipv6: IpLookupTable<Ipv6Addr, T>,
}

impl<T> IpNetworkTable<T> {
    /// Constructs a new, empty `IpNetworkTable<T>`.
    pub fn new() -> Self {
        Self::with_capacity(0, 0)
    }

    /// Constructs a new, empty `IpNetworkTable<T>` with the specified capacity.
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

    /// Returns `true` if table is empty.
    pub fn is_empty(&self) -> bool {
        self.ipv4.is_empty() && self.ipv6.is_empty()
    }

    /// Insert a value for the `IpNetwork`. If prefix existed previously, the old value is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use ip_network_table::IpNetworkTable;
    /// use ip_network::Ipv6Network;
    /// use std::net::Ipv6Addr;
    ///
    /// let mut table: IpNetworkTable<&str> = IpNetworkTable::new();
    /// let network = Ipv6Network::new(Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0), 64).unwrap();
    ///
    /// assert_eq!(table.insert(network.clone(), "foo"), None);
    /// // Insert duplicate
    /// assert_eq!(table.insert(network.clone(), "bar"), Some("foo"));
    /// // Value is replaced
    /// assert_eq!(table.insert(network, "null"), Some("bar"));
    /// ```
    pub fn insert<N: Into<IpNetwork>>(&mut self, network: N, data: T) -> Option<T> {
        match network.into() {
            IpNetwork::V4(ipv4_network) => self.ipv4.insert(
                ipv4_network.network_address(),
                ipv4_network.netmask() as u32,
                data,
            ),
            IpNetwork::V6(ipv6_network) => self.ipv6.insert(
                ipv6_network.network_address(),
                ipv6_network.netmask() as u32,
                data,
            ),
        }
    }

    /// Remove a `IpNetwork` from table. If prefix existed, the value is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use ip_network_table::IpNetworkTable;
    /// use ip_network::Ipv6Network;
    /// use std::net::Ipv6Addr;
    ///
    /// let mut table: IpNetworkTable<&str> = IpNetworkTable::new();
    /// let network = Ipv6Network::new(Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0), 64).unwrap();
    ///
    /// assert_eq!(table.insert(network.clone(), "foo"), None);
    /// // Remove network from table
    /// assert_eq!(table.remove(network.clone()), Some("foo"));
    /// // Network is removed
    /// assert_eq!(table.exact_match(network), None);
    /// ```
    pub fn remove<N: Into<IpNetwork>>(&mut self, network: N) -> Option<T> {
        match network.into() {
            IpNetwork::V4(ipv4_network) => self.ipv4.remove(
                ipv4_network.network_address(),
                ipv4_network.netmask() as u32,
            ),
            IpNetwork::V6(ipv6_network) => self.ipv6.remove(
                ipv6_network.network_address(),
                ipv6_network.netmask() as u32,
            ),
        }
    }

    /// Get pointer to value from table based on exact network match.
    /// If network is not in table, `None` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use ip_network_table::IpNetworkTable;
    /// use ip_network::Ipv6Network;
    /// use std::net::Ipv6Addr;
    ///
    /// let mut table: IpNetworkTable<&str> = IpNetworkTable::new();
    /// let network_a = Ipv6Network::new(Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0), 64).unwrap();
    /// let network_b = Ipv6Network::new(Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0), 128).unwrap();
    ///
    /// assert_eq!(table.insert(network_a.clone(), "foo"), None);
    /// // Get value for network from table
    /// assert_eq!(table.exact_match(network_a.clone()), Some(&"foo"));
    /// // Network B doesnt exists in table
    /// assert_eq!(table.exact_match(network_b), None);
    /// ```
    pub fn exact_match<N: Into<IpNetwork>>(&self, network: N) -> Option<&T> {
        match network.into() {
            IpNetwork::V4(ipv4_network) => self.ipv4.exact_match(
                ipv4_network.network_address(),
                ipv4_network.netmask() as u32,
            ),
            IpNetwork::V6(ipv6_network) => self.ipv6.exact_match(
                ipv6_network.network_address(),
                ipv6_network.netmask() as u32,
            ),
        }
    }

    /// Find most specific IP network in table that contains given IP address. If no network in table contains
    /// given IP address, `None` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use ip_network_table::IpNetworkTable;
    /// use ip_network::{IpNetwork, Ipv6Network};
    /// use std::net::{IpAddr, Ipv6Addr};
    ///
    /// let mut table: IpNetworkTable<&str> = IpNetworkTable::new();
    /// let network = IpNetwork::new(Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0), 64).unwrap();
    /// let ip_address = Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0x1);
    ///
    /// assert_eq!(table.insert(network.clone(), "foo"), None);
    /// // Get value for network from table
    /// assert_eq!(table.longest_match(ip_address), Some((network, &"foo")));
    /// ```
    pub fn longest_match<A: Into<IpAddr>>(&self, ip: A) -> Option<(IpNetwork, &T)> {
        match ip.into() {
            IpAddr::V4(ipv4) => self
                .longest_match_ipv4(ipv4)
                .map(|(n, t)| (IpNetwork::V4(n), t)),
            IpAddr::V6(ipv6) => self
                .longest_match_ipv6(ipv6)
                .map(|(n, t)| (IpNetwork::V6(n), t)),
        }
    }

    /// Specific version of `longest_match` for IPv4 address.
    #[inline]
    pub fn longest_match_ipv4(&self, ip: Ipv4Addr) -> Option<(Ipv4Network, &T)> {
        self.ipv4
            .longest_match(ip)
            .map(|(addr, mask, data)| (Ipv4Network::new(addr, mask as u8).unwrap(), data))
    }

    /// Specific version of `longest_match` for IPv6 address.
    #[inline]
    pub fn longest_match_ipv6(&self, ip: Ipv6Addr) -> Option<(Ipv6Network, &T)> {
        self.ipv6
            .longest_match(ip)
            .map(|(addr, mask, data)| (Ipv6Network::new(addr, mask as u8).unwrap(), data))
    }

    /// Iterator for all networks in table, first are iterated IPv4 and then IPv6 networks. Order is not guaranteed.
    ///
    /// # Examples
    ///
    /// ```
    /// use ip_network_table::IpNetworkTable;
    /// use ip_network::{IpNetwork, Ipv4Network, Ipv6Network};
    /// use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};
    ///
    /// let mut table: IpNetworkTable<&str> = IpNetworkTable::new();
    /// let network_a = Ipv4Network::new(Ipv4Addr::new(192, 168, 0, 0), 24).unwrap();
    /// assert_eq!(table.insert(network_a.clone(), "foo"), None);
    /// let network_b = Ipv6Network::new(Ipv6Addr::new(0x2001, 0xdb8, 0xdead, 0xbeef, 0, 0, 0, 0), 64).unwrap();
    /// assert_eq!(table.insert(network_b.clone(), "foo"), None);
    ///
    /// let mut iterator = table.iter();
    /// assert_eq!(iterator.next(), Some((IpNetwork::V4(network_a), &"foo")));
    /// assert_eq!(iterator.next(), Some((IpNetwork::V6(network_b), &"foo")));
    /// assert_eq!(iterator.next(), None);
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
            Some((addr, mask, data)) => Some((IpNetwork::new(addr, mask as u8).unwrap(), data)),
            None => self
                .ipv6
                .next()
                .map(|(addr, mask, data)| (IpNetwork::new(addr, mask as u8).unwrap(), data)),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::IpNetworkTable;
    use ip_network::{Ipv4Network, Ipv6Network};
    use std::net::{Ipv4Addr, Ipv6Addr};

    #[test]
    fn insert_ipv4_ipv6() {
        let mut table = IpNetworkTable::new();
        table.insert(
            Ipv4Network::new(Ipv4Addr::new(127, 0, 0, 0), 16).unwrap(),
            1,
        );
        table.insert(
            Ipv6Network::new(Ipv6Addr::new(1, 2, 3, 4, 5, 6, 7, 8), 128).unwrap(),
            1,
        );
    }

    #[test]
    fn exact_match_ipv4() {
        let mut table = IpNetworkTable::new();
        table.insert(
            Ipv4Network::new(Ipv4Addr::new(127, 0, 0, 0), 16).unwrap(),
            1,
        );
        let m = table.exact_match(Ipv4Network::new(Ipv4Addr::new(127, 0, 0, 0), 16).unwrap());
        assert_eq!(m, Some(&1));
        let m = table.exact_match(Ipv4Network::new(Ipv4Addr::new(127, 0, 0, 0), 17).unwrap());
        assert_eq!(m, None);
        let m = table.exact_match(Ipv4Network::new(Ipv4Addr::new(127, 0, 0, 0), 15).unwrap());
        assert_eq!(m, None);
    }

    #[test]
    fn exact_match_ipv6() {
        let mut table = IpNetworkTable::new();
        table.insert(
            Ipv6Network::new(Ipv6Addr::new(1, 2, 3, 4, 5, 6, 7, 8), 127).unwrap(),
            1,
        );
        let m = table.exact_match(Ipv6Network::new(Ipv6Addr::new(1, 2, 3, 4, 5, 6, 7, 8), 127).unwrap());
        assert_eq!(m, Some(&1));
        let m = table.exact_match(Ipv6Network::new(Ipv6Addr::new(1, 2, 3, 4, 5, 6, 7, 8), 128).unwrap());
        assert_eq!(m, None);
        let m = table.exact_match(Ipv6Network::new(Ipv6Addr::new(1, 2, 3, 4, 5, 6, 7, 8), 126).unwrap());
        assert_eq!(m, None);
    }
}
