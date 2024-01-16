use crate::IpnetTrie;
use bincode::error::{DecodeError, EncodeError};
use bincode::{encode_to_vec, Decode, Encode};
use ipnet::{IpNet, PrefixLenError};
use std::fmt;
use std::io::{Cursor, Read, Write};

pub struct IpnetTrieError {
    details: String,
}

impl IpnetTrieError {
    pub fn new(msg: &str) -> IpnetTrieError {
        IpnetTrieError {
            details: msg.to_string(),
        }
    }
}

impl std::fmt::Display for IpnetTrieError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.details)
    }
}

impl std::fmt::Debug for IpnetTrieError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.details)
    }
}

impl From<std::io::Error> for IpnetTrieError {
    fn from(error: std::io::Error) -> Self {
        IpnetTrieError::new(&error.to_string())
    }
}

impl From<EncodeError> for IpnetTrieError {
    fn from(error: EncodeError) -> Self {
        IpnetTrieError::new(&error.to_string())
    }
}

impl From<DecodeError> for IpnetTrieError {
    fn from(error: DecodeError) -> Self {
        IpnetTrieError::new(&error.to_string())
    }
}

impl From<PrefixLenError> for IpnetTrieError {
    fn from(error: PrefixLenError) -> Self {
        IpnetTrieError::new(&error.to_string())
    }
}

impl<T: Encode + Decode> IpnetTrie<T> {
    /// Exports the contents of the `IpnetTrie` to a writer.
    ///
    /// # Arguments
    ///
    /// * `writer` - A mutable reference to a writer where the exported data will be written.
    ///
    /// # Errors
    ///
    /// Returns an `IpnetTrieError` if there is an error in encoding or writing the data.
    pub fn export_to_writer(&self, writer: &mut impl Write) -> Result<(), IpnetTrieError> {
        for (ipnet, value) in self.iter() {
            let bytes = encode_to_vec(
                (ipnet.addr(), ipnet.prefix_len(), value),
                bincode::config::standard(),
            )?;
            writer.write_all(&bytes)?;
        }
        Ok(())
    }

    /// Exports all values in the trie to a byte vector.
    ///
    /// # Returns
    ///
    /// A vector of bytes that represents all the values in the trie. Each value is a tuple that
    /// consists of the IP network address, the prefix length, and the value associated with this network.
    pub fn export_to_bytes(&self) -> Vec<u8> {
        let mut bytes = Vec::new();
        for (ipnet, value) in self.iter() {
            bytes.extend(
                encode_to_vec(
                    (ipnet.addr(), ipnet.prefix_len(), value),
                    bincode::config::standard(),
                )
                .unwrap(),
            );
        }
        bytes
    }

    /// Imports all values from a byte slice into the trie.
    ///
    /// # Parameters
    ///
    /// * `bytes` - A slice of bytes that represents all values to be imported. Each value is a tuple that
    /// consists of the IP network address, the prefix length, and the value associated with this network.
    ///
    /// *NOTE: This method drops all existing values in the trie and replaces them with the ones provided.*/
    pub fn import_from_bytes(&mut self, bytes: &[u8]) {
        let mut bytes = bytes;
        let total_len = bytes.len() as u64;
        let mut reader = Cursor::new(&mut bytes);
        while reader.position() < total_len {
            let (addr, prefix_len, value) = bincode::decode_from_std_read::<
                (std::net::IpAddr, u8, T),
                _,
                _,
            >(&mut reader, bincode::config::standard())
            .unwrap();
            let ipnet = IpNet::new(addr, prefix_len).unwrap();
            self.insert(ipnet, value);
        }
    }

    /// Imports IP addresses and their corresponding values from a `Read` trait object.
    ///
    /// # Arguments
    ///
    /// * `reader` - A mutable reference to a `Read` trait object.
    ///
    /// # Errors
    ///
    /// Returns an `IpnetTrieError` if there is an error during the import process.
    pub fn import_from_reader(&mut self, reader: &mut impl Read) -> Result<(), IpnetTrieError> {
        loop {
            let (addr, prefix_len, value) =
                match bincode::decode_from_std_read::<(std::net::IpAddr, u8, T), _, _>(
                    reader,
                    bincode::config::standard(),
                ) {
                    Ok(data) => data,
                    Err(error) => {
                        if let DecodeError::Io { inner, .. } = &error {
                            if inner.kind() == std::io::ErrorKind::UnexpectedEof {
                                // We've reached the end of the file
                                break;
                            }
                        }
                        return Err(error.into());
                    }
                };
            let ipnet = IpNet::new(addr, prefix_len)?;
            self.insert(ipnet, value);
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ipnet::Ipv4Net;
    use std::io::Cursor;
    use std::net::Ipv4Addr;

    impl IpnetTrie<String> {
        fn new_test() -> Self {
            let mut trie = IpnetTrie::new();
            let ipnet = Ipv4Net::new(Ipv4Addr::new(192, 168, 1, 0), 24).unwrap();
            trie.insert(ipnet, "Value 1".to_string());
            trie
        }

        fn new_test_large() -> Self {
            let mut trie = IpnetTrie::new();
            for ip in 0..1_000_000 {
                let ipnet = Ipv4Net::new(Ipv4Addr::from(ip), 32).unwrap();
                trie.insert(ipnet, "Value 1".to_string());
            }
            trie
        }
    }

    #[test]
    fn test_export_import() {
        let trie = IpnetTrie::<String>::new_test();
        let bytes = trie.export_to_bytes();
        let mut new_trie = IpnetTrie::<String>::new_test();
        new_trie.import_from_bytes(&bytes);

        assert_eq!(trie.iter().count(), new_trie.iter().count());
        for (net, value) in trie.iter() {
            assert_eq!(new_trie.exact_match(net).unwrap(), value);
        }
    }

    // Our new test functions
    #[test]
    fn test_export_import_with_writer_reader() {
        let trie = IpnetTrie::<String>::new_test();
        let mut buffer = Vec::new();

        // Use a memory buffer as our Writer in this test
        trie.export_to_writer(&mut buffer).unwrap();

        // Now read it back into a new trie
        let mut new_trie = IpnetTrie::<String>::new();
        let mut reader = Cursor::new(buffer);
        new_trie.import_from_reader(&mut reader).unwrap();

        assert_eq!(trie.iter().count(), new_trie.iter().count());
        for (net, value) in trie.iter() {
            assert_eq!(new_trie.exact_match(net).unwrap(), value);
        }
    }

    #[test]
    fn test_export_import_with_local_files() {
        let trie = IpnetTrie::<String>::new_test_large();

        let tmp_dir = tempdir::TempDir::new("ipnet_trie_test").unwrap();

        let file_path = tmp_dir.path().join("test_ipnet_trie_uncompressed.bin");
        let mut writer = oneio::get_writer(file_path.to_str().unwrap()).unwrap();
        trie.export_to_writer(&mut writer).unwrap();
        drop(writer);
        println!(
            "The size of the file {} is {}",
            file_path.to_str().unwrap(),
            std::fs::metadata(file_path.to_str().unwrap())
                .unwrap()
                .len()
        );

        let mut new_trie = IpnetTrie::<String>::new();
        let mut reader = oneio::get_reader(file_path.to_str().unwrap()).unwrap();
        new_trie.import_from_reader(&mut reader).unwrap();
        assert_eq!(trie.iter().count(), new_trie.iter().count());
        for (net, value) in trie.iter() {
            assert_eq!(new_trie.exact_match(net).unwrap(), value);
        }

        // compressed file should have roughly 20% of the size of the uncompressed file for large tries
        let file_path = tmp_dir.path().join("test_ipnet_trie_compressed.bin.gz");
        let mut writer = oneio::get_writer(file_path.to_str().unwrap()).unwrap();
        trie.export_to_writer(&mut writer).unwrap();
        drop(writer);
        println!(
            "The size of the file {} is {}",
            file_path.to_str().unwrap(),
            std::fs::metadata(file_path.to_str().unwrap())
                .unwrap()
                .len()
        );

        let mut new_trie = IpnetTrie::<String>::new();
        let mut reader = oneio::get_reader(file_path.to_str().unwrap()).unwrap();
        new_trie.import_from_reader(&mut reader).unwrap();
        assert_eq!(trie.iter().count(), new_trie.iter().count());
        for (net, value) in trie.iter() {
            assert_eq!(new_trie.exact_match(net).unwrap(), value);
        }
    }
}
