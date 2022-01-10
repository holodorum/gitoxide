use crate::{extension, State};
use filetime::FileTime;
use git_hash::Kind;

pub mod header {
    pub(crate) const SIZE: usize = 4 /*signature*/ + 4 /*version*/ + 4 /* num entries */;

    mod error {
        use quick_error::quick_error;

        quick_error! {
            #[derive(Debug)]
            pub enum Error {
                Corrupt(message: &'static str) {
                    display("{}", message)
                }
                UnsupportedVersion(version: u32) {
                    display("Index version {} is not supported", version)
                }
            }
        }
    }
    use crate::{util::read_u32, Version};
    pub use error::Error;

    pub(crate) fn decode(data: &[u8], object_hash: git_hash::Kind) -> Result<(crate::Version, u32, &[u8]), Error> {
        if data.len() < (3 * 4) + object_hash.len_in_bytes() {
            return Err(Error::Corrupt(
                "File is too small even for header with zero entries and smallest hash",
            ));
        }

        const SIGNATURE: &[u8] = b"DIRC";
        let (signature, data) = data.split_at(4);
        if signature != SIGNATURE {
            return Err(Error::Corrupt(
                "Signature mismatch - this doesn't claim to be a header file",
            ));
        }

        let (version, data) = data.split_at(4);
        let version = match read_u32(version) {
            2 => Version::V2,
            3 => Version::V3,
            4 => Version::V4,
            unknown => return Err(Error::UnsupportedVersion(unknown)),
        };
        let (entries, data) = data.split_at(4);
        let entries = read_u32(entries);

        Ok((version, entries, data))
    }
}

mod error {
    use quick_error::quick_error;

    use crate::decode;

    quick_error! {
        #[derive(Debug)]
        pub enum Error {
            Header(err: decode::header::Error) {
                display("The header could not be decoded")
                source(err)
                from()
            }
        }
    }
}
pub use error::Error;

impl State {
    pub fn from_bytes(data: &[u8], timestamp: FileTime, object_hash: git_hash::Kind) -> Result<Self, Error> {
        let (version, num_entries, post_header_data) = header::decode(&data, object_hash)?;
        let start_of_extensions = extension::end_of_index_entry::decode(&data, object_hash);
        let mut ext = Extensions::default();

        // Note that we ignore all errors for optional signatures.
        match start_of_extensions {
            Some(offset) => {
                ext = load_extensions(&data[offset..], object_hash);
                todo!("load all extensions in thread, then get IEOT, then possibly multi-threaded entry parsing")
            }
            None => todo!("load entries singlge-threaded, then extensions"),
        }

        Ok(State {
            timestamp,
            version,
            cache_tree: ext.cache_tree,
        })
    }
}

fn load_extensions(beginning_of_extensions: &[u8], object_hash: git_hash::Kind) -> Extensions {
    let extensions = extension::Iter::new_without_checksum(beginning_of_extensions, object_hash);
    let mut ext = Extensions::default();
    for (signature, ext_data) in extensions {
        match signature {
            extension::tree::SIGNATURE => {
                ext.cache_tree = extension::tree::decode(ext_data, object_hash);
            }
            extension::end_of_index_entry::SIGNATURE => {} // skip already done
            _unknown => {}                                 // skip unknown extensions, too
        }
    }
    ext
}

#[derive(Default)]
struct Extensions {
    cache_tree: Option<extension::Tree>,
}
