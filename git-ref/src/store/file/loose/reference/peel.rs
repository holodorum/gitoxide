use quick_error::quick_error;

use crate::{
    file,
    mutable::Target,
    store::{
        file::{find, loose},
        packed,
    },
};

quick_error! {
    /// The error returned by [`loose::Reference::follow_symbolic()`].
    #[derive(Debug)]
    #[allow(missing_docs)]
    pub enum Error {
        FindExisting(err: find::existing::Error) {
            display("Could not resolve symbolic reference name that is expected to exist")
            source(err)
        }
        Decode(err: loose::reference::decode::Error) {
            display("The reference could not be decoded.")
            source(err)
        }
    }
}

/// A function for use in [`loose::Reference::peel_to_id_in_place()`] to indicate no peeling should happen.
pub fn none(_id: &git_hash::oid) -> Result<Option<(git_object::Kind, &'_ [u8])>, Box<dyn std::error::Error>> {
    Ok(Some((git_object::Kind::Commit, &[])))
}

impl loose::Reference {
    /// Follow this symbolic reference one level and return the ref it refers to, possibly providing access to `packed` references for lookup.
    ///
    /// Returns `None` if this is not a symbolic reference, hence the leaf of the chain.
    pub fn follow_symbolic<'p>(
        &self,
        store: &file::Store,
        packed: Option<&'p packed::Buffer>,
    ) -> Option<Result<file::Reference<'p>, Error>> {
        match &self.target {
            Target::Peeled(_) => None,
            Target::Symbolic(full_name) => {
                let path = full_name.to_path();
                match store.find_one_with_verified_input(path.as_ref(), packed) {
                    Ok(Some(next)) => Some(Ok(next)),
                    Ok(None) => Some(Err(Error::FindExisting(find::existing::Error::NotFound(
                        path.into_owned(),
                    )))),
                    Err(err) => Some(Err(Error::FindExisting(find::existing::Error::Find(err)))),
                }
            }
        }
    }
}

///
pub mod to_id {
    use git_hash::oid;
    use quick_error::quick_error;
    use std::{collections::BTreeSet, path::PathBuf};

    use crate::{
        mutable::{FullName, Target},
        store::{file, file::loose, packed},
    };

    quick_error! {
        /// The error returned by [`Reference::peel_to_id_in_place()`].
        #[derive(Debug)]
        #[allow(missing_docs)]
        pub enum Error {
            PeelOne(err: loose::reference::peel::Error) {
                display("Could not peel a single level of a reference")
                from()
                source(err)
            }
            Cycle(start_absolute: PathBuf){
                display("Aborting due to reference cycle with first seen path being '{}'", start_absolute.display())
            }
            DepthLimitExceeded{  max_depth: usize  } {
                display("Refusing to follow more than {} levels of indirection", max_depth)
            }
        }
    }

    impl loose::Reference {
        /// Follow this symbolic reference until the end of the chain is reached and an object ID is available,
        /// and possibly peel this object until the final target object is revealed.
        ///
        /// If an error occurs this reference remains unchanged.
        pub fn peel_to_id_in_place(
            &mut self,
            store: &file::Store,
            packed: Option<&packed::Buffer>,
            _find: impl FnMut(&git_hash::oid) -> Result<Option<(git_object::Kind, &[u8])>, Box<dyn std::error::Error>>,
        ) -> Result<&oid, Error> {
            let mut seen = BTreeSet::new();
            let mut storage;
            let mut cursor = &mut *self;
            while let Some(next) = cursor.follow_symbolic(store, packed) {
                let next_ref = next?;
                if let crate::Kind::Peeled = next_ref.kind() {
                    match next_ref {
                        file::Reference::Loose(r) => *self = r,
                        file::Reference::Packed(p) => {
                            self.target = Target::Peeled(p.object());
                            self.name = FullName(p.name.0.to_owned());
                        }
                    };
                    break;
                }
                storage = next_ref;
                cursor = match &mut storage {
                    file::Reference::Loose(r) => r,
                    file::Reference::Packed(_) => unreachable!("handled above - we are done"),
                };
                if seen.contains(&cursor.name) {
                    return Err(Error::Cycle(store.base.join(cursor.name.to_path())));
                }
                seen.insert(cursor.name.clone());
                const MAX_REF_DEPTH: usize = 5;
                if seen.len() == MAX_REF_DEPTH {
                    return Err(Error::DepthLimitExceeded {
                        max_depth: MAX_REF_DEPTH,
                    });
                }
            }
            Ok(self.target.as_id().expect("to be peeled"))
        }
    }
}
