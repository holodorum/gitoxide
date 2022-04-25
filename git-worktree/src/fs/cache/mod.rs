use super::Cache;
use crate::fs;
use std::path::{Path, PathBuf};

#[derive(Clone)]
pub enum State {
    /// Useful for checkout where directories need creation, but we need to access attributes as well.
    CreateDirectoryAndAttributesStack {
        /// If there is a symlink or a file in our path, try to unlink it before creating the directory.
        unlink_on_collision: bool,

        /// just for testing
        #[cfg(debug_assertions)]
        test_mkdir_calls: usize,
        /// State to handle attribute information
        attributes: state::Attributes,
    },
    /// Used when adding files, requiring access to both attributes and ignore information, for example during add operations.
    AttributesAndIgnoreStack {
        /// State to handle attribute information
        attributes: state::Attributes,
        /// State to handle exclusion information
        ignore: state::Ignore,
    },
    /// Used when providing worktree status information.
    IgnoreStack(state::Ignore),
}

#[cfg(debug_assertions)]
impl Cache {
    pub fn num_mkdir_calls(&self) -> usize {
        match self.state {
            State::CreateDirectoryAndAttributesStack { test_mkdir_calls, .. } => test_mkdir_calls,
            _ => 0,
        }
    }

    pub fn reset_mkdir_calls(&mut self) {
        if let State::CreateDirectoryAndAttributesStack { test_mkdir_calls, .. } = &mut self.state {
            *test_mkdir_calls = 0;
        }
    }

    pub fn unlink_on_collision(&mut self, value: bool) {
        if let State::CreateDirectoryAndAttributesStack {
            unlink_on_collision, ..
        } = &mut self.state
        {
            *unlink_on_collision = value;
        }
    }
}

pub struct Platform<'a> {
    parent: &'a Cache,
    is_dir: Option<bool>,
}

impl Cache {
    /// Create a new instance with `worktree_root` being the base for all future paths we handle, assuming it to be valid which includes
    /// symbolic links to be included in it as well.
    /// The `case` configures attribute and exclusion query case sensitivity.
    pub fn new(worktree_root: impl Into<PathBuf>, mode: State, case: git_glob::pattern::Case, buf: Vec<u8>) -> Self {
        let root = worktree_root.into();
        Cache {
            stack: fs::Stack::new(root),
            state: mode,
            case,
            buf,
        }
    }

    /// Append the `relative` path to the root directory the cache contains and efficiently create leading directories
    /// unless `is_dir` is known (`Some(…)`) then `relative` points to a directory itself in which case the entire resulting
    /// path is created as directory. If it's not known it is assumed to be a file.
    ///
    /// Provide access to cached information for that `relative` entry via the platform returned.
    pub fn at_entry(&mut self, relative: impl AsRef<Path>, is_dir: Option<bool>) -> std::io::Result<Platform<'_>> {
        let mut platform = platform::StackDelegate {
            state: &mut self.state,
            buf: &mut self.buf,
            is_dir,
        };
        self.stack.make_relative_path_current(relative, &mut platform)?;
        Ok(Platform { parent: self, is_dir })
    }
}

mod platform;
///
pub mod state;
