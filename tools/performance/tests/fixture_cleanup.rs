#![cfg(unix)]

mod common;

use common::Temporary;
use flock_performance::Result;
use std::fs;
use std::os::unix::fs::{PermissionsExt, symlink};

#[test]
fn sealed_cleanup_does_not_follow_links_to_outside_data() -> Result<()> {
    let outside = Temporary::new("flock cleanup outside")?;
    let data = outside.join("retained data");
    fs::write(&data, b"outside bytes")?;
    fs::set_permissions(&data, fs::Permissions::from_mode(0o400))?;
    let root = Temporary::new("flock cleanup sealed")?;
    symlink(outside.path(), root.join("directory link"))?;
    symlink(&data, root.join("file link"))?;
    fs::hard_link(&data, root.join("hard link"))?;
    fs::set_permissions(root.path(), fs::Permissions::from_mode(0o555))?;
    let removed = root.path().to_owned();
    drop(root);
    assert!(!removed.exists());
    assert_eq!(fs::read(&data)?, b"outside bytes");
    assert_eq!(fs::metadata(&data)?.permissions().mode() & 0o777, 0o400);
    assert!(outside.is_dir());
    Ok(())
}
