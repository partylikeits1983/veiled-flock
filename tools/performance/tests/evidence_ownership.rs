mod common;

use common::Temporary;
use flock_performance::Result;
use flock_performance::evidence::{self, WriterLock};
use serde_json::json;
use std::fs;
use std::os::unix::fs::symlink;

#[test]
fn inventory_checks_content_membership_and_rejects_symlinks() -> Result<()> {
    let temp = Temporary::new("evidence-inventory")?;
    fs::write(temp.join("payload"), "original")?;
    let inventory = evidence::write_inventory(temp.path(), &["artifacts.json"])?;
    evidence::verify_inventory(temp.path(), &inventory)?;
    fs::write(temp.join("extra"), "new")?;
    assert!(evidence::verify_inventory(temp.path(), &inventory).is_err());
    fs::remove_file(temp.join("extra"))?;
    symlink("payload", temp.join("link"))?;
    assert!(evidence::inventory(temp.path(), &["artifacts.json"]).is_err());
    Ok(())
}

#[test]
fn writer_lock_rejects_active_and_unverified_owners_and_reclaims_dead_owner() -> Result<()> {
    let temp = Temporary::new("writer-lock")?;
    let lock = WriterLock::acquire(temp.path())?;
    assert!(WriterLock::acquire(temp.path()).is_err());
    drop(lock);
    drop(WriterLock::acquire(temp.path())?);
    fs::write(temp.join(".writer-lock"), b"invalid owner")?;
    assert!(WriterLock::acquire(temp.path()).is_err());
    fs::write(
        temp.join(".writer-lock"),
        serde_json::to_vec(
            &json!({"schema_version":1,"process_id":2147483647_u32,"process_start":"dead fixture","nonce":"dead-fixture","released":false}),
        )?,
    )?;
    drop(WriterLock::acquire(temp.path())?);
    assert!(
        temp.join(".writer-lock-history/2147483647-dead-fixture.json")
            .is_file()
    );
    Ok(())
}
