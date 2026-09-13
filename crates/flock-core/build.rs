use std::fs;
use std::path::{Path, PathBuf};

use toml::Value;

fn main() {
    println!("cargo:rerun-if-changed=build.rs");
    let manifest_dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
    let config_dir = manifest_dir.join("configs/ligerito");
    let out_dir = PathBuf::from(std::env::var("OUT_DIR").unwrap());
    let out_path = out_dir.join("ligerito_configs.rs");

    let mut output = String::from(
        "#[cfg(not(feature = \"std\"))]\n\
         fn embedded_security_config_value(\n\
         \tm: usize,\n\
         \tprofile: LigeritoProfile,\n\
         ) -> Option<LigeritoSecurityConfig> {\n\
         \tmatch (m, profile) {\n",
    );

    for m in 22..=35usize {
        for profile in ["fast", "slim", "secure"] {
            let path = config_dir.join(format!("m{m}_{profile}.toml"));
            println!("cargo:rerun-if-changed={}", path.display());
            let source = fs::read_to_string(&path).unwrap_or_else(|e| {
                panic!("read {}: {e}", path.display());
            });
            let value = source.parse::<Value>().unwrap_or_else(|e| {
                panic!("parse {}: {e}", path.display());
            });
            output.push_str(&emit_config_arm(m, profile, &value, &path));
        }
    }

    output.push_str("\t\t_ => None,\n\t}\n}\n");
    fs::write(&out_path, output).unwrap_or_else(|e| {
        panic!("write {}: {e}", out_path.display());
    });
}

fn emit_config_arm(m: usize, profile: &str, value: &Value, path: &Path) -> String {
    let table = value
        .as_table()
        .unwrap_or_else(|| panic!("{}: expected root table", path.display()));
    let levels = table
        .get("levels")
        .and_then(Value::as_array)
        .unwrap_or_else(|| panic!("{}: expected levels array", path.display()));
    let final_block = table
        .get("final_block")
        .and_then(Value::as_table)
        .unwrap_or_else(|| panic!("{}: expected final_block table", path.display()));

    let mut out = format!(
        "\t\t({m}, LigeritoProfile::{}) => Some(LigeritoSecurityConfig {{\n\
         \t\t\tm: {},\n\
         \t\t\tlog_n: {},\n\
         \t\t\tinitial_k: {},\n\
         \t\t\ttarget_security_bits: {},\n\
         \t\t\tanalysis: String::from({:?}),\n\
         \t\t\tfield: String::from({:?}),\n\
         \t\t\thash: String::from({:?}),\n\
         \t\t\tgrinding_step: {},\n\
         \t\t\tlevels: vec![\n",
        profile_variant(profile),
        usize_field(table, "m", path),
        usize_field(table, "log_n", path),
        usize_field(table, "initial_k", path),
        usize_field(table, "target_security_bits", path),
        string_field(table, "analysis", path),
        string_field(table, "field", path),
        string_field(table, "hash", path),
        grinding_step_expr(string_field(table, "grinding_step", path), path),
    );

    for level in levels {
        let level = level
            .as_table()
            .unwrap_or_else(|| panic!("{}: expected level table", path.display()));
        out.push_str(&format!(
            "\t\t\t\tLigeritoLevelConfig {{\n\
             \t\t\t\t\tlog_inv_rate: {},\n\
             \t\t\t\t\tlog_msg_cols: {},\n\
             \t\t\t\t\tlog_num_interleaved: {},\n\
             \t\t\t\t\tk_recursive: {},\n\
             \t\t\t\t\tregime: {},\n\
             \t\t\t\t\teta: {},\n\
             \t\t\t\t\tproximity_loss: {},\n\
             \t\t\t\t\tqueries: {},\n\
             \t\t\t\t\tgrinding_bits: {},\n\
             \t\t\t\t\tfold_grinding_bits: {},\n\
             \t\t\t\t\tood_samples: {},\n\
             \t\t\t\t\ttarget_security_bits: {},\n\
             \t\t\t\t\texpected_eps_pg_bits: {:?},\n\
             \t\t\t\t\texpected_eps_query_bits: {:?},\n\
             \t\t\t\t\texpected_eps_ood_bits: {},\n\
             \t\t\t\t}},\n",
            usize_field(level, "log_inv_rate", path),
            usize_field(level, "log_msg_cols", path),
            usize_field(level, "log_num_interleaved", path),
            usize_field(level, "k_recursive", path),
            regime_expr(string_field(level, "regime", path), path),
            opt_f64_field(level, "eta"),
            opt_f64_field(level, "proximity_loss"),
            usize_field(level, "queries", path),
            usize_field(level, "grinding_bits", path),
            usize_field(level, "fold_grinding_bits", path),
            usize_field(level, "ood_samples", path),
            usize_field(level, "target_security_bits", path),
            f64_field(level, "expected_eps_pg_bits", path),
            f64_field(level, "expected_eps_query_bits", path),
            opt_f64_field(level, "expected_eps_ood_bits"),
        ));
    }

    out.push_str(&format!(
        "\t\t\t],\n\
         \t\t\tfinal_block: FinalBlockConfig {{ yr_log_n: {} }},\n\
         \t\t}}),\n",
        usize_field(final_block, "yr_log_n", path),
    ));
    out
}

fn profile_variant(profile: &str) -> &'static str {
    match profile {
        "fast" => "Fast",
        "slim" => "Slim",
        "secure" => "Secure",
        _ => panic!("unknown profile {profile}"),
    }
}

fn grinding_step_expr(value: &str, path: &Path) -> &'static str {
    match value {
        "post_commit_pre_queries" => "GrindingStep::PostCommitPreQueries",
        _ => panic!("{}: unknown grinding_step {value}", path.display()),
    }
}

fn regime_expr(value: &str, path: &Path) -> &'static str {
    match value {
        "udr" => "SoundnessRegime::Udr",
        "johnson_ood" => "SoundnessRegime::JohnsonOod",
        _ => panic!("{}: unknown regime {value}", path.display()),
    }
}

fn string_field<'a>(table: &'a toml::map::Map<String, Value>, key: &str, path: &Path) -> &'a str {
    table
        .get(key)
        .and_then(Value::as_str)
        .unwrap_or_else(|| panic!("{}: missing string field {key}", path.display()))
}

fn usize_field(table: &toml::map::Map<String, Value>, key: &str, path: &Path) -> usize {
    let value = table
        .get(key)
        .and_then(Value::as_integer)
        .unwrap_or_else(|| panic!("{}: missing integer field {key}", path.display()));
    usize::try_from(value)
        .unwrap_or_else(|_| panic!("{}: invalid usize field {key}", path.display()))
}

fn f64_field(table: &toml::map::Map<String, Value>, key: &str, path: &Path) -> f64 {
    number_field(table, key)
        .unwrap_or_else(|| panic!("{}: missing numeric field {key}", path.display()))
}

fn opt_f64_field(table: &toml::map::Map<String, Value>, key: &str) -> String {
    match number_field(table, key) {
        Some(value) => format!("Some({value:?})"),
        None => "None".to_owned(),
    }
}

fn number_field(table: &toml::map::Map<String, Value>, key: &str) -> Option<f64> {
    match table.get(key) {
        Some(Value::Float(value)) => Some(*value),
        Some(Value::Integer(value)) => Some(*value as f64),
        _ => None,
    }
}
