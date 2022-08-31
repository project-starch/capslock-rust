use colored::*;
use regex::Regex;
use std::path::{Path, PathBuf};
use std::{env, process::Command};
use ui_test::{color_eyre::Result, Config, DependencyBuilder, Mode, OutputConflictHandling};

fn miri_path() -> PathBuf {
    PathBuf::from(option_env!("MIRI").unwrap_or(env!("CARGO_BIN_EXE_miri")))
}

// Build the shared object file for testing external C function calls.
fn build_so_for_c_ffi_tests() -> PathBuf {
    let cc = option_env!("CC").unwrap_or("cc");
    // Target directory that we can write to.
    let so_target_dir = Path::new(&env::var_os("CARGO_TARGET_DIR").unwrap()).join("miri-extern-so");
    // Create the directory if it does not already exist.
    std::fs::create_dir_all(&so_target_dir)
        .expect("Failed to create directory for shared object file");
    let so_file_path = so_target_dir.join("libtestlib.so");
    let cc_output = Command::new(cc)
        .args([
            "-shared",
            "-o",
            so_file_path.to_str().unwrap(),
            "tests/extern-so/test.c",
            // Only add the functions specified in libcode.version to the shared object file.
            // This is to avoid automatically adding `malloc`, etc.
            // Source: https://anadoxin.org/blog/control-over-symbol-exports-in-gcc.html/
            "-fPIC",
            "-Wl,--version-script=tests/extern-so/libcode.version",
        ])
        .output()
        .expect("failed to generate shared object file for testing external C function calls");
    if !cc_output.status.success() {
        panic!("error in generating shared object file for testing external C function calls");
    }
    so_file_path
}

fn run_tests(
    mode: Mode,
    path: &str,
    target: Option<String>,
    with_dependencies: bool,
) -> Result<()> {
    let mut config = Config {
        target,
        stderr_filters: STDERR.clone(),
        stdout_filters: STDOUT.clone(),
        root_dir: PathBuf::from(path),
        mode,
        program: miri_path(),
        quiet: false,
        ..Config::default()
    };

    let in_rustc_test_suite = option_env!("RUSTC_STAGE").is_some();

    // Add some flags we always want.
    config.args.push("--edition".into());
    config.args.push("2018".into());
    if in_rustc_test_suite {
        // Less aggressive warnings to make the rustc toolstate management less painful.
        // (We often get warnings when e.g. a feature gets stabilized or some lint gets added/improved.)
        config.args.push("-Astable-features".into());
        config.args.push("-Aunused".into());
    } else {
        config.args.push("-Dwarnings".into());
        config.args.push("-Dunused".into());
    }
    if let Ok(extra_flags) = env::var("MIRIFLAGS") {
        for flag in extra_flags.split_whitespace() {
            config.args.push(flag.into());
        }
    }
    config.args.push("-Zui-testing".into());
    if let Some(target) = &config.target {
        config.args.push("--target".into());
        config.args.push(target.into());
    }

    // If we're on linux, and we're testing the extern-so functionality,
    // then build the shared object file for testing external C function calls
    // and push the relevant compiler flag.
    if cfg!(target_os = "linux") && path.starts_with("tests/extern-so/") {
        let so_file_path = build_so_for_c_ffi_tests();
        let mut flag = std::ffi::OsString::from("-Zmiri-extern-so-file=");
        flag.push(so_file_path.into_os_string());
        config.args.push(flag);
    }

    let skip_ui_checks = env::var_os("MIRI_SKIP_UI_CHECKS").is_some();

    config.output_conflict_handling = match (env::var_os("MIRI_BLESS").is_some(), skip_ui_checks) {
        (false, false) => OutputConflictHandling::Error,
        (true, false) => OutputConflictHandling::Bless,
        (false, true) => OutputConflictHandling::Ignore,
        (true, true) => panic!("cannot use MIRI_BLESS and MIRI_SKIP_UI_CHECKS at the same time"),
    };

    // Handle command-line arguments.
    config.path_filter.extend(std::env::args().skip(1).filter(|arg| {
        match &**arg {
            "--quiet" => {
                config.quiet = true;
                false
            }
            _ => true,
        }
    }));

    let use_std = env::var_os("MIRI_NO_STD").is_none();

    if with_dependencies && use_std {
        config.dependencies_crate_manifest_path =
            Some(Path::new("test_dependencies").join("Cargo.toml"));
        config.dependency_builder = Some(DependencyBuilder {
            program: std::env::var_os("CARGO").unwrap().into(),
            args: vec![
                "run".into(),
                "--manifest-path".into(),
                "cargo-miri/Cargo.toml".into(),
                "--".into(),
                "miri".into(),
            ],
            envs: vec![],
        });
    }
    ui_test::run_tests(config)
}

macro_rules! regexes {
    ($name:ident: $($regex:expr => $replacement:expr,)*) => {lazy_static::lazy_static! {
        static ref $name: Vec<(Regex, &'static str)> = vec![
            $((Regex::new($regex).unwrap(), $replacement),)*
        ];
    }};
}

regexes! {
    STDOUT:
    // Windows file paths
    r"\\"                           => "/",
}

regexes! {
    STDERR:
    // erase line and column info
    r"\.rs:[0-9]+:[0-9]+(: [0-9]+:[0-9]+)?" => ".rs:LL:CC",
    // erase alloc ids
    "alloc[0-9]+"                    => "ALLOC",
    // erase Stacked Borrows tags
    "<[0-9]+>"                       => "<TAG>",
    // erase whitespace that differs between platforms
    r" +at (.*\.rs)"                 => " at $1",
    // erase generics in backtraces
    "([0-9]+: .*)::<.*>"             => "$1",
    // erase addresses in backtraces
    "([0-9]+: ) +0x[0-9a-f]+ - (.*)" => "$1$2",
    // erase long hexadecimals
    r"0x[0-9a-fA-F]+[0-9a-fA-F]{2,2}" => "$$HEX",
    // erase specific alignments
    "alignment [0-9]+"               => "alignment ALIGN",
    // erase thread caller ids
    r"call [0-9]+"                  => "call ID",
    // erase platform module paths
    "sys::[a-z]+::"                  => "sys::PLATFORM::",
    // Windows file paths
    r"\\"                           => "/",
    // erase Rust stdlib path
    "[^ `]*/(rust[^/]*|checkout)/library/" => "RUSTLIB/",
    // erase platform file paths
    "sys/[a-z]+/"                    => "sys/PLATFORM/",
    // erase paths into the crate registry
    r"[^ ]*/\.?cargo/registry/.*/(.*\.rs)"  => "CARGO_REGISTRY/.../$1",
}

enum Dependencies {
    WithDependencies,
    WithoutDependencies,
}

use Dependencies::*;

fn ui(mode: Mode, path: &str, with_dependencies: Dependencies) -> Result<()> {
    let target = get_target();

    let msg = format!(
        "## Running ui tests in {path} against miri for {}",
        target.as_deref().unwrap_or("host")
    );
    eprintln!("{}", msg.green().bold());

    let with_dependencies = match with_dependencies {
        WithDependencies => true,
        WithoutDependencies => false,
    };
    run_tests(mode, path, target, with_dependencies)
}

fn get_target() -> Option<String> {
    env::var("MIRI_TEST_TARGET").ok()
}

fn main() -> Result<()> {
    ui_test::color_eyre::install()?;

    // Add a test env var to do environment communication tests.
    env::set_var("MIRI_ENV_VAR_TEST", "0");
    // Let the tests know where to store temp files (they might run for a different target, which can make this hard to find).
    env::set_var("MIRI_TEMP", env::temp_dir());

    ui(Mode::Pass, "tests/pass", WithoutDependencies)?;
    ui(Mode::Pass, "tests/pass-dep", WithDependencies)?;
    ui(Mode::Panic, "tests/panic", WithDependencies)?;
    ui(Mode::Fail { require_patterns: true }, "tests/fail", WithDependencies)?;
    if cfg!(target_os = "linux") {
        ui(Mode::Pass, "tests/extern-so/pass", WithoutDependencies)?;
        ui(Mode::Fail { require_patterns: true }, "tests/extern-so/fail", WithDependencies)?;
    }

    Ok(())
}
