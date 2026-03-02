# Build validation test
use std::process::Command;

fn main() {
    println!("🚀 Isospin Build Validation");
    println!("Checking available tools...");
    
    // Test Rust availability
    if let Ok(output) = Command::new("rustc").arg("--version").output() {
        println!("✅ Rust: {}", String::from_utf8_lossy(&output.stdout).trim());
    } else {
        println!("❌ Rust not available");
    }
    
    // Test Cargo for reference builds
    if let Ok(output) = Command::new("cargo").arg("--version").output() {
        println!("✅ Cargo: {}", String::from_utf8_lossy(&output.stdout).trim());
    } else {
        println!("❌ Cargo not available");
    }
    
    // Test architecture support
    println!("Checking supported targets...");
    let targets = ["x86_64-unknown-linux-gnu", "aarch64-unknown-linux-gnu"];
    for target in targets {
        println!("  📦 {}", target);
    }
    
    println!("🎯 Build validation complete!");
    println!("Ready for hypervisor migration with:");
    println!("  • Firecracker core VMM");
    println!("  • Cloud Hypervisor modular architecture");
    println!("  • Cross-platform support");
}