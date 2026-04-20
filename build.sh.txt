#!/bin/bash
set -e

INSTALL_DIR="${HOME}/.local"
CRYPTOL_VERSION="2.13.0"
SAW_VERSION="0.9.0"
LLVM_VERSION="17"

export PATH="${INSTALL_DIR}/bin:${PATH}"

check_dependencies() {
    local missing=()
    for cmd in curl tar gzip make gcc g++; do
        if ! command -v "$cmd" &> /dev/null; then
            missing+=("$cmd")
        fi
    done
    if [ ${#missing[@]} -gt 0 ]; then
        echo "Missing dependencies: ${missing[*]}"
        exit 1
    fi
}

install_llvm() {
    if command -v llvm-config-${LLVM_VERSION} &> /dev/null; then
        echo "LLVM ${LLVM_VERSION} already installed"
        return 0
    fi
    
    if command -v apt-get &> /dev/null; then
        sudo apt-get update
        sudo apt-get install -y llvm-${LLVM_VERSION} llvm-${LLVM_VERSION}-dev clang-${LLVM_VERSION} lld-${LLVM_VERSION}
    elif command -v dnf &> /dev/null; then
        sudo dnf install -y llvm${LLVM_VERSION} llvm${LLVM_VERSION}-devel clang${LLVM_VERSION} lld${LLVM_VERSION}
    elif command -v pacman &> /dev/null; then
        sudo pacman -S --noconfirm llvm clang lld
    elif command -v brew &> /dev/null; then
        brew install llvm@${LLVM_VERSION}
    else
        echo "Unsupported package manager. Please install LLVM ${LLVM_VERSION} manually."
        exit 1
    fi
}

install_cryptol() {
    local cryptol_bin="${INSTALL_DIR}/bin/cryptol"
    if [ -x "$cryptol_bin" ]; then
        echo "Cryptol already installed at $cryptol_bin"
        return 0
    fi
    
    mkdir -p "${INSTALL_DIR}/bin"
    mkdir -p /tmp/cryptol-install
    cd /tmp/cryptol-install
    
    local arch=$(uname -m)
    local platform=$(uname -s | tr '[:upper:]' '[:lower:]')
    
    local cryptol_url="https://github.com/GaloisInc/cryptol/releases/download/v${CRYPTOL_VERSION}/cryptol-${CRYPTOL_VERSION}-${arch}-${platform}.tar.gz"
    
    echo "Downloading Cryptol ${CRYPTOL_VERSION}..."
    curl -sL "$cryptol_url" -o cryptol.tar.gz || {
        cryptol_url="https://github.com/GaloisInc/cryptol/releases/download/v${CRYPTOL_VERSION}/cryptol-${CRYPTOL_VERSION}-${arch}-$(uname -s | tr '[:upper:]' '[:lower:]').tar.gz"
        curl -sL "$cryptol_url" -o cryptol.tar.gz
    }
    
    tar -xzf cryptol.tar.gz
    cd cryptol-${CRYPTOL_VERSION}-*
    
    cp -r bin/* "${INSTALL_DIR}/bin/" || cp cryptol "${INSTALL_DIR}/bin/"
    cp -r lib/* "${INSTALL_DIR}/lib/" 2>/dev/null || true
    cp -r share/* "${INSTALL_DIR}/share/" 2>/dev/null || true
    
    chmod +x "${INSTALL_DIR}/bin/cryptol" 2>/dev/null || true
    
    cd /
    rm -rf /tmp/cryptol-install
    
    echo "Cryptol installed successfully"
}

install_saw() {
    local saw_bin="${INSTALL_DIR}/bin/saw"
    if [ -x "$saw_bin" ]; then
        echo "SAW already installed at $saw_bin"
        return 0
    fi
    
    mkdir -p "${INSTALL_DIR}/bin"
    mkdir -p /tmp/saw-install
    cd /tmp/saw-install
    
    local arch=$(uname -m)
    local platform=$(uname -s | tr '[:upper:]' '[:lower:]')
    
    local saw_url="https://github.com/GaloisInc/saw-script/releases/download/v${SAW_VERSION}/saw-${SAW_VERSION}-${arch}-${platform}.tar.gz"
    
    echo "Downloading SAW ${SAW_VERSION}..."
    curl -sL "$saw_url" -o saw.tar.gz || {
        saw_url="https://github.com/GaloisInc/saw-script/releases/download/v${SAW_VERSION}/saw-${SAW_VERSION}-x86_64-${platform}.tar.gz"
        curl -sL "$saw_url" -o saw.tar.gz
    }
    
    tar -xzf saw.tar.gz
    cd $(find . -type d -name "saw-${SAW_VERSION}-*" | head -n 1)
    
    cp -r bin/* "${INSTALL_DIR}/bin/" || cp saw "${INSTALL_DIR}/bin/"
    cp -r lib/* "${INSTALL_DIR}/lib/" 2>/dev/null || true
    cp -r share/* "${INSTALL_DIR}/share/" 2>/dev/null || true
    
    chmod +x "${INSTALL_DIR}/bin/saw" 2>/dev/null || true
    chmod +x "${INSTALL_DIR}/bin/cryptol-saw" 2>/dev/null || true
    
    cd /
    rm -rf /tmp/saw-install
    
    echo "SAW installed successfully"
}

install_zig() {
    if command -v zig &> /dev/null; then
        echo "Zig already installed"
        return 0
    fi
    
    local zig_version="0.11.0"
    local arch=$(uname -m)
    local platform=$(uname -s | tr '[:upper:]' '[:lower:]')
    
    mkdir -p /tmp/zig-install
    cd /tmp/zig-install
    
    local zig_url="https://ziglang.org/download/${zig_version}/zig-${platform}-${arch}-${zig_version}.tar.xz"
    
    echo "Downloading Zig ${zig_version}..."
    curl -sL "$zig_url" -o zig.tar.xz
    tar -xf zig.tar.xz
    
    cp -r zig-${platform}-${arch}-${zig_version}/* "${INSTALL_DIR}/"
    
    cd /
    rm -rf /tmp/zig-install
    
    echo "Zig installed successfully"
}

install_z3() {
    if command -v z3 &> /dev/null; then
        echo "Z3 already installed"
        return 0
    fi
    
    if command -v apt-get &> /dev/null; then
        sudo apt-get install -y z3
    elif command -v dnf &> /dev/null; then
        sudo dnf install -y z3
    elif command -v pacman &> /dev/null; then
        sudo pacman -S --noconfirm z3
    elif command -v brew &> /dev/null; then
        brew install z3
    else
        local z3_version="4.12.2"
        local arch=$(uname -m)
        local platform=$(uname -s | tr '[:upper:]' '[:lower:]')
        
        mkdir -p /tmp/z3-install
        cd /tmp/z3-install
        
        local z3_url="https://github.com/Z3Prover/z3/releases/download/z3-${z3_version}/z3-${z3_version}-${arch}-${platform}.zip"
        
        echo "Downloading Z3 ${z3_version}..."
        curl -sL "$z3_url" -o z3.zip
        unzip -q z3.zip
        cd z3-*
        
        cp -r bin/* "${INSTALL_DIR}/bin/"
        
        cd /
        rm -rf /tmp/z3-install
    fi
    
    echo "Z3 installed successfully"
}

compile_zig_to_bitcode() {
    local source_file="${1:-main.zig}"
    local output_bc="${2:-main.bc}"
    local llvm_cmd=$(command -v llvm-config-${LLVM_VERSION} || command -v llvm-config)
    
    if [ ! -f "$source_file" ]; then
        echo "Source file not found: $source_file"
        exit 1
    fi
    
    echo "Compiling Zig to LLVM bitcode..."
    
    local opt_level="${ZIG_OPT_LEVEL:-ReleaseSmall}"
    local target="${ZIG_TARGET:-native}"
    
    zig build-obj \
        --name main \
        -femit-bin="${output_bc%.bc}.o" \
        -femit-llvm-bc="${output_bc}" \
        -target "${target}" \
        -O "${opt_level}" \
        -fPIC \
        "${source_file}" || {
        
        echo "Direct bitcode emission failed, generating IR..."
        
        zig build-obj \
            --name main \
            -femit-bin="${output_bc%.bc}.o" \
            -femit-llvm-ir="${output_bc%.bc}.ll" \
            -target "${target}" \
            -O "${opt_level}" \
            -fPIC \
            "${source_file}"
        
        local ll_file="${output_bc%.bc}.ll"
        if [ -f "$ll_file" ]; then
            llvm-as "$ll_file" -o "$output_bc" 2>/dev/null || \
            "${llvm_cmd%/bin/llvm-config}/bin/llvm-as" "$ll_file" -o "$output_bc" || true
        fi
    }
    
    if [ -f "$output_bc" ]; then
        echo "Successfully compiled to: $output_bc"
        ls -la "$output_bc"
    else
        echo "Warning: Bitcode file not created, using object file"
        if [ -f "${output_bc%.bc}.o" ]; then
            cp "${output_bc%.bc}.o" "$output_bc"
            echo "Using object file: $output_bc"
        fi
    fi
}

verify_environment() {
    echo "Verifying installation..."
    
    echo "=== Tool Versions ==="
    
    if command -v zig &> /dev/null; then
        echo "Zig: $(zig version)"
    else
        echo "Zig: NOT FOUND"
    fi
    
    if command -v cryptol &> /dev/null; then
        echo "Cryptol: $(cryptol --version 2>&1 | head -1)"
    else
        echo "Cryptol: NOT FOUND"
    fi
    
    if command -v saw &> /dev/null; then
        echo "SAW: $(saw --version 2>&1 | head -1)"
    else
        echo "SAW: NOT FOUND"
    fi
    
    if command -v z3 &> /dev/null; then
        echo "Z3: $(z3 --version 2>&1 | head -1)"
    else
        echo "Z3: NOT FOUND"
    fi
    
    if command -v llvm-config-${LLVM_VERSION} &> /dev/null; then
        echo "LLVM: $(llvm-config-${LLVM_VERSION} --version)"
    elif command -v llvm-config &> /dev/null; then
        echo "LLVM: $(llvm-config --version)"
    else
        echo "LLVM: NOT FOUND"
    fi
    
    echo "====================="
}

main() {
    local action="${1:-all}"
    local source_file="${2:-main.zig}"
    local output_file="${3:-main.bc}"
    
    case "$action" in
        "check")
            check_dependencies
            ;;
        "install-deps")
            check_dependencies
            install_llvm
            install_z3
            ;;
        "install-cryptol")
            install_cryptol
            ;;
        "install-saw")
            install_saw
            ;;
        "install-zig")
            install_zig
            ;;
        "install-all")
            check_dependencies
            install_llvm
            install_z3
            install_zig
            install_cryptol
            install_saw
            ;;
        "compile")
            compile_zig_to_bitcode "$source_file" "$output_file"
            ;;
        "verify")
            verify_environment
            ;;
        "all")
            check_dependencies
            install_llvm
            install_z3
            install_zig
            install_cryptol
            install_saw
            verify_environment
            compile_zig_to_bitcode "$source_file" "$output_file"
            ;;
        *)
            echo "Usage: $0 {check|install-deps|install-cryptol|install-saw|install-zig|install-all|compile|verify|all} [source.zig] [output.bc]"
            echo ""
            echo "Actions:"
            echo "  check           - Check for required dependencies"
            echo "  install-deps    - Install LLVM and Z3 dependencies"
            echo "  install-cryptol - Install Cryptol only"
            echo "  install-saw     - Install SAW only"
            echo "  install-zig     - Install Zig only"
            echo "  install-all     - Install all tools"
            echo "  compile         - Compile Zig source to LLVM bitcode"
            echo "  verify          - Verify installation"
            echo "  all             - Install everything and compile"
            exit 1
            ;;
    esac
}

main "$@"