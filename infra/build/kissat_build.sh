#!/usr/bin/env bash
# Build script for Kissat SAT solver on ARM64 (M4 MacBook)
# Compiles Kissat from source with LRAT proof logging support

set -euo pipefail

# Configuration
KISSAT_VERSION="rel-3.1.1"  # Pinned version for reproducibility
KISSAT_REPO="https://github.com/arminbiere/kissat.git"
BUILD_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
KISSAT_SRC_DIR="${BUILD_DIR}/kissat-src"
KISSAT_BIN="${BUILD_DIR}/kissat"

# Logging helper
log() {
    echo "[KISSAT BUILD] $*" >&2
}

# Check if already built
if [[ -f "${KISSAT_BIN}" ]]; then
    log "Kissat binary already exists at ${KISSAT_BIN}"
    log "To rebuild, remove ${KISSAT_BIN} and run again"
    exit 0
fi

# Check for required tools
log "Checking build dependencies..."
if ! command -v git &> /dev/null; then
    log "ERROR: git not found. Install with: brew install git"
    exit 1
fi

if ! command -v make &> /dev/null; then
    log "ERROR: make not found. Install Xcode Command Line Tools"
    exit 1
fi

if ! command -v cc &> /dev/null; then
    log "ERROR: C compiler not found. Install Xcode Command Line Tools"
    exit 1
fi

# Clone Kissat repository
log "Cloning Kissat ${KISSAT_VERSION}..."
if [[ -d "${KISSAT_SRC_DIR}" ]]; then
    log "Source directory exists, removing..."
    rm -rf "${KISSAT_SRC_DIR}"
fi

git clone --depth 1 --branch "${KISSAT_VERSION}" "${KISSAT_REPO}" "${KISSAT_SRC_DIR}"

# Build Kissat
log "Building Kissat for ARM64..."
cd "${KISSAT_SRC_DIR}"

# Configure with optimizations for ARM64
# --quiet: suppress verbose output
# CFLAGS: optimize for M4 (ARM64)
log "Running configure..."
./configure --quiet

# Compile
log "Compiling..."
make -j$(sysctl -n hw.ncpu)

# Verify binary
if [[ ! -f "build/kissat" ]]; then
    log "ERROR: Kissat binary not found after build"
    exit 1
fi

# Copy binary to infra/build/
log "Installing binary to ${KISSAT_BIN}..."
cp build/kissat "${KISSAT_BIN}"
chmod +x "${KISSAT_BIN}"

# Verify it works
log "Testing binary..."
if ! "${KISSAT_BIN}" --version &> /dev/null; then
    log "ERROR: Kissat binary is not executable"
    exit 1
fi

# Get version info
VERSION_INFO=$("${KISSAT_BIN}" --version 2>&1 | head -n 1)
log "Successfully built: ${VERSION_INFO}"

# Clean up source directory (save space)
log "Cleaning up source directory..."
cd "${BUILD_DIR}"
rm -rf "${KISSAT_SRC_DIR}"

log "Build complete!"
log "Binary location: ${KISSAT_BIN}"
log "LRAT proof output: Use --lrat flag when running solver"

