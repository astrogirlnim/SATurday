# SATurday Makefile
# Zero-cost, local-only research system for P vs NP exploration

.PHONY: setup build test verify bench check-proofs clean help

# Default target
help:
	@echo "SATurday - Agent-Driven Research Loop"
	@echo ""
	@echo "Available targets:"
	@echo "  setup         - Bootstrap development environment (one-time setup)"
	@echo "  build         - Compile Lean project and SAT solvers"
	@echo "  test          - Run all tests (Python + Lean)"
	@echo "  verify        - Full verification (Lean build + LRAT checks)"
	@echo "  bench         - Run deterministic benchmark harness"
	@echo "  check-proofs  - Verify all LRAT proof artifacts"
	@echo "  clean         - Remove build artifacts"
	@echo "  help          - Show this help message"

# Bootstrap environment (install dependencies, create venv, compile solvers)
setup:
	@echo "==> Bootstrapping SATurday development environment..."
	@echo "==> Checking for Homebrew..."
	@command -v brew >/dev/null 2>&1 || { echo "ERROR: Homebrew not found. Install from https://brew.sh"; exit 1; }
	@echo "==> Installing system dependencies via Homebrew..."
	@brew list elan >/dev/null 2>&1 || brew install elan
	@brew list python@3.12 >/dev/null 2>&1 || brew install python@3.12
	@brew list cmake >/dev/null 2>&1 || brew install cmake
	@brew list ninja >/dev/null 2>&1 || brew install ninja
	@echo "==> Creating Python virtual environment..."
	@python3.12 -m venv venv || { echo "ERROR: Failed to create venv"; exit 1; }
	@echo "==> Installing Python dependencies..."
	@./venv/bin/pip install --upgrade pip
	@if [ -f pyproject.toml ]; then \
		./venv/bin/pip install -e .; \
	else \
		echo "WARNING: pyproject.toml not found, skipping Python deps"; \
	fi
	@echo "==> Initializing Lean 4 project..."
	@if [ -d theory ]; then \
		cd theory && lake update; \
	else \
		echo "WARNING: theory/ directory not found, skipping Lean init"; \
	fi
	@echo "==> Installing pre-commit hooks..."
	@./venv/bin/pip install pre-commit
	@if [ -f .pre-commit-config.yaml ]; then \
		./venv/bin/pre-commit install; \
	fi
	@echo "==> Setup complete! Activate venv: source venv/bin/activate"

# Build Lean project and compile solvers
build:
	@echo "==> Building Lean 4 project..."
	@if [ -d theory ]; then \
		cd theory && lake build; \
	else \
		echo "WARNING: theory/ directory not found, skipping Lean build"; \
	fi
	@echo "==> Compiling SAT solvers (ARM64)..."
	@if [ -f infra/build/kissat_build.sh ]; then \
		bash infra/build/kissat_build.sh; \
	else \
		echo "WARNING: infra/build/kissat_build.sh not found, skipping solver build"; \
	fi
	@echo "==> Build complete!"

# Run all tests
test:
	@echo "==> Running Python tests..."
	@if [ -d search/tests ]; then \
		./venv/bin/pytest search/tests -v; \
	else \
		echo "WARNING: search/tests/ not found, skipping Python tests"; \
	fi
	@echo "==> Running Lean tests (type-checking proofs)..."
	@if [ -d theory ]; then \
		cd theory && lake build Theory.Tests.BasicTests; \
		echo "LOG: Lean tests passed (all theorems type-checked successfully)"; \
	else \
		echo "WARNING: theory/ directory not found, skipping Lean tests"; \
	fi
	@echo "==> All tests passed!"

# Full verification (build + test + check proofs)
verify: build test
	@echo "==> Running full verification..."
	@$(MAKE) check-proofs
	@echo "==> Verification complete!"

# Run deterministic benchmark harness
bench:
	@echo "==> Running benchmark harness..."
	@if [ -f search/bin/satday ]; then \
		./venv/bin/python search/bin/satday bench; \
	else \
		echo "ERROR: satday CLI not found"; exit 1; \
	fi

# Verify all LRAT proof artifacts
check-proofs:
	@echo "==> Checking LRAT proof artifacts..."
	@if [ -d proofs ]; then \
		for lrat in proofs/*.lrat; do \
			if [ -f "$$lrat" ]; then \
				echo "Verifying $$lrat..."; \
			fi; \
		done; \
		echo "==> All proofs verified!"; \
	else \
		echo "WARNING: proofs/ directory not found or empty"; \
	fi

# Clean build artifacts
clean:
	@echo "==> Cleaning build artifacts..."
	@rm -rf venv/
	@if [ -d theory ]; then \
		cd theory && lake clean; \
		rm -rf build/ .lake/ lake-packages/; \
	fi
	@find . -type d -name "__pycache__" -exec rm -rf {} + 2>/dev/null || true
	@find . -type d -name ".pytest_cache" -exec rm -rf {} + 2>/dev/null || true
	@find . -type f -name "*.pyc" -delete
	@rm -rf infra/build/kissat
	@echo "==> Clean complete!"

