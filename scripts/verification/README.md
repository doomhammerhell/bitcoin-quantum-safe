# Verification Scripts

This directory contains executable verification entrypoints and semantic
comparators for the formal-methods pipeline.

The repository root is intentionally kept for project-level manifests,
documentation, and domain directories. New proof/refinement/release-certificate
automation should live here unless it is specific to a narrower subsystem.

## Entry Points

- `build_extraction.sh`: compiles Coq/Rocq modules, extracts OCaml artifacts,
  generates Coq and Rust summaries, and compares the extraction boundary.
- `verify_source_refinement.sh`: runs bounded Kani source-level harnesses.
- `verify_*_refinement.sh`: builds optimized Rust release examples, compares
  their output against Coq-extracted or independent reference summaries, and
  emits hash certificates under `target/`.
- `compare_*.py`: semantic comparators that report structured field-level
  differences for witness-rich refinement artifacts.

These scripts provide executable evidence and translation-validation artifacts.
They do not claim compiler, linker, CPU, operating-system, primitive
cryptographic, or FIPS implementation correctness.
