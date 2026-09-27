#!/usr/bin/env python3
"""Audit CI workflow coverage for formal verification entrypoints.

This is intentionally dependency-free: CI must be able to run it before any
project-specific setup. The audit checks for structural workflow regressions
that can silently skip proof/refinement jobs when shared verification helpers
change.
"""

from __future__ import annotations

import re
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
PO8_WORKFLOW = ROOT / ".github" / "workflows" / "po8-verification.yml"
CI_WORKFLOW = ROOT / ".github" / "workflows" / "ci.yml"

REQUIRED_TRIGGER_PATHS = [
    "formal/coq/**",
    "src/**",
    "tests/**",
    "scripts/verification/**",
    ".github/workflows/po8-verification.yml",
    "Cargo.toml",
]

REQUIRED_JOBS = [
    "extract-coq",
    "generate-rust-vectors",
    "compare-vectors",
    "verify-coq-proofs",
    "verify-rust-source-refinement",
    "verify-compiled-refinement",
    "verify-sighash-refinement",
    "verify-txid-refinement",
    "verify-transition-refinement",
    "verify-transition-kernel-refinement",
    "verify-transition-invariant-refinement",
    "verify-runtime-refinement",
    "verify-pq-profile-refinement",
    "run-benchmarks",
    "verification-summary",
]

REQUIRED_SUMMARY_NEEDS = [
    "compare-vectors",
    "verify-coq-proofs",
    "verify-rust-source-refinement",
    "verify-compiled-refinement",
    "verify-sighash-refinement",
    "verify-txid-refinement",
    "verify-transition-refinement",
    "verify-transition-kernel-refinement",
    "verify-transition-invariant-refinement",
    "verify-runtime-refinement",
    "verify-pq-profile-refinement",
    "run-benchmarks",
]

REQUIRED_VERIFICATION_ENTRYPOINTS = [
    "scripts/verification/build_extraction.sh",
    "scripts/verification/verify_source_refinement.sh",
    "scripts/verification/verify_compiled_refinement.sh",
    "scripts/verification/verify_sighash_refinement.sh",
    "scripts/verification/verify_txid_refinement.sh",
    "scripts/verification/verify_transition_refinement.sh",
    "scripts/verification/verify_transition_kernel_refinement.sh",
    "scripts/verification/verify_transition_invariant_refinement.sh",
    "scripts/verification/verify_runtime_refinement.sh",
    "scripts/verification/verify_pq_profile_refinement.sh",
]

REQUIRED_COMPARATORS = [
    "scripts/verification/compare_transition_kernel_refinement.py",
    "scripts/verification/compare_transition_invariant_refinement.py",
]


def fail(message: str) -> None:
    print(f"workflow audit failure: {message}", file=sys.stderr)
    sys.exit(1)


def load(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except FileNotFoundError:
        fail(f"missing required workflow file: {path.relative_to(ROOT)}")


def job_ids(workflow_text: str) -> set[str]:
    in_jobs = False
    jobs: set[str] = set()
    for line in workflow_text.splitlines():
        if line == "jobs:":
            in_jobs = True
            continue
        if not in_jobs:
            continue
        match = re.match(r"^  ([A-Za-z0-9_-]+):\s*$", line)
        if match:
            jobs.add(match.group(1))
    return jobs


def quoted_path_count(workflow_text: str, path: str) -> int:
    return workflow_text.count(f'- "{path}"') + workflow_text.count(f"- '{path}'")


def job_needs(workflow_text: str, job_id: str) -> set[str]:
    lines = workflow_text.splitlines()
    in_job = False
    needs: set[str] = set()
    for line in lines:
        if line == f"  {job_id}:":
            in_job = True
            continue
        if in_job and re.match(r"^  [A-Za-z0-9_-]+:\s*$", line):
            break
        if not in_job:
            continue

        stripped = line.strip()
        if stripped.startswith("needs: [") and stripped.endswith("]"):
            inline = stripped.removeprefix("needs: [").removesuffix("]")
            return {item.strip() for item in inline.split(",") if item.strip()}
        if stripped.startswith("- "):
            needs.add(stripped.removeprefix("- ").strip())

    return needs


def main() -> None:
    po8 = load(PO8_WORKFLOW)
    ci = load(CI_WORKFLOW)

    for trigger_path in REQUIRED_TRIGGER_PATHS:
        count = quoted_path_count(po8, trigger_path)
        if count != 2:
            fail(
                f"{trigger_path!r} must appear exactly once in both push.paths "
                f"and pull_request.paths; found {count}"
            )

    present_jobs = job_ids(po8)
    missing_jobs = [job for job in REQUIRED_JOBS if job not in present_jobs]
    if missing_jobs:
        fail(f"PO verification workflow is missing jobs: {', '.join(missing_jobs)}")

    compare_needs = job_needs(po8, "compare-vectors")
    missing_compare_needs = [
        job for job in ["extract-coq", "generate-rust-vectors"] if job not in compare_needs
    ]
    if missing_compare_needs:
        fail("compare-vectors no longer depends on: " + ", ".join(missing_compare_needs))

    summary_needs = job_needs(po8, "verification-summary")
    missing_needs = [job for job in REQUIRED_SUMMARY_NEEDS if job not in summary_needs]
    if missing_needs:
        fail(
            "verification-summary no longer depends on all critical jobs: "
            + ", ".join(missing_needs)
        )

    for entrypoint in REQUIRED_VERIFICATION_ENTRYPOINTS + REQUIRED_COMPARATORS:
        if not (ROOT / entrypoint).is_file():
            fail(f"missing verification entrypoint: {entrypoint}")
        if entrypoint not in po8:
            fail(f"PO verification workflow does not reference {entrypoint}")

    if "scripts/verification/audit_workflows.py" not in ci:
        fail("main CI workflow must run scripts/verification/audit_workflows.py")

    print("Workflow audit passed: formal verification triggers and jobs are covered.")


if __name__ == "__main__":
    main()
