#!/usr/bin/env python3
"""Compare PO-5 TransitionKernel per-case refinement witnesses.

The Coq side emits witnesses from the CoqExtractedTransitionKernel oracle. The
Rust side emits witnesses from DeployedTransitionKernel. This comparator reports
semantic field-level diffs by case name instead of dumping opaque hash summaries
or entire JSON objects.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any


DEFAULT_COQ = "formal/coq/extraction/coq_transition_kernel_refinement.json"
DEFAULT_RUST = "rust_transition_kernel_refinement.json"
MAX_DIFFS = 200


def load_json(path: str) -> Any:
    with open(path, "r", encoding="utf-8") as handle:
        return json.load(handle)


def case_key(case: dict[str, Any]) -> str:
    return f"{case.get('kind', '<unknown>')}:{case.get('name', '<unnamed>')}"


def format_value(value: Any) -> str:
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def diff_values(path: str, coq: Any, rust: Any, diffs: list[str]) -> None:
    if len(diffs) >= MAX_DIFFS:
        return

    if type(coq) is not type(rust):
        diffs.append(
            f"{path}: type mismatch Coq={type(coq).__name__} Rust={type(rust).__name__}"
        )
        return

    if isinstance(coq, dict):
        keys = sorted(set(coq) | set(rust))
        for key in keys:
            if len(diffs) >= MAX_DIFFS:
                return
            child_path = f"{path}.{key}" if path else key
            if key not in coq:
                diffs.append(f"{child_path}: missing in Coq, Rust={format_value(rust[key])}")
            elif key not in rust:
                diffs.append(f"{child_path}: missing in Rust, Coq={format_value(coq[key])}")
            else:
                diff_values(child_path, coq[key], rust[key], diffs)
        return

    if isinstance(coq, list):
        if len(coq) != len(rust):
            diffs.append(f"{path}: length mismatch Coq={len(coq)} Rust={len(rust)}")
            return
        for index, (coq_item, rust_item) in enumerate(zip(coq, rust)):
            if len(diffs) >= MAX_DIFFS:
                return
            diff_values(f"{path}[{index}]", coq_item, rust_item, diffs)
        return

    if coq != rust:
        diffs.append(f"{path}: Coq={format_value(coq)} Rust={format_value(rust)}")


def build_case_map(label: str, cases: list[Any]) -> tuple[dict[str, dict[str, Any]], list[str]]:
    by_key: dict[str, dict[str, Any]] = {}
    diffs: list[str] = []

    for index, case in enumerate(cases):
        if not isinstance(case, dict):
            diffs.append(f"{label}[{index}]: expected object, found {type(case).__name__}")
            continue

        key = case_key(case)
        if key in by_key:
            diffs.append(f"{label}.{key}: duplicate case key at index {index}")
            continue

        by_key[key] = case

    return by_key, diffs


def compare_case_set(label: str, coq_cases: list[Any], rust_cases: list[Any]) -> list[str]:
    diffs: list[str] = []
    coq_by_key, coq_shape_diffs = build_case_map(f"{label}.Coq", coq_cases)
    rust_by_key, rust_shape_diffs = build_case_map(f"{label}.Rust", rust_cases)
    diffs.extend(coq_shape_diffs)
    diffs.extend(rust_shape_diffs)

    for key in sorted(set(coq_by_key) | set(rust_by_key)):
        if key not in coq_by_key:
            diffs.append(f"{label}.{key}: missing in Coq")
            continue
        if key not in rust_by_key:
            diffs.append(f"{label}.{key}: missing in Rust")
            continue
        diff_values(f"{label}.{key}", coq_by_key[key], rust_by_key[key], diffs)
        if len(diffs) >= MAX_DIFFS:
            break

    return diffs


def compare_witnesses(coq: dict[str, Any], rust: dict[str, Any]) -> list[str]:
    diffs: list[str] = []

    for key in sorted((set(coq) | set(rust)) - {"cases"}):
        if key not in coq:
            diffs.append(f"{key}: missing in Coq, Rust={format_value(rust[key])}")
        elif key not in rust:
            diffs.append(f"{key}: missing in Rust, Coq={format_value(coq[key])}")
        else:
            diff_values(key, coq[key], rust[key], diffs)

    coq_cases = coq.get("cases", {})
    rust_cases = rust.get("cases", {})
    if not isinstance(coq_cases, dict) or not isinstance(rust_cases, dict):
        diff_values("cases", coq_cases, rust_cases, diffs)
        return diffs

    diffs.extend(
        compare_case_set(
            "cases.transactions",
            coq_cases.get("transactions", []),
            rust_cases.get("transactions", []),
        )
    )
    diffs.extend(
        compare_case_set(
            "cases.blocks",
            coq_cases.get("blocks", []),
            rust_cases.get("blocks", []),
        )
    )
    return diffs[:MAX_DIFFS]


def case_count(value: dict[str, Any], group: str) -> int:
    return len(value.get("cases", {}).get(group, []))


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("coq", nargs="?", default=DEFAULT_COQ)
    parser.add_argument("rust", nargs="?", default=DEFAULT_RUST)
    args = parser.parse_args()

    coq_path = Path(args.coq)
    rust_path = Path(args.rust)
    coq = load_json(str(coq_path))
    rust = load_json(str(rust_path))

    diffs = compare_witnesses(coq, rust)
    if diffs:
        print("=== TRANSITION KERNEL REFINEMENT SEMANTIC DIFF ===")
        print(f"Coq witness:  {coq_path}")
        print(f"Rust witness: {rust_path}")
        for diff in diffs:
            print(f"- {diff}")
        if len(diffs) == MAX_DIFFS:
            print(f"- diff output truncated at {MAX_DIFFS} entries")
        return 1

    print("=== SUCCESS ===")
    print("TransitionKernel per-case structured witnesses match.")
    print(f"Transaction cases: {case_count(coq, 'transactions')}")
    print(f"Block cases: {case_count(coq, 'blocks')}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
