#!/usr/bin/env python3
"""Run Mathlib's style linter over every Lean source module in this project."""

from pathlib import Path
import subprocess
import sys


LEAN_ROOT = Path(__file__).resolve().parents[1]
SOURCE_ROOTS = (
    "Algebra",
    "Analysis",
    "Combinatorics",
    "LinearAlgebra",
    "MeasureTheory",
    "Order",
    "Probability",
    "Topology",
)


def project_modules() -> list[str]:
    return sorted(
        ".".join(path.relative_to(LEAN_ROOT).with_suffix("").parts)
        for root in SOURCE_ROOTS
        for path in (LEAN_ROOT / root).rglob("*.lean")
    )


def main() -> int:
    modules = project_modules()
    if not modules:
        print("no project Lean modules found", file=sys.stderr)
        return 1
    print(f"Running Mathlib lint-style on {len(modules)} project modules.")
    return subprocess.run(
        ["lake", "exe", "lint-style", *modules], cwd=LEAN_ROOT, check=False
    ).returncode


if __name__ == "__main__":
    raise SystemExit(main())
