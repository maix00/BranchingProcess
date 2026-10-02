#!/usr/bin/env python3
"""Require an exact, reviewed axiom set from Lean `#print axioms` output."""

import argparse
from pathlib import Path
import re
import sys


ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AXIOM_LINE = re.compile(r"depends on axioms:\s*\[([^\]]*)\]", re.DOTALL)


def parse_axiom_sets(output: str) -> list[set[str]]:
    return [
        {item.strip() for item in match.group(1).replace("\n", " ").split(",") if item.strip()}
        for match in AXIOM_LINE.finditer(output)
    ]


def check_output(output: str, expected_count: int) -> list[str]:
    found = parse_axiom_sets(output)
    issues: list[str] = []
    if "sorryAx" in output:
        issues.append("unexpected sorryAx in declaration dependencies")
    if len(found) != expected_count:
        issues.append(f"expected {expected_count} axiom reports, found {len(found)}")
    for index, axioms in enumerate(found, start=1):
        if axioms != ALLOWED_AXIOMS:
            issues.append(
                f"axiom report {index} differs from allowlist: "
                f"found {sorted(axioms)}, expected {sorted(ALLOWED_AXIOMS)}"
            )
    return issues


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    parser.add_argument("--expected-count", type=int, required=True)
    args = parser.parse_args()
    issues = check_output(args.output.read_text(), args.expected_count)
    if issues:
        for issue in issues:
            print(issue, file=sys.stderr)
        return 1
    print(f"{args.expected_count} declarations use only the reviewed axiom allowlist.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
