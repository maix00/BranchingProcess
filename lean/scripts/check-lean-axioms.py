#!/usr/bin/env python3
"""Check named Lean declarations against the reviewed axiom allowlist."""

import argparse
from pathlib import Path
import re
import sys


ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
AXIOM_REPORT = re.compile(
    r"(?m)^'([^']+)' depends on axioms:\s*\[([^\]]*)\]", re.DOTALL
)


def parse_axiom_reports(output: str) -> list[tuple[str, set[str]]]:
    return [
        (
            match.group(1),
            {
                item.strip()
                for item in match.group(2).replace("\n", " ").split(",")
                if item.strip()
            },
        )
        for match in AXIOM_REPORT.finditer(output)
    ]


def check_output(output: str, expected: list[str] | tuple[str, ...]) -> list[str]:
    reports = parse_axiom_reports(output)
    issues: list[str] = []
    expected_set = set(expected)
    found_names = [name for name, _ in reports]
    found_set = set(found_names)
    if len(expected_set) != len(expected):
        issues.append("the configured expected declaration list contains duplicates")
    if len(found_set) != len(found_names):
        duplicates = sorted(name for name in found_set if found_names.count(name) > 1)
        issues.append(f"duplicate axiom reports: {duplicates}")
    missing = sorted(expected_set - found_set)
    if missing:
        issues.append(f"missing axiom reports: {missing}")
    unexpected = sorted(found_set - expected_set)
    if unexpected:
        issues.append(f"unexpected declaration reports: {unexpected}")
    for name, axioms in reports:
        if not axioms <= ALLOWED_AXIOMS:
            issues.append(
                f"{name} uses axioms outside the allowlist: "
                f"{sorted(axioms - ALLOWED_AXIOMS)}"
            )
    return issues


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("output", type=Path)
    parser.add_argument("--expected", nargs="+", required=True, metavar="DECLARATION")
    args = parser.parse_args()
    issues = check_output(args.output.read_text(), args.expected)
    if issues:
        for issue in issues:
            print(issue, file=sys.stderr)
        return 1
    print(f"{len(args.expected)} named declarations use only the reviewed axiom allowlist.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
