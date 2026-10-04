#!/usr/bin/env python3
"""Compile every tracked Lean test under BranchingProcessTest."""

import argparse
from pathlib import Path
import subprocess
import sys


def tracked_tests() -> list[Path]:
    result = subprocess.run(
        ["git", "ls-files", "-z", "--", "BranchingProcessTest"],
        check=True,
        stdout=subprocess.PIPE,
    )
    return sorted(
        Path(name.decode())
        for name in result.stdout.split(b"\0")
        if name.endswith(b".lean")
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--output-dir",
        type=Path,
        help="save combined stdout and stderr per test for later CI checks",
    )
    args = parser.parse_args()

    tests = tracked_tests()
    if not tests:
        print("No tracked BranchingProcessTest Lean files found.", file=sys.stderr)
        return 1

    for index, test in enumerate(tests, start=1):
        print(f"[{index}/{len(tests)}] lake env lean {test}", flush=True)
        result = subprocess.run(
            ["lake", "env", "lean", str(test)],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
        )
        if args.output_dir is not None:
            log_path = args.output_dir / f"{test}.log"
            log_path.parent.mkdir(parents=True, exist_ok=True)
            log_path.write_text(result.stdout)
        if result.stdout:
            print(result.stdout, end="", flush=True)
        if result.returncode:
            print(f"Lean test failed: {test}", file=sys.stderr)
            return result.returncode

    print(f"All {len(tests)} tracked Lean tests compiled successfully.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
