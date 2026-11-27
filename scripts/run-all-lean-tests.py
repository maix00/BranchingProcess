#!/usr/bin/env python3
"""Compile tracked and non-ignored untracked Lean tests under BranchingProcessTest."""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
from pathlib import Path
import re
import subprocess
import sys
import tempfile

from lean_test_registry import expected_declarations, registry_entries


def working_tree_tests() -> list[Path]:
    result = subprocess.run(
        [
            "git",
            "ls-files",
            "--cached",
            "--others",
            "--exclude-standard",
            "-z",
            "--",
            "BranchingProcessTest",
        ],
        check=True,
        stdout=subprocess.PIPE,
    )
    return sorted(
        path
        for path in {
            Path(name.decode())
            for name in result.stdout.split(b"\0")
            if name.endswith(b".lean")
        }
        if path.is_file()
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--output-dir",
        type=Path,
        help="save combined stdout and stderr per test for later CI checks",
    )
    parser.add_argument(
        "--jobs",
        type=int,
        default=2,
        help="number of independent Lean test files to compile concurrently (default: 2)",
    )
    parser.add_argument("--test", action="append", type=Path, default=[],
                        help="run only these registered tests (repeatable)")
    args = parser.parse_args()

    if args.jobs < 1:
        parser.error("--jobs must be positive")

    tests = working_tree_tests()
    if not tests:
        print("No BranchingProcessTest Lean files found in the working tree.", file=sys.stderr)
        return 1

    registered = {Path(path) for path, entry in registry_entries('required').items()
                  if entry["category"] == "required"}
    if registered != set(tests):
        print(f"Test registry drift: unregistered={sorted(set(tests)-registered)}, "
              f"missing={sorted(registered-set(tests))}", file=sys.stderr)
        return 1
    if args.test:
        if not set(args.test) <= registered:
            parser.error("--test must name registered required test paths")
        tests = sorted(set(args.test))

    # Some module-syntax regressions expose test-only proof assemblies to
    # legacy-syntax regressions. Build only those imported test modules first.
    support_modules = sorted({
        module
        for test in tests
        for module in re.findall(
            r"^(?:public )?import (?:all )?(BranchingProcessTest\.[A-Za-z0-9_.]+)",
            test.read_text(), re.MULTILINE,
        )
    })
    if support_modules:
        support_build = subprocess.run(["lake", "build", *support_modules])
        if support_build.returncode:
            return support_build.returncode

    def compile_test(index: int, test: Path) -> tuple[Path, subprocess.CompletedProcess[str]]:
        print(f"[{index}/{len(tests)}] lake env lean {test}", flush=True)
        result = subprocess.run(
            ["lake", "env", "lean", str(test)],
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
        )
        return test, result

    with ThreadPoolExecutor(max_workers=args.jobs) as executor:
        futures = {
            executor.submit(compile_test, index, test): test
            for index, test in enumerate(tests, start=1)
        }
        for future in as_completed(futures):
            test, result = future.result()
            if args.output_dir is not None:
                log_path = args.output_dir / f"{test}.log"
                log_path.parent.mkdir(parents=True, exist_ok=True)
                log_path.write_text(result.stdout)
            if result.stdout:
                print(result.stdout, end="", flush=True)
            if result.returncode:
                print(f"Lean test failed: {test}", file=sys.stderr)
                for pending in futures:
                    pending.cancel()
                return result.returncode
            expected = expected_declarations(test, "required")
            if expected or "depends on axioms:" in result.stdout:
                if args.output_dir is not None:
                    axiom_log = args.output_dir / f"{test}.log"
                else:
                    temporary = tempfile.NamedTemporaryFile(
                        mode="w", encoding="utf-8", suffix=".log", delete=False
                    )
                    axiom_log = Path(temporary.name)
                    temporary.close()
                    axiom_log.write_text(result.stdout)
                try:
                    checked = subprocess.run(
                        [
                            sys.executable,
                            "scripts/check-lean-axioms.py",
                            str(axiom_log),
                            "--expected",
                            *expected,
                        ],
                        text=True,
                    )
                finally:
                    if args.output_dir is None:
                        axiom_log.unlink(missing_ok=True)
                if checked.returncode:
                    print(f"Axiom check failed: {test}", file=sys.stderr)
                    for pending in futures:
                        pending.cancel()
                    return checked.returncode

    print(f"All {len(tests)} working-tree Lean tests compiled successfully.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
