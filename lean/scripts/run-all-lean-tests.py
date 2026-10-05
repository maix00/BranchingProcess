#!/usr/bin/env python3
"""Compile every tracked Lean test under BranchingProcessTest."""

import argparse
from pathlib import Path
import subprocess
import sys
import tempfile


AXIOM_EXPECTATIONS = {
    Path("BranchingProcessTest/RandomWalk/FiniteDimensionalIndependentBlocks.lean"): (
        "ProbabilityTheory.RandomWalk.iIndepFun_variableConsecutiveBlockCoordinates",
        "ProbabilityTheory.RandomWalk.iIndepFun_variableConsecutiveBlockSums",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.FiniteDimensional.tendstoInDistribution_consecutiveBlockSums",
        "ProbabilityTheory.RandomWalk.FunctionalLimit.FiniteDimensional.tendstoInDistribution_consecutiveBlockEndpoints",
    ),
    Path("BranchingProcessTest/RandomWalk/TruncationMoments.lean"): (
        "ProbabilityTheory.RandomWalk.integrable_truncatedIncrement_pow",
        "ProbabilityTheory.RandomWalk.integrable_centeredTruncatedIncrement_pow_four",
        "ProbabilityTheory.RandomWalk.integral_partialSum_pow_four_centeredTruncated_le",
        "ProbabilityTheory.RandomWalk.maximal_ineq_pow_four_blockSum_centeredTruncated_bounded",
        "ProbabilityTheory.RandomWalk.measure_exists_block_exists_abs_ge_le_of_truncation_bounded",
    ),
}


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
        expected = AXIOM_EXPECTATIONS.get(test)
        if expected is not None:
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
                return checked.returncode

    print(f"All {len(tests)} tracked Lean tests compiled successfully.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
