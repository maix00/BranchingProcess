#!/usr/bin/env python3
"""Ensure the public relation (21) module stays independent of legacy routes."""

from pathlib import Path
import re
import sys


LEAN_ROOT = Path(__file__).resolve().parents[1] / "lean"
ENTRY = (
    "Probability.Process.Stable.SmallDeviation.Blocks."
    "ShiftComparison.Relation21"
)
FORBIDDEN_PREFIXES = (
    "Probability.Process.Stable.JumpModel",
    "Probability.Process.Stable.SmallDeviation.Blocks.ShiftComparison.PoissonEntrance",
    "Probability.Process.Stable.SmallDeviation.Blocks.ShiftComparison.Feedback",
    "Probability.Process.Stable.SmallDeviation.Blocks.ShiftComparison.Support",
    "Probability.Process.Stable.SmallDeviation.Blocks.Lower.Feedback",
    "Probability.Process.Stable.SmallDeviation.Blocks.Lower.PathSupport",
    "Probability.Process.Path.Skorokhod.Corridor.Support",
)
IMPORT = re.compile(r"^\s*(?:public\s+)?import\s+([\w.]+)", re.MULTILINE)


def source_path(module: str) -> Path:
    return LEAN_ROOT / (module.replace(".", "/") + ".lean")


def main() -> int:
    seen: set[str] = set()
    pending = [ENTRY]
    violations: list[tuple[str, str]] = []
    while pending:
        module = pending.pop()
        if module in seen:
            continue
        seen.add(module)
        path = source_path(module)
        if not path.is_file():
            continue
        for imported in IMPORT.findall(path.read_text()):
            if any(
                imported == prefix or imported.startswith(prefix + ".")
                for prefix in FORBIDDEN_PREFIXES
            ):
                violations.append((module, imported))
            if source_path(imported).is_file():
                pending.append(imported)

    if violations:
        for importer, imported in violations:
            print(f"forbidden import: {importer} -> {imported}", file=sys.stderr)
        return 1
    print(f"{ENTRY}: {len(seen)} local modules; forbidden routes absent")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
