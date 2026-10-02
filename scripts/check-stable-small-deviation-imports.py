#!/usr/bin/env python3
"""Check public stable small-deviation entries and their local import graphs."""

from pathlib import Path
import re
import sys


LEAN_ROOT = Path(__file__).resolve().parents[1]
ENTRY_MODULES = (
    "Probability.Process.Stable.SmallDeviation.ShiftedCorridor",
    "Probability.Process.Stable.SmallDeviation.RangeComparison",
)
FORBIDDEN_PREFIXES = (
    "Probability.Process.Stable.JumpModel",
    "Probability.Process.Stable.SmallDeviation.Blocks.ShiftComparison",
    "Probability.Process.Stable.SmallDeviation.Blocks.Lower.Feedback",
    "Probability.Process.Stable.SmallDeviation.Blocks.Lower.PathSupport",
    "Probability.Process.Path.Skorokhod.Corridor.Support",
)
FEEDBACK_MODULE_STEM = (
    "Probability.Process.Stable.SmallDeviation.Blocks.Lower.Feedback"
)
IMPORT = re.compile(r"^\s*(?:public\s+)?import\s+([\w.]+)", re.MULTILINE)


def source_path(module: str, root: Path = LEAN_ROOT) -> Path:
    return root / (module.replace(".", "/") + ".lean")


def imported_modules(source: str) -> list[str]:
    return IMPORT.findall(source)


def forbidden_import_reason(module: str) -> str | None:
    if module.startswith(FEEDBACK_MODULE_STEM):
        return "legacy Feedback* proof route"
    for prefix in FORBIDDEN_PREFIXES:
        if module == prefix or module.startswith(prefix + "."):
            return prefix
    return None


def inspect_entries(
    entries: tuple[str, ...] | list[str], root: Path = LEAN_ROOT
) -> tuple[dict[str, int], list[str]]:
    counts: dict[str, int] = {}
    issues: list[str] = []
    for entry in entries:
        entry_path = source_path(entry, root)
        if not entry_path.is_file():
            issues.append(f"missing public entry module: {entry} ({entry_path})")
            continue

        seen: set[str] = set()
        pending = [entry]
        while pending:
            module = pending.pop()
            if module in seen:
                continue
            seen.add(module)
            path = source_path(module, root)
            if not path.is_file():
                continue
            for imported in imported_modules(path.read_text()):
                reason = forbidden_import_reason(imported)
                if reason is not None:
                    issues.append(f"forbidden import: {module} -> {imported} ({reason})")
                if source_path(imported, root).is_file():
                    pending.append(imported)
        counts[entry] = len(seen)
    return counts, issues


def main() -> int:
    counts, issues = inspect_entries(ENTRY_MODULES)
    if issues:
        for issue in issues:
            print(issue, file=sys.stderr)
        return 1
    total = sum(counts.values())
    for entry, count in counts.items():
        print(f"{entry}: {count} local modules; forbidden proof routes absent")
    print(f"Checked {len(counts)} public entries ({total} graph visits).")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
