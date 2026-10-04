#!/usr/bin/env python3
"""Check architectural import boundaries in the local Lean module graph."""

from pathlib import Path
import subprocess
import sys
import tempfile


LEAN_ROOT = Path(__file__).resolve().parents[1]
ENTRY_MODULES = (
    "Probability.Process.Stable.Corridor.Law",
    "Probability.Process.Stable.SmallDeviation.ShiftedCorridor",
    "Probability.Process.Stable.SmallDeviation.RangeComparison",
    "Probability.Process.Stable.SmallDeviation.BlockBounds",
    "Probability.Process.Stable.SmallDeviation.Blocks.Upper.ArbitraryHorizon",
    "Probability.Process.Stable.SmallDeviation.EndpointComparison",
    "Probability.Process.Stable.SmallDeviation.EscapeRate",
    "Probability.Process.Stable.SmallDeviation.EscapeRate.Corridor",
    "Probability.Process.Stable.SmallDeviation.EscapeRate.Endpoint",
    "Probability.Process.Stable.SmallDeviation.EscapeRate.Law",
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
GENERAL_LAYER_BOUNDARIES = {
    "Probability.Process.SmallDeviation.Mogulskii.PathClass.Boundary": (
        "Probability.BranchingRandomWalk",
        "Probability.Process.Stable",
    ),
    "Probability.Process.SmallDeviation.Mogulskii.PathClass.Basic": (
        "Probability.BranchingRandomWalk",
        "Probability.Process.Stable",
    ),
    "Probability.Process.SmallDeviation.Mogulskii.PathClass.Energy": (
        "Probability.BranchingRandomWalk",
        "Probability.Process.Stable",
    ),
    "Probability.Process.SmallDeviation.Mogulskii.PathClass.Approximation": (
        "Probability.BranchingRandomWalk",
        "Probability.Process.Stable",
    ),
    "Probability.Process.SmallDeviation.Mogulskii.PathClass.Rate.FiniteUnion": (
        "Probability.BranchingRandomWalk",
        "Probability.Process.Stable",
    ),
    "Probability.Process.SmallDeviation.Mogulskii.PathClass.Rate.Approximation": (
        "Probability.BranchingRandomWalk",
        "Probability.Process.Stable",
    ),
    "Analysis.Fourier.PositiveDefinite": (
        "MeasureTheory.Measure.CharacteristicFunction",
        "Probability",
    ),
    "Analysis.Fourier.CosineTauberian.Kernel": (
        "Probability",
    ),
    "Analysis.Fourier.CosineTauberian.Inversion": (
        "Probability",
    ),
    "Analysis.Fourier.CosineTauberian.Mellin": (
        "Probability",
    ),
    "Analysis.Fourier.CosineTauberian.RegularVariation": (
        "Probability",
    ),
    "Probability.Distributions.CharacteristicFunction.Symmetrization.RegularVariation": (
        "Probability.Distributions.CharacteristicFunction.Tauberian",
        "Probability.Distributions.Stable.Attraction",
        "Analysis.Fourier.CosineTauberian.Inversion",
        "Analysis.Fourier.CosineTauberian.Mellin",
    ),
    "Probability.Distributions.CharacteristicFunction.CosineDefect": (
        "Probability.Distributions.CharacteristicFunction.Tauberian",
        "Analysis.Fourier.CosineTauberian",
    ),
    "Probability.Distributions.CharacteristicFunction.Symmetrization.Tail": (
        "Probability.Distributions.CharacteristicFunction.Tauberian",
        "Analysis.Fourier.CosineTauberian.Inversion",
        "Analysis.Fourier.CosineTauberian.Mellin",
    ),
    "Probability.Distributions.CharacteristicFunction.Tauberian.SecondTail": (
        "Probability.Distributions.Stable.Attraction",
        "Probability.BranchingRandomWalk",
        "Combinatorics.BranchingWalk",
    ),
    "MeasureTheory.Measure.CharacteristicFunction.Nondegenerate": (
        "Probability.Distributions.Stable",
        "Probability.BranchingRandomWalk",
        "Combinatorics.BranchingWalk",
    ),
    "Probability.Distributions.DomainOfAttraction.Basic": (
        "Probability.Distributions.Stable",
        "Probability.BranchingRandomWalk",
        "Combinatorics.BranchingWalk",
    ),
    "Probability.Distributions.DomainOfAttraction.CharacteristicFunction": (
        "Probability.Distributions.Stable",
        "Probability.BranchingRandomWalk",
        "Combinatorics.BranchingWalk",
    ),
    "Probability.Distributions.DomainOfAttraction.Block": (
        "Probability.Distributions.Stable",
        "Probability.BranchingRandomWalk",
        "Combinatorics.BranchingWalk",
    ),
    "Probability.Distributions.Poisson.Basic": (
        "Probability.RandomMeasure",
        "Probability.Process",
        "Probability.BranchingProcess",
        "Probability.BranchingRandomWalk",
        "Combinatorics.BranchingWalk",
    ),
    "Probability.RandomMeasure.Poisson.PointFamily": (
        "Probability.Process.Levy",
        "Probability.Process.Stable",
        "Probability.BranchingProcess",
        "Probability.BranchingRandomWalk",
    ),
    "Probability.RandomMeasure.Poisson.Basic": (
        "Probability.Process.Levy",
        "Probability.Process.Stable",
        "Probability.BranchingProcess",
        "Probability.BranchingRandomWalk",
    ),
    "Probability.RandomMeasure.Poisson.Integral": (
        "Probability.Process.Levy",
        "Probability.Process.Stable",
        "Probability.BranchingProcess",
        "Probability.BranchingRandomWalk",
    ),
    "Probability.Distributions.Moments.Truncated.TailIntegral": (
        "Probability.Distributions.Stable",
        "Probability.BranchingRandomWalk",
        "Combinatorics.BranchingWalk",
    ),
    "Probability.BranchingProcess.Offspring.Law": (
        "Probability.BranchingRandomWalk",
        "Probability.BranchingProcess.GaltonWatson",
    ),
    "Probability.BranchingProcess.Offspring.Map": (
        "Probability.BranchingRandomWalk",
        "Probability.BranchingProcess.GaltonWatson",
    ),
    "Probability.BranchingProcess.Offspring.Count": (
        "Probability.BranchingRandomWalk",
        "Probability.BranchingProcess.GaltonWatson",
    ),
    "Probability.BranchingProcess.Offspring.PointMeasure": (
        "Probability.BranchingRandomWalk",
        "Probability.BranchingProcess.GaltonWatson",
    ),
    "Probability.BranchingProcess.Offspring.FieldLaw": (
        "Probability.BranchingRandomWalk",
        "Probability.BranchingProcess.GaltonWatson",
    ),
}
LEAN_IMPORT_PARSER = Path(__file__).resolve().with_name("parse_lean_imports.lean")


class ImportParseError(RuntimeError):
    """Raised when Lean cannot parse one or more module headers."""


def source_path(module: str, root: Path = LEAN_ROOT) -> Path:
    return root / (module.replace(".", "/") + ".lean")


def parse_imports_from_paths(
    paths: list[Path],
) -> tuple[dict[Path, list[str]], list[str]]:
    """Parse module headers with Lean's parser, preserving its import grammar."""
    normalized = [path.resolve() for path in paths]
    imports = {path: [] for path in normalized}
    if not normalized:
        return imports, []

    try:
        result = subprocess.run(
            ["lake", "env", "lean", "--run", str(LEAN_IMPORT_PARSER)],
            cwd=LEAN_ROOT,
            input="".join(f"{path}\n" for path in normalized),
            text=True,
            capture_output=True,
            check=False,
        )
    except OSError as error:
        raise ImportParseError(f"could not start Lean's import parser: {error}") from error

    issues: list[str] = []
    if result.returncode:
        details = result.stderr.strip() or result.stdout.strip()
        issues.append(f"Lean import parser exited with {result.returncode}: {details}")

    for line in result.stdout.splitlines():
        parts = line.split("\t", maxsplit=2)
        if len(parts) != 3 or parts[0] not in {"I", "E"}:
            issues.append(f"unrecognized Lean import parser output: {line}")
            continue
        _, source_path, value = parts
        path = Path(source_path).resolve()
        if path not in imports:
            issues.append(f"Lean import parser returned an unknown source path: {source_path}")
            continue
        if parts[0] == "E":
            issues.append(f"could not parse imports in {source_path}: {value}")
        else:
            imports[path].append(value)
    return imports, issues


def imported_modules(source: str) -> list[str]:
    """Parse imports in a source snippet using Lean's actual module-header parser."""
    with tempfile.TemporaryDirectory() as directory:
        path = Path(directory) / "Snippet.lean"
        path.write_text(source)
        imports, issues = parse_imports_from_paths([path])
    if issues:
        raise ImportParseError("; ".join(issues))
    return imports[path.resolve()]


def load_import_graph(root: Path) -> tuple[dict[str, list[str]], list[str]]:
    """Parse all local Lean headers once and return module-name adjacency lists."""
    root = root.resolve()
    paths = sorted(
        path
        for path in root.rglob("*.lean")
        if not {".lake", ".git"}.intersection(path.relative_to(root).parts)
    )
    parsed, issues = parse_imports_from_paths(paths)
    graph = {
        ".".join(path.relative_to(root).with_suffix("").parts): imports
        for path, imports in parsed.items()
    }
    return graph, issues


def forbidden_import_reason(module: str) -> str | None:
    if module.startswith(FEEDBACK_MODULE_STEM):
        return "legacy Feedback* proof route"
    for prefix in FORBIDDEN_PREFIXES:
        if module == prefix or module.startswith(prefix + "."):
            return prefix
    return None


def inspect_entries(
    entries: tuple[str, ...] | list[str],
    root: Path = LEAN_ROOT,
    import_graph: dict[str, list[str]] | None = None,
    parse_issues: list[str] | None = None,
) -> tuple[dict[str, int], list[str]]:
    counts: dict[str, int] = {}
    issues: list[str] = list(parse_issues or [])
    if import_graph is None:
        import_graph, graph_issues = load_import_graph(root)
        issues.extend(graph_issues)
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
            for imported in import_graph.get(module, []):
                reason = forbidden_import_reason(imported)
                if reason is not None:
                    issues.append(f"forbidden import: {module} -> {imported} ({reason})")
                if source_path(imported, root).is_file():
                    pending.append(imported)
        counts[entry] = len(seen)
    return counts, issues


def inspect_general_layer_boundaries(
    boundaries: dict[str, tuple[str, ...]] = GENERAL_LAYER_BOUNDARIES,
    root: Path = LEAN_ROOT,
    import_graph: dict[str, list[str]] | None = None,
    parse_issues: list[str] | None = None,
) -> list[str]:
    """Check transitive imports against each module's declared boundaries."""
    issues: list[str] = list(parse_issues or [])
    if import_graph is None:
        import_graph, graph_issues = load_import_graph(root)
        issues.extend(graph_issues)
    for entry, forbidden_prefixes in boundaries.items():
        if not source_path(entry, root).is_file():
            issues.append(f"missing general-layer module: {entry}")
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
            for imported in import_graph.get(module, []):
                for prefix in forbidden_prefixes:
                    if imported == prefix or imported.startswith(prefix + "."):
                        issues.append(
                            f"general-layer dependency crosses boundary: "
                            f"{module} -> {imported} ({prefix})"
                        )
                if source_path(imported, root).is_file():
                    pending.append(imported)
    return issues


def main() -> int:
    import_graph, parse_issues = load_import_graph(LEAN_ROOT)
    counts, issues = inspect_entries(
        ENTRY_MODULES, import_graph=import_graph, parse_issues=parse_issues
    )
    issues.extend(inspect_general_layer_boundaries(import_graph=import_graph))
    if issues:
        for issue in issues:
            print(issue, file=sys.stderr)
        return 1
    total = sum(counts.values())
    for entry, count in counts.items():
        print(f"{entry}: {count} local modules; forbidden proof routes absent")
    print(f"Checked {len(counts)} public entries ({total} graph visits).")
    print("General attraction modules have no branching-walk dependencies.")
    print("Cosine Tauberian analysis modules have no probability dependencies.")
    print(
        "Offspring-law modules have no branching-random-walk or "
        "Galton--Watson dependencies."
    )
    print(
        "Poisson distribution and random-measure modules avoid "
        "application-layer dependencies."
    )
    print(
        "Mogulskii path-class modules have no branching-random-walk or "
        "stable-process dependencies."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
