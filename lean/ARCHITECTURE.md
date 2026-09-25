# Lean source layout

The source tree follows the mathematical dependency direction. Files should
stay small enough to have one principal definition or proof layer.

```text
ThesisSpeed/
  Probability/
    PointProcess/
      Basic.lean              abstract measurable counting measures
      Encoding.lean           optional-slot representation, including zero children
      Measure.lean            Dirac-sum realization using mathlib measures
      LocalFiniteness.lean
      Enumeration/            measurable ordering and coverage
      Law/                    i.i.d. laws and support transfer
    Genealogy/                Ulam--Harris trees, positions, roots, first split
    Population/
      Candidates/             candidate generation, ranking, finite truncation
      Processes/              selected, backbone-truncated, fully truncated processes
      Growth/                 deterministic population-size estimates
    Branching/                subtree independence and branching properties
    Timing/                   stopping times, observability, and counterexamples
  Spine/                      many-to-one ingredients
  Analytic.lean               deterministic closing estimates
```

## Placement rules

1. Abstract point-process definitions must not depend on genealogical trees or
   population selection.
2. A general offspring type must admit the zero measure. Any first-child or
   nonextinction theorem belongs in a law or process file and must state its
   nonempty-support hypothesis.
3. Genealogy contains identities, domains, filtrations, and positions. It does
   not choose the surviving population.
4. Candidate files describe one selection step; process files iterate such a
   step and prove adaptation.
5. Branching and timing consume the preceding definitions. They must not be
   imported back into the foundational layers.
6. When a directory grows beyond a small group of closely related files,
   split it by mathematical role as done for `PointProcess` and `Population`.

The next planned split is `Branching/`: fixed-root results, random-root
results, and multi-root results will become subdirectories when new stopped
or stopping-line theorems are added. Moving the current seven files before
that boundary would add import churn without clarifying a new dependency
layer. `Timing/` currently has four focused files and does not need another
level.
