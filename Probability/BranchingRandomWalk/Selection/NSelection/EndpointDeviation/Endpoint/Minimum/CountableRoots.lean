/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Minimum.Basic
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law.FiniteRestriction
/-!
# Endpoint observations on one countable-root forest

## Public declarations

The declarations in
`ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation` are:

- `countableRootEndpointMinimum`: the generation-`H` endpoint minimum among
  the first `N` selected particles, computed from the first `m` roots of one
  countable-root field:
  `firstNSelectedEndpointMinimum m N H (RootIndexed.StepField.first m field)`.
- `measurable_countableRootEndpointMinimum`: this observable is measurable.
- `countableRootEndpointMinimum_map_eq`: its pushforward law equals the
  pushforward law of the finite-root endpoint minimum:
  $(\nu_{\mathbb N})_*E_{m,N,H}=(\nu_m)_*E^{(m)}_{N,H}$.

Here `E_{m,N,H}` is the countable-root endpoint minimum and
`E^{(m)}_{N,H}` is the finite-root endpoint minimum. The restriction map and
its product-law identity are provided by
`ProbabilityTheory.BranchingRandomWalk.RootIndexed.StepField.measurePreserving_first`.
The observable measurability and law-transfer statements assume the finite-root
node type has the stated measurable space, countability, and linear order;
the pushforward-law identity also assumes that the one-step measure is a
probability measure.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open Combinatorics.Branching
open Combinatorics.UlamHarris

/-- The generation-`H` minimum among the first `N` selected particles from
the first `m` roots, viewed on the common countable-root probability space. -/
noncomputable def countableRootEndpointMinimum (m N H : ℕ)
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (field : CountableRootStepField ℕ ℝ) : ℝ :=
  firstNSelectedEndpointMinimum m N H (RootIndexed.StepField.first m field)

theorem measurable_countableRootEndpointMinimum (m N H : ℕ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    Measurable (countableRootEndpointMinimum m N H) := by
  exact (measurable_firstNSelectedEndpointMinimum m N H).comp
    (RootIndexed.StepField.measurable_first (α := ℕ) (X := ℝ) m)

/-- The endpoint observable on the common countable-root forest has exactly
the same distribution as the finite-root endpoint observable. -/
theorem countableRootEndpointMinimum_map_eq
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (m N H : ℕ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)] :
    (RootIndexed.stepFieldLaw (Root := ℕ) μ).map
        (countableRootEndpointMinimum m N H) =
      (finiteRootStepFieldLaw μ m).map
        (firstNSelectedEndpointMinimum m N H) := by
  rw [show countableRootEndpointMinimum m N H =
      firstNSelectedEndpointMinimum m N H ∘ RootIndexed.StepField.first m by
        rfl]
  rw [← Measure.map_map
    (measurable_firstNSelectedEndpointMinimum m N H)
    (RootIndexed.StepField.measurable_first (α := ℕ) (X := ℝ) m)]
  exact congrArg (fun ν : Measure (FiniteRootStepField m ℕ ℝ) =>
    ν.map (firstNSelectedEndpointMinimum m N H))
      (RootIndexed.StepField.measurePreserving_first μ m).map_eq

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation
