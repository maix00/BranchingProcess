/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Minimum.Basic
import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law.FiniteRestriction
/-!
# Endpoint observations on one countable-root forest

The public declarations in
`ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail` are:

- `countableRootEndpointMinimum`: the generation-`H` endpoint minimum among
  the first `N` selected particles, computed from the first `m` roots of one
  countable-root field:
  `firstNSelectedEndpointMinimum m N H (RootIndexed.StepField.first m field)`.
- `measurable_countableRootEndpointMinimum`: this observable is measurable.
- `countableRootEndpointMinimum_sublevel_measure_eq`: its sublevel probability
  under the countable-root law equals the finite-root sublevel probability:
  $\nu_{\mathbb N}(E_{m,N,H}\le x)=\nu_m(E^{(m)}_{N,H}\le x)$.
- `countableRootEndpointMinimum_map_eq`: its pushforward law equals the
  pushforward law of the finite-root endpoint minimum:
  $(\nu_{\mathbb N})_*E_{m,N,H}=(\nu_m)_*E^{(m)}_{N,H}$.
- `countableRootEndpointMinimum_integral_map_eq`: every measurable real
  observable `g` has equal integrals under these two endpoint laws:
  $\int g(E_{m,N,H})\,d\nu_{\mathbb N}=
  \int g(E^{(m)}_{N,H})\,d\nu_m$.
- `countableRootEndpointMinimum_fourthMoment_eq`: for every `c : ℝ`, the
  centered fourth moments agree:
  $\mathbb E[(E_{m,N,H}-c)^4]=\mathbb E[(E^{(m)}_{N,H}-c)^4]$.

Here `E_{m,N,H}` is the countable-root endpoint minimum and
`E^{(m)}_{N,H}` is the finite-root endpoint minimum. The restriction map and
its product-law identity are provided by
`ProbabilityTheory.BranchingRandomWalk.RootIndexed.StepField.measurePreserving_first`.
The observable measurability and law-transfer statements assume the finite-root
node type has the stated measurable space, countability, and linear order;
the measure identities also assume that the one-step measure is a probability
measure.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

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

theorem countableRootEndpointMinimum_sublevel_measure_eq
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (m N H : ℕ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (x : ℝ) :
    (RootIndexed.stepFieldLaw (Root := ℕ) μ)
        {field | countableRootEndpointMinimum m N H field ≤ x} =
      (finiteRootStepFieldLaw μ m)
        {field | firstNSelectedEndpointMinimum m N H field ≤ x} := by
  have hmap := countableRootStepFieldLaw_first μ m
  have hmeas :=
    RootIndexed.StepField.measurable_first (α := ℕ) (X := ℝ) m
  let s : Set (FiniteRootStepField m ℕ ℝ) :=
    {field | firstNSelectedEndpointMinimum m N H field ≤ x}
  have hs : MeasurableSet s := by
    dsimp [s]
    exact measurableSet_Iic.preimage
      (measurable_firstNSelectedEndpointMinimum m N H)
  rw [← hmap]
  rw [Measure.map_apply hmeas hs]
  rfl

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
      (countableRootStepFieldLaw_first μ m)

/-- Integrals of measurable endpoint observables can be transferred between
the finite forest and the common countable-root forest. -/
theorem countableRootEndpointMinimum_integral_map_eq
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (m N H : ℕ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (g : ℝ → ℝ) (hg : Measurable g) :
    (∫ field, g (countableRootEndpointMinimum m N H field)
        ∂RootIndexed.stepFieldLaw (Root := ℕ) μ) =
      ∫ field, g (firstNSelectedEndpointMinimum m N H field)
        ∂finiteRootStepFieldLaw μ m := by
  have hmap := countableRootEndpointMinimum_map_eq μ m N H
  have hX := measurable_countableRootEndpointMinimum m N H
  have hY := measurable_firstNSelectedEndpointMinimum m N H
  calc
    (∫ field, g (countableRootEndpointMinimum m N H field)
        ∂RootIndexed.stepFieldLaw (Root := ℕ) μ) =
      ∫ x, g x ∂(RootIndexed.stepFieldLaw (Root := ℕ) μ).map
        (countableRootEndpointMinimum m N H) := by
          symm
          exact MeasureTheory.integral_map hX.aemeasurable
            (hg.aestronglyMeasurable)
    _ = ∫ x, g x ∂(finiteRootStepFieldLaw μ m).map
        (firstNSelectedEndpointMinimum m N H) := by rw [hmap]
    _ = ∫ field, g (firstNSelectedEndpointMinimum m N H field)
        ∂finiteRootStepFieldLaw μ m :=
          MeasureTheory.integral_map hY.aemeasurable hg.aestronglyMeasurable

theorem countableRootEndpointMinimum_fourthMoment_eq
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (m N H : ℕ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (c : ℝ) :
    (∫ field, (countableRootEndpointMinimum m N H field - c) ^ 4
      ∂RootIndexed.stepFieldLaw (Root := ℕ) μ) =
      ∫ field, (firstNSelectedEndpointMinimum m N H field - c) ^ 4
        ∂finiteRootStepFieldLaw μ m := by
  let f : FiniteRootStepField m ℕ ℝ → ℝ := fun field =>
    (firstNSelectedEndpointMinimum m N H field - c) ^ 4
  have hf : Measurable f := by
    dsimp [f]
    exact (measurable_firstNSelectedEndpointMinimum m N H).sub
      measurable_const |>.pow_const 4
  simpa [f] using countableRootEndpointMinimum_integral_map_eq
    μ m N H (fun x => (x - c) ^ 4)
    (measurable_id.sub measurable_const |>.pow_const 4)

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
