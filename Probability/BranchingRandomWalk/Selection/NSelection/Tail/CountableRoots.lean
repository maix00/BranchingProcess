/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Tail.EndpointMinimum

/-!
# Endpoint observations on one countable-root forest

The finite-root endpoint variables for different initial population sizes are
realized on the same countable-root product space. Restricting to the first
`m` roots has exactly the finite-root branching law.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris

theorem RootIndexed.StepField.measurable_first (m : ℕ) :
    Measurable
      (RootIndexed.StepField.first m : CountableRootStepField ℕ ℝ →
        FiniteRootStepField m ℕ ℝ) := by
  rw [measurable_pi_iff]
  intro r
  rw [measurable_pi_iff]
  intro u
  exact (measurable_pi_apply u).comp (measurable_pi_apply (Fin.val r))

/-- The first `m` roots of the countable pre-sampled forest have the usual
finite-root product law. -/
theorem RootIndexed.StepField.measurePreserving_first
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ] (m : ℕ) :
    MeasurePreserving (RootIndexed.StepField.first m)
      (RootIndexed.stepFieldLaw (Root := ℕ) μ)
      (finiteRootStepFieldLaw μ m) := by
  refine ⟨RootIndexed.StepField.measurable_first m, ?_⟩
  exact countableRootStepFieldLaw_first μ m

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
    (RootIndexed.StepField.measurable_first m)

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
  have hmeas := RootIndexed.StepField.measurable_first m
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
    (RootIndexed.StepField.measurable_first m)]
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
