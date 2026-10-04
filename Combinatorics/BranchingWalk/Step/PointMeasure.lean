/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.Basic
public import Combinatorics.BranchingWalk.Step.Count
public import Combinatorics.BranchingWalk.Step.Measurability
public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import MeasureTheory.Measure.DiracSum

/-!
# Dirac sums of a branching step

An absent slot contributes nothing and a survive slot contributes the Dirac
mass at its mark, so a step induces a counting measure on mark space. This is
the `Step` instance of `MeasureTheory.Measure.iOptionDiracSum`; it is
deterministic and carries no probability measure, filtration, or sample space.

Measurability of this observation under a random step lives in
`Probability/BranchingRandomWalk/Step/`.
-/

open MeasureTheory
open Classical
open scoped ENNReal

@[expose] public section

namespace Combinatorics

namespace Branching

/-- The Dirac mass of a survive slot, and zero for an absent slot. -/
noncomputable def stepAtomMeasure {ι X : Type*} [MeasurableSpace X]
    (ξ : Step ι X) (i : ι) : Measure X :=
  (ξ i).elim 0 Measure.dirac

/-- The point measure obtained by summing the atoms of a branching step. It is
the Dirac sum over the survive slots. -/
noncomputable def stepPointMeasure {ι X : Type*} [MeasurableSpace X]
    (ξ : Step ι X) : Measure X :=
  Measure.sum (stepAtomMeasure ξ)

theorem stepPointMeasure_eq_iOptionDiracSum {ι X : Type*} [MeasurableSpace X]
    (ξ : Step ι X) :
  stepPointMeasure ξ = Measure.iOptionDiracSum ξ :=
  rfl

/-- Every point measure obtained from a branching step is integer-valued,
including when child marks coincide. -/
theorem stepPointMeasure_isIntegerValued {ι X : Type*} [MeasurableSpace X]
    (ξ : Step ι X) : Measure.IsIntegerValued (stepPointMeasure ξ) := by
  rw [stepPointMeasure_eq_iOptionDiracSum]
  exact Measure.iOptionDiracSum_isIntegerValued ξ

theorem stepAtomMeasure_apply {ι X : Type*} [MeasurableSpace X]
    (ξ : Step ι X) (i : ι) (s : Set X) (hs : MeasurableSet s) :
    stepAtomMeasure ξ i s =
      match ξ i with
      | some x => if x ∈ s then 1 else 0
      | none => 0 := by
  cases h : ξ i <;>
    simp [stepAtomMeasure, h, Measure.dirac_apply' _ hs, Set.indicator_apply]

theorem stepAtomMeasure_univ {ι X : Type*} [MeasurableSpace X]
    (ξ : Step ι X) (i : ι) :
    stepAtomMeasure ξ i Set.univ =
      if survive ξ i then 1 else 0 := by
  cases h : ξ i <;>
    simp [stepAtomMeasure, survive, h]

theorem stepPointMeasure_apply {ι X : Type*} [MeasurableSpace X]
    (ξ : Step ι X) (s : Set X) (hs : MeasurableSet s) :
    stepPointMeasure ξ s =
      ∑' i : ι, match ξ i with
        | some x => if x ∈ s then 1 else 0
        | none => 0 := by
  rw [stepPointMeasure, Measure.sum_apply _ hs]
  exact tsum_congr (fun i => stepAtomMeasure_apply ξ i s hs)

/-- The Dirac mass of a slot is a measurable function of the step: it is the Dirac mass at the slot's value
where the slot is survive, and the zero measure where it is not. -/
theorem stepAtomMeasure_measurable {ι X : Type*} [MeasurableSpace X] (i : ι) :
    Measurable (fun ξ : Step ι X => stepAtomMeasure ξ i) :=
  (Measure.measurable_option_dirac).comp (measurable_pi_apply i)

/-- The point measure of a step is a measurable function of the step. -/
theorem stepPointMeasure_measurable {ι X : Type*} [Countable ι] [MeasurableSpace X] :
    Measurable (fun ξ : Step ι X => stepPointMeasure ξ) := by
  change Measurable (Measure.iOptionDiracSum : (Step ι X) → Measure X)
  exact Measure.iOptionDiracSum_measurable

/-- Mapping each child mark pushes the step's point measure forward through
the same map. Multiplicity and empty configurations are both preserved. -/
theorem stepPointMeasure_map {ι X Y : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] (f : X → Y) (hf : Measurable f) (ξ : Step ι X) :
    stepPointMeasure (ξ.map f) = (stepPointMeasure ξ).map f := by
  rw [stepPointMeasure, stepPointMeasure, Measure.map_sum hf.aemeasurable]
  congr 1
  funext i
  cases h : ξ i with
  | none => simp [stepAtomMeasure, Step.map, h]
  | some x => simp [stepAtomMeasure, Step.map, h, Measure.map_dirac' hf x]

/-- The total mass of the point measure is the extended number of present
slots. This equality includes both empty configurations and infinitely many
children. -/
theorem stepPointMeasure_univ {ι X : Type*} [MeasurableSpace X]
    (ξ : Step ι X) :
    stepPointMeasure ξ Set.univ = (ξ.childCount : ℝ≥0∞) := by
  rw [stepPointMeasure_eq_iOptionDiracSum,
    Measure.iOptionDiracSum_apply ξ MeasurableSet.univ]
  have hterm (i : ι) :
      (match ξ i with
        | some x => Set.univ.indicator (1 : X → ℝ≥0∞) x
        | none => 0) =
        (support ξ).indicator (fun _ => (1 : ℝ≥0∞)) i := by
    cases h : ξ i <;> simp [support, survive, h]
  calc
    _ = ∑' i, (support ξ).indicator (fun _ => (1 : ℝ≥0∞)) i :=
      tsum_congr hterm
    _ = ∑' i : support ξ, (1 : ℝ≥0∞) :=
      (tsum_subtype (support ξ) fun _ => (1 : ℝ≥0∞)).symm
    _ = (support ξ).encard := ENNReal.tsum_set_one (support ξ)
    _ = (ξ.childCount : ℝ≥0∞) := rfl

end Branching

end Combinatorics

end
