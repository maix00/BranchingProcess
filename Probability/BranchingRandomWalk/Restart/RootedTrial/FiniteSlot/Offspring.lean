/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.Selection.FiniteSlot
public import MeasureTheory.BranchingWalk.Step.Selection.FiniteSlot
public import Probability.BranchingProcess.Offspring.Count

/-!
# Finite-slot offspring laws from bounded selections

For a measurable finite selection $S$, the law of its deterministic
binary-slot encoding is an offspring-configuration law. This module relates
that law's expected child count to the probability that the selection splits.

## Public declarations

- `finiteOffspringLaw ν S hS` is the pushforward of the one-step law by
  `S.binaryOffspringStep`.
- `finiteOffspringLaw_isSupercritical` proves that almost-sure nonemptiness,
  capacity at most two, and positive probability of selecting two children
  imply that the encoded offspring mean is greater than one.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching ProbabilityTheory.BranchingProcess

/-- The finite-slot law obtained by applying a measurable selected-child
count to one step. -/
noncomputable def finiteOffspringLaw
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [OrderBot α]
    (ν : ProbabilityMeasure (Step α X))
    (S : Step.FiniteSelection α X) (_hS : Measurable S.select) :
    OffspringConfigurationLaw (Fin 2) PUnit.{1} :=
  ν.map S.binaryOffspringStep

/-- A retained-child count that is positive almost surely and has positive
probability of being two defines a supercritical finite-slot offspring law.
The proof computes its mean as one plus the split probability. -/
theorem finiteOffspringLaw_isSupercritical
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [OrderBot α]
    (ν : ProbabilityMeasure (Step α X))
    (S : Step.FiniteSelection α X) (hS : Measurable S.select)
    (hcapacity : ∀ ξ, (S ξ).card ≤ 2)
    (hnonempty : ∀ᵐ ξ ∂(ν : Measure (Step α X)), (S ξ).Nonempty)
    (hsplit : 0 < (ν : Measure (Step α X)) {ξ | 2 ≤ (S ξ).card}) :
    (finiteOffspringLaw ν S hS).IsSupercritical := by
  let f := S.binaryOffspringStep
  let μ := finiteOffspringLaw ν S hS
  have hmeas : Measurable f :=
    Step.FiniteSelection.binaryOffspringStep_measurable S hS
  have hsplitMeas : MeasurableSet {ξ : Step α X | 2 ≤ (S ξ).card} := by
    have hc : Measurable (fun ξ : Step α X => (S ξ).card) :=
      (measurable_of_countable fun s : Finset α => s.card).comp hS
    change MeasurableSet ((fun ξ : Step α X => (S ξ).card) ⁻¹' Set.Ici 2)
    exact hc measurableSet_Ici
  have hpointwise : ∀ᵐ ξ ∂(ν : Measure (Step α X)),
      ((f ξ).childCount : ℝ≥0∞) =
        1 + (if 2 ≤ (S ξ).card then 1 else 0) := by
    filter_upwards [hnonempty] with ξ hne
    have hpositive : 0 < (S ξ).card := Finset.card_pos.mpr hne
    have hcnt :=
      Step.FiniteSelection.binaryOffspringStep_childCount S ξ (hcapacity ξ)
    have hcap := hcapacity ξ
    by_cases hsplitξ : 2 ≤ (S ξ).card
    · have htwo : (S ξ).card = 2 := by omega
      change ((S.binaryOffspringStep ξ).childCount : ℝ≥0∞) = _
      rw [hcnt, htwo]
      norm_num [hsplitξ]
    · have hone : (S ξ).card = 1 := by omega
      change ((S.binaryOffspringStep ξ).childCount : ℝ≥0∞) = _
      rw [hcnt, hone]
      simp
  have hindicator :
      (fun ξ : Step α X => if 2 ≤ (S ξ).card then 1 else 0) =
        Set.indicator {ξ : Step α X | 2 ≤ (S ξ).card}
          (fun _ => (1 : ℝ≥0∞)) := by
    funext ξ
    by_cases hξ : 2 ≤ (S ξ).card <;> simp [hξ]
  have hpart :
      (∫⁻ ξ : Step α X,
        (if 2 ≤ (S ξ).card then 1 else 0) ∂(ν : Measure (Step α X))) =
        (ν : Measure (Step α X)) {ξ | 2 ≤ (S ξ).card} := by
    rw [hindicator]
    change (∫⁻ ξ : Step α X,
      {ξ | 2 ≤ (S ξ).card}.indicator 1 ξ ∂(ν : Measure (Step α X))) = _
    exact lintegral_indicator_one hsplitMeas
  have hexpect : μ.expectedChildCount =
      1 + (ν : Measure (Step α X)) {ξ | 2 ≤ (S ξ).card} := by
    rw [OffspringConfigurationLaw.expectedChildCount,
      OffspringConfigurationLaw.childCountLaw_toMeasure]
    change (∫⁻ n : ℕ∞, (n : ℝ≥0∞) ∂
        (((ν.map f : OffspringConfigurationLaw (Fin 2) PUnit.{1}).map
          Step.childCount : ProbabilityMeasure ℕ∞) : Measure ℕ∞)) = _
    have hcast : Measurable (fun n : ℕ∞ => (n : ℝ≥0∞)) := by fun_prop
    have hchild : Measurable
        (fun ξ : Step (Fin 2) PUnit.{1} => (ξ.childCount : ℝ≥0∞)) :=
      (measurable_of_countable fun n : ℕ∞ => (n : ℝ≥0∞)).comp
        Step.childCount_measurable
    rw [ProbabilityMeasure.toMeasure_map, lintegral_map hcast
      Step.childCount_measurable]
    rw [ProbabilityMeasure.toMeasure_map, lintegral_map hchild hmeas]
    calc
      (∫⁻ ξ : Step α X, ((f ξ).childCount : ℝ≥0∞) ∂(ν : Measure _)) =
          ∫⁻ ξ : Step α X,
            (1 + (if 2 ≤ (S ξ).card then 1 else 0)) ∂(ν : Measure _) :=
        lintegral_congr_ae hpointwise
      _ = (∫⁻ _ : Step α X, (1 : ℝ≥0∞) ∂(ν : Measure _)) +
          ∫⁻ ξ : Step α X,
            (if 2 ≤ (S ξ).card then 1 else 0) ∂(ν : Measure _) := by
        rw [lintegral_add_left' measurable_const.aemeasurable]
      _ = 1 + (ν : Measure (Step α X)) {ξ | 2 ≤ (S ξ).card} := by
        rw [hpart]
        simp
  change 1 < μ.expectedChildCount
  rw [hexpect]
  have hpTop : (ν : Measure (Step α X)) {ξ | 2 ≤ (S ξ).card} < ∞ :=
    measure_lt_top _ _
  have hsumTop : (1 : ℝ≥0∞) +
      (ν : Measure (Step α X)) {ξ | 2 ≤ (S ξ).card} < ∞ :=
    ENNReal.add_lt_top.mpr ⟨by simp, hpTop⟩
  have hrealPos : 0 <
      ((ν : Measure (Step α X)) {ξ | 2 ≤ (S ξ).card}).toReal :=
    ENNReal.toReal_pos_iff.mpr ⟨hsplit, hpTop⟩
  have hreal : (1 : ℝ) <
      1 + ((ν : Measure (Step α X)) {ξ | 2 ≤ (S ξ).card}).toReal :=
    lt_add_of_pos_right 1 hrealPos
  have hreal' :
      ENNReal.toReal 1 <
        (1 + (ν : Measure (Step α X)) {ξ | 2 ≤ (S ξ).card}).toReal := by
    simpa only [ENNReal.toReal_add ENNReal.one_ne_top hpTop.ne,
      ENNReal.toReal_one] using hreal
  exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hsumTop.ne).mp hreal'

end ProbabilityTheory.BranchingRandomWalk

end
