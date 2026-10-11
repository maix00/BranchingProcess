/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Restart.GoodSplit
import Probability.BranchingProcess.GaltonWatson.BoundedGrowth

/-!
# Bounded offspring law of the reserve selector

The reserve rule keeps between one and two children almost surely. This file
encodes its selected child count as a two-slot unmarked offspring configuration,
proves that this finite-slot law is supercritical from positive split
probability, and exposes the fixed-horizon Galton--Watson estimate for that law.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching ProbabilityTheory.BranchingProcess
  ProbabilityTheory.BranchingProcess.GaltonWatson

/-- Encode the number of children retained by a selector as the initial
segment of a two-slot unmarked offspring configuration. -/
noncomputable def finiteOffspringStep
    {α X : Type*} [LinearOrder α] [OrderBot α]
    (S : Step.FiniteSelection α X) (ξ : Step α X) :
    Step (Fin 2) PUnit.{1} :=
  fun i => if i.val < (S ξ).card then some PUnit.unit else none

theorem finiteOffspringStep_measurable
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [OrderBot α]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select) :
    Measurable (finiteOffspringStep S) := by
  apply measurable_pi_iff.mpr
  intro i
  have hcard : Measurable (fun ξ : Step α X => (S ξ).card) :=
    (measurable_of_countable fun s : Finset α => s.card).comp hS
  have hset : MeasurableSet {ξ : Step α X | i.val < (S ξ).card} := by
    change MeasurableSet ((fun ξ : Step α X => (S ξ).card) ⁻¹' Set.Ioi i.val)
    exact hcard measurableSet_Ioi
  simpa [finiteOffspringStep] using
    (Measurable.ite hset
      (measurable_const : Measurable fun _ : Step α X => some PUnit.unit)
      (measurable_const : Measurable fun _ : Step α X => (none : Option PUnit)))

theorem finiteOffspringStep_childCount
    {α X : Type*} [LinearOrder α] [OrderBot α]
    (S : Step.FiniteSelection α X) (ξ : Step α X)
    (hS : (S ξ).card ≤ 2) :
    (finiteOffspringStep S ξ).childCount = (S ξ).card := by
  classical
  have hsupp : support (finiteOffspringStep S ξ) =
      {i : Fin 2 | i.val < (S ξ).card} := by
    ext i
    change survive (finiteOffspringStep S ξ) i ↔ _
    simp [survive, finiteOffspringStep]
  rw [Step.childCount, hsupp]
  by_cases hzero : (S ξ).card = 0
  · simp [hzero]
  · by_cases hone : (S ξ).card = 1
    · have hsupport : {i : Fin 2 | i.val < (S ξ).card} = {0} := by
        ext i
        fin_cases i <;> simp [hone]
      rw [hsupport]
      simp [hone]
    · have htwo : (S ξ).card = 2 := by omega
      have hsupport : {i : Fin 2 | i.val < (S ξ).card} = Set.univ := by
        rw [htwo]
        ext i
        simp only [Set.mem_ofPred_eq, Set.mem_univ]
        exact ⟨fun _ => trivial, fun _ => i.isLt⟩
      rw [hsupport]
      simp [htwo]

/-- The finite-slot law obtained by applying a measurable selected-child
count to one step. -/
noncomputable def finiteOffspringLaw
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [OrderBot α]
    (ν : ProbabilityMeasure (Step α X))
    (S : Step.FiniteSelection α X) (_hS : Measurable S.select) :
    OffspringConfigurationLaw (Fin 2) PUnit.{1} :=
  ν.map (finiteOffspringStep S)

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
  let f := finiteOffspringStep S
  let μ := finiteOffspringLaw ν S hS
  have hmeas : Measurable f := finiteOffspringStep_measurable S hS
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
    have hcnt := finiteOffspringStep_childCount S ξ (hcapacity ξ)
    have hcap := hcapacity ξ
    by_cases hsplitξ : 2 ≤ (S ξ).card
    · have htwo : (S ξ).card = 2 := by omega
      change ((finiteOffspringStep S ξ).childCount : ℝ≥0∞) = _
      rw [hcnt, htwo]
      norm_num [hsplitξ]
    · have hone : (S ξ).card = 1 := by omega
      change ((finiteOffspringStep S ξ).childCount : ℝ≥0∞) = _
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

/-- The paper's nonempty and supercritical offspring assumptions produce a
finite-slot supercritical Galton--Watson law from the bounded reserve rule.
This theorem applies the finite-slot growth estimate to that law at every
target scale. -/
noncomputable def reserveFiniteOffspringLaw
    {ι α X : Type*} [MeasurableSpace X] [Countable ι]
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (L : StepLaw ι α X) [IsProbabilityMeasure L.raw] (M : ℕ) :
    OffspringConfigurationLaw (Fin 2) PUnit.{1} := by
  let R : Step.FiniteSelection α X :=
    Step.FiniteSelection.firstNBySlotOrder (α := α) (X := X) 2
  have hRmeas : Measurable R.select := by
    simpa [R] using firstTwoBySlotOrder_measurable (α := α) (X := X)
  let S : Step.FiniteSelection α X :=
    reserveSelectionBelowPotential R L.potential (M : ℝ)
  have hSmeas : Measurable S.select := by
    simpa [S] using reserveSelectionBelowPotential_measurable
      R hRmeas L.potential (M : ℝ)
  let ν : ProbabilityMeasure (Step α X) := ⟨L.sorted, inferInstance⟩
  exact finiteOffspringLaw ν S hSmeas

theorem exists_reserveFiniteOffspring_growth_bound
    {ι α X : Type*} [MeasurableSpace X] [Countable ι]
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (L : StepLaw ι α X) [IsProbabilityMeasure L.raw]
    (hnonempty : OffspringConfigurationLaw.HasAtLeastOneChild
      (⟨L.raw, ‹IsProbabilityMeasure L.raw›⟩ : OffspringConfigurationLaw ι X))
    (hsupercritical : OffspringConfigurationLaw.IsSupercritical
      (⟨L.raw, ‹IsProbabilityMeasure L.raw›⟩ : OffspringConfigurationLaw ι X)) :
    ∃ M : ℕ, ∀ N : ℕ, ∀ a : ℝ, 1 ≤ N →
      ((GaltonWatson.law (reserveFiniteOffspringLaw L M) :
        ProbabilityMeasure (Combinatorics.Branching.Process (Fin 2))).toMeasure.real
        {β | (⌊(N : ℝ) ^ a⌋₊ : ℝ) ≤
          generationSizeReal
            ⌈(a * Real.log N + Real.log 2) /
              Real.log ((offspringMean
                (reserveFiniteOffspringLaw L M)).toReal)⌉₊ β}) ≥
        1 / (4 * (1 +
          (offspringSecondFactorialMoment
            (reserveFiniteOffspringLaw L M)).toReal /
            ((offspringMean (reserveFiniteOffspringLaw L M)).toReal *
              ((offspringMean (reserveFiniteOffspringLaw L M)).toReal - 1)))) := by
  obtain ⟨M, hsplit, _hmeas⟩ :=
    exists_nat_cutoff_positive_reserveSplit L hnonempty hsupercritical
  let R : Step.FiniteSelection α X :=
    Step.FiniteSelection.firstNBySlotOrder (α := α) (X := X) 2
  let S : Step.FiniteSelection α X :=
    reserveSelectionBelowPotential R L.potential (M : ℝ)
  let ν : ProbabilityMeasure (Step α X) := ⟨L.sorted, inferInstance⟩
  have hRmeas : Measurable R.select := by
    simpa [R] using firstTwoBySlotOrder_measurable (α := α) (X := X)
  have hRcap : R.IsBoundedBy 2 := by
    simpa [R] using
      (Step.FiniteSelection.firstNBySlotOrder_isBoundedBy
        (α := α) (X := X) 2)
  have hSmeas : Measurable S.select := by
    simpa [S] using reserveSelectionBelowPotential_measurable
      R hRmeas L.potential (M : ℝ)
  let μ : OffspringConfigurationLaw (Fin 2) PUnit.{1} :=
    finiteOffspringLaw ν S hSmeas
  have hScap : ∀ ξ, (S ξ).card ≤ 2 := by
    intro ξ
    exact reserveSelectionBelowPotential_isBoundedBy
      R L.potential (M : ℝ) hRcap ξ
  have hSnonempty : ∀ᵐ ξ ∂(ν : Measure (Step α X)), (S ξ).Nonempty := by
    simpa [ν, S] using reserveSelectionBelowPotential_nonempty_ae
      L hnonempty (M : ℝ)
  have hSsplit :
      0 < (ν : Measure (Step α X)) {ξ | 2 ≤ (S ξ).card} := by
    simpa [ν, S, splitBy] using hsplit
  have hμsupercritical : μ.IsSupercritical :=
    finiteOffspringLaw_isSupercritical ν S hSmeas hScap
      hSnonempty hSsplit
  refine ⟨M, ?_⟩
  intro N a hN
  have hμ : μ = reserveFiniteOffspringLaw L M := by
    simp [μ, reserveFiniteOffspringLaw, R, S, ν]
  rw [← hμ]
  exact GaltonWatson.measure_generation_ge_floor_rpow_of_supercritical_finite_slots
    μ hμsupercritical N a hN

end ProbabilityTheory.BranchingRandomWalk
