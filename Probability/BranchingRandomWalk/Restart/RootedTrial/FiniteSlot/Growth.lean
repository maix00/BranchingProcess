/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Restart.RootedTrial.Reserve.Causal
import Probability.BranchingRandomWalk.Restart.RootedTrial.FiniteSlot.Moments
/-!
# Growth estimates for bounded selected populations

The finite-slot row law and its first two moment recursions apply to the
actual selected population on the pre-sampled tree.  This file turns those
recursions into a fixed-horizon probability bound and then into the complete
observable growth-trial event used by causal reserve candidates.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingProcess
  ProbabilityTheory.BranchingProcess.GaltonWatson

/-- The variance of a finite-slot offspring count is nonnegative. -/
theorem finiteSlotOffspringVarianceReal_nonneg
    (ν : ProbabilityMeasure (Step (Fin 2) PUnit.{1})) :
    0 ≤ finiteSlotOffspringSecondMomentReal ν -
      finiteSlotOffspringMeanReal ν ^ 2 := by
  let X := finiteSlotChildCountReal
  let m := finiteSlotOffspringMeanReal ν
  let q := finiteSlotOffspringSecondMomentReal ν
  have hXmem : MemLp X 2 (ν : Measure _) := by
    apply MemLp.of_bound finiteSlotChildCountReal_measurable.aestronglyMeasurable 2
    filter_upwards [] with ξ
    exact finiteSlotChildCountReal_bound ξ
  have hvar := variance_nonneg X (ν : Measure _)
  rw [variance_eq_sub hXmem] at hvar
  simpa [m, q, X, finiteSlotOffspringMeanReal,
    finiteSlotOffspringSecondMomentReal] using hvar

/-- A binary selected offspring law is supercritical as a real-valued mean
whenever it is almost surely nonempty and splits with positive probability. -/
theorem finiteSlotOffspringMeanReal_gt_one_of_nonempty_and_split
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [OrderBot α]
    (ν : ProbabilityMeasure (Step α X))
    (S : Step.FiniteSelection α X) (hS : Measurable S.select)
    (hcapacity : ∀ ξ, (S ξ).card ≤ 2)
    (hnonempty : ∀ᵐ ξ ∂(ν : Measure (Step α X)), (S ξ).Nonempty)
    (hsplitMeas : MeasurableSet {ξ : Step α X | 2 ≤ (S ξ).card})
    (hsplit : 0 < (ν : Measure (Step α X)) {ξ | 2 ≤ (S ξ).card}) :
    1 < finiteSlotOffspringMeanReal (finiteOffspringLaw ν S hS) := by
  let split : Set (Step α X) := {ξ | 2 ≤ (S ξ).card}
  have hsplitMeas' : MeasurableSet split := by
    simpa [split] using hsplitMeas
  have hmeas : Measurable (finiteOffspringStep S) :=
    finiteOffspringStep_measurable S hS
  have hpointwise : ∀ᵐ ξ ∂(ν : Measure (Step α X)),
      finiteSlotChildCountReal (finiteOffspringStep S ξ) =
        1 + (if ξ ∈ split then 1 else 0) := by
    filter_upwards [hnonempty] with ξ hnonemptyξ
    have hpositive : 0 < (S ξ).card := Finset.card_pos.mpr hnonemptyξ
    have hcap : (S ξ).card ≤ 2 := hcapacity ξ
    have hcount := finiteOffspringStep_childCount S ξ (hcapacity ξ)
    by_cases hξ : ξ ∈ split
    · have htwo : (S ξ).card = 2 := by
        dsimp [split] at hξ
        omega
      have hchild : (finiteOffspringStep S ξ).childCount.toNat = 2 := by
        rw [hcount]
        simp [htwo]
      change ((finiteOffspringStep S ξ).childCount.toNat : ℝ) = _
      rw [hchild]
      norm_num [hξ]
    · have hone : (S ξ).card = 1 := by
        dsimp [split] at hξ
        omega
      have hchild : (finiteOffspringStep S ξ).childCount.toNat = 1 := by
        rw [hcount]
        simp [hone]
      change ((finiteOffspringStep S ξ).childCount.toNat : ℝ) = _
      rw [hchild]
      simp [hξ]
  have hindicator : (fun ξ : Step α X =>
      if ξ ∈ split then (1 : ℝ) else 0) =
        split.indicator (fun _ => (1 : ℝ)) := by
    funext ξ
    by_cases hξ : ξ ∈ split <;> simp [hξ]
  have hintervalIntegrable : Integrable
      (split.indicator (fun _ => (1 : ℝ))) (ν : Measure (Step α X)) :=
    (integrable_indicator_iff hsplitMeas).2 (integrable_const 1)
  have hmeanMap : finiteSlotOffspringMeanReal (finiteOffspringLaw ν S hS) =
      ∫ ξ, finiteSlotChildCountReal (finiteOffspringStep S ξ)
        ∂(ν : Measure (Step α X)) := by
    change (∫ ξ, finiteSlotChildCountReal ξ ∂
        (ν.map (finiteOffspringStep S) : ProbabilityMeasure _)) = _
    rw [ProbabilityMeasure.toMeasure_map]
    exact integral_map hmeas.aemeasurable
      finiteSlotChildCountReal_measurable.aestronglyMeasurable
  have hmeanEq : finiteSlotOffspringMeanReal (finiteOffspringLaw ν S hS) =
      1 + (ν : Measure (Step α X)).real split := by
    rw [hmeanMap]
    calc
      (∫ ξ, finiteSlotChildCountReal (finiteOffspringStep S ξ)
          ∂(ν : Measure (Step α X))) =
        ∫ ξ, 1 + split.indicator (fun _ => (1 : ℝ)) ξ
          ∂(ν : Measure (Step α X)) := by
            apply integral_congr_ae
            filter_upwards [hpointwise] with ξ hξ
            have hi : (if ξ ∈ split then (1 : ℝ) else 0) =
                split.indicator (fun _ => (1 : ℝ)) ξ := by
              by_cases hmem : ξ ∈ split <;> simp [hmem]
            calc
              finiteSlotChildCountReal (finiteOffspringStep S ξ) =
                  1 + (if ξ ∈ split then 1 else 0) := hξ
              _ = 1 + split.indicator (fun _ => (1 : ℝ)) ξ := by rw [hi]
      _ = (∫ _ξ, (1 : ℝ) ∂(ν : Measure (Step α X))) +
          ∫ ξ, split.indicator (fun _ => (1 : ℝ)) ξ
            ∂(ν : Measure (Step α X)) := by
            rw [integral_add (integrable_const 1) hintervalIntegrable]
      _ = 1 + (ν : Measure (Step α X)).real split := by
            have hI : ∫ ξ, split.indicator (fun _ : Step α X => (1 : ℝ)) ξ
                ∂(ν : Measure (Step α X)) = (ν : Measure (Step α X)).real split := by
              simpa [Measure.real] using (integral_indicator_const (1 : ℝ) hsplitMeas')
            rw [hI]
            simp
  have hsplitReal : 0 < (ν : Measure (Step α X)).real split := by
    simpa [split, Measure.real] using
      (ENNReal.toReal_pos_iff.mpr ⟨hsplit, measure_lt_top _ _⟩)
  rw [hmeanEq]
  exact lt_add_of_pos_right 1 hsplitReal

/-- The mean of the actual bounded selected population is the corresponding
power of its one-step finite-slot offspring mean. -/
theorem finiteSlotPopulationSizeReal_integral_eq_pow
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select)
    (hcapacity : ∀ ξ, (S ξ).card ≤ 2) :
    ∀ n, ∫ ω, finiteSlotPopulationSizeReal S ω n ∂stepFieldLaw μ =
      finiteSlotOffspringMeanReal
        (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _)
          S hS) ^ n := by
  let ρ := finiteSlotOffspringMeanReal
    (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS)
  have hzero : ∀ ω, finiteSlotPopulationSizeReal S ω 0 = 1 := by
    intro ω
    rw [finiteSlotPopulationSizeReal, finiteSlotActiveLabels_card_eq_population_card
      S ω hcapacity 0]
    simp [StepSelection.population_zero]
  intro n
  induction n with
  | zero =>
      simp [hzero]
  | succ n ih =>
      rw [finiteSlotPopulationSizeReal_integral_succ_eq
        μ S hS hcapacity n, ih]
      simp [pow_succ, mul_comm]

/-- The second moment of the actual bounded selected population satisfies
the Galton--Watson recursion, with the variance of the finite-slot row law.
-/
theorem finiteSlotPopulationSizeReal_sq_integral_eq_recursion
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select)
    (hcapacity : ∀ ξ, (S ξ).card ≤ 2) :
    let ν := finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _)
      S hS
    let ρ := finiteSlotOffspringMeanReal ν
    let v := finiteSlotOffspringSecondMomentReal ν - ρ ^ 2
    ∀ n, ∫ ω, finiteSlotPopulationSizeReal S ω (n + 1) ^ 2 ∂stepFieldLaw μ =
      ρ ^ 2 * ∫ ω, finiteSlotPopulationSizeReal S ω n ^ 2 ∂stepFieldLaw μ +
        v * ρ ^ n := by
  dsimp only
  let ν := finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS
  let ρ := finiteSlotOffspringMeanReal ν
  let v := finiteSlotOffspringSecondMomentReal ν - ρ ^ 2
  have hmean := finiteSlotPopulationSizeReal_integral_eq_pow μ S hS hcapacity
  intro n
  rw [finiteSlotPopulationSizeReal_sq_integral_succ_eq μ S hS hcapacity n,
    hmean n]

/-- The finite-slot population reaches its power-scale target at the usual
logarithmic horizon with a probability bounded below independently of the
scale.  Only the original offspring mean is used: second moments are finite
because the selected row has at most two children. -/
theorem measure_finiteSlotPopulation_ge_floor_rpow
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select)
    (hcapacity : ∀ ξ, (S ξ).card ≤ 2)
    (hmean : 1 < finiteSlotOffspringMeanReal
      (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS))
    (N : ℕ) (a : ℝ) (hN : 1 ≤ N) :
    (stepFieldLaw μ).real
      {ω | (⌊(N : ℝ) ^ a⌋₊ : ℝ) ≤
        finiteSlotPopulationSizeReal S ω
          ⌈(a * Real.log N + Real.log 2) /
            Real.log (finiteSlotOffspringMeanReal
              (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _)
                S hS))⌉₊} ≥
      1 / (4 * normalizedSecondMomentConstant
        (finiteSlotOffspringMeanReal
          (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS))
        (finiteSlotOffspringSecondMomentReal
          (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS) -
          (finiteSlotOffspringMeanReal
            (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS)) ^ 2)) := by
  let ν := finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS
  let ρ := finiteSlotOffspringMeanReal ν
  let v := finiteSlotOffspringSecondMomentReal ν - ρ ^ 2
  let Z := fun n ω => finiteSlotPopulationSizeReal S ω n
  let m₂ := fun n => ∫ ω, Z n ω ^ 2 ∂stepFieldLaw μ
  have hvar : 0 ≤ v := by
    exact finiteSlotOffspringVarianceReal_nonneg ν
  have hZmeas : ∀ n, Measurable (Z n) := by
    intro n
    exact finiteSlotPopulationSizeReal_measurable S hS hcapacity n
  have hZnonneg : ∀ n, 0 ≤ᵐ[stepFieldLaw μ] Z n := by
    intro n
    exact ae_of_all _ (fun ω => by simp [Z, finiteSlotPopulationSizeReal])
  have hZint : ∀ n, Integrable (Z n) (stepFieldLaw μ) := by
    intro n
    exact finiteSlotPopulationSizeReal_integrable μ S hS hcapacity n
  have hZmem : ∀ n, MemLp (Z n) 2 (stepFieldLaw μ) := by
    intro n
    apply MemLp.of_bound (hZmeas n).aestronglyMeasurable ((2 : ℝ) ^ n)
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (by simp [Z, finiteSlotPopulationSizeReal])]
    exact finiteSlotPopulationSizeReal_bound S hcapacity ω n
  have hmean' : ∀ n, ∫ ω, Z n ω ∂stepFieldLaw μ = ρ ^ n := by
    intro n
    simpa [Z, ν, ρ] using
      finiteSlotPopulationSizeReal_integral_eq_pow μ S hS hcapacity n
  have hm₂zero : m₂ 0 = 1 := by
    have hcard : ∀ ω, (finiteSlotActiveLabels S ω 0).card = 1 := by
      intro ω
      rw [finiteSlotActiveLabels_card_eq_population_card S ω hcapacity 0]
      simp [StepSelection.population_zero]
    have hz : ∀ ω, Z 0 ω = 1 := by
      intro ω
      change ((finiteSlotActiveLabels S ω 0).card : ℝ) = 1
      rw [hcard]
      norm_num
    simp [m₂, hz]
  have hm₂succ : ∀ n, m₂ (n + 1) = ρ ^ 2 * m₂ n + v * ρ ^ n := by
    intro n
    simpa [m₂, Z, ν, ρ, v] using
      finiteSlotPopulationSizeReal_sq_integral_eq_recursion μ S hS hcapacity n
  have hprob := measure_generation_ge_floor_rpow_of_moment_recursion
    (stepFieldLaw μ) ρ v hmean hvar Z m₂ hZmeas hZnonneg hZint hZmem
    hmean' hm₂zero
    (fun n => rfl) hm₂succ N a hN
  simpa [Z, ν, ρ, v] using hprob

/-- If every one-step selected family is nonempty and reproduction is binary,
then the actual population stays positive at every finite age. -/
theorem population_nonempty_of_all_selected_marks_nonempty
    {α X : Type*} [LinearOrder α] [OrderBot α]
    (S : Step.FiniteSelection α X) (ω : Mark α (Step α X))
    (hmarks : ∀ u : TreeNode α, (S (ω u)).Nonempty) :
    ∀ n, (StepSelection.population S n ω).Nonempty := by
  classical
  intro n
  induction n with
  | zero => simp [StepSelection.population]
  | succ n ih =>
      obtain ⟨p, hp⟩ := ih
      have hdepth := StepSelection.population_depth S ω n p hp
      obtain ⟨i, hi⟩ := hmarks p
      refine ⟨p ++ [i], ?_⟩
      rw [StepSelection.population_succ]
      apply (StepSelection.mem_grow_iff S
        (StepSelection.population S n ω) (frontierMarks n ω) (p ++ [i])).2
      refine ⟨p, hp, i, ?_, rfl⟩
      simpa [frontierMarks, hdepth] using hi

/-- For the binary selector, a power-scale endpoint event is a complete
growth trial: earlier populations are positive and strictly below the
endpoint capacity. -/
theorem growthTrialSuccess_of_population_ge_lower
    {α X : Type*} [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α]
    (S : Step.FiniteSelection α X) (hcapacity : ∀ ξ, (S ξ).card ≤ 2)
    (ω : Mark α (Step α X))
    (hmarks : ∀ u : TreeNode α, (S (ω u)).Nonempty)
    (lower duration upper : ℕ) (hupper : 2 ^ duration ≤ upper)
    (hlower : lower ≤ (StepSelection.population S duration ω).card) :
    growthTrialSuccess S lower upper duration ω := by
  classical
  have hpop : ∀ n, (StepSelection.population S n ω).Nonempty :=
    population_nonempty_of_all_selected_marks_nonempty S ω hmarks
  have hcardBound : ∀ n, (StepSelection.population S n ω).card ≤ 2 ^ n := by
    intro n
    exact StepSelection.population_card_le S 2 hcapacity ω n
  have hendpointUpper :
      (StepSelection.population S duration ω).card ≤ upper :=
    (hcardBound duration).trans hupper
  refine ⟨hlower, hendpointUpper, ?_⟩
  intro k
  have hage : k.val + 1 < duration := by omega
  have hpow : 2 ^ (k.val + 1) < 2 ^ duration :=
    Nat.pow_lt_pow_right (by decide) hage
  have hsmall :
      (StepSelection.population S (k.val + 1) ω).card < upper := by
    exact (hcardBound (k.val + 1)).trans_lt (hpow.trans_le hupper)
  exact ⟨Finset.card_pos.mpr (hpop (k.val + 1)), hsmall⟩

/-- The finite-slot second-moment bound applies to the complete growth-trial
event on the actual pre-sampled selected population. The endpoint estimate is
lifted using the almost-sure nonemptiness of every selected one-step family. -/
theorem measure_finiteSlotGrowthTrialSuccess_ge_floor_rpow
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select)
    (hcapacity : ∀ ξ, (S ξ).card ≤ 2)
    (hnonempty : ∀ᵐ ξ ∂μ, (S ξ).Nonempty)
    (hmean : 1 < finiteSlotOffspringMeanReal
      (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS))
    (N : ℕ) (a : ℝ) (hN : 1 ≤ N) :
    (stepFieldLaw μ).real
      {ω | growthTrialSuccess S (⌊(N : ℝ) ^ a⌋₊)
        (2 ^ ⌈(a * Real.log N + Real.log 2) /
          Real.log (finiteSlotOffspringMeanReal
            (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS))⌉₊)
        ⌈(a * Real.log N + Real.log 2) /
          Real.log (finiteSlotOffspringMeanReal
            (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS))⌉₊ ω} ≥
      1 / (4 * normalizedSecondMomentConstant
        (finiteSlotOffspringMeanReal
          (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS))
        (finiteSlotOffspringSecondMomentReal
          (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS) -
          (finiteSlotOffspringMeanReal
            (finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS)) ^ 2)) := by
  let ν := finiteOffspringLaw (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS
  let ρ := finiteSlotOffspringMeanReal ν
  let v := finiteSlotOffspringSecondMomentReal ν - ρ ^ 2
  let duration := ⌈(a * Real.log N + Real.log 2) / Real.log ρ⌉₊
  let lower := ⌊(N : ℝ) ^ a⌋₊
  let upper := 2 ^ duration
  let endpoint : Set (Mark α (Step α X)) :=
    {ω | (lower : ℝ) ≤ finiteSlotPopulationSizeReal S ω duration}
  let success : Set (Mark α (Step α X)) :=
    {ω | growthTrialSuccess S lower upper duration ω}
  have hsplitMeas : MeasurableSet {ξ : Step α X | (S ξ).Nonempty} := by
    have hcard : Measurable (fun ξ : Step α X => (S ξ).card) :=
      (measurable_of_countable fun t : Finset α => t.card).comp hS
    have heq : {ξ : Step α X | (S ξ).Nonempty} =
        {ξ | 0 < (S ξ).card} := by
      ext ξ
      simp
    rw [heq]
    exact hcard measurableSet_Ioi
  have hsplitOne : μ {ξ : Step α X | (S ξ).Nonempty} = 1 := by
    have hset : {ξ : Step α X | (S ξ).Nonempty} =ᵐ[μ] Set.univ := by
      filter_upwards [hnonempty] with ξ hξ
      simp [hξ]
    exact (measure_congr hset).trans measure_univ
  have hall : ∀ᵐ ω ∂stepFieldLaw μ,
      ∀ u : TreeNode α, (S (ω u)).Nonempty := by
    apply ae_all_iff.2
    intro u
    have heval : Measurable (fun ω : Mark α (Step α X) => ω u) :=
      measurable_pi_apply u
    apply (ae_mem_iff_measure_eq (heval hsplitMeas).nullMeasurableSet).2
    rw [← Measure.map_apply heval hsplitMeas,
      stepFieldLaw_coordinate μ u, hsplitOne]
    simp
  have hendpoint := measure_finiteSlotPopulation_ge_floor_rpow
    μ S hS hcapacity hmean N a hN
  have hsuccess_mono : (stepFieldLaw μ).real endpoint ≤
      (stepFieldLaw μ).real success := by
    have hsub : endpoint ≤ᵐ[stepFieldLaw μ] success := by
      filter_upwards [hall] with ω hmarks
      intro hendpoint
      have hcard : lower ≤ (StepSelection.population S duration ω).card := by
        have hendpoint' := hendpoint
        change (lower : ℝ) ≤
          ((finiteSlotActiveLabels S ω duration).card : ℝ) at hendpoint'
        rw [finiteSlotActiveLabels_card_eq_population_card S ω hcapacity duration]
          at hendpoint'
        exact_mod_cast hendpoint'
      exact growthTrialSuccess_of_population_ge_lower
        S hcapacity ω hmarks lower duration upper (by rfl) hcard
    change (stepFieldLaw μ endpoint).toReal ≤ (stepFieldLaw μ success).toReal
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  change 1 / (4 * normalizedSecondMomentConstant ρ v) ≤
    (stepFieldLaw μ).real success
  calc
    1 / (4 * normalizedSecondMomentConstant ρ v) ≤
        (stepFieldLaw μ).real endpoint := by
      simpa [endpoint, duration, lower, ν, ρ, v] using hendpoint
    _ ≤ (stepFieldLaw μ).real success := hsuccess_mono

/-- Under the offspring assumptions, a finite reserve cutoff gives a
supercritical binary selector. Its actual selected population has a uniformly
positive probability of satisfying the complete logarithmic growth-trial
conditions, without a moment assumption on the original offspring law. -/
theorem exists_reserveGrowthTrialSuccess_probability_lower_bound
    {ι α X : Type*} [MeasurableSpace X] [Countable ι]
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (L : StepLaw ι α X) [IsProbabilityMeasure L.raw]
    (hnonempty : OffspringConfigurationLaw.HasAtLeastOneChild
      (⟨L.raw, ‹IsProbabilityMeasure L.raw›⟩ : OffspringConfigurationLaw ι X))
    (hsupercritical : OffspringConfigurationLaw.IsSupercritical
      (⟨L.raw, ‹IsProbabilityMeasure L.raw›⟩ : OffspringConfigurationLaw ι X)) :
    ∃ M : ℕ, ∀ N : ℕ, ∀ a : ℝ, 1 ≤ N →
      let S : Step.FiniteSelection α X :=
        reserveSelectionBelowPotential
          (Step.FiniteSelection.firstNBySlotOrder (α := α) (X := X) 2)
          L.potential (M : ℝ)
      let law := reserveFiniteOffspringLaw L M
      let ρ := finiteSlotOffspringMeanReal law
      let duration := ⌈(a * Real.log N + Real.log 2) / Real.log ρ⌉₊
      let variance := finiteSlotOffspringSecondMomentReal law - ρ ^ 2
      (stepFieldLaw L.sorted).real
        {ω | growthTrialSuccess S (⌊(N : ℝ) ^ a⌋₊)
          (2 ^ duration) duration ω} ≥
        1 / (4 * normalizedSecondMomentConstant ρ variance) := by
  obtain ⟨M, hsplit, _hsplitMeas⟩ :=
    exists_nat_cutoff_positive_reserveSplit L hnonempty hsupercritical
  refine ⟨M, ?_⟩
  intro N a hN
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
  have hScap : ∀ ξ, (S ξ).card ≤ 2 := by
    intro ξ
    exact reserveSelectionBelowPotential_isBoundedBy
      R L.potential (M : ℝ) hRcap ξ
  have hSnonempty : ∀ᵐ ξ ∂(ν : Measure (Step α X)), (S ξ).Nonempty := by
    simpa [ν, S] using reserveSelectionBelowPotential_nonempty_ae
      L hnonempty (M : ℝ)
  have hSsplit : 0 < (ν : Measure (Step α X))
      {ξ | 2 ≤ (S ξ).card} := by
    simpa [ν, S, splitBy] using hsplit
  have hSsplitMeas : MeasurableSet {ξ : Step α X | 2 ≤ (S ξ).card} := by
    simpa [splitBy] using splitBy_measurable S hSmeas
  have hmean : 1 < finiteSlotOffspringMeanReal
      (finiteOffspringLaw ν S hSmeas) :=
    finiteSlotOffspringMeanReal_gt_one_of_nonempty_and_split ν S hSmeas
      hScap hSnonempty hSsplitMeas hSsplit
  have hbound := measure_finiteSlotGrowthTrialSuccess_ge_floor_rpow
    L.sorted S hSmeas hScap hSnonempty hmean N a hN
  have hlaw : reserveFiniteOffspringLaw L M =
      finiteOffspringLaw ν S hSmeas := by
    simp [reserveFiniteOffspringLaw, R, S, ν]
  simpa [R, S, ν, hlaw] using hbound

/-- A reserve candidate's growth trial is successful whenever its observable
split is enabled, almost surely, if its binary horizon fits under the cap.
All coordinates belong to the same pre-sampled field; the proof does not
resample a trial after inspecting another trial's outcome. -/
theorem selectedReserveSpineCandidateSuccessEvent_of_binary_horizon_ae
    {Root α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [LinearOrder α] [LocallyFiniteOrder α]
    [OrderBot α] [NoMaxOrder α] [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (R growth : Step.FiniteSelection α X) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select)
    (hnonempty : ∀ᵐ ξ ∂μ, (growth ξ).Nonempty)
    (hcapacity : ∀ ξ, (growth ξ).card ≤ 2)
    (upper duration : ℕ) (hupper : 2 ^ duration ≤ upper)
    (r : Root) (k : ℕ) :
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root) μ,
      (selectedReserveSpineAlive R r k field ∧
        field r (selectedReserveSpinePath R r k field) ∈ splitBy R) →
      field ∈ selectedReserveSpineCandidateSuccessEvent R growth hR
        1 upper duration r k := by
  classical
  let split : Set (Step α X) := {ξ | (growth ξ).Nonempty}
  have hsplit : MeasurableSet split := by
    change MeasurableSet {ξ | (growth ξ).Nonempty}
    have hcard : Measurable (fun ξ : Step α X => (growth ξ).card) :=
      (measurable_of_countable fun s : Finset α => s.card).comp hgrowth
    have heq : {ξ | (growth ξ).Nonempty} =
        {ξ | 0 < (growth ξ).card} := by
      ext ξ
      simp
    rw [heq]
    exact hcard measurableSet_Ioi
  have hsplitOne : μ split = 1 := by
    have hset : split =ᵐ[μ] Set.univ := by
      filter_upwards [hnonempty] with ξ hξ
      simp [split, hξ]
    exact (measure_congr hset).trans (measure_univ)
  have hall : ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root) μ,
      ∀ u : TreeNode α, (growth (field r u)).Nonempty := by
    apply ae_all_iff.2
    intro u
    have heval : Measurable
        (fun field : RootIndexed.StepField Root α X => field r u) :=
      (measurable_pi_apply u).comp (measurable_pi_apply r)
    apply (ae_mem_iff_measure_eq (heval hsplit).nullMeasurableSet).2
    rw [← Measure.map_apply heval hsplit,
      RootIndexed.stepFieldLaw_coordinate_marginal μ r u, hsplitOne]
    simp
  filter_upwards [hall] with field hmarks
  intro hsplitCandidate
  rcases hsplitCandidate with ⟨halive, hsplitCandidate⟩
  change selectedReserveSpineAlive R r k field ∧
    field r (selectedReserveSpinePath R r k field) ∈ splitBy R ∧
    growthTrialSuccess growth 1 upper duration
      (fun v => field r
        (((selectedReserveSpineLineages R hR).firstChildRootAt
          R r PUnit.unit (k + 1) field).2 ++ v))
  refine ⟨halive, hsplitCandidate, ?_⟩
  refine growthTrialSuccess_of_population_ge_lower
    growth hcapacity
    (fun v => field r
      (((selectedReserveSpineLineages R hR).firstChildRootAt
        R r PUnit.unit (k + 1) field).2 ++ v))
    (fun v => hmarks (((selectedReserveSpineLineages R hR).firstChildRootAt
      R r PUnit.unit (k + 1) field).2 ++ v))
    1 duration upper hupper ?_
  let trial : Mark α (Step α X) := fun v => field r
    (((selectedReserveSpineLineages R hR).firstChildRootAt
      R r PUnit.unit (k + 1) field).2 ++ v)
  have hpop : (StepSelection.population growth duration trial).Nonempty :=
    population_nonempty_of_all_selected_marks_nonempty growth trial
      (fun v => hmarks (((selectedReserveSpineLineages R hR).firstChildRootAt
        R r PUnit.unit (k + 1) field).2 ++ v)) duration
  exact Finset.card_pos.mpr hpop

end ProbabilityTheory.BranchingRandomWalk
