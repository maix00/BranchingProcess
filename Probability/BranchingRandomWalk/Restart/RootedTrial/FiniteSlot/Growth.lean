/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Restart.RootedTrial.FiniteSlot.Moments
import Probability.MeasureTheory.Moments.SecondMomentGrowth
import Probability.BranchingRandomWalk.Restart.Trial.Basic
import Probability.BranchingProcess.Offspring.FieldLaw
/-!
# Growth estimates for bounded selected populations

The finite-slot row law and its first two moment recursions apply to the
actual selected population on the pre-sampled tree. This file turns those
recursions into fixed-horizon probability bounds.

## Public declarations

* `finiteSlotOffspringMeanReal_gt_one_of_nonempty_and_split` converts the
  supercriticality of the encoded offspring law into the real-valued mean
  hypothesis used by the population moment recursion, under almost-sure
  nonemptiness and positive split probability.
* `measure_finiteSlotPopulation_ge_floor_rpow` gives a scale-uniform lower
  bound for the event that the selected population reaches `⌊N ^ a⌋₊` by its
  logarithmic horizon:
  `P(Z_⌈(a log N + log 2)/log ρ⌉₊ ≥ ⌊N ^ a⌋₊) ≥ 1/(4 K(ρ,v))`.
* `measure_finiteSlotGrowthTrialSuccess_ge_floor_rpow` gives the same lower
  bound for the full trial event, including nonempty intermediate generations
  and the endpoint upper cap `2 ^ duration`.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingProcess

/-- The variance of a finite-slot offspring count is nonnegative. -/
private theorem finiteSlotOffspringVarianceReal_nonneg
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
    (hsplit : 0 < (ν : Measure (Step α X)) {ξ | 2 ≤ (S ξ).card}) :
    1 < finiteSlotOffspringMeanReal (finiteOffspringLaw ν S hS) := by
  let μ := finiteOffspringLaw ν S hS
  have hsuper : μ.IsSupercritical :=
    finiteOffspringLaw_isSupercritical ν S hS hcapacity hnonempty hsplit
  have hcount (ξ : Step (Fin 2) PUnit.{1}) : ξ.childCount ≤ (2 : ℕ∞) := by
    rw [Step.childCount]
    calc
      (support ξ).encard ≤ ENat.card (Fin 2) := Set.encard_le_card
      _ = (2 : ℕ∞) := by simp
  have htop : μ.expectedChildCount < ∞ := by
    rw [ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.expectedChildCount,
      ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.childCountLaw_toMeasure]
    rw [lintegral_map (by fun_prop : Measurable (fun n : ℕ∞ => (n : ℝ≥0∞)))
      Step.childCount_measurable]
    calc
      ∫⁻ ξ : Step (Fin 2) PUnit.{1}, (ξ.childCount : ℝ≥0∞)
          ∂(μ : Measure _) ≤
        ∫⁻ _ξ : Step (Fin 2) PUnit.{1}, (2 : ℝ≥0∞) ∂(μ : Measure _) := by
          apply lintegral_mono
          intro ξ
          change (ξ.childCount : ℝ≥0∞) ≤ (2 : ℝ≥0∞)
          have hnat : ξ.childCount.toNat ≤ 2 :=
            ENat.toNat_le_of_le_natCast (hcount ξ)
          have htop : ξ.childCount ≠ ⊤ := by
            exact ne_top_of_lt (lt_of_le_of_lt (hcount ξ) (ENat.natCast_lt_top 2))
          rw [← ENat.natCast_toNat htop]
          exact_mod_cast hnat
      _ = 2 := by simp
      _ < ∞ := ENNReal.ofNat_lt_top
  have hmeanToReal : 1 < μ.expectedChildCount.toReal :=
    (ENNReal.toReal_lt_toReal ENNReal.one_ne_top htop.ne).2 hsuper
  rw [show finiteSlotOffspringMeanReal μ = μ.expectedChildCount.toReal by
    exact finiteSlotOffspringMeanReal_eq_expectedChildCount_toReal μ]
  exact hmeanToReal

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
    (offspringFieldLaw μ).real
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
  let m₂ := fun n => ∫ ω, Z n ω ^ 2 ∂offspringFieldLaw μ
  have hvar : 0 ≤ v := by
    exact finiteSlotOffspringVarianceReal_nonneg ν
  have hZmeas : ∀ n, Measurable (Z n) := by
    intro n
    exact finiteSlotPopulationSizeReal_measurable S hS hcapacity n
  have hZnonneg : ∀ n, 0 ≤ᵐ[offspringFieldLaw μ] Z n := by
    intro n
    exact ae_of_all _ (fun ω => by simp [Z, finiteSlotPopulationSizeReal])
  have hZint : ∀ n, Integrable (Z n) (offspringFieldLaw μ) := by
    intro n
    exact finiteSlotPopulationSizeReal_integrable μ S hS hcapacity n
  have hZmem : ∀ n, MemLp (Z n) 2 (offspringFieldLaw μ) := by
    intro n
    apply MemLp.of_bound (hZmeas n).aestronglyMeasurable ((2 : ℝ) ^ n)
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (by simp [Z, finiteSlotPopulationSizeReal])]
    exact finiteSlotPopulationSizeReal_bound S hcapacity ω n
  have hmean' : ∀ n, ∫ ω, Z n ω ∂offspringFieldLaw μ = ρ ^ n := by
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
  have hprob := measure_ge_floor_rpow_of_moment_recursion
    (offspringFieldLaw μ) ρ v hmean hvar Z m₂ hZmeas hZnonneg hZint hZmem
    hmean' hm₂zero
    (fun n => rfl) hm₂succ N a hN
  simpa [Z, ν, ρ, v] using hprob

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
    (offspringFieldLaw μ).real
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
  have hall : ∀ᵐ ω ∂offspringFieldLaw μ,
      ∀ u : TreeNode α, (S (ω u)).Nonempty := by
    apply ae_all_iff.2
    intro u
    have heval : Measurable (fun ω : Mark α (Step α X) => ω u) :=
      measurable_pi_apply u
    apply (ae_mem_iff_measure_eq (heval hsplitMeas).nullMeasurableSet).2
    rw [← Measure.map_apply heval hsplitMeas,
      offspringFieldLaw_coordinate μ u, hsplitOne]
    simp
  have hendpoint := measure_finiteSlotPopulation_ge_floor_rpow
    μ S hS hcapacity hmean N a hN
  have hsuccess_mono : (offspringFieldLaw μ).real endpoint ≤
      (offspringFieldLaw μ).real success := by
    have hsub : endpoint ≤ᵐ[offspringFieldLaw μ] success := by
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
    change (offspringFieldLaw μ endpoint).toReal ≤ (offspringFieldLaw μ success).toReal
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)
  change 1 / (4 * normalizedSecondMomentConstant ρ v) ≤
    (offspringFieldLaw μ).real success
  calc
    1 / (4 * normalizedSecondMomentConstant ρ v) ≤
        (offspringFieldLaw μ).real endpoint := by
      simpa [endpoint, duration, lower, ν, ρ, v] using hendpoint
    _ ≤ (offspringFieldLaw μ).real success := hsuccess_mono


end ProbabilityTheory.BranchingRandomWalk
