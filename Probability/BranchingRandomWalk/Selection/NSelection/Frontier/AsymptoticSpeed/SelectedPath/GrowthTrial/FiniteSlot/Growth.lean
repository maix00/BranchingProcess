/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.FiniteSlot.Moments
public import Probability.BranchingRandomWalk.Step.Selection.BinaryOffspringLaw
public import MeasureTheory.BranchingWalk.Step.Selection.Potential
public import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.Basic
public import Probability.BranchingProcess.Offspring.FieldLaw
/-!
# Growth estimates for bounded selected populations

The finite-slot row law and its first two moment recursions apply to the
actual selected population on the pre-sampled tree. This file turns those
recursions into a bound on reaching capacity by a fixed horizon.

## Public declarations

* `finiteSlotOffspringVarianceReal_nonneg`: for the encoded binary offspring
  law, $\mathbb E[X^2]-(\mathbb E[X])^2\ge0$.
* `finiteSlotOffspringMeanReal_gt_one_of_nonempty_and_split` converts the
  supercriticality of the encoded offspring law into the real-valued mean
  hypothesis used by the population moment recursion, under almost-sure
  nonemptiness and positive split probability.
* `measure_selects_two_pos_of_binaryOffspringMean_gt_one`: mean $>1$
  for a binary selector implies $\mathbb P(\#S=2)>0$.
* `exists_nat_cutoff_binaryOffspringMean_gt_one`: if $\rho>1$, filtering
  all retained marks at a large enough common cutoff preserves mean $>1$.
* `measure_finiteSlotPopulation_hits_capacity_le`: if $K>0$, then
  $P(\exists j\le d,\ Z_j\ge K)\le K^{-1}\sum_{j=0}^{d}\rho^j$.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.FiniteSlot

open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial
open Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingProcess

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
    (hsplit : 0 < (ν : Measure (Step α X)) {ξ | 2 ≤ (S ξ).card}) :
    1 < finiteSlotOffspringMeanReal (ProbabilityTheory.BranchingRandomWalk.Selection.Stepwise.binaryOffspringLaw ν S hS) := by
  let μ := ProbabilityTheory.BranchingRandomWalk.Selection.Stepwise.binaryOffspringLaw ν S hS
  have hsuper : μ.IsSupercritical :=
    ProbabilityTheory.BranchingRandomWalk.Selection.Stepwise.binaryOffspringLaw_isSupercritical ν S hS hcapacity hnonempty hsplit
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

private lemma binaryOffspringMean_eq_integral_card
    {α X : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace X] [LinearOrder α] [OrderBot α]
    (ν : ProbabilityMeasure (Step α X))
    (S : Step.FiniteSelection α X) (hS : Measurable S.select)
    (hcap : S.IsBoundedBy 2) :
    finiteSlotOffspringMeanReal (Selection.Stepwise.binaryOffspringLaw ν S hS) =
      ∫ ξ, ((S ξ).card : ℝ) ∂(ν : Measure _) := by
  rw [finiteSlotOffspringMeanReal, Selection.Stepwise.binaryOffspringLaw,
    ProbabilityMeasure.toMeasure_map,
    integral_map (S.binaryOffspringStep_measurable hS).aemeasurable
      finiteSlotChildCountReal_measurable.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with ξ
  change ((((S.binaryOffspringStep ξ).childCount.toNat : ℕ) : ℝ)) = _
  rw [S.binaryOffspringStep_childCount ξ (hcap ξ)]
  simp

/-- An encoded binary offspring law with mean greater than one selects
two children on an event of positive probability, allowing extinction. -/
theorem measure_selects_two_pos_of_binaryOffspringMean_gt_one
    {α X : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace X] [LinearOrder α] [OrderBot α]
    (ν : ProbabilityMeasure (Step α X))
    (S : Step.FiniteSelection α X) (hS : Measurable S.select)
    (hcap : S.IsBoundedBy 2)
    (hmean : 1 < finiteSlotOffspringMeanReal (Selection.Stepwise.binaryOffspringLaw ν S hS)) :
    0 < (ν : Measure _) {ξ | 2 ≤ (S ξ).card} := by
  by_contra! hzero
  have hsmall : ∀ᵐ ξ ∂(ν : Measure _), (S ξ).card ≤ 1 := by
    have hnull : ∀ᵐ ξ ∂(ν : Measure _), ¬ 2 ≤ (S ξ).card :=
      ae_iff.mpr (by simpa only [not_not] using le_antisymm hzero zero_le)
    exact hnull.mono fun _ h => by omega
  have hcard : Measurable (fun ξ => ((S ξ).card : ℝ)) :=
    (measurable_of_countable fun f : Finset α => (f.card : ℝ)).comp hS
  have hint : Integrable (fun ξ => ((S ξ).card : ℝ)) (ν : Measure _) := by
    refine (integrable_const (2 : ℝ)).mono' hcard.aestronglyMeasurable ?_
    exact ae_of_all _ fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact_mod_cast hcap ξ
  rw [binaryOffspringMean_eq_integral_card ν S hS hcap] at hmean
  apply hmean.not_ge
  have hle : ∀ᵐ ξ ∂(ν : Measure _), ((S ξ).card : ℝ) ≤ 1 :=
    hsmall.mono fun _ h => by exact_mod_cast h
  calc
    (∫ ξ, ((S ξ).card : ℝ) ∂(ν : Measure _)) ≤ ∫ _ξ : Step α X, (1 : ℝ) ∂(ν : Measure _) :=
      integral_mono_ae hint (integrable_const _) hle
    _ = 1 := by simp

/-- A supercritical finite selector remains supercritical after imposing
a sufficiently large common cutoff on every retained displacement. -/
theorem exists_nat_cutoff_binaryOffspringMean_gt_one
    {α X : Type*} [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace X] [LinearOrder α] [OrderBot α]
    (ν : ProbabilityMeasure (Step α X))
    (S : Step.FiniteSelection α X) (hS : Measurable S.select)
    (hcap : S.IsBoundedBy 2) (φ : Potential X)
    (hmean : 1 < finiteSlotOffspringMeanReal
      (Selection.Stepwise.binaryOffspringLaw ν S hS)) :
    ∃ M : ℕ, 1 < finiteSlotOffspringMeanReal (Selection.Stepwise.binaryOffspringLaw ν
      (S.belowPotential φ (M : ℝ)) (S.belowPotential_measurable hS φ (M : ℝ))) := by
  classical
  let R := fun M : ℕ => S.belowPotential φ (M : ℝ)
  let count := fun (R' : Step.FiniteSelection α X) ξ => ((R' ξ).card : ℝ)
  have hsub (M : ℕ) (ξ : Step α X) : R M ξ ⊆ S ξ := by
    intro i hi
    exact ((Step.FiniteSelection.mem_filter S _ ξ i).mp hi).1
  have hcapR (M : ℕ) : (R M).IsBoundedBy 2 := fun ξ =>
    (Finset.card_le_card (hsub M ξ)).trans (hcap ξ)
  have hmeas (M : ℕ) : Measurable (count (R M)) :=
    (measurable_of_countable fun f : Finset α => (f.card : ℝ)).comp
      (S.belowPotential_measurable hS φ (M : ℝ))
  have hlim : Tendsto (fun M => ∫ ξ, count (R M) ξ ∂(ν : Measure _)) atTop
      (𝓝 (∫ ξ, count S ξ ∂(ν : Measure _))) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (2 : ℝ))
      (fun M => (hmeas M).aestronglyMeasurable) (integrable_const _)
    · intro M
      exact ae_of_all _ fun ξ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ count (R M) ξ)]
        change (((R M ξ).card : ℕ) : ℝ) ≤ 2
        exact_mod_cast hcapR M ξ
    · apply ae_of_all
      intro ξ
      have hEq : (fun M => count (R M) ξ) =ᶠ[atTop] fun _ => count S ξ := by
        let M₀ := (S ξ).sup fun i => ⌈ξ.potentialValue' φ i⌉₊
        filter_upwards [eventually_ge_atTop M₀] with M hM
        have hset : R M ξ = S ξ := by
          refine Finset.Subset.antisymm (hsub M ξ) ?_
          intro i hi
          apply (Step.FiniteSelection.mem_filter S _ ξ i).mpr
          refine ⟨hi, (Nat.le_ceil _).trans ?_⟩
          exact_mod_cast (Finset.le_sup (f := fun i => ⌈ξ.potentialValue' φ i⌉₊) hi).trans hM
        change ((R M ξ).card : ℝ) = _
        rw [hset]
      exact tendsto_const_nhds.congr' hEq.symm
  have hlarge : ∀ᶠ M : ℕ in atTop, 1 < ∫ ξ, count (R M) ξ ∂(ν : Measure _) := by
    rw [binaryOffspringMean_eq_integral_card ν S hS hcap] at hmean
    exact hlim (Ioi_mem_nhds hmean)
  obtain ⟨M, hM⟩ := hlarge.exists
  refine ⟨M, ?_⟩
  rw [binaryOffspringMean_eq_integral_card ν (R M) (S.belowPotential_measurable hS φ M) (hcapR M)]
  exact hM

/-- Markov's inequality at each generation bounds the probability that a finite
trial reaches its capacity by age `duration`. -/
theorem measure_finiteSlotPopulation_hits_capacity_le
    {α X : Type*} [Countable α] [MeasurableSpace α]
    [MeasurableSingletonClass α] [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    (S : Step.FiniteSelection α X) (hS : Measurable S.select)
    (hcap : S.IsBoundedBy 2) (duration : ℕ) {capacity : ℝ} (hcapacity : 0 < capacity) :
    let ρ := finiteSlotOffspringMeanReal
      (Selection.Stepwise.binaryOffspringLaw
        (⟨μ, inferInstance⟩ : ProbabilityMeasure _) S hS)
    (offspringFieldLaw μ).real
      {ω | ∃ j ≤ duration, capacity ≤ finiteSlotPopulationSizeReal S ω j} ≤
      (∑ j ∈ Finset.range (duration + 1), ρ ^ j) / capacity := by
  intro ρ
  let P := offspringFieldLaw μ
  let hit (j : ℕ) : Set (Mark α (Step α X)) :=
    {ω | capacity ≤ finiteSlotPopulationSizeReal S ω j}
  have hset : {ω | ∃ j ≤ duration, capacity ≤ finiteSlotPopulationSizeReal S ω j} =
      ⋃ j ∈ Finset.range (duration + 1), hit j := by
    ext ω
    simp [hit]
  rw [hset]
  refine (measureReal_biUnion_finset_le _ hit).trans ?_
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun j _ => ?_
  apply (le_div_iff₀ hcapacity).2
  rw [mul_comm, ← finiteSlotPopulationSizeReal_integral_eq_pow μ S hS hcap j]
  exact mul_meas_ge_le_integral_of_nonneg
    (ae_of_all P fun ω => by
      change 0 ≤ ((finiteSlotActiveLabels S ω j).card : ℝ)
      positivity)
    (finiteSlotPopulationSizeReal_integrable μ S hS hcap j) capacity


end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.GrowthTrial.FiniteSlot

end
