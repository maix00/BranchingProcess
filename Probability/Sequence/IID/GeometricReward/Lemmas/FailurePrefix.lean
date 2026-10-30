/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.Sequence.IID.GeometricReward.Definitions
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.Independence.Integration

/-!
# Failure-prefix factorization for geometric trial rewards

## Internal proof declarations

- `indep_geometricFailurePrefix_current` derives independence between the current trial reward
  $R(X_n)$ and the event that all preceding trials missed $B$.
- `integral_geometricPrefixRewardTerm` computes the one-term expectation as
  $\left(\int R\,d\nu\right)\nu(B^c)^n$ under an IID sequence with common law $\nu$.

These calculations support the complete reward identities in
`Probability.Sequence.IID.GeometricReward.FirstMoment`; they are kept here because they are proof
steps specific to that derivation.
They use Mathlib's `iIndepFun.indepFun_finset`, `IndepFun.integral_fun_mul_eq_mul_integral`, and `iIndepFun.measure_inter_preimage_eq_mul` interfaces.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace ProbabilityTheory

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

lemma indep_geometricFailurePrefix_current
    (μ : Measure Ω) (X : ℕ → Ω → α)
    (hX : ∀ i, Measurable (X i)) (hXi : iIndepFun X μ)
    (B : Set α) (hB : MeasurableSet B) (R : α → ℝ) (hR : Measurable R)
    (n : ℕ) :
    IndepFun (fun ω => R (X n ω))
      ((geometricFailurePrefix X B n).indicator (fun _ => (1 : ℝ))) μ := by
  classical
  let past : Finset ℕ := Finset.range n
  let current : Finset ℕ := {n}
  let pastTuple : Ω → (∀ i : past, α) := fun ω i => X i.1 ω
  let currentTuple : Ω → (∀ i : current, α) := fun ω i => X i.1 ω
  let pastGood : Set (∀ i : past, α) := {x | ∀ i, x i ∉ B}
  let pastGoodIndicator : (∀ i : past, α) → ℝ :=
    pastGood.indicator (fun _ => (1 : ℝ))
  have hnCurrent : n ∈ current := by simp [current]
  let currentValue : (∀ i : current, α) → α :=
    fun x => x (⟨n, hnCurrent⟩ : current)
  have hdisj : Disjoint past current := by
    rw [Finset.disjoint_singleton_right]
    simp [past, Finset.mem_range]
  have htuple := hXi.indepFun_finset past current hdisj hX
  have hpastGood : MeasurableSet pastGood := by
    rw [show pastGood = ⋂ i : past,
        {v : (∀ j : past, α) | v i ∈ Bᶜ} by
      ext v
      simp [pastGood]]
    exact MeasurableSet.iInter fun i =>
      MeasurableSet.preimage hB.compl (measurable_pi_apply i)
  have hpastGoodMeas : Measurable pastGoodIndicator :=
    measurable_const.indicator hpastGood
  have hcurrentMeas : Measurable (R ∘ currentValue) :=
    hR.comp (measurable_pi_apply (⟨n, hnCurrent⟩ : ↥current))
  have hcomp := htuple.comp hpastGoodMeas hcurrentMeas
  have hpastEq :
      (pastGoodIndicator ∘ pastTuple) =
        (geometricFailurePrefix X B n).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    have hmem : pastTuple ω ∈ pastGood ↔
        ω ∈ geometricFailurePrefix X B n := by
      simp [pastGood, pastTuple, geometricFailurePrefix, past, Finset.mem_range]
    by_cases hω : ω ∈ geometricFailurePrefix X B n
    · have hpast : pastTuple ω ∈ pastGood := hmem.mpr hω
      simp [pastGoodIndicator, hω, hpast]
    · have hpast : pastTuple ω ∉ pastGood := fun hm => hω (hmem.mp hm)
      simp [pastGoodIndicator, hω, hpast]
  have hcurrentEq : (R ∘ currentValue) ∘ currentTuple =
      fun ω => R (X n ω) := by
    funext ω
    simp [currentValue, currentTuple]
  rw [hpastEq, hcurrentEq] at hcomp
  exact hcomp.symm

lemma integral_geometricPrefixRewardTerm
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure α) [IsProbabilityMeasure ν]
    (X : ℕ → Ω → α) (hX : ∀ i, Measurable (X i))
    (hXi : iIndepFun X μ) (hLaw : ∀ i, μ.map (X i) = ν)
    (B : Set α) (hB : MeasurableSet B) (R : α → ℝ)
    (hR : Measurable R) (hRi : Integrable R ν) (n : ℕ) :
    ∫ ω, geometricPrefixRewardTerm X B R n ω ∂μ =
      (∫ x, R x ∂ν) * (ν.real Bᶜ) ^ n := by
  let pastIndicator :=
    (geometricFailurePrefix X B n).indicator (fun _ => (1 : ℝ))
  have hprefixMeas := measurableSet_geometricFailurePrefix hX hB n
  have hprefixInt : Integrable pastIndicator μ :=
    (integrable_const (1 : ℝ)).indicator hprefixMeas
  have hRcompInt : Integrable (fun ω => R (X n ω)) μ :=
    (show Integrable R (μ.map (X n)) by rw [hLaw n]; exact hRi).comp_measurable (hX n)
  have hInd := indep_geometricFailurePrefix_current μ X hX hXi B hB R hR n
  have hfactor := hInd.integral_fun_mul_eq_mul_integral
    hRcompInt.aestronglyMeasurable hprefixInt.aestronglyMeasurable
  have hprefixIntegral : ∫ ω, pastIndicator ω ∂μ = (ν.real Bᶜ) ^ n := by
    have hprob := hXi.measure_inter_preimage_eq_mul (Finset.range n)
      (sets := fun _ : ℕ => Bᶜ) (by intro i hi; exact hB.compl)
    have hsets : geometricFailurePrefix X B n =
        ⋂ i ∈ Finset.range n, X i ⁻¹' Bᶜ := rfl
    rw [show pastIndicator =
      (geometricFailurePrefix X B n).indicator (fun _ => (1 : ℝ)) by rfl,
      integral_indicator_const (1 : ℝ) hprefixMeas]
    have hmap : ∀ i ∈ Finset.range n, μ.real (X i ⁻¹' Bᶜ) = ν.real Bᶜ := by
      intro i hi
      rw [← hLaw i, map_measureReal_apply_of_aemeasurable
        (hX i).aemeasurable hB.compl]
    have hprobReal : μ.real (⋂ i ∈ Finset.range n, X i ⁻¹' Bᶜ) =
        ∏ i ∈ Finset.range n, μ.real (X i ⁻¹' Bᶜ) := by
      calc
        μ.real (⋂ i ∈ Finset.range n, X i ⁻¹' Bᶜ) =
            (μ (⋂ i ∈ Finset.range n, X i ⁻¹' Bᶜ)).toReal := rfl
        _ = (∏ i ∈ Finset.range n, μ (X i ⁻¹' Bᶜ)).toReal :=
          congrArg ENNReal.toReal hprob
        _ = ∏ i ∈ Finset.range n, (μ (X i ⁻¹' Bᶜ)).toReal :=
          ENNReal.toReal_prod _ _
        _ = ∏ i ∈ Finset.range n, μ.real (X i ⁻¹' Bᶜ) := rfl
    rw [hsets, hprobReal]
    have hprod :
        (∏ i ∈ Finset.range n, μ.real (X i ⁻¹' Bᶜ)) =
          (ν.real Bᶜ) ^ n := by
      calc
        (∏ i ∈ Finset.range n, μ.real (X i ⁻¹' Bᶜ)) =
            ∏ i ∈ Finset.range n, ν.real Bᶜ := by
              apply Finset.prod_congr rfl
              intro i hi
              exact hmap i hi
        _ = (ν.real Bᶜ) ^ n := by simp
    rw [hprod]
    simp
  calc
    ∫ ω, geometricPrefixRewardTerm X B R n ω ∂μ =
        (∫ ω, pastIndicator ω ∂μ) *
          (∫ ω, R (X n ω) ∂μ) := by
            change ∫ ω, R (X n ω) * pastIndicator ω ∂μ = _
            rw [hfactor]
            ring
    _ = (ν.real Bᶜ) ^ n * (∫ x, R x ∂ν) := by
          rw [hprefixIntegral, ← integral_map (hX n).aemeasurable
            hR.aestronglyMeasurable, hLaw n]
    _ = _ := by ring

end ProbabilityTheory
