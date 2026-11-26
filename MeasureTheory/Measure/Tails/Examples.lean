/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.Measure.Tails.Quadratic
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# A vanishing quadratic tail with infinite second moment

## Public declarations

* `MeasureTheory.exists_probabilityMeasure_nat_vanishingQuadraticTail_infinite_secondMoment`:
  there is a probability measure `μ` on `ℕ` for which `X(n)=2^n` satisfies
  `x²μ{X>x}→0`, while `∫⁻n, ofReal(X(n)²)dμ=∞`.

The mass at `n` is the difference of consecutive survival values
`u_n=4^(-n)/(n+1)`. Telescoping gives total mass one and the exact survival
function. The second-moment series dominates the harmonic series. This is
an explicit strictness example for the measure-level quadratic-tail condition;
no branching process or independence is involved.
-/

@[expose] public section
namespace MeasureTheory
open Filter
open scoped ENNReal Topology

set_option backward.isDefEq.respectTransparency false

private noncomputable def survival (n : ℕ) : ℝ := (1 / 4 : ℝ) ^ n / (n + 1)
private noncomputable def mass (n : ℕ) : ℝ := survival n - survival (n + 1)
private noncomputable def tailMeasure : Measure ℕ :=
  Measure.sum (fun n => ENNReal.ofReal (mass n) • Measure.dirac n)

private lemma survival_nonneg (n : ℕ) : 0 ≤ survival n := by unfold survival; positivity

private lemma survival_succ_le (n : ℕ) : survival (n + 1) ≤ survival n / 4 := by
  dsimp [survival]
  norm_num only [Nat.cast_add, Nat.cast_one]
  rw [pow_succ]
  calc
    _ ≤ ((1 / 4 : ℝ) ^ n * (1 / 4)) / (n + 1) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    _ = _ := by ring

private lemma mass_nonneg (n : ℕ) : 0 ≤ mass n := by
  have h := survival_succ_le n
  have h' := survival_nonneg n
  dsimp [mass]
  linarith

private lemma partial_mass (n : ℕ) : ∑ i ∈ Finset.range n, mass i = 1 - survival n := by
  induction n with
  | zero => simp [survival]
  | succ n ih => rw [Finset.sum_range_succ, ih]; unfold mass; ring

private lemma survival_tendsto : Tendsto survival atTop (𝓝 0) := by
  apply squeeze_zero (fun n => survival_nonneg n) _
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num))
  intro n
  dsimp [survival]
  exact div_le_self (show (0 : ℝ) ≤ (1 / 4 : ℝ) ^ n by positivity)
    (show (1 : ℝ) ≤ (n : ℝ) + 1 by linarith only [show (0 : ℝ) ≤ n from Nat.cast_nonneg n])

private lemma mass_hasSum : HasSum mass 1 := by
  apply (hasSum_iff_tendsto_nat_of_nonneg mass_nonneg 1).mpr
  simp_rw [partial_mass]
  simpa using tendsto_const_nhds.sub survival_tendsto

private instance tailMeasure_probability : IsProbabilityMeasure tailMeasure :=
  mass_hasSum.isProbabilityMeasure_sum_dirac mass_nonneg

private lemma tailMeasure_singleton (n : ℕ) : tailMeasure {n} = ENNReal.ofReal (mass n) := by
  exact Measure.sum_smul_dirac_singleton

private lemma tailMeasure_Ici (k : ℕ) : tailMeasure.real (Set.Ici k) = survival k := by
  have he : (Set.Iio k : Set ℕ) = (↑(Finset.range k) : Set ℕ) := by ext n; simp
  have hf : tailMeasure.real (Set.Iio k) = 1 - survival k := by
    rw [he, ← sum_measureReal_singleton]
    simp only [measureReal_def, tailMeasure_singleton, ENNReal.toReal_ofReal (mass_nonneg _)]
    exact partial_mass k
  rw [← Set.compl_Iio, measureReal_compl measurableSet_Iio, probReal_univ, hf]
  ring

private lemma pow_survival (n : ℕ) :
    ((2 : ℝ) ^ n) ^ 2 * survival n = 1 / (n + 1) := by
  have he : ((2 : ℝ) ^ n) ^ 2 * (1 / 4 : ℝ) ^ n = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, ← mul_pow]
    norm_num
  dsimp [survival]
  rw [← mul_div_assoc, he]

private lemma weak_tail : HasVanishingQuadraticTail tailMeasure (fun n => (2 : ℝ) ^ n) := by
  rw [HasVanishingQuadraticTail, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_one_div_lt hε
  refine ⟨(2 : ℝ) ^ K, fun x hx => ?_⟩
  have hx1 : 1 ≤ x := (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)).trans hx
  obtain ⟨k, hk, hk'⟩ := exists_nat_pow_near hx1 (by norm_num : (1 : ℝ) < 2)
  have hKk : K ≤ k := by
    by_contra h
    have hle : k + 1 ≤ K := by omega
    have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hle
    linarith
  have hset : {n : ℕ | x < (2 : ℝ) ^ n} ⊆ Set.Ici (k + 1) := by
    intro n hn
    by_contra h
    have hnk : n ≤ k := by simpa using (Nat.le_of_lt_succ (not_le.mp h))
    have := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hnk
    exact not_lt_of_ge (this.trans hk) hn
  have hb := measureReal_mono (μ := tailMeasure) hset
  rw [tailMeasure_Ici] at hb
  have hpow : x ^ 2 ≤ ((2 : ℝ) ^ (k + 1)) ^ 2 := by nlinarith
  have hbound : x ^ 2 * tailMeasure.real {n : ℕ | x < (2 : ℝ) ^ n} ≤ 1 / (K + 1) := by
    calc
      _ ≤ ((2 : ℝ) ^ (k + 1)) ^ 2 * survival (k + 1) :=
        (mul_le_mul_of_nonneg_left hb (sq_nonneg _)).trans
          (mul_le_mul_of_nonneg_right hpow (survival_nonneg _))
      _ = 1 / ((k + 1 : ℕ) + 1 : ℝ) := pow_survival _
      _ ≤ 1 / (K + 1 : ℝ) := by gcongr; exact_mod_cast (by omega : K ≤ k + 1)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (sq_nonneg _) measureReal_nonneg)]
  exact hbound.trans_lt hK

private lemma infinite_second_moment :
    (∫⁻ n, ENNReal.ofReal (((2 : ℝ) ^ n) ^ 2) ∂tailMeasure) = ∞ := by
  have hh : ¬ Summable (fun n : ℕ => (3 / 4 : ℝ) / (n + 1)) := by
    intro h
    have hi := h.mul_left (4 / 3 : ℝ)
    have hi' : Summable (fun n : ℕ => 1 / (n + 1 : ℝ)) := by
      convert hi using 1
      funext n
      ring
    have h0 := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 1).mp
      (by simpa using hi')
    exact Real.not_summable_one_div_natCast h0
  have ht : (∑' n : ℕ, ENNReal.ofReal ((3 / 4 : ℝ) / (n + 1))) = ∞ := by
    by_contra h
    exact hh ((ENNReal.summable_toReal h).congr (fun n => ENNReal.toReal_ofReal (by positivity)))
  rw [tailMeasure, lintegral_sum_measure]
  apply top_unique
  rw [← ht]
  apply tsum_le_tsum
  intro n
  change ENNReal.ofReal ((3 / 4 : ℝ) / (n + 1)) ≤
    ∫⁻ a, ENNReal.ofReal (((2 : ℝ) ^ a) ^ 2) ∂(ENNReal.ofReal (mass n) • Measure.dirac n)
  rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul,
    ← ENNReal.ofReal_mul (mass_nonneg n)]
  apply ENNReal.ofReal_le_ofReal
  have hb : 3 / 4 * survival n ≤ mass n := by
    have := survival_succ_le n
    dsimp [mass]
    linarith
  have hp := pow_survival n
  have hm := mul_le_mul_of_nonneg_right hb (sq_nonneg ((2 : ℝ) ^ n))
  calc
    _ = (3 / 4 : ℝ) * (((2 : ℝ) ^ n) ^ 2 * survival n) := by rw [hp]; ring
    _ = (3 / 4 : ℝ) * survival n * ((2 : ℝ) ^ n) ^ 2 := by ring
    _ ≤ _ := hm

/-- The weak quadratic upper-tail condition is strictly weaker than a finite
second moment, even for a nonnegative discrete observation. -/
theorem exists_probabilityMeasure_nat_vanishingQuadraticTail_infinite_secondMoment :
    ∃ μ : Measure ℕ, IsProbabilityMeasure μ ∧
      HasVanishingQuadraticTail μ (fun n => (2 : ℝ) ^ n) ∧
      (∫⁻ n, ENNReal.ofReal (((2 : ℝ) ^ n) ^ 2) ∂μ) = ∞ :=
  ⟨tailMeasure, inferInstance, weak_tail, infinite_second_moment⟩

end MeasureTheory
