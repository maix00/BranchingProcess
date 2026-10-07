/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Stable.Basic
public import Probability.Distributions.Stable.Gaussian
public import Probability.Distributions.Stable.Sign
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Probability.Moments.Variance

/-!
# Strictly stable laws do not have bounded support below index two

A bounded nondegenerate law has finite variance. The strict stability identity
then forces the scaling exponent to be two. Consequently, a strictly stable
law of index below two assigns positive mass outside every bounded interval.
-/

@[expose] public section

namespace ProbabilityTheory

open Filter MeasureTheory Set Topology
open scoped ProbabilityTheory

/-- A nondegenerate strictly `α`-stable probability law with `α < 2` cannot be
concentrated on a bounded interval. The proof uses only its two-copy scaling
identity and Mathlib's variance API. -/
theorem IsStrictlyAlphaStable.measure_Icc_lt_one_of_lt_two
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (hα₂ : α < 2) {r : ℝ} :
    μ (Icc (-r) r) < 1 := by
  let : IsProbabilityMeasure μ := h.isProbabilityMeasure
  by_contra hnot
  have hmass : μ (Icc (-r) r) = 1 := by
    apply le_antisymm
    · calc
        μ (Icc (-r) r) ≤ μ Set.univ := measure_mono (subset_univ _)
        _ = 1 := measure_univ
    · exact le_of_not_gt hnot
  have hcompl : μ (Icc (-r) r)ᶜ = 0 := by
    rw [measure_compl measurableSet_Icc (by finiteness)]
    rw [measure_univ, hmass]
    simp
  have haebound : ∀ᵐ x ∂μ, x ∈ Icc (-r) r := by
    rw [ae_iff]
    change μ (Icc (-r) r)ᶜ = 0
    exact hcompl
  have hid : MemLp (fun x : ℝ => x) 2 μ :=
    memLp_of_bounded haebound (by fun_prop) 2
  have hvarne : variance (fun x : ℝ => x) μ ≠ 0 := by
    intro hvar
    have hconst := ae_eq_integral_of_variance_eq_zero hid hvar
    have hId : (fun x : ℝ => x) =ᵐ[μ] fun _ => μ[fun x : ℝ => x] := by
      filter_upwards [hconst] with x hx
      exact hx
    have hmap : Measure.map (fun x : ℝ => x) μ =
        Measure.map (fun _ : ℝ => μ[fun x : ℝ => x]) μ :=
      Measure.map_congr hId
    have hdirac : μ = Measure.dirac (μ[fun x : ℝ => x]) := by
      simpa [Measure.map_id, Measure.map_const, measure_univ] using hmap
    exact h.nondegenerate ⟨μ[fun x : ℝ => x], hdirac⟩
  have hvarpos : 0 < variance (fun x : ℝ => x) μ :=
    lt_of_le_of_ne (variance_nonneg _ _) (Ne.symm hvarne)
  let s : ℝ := alphaStableScale α 1 1
  have hstable :
      (μ.prod μ).map (fun p : ℝ × ℝ => p.1 + p.2) =
        μ.map (fun x : ℝ => s * x) := by
    have h := h.2.2.2.2 1 1 (by norm_num) (by norm_num)
    have hfun : weightedSum 1 1 = (fun p : ℝ × ℝ => p.1 + p.2) := by
      funext p
      simp [weightedSum]
    rw [hfun] at h
    simpa [s] using h
  have hvariance := congrArg
    (fun ρ : Measure ℝ => variance id ρ) hstable
  have hvarianceLeft :
      variance id ((μ.prod μ).map (fun p : ℝ × ℝ => p.1 + p.2)) =
        variance (fun p : ℝ × ℝ => p.1 + p.2) (μ.prod μ) :=
    variance_id_map (by fun_prop)
  have hvarianceRight :
      variance id (μ.map (fun x : ℝ => s * x)) =
        variance (fun x : ℝ => s * x) μ :=
    variance_id_map (by fun_prop)
  rw [hvarianceLeft, hvarianceRight] at hvariance
  have hsumvariance :
      variance (fun p : ℝ × ℝ => p.1 + p.2) (μ.prod μ) =
        variance (fun x : ℝ => x) μ + variance (fun x : ℝ => x) μ := by
    simpa using (variance_add_prod hid hid)
  have hscalevariance :
      variance (fun x : ℝ => s * x) μ =
        s ^ 2 * variance (fun x : ℝ => x) μ := by
    exact variance_const_mul s (fun x : ℝ => x) μ
  rw [hsumvariance, hscalevariance] at hvariance
  have hs : s = 2 ^ (1 / α) := by
    norm_num [s, alphaStableScale]
  have hexp : 1 < 2 / α := (lt_div_iff₀ h.1).2 (by linarith)
  have hsquare : 2 < s ^ 2 := by
    rw [hs]
    have hp := Real.rpow_lt_rpow_of_exponent_lt
      (by norm_num : (1 : ℝ) < 2) hexp
    have hpow : (2 : ℝ) ^ (2 / α) = (2 ^ (1 / α)) ^ (2 : ℝ) := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    calc
      2 < (2 : ℝ) ^ (2 / α) := by simpa using hp
      _ = (2 ^ (1 / α)) ^ (2 : ℝ) := hpow
      _ = (2 ^ (1 / α)) ^ 2 := by rw [Real.rpow_two]
  nlinarith [hvarpos]

/-- The endpoint law of a nondegenerate strictly stable law of index below two
has strict mass loss from every fixed bounded interval after positive scaling.
This is the exact strict-mass input used by the discrete endpoint upper bound. -/
theorem IsStrictlyAlphaStable.measure_map_rpow_Icc_lt_one_of_lt_two
    {α constant : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ)
    (hα₂ : α < 2) (hconstant : 0 < constant) :
    (μ.map (fun x : ℝ => constant ^ (1 / α) * x)) (Icc (-1 : ℝ) 1) < 1 := by
  let c : ℝ := constant ^ (1 / α)
  have hc : 0 < c := Real.rpow_pos_of_pos hconstant _
  have hinterval : μ (Icc (-(1 / c)) (1 / c)) < 1 :=
    h.measure_Icc_lt_one_of_lt_two hα₂
  have hpre : (fun x : ℝ => c * x) ⁻¹' Icc (-1 : ℝ) 1 =
      Icc (-(1 / c)) (1 / c) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor
    · rintro ⟨hlo, hhi⟩
      constructor
      · have hm : (-1 : ℝ) ≤ x * c := by simpa [mul_comm] using hlo
        have hd : (-1 : ℝ) / c ≤ x := (div_le_iff₀ hc).2 hm
        simpa [neg_div] using hd
      · exact (le_div_iff₀ hc).2 (by simpa [mul_comm] using hhi)
    · rintro ⟨hlo, hhi⟩
      constructor
      · have hlo' : (-1 : ℝ) / c ≤ x := by simpa [neg_div] using hlo
        have h := (div_le_iff₀ hc).1 hlo'
        simpa [mul_comm] using h
      · have h := (le_div_iff₀ hc).1 hhi
        simpa [mul_comm] using h
  rw [Measure.map_apply (by fun_prop) measurableSet_Icc]
  change μ ((fun x : ℝ => c * x) ⁻¹' Icc (-1 : ℝ) 1) < 1
  rw [hpre]
  exact hinterval

/-- A nondegenerate strictly `2`-stable law has unbounded positive support.
The source condition `0 < F(0) < 1` gives positive mass above zero; the
two-copy scaling identity then amplifies every positive tail threshold by a
factor greater than one. -/
theorem IsStrictlyAlphaStable.measure_Ioi_pos_indexTwo
    {μ : Measure ℝ} (h : IsStrictlyAlphaStable 2 μ)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1) (v : ℝ) :
    0 < μ (Ioi v) := by
  let : IsProbabilityMeasure μ := h.isProbabilityMeasure
  let s : ℝ := alphaStableScale 2 1 1
  let ratio : ℝ := 2 / s
  have hspos : 0 < s := by
    dsimp [s, alphaStableScale]
    positivity
  have hsquare : s ^ 2 = 2 := by
    dsimp [s]
    rw [alphaStableScale_two_sq]
    norm_num
  have hslt : s < 2 := by nlinarith
  have hratio : 1 < ratio := by
    dsimp [ratio]
    exact (lt_div_iff₀ hspos).2 (by linarith)
  have hratioPos : 0 < ratio := by linarith
  have hpositiveZero : 0 < μ (Ioi 0) :=
    h.twoSidedMass_of_cdfAtZero hcdf |>.2
  have hthresholdTendsto :
      Tendsto (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa [Function.comp_def, Nat.cast_add, Nat.cast_one] using
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp
        (tendsto_add_atTop_nat 1)
  have hthresholdUnion :
      (⋃ n : ℕ, Ioi ((1 : ℝ) / ((n + 1 : ℕ) : ℝ))) = Ioi 0 := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_Ioi]
    constructor
    · rintro ⟨n, hx⟩
      have hnonneg : 0 ≤ (1 : ℝ) / ((n + 1 : ℕ) : ℝ) := by positivity
      linarith
    · intro hx
      obtain ⟨n, hn⟩ :=
        (hthresholdTendsto.eventually (Iio_mem_nhds hx)).exists
      exact ⟨n, hn⟩
  obtain ⟨n₀, hn₀⟩ :
      ∃ n : ℕ, 0 < μ (Ioi ((1 : ℝ) / ((n + 1 : ℕ) : ℝ))) := by
    by_contra hn
    have hn : ∀ n : ℕ,
        ¬ 0 < μ (Ioi ((1 : ℝ) / ((n + 1 : ℕ) : ℝ))) := by
      simpa only [not_exists] using hn
    have hzero (n : ℕ) :
        μ (Ioi ((1 : ℝ) / ((n + 1 : ℕ) : ℝ))) = 0 :=
      nonpos_iff_eq_zero.mp (not_lt.mp (hn n))
    have hnull := measure_iUnion_null hzero
    rw [hthresholdUnion] at hnull
    exact (ne_of_gt hpositiveZero) hnull
  let initial : ℝ := (1 : ℝ) / ((n₀ + 1 : ℕ) : ℝ)
  have hinitial : 0 < initial := by
    dsimp [initial]
    positivity
  have hinitialTail : 0 < μ (Ioi initial) := by
    simpa [initial] using hn₀
  have hstep {t : ℝ} (ht : 0 < t) (htail : 0 < μ (Ioi t)) :
      0 < μ (Ioi (ratio * t)) := by
    let sum : ℝ × ℝ → ℝ := fun p => p.1 + p.2
    have hsumStable :
        (μ.prod μ).map sum = μ.map (fun x : ℝ => s * x) := by
      have hsum := h.2.2.2.2 1 1 (by norm_num) (by norm_num)
      have hfun : weightedSum 1 1 = sum := by
        funext p
        simp [sum, weightedSum]
      rw [hfun] at hsum
      simpa [s] using hsum
    have hprod : μ.prod μ (Ioi t ×ˢ Ioi t) = μ (Ioi t) * μ (Ioi t) :=
      Measure.prod_prod _ _
    have hsubset : Ioi t ×ˢ Ioi t ⊆ sum ⁻¹' Ioi (2 * t) := by
      intro p hp
      simp only [Set.mem_prod, Set.mem_Ioi] at hp
      simp only [Set.mem_preimage, Set.mem_Ioi, sum]
      linarith
    have hsumPos : 0 < (μ.prod μ) (sum ⁻¹' Ioi (2 * t)) := by
      calc
        0 < μ (Ioi t) * μ (Ioi t) := ENNReal.mul_pos htail.ne' htail.ne'
        _ = (μ.prod μ) (Ioi t ×ˢ Ioi t) := hprod.symm
        _ ≤ (μ.prod μ) (sum ⁻¹' Ioi (2 * t)) := measure_mono hsubset
    have hpre : (fun x : ℝ => s * x) ⁻¹' Ioi (2 * t) = Ioi (ratio * t) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Ioi]
      have hiff : (2 * t) / s < x ↔ 2 * t < x * s := div_lt_iff₀ hspos
      simpa [ratio, div_eq_mul_inv, mul_assoc, mul_comm] using hiff.symm
    have hmeasureEq := congrArg (fun ρ : Measure ℝ => ρ (Ioi (2 * t))) hsumStable
    rw [Measure.map_apply (by fun_prop) measurableSet_Ioi,
      Measure.map_apply (by fun_prop) measurableSet_Ioi, hpre] at hmeasureEq
    rw [← hmeasureEq]
    exact hsumPos
  have hiter : ∀ k : ℕ, 0 < μ (Ioi (ratio ^ k * initial)) := by
    intro k
    induction k with
    | zero => simpa using hinitialTail
    | succ k ih =>
        have hnext := hstep (by positivity) ih
        have halg : ratio * (ratio ^ k * initial) = ratio ^ (k + 1) * initial := by
          rw [pow_succ]
          ring
        simpa [halg] using hnext
  have hthreshold : Tendsto (fun n : ℕ => ratio ^ n * initial) atTop atTop :=
    Tendsto.atTop_mul_const hinitial (tendsto_pow_atTop_atTop_of_one_lt hratio)
  obtain ⟨n, hn⟩ :=
    (hthreshold.eventually (eventually_gt_atTop v)).exists
  have hsubset : Ioi (ratio ^ n * initial) ⊆ Ioi v := by
    intro x hx
    exact lt_trans hn hx
  exact lt_of_lt_of_le (hiter n) (measure_mono hsubset)

/-- The source condition `0 < F(0) < 1` makes every bounded interval have
strictly less than full mass for a nondegenerate strictly `2`-stable law. -/
theorem IsStrictlyAlphaStable.measure_Icc_lt_one_indexTwo
    {μ : Measure ℝ} (h : IsStrictlyAlphaStable 2 μ)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1) (r : ℝ) :
    μ (Icc (-r) r) < 1 := by
  let : IsProbabilityMeasure μ := h.isProbabilityMeasure
  have htail := h.measure_Ioi_pos_indexTwo hcdf r
  by_contra hnot
  have hmass : μ (Icc (-r) r) = 1 := by
    apply le_antisymm
    · calc
        μ (Icc (-r) r) ≤ μ Set.univ := measure_mono (subset_univ _)
        _ = 1 := measure_univ
    · exact le_of_not_gt hnot
  have hcompl : μ (Icc (-r) r)ᶜ = 0 := by
    rw [measure_compl measurableSet_Icc (by finiteness), measure_univ, hmass]
    simp
  have hsubset : Ioi r ⊆ (Icc (-r) r)ᶜ := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_Icc]
    intro hinterval
    exact not_le_of_gt hx hinterval.2
  have hpositive : 0 < μ (Icc (-r) r)ᶜ :=
    lt_of_lt_of_le htail (measure_mono hsubset)
  exact (ne_of_gt hpositive) hcompl

/-- The source endpoint-mass condition for a positive scale in the strictly
`2`-stable case. -/
theorem IsStrictlyAlphaStable.measure_map_rpow_Icc_lt_one_indexTwo
    {constant : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable 2 μ)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1) (hconstant : 0 < constant) :
    (μ.map (fun x : ℝ => constant ^ (1 / (2 : ℝ)) * x))
      (Icc (-1 : ℝ) 1) < 1 := by
  let c : ℝ := constant ^ (1 / (2 : ℝ))
  have hc : 0 < c := Real.rpow_pos_of_pos hconstant _
  have hinterval : μ (Icc (-(1 / c)) (1 / c)) < 1 :=
    h.measure_Icc_lt_one_indexTwo hcdf (1 / c)
  have hpre : (fun x : ℝ => c * x) ⁻¹' Icc (-1 : ℝ) 1 =
      Icc (-(1 / c)) (1 / c) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor
    · rintro ⟨hlo, hhi⟩
      constructor
      · have hm : (-1 : ℝ) ≤ x * c := by simpa [mul_comm] using hlo
        have hd : (-1 : ℝ) / c ≤ x := (div_le_iff₀ hc).2 hm
        simpa [neg_div] using hd
      · exact (le_div_iff₀ hc).2 (by simpa [mul_comm] using hhi)
    · rintro ⟨hlo, hhi⟩
      constructor
      · have hlo' : (-1 : ℝ) / c ≤ x := by simpa [neg_div] using hlo
        have hm := (div_le_iff₀ hc).1 hlo'
        simpa [mul_comm] using hm
      · have hm := (le_div_iff₀ hc).1 hhi
        simpa [mul_comm] using hm
  rw [Measure.map_apply (by fun_prop) measurableSet_Icc]
  change μ ((fun x : ℝ => c * x) ⁻¹' Icc (-1 : ℝ) 1) < 1
  rw [hpre]
  exact hinterval

end ProbabilityTheory

end
