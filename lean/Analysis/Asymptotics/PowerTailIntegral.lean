/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Integrals of power-tailed functions

This file proves the integral form of Karamata's theorem for a nonnegative,
antitone function bounded by one. The assumptions are stated directly in terms
of a power-tail limit, without introducing a separate regular-variation
structure.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Interval

namespace Asymptotics

/-- A bounded monotone function with tail `g(t) ~ C t⁻ᵝ`, for `0 < β < 1`, has
integral asymptotic `∫₀ᵁ g(t) dt ~ C U^(1-β) / (1-β)`. -/
theorem tendsto_rpow_mul_intervalIntegral_of_tendsto_rpow_mul
    {g : ℝ → ℝ} {β C : ℝ}
    (hβ₁ : β < 1) (hC : 0 < C)
    (hg_anti : Antitone g)
    (hg_nonneg : ∀ ⦃t : ℝ⦄, 0 ≤ t → 0 ≤ g t)
    (hg_le_one : ∀ ⦃t : ℝ⦄, 0 ≤ t → g t ≤ 1)
    (hlim : Tendsto (fun t : ℝ => t ^ β * g t) atTop (nhds C)) :
    Tendsto (fun U : ℝ => U ^ (β - 1) * ∫ t in (0:ℝ)..U, g t)
      atTop (nhds (C / (1 - β))) := by
  let D : ℝ := 1 - β
  have hD : 0 < D := by dsimp [D]; linarith
  have hInt : ∀ a b : ℝ, IntervalIntegrable g volume a b := by
    intro a b
    exact (hg_anti.intervalIntegrable : IntervalIntegrable g volume a b)
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  let δ : ℝ := min (C / 2) (D * ε / 8) / 2
  have hδpos : 0 < δ := by
    dsimp [δ]
    positivity
  have hδC : δ < C := by
    dsimp [δ]
    have hminpos : 0 < min (C / 2) (D * ε / 8) := by positivity
    have hminle : min (C / 2) (D * ε / 8) ≤ C / 2 := min_le_left _ _
    nlinarith
  have hδD : δ / D < ε / 8 := by
    dsimp [δ]
    have hmin : min (C / 2) (D * ε / 8) ≤ D * ε / 8 := min_le_right _ _
    have hminpos : 0 < min (C / 2) (D * ε / 8) := by positivity
    rw [div_lt_iff₀ hD]
    nlinarith
  have hIoo : Ioo (C - δ) (C + δ) ∈ nhds C := by
    apply isOpen_Ioo.mem_nhds
    constructor <;> linarith [hδpos]
  have hnear : ∀ᶠ t : ℝ in atTop,
      C - δ < t ^ β * g t ∧ t ^ β * g t < C + δ := by
    simpa only [Set.mem_Ioo] using hlim.eventually hIoo
  obtain ⟨R₀, hR₀⟩ := eventually_atTop.1 hnear
  let R : ℝ := max 1 R₀
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hRge : R₀ ≤ R := le_max_right _ _
  have hRbound : ∀ ⦃t : ℝ⦄, R ≤ t →
      C - δ < t ^ β * g t ∧ t ^ β * g t < C + δ := by
    intro t ht
    exact hR₀ t (le_trans hRge ht)
  have hpow_pos : ∀ ⦃t : ℝ⦄, 0 < t → 0 < t ^ β :=
    fun _ ht => Real.rpow_pos_of_pos ht _
  have htail_bounds : ∀ ⦃t : ℝ⦄, R ≤ t →
      (C - δ) * t ^ (-β) ≤ g t ∧ g t ≤ (C + δ) * t ^ (-β) := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le hRpos ht
    have hp : 0 < t ^ β := hpow_pos htpos
    obtain ⟨hlo, hhi⟩ := hRbound ht
    have hlo' : (C - δ) * (t ^ β)⁻¹ ≤ g t := by
      have hmul := mul_le_mul_of_nonneg_right hlo.le (inv_nonneg.mpr hp.le)
      calc
        (C - δ) * (t ^ β)⁻¹ ≤ (t ^ β * g t) * (t ^ β)⁻¹ := hmul
        _ = g t := by field_simp
    have hhi' : g t ≤ (C + δ) * (t ^ β)⁻¹ := by
      have hmul := mul_le_mul_of_nonneg_right hhi.le (inv_nonneg.mpr hp.le)
      calc
        g t = (t ^ β * g t) * (t ^ β)⁻¹ := by field_simp
        _ ≤ (C + δ) * (t ^ β)⁻¹ := hmul
    exact ⟨by simpa only [Real.rpow_neg htpos.le β] using hlo',
      by simpa only [Real.rpow_neg htpos.le β] using hhi'⟩
  have hpowInt : ∀ a b : ℝ,
      IntervalIntegrable (fun t : ℝ => t ^ (-β)) volume a b := by
    intro a b
    exact intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < -β)
  have hbase_nonneg (U : ℝ) (hU : 0 ≤ U) :
      0 ≤ ∫ t in (0:ℝ)..U, g t := by
    have hzero : IntervalIntegrable (fun _ : ℝ => (0:ℝ)) volume 0 U := intervalIntegrable_const
    simpa using intervalIntegral.integral_mono_on hU hzero (hInt 0 U)
      (fun t ht => hg_nonneg ht.1)
  have hbase_le (U : ℝ) (hU : 0 ≤ U) :
      ∫ t in (0:ℝ)..U, g t ≤ U := by
    have hone : IntervalIntegrable (fun _ : ℝ => (1:ℝ)) volume 0 U := intervalIntegrable_const
    have hmono := intervalIntegral.integral_mono_on hU (hInt 0 U) hone
      (fun t ht => hg_le_one ht.1)
    simpa using hmono
  have hshiftIntegral (U : ℝ) (hRU : R ≤ U) :
      ∫ t in (0:ℝ)..U, g t =
        (∫ t in (0:ℝ)..R, g t) + ∫ t in R..U, g t := by
    symm
    exact intervalIntegral.integral_add_adjacent_intervals (hInt 0 R) (hInt R U)
  have hpowerIntegral (U : ℝ) (hRU : R ≤ U) :
      ∫ t in R..U, t ^ (-β) =
        (U ^ D - R ^ D) / D := by
    calc
      ∫ t in R..U, t ^ (-β) =
          (U ^ (-β + 1) - R ^ (-β + 1)) / (-β + 1) :=
        integral_rpow (Or.inl (by linarith : -1 < -β))
      _ = (U ^ D - R ^ D) / D := by
        rw [show -β + 1 = D by dsimp [D]; ring]
  have htailIntegralLower (U : ℝ) (hRU : R ≤ U) :
      (C - δ) * ∫ t in R..U, t ^ (-β) ≤ ∫ t in R..U, g t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hRU
      ((hpowInt R U).const_mul (C - δ)) (hInt R U)
    intro t ht
    exact (htail_bounds ht.1).1
  have htailIntegralUpper (U : ℝ) (hRU : R ≤ U) :
      ∫ t in R..U, g t ≤ (C + δ) * ∫ t in R..U, t ^ (-β) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hRU
      (hInt R U) ((hpowInt R U).const_mul (C + δ))
    intro t ht
    exact (htail_bounds ht.1).2
  have hlow (U : ℝ) (hRU : R ≤ U) :
      (C - δ) * ((U ^ D - R ^ D) / D) ≤ ∫ t in (0:ℝ)..U, g t := by
    rw [← hpowerIntegral U hRU]
    rw [hshiftIntegral U hRU]
    have := htailIntegralLower U hRU
    have hbase := hbase_nonneg R hRpos.le
    nlinarith
  have hupp (U : ℝ) (hRU : R ≤ U) :
      ∫ t in (0:ℝ)..U, g t ≤ R + (C + δ) * ((U ^ D - R ^ D) / D) := by
    rw [hshiftIntegral U hRU]
    have hbase := hbase_le R hRpos.le
    have htail := htailIntegralUpper U hRU
    rw [hpowerIntegral U hRU] at htail
    linarith
  have hnegpow : Tendsto (fun U : ℝ => U ^ (-D)) atTop (nhds 0) :=
    tendsto_rpow_neg_atTop hD
  have hratio : Tendsto (fun U : ℝ => R ^ D * U ^ (-D)) atTop (nhds 0) :=
    by simpa using (tendsto_const_nhds.mul hnegpow)
  have hfactor : Tendsto (fun U : ℝ => 1 - R ^ D * U ^ (-D)) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub hratio
  have hsmall : Tendsto (fun U : ℝ => R * U ^ (-D)) atTop (nhds 0) :=
    by simpa using (tendsto_const_nhds.mul hnegpow)
  have hmain (U : ℝ) (hU : 0 < U) :
      U ^ (β - 1) * (U ^ D - R ^ D) = 1 - R ^ D * U ^ (-D) := by
    have hbeta : β - 1 = -D := by dsimp [D]; ring
    rw [hbeta]
    have hcancel : U ^ (-D) * U ^ D = 1 := by
      rw [← Real.rpow_add hU, neg_add_cancel, Real.rpow_zero]
    calc
      U ^ (-D) * (U ^ D - R ^ D) = U ^ (-D) * U ^ D - U ^ (-D) * R ^ D := by ring
      _ = 1 - R ^ D * U ^ (-D) := by rw [hcancel, mul_comm (U ^ (-D)) (R ^ D)]
  have hlowLimit : Tendsto
      (fun U : ℝ => U ^ (β - 1) * ((C - δ) * ((U ^ D - R ^ D) / D)))
      atTop (nhds ((C - δ) / D)) := by
    have hlim' : Tendsto
        (fun U : ℝ => ((C - δ) / D) * (1 - R ^ D * U ^ (-D)))
        atTop (nhds ((C - δ) / D)) := by
      simpa using tendsto_const_nhds.mul hfactor
    apply hlim'.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with U hU
    calc
      ((C - δ) / D) * (1 - R ^ D * U ^ (-D)) =
          ((C - δ) / D) * (U ^ (β - 1) * (U ^ D - R ^ D)) := by
            rw [← hmain U hU]
      _ = U ^ (β - 1) * ((C - δ) * ((U ^ D - R ^ D) / D)) := by ring
  have huppLimit : Tendsto
      (fun U : ℝ => U ^ (β - 1) * (R + (C + δ) * ((U ^ D - R ^ D) / D)))
      atTop (nhds ((C + δ) / D)) := by
    have hlim' : Tendsto
        (fun U : ℝ => R * U ^ (-D) + ((C + δ) / D) *
          (1 - R ^ D * U ^ (-D))) atTop (nhds ((C + δ) / D)) := by
      have hmulconst : Tendsto
          (fun U : ℝ => ((C + δ) / D) * (1 - R ^ D * U ^ (-D)))
          atTop (nhds ((C + δ) / D)) := by
        simpa using tendsto_const_nhds.mul hfactor
      have := hsmall.add hmulconst
      simpa using this
    apply hlim'.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with U hU
    have hbeta : β - 1 = -D := by dsimp [D]; ring
    rw [← hmain U hU]
    rw [show U ^ (β - 1) = U ^ (-D) by exact congrArg (fun p : ℝ => U ^ p) hbeta]
    ring
  have hlowTarget : C / D - ε < (C - δ) / D := by
    rw [sub_div]
    have hδε : δ / D < ε := lt_trans hδD (by linarith)
    linarith
  have huppTarget : (C + δ) / D < C / D + ε := by
    rw [add_div]
    have hδε : δ / D < ε := lt_trans hδD (by linarith)
    linarith
  have hlowEvent : ∀ᶠ U : ℝ in atTop,
      (C / D) - ε < U ^ (β - 1) * ((C - δ) * ((U ^ D - R ^ D) / D)) := by
    have hlimlo := hlowLimit.eventually (Ioi_mem_nhds hlowTarget)
    filter_upwards [hlimlo] with U hU
    exact hU
  have huppEvent : ∀ᶠ U : ℝ in atTop,
      U ^ (β - 1) * (R + (C + δ) * ((U ^ D - R ^ D) / D)) < (C / D) + ε := by
    have hlimhi := huppLimit.eventually (Iio_mem_nhds huppTarget)
    filter_upwards [hlimhi] with U hU
    exact hU
  have hpowUpos : ∀ᶠ U : ℝ in atTop, 0 < U ^ (β - 1) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with U hU
    exact Real.rpow_pos_of_pos hU _
  filter_upwards [hlowEvent, huppEvent, eventually_ge_atTop R,
    hpowUpos] with U hloEvent' hhiEvent' hRU hmult
  have hlo' := mul_le_mul_of_nonneg_left (hlow U hRU) hmult.le
  have hhi' := mul_le_mul_of_nonneg_left (hupp U hRU) hmult.le
  have hlo'' : C / D - ε < U ^ (β - 1) * ∫ t in (0:ℝ)..U, g t :=
    lt_of_lt_of_le hloEvent' hlo'
  have hhi'' : U ^ (β - 1) * ∫ t in (0:ℝ)..U, g t < C / D + ε :=
    lt_of_le_of_lt hhi' hhiEvent'
  rw [Real.dist_eq]
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

end Asymptotics
