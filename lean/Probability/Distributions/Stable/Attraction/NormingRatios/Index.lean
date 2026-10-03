/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import MeasureTheory.Measure.CharacteristicFunction.Convergence
public import Probability.Distributions.CharacteristicFunction.Symmetrization
public import Probability.Distributions.Stable.Attraction.CharacteristicFunction
public import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Ratios of stable norming sequences

Characteristic functions of symmetrized sums remove deterministic centering.
This module develops the ratio consequences of attraction without assuming
monotonicity of the norming sequence.
-/

open Filter MeasureTheory
open scoped Topology Uniformity

@[expose] public section

namespace ProbabilityTheory

/-- The law of an i.i.d. sum with a specified number of terms and a possibly
different scale index. -/
private noncomputable def normalizedSumLaw (ν : Measure ℝ) (scale : ℝ)
    (count : ℕ) : Measure ℝ :=
  (iidSequenceLaw ν).map (normalizedIidSum (fun _ => scale) (fun _ => 0) count)

private theorem charFun_normalizedSumLaw {ν : Measure ℝ}
    [IsProbabilityMeasure ν] (scale : ℝ) (count : ℕ) (t : ℝ) :
    charFun (normalizedSumLaw ν scale count) t =
      charFun ν (scale⁻¹ * t) ^ count := by
  rw [normalizedSumLaw, charFun_map_normalizedIidSum]
  simp

/-- A positive logarithmic defect, scaled by time, determines the asymptotic
power of the one-step modulus at any asymptotically proportional time index. -/
private theorem tendsto_pow_two_mul_of_tendsto_negLog
    {r : ℕ → ℝ} {m : ℕ → ℕ} {c ratioLimit : ℝ}
    (hr : ∀ᶠ n : ℕ in atTop, 0 < r n)
    (hn : ∀ᶠ n : ℕ in atTop, 0 < n)
    (hlog : Tendsto (fun n : ℕ => (n : ℝ) * (-Real.log (r n))) atTop (nhds c))
    (hm : Tendsto (fun n : ℕ => (m n : ℝ) / (n : ℝ)) atTop (nhds ratioLimit)) :
    Tendsto (fun n : ℕ => r n ^ (2 * m n)) atTop
      (nhds (Real.exp (-2 * c * ratioLimit))) := by
  have hprod : Tendsto
      (fun n : ℕ => ((m n : ℝ) / (n : ℝ)) *
        ((n : ℝ) * (-Real.log (r n)))) atTop (nhds (ratioLimit * c)) := hm.mul hlog
  have hexpArg : Tendsto
      (fun n : ℕ => -2 * (((m n : ℝ) / (n : ℝ)) *
        ((n : ℝ) * (-Real.log (r n))))) atTop
      (nhds (-2 * (ratioLimit * c))) :=
    hprod.const_mul (-2)
  have hexp : Tendsto
      (fun n : ℕ => Real.exp (-2 * (((m n : ℝ) / (n : ℝ)) *
        ((n : ℝ) * (-Real.log (r n)))))) atTop
      (nhds (Real.exp (-2 * (ratioLimit * c)))) :=
    Real.continuous_exp.continuousAt.tendsto.comp hexpArg
  have hEq : (fun n : ℕ => r n ^ (2 * m n)) =ᶠ[atTop]
      fun n => Real.exp (-2 * (((m n : ℝ) / (n : ℝ)) *
        ((n : ℝ) * (-Real.log (r n))))) := by
    filter_upwards [hr, hn] with n hrn hnn
    have hnn' : (n : ℝ) ≠ 0 := by exact_mod_cast hnn.ne'
    rw [← Real.exp_log (pow_pos hrn _), Real.log_pow]
    congr 1
    push_cast
    field_simp [hnn']
  have hlimit : Real.exp (-2 * (ratioLimit * c)) =
      Real.exp (-2 * c * ratioLimit) := by
    congr 1
    ring
  rw [← hlimit]
  exact hexp.congr' hEq.symm

/-- Number of repeated halvings needed to reach the fixed initial interval
`[N, 2 * N)`. -/
private def halvingDepth (N : ℕ) (hN : 0 < N) (n : ℕ) : ℕ :=
  if n < 2 * N then 0 else halvingDepth N hN (n / 2) + 1
termination_by n
decreasing_by omega

/-- A positive sequence that grows by a fixed factor under each sufficiently
large doubling tends to infinity.  The proof uses repeated halving, without
assuming the sequence is monotone. -/
private theorem tendsto_atTop_of_halving_growth
    {b : ℕ → ℝ} (N : ℕ) (hN : 0 < N) (c p : ℝ)
    (hc : 0 < c) (hp : 1 < p)
    (hbase : ∀ n, N ≤ n → n < 2 * N → c ≤ b n)
    (hstep : ∀ n, N ≤ n → p * b (n / 2) ≤ b n) :
    Tendsto b atTop atTop := by
  let d : ℕ → ℕ := halvingDepth N hN
  have hbound : ∀ n, N ≤ n → c * p ^ d n ≤ b n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      by_cases hsmall : n < 2 * N
      · have hd : d n = 0 := by
          dsimp [d]
          rw [halvingDepth, if_pos hsmall]
        rw [hd, pow_zero, mul_one]
        exact hbase n hn hsmall
      · have hhalfN : N ≤ n / 2 := by omega
        have hhalfLt : n / 2 < n := by omega
        have hhalfBound := ih (n / 2) hhalfLt hhalfN
        have hd : d n = d (n / 2) + 1 := by
          dsimp [d]
          rw [halvingDepth, if_neg hsmall]
        rw [hd, pow_succ]
        calc
          c * (p ^ d (n / 2) * p) = p * (c * p ^ d (n / 2)) := by ring
          _ ≤ p * b (n / 2) :=
            mul_le_mul_of_nonneg_left hhalfBound (le_of_lt (lt_trans zero_lt_one hp))
          _ ≤ b n := hstep n hn
  have hdAtTop : Tendsto d atTop atTop := by
    apply tendsto_atTop.2
    intro k
    have hev : ∀ᶠ n : ℕ in atTop, 2 * N * 2 ^ k ≤ n :=
      eventually_atTop.2 ⟨2 * N * 2 ^ k, fun n hn => hn⟩
    filter_upwards [hev] with n hn
    have hdepthLower : ∀ k n, 2 * N * 2 ^ k ≤ n → k ≤ d n := by
      intro k
      induction k with
      | zero => intro n hn; exact Nat.zero_le _
      | succ k ih =>
        intro n hn
        have hpow : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
        have hmul : 4 * N ≤ 2 * N * 2 ^ (k + 1) := by
          calc
            4 * N = (2 * N) * 1 * 2 := by ring
            _ ≤ (2 * N) * 2 ^ k * 2 := by gcongr
            _ = 2 * N * 2 ^ (k + 1) := by rw [pow_succ]; ring
        have hnot : ¬ n < 2 * N := by
          have hbig := hmul.trans hn
          omega
        have hhalf : 2 * N * 2 ^ k ≤ n / 2 := by
          apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).2
          have hrew : (2 * N * 2 ^ k) * 2 = 2 * N * 2 ^ (k + 1) := by
            rw [pow_succ]
            ring
          rw [hrew]
          exact hn
        have hih := ih (n / 2) hhalf
        have hd : d n = d (n / 2) + 1 := by
          dsimp [d]
          rw [halvingDepth, if_neg hnot]
        rw [hd]
        omega
    exact hdepthLower k n hn
  have hpTop : Tendsto (fun n : ℕ => p ^ d n) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hp).comp hdAtTop
  have hscaled : Tendsto (fun n : ℕ => c * p ^ d n) atTop atTop :=
    hpTop.const_mul_atTop hc
  have hboundEventually : ∀ᶠ n : ℕ in atTop, c * p ^ d n ≤ b n :=
    eventually_atTop.2 ⟨N, fun n hn => hbound n hn⟩
  exact tendsto_atTop_mono' atTop hboundEventually hscaled

/-- If `m n / n → ratio`, then a stable domain-of-attraction norming has the
corresponding ratio, without any monotonicity assumption on the norming. -/
theorem IsInDomainOfAttractionAlong.tendsto_norming_ratio
    {α : ℝ} {ν limit : Measure ℝ} [IsProbabilityMeasure ν]
    (hlimit : IsAlphaStable α limit)
    {scale center : ℕ → ℝ}
    (h : @IsInDomainOfAttractionAlong ν limit inferInstance
      hlimit.isProbabilityMeasure scale center)
    (m : ℕ → ℕ) (ratio : ℝ) (hratio : 0 < ratio)
    (hm : Tendsto (fun n : ℕ => (m n : ℝ) / (n : ℝ)) atTop (nhds ratio)) :
    Tendsto (fun n : ℕ => scale (m n) / scale n) atTop
      (nhds (Real.rpow ratio α⁻¹)) := by
  letI : IsProbabilityMeasure limit := hlimit.isProbabilityMeasure
  obtain ⟨c, hc, hchar⟩ := hlimit.exists_pos_norm_charFun_eq_exp
  let η := symmetrizedMeasure ν
  let ρ := symmetrizedMeasure limit
  let factor : ℝ := Real.rpow ratio α⁻¹
  let ρfactor : Measure ℝ := ρ.map (fun x => factor * x)
  let A : ℕ → Measure ℝ := fun n => normalizedSumLaw η (scale (m n)) (m n)
  let C : ℕ → Measure ℝ := fun n => normalizedSumLaw η (scale n) (m n)
  let a : ℕ → ℝ := fun n => scale (m n) / scale n
  haveI hη : IsProbabilityMeasure η := by
    dsimp [η, symmetrizedMeasure]
    infer_instance
  haveI hρ : IsProbabilityMeasure ρ := by
    dsimp [ρ, symmetrizedMeasure]
    infer_instance
  haveI hρfactor : IsProbabilityMeasure ρfactor := by
    dsimp [ρfactor]
    infer_instance
  haveI hAprob : ∀ n, IsProbabilityMeasure (A n) := by
    intro n
    dsimp [A, normalizedSumLaw]
    infer_instance
  haveI hCprob : ∀ n, IsProbabilityMeasure (C n) := by
    intro n
    dsimp [C, normalizedSumLaw]
    infer_instance
  have hmLower : ∀ᶠ n : ℕ in atTop, ratio / 2 < (m n : ℝ) / (n : ℝ) :=
    hm.eventually (Ioi_mem_nhds (by linarith))
  have hlinear : Tendsto (fun n : ℕ => (ratio / 2) * (n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
      |>.const_mul_atTop (by positivity)
  have hmLowerMul : ∀ᶠ n : ℕ in atTop,
      (ratio / 2) * (n : ℝ) ≤ (m n : ℝ) := by
    filter_upwards [hmLower, eventually_gt_atTop 0] with n hratioN hn
    have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
    have hmul := (lt_div_iff₀ hnReal).1 hratioN
    nlinarith
  have hmTopReal : Tendsto (fun n : ℕ => (m n : ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop hmLowerMul hlinear
  have hmTop : Tendsto m atTop atTop := by
    apply tendsto_atTop.2
    intro k
    have hk := (tendsto_atTop.1 hmTopReal) (k : ℝ)
    filter_upwards [hk] with n hn
    exact_mod_cast hn
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale n := h.eventually_scale_pos
  have hscaleMPos : ∀ᶠ n : ℕ in atTop, 0 < scale (m n) := hmTop.eventually hscalePos
  have haPos : ∀ᶠ n : ℕ in atTop, 0 < a n := by
    filter_upwards [hscalePos, hscaleMPos] with n hn hm
    dsimp [a]
    exact div_pos hm hn
  have hlog (t : ℝ) : Tendsto
      (fun n : ℕ => (n : ℝ) * (-Real.log ‖charFun ν ((scale n)⁻¹ * t)‖))
      atTop (nhds (c * |t| ^ α)) :=
    (h.tendsto_log_norm_charFun_and_norm_defect_of_charFun_norm
      hlimit c hc hchar t).1
  have hnormPow (t : ℝ) : Tendsto
      (fun n : ℕ => ‖charFun ν ((scale n)⁻¹ * t)‖ ^ n) atTop
      (nhds (Real.exp (-c * |t| ^ α))) := by
    simpa [hchar t] using h.tendsto_norm_charFun_oneStep_pow t
  have hρchar (t : ℝ) :
      charFun ρ t = (Real.exp (-(2 * c * |t| ^ α)) : ℂ) := by
    rw [show ρ = symmetrizedMeasure limit by rfl, charFun_symmetrizedMeasure, hchar t]
    norm_cast
    rw [pow_two]
    rw [← Real.exp_add]
    congr 1
    ring
  have hfactorPow : factor ^ α = ratio := by
    dsimp [factor]
    rw [← Real.rpow_mul (le_of_lt hratio)]
    rw [show α⁻¹ * α = 1 by field_simp [ne_of_gt hlimit.alpha_pos]]
    exact Real.rpow_one ratio
  have hρfactorChar (t : ℝ) :
      charFun ρfactor t = (Real.exp (-(2 * c * ratio * |t| ^ α)) : ℂ) := by
    rw [show ρfactor = ρ.map (fun x => factor * x) by rfl,
      charFun_map_mul, hρchar]
    have hfactorPos : 0 < factor := Real.rpow_pos_of_pos hratio _
    rw [abs_mul, abs_of_pos hfactorPos, Real.mul_rpow hfactorPos.le (abs_nonneg t), hfactorPow]
    norm_cast
    congr 1
    ring
  have hApoint (t : ℝ) : Tendsto (fun n : ℕ => charFun (A n) t) atTop
      (nhds (charFun ρ t)) := by
    let r : ℕ → ℝ := fun n => ‖charFun ν ((scale n)⁻¹ * t)‖
    have hpow : Tendsto (fun n : ℕ => r (m n) ^ (m n)) atTop
      (nhds (Real.exp (-c * |t| ^ α))) := by
      change Tendsto
        ((fun n : ℕ => ‖charFun ν ((scale n)⁻¹ * t)‖ ^ n) ∘ m)
        atTop (nhds (Real.exp (-c * |t| ^ α)))
      exact (hnormPow t).comp hmTop
    have hformula (n : ℕ) : charFun (A n) t =
        (↑(r (m n) ^ (m n) * r (m n) ^ (m n)) : ℂ) := by
      change charFun (normalizedSumLaw η (scale (m n)) (m n)) t = _
      rw [charFun_normalizedSumLaw, charFun_symmetrizedMeasure]
      norm_cast
      rw [← pow_mul, show 2 * m n = m n + m n by omega, pow_add]
    have hcast := (Complex.continuous_ofReal.continuousAt).tendsto.comp
      (hpow.mul hpow)
    have hlim : (↑(Real.exp (-c * |t| ^ α) * Real.exp (-c * |t| ^ α)) : ℂ) =
        charFun ρ t := by
      rw [hρchar]
      norm_cast
      rw [← Real.exp_add]
      congr 1
      ring
    convert hcast using 1
    · funext n
      rw [hformula]
      simp [pow_two]
    · rw [← hlim]
  have hCpoint (t : ℝ) : Tendsto (fun n : ℕ => charFun (C n) t) atTop
      (nhds (charFun ρfactor t)) := by
    let r : ℕ → ℝ := fun n => ‖charFun ν ((scale n)⁻¹ * t)‖
    have hnPos : ∀ᶠ n : ℕ in atTop, 0 < n := by
      exact eventually_atTop.2 ⟨1, fun n hn => Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩
    have hrPos : ∀ᶠ n : ℕ in atTop, 0 < r n := by
      have hpowPos : ∀ᶠ n : ℕ in atTop,
          0 < r n ^ n := (hnormPow t).eventually (Ioi_mem_nhds (Real.exp_pos _))
      filter_upwards [hpowPos, hnPos] with n hpowPos hn
      by_contra hnot
      have hr0 : r n = 0 := le_antisymm (le_of_not_gt hnot) (norm_nonneg _)
      simp [hr0, Nat.ne_of_gt hn] at hpowPos
    have hpow := tendsto_pow_two_mul_of_tendsto_negLog hrPos hnPos (hlog t) hm
    have hformula (n : ℕ) : charFun (C n) t = (↑(r n ^ (2 * m n)) : ℂ) := by
      change charFun (normalizedSumLaw η (scale n) (m n)) t = _
      rw [charFun_normalizedSumLaw, charFun_symmetrizedMeasure]
      have hpowEq : (r n ^ 2) ^ (m n) = r n ^ (2 * m n) := by
        rw [← pow_mul]
      norm_cast
    have hcast := (Complex.continuous_ofReal.continuousAt).tendsto.comp hpow
    have hlim : (↑(Real.exp (-2 * (c * |t| ^ α) * ratio) : ℝ) : ℂ) =
        charFun ρfactor t := by
      rw [hρfactorChar]
      norm_cast
      congr 1
      norm_num
      ring
    convert hcast using 1
    · funext n
      rw [hformula]
      rfl
    · rw [← hlim]

  have hAformula (n : ℕ) (t : ℝ) :
      charFun (A n) t =
        (‖charFun ν ((scale (m n))⁻¹ * t)‖ ^ (2 * m n) : ℂ) := by
    change charFun (normalizedSumLaw η (scale (m n)) (m n)) t = _
    rw [charFun_normalizedSumLaw, charFun_symmetrizedMeasure]
    norm_cast
    rw [← pow_mul]
  have hCformula (n : ℕ) (t : ℝ) :
      charFun (C n) t =
        (‖charFun ν ((scale n)⁻¹ * t)‖ ^ (2 * m n) : ℂ) := by
    change charFun (normalizedSumLaw η (scale n) (m n)) t = _
    rw [charFun_normalizedSumLaw, charFun_symmetrizedMeasure]
    norm_cast
    rw [← pow_mul]
  have hratioArguments (n : ℕ) (hn : 0 < scale n)
    (hmn : 0 < scale (m n)) :
      (scale n)⁻¹ = (scale (m n))⁻¹ * a n := by
    dsimp [a]
    field_simp [ne_of_gt hn, ne_of_gt hmn]
  have hinvRatioArguments (n : ℕ) (hn : 0 < scale n)
      (hmn : 0 < scale (m n)) :
      (scale (m n))⁻¹ = (scale n)⁻¹ * (a n)⁻¹ := by
    dsimp [a]
    field_simp [ne_of_gt hn, ne_of_gt hmn]
  have hrelLower : ∀ᶠ n : ℕ in atTop,
      charFun (C n) 1 = charFun (A n) (a n) := by
    filter_upwards [hscalePos, hscaleMPos] with n hn hmn
    rw [hCformula, hAformula]
    simp only [mul_one]
    rw [hratioArguments n hn hmn]
  have hrelUpper : ∀ᶠ n : ℕ in atTop,
      charFun (A n) 1 = charFun (C n) (a n)⁻¹ := by
    filter_upwards [hscalePos, hscaleMPos] with n hn hmn
    rw [hAformula, hCformula]
    simp only [mul_one]
    rw [hinvRatioArguments n hn hmn]

  have hρone_ne : charFun ρ 1 ≠ (1 : ℂ) := by
    have hnorm : ‖charFun ρ 1‖ < 1 := by
      rw [hρchar]
      norm_cast
      have hone : (1 : ℝ) ^ α = 1 := Real.one_rpow _
      rw [hone]
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_lt_one_iff.mpr (by nlinarith [hc])
    intro heq
    rw [heq] at hnorm
    simp at hnorm
  have hρfactorOne_ne : charFun ρfactor 1 ≠ (1 : ℂ) := by
    have hnorm : ‖charFun ρfactor 1‖ < 1 := by
      rw [hρfactorChar]
      norm_cast
      have hone : (1 : ℝ) ^ α = 1 := Real.one_rpow _
      rw [hone]
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_lt_one_iff.mpr (by nlinarith [hc, hratio])
    intro heq
    rw [heq] at hnorm
    simp at hnorm

  have htightA : IsTightMeasureSet (Set.range A) :=
    isTightMeasureSet_of_tendsto_charFun
      (continuous_charFun (μ := ρ)).continuousAt hApoint
  have htightC : IsTightMeasureSet (Set.range C) :=
    isTightMeasureSet_of_tendsto_charFun
      (continuous_charFun (μ := ρfactor)).continuousAt hCpoint
  have hEquiA := equicontinuous_charFun_of_isTightMeasureSet htightA
  have hEquiC := equicontinuous_charFun_of_isTightMeasureSet htightC

  let δA : ℝ := dist (1 : ℂ) (charFun ρfactor 1) / 4
  have hδA : 0 < δA := by
    dsimp [δA]
    exact div_pos (dist_pos.mpr (Ne.symm hρfactorOne_ne)) (by norm_num)
  let UA : Set (ℂ × ℂ) := {p | dist p.1 p.2 < δA}
  have hUA : UA ∈ 𝓤 ℂ := by
    simpa [UA] using Metric.dist_mem_uniformity hδA
  have hAnearEvent : ∀ᶠ x : ℝ in 𝓝 0,
      ∀ n, dist (charFun (A n) 0) (charFun (A n) x) < δA := by
    simpa [UA] using hEquiA 0 UA hUA
  obtain ⟨εA, hεA, hAnear⟩ := Metric.eventually_nhds_iff.mp hAnearEvent
  have hAnearOne (n : ℕ) (x : ℝ) (hx : |x| < εA) :
      dist (1 : ℂ) (charFun (A n) x) < δA := by
    have hx' : dist x 0 < εA := by simpa [Real.dist_eq] using hx
    simpa using hAnear hx' n

  have hCclose : ∀ᶠ n : ℕ in atTop,
      dist (charFun (C n) 1) (charFun ρfactor 1) < δA := by
    exact (hCpoint 1).eventually (Metric.ball_mem_nhds _ hδA)
  have haLower : ∀ᶠ n : ℕ in atTop, εA ≤ a n := by
    filter_upwards [hCclose, hrelLower, haPos] with n hclose hrel ha
    by_contra hnot
    have hsmall : a n < εA := lt_of_not_ge hnot
    have hnear := hAnearOne n (a n) (by simpa [abs_of_pos ha] using hsmall)
    have htriangle := dist_triangle (1 : ℂ) (charFun (C n) 1) (charFun ρfactor 1)
    have hfirst : dist (1 : ℂ) (charFun (C n) 1) < δA := by
      rw [hrel]
      exact hnear
    have hsum : dist (1 : ℂ) (charFun ρfactor 1) < δA + δA := by
      exact htriangle.trans_lt (add_lt_add hfirst hclose)
    dsimp [δA] at hsum
    have hgap := dist_pos.mpr (Ne.symm hρfactorOne_ne)
    linarith

  let δC : ℝ := dist (1 : ℂ) (charFun ρ 1) / 4
  have hδC : 0 < δC := by
    dsimp [δC]
    exact div_pos (dist_pos.mpr (Ne.symm hρone_ne)) (by norm_num)
  let UC : Set (ℂ × ℂ) := {p | dist p.1 p.2 < δC}
  have hUC : UC ∈ 𝓤 ℂ := by
    simpa [UC] using Metric.dist_mem_uniformity hδC
  have hCnearEvent : ∀ᶠ x : ℝ in 𝓝 0,
      ∀ n, dist (charFun (C n) 0) (charFun (C n) x) < δC := by
    simpa [UC] using hEquiC 0 UC hUC
  obtain ⟨εC, hεC, hCnear⟩ := Metric.eventually_nhds_iff.mp hCnearEvent
  have hCnearOne (n : ℕ) (x : ℝ) (hx : |x| < εC) :
      dist (1 : ℂ) (charFun (C n) x) < δC := by
    have hx' : dist x 0 < εC := by simpa [Real.dist_eq] using hx
    simpa using hCnear hx' n
  have hAclose : ∀ᶠ n : ℕ in atTop,
      dist (charFun (A n) 1) (charFun ρ 1) < δC := by
    exact (hApoint 1).eventually (Metric.ball_mem_nhds _ hδC)
  have haUpper : ∀ᶠ n : ℕ in atTop, a n ≤ εC⁻¹ := by
    filter_upwards [hAclose, hrelUpper, haPos] with n hclose hrel ha
    by_contra hnot
    have hlarge : εC⁻¹ < a n := lt_of_not_ge hnot
    have hprod : 1 < a n * εC := by
      have hlarge' : 1 / εC < a n := by simpa [one_div] using hlarge
      have := (div_lt_iff₀ hεC).1 hlarge'
      nlinarith
    have hinv' : 1 / a n < εC := (div_lt_iff₀ ha).2 (by nlinarith [hprod])
    have hinv : (a n)⁻¹ < εC := by simpa only [one_div] using hinv'
    have hnear := hCnearOne n (a n)⁻¹ (by simpa [abs_of_pos (inv_pos.mpr ha)] using hinv)
    have htriangle := dist_triangle (charFun ρ 1) (charFun (A n) 1) (1 : ℂ)
    have hsecond : dist (charFun (A n) 1) (1 : ℂ) < δC := by
      rw [hrel]
      simpa [dist_comm] using hnear
    have hsum : dist (charFun ρ 1) (1 : ℂ) < δC + δC := by
      exact htriangle.trans_lt (add_lt_add (by simpa [dist_comm] using hclose) hsecond)
    dsimp [δC] at hsum
    rw [dist_comm] at hsum
    have hgap := dist_pos.mpr (Ne.symm hρone_ne)
    linarith

  have hbounds : ∀ᶠ n : ℕ in atTop, εA ≤ a n ∧ a n ≤ εC⁻¹ :=
    haLower.and haUpper
  obtain ⟨n₀, hn₀⟩ := hbounds.exists
  have hK : IsCompact (Set.Icc εA εC⁻¹) := isCompact_Icc
  have hUniform :=
    MeasureTheory.tendstoUniformlyOn_charFun_of_tendsto hK hApoint
  have hcharRatio : Tendsto (fun n : ℕ => charFun ρ (a n)) atTop
      (nhds (charFun ρfactor 1)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hhalf : 0 < ε / 2 := by positivity
    have hCevent : ∀ᶠ n : ℕ in atTop,
        dist (charFun (C n) 1) (charFun ρfactor 1) < ε / 2 :=
      (hCpoint 1).eventually (Metric.ball_mem_nhds _ hhalf)
    have hUevent : ∀ᶠ n : ℕ in atTop,
        ∀ x ∈ Set.Icc εA εC⁻¹,
          dist (charFun ρ x) (charFun (A n) x) < ε / 2 :=
      (Metric.tendstoUniformlyOn_iff.mp hUniform) (ε / 2) hhalf
    filter_upwards [hCevent, hUevent, hbounds, hrelLower] with n hc hu hb hrel
    have hleft : dist (charFun ρ (a n)) (charFun (A n) (a n)) < ε / 2 :=
      hu (a n) ⟨hb.1, hb.2⟩
    have hright : dist (charFun (A n) (a n)) (charFun ρfactor 1) < ε / 2 := by
      rw [← hrel]
      exact hc
    calc
      dist (charFun ρ (a n)) (charFun ρfactor 1) ≤
          dist (charFun ρ (a n)) (charFun (A n) (a n)) +
            dist (charFun (A n) (a n)) (charFun ρfactor 1) :=
        dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add hleft hright
      _ = ε := by ring

  have hrealChar : Tendsto (fun n : ℕ => (charFun ρ (a n)).re) atTop
      (nhds (charFun ρfactor 1).re) :=
    Complex.continuous_re.continuousAt.tendsto.comp hcharRatio
  have hexpEq : (fun n : ℕ => Real.exp (-(2 * c * (a n) ^ α))) =ᶠ[atTop]
      fun n => (charFun ρ (a n)).re := by
    filter_upwards [haPos] with n ha
    rw [hρchar, Complex.ofReal_re, abs_of_pos ha]
  have hexpLimit : (charFun ρfactor 1).re = Real.exp (-(2 * c * ratio)) := by
    rw [hρfactorChar]
    simp only [Complex.ofReal_re, abs_one, Real.one_rpow]
    ring_nf
  have hexpReal : Tendsto (fun n : ℕ => Real.exp (-(2 * c * (a n) ^ α))) atTop
      (nhds (Real.exp (-(2 * c * ratio)))) := by
    exact (tendsto_congr' hexpEq).2 (by simpa [hexpLimit] using hrealChar)
  have hlogExp : Tendsto (fun n : ℕ => Real.log (Real.exp (-(2 * c * (a n) ^ α))))
      atTop (nhds (Real.log (Real.exp (-(2 * c * ratio))))) :=
    (Real.continuousAt_log (ne_of_gt (Real.exp_pos _))).tendsto.comp hexpReal
  have hpowerLinear : Tendsto (fun n : ℕ => -(2 * c * (a n) ^ α)) atTop
      (nhds (-(2 * c * ratio))) := by
    simpa only [Real.log_exp] using hlogExp
  have hpower : Tendsto (fun n : ℕ => (a n) ^ α) atTop (nhds ratio) := by
    have hmul := hpowerLinear.const_mul (-(2 * c))⁻¹
    have hlimit : (-(2 * c))⁻¹ * (-(2 * c * ratio)) = ratio := by
      field_simp [ne_of_gt hc]
    have hmul' : Tendsto
        (fun n : ℕ => (-(2 * c))⁻¹ * (-(2 * c * (a n) ^ α))) atTop
        (nhds ratio) := by
      simpa only [hlimit] using hmul
    have heq : (fun n : ℕ => (-(2 * c))⁻¹ * (-(2 * c * (a n) ^ α))) =ᶠ[atTop]
        fun n => (a n) ^ α := by
      filter_upwards [] with n
      field_simp [ne_of_gt hc]
    exact hmul'.congr' heq
  have hroot : Tendsto (fun n : ℕ => ((a n) ^ α) ^ α⁻¹) atTop
      (nhds (ratio ^ α⁻¹)) := by
    exact (Real.continuousAt_rpow_const ratio α⁻¹ (Or.inl hratio.ne')).tendsto.comp hpower
  have hrootEq : (fun n : ℕ => ((a n) ^ α) ^ α⁻¹) =ᶠ[atTop] a := by
    filter_upwards [haPos] with n ha
    rw [← Real.rpow_mul (le_of_lt ha)]
    rw [show α * α⁻¹ = 1 by field_simp [ne_of_gt hlimit.alpha_pos], Real.rpow_one]
  have hresult := hroot.congr' hrootEq
  simpa [a, factor] using hresult

/-- Consecutive values of a stable norming are asymptotically equivalent.
This is a consequence of the ratio theorem and does not assume monotonicity. -/
theorem IsInDomainOfAttractionAlong.tendsto_norming_succ_ratio
    {α : ℝ} {ν limit : Measure ℝ} [IsProbabilityMeasure ν]
    (hlimit : IsAlphaStable α limit)
    {scale center : ℕ → ℝ}
    (h : @IsInDomainOfAttractionAlong ν limit inferInstance
      hlimit.isProbabilityMeasure scale center) :
    Tendsto (fun n : ℕ => scale (n + 1) / scale n) atTop (nhds 1) := by
  have hInv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
  have hsum : Tendsto (fun n : ℕ => 1 + (n : ℝ)⁻¹) atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add hInv
  have hindex : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / (n : ℝ)) atTop
      (nhds 1) := by
    apply (tendsto_congr' ?_).2 hsum
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    push_cast
    field_simp [hn']
  simpa [Real.one_rpow] using
    h.tendsto_norming_ratio hlimit (fun n => n + 1) 1 (by norm_num) hindex

/-- A subsequence on the fixed dyadic scale tends to infinity. -/
private theorem tendsto_nat_half_atTop :
    Tendsto (fun n : ℕ => n / 2) atTop atTop := by
  have hfloor : Tendsto (fun n : ℕ => ⌊(1 / 2 : ℝ) * (n : ℝ)⌋₊) atTop atTop :=
    tendsto_nat_floor_mul_atTop (1 / 2 : ℝ) (by norm_num)
  have heq : (fun n : ℕ => ⌊(1 / 2 : ℝ) * (n : ℝ)⌋₊) =
      fun n => n / 2 := by
    funext n
    rw [show (1 / 2 : ℝ) * (n : ℝ) = (n : ℝ) / 2 by ring]
    change ⌊(n : ℝ) / (2 : ℕ)⌋₊ = n / 2
    exact Nat.floor_div_eq_div n 2
  rw [← heq]
  exact hfloor

/-- A stable domain-of-attraction norming diverges. The proof derives a
strict growth factor from the half-index ratio and iterates it by halving;
no monotonicity of the norming is used. -/
theorem IsInDomainOfAttractionAlong.tendsto_scale_atTop
    {α : ℝ} {ν limit : Measure ℝ} [IsProbabilityMeasure ν]
    (hlimit : IsAlphaStable α limit)
    {scale center : ℕ → ℝ}
    (h : @IsInDomainOfAttractionAlong ν limit inferInstance
      hlimit.isProbabilityMeasure scale center) :
    Tendsto scale atTop atTop := by
  letI : IsProbabilityMeasure limit := hlimit.isProbabilityMeasure
  have hhalfIndex : Tendsto (fun n : ℕ => ((n / 2 : ℕ) : ℝ) / (n : ℝ)) atTop
      (nhds (1 / 2)) := by
    have hfloor := (tendsto_nat_floor_mul_div_atTop
      (a := (1 / 2 : ℝ)) (by norm_num)).comp
      (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
    have heq : (fun n : ℕ =>
        (⌊(1 / 2 : ℝ) * (n : ℝ)⌋₊ : ℝ) / (n : ℝ)) =
        fun n => ((n / 2 : ℕ) : ℝ) / (n : ℝ) := by
      funext n
      rw [show (1 / 2 : ℝ) * (n : ℝ) = (n : ℝ) / 2 by ring]
      change (⌊(n : ℝ) / (2 : ℕ)⌋₊ : ℝ) / (n : ℝ) = _
      rw [Nat.floor_div_eq_div]
    exact hfloor.congr' (Filter.Eventually.of_forall fun n => congrFun heq n)
  have hhalfRatio := h.tendsto_norming_ratio hlimit (fun n => n / 2)
    (1 / 2 : ℝ) (by norm_num) hhalfIndex
  let r : ℝ := Real.rpow (1 / 2 : ℝ) α⁻¹
  have hrpos : 0 < r := by
    dsimp [r]
    exact Real.rpow_pos_of_pos (by norm_num) _
  have hrlt : r < 1 := by
    dsimp [r]
    exact Real.rpow_lt_one (by norm_num) (by norm_num)
      (inv_pos.mpr hlimit.alpha_pos)
  let q : ℝ := (r + 1) / 2
  have hqpos : 0 < q := by dsimp [q]; linarith
  have hrq : r < q := by dsimp [q]; linarith
  have hqone : q < 1 := by dsimp [q]; linarith
  have hratioEventually : ∀ᶠ n : ℕ in atTop,
      scale (n / 2) / scale n < q := by
    have := hhalfRatio.eventually (Iio_mem_nhds hrq)
    simpa [r] using this
  obtain ⟨Npos, hNpos⟩ := Filter.eventually_atTop.1 h.eventually_scale_pos
  obtain ⟨Nratio, hNratio⟩ := Filter.eventually_atTop.1 hratioEventually
  let N : ℕ := max Npos (max Nratio 1)
  have hN : 0 < N := by dsimp [N]; omega
  have hNpos' : Npos ≤ N := by dsimp [N]; omega
  have hNratio' : Nratio ≤ N := by dsimp [N]; omega
  have hbasePositive : ∀ n, N ≤ n → 0 < scale n := by
    intro n hn
    exact hNpos n (le_trans hNpos' hn)
  have hstep : ∀ n, N ≤ n → q⁻¹ * scale (n / 2) ≤ scale n := by
    intro n hn
    have hqratio := hNratio n (le_trans hNratio' hn)
    have hden : 0 < scale n := hbasePositive n hn
    have hmul : scale (n / 2) < q * scale n :=
      (div_lt_iff₀ hden).1 hqratio
    exact le_of_lt (calc
      q⁻¹ * scale (n / 2) < q⁻¹ * (q * scale n) :=
        mul_lt_mul_of_pos_left hmul (inv_pos.mpr hqpos)
      _ = scale n := by field_simp
      )
  let baseRange : Finset ℕ := Finset.Ico N (2 * N)
  have hbaseRange : baseRange.Nonempty := by
    refine ⟨N, ?_⟩
    simp only [baseRange, Finset.mem_Ico]
    omega
  let c : ℝ := baseRange.inf' hbaseRange scale
  have hc : 0 < c := by
    obtain ⟨i, hi, hci⟩ := Finset.exists_mem_eq_inf' (s := baseRange)
      hbaseRange scale
    rw [show c = baseRange.inf' hbaseRange scale by rfl, hci]
    have hi' : N ≤ i := (Finset.mem_Ico.mp hi).1
    exact hbasePositive i hi'
  have hbase : ∀ n, N ≤ n → n < 2 * N → c ≤ scale n := by
    intro n hn₁ hn₂
    have hnmem : n ∈ baseRange := by simp [baseRange, hn₁, hn₂]
    exact Finset.inf'_le _ hnmem
  have hp : 1 < q⁻¹ := (one_lt_inv₀ hqpos).2 hqone
  exact tendsto_atTop_of_halving_growth N hN c q⁻¹ hc hp hbase hstep

end ProbabilityTheory

end
