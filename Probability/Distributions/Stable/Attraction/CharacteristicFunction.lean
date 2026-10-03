module

public import Probability.Distributions.Stable.Attraction
public import Probability.Distributions.Stable.CharacteristicFunction
public import Probability.Sequence.IID.CharacteristicFunction
public import Mathlib.MeasureTheory.Measure.LevyConvergence

/-!
# Characteristic functions in a domain of attraction

The characteristic function of a normalized i.i.d. sum is written explicitly
in terms of the one-step characteristic function, scale, and centering.
-/

open Filter MeasureTheory
open scoped Topology

@[expose] public section

namespace ProbabilityTheory

/-- The characteristic function of a normalized centered sum under the
canonical i.i.d. sequence law. -/
theorem charFun_map_normalizedIidSum
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (scale center : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    charFun ((iidSequenceLaw ν).map (normalizedIidSum scale center n)) t =
      (charFun ν ((scale n)⁻¹ * t)) ^ n *
        Complex.exp ((inner ℝ (-((scale n)⁻¹ * center n)) t) * Complex.I) := by
  let S : (ℕ → ℝ) → ℝ := fun sequence =>
    ∑ k ∈ Finset.range n, sequence k
  let r : ℝ := (scale n)⁻¹
  let q : ℝ := -(r * center n)
  have hnorm : normalizedIidSum scale center n = fun sequence => r * S sequence + q := by
    funext sequence
    simp [normalizedIidSum, S, r, q]
    ring
  have hsumMeas : AEMeasurable S (iidSequenceLaw ν) := by
    exact (Finset.measurable_sum (Finset.range n)
      (fun k _ => measurable_pi_apply k)).aemeasurable
  have hsumChar := iidSequenceLaw_charFun_sum (ν := ν) n
  rw [hnorm]
  have hmap : (iidSequenceLaw ν).map (fun sequence => r * S sequence + q) =
      ((iidSequenceLaw ν).map (fun sequence => r * S sequence)).map (fun x => x + q) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [hmap, charFun_map_add_const]
  rw [charFun_map_mul_comp hsumMeas r t, hsumChar]

/-- Convergence in distribution in a stable domain of attraction forces the
corresponding explicit characteristic-function expression to converge. -/
theorem IsInDomainOfAttractionAlong.tendsto_charFun_normalizedIidSum
    {ν limit : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure limit]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν limit scale center) (t : ℝ) :
    Tendsto
      (fun n => (charFun ν ((scale n)⁻¹ * t)) ^ n *
        Complex.exp ((inner ℝ (-((scale n)⁻¹ * center n)) t) * Complex.I))
      atTop (nhds (charFun limit t)) := by
  have hchar := h.tendstoInDistribution.tendsto_charFun t
  have heq : (fun n =>
      charFun ((iidSequenceLaw ν).map (normalizedIidSum scale center n)) t) =ᶠ[atTop]
      (fun n => (charFun ν ((scale n)⁻¹ * t)) ^ n *
        Complex.exp ((inner ℝ (-((scale n)⁻¹ * center n)) t) * Complex.I)) := by
    filter_upwards [] with n
    exact charFun_map_normalizedIidSum (ν := ν) scale center n t
  simpa using hchar.congr' heq

/-- Taking absolute values removes the deterministic centering phase from the
domain-of-attraction characteristic-function limit. -/
theorem IsInDomainOfAttractionAlong.tendsto_norm_charFun_oneStep_pow
    {ν limit : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure limit]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν limit scale center) (t : ℝ) :
    Tendsto (fun n => ‖charFun ν ((scale n)⁻¹ * t)‖ ^ n)
      atTop (nhds ‖charFun limit t‖) := by
  have hcomplex := h.tendsto_charFun_normalizedIidSum t
  have hnorm := hcomplex.norm
  have hphase (n : ℕ) :
      ‖Complex.exp (inner ℝ (-((scale n)⁻¹ * center n)) t * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  have heq : (fun n =>
      ‖(charFun ν ((scale n)⁻¹ * t)) ^ n *
        Complex.exp (inner ℝ (-((scale n)⁻¹ * center n)) t * Complex.I)‖) =
      fun n => ‖charFun ν ((scale n)⁻¹ * t)‖ ^ n := by
    funext n
    rw [norm_mul, norm_pow, hphase]
    simp
  rw [heq] at hnorm
  exact hnorm

/-- For a law in the domain of attraction of a nondegenerate alpha-stable law,
the logarithmic characteristic-function defect has the stable first-order
asymptotic. The stable-law modulus constant is obtained internally from the
abstract stability hypothesis. -/
theorem IsInDomainOfAttractionAlong.exists_pos_tendsto_log_norm_charFun_and_norm_defect
    {α : ℝ} {ν limit : Measure ℝ} [IsProbabilityMeasure ν]
    {scale center : ℕ → ℝ}
    (hlimit : IsAlphaStable α limit)
    (h : @IsInDomainOfAttractionAlong ν limit inferInstance
      hlimit.isProbabilityMeasure scale center) (t : ℝ) :
    ∃ c : ℝ, 0 < c ∧
      Tendsto
        (fun n : ℕ => (n : ℝ) * (-Real.log ‖charFun ν ((scale n)⁻¹ * t)‖))
        atTop (nhds (c * |t| ^ α)) ∧
      Tendsto
        (fun n : ℕ => (n : ℝ) * (1 - ‖charFun ν ((scale n)⁻¹ * t)‖ ^ 2))
        atTop (nhds (2 * c * |t| ^ α)) := by
  letI : IsProbabilityMeasure limit := hlimit.isProbabilityMeasure
  obtain ⟨c, hc, hchar⟩ := hlimit.exists_pos_norm_charFun_eq_exp
  let u : ℕ → ℝ := fun n => ‖charFun ν ((scale n)⁻¹ * t)‖
  let C : ℝ := c * |t| ^ α
  have hpow : Tendsto (fun n : ℕ => u n ^ n) atTop (nhds (Real.exp (-C))) := by
    simpa [u, C, hchar t] using h.tendsto_norm_charFun_oneStep_pow t
  have hCexp : 0 < Real.exp (-C) := Real.exp_pos _
  have hlogpow :
      Tendsto (fun n : ℕ => -Real.log (u n ^ n)) atTop (nhds C) := by
    have h :=
      (ContinuousAt.neg (Real.continuousAt_log (ne_of_gt hCexp))).tendsto.comp hpow
    convert h using 1 <;> simp [Function.comp_def, Real.log_exp]
  have huPowPos : ∀ᶠ n : ℕ in atTop, 0 < u n ^ n :=
    hpow.eventually (Ioi_mem_nhds hCexp)
  have hnPos : ∀ᶠ n : ℕ in atTop, 0 < n := by
    exact eventually_atTop.2 ⟨1, fun n hn => Nat.lt_of_lt_of_le Nat.zero_lt_one hn⟩
  have huPos : ∀ᶠ n : ℕ in atTop, 0 < u n := by
    filter_upwards [huPowPos, hnPos] with n hpow_pos hn
    by_contra hnot
    have hu0 : u n = 0 := le_antisymm (le_of_not_gt hnot) (norm_nonneg _)
    simp [hu0, Nat.ne_of_gt hn] at hpow_pos
  have hlogEq :
      (fun n : ℕ => (n : ℝ) * (-Real.log (u n))) =ᶠ[atTop]
        fun n => -Real.log (u n ^ n) := by
    filter_upwards [huPos] with n hn
    rw [Real.log_pow]
    ring
  have hlog :
      Tendsto (fun n : ℕ => (n : ℝ) * (-Real.log (u n))) atTop (nhds C) :=
    hlogpow.congr' hlogEq.symm
  have hfirst :
      Tendsto
        (fun n : ℕ => (n : ℝ) * (-Real.log ‖charFun ν ((scale n)⁻¹ * t)‖))
        atTop (nhds (c * |t| ^ α)) := by
    simpa [u, C] using hlog
  refine ⟨c, hc, hfirst, ?_⟩
  by_cases ht : t = 0
  · subst t
    simp [hlimit.alpha_pos.ne']
  · have habs : 0 < |t| := abs_pos.mpr ht
    have hCpos : 0 < C := mul_pos hc (Real.rpow_pos_of_pos habs _)
    let x : ℕ → ℝ := fun n => -Real.log (u n)
    have hnRealPos : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) := by
      filter_upwards [hnPos] with n hn
      exact_mod_cast hn
    have hnInv : Tendsto (fun n : ℕ => (n : ℝ)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop :
        Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
    have hproductZero :
        Tendsto (fun n : ℕ => ((n : ℝ) * x n) * (n : ℝ)⁻¹) atTop (nhds 0) := by
      have hmul := hlog.mul hnInv
      simpa [x] using hmul
    have hproductEq :
        (fun n : ℕ => ((n : ℝ) * x n) * (n : ℝ)⁻¹) =ᶠ[atTop] x := by
      filter_upwards [hnRealPos] with n hn
      dsimp [x]
      field_simp
    have hxZero : Tendsto x atTop (nhds 0) := hproductZero.congr' hproductEq
    have hxPos : ∀ᶠ n : ℕ in atTop, 0 < x n := by
      filter_upwards [hlog.eventually (Ioi_mem_nhds hCpos), hnRealPos] with n hnx hn
      dsimp [x]
      exact (mul_pos_iff_of_pos_left hn).mp hnx
    have hxWithin : Tendsto x atTop (nhdsWithin 0 (Set.Ioi 0)) :=
      (tendsto_nhdsWithin_iff).2 ⟨hxZero, by simpa using hxPos⟩
    have hExpDeriv : HasDerivAt (fun z : ℝ => Real.exp (-2 * z)) (-2) 0 := by
      have hg : HasDerivAt (fun z : ℝ => -2 * z) (-2) 0 := by
        simpa using (hasDerivAt_const_mul (-2) : HasDerivAt (fun z : ℝ => -2 * z) (-2) 0)
      have he : HasDerivAt Real.exp 1 (-2 * 0) := by
        convert Real.hasDerivAt_exp 0 using 1 <;> norm_num
      convert he.comp 0 hg using 1 <;> norm_num [Function.comp_def]
    have hderiv : HasDerivAt (fun z : ℝ => 1 - Real.exp (-2 * z)) 2 0 := by
      convert (hasDerivAt_const 0 (1 : ℝ)).sub hExpDeriv using 1
      all_goals norm_num [Function.comp_def]
    have hratio :
        Tendsto (fun z : ℝ => z⁻¹ * (1 - Real.exp (-2 * z)))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 2) := by
      simpa [smul_eq_mul, Function.comp_def] using hderiv.tendsto_slope_zero_right
    have hratioSeq :
        Tendsto (fun n : ℕ => (x n)⁻¹ * (1 - Real.exp (-2 * x n)))
          atTop (nhds 2) := hratio.comp hxWithin
    have hsecondProduct :
        Tendsto
          (fun n : ℕ => ((n : ℝ) * x n) *
            ((x n)⁻¹ * (1 - Real.exp (-2 * x n))))
          atTop (nhds (C * 2)) := by
      exact hlog.mul hratioSeq
    have hexpEq : ∀ᶠ n : ℕ in atTop, Real.exp (-2 * x n) = u n ^ 2 := by
      filter_upwards [huPos] with n hn
      rw [show -2 * x n = Real.log (u n) + Real.log (u n) by
        dsimp [x]
        ring, Real.exp_add, Real.exp_log hn]
      ring
    have hdefectEq :
        (fun n : ℕ => (n : ℝ) * (1 - u n ^ 2)) =ᶠ[atTop]
          fun n => ((n : ℝ) * x n) *
            ((x n)⁻¹ * (1 - Real.exp (-2 * x n))) := by
      filter_upwards [hxPos, hexpEq] with n hn hexp
      rw [hexp]
      field_simp [ne_of_gt hn]
    have hdefect := hsecondProduct.congr' hdefectEq.symm
    have hdefectChar :
        Tendsto
          (fun n : ℕ => (n : ℝ) *
            (1 - ‖charFun ν ((scale n)⁻¹ * t)‖ ^ 2))
          atTop (nhds (C * 2)) := by
      simpa [u] using hdefect
    have hsecond :
        Tendsto
          (fun n : ℕ => (n : ℝ) * (1 - ‖charFun ν ((scale n)⁻¹ * t)‖ ^ 2))
          atTop (nhds (2 * c * |t| ^ α)) := by
      have hCmul : C * 2 = 2 * c * |t| ^ α := by
        dsimp [C]
        ring
      simpa only [hCmul] using hdefectChar
    exact hsecond

end ProbabilityTheory

end
