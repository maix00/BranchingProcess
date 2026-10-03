/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import MeasureTheory.Measure.CharacteristicFunction.Convergence
public import Probability.Distributions.Stable.Attraction.CharacteristicFunction

/-!
# Compact-uniform characteristic-function defects

Weak convergence of symmetrized normalized sums first gives compact-uniform
convergence of their characteristic functions. Positivity of the stable limit
then permits logarithms, and a uniform exponential remainder gives the
compact-uniform squared-modulus defect.
-/

open Filter MeasureTheory
open scoped Topology Uniformity

@[expose] public section

namespace ProbabilityTheory

private noncomputable def symmetrizedMeasure (ν : Measure ℝ) : Measure ℝ :=
  ν ∗ ν.map (fun x : ℝ => -x)

private theorem charFun_symmetrizedMeasure {ν : Measure ℝ}
    [IsProbabilityMeasure ν] (t : ℝ) :
    charFun (symmetrizedMeasure ν) t = (‖charFun ν t‖ ^ 2 : ℂ) := by
  have hneg : charFun (ν.map (fun x : ℝ => -x)) t = charFun ν (-t) := by
    have hmap : (fun x : ℝ => -x) = fun x => (-1 : ℝ) * x := by
      funext x
      ring
    rw [hmap, charFun_map_mul, neg_one_mul]
  rw [symmetrizedMeasure, charFun_conv, hneg, charFun_neg, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  norm_cast

private noncomputable def normalizedSymmetricSumLaw (ν : Measure ℝ)
    (scale : ℝ) (count : ℕ) : Measure ℝ :=
  (iidSequenceLaw (symmetrizedMeasure ν)).map
    (normalizedIidSum (fun _ => scale) (fun _ => 0) count)

private theorem charFun_normalizedSymmetricSumLaw {ν : Measure ℝ}
    [IsProbabilityMeasure ν] (scale : ℝ) (count : ℕ) (t : ℝ) :
    charFun (normalizedSymmetricSumLaw ν scale count) t =
      (‖charFun ν (scale⁻¹ * t)‖ ^ (2 * count) : ℂ) := by
  haveI : IsProbabilityMeasure (symmetrizedMeasure ν) := by
    dsimp [symmetrizedMeasure]
    infer_instance
  rw [normalizedSymmetricSumLaw, charFun_map_normalizedIidSum]
  simp [charFun_symmetrizedMeasure]
  rw [pow_mul]

/-- A uniform logarithmic limit controls the corresponding exponential
defect. The compact parameter set is arbitrary; the boundedness assumption is
only on the limiting function. -/
private theorem tendstoUniformlyOn_scaledExpDefect
    {K : Set ℝ} {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (hg : ∀ t ∈ K, g t ≤ M)
    (hfg : TendstoUniformlyOn f g atTop K)
    (hf_nonneg : ∀ᶠ n : ℕ in atTop, ∀ t ∈ K, 0 ≤ f n t) :
    TendstoUniformlyOn
      (fun (n : ℕ) t => (n : ℝ) * (1 - Real.exp (-(f n t) / (n : ℝ))))
      g atTop K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hεhalf : 0 < ε / 2 := by positivity
  have hclose := (Metric.tendstoUniformlyOn_iff.mp hfg) (ε / 2) hεhalf
  have hbounded := (Metric.tendstoUniformlyOn_iff.mp hfg) 1 (by norm_num)
  let M' : ℝ := M + 1
  have hM' : 0 < M' := by dsimp [M']; linarith
  have hlarge : ∀ᶠ n : ℕ in atTop,
      M' ^ 2 / (ε / 2) < (n : ℝ) ∧ M' ≤ (n : ℝ) := by
    have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hev := hnat.eventually_gt_atTop (max (M' ^ 2 / (ε / 2)) M')
    filter_upwards [hev] with n hn
    exact ⟨lt_of_le_of_lt (le_max_left _ _) hn,
      le_of_lt (lt_of_le_of_lt (le_max_right _ _) hn)⟩
  filter_upwards [hclose, hbounded, hf_nonneg, hlarge,
    eventually_gt_atTop (0 : ℕ)] with n hcloseN hboundedN hnonnegN hlargeN hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  intro t ht
  have hfnBound : f n t ≤ M' := by
    have hdist := hboundedN t ht
    rw [Real.dist_eq] at hdist
    have hshift : f n t - g t ≤ |g t - f n t| := by
      calc
        f n t - g t = -(g t - f n t) := by ring
        _ ≤ |-(g t - f n t)| := le_abs_self _
        _ = |g t - f n t| := abs_neg _
    have hgt := hg t ht
    dsimp [M']
    linarith
  let z : ℝ := f n t / (n : ℝ)
  have hzNonneg : 0 ≤ z := by
    dsimp [z]
    exact div_nonneg (hnonnegN t ht) hnR.le
  have hzLe : z ≤ 1 := by
    dsimp [z]
    exact (div_le_one hnR).2 (hfnBound.trans hlargeN.2)
  have harg : |(-z)| ≤ 1 := by
    rw [abs_neg, abs_of_nonneg hzNonneg]
    exact hzLe
  have hTaylor := Real.abs_exp_sub_one_sub_id_le harg
  have herror : |(n : ℝ) * (1 - Real.exp (-z)) - f n t| ≤ M' ^ 2 / (n : ℝ) := by
    have hidentity : (n : ℝ) * (1 - Real.exp (-z)) - f n t =
        (n : ℝ) * (1 - Real.exp (-z) - z) := by
      dsimp [z]
      field_simp [hnR.ne']
    rw [hidentity, abs_mul, abs_of_pos hnR]
    have hTaylor' : |1 - Real.exp (-z) - z| ≤ z ^ 2 := by
      rw [show 1 - Real.exp (-z) - z = -(Real.exp (-z) - 1 + z) by ring,
        abs_neg]
      simpa using hTaylor
    have hsq : z ^ 2 = (f n t) ^ 2 / (n : ℝ) ^ 2 := by
      dsimp [z]
      rw [div_pow]
    calc
      (n : ℝ) * |1 - Real.exp (-z) - z| ≤ (n : ℝ) * z ^ 2 :=
        mul_le_mul_of_nonneg_left hTaylor' hnR.le
      _ = (n : ℝ) * ((f n t) ^ 2 / (n : ℝ) ^ 2) := by rw [hsq]
      _ ≤ (n : ℝ) * (M' ^ 2 / (n : ℝ) ^ 2) := by
        have hsqBound : (f n t) ^ 2 ≤ M' ^ 2 := by
          have hnonneg : 0 ≤ f n t := hnonnegN t ht
          nlinarith [sq_nonneg (f n t), sq_nonneg M']
        exact mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hsqBound (sq_nonneg (n : ℝ))) hnR.le
      _ = M' ^ 2 / (n : ℝ) := by
        field_simp [hnR.ne']
  have herrorSmall : |(n : ℝ) * (1 - Real.exp (-z)) - f n t| < ε / 2 := by
    apply lt_of_le_of_lt herror
    apply (div_lt_iff₀ hnR).2
    have hmul := (div_lt_iff₀ hεhalf).1 hlargeN.1
    nlinarith
  have hclosePoint := hcloseN t ht
  rw [Real.dist_eq] at hclosePoint
  have hclosePoint' : |f n t - g t| < ε / 2 := by
    simpa [abs_sub_comm] using hclosePoint
  have herrorSmall' : |f n t - (n : ℝ) * (1 - Real.exp (-z))| < ε / 2 := by
    simpa [abs_sub_comm] using herrorSmall
  calc
    dist (g t) ((n : ℝ) * (1 - Real.exp (-(f n t) / (n : ℝ)))) =
        |g t - ((n : ℝ) * (1 - Real.exp (-z)))| := by
          rw [Real.dist_eq]
          congr 1
          simp [z, neg_div]
    _ ≤ |g t - f n t| + |f n t - (n : ℝ) * (1 - Real.exp (-z))| :=
          abs_sub_le _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add hclosePoint herrorSmall'
    _ = ε := by ring

/-- On every compact frequency set, the squared-modulus defect of an
attracted increment law converges uniformly to the stable power function.
No moment condition on the increment law is used. -/
theorem IsInDomainOfAttractionAlong.exists_tendstoUniformlyOn_normDefect
    {α : ℝ} {ν limit : Measure ℝ} [IsProbabilityMeasure ν]
    (hlimit : IsAlphaStable α limit)
    {scale center : ℕ → ℝ}
    (h : @IsInDomainOfAttractionAlong ν limit inferInstance
      hlimit.isProbabilityMeasure scale center)
    {K : Set ℝ} (hK : IsCompact K) :
    ∃ c : ℝ, 0 < c ∧
    TendstoUniformlyOn
        (fun (n : ℕ) t => (n : ℝ) *
          (1 - ‖charFun ν ((scale n)⁻¹ * t)‖ ^ 2))
        (fun t => 2 * c * |t| ^ α) atTop K := by
  letI : IsProbabilityMeasure limit := hlimit.isProbabilityMeasure
  obtain ⟨c, hc, hchar⟩ := hlimit.exists_pos_norm_charFun_eq_exp
  let ρ := symmetrizedMeasure limit
  let A : ℕ → Measure ℝ := fun n => normalizedSymmetricSumLaw ν (scale n) n
  haveI hη : IsProbabilityMeasure (symmetrizedMeasure ν) := by
    dsimp [symmetrizedMeasure]
    infer_instance
  haveI hρ : IsProbabilityMeasure ρ := by
    dsimp [ρ, symmetrizedMeasure]
    infer_instance
  haveI hA : ∀ n, IsProbabilityMeasure (A n) := by
    intro n
    dsimp [A, normalizedSymmetricSumLaw]
    infer_instance
  have hρchar (t : ℝ) :
      charFun ρ t = (Real.exp (-(2 * c * |t| ^ α)) : ℂ) := by
    rw [show ρ = symmetrizedMeasure limit by rfl,
      charFun_symmetrizedMeasure, hchar t]
    norm_cast
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hApoint (t : ℝ) : Tendsto (fun n : ℕ => charFun (A n) t) atTop
      (nhds (charFun ρ t)) := by
    let u : ℕ → ℝ := fun n => ‖charFun ν ((scale n)⁻¹ * t)‖
    have huPow : Tendsto (fun n : ℕ => u n ^ n) atTop
        (nhds (Real.exp (-c * |t| ^ α))) := by
      simpa [u, hchar t] using h.tendsto_norm_charFun_oneStep_pow t
    have huSquare : Tendsto (fun n : ℕ => (u n ^ n) * (u n ^ n)) atTop
        (nhds (Real.exp (-c * |t| ^ α) * Real.exp (-c * |t| ^ α))) :=
      huPow.mul huPow
    have hformula (n : ℕ) : charFun (A n) t =
        (↑(u n ^ n * u n ^ n) : ℂ) := by
      change charFun (normalizedSymmetricSumLaw ν (scale n) n) t = _
      rw [charFun_normalizedSymmetricSumLaw]
      dsimp [u]
      rw [show 2 * n = n + n by omega, pow_add]
      simp only [Complex.ofReal_pow, Complex.ofReal_mul]
    have hcast := Complex.continuous_ofReal.continuousAt.tendsto.comp huSquare
    have hlim :
        (↑(Real.exp (-c * |t| ^ α) * Real.exp (-c * |t| ^ α)) : ℂ) =
          charFun ρ t := by
      rw [hρchar]
      norm_cast
      rw [← Real.exp_add]
      congr 1
      ring
    convert hcast using 1
    · funext n
      rw [hformula]
      norm_cast
    · rw [← hlim]
  have hUniformChar := MeasureTheory.tendstoUniformlyOn_charFun_of_tendsto hK hApoint
  have hUniformReal : TendstoUniformlyOn
      (fun n t => (charFun (A n) t).re)
      (fun t => (charFun ρ t).re) atTop K := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hC := (Metric.tendstoUniformlyOn_iff.mp hUniformChar) ε hε
    filter_upwards [hC] with n hn t ht
    have hcomplex := hn t ht
    calc
      dist ((charFun ρ t).re) ((charFun (A n) t).re) =
          |(charFun ρ t - charFun (A n) t).re| := by
            rw [Real.dist_eq, Complex.sub_re]
      _ ≤ ‖charFun ρ t - charFun (A n) t‖ :=
        RCLike.abs_re_le_norm (charFun ρ t - charFun (A n) t)
      _ = dist (charFun ρ t) (charFun (A n) t) := (dist_eq_norm _ _).symm
      _ < ε := hcomplex
  let H : ℝ → ℝ := fun t => 2 * c * |t| ^ α
  let G : ℝ → ℝ := fun t => Real.exp (-H t)
  obtain ⟨R, hR, hKR⟩ := hK.isBounded.subset_closedBall_lt 0 (0 : ℝ)
  have hRnonneg : 0 ≤ R := le_of_lt hR
  have hHt : ∀ t ∈ K, 0 ≤ H t ∧ H t ≤ 2 * c * R ^ α := by
    intro t ht
    have htR : |t| ≤ R := by
      have := hKR ht
      simpa [Metric.mem_closedBall, Real.dist_eq] using this
    have hpow : |t| ^ α ≤ R ^ α := Real.rpow_le_rpow
      (abs_nonneg t) htR hlimit.alpha_pos.le
    constructor
    · dsimp [H]
      positivity
    · dsimp [H]
      exact mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 2 * c)
  let M : ℝ := 2 * c * R ^ α
  have hMnonneg : 0 ≤ M := by dsimp [M]; positivity
  have hGbounds : ∀ t ∈ K, G t ∈ Set.Icc (Real.exp (-M)) 1 := by
    intro t ht
    have ⟨hH0, hHupper⟩ := hHt t ht
    constructor
    · dsimp [G, H, M]
      exact Real.exp_le_exp.mpr (by nlinarith)
    · dsimp [G]
      exact Real.exp_le_one_iff.mpr (by dsimp [H]; nlinarith [hH0])
  let δ : ℝ := Real.exp (-M) / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  let L : Set ℝ := Set.Icc δ 1
  have hLcompact : IsCompact L := isCompact_Icc
  have hlogUC : UniformContinuousOn Real.log L :=
    hLcompact.uniformContinuousOn_of_continuous
      (Real.continuousOn_log.mono (by
        intro x hx
        change x ∈ Set.Icc δ 1 at hx
        exact ne_of_gt (lt_of_lt_of_le hδ hx.1)))
  let F : ℕ → ℝ → ℝ := fun n t => (charFun (A n) t).re
  have hAcharFormula (n : ℕ) (t : ℝ) :
      charFun (A n) t =
        (↑(‖charFun ν ((scale n)⁻¹ * t)‖ ^ (2 * n)) : ℂ) := by
    simpa [A] using charFun_normalizedSymmetricSumLaw (ν := ν) (scale n) n t
  have hFbounds : ∀ n t, 0 ≤ F n t ∧ F n t ≤ 1 := by
    intro n t
    rw [show F n t = (‖charFun ν ((scale n)⁻¹ * t)‖ ^ (2 * n) : ℝ) by
        simp only [F, hAcharFormula, Complex.ofReal_re]]
    constructor
    · positivity
    · exact pow_le_one₀ (norm_nonneg _) (norm_charFun_le_one _)
  have hrealLimit : ∀ t, (charFun ρ t).re = G t := by
    intro t
    rw [hρchar]
    simp only [Complex.ofReal_re]
    simp [G, H]
  have hGintoL : ∀ t ∈ K, G t ∈ L := by
    intro t ht
    have h := hGbounds t ht
    constructor
    · have hδle : δ ≤ Real.exp (-M) := by dsimp [δ]; linarith [Real.exp_pos (-M)]
      exact hδle.trans h.1
    · exact h.2
  have hUniformF : TendstoUniformlyOn F G atTop K := by
    have hlimitEq : G = fun t => (charFun ρ t).re := by
      funext t
      exact (hrealLimit t).symm
    simpa only [F, ← hlimitEq] using hUniformReal
  have hFintoLEventually : ∀ᶠ n : ℕ in atTop, ∀ t ∈ K, F n t ∈ L := by
    have hclose := (Metric.tendstoUniformlyOn_iff.mp hUniformF) (δ / 2) (by positivity)
    filter_upwards [hclose] with n hn t ht
    have hdist := hn t ht
    rw [Real.dist_eq] at hdist
    have hGap : δ < F n t := by
      have hlow := (abs_lt.mp hdist).2
      have hGlo : 2 * δ ≤ G t := by
        rw [show 2 * δ = Real.exp (-M) by dsimp [δ]; ring]
        exact (hGbounds t ht).1
      linarith
    exact ⟨le_of_lt hGap, (hFbounds n t).2⟩
  have hLogUniform : TendstoUniformlyOn
      (fun n t => Real.log (F n t)) (fun t => Real.log (G t)) atTop K :=
    hlogUC.comp_tendstoUniformlyOn_eventually hFintoLEventually hGintoL hUniformF
  have hlogToPower : TendstoUniformlyOn
      (fun n t => -(Real.log (F n t))) H atTop K := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have h := (Metric.tendstoUniformlyOn_iff.mp hLogUniform) ε hε
    filter_upwards [h] with n hn t ht
    have hh := hn t ht
    have hlogG : Real.log (G t) = -H t := by
      simp [G, Real.log_exp]
    rw [hlogG] at hh
    have hneg : -H t - Real.log (F n t) = -(H t + Real.log (F n t)) := by ring
    have htarget : dist (H t) (-Real.log (F n t)) =
        dist (-H t) (Real.log (F n t)) := by
      rw [Real.dist_eq, Real.dist_eq]
      rw [show H t - -Real.log (F n t) = -( -H t - Real.log (F n t)) by ring,
        abs_neg]
    rw [htarget]
    exact hh
  have hlogNonneg : ∀ᶠ n : ℕ in atTop, ∀ t ∈ K, 0 ≤ -(Real.log (F n t)) := by
    filter_upwards [hFintoLEventually] with n hn t ht
    have hFle := (hn t ht).2
    have hFpos : 0 < F n t := lt_of_lt_of_le hδ (hn t ht).1
    exact neg_nonneg.mpr (Real.log_nonpos hFpos.le hFle)
  have hlogBound : ∀ t ∈ K, H t ≤ M := by
    intro t ht
    exact hHt t ht |>.2
  have hdefectUniform := tendstoUniformlyOn_scaledExpDefect hMnonneg hlogBound
    hlogToPower hlogNonneg
  refine ⟨c, hc, ?_⟩
  have hEqOn : ∀ᶠ n : ℕ in atTop, Set.EqOn
      (fun t => (n : ℝ) *
        (1 - Real.exp (-(-(Real.log (F n t))) / (n : ℝ))))
      (fun t => (n : ℝ) *
        (1 - ‖charFun ν ((scale n)⁻¹ * t)‖ ^ 2)) K := by
    filter_upwards [hFintoLEventually, eventually_gt_atTop 0] with n hnF hn t htK
    have hFpos : 0 < F n t := lt_of_lt_of_le hδ (hnF t htK).1
    let q : ℝ := ‖charFun ν ((scale n)⁻¹ * t)‖ ^ 2
    have hqnonneg : 0 ≤ q := by dsimp [q]; positivity
    have hpow : q ^ n = F n t := by
      rw [show q ^ n = ‖charFun ν ((scale n)⁻¹ * t)‖ ^ (2 * n) by
        dsimp [q]
        rw [← pow_mul]]
      have hformulaReal : F n t = ‖charFun ν ((scale n)⁻¹ * t)‖ ^ (2 * n) := by
        dsimp [F]
        rw [hAcharFormula]
        exact Complex.ofReal_re _
      rw [hformulaReal]
    have hqpos : 0 < q := by
      by_contra hq
      have hqzero : q = 0 := le_antisymm (le_of_not_gt hq) hqnonneg
      rw [hqzero, zero_pow hn.ne'] at hpow
      linarith
    have hlogpow : Real.log (F n t) = (n : ℝ) * Real.log q := by
      rw [← hpow, Real.log_pow]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hlogq : Real.log q = Real.log (F n t) / (n : ℝ) := by
      rw [hlogpow]
      field_simp
    have hqexp : q = Real.exp (-(-(Real.log (F n t))) / (n : ℝ)) := by
      calc
        q = Real.exp (Real.log q) := (Real.exp_log hqpos).symm
        _ = Real.exp (Real.log (F n t) / (n : ℝ)) := by rw [hlogq]
        _ = Real.exp (-(-(Real.log (F n t))) / (n : ℝ)) := by congr 1 <;> ring
    change (n : ℝ) * (1 - Real.exp (-(-(Real.log (F n t))) / (n : ℝ))) =
      (n : ℝ) * (1 - q)
    rw [hqexp]
  /- Equality of the logarithmic representation and the original defect holds
  on the compact frequency set, where the limiting characteristic function is
  bounded away from zero. -/
  exact hdefectUniform.congr hEqOn

end ProbabilityTheory

end
