/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Probability.Distributions.CharacteristicFunction.CosineDefect
public import Probability.Distributions.CharacteristicFunction.Symmetrization
public import Probability.Distributions.Stable.Attraction.NormingRatios.RegularVariation
public import Probability.Distributions.Stable.Attraction.Norming
public import Probability.Distributions.CharacteristicFunction.Symmetrization.RegularVariation
public import Analysis.Asymptotics.RegularVariation.AtZero.Potter
public import Analysis.Fourier.CosineTauberian.Mellin
public import Analysis.Fourier.CosineTauberian.RegularVariation
public import Probability.Distributions.CharacteristicFunction.Tauberian.SecondTail

/-!
# Stable attraction and the symmetric cosine defect

The squared-modulus defect of an increment characteristic function is the
cosine defect of the symmetrized increment law. This bridge keeps the law
whose tail enters the inverse Tauberian theorem explicit.
-/

open Filter MeasureTheory
open scoped Topology
open Analysis.Fourier.CosineTauberian

@[expose] public section

namespace ProbabilityTheory

/-- In a stable domain of attraction, the cosine defect of the symmetrized
increment law is regularly varying at zero with the stable index. -/
theorem IsInDomainOfAttractionAlong.isRegularlyVarying_symmetrizedCosineDefect
    {α : ℝ} {ν limit : Measure ℝ} [IsProbabilityMeasure ν]
    (hlimit : IsAlphaStable α limit)
    {scale center : ℕ → ℝ}
    (h : @IsInDomainOfAttractionAlong ν limit inferInstance
      hlimit.isProbabilityMeasure scale center) :
    Asymptotics.IsRegularlyVaryingAtZero
      (fun u => cosineDefectIntegral (symmetrizedMeasure ν) u) α := by
  have hreg := h.isRegularlyVarying_normDefect_atZero hlimit
  refine ⟨?_, ?_⟩
  · filter_upwards [hreg.eventually_pos] with u hu
    simpa only [cosineDefectIntegral_symmetrizedMeasure] using hu
  · intro s hs
    have heq : (fun u : ℝ =>
        cosineDefectIntegral (symmetrizedMeasure ν) (s * u) /
          cosineDefectIntegral (symmetrizedMeasure ν) u) =ᶠ[𝓝[>] (0 : ℝ)]
        fun u => (1 - ‖charFun ν (s * u)‖ ^ 2) /
          (1 - ‖charFun ν u‖ ^ 2) := by
      filter_upwards [] with u
      rw [cosineDefectIntegral_symmetrizedMeasure,
        cosineDefectIntegral_symmetrizedMeasure]
    exact (hreg.ratio_tendsto hs).congr' heq.symm

/-- Potter bounds for the symmetrized cosine defect in a stable domain of
attraction. The bound is nonmonotone: it follows from compact-uniform ratio
convergence at multipliers in `[1, 2]`, not from monotonicity of the defect. -/
theorem IsInDomainOfAttractionAlong.exists_potter_bound_symmetrizedCosineDefect
    {α : ℝ} {ν limit : Measure ℝ} [IsProbabilityMeasure ν]
    (hlimit : IsAlphaStable α limit)
    {scale center : ℕ → ℝ}
    (h : @IsInDomainOfAttractionAlong ν limit inferInstance
      hlimit.isProbabilityMeasure scale center)
    {δ : ℝ} (hδ : 0 < δ) (hδα : δ < α) :
    ∃ U : ℝ, 0 < U ∧
      (∀ ⦃u : ℝ⦄, 0 < u → u < U →
        0 < cosineDefectIntegral (symmetrizedMeasure ν) u) ∧
      ∀ ⦃u v : ℝ⦄, 0 < u → u ≤ v → v < U →
      (1 / (2 * 2 ^ (α - δ))) * (v / u) ^ (α - δ) ≤
          cosineDefectIntegral (symmetrizedMeasure ν) v /
            cosineDefectIntegral (symmetrizedMeasure ν) u ∧
        cosineDefectIntegral (symmetrizedMeasure ν) v /
            cosineDefectIntegral (symmetrizedMeasure ν) u ≤
          (2 ^ α + 1) * (v / u) ^ (α + δ) := by
  let f : ℝ → ℝ := fun u => cosineDefectIntegral (symmetrizedMeasure ν) u
  have hreg := h.isRegularlyVarying_symmetrizedCosineDefect hlimit
  have hpos : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ), 0 < f u := by
    filter_upwards [hreg.eventually_pos] with u hu
    exact hu
  have huniform : TendstoUniformlyOn
      (fun u s => f (s * u) / f u) (fun s => s ^ α)
      (𝓝[>] (0 : ℝ)) (Set.Icc 1 2) := by
    simpa only [f, cosineDefectIntegral_symmetrizedMeasure] using
      h.tendstoUniformlyOn_normDefect_ratio_nhdsGT_zero hlimit
  simpa only [f] using
    (Asymptotics.IsRegularlyVaryingAtZero.exists_potter_bound_of_uniform_ratio
      hpos huniform hlimit.alpha_pos hδ hδα)

/-- A single power envelope for all rescaled symmetrized cosine defects in a
stable domain of attraction. This is the form used to dominate the Mellin
kernel integral; no monotonicity of the defect is assumed. -/
theorem IsInDomainOfAttractionAlong.exists_potter_envelope_symmetrizedCosineDefect
    {α : ℝ} {ν limit : Measure ℝ} [IsProbabilityMeasure ν]
    (hlimit : IsAlphaStable α limit)
    {scale center : ℕ → ℝ}
    (h : @IsInDomainOfAttractionAlong ν limit inferInstance
      hlimit.isProbabilityMeasure scale center)
    {δ : ℝ} (hδ : 0 < δ) (hδα : δ < α) :
    ∃ U C : ℝ, 0 < U ∧ 0 < C ∧
      (∀ ⦃u : ℝ⦄, 0 < u → u < U →
        0 < cosineDefectIntegral (symmetrizedMeasure ν) u) ∧
      ∀ ⦃u s : ℝ⦄, 0 < u → u < U → 0 < s → s * u < U →
        cosineDefectIntegral (symmetrizedMeasure ν) (s * u) /
          cosineDefectIntegral (symmetrizedMeasure ν) u ≤
          C * (s ^ (α - δ) + s ^ (α + δ)) := by
  let f : ℝ → ℝ := fun u => cosineDefectIntegral (symmetrizedMeasure ν) u
  have hreg := h.isRegularlyVarying_symmetrizedCosineDefect hlimit
  have hpos : ∀ᶠ u : ℝ in 𝓝[>] (0 : ℝ), 0 < f u := by
    filter_upwards [hreg.eventually_pos] with u hu
    exact hu
  have huniform : TendstoUniformlyOn
      (fun u s => f (s * u) / f u) (fun s => s ^ α)
      (𝓝[>] (0 : ℝ)) (Set.Icc 1 2) := by
    simpa only [f, cosineDefectIntegral_symmetrizedMeasure] using
      h.tendstoUniformlyOn_normDefect_ratio_nhdsGT_zero hlimit
  simpa only [f] using
    (Asymptotics.IsRegularlyVaryingAtZero.exists_potter_envelope_of_uniform_ratio
      hpos huniform hlimit.alpha_pos hδ hδα)

/-- In a stable domain of attraction with index in `(0, 2)`, the twice-
integrated tail of the symmetrized increment law is asymptotic to the
cosine-defect scale. The limiting constant is the Mellin moment of the
Tauberian kernel. -/
theorem IsInDomainOfAttractionAlong.tendsto_secondTailIntegral_ratio
    {α : ℝ} {ν limit : Measure ℝ} [IsProbabilityMeasure ν]
    (hlimit : IsAlphaStable α limit)
    {scale center : ℕ → ℝ}
    (h : @IsInDomainOfAttractionAlong ν limit inferInstance
      hlimit.isProbabilityMeasure scale center)
    (hα₀ : 0 < α) (hα₂ : α < 2) :
    Tendsto
      (fun x : ℝ =>
        Asymptotics.secondTailIntegral
          (fun t => (symmetrizedMeasure ν).real {y : ℝ | t < |y|}) x /
          (x ^ 3 * cosineDefectIntegral (symmetrizedMeasure ν) x⁻¹))
      atTop (nhds (Analysis.Fourier.CosineTauberian.cosineTauberianConstant α)) := by
  let μs : Measure ℝ := symmetrizedMeasure ν
  let f : ℝ → ℝ := cosineDefectIntegral μs
  have hreg : Asymptotics.IsRegularlyVaryingAtZero f α := by
    simpa [μs, f] using h.isRegularlyVarying_symmetrizedCosineDefect hlimit
  have hcont : Continuous f := by
    exact continuous_cosineDefectIntegral μs
  have huniform : TendstoUniformlyOn
      (fun u s => f (s * u) / f u) (fun s => s ^ α)
      (𝓝[>] (0 : ℝ)) (Set.Icc 1 2) := by
    simpa [μs, f, cosineDefectIntegral_symmetrizedMeasure] using
      h.tendstoUniformlyOn_normDefect_ratio_nhdsGT_zero hlimit
  let δ : ℝ := min α (2 - α) / 2
  have hδ₀ : 0 < δ := by dsimp [δ]; positivity
  have hδα : δ < α := by
    dsimp [δ]
    calc
      min α (2 - α) / 2 ≤ α / 2 := by
        exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
      _ < α := by linarith
  have hαδ₂ : α + δ < 2 := by
    dsimp [δ]
    have hmin' : min α (2 - α) / 2 < 2 - α := by
      calc
        min α (2 - α) / 2 ≤ (2 - α) / 2 := by
          exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
        _ < 2 - α := by linarith
    linarith
  have hM₀ : 0 ≤ (2 : ℝ) := by norm_num
  have hnonneg : ∀ x : ℝ, 0 ≤ f x := by
    intro x
    exact (cosineDefectIntegral_mem_Icc μs x).1
  have hbounded : ∀ x : ℝ, f x ≤ 2 := by
    intro x
    exact (cosineDefectIntegral_mem_Icc μs x).2
  let Q : ℝ → ℝ := fun u =>
    ∫ s in Set.Ioi (0 : ℝ), f (s * u) / f u * cosineTauberianKernel s
  have hQ : Tendsto Q (𝓝[>] (0 : ℝ))
      (nhds (cosineTauberianMellinMoment α)) := by
    simpa [Q, f, μs, cosineTauberianMellinMoment] using
      Analysis.Fourier.CosineTauberian.tendsto_integral_ratio_mul_cosineTauberianKernel
        hcont hreg huniform hα₀ hδ₀ hδα hαδ₂ hM₀ hnonneg hbounded
  have hQtop : Tendsto (fun x : ℝ => Q x⁻¹) atTop
      (nhds (cosineTauberianMellinMoment α)) :=
    hQ.comp tendsto_inv_atTop_nhdsGT_zero
  have hInv : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_inv_atTop_nhdsGT_zero
  have hposInv : ∀ᶠ x : ℝ in atTop, 0 < f x⁻¹ :=
    hInv.eventually hreg.eventually_pos
  have hevent : ∀ᶠ x : ℝ in atTop, 0 < x :=
    eventually_gt_atTop 0
  have hfactor : (fun x : ℝ =>
      Asymptotics.secondTailIntegral
        (fun t => μs.real {y : ℝ | t < |y|}) x /
        (x ^ 3 * f x⁻¹)) =ᶠ[atTop]
      fun x => (2 / Real.pi) * Q x⁻¹ := by
    filter_upwards [hevent, hposInv] with x hxpos hfupos
    have hu : 0 < x⁻¹ := inv_pos.mpr hxpos
    have hkernel := secondTailIntegral_eq_cosineDefect_kernel μs hxpos
    have hQeq : Q x⁻¹ = (f x⁻¹)⁻¹ *
        (∫ s in Set.Ioi (0 : ℝ), f (s / x) * cosineTauberianKernel s) := by
      dsimp [Q]
      calc
        (∫ s in Set.Ioi (0 : ℝ), f (s * x⁻¹) / f x⁻¹ *
            cosineTauberianKernel s) =
          ∫ s in Set.Ioi (0 : ℝ), (f x⁻¹)⁻¹ *
            (f (s / x) * cosineTauberianKernel s) := by
              apply integral_congr_ae
              filter_upwards [] with s
              have hsx : s * x⁻¹ = s / x := by
                simp [div_eq_mul_inv]
              rw [hsx, div_eq_mul_inv]
              ring
        _ = (f x⁻¹)⁻¹ *
            (∫ s in Set.Ioi (0 : ℝ), f (s / x) * cosineTauberianKernel s) :=
              integral_const_mul _ _
    have htail := hkernel
    dsimp [μs, f] at htail
    rw [htail, hQeq]
    field_simp [ne_of_gt hxpos, ne_of_gt hfupos]
    ring
  have hlimit := hQtop.const_mul (2 / Real.pi)
  have hratio : Tendsto
      (fun x : ℝ =>
        Asymptotics.secondTailIntegral
          (fun t => μs.real {y : ℝ | t < |y|}) x /
          (x ^ 3 * f x⁻¹)) atTop
      (nhds ((2 / Real.pi) * cosineTauberianMellinMoment α)) := by
    exact hlimit.congr' hfactor.symm
  simpa [f, μs, Analysis.Fourier.CosineTauberian.cosineTauberianConstant] using hratio

/-- The exact second-tail asymptotic transfers regular variation of the
characteristic defect to the two-sided tail of the symmetrized increment law.
The inverse step is Mathlib's monotone second-tail Tauberian theorem. -/
theorem IsInDomainOfAttractionAlong.isRegularlyVarying_symmetrizedTwoSidedTail
    {α : ℝ} {ν limit : Measure ℝ} [IsProbabilityMeasure ν]
    (hlimit : IsAlphaStable α limit)
    {scale center : ℕ → ℝ}
    (h : @IsInDomainOfAttractionAlong ν limit inferInstance
      hlimit.isProbabilityMeasure scale center)
    (hα₀ : 0 < α) (hα₂ : α < 2) :
    Asymptotics.IsRegularlyVaryingAtTop
      (fun x : ℝ => (symmetrizedMeasure ν).real {y : ℝ | x < |y|}) (-α) := by
  let μs : Measure ℝ := symmetrizedMeasure ν
  let tail : ℝ → ℝ := fun x => μs.real {y : ℝ | x < |y|}
  let H₂ : ℝ → ℝ := Asymptotics.secondTailIntegral tail
  let defect : ℝ → ℝ := cosineDefectIntegral μs
  let scaleFun : ℝ → ℝ := fun x => x ^ 3 * defect x⁻¹
  let ratio : ℝ → ℝ := fun x => H₂ x / scaleFun x
  have hdefectRV : Asymptotics.IsRegularlyVaryingAtZero defect α := by
    simpa [μs, defect] using h.isRegularlyVarying_symmetrizedCosineDefect hlimit
  have hscaleRV : Asymptotics.IsRegularlyVaryingAtTop scaleFun (3 - α) := by
    have hinv := hdefectRV.comp_inv
    have hpowEq : (fun x : ℝ => x ^ (3 : ℝ)) =ᶠ[atTop]
        fun x => x ^ 3 := by
      filter_upwards [] with x
      exact Real.rpow_natCast x 3
    have hpow : Asymptotics.IsRegularlyVaryingAtTop (fun x : ℝ => x ^ 3) 3 :=
      (Asymptotics.IsRegularlyVaryingAtTop.rpow (3 : ℝ)).congr hpowEq
    have hmul := hpow.mul hinv
    have hindex : 3 + -α = 3 - α := by ring
    rw [hindex] at hmul
    simpa [scaleFun] using hmul
  have hratio : Tendsto ratio atTop
      (nhds (cosineTauberianConstant α)) := by
    simpa [ratio, H₂, scaleFun, tail, defect, μs] using
      h.tendsto_secondTailIntegral_ratio hlimit hα₀ hα₂
  have hconstant : 0 < cosineTauberianConstant α :=
    cosineTauberianConstant_pos hα₀ hα₂
  have hratioRV : Asymptotics.IsSlowlyVaryingAtTop ratio :=
    Asymptotics.IsSlowlyVaryingAtTop.of_tendsto_pos hconstant hratio
  have hproductRV : Asymptotics.IsRegularlyVaryingAtTop
      (fun x : ℝ => scaleFun x * ratio x) (3 - α) := by
    simpa [Asymptotics.IsSlowlyVaryingAtTop] using hscaleRV.mul hratioRV
  have hproductEq : (fun x : ℝ => scaleFun x * ratio x) =ᶠ[atTop] H₂ := by
    filter_upwards [hscaleRV.eventually_pos] with x hx
    dsimp [ratio]
    field_simp
  have hH₂RV : Asymptotics.IsRegularlyVaryingAtTop H₂ (3 - α) :=
    hproductRV.congr hproductEq
  have htailAnti : Antitone tail := by
    intro x y hxy
    apply measureReal_mono (μ := μs)
      (s₁ := {z : ℝ | y < |z|}) (s₂ := {z : ℝ | x < |z|})
    · intro z hz
      exact lt_of_le_of_lt hxy hz
  have htailNonneg : ∀ x, 0 ≤ tail x := fun _ => measureReal_nonneg
  have htailLeOne : ∀ ⦃x : ℝ⦄, 0 ≤ x → tail x ≤ 1 := by
    intro x _
    exact measureReal_le_one
  have htailIntegrable : ∀ a b : ℝ,
      IntervalIntegrable (fun t : ℝ => t * tail t) volume a b := by
    intro a b
    exact htailAnti.intervalIntegrable.continuousOn_mul continuousOn_id
  have hsecondIff := Asymptotics.IsRegularlyVaryingAtTop.secondTailIntegral_iff
    hα₀ hα₂ htailAnti htailNonneg htailLeOne htailIntegrable
  exact hsecondIff.mpr (by simpa [H₂, tail] using hH₂RV)

/-- For stable attraction indices in `(0, 2)`, the inverse cosine Tauberian
theorem first gives regular variation of the symmetrized tail. The elementary
product bounds for iid differences then transfer the same index to the
original increment law. -/
theorem IsInDomainOfAttractionAlong.isRegularlyVarying_twoSidedTail
    {α : ℝ} {ν limit : Measure ℝ} [IsProbabilityMeasure ν]
    (hlimit : IsAlphaStable α limit)
    {scale center : ℕ → ℝ}
    (h : @IsInDomainOfAttractionAlong ν limit inferInstance
      hlimit.isProbabilityMeasure scale center)
    (hα₀ : 0 < α) (hα₂ : α < 2) :
    Asymptotics.IsRegularlyVaryingAtTop
      (fun x : ℝ => ν.real {y : ℝ | x < |y|}) (-α) := by
  have hsym := h.isRegularlyVarying_symmetrizedTwoSidedTail hlimit hα₀ hα₂
  change Asymptotics.IsRegularlyVaryingAtTop (twoSidedTail ν) (-α)
  exact twoSidedTail_isRegularlyVarying_of_symmetrized ν hsym

/-- In the stable domain of attraction with index in `(0, 2)`, the original
increment law's truncated-moment factor is slowly varying. This packages the
characteristic-function, inverse-Tauberian, and symmetrization steps with the
general truncated-moment Karamata theorem. -/
theorem IsInDomainOfAttractionAlong.isSlowlyVarying_stableSlowVariation
    {α : ℝ} {ν limit : Measure ℝ} [IsProbabilityMeasure ν]
    (hlimit : IsAlphaStable α limit)
    {scale center : ℕ → ℝ}
    (h : @IsInDomainOfAttractionAlong ν limit inferInstance
      hlimit.isProbabilityMeasure scale center)
    (hα₀ : 0 < α) (hα₂ : α < 2) :
    Asymptotics.IsSlowlyVaryingAtTop (stableSlowVariation α ν) := by
  exact stableSlowVariation_isSlowlyVarying_of_regularlyVaryingTail
    hα₀ hα₂ (h.isRegularlyVarying_twoSidedTail hlimit hα₀ hα₂)

/-- The Tauberian asymptotic and the exact Karamata ratio for a twice-
integrated tail give the tail-to-defect constant for the symmetrized law. -/
theorem IsInDomainOfAttractionAlong.tendsto_symmetrizedTail_div_cosineDefect
    {α : ℝ} {ν limit : Measure ℝ} [IsProbabilityMeasure ν]
    (hlimit : IsAlphaStable α limit)
    {scale center : ℕ → ℝ}
    (h : @IsInDomainOfAttractionAlong ν limit inferInstance
      hlimit.isProbabilityMeasure scale center)
    (hα₀ : 0 < α) (hα₂ : α < 2) :
    Tendsto
      (fun x : ℝ =>
        (symmetrizedMeasure ν).real {y : ℝ | x < |y|} /
          cosineDefectIntegral (symmetrizedMeasure ν) x⁻¹)
      atTop (nhds (1 / (α * cosineTauberianCosineMoment α))) := by
  let μs : Measure ℝ := symmetrizedMeasure ν
  let tail : ℝ → ℝ := fun x => μs.real {y : ℝ | x < |y|}
  let defect : ℝ → ℝ := cosineDefectIntegral μs
  let H₂ : ℝ → ℝ := Asymptotics.secondTailIntegral tail
  let tauberianRatio : ℝ → ℝ := fun x => H₂ x / (x ^ 3 * defect x⁻¹)
  let tailRatio : ℝ → ℝ := fun x => H₂ x / (x ^ 3 * tail x)
  let target : ℝ → ℝ := fun x => tail x / defect x⁻¹
  have htailRV : Asymptotics.IsRegularlyVaryingAtTop tail (-α) := by
    simpa [tail, μs] using
      h.isRegularlyVarying_symmetrizedTwoSidedTail hlimit hα₀ hα₂
  have htailAnti : Antitone tail := by
    intro x y hxy
    apply measureReal_mono (μ := μs)
      (s₁ := {z : ℝ | y < |z|}) (s₂ := {z : ℝ | x < |z|})
    · intro z hz
      exact lt_of_le_of_lt hxy hz
  have htailNonneg : ∀ x, 0 ≤ tail x := fun _ => measureReal_nonneg
  have htailLeOne : ∀ ⦃x : ℝ⦄, 0 ≤ x → tail x ≤ 1 := by
    intro x _
    exact measureReal_le_one
  have htailIntegrable : ∀ a b : ℝ,
      IntervalIntegrable (fun t : ℝ => t * tail t) volume a b := by
    intro a b
    exact htailAnti.intervalIntegrable.continuousOn_mul continuousOn_id
  have htailRatio : Tendsto tailRatio atTop
      (nhds (1 / ((2 - α) * (3 - α)))) := by
    simpa [tailRatio, H₂] using htailRV.tendsto_secondTailIntegral_div_mul
      hα₀ hα₂ htailAnti htailNonneg htailLeOne htailIntegrable
  have hdefectRV : Asymptotics.IsRegularlyVaryingAtZero defect α := by
    simpa [defect, μs] using h.isRegularlyVarying_symmetrizedCosineDefect hlimit
  have htauberian : Tendsto tauberianRatio atTop
      (nhds (cosineTauberianConstant α)) := by
    simpa [tauberianRatio, H₂, tail, defect, μs] using
      h.tendsto_secondTailIntegral_ratio hlimit hα₀ hα₂
  have hdenPos : 0 < 1 / ((2 - α) * (3 - α)) := by
    apply one_div_pos.mpr
    exact mul_pos (by linarith) (by linarith)
  have htailRatioPos : ∀ᶠ x : ℝ in atTop, 0 < tailRatio x := by
    exact htailRatio.eventually (isOpen_Ioi.mem_nhds hdenPos)
  have htailPos : ∀ᶠ x : ℝ in atTop, 0 < tail x := htailRV.eventually_pos
  have hdefectPos : ∀ᶠ x : ℝ in atTop, 0 < defect x⁻¹ := by
    exact tendsto_inv_atTop_nhdsGT_zero.eventually hdefectRV.eventually_pos
  have hH₂Pos : ∀ᶠ x : ℝ in atTop, 0 < H₂ x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), htailPos, htailRatioPos]
      with x hx htx hratio
    have hden : 0 < x ^ 3 * tail x := mul_pos (pow_pos hx _) htx
    have hdiv : 0 < H₂ x / (x ^ 3 * tail x) := by
      simpa [tailRatio] using hratio
    exact (div_pos_iff_of_pos_right hden).mp hdiv
  have hquot : Tendsto (fun x : ℝ => tauberianRatio x / tailRatio x) atTop
      (nhds (cosineTauberianConstant α /
        (1 / ((2 - α) * (3 - α))))) := by
    exact htauberian.div htailRatio (ne_of_gt hdenPos)
  have heq : target =ᶠ[atTop] fun x => tauberianRatio x / tailRatio x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), htailPos, hdefectPos, hH₂Pos]
      with x hx htx hfx hH₂x
    dsimp [target, tauberianRatio, tailRatio, H₂]
    field_simp [ne_of_gt hx, ne_of_gt htx, ne_of_gt hfx, ne_of_gt hH₂x]
    exact (div_self (ne_of_gt hH₂x)).symm
  have hconst : cosineTauberianConstant α /
      (1 / ((2 - α) * (3 - α))) =
        1 / (α * cosineTauberianCosineMoment α) := by
    rw [cosineTauberianConstant_eq hα₀ hα₂]
    have h₂ : 0 < 2 - α := by linarith
    have h₃ : 0 < 3 - α := by linarith
    have hJ : 0 < cosineTauberianCosineMoment α :=
      cosineTauberianCosineMoment_pos hα₀ hα₂
    field_simp [ne_of_gt hα₀, ne_of_gt h₂, ne_of_gt h₃, ne_of_gt hJ]
  have hlimit := hquot.congr' heq.symm
  rw [hconst] at hlimit
  simpa [target, tail, μs, defect] using hlimit

/-- The exact tail-to-defect asymptotic for the original increment law. The
factor one half comes from passing from the difference of two iid variables
back to one copy. -/
theorem IsInDomainOfAttractionAlong.tendsto_twoSidedTail_div_cosineDefect
    {α : ℝ} {ν limit : Measure ℝ} [IsProbabilityMeasure ν]
    (hlimit : IsAlphaStable α limit)
    {scale center : ℕ → ℝ}
    (h : @IsInDomainOfAttractionAlong ν limit inferInstance
      hlimit.isProbabilityMeasure scale center)
    (hα₀ : 0 < α) (hα₂ : α < 2) :
    Tendsto
      (fun x : ℝ =>
        ν.real {y : ℝ | x < |y|} /
          (1 - ‖charFun ν x⁻¹‖ ^ 2))
      atTop (nhds (1 / (2 * α * cosineTauberianCosineMoment α))) := by
  let T : ℝ → ℝ := fun x => ν.real {y : ℝ | x < |y|}
  let S : ℝ → ℝ := fun x =>
    (symmetrizedMeasure ν).real {y : ℝ | x < |y|}
  let defect : ℝ → ℝ := fun x => 1 - ‖charFun ν x⁻¹‖ ^ 2
  have hSymRV : Asymptotics.IsRegularlyVaryingAtTop S (-α) := by
    simpa [S] using h.isRegularlyVarying_symmetrizedTwoSidedTail hlimit hα₀ hα₂
  have hSymRatio : Tendsto (fun x : ℝ => T x / S x) atTop (nhds (1 / 2 : ℝ)) := by
    simpa [T, S, twoSidedTail] using
      twoSidedTail_div_symmetrized_tendsto_half (μ := ν) (α := α) hSymRV
  have hDefect : Tendsto (fun x : ℝ => S x / defect x) atTop
      (nhds (1 / (α * cosineTauberianCosineMoment α))) := by
    simpa [S, defect, cosineDefectIntegral_symmetrizedMeasure] using
      h.tendsto_symmetrizedTail_div_cosineDefect hlimit hα₀ hα₂
  have hprod := hSymRatio.mul hDefect
  have hSpos : ∀ᶠ x : ℝ in atTop, 0 < S x := hSymRV.eventually_pos
  have hdefectPos : ∀ᶠ x : ℝ in atTop, 0 < defect x := by
    exact tendsto_inv_atTop_nhdsGT_zero.eventually
      (h.isRegularlyVarying_normDefect_atZero hlimit).eventually_pos
  have heq : (fun x : ℝ => T x / S x * (S x / defect x)) =ᶠ[atTop]
      fun x => T x / defect x := by
    filter_upwards [hSpos, hdefectPos] with x hxS hxdefect
    field_simp [ne_of_gt hxS, ne_of_gt hxdefect]
  have hconst : (1 / 2 : ℝ) * (1 / (α * cosineTauberianCosineMoment α)) =
      1 / (2 * α * cosineTauberianCosineMoment α) := by
    have hJ : 0 < cosineTauberianCosineMoment α :=
      cosineTauberianCosineMoment_pos hα₀ hα₂
    field_simp [ne_of_gt hα₀, ne_of_gt hJ]
  have hfinal := hprod.congr' heq
  rw [hconst] at hfinal
  simpa [T, defect] using hfinal

/-- The truncated second moment has the corresponding exact asymptotic after
normalization by the squared scale and the characteristic-function defect.
This is the direct input needed to compare the stable norming factor with the
small-frequency defect. -/
theorem IsInDomainOfAttractionAlong.tendsto_truncatedSecondMoment_div_scaledCosineDefect
    {α : ℝ} {ν limit : Measure ℝ} [IsProbabilityMeasure ν]
    (hlimit : IsAlphaStable α limit)
    {scale center : ℕ → ℝ}
    (h : @IsInDomainOfAttractionAlong ν limit inferInstance
      hlimit.isProbabilityMeasure scale center)
    (hα₀ : 0 < α) (hα₂ : α < 2) :
    Tendsto
      (fun x : ℝ => truncatedSecondMoment ν x /
        (x ^ 2 * (1 - ‖charFun ν x⁻¹‖ ^ 2)))
      atTop
      (nhds (1 / (2 * (2 - α) * cosineTauberianCosineMoment α))) := by
  let tail : ℝ → ℝ := fun x => ν.real {y : ℝ | x < |y|}
  let defect : ℝ → ℝ := fun x => 1 - ‖charFun ν x⁻¹‖ ^ 2
  have htailRV : Asymptotics.IsRegularlyVaryingAtTop tail (-α) := by
    simpa [tail] using h.isRegularlyVarying_twoSidedTail hlimit hα₀ hα₂
  have hmomentTail : Tendsto
      (fun x : ℝ => truncatedSecondMoment ν x / (x ^ 2 * tail x)) atTop
      (nhds (α / (2 - α))) := by
    simpa [tail, twoSidedTail] using
      tendsto_truncatedSecondMoment_div_tail_of_regularlyVarying
        ν hα₀ hα₂ htailRV
  have htailDefect : Tendsto (fun x : ℝ => tail x / defect x) atTop
      (nhds (1 / (2 * α * cosineTauberianCosineMoment α))) := by
    simpa [tail, defect, twoSidedTail] using
      h.tendsto_twoSidedTail_div_cosineDefect hlimit hα₀ hα₂
  have hproduct := hmomentTail.mul htailDefect
  have htailPos : ∀ᶠ x : ℝ in atTop, 0 < tail x := htailRV.eventually_pos
  have hdefectPos : ∀ᶠ x : ℝ in atTop, 0 < defect x := by
    exact tendsto_inv_atTop_nhdsGT_zero.eventually
      (h.isRegularlyVarying_normDefect_atZero hlimit).eventually_pos
  have heq : (fun x : ℝ =>
      truncatedSecondMoment ν x / (x ^ 2 * tail x) * (tail x / defect x)) =ᶠ[atTop]
      fun x => truncatedSecondMoment ν x / (x ^ 2 * defect x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ), htailPos, hdefectPos]
      with x hx htx hdx
    field_simp [ne_of_gt hx, ne_of_gt htx, ne_of_gt hdx]
  have hconst : α / (2 - α) *
      (1 / (2 * α * cosineTauberianCosineMoment α)) =
        1 / (2 * (2 - α) * cosineTauberianCosineMoment α) := by
    have h₂ : 0 < 2 - α := by linarith
    have hJ : 0 < cosineTauberianCosineMoment α :=
      cosineTauberianCosineMoment_pos hα₀ hα₂
    field_simp [ne_of_gt hα₀, ne_of_gt h₂, ne_of_gt hJ]
  have hfinal := hproduct.congr' heq
  rw [hconst] at hfinal
  simpa [defect] using hfinal

end ProbabilityTheory

end
