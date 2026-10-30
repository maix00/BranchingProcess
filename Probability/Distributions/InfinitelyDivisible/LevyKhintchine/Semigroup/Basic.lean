/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license; see docs/third_party/LeanLevy/LICENSE.
Modified for this project from slink/LeanLevy at revision
7e73fd9b23ad52956ec2756a815889a783131ce4; see
docs/third_party/LeanLevy/provenance.md.
Authors: LeanLevy Contributors
-/
module

public import Analysis.Fourier.Bochner.Theorem
public import Analysis.Fourier.PositiveDefinite
public import Analysis.Fourier.ConditionallyPositiveDefinite.Schoenberg
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import MeasureTheory.Measure.CharacteristicFunction.PositiveDefinite
public import Probability.Distributions.InfinitelyDivisible.Basic
public import Probability.Distributions.InfinitelyDivisible.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Analysis.SpecialFunctions.Complex.Exponential
import MeasureTheory.Measure.CharacteristicFunction.Convolution
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Lifting

/-!
# Convolution semigroups and conditional positive definiteness

## Public declarations

* `IsInfinitelyDivisible.isConditionallyPositiveDefinite_log`: a continuous logarithm `ψ` of
  the characteristic function of an infinitely divisible probability measure, normalized by
  `ψ(0) = 0`, is conditionally positive definite.
* `ConvolutionSemigroup`: a family of probability measures `μ_t`, `t > 0`, with a continuous
  exponent `ψ` satisfying `charFun μ_t ξ = exp (t * ψ ξ)`. Its methods state the semigroup
  characteristic-function law, scaling of the measure by `1/t`, the corresponding integral
  formula, and the limit `(charFun μ_t ξ - 1) / t → ψ ξ` as `t → 0⁺`.
* `convolutionSemigroupOfCPD` constructs a semigroup from a continuous, Hermitian conditionally
  positive-definite exponent vanishing at zero. `convolutionSemigroupOfMeasure` constructs the
  semigroup associated with an infinitely divisible law and identifies its time-one member
  with the original law.

These interfaces support the representation theorem in `Representation.lean`; its Lévy-measure
extraction estimates are grouped under `Lemmas/Representation/`.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder

namespace ProbabilityTheory

private lemma charFun_zero_eq_one {ν : Measure ℝ} [IsProbabilityMeasure ν] :
    charFun ν 0 = 1 := by
  simp [charFun_zero, Measure.real, measure_univ]

private lemma double_sum_conj_mul_eq_zero {n : ℕ} {c : Fin n → ℂ}
    (hc : ∑ i, c i = 0) :
    ∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i) * c j = 0 := by
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  simp [hc]

/-- When `∑ c = 0`, PSD implies the "1 minus charFun" form is non-positive. -/
private lemma one_sub_charFun_form_nonpos {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {n : ℕ} (ξ : Fin n → ℝ) (c : Fin n → ℂ) (hc : ∑ i, c i = 0) :
    (∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * (1 - charFun ν (ξ i - ξ j))).re ≤ 0 := by
  let P : ProbabilityMeasure ℝ := ⟨ν, inferInstance⟩
  have hcpd := IsPositiveDefinite.cpd_sub_one
    (MeasureTheory.ProbabilityMeasure.isPositiveDefinite_charFun P)
  have hposQ : 0 ≤ ∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * (charFun ν (ξ i - ξ j) - 1) := by
    simpa only [show (↑P : Measure ℝ) = ν from rfl] using hcpd n ξ c hc
  have hpos := (Complex.nonneg_iff.mp hposQ).1
  have hzero := double_sum_conj_mul_eq_zero hc
  have hleft : (∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * (1 - charFun ν (ξ i - ξ j))) =
      -(∑ i : Fin n, ∑ j : Fin n,
        starRingEnd ℂ (c i) * c j * charFun ν (ξ i - ξ j)) := by
    calc
      _ = (∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i) * c j)
          - (∑ i : Fin n, ∑ j : Fin n,
            starRingEnd ℂ (c i) * c j * charFun ν (ξ i - ξ j)) := by
        simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib]
      _ = _ := by rw [hzero, zero_sub]
  have hright : (∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * (charFun ν (ξ i - ξ j) - 1)) =
      ∑ i : Fin n, ∑ j : Fin n,
        starRingEnd ℂ (c i) * c j * charFun ν (ξ i - ξ j) := by
    calc
      _ = (∑ i : Fin n, ∑ j : Fin n,
          starRingEnd ℂ (c i) * c j * charFun ν (ξ i - ξ j))
          - (∑ i : Fin n, ∑ j : Fin n, starRingEnd ℂ (c i) * c j) := by
        simp_rw [mul_sub, mul_one, Finset.sum_sub_distrib]
      _ = _ := by rw [hzero, sub_zero]
  have hform : ∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * (1 - charFun ν (ξ i - ξ j)) =
    -(∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * (charFun ν (ξ i - ξ j) - 1)) := by
    rw [hleft, hright]
  rw [hform, Complex.neg_re]
  linarith

/-- If `(charFun ν)^m = exp(ψ)` where `ψ` is a continuous log with `ψ(0) = 0`,
then `charFun ν = exp(ψ/m)`.

This uses the uniqueness of lifts through the exponential covering map:
both `charFun ν` and `exp(ψ/m)` are continuous, map `0 ↦ 1`, and satisfy
`f^m = exp(ψ)`. -/
private lemma charFun_eq_exp_div {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {ψ : ℝ → ℂ} (hψ_cont : Continuous ψ) (hψ_zero : ψ 0 = 0)
    {m : ℕ} (hm : 0 < m) (hpow : ∀ ξ, (charFun ν ξ) ^ m = exp (ψ ξ)) :
    ∀ ξ, charFun ν ξ = exp (ψ ξ / ↑m) := by
  -- Step 1: charFun ν is continuous and never zero (from hpow + exp_ne_zero)
  have hcont : Continuous (charFun ν) := MeasureTheory.continuous_charFun
  have hne : ∀ ξ, charFun ν ξ ≠ 0 := by
    intro ξ habs
    have : (charFun ν ξ) ^ m = 0 := by rw [habs, zero_pow (by omega)]
    rw [hpow] at this
    exact exp_ne_zero _ this
  -- Step 2: Lift charFun ν through exp to get logν : C(ℝ, ℂ) with logν(0) = 0
  have hφ0 : charFun ν 0 = 1 := charFun_zero_eq_one
  set fν : C(ℝ, ℂ) := ⟨charFun ν, hcont⟩
  have heν : Complex.exp (0 : ℂ) = fν (0 : ℝ) := by simp [fν, hφ0]
  have hsν : ∀ ξ : ℝ, fν ξ ∈ ({0}ᶜ : Set ℂ) := fun ξ =>
    Set.mem_compl_singleton_iff.mpr (hne ξ)
  obtain ⟨logν, ⟨hlogν0, hlogν_exp⟩, hlogν_unique⟩ :=
    Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts fν heν hsν
  -- logν 0 = 0 and exp ∘ logν = charFun ν
  -- Step 3: Build the base map g := exp ∘ ψ as a ContinuousMap
  set g : C(ℝ, ℂ) := ⟨fun ξ => exp (ψ ξ), hψ_cont.cexp⟩
  -- g maps into ℂ \ {0}
  have hsg : ∀ ξ : ℝ, g ξ ∈ ({0}ᶜ : Set ℂ) := fun ξ =>
    Set.mem_compl_singleton_iff.mpr (exp_ne_zero _)
  have heg : Complex.exp (0 : ℂ) = g (0 : ℝ) := by simp [g, hψ_zero]
  -- Step 4: ψ is a lift of g through exp
  set ψ_cm : C(ℝ, ℂ) := ⟨ψ, hψ_cont⟩
  have hψ_lift_val : ψ_cm (0 : ℝ) = 0 := hψ_zero
  have hψ_lift_comp : Complex.exp ∘ ψ_cm = g := by
    ext ξ; simp [ψ_cm, g]
  -- Step 5: m * logν is also a lift of g through exp
  set mlogν : C(ℝ, ℂ) := ⟨fun ξ => (↑m : ℂ) * logν ξ,
    continuous_const.mul logν.continuous⟩
  have hmlogν_val : mlogν (0 : ℝ) = 0 := by simp [mlogν, hlogν0]
  have hmlogν_comp : Complex.exp ∘ mlogν = g := by
    ext ξ
    simp only [Function.comp_apply, ContinuousMap.coe_mk, mlogν, g]
    -- exp(m * logν(ξ)) = (exp(logν(ξ)))^m = (charFun ν ξ)^m = exp(ψ ξ)
    rw [Complex.exp_nat_mul]
    have hexp_logν : Complex.exp (logν ξ) = charFun ν ξ := by
      have := congr_fun hlogν_exp ξ
      simp [Function.comp_apply] at this
      exact this
    rw [hexp_logν, hpow]
  -- Step 6: By uniqueness of lifts, ψ = m * logν
  obtain ⟨_, ⟨_, _⟩, huniq⟩ :=
    Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts g heg hsg
  have hψ_eq_mlogν : ψ_cm = mlogν := by
    have hψ_uniq := huniq ψ_cm ⟨hψ_lift_val, hψ_lift_comp⟩
    have hmlogν_uniq := huniq mlogν ⟨hmlogν_val, hmlogν_comp⟩
    rw [hψ_uniq, hmlogν_uniq]
  -- Step 7: Therefore charFun ν = exp(logν) = exp(ψ/m)
  intro ξ
  have hexp_logν : Complex.exp (logν ξ) = charFun ν ξ := by
    have := congr_fun hlogν_exp ξ
    simp [Function.comp_apply] at this
    exact this
  rw [← hexp_logν]
  congr 1
  -- logν ξ = ψ ξ / m, from ψ ξ = m * logν ξ
  have hψ_eq : ψ ξ = (↑m : ℂ) * logν ξ := by
    have := congr_fun (congrArg DFunLike.coe hψ_eq_mlogν) ξ
    simp [ψ_cm, mlogν] at this
    exact this
  rw [hψ_eq]
  rw [mul_div_cancel_left₀]
  exact Nat.cast_ne_zero.mpr (by omega)

/-- The complex limit `m * (1 - exp(z / m)) → -z` as `m → ∞`. -/
private lemma tendsto_mul_one_sub_exp_div (z : ℂ) :
    Tendsto (fun m : ℕ => (↑m : ℂ) * (1 - exp (z / ↑m))) atTop (nhds (-z)) := by
  by_cases hz : z = 0
  · -- Case z = 0: everything is zero
    simp [hz]
  · -- Case z ≠ 0: use (exp w - 1)/w → 1 as w → 0
    -- Step 1: The derivative of exp at 0 gives slope cexp 0 → 1 in 𝓝[≠] 0
    have hslope : Tendsto (slope cexp 0) (𝓝[≠] 0) (nhds 1) := by
      have h := hasDerivAt_exp (0 : ℂ)
      rw [exp_zero] at h
      exact h.tendsto_slope
    -- Step 2: z / m → 0 as m → ∞ (in ℂ)
    have hdiv_tendsto : Tendsto (fun m : ℕ => z / (↑m : ℂ)) atTop (nhds 0) := by
      have hinv : Tendsto (fun m : ℕ => (↑m : ℂ)⁻¹) atTop (nhds 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        have : (fun m : ℕ => ‖(↑m : ℂ)⁻¹‖) = fun m : ℕ => ((↑m : ℝ))⁻¹ := by
          ext m; rw [norm_inv, Complex.norm_natCast]
        rw [this]
        exact tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
      rw [show (0 : ℂ) = z * 0 from by ring]
      simp only [div_eq_mul_inv]
      exact tendsto_const_nhds.mul hinv
    -- Step 3: z / m ≠ 0 eventually (since z ≠ 0 and m ≥ 1)
    have hdiv_ne : ∀ᶠ m : ℕ in atTop, z / (↑m : ℂ) ∈ ({0}ᶜ : Set ℂ) := by
      filter_upwards [Filter.Ici_mem_atTop 1] with m (hm : 1 ≤ m)
      exact Set.mem_compl_singleton_iff.mpr
        (div_ne_zero hz (Nat.cast_ne_zero.mpr (by omega)))
    -- Step 4: Compose to get slope cexp 0 (z/m) → 1
    have hcomp : Tendsto (fun m : ℕ => slope cexp 0 (z / (↑m : ℂ))) atTop (nhds 1) :=
      hslope.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hdiv_tendsto hdiv_ne)
    -- Step 5: slope cexp 0 (z/m) * z → 1 * z = z
    have hmul_z : Tendsto (fun m : ℕ => slope cexp 0 (z / (↑m : ℂ)) * z) atTop (nhds z) := by
      have := hcomp.mul_const z
      rwa [one_mul] at this
    -- Step 6: -(slope cexp 0 (z/m) * z) → -z
    have hneg_z : Tendsto (fun m : ℕ => -(slope cexp 0 (z / (↑m : ℂ)) * z)) atTop (nhds (-z)) :=
      hmul_z.neg
    -- Step 7: For m ≥ 1, m * (1 - exp(z/m)) = -(slope cexp 0 (z/m) * z)
    have heq : ∀ᶠ m : ℕ in atTop,
        (↑m : ℂ) * (1 - exp (z / ↑m)) = -(slope cexp 0 (z / (↑m : ℂ)) * z) := by
      filter_upwards [Filter.Ici_mem_atTop 1] with m (hm : 1 ≤ m)
      have hm_ne : (↑m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      simp only [slope, sub_zero, exp_zero, vsub_eq_sub, smul_eq_mul]
      have hz_div_ne : z / (↑m : ℂ) ≠ 0 := div_ne_zero hz hm_ne
      field_simp
      ring
    -- Step 8: Conclude by eventually-equal
    exact (tendsto_congr' heq).mpr hneg_z

private lemma hermitian_quadratic_form_im_eq_zero
    {G : Type*} [AddCommGroup G] {ψ : G → ℂ}
    (hψ_herm : ∀ x, ψ (-x) = starRingEnd ℂ (ψ x))
    (n : ℕ) (x : Fin n → G) (c : Fin n → ℂ) :
    (∑ i, ∑ j, starRingEnd ℂ (c i) * c j * ψ (x i - x j)).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  calc
    starRingEnd ℂ (∑ i, ∑ j,
        starRingEnd ℂ (c i) * c j * ψ (x i - x j))
        = ∑ i, ∑ j, c i * starRingEnd ℂ (c j) * ψ (x j - x i) := by
          simp only [_root_.map_sum, map_mul, starRingEnd_self_apply]
          simp_rw [← hψ_herm, neg_sub]
    _ = ∑ i, ∑ j, starRingEnd ℂ (c i) * c j * ψ (x i - x j) := by
          rw [Finset.sum_comm]
          congr 1
          ext i
          congr 1
          ext j
          ring

/-- The continuous logarithm of an infinitely divisible characteristic function is
conditionally positive definite. -/
theorem IsInfinitelyDivisible.isConditionallyPositiveDefinite_log
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (h : IsInfinitelyDivisible μ)
    {ψ : ℝ → ℂ} (hψ_cont : Continuous ψ) (hψ_zero : ψ 0 = 0)
    (hψ_exp : ∀ ξ, charFun μ ξ = exp (ψ ξ)) :
    IsConditionallyPositiveDefinite ψ := by
  intro n ξ c hc
  have hψ_herm := h.hermitian_log hψ_cont hψ_zero hψ_exp
  -- For each m ≥ 1, PSD of the m-th root measure gives:
  --   (∑ᵢ ∑ⱼ conj(cᵢ) cⱼ · m(1 - exp(ψ(ξᵢ-ξⱼ)/m))).re ≤ 0
  -- As m → ∞, m(1 - exp(z/m)) → -z, so the limit gives CPD.

  -- The bound for each m
  have hbound : ∀ m : ℕ, 0 < m →
      (∑ i : Fin n, ∑ j : Fin n,
        starRingEnd ℂ (c i) * c j *
          ((↑m : ℂ) * (1 - exp (ψ (ξ i - ξ j) / ↑m)))).re ≤ 0 := by
    intro m hm
    obtain ⟨ν, hνP, hμ_eq⟩ := h m hm
    have := hνP
    have hpow : ∀ ξ', (charFun ν ξ') ^ m = exp (ψ ξ') := by
      intro ξ'; rw [← hψ_exp, hμ_eq, charFun_convPower]
    have hν_exp := charFun_eq_exp_div hψ_cont hψ_zero hm hpow
    have hsub : ∀ i j : Fin n,
        1 - charFun ν (ξ i - ξ j) = 1 - exp (ψ (ξ i - ξ j) / ↑m) := by
      intro i j; rw [hν_exp]
    have hnonpos := one_sub_charFun_form_nonpos ξ c hc (ν := ν)
    simp_rw [hsub] at hnonpos
    -- Factor out m from each summand
    have hfactor : ∀ i j : Fin n,
        starRingEnd ℂ (c i) * c j * ((↑m : ℂ) * (1 - exp (ψ (ξ i - ξ j) / ↑m))) =
        (↑m : ℂ) * (starRingEnd ℂ (c i) * c j * (1 - exp (ψ (ξ i - ξ j) / ↑m))) := by
      intro i j; ring
    simp_rw [hfactor, ← Finset.mul_sum]
    -- (↑m : ℂ) * S has .re = m * S.re (since m is real, i.e., (↑m).im = 0)
    have hm_re : ((↑m : ℂ) * (∑ i : Fin n, ∑ j : Fin n,
        starRingEnd ℂ (c i) * c j * (1 - exp (ψ (ξ i - ξ j) / ↑m)))).re =
      ↑m * (∑ i : Fin n, ∑ j : Fin n,
        starRingEnd ℂ (c i) * c j * (1 - exp (ψ (ξ i - ξ j) / ↑m))).re := by
      rw [Complex.mul_re]
      simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
    rw [hm_re]
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg' m) hnonpos

  -- The limit as m → ∞
  have hlim : Tendsto
      (fun m : ℕ => (∑ i : Fin n, ∑ j : Fin n,
        starRingEnd ℂ (c i) * c j *
          ((↑m : ℂ) * (1 - exp (ψ (ξ i - ξ j) / ↑m)))).re)
      atTop
      (nhds (∑ i : Fin n, ∑ j : Fin n,
        starRingEnd ℂ (c i) * c j * (-ψ (ξ i - ξ j))).re) := by
    apply Complex.continuous_re.continuousAt.tendsto.comp
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    apply Filter.Tendsto.const_mul
    exact tendsto_mul_one_sub_exp_div (ψ (ξ i - ξ j))

  -- The limit of non-positive values is non-positive
  have hle : (∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * (-ψ (ξ i - ξ j))).re ≤ 0 :=
    le_of_tendsto hlim (Eventually.of_forall fun m => by
      by_cases hm : m = 0
      · simp [hm]
      · exact hbound m (Nat.pos_of_ne_zero hm))

  -- ∑ conj(cᵢ) cⱼ (-ψ) = -(∑ conj(cᵢ) cⱼ ψ), so -(∑ ... ψ).re ≤ 0 ⇒ (∑ ... ψ).re ≥ 0
  have hneg : (∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * (-ψ (ξ i - ξ j))).re =
    -(∑ i : Fin n, ∑ j : Fin n,
      starRingEnd ℂ (c i) * c j * ψ (ξ i - ξ j)).re := by
    simp_rw [mul_neg, Finset.sum_neg_distrib, Complex.neg_re]
  rw [Complex.nonneg_iff]
  constructor
  · linarith [hneg]
  · exact (hermitian_quadratic_form_im_eq_zero hψ_herm n ξ c).symm

/-! ## Convolution semigroup structure -/

/-- A **convolution semigroup** on `ℝ` is a family of probability measures `μ_t` indexed by
`t > 0` whose characteristic functions satisfy the semigroup law:
`charFun(μ_{s+t}) = charFun(μ_s) · charFun(μ_t)` for all `ξ`.

Equivalently, `charFun(μ_t)(ξ) = exp(tψ(ξ))` for a continuous function `ψ` with `ψ(0) = 0`.
The Lévy-Khintchine theorem extracts the triple `(b, σ², ν)` from `ψ`. -/
structure ConvolutionSemigroup where
  /-- The exponent function: `charFun(μ_t) = exp(t · ψ)`. -/
  exponent : ℝ → ℂ
  /-- The exponent is continuous. -/
  exponent_continuous : Continuous exponent
  /-- The exponent vanishes at 0. -/
  exponent_zero : exponent 0 = 0
  /-- For each `t > 0`, a probability measure whose characteristic function is `exp(tψ)`. -/
  measure : {t : ℝ // 0 < t} → MeasureTheory.ProbabilityMeasure ℝ
  /-- The characteristic function identity. -/
  charFun_eq : ∀ (t : {t : ℝ // 0 < t}) (ξ : ℝ),
    charFun (measure t : Measure ℝ) ξ =
      exp ((↑t.val : ℂ) * exponent ξ)

namespace ConvolutionSemigroup

variable (S : ConvolutionSemigroup)

/-- The semigroup law: `charFun(μ_s) · charFun(μ_t) = charFun(μ_{s+t})` at the level
of exponents. This follows from the exponential identity `exp(sψ) · exp(tψ) = exp((s+t)ψ)`. -/
theorem charFun_mul (s t : {r : ℝ // 0 < r}) (ξ : ℝ) :
    charFun (S.measure s : Measure ℝ) ξ *
    charFun (S.measure t : Measure ℝ) ξ =
    exp ((↑(s.val + t.val) : ℂ) * S.exponent ξ) := by
  rw [S.charFun_eq s ξ, S.charFun_eq t ξ, ← exp_add]
  congr 1
  push_cast; ring

/-- The scaled measure `(1/t) · μ_t`. When `charFun(μ_t) = exp(tψ)`, the scaled measure
    captures the behaviour of `(exp(tψ) − 1)/t → ψ` as `t → 0⁺`. -/
noncomputable def scaledMeasure (t : {t : ℝ // 0 < t}) : Measure ℝ :=
  ENNReal.ofReal t.val⁻¹ • (S.measure t : Measure ℝ)

@[simp]
theorem scaledMeasure_apply (t : {t : ℝ // 0 < t}) (A : Set ℝ) :
    S.scaledMeasure t A = ENNReal.ofReal t.val⁻¹ * (S.measure t : Measure ℝ) A := by
  simp [scaledMeasure, Measure.smul_apply]

/-- Integration against the scaled measure: `∫ f d(scaledMeasure t) = t⁻¹ • ∫ f dμ_t`.
    Here `•` is the scalar action of `ℝ` on the codomain (typically `ℂ`). -/
theorem integral_scaledMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (t : {t : ℝ // 0 < t}) (f : ℝ → E) :
    ∫ x, f x ∂(S.scaledMeasure t) = t.val⁻¹ • ∫ x, f x ∂(S.measure t : Measure ℝ) := by
  simp only [scaledMeasure]
  rw [integral_smul_measure]
  rw [ENNReal.toReal_ofReal (le_of_lt (inv_pos.mpr t.prop))]

/-- Scaled characteristic function limit: `(charFun(μ_t)(ξ) − 1)/t → ψ(ξ)` as `t → 0⁺`.
Since `charFun(μ_t)(ξ) = exp(tψ(ξ))`, this follows from the first-order exponential limit. -/
theorem charFun_scaled_limit (ξ : ℝ) :
    Tendsto (fun t : {t : ℝ // 0 < t} =>
      (charFun (S.measure t : Measure ℝ) ξ - 1) / (↑t.val : ℂ))
      (comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 (S.exponent ξ)) := by
  -- Rewrite charFun using the semigroup identity.
  suffices Tendsto (fun t : {t : ℝ // 0 < t} =>
      (exp ((↑t.val : ℂ) * S.exponent ξ) - 1) / (↑t.val : ℂ))
      (comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝 (S.exponent ξ)) by
    refine this.congr (fun t => ?_)
    rw [S.charFun_eq t ξ]
  -- The target is `Complex.tendsto_exp_mul_real_div ψ(ξ) ∘ Subtype.val`.
  exact (Complex.tendsto_exp_mul_real_div (S.exponent ξ)).comp
    ((tendsto_comap.mono_right (nhdsGT_le_nhdsNE 0) : Tendsto Subtype.val
      (comap Subtype.val (𝓝[>] (0 : ℝ))) (𝓝[≠] (0 : ℝ))))

end ConvolutionSemigroup

/-- Build a convolution semigroup from a CPD exponent via Schoenberg + Bochner. -/
noncomputable def convolutionSemigroupOfCPD
    {ψ : ℝ → ℂ} (hψ_cont : Continuous ψ) (hψ_zero : ψ 0 = 0)
    (hψ_cpd : IsConditionallyPositiveDefinite ψ)
    (hψ_herm : ∀ ξ, ψ (-ξ) = starRingEnd ℂ (ψ ξ)) :
    ConvolutionSemigroup where
  exponent := ψ
  exponent_continuous := hψ_cont
  exponent_zero := hψ_zero
  measure := fun ⟨t, ht⟩ =>
    (bochner _ (by fun_prop : Continuous (fun ξ => exp ((↑t : ℂ) * ψ ξ)))
      (IsConditionallyPositiveDefinite.schoenberg_exp hψ_cpd hψ_herm t ht.le)
      (by rw [hψ_zero, mul_zero, exp_zero])).choose
  charFun_eq := fun ⟨t, ht⟩ ξ =>
    (bochner _ (by fun_prop : Continuous (fun ξ => exp ((↑t : ℂ) * ψ ξ)))
      (IsConditionallyPositiveDefinite.schoenberg_exp hψ_cpd hψ_herm t ht.le)
      (by rw [hψ_zero, mul_zero, exp_zero])).choose_spec ξ

/-- Convolution semigroup canonically associated with an infinitely divisible
probability measure `μ`. By construction, the t=1 member of the semigroup is
literally `μ` (see `convolutionSemigroupOfMeasure_one`).

This bundles `exists_continuous_log`, `isConditionallyPositiveDefinite_log`,
`hermitian_log`, and `convolutionSemigroupOfCPD`, then patches the t=1 slot to
be exactly `μ` (rather than the abstract Bochner-extracted measure that merely
shares its characteristic function). The patch preserves the convolution-semigroup
laws because `charFun μ = exp ψ` by `exists_continuous_log`. -/
noncomputable def convolutionSemigroupOfMeasure
    (μ : Measure ℝ) [hμ : IsProbabilityMeasure μ] (h : IsInfinitelyDivisible μ) :
    ConvolutionSemigroup :=
  let ψ_data := h.exists_continuous_log
  let ψ := ψ_data.choose
  let hψ_cont := ψ_data.choose_spec.1
  let hψ_zero := ψ_data.choose_spec.2.1
  let hψ_exp := ψ_data.choose_spec.2.2
  let hψ_cpd := h.isConditionallyPositiveDefinite_log hψ_cont hψ_zero hψ_exp
  let hψ_herm := h.hermitian_log hψ_cont hψ_zero hψ_exp
  let S₀ := convolutionSemigroupOfCPD hψ_cont hψ_zero hψ_cpd hψ_herm
  { exponent := S₀.exponent
    exponent_continuous := S₀.exponent_continuous
    exponent_zero := S₀.exponent_zero
    measure := fun t =>
      if h1 : t.val = 1 then ⟨μ, hμ⟩ else S₀.measure t
    charFun_eq := by
      intro t ξ
      by_cases ht : t.val = 1
      · simp [ht]
        change charFun μ ξ = exp (ψ ξ)
        exact hψ_exp ξ
      · simp [ht]
        exact S₀.charFun_eq t ξ }

/-- The t=1 member of `convolutionSemigroupOfMeasure μ h` is literally `μ`
(as a `ProbabilityMeasure`). -/
@[simp]
theorem convolutionSemigroupOfMeasure_one
    (μ : Measure ℝ) [hμ : IsProbabilityMeasure μ] (h : IsInfinitelyDivisible μ) :
    ((convolutionSemigroupOfMeasure μ h).measure ⟨1, one_pos⟩ :
        MeasureTheory.ProbabilityMeasure ℝ) = ⟨μ, hμ⟩ := by
  show (if _ : (1 : ℝ) = 1 then (⟨μ, hμ⟩ : MeasureTheory.ProbabilityMeasure ℝ) else _) = _
  simp

/-- The underlying measure of the t=1 member is `μ`. -/
@[simp]
theorem convolutionSemigroupOfMeasure_one_coe
    (μ : Measure ℝ) [hμ : IsProbabilityMeasure μ] (h : IsInfinitelyDivisible μ) :
    (((convolutionSemigroupOfMeasure μ h).measure ⟨1, one_pos⟩ :
        MeasureTheory.ProbabilityMeasure ℝ) : Measure ℝ) = μ := by
  rw [convolutionSemigroupOfMeasure_one]
  rfl
end ProbabilityTheory
