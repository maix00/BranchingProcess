/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license; see docs/third_party/LeanLevy/LICENSE.
Modified for this project from slink/LeanLevy at revision
7e73fd9b23ad52956ec2756a815889a783131ce4; see
docs/third_party/LeanLevy/provenance.md.
Authors: LeanLevy Contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Probability.Distributions.InfinitelyDivisible.Basic
import Analysis.Fourier.PositiveDefinite
import Mathlib.Analysis.Complex.CoveringMap
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Matrix.Order
import MeasureTheory.Measure.CharacteristicFunction.Convolution
import MeasureTheory.Measure.CharacteristicFunction.PositiveDefinite
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.Topology.Homotopy.Lifting
import Probability.Distributions.CharacteristicFunction.Zero

/-!
# Characteristic functions of infinitely divisible measures

## Public declarations

* `IsInfinitelyDivisible.charFun_ne_zero`: if `μ` is infinitely divisible, then
  `charFun μ ξ ≠ 0` for every `ξ : ℝ`.
* `IsInfinitelyDivisible.exists_continuous_log`: there is a continuous `ψ : ℝ → ℂ`
  with `ψ(0)=0` and `charFun μ ξ = exp(ψ ξ)` for every `ξ`.
* `IsInfinitelyDivisible.hermitian_log`: every such logarithm satisfies
  `ψ(-ξ)=conj(ψ ξ)`.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure ProbabilityTheory Complex Filter Topology
open scoped NNReal ENNReal ComplexOrder

namespace ProbabilityTheory

section NonVanishing

private lemma charFun_half_eq_zero_of_charFun_eq_zero
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (h : IsInfinitelyDivisible μ)
    {ξ₀ : ℝ} (hξ : charFun μ ξ₀ = 0) :
    charFun μ (ξ₀ / 2) = 0 := by
  rw [← norm_eq_zero]
  suffices hle : ∀ n : ℕ, 0 < n → ‖charFun μ (ξ₀ / 2)‖ ≤ (3 / 4 : ℝ) ^ n by
    apply le_antisymm _ (norm_nonneg _)
    by_contra hc; push Not at hc
    have htend : Tendsto (fun n : ℕ => (3 / 4 : ℝ) ^ n) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (by norm_num)
    have hev := htend.eventually (Iio_mem_nhds hc)
    obtain ⟨N, hN⟩ := hev.exists_forall_of_atTop
    have h1 := hle (N + 1) (Nat.succ_pos N)
    have h2 := hN (N + 1) (by omega)
    linarith
  intro n hn
  obtain ⟨ν, hν_prob, hμ_eq⟩ := h n hn
  have hpow : ∀ ξ, charFun μ ξ = (charFun ν ξ) ^ n := by
    intro ξ; rw [hμ_eq, charFun_convPower]
  have hν_zero : charFun ν ξ₀ = 0 := by
    have h1 := hpow ξ₀; rw [hξ] at h1
    exact (pow_eq_zero_iff (by omega : n ≠ 0)).mp h1.symm
  have hν_half := norm_charFun_half_le_of_charFun_eq_zero hν_zero
  have hhalf : (1 / 2 : ℝ) • ξ₀ = ξ₀ / 2 := by
    simp only [smul_eq_mul, div_eq_mul_inv]
    ring
  have hν_half' : ‖charFun ν (ξ₀ / 2)‖ ≤ 3 / 4 := by
    simpa only [hhalf] using hν_half
  calc ‖charFun μ (ξ₀ / 2)‖
      = ‖charFun ν (ξ₀ / 2)‖ ^ n := by rw [hpow, norm_pow]
    _ ≤ (3 / 4 : ℝ) ^ n := pow_le_pow_left₀ (norm_nonneg _) hν_half' n

/-- The characteristic function of an infinitely divisible probability measure never vanishes.

**Proof:** Suppose `charFun μ ξ₀ = 0` for some `ξ₀`. By repeated halving,
`charFun μ (ξ₀ / 2^k) = 0` for all `k`. But `ξ₀ / 2^k → 0` and `charFun μ` is continuous
with `charFun μ 0 = 1`, contradiction. -/
theorem IsInfinitelyDivisible.charFun_ne_zero
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (h : IsInfinitelyDivisible μ) (ξ : ℝ) :
    charFun μ ξ ≠ 0 := by
  intro habs
  have hzero : ∀ k : ℕ, charFun μ (ξ / 2 ^ k) = 0 := by
    intro k; induction k with
    | zero => simpa using habs
    | succ k ih =>
      rw [show ξ / 2 ^ (k + 1) = ξ / 2 ^ k / 2 from by rw [div_div, ← pow_succ]]
      exact charFun_half_eq_zero_of_charFun_eq_zero h ih
  have htend : Tendsto (fun k : ℕ => ξ / (2 : ℝ) ^ k) atTop (nhds 0) := by
    have h2 : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
    exact tendsto_const_nhds.div_atTop h2
  have hcont : Continuous (charFun μ) := MeasureTheory.continuous_charFun
  have hφ0 : charFun μ 0 = 1 := by simp [charFun_zero, Measure.real, measure_univ]
  have hlim : Tendsto (fun k => charFun μ (ξ / 2 ^ k)) atTop (nhds 1) := by
    rw [← hφ0]; exact (hcont.tendsto 0).comp htend
  have hlim0 : Tendsto (fun k => charFun μ (ξ / 2 ^ k)) atTop (nhds 0) := by
    rw [show (fun k => charFun μ (ξ / 2 ^ k)) = fun _ => (0 : ℂ) from funext hzero]
    exact tendsto_const_nhds
  exact one_ne_zero (tendsto_nhds_unique hlim0 hlim).symm

end NonVanishing

/-! ## Sub-lemma 2: Continuous logarithm -/


/-- An infinitely divisible probability measure has a continuous logarithm of its
characteristic function: there exists `ψ : ℝ → ℂ` continuous with `ψ 0 = 0` and
`charFun μ ξ = exp(ψ ξ)` for all `ξ`. -/
theorem IsInfinitelyDivisible.exists_continuous_log
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (h : IsInfinitelyDivisible μ) :
    ∃ ψ : ℝ → ℂ, Continuous ψ ∧ ψ 0 = 0 ∧ ∀ ξ, charFun μ ξ = exp (ψ ξ) := by
  -- The characteristic function is continuous and never vanishes
  have hcont : Continuous (charFun μ) := MeasureTheory.continuous_charFun
  have hne : ∀ ξ, charFun μ ξ ≠ 0 := h.charFun_ne_zero
  -- charFun μ 0 = 1
  have hφ0 : charFun μ 0 = 1 := by simp [charFun_zero, Measure.real, measure_univ]
  -- Build the ContinuousMap f : C(ℝ, ℂ) for the characteristic function
  set f : C(ℝ, ℂ) := ⟨charFun μ, hcont⟩
  -- exp 0 = 1 = charFun μ 0 = f 0
  have he : Complex.exp (0 : ℂ) = f (0 : ℝ) := by simp [f, hφ0]
  -- charFun μ maps into ℂ \ {0}
  have hs : ∀ ξ : ℝ, f ξ ∈ ({0}ᶜ : Set ℂ) := fun ξ => Set.mem_compl_singleton_iff.mpr (hne ξ)
  -- Apply the lifting theorem for covering maps:
  -- exp : ℂ → ℂ is a covering map on {0}ᶜ, ℝ is simply connected and locally path-connected
  obtain ⟨F, ⟨hF0, hFexp⟩, _⟩ :=
    Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts f he hs
  -- F is our continuous logarithm
  exact ⟨F, F.continuous, hF0, fun ξ => by
    have := congr_fun hFexp ξ
    simp [Function.comp] at this
    exact this.symm⟩

/-- Hermitian symmetry of the continuous logarithm: `ψ(-ξ) = conj(ψ(ξ))`.

Both `ψ` and `ξ ↦ conj(ψ(-ξ))` are continuous lifts of `charFun μ` through `exp`,
both equal to 0 at 0; by uniqueness of covering map lifts they coincide. -/
theorem IsInfinitelyDivisible.hermitian_log
    {μ : Measure ℝ} [IsProbabilityMeasure μ] (h : IsInfinitelyDivisible μ)
    {ψ : ℝ → ℂ} (hψ_cont : Continuous ψ) (hψ_zero : ψ 0 = 0)
    (hψ_exp : ∀ ξ, charFun μ ξ = exp (ψ ξ)) :
    ∀ ξ, ψ (-ξ) = starRingEnd ℂ (ψ ξ) := by
  have hcont : Continuous (charFun μ) := MeasureTheory.continuous_charFun
  have hne : ∀ ξ, charFun μ ξ ≠ 0 := h.charFun_ne_zero
  have hφ0 : charFun μ 0 = 1 := by simp [charFun_zero, Measure.real, measure_univ]
  set f : C(ℝ, ℂ) := ⟨charFun μ, hcont⟩
  have he : Complex.exp (0 : ℂ) = f (0 : ℝ) := by simp [f, hφ0]
  have hs : ∀ ξ : ℝ, f ξ ∈ ({0}ᶜ : Set ℂ) := fun ξ => Set.mem_compl_singleton_iff.mpr (hne ξ)
  obtain ⟨F, ⟨_hF0, _hFexp⟩, hF_unique⟩ :=
    Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts f he hs
  set Ψ : C(ℝ, ℂ) := ⟨ψ, hψ_cont⟩
  have hΨ_lift : Ψ 0 = 0 ∧ Complex.exp ∘ Ψ = f := by
    refine ⟨hψ_zero, ?_⟩
    ext ξ; simp [Ψ, f, hψ_exp ξ]
  set G : C(ℝ, ℂ) := ⟨fun ξ => starRingEnd ℂ (ψ (-ξ)), by
    exact continuous_star.comp (hψ_cont.comp continuous_neg)⟩
  have hG_lift : G 0 = 0 ∧ Complex.exp ∘ G = f := by
    refine ⟨by simp [G, hψ_zero], ?_⟩
    ext ξ; simp only [G, ContinuousMap.coe_mk, Function.comp_apply, f]
    rw [exp_conj, ← hψ_exp (-ξ), charFun_neg, starRingEnd_self_apply]
  have hΨ_eq : Ψ = F := hF_unique Ψ hΨ_lift
  have hG_eq : G = F := hF_unique G hG_lift
  have hΨG : ∀ ξ, ψ ξ = starRingEnd ℂ (ψ (-ξ)) := fun ξ => by
    have := congr_arg (· ξ) (hΨ_eq.trans hG_eq.symm)
    exact this
  intro ξ
  have := hΨG (-ξ)
  simp only [neg_neg] at this
  exact this


end ProbabilityTheory
