/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license; see docs/third_party/LeanLevy/LICENSE.
Modified for this project from slink/LeanLevy at revision
7e73fd9b23ad52956ec2756a815889a783131ce4; see
docs/third_party/LeanLevy/provenance.md.
Authors: LeanLevy Contributors
-/
module

public import Analysis.Fourier.PositiveDefinite
public import MeasureTheory.Measure.CharacteristicFunction.PositiveDefinite
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Probability.Distributions.Gaussian.Real
import all Analysis.Fourier.Bochner.Lemmas.GaussianSmoothing

/-!
# Bochner's theorem on ℝ

## Public declarations

* `ProbabilityTheory.bochner`: for every continuous positive-definite φ : ℝ → ℂ with
  φ 0 = 1, there is a probability measure μ on ℝ such that
  $∀ ξ ∈ ℝ, charFun(μ, ξ) = φ(ξ)$.

  Its full implication is
  $∀ φ ∈ C(ℝ; ℂ), IsPositiveDefinite(φ) ∧ φ(0) = 1 ⟹
  ∃ μ ∈ 𝒫(ℝ), ∀ ξ ∈ ℝ, charFun(μ, ξ) = φ(ξ)$.

## Proof route

The proof first multiplies `φ` by Gaussian characteristic functions to obtain integrable
positive-definite functions. The inverse-Fourier density construction, its Fejér approximation,
and the Gaussian-smoothing estimates are grouped under `Lemmas/`. The final step uses tightness,
Prokhorov compactness, and uniqueness of pointwise limits.

The theorem is stated on `ℝ`, matching the one-dimensional Fourier and Gaussian APIs used by this
construction. The internal proof stages are not exported as public results.

## Source

This is the probability-normalized form of S. Bochner, “A theorem on Fourier-Stieltjes integrals,”
*Bulletin of the American Mathematical Society* 40, no. 4 (1934), 271–276, §1,
https://doi.org/10.1090/S0002-9904-1934-05843-9. Bochner's representation is by a finite positive
measure; the condition `φ 0 = 1` makes its total mass one.
-/

@[expose] public section

open MeasureTheory Complex ComplexConjugate Filter Topology Set Function
open scoped NNReal ENNReal FourierTransform RealInnerProductSpace

namespace ProbabilityTheory

/-! ### Main theorem -/

/-- **Bochner's theorem (ℝ only).** A continuous positive definite function `φ : ℝ → ℂ`
with `φ(0) = 1` is the characteristic function of a probability measure on ℝ.

This is the probability-normalized Fourier-Stieltjes representation in Bochner,
“A theorem on Fourier-Stieltjes integrals,” *Bull. Amer. Math. Soc.* 40, no. 4 (1934), §1.

Proof: Gaussian smoothing + Prokhorov + charfun identification. -/
theorem bochner
    (φ : ℝ → ℂ) (hφc : Continuous φ) (hpd : IsPositiveDefinite φ)
    (h0 : φ 0 = 1) :
    ∃ μ : ProbabilityMeasure ℝ,
      ∀ ξ, charFun (μ : Measure ℝ) ξ = φ ξ := by
  -- Step 1: For each n, the smoothed function φₙ(ξ) = φ(ξ) · charFun(N(0,1/(n+1)))(ξ)
  -- is continuous, PD, L¹, and equals 1 at 0.
  -- By exists_probMeasure_of_pd_integrable, get μₙ with charFun μₙ = φₙ.
  have hsmoothed : ∀ n : ℕ, ∃ μn : ProbabilityMeasure ℝ,
      ∀ ξ, charFun (μn : Measure ℝ) ξ =
        φ ξ * charFun (gaussianReal 0 (gaussianVar n)) ξ :=
    fun n => exists_probMeasure_of_pd_integrable _ (continuous_smoothed hφc n)
      (pd_smoothed hpd n) (smoothed_at_zero h0 n) (integrable_smoothed hφc hpd h0 n)
  -- Extract the sequence using choice.
  choose μs hμs using hsmoothed
  -- Step 2: The characteristic functions of μₙ converge pointwise to φ.
  have hcharfun_conv :
      ∀ ξ, Tendsto (fun n => charFun (μs n : Measure ℝ) ξ) atTop (𝓝 (φ ξ)) := by
    intro ξ
    have : ∀ n, charFun (μs n : Measure ℝ) ξ =
        φ ξ * charFun (gaussianReal 0 (gaussianVar n)) ξ := by
      intro n; exact (hμs n ξ).symm ▸ rfl
    simp_rw [this]
    exact tendsto_smoothed φ ξ
  -- Step 3: The sequence {μₙ} is tight.
  have htight := isTight_of_charFun_pointwise_tendsto hφc hcharfun_conv
  -- Step 4: Convert to the right form for Prokhorov.
  have htight' : IsTightMeasureSet
      {((ν : ProbabilityMeasure ℝ) : Measure ℝ) | ν ∈ range μs} := by
    convert htight using 1
    ext x; simp [mem_range]
  -- Step 5: By Prokhorov, the closure of the range is compact.
  have hcompact : IsCompact (closure (range μs)) :=
    isCompact_closure_of_isTightMeasureSet htight'
  -- Step 6: Extract a convergent subsequence.
  have hin_closure : ∀ n, μs n ∈ closure (range μs) :=
    fun n => subset_closure (mem_range_self n)
  obtain ⟨ν, _, ns, hns_mono, hns_tendsto⟩ := hcompact.tendsto_subseq hin_closure
  -- Step 7: By the easy direction of Lévy, charFun ν = lim charFun μₙₖ.
  -- Also charFun μₙₖ → φ by our construction. By limit uniqueness, charFun ν = φ.
  have hcharfun_ν : ∀ ξ, charFun (ν : Measure ℝ) ξ = φ ξ := by
    intro ξ
    -- charFun (μs (ns n)) ξ → charFun ν ξ (by weak convergence)
    have h_weak := ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp hns_tendsto ξ
    simp only [Function.comp_def] at h_weak
    -- charFun (μs (ns n)) ξ → φ ξ (by our convergence + subsequence)
    have h_phi := (hcharfun_conv ξ).comp hns_mono.tendsto_atTop
    -- By uniqueness of limits
    exact tendsto_nhds_unique h_weak h_phi
  -- Step 8: ν is the desired probability measure.
  exact ⟨ν, hcharfun_ν⟩

end ProbabilityTheory
