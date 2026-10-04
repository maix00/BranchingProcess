/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Sequence.IID
public import Probability.ConvergenceInDistribution.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Domains of attraction

General domain-of-attraction definitions for normalized i.i.d. sums.  Stable
limit laws are added in the stable-distribution layer.
-/

open Filter MeasureTheory
open scoped BigOperators

@[expose] public section

namespace ProbabilityTheory

/-- A centered and scaled sum of the first `n` coordinates. -/
noncomputable def normalizedIidSum (scale center : ℕ → ℝ) (n : ℕ)
    (sequence : ℕ → ℝ) : ℝ :=
  (scale n)⁻¹ * ((∑ k ∈ Finset.range n, sequence k) - center n)

theorem normalizedIidSum_measurable (scale center : ℕ → ℝ) (n : ℕ) :
    Measurable (normalizedIidSum scale center n) := by
  unfold normalizedIidSum
  fun_prop

/-- Attraction to `limit` along specified normalization and centering
sequences.  Keeping these witnesses visible is necessary for functional
limit theorems on path space. -/
def IsInDomainOfAttractionAlong (ν limit : Measure ℝ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure limit]
    (scale center : ℕ → ℝ) : Prop :=
  (∀ᶠ n in atTop, 0 < scale n) ∧
    TendstoInDistribution (normalizedIidSum scale center) atTop id
      (fun _ => iidSequenceLaw ν) limit

namespace IsInDomainOfAttractionAlong

theorem eventually_scale_pos {ν limit : Measure ℝ}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure limit]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν limit scale center) :
    ∀ᶠ n in atTop, 0 < scale n := h.1

theorem tendstoInDistribution {ν limit : Measure ℝ}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure limit]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν limit scale center) :
    TendstoInDistribution (normalizedIidSum scale center) atTop id
      (fun _ => iidSequenceLaw ν) limit := h.2

end IsInDomainOfAttractionAlong

set_option linter.style.haveILetI false in
/-- Rescaling the normalization by `r⁻¹` rescales the limiting law by `r`.
This is the continuous-mapping theorem together with the identity between the
two normalized sums; only eventual positivity of the original scale is needed. -/
theorem IsInDomainOfAttractionAlong.rescale
    {ν limit : Measure ℝ} [IsProbabilityMeasure ν] [IsProbabilityMeasure limit]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν limit scale center)
    (r : ℝ) (hr : 0 < r) :
    IsInDomainOfAttractionAlong ν (limit.map fun x => r * x)
      (fun n => r⁻¹ * scale n) center := by
  let f : ℝ → ℝ := fun x => r * x
  let scale' : ℕ → ℝ := fun n => r⁻¹ * scale n
  let limit' : Measure ℝ := limit.map f
  have hf : Measurable f := by fun_prop
  have hfcont : Continuous f := by fun_prop
  have hscalePos : ∀ᶠ n : ℕ in atTop, 0 < scale' n := by
    filter_upwards [h.eventually_scale_pos] with n hn
    exact mul_pos (inv_pos.mpr hr) hn
  have hcontinuous := h.tendstoInDistribution.continuous_comp hfcont
  haveI : IsProbabilityMeasure limit' := by
    dsimp [limit']
    infer_instance
  have hlimitLaw : limit.map (f ∘ id) = limit'.map id := by
    simp [limit']
  have hcontinuous' := MeasureTheory.TendstoInDistribution.congr_limit
    hcontinuous aemeasurable_id hlimitLaw
  have hscaleEq : ∀ᶠ n : ℕ in atTop,
      (fun ω => f (normalizedIidSum scale center n ω)) =ᵐ[iidSequenceLaw ν]
        normalizedIidSum scale' center n := by
    filter_upwards [h.eventually_scale_pos] with n hn
    filter_upwards [] with ω
    have hscaleNe : scale n ≠ 0 := hn.ne'
    dsimp [normalizedIidSum, f, scale']
    have hfactor : (r⁻¹ * scale n)⁻¹ = r * (scale n)⁻¹ := by
      field_simp [hr.ne', hscaleNe]
    rw [hfactor]
    ring
  have hconvergence := hcontinuous'.congr_eventually hscaleEq
    (fun n => (normalizedIidSum_measurable scale' center n).aemeasurable)
  exact ⟨hscalePos, hconvergence⟩

/-- A one-step law belongs to the domain of attraction of `limit` when some
eventually positive scaling and deterministic centering make its normalized
i.i.d. sums converge to `limit` in distribution. -/
def IsInDomainOfAttraction (ν limit : Measure ℝ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure limit] : Prop :=
  ∃ scale center : ℕ → ℝ,
    IsInDomainOfAttractionAlong ν limit scale center

theorem IsInDomainOfAttractionAlong.isInDomainOfAttraction
    {ν limit : Measure ℝ}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure limit]
    {scale center : ℕ → ℝ}
    (h : IsInDomainOfAttractionAlong ν limit scale center) :
    IsInDomainOfAttraction ν limit := ⟨scale, center, h⟩

end ProbabilityTheory

end
