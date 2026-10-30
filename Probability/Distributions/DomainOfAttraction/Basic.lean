/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Sequence.IID.Basic
public import Probability.ConvergenceInDistribution.Basic
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Domains of attraction

General domain-of-attraction definitions for normalized i.i.d. sums.  Stable
limit laws are added in the stable-distribution layer.

## Public declarations

* `ProbabilityTheory.normalizedIidSum` is the centered normalized sum
  $a_n^{-1}(\sum_{k<n}x_k-b_n)$, and
  `ProbabilityTheory.normalizedIidSum_measurable` proves it measurable.
* `ProbabilityTheory.IsInDomainOfAttractionAlong(ν, μ, a, b)` records eventual positivity of
  $a_n$ and convergence in distribution of the normalized i.i.d. sums with
  increment law $ν$ to $μ$. Its projections are
  `ProbabilityTheory.IsInDomainOfAttractionAlong.eventually_scale_pos` and
  `ProbabilityTheory.IsInDomainOfAttractionAlong.tendstoInDistribution`.
* `ProbabilityTheory.IsInDomainOfAttraction(ν, μ)` existentially packages a
  normalization and centering for that convergence;
  `ProbabilityTheory.IsInDomainOfAttractionAlong.isInDomainOfAttraction`
  forgets the specified sequences.
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
