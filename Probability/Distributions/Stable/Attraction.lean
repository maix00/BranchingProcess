import Probability.Distributions.Stable.Basic
import Probability.Sequence.IID
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-!
# Domains of attraction

The definition uses the canonical i.i.d. sequence law, so membership is a
property of the one-step measure and does not depend on a chosen probability
space realization.
-/

open Filter MeasureTheory
open scoped BigOperators

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

/-- Domain of attraction together with the assertion that the limiting law
is a nondegenerate `α`-stable law. -/
def IsInAlphaStableDomainOfAttraction
    (α : ℝ) (ν limit : Measure ℝ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure limit] : Prop :=
  IsAlphaStable α limit ∧ IsInDomainOfAttraction ν limit

/-- The witness-preserving version of `IsInAlphaStableDomainOfAttraction`.

Mogulskii's proof uses the actual norming and centering sequences in every
block.  The existential domain-of-attraction predicate is therefore too weak
for that purpose: it records that some witnesses exist, but does not expose
which witnesses are used by the functional limit theorem. -/
def IsInAlphaStableDomainOfAttractionAlong
    (α : ℝ) (ν limit : Measure ℝ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure limit]
    (scale center : ℕ → ℝ) : Prop :=
  IsAlphaStable α limit ∧
    IsInDomainOfAttractionAlong ν limit scale center

namespace IsInAlphaStableDomainOfAttraction

theorem stable {α : ℝ} {ν limit : Measure ℝ}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure limit]
    (h : IsInAlphaStableDomainOfAttraction α ν limit) :
    IsAlphaStable α limit := h.1

theorem domain {α : ℝ} {ν limit : Measure ℝ}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure limit]
    (h : IsInAlphaStableDomainOfAttraction α ν limit) :
    IsInDomainOfAttraction ν limit := h.2

end IsInAlphaStableDomainOfAttraction

namespace IsInAlphaStableDomainOfAttractionAlong

theorem stable {α : ℝ} {ν limit : Measure ℝ}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure limit]
    {scale center : ℕ → ℝ}
    (h : IsInAlphaStableDomainOfAttractionAlong α ν limit scale center) :
    IsAlphaStable α limit := h.1

theorem attraction {α : ℝ} {ν limit : Measure ℝ}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure limit]
    {scale center : ℕ → ℝ}
    (h : IsInAlphaStableDomainOfAttractionAlong α ν limit scale center) :
    IsInDomainOfAttractionAlong ν limit scale center := h.2

theorem isInAlphaStableDomainOfAttraction
    {α : ℝ} {ν limit : Measure ℝ}
    [IsProbabilityMeasure ν] [IsProbabilityMeasure limit]
    {scale center : ℕ → ℝ}
    (h : IsInAlphaStableDomainOfAttractionAlong α ν limit scale center) :
    IsInAlphaStableDomainOfAttraction α ν limit :=
  ⟨h.1, h.2.isInDomainOfAttraction⟩

end IsInAlphaStableDomainOfAttractionAlong

end ProbabilityTheory
