/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.DomainOfAttraction.Basic
public import Probability.Distributions.Stable.Basic

/-!
# Stable domains of attraction

The general attraction predicate is defined in
`Probability.Distributions.DomainOfAttraction.Basic`.  This module adds the
stable-limit combinations and keeps their established import path.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory

/-- Domain of attraction together with the assertion that the limiting law
is a nondegenerate `α`-stable law. -/
def IsInAlphaStableDomainOfAttraction
    (α : ℝ) (ν limit : Measure ℝ)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure limit] : Prop :=
  IsAlphaStable α limit ∧ IsInDomainOfAttraction ν limit

/-- The witness-preserving version of `IsInAlphaStableDomainOfAttraction`.

The actual norming and centering sequences are retained for functional limit
theorems on path space. -/
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

end
