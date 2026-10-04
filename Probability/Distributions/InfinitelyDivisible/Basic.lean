/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license; see docs/third_party/LeanLevy/LICENSE.
Modified for this project from slink/LeanLevy at revision
7e73fd9b23ad52956ec2756a815889a783131ce4; see
docs/third_party/LeanLevy/provenance.md.
Authors: LeanLevy Contributors
-/
module

public import MeasureTheory.Measure.Convolution.Power

/-!
# Infinitely Divisible Probability Measures

This file defines infinite divisibility in terms of the shared measure
convolution power.

## Main definition

* `ProbabilityTheory.IsInfinitelyDivisible` — a probability measure `μ` is infinitely divisible
  if for every `n ≥ 1` there exists a probability measure `ν` with `μ = ν^{∗n}`.

Natural convolution powers are provided by
`MeasureTheory.Measure.Convolution.Power`, and characteristic-function
identities for them are provided by
`MeasureTheory.Measure.CharacteristicFunction.Convolution`.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal

namespace ProbabilityTheory

variable {E : Type*} [AddCommMonoid E] [MeasurableSpace E]

/-- A probability measure `μ` is **infinitely divisible** if for every `n ≥ 1`,
there exists a probability measure `ν` such that `μ = ν^{∗n}`. -/
def IsInfinitelyDivisible (μ : Measure E) : Prop :=
  ∀ n : ℕ, 0 < n → ∃ ν : Measure E, IsProbabilityMeasure ν ∧ μ = ν.convPower n


end ProbabilityTheory
