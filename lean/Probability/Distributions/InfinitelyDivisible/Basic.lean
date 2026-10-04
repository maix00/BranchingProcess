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

@[expose] public section

/-!
# Infinitely Divisible Probability Measures

This file defines infinite divisibility in terms of the shared measure
convolution power.

## Main definitions

* `MeasureTheory.Measure.convPower` — the `n`-fold convolution power `μ^{∗n}`.
* `ProbabilityTheory.IsInfinitelyDivisible` — a probability measure `μ` is infinitely divisible
  if for every `n ≥ 1` there exists a probability measure `ν` with `μ = ν^{∗n}`.

## Main results

* `ProbabilityTheory.isInfinitelyDivisible_poissonMeasure_map` — the Poisson distribution
  is infinitely divisible.
* `ProbabilityTheory.IsLevyProcess.charFun_marginal_nat_pow` — for a Lévy process,
  `charFun(X(n)) = charFun(X(1))^n`.
-/

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal

/-! ## Infinite divisibility -/

namespace ProbabilityTheory

variable {E : Type*} [AddCommMonoid E] [MeasurableSpace E]

/-- A probability measure `μ` is **infinitely divisible** if for every `n ≥ 1`,
there exists a probability measure `ν` such that `μ = ν^{∗n}`. -/
def IsInfinitelyDivisible (μ : Measure E) : Prop :=
  ∀ n : ℕ, 0 < n → ∃ ν : Measure E, IsProbabilityMeasure ν ∧ μ = ν.convPower n


end ProbabilityTheory
