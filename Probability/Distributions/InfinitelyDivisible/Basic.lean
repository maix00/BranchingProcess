/-
Copyright (c) 2026 LeanLevy Contributors. All rights reserved.
Released under MIT license; see docs/third_party/LeanLevy/LICENSE.
Modified for this project from slink/LeanLevy at revision
7e73fd9b23ad52956ec2756a815889a783131ce4; see
docs/third_party/LeanLevy/provenance.md.
Authors: LeanLevy Contributors
-/
import MeasureTheory.Measure.Convolution.Power
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Infinitely Divisible Probability Measures

This file defines infinite divisibility and records the characteristic-function
formula for the shared measure convolution power.

## Main definitions

* `MeasureTheory.Measure.convPower` — the `n`-fold convolution power `μ^{∗n}`.
* `ProbabilityTheory.IsInfinitelyDivisible` — a probability measure `μ` is infinitely divisible
  if for every `n ≥ 1` there exists a probability measure `ν` with `μ = ν^{∗n}`.

## Main results

* `MeasureTheory.Measure.charFun_convPower` — `charFun (μ^{∗n}) t = (charFun μ t) ^ n`.
* `ProbabilityTheory.isInfinitelyDivisible_poissonMeasure_map` — the Poisson distribution
  is infinitely divisible.
* `ProbabilityTheory.IsLevyProcess.charFun_marginal_nat_pow` — for a Lévy process,
  `charFun(X(n)) = charFun(X(1))^n`.
-/

open MeasureTheory MeasureTheory.Measure ProbabilityTheory
open scoped NNReal ENNReal

/-! ## Characteristic functions of convolution powers -/

namespace MeasureTheory.Measure
theorem charFun_convPower {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [MeasurableAdd₂ E]
    (μ : Measure E) [IsProbabilityMeasure μ] (n : ℕ) (t : E) :
    charFun (μ.convPower n) t = (charFun μ t) ^ n := by
  induction n with
  | zero =>
    simp only [convPower_zero, charFun_dirac, inner_zero_left, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, pow_zero]
  | succ n ih =>
    rw [convPower_succ, charFun_conv, ih, pow_succ, mul_comm]

end MeasureTheory.Measure

/-! ## Infinite divisibility -/

namespace ProbabilityTheory

variable {E : Type*} [AddCommMonoid E] [MeasurableSpace E]

/-- A probability measure `μ` is **infinitely divisible** if for every `n ≥ 1`,
there exists a probability measure `ν` such that `μ = ν^{∗n}`. -/
def IsInfinitelyDivisible (μ : Measure E) : Prop :=
  ∀ n : ℕ, 0 < n → ∃ ν : Measure E, IsProbabilityMeasure ν ∧ μ = ν.convPower n


end ProbabilityTheory
