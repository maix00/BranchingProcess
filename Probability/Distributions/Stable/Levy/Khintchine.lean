/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Stable.Basic
public import Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Defs
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Probability.Distributions.Stable.Operations.Convolution
import Probability.Distributions.InfinitelyDivisible.LevyKhintchine.Uniqueness

/-!
# Lévy–Khintchine representation of a strictly stable law

This file applies the measure-level Lévy–Khintchine theorem to strictly stable
laws.

Strict stability first yields infinite divisibility.  Writing
`\widehat\mu(\xi)=charFun μ ξ`, there is a unique Lévy–Khintchine triple `T`
whose exponent represents the characteristic function:

\[
\exists!\,T\quad
\forall\xi\in\mathbb R,\qquad
\widehat\mu(\xi)=\exp(T.\operatorname{exponent}(\xi)).
\]

## Public declarations

* `IsStrictlyAlphaStable.isInfinitelyDivisible`: every strictly stable law is
  infinitely divisible, with each positive convolution order witnessed by a
  probability measure.
* `IsStrictlyAlphaStable.existsUnique_levyKhintchineTriple`: each strictly
  stable law has a unique triple `T` satisfying
  `charFun μ ξ = Complex.exp (T.exponent ξ)` for all `ξ`.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory MeasureTheory.Measure

/-- A strictly stable law is infinitely divisible. -/
theorem IsStrictlyAlphaStable.isInfinitelyDivisible
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ) :
    IsInfinitelyDivisible μ := by
  intro n hn
  obtain ⟨ν, hν, hpower⟩ := h.exists_convPower_root n hn
  exact ⟨ν, hν, hpower⟩

/-- The real stable law has a unique Lévy–Khintchine triple. -/
theorem IsStrictlyAlphaStable.existsUnique_levyKhintchineTriple
    {α : ℝ} {μ : Measure ℝ} (h : IsStrictlyAlphaStable α μ) :
    ∃! T : LevyKhintchineTriple,
      ∀ ξ : ℝ, charFun μ ξ = Complex.exp (T.exponent ξ) := by
  let : IsProbabilityMeasure μ := h.isProbabilityMeasure
  exact ProbabilityTheory.existsUnique_levyKhintchineTriple
    h.isInfinitelyDivisible

end ProbabilityTheory
