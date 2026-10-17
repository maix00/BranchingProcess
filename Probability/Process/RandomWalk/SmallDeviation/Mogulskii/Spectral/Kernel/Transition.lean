/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Basic
public import Probability.Distributions.Rademacher

/-!
# Rademacher transition and the sine ground state

This file identifies the analytic symmetric averaging operator with the
one-step transition of the Rademacher random walk.  Its public declarations
are:

* `integral_add_rademacherMeasure` proves
  $\mathbb E[f(x+X_1)]=\frac12(f(x-1)+f(x+1))$ for a fair Rademacher
  increment $X_1$.
* `integral_dirichletSine_add_rademacherMeasure` proves that the translated
  Dirichlet sine profile is an eigenfunction of this transition:
  $\mathbb E[\sin(\pi(x+X_1)/L)]=
  \cos(\pi/L)\sin(\pi x/L)$.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- The one-step expectation of a translated test function under the
Rademacher increment law is `symmetricStep`. -/
theorem integral_add_rademacherMeasure (f : ℝ → ℝ) (x : ℝ) :
    ∫ increment, f (x + increment) ∂rademacherMeasure = symmetricStep f x := by
  rw [integral_rademacherMeasure]
  rw [show x + (-1 : ℝ) = x - 1 by ring]
  rfl

/-- The Dirichlet sine profile is an eigenfunction of the actual one-step
Rademacher transition kernel. -/
theorem integral_dirichletSine_add_rademacherMeasure (length x : ℝ) :
    ∫ increment, dirichletSine length (x + increment) ∂rademacherMeasure =
      Real.cos (Real.pi / length) * dirichletSine length x := by
  rw [integral_add_rademacherMeasure, symmetricStep_dirichletSine]

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
