/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Rademacher.Transition.Basic
public import Probability.Distributions.Rademacher

/-!
# Rademacher expectation of the transition operator

For the Rademacher law $\nu=\frac12(\delta_{-1}+\delta_1)$, the public
declarations identify the operator with its one-step expectation:

- `ProbabilityTheory.RandomWalk.Rademacher.integral_add_rademacherMeasure`:
  $\int f(x+y)\,\nu(dy)=\frac{f(x-1)+f(x+1)}2$.
- `integral_dirichletSine_add_rademacherMeasure`:
  $\int\phi_L(x+y)\,\nu(dy)=\cos(\pi/L)\phi_L(x)$, where
  $\phi_L(x)=\sin(\pi x/L)$.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk.Rademacher

/-- The one-step expectation of a translated test function under the
Rademacher increment law is `symmetricStep`. -/
theorem integral_add_rademacherMeasure (f : ℝ → ℝ) (x : ℝ) :
    ∫ increment, f (x + increment) ∂rademacherMeasure = symmetricStep f x := by
  rw [integral_rademacherMeasure]
  rw [show x + (-1 : ℝ) = x - 1 by ring]
  rfl

/-- The Dirichlet sine profile is an eigenfunction of the one-step
Rademacher transition. -/
theorem integral_dirichletSine_add_rademacherMeasure (length x : ℝ) :
    ∫ increment, dirichletSine length (x + increment) ∂rademacherMeasure =
      Real.cos (Real.pi / length) * dirichletSine length x := by
  rw [integral_add_rademacherMeasure, symmetricStep_dirichletSine]

end ProbabilityTheory.RandomWalk.Rademacher
