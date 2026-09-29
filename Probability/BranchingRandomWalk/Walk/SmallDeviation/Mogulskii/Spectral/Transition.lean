module

public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.Basic
public import Probability.Distributions.Rademacher

/-!
# Rademacher transition and the sine ground state

This file identifies the analytic symmetric averaging operator with the
one-step transition of the Rademacher random walk.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk.Mogulskii

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

end ProbabilityTheory.RandomWalk.Mogulskii
