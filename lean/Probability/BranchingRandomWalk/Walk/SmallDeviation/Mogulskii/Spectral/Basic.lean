import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Spectral input for the symmetric lattice walk

The killed simple symmetric walk on an interval has a sine ground state.
This file isolates the analytic identity behind that computation from the
probability-space realization of the walk.
-/

namespace ProbabilityTheory.RandomWalk.Mogulskii

/-- The one-step averaging operator of the simple symmetric walk. -/
noncomputable def symmetricStep (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  (f (x - 1) + f (x + 1)) / 2

/-- A sine wave is an eigenfunction of the symmetric averaging operator. -/
theorem symmetricStep_sine (frequency x : ℝ) :
    symmetricStep (fun y => Real.sin (frequency * y)) x =
      Real.cos frequency * Real.sin (frequency * x) := by
  rw [symmetricStep]
  rw [show frequency * (x - 1) = frequency * x - frequency by ring,
    show frequency * (x + 1) = frequency * x + frequency by ring]
  rw [Real.sin_sub, Real.sin_add]
  ring

/-- The Dirichlet sine profile for an interval of real length `length`. -/
noncomputable def dirichletSine (length x : ℝ) : ℝ :=
  Real.sin ((Real.pi / length) * x)

@[simp]
theorem dirichletSine_zero (length : ℝ) :
    dirichletSine length 0 = 0 := by
  simp [dirichletSine]

@[simp]
theorem dirichletSine_right (length : ℝ) (hlength : length ≠ 0) :
    dirichletSine length length = 0 := by
  simp [dirichletSine, hlength]

/-- The Dirichlet sine profile is strictly positive inside a positive
interval. -/
theorem dirichletSine_pos {length x : ℝ} (hlength : 0 < length)
    (hx : x ∈ Set.Ioo 0 length) :
    0 < dirichletSine length x := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact mul_pos (div_pos Real.pi_pos hlength) hx.1
  · rw [div_mul_eq_mul_div, div_lt_iff₀ hlength]
    nlinarith [Real.pi_pos, hx.2]

/-- The sine ground state has eigenvalue `cos (π / length)`. -/
theorem symmetricStep_dirichletSine (length x : ℝ) :
    symmetricStep (dirichletSine length) x =
      Real.cos (Real.pi / length) * dirichletSine length x := by
  change symmetricStep (fun y => Real.sin ((Real.pi / length) * y)) x = _
  exact symmetricStep_sine (Real.pi / length) x

/-- Iterating the symmetric averaging operator raises the sine eigenvalue to
the corresponding power. -/
theorem iterate_symmetricStep_dirichletSine (length : ℝ) (n : ℕ) :
    (symmetricStep^[n]) (dirichletSine length) =
      fun x => Real.cos (Real.pi / length) ^ n * dirichletSine length x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      funext x
      simp only [symmetricStep, dirichletSine]
      rw [show (Real.pi / length) * (x - 1) =
          (Real.pi / length) * x - Real.pi / length by ring,
        show (Real.pi / length) * (x + 1) =
          (Real.pi / length) * x + Real.pi / length by ring]
      rw [Real.sin_sub, Real.sin_add]
      ring

end ProbabilityTheory.RandomWalk.Mogulskii
