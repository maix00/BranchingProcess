import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic

/-!
# Bounds from a positive eigenfunction

These finite-state inequalities convert a weighted mass identity into upper
and lower bounds for total mass.  In the killed-walk application, total mass
is survival probability and the weight is the positive ground state.
-/

open scoped BigOperators

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk.Mogulskii

section FiniteState

variable {ι : Type*}

/-- A pointwise lower bound on a nonnegative weight gives a lower bound on
weighted mass. -/
theorem mul_sum_le_sum_mul_of_le
    (s : Finset ι) (mass weight : ι → ℝ) (lower : ℝ)
    (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (hweight : ∀ i ∈ s, lower ≤ weight i) :
    lower * ∑ i ∈ s, mass i ≤ ∑ i ∈ s, mass i * weight i := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi =>
    by simpa [mul_comm] using
      mul_le_mul_of_nonneg_left (hweight i hi) (hmass i hi)

/-- A pointwise upper bound on a nonnegative weight gives an upper bound on
weighted mass. -/
theorem sum_mul_le_mul_sum_of_le
    (s : Finset ι) (mass weight : ι → ℝ) (upper : ℝ)
    (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (hweight : ∀ i ∈ s, weight i ≤ upper) :
    (∑ i ∈ s, mass i * weight i) ≤ upper * ∑ i ∈ s, mass i := by
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi =>
    by simpa [mul_comm] using
      mul_le_mul_of_nonneg_left (hweight i hi) (hmass i hi)

/-- If a weighted mass equals `spectralMass`, bounds on the weight turn it
into bounds on total mass. -/
theorem totalMass_bounds_of_weightedMass
    (s : Finset ι) (mass weight : ι → ℝ) (lower upper spectralMass : ℝ)
    (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (hlower : ∀ i ∈ s, lower ≤ weight i)
    (hupper : ∀ i ∈ s, weight i ≤ upper)
    (hweighted : ∑ i ∈ s, mass i * weight i = spectralMass) :
    lower * ∑ i ∈ s, mass i ≤ spectralMass ∧
      spectralMass ≤ upper * ∑ i ∈ s, mass i := by
  rw [← hweighted]
  exact ⟨mul_sum_le_sum_mul_of_le s mass weight lower hmass hlower,
    sum_mul_le_mul_sum_of_le s mass weight upper hmass hupper⟩

/-- Solved form of the lower survival bound: weighted mass divided by an
upper ground-state bound is at most total mass. -/
theorem div_le_totalMass_of_weightedMass
    (s : Finset ι) (mass weight : ι → ℝ) (upper spectralMass : ℝ)
    (hupper_pos : 0 < upper)
    (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (hweight : ∀ i ∈ s, weight i ≤ upper)
    (hweighted : ∑ i ∈ s, mass i * weight i = spectralMass) :
    spectralMass / upper ≤ ∑ i ∈ s, mass i := by
  rw [div_le_iff₀ hupper_pos, ← hweighted]
  simpa [mul_comm] using
    sum_mul_le_mul_sum_of_le s mass weight upper hmass hweight

/-- Solved form of the upper survival bound: total mass is at most weighted
mass divided by a positive lower ground-state bound. -/
theorem totalMass_le_div_of_weightedMass
    (s : Finset ι) (mass weight : ι → ℝ) (lower spectralMass : ℝ)
    (hlower_pos : 0 < lower)
    (hmass : ∀ i ∈ s, 0 ≤ mass i)
    (hweight : ∀ i ∈ s, lower ≤ weight i)
    (hweighted : ∑ i ∈ s, mass i * weight i = spectralMass) :
    (∑ i ∈ s, mass i) ≤ spectralMass / lower := by
  rw [le_div_iff₀ hlower_pos, ← hweighted]
  simpa [mul_comm] using
    mul_sum_le_sum_mul_of_le s mass weight lower hmass hweight

end FiniteState

end ProbabilityTheory.BranchingRandomWalk.RandomWalk.Mogulskii
