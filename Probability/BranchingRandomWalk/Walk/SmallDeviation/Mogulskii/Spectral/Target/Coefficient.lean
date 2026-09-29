module

public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.Target.Expansion

/-!
# Principal coefficient of an interior terminal target

The first Dirichlet coefficient of a terminal target is the normalized sum
of the positive ground state over that target.  A target occupying a fixed
fraction of an interior region therefore has a coefficient bounded away
from zero uniformly in the lattice width.
-/

open scoped BigOperators Matrix

@[expose] public section

namespace ProbabilityTheory.RandomWalk.Mogulskii

/-- Pairing a sine mode with a target indicator restricts the sum to the
target. -/
theorem intervalSineMode_dotProduct_targetIndicator
    {interiorCount : ℕ} (mode : Fin interiorCount)
    (target : Finset (Fin interiorCount)) :
    intervalSineMode interiorCount mode ⬝ᵥ intervalTargetIndicator target =
      ∑ i ∈ target, intervalSineMode interiorCount mode i := by
  classical
  rw [dotProduct]
  simp only [intervalTargetIndicator, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  simp

/-- The first sine-basis coefficient is the normalized ground-state mass of
the terminal target. -/
theorem intervalSineBasis_repr_targetIndicator_zero
    {interiorCount : ℕ} (hcount : 0 < interiorCount)
    (target : Finset (Fin interiorCount)) :
    (intervalSineBasis interiorCount).repr
        (intervalTargetIndicator target) ⟨0, hcount⟩ =
      2 * (∑ i ∈ target, intervalSineWeight interiorCount i) /
        ((interiorCount + 1 : ℕ) : ℝ) := by
  rw [intervalSineBasis_repr_eq_two_mul_dotProduct_div,
    intervalSineMode_dotProduct_targetIndicator,
    intervalSineMode_zero hcount]

/-- A pointwise ground-state lower bound on the target gives a quantitative
lower bound on its principal sine coefficient. -/
theorem two_mul_mul_card_div_le_intervalSineBasis_repr_targetIndicator_zero
    {interiorCount : ℕ} (hcount : 0 < interiorCount)
    (target : Finset (Fin interiorCount)) {weight : ℝ}
    (htarget : ∀ i ∈ target, weight ≤ intervalSineWeight interiorCount i) :
    2 * weight * target.card / ((interiorCount + 1 : ℕ) : ℝ) ≤
      (intervalSineBasis interiorCount).repr
        (intervalTargetIndicator target) ⟨0, hcount⟩ := by
  rw [intervalSineBasis_repr_targetIndicator_zero hcount]
  have hsum : weight * target.card ≤
      ∑ i ∈ target, intervalSineWeight interiorCount i := by
    calc
      weight * target.card = ∑ _i ∈ target, weight := by
        simp [mul_comm]
      _ ≤ _ := Finset.sum_le_sum fun i hi ↦ htarget i hi
  have hwidth : (0 : ℝ) < (interiorCount + 1 : ℕ) := by positivity
  apply (div_le_div_iff_of_pos_right hwidth).2
  nlinarith

/-- A lower bound on both the ground-state values and the relative target
cardinality gives a width-independent positive principal coefficient. -/
theorem two_mul_mul_le_intervalSineBasis_repr_targetIndicator_zero
    {interiorCount : ℕ} (hcount : 0 < interiorCount)
    (target : Finset (Fin interiorCount)) {weight proportion : ℝ}
    (hweight : 0 ≤ weight)
    (htarget : ∀ i ∈ target, weight ≤ intervalSineWeight interiorCount i)
    (hcard : proportion * ((interiorCount + 1 : ℕ) : ℝ) ≤ target.card) :
    2 * weight * proportion ≤
      (intervalSineBasis interiorCount).repr
        (intervalTargetIndicator target) ⟨0, hcount⟩ := by
  refine le_trans ?_
    (two_mul_mul_card_div_le_intervalSineBasis_repr_targetIndicator_zero
      hcount target htarget)
  have hwidth : (0 : ℝ) < (interiorCount + 1 : ℕ) := by positivity
  rw [le_div_iff₀ hwidth]
  have hmul : (2 * weight) *
        (proportion * ((interiorCount + 1 : ℕ) : ℝ)) ≤
      (2 * weight) * target.card :=
    mul_le_mul_of_nonneg_left hcard (mul_nonneg (by norm_num) hweight)
  nlinarith

end ProbabilityTheory.RandomWalk.Mogulskii
