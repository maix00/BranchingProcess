import Probability.Distributions.CharacteristicFunction.Tauberian.SecondTail

/-! Check exact tail inversion on general probability laws, including point
masses. No density, symmetry, or nondegeneracy is part of this API. -/

open MeasureTheory

example (y x : ℝ) (hx : 0 ≤ x) :
    Asymptotics.secondTailIntegral
      (fun t : ℝ => (Measure.dirac y).real {z : ℝ | t < |z|}) x =
      x * (min |y| x) ^ 2 / 2 - (min |y| x) ^ 3 / 3 := by
  rw [ProbabilityTheory.secondTailIntegral_twoSidedTail_eq_cappedCubic
    (Measure.dirac y) hx]
  simp

example (x : ℝ) (hx : 0 ≤ x) :
    Asymptotics.secondTailIntegral
      (fun t : ℝ => (Measure.dirac (0 : ℝ)).real {z : ℝ | t < |z|}) x = 0 := by
  rw [ProbabilityTheory.secondTailIntegral_twoSidedTail_eq_cappedCubic
    (Measure.dirac (0 : ℝ)) hx]
  simp [min_eq_left hx]

#print axioms ProbabilityTheory.secondTailIntegral_eq_cosineDefect_kernel
#print axioms ProbabilityTheory.secondTailIntegral_twoSidedTail_eq_cappedCubic
