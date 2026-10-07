import Probability.Distributions.CharacteristicFunction.Tauberian.SecondTail
import Probability.Distributions.CharacteristicFunction.Tauberian.FrequencyAverage
import Probability.Distributions.CharacteristicFunction.Tauberian.FrequencyAverageLimit

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
#print axioms ProbabilityTheory.intervalIntegral_four_cosineDefect_sub_double
#print axioms ProbabilityTheory.exists_pos_closedAbsTail_le_cosineDefectFrequencyAverage
#print axioms ProbabilityTheory.exists_pos_symmetrizedClosedAbsTail_le_normDefectFrequencyAverage
#print axioms ProbabilityTheory.tendsto_frequencyCancellation_ratio_nhdsGT_zero
#print axioms ProbabilityTheory.exists_pos_closedAbsTail_le_cosineDefectFrequencyAverage_all
#print axioms ProbabilityTheory.tendsto_closedAbsTail_div_cosineDefect_atTop
#print axioms ProbabilityTheory.tendsto_symmetrizedClosedAbsTail_div_normDefect_atTop
