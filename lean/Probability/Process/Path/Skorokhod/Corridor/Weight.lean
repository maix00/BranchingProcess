import Mathlib.Topology.UnitInterval
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Topology.Cadlag.Skorokhod.Corridor.Weight

/-!
# Measure bounds for Skorokhod corridor weights

The cutoff weights are path-space objects.  Their elementary domination by
the corresponding open corridor event is independent of any random-walk
construction and is kept next to the process-level Skorokhod Portmanteau
lemmas.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

/-- The corridor/endpoint cutoff is bounded by the probability of the strict
Skorokhod event on which it is positive. -/
theorem lintegral_corridorEndsInWeight_le_measure
    (μ : Measure (CadlagPath unitInterval ℝ))
    (lower upper endpointLower endpointUpper : ℝ) :
    ∫⁻ path, ENNReal.ofReal
        (Skorokhod.corridorEndsInWeight lower upper endpointLower endpointUpper path) ∂μ ≤
      μ (Skorokhod.rangeInOpenIntervalEndsIn
        lower upper endpointLower endpointUpper) := by
  let pathConstant : (CadlagPath unitInterval ℝ) → ℝ≥0∞ :=
    fun _ => 1
  let event := Skorokhod.rangeInOpenIntervalEndsIn
    lower upper endpointLower endpointUpper
  calc
    ∫⁻ path, ENNReal.ofReal
        (Skorokhod.corridorEndsInWeight lower upper endpointLower endpointUpper path) ∂μ ≤
        ∫⁻ path, (Set.indicator event pathConstant path) ∂μ := by
      apply lintegral_mono
      intro path
      by_cases hevent : path ∈ event
      · rw [Set.indicator_of_mem hevent]
        change ENNReal.ofReal
          (Skorokhod.corridorEndsInWeight lower upper endpointLower endpointUpper path) ≤ 1
        exact ENNReal.ofReal_le_one.mpr
          (Skorokhod.corridorEndsInWeight_le_one
            lower upper endpointLower endpointUpper path)
      · have hnotpos : ¬ 0 <
            Skorokhod.corridorEndsInWeight lower upper endpointLower endpointUpper path := by
          intro hpos
          apply hevent
          rw [Skorokhod.mem_rangeInOpenIntervalEndsIn_iff]
          exact (Skorokhod.corridorEndsInWeight_pos_iff
            lower upper endpointLower endpointUpper path).mp hpos
        have hzero :
            Skorokhod.corridorEndsInWeight lower upper endpointLower endpointUpper path = 0 :=
          le_antisymm (le_of_not_gt hnotpos)
            (Skorokhod.corridorEndsInWeight_nonneg
              lower upper endpointLower endpointUpper path)
        rw [Set.indicator_of_notMem hevent]
        change ENNReal.ofReal
          (Skorokhod.corridorEndsInWeight lower upper endpointLower endpointUpper path) ≤ 0
        simp [hzero]
    _ ≤ μ event := by
      dsimp [pathConstant]
      exact lintegral_indicator_one_le event

end ProbabilityTheory
