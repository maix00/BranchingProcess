import Probability.Process.RandomWalk.Rademacher
import Probability.Process.RandomWalk.Path.Basic
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Range.Basic

open MeasureTheory ProbabilityTheory
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

namespace ProbabilityTheory.RandomWalk.SmallDeviation.MogulskiiTest

/-- A fixed-width endpoint window strictly between consecutive lattice points. -/
def latticeEndpointWindowEvent (length : ℕ) : Set (ℕ → ℝ) :=
  {increment | AdditivePath.displacement length increment ∈
    Set.Icc (1 / 3 : ℝ) (2 / 3)}

theorem measurableSet_latticeEndpointWindowEvent (length : ℕ) :
    MeasurableSet (latticeEndpointWindowEvent length) := by
  exact measurableSet_Icc.preimage
    (ProbabilityTheory.RandomWalk.displacement_measurable length)

/-- For the simple symmetric walk, the endpoint window `[1/3, 2/3]` is
impossible at every integer time: the endpoint is integer-valued. This is the
lattice obstruction to an endpoint-window theorem with no fixed interior
width assumption. -/
theorem rademacher_latticeEndpointWindowEvent_measure_eq_zero
    (length : ℕ) :
    ProbabilityTheory.iidSequenceLaw rademacherMeasure
      (latticeEndpointWindowEvent length) = 0 := by
  rw [← ProbabilityTheory.RandomWalk.map_iidSequenceLaw_rademacherIncrementPath]
  rw [Measure.map_apply ProbabilityTheory.RandomWalk.measurable_rademacherIncrementPath
    (measurableSet_latticeEndpointWindowEvent length)]
  have hpreimage :
      ProbabilityTheory.RandomWalk.rademacherIncrementPath ⁻¹'
        latticeEndpointWindowEvent length = ∅ := by
    ext branch
    constructor
    · intro h
      have hwindow :
          (1 / 3 : ℝ) ≤ rademacherPartialSum length branch ∧
            rademacherPartialSum length branch ≤ 2 / 3 := by
        exact h
      rw [rademacherPartialSum_eq_intCast] at hwindow
      have hpos : (0 : ℝ) <
          (∑ k ∈ Finset.range length,
            rademacherIntIncrement (branch k) : ℤ) := by
        exact lt_of_lt_of_le (by norm_num) hwindow.1
      have hltReal :
          ((∑ k ∈ Finset.range length,
            rademacherIntIncrement (branch k) : ℤ) : ℝ) < 1 :=
        lt_of_le_of_lt hwindow.2 (by norm_num)
      have hlt :
          (∑ k ∈ Finset.range length,
            rademacherIntIncrement (branch k) : ℤ) < 1 := by
        exact_mod_cast hltReal
      have hposInt :
          (0 : ℤ) < ∑ k ∈ Finset.range length,
            rademacherIntIncrement (branch k) := by
        exact_mod_cast hpos
      omega
    · intro h
      cases h
  rw [hpreimage]
  simp

end ProbabilityTheory.RandomWalk.SmallDeviation.MogulskiiTest

#print axioms
  ProbabilityTheory.RandomWalk.SmallDeviation.MogulskiiTest.rademacher_latticeEndpointWindowEvent_measure_eq_zero
