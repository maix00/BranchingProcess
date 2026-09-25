import ThesisSpeed.Probability.PointProcess.Measure

/-!
# Finite truncations of the spine weight

The full offspring weight is a countable `ENNReal` sum.  This file records
the measurable finite truncations used before applying monotone convergence.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace ThesisSpeed.Spine

noncomputable def truncatedChildWeight (n : ℕ) (ξ : OffspringMark) : ENNReal :=
  by
    classical
    exact ∑ i ∈ Finset.range n, if ξ ∈ childRealized i then
      ENNReal.ofReal (Real.exp (-childDisplacement ξ i)) else 0

theorem truncatedChildWeight_measurable (n : ℕ) :
    Measurable (truncatedChildWeight n) := by
  classical
  unfold truncatedChildWeight
  apply Finset.measurable_sum
  intro i hi
  have hval : Measurable (fun ξ : OffspringMark =>
      ENNReal.ofReal (Real.exp (-childDisplacement ξ i))) :=
    ENNReal.measurable_ofReal.comp
      ((childDisplacement_measurable i).neg.exp)
  exact hval.ite (childRealized_measurable i) measurable_const

theorem truncatedChildWeight_mono {n : ℕ} (ξ : OffspringMark) :
    truncatedChildWeight n ξ ≤ truncatedChildWeight (n + 1) ξ := by
  classical
  unfold truncatedChildWeight
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_subset_range.mpr (Nat.le_succ n)
  · intro i hi hnot
    positivity

end ThesisSpeed.Spine
