import Probability.BranchingRandomWalk.PointProcess.PointMeasure

/-!
# Finite truncations of the spine weight

The full child weight is a countable `ENNReal` sum.  This file records
the measurable finite truncations used before applying monotone convergence.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open UlamHarris BranchingStep MeasureTheory



noncomputable def truncatedChildWeight (n : ℕ) (ξ : NatRealBranchingStep) : ENNReal :=
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
  have hval : Measurable (fun ξ : NatRealBranchingStep =>
      ENNReal.ofReal (Real.exp (-childDisplacement ξ i))) :=
    ENNReal.measurable_ofReal.comp
      ((childDisplacement_measurable i).neg.exp)
  exact hval.ite (childRealized_measurable i) measurable_const

theorem truncatedChildWeight_mono {n : ℕ} (ξ : NatRealBranchingStep) :
    truncatedChildWeight n ξ ≤ truncatedChildWeight (n + 1) ξ := by
  classical
  unfold truncatedChildWeight
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_subset_range.mpr (Nat.le_succ n)
  · intro i hi hnot
    positivity

theorem truncatedChildWeight_eq_finset_sum (n : ℕ) (ξ : NatRealBranchingStep) :
    truncatedChildWeight n ξ =
      ∑ i ∈ Finset.range n, realizedChildWeight ξ i := by
  rfl

theorem truncatedChildWeight_le_total (n : ℕ) (ξ : NatRealBranchingStep) :
    truncatedChildWeight n ξ ≤ totalChildWeight ξ := by
  rw [truncatedChildWeight_eq_finset_sum]
  exact ENNReal.sum_le_tsum (Finset.range n)

theorem truncatedChildWeight_iSup (ξ : NatRealBranchingStep) :
    ⨆ n : ℕ, truncatedChildWeight n ξ = totalChildWeight ξ := by
  apply le_antisymm
  · refine iSup_le fun n => truncatedChildWeight_le_total n ξ
  · apply ENNReal.tsum_le_of_sum_range_le
    intro n
    exact le_iSup (fun k : ℕ => truncatedChildWeight k ξ) n

end ProbabilityTheory.BranchingRandomWalk.Spine
