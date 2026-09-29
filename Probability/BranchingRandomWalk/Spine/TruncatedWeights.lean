module

public import Combinatorics.BranchingWalk.Step.ExponentialWeight
public import Combinatorics.BranchingWalk.Step.SlotOrder

@[expose] public section

/-!
# Finite truncations of a spine weight

The full child weight is a countable `ENNReal` sum.  For any abstract ordered
slot type of order type `ℕ`, the first `n` slots give measurable finite
truncations increasing to the full potential weight.
-/

open MeasureTheory
open scoped ENNReal BigOperators

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching MeasureTheory

noncomputable def truncatedPotentialWeight
    {ι X : Type*} [LinearOrder ι] [LocallyFiniteOrder ι]
    [OrderBot ι] [NoMaxOrder ι] [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (n : ℕ) (ξ : Step ι X) : ENNReal :=
  ∑ i ∈ firstSlots ι n, realizedPotentialWeight φ θ ξ i

theorem truncatedPotentialWeight_measurable
    {ι X : Type*} [LinearOrder ι] [LocallyFiniteOrder ι]
    [OrderBot ι] [NoMaxOrder ι] [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (n : ℕ) :
    Measurable (truncatedPotentialWeight (ι := ι) φ θ n) := by
  classical
  unfold truncatedPotentialWeight
  exact Finset.measurable_sum (firstSlots ι n)
    (fun i _ => realizedPotentialWeight_measurable φ θ i)

theorem truncatedPotentialWeight_mono
    {ι X : Type*} [LinearOrder ι] [LocallyFiniteOrder ι]
    [OrderBot ι] [NoMaxOrder ι] [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) {n : ℕ} (ξ : Step ι X) :
    truncatedPotentialWeight φ θ n ξ ≤
      truncatedPotentialWeight φ θ (n + 1) ξ := by
  classical
  unfold truncatedPotentialWeight
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (firstSlots_mono (Nat.le_succ n)) (fun _ _ _ => bot_le)

theorem truncatedPotentialWeight_le_total
    {ι X : Type*} [LinearOrder ι] [LocallyFiniteOrder ι]
    [OrderBot ι] [NoMaxOrder ι] [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (n : ℕ) (ξ : Step ι X) :
    truncatedPotentialWeight φ θ n ξ ≤ totalPotentialWeight φ θ ξ := by
  unfold truncatedPotentialWeight totalPotentialWeight
  exact ENNReal.sum_le_tsum (firstSlots ι n)

theorem truncatedPotentialWeight_iSup
    {ι X : Type*} [LinearOrder ι] [LocallyFiniteOrder ι]
    [OrderBot ι] [NoMaxOrder ι] [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (ξ : Step ι X) :
    ⨆ n : ℕ, truncatedPotentialWeight φ θ n ξ =
      totalPotentialWeight φ θ ξ := by
  unfold truncatedPotentialWeight totalPotentialWeight
  rw [ENNReal.tsum_eq_iSup_sum'
    (fun n : ℕ => firstSlots ι n) exists_subset_firstSlots]

/-- The previous real-valued boundary weight is the specialization
`X = ℝ`, `φ = id`, and `θ = -1`. -/
noncomputable def truncatedChildWeight (n : ℕ) (ξ : Step ℕ ℝ) : ENNReal :=
  truncatedPotentialWeight realPotential (-1) n ξ

@[simp] theorem truncatedChildWeight_eq_potential (n : ℕ)
    (ξ : Step ℕ ℝ) :
    truncatedChildWeight n ξ =
      truncatedPotentialWeight realPotential (-1) n ξ := rfl

theorem truncatedChildWeight_measurable (n : ℕ) :
    Measurable (truncatedChildWeight n) :=
  truncatedPotentialWeight_measurable realPotential (-1) n

theorem truncatedChildWeight_mono {n : ℕ} (ξ : Step ℕ ℝ) :
    truncatedChildWeight n ξ ≤ truncatedChildWeight (n + 1) ξ :=
  truncatedPotentialWeight_mono realPotential (-1) ξ

theorem truncatedChildWeight_le_total (n : ℕ) (ξ : Step ℕ ℝ) :
    truncatedChildWeight n ξ ≤ totalChildWeight ξ := by
  simpa using truncatedPotentialWeight_le_total realPotential (-1) n ξ

theorem truncatedChildWeight_iSup (ξ : Step ℕ ℝ) :
    ⨆ n : ℕ, truncatedChildWeight n ξ = totalChildWeight ξ := by
  simpa using truncatedPotentialWeight_iSup realPotential (-1) ξ

end ProbabilityTheory.BranchingRandomWalk.Spine
