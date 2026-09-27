import Probability.BranchingRandomWalk.PointProcess.Enumeration.Recursive
import Combinatorics.BranchingWalk.Step.Measurability
import Combinatorics.BranchingWalk.Step.Basic

/-!
# Coverage of the measurable child-slot enumeration

Finite exponential weight implies every displacement sublevel has only
finitely many realized children. Hence a realized raw slot cannot be
postponed forever by the successive leftmost selection.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory



/-- Every realized raw child occurs at a finite rank of the ordered
enumeration, provided the total exponential weight is finite. -/
theorem enumeratedSlot_covers_realized (ξ : Step ℕ ℝ)
    (hsum : totalChildWeight ξ ≠ ∞) (i : ℕ)
    (hi : survive ξ i) :
    ∃ n : ℕ, enumeratedSlot ξ n = some i := by
  classical
  by_contra hnever
  have hnever' : ∀ n, enumeratedSlot ξ n ≠ some i := by
    simpa only [not_exists] using hnever
  let s : Finset ℕ :=
    ((finite_realized_children_below ξ hsum
      (value' ξ i)).toFinset)
  have hs : ∀ j : ℕ, j ∈ s ↔
      survive ξ j ∧
        value' ξ j ≤ value' ξ i := by
    intro j
    simp [s]
  have hbound : ∀ n : ℕ,
      i ∉ enumeratedSlots n ξ ∧
      enumeratedSlots n ξ ⊆ s ∧
      (enumeratedSlots n ξ).card = n := by
    intro n
    induction n with
    | zero => simp [enumeratedSlots]
    | succ n ih =>
        have havailable : ∃ j, survive ξ j ∧
            j ∉ enumeratedSlots n ξ := ⟨i, hi, ih.1⟩
        obtain ⟨j, hj⟩ :=
          nextAtomAt_exists_of_finite_sublevels ξ
            (enumeratedSlots n ξ)
            (finite_realized_children_below ξ hsum) havailable
        have hslot : enumeratedSlot ξ n = some j :=
          (nextAtomIndex_eq_some_iff ξ (enumeratedSlots n ξ) j).2 hj
        have hji : j ≠ i := by
          intro heq
          exact hnever' n (heq ▸ hslot)
        have hjmem : j ∈ s :=
          (hs j).2 ⟨hj.1, hj.2.2.1 i hi ih.1⟩
        rw [enumeratedSlots_succ_of_some ξ n j hslot]
        refine ⟨?_, ?_, ?_⟩
        · simp [ih.1, Ne.symm hji]
        · exact Finset.insert_subset hjmem ih.2.1
        · rw [Finset.card_insert_of_notMem hj.2.1, ih.2.2]
  have hcard := Finset.card_le_card (hbound (s.card + 1)).2.1
  rw [(hbound (s.card + 1)).2.2] at hcard
  omega

/-- The successive selector enumerates exactly the realized raw slots. -/
theorem realized_iff_enumerated (ξ : Step ℕ ℝ)
    (hsum : totalChildWeight ξ ≠ ∞) (i : ℕ) :
    survive ξ i ↔
      ∃ n : ℕ, enumeratedSlot ξ n = some i := by
  constructor
  · exact enumeratedSlot_covers_realized ξ hsum i
  · rintro ⟨n, hn⟩
    exact ((nextAtomIndex_eq_some_iff ξ
      (enumeratedSlots n ξ) i).1 hn).1

end ProbabilityTheory.BranchingRandomWalk
