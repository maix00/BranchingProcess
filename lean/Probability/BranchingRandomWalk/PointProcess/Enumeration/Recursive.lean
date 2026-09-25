import Probability.BranchingRandomWalk.PointProcess.Enumeration.NextAtom

/-!
# Recursive measurable enumeration of child slots

The `n`th output is an optional raw slot index. A finite point process
eventually returns `none`; an infinite one can keep producing indices. The
prefix stores exactly the raw slots already chosen, so this construction
does not impose binary branching or a fixed child count.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk

open UlamHarris BranchingStep MeasureTheory



/-- Add a selected slot to the used set; `none` leaves it unchanged. -/
def addEnumeratedSlot (p : Finset ℕ × Option ℕ) : Finset ℕ :=
  match p.2 with
  | none => p.1
  | some i => insert i p.1

theorem addEnumeratedSlot_measurable :
    Measurable addEnumeratedSlot :=
  measurable_of_countable addEnumeratedSlot

/-- Raw indices used before choosing the child at ordered rank `n`. -/
noncomputable def enumeratedSlots :
    ℕ → NatRealBranchingStep → Finset ℕ
  | 0, _ => ∅
  | n + 1, ξ =>
      addEnumeratedSlot
        (enumeratedSlots n ξ,
          nextAtomIndex (enumeratedSlots n ξ) ξ)

theorem enumeratedSlots_measurable :
    ∀ n, Measurable (enumeratedSlots n) := by
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      have hnext : Measurable
          (fun ξ : NatRealBranchingStep =>
            nextAtomIndex (enumeratedSlots n ξ) ξ) :=
        nextAtomIndex_joint_measurable.comp
          (ih.prodMk measurable_id)
      exact addEnumeratedSlot_measurable.comp (ih.prodMk hnext)

/-- The raw slot index of the child at ordered rank `n`, or `none` after
the last child of a finite branching-step point process. -/
noncomputable def enumeratedSlot (ξ : NatRealBranchingStep)
    (n : ℕ) : Option ℕ :=
  nextAtomIndex (enumeratedSlots n ξ) ξ

theorem enumeratedSlot_measurable (n : ℕ) :
    Measurable (fun ξ : NatRealBranchingStep => enumeratedSlot ξ n) :=
  nextAtomIndex_joint_measurable.comp
    ((enumeratedSlots_measurable n).prodMk measurable_id)

theorem enumeratedSlot_some_not_used (ξ : NatRealBranchingStep)
    (n i : ℕ) (h : enumeratedSlot ξ n = some i) :
    i ∉ enumeratedSlots n ξ :=
  (nextAtomIndex_eq_some_iff ξ (enumeratedSlots n ξ) i).1 h |>.2.1

theorem enumeratedSlots_succ_of_some (ξ : NatRealBranchingStep)
    (n i : ℕ) (h : enumeratedSlot ξ n = some i) :
    enumeratedSlots (n + 1) ξ =
      insert i (enumeratedSlots n ξ) := by
  simp [enumeratedSlots, enumeratedSlot] at *
  rw [h]
  rfl

theorem enumeratedSlots_succ_of_none (ξ : NatRealBranchingStep)
    (n : ℕ) (h : enumeratedSlot ξ n = none) :
    enumeratedSlots (n + 1) ξ = enumeratedSlots n ξ := by
  simp [enumeratedSlots, enumeratedSlot] at *
  rw [h]
  rfl

theorem enumeratedSlots_step_subset (ξ : NatRealBranchingStep) (n : ℕ) :
    enumeratedSlots n ξ ⊆ enumeratedSlots (n + 1) ξ := by
  change enumeratedSlots n ξ ⊆
    addEnumeratedSlot
      (enumeratedSlots n ξ, nextAtomIndex (enumeratedSlots n ξ) ξ)
  cases h : nextAtomIndex (enumeratedSlots n ξ) ξ with
  | none => simp [addEnumeratedSlot]
  | some i => simp [addEnumeratedSlot]

theorem enumeratedSlots_mono (ξ : NatRealBranchingStep) :
    Monotone (fun n => enumeratedSlots n ξ) :=
  monotone_nat_of_le_succ (enumeratedSlots_step_subset ξ)

/-- A raw child slot is never enumerated twice. -/
theorem enumeratedSlot_injective_on_some (ξ : NatRealBranchingStep)
    {n k i : ℕ} (hn : enumeratedSlot ξ n = some i)
    (hk : enumeratedSlot ξ k = some i) : n = k := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hnk | hkn
  · have hmem : i ∈ enumeratedSlots (n + 1) ξ := by
      rw [enumeratedSlots_succ_of_some ξ n i hn]
      simp
    have hmemk : i ∈ enumeratedSlots k ξ :=
      (enumeratedSlots_mono ξ (Nat.succ_le_of_lt hnk)) hmem
    exact (enumeratedSlot_some_not_used ξ k i hk) hmemk
  · have hmem : i ∈ enumeratedSlots (k + 1) ξ := by
      rw [enumeratedSlots_succ_of_some ξ k i hk]
      simp
    have hmemn : i ∈ enumeratedSlots n ξ :=
      (enumeratedSlots_mono ξ (Nat.succ_le_of_lt hkn)) hmem
    exact (enumeratedSlot_some_not_used ξ n i hn) hmemn

/-- Once the enumeration terminates, later ranks also return `none`. -/
theorem enumeratedSlot_none_persists (ξ : NatRealBranchingStep)
    (n : ℕ) (hn : enumeratedSlot ξ n = none) :
    ∀ t : ℕ, enumeratedSlot ξ (n + t) = none := by
  intro t
  induction t with
  | zero => simpa using hn
  | succ t ih =>
      have hused := enumeratedSlots_succ_of_none ξ (n + t) ih
      simpa only [Nat.add_succ, enumeratedSlot, hused] using ih

/-- Consecutive selected children are ordered by displacement. -/
theorem enumeratedSlot_succ_displacement_le (ξ : NatRealBranchingStep)
    (n i j : ℕ) (hi : enumeratedSlot ξ n = some i)
    (hj : enumeratedSlot ξ (n + 1) = some j) :
    childDisplacement ξ i ≤ childDisplacement ξ j := by
  have hfirst :=
    (nextAtomIndex_eq_some_iff ξ (enumeratedSlots n ξ) i).1 hi
  have hnext :=
    (nextAtomIndex_eq_some_iff ξ (enumeratedSlots (n + 1) ξ) j).1 hj
  have hnot : j ∉ enumeratedSlots n ξ := by
    intro hmem
    apply hnext.2.1
    exact (enumeratedSlots_step_subset ξ n) hmem
  exact hfirst.2.2.1 j hnext.1 hnot

/-- Rank zero is the previously constructed measurable first-atom selector
whenever the exponential total weight is finite. -/
theorem enumeratedSlot_zero_of_finite_weight
    (ξ : NatRealBranchingStep) (hsum : totalChildWeight ξ ≠ ∞)
    (hnonempty : ∃ i, ξ ∈ childRealized i) :
    enumeratedSlot ξ 0 = some (firstAtomIndex ξ) := by
  apply (nextAtomIndex_eq_some_iff ξ (enumeratedSlots 0 ξ)
    (firstAtomIndex ξ)).2
  have hfirst := firstAtomIndex_spec_of_finite_weight ξ hsum hnonempty
  simpa [nextAtomAt, firstAtomAt, enumeratedSlots] using hfirst

end ProbabilityTheory.BranchingRandomWalk
