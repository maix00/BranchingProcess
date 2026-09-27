import Combinatorics.BranchingWalk.Selection.Basic
import Mathlib.Data.Set.Card

/-!
# Selection mechanisms of capacity `N`

`NSelection ι N` is the general capacity selection on arbitrary candidate
sets. `FiniteNSelection ι N` is its finite-input algorithmic interface. Both
keep all candidates below capacity and exactly `N` candidates at or above
capacity.

Reversing the order on candidates transports an `NSelection` to an `NSelection`
of the same capacity, because the transport is a bijection on candidate sets.
The leftmost rule of capacity `N` is `NSelection.leftmost`; the rightmost rule is
its transport, `NSelection.rightmost`.
-/

open Classical

namespace Combinatorics

namespace Branching

namespace Selection

variable {ι : Type*} {N : ℕ}

/-- A capacity-`N` selection on an arbitrary candidate population.  Its input
may be finite, countably infinite, or uncountable.  The retained population is
finite: below capacity every candidate is retained, and otherwise exactly
`N` candidates are retained. -/
structure NSelection (ι : Type*) (N : ℕ) where
  select : Set ι → Finset ι
  subset : ∀ s q, q ∈ select s → q ∈ s
  card_finite : ∀ s, ∀ h : s.Finite,
    (select s).card = min N h.toFinset.card
  card_infinite : ∀ s, s.Infinite → (select s).card = N

namespace NSelection

instance (ι : Type*) (N : ℕ) :
    CoeFun (NSelection ι N) (fun _ => Set ι → Finset ι) :=
  ⟨NSelection.select⟩

/-- Forget the capacity law. -/
def toMechanism (M : NSelection ι N) : Mechanism ι where
  select s := ↑(M.select s)
  subset s := M.subset s

theorem select_card_le_set (M : NSelection ι N) (s : Set ι) :
    (M.select s).card ≤ N := by
  rcases s.finite_or_infinite with h | h
  · rw [M.card_finite s h]
    exact min_le_left _ _
  · rw [M.card_infinite s h]

@[simp] theorem select_mem_set (M : NSelection ι N) {s : Set ι} {q : ι}
    (hq : q ∈ M.select s) : q ∈ s :=
  M.subset s q hq

end NSelection

/-- A selection mechanism of capacity `N`: it retains the whole candidate set
below capacity and exactly `N` candidates at or above capacity. -/
structure FiniteNSelection (ι : Type*) (N : ℕ) extends FiniteMechanism ι where
  /-- Exact cardinality of the selected population. -/
  card_eq : ∀ s, (select s).card = min N s.card

namespace NSelection

/-- Restrict a general capacity selection to finite inputs. -/
noncomputable def toFiniteNSelection (M : NSelection ι N) :
    FiniteNSelection ι N where
  toFiniteMechanism := FiniteMechanism.ofMechanism M.toMechanism
  card_eq s := by
    have hselect :
        (FiniteMechanism.ofMechanism M.toMechanism).select s =
          M.select (↑s : Set ι) := by
      apply Finset.coe_injective
      exact FiniteMechanism.coe_select_ofMechanism M.toMechanism s
    rw [hselect, M.card_finite (↑s : Set ι) s.finite_toSet]
    rw [show s.finite_toSet.toFinset = s from
      Finset.coe_injective s.finite_toSet.coe_toFinset]

/-- The rank of `q` among the candidates `s`: the number of candidates that
strictly precede it. -/
noncomputable def rank [LinearOrder ι] (s : Finset ι) (q : ι) : ℕ :=
  (s.filter fun p => p < q).card

theorem rank_def [LinearOrder ι] (s : Finset ι) (q : ι) :
    rank s q = (s.filter fun p => p < q).card :=
  rfl

/-- Keep the `N` smallest candidates. -/
noncomputable def selectFirstN [LinearOrder ι] (N : ℕ) (s : Finset ι) : Finset ι :=
  s.filter fun q => rank s q < N

theorem selectFirstN_def [LinearOrder ι] (N : ℕ) (s : Finset ι) :
    selectFirstN N s = s.filter fun q => rank s q < N :=
  rfl

@[simp] theorem mem_selectFirstN_iff [LinearOrder ι]
    {N : ℕ} {s : Finset ι} {q : ι} :
    q ∈ selectFirstN N s ↔ q ∈ s ∧ rank s q < N :=
  Finset.mem_filter

theorem selectFirstN_subset [LinearOrder ι] (N : ℕ) (s : Finset ι) :
    selectFirstN N s ⊆ s := by
  intro q hq
  exact (Finset.mem_filter.mp hq).1

/-- Keep the `N` greatest candidates. -/
noncomputable def selectLastN [LinearOrder ι] (N : ℕ) (s : Finset ι) : Finset ι :=
  s.filter fun q => (s.filter fun p => q < p).card < N

theorem selectLastN_def [LinearOrder ι] (N : ℕ) (s : Finset ι) :
    selectLastN N s = s.filter fun q => (s.filter fun p => q < p).card < N :=
  rfl

@[simp] theorem mem_selectLastN_iff [LinearOrder ι]
    {N : ℕ} {s : Finset ι} {q : ι} :
    q ∈ selectLastN N s ↔ q ∈ s ∧ (s.filter fun p => q < p).card < N :=
  Finset.mem_filter

theorem selectLastN_subset [LinearOrder ι] (N : ℕ) (s : Finset ι) :
    selectLastN N s ⊆ s := by
  intro q hq
  exact (Finset.mem_filter.mp hq).1

instance (ι : Type*) (N : ℕ) :
    CoeFun (FiniteNSelection ι N) (fun _ => Finset ι → Finset ι) :=
  ⟨fun M => M.select⟩

variable {M M' : FiniteNSelection ι N}

@[ext] theorem ext (h : ∀ s, M.select s = M'.select s) : M = M' := by
  have hsel : M.select = M'.select := funext h
  obtain ⟨sm, card⟩ := M
  obtain ⟨sm', card'⟩ := M'
  obtain ⟨sel, sub⟩ := sm
  obtain ⟨sel', sub'⟩ := sm'
  simp only at hsel
  cases hsel
  rw [Subsingleton.elim sub sub', Subsingleton.elim card card']

/-- The exact-cardinality law implies the capacity bound. -/
theorem select_card_le (M : FiniteNSelection ι N) (s : Finset ι) :
    (M.select s).card ≤ N :=
  (M.card_eq s).le.trans (min_le_left _ _)

@[simp] theorem select_card (M : FiniteNSelection ι N) (s : Finset ι) :
    (M.select s).card = min N s.card :=
  M.card_eq s

theorem select_card_eq_of_card_le (M : FiniteNSelection ι N) (s : Finset ι)
    (h : s.card ≤ N) : (M.select s).card = s.card := by
  rw [M.card_eq, min_eq_right h]

theorem select_card_eq_of_le_card (M : FiniteNSelection ι N) (s : Finset ι)
    (h : N ≤ s.card) : (M.select s).card = N := by
  rw [M.card_eq, min_eq_left h]

/-- Below capacity an `NSelection` keeps every candidate, not merely the same
number of candidates. -/
theorem select_eq_self_of_card_le (M : FiniteNSelection ι N) (s : Finset ι)
    (h : s.card ≤ N) : M.select s = s := by
  exact Finset.eq_of_subset_of_card_le (M.subset s)
    (by rw [select_card_eq_of_card_le M s h])

@[simp] theorem select_mem (M : FiniteNSelection ι N) {s : Finset ι} {q : ι}
    (h : q ∈ M.select s) : q ∈ s :=
  M.subset s h

/-- The capacity of a selection is preserved by reversing the order on
candidates. -/
noncomputable def mapOrderDual [DecidableEq ι] (M : FiniteNSelection ι N) :
    FiniteNSelection (OrderDual ι) N where
  toFiniteMechanism := M.toFiniteMechanism.mapOrderDual
  card_eq s := by
    rw [FiniteMechanism.mapOrderDual_select,
      Finset.card_image_of_injective _ OrderDual.toDual.injective,
      M.card_eq,
      Finset.card_image_of_injective _ OrderDual.ofDual.injective]

@[simp] theorem mapOrderDual_select [DecidableEq ι] (M : FiniteNSelection ι N)
    (s : Finset (OrderDual ι)) :
    (NSelection.mapOrderDual M).select s =
      (M.select (s.image OrderDual.ofDual)).image OrderDual.toDual :=
  rfl

/-- The underlying abstract mechanism of the transported selection is the
transport of the underlying abstract mechanism. -/
@[simp] theorem toFiniteMechanism_mapOrderDual [DecidableEq ι] (M : FiniteNSelection ι N) :
    (NSelection.mapOrderDual M).toFiniteMechanism =
      M.toFiniteMechanism.mapOrderDual :=
  rfl

end NSelection end Selection

end Branching

end Combinatorics
