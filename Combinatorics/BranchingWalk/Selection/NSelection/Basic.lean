import Combinatorics.BranchingWalk.Selection.Basic

/-!
# Selection mechanisms of capacity `N`

`NSelection ι N` is an abstract selection mechanism on `ι` that keeps exactly
`min N s.card` candidates from every finite candidate set `s`. Thus it keeps
all candidates when fewer than `N` are available and exactly `N` otherwise.

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

/-- A selection mechanism of capacity `N`: it retains the whole candidate set
below capacity and exactly `N` candidates at or above capacity. -/
structure NSelection (ι : Type*) (N : ℕ) extends Mechanism ι where
  /-- Exact cardinality of the selected population. -/
  card_eq : ∀ s, (select s).card = min N s.card

namespace NSelection

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
    CoeFun (NSelection ι N) (fun _ => Finset ι → Finset ι) :=
  ⟨fun M => M.select⟩

variable {M M' : NSelection ι N}

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
theorem select_card_le (M : NSelection ι N) (s : Finset ι) :
    (M.select s).card ≤ N :=
  (M.card_eq s).le.trans (min_le_left _ _)

@[simp] theorem select_card (M : NSelection ι N) (s : Finset ι) :
    (M.select s).card = min N s.card :=
  M.card_eq s

theorem select_card_eq_of_card_le (M : NSelection ι N) (s : Finset ι)
    (h : s.card ≤ N) : (M.select s).card = s.card := by
  rw [M.card_eq, min_eq_right h]

theorem select_card_eq_of_le_card (M : NSelection ι N) (s : Finset ι)
    (h : N ≤ s.card) : (M.select s).card = N := by
  rw [M.card_eq, min_eq_left h]

/-- Below capacity an `NSelection` keeps every candidate, not merely the same
number of candidates. -/
theorem select_eq_self_of_card_le (M : NSelection ι N) (s : Finset ι)
    (h : s.card ≤ N) : M.select s = s := by
  exact Finset.eq_of_subset_of_card_le (M.subset s)
    (by rw [M.select_card_eq_of_card_le s h])

@[simp] theorem select_mem (M : NSelection ι N) {s : Finset ι} {q : ι}
    (h : q ∈ M.select s) : q ∈ s :=
  M.subset s h

/-- The capacity of a selection is preserved by reversing the order on
candidates. -/
noncomputable def mapOrderDual [DecidableEq ι] (M : NSelection ι N) :
    NSelection (OrderDual ι) N where
  toMechanism := M.toMechanism.mapOrderDual
  card_eq s := by
    rw [Mechanism.mapOrderDual_select,
      Finset.card_image_of_injective _ OrderDual.toDual.injective,
      M.card_eq,
      Finset.card_image_of_injective _ OrderDual.ofDual.injective]

@[simp] theorem mapOrderDual_select [DecidableEq ι] (M : NSelection ι N)
    (s : Finset (OrderDual ι)) :
    (M.mapOrderDual).select s =
      (M.select (s.image OrderDual.ofDual)).image OrderDual.toDual :=
  rfl

/-- The underlying abstract mechanism of the transported selection is the
transport of the underlying abstract mechanism. -/
@[simp] theorem toMechanism_mapOrderDual [DecidableEq ι] (M : NSelection ι N) :
    M.mapOrderDual.toMechanism = M.toMechanism.mapOrderDual :=
  rfl

end NSelection

end Selection

end Branching

end Combinatorics
