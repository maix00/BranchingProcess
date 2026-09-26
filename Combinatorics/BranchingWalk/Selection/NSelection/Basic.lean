import Combinatorics.BranchingWalk.Selection.SelectMechanism

/-!
# Selection mechanisms of capacity `N`

`NSelection ι N` is an abstract selection mechanism on `ι` that keeps at most
`N` candidates out of every candidate set. It is the capacity condition of the
paper's `N`-branching walk: the walk keeps `N` particles per generation.

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

/-- A selection mechanism of capacity `N`: an abstract selection mechanism that
selects a sub-collection of at most `N` candidates. -/
structure NSelection (ι : Type*) (N : ℕ) extends SelectMechanism ι where
  /-- The capacity bound. -/
  card_le : ∀ s, (select s).card ≤ N

namespace NSelection

/-- The rank of `q` among the candidates `s`: the number of candidates that
strictly precede it. -/
noncomputable def rank [LinearOrder ι] (s : Finset ι) (q : ι) : ℕ :=
  (s.filter fun p => p < q).card

theorem rank_def [LinearOrder ι] (s : Finset ι) (q : ι) :
    rank s q = (s.filter fun p => p < q).card :=
  rfl

/-- Keep the `N` smallest candidates. -/
noncomputable def keepFirst [LinearOrder ι] (N : ℕ) (s : Finset ι) : Finset ι :=
  s.filter fun q => rank s q < N

theorem keepFirst_def [LinearOrder ι] (N : ℕ) (s : Finset ι) :
    keepFirst N s = s.filter fun q => rank s q < N :=
  rfl

@[simp] theorem mem_keepFirst_iff [LinearOrder ι]
    {N : ℕ} {s : Finset ι} {q : ι} :
    q ∈ keepFirst N s ↔ q ∈ s ∧ rank s q < N :=
  Finset.mem_filter

theorem keepFirst_subset [LinearOrder ι] (N : ℕ) (s : Finset ι) :
    keepFirst N s ⊆ s := by
  intro q hq
  exact (Finset.mem_filter.mp hq).1

/-- Keep the `N` greatest candidates. -/
noncomputable def keepLast [LinearOrder ι] (N : ℕ) (s : Finset ι) : Finset ι :=
  s.filter fun q => (s.filter fun p => q < p).card < N

theorem keepLast_def [LinearOrder ι] (N : ℕ) (s : Finset ι) :
    keepLast N s = s.filter fun q => (s.filter fun p => q < p).card < N :=
  rfl

@[simp] theorem mem_keepLast_iff [LinearOrder ι]
    {N : ℕ} {s : Finset ι} {q : ι} :
    q ∈ keepLast N s ↔ q ∈ s ∧ (s.filter fun p => q < p).card < N :=
  Finset.mem_filter

theorem keepLast_subset [LinearOrder ι] (N : ℕ) (s : Finset ι) :
    keepLast N s ⊆ s := by
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

/-- The capacity bound of the mechanism. -/
theorem select_card_le (M : NSelection ι N) (s : Finset ι) :
    (M.select s).card ≤ N :=
  M.card_le s

@[simp] theorem select_mem (M : NSelection ι N) {s : Finset ι} {q : ι}
    (h : q ∈ M.select s) : q ∈ s :=
  M.subset s h

/-- The capacity of a selection is preserved by reversing the order on
candidates. -/
noncomputable def mapOrderDual [DecidableEq ι] (M : NSelection ι N) :
    NSelection (OrderDual ι) N where
  toSelectMechanism := M.toSelectMechanism.mapOrderDual
  card_le s := by
    rw [SelectMechanism.mapOrderDual_select,
      Finset.card_image_of_injective _ OrderDual.toDual.injective]
    exact M.card_le _

@[simp] theorem mapOrderDual_select [DecidableEq ι] (M : NSelection ι N)
    (s : Finset (OrderDual ι)) :
    (M.mapOrderDual).select s =
      (M.select (s.image OrderDual.ofDual)).image OrderDual.toDual :=
  rfl

/-- The underlying abstract mechanism of the transported selection is the
transport of the underlying abstract mechanism. -/
@[simp] theorem toSelectMechanism_mapOrderDual [DecidableEq ι] (M : NSelection ι N) :
    M.mapOrderDual.toSelectMechanism = M.toSelectMechanism.mapOrderDual :=
  rfl

end NSelection

end Selection

end Branching

end Combinatorics
