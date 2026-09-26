import Combinatorics.BranchingWalk.Selection.SelectMechanism

/-!
# Selection mechanisms of capacity `N`

`NSelection ι N` is an abstract selection mechanism on `ι` that keeps at most
`N` candidates out of every candidate set. It is the capacity condition of the
paper's `N`-branching walk: the walk keeps `N` particles per generation.

Reversing the order on candidates transports an `NSelection` to an `NSelection`
of the same capacity, because the transport is a bijection on candidate sets.
The leftmost rule of capacity `N` is `Selection.leftmost`; the rightmost rule is
its transport, `Selection.rightmost`.
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
