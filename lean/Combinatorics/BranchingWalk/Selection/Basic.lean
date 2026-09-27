import Mathlib.Data.Finset.Card
import Mathlib.Order.Bounds.Basic

/-!
# Selection mechanisms on finite candidate sets

A `Mechanism` is an abstract rule:
from a finite candidate set it returns a sub-collection of the candidates. The
rule itself is deterministic. Environment-dependent measurable rules belong to
the probability layer.

The abstract concept carries no capacity bound. A mechanism that keeps at most
`N` candidates is an `NSelection`, defined in `Selection/NSelection/Basic.lean`.
`PreservesLeast` and `PreservesGreatest` are the two
order properties that make the leftmost and rightmost rules work; they mention
only `select`, so they belong to the abstract layer.
-/

open Classical

namespace Combinatorics

namespace Branching

namespace Selection

variable {ι : Type*}

/-- An abstract selection mechanism on `ι`: from every finite candidate set it
selects a sub-collection of the candidates. -/
structure Mechanism (ι : Type*) where
  /-- The selected sub-collection of a candidate set. -/
  select : Finset ι → Finset ι
  /-- Selection keeps only candidates that were already survive. -/
  subset : ∀ s, select s ⊆ s

namespace Mechanism

instance (ι : Type*) : CoeFun (Mechanism ι) (fun _ => Finset ι → Finset ι) :=
  ⟨Mechanism.select⟩

variable {M M' : Mechanism ι}

@[ext] theorem ext (h : ∀ s, M.select s = M'.select s) : M = M' := by
  have hsel : M.select = M'.select := funext h
  obtain ⟨sel, sub⟩ := M
  obtain ⟨sel', sub'⟩ := M'
  simp only at hsel
  cases hsel
  rw [Subsingleton.elim sub sub']

theorem select_subset (M : Mechanism ι) (s : Finset ι) :
    M.select s ⊆ s :=
  M.subset s

@[simp] theorem select_mem (M : Mechanism ι) {s : Finset ι} {q : ι}
    (h : q ∈ M.select s) : q ∈ s :=
  M.subset s h

/-- A mechanism preserves the least candidate of every candidate set. The
leftmost-`N` rule has this property, and it is exactly what lets the leftmost
particle survive the selection. -/
def PreservesLeast [LE ι] (M : Mechanism ι) : Prop :=
  ∀ ⦃s : Finset ι⦄ ⦃x : ι⦄, IsLeast (↑s : Set ι) x → x ∈ M.select s

/-- The order-dual property: a mechanism preserves the greatest candidate of
every candidate set. The rightmost-`N` rule has this property. -/
def PreservesGreatest [LE ι] (M : Mechanism ι) : Prop :=
  ∀ ⦃s : Finset ι⦄ ⦃x : ι⦄, IsGreatest (↑s : Set ι) x → x ∈ M.select s

/-- Transport a selection mechanism to the reversed order. The candidate sets
are transported by `OrderDual.ofDual`, selected there, and transported back. -/
noncomputable def mapOrderDual [DecidableEq ι] (M : Mechanism ι) :
    Mechanism (OrderDual ι) where
  select s := (M.select (s.image OrderDual.ofDual)).image OrderDual.toDual
  subset s := by
    intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    obtain ⟨r, hr, hrp⟩ := Finset.mem_image.mp (M.subset _ hp)
    rw [← hrp]
    simpa using hr

@[simp] theorem mapOrderDual_select [DecidableEq ι] (M : Mechanism ι)
    (s : Finset (OrderDual ι)) :
    (M.mapOrderDual).select s =
      (M.select (s.image OrderDual.ofDual)).image OrderDual.toDual :=
  rfl

end Mechanism

end Selection

end Branching

end Combinatorics
