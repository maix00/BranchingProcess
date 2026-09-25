import Mathlib.Data.PFun

/-!
# Deterministic Ulam--Harris trees and marked trees

`TreeNode α` is the abstract address type `List α` of a rooted tree whose
child labels live in `α`; it is not tied to `ℕ`. `Tree α` is a
deterministic rooted tree of such addresses, carrying the root, prefix, and
ordered-sibling axioms, so a bare `Set (List α)` is only its carrier.
`MarkedTree α X` pairs one realized tree with a mark on every realized node,
and `𝕍 = TreeNode ℕ` is the Ulam--Harris vertex set of the paper.

`Mark α M` is the mark function `TreeNode α → M`: it assigns a mark to
*every* address, including reserve branches the walk never visits, and the
generation filtration of `Probability/BranchingRandomWalk/Tree/Filtration.lean` is defined on it. This is a
separate object from a `MarkedTree`, which carries marks only on its realized
nodes; those marks are exposed here as the partial function `partialMark` and
the `Option`-valued accessor `mark?`.
-/

namespace MeasureTheory

namespace UlamHarris

/-- Addresses of a rooted tree whose child labels live in `α`. This is the
abstract word type; `TreeNode ℕ` is the Ulam--Harris instance. -/
abbrev TreeNode (α : Type*) := List α

/-- The Ulam--Harris vertex set `𝕍 = ⋃ₙ ℕⁿ` of the paper. -/
abbrev 𝕍 := TreeNode ℕ

/-- A rooted tree of addresses. The carrier contains the root, is prefix
closed, and for ordered child labels contains every smaller sibling below a
present child. `Set (List α)` is only the underlying carrier of this
structure. -/
structure Tree (α : Type*) [LT α] where
  carrier : Set (List α)
  root_mem : [] ∈ carrier
  prefix_closed : ∀ {u v : List α}, u ++ v ∈ carrier → u ∈ carrier
  sibling_closed : ∀ {u : List α} {i j : α},
    u ++ [j] ∈ carrier → i < j → u ++ [i] ∈ carrier

@[simp] theorem Tree.root_mem' {α : Type*} [LT α]
    (T : Tree α) :
    [] ∈ T.carrier := T.root_mem

theorem Tree.mem_prefix {α : Type*} [LT α] (T : Tree α)
    {u v : List α} (h : u ++ v ∈ T.carrier) : u ∈ T.carrier :=
  T.prefix_closed h

/-- A realized tree together with a mark on each of its realized nodes. This
is the object meant when one says "marked tree"; it is not the full address
field. -/
structure MarkedTree (α X : Type*) [LT α] where
  tree : Tree α
  mark : (u : List α) → u ∈ tree.carrier → X

namespace MarkedTree

variable {α X : Type*} [LT α]

/-- The mark at the root. -/
def rootMark (T : MarkedTree α X) : X := T.mark [] T.tree.root_mem

@[simp] theorem rootMark_eq (T : MarkedTree α X) :
    T.rootMark = T.mark [] T.tree.root_mem := rfl

end MarkedTree

/-- The mark function of the paper: a mark in `M` attached to every address
before any realized-tree restriction. The address type is arbitrary;
`Mark ℕ M` is the mark function on `𝕍`. The generation filtration is defined
directly on it, and a `MarkedTree` is what remains after keeping only the
realized nodes.

The name `Mark` is the object (a function on addresses), not a single mark:
a single mark is a term of the value type `M`. -/
abbrev Mark (α : Type*) (M : Type*) := TreeNode α → M

namespace MarkedTree

variable {α X : Type*} [LT α]

/-! The marks of a `MarkedTree` are defined only on the realized nodes, that
is, on a part of the address space. Mathlib represents a function whose domain
is only part of a type as a partial function `α →. β = α → Part β`
(`Mathlib/Data/PFun.lean`); accessors returning `Option` carry the `?` suffix
(`List.get?`). Both views are provided below, so no `?`-suffixed *type* is
needed. -/

/-- The marks of a marked tree as a partial function on addresses, defined
exactly on the realized nodes. -/
def partialMark (T : MarkedTree α X) : (TreeNode α) →. X :=
  fun u => ⟨u ∈ T.tree.carrier, fun h => T.mark u h⟩

/-- The domain of `partialMark` is the realized tree. -/
@[simp] theorem partialMark_dom (T : MarkedTree α X) :
    T.partialMark.Dom = T.tree.carrier := rfl

/-- Evaluating `partialMark` at a realized node returns the mark of that
node. -/
@[simp] theorem partialMark_asSubtype (T : MarkedTree α X) (u : TreeNode α)
    (h : u ∈ T.tree.carrier) : T.partialMark.asSubtype ⟨u, h⟩ = T.mark u h :=
  rfl

/-- The marks of a marked tree as an `Option`-valued function of addresses:
`some` on a realized node and `none` elsewhere. This is the `?` convention of
mathlib for partial accessors (`List.get?`); it is the `Option` view of
`partialMark`. -/
noncomputable def mark? (T : MarkedTree α X) : TreeNode α → Option X := by
  classical
  exact fun u => if h : u ∈ T.tree.carrier then some (T.mark u h) else none

@[simp] theorem mark?_apply_mem (T : MarkedTree α X) {u : TreeNode α}
    (h : u ∈ T.tree.carrier) : T.mark? u = some (T.mark u h) := by
  classical
  simp [mark?, h]

@[simp] theorem mark?_apply_notMem (T : MarkedTree α X) {u : TreeNode α}
    (h : u ∉ T.tree.carrier) : T.mark? u = none := by
  classical
  simp [mark?, h]

end MarkedTree

end UlamHarris

end MeasureTheory
