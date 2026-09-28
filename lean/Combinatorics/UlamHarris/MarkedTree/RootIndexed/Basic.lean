import Combinatorics.UlamHarris.MarkedTree.Basic

/-!
# Root-indexed marked Ulam--Harris trees

`RootIndexed.MarkedTree Root α X` is one marked tree for each initial ancestor.
It is a multi-root marked object: the roots stay separate, as in
`RootIndexed.Tree`, and each tree carries marks on its own realized nodes.

The marks are exposed through the same partial and `Option`-valued views as for
a single marked tree. No additive structure on `X` is assumed here; displaced
positions belong to the branching-walk layer.
-/

namespace Combinatorics

namespace UlamHarris

namespace RootIndexed

/-- One marked Ulam--Harris tree for each initial ancestor. -/
abbrev MarkedTree (Root α X : Type*) [LT α] :=
  Root → UlamHarris.MarkedTree α X

namespace MarkedTree

variable {Root NewRoot α X : Type*} [LT α]

/-- The realized tree of the initial ancestor `r`. -/
def tree (M : RootIndexed.MarkedTree Root α X) (r : Root) : UlamHarris.Tree α :=
  (M r).tree

/-- The partial mark of the initial ancestor `r`. -/
def partialMark (M : RootIndexed.MarkedTree Root α X) (r : Root) :
    (List α) →. X :=
  (M r).partialMark

/-- The `Option`-valued mark of the initial ancestor `r`. -/
noncomputable def mark? (M : RootIndexed.MarkedTree Root α X) (r : Root) :
    List α → Option X :=
  (M r).mark?

@[simp]
theorem tree_apply (M : RootIndexed.MarkedTree Root α X) (r : Root) :
    M.tree r = (M r).tree := rfl

@[simp]
theorem partialMark_apply (M : RootIndexed.MarkedTree Root α X) (r : Root) :
    M.partialMark r = (M r).partialMark := rfl

@[simp]
theorem mark?_apply (M : RootIndexed.MarkedTree Root α X) (r : Root) :
    M.mark? r = (M r).mark? := rfl

/-- The root mark of the initial ancestor `r`. -/
def rootMark (M : RootIndexed.MarkedTree Root α X) (r : Root) : X :=
  (M r).rootMark

/-- Two root-indexed marked trees are equal as soon as they agree at every
initial ancestor. -/
@[ext]
theorem ext {M N : RootIndexed.MarkedTree Root α X}
    (h : ∀ r, M r = N r) : M = N :=
  funext h

/-- Reindexing the initial ancestors along a map of index types. -/
def reindex (f : NewRoot → Root) (M : RootIndexed.MarkedTree Root α X) :
    RootIndexed.MarkedTree NewRoot α X :=
  fun r => M (f r)

@[simp]
theorem reindex_apply (f : NewRoot → Root)
    (M : RootIndexed.MarkedTree Root α X) (r : NewRoot) :
    M.reindex f r = M (f r) := rfl

@[simp]
theorem reindex_id (M : RootIndexed.MarkedTree Root α X) :
    M.reindex id = M := rfl

theorem reindex_comp (f : NewRoot → Root) {NewerRoot : Type*}
    (g : NewerRoot → NewRoot) (M : RootIndexed.MarkedTree Root α X) :
    (M.reindex f).reindex g = M.reindex (f ∘ g) := rfl

/-- Root-indexed marked trees over countably many initial ancestors. -/
abbrev CountableRootMarkedTree (α X : Type*) [LT α] :=
  RootIndexed.MarkedTree ℕ α X

end MarkedTree

end RootIndexed

end UlamHarris

end Combinatorics
