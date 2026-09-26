import MeasureTheory.UlamHarris.MarkedTree.Basic

/-!
# Root-indexed marked Ulam--Harris trees

`RootIndexedMarkedTree Root α X` is one marked tree for each initial ancestor.
It is the multi-root marked object of the paper: the roots stay separate, as in
`RootIndexedTree`, and each tree carries marks on its own realized nodes.

The marks are exposed through the same partial and `Option`-valued views as for
a single marked tree. No additive structure on `X` is assumed here; displaced
positions belong to the branching-walk layer.
-/

namespace MeasureTheory

namespace UlamHarris

/-- One marked Ulam--Harris tree for each initial ancestor. -/
abbrev RootIndexedMarkedTree (Root α X : Type*) [LT α] :=
  Root → MarkedTree α X

namespace RootIndexedMarkedTree

variable {Root NewRoot α X : Type*} [LT α]

/-- The realized tree of the initial ancestor `r`. -/
def tree (M : RootIndexedMarkedTree Root α X) (r : Root) : UlamHarris.Tree α :=
  (M r).tree

/-- The partial mark of the initial ancestor `r`. -/
def partialMark (M : RootIndexedMarkedTree Root α X) (r : Root) :
    (List α) →. X :=
  (M r).partialMark

/-- The `Option`-valued mark of the initial ancestor `r`. -/
noncomputable def mark? (M : RootIndexedMarkedTree Root α X) (r : Root) :
    List α → Option X :=
  (M r).mark?

@[simp]
theorem tree_apply (M : RootIndexedMarkedTree Root α X) (r : Root) :
    M.tree r = (M r).tree := rfl

@[simp]
theorem partialMark_apply (M : RootIndexedMarkedTree Root α X) (r : Root) :
    M.partialMark r = (M r).partialMark := rfl

@[simp]
theorem mark?_apply (M : RootIndexedMarkedTree Root α X) (r : Root) :
    M.mark? r = (M r).mark? := rfl

/-- The root mark of the initial ancestor `r`. -/
def rootMark (M : RootIndexedMarkedTree Root α X) (r : Root) : X :=
  (M r).rootMark

/-- Two root-indexed marked trees are equal as soon as they agree at every
initial ancestor. -/
@[ext]
theorem ext {M N : RootIndexedMarkedTree Root α X}
    (h : ∀ r, M r = N r) : M = N :=
  funext h

/-- Reindexing the initial ancestors along a map of index types. -/
def reindex (f : NewRoot → Root) (M : RootIndexedMarkedTree Root α X) :
    RootIndexedMarkedTree NewRoot α X :=
  fun r => M (f r)

@[simp]
theorem reindex_apply (f : NewRoot → Root)
    (M : RootIndexedMarkedTree Root α X) (r : NewRoot) :
    M.reindex f r = M (f r) := rfl

@[simp]
theorem reindex_id (M : RootIndexedMarkedTree Root α X) :
    M.reindex id = M := rfl

theorem reindex_comp (f : NewRoot → Root) {NewerRoot : Type*}
    (g : NewerRoot → NewRoot) (M : RootIndexedMarkedTree Root α X) :
    (M.reindex f).reindex g = M.reindex (f ∘ g) := rfl

/-- Root-indexed marked trees over finitely many initial ancestors. -/
abbrev FiniteRootMarkedTree (m : ℕ) (α X : Type*) [LT α] :=
  RootIndexedMarkedTree (Fin m) α X

/-- Root-indexed marked trees over countably many initial ancestors. -/
abbrev CountableRootMarkedTree (α X : Type*) [LT α] :=
  RootIndexedMarkedTree ℕ α X

theorem finiteRootMarkedTree_ext {m : ℕ} {M N : FiniteRootMarkedTree m α X}
    (h : ∀ r, M r = N r) : M = N :=
  ext h

end RootIndexedMarkedTree

end UlamHarris

end MeasureTheory
