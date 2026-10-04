/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.UlamHarris.Tree.Defs
public import Mathlib.Data.PFun

/-!
# Marked Ulam--Harris trees

`MarkedTree α X` pairs a realized tree `Tree α` with a mark in `X` on every
realized node; it is the object meant when one says "marked tree". The marks
are defined only on a part of the address space, so they are exposed as the
partial function `partialMark : TreeNode α →. X` and the `Option`-valued
accessor `mark? : TreeNode α → Option X`. Neither view needs a `?`-suffixed
*type*: `?` names functions returning `Option`. The induced measurable space
and its coordinate measurability statements live in `Measurability.lean`.
-/

@[expose] public section

/-! The marks of a `MarkedTree` are defined only on the realized nodes, that
is, on a part of the address space. Mathlib extends a function whose domain
is only part of a type as a partial function `α →. β = α → Part β`
(`Mathlib/Data/PFun.lean`); accessors returning `Option` carry the `?` suffix
(`List.get?`). Both views are provided below. -/

namespace Combinatorics

namespace UlamHarris

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

/-- Two marked trees are equal as soon as their trees are equal and their marks
agree, the marks of the second being read along the tree equality. -/
@[ext (iff := false)]
theorem ext {M N : MarkedTree α X} (htree : M.tree = N.tree)
    (hmark : ∀ (u : List α) (hu : u ∈ M.tree.carrier),
      M.mark u hu = N.mark u (htree ▸ hu)) : M = N := by
  obtain ⟨T, m⟩ := M
  obtain ⟨T', m'⟩ := N
  have h : T = T' := htree
  subst h
  congr 1
  funext u hu
  simpa using hmark u hu

/-- The marks of a marked tree as a partial function on addresses, defined
exactly on the realized nodes. -/
def partialMark (T : MarkedTree α X) : (List α) →. X :=
  fun u => ⟨u ∈ T.tree.carrier, fun h => T.mark u h⟩

/-- The domain of `partialMark` is the realized tree. -/
@[simp] theorem partialMark_dom (T : MarkedTree α X) :
    T.partialMark.Dom = T.tree.carrier := rfl

/-- Evaluating `partialMark` at a realized node returns the mark of that
node. -/
@[simp] theorem partialMark_asSubtype (T : MarkedTree α X) (u : List α)
    (h : u ∈ T.tree.carrier) : T.partialMark.asSubtype ⟨u, h⟩ = T.mark u h :=
  rfl

/-- The marks of a marked tree as an `Option`-valued function of addresses:
`some` on a realized node and `none` elsewhere. This is the `?` convention of
mathlib for partial accessors (`List.get?`); it is the `Option` view of
`partialMark`. -/
noncomputable def mark? (T : MarkedTree α X) : List α → Option X := by
  classical
  exact fun u => if h : u ∈ T.tree.carrier then some (T.mark u h) else none

@[simp] theorem mark?_apply_mem (T : MarkedTree α X) {u : List α}
    (h : u ∈ T.tree.carrier) : T.mark? u = some (T.mark u h) := by
  classical
  simp [mark?, h]

@[simp] theorem mark?_apply_notMem (T : MarkedTree α X) {u : List α}
    (h : u ∉ T.tree.carrier) : T.mark? u = none := by
  classical
  simp [mark?, h]

end MarkedTree

namespace RootIndexed

/-! ### Families indexed by several initial ancestors

The multi-root object is an indexed family of the single-root object.  Keeping
this definition in the same module makes the relationship visible without a
parallel source tree.
-/

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

/-- The root mark of the tree belonging to the initial ancestor `r`. -/
def rootMark (M : RootIndexed.MarkedTree Root α X) (r : Root) : X :=
  (M r).rootMark

@[ext (iff := false)]
theorem ext {M N : RootIndexed.MarkedTree Root α X}
    (hmark : ∀ r, M r = N r) : M = N := by
  funext r
  exact hmark r

/-- Reindex a family of marked trees along a map of initial ancestors. -/
def reindex (f : NewRoot → Root) (M : RootIndexed.MarkedTree Root α X) :
    RootIndexed.MarkedTree NewRoot α X :=
  fun r => M (f r)

@[simp]
theorem reindex_apply (f : NewRoot → Root)
    (M : RootIndexed.MarkedTree Root α X) (r : NewRoot) :
    M.reindex f r = M (f r) := rfl

@[simp]
theorem reindex_id (M : RootIndexed.MarkedTree Root α X) : M.reindex id = M := rfl

@[simp]
theorem reindex_comp (f : NewRoot → Root) {NewerRoot : Type*}
    (g : NewerRoot → NewRoot) (M : RootIndexed.MarkedTree Root α X) :
    (M.reindex f).reindex g = M.reindex (f ∘ g) := rfl

end MarkedTree

end RootIndexed

end UlamHarris

end Combinatorics

end
