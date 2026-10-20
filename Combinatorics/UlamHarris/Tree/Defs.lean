/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.UlamHarris.Basic

/-!
# Deterministic Ulam--Harris trees

`Tree α` is a deterministic rooted tree of addresses `TreeNode α`. Its carrier
contains the root, is parent closed, and is closed under smaller sibling
labels. The structure is not assumed to be finite, countable, or locally
finite. This file contains only the deterministic tree and root-indexed tree
definitions; their measurable spaces live in
`Combinatorics.UlamHarris.Tree.Topology.MeasurableSpace`.

The public declarations are:

* `Combinatorics.UlamHarris.Tree`: a carrier `C : Set (List α)` with `[] ∈ C`,
  `u ++ v ∈ C → u ∈ C`, and
  `u ++ [j] ∈ C → i < j → u ++ [i] ∈ C`.
* `Combinatorics.UlamHarris.Tree.ext`:
  `T.carrier = T'.carrier → T = T'`.
* `Combinatorics.UlamHarris.Tree.mem_parent` states
  `u ++ v ∈ T.carrier → u ∈ T.carrier`.
* `Combinatorics.UlamHarris.RootIndexed.Tree Root α`: the family type
  `Root → Tree α`; each coordinate carries the root, parent-closure, and
  sibling-closure properties of `Combinatorics.UlamHarris.Tree`.
-/

@[expose] public section

/-! ### Families indexed by several initial ancestors

The root-indexed tree is an indexed family of ordinary trees. Its type alias
lives beside the single-root definition; properties are read coordinatewise
from each tree.
-/

namespace Combinatorics

namespace UlamHarris

/-- A rooted tree of addresses. The carrier contains the root, is parent
closed, and for ordered child labels contains every smaller sibling below a
survive child. `Set (List α)` is only the underlying carrier of this
structure. -/
structure Tree (α : Type*) [LT α] where
  carrier : Set (List α)
  root_mem : [] ∈ carrier
  parent_closed : ∀ {u v : List α}, u ++ v ∈ carrier → u ∈ carrier
  sibling_closed : ∀ {u : List α} {i j : α},
    u ++ [j] ∈ carrier → i < j → u ++ [i] ∈ carrier

/-- Two trees are equal as soon as their carriers are equal: the remaining
fields of `Tree` are propositions and hence proof irrelevant. -/
@[ext]
theorem Tree.ext {α : Type*} [LT α] {T T' : Tree α}
    (h : T.carrier = T'.carrier) : T = T' := by
  cases T
  cases T'
  simp only at h
  cases h
  rfl

theorem Tree.mem_parent {α : Type*} [LT α] (T : Tree α)
    {u v : List α} (h : u ++ v ∈ T.carrier) : u ∈ T.carrier :=
  T.parent_closed h

namespace RootIndexed

/-- A deterministic tree for every initial ancestor. -/
abbrev Tree (Root α : Type*) [LT α] := Root → UlamHarris.Tree α

end RootIndexed

end UlamHarris

end Combinatorics

end
