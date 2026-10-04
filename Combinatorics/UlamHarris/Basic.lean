/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Data.List.Basic

/-!
# Ulam--Harris addresses and mark functions

`TreeNode α` is the abstract address type `List α` of a rooted tree whose
child labels live in `α`; it is not tied to `ℕ`. `𝕍 = TreeNode ℕ` is the
Ulam--Harris node set in standard notation.

`Mark α M` is the mark function `TreeNode α → M`: it assigns a mark to
*every* address, including reserve branches the walk never visits, and the
generation filtration of
`Probability/BranchingRandomWalk/Tree/Filtration.lean` is defined on it. This
is a separate object from a `MarkedTree`, which carries marks only on its
realized nodes; the realized-tree layer is in `Tree/Basic.lean` and the
marked-tree layer in `MarkedTree/Basic.lean`.
-/

public section

namespace Combinatorics

namespace UlamHarris

/-- Addresses of a rooted tree whose child labels live in `α`. This is the
abstract word type; `TreeNode ℕ` is the Ulam--Harris instance. -/
abbrev TreeNode (α : Type*) := List α

namespace RootIndexed

/-- A particle of a root-indexed tree: an address together with the root it belongs to. This is the
index a root-indexed walk's cloud is presented on, so it is named once here instead of spelling the
product out at every use. -/
abbrev TreeNode (Root α : Type*) := Root × UlamHarris.TreeNode α

end RootIndexed

/-- The Ulam--Harris node set `𝕍 = ⋃ₙ ℕⁿ` in standard notation. -/
abbrev 𝕍 := TreeNode ℕ

/-- The mark function in standard notation: a mark in `M` attached to every address
before any realized-tree restriction. The address type is arbitrary;
`Mark ℕ M` is the mark function on `𝕍`. The generation filtration is defined
directly on it, and a `MarkedTree` is what remains after keeping only the
realized nodes.

The name `Mark` is the object (a function on addresses), not a single mark:
a single mark is a term of the value type `M`. -/
abbrev Mark (α : Type*) (M : Type*) := TreeNode α → M

end UlamHarris

end Combinatorics

end
