/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.UlamHarris.Tree.Defs

/-!
# Deterministic branching trees

This layer contains no probability law. A branching tree is the genealogical
Ulam--Harris object on which later random tree laws are placed.
-/

@[expose] public section

namespace Combinatorics.Branching

/-- A deterministic branching genealogy. -/
abbrev Tree (α : Type*) [LT α] := Combinatorics.UlamHarris.Tree α

end Combinatorics.Branching
