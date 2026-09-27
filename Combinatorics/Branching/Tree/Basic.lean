import Combinatorics.UlamHarris.Tree.Basic

/-!
# Deterministic branching trees

This layer contains no probability law. A branching tree is the genealogical
Ulam--Harris object on which later random tree laws are placed.
-/

namespace Combinatorics.Branching

/-- A deterministic branching genealogy. -/
abbrev Tree (α : Type*) [LT α] := Combinatorics.UlamHarris.Tree α

end Combinatorics.Branching
