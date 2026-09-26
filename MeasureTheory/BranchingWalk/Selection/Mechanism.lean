import MeasureTheory.BranchingWalk.Selection.Contain

/-!
# Selection mechanisms on branching walks

A `SelectionMechanism` is a map `BranchingWalk → BranchingWalk` that always
selects a sub-walk: the image is contained in the source in the `SelectContain`
order. It is the deterministic, walk-level notion of "keeping some children of
every node"; the per-node rule on finite candidate sets is the `SelectMechanism`
of `Selection/SelectMechanism.lean`.

A random selection mechanism is a law on these objects and belongs to the
probability layer. The special mechanisms that bound the number of kept
children by a capacity `N` are the `NSelection`s of `Selection/NSelection/`.
-/

namespace MeasureTheory

namespace BranchingWalk

namespace Selection

/-- A deterministic selection mechanism: a map on branching walks that keeps a
sub-walk of its input, in the `SelectContain` order. -/
structure SelectionMechanism (α X : Type*) where
  /-- The selected sub-walk. -/
  select : BranchingWalk α X → BranchingWalk α X
  /-- Selection keeps only children that were already present. -/
  contained : ∀ ω, SelectContain (select ω) ω

instance (α X : Type*) :
    CoeFun (SelectionMechanism α X) (fun _ => BranchingWalk α X → BranchingWalk α X) :=
  ⟨SelectionMechanism.select⟩

namespace SelectionMechanism

variable {α X : Type*}

@[ext] theorem ext {M M' : SelectionMechanism α X}
    (h : ∀ ω, M.select ω = M'.select ω) : M = M' := by
  obtain ⟨sel, con⟩ := M
  obtain ⟨sel', con'⟩ := M'
  have hsel : sel = sel' := funext h
  cases hsel
  rw [Subsingleton.elim con con']

end SelectionMechanism

end Selection

end BranchingWalk

end MeasureTheory
