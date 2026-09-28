import Combinatorics.BranchingWalk.Selection.Coupling.Offspring
import Combinatorics.BranchingWalk.Step.Basic

/-!
# Populations in a branching field

A population is indexed by the natural-number generations of one fixed
branching field.  It contains no probability space, filtration, measurability,
position, order, or selection mechanism.
-/

namespace Combinatorics.Branching

open Combinatorics.UlamHarris

/-- A set-valued population following a fixed root-indexed branching field. -/
structure Population {Root α X : Type*}
    (stepField : Root → StepField α X) where
  particles : ℕ → Set (RootIndexed.TreeNode Root α)
  depth : ∀ n p, p ∈ particles n → p.2.length = n
  successor : ∀ n,
    particles (n + 1) ⊆
      Selection.Coupling.offspringAddressSet (particles n)
        (fun p => support (stepField p.1 p.2))

namespace Population

variable {Root α X : Type*} {stepField : Root → StepField α X}

instance : CoeFun (Population stepField)
    (fun _ => ℕ → Set (RootIndexed.TreeNode Root α)) :=
  ⟨Population.particles⟩

end Population
end Combinatorics.Branching
