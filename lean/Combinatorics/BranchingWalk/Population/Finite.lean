import Combinatorics.BranchingWalk.Population.Basic
import Mathlib.Data.Finset.Basic

/-!
# Layerwise finite populations in a branching field
-/

namespace Combinatorics.Branching

open Combinatorics.UlamHarris

/-- A branching population represented by a finite set at every generation. -/
structure FinitePopulation {Root α X : Type*}
    (stepField : Root → StepField α X) where
  particles : ℕ → Finset (RootIndexed.TreeNode Root α)
  depth : ∀ n p, p ∈ particles n → p.2.length = n
  successor : ∀ n,
    ↑(particles (n + 1)) ⊆
      Selection.Coupling.offspringAddressSet (↑(particles n))
        (fun p => support (stepField p.1 p.2))

namespace FinitePopulation

variable {Root α X : Type*} {stepField : Root → StepField α X}

instance : CoeFun (FinitePopulation stepField)
    (fun _ => ℕ → Finset (RootIndexed.TreeNode Root α)) :=
  ⟨FinitePopulation.particles⟩

/-- Forget the layerwise finite representation. -/
def toPopulation (P : FinitePopulation stepField) : Population stepField where
  particles n := ↑(P n)
  depth n p hp := P.depth n p hp
  successor n := P.successor n

@[simp] theorem mem_toPopulation (P : FinitePopulation stepField)
    (n : ℕ) (p : RootIndexed.TreeNode Root α) :
    p ∈ P.toPopulation n ↔ p ∈ P n :=
  Iff.rfl

end FinitePopulation
end Combinatorics.Branching
