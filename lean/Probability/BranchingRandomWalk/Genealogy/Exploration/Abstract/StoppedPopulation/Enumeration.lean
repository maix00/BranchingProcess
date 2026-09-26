import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.DomainFlow.Independence

/-!
# Enumerating a finite labelled population

A finite finset of multi-root addresses can be listed injectively by a `Fin`-indexed
family covering exactly that set.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory


theorem finiteMultiRootAddress_enumeration {m : ℕ}
    (s : Finset (Fin m × 𝕍)) :
    ∃ roots : Fin s.card → Fin m × 𝕍,
      s = Finset.univ.image roots ∧ Function.Injective roots := by
  classical
  let e : {p : Fin m × 𝕍 // p ∈ s} ≃ Fin s.card :=
    Fintype.equivFinOfCardEq (by simp)
  let roots : Fin s.card → Fin m × 𝕍 := fun j => (e.symm j).1
  refine ⟨roots, ?_, ?_⟩
  · ext p
    constructor
    · intro hp
      exact Finset.mem_image.mpr
        ⟨e ⟨p, hp⟩, Finset.mem_univ _, by simp [roots]⟩
    · intro hp
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
      exact (e.symm j).2
  · intro i j hij
    apply e.symm.injective
    exact Subtype.ext hij

end ProbabilityTheory.BranchingRandomWalk
