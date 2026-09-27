import Combinatorics.BranchingWalk.Step.Basic

/-!
# Finite selections from a branching step

A finite step selection chooses finitely many surviving child slots from an
otherwise arbitrary branching step.  It does not prescribe an enumeration,
a distinguished slot, an order, or a capacity.  Those are properties of
particular rules rather than of the branching-step representation.
-/

namespace Combinatorics.Branching

/-- A finite selection of surviving slots from every branching step. -/
structure Step.FiniteSelection (α X : Type*) where
  select : Step α X → Finset α
  subset_support : ∀ ξ i, i ∈ select ξ → survive ξ i

namespace Step.FiniteSelection

variable {α X : Type*}

instance : CoeFun (Step.FiniteSelection α X)
    (fun _ => Step α X → Finset α) :=
  ⟨Step.FiniteSelection.select⟩

@[simp] theorem mem_support (R : Step.FiniteSelection α X)
    (ξ : Step α X) {i : α} (hi : i ∈ R ξ) : survive ξ i :=
  R.subset_support ξ i hi

/-- A uniform capacity bound on the number of selected child slots. -/
def IsBoundedBy (R : Step.FiniteSelection α X) (N : ℕ) : Prop :=
  ∀ ξ, (R ξ).card ≤ N

end Step.FiniteSelection

end Combinatorics.Branching
