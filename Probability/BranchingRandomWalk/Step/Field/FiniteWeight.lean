/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Assumptions.Structural
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law.Basic

/-!
# Almost-sure finite exponential weights in pre-sampled fields

Boundary normalization first gives one-step almost-sure finiteness.  For
countable root and address labels, the same property holds simultaneously at
every coordinate of the root-indexed product field.

For the root-indexed field law, the simultaneous conclusion is

\[\mathbb P\!\left(\forall r\in\mathrm{Root},\ \forall u\in\mathbb V,\;
  \operatorname{totalPotentialWeight}_{\phi,-1}(\omega(r,u))\ne\infty\right)=1.\]

## Public declarations

- `ProbabilityTheory.BranchingRandomWalk.RootIndexed.stepFieldLaw_all_finitePotentialWeight`:
  for countable roots and slots, the negative exponential weight is finite at
  every field coordinate almost surely.

-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching

/-- Under boundary normalization, the negative exponential child weight is
finite at every address in a countably indexed pre-sampled forest, almost surely. -/
theorem RootIndexed.stepFieldLaw_all_finitePotentialWeight
    {Root α X : Type*} [Countable Root] [Countable α] [MeasurableSpace X]
    (φ : Potential X)
    (μ : Measure (Combinatorics.Branching.Step α X)) [IsProbabilityMeasure μ]
    (h : HasBoundaryNormalization φ μ) :
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root) μ,
      ∀ r : Root, ∀ u : TreeNode α,
        totalPotentialWeight φ (-1) (field r u) ≠ ∞ := by
  let A : Set (Combinatorics.Branching.Step α X) :=
    {ξ | totalPotentialWeight φ (-1) ξ ≠ ∞}
  have hA : MeasurableSet A := by
    exact (totalPotentialWeight_measurable φ (-1)
      (measurableSet_singleton (∞ : ENNReal))).compl
  have hμA : μ A = 1 := by
    calc
      μ A = μ Set.univ :=
        (ae_mem_iff_measure_eq hA.nullMeasurableSet).mp (by
          change ∀ᵐ ξ ∂μ, totalPotentialWeight φ (-1) ξ ≠ ∞
          exact h.ae_totalPotentialWeight_ne_top φ μ)
      _ = 1 := measure_univ
  simpa only [A, Set.mem_ofPred_eq] using
    (RootIndexed.stepFieldLaw_ae_all_of_measure_one hA μ hμA)

end ProbabilityTheory.BranchingRandomWalk
