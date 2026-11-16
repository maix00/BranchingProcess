/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.UlamHarris.Relation

public import Probability.BranchingRandomWalk.Selection.NSelection.Admissible.Real
public import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Drawdown.Population
public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law.Basic
public import Combinatorics.BranchingWalk.Step.Basic
/-!
# Nonempty selected generations

## Public declarations

In the namespace
`ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation`,
`finiteRootStepFieldLaw_firstNSelectedPopulation_nonempty_ae` states that if
`m > 0`, `N > 0`, the boundary is normalized, and a single step has nonempty
offspring almost surely, then for almost every `m`-root field the totalized
first-`N` selected population is nonempty at every generation:
\[
\forall^{\mathrm{a.e.}}\,\omega,\quad
\forall n,\quad
\operatorname{selectedPopulationTotalized}(N,\mathrm{Fin}(m),n,\omega)
\ne\varnothing.
\]
Here `μ` is a probability law with boundary normalization and
`μ nonemptySupport = 1`.

Under the nonempty-offspring and boundary-normalization assumptions,
the totalized first-`N` population is nonempty at every generation almost
surely, provided the initial population and selection capacity are nonempty.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

open Combinatorics.Branching
open Combinatorics.UlamHarris
open _root_.Combinatorics.Selection.NSelection

theorem finiteRootStepFieldLaw_firstNSelectedPopulation_nonempty_ae
    (m N : ℕ) (hm : 0 < m) (hN : 0 < N)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [DecidableEq (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization realPotential μ)
    (hnonempty : μ nonemptySupport = 1) :
    ∀ᵐ field ∂finiteRootStepFieldLaw μ m,
      ∀ n, (RootIndexed.selectedPopulationTotalized N
        (Finset.univ : Finset (Fin m)) (fun _ => (0 : ℝ)) id id n field).Nonempty :=
  RootIndexed.selectedPopulationTotalized_nonempty_ae N Finset.univ
    ⟨(⟨0, hm⟩ : Fin m), Finset.mem_univ _⟩ (fun _ : Fin m => 0) hN μ hboundary hnonempty

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation

end
