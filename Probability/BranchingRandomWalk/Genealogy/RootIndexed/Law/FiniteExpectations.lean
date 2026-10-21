/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Genealogy.RootIndexed.Law.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-!
# Finite sums of root-indexed expectations

In namespace `ProbabilityTheory.BranchingRandomWalk`, write
`ν_Root := RootIndexed.stepFieldLaw (Root := Root) μ` and
`ν₁ := ProbabilityTheory.BranchingRandomWalk.stepFieldLaw μ`. The public
expectation identities assume a probability measure `μ` and measurable
observables:

- `RootIndexed.lintegral_root_observable μ r g hg`:
  $\int^- g(\mathrm{field}(r))\,d\nu_{Root}(\mathrm{field})=
  \int^- g(\mathrm{tree})\,d\nu_1(\mathrm{tree})$.
- `RootIndexed.lintegral_finset_root_observables μ A g hg`:
  $\int^- \sum_{r\in A}g_r(\mathrm{field}(r))\,d\nu_{Root}=
  \sum_{r\in A}\int^- g_r(\mathrm{tree})\,d\nu_1$.
  The observable may depend on `r`.
- `RootIndexed.lintegral_finset_root_observable μ A g hg` gives the common-
  observable case as $\int^- \sum_{r\in A}g(\mathrm{field}(r))\,d\nu_{Root}
  = |A|\int^-g(\mathrm{tree})\,d\nu_1$.

The root-indexed product space carries many copies of the single-root model;
it does not alter any single-root identity. This file transfers measurable
single-root observables to one labelled root and then sums those identities
over a finite set of roots. It is the interface through which a single-root
many-to-one theorem is reused for finitely many initial particles.
-/

open MeasureTheory ProbabilityTheory

@[expose] public section
open scoped BigOperators ENNReal

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching

/-- A measurable observable of one root has the same expectation on the joint
root-indexed space as on the single-root step-field law. -/
theorem RootIndexed.lintegral_root_observable
    {Root α X : Type*} [MeasurableSpace X]
    (μ : Measure (Combinatorics.Branching.Step α X)) [IsProbabilityMeasure μ]
    (r : Root) (g : Combinatorics.Branching.StepField α X → ENNReal) (hg : Measurable g) :
    (∫⁻ field, g (field r) ∂RootIndexed.stepFieldLaw (Root := Root) μ) =
      ∫⁻ tree : Combinatorics.Branching.StepField α X,
        g tree ∂ProbabilityTheory.BranchingRandomWalk.stepFieldLaw (α := α) (X := X) μ := by
  rw [← RootIndexed.stepFieldLaw_root_marginal
    (Root := Root) (α := α) μ r]
  rw [lintegral_map hg (measurable_pi_apply r)]

/-- Finite root sums are obtained by applying the single-root expectation
identity separately at each root.  The test may depend on the root label. -/
theorem RootIndexed.lintegral_finset_root_observables
    {Root α X : Type*} [MeasurableSpace X]
    (μ : Measure (Combinatorics.Branching.Step α X)) [IsProbabilityMeasure μ]
    (A : Finset Root) (g : Root → Combinatorics.Branching.StepField α X → ENNReal)
    (hg : ∀ r ∈ A, Measurable (g r)) :
    (∫⁻ field, ∑ r ∈ A, g r (field r)
        ∂RootIndexed.stepFieldLaw (Root := Root) μ) =
      ∑ r ∈ A, ∫⁻ tree : Combinatorics.Branching.StepField α X,
        g r tree ∂ProbabilityTheory.BranchingRandomWalk.stepFieldLaw (α := α) (X := X) μ := by
  rw [lintegral_finsetSum]
  · apply Finset.sum_congr rfl
    intro r hr
    exact RootIndexed.lintegral_root_observable μ r (g r) (hg r hr)
  · intro r hr
    exact (hg r hr).comp (measurable_pi_apply r)

/-- For an identical test at every root, the finite-root expectation is the
finite cardinality times the single-root expectation. -/
theorem RootIndexed.lintegral_finset_root_observable
    {Root α X : Type*} [MeasurableSpace X]
    (μ : Measure (Combinatorics.Branching.Step α X)) [IsProbabilityMeasure μ]
    (A : Finset Root) (g : Combinatorics.Branching.StepField α X → ENNReal) (hg : Measurable g) :
    (∫⁻ field, ∑ r ∈ A, g (field r)
        ∂RootIndexed.stepFieldLaw (Root := Root) μ) =
      A.card • (∫⁻ tree : Combinatorics.Branching.StepField α X,
        g tree ∂ProbabilityTheory.BranchingRandomWalk.stepFieldLaw (α := α) (X := X) μ) := by
  rw [RootIndexed.lintegral_finset_root_observables μ A (fun _ => g)
    (fun _ _ => hg)]
  simp

end ProbabilityTheory.BranchingRandomWalk
