/-
Copyright (c) 2026 WANG Yiyang.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
import Probability.BranchingRandomWalk.Step.Law

/-!
# Independence on a pre-sampled tree

The address map is supplied as ordinary deterministic data.  In particular,
the theorem below does not require the selected addresses to be stopping
times.  This is the formal interface used for reserve branches and stopping
line arguments: once the addresses are fixed on the pre-sampled tree, an
injective address map gives independent marks.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching

theorem preSampled_coordinates_independent
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {ι : Type*}
    (σ : ι → TreeNode α) (hσ : Function.Injective σ) :
    iIndepFun (fun i (ω : StepField α X) => ω (σ i))
      (stepFieldLaw μ) :=
  by simpa only [stepFieldLaw] using
    (ProbabilityTheory.BranchingProcess.offspringFieldLaw_injective_coordinates_independent
      μ σ hσ)

theorem preSampled_measurable_observables_independent
    {α X : Type*} [MeasurableSpace X]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
    {ι : Type*} {β : ι → Type*}
    [∀ i, MeasurableSpace (β i)]
    (σ : ι → TreeNode α) (hσ : Function.Injective σ)
    (g : ∀ i, Step α X → β i)
    (hg : ∀ i, Measurable (g i)) :
    iIndepFun
      (fun i (ω : StepField α X) => g i (ω (σ i)))
      (stepFieldLaw μ) :=
  by simpa only [stepFieldLaw] using
    (ProbabilityTheory.BranchingProcess.offspringFieldLaw_injective_coordinates_comp_independent
      μ σ hσ g hg)

end ProbabilityTheory.BranchingRandomWalk
