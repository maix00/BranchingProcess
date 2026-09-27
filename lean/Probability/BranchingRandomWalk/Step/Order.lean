import Probability.BranchingRandomWalk.Step.Basic

/-!
# Ordered random branching steps

Ordering is a deterministic property of a `Step`. This file only transfers
that property through a random step and its pushforward law.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching

theorem Step.law_ordered
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [LT ι] [LE X] (Ξ : Step Ω ι X) (P : Measure Ω)
    (hmeas : MeasurableSet
      (orderedSteps : Set (Combinatorics.Branching.Step ι X)))
    (hordered : ∀ ω, Ξ ω ∈ orderedSteps) :
    Ξ.law P orderedSteps = P Set.univ := by
  rw [Ξ.law_apply P orderedSteps hmeas]
  congr 1
  ext ω
  simp [hordered ω]

theorem Step.law_nonempty
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable ι]
    (Ξ : Step Ω ι X) (P : Measure Ω)
    (hnonempty : ∀ ω, Ξ ω ∈ nonemptySupport) :
    Ξ.law P nonemptySupport = P Set.univ := by
  rw [Ξ.law_apply P nonemptySupport nonemptySupport_measurable]
  congr 1
  ext ω
  simp [hnonempty ω]

end ProbabilityTheory.BranchingRandomWalk
