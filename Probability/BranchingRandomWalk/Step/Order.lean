module

public import Probability.BranchingRandomWalk.Step.Presentation
public import Combinatorics.BranchingWalk.Step.Monotone

@[expose] public section

/-!
# Ordered random branching steps

Ordering is a deterministic property of a `Step`. This file only transfers
that property through a random step and its pushforward law.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching

theorem StepPresentation.indexedLaw_ordered
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [LT ι] [LE X] (S : StepPresentation Ω ι X) (P : Measure Ω)
    (hmeas : MeasurableSet
      (orderedSteps : Set (Combinatorics.Branching.Step ι X)))
    (hordered : ∀ ω, S ω ∈ orderedSteps) :
    S.indexedLaw P orderedSteps = P Set.univ := by
  rw [S.indexedLaw_apply P orderedSteps hmeas]
  congr 1
  ext ω
  simp [hordered ω]

theorem StepPresentation.indexedLaw_nonempty
    {Ω ι X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable ι]
    (S : StepPresentation Ω ι X) (P : Measure Ω)
    (hnonempty : ∀ ω, S ω ∈ nonemptySupport) :
    S.indexedLaw P nonemptySupport = P Set.univ := by
  rw [S.indexedLaw_apply P nonemptySupport nonemptySupport_measurable]
  congr 1
  ext ω
  simp [hnonempty ω]

end ProbabilityTheory.BranchingRandomWalk
