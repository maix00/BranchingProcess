/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Assumptions.Moments
public import Probability.BranchingRandomWalk.Assumptions.CrossWeight
public import Probability.BranchingRandomWalk.Assumptions.Structural
public import Probability.BranchingProcess.Offspring.Count
public import Probability.BranchingRandomWalk.Step.OrderingLaw
public import Mathlib.Order.SuccPred.LinearLocallyFinite

/-!
# Named assumption bundles for the thesis theorems

Bundles record the statements currently used by each main theorem. Keeping
the component predicates public lets intermediate lemmas request a smaller
set of hypotheses.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching MeasureTheory



structure BasicBranchingAssumptions {ι α X : Type*} [MeasurableSpace X]
    [Countable ι]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (L : StepLaw ι α X) : Prop where
  rawProbability : IsProbabilityMeasure L.raw
  nonempty :
    ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.HasAtLeastOneChild
      (⟨L.raw, rawProbability⟩ :
        ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι X)
  supercritical :
    ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw.IsSupercritical
      (⟨L.raw, rawProbability⟩ :
        ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι X)
  normalized : HasBoundaryNormalization L.potential L.raw

/-- Moment assumptions separately stated for Theorem 1.1 when `a > 0`.
The centered-spine and finite-variance fields will be added with the
measure-theoretic spine law, rather than duplicated as raw slot formulas. -/
structure TrajectoryMomentAssumptions {ι α X : Type*} [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (L : StepLaw ι α X) : Prop where
  cross : HasFiniteCrossWeight L.potential L.raw
  first : HasLeftmostFirstMoment L
  fourth : HasLeftmostFourthMoment L

/-- The extra hypothesis separately used for the `a = 0` trajectory argument. -/
structure RestartMomentAssumption {ι α X : Type*} [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (L : StepLaw ι α X) : Prop where
  exponential : HasLeftmostPositiveExponentialMoment L

/-- The intended moment layer for the one-sided Theorem 1.3 proof. -/
structure SpeedL1MomentAssumption {ι α X : Type*} [MeasurableSpace X]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (L : StepLaw ι α X) : Prop where
  first : HasLeftmostFirstMoment L

end ProbabilityTheory.BranchingRandomWalk
