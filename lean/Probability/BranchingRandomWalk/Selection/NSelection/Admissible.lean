/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.Infinite
public import Mathlib.MeasureTheory.MeasurableSpace.NCard

/-!
# Measurable domain of first-N selection

Lower-finiteness is a sufficient condition for an infinite candidate set to
admit its first `N` elements.  This file proves that the condition is
measurable when labels are countable and the candidate and order comparisons
are measurable.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.Branching.Selection.NSelection

variable {Ω ι Value : Type*} [MeasurableSpace Ω]

/-- The candidates no larger than a given candidate in the dynamic key order. -/
def lowerSection
    [LinearOrder ι] [LinearOrder Value]
    (value : Ω → ι → Value) (candidates : Ω → Set ι) (p : ι) :
    Ω → Set ι := fun ω =>
      {q | q ∈ candidates ω ∧
        valueKey (value ω) q ≤ valueKey (value ω) p}

/-- Samples for which every candidate has finitely many predecessors up to
its own key.  This sufficient condition includes finite and infinite
populations. -/
def lowerFiniteDomain
    [LinearOrder ι] [LinearOrder Value]
    (value : Ω → ι → Value) (candidates : Ω → Set ι) : Set Ω :=
  {ω | IsLowerFiniteBy (value ω) (candidates ω)}

theorem measurable_lowerSection
    [LinearOrder ι] [LinearOrder Value]
    (value : Ω → ι → Value) (candidates : Ω → Set ι) (p : ι)
    (hcandidates : Measurable candidates)
    (hkey : ∀ p q : ι, Measurable fun ω =>
      valueKey (value ω) q < valueKey (value ω) p) :
    Measurable (lowerSection value candidates p) := by
  rw [measurable_set_iff]
  intro q
  have hle : Measurable fun ω =>
      valueKey (value ω) q ≤ valueKey (value ω) p := by
    have hnot := (hkey q p).not
    simpa [not_lt] using hnot
  exact ((measurable_set_mem q).comp hcandidates).and hle

theorem measurableSet_lowerFiniteDomain
    [Countable ι] [LinearOrder ι] [LinearOrder Value]
    (value : Ω → ι → Value) (candidates : Ω → Set ι)
    (hcandidates : Measurable candidates)
    (hkey : ∀ p q : ι, Measurable fun ω =>
      valueKey (value ω) q < valueKey (value ω) p) :
    MeasurableSet (lowerFiniteDomain value candidates) := by
  change MeasurableSet
    {ω | ∀ p, p ∈ candidates ω → (lowerSection value candidates p ω).Finite}
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro p
  have hmem : Measurable fun ω => p ∈ candidates ω :=
    (measurable_set_mem p).comp hcandidates
  have hlower := measurable_lowerSection value candidates p hcandidates hkey
  have hfinite : Measurable fun ω => (lowerSection value candidates p ω).Finite := by
    apply measurableSet_setOfPred.mp
    exact MeasurableSet.setOfPred_finite.preimage hlower
  exact measurableSet_setOfPred.mpr (hmem.imp hfinite)

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection
