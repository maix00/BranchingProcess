/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Selection.NSelection.Infinite
public import Mathlib.MeasureTheory.MeasurableSpace.NCard

/-!
# Measurable selection from possibly infinite populations

The intrinsic first-`N` segment is unique. On a countable label space its
membership is measurable through the finite strict-predecessor condition,
even when the candidate population itself is infinite.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.Branching.Selection.NSelection

variable {Ω ι Value : Type*} [MeasurableSpace Ω]

/-- A measurable realization of the intrinsic first-`N` specification.
This interface does not impose countability on the ambient candidate type;
different point-process models may establish measurability by different
selection theorems. -/
structure MeasurableFirstNBy
    [MeasurableSpace ι] [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (value : Ω → ι → Value) (candidates : Ω → Set ι) where
  selected : Ω → Finset ι
  measurable_selected : Measurable selected
  isFirst : ∀ ω, IsFirstNBy N (value ω) (candidates ω) (selected ω)

/-- Any measurable realization of the intrinsic specification proves that
the canonical, choice-based first-`N` set is measurable, by uniqueness. -/
theorem measurable_selectFirstNFromSet_of_selector
    [MeasurableSpace ι] [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (value : Ω → ι → Value) (candidates : Ω → Set ι)
    (hadmits : ∀ ω, AdmitsFirstNBy N (value ω) (candidates ω))
    (selector : MeasurableFirstNBy N value candidates) :
    Measurable fun ω =>
      selectFirstNFromSet N (value ω) (candidates ω) (hadmits ω) := by
  convert selector.measurable_selected using 1
  funext ω
  exact (selectFirstNFromSet_spec N (value ω) (candidates ω)
    (hadmits ω)).unique (selector.isFirst ω)

/-- The uniquely specified first-`N` segment of a measurable, possibly
infinite, candidate population is measurable. Countability concerns labels,
not the candidate population, and is used for `Set.ncard` measurability. -/
theorem measurable_selectFirstNFromSet
    [Countable ι] [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (value : Ω → ι → Value) (candidates : Ω → Set ι)
    (hadmits : ∀ ω, AdmitsFirstNBy N (value ω) (candidates ω))
    (hcandidates : Measurable candidates)
    (hkey : ∀ p q : ι, Measurable fun ω =>
      valueKey (value ω) q < valueKey (value ω) p) :
    Measurable fun ω =>
      selectFirstNFromSet N (value ω) (candidates ω) (hadmits ω) := by
  rw [measurable_finset_iff]
  intro p
  simp_rw [mem_selectFirstNFromSet_iff]
  let lower : Ω → Set ι := fun ω =>
    {q | q ∈ candidates ω ∧
      valueKey (value ω) q < valueKey (value ω) p}
  have hlower : Measurable lower := by
    rw [measurable_set_iff]
    intro q
    exact ((measurable_set_mem q).comp hcandidates).and (hkey p q)
  have hfinite : Measurable fun ω => (lower ω).Finite := by
    apply measurableSet_setOfPred.mp
    exact MeasurableSet.setOfPred_finite.preimage hlower
  have hncard : Measurable fun ω => (lower ω).ncard :=
    measurable_ncard.comp hlower
  exact ((measurable_set_mem p).comp hcandidates).and
    (hfinite.and
      ((measurable_of_countable (fun k : ℕ => k < N)).comp hncard))

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection
