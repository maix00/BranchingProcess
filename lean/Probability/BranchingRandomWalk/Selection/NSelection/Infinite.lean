import Combinatorics.BranchingWalk.Selection.NSelection.Infinite
import Mathlib.MeasureTheory.MeasurableSpace.NCard

/-!
# Measurable selection from possibly infinite populations

The intrinsic first-`N` segment is unique. On a countable label space its
membership is measurable through the finite strict-predecessor condition,
even when the candidate population itself is infinite.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.Branching.Selection.NSelection

variable {Ω ι Value : Type*} [MeasurableSpace Ω]

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
