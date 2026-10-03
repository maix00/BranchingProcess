module

public import Probability.BranchingRandomWalk.Selection.NSelection.Admissible

/-!
# Totalized first-N selection

The first-N selector is defined on every input.  It uses the unique first-N
segment on the measurable lower-finite domain and returns the empty set off
that domain.  Exact first-N specifications are stated only on the valid
domain.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.Branching.Selection.NSelection

variable {Ω ι Value : Type*}

/-- A total first-N selector.  When lower-finiteness fails, the result is
empty; the exact first-N property is only promised where lower-finiteness
holds. -/
noncomputable def selectFirstNFromSetTotalized
    [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (value : Ω → ι → Value) (candidates : Ω → Set ι)
    (ω : Ω) : Finset ι := by
  classical
  exact if h : IsLowerFiniteBy (value ω) (candidates ω) then
    selectFirstNFromSet N (value ω) (candidates ω)
      (admitsFirstNBy_of_lowerFinite N (value ω) h)
  else ∅

theorem selectFirstNFromSetTotalized_spec
    [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (value : Ω → ι → Value) (candidates : Ω → Set ι)
    (ω : Ω) (hgood : IsLowerFiniteBy (value ω) (candidates ω)) :
    IsFirstNBy N (value ω) (candidates ω)
      (selectFirstNFromSetTotalized N value candidates ω) := by
  classical
  simp [selectFirstNFromSetTotalized, hgood,
    selectFirstNFromSet_spec]

theorem selectFirstNFromSetTotalized_empty_of_not_lowerFinite
    [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (value : Ω → ι → Value) (candidates : Ω → Set ι)
    (ω : Ω) (hbad : ¬ IsLowerFiniteBy (value ω) (candidates ω)) :
    selectFirstNFromSetTotalized N value candidates ω = ∅ := by
  simp [selectFirstNFromSetTotalized, hbad]

theorem mem_selectFirstNFromSetTotalized_iff
    [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (value : Ω → ι → Value) (candidates : Ω → Set ι)
    (ω : Ω) (p : ι) :
    p ∈ selectFirstNFromSetTotalized N value candidates ω ↔
      IsLowerFiniteBy (value ω) (candidates ω) ∧
      p ∈ candidates ω ∧
      {q | q ∈ candidates ω ∧
        valueKey (value ω) q < valueKey (value ω) p}.Finite ∧
      {q | q ∈ candidates ω ∧
        valueKey (value ω) q < valueKey (value ω) p}.ncard < N := by
  classical
  by_cases hgood : IsLowerFiniteBy (value ω) (candidates ω)
  · rw [show selectFirstNFromSetTotalized N value candidates ω =
        selectFirstNFromSet N (value ω) (candidates ω)
          (admitsFirstNBy_of_lowerFinite N (value ω) hgood) by
      simp [selectFirstNFromSetTotalized, hgood]]
    rw [(selectFirstNFromSet_spec N (value ω) (candidates ω)
      (admitsFirstNBy_of_lowerFinite N (value ω) hgood)).mem_iff_ncard_lt p]
    simp [hgood]
  · simp [selectFirstNFromSetTotalized, hgood]

theorem measurable_selectFirstNFromSetTotalized
    [MeasurableSpace Ω]
    [Countable ι] [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (value : Ω → ι → Value) (candidates : Ω → Set ι)
    (hcandidates : Measurable candidates)
    (hkey : ∀ p q : ι, Measurable fun ω =>
      valueKey (value ω) q < valueKey (value ω) p) :
    Measurable fun ω => selectFirstNFromSetTotalized N value candidates ω := by
  classical
  rw [measurable_finset_iff]
  intro p
  simp_rw [mem_selectFirstNFromSetTotalized_iff]
  have hgood : Measurable fun ω => IsLowerFiniteBy (value ω) (candidates ω) :=
    measurableSet_setOfPred.mp
      (measurableSet_lowerFiniteDomain value candidates hcandidates hkey)
  have hmem : Measurable fun ω => p ∈ candidates ω :=
    (measurable_set_mem p).comp hcandidates
  let lower : Ω → Set ι := fun ω =>
    {q | q ∈ candidates ω ∧ valueKey (value ω) q < valueKey (value ω) p}
  have hlower : Measurable lower := by
    rw [measurable_set_iff]
    intro q
    exact ((measurable_set_mem q).comp hcandidates).and (hkey p q)
  have hfinite : Measurable fun ω => (lower ω).Finite := by
    apply measurableSet_setOfPred.mp
    exact MeasurableSet.setOfPred_finite.preimage hlower
  have hncard : Measurable fun ω => (lower ω).ncard := measurable_ncard.comp hlower
  exact hgood.and (hmem.and
    (hfinite.and ((measurable_of_countable (fun k : ℕ => k < N)).comp hncard)))

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection
