/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

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

/-- Totalized first-`N` selection depends only on the observed values of
candidates. In particular, changing an observation away from the candidate
set does not change either the admissibility test or the selected segment. -/
theorem selectFirstNFromSetTotalized_congr_value
    [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (value other : Ω → ι → Value) (candidates : Ω → Set ι)
    (ω : Ω) (hvalue : Set.EqOn (value ω) (other ω) (candidates ω)) :
    selectFirstNFromSetTotalized N value candidates ω =
      selectFirstNFromSetTotalized N other candidates ω := by
  classical
  have hkeyEq (p : ι) (hp : p ∈ candidates ω)
      (q : ι) (hq : q ∈ candidates ω) :
      valueKey (value ω) q = valueKey (other ω) q := by
    simp [valueKey, hvalue hq]
  have hlower :
      IsLowerFiniteBy (value ω) (candidates ω) ↔
        IsLowerFiniteBy (other ω) (candidates ω) := by
    constructor <;> intro h p hp
    · have hset :
          {q | q ∈ candidates ω ∧
            valueKey (value ω) q ≤ valueKey (value ω) p} =
          {q | q ∈ candidates ω ∧
            valueKey (other ω) q ≤ valueKey (other ω) p} := by
        ext q
        by_cases hq : q ∈ candidates ω
        · simp [hq, hkeyEq p hp q hq, hkeyEq p hp p hp]
        · simp [hq]
      simpa [hset] using h p hp
    · have hset :
          {q | q ∈ candidates ω ∧
            valueKey (other ω) q ≤ valueKey (other ω) p} =
          {q | q ∈ candidates ω ∧
            valueKey (value ω) q ≤ valueKey (value ω) p} := by
        ext q
        by_cases hq : q ∈ candidates ω
        · simp [hq, hkeyEq p hp q hq, hkeyEq p hp p hp]
        · simp [hq]
      simpa [hset] using h p hp
  by_cases h : IsLowerFiniteBy (value ω) (candidates ω)
  · have h' : IsLowerFiniteBy (other ω) (candidates ω) := hlower.mp h
    rw [show selectFirstNFromSetTotalized N value candidates ω =
        selectFirstNFromSet N (value ω) (candidates ω)
          (admitsFirstNBy_of_lowerFinite N (value ω) h) by
      simp [selectFirstNFromSetTotalized, h]]
    rw [show selectFirstNFromSetTotalized N other candidates ω =
        selectFirstNFromSet N (other ω) (candidates ω)
          (admitsFirstNBy_of_lowerFinite N (other ω) h') by
      simp [selectFirstNFromSetTotalized, h']]
    apply (selectFirstNFromSet_spec N (value ω) (candidates ω)
      (admitsFirstNBy_of_lowerFinite N (value ω) h)).unique
    apply (selectFirstNFromSet_spec N (other ω) (candidates ω)
      (admitsFirstNBy_of_lowerFinite N (other ω) h')).congr_value
    intro p hp
    exact (hvalue hp).symm
  · have h' : ¬ IsLowerFiniteBy (other ω) (candidates ω) :=
      fun h' => h (hlower.mpr h')
    simp [selectFirstNFromSetTotalized, h, h']

/-- Totalized selection is invariant when both the candidate set and all
candidate observations agree, even if the two inputs use different sample
points. -/
theorem selectFirstNFromSetTotalized_congr
    [LinearOrder ι] [LinearOrder Value]
    (N : ℕ) (value other : Ω → ι → Value)
    (candidates otherCandidates : Ω → Set ι) (ω ω' : Ω)
    (hcandidates : candidates ω = otherCandidates ω')
    (hvalue : Set.EqOn (value ω) (other ω') (candidates ω)) :
    selectFirstNFromSetTotalized N value candidates ω =
      selectFirstNFromSetTotalized N other otherCandidates ω' := by
  change selectFirstNFromSetTotalized N (fun _ p => value ω p)
      (fun _ => candidates ω) () =
    selectFirstNFromSetTotalized N (fun _ p => other ω' p)
      (fun _ => otherCandidates ω') ()
  have h := selectFirstNFromSetTotalized_congr_value N
    (fun _ p => value ω p) (fun _ p => other ω' p)
    (fun _ => candidates ω) () hvalue
  rw [← hcandidates]
  exact h

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
