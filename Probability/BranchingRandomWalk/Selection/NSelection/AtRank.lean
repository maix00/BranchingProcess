import Probability.BranchingRandomWalk.Selection.NSelection.ByValue
import Combinatorics.BranchingWalk.Selection.NSelection.AtRank

/-!
# Measurability of finite dynamic ranks

The particle at a prescribed dynamic rank has measurable fibres whenever the
finite candidate set has measurable fibres and countable actual range, and
the pairwise dynamic-key comparisons are measurable.  The ambient particle
type need not be countable.
-/

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.Branching.Selection.NSelection

variable {Ω ι Value : Type*} [MeasurableSpace Ω]

/-- Membership in a random finite candidate set is measurable when its
actual range is countable and its fibres are measurable.  No countability of
the ambient candidate type is needed. -/
theorem measurableSet_mem_candidates
    (candidates : Ω → Finset ι)
    (hcandidateFiber : ∀ s, MeasurableSet {ω | candidates ω = s})
    (hcandidateRange : (Set.range candidates).Countable) (p : ι) :
    MeasurableSet {ω | p ∈ candidates ω} := by
  let S : Set (Finset ι) := Set.range candidates
  let _ : Countable S := Set.countable_coe_iff.mpr hcandidateRange
  have hset : {ω | p ∈ candidates ω} =
      ⋃ s : {s : S // p ∈ s.1}, {ω | candidates ω = s.1.1} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hp
      exact ⟨⟨⟨candidates ω, Set.mem_range_self ω⟩, hp⟩, rfl⟩
    · rintro ⟨s, hs⟩
      simpa [hs] using s.2
  rw [hset]
  exact MeasurableSet.iUnion fun s => hcandidateFiber s.1.1

/-- Dynamic rank in one fixed finite candidate set is measurable. -/
theorem measurable_rankBy_fixed
    [LinearOrder ι] [LinearOrder Value]
    (value : Ω → ι → Value) (s : Finset ι) (p : ι)
    (hkey : ∀ q : ι, Measurable fun ω =>
      valueKey (value ω) q < valueKey (value ω) p) :
    Measurable fun ω => rankBy (value ω) s p := by
  have hsum : Measurable fun ω =>
      ∑ q ∈ s, if valueKey (value ω) q < valueKey (value ω) p
        then 1 else 0 := by
    apply Finset.measurable_sum
    intro q _
    apply measurable_const.ite _ measurable_const
    simpa using (hkey q) (measurableSet_singleton True)
  convert hsum using 1
  funext ω
  unfold rankBy rank
  rw [Finset.filter_image]
  exact (Finset.card_image_of_injective _
    (valueKey_injective (value ω))).trans (Finset.card_filter _ _)

/-- Dynamic rank remains measurable for a random finite candidate set.  Only
the actual range of the candidate-set random variable is required to be
countable; the ambient particle type may be uncountable. -/
theorem measurable_rankBy
    [LinearOrder ι] [LinearOrder Value]
    (value : Ω → ι → Value) (candidates : Ω → Finset ι) (p : ι)
    (hcandidateFiber : ∀ s, MeasurableSet {ω | candidates ω = s})
    (hcandidateRange : (Set.range candidates).Countable)
    (hkey : ∀ q : ι, Measurable fun ω =>
      valueKey (value ω) q < valueKey (value ω) p) :
    Measurable fun ω => rankBy (value ω) (candidates ω) p := by
  apply measurable_to_countable'
  intro k
  let S : Set (Finset ι) := Set.range candidates
  let _ : Countable S := Set.countable_coe_iff.mpr hcandidateRange
  have hset :
      {ω | rankBy (value ω) (candidates ω) p = k} =
        ⋃ s : S, {ω | candidates ω = s.1} ∩
          {ω | rankBy (value ω) s.1 p = k} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨⟨candidates ω, Set.mem_range_self ω⟩, rfl, h⟩
    · rintro ⟨s, hs, h⟩
      simpa [hs] using h
  rw [show (fun ω => rankBy (value ω) (candidates ω) p) ⁻¹' {k} =
      {ω | rankBy (value ω) (candidates ω) p = k} by ext; simp,
    hset]
  apply MeasurableSet.iUnion
  intro s
  apply (hcandidateFiber s.1).inter
  apply measurableSet_setOfPred.mpr
  exact (measurable_of_countable (fun r : ℕ => r = k)).comp
    (measurable_rankBy_fixed value s.1 p hkey)

/-- The fibre of a prescribed dynamically ranked particle is measurable for
a random finite candidate set with countable actual range. -/
theorem measurableSet_particleAtRankBy_eq_some
    [LinearOrder ι] [LinearOrder Value]
    (value : Ω → ι → Value) (candidates : Ω → Finset ι)
    (hcandidateFiber : ∀ s, MeasurableSet {ω | candidates ω = s})
    (hcandidateRange : (Set.range candidates).Countable)
    (hkey : ∀ p q : ι, Measurable fun ω =>
      valueKey (value ω) q < valueKey (value ω) p)
    (k : ℕ) (p : ι) :
    MeasurableSet {ω | particleAtRankBy (value ω) (candidates ω) k = some p} := by
  let S : Set (Finset ι) := Set.range candidates
  let _ : Countable S := Set.countable_coe_iff.mpr hcandidateRange
  have hset : {ω | particleAtRankBy (value ω) (candidates ω) k = some p} =
      ⋃ s : S, {ω | candidates ω = s.1} ∩
        {ω | particleAtRankBy (value ω) s.1 k = some p} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨⟨candidates ω, Set.mem_range_self ω⟩, rfl, h⟩
    · rintro ⟨s, hs, h⟩
      simpa [hs] using h
  rw [hset]
  apply MeasurableSet.iUnion
  intro s
  apply (hcandidateFiber s.1).inter
  simp_rw [particleAtRankBy_eq_some_iff]
  by_cases hp : p ∈ s.1
  · simp only [hp, true_and]
    apply measurableSet_setOfPred.mpr
    exact (measurable_of_countable (fun r : ℕ => r = k)).comp
      (measurable_rankBy_fixed value s.1 p (hkey p))
  · simp [hp]

/-- The `none` fibre is measurable without enumerating the ambient particle
type: it is determined solely by the random candidate cardinality. -/
theorem measurableSet_particleAtRankBy_eq_none
    [LinearOrder ι] [LinearOrder Value]
    (value : Ω → ι → Value) (candidates : Ω → Finset ι)
    (hcandidateFiber : ∀ s, MeasurableSet {ω | candidates ω = s})
    (hcandidateRange : (Set.range candidates).Countable)
    (k : ℕ) :
    MeasurableSet {ω | particleAtRankBy (value ω) (candidates ω) k = none} := by
  let S : Set (Finset ι) := Set.range candidates
  let _ : Countable S := Set.countable_coe_iff.mpr hcandidateRange
  have hset : {ω | particleAtRankBy (value ω) (candidates ω) k = none} =
      ⋃ s : {s : S // s.1.card ≤ k}, {ω | candidates ω = s.1.1} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    rw [particleAtRankBy_eq_none_iff]
    constructor
    · intro h
      exact ⟨⟨⟨candidates ω, Set.mem_range_self ω⟩, h⟩, rfl⟩
    · rintro ⟨s, hs⟩
      simpa [hs] using s.2
  rw [hset]
  exact MeasurableSet.iUnion fun s => hcandidateFiber s.1.1

/-- A dynamically ranked particle remains fibre-measurable when the rank is
itself a measurable natural-valued random variable. -/
theorem measurableSet_particleAtRankBy_randomRank_eq_some
    [LinearOrder ι] [LinearOrder Value]
    (value : Ω → ι → Value) (candidates : Ω → Finset ι)
    (hcandidateFiber : ∀ s, MeasurableSet {ω | candidates ω = s})
    (hcandidateRange : (Set.range candidates).Countable)
    (hkey : ∀ p q : ι, Measurable fun ω =>
      valueKey (value ω) q < valueKey (value ω) p)
    (rank : Ω → ℕ) (hrank : Measurable rank) (p : ι) :
    MeasurableSet
      {ω | particleAtRankBy (value ω) (candidates ω) (rank ω) = some p} := by
  have hset :
      {ω | particleAtRankBy (value ω) (candidates ω) (rank ω) = some p} =
        ⋃ k : ℕ, {ω | rank ω = k} ∩
          {ω | particleAtRankBy (value ω) (candidates ω) k = some p} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨rank ω, rfl, h⟩
    · rintro ⟨k, hk, h⟩
      simpa [hk] using h
  rw [hset]
  apply MeasurableSet.iUnion
  intro k
  have hrankSet : MeasurableSet {ω | rank ω = k} := by
    apply measurableSet_setOfPred.mpr
    exact (measurable_of_countable (fun r : ℕ => r = k)).comp hrank
  exact hrankSet.inter
    (measurableSet_particleAtRankBy_eq_some value candidates
      hcandidateFiber hcandidateRange hkey k p)

/-- The `none` fibre remains measurable for a measurable random rank. -/
theorem measurableSet_particleAtRankBy_randomRank_eq_none
    [LinearOrder ι] [LinearOrder Value]
    (value : Ω → ι → Value) (candidates : Ω → Finset ι)
    (hcandidateFiber : ∀ s, MeasurableSet {ω | candidates ω = s})
    (hcandidateRange : (Set.range candidates).Countable)
    (rank : Ω → ℕ) (hrank : Measurable rank) :
    MeasurableSet
      {ω | particleAtRankBy (value ω) (candidates ω) (rank ω) = none} := by
  have hset :
      {ω | particleAtRankBy (value ω) (candidates ω) (rank ω) = none} =
        ⋃ k : ℕ, {ω | rank ω = k} ∩
          {ω | particleAtRankBy (value ω) (candidates ω) k = none} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨rank ω, rfl, h⟩
    · rintro ⟨k, hk, h⟩
      simpa [hk] using h
  rw [hset]
  apply MeasurableSet.iUnion
  intro k
  have hrankSet : MeasurableSet {ω | rank ω = k} := by
    apply measurableSet_setOfPred.mpr
    exact (measurable_of_countable (fun r : ℕ => r = k)).comp hrank
  exact hrankSet.inter
    (measurableSet_particleAtRankBy_eq_none value candidates
      hcandidateFiber hcandidateRange k)


end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection
