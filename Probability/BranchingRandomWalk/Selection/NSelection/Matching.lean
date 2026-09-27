import Probability.BranchingRandomWalk.Selection.NSelection.AtRank
import Probability.BranchingRandomWalk.Selection.Coupling.Matching
import Combinatorics.BranchingWalk.Selection.NSelection.Matching
import Combinatorics.BranchingWalk.Step.Map

/-!
# Measurability of dynamic-rank matching

The canonical equal-rank match has measurable fibres when the two random
finite populations have countable actual ranges.  The ambient particle types
remain unrestricted.
-/

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open MeasureTheory
open Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection
open Combinatorics.UlamHarris

variable {Ω Value : Type*} [MeasurableSpace Ω]

/-- Membership in a random finite set is measurable when its actual range is
countable and all set fibres are measurable.  The ambient element type need
not be countable. -/
theorem measurableSet_mem_finset
    {ι : Type*} (s : Ω → Finset ι)
    (hfiber : ∀ t, MeasurableSet {ω | s ω = t})
    (hrange : (Set.range s).Countable) (i : ι) :
    MeasurableSet {ω | i ∈ s ω} := by
  let S : Set (Finset ι) := Set.range s
  let _ : Countable S := Set.countable_coe_iff.mpr hrange
  have hset : {ω | i ∈ s ω} =
      ⋃ t : {t : S // i ∈ t.1}, {ω | s ω = t.1.1} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hi
      exact ⟨⟨⟨s ω, Set.mem_range_self ω⟩, hi⟩, rfl⟩
    · rintro ⟨t, ht⟩
      simpa [ht] using t.2
  rw [hset]
  exact MeasurableSet.iUnion fun t => hfiber t.1.1

omit [MeasurableSpace Ω] in
/-- For a fixed source label, optional equal-rank lookup has countable actual
range whenever the random target finite set has countable actual range. -/
theorem particleAtSourceRankBy_range_countable
    {Source Target : Type*}
    [LinearOrder Source] [LinearOrder Target] [LinearOrder Value]
    (sourceValue : Ω → Source → Value)
    (targetValue : Ω → Target → Value)
    (source : Ω → Finset Source) (target : Ω → Finset Target)
    (htargetRange : (Set.range target).Countable) (p : Source) :
    (Set.range fun ω =>
      particleAtSourceRankBy (sourceValue ω) (targetValue ω)
        (source ω) (target ω) p).Countable := by
  let S : Set (Finset Target) := Set.range target
  let _ : Countable S := Set.countable_coe_iff.mpr htargetRange
  have htargets : (⋃ s : S, Option.some '' (↑s.1 : Set Target)).Countable :=
    Set.countable_iUnion fun s : S => s.1.countable_toSet.image Option.some
  apply (Set.countable_singleton none).union htargets |>.mono
  rintro o ⟨ω, rfl⟩
  cases hlookup : particleAtSourceRankBy (sourceValue ω) (targetValue ω)
      (source ω) (target ω) p with
  | none =>
      simp [hlookup]
  | some q =>
      apply Set.mem_union_right
      apply Set.mem_iUnion_of_mem
        (⟨target ω, Set.mem_range_self ω⟩ : S)
      exact ⟨q,
        (particleAtSourceRankBy_eq_some_iff.mp hlookup).1, hlookup.symm⟩

omit [MeasurableSpace Ω] in
/-- The guarded inverse match has countable actual range whenever the random
source population does. -/
theorem preimageByRank_range_countable
    {Particle : Type*} [LinearOrder Particle] [LinearOrder Value]
    (sourceValue targetValue : Ω → Particle → Value)
    (source target : Ω → Finset Particle)
    (hsourceRange : (Set.range source).Countable) (q : Particle) :
    (Set.range fun ω => preimageByRank (sourceValue ω) (targetValue ω)
      (source ω) (target ω) q).Countable := by
  have hlookup := particleAtSourceRankBy_range_countable
    targetValue sourceValue target source hsourceRange q
  apply (Set.countable_singleton none).union hlookup |>.mono
  rintro o ⟨ω, rfl⟩
  by_cases hq : q ∈ target ω
  · exact Set.mem_union_right _ ⟨ω, by simp [preimageByRank, hq]⟩
  · exact Set.mem_union_left _ (by simp [preimageByRank, hq])

omit [MeasurableSpace Ω] in
/-- For a fixed source label, the total equal-rank match has countable actual
range whenever the random target finite set has countable actual range. -/
theorem matchByRankOrSelf_range_countable
    {Particle : Type*} [LinearOrder Particle] [LinearOrder Value]
    (sourceValue targetValue : Ω → Particle → Value)
    (source target : Ω → Finset Particle)
    (hcard : ∀ ω, (source ω).card ≤ (target ω).card)
    (htargetRange : (Set.range target).Countable) (p : Particle) :
    (Set.range fun ω =>
      matchByRankOrSelf (sourceValue ω) (targetValue ω)
        (source ω) (target ω) (hcard ω) p).Countable := by
  let S : Set (Finset Particle) := Set.range target
  let _ : Countable S := Set.countable_coe_iff.mpr htargetRange
  have htargets : (⋃ s : S, (↑s.1 : Set Particle)).Countable :=
    Set.countable_iUnion fun s : S => s.1.countable_toSet
  apply (Set.countable_singleton p).union htargets |>.mono
  rintro q ⟨ω, rfl⟩
  by_cases hp : p ∈ source ω
  · apply Set.mem_union_right
    apply Set.mem_iUnion_of_mem
      (⟨target ω, Set.mem_range_self ω⟩ : S)
    exact matchByRankOrSelf_mem (sourceValue ω) (targetValue ω)
      (source ω) (target ω) (hcard ω) hp
  · exact Set.mem_union_left _ (by simp [matchByRankOrSelf, hp])

/-- The fibre of the target particle having the same dynamic rank as a fixed
source particle is measurable.  Countability is confined to the actual
ranges of the two random finite candidate sets. -/
theorem measurableSet_particleAtSourceRankBy_eq_some
    {Source Target : Type*}
    [LinearOrder Source] [LinearOrder Target] [LinearOrder Value]
    (sourceValue : Ω → Source → Value)
    (targetValue : Ω → Target → Value)
    (source : Ω → Finset Source) (target : Ω → Finset Target)
    (hsourceFiber : ∀ s, MeasurableSet {ω | source ω = s})
    (hsourceRange : (Set.range source).Countable)
    (htargetFiber : ∀ s, MeasurableSet {ω | target ω = s})
    (htargetRange : (Set.range target).Countable)
    (hsourceKey : ∀ p q : Source, Measurable fun ω =>
      valueKey (sourceValue ω) q < valueKey (sourceValue ω) p)
    (htargetKey : ∀ p q : Target, Measurable fun ω =>
      valueKey (targetValue ω) q < valueKey (targetValue ω) p)
    (p : Source) (q : Target) :
    MeasurableSet {ω |
      particleAtSourceRankBy (sourceValue ω) (targetValue ω)
        (source ω) (target ω) p = some q} := by
  exact measurableSet_particleAtRankBy_randomRank_eq_some
    targetValue target htargetFiber htargetRange htargetKey
    (fun ω => rankBy (sourceValue ω) (source ω) p)
    (measurable_rankBy sourceValue source p hsourceFiber hsourceRange
      (hsourceKey p)) q

/-- Every optional equal-rank lookup fibre is measurable. -/
theorem measurableSet_particleAtSourceRankBy_eq
    {Source Target : Type*}
    [LinearOrder Source] [LinearOrder Target] [LinearOrder Value]
    (sourceValue : Ω → Source → Value)
    (targetValue : Ω → Target → Value)
    (source : Ω → Finset Source) (target : Ω → Finset Target)
    (hsourceFiber : ∀ s, MeasurableSet {ω | source ω = s})
    (hsourceRange : (Set.range source).Countable)
    (htargetFiber : ∀ s, MeasurableSet {ω | target ω = s})
    (htargetRange : (Set.range target).Countable)
    (hsourceKey : ∀ p q : Source, Measurable fun ω =>
      valueKey (sourceValue ω) q < valueKey (sourceValue ω) p)
    (htargetKey : ∀ p q : Target, Measurable fun ω =>
      valueKey (targetValue ω) q < valueKey (targetValue ω) p)
    (p : Source) (o : Option Target) :
    MeasurableSet {ω |
      particleAtSourceRankBy (sourceValue ω) (targetValue ω)
        (source ω) (target ω) p = o} := by
  cases o with
  | some q =>
      exact measurableSet_particleAtSourceRankBy_eq_some
        sourceValue targetValue source target hsourceFiber hsourceRange
        htargetFiber htargetRange hsourceKey htargetKey p q
  | none =>
      exact measurableSet_particleAtRankBy_randomRank_eq_none
        targetValue target htargetFiber htargetRange
        (fun ω => rankBy (sourceValue ω) (source ω) p)
        (measurable_rankBy sourceValue source p hsourceFiber hsourceRange
          (hsourceKey p))

/-- Every fibre of the guarded inverse rank match is measurable. -/
theorem measurableSet_preimageByRank_eq
    {Particle : Type*} [LinearOrder Particle] [LinearOrder Value]
    (sourceValue targetValue : Ω → Particle → Value)
    (source target : Ω → Finset Particle)
    (hsourceFiber : ∀ s, MeasurableSet {ω | source ω = s})
    (hsourceRange : (Set.range source).Countable)
    (htargetFiber : ∀ s, MeasurableSet {ω | target ω = s})
    (htargetRange : (Set.range target).Countable)
    (hsourceKey : ∀ p q : Particle, Measurable fun ω =>
      valueKey (sourceValue ω) q < valueKey (sourceValue ω) p)
    (htargetKey : ∀ p q : Particle, Measurable fun ω =>
      valueKey (targetValue ω) q < valueKey (targetValue ω) p)
    (q : Particle) (o : Option Particle) :
    MeasurableSet {ω | preimageByRank (sourceValue ω) (targetValue ω)
      (source ω) (target ω) q = o} := by
  have hmem : MeasurableSet {ω | q ∈ target ω} :=
    measurableSet_mem_finset target htargetFiber htargetRange q
  have hlookup : ∀ o, MeasurableSet {ω |
      particleAtSourceRankBy (targetValue ω) (sourceValue ω)
        (target ω) (source ω) q = o} :=
    measurableSet_particleAtSourceRankBy_eq targetValue sourceValue
      target source htargetFiber htargetRange hsourceFiber hsourceRange
      htargetKey hsourceKey q
  cases o with
  | some p =>
      have hset : {ω | preimageByRank (sourceValue ω) (targetValue ω)
          (source ω) (target ω) q = some p} =
          {ω | q ∈ target ω} ∩ {ω |
            particleAtSourceRankBy (targetValue ω) (sourceValue ω)
              (target ω) (source ω) q = some p} := by
        ext ω
        by_cases hq : q ∈ target ω <;> simp [preimageByRank, hq]
      rw [hset]
      exact hmem.inter (hlookup (some p))
  | none =>
      have hset : {ω | preimageByRank (sourceValue ω) (targetValue ω)
          (source ω) (target ω) q = none} =
          {ω | q ∈ target ω}ᶜ ∪
            ({ω | q ∈ target ω} ∩ {ω |
              particleAtSourceRankBy (targetValue ω) (sourceValue ω)
                (target ω) (source ω) q = none}) := by
        ext ω
        by_cases hq : q ∈ target ω <;> simp [preimageByRank, hq]
      rw [hset]
      exact hmem.compl.union (hmem.inter (hlookup none))

/-- Install source values at target labels of the same dynamic rank; target
labels beyond the source rank range retain their fallback values. -/
noncomputable def valueAtMatchedRank
    {Particle Y : Type*} [LinearOrder Particle] [LinearOrder Value]
    (sourceValue targetValue : Ω → Particle → Value)
    (source target : Ω → Finset Particle)
    (sourceData fallback : Ω → Particle → Y)
    (ω : Ω) (q : Particle) : Y :=
  Selection.Coupling.valueAtPreimage sourceData fallback
    (fun sample targetParticle =>
      preimageByRank (sourceValue sample) (targetValue sample)
        (source sample) (target sample) targetParticle) ω q

omit [MeasurableSpace Ω] in
/-- Source data is recovered exactly at every canonically matched target. -/
theorem valueAtMatchedRank_matchByRankOrSelf
    {Particle Y : Type*} [LinearOrder Particle] [LinearOrder Value]
    (sourceValue targetValue : Ω → Particle → Value)
    (source target : Ω → Finset Particle)
    (ω : Ω) (hcard : (source ω).card ≤ (target ω).card)
    (sourceData fallback : Ω → Particle → Y)
    {p : Particle} (hp : p ∈ source ω) :
    valueAtMatchedRank sourceValue targetValue source target sourceData fallback
        ω (matchByRankOrSelf (sourceValue ω) (targetValue ω)
          (source ω) (target ω) hcard p) =
      sourceData ω p := by
  have htarget := matchByRankOrSelf_mem
    (sourceValue ω) (targetValue ω) (source ω) (target ω) hcard hp
  simp [valueAtMatchedRank, Selection.Coupling.valueAtPreimage,
    preimageByRank, htarget,
    particleAtSourceRankBy_matchByRankOrSelf
      (sourceValue ω) (targetValue ω) (source ω) (target ω) hcard hp]

/-- Rank-matched installation is measurable as a whole target-indexed
family.  Countability concerns only the actual random finite populations. -/
theorem valueAtMatchedRank_measurable
    {Particle Y : Type*} [LinearOrder Particle] [LinearOrder Value]
    [MeasurableSpace Y]
    (sourceValue targetValue : Ω → Particle → Value)
    (source target : Ω → Finset Particle)
    (sourceData fallback : Ω → Particle → Y)
    (hsourceFiber : ∀ s, MeasurableSet {ω | source ω = s})
    (hsourceRange : (Set.range source).Countable)
    (htargetFiber : ∀ s, MeasurableSet {ω | target ω = s})
    (htargetRange : (Set.range target).Countable)
    (hsourceKey : ∀ p q : Particle, Measurable fun ω =>
      valueKey (sourceValue ω) q < valueKey (sourceValue ω) p)
    (htargetKey : ∀ p q : Particle, Measurable fun ω =>
      valueKey (targetValue ω) q < valueKey (targetValue ω) p)
    (hsourceData : ∀ p, Measurable fun ω => sourceData ω p)
    (hfallback : ∀ q, Measurable fun ω => fallback ω q) :
    Measurable fun ω q =>
      valueAtMatchedRank sourceValue targetValue source target
        sourceData fallback ω q := by
  apply Selection.Coupling.valueAtPreimage_measurable_pi
  · intro q
    exact preimageByRank_range_countable sourceValue targetValue
      source target hsourceRange q
  · intro q o
    exact measurableSet_preimageByRank_eq sourceValue targetValue source target
      hsourceFiber hsourceRange htargetFiber htargetRange hsourceKey
      htargetKey q o
  · exact hsourceData
  · exact hfallback

/-- Install the step of each source particle at the target particle of the
same dynamic rank.  Target particles outside the source rank range retain
their fallback step. -/
noncomputable def RootIndexed.matchedStepField
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (sourceValue targetValue : Ω → RootIndexed.TreeNode Root α → Value)
    (source target : Ω → Finset (RootIndexed.TreeNode Root α))
    (sourceStep fallback : Ω → RootIndexed.StepField Root α X)
    (ω : Ω) : RootIndexed.StepField Root α X :=
  fun r u => valueAtMatchedRank sourceValue targetValue source target
    (fun sample p => sourceStep sample p.1 p.2)
    (fun sample q => fallback sample q.1 q.2) ω (r, u)

omit [MeasurableSpace Ω] in
/-- At every canonical equal-rank match, `matchedStepField` contains exactly
the corresponding source step. -/
theorem RootIndexed.matchedStepField_matchByRankOrSelf
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (sourceValue targetValue : Ω → RootIndexed.TreeNode Root α → Value)
    (source target : Ω → Finset (RootIndexed.TreeNode Root α))
    (ω : Ω) (hcard : (source ω).card ≤ (target ω).card)
    (sourceStep fallback : Ω → RootIndexed.StepField Root α X)
    {p : RootIndexed.TreeNode Root α} (hp : p ∈ source ω) :
    RootIndexed.matchedStepField sourceValue targetValue source target
        sourceStep fallback ω
        (matchByRankOrSelf (sourceValue ω) (targetValue ω)
          (source ω) (target ω) hcard p).1
        (matchByRankOrSelf (sourceValue ω) (targetValue ω)
          (source ω) (target ω) hcard p).2 =
      sourceStep ω p.1 p.2 := by
  exact valueAtMatchedRank_matchByRankOrSelf sourceValue targetValue
    source target ω hcard
    (fun sample q => sourceStep sample q.1 q.2)
    (fun sample q => fallback sample q.1 q.2) hp

omit [MeasurableSpace Ω] in
theorem RootIndexed.survive_matchedStepField_matchByRankOrSelf
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (sourceValue targetValue : Ω → RootIndexed.TreeNode Root α → Value)
    (source target : Ω → Finset (RootIndexed.TreeNode Root α))
    (ω : Ω) (hcard : (source ω).card ≤ (target ω).card)
    (sourceStep fallback : Ω → RootIndexed.StepField Root α X)
    {p : RootIndexed.TreeNode Root α} (hp : p ∈ source ω)
    (i : α) :
    survive (RootIndexed.matchedStepField sourceValue targetValue source target
      sourceStep fallback ω
      (matchByRankOrSelf (sourceValue ω) (targetValue ω)
        (source ω) (target ω) hcard p).1
      (matchByRankOrSelf (sourceValue ω) (targetValue ω)
        (source ω) (target ω) hcard p).2) i =
      survive (sourceStep ω p.1 p.2) i := by
  rw [RootIndexed.matchedStepField_matchByRankOrSelf sourceValue targetValue
    source target ω hcard sourceStep fallback hp]

omit [MeasurableSpace Ω] in
theorem RootIndexed.value'_map_matchedStepField_matchByRankOrSelf
    {Root α X Position Value : Type*}
    [Zero Position]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (sourceValue targetValue : Ω → RootIndexed.TreeNode Root α → Value)
    (source target : Ω → Finset (RootIndexed.TreeNode Root α))
    (ω : Ω) (hcard : (source ω).card ≤ (target ω).card)
    (sourceStep fallback : Ω → RootIndexed.StepField Root α X)
    (d : X → Position)
    {p : RootIndexed.TreeNode Root α} (hp : p ∈ source ω) (i : α) :
    value' ((RootIndexed.matchedStepField sourceValue targetValue source target
      sourceStep fallback ω
      (matchByRankOrSelf (sourceValue ω) (targetValue ω)
        (source ω) (target ω) hcard p).1
      (matchByRankOrSelf (sourceValue ω) (targetValue ω)
        (source ω) (target ω) hcard p).2).map d) i =
      value' ((sourceStep ω p.1 p.2).map d) i := by
  rw [RootIndexed.matchedStepField_matchByRankOrSelf sourceValue targetValue
    source target ω hcard sourceStep fallback hp]

/-- The field obtained by installing source steps at equal-rank target
particles is measurable.  Countability is required only for the actual
random finite populations used to compute the ranks. -/
theorem RootIndexed.matchedStepField_measurable
    {Root α X Value : Type*} [MeasurableSpace X]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (sourceValue targetValue : Ω → RootIndexed.TreeNode Root α → Value)
    (source target : Ω → Finset (RootIndexed.TreeNode Root α))
    (sourceStep fallback : Ω → RootIndexed.StepField Root α X)
    (hsourceFiber : ∀ s, MeasurableSet {ω | source ω = s})
    (hsourceRange : (Set.range source).Countable)
    (htargetFiber : ∀ s, MeasurableSet {ω | target ω = s})
    (htargetRange : (Set.range target).Countable)
    (hsourceKey : ∀ p q, Measurable fun ω =>
      valueKey (sourceValue ω) q < valueKey (sourceValue ω) p)
    (htargetKey : ∀ p q, Measurable fun ω =>
      valueKey (targetValue ω) q < valueKey (targetValue ω) p)
    (hsourceStep : ∀ p : RootIndexed.TreeNode Root α,
      Measurable fun ω => sourceStep ω p.1 p.2)
    (hfallback : ∀ q : RootIndexed.TreeNode Root α,
      Measurable fun ω => fallback ω q.1 q.2) :
    Measurable fun ω => RootIndexed.matchedStepField sourceValue targetValue
      source target sourceStep fallback ω := by
  have h := valueAtMatchedRank_measurable sourceValue targetValue source target
    (fun sample p => sourceStep sample p.1 p.2)
    (fun sample q => fallback sample q.1 q.2)
    hsourceFiber hsourceRange htargetFiber htargetRange
    hsourceKey htargetKey hsourceStep hfallback
  apply measurable_pi_iff.mpr
  intro r
  apply measurable_pi_iff.mpr
  intro u
  exact (measurable_pi_apply (r, u)).comp h

/-- Every fibre of the total equal-rank match is measurable.  Outside the
source population the total map fixes the particle label. -/
theorem measurableSet_matchByRankOrSelf_eq
    {Particle : Type*} [LinearOrder Particle] [LinearOrder Value]
    (sourceValue targetValue : Ω → Particle → Value)
    (source target : Ω → Finset Particle)
    (hcard : ∀ ω, (source ω).card ≤ (target ω).card)
    (hsourceFiber : ∀ s, MeasurableSet {ω | source ω = s})
    (hsourceRange : (Set.range source).Countable)
    (htargetFiber : ∀ s, MeasurableSet {ω | target ω = s})
    (htargetRange : (Set.range target).Countable)
    (hsourceKey : ∀ p q : Particle, Measurable fun ω =>
      valueKey (sourceValue ω) q < valueKey (sourceValue ω) p)
    (htargetKey : ∀ p q : Particle, Measurable fun ω =>
      valueKey (targetValue ω) q < valueKey (targetValue ω) p)
    (p q : Particle) :
    MeasurableSet {ω |
      matchByRankOrSelf (sourceValue ω) (targetValue ω)
        (source ω) (target ω) (hcard ω) p = q} := by
  let sourceMem : Set Ω := {ω | p ∈ source ω}
  let matched : Set Ω := {ω |
    particleAtSourceRankBy (sourceValue ω) (targetValue ω)
      (source ω) (target ω) p = some q}
  have hsourceMem : MeasurableSet sourceMem :=
    measurableSet_mem_candidates source hsourceFiber hsourceRange p
  have hmatched : MeasurableSet matched :=
    measurableSet_particleAtSourceRankBy_eq_some sourceValue targetValue
      source target hsourceFiber hsourceRange htargetFiber htargetRange
      hsourceKey htargetKey p q
  by_cases hpq : p = q
  · have hset : {ω |
        matchByRankOrSelf (sourceValue ω) (targetValue ω)
          (source ω) (target ω) (hcard ω) p = q} =
        (sourceMem ∩ matched) ∪ sourceMemᶜ := by
      ext ω
      subst q
      by_cases hp : p ∈ source ω
      · have hsome := particleAtSourceRankBy_matchByRank
          (sourceValue ω) (targetValue ω) (source ω) (target ω)
          (hcard ω) p hp
        simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff,
          Set.mem_ofPred_eq, sourceMem, matched]
        rw [matchByRankOrSelf_of_mem _ _ _ _ _ hp]
        constructor
        · intro h
          exact Or.inl ⟨hp, hsome.trans (congrArg some h)⟩
        · rintro (⟨_, h⟩ | hnot)
          · exact Option.some.inj (hsome.symm.trans h)
          · exact (hnot hp).elim
      · simp [sourceMem, matched, hp]
    rw [hset]
    exact (hsourceMem.inter hmatched).union hsourceMem.compl
  · have hset : {ω |
        matchByRankOrSelf (sourceValue ω) (targetValue ω)
          (source ω) (target ω) (hcard ω) p = q} =
        sourceMem ∩ matched := by
      ext ω
      by_cases hp : p ∈ source ω
      · have hsome := particleAtSourceRankBy_matchByRank
          (sourceValue ω) (targetValue ω) (source ω) (target ω)
          (hcard ω) p hp
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, sourceMem, matched]
        rw [matchByRankOrSelf_of_mem _ _ _ _ _ hp]
        constructor
        · intro h
          exact ⟨hp, hsome.trans (congrArg some h)⟩
        · rintro ⟨_, h⟩
          exact Option.some.inj (hsome.symm.trans h)
      · simp [sourceMem, matched, hp, hpq]
    rw [hset]
    exact hsourceMem.inter hmatched

/-- The target-step family read through canonical equal-rank matching is
measurable in the generation domain flow.  The root and child-slot types are
unrestricted; all countability assumptions concern actual random ranges. -/
theorem RootIndexed.matchedSteps_matchByRankOrSelf_measurable
    {Root α X Value : Type*} [MeasurableSpace X]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value] {n : ℕ}
    (sourceValue targetValue :
      BranchingRandomWalk.RootIndexed.StepField Root α X →
        RootIndexed.TreeNode Root α → Value)
    (source target : BranchingRandomWalk.RootIndexed.StepField Root α X →
      Finset (RootIndexed.TreeNode Root α))
    (hcard : ∀ ω, (source ω).card ≤ (target ω).card)
    (hsourceFiber : ∀ s,
      MeasurableSet[BranchingRandomWalk.RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X) n] {ω | source ω = s})
    (hsourceRange : (Set.range source).Countable)
    (htargetFiber : ∀ s,
      MeasurableSet[BranchingRandomWalk.RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X) n] {ω | target ω = s})
    (htargetRange : (Set.range target).Countable)
    (hsourceKey : ∀ p q,
      Measurable[BranchingRandomWalk.RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X) n] fun ω =>
        valueKey (sourceValue ω) q < valueKey (sourceValue ω) p)
    (htargetKey : ∀ p q,
      Measurable[BranchingRandomWalk.RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X) n] fun ω =>
        valueKey (targetValue ω) q < valueKey (targetValue ω) p)
    (hdepth : ∀ ω p,
      (matchByRankOrSelf (sourceValue ω) (targetValue ω)
        (source ω) (target ω) (hcard ω) p).2.length < n) :
    Measurable[BranchingRandomWalk.RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (Selection.Coupling.RootIndexed.matchedSteps fun ω p =>
        matchByRankOrSelf (sourceValue ω) (targetValue ω)
          (source ω) (target ω) (hcard ω) p) := by
  let _ : MeasurableSpace
      (BranchingRandomWalk.RootIndexed.StepField Root α X) :=
    BranchingRandomWalk.RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n
  apply Selection.Coupling.RootIndexed.matchedSteps_measurable
  · intro p
    exact matchByRankOrSelf_range_countable sourceValue targetValue
      source target hcard htargetRange p
  · intro p q
    exact measurableSet_matchByRankOrSelf_eq sourceValue targetValue
      source target hcard hsourceFiber hsourceRange htargetFiber htargetRange
      hsourceKey htargetKey p q
  · exact hdepth


end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection
