import Probability.BranchingRandomWalk.Selection.NSelection.AtRank
import Probability.BranchingRandomWalk.Coupling.Field.Preimage
import Combinatorics.BranchingWalk.Selection.NSelection.RankMap
import Combinatorics.BranchingWalk.Step.Map

/-!
# Rank preimage measurability

Countable-range and generation-domain-flow measurability for the guarded
rank inverse and its optional value lookup.
-/

namespace ProbabilityTheory.BranchingRandomWalk.Coupling

open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open MeasureTheory
open Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection
open Combinatorics.UlamHarris

variable {Ω Value : Type*} [MeasurableSpace Ω]

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
/-- The complete guarded inverse match has countable actual range when its
random finite source and target supports do.  No countability assumption is
placed on the ambient particle type. -/
theorem preimageByRank_function_range_countable
    {Particle : Type*} [LinearOrder Particle] [LinearOrder Value]
    (sourceValue targetValue : Ω → Particle → Value)
    (source target : Ω → Finset Particle)
    (hsourceRange : (Set.range source).Countable)
    (htargetRange : (Set.range target).Countable) :
    (Set.range fun ω q => preimageByRank (sourceValue ω) (targetValue ω)
      (source ω) (target ω) q).Countable := by
  let S : Set (Finset Particle) := Set.range source
  let T : Set (Finset Particle) := Set.range target
  let _ : Countable S := Set.countable_coe_iff.mpr hsourceRange
  let _ : Countable T := Set.countable_coe_iff.mpr htargetRange
  let valid (s : S) (t : T) : Set (Particle → Option Particle) :=
    {f | (∀ q, q ∉ t.1 → f q = none) ∧
      (∀ q p, f q = some p → p ∈ s.1)}
  have hvalid : ∀ s t, (valid s t).Countable := by
    intro s t
    exact (preimageByRank_maps_finite s.1 t.1).countable
  have hall : (⋃ s : S, ⋃ t : T, valid s t).Countable :=
    Set.countable_iUnion fun s => Set.countable_iUnion fun t => hvalid s t
  apply hall.mono
  rintro f ⟨ω, rfl⟩
  apply Set.mem_iUnion_of_mem
    (⟨source ω, Set.mem_range_self ω⟩ : S)
  apply Set.mem_iUnion_of_mem
    (⟨target ω, Set.mem_range_self ω⟩ : T)
  constructor
  · intro q hq
    simp [preimageByRank, hq]
  · intro q p hp
    exact (preimageByRank_eq_some_iff.mp hp).2.1

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

/-- Every fibre of the complete guarded inverse function is measurable.
Function equality is checked only on the finite random target support; off
that support both sides are forced to be `none`. -/
theorem measurableSet_preimageByRank_function_eq
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
    (f : Particle → Option Particle) :
    MeasurableSet {ω | (fun q => preimageByRank
      (sourceValue ω) (targetValue ω) (source ω) (target ω) q) = f} := by
  let T : Set (Finset Particle) := Set.range target
  let _ : Countable T := Set.countable_coe_iff.mpr htargetRange
  let U := {t : T // ∀ q, q ∉ t.1 → f q = none}
  have hset : {ω | (fun q => preimageByRank
      (sourceValue ω) (targetValue ω) (source ω) (target ω) q) = f} =
      ⋃ t : U, {ω | target ω = t.1.1} ∩
        ⋂ q : {q : Particle // q ∈ t.1.1},
          {ω | preimageByRank (sourceValue ω) (targetValue ω)
            (source ω) (target ω) q.1 = f q.1} := by
    ext ω
    constructor
    · intro h
      have hout : ∀ q, q ∉ target ω → f q = none := by
        intro q hq
        rw [← congrFun h q]
        simp [preimageByRank, hq]
      let t : U := ⟨⟨target ω, Set.mem_range_self ω⟩, hout⟩
      apply Set.mem_iUnion_of_mem t
      constructor
      · rfl
      · simp only [Set.mem_iInter, Set.mem_ofPred_eq]
        intro q
        exact congrFun h q.1
    · intro h
      obtain ⟨t, htarget, hcoords⟩ := Set.mem_iUnion.mp h
      simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hcoords
      funext q
      by_cases hq : q ∈ t.1.1
      · exact hcoords ⟨q, hq⟩
      · have hq' : q ∉ target ω := by
          rw [htarget]
          exact hq
        rw [t.2 q hq]
        simp [preimageByRank, hq']
  rw [hset]
  apply MeasurableSet.iUnion
  intro t
  apply (htargetFiber t.1.1).inter
  apply MeasurableSet.iInter
  intro q
  exact measurableSet_preimageByRank_eq sourceValue targetValue source target
    hsourceFiber hsourceRange htargetFiber htargetRange hsourceKey htargetKey
    q.1 (f q.1)

/-- Install source values at target labels of the same dynamic rank; target
labels beyond the source rank range retain their fallback values. -/
noncomputable def valueAtMatchedRank
    {Particle Y : Type*} [LinearOrder Particle] [LinearOrder Value]
    (sourceValue targetValue : Ω → Particle → Value)
    (source target : Ω → Finset Particle)
    (sourceData fallback : Ω → Particle → Y)
    (ω : Ω) (q : Particle) : Y :=
  Coupling.valueAtPreimage sourceData fallback
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
  simp [valueAtMatchedRank, Coupling.valueAtPreimage,
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
  apply Coupling.valueAtPreimage_measurable_pi
  · intro q
    exact preimageByRank_range_countable sourceValue targetValue
      source target hsourceRange q
  · intro q o
    exact measurableSet_preimageByRank_eq sourceValue targetValue source target
      hsourceFiber hsourceRange htargetFiber htargetRange hsourceKey
      htargetKey q o
  · exact hsourceData
  · exact hfallback

end ProbabilityTheory.BranchingRandomWalk.Coupling
