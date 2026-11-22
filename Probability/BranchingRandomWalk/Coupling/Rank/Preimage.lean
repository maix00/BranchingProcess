/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.Selection.NSelection.AtRank
public import Probability.BranchingRandomWalk.Coupling.Field.Preimage
public import Combinatorics.Selection.NSelection.Matching.ByRank
public import Combinatorics.BranchingWalk.Step.Map
import MeasureTheory.MeasurableSpace.CountableEvaluation

/-!
# Rank preimage measurability

Countable-range and generation-domain-flow measurability for the guarded
rank inverse and its optional value lookup.

## Public declarations

Rank-matched data is read from the matched object at the guarded equal-rank
preimage, with fallback data used when that preimage is absent. Canonical
matches recover the object's value:

\[\begin{aligned}
\operatorname{valueAtMatchedRank}(\omega,q)
&=\begin{cases}
S(\omega,p),&\operatorname{objectAtPartnerRankBy}(\omega,q)=\operatorname{some}(p),\\
F(\omega,q),&\operatorname{objectAtPartnerRankBy}(\omega,q)=\operatorname{none},
\end{cases}\\
p\in\operatorname{objectsToMatch}(\omega),\quad
|\operatorname{objectsToMatch}(\omega)|\le|\operatorname{availablePartners}(\omega)|
&\Longrightarrow
\operatorname{valueAtMatchedRank}(\omega,\operatorname{matchByRankOrSelf}(p))
=S(\omega,p).
\end{aligned}\]

* `preimageByRank_function_range_countable` states that the actual range of
  `(ω, q) ↦ objectAtPartnerRankBy (objectOrderKey ω) (partnerOrderKey ω) (objectsToMatch ω)
  (availablePartners ω) q` is countable when both random finite populations have countable actual ranges.
* `matchByRankOrSelf_range_countable` states that the canonical equal-rank
  match, with identity fallback, has countable actual range under a
  countable-range hypothesis on the availablePartners support.
* `measurableSet_partnerAtObjectRankBy_eq_some` proves measurability of each
  event where an object's rank lookup returns a specified partner.
* `measurableSet_preimageByRank_function_eq` proves measurability of every
  fibre of the entire guarded inverse function, not just one coordinate.
* `valueAtMatchedRank` installs object data at the partner label of equal rank
  and uses fallback data where no object at that rank is available.
* `valueAtMatchedRank_matchByRankOrSelf` states that the installed value at a
  canonical match equals the original object value.
* `valueAtMatchedRank_measurable` proves measurability of the installed
  partner-indexed family from measurable object and fallback data.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Coupling

open MeasureTheory
open Combinatorics.Selection.NSelection
open Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection
open Combinatorics.UlamHarris

variable {Ω Value : Type*} [MeasurableSpace Ω]

private theorem measurableSet_mem_finset
    {ι : Type*} (s : Ω → Finset ι)
    (hfiber : ∀ t, MeasurableSet {ω | s ω = t})
    (hrange : (Set.range s).Countable) (i : ι) :
    MeasurableSet {ω | i ∈ s ω} := by
  have hs : Measurable s :=
    measurable_of_countable_range_of_fibers s hfiber hrange
  exact measurableSet_setOfPred.2 (measurable_finset_iff.mp hs i)

omit [MeasurableSpace Ω] in
/-- For a fixed object label, optional equal-rank lookup has countable actual
range whenever the random finite population of available partners has
countable actual range. -/
private theorem partnerAtObjectRankBy_range_countable
    {Object Partner : Type*}
    [LinearOrder Object] [LinearOrder Partner] [LinearOrder Value]
    (objectOrderKey : Ω → Object → Value)
    (partnerOrderKey : Ω → Partner → Value)
    (objectsToMatch : Ω → Finset Object) (availablePartners : Ω → Finset Partner)
    (havailablePartnersRange : (Set.range availablePartners).Countable) (p : Object) :
    (Set.range fun ω =>
      partnerAtObjectRankBy (objectOrderKey ω) (partnerOrderKey ω)
        (objectsToMatch ω) (availablePartners ω) p).Countable := by
  let S : Set (Finset Partner) := Set.range availablePartners
  let _ : Countable S := Set.countable_coe_iff.mpr havailablePartnersRange
  have partnerOptions : (⋃ s : S, Option.some '' (↑s.1 : Set Partner)).Countable :=
    Set.countable_iUnion fun s : S => s.1.countable_toSet.image Option.some
  apply (Set.countable_singleton none).union partnerOptions |>.mono
  rintro o ⟨ω, rfl⟩
  cases hlookup : partnerAtObjectRankBy (objectOrderKey ω) (partnerOrderKey ω)
      (objectsToMatch ω) (availablePartners ω) p with
  | none =>
      simp [hlookup]
  | some q =>
      apply Set.mem_union_right
      apply Set.mem_iUnion_of_mem
        (⟨availablePartners ω, Set.mem_range_self ω⟩ : S)
      exact ⟨q,
        (partnerAtObjectRankBy_eq_some_iff.mp hlookup).1, hlookup.symm⟩

omit [MeasurableSpace Ω] in
/-- The guarded inverse match has countable actual range whenever the random object population does. -/
private theorem preimageByRank_range_countable
    {Particle : Type*} [LinearOrder Particle] [LinearOrder Value]
    (objectOrderKey partnerOrderKey : Ω → Particle → Value)
    (objectsToMatch availablePartners : Ω → Finset Particle)
    (hobjectsToMatchRange : (Set.range objectsToMatch).Countable) (q : Particle) :
    (Set.range fun ω => objectAtPartnerRankBy (objectOrderKey ω) (partnerOrderKey ω)
      (objectsToMatch ω) (availablePartners ω) q).Countable := by
  have hlookup := partnerAtObjectRankBy_range_countable
    partnerOrderKey objectOrderKey availablePartners objectsToMatch hobjectsToMatchRange q
  apply (Set.countable_singleton none).union hlookup |>.mono
  rintro o ⟨ω, rfl⟩
  by_cases hq : q ∈ availablePartners ω
  · exact Set.mem_union_right _ ⟨ω, by simp [objectAtPartnerRankBy, hq]⟩
  · exact Set.mem_union_left _ (by simp [objectAtPartnerRankBy, hq])

private lemma finite_optionMaps_supportedOn
    {Object Partner : Type*} (objectsToMatch : Finset Object) (availablePartners : Finset Partner) :
    {f : Partner → Option Object |
      (∀ q, q ∉ availablePartners → f q = none) ∧
      (∀ q p, f q = some p → p ∈ objectsToMatch)}.Finite := by
  classical
  let PartnerLabel := {q : Partner // q ∈ availablePartners}
  let ObjectLabel := {p : Object // p ∈ objectsToMatch}
  let _ : Finite PartnerLabel := availablePartners.finite_toSet.to_subtype
  let _ : Finite ObjectLabel := objectsToMatch.finite_toSet.to_subtype
  let S : Set (Partner → Option Object) :=
    {f | (∀ q, q ∉ availablePartners → f q = none) ∧
      (∀ q p, f q = some p → p ∈ objectsToMatch)}
  let code : S → (PartnerLabel → Option ObjectLabel) := fun f q =>
    match h : f.1 q.1 with
    | none => none
    | some p => some ⟨p, f.2.2 q.1 p h⟩
  have hdecode (f : S) (q : PartnerLabel) :
      Option.map Subtype.val (code f q) = f.1 q.1 := by
    simp only [code]
    split <;> rename_i h
    · exact h.symm
    · simp only [Option.map_some]
      exact h.symm
  have hcode : Function.Injective code := by
    intro f g hfg
    apply Subtype.ext
    funext q
    by_cases hq : q ∈ availablePartners
    · rw [← hdecode f ⟨q, hq⟩, ← hdecode g ⟨q, hq⟩,
        congrFun hfg ⟨q, hq⟩]
    · rw [f.2.1 q hq, g.2.1 q hq]
  let _ : Finite (PartnerLabel → Option ObjectLabel) := inferInstance
  let _ : Finite S := Finite.of_injective code hcode
  exact Set.finite_coe_iff.mp inferInstance

omit [MeasurableSpace Ω] in
/-- The complete guarded inverse match has countable actual range when its
random finite object and partner populations have countable actual ranges.
No countability assumption is placed on the ambient particle type. -/
theorem preimageByRank_function_range_countable
    {Particle : Type*} [LinearOrder Particle] [LinearOrder Value]
    (objectOrderKey partnerOrderKey : Ω → Particle → Value)
    (objectsToMatch availablePartners : Ω → Finset Particle)
    (hobjectsToMatchRange : (Set.range objectsToMatch).Countable)
    (havailablePartnersRange : (Set.range availablePartners).Countable) :
    (Set.range fun ω q => objectAtPartnerRankBy (objectOrderKey ω) (partnerOrderKey ω)
      (objectsToMatch ω) (availablePartners ω) q).Countable := by
  let S : Set (Finset Particle) := Set.range objectsToMatch
  let T : Set (Finset Particle) := Set.range availablePartners
  let _ : Countable S := Set.countable_coe_iff.mpr hobjectsToMatchRange
  let _ : Countable T := Set.countable_coe_iff.mpr havailablePartnersRange
  let valid (s : S) (t : T) : Set (Particle → Option Particle) :=
    {f | (∀ q, q ∉ t.1 → f q = none) ∧
      (∀ q p, f q = some p → p ∈ s.1)}
  have hvalid : ∀ s t, (valid s t).Countable := by
    intro s t
    exact (finite_optionMaps_supportedOn s.1 t.1).countable
  have hall : (⋃ s : S, ⋃ t : T, valid s t).Countable :=
    Set.countable_iUnion fun s => Set.countable_iUnion fun t => hvalid s t
  apply hall.mono
  rintro f ⟨ω, rfl⟩
  apply Set.mem_iUnion_of_mem
    (⟨objectsToMatch ω, Set.mem_range_self ω⟩ : S)
  apply Set.mem_iUnion_of_mem
    (⟨availablePartners ω, Set.mem_range_self ω⟩ : T)
  constructor
  · intro q hq
    simp [objectAtPartnerRankBy, hq]
  · intro q p hp
    exact (objectAtPartnerRankBy_eq_some_iff.mp hp).2.1

omit [MeasurableSpace Ω] in
/-- For a fixed objectsToMatch label, the total equal-rank match has countable actual
range whenever the random available-partner population has countable actual range. -/
theorem matchByRankOrSelf_range_countable
    {Particle : Type*} [LinearOrder Particle] [LinearOrder Value]
    (objectOrderKey partnerOrderKey : Ω → Particle → Value)
    (objectsToMatch availablePartners : Ω → Finset Particle)
    (hcard : ∀ ω, (objectsToMatch ω).card ≤ (availablePartners ω).card)
    (havailablePartnersRange : (Set.range availablePartners).Countable) (p : Particle) :
    (Set.range fun ω =>
      matchByRankOrSelf (objectOrderKey ω) (partnerOrderKey ω)
        (objectsToMatch ω) (availablePartners ω) (hcard ω) p).Countable := by
  let S : Set (Finset Particle) := Set.range availablePartners
  let _ : Countable S := Set.countable_coe_iff.mpr havailablePartnersRange
  have partnerOptions : (⋃ s : S, (↑s.1 : Set Particle)).Countable :=
    Set.countable_iUnion fun s : S => s.1.countable_toSet
  apply (Set.countable_singleton p).union partnerOptions |>.mono
  rintro q ⟨ω, rfl⟩
  by_cases hp : p ∈ objectsToMatch ω
  · apply Set.mem_union_right
    apply Set.mem_iUnion_of_mem
      (⟨availablePartners ω, Set.mem_range_self ω⟩ : S)
    exact matchByRankOrSelf_mem (objectOrderKey ω) (partnerOrderKey ω)
      (objectsToMatch ω) (availablePartners ω) (hcard ω) hp
  · exact Set.mem_union_left _ (by simp [matchByRankOrSelf, hp])

/-- The fibre of the availablePartners particle having the same dynamic rank as a fixed
objectsToMatch particle is measurable.  Countability is confined to the actual
ranges of the two random finite candidate sets. -/
theorem measurableSet_partnerAtObjectRankBy_eq_some
    {Object Partner : Type*}
    [LinearOrder Object] [LinearOrder Partner] [LinearOrder Value]
    (objectOrderKey : Ω → Object → Value)
    (partnerOrderKey : Ω → Partner → Value)
    (objectsToMatch : Ω → Finset Object) (availablePartners : Ω → Finset Partner)
    (hobjectsToMatchFiber : ∀ s, MeasurableSet {ω | objectsToMatch ω = s})
    (hobjectsToMatchRange : (Set.range objectsToMatch).Countable)
    (havailablePartnersFiber : ∀ s, MeasurableSet {ω | availablePartners ω = s})
    (havailablePartnersRange : (Set.range availablePartners).Countable)
    (hobjectOrderKeyMeasurable : ∀ p q : Object, Measurable fun ω =>
      valueKey (objectOrderKey ω) q < valueKey (objectOrderKey ω) p)
    (hpartnerOrderKeyMeasurable : ∀ p q : Partner, Measurable fun ω =>
      valueKey (partnerOrderKey ω) q < valueKey (partnerOrderKey ω) p)
    (p : Object) (q : Partner) :
    MeasurableSet {ω |
      partnerAtObjectRankBy (objectOrderKey ω) (partnerOrderKey ω)
        (objectsToMatch ω) (availablePartners ω) p = some q} := by
  exact measurableSet_particleAtRankBy_randomRank_eq_some
    partnerOrderKey availablePartners havailablePartnersFiber havailablePartnersRange hpartnerOrderKeyMeasurable
    (fun ω => rankBy (objectOrderKey ω) (objectsToMatch ω) p)
    (measurable_rankBy objectOrderKey objectsToMatch p hobjectsToMatchFiber hobjectsToMatchRange
      (hobjectOrderKeyMeasurable p)) q

/-- Every optional equal-rank lookup fibre is measurable. -/
private theorem measurableSet_partnerAtObjectRankBy_eq
    {Object Partner : Type*}
    [LinearOrder Object] [LinearOrder Partner] [LinearOrder Value]
    (objectOrderKey : Ω → Object → Value)
    (partnerOrderKey : Ω → Partner → Value)
    (objectsToMatch : Ω → Finset Object) (availablePartners : Ω → Finset Partner)
    (hobjectsToMatchFiber : ∀ s, MeasurableSet {ω | objectsToMatch ω = s})
    (hobjectsToMatchRange : (Set.range objectsToMatch).Countable)
    (havailablePartnersFiber : ∀ s, MeasurableSet {ω | availablePartners ω = s})
    (havailablePartnersRange : (Set.range availablePartners).Countable)
    (hobjectOrderKeyMeasurable : ∀ p q : Object, Measurable fun ω =>
      valueKey (objectOrderKey ω) q < valueKey (objectOrderKey ω) p)
    (hpartnerOrderKeyMeasurable : ∀ p q : Partner, Measurable fun ω =>
      valueKey (partnerOrderKey ω) q < valueKey (partnerOrderKey ω) p)
    (p : Object) (o : Option Partner) :
    MeasurableSet {ω |
      partnerAtObjectRankBy (objectOrderKey ω) (partnerOrderKey ω)
        (objectsToMatch ω) (availablePartners ω) p = o} := by
  cases o with
  | some q =>
      exact measurableSet_partnerAtObjectRankBy_eq_some
        objectOrderKey partnerOrderKey objectsToMatch availablePartners hobjectsToMatchFiber hobjectsToMatchRange
        havailablePartnersFiber havailablePartnersRange hobjectOrderKeyMeasurable hpartnerOrderKeyMeasurable p q
  | none =>
      exact measurableSet_particleAtRankBy_randomRank_eq_none
        partnerOrderKey availablePartners havailablePartnersFiber havailablePartnersRange
        (fun ω => rankBy (objectOrderKey ω) (objectsToMatch ω) p)
        (measurable_rankBy objectOrderKey objectsToMatch p hobjectsToMatchFiber hobjectsToMatchRange
          (hobjectOrderKeyMeasurable p))

/-- Every fibre of the guarded inverse rank match is measurable. -/
private theorem measurableSet_preimageByRank_eq
    {Particle : Type*} [LinearOrder Particle] [LinearOrder Value]
    (objectOrderKey partnerOrderKey : Ω → Particle → Value)
    (objectsToMatch availablePartners : Ω → Finset Particle)
    (hobjectsToMatchFiber : ∀ s, MeasurableSet {ω | objectsToMatch ω = s})
    (hobjectsToMatchRange : (Set.range objectsToMatch).Countable)
    (havailablePartnersFiber : ∀ s, MeasurableSet {ω | availablePartners ω = s})
    (havailablePartnersRange : (Set.range availablePartners).Countable)
    (hobjectOrderKeyMeasurable : ∀ p q : Particle, Measurable fun ω =>
      valueKey (objectOrderKey ω) q < valueKey (objectOrderKey ω) p)
    (hpartnerOrderKeyMeasurable : ∀ p q : Particle, Measurable fun ω =>
      valueKey (partnerOrderKey ω) q < valueKey (partnerOrderKey ω) p)
    (q : Particle) (o : Option Particle) :
    MeasurableSet {ω | objectAtPartnerRankBy (objectOrderKey ω) (partnerOrderKey ω)
      (objectsToMatch ω) (availablePartners ω) q = o} := by
  have hmem : MeasurableSet {ω | q ∈ availablePartners ω} :=
    measurableSet_mem_finset availablePartners havailablePartnersFiber havailablePartnersRange q
  have hlookup : ∀ o, MeasurableSet {ω |
      partnerAtObjectRankBy (partnerOrderKey ω) (objectOrderKey ω)
        (availablePartners ω) (objectsToMatch ω) q = o} :=
    measurableSet_partnerAtObjectRankBy_eq partnerOrderKey objectOrderKey
      availablePartners objectsToMatch havailablePartnersFiber havailablePartnersRange hobjectsToMatchFiber hobjectsToMatchRange
      hpartnerOrderKeyMeasurable hobjectOrderKeyMeasurable q
  cases o with
  | some p =>
      have hset : {ω | objectAtPartnerRankBy (objectOrderKey ω) (partnerOrderKey ω)
          (objectsToMatch ω) (availablePartners ω) q = some p} =
          {ω | q ∈ availablePartners ω} ∩ {ω |
            partnerAtObjectRankBy (partnerOrderKey ω) (objectOrderKey ω)
              (availablePartners ω) (objectsToMatch ω) q = some p} := by
        ext ω
        by_cases hq : q ∈ availablePartners ω <;> simp [objectAtPartnerRankBy, hq]
      rw [hset]
      exact hmem.inter (hlookup (some p))
  | none =>
      have hset : {ω | objectAtPartnerRankBy (objectOrderKey ω) (partnerOrderKey ω)
          (objectsToMatch ω) (availablePartners ω) q = none} =
          {ω | q ∈ availablePartners ω}ᶜ ∪
            ({ω | q ∈ availablePartners ω} ∩ {ω |
              partnerAtObjectRankBy (partnerOrderKey ω) (objectOrderKey ω)
                (availablePartners ω) (objectsToMatch ω) q = none}) := by
        ext ω
        by_cases hq : q ∈ availablePartners ω <;> simp [objectAtPartnerRankBy, hq]
      rw [hset]
      exact hmem.compl.union (hmem.inter (hlookup none))

/-- Every fibre of the complete guarded inverse function is measurable.
Function equality is checked only on the finite random availablePartners support; off
that support both sides are forced to be `none`. -/
theorem measurableSet_preimageByRank_function_eq
    {Particle : Type*} [LinearOrder Particle] [LinearOrder Value]
    (objectOrderKey partnerOrderKey : Ω → Particle → Value)
    (objectsToMatch availablePartners : Ω → Finset Particle)
    (hobjectsToMatchFiber : ∀ s, MeasurableSet {ω | objectsToMatch ω = s})
    (hobjectsToMatchRange : (Set.range objectsToMatch).Countable)
    (havailablePartnersFiber : ∀ s, MeasurableSet {ω | availablePartners ω = s})
    (havailablePartnersRange : (Set.range availablePartners).Countable)
    (hobjectOrderKeyMeasurable : ∀ p q : Particle, Measurable fun ω =>
      valueKey (objectOrderKey ω) q < valueKey (objectOrderKey ω) p)
    (hpartnerOrderKeyMeasurable : ∀ p q : Particle, Measurable fun ω =>
      valueKey (partnerOrderKey ω) q < valueKey (partnerOrderKey ω) p)
    (f : Particle → Option Particle) :
    MeasurableSet {ω | (fun q => objectAtPartnerRankBy
      (objectOrderKey ω) (partnerOrderKey ω) (objectsToMatch ω) (availablePartners ω) q) = f} := by
  let T : Set (Finset Particle) := Set.range availablePartners
  let _ : Countable T := Set.countable_coe_iff.mpr havailablePartnersRange
  let U := {t : T // ∀ q, q ∉ t.1 → f q = none}
  have hset : {ω | (fun q => objectAtPartnerRankBy
      (objectOrderKey ω) (partnerOrderKey ω) (objectsToMatch ω) (availablePartners ω) q) = f} =
      ⋃ t : U, {ω | availablePartners ω = t.1.1} ∩
        ⋂ q : {q : Particle // q ∈ t.1.1},
          {ω | objectAtPartnerRankBy (objectOrderKey ω) (partnerOrderKey ω)
            (objectsToMatch ω) (availablePartners ω) q.1 = f q.1} := by
    ext ω
    constructor
    · intro h
      have hout : ∀ q, q ∉ availablePartners ω → f q = none := by
        intro q hq
        rw [← congrFun h q]
        simp [objectAtPartnerRankBy, hq]
      let t : U := ⟨⟨availablePartners ω, Set.mem_range_self ω⟩, hout⟩
      apply Set.mem_iUnion_of_mem t
      constructor
      · rfl
      · simp only [Set.mem_iInter, Set.mem_ofPred_eq]
        intro q
        exact congrFun h q.1
    · intro h
      obtain ⟨t, havailablePartners, hcoords⟩ := Set.mem_iUnion.mp h
      simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hcoords
      funext q
      by_cases hq : q ∈ t.1.1
      · exact hcoords ⟨q, hq⟩
      · have hq' : q ∉ availablePartners ω := by
          rw [havailablePartners]
          exact hq
        rw [t.2 q hq]
        simp [objectAtPartnerRankBy, hq']
  rw [hset]
  apply MeasurableSet.iUnion
  intro t
  apply (havailablePartnersFiber t.1.1).inter
  apply MeasurableSet.iInter
  intro q
  exact measurableSet_preimageByRank_eq objectOrderKey partnerOrderKey objectsToMatch availablePartners
    hobjectsToMatchFiber hobjectsToMatchRange havailablePartnersFiber havailablePartnersRange hobjectOrderKeyMeasurable hpartnerOrderKeyMeasurable
    q.1 (f q.1)

/-- Install objectsToMatch values at availablePartners labels of the same dynamic rank; availablePartners
labels beyond the objectsToMatch rank range retain their fallback values. -/
noncomputable def valueAtMatchedRank
    {Particle Y : Type*} [LinearOrder Particle] [LinearOrder Value]
    (objectOrderKey partnerOrderKey : Ω → Particle → Value)
    (objectsToMatch availablePartners : Ω → Finset Particle)
    (objectData fallback : Ω → Particle → Y)
    (ω : Ω) (q : Particle) : Y :=
  Coupling.valueAtObjectPreimage objectData fallback
    (fun sample partnerParticle =>
      objectAtPartnerRankBy (objectOrderKey sample) (partnerOrderKey sample)
        (objectsToMatch sample) (availablePartners sample) partnerParticle) ω q

omit [MeasurableSpace Ω] in
/-- Object data is recovered exactly at every canonically matched availablePartners. -/
theorem valueAtMatchedRank_matchByRankOrSelf
    {Particle Y : Type*} [LinearOrder Particle] [LinearOrder Value]
    (objectOrderKey partnerOrderKey : Ω → Particle → Value)
    (objectsToMatch availablePartners : Ω → Finset Particle)
    (ω : Ω) (hcard : (objectsToMatch ω).card ≤ (availablePartners ω).card)
    (objectData fallback : Ω → Particle → Y)
    {p : Particle} (hp : p ∈ objectsToMatch ω) :
    valueAtMatchedRank objectOrderKey partnerOrderKey objectsToMatch availablePartners objectData fallback
        ω (matchByRankOrSelf (objectOrderKey ω) (partnerOrderKey ω)
          (objectsToMatch ω) (availablePartners ω) hcard p) =
      objectData ω p := by
  have havailablePartners := matchByRankOrSelf_mem
    (objectOrderKey ω) (partnerOrderKey ω) (objectsToMatch ω) (availablePartners ω) hcard hp
  simp [valueAtMatchedRank, Coupling.valueAtObjectPreimage,
    objectAtPartnerRankBy, havailablePartners,
    partnerAtObjectRankBy_matchByRankOrSelf
      (objectOrderKey ω) (partnerOrderKey ω) (objectsToMatch ω) (availablePartners ω) hcard hp]

/-- Rank-matched installation is measurable as a whole availablePartners-indexed
family.  Countability concerns only the actual random finite populations. -/
theorem valueAtMatchedRank_measurable
    {Particle Y : Type*} [LinearOrder Particle] [LinearOrder Value]
    [MeasurableSpace Y]
    (objectOrderKey partnerOrderKey : Ω → Particle → Value)
    (objectsToMatch availablePartners : Ω → Finset Particle)
    (objectData fallback : Ω → Particle → Y)
    (hobjectsToMatchFiber : ∀ s, MeasurableSet {ω | objectsToMatch ω = s})
    (hobjectsToMatchRange : (Set.range objectsToMatch).Countable)
    (havailablePartnersFiber : ∀ s, MeasurableSet {ω | availablePartners ω = s})
    (havailablePartnersRange : (Set.range availablePartners).Countable)
    (hobjectOrderKeyMeasurable : ∀ p q : Particle, Measurable fun ω =>
      valueKey (objectOrderKey ω) q < valueKey (objectOrderKey ω) p)
    (hpartnerOrderKeyMeasurable : ∀ p q : Particle, Measurable fun ω =>
      valueKey (partnerOrderKey ω) q < valueKey (partnerOrderKey ω) p)
    (hobjectData : ∀ p, Measurable fun ω => objectData ω p)
    (hfallback : ∀ q, Measurable fun ω => fallback ω q) :
    Measurable fun ω q =>
      valueAtMatchedRank objectOrderKey partnerOrderKey objectsToMatch availablePartners
        objectData fallback ω q := by
  apply measurable_pi_iff.mpr
  intro q
  let pre : Ω → Option Particle := fun ω =>
    objectAtPartnerRankBy (objectOrderKey ω) (partnerOrderKey ω)
      (objectsToMatch ω) (availablePartners ω) q
  let field : Ω → Option Particle → Y := fun ω o =>
    o.elim (fallback ω q) (objectData ω)
  have hfield : Measurable (fun ω => field ω (pre ω)) := by
    apply Measurable.eval_of_countable_range field pre
    · intro o _
      cases o with
      | none => simpa [field] using hfallback q
      | some p => simpa [field] using hobjectData p
    · intro o _
      exact measurableSet_preimageByRank_eq objectOrderKey partnerOrderKey
        objectsToMatch availablePartners hobjectsToMatchFiber hobjectsToMatchRange havailablePartnersFiber havailablePartnersRange
        hobjectOrderKeyMeasurable hpartnerOrderKeyMeasurable q o
    · exact preimageByRank_range_countable objectOrderKey partnerOrderKey
        objectsToMatch availablePartners hobjectsToMatchRange q
  simpa [valueAtMatchedRank, Coupling.valueAtObjectPreimage, pre, field] using hfield

end ProbabilityTheory.BranchingRandomWalk.Coupling
