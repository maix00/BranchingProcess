/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Coupling.Rank.Preimage
public import Combinatorics.BranchingWalk.Step.Map

/-!
# Rank-installed step fields

The deterministic rank-installed StepField, its pointwise identities, and
measurability under finite-support hypotheses.

## Public declarations

Installing object steps by equal dynamic rank recovers the object step at
each canonical match:

\[
p\in\operatorname{objectsToMatch}(\omega),\quad
|\operatorname{objectsToMatch}(\omega)|\le|\operatorname{availablePartners}(\omega)|
\Longrightarrow
\operatorname{rankInstalledStepField}(\omega)
  (\operatorname{matchByRankOrSelf}(p))
=\operatorname{objectStep}(\omega,p).
\]

* `RootIndexed.rankInstalledStepField` installs each object step at the
  partner node of equal dynamic rank and leaves unmatched partner steps at
  their fallback values.
* `RootIndexed.rankInstalledStepField_matchByRankOrSelf` states that the
  installed field recovers the object step at every canonical equal-rank
  match.
* `RootIndexed.rankInstalledStepField_measurable` proves measurability of
  the installed field from measurable support fibres, rank comparisons, and
  object/fallback steps.
* `RootIndexed.reindexedSteps_matchByRankOrSelf_measurable` proves
  measurability in the generation domain flow of the step family read through
  the canonical equal-rank matching.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Coupling

open MeasureTheory
open Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection
open Combinatorics.UlamHarris

variable {Ω Value : Type*} [MeasurableSpace Ω]

/-- Install the step of each object particle at the partner particle of the
same dynamic rank. Partner particles outside the object rank range retain
their fallback step. -/
noncomputable def RootIndexed.rankInstalledStepField
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (objectOrderKey partnerOrderKey : Ω → RootIndexed.TreeNode Root α → Value)
    (objectsToMatch availablePartners : Ω → Finset (RootIndexed.TreeNode Root α))
    (objectStep fallback : Ω → RootIndexed.StepField Root α X)
    (ω : Ω) : RootIndexed.StepField Root α X :=
  fun r u => valueAtMatchedRank objectOrderKey partnerOrderKey objectsToMatch availablePartners
    (fun sample p => objectStep sample p.1 p.2)
    (fun sample q => fallback sample q.1 q.2) ω (r, u)

omit [MeasurableSpace Ω] in
/-- At every canonical equal-rank match, `rankInstalledStepField` contains the
corresponding object step. -/
theorem RootIndexed.rankInstalledStepField_matchByRankOrSelf
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (objectOrderKey partnerOrderKey : Ω → RootIndexed.TreeNode Root α → Value)
    (objectsToMatch availablePartners : Ω → Finset (RootIndexed.TreeNode Root α))
    (ω : Ω) (hcard : (objectsToMatch ω).card ≤ (availablePartners ω).card)
    (objectStep fallback : Ω → RootIndexed.StepField Root α X)
    {p : RootIndexed.TreeNode Root α} (hp : p ∈ objectsToMatch ω) :
    RootIndexed.rankInstalledStepField objectOrderKey partnerOrderKey objectsToMatch availablePartners
        objectStep fallback ω
        (matchByRankOrSelf (objectOrderKey ω) (partnerOrderKey ω)
          (objectsToMatch ω) (availablePartners ω) hcard p).1
        (matchByRankOrSelf (objectOrderKey ω) (partnerOrderKey ω)
          (objectsToMatch ω) (availablePartners ω) hcard p).2 =
      objectStep ω p.1 p.2 := by
  exact valueAtMatchedRank_matchByRankOrSelf objectOrderKey partnerOrderKey
    objectsToMatch availablePartners ω hcard
    (fun sample q => objectStep sample q.1 q.2)
    (fun sample q => fallback sample q.1 q.2) hp

omit [MeasurableSpace Ω] in
private theorem RootIndexed.survive_rankInstalledStepField_matchByRankOrSelf
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (objectOrderKey partnerOrderKey : Ω → RootIndexed.TreeNode Root α → Value)
    (objectsToMatch availablePartners : Ω → Finset (RootIndexed.TreeNode Root α))
    (ω : Ω) (hcard : (objectsToMatch ω).card ≤ (availablePartners ω).card)
    (objectStep fallback : Ω → RootIndexed.StepField Root α X)
    {p : RootIndexed.TreeNode Root α} (hp : p ∈ objectsToMatch ω)
    (i : α) :
    survive (RootIndexed.rankInstalledStepField objectOrderKey partnerOrderKey objectsToMatch availablePartners
      objectStep fallback ω
      (matchByRankOrSelf (objectOrderKey ω) (partnerOrderKey ω)
        (objectsToMatch ω) (availablePartners ω) hcard p).1
      (matchByRankOrSelf (objectOrderKey ω) (partnerOrderKey ω)
        (objectsToMatch ω) (availablePartners ω) hcard p).2) i =
      survive (objectStep ω p.1 p.2) i := by
  rw [RootIndexed.rankInstalledStepField_matchByRankOrSelf objectOrderKey partnerOrderKey
    objectsToMatch availablePartners ω hcard objectStep fallback hp]

omit [MeasurableSpace Ω] in
private theorem RootIndexed.value'_map_rankInstalledStepField_matchByRankOrSelf
    {Root α X Position Value : Type*}
    [Zero Position]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (objectOrderKey partnerOrderKey : Ω → RootIndexed.TreeNode Root α → Value)
    (objectsToMatch availablePartners : Ω → Finset (RootIndexed.TreeNode Root α))
    (ω : Ω) (hcard : (objectsToMatch ω).card ≤ (availablePartners ω).card)
    (objectStep fallback : Ω → RootIndexed.StepField Root α X)
    (d : X → Position)
    {p : RootIndexed.TreeNode Root α} (hp : p ∈ objectsToMatch ω) (i : α) :
    value' ((RootIndexed.rankInstalledStepField objectOrderKey partnerOrderKey objectsToMatch availablePartners
      objectStep fallback ω
      (matchByRankOrSelf (objectOrderKey ω) (partnerOrderKey ω)
        (objectsToMatch ω) (availablePartners ω) hcard p).1
      (matchByRankOrSelf (objectOrderKey ω) (partnerOrderKey ω)
        (objectsToMatch ω) (availablePartners ω) hcard p).2).map d) i =
      value' ((objectStep ω p.1 p.2).map d) i := by
  rw [RootIndexed.rankInstalledStepField_matchByRankOrSelf objectOrderKey partnerOrderKey
    objectsToMatch availablePartners ω hcard objectStep fallback hp]

/-- The field obtained by installing object steps at equal-rank partner
particles is measurable. Countability is required only for the actual
random finite populations used to compute the ranks. -/
theorem RootIndexed.rankInstalledStepField_measurable
    {Root α X Value : Type*} [MeasurableSpace X]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (objectOrderKey partnerOrderKey : Ω → RootIndexed.TreeNode Root α → Value)
    (objectsToMatch availablePartners : Ω → Finset (RootIndexed.TreeNode Root α))
    (objectStep fallback : Ω → RootIndexed.StepField Root α X)
    (hobjectsToMatchFiber : ∀ s, MeasurableSet {ω | objectsToMatch ω = s})
    (hobjectsToMatchRange : (Set.range objectsToMatch).Countable)
    (havailablePartnersFiber : ∀ s, MeasurableSet {ω | availablePartners ω = s})
    (havailablePartnersRange : (Set.range availablePartners).Countable)
    (hobjectOrderKeyMeasurable : ∀ p q, Measurable fun ω =>
      valueKey (objectOrderKey ω) q < valueKey (objectOrderKey ω) p)
    (hpartnerOrderKeyMeasurable : ∀ p q, Measurable fun ω =>
      valueKey (partnerOrderKey ω) q < valueKey (partnerOrderKey ω) p)
    (hobjectStep : ∀ p : RootIndexed.TreeNode Root α,
      Measurable fun ω => objectStep ω p.1 p.2)
    (hfallback : ∀ q : RootIndexed.TreeNode Root α,
      Measurable fun ω => fallback ω q.1 q.2) :
    Measurable fun ω => RootIndexed.rankInstalledStepField objectOrderKey partnerOrderKey
      objectsToMatch availablePartners objectStep fallback ω := by
  have h := valueAtMatchedRank_measurable objectOrderKey partnerOrderKey objectsToMatch availablePartners
    (fun sample p => objectStep sample p.1 p.2)
    (fun sample q => fallback sample q.1 q.2)
    hobjectsToMatchFiber hobjectsToMatchRange havailablePartnersFiber havailablePartnersRange
    hobjectOrderKeyMeasurable hpartnerOrderKeyMeasurable hobjectStep hfallback
  apply measurable_pi_iff.mpr
  intro r
  apply measurable_pi_iff.mpr
  intro u
  exact (measurable_pi_apply (r, u)).comp h

/-- Every fibre of the total equal-rank match is measurable. Outside the
object population the total map fixes the particle label. -/
private theorem measurableSet_matchByRankOrSelf_eq
    {Particle : Type*} [LinearOrder Particle] [LinearOrder Value]
    (objectOrderKey partnerOrderKey : Ω → Particle → Value)
    (objectsToMatch availablePartners : Ω → Finset Particle)
    (hcard : ∀ ω, (objectsToMatch ω).card ≤ (availablePartners ω).card)
    (hobjectsToMatchFiber : ∀ s, MeasurableSet {ω | objectsToMatch ω = s})
    (hobjectsToMatchRange : (Set.range objectsToMatch).Countable)
    (havailablePartnersFiber : ∀ s, MeasurableSet {ω | availablePartners ω = s})
    (havailablePartnersRange : (Set.range availablePartners).Countable)
    (hobjectOrderKeyMeasurable : ∀ p q : Particle, Measurable fun ω =>
      valueKey (objectOrderKey ω) q < valueKey (objectOrderKey ω) p)
    (hpartnerOrderKeyMeasurable : ∀ p q : Particle, Measurable fun ω =>
      valueKey (partnerOrderKey ω) q < valueKey (partnerOrderKey ω) p)
    (p q : Particle) :
    MeasurableSet {ω |
      matchByRankOrSelf (objectOrderKey ω) (partnerOrderKey ω)
        (objectsToMatch ω) (availablePartners ω) (hcard ω) p = q} := by
  let objectsToMatchMem : Set Ω := {ω | p ∈ objectsToMatch ω}
  let matched : Set Ω := {ω |
    partnerAtObjectRankBy (objectOrderKey ω) (partnerOrderKey ω)
      (objectsToMatch ω) (availablePartners ω) p = some q}
  have hobjectsToMatchMem : MeasurableSet objectsToMatchMem :=
    measurableSet_mem_candidates objectsToMatch hobjectsToMatchFiber hobjectsToMatchRange p
  have hmatched : MeasurableSet matched :=
    measurableSet_partnerAtObjectRankBy_eq_some objectOrderKey partnerOrderKey
      objectsToMatch availablePartners hobjectsToMatchFiber hobjectsToMatchRange havailablePartnersFiber havailablePartnersRange
      hobjectOrderKeyMeasurable hpartnerOrderKeyMeasurable p q
  by_cases hpq : p = q
  · have hset : {ω |
        matchByRankOrSelf (objectOrderKey ω) (partnerOrderKey ω)
          (objectsToMatch ω) (availablePartners ω) (hcard ω) p = q} =
        (objectsToMatchMem ∩ matched) ∪ objectsToMatchMemᶜ := by
      ext ω
      subst q
      by_cases hp : p ∈ objectsToMatch ω
      · have hsome := partnerAtObjectRankBy_matchByRank
          (objectOrderKey ω) (partnerOrderKey ω) (objectsToMatch ω) (availablePartners ω)
          (hcard ω) p hp
        simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff,
          Set.mem_ofPred_eq, objectsToMatchMem, matched]
        rw [matchByRankOrSelf_of_mem _ _ _ _ _ hp]
        constructor
        · intro h
          exact Or.inl ⟨hp, hsome.trans (congrArg some h)⟩
        · rintro (⟨_, h⟩ | hnot)
          · exact Option.some.inj (hsome.symm.trans h)
          · exact (hnot hp).elim
      · simp [objectsToMatchMem, matched, hp]
    rw [hset]
    exact (hobjectsToMatchMem.inter hmatched).union hobjectsToMatchMem.compl
  · have hset : {ω |
        matchByRankOrSelf (objectOrderKey ω) (partnerOrderKey ω)
          (objectsToMatch ω) (availablePartners ω) (hcard ω) p = q} =
        objectsToMatchMem ∩ matched := by
      ext ω
      by_cases hp : p ∈ objectsToMatch ω
      · have hsome := partnerAtObjectRankBy_matchByRank
          (objectOrderKey ω) (partnerOrderKey ω) (objectsToMatch ω) (availablePartners ω)
          (hcard ω) p hp
        simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, objectsToMatchMem, matched]
        rw [matchByRankOrSelf_of_mem _ _ _ _ _ hp]
        constructor
        · intro h
          exact ⟨hp, hsome.trans (congrArg some h)⟩
        · rintro ⟨_, h⟩
          exact Option.some.inj (hsome.symm.trans h)
      · simp [objectsToMatchMem, matched, hp, hpq]
    rw [hset]
    exact hobjectsToMatchMem.inter hmatched

/-- The partner-step family read through canonical equal-rank matching is
measurable in the generation domain flow.  The root and child-slot types are
unrestricted; all countability assumptions concern actual random ranges. -/
theorem RootIndexed.reindexedSteps_matchByRankOrSelf_measurable
    {Root α X Value : Type*} [MeasurableSpace X]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value] {n : ℕ}
    (objectOrderKey partnerOrderKey :
      BranchingRandomWalk.RootIndexed.StepField Root α X →
        RootIndexed.TreeNode Root α → Value)
    (objectsToMatch availablePartners : BranchingRandomWalk.RootIndexed.StepField Root α X →
      Finset (RootIndexed.TreeNode Root α))
    (hcard : ∀ ω, (objectsToMatch ω).card ≤ (availablePartners ω).card)
    (hobjectsToMatchFiber : ∀ s,
      MeasurableSet[BranchingRandomWalk.RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X) n] {ω | objectsToMatch ω = s})
    (hobjectsToMatchRange : (Set.range objectsToMatch).Countable)
    (havailablePartnersFiber : ∀ s,
      MeasurableSet[BranchingRandomWalk.RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X) n] {ω | availablePartners ω = s})
    (havailablePartnersRange : (Set.range availablePartners).Countable)
    (hobjectOrderKeyMeasurable : ∀ p q,
      Measurable[BranchingRandomWalk.RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X) n] fun ω =>
        valueKey (objectOrderKey ω) q < valueKey (objectOrderKey ω) p)
    (hpartnerOrderKeyMeasurable : ∀ p q,
      Measurable[BranchingRandomWalk.RootIndexed.stepFiltration
        (Root := Root) (α := α) (X := X) n] fun ω =>
        valueKey (partnerOrderKey ω) q < valueKey (partnerOrderKey ω) p)
    (hdepth : ∀ ω p,
      (matchByRankOrSelf (objectOrderKey ω) (partnerOrderKey ω)
        (objectsToMatch ω) (availablePartners ω) (hcard ω) p).2.length < n) :
    Measurable[BranchingRandomWalk.RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n]
      (Coupling.RootIndexed.reindexedSteps fun ω p =>
        matchByRankOrSelf (objectOrderKey ω) (partnerOrderKey ω)
          (objectsToMatch ω) (availablePartners ω) (hcard ω) p) := by
  let _ : MeasurableSpace
      (BranchingRandomWalk.RootIndexed.StepField Root α X) :=
    BranchingRandomWalk.RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n
  apply Coupling.RootIndexed.reindexedSteps_measurable
  · intro p
    exact matchByRankOrSelf_range_countable objectOrderKey partnerOrderKey
      objectsToMatch availablePartners hcard havailablePartnersRange p
  · intro p q
    exact measurableSet_matchByRankOrSelf_eq objectOrderKey partnerOrderKey
      objectsToMatch availablePartners hcard hobjectsToMatchFiber hobjectsToMatchRange havailablePartnersFiber havailablePartnersRange
      hobjectOrderKeyMeasurable hpartnerOrderKeyMeasurable p q
  · exact hdepth

end ProbabilityTheory.BranchingRandomWalk.Coupling
