import Probability.BranchingRandomWalk.Coupling.Rank.Preimage
import Combinatorics.BranchingWalk.Step.Map

/-!
# Rank-installed step fields

The deterministic rank-installed StepField, its pointwise identities, and
measurability under finite-support hypotheses.
-/

namespace ProbabilityTheory.BranchingRandomWalk.Coupling

open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open MeasureTheory
open Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection
open Combinatorics.UlamHarris

variable {Ω Value : Type*} [MeasurableSpace Ω]

/-- Install the step of each source particle at the target particle of the
same dynamic rank.  Target particles outside the source rank range retain
their fallback step. -/
noncomputable def RootIndexed.rankInstalledStepField
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
/-- At every canonical equal-rank match, `rankInstalledStepField` contains exactly
the corresponding source step. -/
theorem RootIndexed.rankInstalledStepField_matchByRankOrSelf
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (sourceValue targetValue : Ω → RootIndexed.TreeNode Root α → Value)
    (source target : Ω → Finset (RootIndexed.TreeNode Root α))
    (ω : Ω) (hcard : (source ω).card ≤ (target ω).card)
    (sourceStep fallback : Ω → RootIndexed.StepField Root α X)
    {p : RootIndexed.TreeNode Root α} (hp : p ∈ source ω) :
    RootIndexed.rankInstalledStepField sourceValue targetValue source target
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
theorem RootIndexed.survive_rankInstalledStepField_matchByRankOrSelf
    {Root α X Value : Type*}
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (sourceValue targetValue : Ω → RootIndexed.TreeNode Root α → Value)
    (source target : Ω → Finset (RootIndexed.TreeNode Root α))
    (ω : Ω) (hcard : (source ω).card ≤ (target ω).card)
    (sourceStep fallback : Ω → RootIndexed.StepField Root α X)
    {p : RootIndexed.TreeNode Root α} (hp : p ∈ source ω)
    (i : α) :
    survive (RootIndexed.rankInstalledStepField sourceValue targetValue source target
      sourceStep fallback ω
      (matchByRankOrSelf (sourceValue ω) (targetValue ω)
        (source ω) (target ω) hcard p).1
      (matchByRankOrSelf (sourceValue ω) (targetValue ω)
        (source ω) (target ω) hcard p).2) i =
      survive (sourceStep ω p.1 p.2) i := by
  rw [RootIndexed.rankInstalledStepField_matchByRankOrSelf sourceValue targetValue
    source target ω hcard sourceStep fallback hp]

omit [MeasurableSpace Ω] in
theorem RootIndexed.value'_map_rankInstalledStepField_matchByRankOrSelf
    {Root α X Position Value : Type*}
    [Zero Position]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (sourceValue targetValue : Ω → RootIndexed.TreeNode Root α → Value)
    (source target : Ω → Finset (RootIndexed.TreeNode Root α))
    (ω : Ω) (hcard : (source ω).card ≤ (target ω).card)
    (sourceStep fallback : Ω → RootIndexed.StepField Root α X)
    (d : X → Position)
    {p : RootIndexed.TreeNode Root α} (hp : p ∈ source ω) (i : α) :
    value' ((RootIndexed.rankInstalledStepField sourceValue targetValue source target
      sourceStep fallback ω
      (matchByRankOrSelf (sourceValue ω) (targetValue ω)
        (source ω) (target ω) hcard p).1
      (matchByRankOrSelf (sourceValue ω) (targetValue ω)
        (source ω) (target ω) hcard p).2).map d) i =
      value' ((sourceStep ω p.1 p.2).map d) i := by
  rw [RootIndexed.rankInstalledStepField_matchByRankOrSelf sourceValue targetValue
    source target ω hcard sourceStep fallback hp]

/-- The field obtained by installing source steps at equal-rank target
particles is measurable.  Countability is required only for the actual
random finite populations used to compute the ranks. -/
theorem RootIndexed.rankInstalledStepField_measurable
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
    Measurable fun ω => RootIndexed.rankInstalledStepField sourceValue targetValue
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
theorem RootIndexed.reindexedSteps_matchByRankOrSelf_measurable
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
      (Coupling.RootIndexed.reindexedSteps fun ω p =>
        matchByRankOrSelf (sourceValue ω) (targetValue ω)
          (source ω) (target ω) (hcard ω) p) := by
  let _ : MeasurableSpace
      (BranchingRandomWalk.RootIndexed.StepField Root α X) :=
    BranchingRandomWalk.RootIndexed.stepFiltration
      (Root := Root) (α := α) (X := X) n
  apply Coupling.RootIndexed.reindexedSteps_measurable
  · intro p
    exact matchByRankOrSelf_range_countable sourceValue targetValue
      source target hcard htargetRange p
  · intro p q
    exact measurableSet_matchByRankOrSelf_eq sourceValue targetValue
      source target hcard hsourceFiber hsourceRange htargetFiber htargetRange
      hsourceKey htargetKey p q
  · exact hdepth

end ProbabilityTheory.BranchingRandomWalk.Coupling
