/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Cloud.Order.Domination
public import Combinatorics.BranchingWalk.Cloud.Order.DynamicSelection
public import Combinatorics.Selection.NSelection.Mechanism.Finite.Threshold
public import Combinatorics.BranchingWalk.Selection.NSelection.Coupling.Step
public import Combinatorics.Selection.NSelection.Mechanism.Finite.AtRank

/-!
# Domination under leftmost selection

The finite counting lemma for `selectFirstN` is lifted here to the existing cloud
orders.  Positions may be abstract; comparison takes place after an ordered
observation `φ`. Equal observed positions retain their distinct particle
identities.

## Public declarations

Let \(C_{\mathrm{o}}\) and \(C_{\mathrm{p}}\) be the object and partner
clouds. Suppose \(C_{\mathrm{o}}\) rankwise dominates \(C_{\mathrm{p}}\), each
retained slice \(R_t\) is a subset of the object-cloud slice with at most
\(N\) particles, and the observed positions are nondecreasing in the address
order on both slices. Write \(C_{\mathrm{p},t}^{[N]}\) for the first \(N\)
addresses of the partner-cloud slice and \(C_{\mathrm{o},R}\) for the object
cloud restricted to \(R_t\). Then the retained object cloud rankwise
dominates the selected partner cloud:

\[C_{\mathrm{o}}\succeq_{\mathrm{rank},\phi}C_{\mathrm{p}},\quad
  R_t\subseteq C_{\mathrm{o},t},\quad |R_t|\le N
  \quad\Longrightarrow\quad
  C_{\mathrm{o},R}\succeq_{\mathrm{rank},\phi}C_{\mathrm{p},t}^{[N]}.\]

In addition, if \(N>0\), each object particle has a selected partner whose
observed position is no larger:

\[N>0,\quad p\in C_{\mathrm{o},t}
  \quad\Longrightarrow\quad
  \exists q\in C_{\mathrm{p},t}^{[N]},\quad
  \phi(\operatorname{position}_{C_{\mathrm{p}}}(q))
  \le\phi(\operatorname{position}_{C_{\mathrm{o}}}(p)).\]

- `Cloud.rankwiseDominatesBy_leftmost_of_subset` proves
  `(objectsToMatchCloud.withFinsetParticles retained).RankwiseDominatesBy φ
  (availablePartnersCloud.withFinsetParticles selectedPartners) t`, where
  `selectedPartners t = selectFirstN N (havailablePartnersFinite t).toFinset`, when each retained slice
  is a subset of `objectsToMatchCloud.particles t` of size at most `N`, `objectsToMatchCloud` rankwise dominates
  `availablePartnersCloud`, and `φ` is monotone along both index orders.
- `Cloud.dominatesBy_leftmost_of_subset` gives the corresponding
  measure-level relation
  `(objectsToMatchCloud.withFinsetParticles retained).DominatesBy φ
  (availablePartnersCloud.withFinsetParticles selectedPartners)` when the particle type is countable and
  observed values have measurable singletons.
- `Cloud.exists_leftmost_le_of_mem` proves
  `∀ p ∈ objectsToMatchCloud.particles t, ∃ q ∈ selectFirstN N (availablePartnersCloud.particles t),
  φ (availablePartnersCloud.position q.1 q.2) ≤ φ (objectsToMatchCloud.position p.1 p.2)` when `N > 0` and `objectsToMatchCloud`
  rankwise dominates `availablePartnersCloud` at `t`.
-/

open Combinatorics.UlamHarris

@[expose] public section

namespace Combinatorics.Branching

open _root_.Combinatorics.Branching.Selection

set_option linter.style.haveILetI false

variable {Time Root α Position Value : Type*}

/-- A retained object subpopulation of size at most `N` dominates the leftmost
`N` partner population whenever the object candidate cloud dominates the
partner candidate cloud. This is the deterministic one-generation core of
the selected-BRW/n-selected-BRW coupling. -/
theorem Cloud.rankwiseDominatesBy_leftmost_of_subset
    [LinearOrder (RootIndexed.TreeNode Root α)] [Preorder Value]
    (φ : Position → Value) (N : ℕ)
    (objectsToMatchCloud availablePartnersCloud : Cloud Time Root α Position)
    (retained : Time → Finset (RootIndexed.TreeNode Root α))
    (hobjectsToMatchFinite : ∀ t, (objectsToMatchCloud.particles t).Finite)
    (havailablePartnersFinite : ∀ t, (availablePartnersCloud.particles t).Finite)
    (hretained : ∀ t, ↑(retained t) ⊆ objectsToMatchCloud.particles t)
    (hcard : ∀ t, (retained t).card ≤ N)
    (hobjectPositionMonotone : ∀ t p, p ∈ objectsToMatchCloud.particles t → ∀ q, q ∈ objectsToMatchCloud.particles t →
      p < q → φ (objectsToMatchCloud.position p.1 p.2) ≤ φ (objectsToMatchCloud.position q.1 q.2))
    (hpartnerPositionMonotone : ∀ t p, p ∈ availablePartnersCloud.particles t → ∀ q, q ∈ availablePartnersCloud.particles t →
      p < q → φ (availablePartnersCloud.position p.1 p.2) ≤ φ (availablePartnersCloud.position q.1 q.2))
    (hobjectCloudDominatesPartnerCloud : ∀ t, objectsToMatchCloud.RankwiseDominatesBy φ availablePartnersCloud t) :
    let selectedPartners := fun t => Selection.NSelection.selectFirstN N (havailablePartnersFinite t).toFinset
    ∀ t, (objectsToMatchCloud.withFinsetParticles retained).RankwiseDominatesBy φ
      (availablePartnersCloud.withFinsetParticles selectedPartners) t := by
  classical
  dsimp only
  intro t
  let objectsToMatch : Finset (RootIndexed.TreeNode Root α) := (hobjectsToMatchFinite t).toFinset
  let availablePartners : Finset (RootIndexed.TreeNode Root α) := (havailablePartnersFinite t).toFinset
  let retainedObjectCloud := (objectsToMatchCloud.withFinsetParticles retained).mapPosition φ
  let selectedPartnerCloud :=
    (availablePartnersCloud.withFinsetParticles (fun u =>
      Selection.NSelection.selectFirstN N (havailablePartnersFinite u).toFinset)).mapPosition φ
  change retainedObjectCloud.RankwiseDominates selectedPartnerCloud t
  have hleftFinite : (retainedObjectCloud.particles t).Finite := by
    simp [retainedObjectCloud]
  have hrightFinite : (selectedPartnerCloud.particles t).Finite := by
    simp [selectedPartnerCloud]
  letI : Fintype (retainedObjectCloud.particles t) := hleftFinite.fintype
  letI : Fintype (selectedPartnerCloud.particles t) := hrightFinite.fintype
  letI : Fintype ↑((objectsToMatchCloud.mapPosition φ).particles t) :=
    (show ((objectsToMatchCloud.mapPosition φ).particles t).Finite by simpa using hobjectsToMatchFinite t).fintype
  letI : Fintype ↑((availablePartnersCloud.mapPosition φ).particles t) :=
    (show ((availablePartnersCloud.mapPosition φ).particles t).Finite by simpa using havailablePartnersFinite t).fintype
  apply Cloud.rankwiseDominates_of_encard_Iic_le t
  · intro p hp q hq hpq
    exact hobjectPositionMonotone t p (hretained t hp) q (hretained t hq) hpq
  · intro p hp q hq hpq
    have hp' : p ∈ Selection.NSelection.selectFirstN N availablePartners := by
      simpa [selectedPartnerCloud, availablePartners] using hp
    have hq' : q ∈ Selection.NSelection.selectFirstN N availablePartners := by
      simpa [selectedPartnerCloud, availablePartners] using hq
    have hpD : p ∈ availablePartnersCloud.particles t := ((havailablePartnersFinite t).mem_toFinset).mp
      (Selection.NSelection.selectFirstN_subset N availablePartners hp')
    have hqD : q ∈ availablePartnersCloud.particles t := ((havailablePartnersFinite t).mem_toFinset).mp
      (Selection.NSelection.selectFirstN_subset N availablePartners hq')
    exact hpartnerPositionMonotone t p hpD q hqD hpq
  · intro a
    have hthreshold : ∀ b : Value,
        (objectsToMatch.filter fun p => φ (objectsToMatchCloud.position p.1 p.2) ≤ b).card ≤
          (availablePartners.filter fun q => φ (availablePartnersCloud.position q.1 q.2) ≤ b).card := by
      intro b
      have h := Cloud.rankwiseDominates_encard_Iic_le t (hobjectCloudDominatesPartnerCloud t) b
      have h' :
          {p | p ∈ objectsToMatchCloud.particles t ∧ φ (objectsToMatchCloud.position p.1 p.2) ≤ b}.encard ≤
            {q | q ∈ availablePartnersCloud.particles t ∧ φ (availablePartnersCloud.position q.1 q.2) ≤ b}.encard := by
        simpa only [Cloud.mapPosition_particles, Cloud.mapPosition_position] using h
      have hobjectsToMatchSet : {p | p ∈ objectsToMatchCloud.particles t ∧ φ (objectsToMatchCloud.position p.1 p.2) ≤ b} =
          ↑(objectsToMatch.filter fun p => φ (objectsToMatchCloud.position p.1 p.2) ≤ b) := by
        ext p
        simp [objectsToMatch]
      have havailablePartnersSet : {q | q ∈ availablePartnersCloud.particles t ∧ φ (availablePartnersCloud.position q.1 q.2) ≤ b} =
          ↑(availablePartners.filter fun q => φ (availablePartnersCloud.position q.1 q.2) ≤ b) := by
        ext q
        simp [availablePartners]
      rw [hobjectsToMatchSet, havailablePartnersSet, Set.encard_coe_eq_coe_finsetCard,
        Set.encard_coe_eq_coe_finsetCard] at h'
      exact_mod_cast h'
    have hnat := Selection.NSelection.filter_card_le_filter_selectFirstN N
      (fun p => φ (objectsToMatchCloud.position p.1 p.2))
      (fun q => φ (availablePartnersCloud.position q.1 q.2))
      (retained t) objectsToMatch availablePartners
      (by
        intro p hp
        exact ((hobjectsToMatchFinite t).mem_toFinset).mpr (hretained t hp))
      (hcard t) hthreshold
      (by
        intro p q hp hq hqp
        rcases eq_or_lt_of_le hqp with rfl | hqp'
        · exact le_rfl
        · exact hpartnerPositionMonotone t q (((havailablePartnersFinite t).mem_toFinset).mp hq) p
            (((havailablePartnersFinite t).mem_toFinset).mp hp) hqp') a
    have hleft : {p | p ∈ retainedObjectCloud.particles t ∧
        retainedObjectCloud.position p.1 p.2 ≤ a} =
        ↑((retained t).filter fun p => φ (objectsToMatchCloud.position p.1 p.2) ≤ a) := by
      ext p
      simp [retainedObjectCloud]
    have hright : {q | q ∈ selectedPartnerCloud.particles t ∧
        selectedPartnerCloud.position q.1 q.2 ≤ a} =
        ↑((Selection.NSelection.selectFirstN N availablePartners).filter fun q =>
          φ (availablePartnersCloud.position q.1 q.2) ≤ a) := by
      ext q
      simp [selectedPartnerCloud, availablePartners]
    rw [hleft, hright, Set.encard_coe_eq_coe_finsetCard,
      Set.encard_coe_eq_coe_finsetCard]
    exact_mod_cast hnat

/-- Measure-level form of `rankwiseDominatesBy_leftmost_of_subset`, expressed
with the repository's existing `Cloud.DominatesBy` relation. -/
theorem Cloud.dominatesBy_leftmost_of_subset
    [LinearOrder (RootIndexed.TreeNode Root α)]
    [Countable (RootIndexed.TreeNode Root α)]
    [MeasurableSpace Value] [MeasurableSingletonClass Value] [Preorder Value]
    (φ : Position → Value) (N : ℕ)
    (objectsToMatchCloud availablePartnersCloud : Cloud Time Root α Position)
    (retained : Time → Finset (RootIndexed.TreeNode Root α))
    (hobjectsToMatchFinite : ∀ t, (objectsToMatchCloud.particles t).Finite)
    (havailablePartnersFinite : ∀ t, (availablePartnersCloud.particles t).Finite)
    (hretained : ∀ t, ↑(retained t) ⊆ objectsToMatchCloud.particles t)
    (hcard : ∀ t, (retained t).card ≤ N)
    (hobjectPositionMonotone : ∀ t p, p ∈ objectsToMatchCloud.particles t → ∀ q, q ∈ objectsToMatchCloud.particles t →
      p < q → φ (objectsToMatchCloud.position p.1 p.2) ≤ φ (objectsToMatchCloud.position q.1 q.2))
    (hpartnerPositionMonotone : ∀ t p, p ∈ availablePartnersCloud.particles t → ∀ q, q ∈ availablePartnersCloud.particles t →
      p < q → φ (availablePartnersCloud.position p.1 p.2) ≤ φ (availablePartnersCloud.position q.1 q.2))
    (hobjectCloudDominatesPartnerCloud : ∀ t, objectsToMatchCloud.RankwiseDominatesBy φ availablePartnersCloud t) :
    let selectedPartners := fun t => Selection.NSelection.selectFirstN N (havailablePartnersFinite t).toFinset
    (objectsToMatchCloud.withFinsetParticles retained).DominatesBy φ
      (availablePartnersCloud.withFinsetParticles selectedPartners) := by
  dsimp only
  apply Cloud.dominatesBy_of_rankwiseDominatesBy_of_countable φ
  · intro t
    have hfinite :
        (((objectsToMatchCloud.withFinsetParticles retained).mapPosition φ).particles t).Finite := by
      simp
    letI : Fintype ↑(((objectsToMatchCloud.withFinsetParticles retained).mapPosition φ).particles t) :=
      hfinite.fintype
    exact Cloud.sliceRank_injOn_of_finite
      ((objectsToMatchCloud.withFinsetParticles retained).mapPosition φ) t
  · exact Cloud.rankwiseDominatesBy_leftmost_of_subset φ N objectsToMatchCloud availablePartnersCloud retained
      hobjectsToMatchFinite havailablePartnersFinite hretained hcard hobjectPositionMonotone hpartnerPositionMonotone hobjectCloudDominatesPartnerCloud

/-- At an overflow slice full domination need not hold, but every retained
objectsToMatch particle still has a particle in the leftmost `N` partner population
weakly to its left. In particular this applies to an attained left frontier. -/
theorem Cloud.exists_leftmost_le_of_mem
    [LinearOrder (RootIndexed.TreeNode Root α)] [Preorder Value]
    (φ : Position → Value) (N : ℕ) (hN : 0 < N)
    (objectsToMatchCloud availablePartnersCloud : Cloud Time Root α Position) (t : Time)
    (hobjectsToMatchFinite : (objectsToMatchCloud.particles t).Finite)
    (havailablePartnersFinite : (availablePartnersCloud.particles t).Finite)
    (hpartnerPositionMonotone : ∀ p, p ∈ availablePartnersCloud.particles t → ∀ q, q ∈ availablePartnersCloud.particles t →
      p < q → φ (availablePartnersCloud.position p.1 p.2) ≤ φ (availablePartnersCloud.position q.1 q.2))
    (hobjectCloudDominatesPartnerCloud : objectsToMatchCloud.RankwiseDominatesBy φ availablePartnersCloud t)
    {p : RootIndexed.TreeNode Root α} (hp : p ∈ objectsToMatchCloud.particles t) :
    ∃ q ∈ Selection.NSelection.selectFirstN N havailablePartnersFinite.toFinset,
      φ (availablePartnersCloud.position q.1 q.2) ≤ φ (objectsToMatchCloud.position p.1 p.2) := by
  classical
  let objectsToMatch : Finset (RootIndexed.TreeNode Root α) := hobjectsToMatchFinite.toFinset
  let availablePartners : Finset (RootIndexed.TreeNode Root α) := havailablePartnersFinite.toFinset
  letI : Fintype ↑((objectsToMatchCloud.mapPosition φ).particles t) :=
    (show ((objectsToMatchCloud.mapPosition φ).particles t).Finite by simpa using hobjectsToMatchFinite).fintype
  letI : Fintype ↑((availablePartnersCloud.mapPosition φ).particles t) :=
    (show ((availablePartnersCloud.mapPosition φ).particles t).Finite by simpa using havailablePartnersFinite).fintype
  have hthreshold : ∀ b : Value,
      (objectsToMatch.filter fun p => φ (objectsToMatchCloud.position p.1 p.2) ≤ b).card ≤
        (availablePartners.filter fun q => φ (availablePartnersCloud.position q.1 q.2) ≤ b).card := by
    intro b
    have h := Cloud.rankwiseDominates_encard_Iic_le t hobjectCloudDominatesPartnerCloud b
    have h' :
        {p | p ∈ objectsToMatchCloud.particles t ∧ φ (objectsToMatchCloud.position p.1 p.2) ≤ b}.encard ≤
          {q | q ∈ availablePartnersCloud.particles t ∧ φ (availablePartnersCloud.position q.1 q.2) ≤ b}.encard := by
      simpa only [Cloud.mapPosition_particles, Cloud.mapPosition_position] using h
    have hobjectsToMatchSet : {p | p ∈ objectsToMatchCloud.particles t ∧ φ (objectsToMatchCloud.position p.1 p.2) ≤ b} =
        ↑(objectsToMatch.filter fun p => φ (objectsToMatchCloud.position p.1 p.2) ≤ b) := by
      ext r
      simp [objectsToMatch]
    have havailablePartnersSet : {q | q ∈ availablePartnersCloud.particles t ∧ φ (availablePartnersCloud.position q.1 q.2) ≤ b} =
        ↑(availablePartners.filter fun q => φ (availablePartnersCloud.position q.1 q.2) ≤ b) := by
      ext r
      simp [availablePartners]
    rw [hobjectsToMatchSet, havailablePartnersSet, Set.encard_coe_eq_coe_finsetCard,
      Set.encard_coe_eq_coe_finsetCard] at h'
    exact_mod_cast h'
  apply Selection.NSelection.exists_selectFirstN_le_of_mem N hN
    (fun p => φ (objectsToMatchCloud.position p.1 p.2))
    (fun q => φ (availablePartnersCloud.position q.1 q.2)) objectsToMatch availablePartners hthreshold
  · intro r s hr hs hsr
    rcases eq_or_lt_of_le hsr with rfl | hsr'
    · exact le_rfl
    · exact hpartnerPositionMonotone s (havailablePartnersFinite.mem_toFinset.mp hs) r
        (havailablePartnersFinite.mem_toFinset.mp hr) hsr'
  · exact hobjectsToMatchFinite.mem_toFinset.mpr hp

end Combinatorics.Branching

end
