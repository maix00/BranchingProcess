/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Cloud.Order.Basic
public import Combinatorics.BranchingWalk.Selection.NSelection.Coupling

/-!
# Domination under leftmost selection

The finite counting lemma for `selectFirstN` is lifted here to the existing cloud
orders.  Positions may be abstract; comparison takes place after an ordered
observation `φ`. Equal observed positions retain their distinct particle
identities.
-/

open Combinatorics.UlamHarris

@[expose] public section

namespace Combinatorics.Branching

open Selection

set_option linter.style.haveILetI false

variable {Time Root α Position Value : Type*}

/-- A retained subpopulation of size at most `N` dominates the leftmost `N`
population whenever its source candidate cloud dominates the other candidate
cloud. This is the deterministic one-generation core of the killed-BRW
coupling. -/
theorem Cloud.rankwiseDominatesBy_leftmost_of_subset
    [LinearOrder (RootIndexed.TreeNode Root α)] [Preorder Value]
    (φ : Position → Value) (N : ℕ)
    (C D : Cloud Time Root α Position)
    (retained : Time → Finset (RootIndexed.TreeNode Root α))
    (hCfinite : ∀ t, (C.particles t).Finite)
    (hDfinite : ∀ t, (D.particles t).Finite)
    (hretained : ∀ t, ↑(retained t) ⊆ C.particles t)
    (hcard : ∀ t, (retained t).card ≤ N)
    (hCmono : ∀ t p, p ∈ C.particles t → ∀ q, q ∈ C.particles t →
      p < q → φ (C.position p.1 p.2) ≤ φ (C.position q.1 q.2))
    (hDmono : ∀ t p, p ∈ D.particles t → ∀ q, q ∈ D.particles t →
      p < q → φ (D.position p.1 p.2) ≤ φ (D.position q.1 q.2))
    (hdom : ∀ t, C.RankwiseDominatesBy φ D t) :
    let right := fun t => Selection.NSelection.selectFirstN N (hDfinite t).toFinset
    ∀ t, (C.withFinsetParticles retained).RankwiseDominatesBy φ
      (D.withFinsetParticles right) t := by
  classical
  dsimp only
  intro t
  let source : Finset (RootIndexed.TreeNode Root α) := (hCfinite t).toFinset
  let candidates : Finset (RootIndexed.TreeNode Root α) := (hDfinite t).toFinset
  let leftCloud := (C.withFinsetParticles retained).mapPosition φ
  let rightCloud :=
    (D.withFinsetParticles (fun u =>
      Selection.NSelection.selectFirstN N (hDfinite u).toFinset)).mapPosition φ
  change leftCloud.RankwiseDominates rightCloud t
  have hleftFinite : (leftCloud.particles t).Finite := by
    simp [leftCloud]
  have hrightFinite : (rightCloud.particles t).Finite := by
    simp [rightCloud]
  letI : Fintype (leftCloud.particles t) := hleftFinite.fintype
  letI : Fintype (rightCloud.particles t) := hrightFinite.fintype
  letI : Fintype ↑((C.mapPosition φ).particles t) :=
    (show ((C.mapPosition φ).particles t).Finite by simpa using hCfinite t).fintype
  letI : Fintype ↑((D.mapPosition φ).particles t) :=
    (show ((D.mapPosition φ).particles t).Finite by simpa using hDfinite t).fintype
  apply Cloud.rankwiseDominates_of_encard_Iic_le t
  · intro p hp q hq hpq
    exact hCmono t p (hretained t hp) q (hretained t hq) hpq
  · intro p hp q hq hpq
    have hp' : p ∈ Selection.NSelection.selectFirstN N candidates := by
      simpa [rightCloud, candidates] using hp
    have hq' : q ∈ Selection.NSelection.selectFirstN N candidates := by
      simpa [rightCloud, candidates] using hq
    have hpD : p ∈ D.particles t := ((hDfinite t).mem_toFinset).mp
      (Selection.NSelection.selectFirstN_subset N candidates hp')
    have hqD : q ∈ D.particles t := ((hDfinite t).mem_toFinset).mp
      (Selection.NSelection.selectFirstN_subset N candidates hq')
    exact hDmono t p hpD q hqD hpq
  · intro a
    have hthreshold : ∀ b : Value,
        (source.filter fun p => φ (C.position p.1 p.2) ≤ b).card ≤
          (candidates.filter fun q => φ (D.position q.1 q.2) ≤ b).card := by
      intro b
      have h := Cloud.rankwiseDominates_encard_Iic_le t (hdom t) b
      have h' :
          {p | p ∈ C.particles t ∧ φ (C.position p.1 p.2) ≤ b}.encard ≤
            {q | q ∈ D.particles t ∧ φ (D.position q.1 q.2) ≤ b}.encard := by
        simpa only [Cloud.mapPosition_particles, Cloud.mapPosition_position] using h
      have hCs : {p | p ∈ C.particles t ∧ φ (C.position p.1 p.2) ≤ b} =
          ↑(source.filter fun p => φ (C.position p.1 p.2) ≤ b) := by
        ext p
        simp [source]
      have hDs : {q | q ∈ D.particles t ∧ φ (D.position q.1 q.2) ≤ b} =
          ↑(candidates.filter fun q => φ (D.position q.1 q.2) ≤ b) := by
        ext q
        simp [candidates]
      rw [hCs, hDs, Set.encard_coe_eq_coe_finsetCard,
        Set.encard_coe_eq_coe_finsetCard] at h'
      exact_mod_cast h'
    have hnat := Selection.NSelection.filter_card_le_filter_selectFirstN N
      (fun p => φ (C.position p.1 p.2))
      (fun q => φ (D.position q.1 q.2))
      (retained t) source candidates
      (by
        intro p hp
        exact ((hCfinite t).mem_toFinset).mpr (hretained t hp))
      (hcard t) hthreshold
      (by
        intro p q hp hq hqp
        rcases eq_or_lt_of_le hqp with rfl | hqp'
        · exact le_rfl
        · exact hDmono t q (((hDfinite t).mem_toFinset).mp hq) p
            (((hDfinite t).mem_toFinset).mp hp) hqp') a
    have hleft : {p | p ∈ leftCloud.particles t ∧
        leftCloud.position p.1 p.2 ≤ a} =
        ↑((retained t).filter fun p => φ (C.position p.1 p.2) ≤ a) := by
      ext p
      simp [leftCloud]
    have hright : {q | q ∈ rightCloud.particles t ∧
        rightCloud.position q.1 q.2 ≤ a} =
        ↑((Selection.NSelection.selectFirstN N candidates).filter fun q =>
          φ (D.position q.1 q.2) ≤ a) := by
      ext q
      simp [rightCloud, candidates]
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
    (C D : Cloud Time Root α Position)
    (retained : Time → Finset (RootIndexed.TreeNode Root α))
    (hCfinite : ∀ t, (C.particles t).Finite)
    (hDfinite : ∀ t, (D.particles t).Finite)
    (hretained : ∀ t, ↑(retained t) ⊆ C.particles t)
    (hcard : ∀ t, (retained t).card ≤ N)
    (hCmono : ∀ t p, p ∈ C.particles t → ∀ q, q ∈ C.particles t →
      p < q → φ (C.position p.1 p.2) ≤ φ (C.position q.1 q.2))
    (hDmono : ∀ t p, p ∈ D.particles t → ∀ q, q ∈ D.particles t →
      p < q → φ (D.position p.1 p.2) ≤ φ (D.position q.1 q.2))
    (hdom : ∀ t, C.RankwiseDominatesBy φ D t) :
    let right := fun t => Selection.NSelection.selectFirstN N (hDfinite t).toFinset
    (C.withFinsetParticles retained).DominatesBy φ
      (D.withFinsetParticles right) := by
  dsimp only
  apply Cloud.dominatesBy_of_rankwiseDominatesBy_of_countable φ
  · intro t
    have hfinite :
        (((C.withFinsetParticles retained).mapPosition φ).particles t).Finite := by
      simp
    letI : Fintype ↑(((C.withFinsetParticles retained).mapPosition φ).particles t) :=
      hfinite.fintype
    exact Cloud.sliceRank_injOn_of_finite
      ((C.withFinsetParticles retained).mapPosition φ) t
  · exact Cloud.rankwiseDominatesBy_leftmost_of_subset φ N C D retained
      hCfinite hDfinite hretained hcard hCmono hDmono hdom

/-- At an overflow slice full domination need not hold, but every retained
source particle still has a particle in the leftmost `N` target population
weakly to its left. In particular this applies to an attained left frontier. -/
theorem Cloud.exists_leftmost_le_of_mem
    [LinearOrder (RootIndexed.TreeNode Root α)] [Preorder Value]
    (φ : Position → Value) (N : ℕ) (hN : 0 < N)
    (C D : Cloud Time Root α Position) (t : Time)
    (hCfinite : (C.particles t).Finite)
    (hDfinite : (D.particles t).Finite)
    (hDmono : ∀ p, p ∈ D.particles t → ∀ q, q ∈ D.particles t →
      p < q → φ (D.position p.1 p.2) ≤ φ (D.position q.1 q.2))
    (hdom : C.RankwiseDominatesBy φ D t)
    {p : RootIndexed.TreeNode Root α} (hp : p ∈ C.particles t) :
    ∃ q ∈ Selection.NSelection.selectFirstN N hDfinite.toFinset,
      φ (D.position q.1 q.2) ≤ φ (C.position p.1 p.2) := by
  classical
  let source : Finset (RootIndexed.TreeNode Root α) := hCfinite.toFinset
  let candidates : Finset (RootIndexed.TreeNode Root α) := hDfinite.toFinset
  letI : Fintype ↑((C.mapPosition φ).particles t) :=
    (show ((C.mapPosition φ).particles t).Finite by simpa using hCfinite).fintype
  letI : Fintype ↑((D.mapPosition φ).particles t) :=
    (show ((D.mapPosition φ).particles t).Finite by simpa using hDfinite).fintype
  have hthreshold : ∀ b : Value,
      (source.filter fun p => φ (C.position p.1 p.2) ≤ b).card ≤
        (candidates.filter fun q => φ (D.position q.1 q.2) ≤ b).card := by
    intro b
    have h := Cloud.rankwiseDominates_encard_Iic_le t hdom b
    have h' :
        {p | p ∈ C.particles t ∧ φ (C.position p.1 p.2) ≤ b}.encard ≤
          {q | q ∈ D.particles t ∧ φ (D.position q.1 q.2) ≤ b}.encard := by
      simpa only [Cloud.mapPosition_particles, Cloud.mapPosition_position] using h
    have hCs : {p | p ∈ C.particles t ∧ φ (C.position p.1 p.2) ≤ b} =
        ↑(source.filter fun p => φ (C.position p.1 p.2) ≤ b) := by
      ext r
      simp [source]
    have hDs : {q | q ∈ D.particles t ∧ φ (D.position q.1 q.2) ≤ b} =
        ↑(candidates.filter fun q => φ (D.position q.1 q.2) ≤ b) := by
      ext r
      simp [candidates]
    rw [hCs, hDs, Set.encard_coe_eq_coe_finsetCard,
      Set.encard_coe_eq_coe_finsetCard] at h'
    exact_mod_cast h'
  apply Selection.NSelection.exists_selectFirstN_le_of_mem N hN
    (fun p => φ (C.position p.1 p.2))
    (fun q => φ (D.position q.1 q.2)) source candidates hthreshold
  · intro r s hr hs hsr
    rcases eq_or_lt_of_le hsr with rfl | hsr'
    · exact le_rfl
    · exact hDmono s (hDfinite.mem_toFinset.mp hs) r
        (hDfinite.mem_toFinset.mp hr) hsr'
  · exact hCfinite.mem_toFinset.mpr hp

end Combinatorics.Branching

end
