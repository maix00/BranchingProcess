/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Population.Processes.Causal.Basic
public import Probability.BranchingRandomWalk.Selection.NSelection.AtRank

/-!
# Predictable roots from finite population slices

When a killed generation contains at least `K` particles, choose its first
`K` labels in the fixed genealogical order.  On the complementary event use
distinct initial-root labels as a totalization.  This gives the measurable,
injective family required by the independent fresh-subtree estimate, while
on the large-population event every chosen label is an actual particle.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.RootIndexed
open Combinatorics.Branching.Selection.NSelection

@[expose] public section

abbrev RestartedField (m : ℕ) := RootIndexed.StepField (Fin m) ℕ ℝ

abbrev RestartedPopulation (m : ℕ) :=
  RootIndexed.CausalPopulation (RestartedField m) (Fin m) ℕ ℝ
    (RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ)) id

/-- Select a deterministic rank from a finite population slice.  If the slice
is too small, use a distinct address at the requested generation. -/
noncomputable def rightTailSecondStageRankRoot
    {m K : ℕ} [treeOrder : LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (hKm : K ≤ m) (P : RestartedPopulation m) (hP : P.FiniteSlices)
    (generation : ℕ) (field : RestartedField m) (i : Fin K) :
    RootIndexed.TreeNode (Fin m) ℕ := by
  classical
  let candidates := hP.toFinset generation field
  let fallback : RootIndexed.TreeNode (Fin m) ℕ :=
    (i.castLE hKm, List.replicate generation 0)
  exact if hcard : K ≤ candidates.card then
    (Combinatorics.Branching.Selection.NSelection.particleAtRankBy
      (fun _ : RootIndexed.TreeNode (Fin m) ℕ => (0 : ℝ)) candidates i.val).getD
        fallback
  else
    fallback

/-- In a sufficiently large slice, the selected rank is an actual member of
the finite population and its dynamic rank is the requested index. -/
theorem rightTailSecondStageRankRoot_eq_ranked_of_card
    {m K : ℕ} [treeOrder : LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (hKm : K ≤ m) (P : RestartedPopulation m)
    (hP : P.FiniteSlices) (generation : ℕ) (field : RestartedField m)
    (i : Fin K) (hcard : K ≤ (hP.toFinset generation field).card) :
    ∃ p ∈ hP.toFinset generation field,
      rightTailSecondStageRankRoot hKm P hP generation field i = p ∧
        Combinatorics.Branching.Selection.NSelection.rankBy
          (fun _ : RootIndexed.TreeNode (Fin m) ℕ => (0 : ℝ))
          (hP.toFinset generation field) p = i.val := by
  classical
  let candidates := hP.toFinset generation field
  let value : RootIndexed.TreeNode (Fin m) ℕ → ℝ := fun _ => 0
  have hnon : Combinatorics.Branching.Selection.NSelection.particleAtRankBy
      value candidates i.val ≠ none := by
    intro hn
    have hle :=
      Combinatorics.Branching.Selection.NSelection.particleAtRankBy_eq_none_iff.mp hn
    exact (Nat.not_le_of_gt (lt_of_lt_of_le i.isLt hcard)) hle
  obtain ⟨p, hp⟩ := Option.ne_none_iff_exists.mp hnon
  have hp' :=
    Combinatorics.Branching.Selection.NSelection.particleAtRankBy_eq_some_iff.mp hp.symm
  have hroot :
      rightTailSecondStageRankRoot hKm P hP generation field i = p := by
    have hpopt : Combinatorics.Branching.Selection.NSelection.particleAtRankBy
        value candidates i.val = some p := hp.symm
    simp [rightTailSecondStageRankRoot, candidates, value, hcard, hpopt]
  refine ⟨p, hp'.1, hroot, ?_⟩
  simpa [value] using hp'.2

/-- The totalized root always lies at the requested generation. -/
theorem rightTailSecondStageRankRoot_depth
    {m K : ℕ} [treeOrder : LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (hKm : K ≤ m) (P : RestartedPopulation m)
    (hP : P.FiniteSlices) (generation : ℕ) (field : RestartedField m)
    (i : Fin K) :
    (rightTailSecondStageRankRoot hKm P hP generation field i).2.length = generation := by
  classical
  let candidates := hP.toFinset generation field
  by_cases hcard : K ≤ candidates.card
  · obtain ⟨p, hp, hroot, _⟩ :=
      rightTailSecondStageRankRoot_eq_ranked_of_card hKm P hP generation field i
        (by simpa [candidates] using hcard)
    rw [hroot]
    exact P.depth generation field p
      ((hP.mem_toFinset generation field p).mp hp)
  · simp [rightTailSecondStageRankRoot, candidates, hcard]

/-- The totalized root family is injective for every field. -/
theorem rightTailSecondStageRankRoot_injective
    {m K : ℕ} [treeOrder : LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (hKm : K ≤ m) (P : RestartedPopulation m)
    (hP : P.FiniteSlices) (generation : ℕ) (field : RestartedField m)
    :
    Function.Injective (rightTailSecondStageRankRoot hKm P hP generation field) := by
  classical
  let candidates := hP.toFinset generation field
  let value : RootIndexed.TreeNode (Fin m) ℕ → ℝ := fun _ => 0
  by_cases hcard : K ≤ candidates.card
  · intro i j hij
    obtain ⟨p, hp, hpi, hri⟩ :=
      rightTailSecondStageRankRoot_eq_ranked_of_card hKm P hP generation field i
        (by simpa [candidates] using hcard)
    obtain ⟨q, hq, hpj, hrj⟩ :=
      rightTailSecondStageRankRoot_eq_ranked_of_card hKm P hP generation field j
        (by simpa [candidates] using hcard)
    have hpq : p = q := by
      calc
        p = rightTailSecondStageRankRoot hKm P hP generation field i := hpi.symm
        _ = rightTailSecondStageRankRoot hKm P hP generation field j := hij
        _ = q := hpj
    apply Fin.ext
    calc
      i.val = Combinatorics.Branching.Selection.NSelection.rankBy value candidates p := by
        simpa [value, candidates] using hri.symm
      _ = Combinatorics.Branching.Selection.NSelection.rankBy value candidates q := by
        rw [hpq]
      _ = j.val := by simpa [value, candidates] using hrj
  · intro i j hij
    have hij' :
        (i.castLE hKm, List.replicate generation 0) =
          (j.castLE hKm, List.replicate generation 0) := by
      simpa [rightTailSecondStageRankRoot, candidates, hcard] using hij
    have hfst : i.castLE hKm = j.castLE hKm := congrArg Prod.fst hij'
    apply Fin.ext
    simpa using congrArg Fin.val hfst

/-- A generation-dependent family of `K` totalized particles chosen from the
finite slices of a causal population. -/
noncomputable def rightTailSecondStageRoots
    {m K : ℕ} [treeOrder : LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (hKm : K ≤ m)
    (P : ℕ → RestartedPopulation m) (hP : ∀ n, (P n).FiniteSlices)
    (generation : ℕ → ℕ) :
    ℕ → RestartedField m → Fin K → RootIndexed.TreeNode (Fin m) ℕ :=
  fun n field i =>
    rightTailSecondStageRankRoot hKm (P n) (hP n) (generation n) field i

theorem rightTailSecondStageRoots_depth
    {m K : ℕ} [treeOrder : LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (hKm : K ≤ m)
    (P : ℕ → RestartedPopulation m) (hP : ∀ n, (P n).FiniteSlices)
    (generation : ℕ → ℕ) (n : ℕ) (field : RestartedField m)
    (i : Fin K) :
    (rightTailSecondStageRoots hKm P hP generation n field i).2.length =
      generation n :=
  rightTailSecondStageRankRoot_depth hKm (P n) (hP n) (generation n) field i

theorem rightTailSecondStageRoots_injective
    {m K : ℕ} [treeOrder : LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (hKm : K ≤ m)
    (P : ℕ → RestartedPopulation m) (hP : ∀ n, (P n).FiniteSlices)
    (generation : ℕ → ℕ) (n : ℕ) (field : RestartedField m)
    :
    Function.Injective (rightTailSecondStageRoots hKm P hP generation n field) :=
  rightTailSecondStageRankRoot_injective hKm (P n) (hP n) (generation n) field

theorem rightTailSecondStageRoots_countable
    {m K : ℕ} [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (hKm : K ≤ m)
    (P : ℕ → RestartedPopulation m) (hP : ∀ n, (P n).FiniteSlices)
    (generation : ℕ → ℕ) :
    ∀ n, (Set.range (rightTailSecondStageRoots hKm P hP generation n)).Countable :=
  fun _ => Set.to_countable _

private theorem measurableSet_rightTailSecondStageRankRoot_eq
    {m K : ℕ} (hKm : K ≤ m) (P : RestartedPopulation m)
    (hP : P.FiniteSlices) (generation : ℕ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode (Fin m) ℕ)]
    [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (i : Fin K) (p : RootIndexed.TreeNode (Fin m) ℕ) :
    MeasurableSet[RootIndexed.stepFiltration
      (Root := Fin m) (α := ℕ) (X := ℝ) generation]
      {field | rightTailSecondStageRankRoot hKm P hP generation field i = p} := by
  classical
  let F := RootIndexed.stepFiltration (Root := Fin m) (α := ℕ) (X := ℝ)
  let candidates : RestartedField m → Finset (RootIndexed.TreeNode (Fin m) ℕ) :=
    fun field => hP.toFinset generation field
  let value : RestartedField m → RootIndexed.TreeNode (Fin m) ℕ → ℝ :=
    fun _ _ => 0
  have hcandidates : Measurable[F generation] candidates := by
    dsimp [candidates]
    exact hP.measurable_toFinset generation
  have hcandidatesFiber (s : Finset (RootIndexed.TreeNode (Fin m) ℕ)) :
      MeasurableSet[F generation] {field | candidates field = s} :=
    hcandidates (measurableSet_singleton s)
  have hcandidatesRange : (Set.range candidates).Countable := Set.to_countable _
  have hcard : Measurable[F generation]
      (fun field => (candidates field).card) :=
    (measurable_of_countable
      (fun s : Finset (RootIndexed.TreeNode (Fin m) ℕ) => s.card)).comp
        hcandidates
  have hfull : Measurable[F generation]
      (fun field => K ≤ (candidates field).card) :=
    (measurable_of_countable (fun n : ℕ => K ≤ n)).comp hcard
  let S : Set (Finset (RootIndexed.TreeNode (Fin m) ℕ)) := Set.range candidates
  let _ : Countable S := Set.countable_coe_iff.mpr hcandidatesRange
  have hrankSet :
      {field | Combinatorics.Branching.Selection.NSelection.particleAtRankBy
        (value field) (candidates field) i.val = some p} =
        ⋃ s : S, {field | candidates field = s.1} ∩
          {field | Combinatorics.Branching.Selection.NSelection.particleAtRankBy
            (value field) s.1 i.val = some p} := by
    ext field
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · intro h
      exact ⟨⟨candidates field, Set.mem_range_self field⟩, rfl, h⟩
    · rintro ⟨s, hs, h⟩
      simpa [hs] using h
  have hrank : MeasurableSet[F generation]
      {field | Combinatorics.Branching.Selection.NSelection.particleAtRankBy
        (value field) (candidates field) i.val = some p} := by
    rw [hrankSet]
    apply MeasurableSet.iUnion
    intro s
    apply (hcandidatesFiber s.1).inter
    change MeasurableSet[F generation]
      {field : RestartedField m |
        Combinatorics.Branching.Selection.NSelection.particleAtRankBy
          (fun _ : RootIndexed.TreeNode (Fin m) ℕ => (0 : ℝ))
          s.1 i.val = some p}
    by_cases h : Combinatorics.Branching.Selection.NSelection.particleAtRankBy
        (fun _ : RootIndexed.TreeNode (Fin m) ℕ => (0 : ℝ)) s.1 i.val = some p
    · simp [h]
    · simp [h]
  let fallback : RootIndexed.TreeNode (Fin m) ℕ :=
    (i.castLE hKm, List.replicate generation 0)
  have hset :
      {field | rightTailSecondStageRankRoot hKm P hP generation field i = p} =
        ({field | K ≤ (candidates field).card} ∩
          {field | Combinatorics.Branching.Selection.NSelection.particleAtRankBy
            (value field) (candidates field) i.val = some p}) ∪
        ({field | ¬ K ≤ (candidates field).card} ∩ {field | fallback = p}) := by
    ext field
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff]
    by_cases hlarge : K ≤ (candidates field).card
    · have hnon : Combinatorics.Branching.Selection.NSelection.particleAtRankBy
        (value field) (candidates field) i.val ≠ none := by
        intro hn
        have hle :=
          Combinatorics.Branching.Selection.NSelection.particleAtRankBy_eq_none_iff.mp hn
        exact (Nat.not_le_of_gt (lt_of_lt_of_le i.isLt hlarge)) hle
      have hget :
          (Combinatorics.Branching.Selection.NSelection.particleAtRankBy
            (value field) (candidates field) i.val).getD fallback = p ↔
            Combinatorics.Branching.Selection.NSelection.particleAtRankBy
              (value field) (candidates field) i.val = some p := by
        cases hopt : Combinatorics.Branching.Selection.NSelection.particleAtRankBy
            (value field) (candidates field) i.val with
        | none => exact (hnon hopt).elim
        | some q => simp
      change (if K ≤ (candidates field).card then
          (Combinatorics.Branching.Selection.NSelection.particleAtRankBy
            (value field) (candidates field) i.val).getD fallback else fallback) = p ↔ _
      rw [ite_eq_left hlarge, hget]
      simp [hlarge]
    · change (if K ≤ (candidates field).card then
          (Combinatorics.Branching.Selection.NSelection.particleAtRankBy
            (value field) (candidates field) i.val).getD fallback else fallback) = p ↔ _
      rw [ite_eq_right hlarge]
      simp [hlarge]
  rw [hset]
  have hfullSet : MeasurableSet[F generation]
      {field | K ≤ (candidates field).card} := by
    simpa using hfull (measurableSet_singleton True)
  have hsmallSet : MeasurableSet[F generation]
      {field | ¬ K ≤ (candidates field).card} := by
    simpa using hfull (measurableSet_singleton False)
  have hfallback : MeasurableSet[F generation] {field | fallback = p} := by
    by_cases hp : fallback = p <;> simp [hp]
  exact (hfullSet.inter hrank).union (hsmallSet.inter hfallback)

/-- The chosen family has measurable fibres at the generation it observes. -/
theorem measurableSet_rightTailSecondStageRoots_eq
    {m K : ℕ} [treeOrder : LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (hKm : K ≤ m) (P : ℕ → RestartedPopulation m)
    (hP : ∀ n, (P n).FiniteSlices) (generation : ℕ → ℕ) (n : ℕ)
    [MeasurableSpace (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Fin m) ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode (Fin m) ℕ)]
    (roots : Fin K → RootIndexed.TreeNode (Fin m) ℕ) :
    MeasurableSet[RootIndexed.stepFiltration
      (Root := Fin m) (α := ℕ) (X := ℝ) (generation n)]
      {field | rightTailSecondStageRoots hKm P hP generation n field = roots} := by
  classical
  have hset :
      {field | rightTailSecondStageRoots hKm P hP generation n field = roots} =
        ⋂ i : Fin K,
          {field | rightTailSecondStageRoots hKm P hP generation n field i = roots i} := by
    ext field
    simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h i
      exact congrFun h i
    · intro h
      funext i
      exact h i
  rw [hset]
  exact MeasurableSet.iInter fun i =>
    measurableSet_rightTailSecondStageRankRoot_eq hKm (P n) (hP n)
      (generation n) i (roots i)

end

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Tail
