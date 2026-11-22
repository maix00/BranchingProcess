/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Restarted.Trajectory
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.FixedFamily

/-!
# Rank installation up to a stopping time

## Public declarations

* `RootIndexed.restartedRealPositionNSelectedBRWField_filtration_measurable`:
  the stage-$n$ installed field is measurable from the joint generation-$n$
  past to the selected field's generation-$n$ past.
* `RootIndexed.stoppedRankInstalledTrajectoryField`: the coherent rank-installed field with installation
  at generation $j$ only on $\{j<\tau\}$.
* `RootIndexed.stoppedRankInstalledTrajectoryField_eq_stage`: on $\{\tau=n\}$ the resulting full field
  equals the original stage-$n$ field. The stages agree through the entrance,
  and the marks of depths $j\ge n$ are the fallback marks.
* `RootIndexed.stoppedRankInstalledTrajectoryField_measurable_law`: this field has the same product
  offspring law as the original first-$N$ process.

* `RootIndexed.stoppedRankInstalledTrajectoryField_eq_stage_before`: if
  $n\le\tau$, the stopped installation and the stage-$n$ installation agree
  on every mark revealed strictly before $n$.
* `RootIndexed.stoppedRankInstalledTrajectoryField_apply_of_le_length`: on
  $\{\tau=n\}$, every mark at depth at least $n$ is its right-field mark.
* `RootIndexed.stoppedRankInstalledTrajectoryField_subtrees_factorization`:
  on a generation-$n$ event $A\subseteq\{\tau=n\}$, the subtrees of
  distinct prescribed depth-$n$ roots have the product offspring law $Q$,
  so $\mathbb P(A\cap\{\Phi\in B\})=\mathbb P(A)Q(B)$.

This supplies the switch to fresh marks in the stopping-time continuation
of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring* (Fudan University, 2026), Chapter 4, Theorem 1.1 at $a=0$.
-/

open MeasureTheory ProbabilityTheory

public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Coupling
open _root_.Combinatorics.Selection.NSelection

private def beforeStop
    {Ω Root α X : Type*} [MeasurableSpace Ω]
    {ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)}
    {stepField : Ω → RootIndexed.StepField Root α X}
    (P : RootIndexed.CausalPopulation Ω Root α X ℱ stepField)
    (τ : Ω → WithTop ℕ) (hτ : IsStoppingTime ℱ τ) :
    RootIndexed.CausalPopulation Ω Root α X ℱ stepField where
  toPopulation ω :=
    { particles := fun n => {p | p ∈ P n ω ∧ (n : WithTop ℕ) < τ ω}
      depth := fun n p hp => P.depth n ω p hp.1
      successor := by
        intro n q hq
        obtain ⟨p, hp, i, hi, heq⟩ := Combinatorics.Branching.Population.mem_offspringAddressSet.mp
          (P.successor n ω hq.1)
        exact Combinatorics.Branching.Population.mem_offspringAddressSet.mpr
          ⟨p, ⟨hp, lt_trans (by exact_mod_cast Nat.lt_succ_self n) hq.2⟩, i, hi, heq⟩ }
  adapted p n := by
    apply (@measurableSet_setOfPred Ω (ℱ n) _).mp
    have hp : MeasurableSet[ℱ n] {ω | p ∈ P n ω} :=
      (@measurableSet_setOfPred Ω (ℱ n) _).mpr (P.measurable_mem n p)
    have hs : MeasurableSet[ℱ n] {ω | (n : WithTop ℕ) < τ ω} := by
      convert (hτ n).compl using 1
      ext ω
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le]
      rfl
    change MeasurableSet[ℱ n] ({ω | p ∈ P n ω} ∩ {ω | (n : WithTop ℕ) < τ ω})
    exact hp.inter hs

private lemma beforeStop_finiteSlices
    {Ω Root α X : Type*} [MeasurableSpace Ω]
    {ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)}
    {stepField : Ω → RootIndexed.StepField Root α X}
    {P : RootIndexed.CausalPopulation Ω Root α X ℱ stepField}
    (hP : P.FiniteSlices) (τ : Ω → WithTop ℕ) (hτ : IsStoppingTime ℱ τ) :
    (beforeStop P τ hτ).FiniteSlices :=
  fun n ω => (hP n ω).subset fun _ hp => hp.1

private lemma beforeStop_toFinset
    {Ω Root α X : Type*} [MeasurableSpace Ω]
    {ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)}
    {stepField : Ω → RootIndexed.StepField Root α X}
    {P : RootIndexed.CausalPopulation Ω Root α X ℱ stepField}
    (hP : P.FiniteSlices) (τ : Ω → WithTop ℕ) (hτ : IsStoppingTime ℱ τ) (n : ℕ) (ω : Ω) :
    (beforeStop_finiteSlices hP τ hτ).toFinset n ω =
      if (n : WithTop ℕ) < τ ω then hP.toFinset n ω else ∅ := by
  classical
  ext p
  rw [RootIndexed.CausalPopulation.FiniteSlices.mem_toFinset]
  change (p ∈ P n ω ∧ (n : WithTop ℕ) < τ ω) ↔ _
  by_cases hn : (n : WithTop ℕ) < τ ω <;> simp [hn]

section RankInstallation

variable {Ω Root α X Value : Type*} [MeasurableSpace Ω]
  [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]

omit [MeasurableSpace Ω] in
private lemma rankInstalledField_eq_of_slices_eq
    (order₁ : ℕ → Ω → RootIndexed.TreeNode Root α → Value)
    (order₂ : ℕ → Ω → RootIndexed.StepField Root α X → RootIndexed.TreeNode Root α → Value)
    (P Q : ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (target : ℕ → Ω → RootIndexed.StepField Root α X → Finset (RootIndexed.TreeNode Root α))
    (left right : Ω → RootIndexed.StepField Root α X)
    (n : ℕ) (ω : Ω) (heq : ∀ j < n, P j ω = Q j ω) :
    RootIndexed.rankInstalledField order₁ order₂ P target left right n ω =
      RootIndexed.rankInstalledField order₁ order₂ Q target left right n ω := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hearlier := ih (fun j hj => heq j (hj.trans (Nat.lt_succ_self n)))
    have hnow := heq n (Nat.lt_succ_self n)
    funext r u
    simp only [RootIndexed.rankInstalledField_succ, RootIndexed.StepField.updateGeneration_apply,
      RootIndexed.rankInstalledStepField, valueAtMatchedRank, valueAtObjectPreimage]
    rw [hearlier, hnow]

omit [MeasurableSpace Ω] in
private lemma rankInstalledField_succ_eq_of_empty
    (order₁ : ℕ → Ω → RootIndexed.TreeNode Root α → Value)
    (order₂ : ℕ → Ω → RootIndexed.StepField Root α X → RootIndexed.TreeNode Root α → Value)
    (P : ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (target : ℕ → Ω → RootIndexed.StepField Root α X → Finset (RootIndexed.TreeNode Root α))
    (left right : Ω → RootIndexed.StepField Root α X)
    (n : ℕ) (ω : Ω) (he : P n ω = ∅) :
    RootIndexed.rankInstalledField order₁ order₂ P target left right (n + 1) ω =
      RootIndexed.rankInstalledField order₁ order₂ P target left right n ω := by
  classical
  funext r u
  simp only [RootIndexed.rankInstalledField_succ, RootIndexed.StepField.updateGeneration_apply,
    RootIndexed.rankInstalledStepField, valueAtMatchedRank, valueAtObjectPreimage,
    objectAtPartnerRankBy, he]
  by_cases hmem : (r, u) ∈ target n ω
      (RootIndexed.rankInstalledField order₁ order₂ P target left right n ω)
  · have hn (k : ℕ) : particleAtRankBy (order₁ n ω) ∅ k = none :=
      particleAtRankBy_eq_none_iff.mpr (by simp)
    simp [hmem, partnerAtObjectRankBy, hn]
  · simp [hmem]

end RankInstallation

section StoppedField

variable {Root α : Type*}
  [MeasurableSpace (RootIndexed.TreeNode Root α)]
  [Countable (RootIndexed.TreeNode Root α)] [LinearOrder (RootIndexed.TreeNode Root α)]

local notation "Ωf" => RootIndexed.StepField (Root ⊕ Root) α ℝ
local notation "𝔽" => RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := α) (X := ℝ)

/-- The first-`N` stage field is adapted to the joint past of the coupling. -/
lemma RootIndexed.restartedRealPositionNSelectedBRWField_filtration_measurable
    (N : ℕ) (roots : Finset Root) (initialPosition : Root → ℝ)
    {P : RootIndexed.CausalPopulation Ωf Root α ℝ 𝔽 RootIndexed.StepField.left}
    (hP : P.FiniteSlices) (n : ℕ) :
    @Measurable Ωf (RootIndexed.StepField Root α ℝ) (𝔽 n)
      (RootIndexed.stepFiltration (Root := Root) (α := α) (X := ℝ) n)
      (RootIndexed.restartedRealPositionNSelectedBRWField N roots initialPosition id hP.toFinset n) := by
  apply RootIndexed.rankInstalledField_totalizedSelectedPopulation_filtration_measurable
    N roots initialPosition id measurable_id id measurable_id
    (fun k field p => RootIndexed.observedPositionAtGeneration initialPosition id id k
      (RootIndexed.StepField.left field) p) hP.toFinset
  · intro k field p hp
    exact P.depth k field p ((hP.mem_toFinset k field p).mp hp)
  · intro k s
    exact hP.measurable_toFinset k (measurableSet_singleton s)
  · intro k
    exact Set.to_countable _
  · intro k p q
    let _ : MeasurableSpace Ωf := 𝔽 k
    apply measurable_valueKey_lt
    intro z
    exact (RootIndexed.positionAtGeneration_measurable initialPosition id measurable_id
      k z.1 z.2).comp (RootIndexed.StepField.reindex_filtration_measurable Sum.inl k)

/-- Install ranks from the causal population at precisely the generations strictly before `τ`. -/
noncomputable def RootIndexed.stoppedRankInstalledTrajectoryField
    (N : ℕ) (roots : Finset Root) (initialPosition : Root → ℝ)
    {P : RootIndexed.CausalPopulation Ωf Root α ℝ 𝔽 RootIndexed.StepField.left}
    (hP : P.FiniteSlices)
    (τ : Ωf → WithTop ℕ) (hτ : IsStoppingTime 𝔽 τ) :
    Ωf → RootIndexed.StepField Root α ℝ :=
  RootIndexed.restartedRealPositionTrajectoryField N roots initialPosition id
    (beforeStop_finiteSlices hP τ hτ).toFinset

omit [MeasurableSpace (RootIndexed.TreeNode Root α)]
  [Countable (RootIndexed.TreeNode Root α)] in
lemma RootIndexed.stoppedRankInstalledTrajectoryField_eq_stage
    (N : ℕ) (roots : Finset Root) (initialPosition : Root → ℝ)
    {P : RootIndexed.CausalPopulation Ωf Root α ℝ 𝔽 RootIndexed.StepField.left}
    (hP : P.FiniteSlices)
    (τ : Ωf → WithTop ℕ) (hτ : IsStoppingTime 𝔽 τ)
    (ω : Ωf) (n : ℕ) (hn : τ ω = n) :
    RootIndexed.stoppedRankInstalledTrajectoryField N roots initialPosition hP τ hτ ω =
      RootIndexed.restartedRealPositionNSelectedBRWField N roots initialPosition id
        hP.toFinset n ω := by
  let cut := (beforeStop_finiteSlices hP τ hτ).toFinset
  let U := RootIndexed.restartedRealPositionNSelectedBRWField N roots initialPosition id cut
  let V := RootIndexed.restartedRealPositionNSelectedBRWField N roots initialPosition id hP.toFinset
  have hstage : U n ω = V n ω := by
    dsimp only [U, V, RootIndexed.restartedRealPositionNSelectedBRWField]
    apply rankInstalledField_eq_of_slices_eq
    intro j hj
    have hlt : (j : WithTop ℕ) < τ ω := by rw [hn]; exact_mod_cast hj
    change cut j ω = _
    rw [show cut j ω = _ from beforeStop_toFinset hP τ hτ j ω, ite_eq_left hlt]
  have hafter (j : ℕ) (hjn : n ≤ j) : U j ω = U n ω := by
    induction j, hjn using Nat.le_induction with
    | base => rfl
    | succ j hj ih =>
      rw [← ih]
      dsimp only [U, RootIndexed.restartedRealPositionNSelectedBRWField]
      apply rankInstalledField_succ_eq_of_empty
      have hlt : ¬ (j : WithTop ℕ) < τ ω := by rw [hn]; exact_mod_cast (not_lt_of_ge hj)
      change cut j ω = ∅
      rw [show cut j ω = _ from beforeStop_toFinset hP τ hτ j ω, ite_eq_right hlt]
  funext r u
  change RootIndexed.restartedRealPositionTrajectoryField N roots initialPosition id cut ω r u =
    V n ω r u
  by_cases hu : u.length < n
  · rw [RootIndexed.restartedRealPositionTrajectoryField_eq_stage _ _ _ _ _ _ n r u hu]
    exact congrFun (congrFun hstage r) u
  · change U (u.length + 1) ω r u = V n ω r u
    rw [hafter _ (by omega), hstage]

omit [MeasurableSpace (RootIndexed.TreeNode Root α)]
  [Countable (RootIndexed.TreeNode Root α)] in
/-- The installed field agrees with the ordinary stage on all marks exposed
before that stage, provided the installation has not stopped earlier. -/
lemma RootIndexed.stoppedRankInstalledTrajectoryField_eq_stage_before
    (N : ℕ) (roots : Finset Root) (initialPosition : Root → ℝ)
    {P : RootIndexed.CausalPopulation Ωf Root α ℝ 𝔽 RootIndexed.StepField.left}
    (hP : P.FiniteSlices)
    (τ : Ωf → WithTop ℕ) (hτ : IsStoppingTime 𝔽 τ)
    (ω : Ωf) (n : ℕ) (hn : (n : WithTop ℕ) ≤ τ ω)
    (r : Root) (u : TreeNode α) (hu : u.length < n) :
    RootIndexed.stoppedRankInstalledTrajectoryField N roots initialPosition hP τ hτ ω r u =
      RootIndexed.restartedRealPositionNSelectedBRWField N roots initialPosition id
        hP.toFinset n ω r u := by
  let cut := (beforeStop_finiteSlices hP τ hτ).toFinset
  have hstage : RootIndexed.restartedRealPositionNSelectedBRWField N roots initialPosition id cut n ω =
      RootIndexed.restartedRealPositionNSelectedBRWField N roots initialPosition id hP.toFinset n ω := by
    dsimp only [RootIndexed.restartedRealPositionNSelectedBRWField]
    apply rankInstalledField_eq_of_slices_eq
    intro j hj
    have hlt : (j : WithTop ℕ) < τ ω := (WithTop.coe_lt_coe.mpr hj).trans_le hn
    change cut j ω = _
    rw [show cut j ω = _ from beforeStop_toFinset hP τ hτ j ω, ite_eq_left hlt]
  change RootIndexed.restartedRealPositionTrajectoryField N roots initialPosition id cut ω r u = _
  rw [RootIndexed.restartedRealPositionTrajectoryField_eq_stage _ _ _ _ _ _ n r u hu, hstage]

omit [MeasurableSpace (RootIndexed.TreeNode Root α)]
  [Countable (RootIndexed.TreeNode Root α)] in
/-- At or beyond the stopping generation, the stopped installation uses the right field. -/
lemma RootIndexed.stoppedRankInstalledTrajectoryField_apply_of_le_length
    (N : ℕ) (roots : Finset Root) (initialPosition : Root → ℝ)
    {P : RootIndexed.CausalPopulation Ωf Root α ℝ 𝔽 RootIndexed.StepField.left}
    (hP : P.FiniteSlices) (τ : Ωf → WithTop ℕ) (hτ : IsStoppingTime 𝔽 τ)
    (ω : Ωf) (n : ℕ) (hn : τ ω = n) (r : Root) (u : TreeNode α) (hu : n ≤ u.length) :
    RootIndexed.stoppedRankInstalledTrajectoryField N roots initialPosition hP τ hτ ω r u =
      ω (Sum.inr r) u := by
  rw [RootIndexed.stoppedRankInstalledTrajectoryField_eq_stage N roots initialPosition hP τ hτ ω n hn]
  exact Coupling.RootIndexed.rankInstalledField_apply_of_le_length _ _ _ _ _ _ n ω r u hu

omit [MeasurableSpace (RootIndexed.TreeNode Root α)]
  [Countable (RootIndexed.TreeNode Root α)] in
/-- On a specified finite stopping cell, any fixed family of distinct roots
at the stopping generation has the fresh product law. The event may depend
on the selected population and the positions observed at that generation. -/
lemma RootIndexed.stoppedRankInstalledTrajectoryField_subtrees_factorization
    {κ : Type*} (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (N : ℕ) (roots : Finset Root) (initialPosition : Root → ℝ)
    {P : RootIndexed.CausalPopulation Ωf Root α ℝ 𝔽 RootIndexed.StepField.left}
    (hP : P.FiniteSlices) (τ : Ωf → WithTop ℕ) (hτ : IsStoppingTime 𝔽 τ)
    {n : ℕ} (subtreeRoots : κ → RootIndexed.TreeNode Root α)
    (hdepth : ∀ i, (subtreeRoots i).2.length = n)
    (hinj : Function.Injective subtreeRoots)
    (A : Set Ωf) (hA : MeasurableSet[𝔽 n] A)
    (hAt : ∀ ω ∈ A, τ ω = n)
    (B : Set (RootIndexed.StepField κ α ℝ)) (hB : MeasurableSet B) :
    let law := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
    let installed := RootIndexed.stoppedRankInstalledTrajectoryField N roots initialPosition hP τ hτ
    law (A ∩ (fun ω => RootIndexed.subtreeStepFieldVector subtreeRoots (installed ω)) ⁻¹' B) =
      law A * RootIndexed.stepFieldLaw μ B := by
  intro law installed
  let rightRoots (i : κ) : RootIndexed.TreeNode (Root ⊕ Root) α :=
    (Sum.inr (subtreeRoots i).1, (subtreeRoots i).2)
  have hright : Function.Injective rightRoots := by
    intro i j heq
    apply hinj
    exact Prod.ext (Sum.inr_injective (congrArg Prod.fst heq)) (congrArg (fun p : RootIndexed.TreeNode (Root ⊕ Root) α => p.2) heq)
  have htest :
      A ∩ (fun ω => RootIndexed.subtreeStepFieldVector subtreeRoots (installed ω)) ⁻¹' B =
        A ∩ RootIndexed.subtreeStepFieldVector rightRoots ⁻¹' B := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    refine and_congr_right fun hω => ?_
    have heq : RootIndexed.subtreeStepFieldVector subtreeRoots (installed ω) =
        RootIndexed.subtreeStepFieldVector rightRoots ω := by
      funext i v
      exact RootIndexed.stoppedRankInstalledTrajectoryField_apply_of_le_length
        N roots initialPosition hP τ hτ ω n (hAt ω hω) _ _ (by
          rw [List.length_append, hdepth i]
          exact Nat.le_add_right _ _)
    rw [heq]
  rw [htest]
  exact RootIndexed.subtreeStepFieldVector_event_factorization μ rightRoots hdepth hright A B hA hB

/-- Stopping the installation retains the original product offspring law. -/
lemma RootIndexed.stoppedRankInstalledTrajectoryField_measurable_law
    [Countable α]
    (μ : Measure (Step α ℝ)) [IsProbabilityMeasure μ]
    (N : ℕ) (roots : Finset Root) (initialPosition : Root → ℝ)
    {P : RootIndexed.CausalPopulation Ωf Root α ℝ 𝔽 RootIndexed.StepField.left}
    (hP : P.FiniteSlices)
    (τ : Ωf → WithTop ℕ) (hτ : IsStoppingTime 𝔽 τ) :
    Measurable (RootIndexed.stoppedRankInstalledTrajectoryField N roots initialPosition hP τ hτ) ∧
      (RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).map
        (RootIndexed.stoppedRankInstalledTrajectoryField N roots initialPosition hP τ hτ) =
          RootIndexed.stepFieldLaw (Root := Root) μ :=
  RootIndexed.restartedRealPositionTrajectoryField_measurable_law μ N roots initialPosition
    (beforeStop P τ hτ) (beforeStop_finiteSlices hP τ hτ)

end StoppedField

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

end
