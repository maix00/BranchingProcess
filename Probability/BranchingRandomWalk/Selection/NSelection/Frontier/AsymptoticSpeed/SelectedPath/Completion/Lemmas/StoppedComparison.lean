/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Restarted.Continuation
import all Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.Restarted.Stopping
import Probability.BranchingRandomWalk.Selection.NSelection.Law.Causal.EndpointOrder
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.FixedHorizon

/-!
# Endpoint comparison on a successful entrance cell

## Internal proof declarations

* `measure_stoppedEndpointAtLeast_le_on_cell`: on a stopped generation-$n$
  cell $A$ with a fixed set of occupied addresses and at least $m$ positions
  bounded above by an observable $c$, the centered actual endpoint upper-tail probability satisfies
  $\mathbb P(A,M_{n+k}\ge x+c)\le\mathbb P(A)\mathbb P(M^{(m)}_k\ge x)$.
  Here the comparison process starts with $m$ particles at zero.
* `measure_stoppedEndpointAtLeast_le_reset_on_cell`: if the reset roots
  are fixed on the stopped cell $A$, the same upper-tail inequality compares
  the actual continuation with the continuation using those roots on the
  original marked tree, translated by the observed $c$.
* `measure_stoppedEndpointAtLeast_le_of_remainingHorizon`: summing the
  same comparison over the finite stopping window and the occupied
  address sets gives $\mathbb P(M_H\ge x+c,\tau\le T,\mathrm{good})\le b$
  whenever all the zero-start probabilities at horizons $H-n$, $n\le T$,
  are bounded by $b$.

This is the stopped branching, initial-population comparison, and spatial
translation in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk
with Infinite Offspring* (Fudan University, 2026), Chapter 4, Theorem 1.1
for $a=0$, and Theorem 1.2 for the endpoint at the reset location.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas

open Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Coupling

local instance (priority := high) addressDecidableEq
    {κ : Type*} [LinearOrder (RootIndexed.TreeNode κ ℕ)] :
    DecidableEq (RootIndexed.TreeNode κ ℕ) :=
  LinearOrder.toDecidableEq

variable {Root : Type*} [MeasurableSpace (RootIndexed.TreeNode Root ℕ)]
  [Countable (RootIndexed.TreeNode Root ℕ)] [LinearOrder (RootIndexed.TreeNode Root ℕ)]

local notation "Ωf" => RootIndexed.StepField (Root ⊕ Root) ℕ ℝ
local notation "𝔽" => RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := ℕ) (X := ℝ)

private lemma measurableSet_jointInitialEndpoint {s : ℕ}
    [LinearOrder (RootIndexed.TreeNode (Fin s) ℕ)]
    (N k : ℕ) (x : ℝ) :
    MeasurableSet {z : (Fin s → ℝ) × RootIndexed.StepField (Fin s) ℕ ℝ |
      z.2 ∈ RootIndexed.selectedPopulationEndpointAtLeast N Finset.univ z.1 k x} := by
  have hpop := FixedHorizon.selectedPopulationTotalized_jointInitial_measurable
    (α := ℕ) (lower := s) N k
  have heq : {z : (Fin s → ℝ) × RootIndexed.StepField (Fin s) ℕ ℝ |
      z.2 ∈ RootIndexed.selectedPopulationEndpointAtLeast N Finset.univ z.1 k x} =
      ⋂ p : RootIndexed.TreeNode (Fin s) ℕ, {z |
        p ∈ RootIndexed.selectedPopulationTotalized N Finset.univ z.1 id id k z.2 →
        x ≤ RootIndexed.observedPositionAtGeneration z.1 id id k z.2 p} := by
    ext z
    simp only [RootIndexed.selectedPopulationEndpointAtLeast, Set.mem_iInter, Set.mem_ofPred_eq]
    apply forall_congr'
    intro p
    exact imp_congr_right fun hp => by
      have hdepth := RootIndexed.selectedPopulationTotalized_depth N Finset.univ z.1 id id k z.2 p hp
      rw [RootIndexed.observedPositionAtGeneration_eq _ _ _ _ _ _ hdepth]
      rfl
  rw [heq]
  exact MeasurableSet.iInter fun p => (hpop (measurableSet_mem_finset p)).imp
    (FixedHorizon.observedPosition_jointInitial_measurable k p measurableSet_Ici)

lemma measure_stoppedEndpointAtLeast_le_on_cell
    {m s : ℕ} [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    [sOrder : LinearOrder (RootIndexed.TreeNode (Fin s) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (hN : 0 < N) (hm : m ≤ N)
    (initialRoots : Finset Root) (initialPosition : Root → ℝ)
    {P : RootIndexed.CausalPopulation Ωf Root ℕ ℝ 𝔽 RootIndexed.StepField.left}
    (hP : P.FiniteSlices) (τ : Ωf → WithTop ℕ) (hτ : IsStoppingTime 𝔽 τ)
    (n k : ℕ) (roots : Fin s → RootIndexed.TreeNode Root ℕ)
    (hdepth : ∀ i, (roots i).2.length = n) (hinj : Function.Injective roots)
    (horder : ∀ p q : RootIndexed.TreeNode (Fin s) ℕ, @LT.lt _ sOrder.toLT p q ↔
      ((roots p.1).1, (roots p.1).2 ++ p.2) < ((roots q.1).1, (roots q.1).2 ++ q.2))
    (E : Set Ωf) (hE : MeasurableSet[𝔽 n] E) (x : ℝ) (c : Ωf → ℝ) (hc : Measurable[𝔽 n] c) :
    let installed := RootIndexed.stoppedRankInstalledTrajectoryField N initialRoots initialPosition hP τ hτ
    let stage := RootIndexed.restartedRealPositionNSelectedBRWField N initialRoots
      initialPosition id hP.toFinset n
    let A := E ∩ {ω | τ ω = n ∧ RootIndexed.selectedPopulationTotalized N initialRoots
      initialPosition id id n (stage ω) = Finset.univ.image roots}
    let X := fun ω => RootIndexed.subtreeInitialPosition initialPosition id (stage ω) roots
    let law := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
    (∀ ω ∈ A, ∃ e : Fin m ↪ Fin s, ∀ i, X ω (e i) ≤ c ω) →
    law (A ∩ {ω | installed ω ∈ RootIndexed.selectedPopulationEndpointAtLeast
      N initialRoots initialPosition (n + k) (x + c ω)}) ≤
      law A * RootIndexed.stepFieldLaw (Root := Fin m) μ
        (RootIndexed.selectedPopulationEndpointAtLeast N Finset.univ (fun _ => 0) k x) := by
  intro installed stage A X law hgood
  obtain ⟨hA, hX, _, _, hpop⟩ :=
    RootIndexed.stoppedRankInstalledTrajectoryField_continuation_on_cell μ N initialRoots
      initialPosition hP τ hτ n roots hdepth hinj horder E hE
  have hAfull : MeasurableSet A := ((𝔽).le n) _ hA
  let V := fun ω => RootIndexed.subtreeStepFieldVector roots (installed ω)
  let Y := fun ω i => X ω i - c ω
  have hYpast : Measurable[𝔽 n] Y := by
    let _ : MeasurableSpace Ωf := 𝔽 n
    exact measurable_pi_iff.mpr fun i => ((measurable_pi_apply i).comp hX).sub hc
  have hY : Measurable Y := hYpast.mono ((𝔽).le n) le_rfl
  let outcome := fun ω => (Y ω, V ω)
  let Q := RootIndexed.stepFieldLaw (Root := Fin s) μ
  let B := {z : (Fin s → ℝ) × RootIndexed.StepField (Fin s) ℕ ℝ |
    z.2 ∈ RootIndexed.selectedPopulationEndpointAtLeast N Finset.univ z.1 k x}
  have hB : MeasurableSet B := measurableSet_jointInitialEndpoint N k x
  have hV : Measurable V := (RootIndexed.subtreeStepFieldVector_measurable roots).comp
    (RootIndexed.stoppedRankInstalledTrajectoryField_measurable_law
      μ N initialRoots initialPosition hP τ hτ).1
  have hmeas : Measurable outcome := hY.prodMk hV
  have hlaw : (law.restrict A).map outcome = ((law.restrict A).map Y).prod Q := by
    apply Measure.ext_prod
    intro S U hS hU
    rw [Measure.map_apply hmeas (hS.prod hU), Measure.prod_prod, Measure.map_apply hY hS,
      Measure.restrict_apply (hY hS), Measure.restrict_apply (hmeas (hS.prod hU))]
    have hfactor := RootIndexed.stoppedRankInstalledTrajectoryField_subtrees_factorization
      μ N initialRoots initialPosition hP τ hτ roots hdepth hinj (A ∩ Y ⁻¹' S)
      (hA.inter (hYpast hS)) (fun ω hω => hω.1.2.1) U hU
    simpa only [outcome, V, Q, law, installed, Set.inter_assoc, Set.inter_left_comm, Set.inter_comm,
      show (fun ω => (Y ω, V ω)) ⁻¹' (S ×ˢ U) = Y ⁻¹' S ∩ V ⁻¹' U from rfl] using hfactor
  have hcompare :
      A ∩ {ω | installed ω ∈ RootIndexed.selectedPopulationEndpointAtLeast
        N initialRoots initialPosition (n + k) (x + c ω)} = A ∩ outcome ⁻¹' B := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    refine and_congr_right fun hω => ?_
    have htranslate :
        RootIndexed.selectedPopulationEndpointAtLeast (α := ℕ) N Finset.univ (X ω) k (x + c ω) =
          RootIndexed.selectedPopulationEndpointAtLeast (α := ℕ) N Finset.univ (Y ω) k x := by
      have heq : (fun i => Y ω i + c ω) = X ω := by
        funext i
        exact sub_add_cancel _ _
      rw [← RootIndexed.selectedPopulationEndpointAtLeast_add_initial (α := ℕ) N Finset.univ (Y ω)
        k x (c ω), heq]
    change (installed ω ∈ RootIndexed.selectedPopulationEndpointAtLeast N initialRoots
      initialPosition (n + k) (x + c ω)) ↔
        V ω ∈ RootIndexed.selectedPopulationEndpointAtLeast (α := ℕ) N Finset.univ (Y ω) k x
    rw [← htranslate]
    have hpositions (p : RootIndexed.TreeNode (Fin s) ℕ) :
        RootIndexed.position (X ω) id (V ω) p.1 p.2 =
          RootIndexed.position initialPosition id (installed ω)
            (roots p.1).1 ((roots p.1).2 ++ p.2) := by
      have hstage : installed ω = stage ω :=
        RootIndexed.stoppedRankInstalledTrajectoryField_eq_stage
          N initialRoots initialPosition hP τ hτ ω n hω.2.1
      dsimp only [X, V]
      rw [hstage]
      exact RootIndexed.position_subtreeStepFieldVector initialPosition id (stage ω) roots p.1 p.2
    simp only [RootIndexed.selectedPopulationEndpointAtLeast, Set.mem_ofPred_eq]
    change (∀ p ∈ RootIndexed.selectedPopulationTotalized N initialRoots initialPosition
        id id (n + k) (installed ω), x + c ω ≤ RootIndexed.position initialPosition id (installed ω) p.1 p.2) ↔
      ∀ p ∈ RootIndexed.selectedPopulationTotalized N Finset.univ (X ω) id id k (V ω),
        x + c ω ≤ RootIndexed.position (X ω) id (V ω) p.1 p.2
    rw [hpop ω hω k]
    constructor
    · intro h p hp
      rw [hpositions]
      exact h _ (Finset.mem_image_of_mem _ hp)
    · intro h p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      exact (hpositions q) ▸ h q hq
  let b := RootIndexed.stepFieldLaw (Root := Fin m) μ
    (RootIndexed.selectedPopulationEndpointAtLeast N Finset.univ (fun _ => 0) k x)
  let ν := (law.restrict A).map Y
  have htest : ∀ᵐ y ∂ν, Q (Prod.mk y ⁻¹' B) ≤ b := by
    apply (ae_map_iff hY.aemeasurable
      (measurableSet_le (measurable_measure_prodMk_left (ν := Q) hB) measurable_const)).mpr
    filter_upwards [ae_restrict_mem hAfull] with ω hω
    obtain ⟨e, he⟩ := hgood ω hω
    exact RootIndexed.measure_selectedPopulationEndpointAtLeast_le_of_cloudEmbedding
      μ hnorm N hN (by simpa using hm) (fun _ : Fin m => 0) (Y ω) e
      (fun i => sub_nonpos.mpr (he i)) k x
  rw [hcompare, Set.inter_comm, ← Measure.restrict_apply' hAfull,
    ← Measure.map_apply_of_aemeasurable hmeas.aemeasurable hB, hlaw, Measure.prod_apply hB]
  change (∫⁻ y, Q (Prod.mk y ⁻¹' B) ∂ν) ≤ law A * b
  calc
    _ ≤ ∫⁻ _, b ∂ν := lintegral_mono_ae htest
    _ = _ := by
      rw [lintegral_const, Measure.map_apply hY MeasurableSet.univ, Set.preimage_univ,
        Measure.restrict_apply_univ, mul_comm]

/-- Compare both continuations on the same stopped cell. The reset uses
the pre-sampled descendants of its original roots. Conditioning on the cell
gives the same fresh offspring law as in the initial-population comparison. -/
lemma measure_stoppedEndpointAtLeast_le_reset_on_cell
    {m s : ℕ} [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    [sOrder : LinearOrder (RootIndexed.TreeNode (Fin s) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (hN : 0 < N) (hm : m ≤ N)
    (initialRoots : Finset Root) (initialPosition : Root → ℝ)
    {P : RootIndexed.CausalPopulation Ωf Root ℕ ℝ 𝔽 RootIndexed.StepField.left}
    (hP : P.FiniteSlices) (τ : Ωf → WithTop ℕ) (hτ : IsStoppingTime 𝔽 τ)
    (n k : ℕ) (roots : Fin s → RootIndexed.TreeNode Root ℕ)
    (hdepth : ∀ i, (roots i).2.length = n) (hinj : Function.Injective roots)
    (horder : ∀ p q : RootIndexed.TreeNode (Fin s) ℕ, @LT.lt _ sOrder.toLT p q ↔
      ((roots p.1).1, (roots p.1).2 ++ p.2) < ((roots q.1).1, (roots q.1).2 ++ q.2))
    (resetRoots : Fin m → RootIndexed.TreeNode (Root ⊕ Root) ℕ)
    (hresetDepth : ∀ i, (resetRoots i).2.length = n) (hresetInj : Function.Injective resetRoots)
    (E : Set Ωf) (hE : MeasurableSet[𝔽 n] E) (x : ℝ) (c : Ωf → ℝ) (hc : Measurable[𝔽 n] c) :
    let installed := RootIndexed.stoppedRankInstalledTrajectoryField N initialRoots initialPosition hP τ hτ
    let stage := RootIndexed.restartedRealPositionNSelectedBRWField N initialRoots
      initialPosition id hP.toFinset n
    let A := E ∩ {ω | τ ω = n ∧ RootIndexed.selectedPopulationTotalized N initialRoots
      initialPosition id id n (stage ω) = Finset.univ.image roots}
    let X := fun ω => RootIndexed.subtreeInitialPosition initialPosition id (stage ω) roots
    let law := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
    (∀ ω ∈ A, ∃ e : Fin m ↪ Fin s, ∀ i, X ω (e i) ≤ c ω) →
    law (A ∩ {ω | installed ω ∈ RootIndexed.selectedPopulationEndpointAtLeast
      N initialRoots initialPosition (n + k) (x + c ω)}) ≤
      law (A ∩ {ω | RootIndexed.subtreeStepFieldVector resetRoots ω ∈
        RootIndexed.selectedPopulationEndpointAtLeast N Finset.univ (fun _ => c ω) k (x + c ω)}) := by
  intro installed stage A X law hgood
  have hA : MeasurableSet[𝔽 n] A :=
    (RootIndexed.stoppedRankInstalledTrajectoryField_continuation_on_cell μ N initialRoots
      initialPosition hP τ hτ n roots hdepth hinj horder E hE).1
  let B := RootIndexed.selectedPopulationEndpointAtLeast (α := ℕ) N (Finset.univ : Finset (Fin m))
    (fun _ => 0) k x
  have hB : MeasurableSet B := RootIndexed.measurableSet_selectedPopulationEndpointAtLeast _ _ _ _ _
  have hshift (ω : Ωf) :
      RootIndexed.selectedPopulationEndpointAtLeast (α := ℕ) N (Finset.univ : Finset (Fin m))
        (fun _ => c ω) k (x + c ω) = B := by
    simpa only [zero_add] using
      RootIndexed.selectedPopulationEndpointAtLeast_add_initial (α := ℕ) N
        (Finset.univ : Finset (Fin m)) (fun _ => 0) k x (c ω)
  simp_rw [hshift]
  change _ ≤ law (A ∩ RootIndexed.subtreeStepFieldVector resetRoots ⁻¹' B)
  rw [RootIndexed.subtreeStepFieldVector_event_factorization μ resetRoots hresetDepth hresetInj A B hA hB]
  exact measure_stoppedEndpointAtLeast_le_on_cell μ hnorm N hN hm initialRoots initialPosition
    hP τ hτ n k roots hdepth hinj horder E hE x c hc hgood

lemma measure_stoppedEndpointAtLeast_le_of_remainingHorizon
    {m : ℕ} [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (hN : 0 < N) (hm : m ≤ N)
    (initialRoots : Finset Root) (initialPosition : Root → ℝ)
    {P : RootIndexed.CausalPopulation Ωf Root ℕ ℝ 𝔽 RootIndexed.StepField.left}
    (hP : P.FiniteSlices) (τ : Ωf → WithTop ℕ) (hτ : IsStoppingTime 𝔽 τ)
    (H T : ℕ) (hT : T ≤ H)
    (E : ℕ → Set Ωf) (hE : ∀ n, MeasurableSet[𝔽 n] (E n)) (x c : ℝ) (b : ℝ≥0∞)
    (hbound : ∀ n ≤ T, RootIndexed.stepFieldLaw (Root := Fin m) μ
      (RootIndexed.selectedPopulationEndpointAtLeast N Finset.univ (fun _ => 0) (H - n) x) ≤ b) :
    let installed := RootIndexed.stoppedRankInstalledTrajectoryField N initialRoots initialPosition hP τ hτ
    let stage := RootIndexed.restartedRealPositionNSelectedBRWField N initialRoots
      initialPosition id hP.toFinset
    let Pop n ω := RootIndexed.selectedPopulationTotalized N initialRoots initialPosition id id n (stage n ω)
    (∀ ω n, ω ∈ E n → τ ω = n →
      ∃ e : Fin m ↪ RootIndexed.TreeNode Root ℕ, ∀ i, e i ∈ Pop n ω ∧
        RootIndexed.position initialPosition id (stage n ω) (e i).1 (e i).2 ≤ c) →
    RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
      ({ω | ∃ n ≤ T, ω ∈ E n ∧ τ ω = n} ∩
        installed ⁻¹' RootIndexed.selectedPopulationEndpointAtLeast N initialRoots
          initialPosition H (x + c)) ≤ b := by
  intro installed stage Pop hgood
  classical
  let law := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
  let I := Fin (T + 1) × Finset (RootIndexed.TreeNode Root ℕ)
  let A (j : I) := E j.1 ∩ {ω | τ ω = (j.1.val : WithTop ℕ) ∧ Pop j.1 ω = j.2}
  let B := installed ⁻¹' RootIndexed.selectedPopulationEndpointAtLeast N initialRoots
    initialPosition H (x + c)
  have hset : {ω | ∃ n ≤ T, ω ∈ E n ∧ τ ω = n} ∩ B = ⋃ j, A j ∩ B := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, A]
    constructor
    · rintro ⟨⟨n, hn, hEn, hτn⟩, hB⟩
      exact ⟨(⟨n, Nat.lt_succ_of_le hn⟩, Pop n ω), ⟨hEn, hτn, rfl⟩, hB⟩
    · rintro ⟨⟨i, s⟩, ⟨hEn, hτn, _⟩, hB⟩
      exact ⟨⟨i, Nat.le_of_lt_succ i.isLt, hEn, hτn⟩, hB⟩
  have hAmeas (j : I) : MeasurableSet (A j) := by
    have hstage := RootIndexed.restartedRealPositionNSelectedBRWField_filtration_measurable
      N initialRoots initialPosition hP j.1.val
    have hpop : Measurable[𝔽 j.1.val] (Pop j.1.val) :=
      (RootIndexed.selectedPopulationTotalized_adapted N initialRoots initialPosition
        id measurable_id id measurable_id j.1.val).comp hstage
    exact ((𝔽).le j.1.val) _
      ((hE j.1.val).inter ((hτ.measurableSet_eq j.1.val).inter (hpop (measurableSet_singleton _))))
  have hdisj : Pairwise (fun j k : I => Disjoint (A j) (A k)) := by
    intro j k hjk
    apply Set.disjoint_left.mpr
    intro ω hj hk
    apply hjk
    have htime : j.1 = k.1 := Fin.ext (WithTop.coe_injective (hj.2.1.symm.trans hk.2.1))
    exact Prod.ext htime (hj.2.2.symm.trans (by simpa only [htime] using hk.2.2))
  have hcell (j : I) : law (A j ∩ B) ≤ law (A j) * b := by
    obtain ⟨n, S⟩ := j
    obtain ⟨roots, hmap⟩ :=
      Function.Embedding.exists_of_card_eq_finset (α := Fin S.card) (s := S) (by simp)
    have hcover : Finset.univ.image roots = S := by
      rw [← Finset.map_eq_image]
      exact hmap
    by_cases hdepth : ∀ i, (roots i).2.length = n.val
    · let embed (p : RootIndexed.TreeNode (Fin S.card) ℕ) : RootIndexed.TreeNode Root ℕ :=
        ((roots p.1).1, (roots p.1).2 ++ p.2)
      let o : LinearOrder (RootIndexed.TreeNode (Fin S.card) ℕ) :=
        LinearOrder.lift' embed (Combinatorics.UlamHarris.RootIndexed.appendAddresses_injective
          roots hdepth roots.injective)
      have hgoodCell (ω : Ωf) (hω : ω ∈ A (n, S)) :
          ∃ e : Fin m ↪ Fin S.card, ∀ i,
            RootIndexed.subtreeInitialPosition initialPosition id (stage n.val ω) roots (e i) ≤ c := by
        obtain ⟨e, he⟩ := hgood ω n.val hω.1 hω.2.1
        have hpre (i : Fin m) : ∃ j, roots j = e i := by
          have hi := (he i).1
          rw [hω.2.2, ← hcover] at hi
          obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hi
          exact ⟨k, hk⟩
        choose f hf using hpre
        refine ⟨⟨f, fun i j hij => e.injective ((hf i).symm.trans ((congrArg roots hij).trans (hf j)))⟩,
          fun i => ?_⟩
        change RootIndexed.position initialPosition id (stage n.val ω)
          (roots (f i)).1 (roots (f i)).2 ≤ c
        rw [hf i]
        exact (he i).2
      have hnT := Nat.le_of_lt_succ n.isLt
      have h := @measure_stoppedEndpointAtLeast_le_on_cell Root _ _ _ m S.card _ o
        μ _ hnorm N hN hm initialRoots initialPosition P hP τ hτ n.val (H - n.val)
        roots hdepth roots.injective (fun _ _ => Iff.rfl) (E n.val) (hE n.val) x (fun _ => c) measurable_const
      have hc : n.val + (H - n.val) = H := Nat.add_sub_of_le (hnT.trans hT)
      have hAeq : A (n, S) =
          E n.val ∩ {ω | τ ω = n.val ∧ Pop n.val ω = Finset.univ.image roots} := by
        ext ω
        simp only [A, hcover]
      have hconcl := h (fun ω hω => hgoodCell ω (hAeq ▸ hω))
      rw [hc] at hconcl
      change law ((E n.val ∩ {ω | τ ω = n.val ∧
        Pop n.val ω = Finset.univ.image roots}) ∩ B) ≤
        law (E n.val ∩ {ω | τ ω = n.val ∧ Pop n.val ω = Finset.univ.image roots}) * _ at hconcl
      rw [← hAeq] at hconcl
      exact hconcl.trans (mul_le_mul_right (hbound _ hnT) _)
    · have hnil : A (n, S) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro ω hω
        apply hdepth
        intro i
        have hm : roots i ∈ Pop n.val ω := by
          have hr : roots i ∈ Finset.univ.image roots :=
            Finset.mem_image_of_mem _ (Finset.mem_univ i)
          have hpop : Pop n.val ω = S := hω.2.2
          rw [hpop]
          exact (congrArg (fun s : Finset (RootIndexed.TreeNode Root ℕ) => roots i ∈ s)
            hcover).mp hr
        exact RootIndexed.selectedPopulationTotalized_depth N initialRoots initialPosition
          id id n.val (stage n.val ω) (roots i) hm
      simp [hnil]
  change law (_ ∩ B) ≤ b
  rw [hset]
  calc
    _ ≤ ∑' j, law (A j ∩ B) := measure_iUnion_le _
    _ ≤ ∑' j, law (A j) * b := tsum_le_tsum hcell
    _ = law (⋃ j, A j) * b := by rw [ENNReal.tsum_mul_right, measure_iUnion hdisj hAmeas]
    _ ≤ b := by
      have hmass : law (⋃ j, A j) ≤ 1 :=
        (measure_mono (Set.subset_univ _)).trans_eq measure_univ
      simpa using mul_le_mul_left hmass b

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas
