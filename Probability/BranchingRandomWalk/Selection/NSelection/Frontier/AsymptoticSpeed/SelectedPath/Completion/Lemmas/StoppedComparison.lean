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
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.Entrance

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
  original marked tree, translated by the observed $c$. The threshold is a
  fixed absolute endpoint level $x$.
* `measure_stoppedEndpointAtLeast_le_reset_on_finiteCompletion` sums the absolute
  tail comparison over the stopping generations up to the terminal horizon
  and over the two vectors of descendant roots.
* `measure_stoppedEndpointAtLeast_le_trialReset`: from the original trial
  maximum and a stopped enumeration of its roots, the comparison applies
  on all completions up to the terminal generation.
* `trialRestartEndpointAtLeast_beforeReset_ae`: on $H\le\tau$, the actual
  tail event at level $x$ implies the same lower bound for every particle of
  the original pre-reset terminal slice.
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
      μ hnorm.ae_isLeftLocallyFinite N hN (by simpa using hm) (fun _ : Fin m => 0) (Y ω) e
      (fun i => sub_nonpos.mpr (he i)) k x
  rw [hcompare, Set.inter_comm, ← Measure.restrict_apply' hAfull,
    ← Measure.map_apply_of_aemeasurable hmeas.aemeasurable hB, hlaw, Measure.prod_apply hB]
  change (∫⁻ y, Q (Prod.mk y ⁻¹' B) ∂ν) ≤ law A * b
  calc
    _ ≤ ∫⁻ _, b ∂ν := lintegral_mono_ae htest
    _ = _ := by
      rw [lintegral_const, Measure.map_apply hY MeasurableSet.univ, Set.preimage_univ,
        Measure.restrict_apply_univ, mul_comm]

omit [MeasurableSpace (RootIndexed.TreeNode Root ℕ)]
  [Countable (RootIndexed.TreeNode Root ℕ)] [LinearOrder (RootIndexed.TreeNode Root ℕ)] in
private lemma measure_cell_test_eq_lintegral
    {Past Future : Type*} [MeasurableSpace Past] [MeasurableSpace Future]
    (law : Measure Ωf) [IsFiniteMeasure law] (Q : Measure Future) [IsFiniteMeasure Q]
    (n : ℕ) (A : Set Ωf) (hA : MeasurableSet[𝔽 n] A)
    (past : Ωf → Past) (hpast : Measurable[𝔽 n] past)
    (future : Ωf → Future) (hfuture : Measurable future)
    (hfactor : ∀ (S : Set Past), MeasurableSet S → ∀ (U : Set Future), MeasurableSet U →
      law ((A ∩ past ⁻¹' S) ∩ future ⁻¹' U) = law (A ∩ past ⁻¹' S) * Q U)
    (B : Set (Past × Future)) (hB : MeasurableSet B) :
    law (A ∩ (fun ω => (past ω, future ω)) ⁻¹' B) =
      ∫⁻ ω in A, Q (Prod.mk (past ω) ⁻¹' B) ∂law := by
  have hAfull : MeasurableSet A := ((𝔽).le n) _ hA
  have hp : Measurable past := hpast.mono ((𝔽).le n) le_rfl
  have hpair := hp.prodMk hfuture
  have hprod : (law.restrict A).map (fun ω => (past ω, future ω)) =
      ((law.restrict A).map past).prod Q := by
    apply Measure.ext_prod
    intro S U hS hU
    rw [Measure.map_apply hpair (hS.prod hU), Measure.prod_prod,
      Measure.map_apply hp hS, Measure.restrict_apply (hp hS),
      Measure.restrict_apply (hpair (hS.prod hU))]
    simpa only [Set.inter_assoc, Set.inter_left_comm, Set.inter_comm,
      show (fun ω => (past ω, future ω)) ⁻¹' (S ×ˢ U) =
        past ⁻¹' S ∩ future ⁻¹' U from rfl] using hfactor S hS U hU
  rw [Set.inter_comm, ← Measure.restrict_apply' hAfull, ← Measure.map_apply hpair hB,
    hprod, Measure.prod_apply hB, lintegral_map (measurable_measure_prodMk_left (ν := Q) hB) hp]

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
      N initialRoots initialPosition (n + k) x}) ≤
      law (A ∩ {ω | RootIndexed.subtreeStepFieldVector resetRoots ω ∈
        RootIndexed.selectedPopulationEndpointAtLeast N Finset.univ (fun _ => c ω) k x}) := by
  intro installed stage A X law hgood
  obtain ⟨hA, hX, _, _, hpop⟩ :=
    RootIndexed.stoppedRankInstalledTrajectoryField_continuation_on_cell μ N initialRoots
      initialPosition hP τ hτ n roots hdepth hinj horder E hE
  let Q := RootIndexed.stepFieldLaw (Root := Fin s) μ
  let Qreset := RootIndexed.stepFieldLaw (Root := Fin m) μ
  let V := fun ω => RootIndexed.subtreeStepFieldVector roots (installed ω)
  let W : Ωf → RootIndexed.StepField (Fin m) ℕ ℝ := RootIndexed.subtreeStepFieldVector resetRoots
  let B := {z : (Fin s → ℝ) × RootIndexed.StepField (Fin s) ℕ ℝ |
    z.2 ∈ RootIndexed.selectedPopulationEndpointAtLeast N Finset.univ z.1 k x}
  let Breset := {z : (Fin m → ℝ) × RootIndexed.StepField (Fin m) ℕ ℝ |
    z.2 ∈ RootIndexed.selectedPopulationEndpointAtLeast N Finset.univ z.1 k x}
  let C : Ωf → Fin m → ℝ := fun ω _ => c ω
  have hB : MeasurableSet B := measurableSet_jointInitialEndpoint N k x
  have hBreset : MeasurableSet Breset := measurableSet_jointInitialEndpoint N k x
  have hC : Measurable[𝔽 n] C := by
    let _ : MeasurableSpace Ωf := 𝔽 n
    exact measurable_pi_iff.mpr fun _ => hc
  have hV : Measurable V := (RootIndexed.subtreeStepFieldVector_measurable roots).comp
    (RootIndexed.stoppedRankInstalledTrajectoryField_measurable_law
      μ N initialRoots initialPosition hP τ hτ).1
  have hW : Measurable W := RootIndexed.subtreeStepFieldVector_measurable resetRoots
  have hactual := measure_cell_test_eq_lintegral law Q n A hA X hX V hV
    (fun S hS U hU =>
      RootIndexed.stoppedRankInstalledTrajectoryField_subtrees_factorization μ N
        initialRoots initialPosition hP τ hτ roots hdepth hinj
        (A ∩ X ⁻¹' S) (hA.inter (hX hS)) (fun ω hω => hω.1.2.1) U hU) B hB
  have hreset := measure_cell_test_eq_lintegral law Qreset n A hA C hC W hW
    (fun S hS U hU => RootIndexed.subtreeStepFieldVector_event_factorization μ
      resetRoots hresetDepth hresetInj (A ∩ C ⁻¹' S) U (hA.inter (hC hS)) hU) Breset hBreset
  have hcompare : A ∩ {ω | installed ω ∈ RootIndexed.selectedPopulationEndpointAtLeast
      N initialRoots initialPosition (n + k) x} = A ∩ (fun ω => (X ω, V ω)) ⁻¹' B := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    refine and_congr_right fun hω => ?_
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
    change (∀ p ∈ RootIndexed.selectedPopulationTotalized N initialRoots initialPosition
        id id (n + k) (installed ω), x ≤ RootIndexed.position initialPosition id (installed ω) p.1 p.2) ↔
      ∀ p ∈ RootIndexed.selectedPopulationTotalized N Finset.univ (X ω) id id k (V ω),
        x ≤ RootIndexed.position (X ω) id (V ω) p.1 p.2
    rw [hpop ω hω k]
    constructor
    · intro h p hp
      rw [hpositions]
      exact h _ (Finset.mem_image_of_mem _ hp)
    · intro h p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      exact (hpositions q) ▸ h q hq
  rw [hcompare, hactual]
  change _ ≤ law (A ∩ (fun ω => (C ω, W ω)) ⁻¹' Breset)
  rw [hreset]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (((𝔽).le n) _ hA)] with ω hω
  obtain ⟨e, he⟩ := hgood ω hω
  exact RootIndexed.measure_selectedPopulationEndpointAtLeast_le_of_cloudEmbedding
    μ hnorm.ae_isLeftLocallyFinite N hN (by simpa using hm) (C ω) (X ω) e he k x

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

/-- Sum the comparison over the stopping generation, the occupied actual
addresses, and the original reset roots. The threshold is kept fixed in
absolute position, which permits comparison of the negative endpoint tails. -/
lemma measure_stoppedEndpointAtLeast_le_reset_on_finiteCompletion
    {m : ℕ} [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    [Countable (RootIndexed.TreeNode (Root ⊕ Root) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (hN : 0 < N) (hm : m ≤ N)
    (initialRoots : Finset Root) (initialPosition : Root → ℝ)
    {P : RootIndexed.CausalPopulation Ωf Root ℕ ℝ 𝔽 RootIndexed.StepField.left}
    (hP : P.FiniteSlices) (τ : Ωf → WithTop ℕ) (hτ : IsStoppingTime 𝔽 τ)
    (H : ℕ) (x : ℝ)
    (E : ℕ → Set Ωf) (hE : ∀ n, MeasurableSet[𝔽 n] (E n))
    (c : ℕ → Ωf → ℝ) (hc : ∀ n, Measurable[𝔽 n] (c n))
    (resetRoots : Ωf → Fin m → RootIndexed.TreeNode (Root ⊕ Root) ℕ)
    (hfiber : ∀ v, MeasurableSet[hτ.measurableSpace] {ω | resetRoots ω = v})
    (hdepth : ∀ ω (n : ℕ), τ ω = n → ∀ i, (resetRoots ω i).2.length = n)
    (hinj : ∀ ω, τ ω ≠ ⊤ → Function.Injective (resetRoots ω)) :
    let installed := RootIndexed.stoppedRankInstalledTrajectoryField N initialRoots initialPosition hP τ hτ
    let stage := RootIndexed.restartedRealPositionNSelectedBRWField N initialRoots
      initialPosition id hP.toFinset
    let Pop n ω := RootIndexed.selectedPopulationTotalized N initialRoots initialPosition id id n (stage n ω)
    let law := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
    (∀ᵐ ω ∂law, ∀ n ≤ H, ω ∈ E n → τ ω = n →
      ∃ e : Fin m ↪ RootIndexed.TreeNode Root ℕ, ∀ i, e i ∈ Pop n ω ∧
        RootIndexed.position initialPosition id (stage n ω) (e i).1 (e i).2 ≤ c n ω) →
    law ({ω | ∃ n ≤ H, ω ∈ E n ∧ τ ω = n} ∩ installed ⁻¹'
      RootIndexed.selectedPopulationEndpointAtLeast N initialRoots initialPosition H x) ≤
      law {ω | ∃ n ≤ H, ω ∈ E n ∧ τ ω = n ∧
        RootIndexed.subtreeStepFieldVector (resetRoots ω) ω ∈
          RootIndexed.selectedPopulationEndpointAtLeast N Finset.univ (fun _ => c n ω) (H - n) x} := by
  intro installed stage Pop law hgood
  classical
  let I := Fin (H + 1) × Finset (RootIndexed.TreeNode Root ℕ) ×
    (Fin m → RootIndexed.TreeNode (Root ⊕ Root) ℕ)
  let B := installed ⁻¹' RootIndexed.selectedPopulationEndpointAtLeast N initialRoots initialPosition H x
  let A (j : I) := (E j.1 ∩ {ω | resetRoots ω = j.2.2}) ∩
    {ω | τ ω = (j.1.val : WithTop ℕ) ∧ Pop j.1 ω = j.2.1}
  let D (j : I) := {ω | RootIndexed.subtreeStepFieldVector j.2.2 ω ∈
    RootIndexed.selectedPopulationEndpointAtLeast N Finset.univ (fun _ => c j.1 ω) (H - j.1) x}
  let good (n : ℕ) : Set Ωf := {ω | ∃ e : Fin m ↪ RootIndexed.TreeNode Root ℕ,
    ∀ i, e i ∈ Pop n ω ∧
      RootIndexed.position initialPosition id (stage n ω) (e i).1 (e i).2 ≤ c n ω}
  have hstage (n : ℕ) := RootIndexed.restartedRealPositionNSelectedBRWField_filtration_measurable
    N initialRoots initialPosition hP n
  have hpop (n : ℕ) : Measurable[𝔽 n] (Pop n) :=
    (RootIndexed.selectedPopulationTotalized_adapted N initialRoots initialPosition
      id measurable_id id measurable_id n).comp (hstage n)
  let _ : Countable (Fin m ↪ RootIndexed.TreeNode Root ℕ) :=
    Function.Embedding.coe_injective.countable
  have hgoodMeas (n : ℕ) : MeasurableSet[𝔽 n] (good n) := by
    have hset : good n = ⋃ e : Fin m ↪ RootIndexed.TreeNode Root ℕ,
        ⋂ i : Fin m, {ω | e i ∈ Pop n ω ∧
          RootIndexed.position initialPosition id (stage n ω) (e i).1 (e i).2 ≤ c n ω} := by
      ext ω
      simp [good]
    rw [hset]
    apply MeasurableSet.iUnion
    intro e
    apply MeasurableSet.iInter
    intro i
    have hpos := (RootIndexed.positionAtGeneration_measurable initialPosition id measurable_id
      n (e i).1 (e i).2).comp (hstage n)
    have hmem := hpop n (measurableSet_mem_finset (e i))
    convert hmem.inter (measurableSet_le hpos (hc n)) using 1
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage]
    refine and_congr_right fun hω => ?_
    have he := RootIndexed.selectedPopulationTotalized_depth N initialRoots initialPosition
      id id n (stage n ω) (e i) hω
    simp [RootIndexed.positionAtGeneration, he, stage]
  have hEcell (j : I) : MeasurableSet[𝔽 j.1.val]
      ((E j.1 ∩ {ω | resetRoots ω = j.2.2}) ∩ {ω | τ ω = (j.1.val : WithTop ℕ)}) := by
    have hh := (hτ.measurableSet_inter_eq_iff {ω | resetRoots ω = j.2.2} j.1.val).1
      ((hfiber j.2.2).inter (hτ.measurable (measurableSet_singleton _)))
    rw [Set.inter_assoc]
    exact (hE j.1.val).inter hh
  have hAmeas (j : I) : MeasurableSet[𝔽 j.1.val] (A j) := by
    have hm : MeasurableSet[𝔽 j.1.val] {ω | Pop j.1.val ω = j.2.1} :=
      hpop j.1.val (measurableSet_singleton j.2.1)
    rw [show A j = ((E j.1 ∩ {ω | resetRoots ω = j.2.2}) ∩
      {ω | τ ω = (j.1.val : WithTop ℕ)}) ∩ {ω | Pop j.1 ω = j.2.1} by
        ext ω
        simp only [A, Set.mem_inter_iff, Set.mem_ofPred_eq, and_assoc]]
    exact (hEcell j).inter hm
  have hDmeas (j : I) : MeasurableSet (D j) := by
    let f : Ωf → (Fin m → ℝ) × RootIndexed.StepField (Fin m) ℕ ℝ :=
      fun ω => ((fun _ => c j.1 ω), RootIndexed.subtreeStepFieldVector j.2.2 ω)
    have hf : Measurable f := (measurable_pi_iff.mpr fun _ =>
      (hc j.1.val).mono ((𝔽).le j.1.val) le_rfl).prodMk
      (RootIndexed.subtreeStepFieldVector_measurable j.2.2)
    exact hf (measurableSet_jointInitialEndpoint N (H - j.1.val) x)
  have hdisj : Pairwise (fun j k : I => Disjoint (A j ∩ D j) (A k ∩ D k)) := by
    intro j k hjk
    apply Set.disjoint_left.mpr
    intro ω hj hk
    apply hjk
    have ht : j.1 = k.1 :=
      Fin.ext (WithTop.coe_injective (hj.1.2.1.symm.trans hk.1.2.1))
    refine Prod.ext ht (Prod.ext ?_ (hj.1.1.2.symm.trans hk.1.1.2))
    exact hj.1.2.2.symm.trans (by simpa only [ht] using hk.1.2.2)
  have hcell (j : I) : law (A j ∩ B) ≤ law (A j ∩ D j) := by
    obtain ⟨n, S, v⟩ := j
    have hn : n.val ≤ H := Nat.le_of_lt_succ n.isLt
    by_cases hempty : (A (n, S, v)).Nonempty
    · obtain ⟨ω₀, hω₀⟩ := hempty
      obtain ⟨roots, hmap⟩ :=
        Function.Embedding.exists_of_card_eq_finset (α := Fin S.card) (s := S) (by simp)
      have hcover : Finset.univ.image roots = S := by
        rw [← Finset.map_eq_image]
        exact hmap
      have hrootsDepth (i : Fin S.card) : (roots i).2.length = n.val := by
        apply RootIndexed.selectedPopulationTotalized_depth N initialRoots initialPosition
          id id n.val (stage n.val ω₀)
        change roots i ∈ Pop n.val ω₀
        have hs : Pop n.val ω₀ = S := hω₀.2.2
        rw [hs]
        exact (congrArg (fun s : Finset (RootIndexed.TreeNode Root ℕ) => roots i ∈ s) hcover).mp
          (Finset.mem_image_of_mem _ (Finset.mem_univ i))
      have hv : resetRoots ω₀ = v := hω₀.1.2
      have hvDepth : ∀ i, (v i).2.length = n.val := hv ▸ hdepth ω₀ n.val hω₀.2.1
      have hvInj : Function.Injective v := hv ▸ hinj ω₀ (hω₀.2.1.trans_ne WithTop.coe_ne_top)
      let embed (p : RootIndexed.TreeNode (Fin S.card) ℕ) : RootIndexed.TreeNode Root ℕ :=
        ((roots p.1).1, (roots p.1).2 ++ p.2)
      let o : LinearOrder (RootIndexed.TreeNode (Fin S.card) ℕ) :=
        LinearOrder.lift' embed (Combinatorics.UlamHarris.RootIndexed.appendAddresses_injective
          roots hrootsDepth roots.injective)
      let cell := ((E n.val ∩ {ω | resetRoots ω = v}) ∩ {ω | τ ω = (n.val : WithTop ℕ)})
        ∩ good n.val
      have hcellMeas : MeasurableSet[𝔽 n.val] cell :=
        (hEcell (n, S, v)).inter (hgoodMeas n.val)
      have hAeq : cell ∩ {ω | τ ω = (n.val : WithTop ℕ) ∧
          Pop n.val ω = Finset.univ.image roots} = A (n, S, v) ∩ good n.val := by
        ext ω
        simp only [cell, A, hcover, Set.mem_inter_iff, Set.mem_ofPred_eq]
        tauto
      have hmatch (ω : Ωf) (hω : ω ∈ A (n, S, v) ∩ good n.val) :
          ∃ e : Fin m ↪ Fin S.card, ∀ i,
            RootIndexed.subtreeInitialPosition initialPosition id (stage n.val ω) roots (e i) ≤ c n.val ω := by
        obtain ⟨e, he⟩ := hω.2
        have hpre (i : Fin m) : ∃ j, roots j = e i := by
          have hi := (he i).1
          rw [hω.1.2.2, ← hcover] at hi
          obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hi
          exact ⟨k, hk⟩
        choose f hf using hpre
        refine ⟨⟨f, fun i j hij => e.injective ((hf i).symm.trans ((congrArg roots hij).trans (hf j)))⟩,
          fun i => ?_⟩
        change RootIndexed.position initialPosition id (stage n.val ω)
          (roots (f i)).1 (roots (f i)).2 ≤ c n.val ω
        rw [hf i]
        exact (he i).2
      have h := @measure_stoppedEndpointAtLeast_le_reset_on_cell Root _ _ _ m S.card _ o
        μ _ hnorm N hN hm initialRoots initialPosition P hP τ hτ n.val (H - n.val)
        roots hrootsDepth roots.injective (fun _ _ => Iff.rfl) v hvDepth hvInj
        cell hcellMeas x (c n.val) (hc n.val)
      have hbound := h (fun ω hω => hmatch ω (hAeq ▸ hω))
      rw [Nat.add_sub_of_le hn] at hbound
      change law ((cell ∩ {ω | τ ω = (n.val : WithTop ℕ) ∧
        Pop n.val ω = Finset.univ.image roots}) ∩ B) ≤ _ at hbound
      rw [hAeq] at hbound
      have htrim : A (n, S, v) ∩ B =ᵐ[law] (A (n, S, v) ∩ good n.val) ∩ B := by
        filter_upwards [hgood] with ω hω
        constructor
        · intro hh
          exact ⟨⟨hh.1, hω n.val hn hh.1.1.1 hh.1.2.1⟩, hh.2⟩
        · exact fun hh => ⟨hh.1.1, hh.2⟩
      rw [measure_congr htrim]
      exact hbound.trans (measure_mono fun ω hω => ⟨hω.1.1, hω.2⟩)
    · rw [Set.not_nonempty_iff_eq_empty.mp hempty, Set.empty_inter, measure_empty]
      exact bot_le
  have hleft : {ω | ∃ n ≤ H, ω ∈ E n ∧ τ ω = n} ∩ B = ⋃ j, A j ∩ B := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion, A]
    constructor
    · rintro ⟨⟨n, hn, hEn, hτn⟩, hB⟩
      exact ⟨(⟨n, Nat.lt_succ_of_le hn⟩, Pop n ω, resetRoots ω), ⟨⟨hEn, rfl⟩, hτn, rfl⟩, hB⟩
    · rintro ⟨⟨i, _, _⟩, ⟨⟨hEn, _⟩, hτn, _⟩, hB⟩
      exact ⟨⟨i, Nat.le_of_lt_succ i.isLt, hEn, hτn⟩, hB⟩
  change law (_ ∩ B) ≤ _
  rw [hleft]
  calc
    _ ≤ ∑' j, law (A j ∩ B) := measure_iUnion_le _
    _ ≤ ∑' j, law (A j ∩ D j) := tsum_le_tsum hcell
    _ = law (⋃ j, A j ∩ D j) := by
      rw [measure_iUnion hdisj (fun j => (((𝔽).le j.1.val) _ (hAmeas j)).inter (hDmeas j))]
    _ ≤ _ := by
      apply measure_mono
      intro ω hω
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hω
      refine ⟨j.1.val, Nat.le_of_lt_succ j.1.isLt, hj.1.1.1, hj.1.2.1, ?_⟩
      have heq : resetRoots ω = j.2.2 := hj.1.1.2
      rw [heq]
      exact hj.2

open SelectedPath.GrowthTrial in
/-- Use the maximum of the successful trial as the reset position on the
pre-sampled marked tree. Each root vector is selected at the completion
generation. -/
lemma measure_stoppedEndpointAtLeast_le_trialReset
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root ℕ)]
    [Countable (RootIndexed.TreeNode (Root ⊕ Root) ℕ)]
    {m : ℕ} [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (hN : 0 < N) (hm : m ≤ N)
    (R growth : Step.FiniteSelection ℕ ℝ)
    (hR : Measurable R.select) (hgrowth : Measurable growth.select)
    (lower upper duration : ℕ) (hmLower : m ≤ lower) (hupper : 1 ≤ upper)
    (hbounded : growth.IsBoundedBy 2) (hcapacity : 1 + (duration + 1) * (2 * upper) ≤ N)
    (r : Root) (H : ℕ) (x : ℝ)
    (E : ℕ → Set Ωf) (hE : ∀ n, MeasurableSet[𝔽 n] (E n))
    (resetRoots : Ωf → Fin m → RootIndexed.TreeNode (Root ⊕ Root) ℕ) :
    let τ := Completion.time R growth hR hgrowth lower upper duration r
    let hτ := Completion.time_isStoppingTime R growth hR hgrowth lower upper duration r
    let trials := SelectedPath.Population.leftBRWFamily_finiteSlices R growth hR hgrowth
      upper duration r
    let installed := RootIndexed.stoppedRankInstalledTrajectoryField N {r}
      (fun _ => 0) trials τ hτ
    let c n ω := trialResetPositionAtGeneration R growth hR upper duration r n
      (RootIndexed.StepField.left ω)
    let law := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
    (∀ v, MeasurableSet[hτ.measurableSpace] {ω | resetRoots ω = v}) →
    (∀ ω (n : ℕ), τ ω = n → ∀ i, (resetRoots ω i).2.length = n) →
    (∀ ω, τ ω ≠ ⊤ → Function.Injective (resetRoots ω)) →
    law ({ω | ∃ n ≤ H, ω ∈ E n ∧ τ ω = n} ∩ installed ⁻¹'
      RootIndexed.selectedPopulationEndpointAtLeast N {r} (fun _ => 0) H x) ≤
      law {ω | ∃ n ≤ H, ω ∈ E n ∧ τ ω = n ∧
        RootIndexed.subtreeStepFieldVector (resetRoots ω) ω ∈
          RootIndexed.selectedPopulationEndpointAtLeast N Finset.univ (fun _ => c n ω) (H - n) x} := by
  intro τ hτ trials installed c law hfiber hdepth hinj
  let E' (n : ℕ) := if duration ≤ n then E n else ∅
  let c' (n : ℕ) : Ωf → ℝ := if duration ≤ n then c n else fun _ => 0
  have hE' (n : ℕ) : MeasurableSet[𝔽 n] (E' n) := by
    by_cases hn : duration ≤ n <;> simp [E', hn, hE]
  have hc' (n : ℕ) : Measurable[𝔽 n] (c' n) := by
    by_cases hn : duration ≤ n
    · simpa only [c', c, ite_eq_left hn, Function.comp_def, RootIndexed.StepField.left] using
        (trialResetPositionAtGeneration_measurable R growth hR hgrowth upper duration r n hn).comp
          (RootIndexed.StepField.reindex_filtration_measurable Sum.inl n)
    · simp [c', hn]
  let declarations : ℕ → Set (RootIndexed.StepField Root ℕ ℝ) := fun n =>
    {ω | ∃ k, ((k + 1 + duration : ℕ) : WithTop ℕ) = n ∧
      ω ∈ successEvent R growth hR lower upper duration r k}
  have htrial (ω : Ωf) (n : ℕ) (ht : τ ω = n) :
      ∃ k, n = k + 1 + duration ∧
        RootIndexed.StepField.left ω ∈ successEvent R growth hR lower upper duration r k := by
    have ht' : firstDeclaredSuccess declarations (RootIndexed.StepField.left ω) = (n : WithTop ℕ) := ht
    obtain ⟨k, hk, hs⟩ := ((firstDeclaredSuccess_eq_iff declarations _ n).mp ht').1
    exact ⟨k, (WithTop.coe_injective hk).symm, hs⟩
  have hcount (k : ℕ) := entrance_count_le_at_trialResetPosition_ae
    μ hnorm N R growth hR hgrowth lower upper duration hupper hbounded hcapacity r k
  have hgood : ∀ᵐ ω ∂law, ∀ n ≤ H, ω ∈ E' n → τ ω = n →
      ∃ e : Fin m ↪ RootIndexed.TreeNode Root ℕ, ∀ i,
        e i ∈ RootIndexed.restartedRealPositionNSelectedBRWPopulation N {r} (fun _ => 0)
            id trials.toFinset n ω ∧
          RootIndexed.position (fun _ => 0) id
            (RootIndexed.restartedRealPositionNSelectedBRWField N {r} (fun _ => 0)
              id trials.toFinset n ω) (e i).1 (e i).2 ≤ c' n ω := by
    filter_upwards [ae_all_iff.2 hcount] with ω hω
    intro n _ _ ht
    obtain ⟨k, rfl, hs⟩ := htrial ω n ht
    have hcard := hmLower.trans (hω k hs)
    obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset (α := Fin m)
      (by simpa using hcard)
    refine ⟨e, fun i => ?_⟩
    have hi := Finset.mem_filter.mp (he (Set.mem_range_self i))
    exact ⟨hi.1, by simpa only [c', ite_eq_left (by omega : duration ≤ k + 1 + duration)] using hi.2⟩
  have h :=
    measure_stoppedEndpointAtLeast_le_reset_on_finiteCompletion μ hnorm N hN hm {r}
      (fun _ => 0) trials τ hτ H x E' hE' c' hc' resetRoots hfiber hdepth hinj hgood
  have hleft : {ω | ∃ n ≤ H, ω ∈ E' n ∧ τ ω = n} =
      {ω | ∃ n ≤ H, ω ∈ E n ∧ τ ω = n} := by
    ext ω
    constructor <;> rintro ⟨n, hn, he, ht⟩ <;>
      obtain ⟨k, rfl, _⟩ := htrial ω n ht <;>
      exact ⟨_, hn, by simpa only [E', ite_eq_left (by omega : duration ≤ k + 1 + duration)]
        using he, ht⟩
  rw [hleft] at h
  refine h.trans (measure_mono fun ω hω => ?_)
  obtain ⟨n, hn, he, ht, hv⟩ := hω
  obtain ⟨k, rfl, _⟩ := htrial ω n ht
  refine ⟨_, hn, ?_, ht, ?_⟩
  · simpa only [E', ite_eq_left (by omega : duration ≤ k + 1 + duration)] using he
  · simpa only [c', ite_eq_left (by omega : duration ≤ k + 1 + duration)] using hv

open SelectedPath.GrowthTrial in
/-- If the terminal generation precedes the reset, use the comparison
of the pre-reset slice with the actual endpoint on the installed field. -/
lemma trialRestartEndpointAtLeast_beforeReset_ae
    [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (R growth : Step.FiniteSelection ℕ ℝ)
    (hR : Measurable R.select) (hgrowth : Measurable growth.select)
    (lower upper duration : ℕ) (hupper : 1 ≤ upper) (hbounded : growth.IsBoundedBy 2)
    (hcapacity : 1 + (duration + 1) * (2 * upper) ≤ N) (r : Root) (H : ℕ) (x : ℝ) :
    let τ := Completion.time R growth hR hgrowth lower upper duration r
    let hτ := Completion.time_isStoppingTime R growth hR hgrowth lower upper duration r
    let trials := SelectedPath.Population.leftBRWFamily_finiteSlices R growth hR hgrowth
      upper duration r
    let installed := RootIndexed.stoppedRankInstalledTrajectoryField N {r}
      (fun _ => 0) trials τ hτ
    ∀ᵐ field ∂RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ,
      let left := RootIndexed.StepField.left field
      (H : WithTop ℕ) ≤ τ field → SelectedPath.isAlive R r H left →
      installed field ∈ RootIndexed.selectedPopulationEndpointAtLeast N {r} (fun _ => 0) H x →
      ∀ q ∈ trialRestartPopulationBeforeReset R growth hR lower upper duration r H left,
        x ≤ RootIndexed.position (fun _ => 0) id left q.1 q.2 := by
  intro τ hτ trials installed
  have h := trialRestartPopulationBeforeReset_positionWitness_ae
    μ hnorm N R growth hR hgrowth lower upper duration hupper hbounded hcapacity r
  filter_upwards [h] with field hfield
  intro left htime hAlive hactual q hq
  obtain ⟨p, hp, hpq⟩ := hfield H hAlive q hq
  let S := RootIndexed.restartedRealPositionNSelectedBRWField N {r} (fun _ => 0)
    id trials.toFinset H field
  have hagree := RootIndexed.stoppedRankInstalledTrajectoryField_eq_stage_before
    N {r} (fun _ => 0) trials τ hτ field H htime
  have hpop :
      RootIndexed.selectedPopulationTotalized N {r} (fun _ => 0) id id H (installed field) =
        RootIndexed.selectedPopulationTotalized N {r} (fun _ => 0) id id H S :=
    RootIndexed.adapted_eq_of_agree_before H _ (RootIndexed.selectedPopulationTotalized_adapted
      N {r} (fun _ => 0) id measurable_id id measurable_id H) (installed field) S hagree
  have hpS : p ∈ RootIndexed.selectedPopulationTotalized N {r} (fun _ => 0) id id H S := hp
  have hpI := hpop.symm ▸ hpS
  have hdepth := RootIndexed.selectedPopulationTotalized_depth N {r}
    (fun _ => 0) id id H S p hpS
  have heq := RootIndexed.adapted_eq_of_agree_before H _ (RootIndexed.positionAtGeneration_measurable
    (fun _ : Root => (0 : ℝ)) id measurable_id H p.1 p.2) (installed field) S hagree
  have hpos : RootIndexed.position (fun _ => 0) id (installed field) p.1 p.2 =
      RootIndexed.position (fun _ => 0) id S p.1 p.2 := by
    simpa only [RootIndexed.positionAtGeneration, hdepth, ite_true] using heq
  have hbound := hactual p hpI
  rw [hpos] at hbound
  exact hbound.trans hpq

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas
