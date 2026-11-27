/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Basic
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.StoppedComparison
import LiteratureProofTest.Wang2026AsymptoticSpeed.EndpointUpperTail.HorizonWindow

/-!
# Remaining-horizon bound after a successful entrance

## Internal proof declarations

* `eventually_measure_actualEndpoint_ge_le_badEntrance_add_polynomial`:
  write $G_N$ for $\{\tau_N\le T_N\}$ with at least $m_N=\lfloor N^a\rfloor$
  actual particles at or below $c_N$ at entrance. Then
  $\mathbb P(M_{H_N}\ge c_N+\zeta\log N)\le\mathbb P(G_N^c)+N^{-p}$
  eventually for some $p>0$. Here $0<a<1$, $H_N/\log^3 N\to t>0$,
  $T_N/\log^3 N\to0$, and $\zeta>-a+\pi^2\sigma^2t/2$.

This is the remaining-time step in Wang Yiyang, *Asymptotic Speed of the
N-Branching Random Walk with Infinite Offspring* (Fudan University, 2026),
Chapter 4, Theorem 1.1 for $a=0$.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace LiteratureProofTest.Wang2026AsymptoticSpeed.SingleRoot

open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath

open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas

open Combinatorics.Branching Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation
open ProbabilityTheory.BranchingRandomWalk.Spine

local instance (priority := high) addressDecidableEq
    {κ : Type*} [LinearOrder (RootIndexed.TreeNode κ ℕ)] :
    DecidableEq (RootIndexed.TreeNode κ ℕ) :=
  LinearOrder.toDecidableEq

/-- Compare the actual continuation to the zero-start positive-exponent
continuation on the event of a short entrance with sufficiently many
selected particles below the entrance position bound. -/
lemma eventually_measure_actualEndpoint_ge_le_badEntrance_add_polynomial
    {Root : Type*} [MeasurableSpace Root] [MeasurableSingletonClass Root]
    [MeasurableSpace (RootIndexed.TreeNode Root ℕ)]
    [MeasurableSingletonClass (RootIndexed.TreeNode Root ℕ)]
    [Countable (RootIndexed.TreeNode Root ℕ)]
    [LinearOrder (RootIndexed.TreeNode Root ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (hcross : HasFiniteCrossWeight realPotential μ)
    (hne : μ nonemptySupport = 1)
    {N H T : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    {sigma a t ζ : ℝ} (hsigma : 0 < sigma)
    (hcentered : IsCenteredSecondMoment (tiltedPotentialLaw realPotential (-1) μ) (sigma ^ 2))
    (ha : 0 < a) (ha1 : a < 1) (ht : 0 < t)
    (hgap : -a + (Real.pi ^ 2 / 2) * sigma ^ 2 * t < ζ)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 t))
    (hT : Tendsto (fun n => (T n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 0))
    (hTH : ∀ᶠ n in atTop, T n ≤ H n)
    (horder : ∀ n, LinearOrder (RootIndexed.TreeNode (Fin (Nat.floor ((N n : ℝ) ^ a))) ℕ))
    (r : Root)
    (R growth : Step.FiniteSelection ℕ ℝ) (hR : Measurable R.select)
    (hgrowth : Measurable growth.select)
    (upper duration : ℕ → ℕ) (c : ℕ → ℝ) :
    let lower := fun n => Nat.floor ((N n : ℝ) ^ a)
    let τ := fun n => Completion.time R growth hR hgrowth ⌈(N n : ℝ) ^ a⌉₊ (upper n) (duration n) r
    let hτ := fun n => Completion.time_isStoppingTime R growth hR hgrowth
      ⌈(N n : ℝ) ^ a⌉₊ (upper n) (duration n) r
    let trials := fun n => SelectedPath.Population.leftBRWFamily_finiteSlices R growth
      hR hgrowth (upper n) (duration n) r
    let installed := fun n => RootIndexed.stoppedRankInstalledTrajectoryField (N n) {r}
      (fun _ => 0) (trials n) (τ n) (hτ n)
    let stage := fun n => ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.RootIndexed.restartedRealPositionNSelectedBRWField (N n) {r}
      (fun _ => 0) id (trials n).toFinset
    let Pop := fun n i => ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.RootIndexed.restartedRealPositionNSelectedBRWPopulation (N n) {r}
      (fun _ => 0) id (trials n).toFinset i
    let good := fun n i => {field | ∃ e : Fin (lower n) ↪ RootIndexed.TreeNode Root ℕ,
      ∀ j, e j ∈ Pop n i field ∧
        RootIndexed.position (fun _ => 0) id (stage n i field) (e j).1 (e j).2 ≤ c n}
    let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
    ∃ p : ℝ, 0 < p ∧ ∀ᶠ n in atTop,
      P (installed n ⁻¹' RootIndexed.selectedPopulationEndpointAtLeast (N n) {r}
          (fun _ => 0) (H n) (ζ * Real.log (N n : ℝ) + c n)) ≤
        P {field | ¬ ∃ i ≤ T n, field ∈ good n i ∧ τ n field = i} +
          ENNReal.ofReal (Real.exp (-p * Real.log (N n : ℝ))) := by
  intro lower τ hτ trials installed stage Pop good P
  obtain ⟨p, hp, hwindow⟩ :=
    LiteratureProofTest.Wang2026AsymptoticSpeed.eventually_countableRootEndpointMinimum_ge_le_polynomial_sub_horizon hN μ hnorm
      hcross hsigma hcentered ha ha1 ht hgap hH hT horder
  refine ⟨p, hp, ?_⟩
  filter_upwards [hwindow, hTH, hN.eventually_ge_atTop 1] with n hn hTHn hNn
  let _ := horder n
  have hNreal : (1 : ℝ) ≤ N n := by exact_mod_cast hNn
  have hpositive : 0 < lower n := Nat.floor_pos.mpr (Real.one_le_rpow hNreal ha.le)
  have hNpos : 0 < N n := hNn
  have hmN : lower n ≤ N n := by
    apply Nat.floor_le_of_le
    simpa using Real.rpow_le_rpow_of_exponent_le hNreal ha1.le
  let F := RootIndexed.stepFiltration (Root := Root ⊕ Root) (α := ℕ) (X := ℝ)
  have hgood (i : ℕ) : MeasurableSet[F i] (good n i) := by
    let _ : Countable (Fin (lower n) ↪ RootIndexed.TreeNode Root ℕ) :=
      (show Function.Injective (fun e : Fin (lower n) ↪ RootIndexed.TreeNode Root ℕ =>
        (e : Fin (lower n) → RootIndexed.TreeNode Root ℕ)) from
          fun _ _ h => Function.Embedding.ext fun i => congrFun h i).countable
    have hstage := ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.RootIndexed.restartedRealPositionNSelectedBRWField_filtration_measurable
      (N n) {r} (fun _ => 0) (trials n) i
    have hPop : Measurable[F i] (Pop n i) :=
      (RootIndexed.selectedPopulationTotalized_adapted (N n) {r} (fun _ => 0)
        id measurable_id id measurable_id i).comp hstage
    rw [show good n i = ⋃ e : Fin (lower n) ↪ RootIndexed.TreeNode Root ℕ,
      ⋂ j, {field | e j ∈ Pop n i field ∧
        RootIndexed.observedPositionAtGeneration (fun _ => 0) id id i (stage n i field) (e j) ≤ c n} by
          ext field
          simp only [good, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_iInter]
          apply exists_congr
          intro e
          apply forall_congr'
          intro j
          refine and_congr_right fun hj => ?_
          have hd := RootIndexed.selectedPopulationTotalized_depth (N n) {r} (fun _ => 0)
            id id i (stage n i field) (e j) hj
          rw [RootIndexed.observedPositionAtGeneration_eq _ _ _ _ _ _ hd]
          rfl]
    refine MeasurableSet.iUnion fun e => MeasurableSet.iInter fun j => ?_
    have hpos : Measurable[F i] (fun field =>
        RootIndexed.observedPositionAtGeneration (fun _ => 0) id id i (stage n i field) (e j)) :=
      (RootIndexed.positionAtGeneration_measurable (fun _ => 0) id measurable_id
        i (e j).1 (e j).2).comp hstage
    exact (hPop (measurableSet_mem_finset (e j))).inter (hpos measurableSet_Iic)
  let G := {field | ∃ i ≤ T n, field ∈ good n i ∧ τ n field = i}
  let B := installed n ⁻¹' RootIndexed.selectedPopulationEndpointAtLeast (N n) {r}
    (fun _ => 0) (H n) (ζ * Real.log (N n : ℝ) + c n)
  let bound := ENNReal.ofReal (Real.exp (-p * Real.log (N n : ℝ)))
  have hgoodBound : P (G ∩ B) ≤ bound := by
    refine measure_stoppedEndpointAtLeast_le_of_remainingHorizon μ hnorm (N n) hNpos hmN
      {r} (fun _ => 0) (trials n) (τ n) (hτ n) (H n) (T n) hTHn (good n) hgood _ _ _ ?_
      (fun field i hi _ => hi)
    intro i hi
    let x := ζ * Real.log (N n : ℝ)
    have hmap := congrArg (fun law : Measure ℝ => law (Set.Ici x))
      (countableRootEndpointMinimum_map_eq μ (lower n) (N n) (H n - i))
    rw [Measure.map_apply (measurable_countableRootEndpointMinimum (lower n) (N n) (H n - i))
        measurableSet_Ici,
      Measure.map_apply (measurable_firstNSelectedEndpointMinimum (lower n) (N n) (H n - i))
        measurableSet_Ici] at hmap
    have hsame :
        RootIndexed.selectedPopulationEndpointAtLeast (N n) Finset.univ
          (fun _ : Fin (lower n) => 0) (H n - i) x =ᵐ[finiteRootStepFieldLaw μ (lower n)]
          {field | x ≤ firstNSelectedEndpointMinimum (lower n) (N n) (H n - i) field} := by
      filter_upwards [firstNSelectedEndpointMinimum_eq_population_inf'_ae
        (lower n) (N n) (H n - i) hpositive hNpos μ hnorm hne] with field hfield
      obtain ⟨hne, hmin⟩ := hfield
      rw [hmin, Finset.le_inf'_iff]
      have hpop : firstNSelectedPopulation (lower n) (N n) (H n - i) field =
          RootIndexed.selectedPopulationTotalized (N n) Finset.univ
            (fun _ : Fin (lower n) => (0 : ℝ)) id id (H n - i) field := by
        unfold firstNSelectedPopulation
        congr 1
        exact Subsingleton.elim _ _
      rw [hpop]
      rfl
    exact (measure_congr hsame).le.trans (hmap.ge.trans (hn i hi))
  change P B ≤ P Gᶜ + bound
  have hsubset : B ⊆ Gᶜ ∪ (G ∩ B) := by
    intro ω hω
    by_cases h : ω ∈ G
    · exact Or.inr ⟨h, hω⟩
    · exact Or.inl h
  calc
    P B ≤ P (Gᶜ ∪ (G ∩ B)) := measure_mono hsubset
    _ ≤ P Gᶜ + P (G ∩ B) := measure_union_le _ _
    _ ≤ P Gᶜ + bound := add_le_add_right hgoodBound _

end LiteratureProofTest.Wang2026AsymptoticSpeed.SingleRoot
