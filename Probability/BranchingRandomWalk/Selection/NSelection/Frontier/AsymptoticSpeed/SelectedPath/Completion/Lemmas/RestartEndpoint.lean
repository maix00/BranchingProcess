/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.StoppedComparison
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.Entrance
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.TrialRoots
import Combinatorics.UlamHarris.Order

/-!
# Terminal comparison of the restart process

## Internal proof declarations

* `trialRestartEndpointAtLeast` is the terminal upper-tail event for the
  original growth-trial slice before completion and for the translated
  $N$-selection continuation after completion.
* `exists_trialRestartEndpoint_tail_comparison` chooses the stopped vector of
  distinct trial roots on the pre-sampled tree. With those roots, at every
  terminal generation $H$ and threshold $x$ the actual upper-tail probability
  is bounded by that of the restart process.

This assembles the endpoint comparison in Wang Yiyang, *Asymptotic Speed of
the N-Branching Random Walk with Infinite Offspring* (Fudan University, 2026),
Chapter 4, Theorem 1.2.
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

local notation "Ωf" => RootIndexed.StepField (ℕ ⊕ ℕ) ℕ ℝ
local notation "𝔽" => RootIndexed.stepFiltration (Root := ℕ ⊕ ℕ) (α := ℕ) (X := ℝ)

open SelectedPath.GrowthTrial GrowthTrial.Population

noncomputable local instance natTreeOrder : LinearOrder (RootIndexed.TreeNode ℕ ℕ) :=
  RootIndexed.addressLinearOrder ℕ ℕ

/-- The terminal upper tail, using the pre-reset slice when the completion
has not occurred by the terminal generation. -/
noncomputable def trialRestartEndpointAtLeast
    {m : ℕ} [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (N : ℕ) (R growth : Step.FiniteSelection ℕ ℝ)
    (hR : Measurable R.select) (hgrowth : Measurable growth.select)
    (lower upper duration r H : ℕ) (roots : Ωf → Fin m → RootIndexed.TreeNode (ℕ ⊕ ℕ) ℕ)
    (x : ℝ) : Set Ωf :=
  let τ := Completion.time R growth hR hgrowth lower upper duration r
  {ω | (H : WithTop ℕ) < τ ω ∧
      ∀ q ∈ trialRestartPopulationBeforeReset R growth hR lower upper duration r H
          (RootIndexed.StepField.left ω),
        x ≤ RootIndexed.position (fun _ => 0) id (RootIndexed.StepField.left ω) q.1 q.2}
    ∪ {ω | ∃ n ≤ H, τ ω = n ∧
        RootIndexed.subtreeStepFieldVector (roots ω) ω ∈
          RootIndexed.selectedPopulationEndpointAtLeast N Finset.univ
            (fun _ => trialResetPositionAtGeneration R growth hR upper duration r n
              (RootIndexed.StepField.left ω)) (H - n) x}

set_option maxHeartbeats 1000000 in
lemma exists_trialRestartEndpoint_tail_comparison
    {m : ℕ} [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ)
    (N : ℕ) (hN : 0 < N) (hm : m ≤ N)
    (R growth : Step.FiniteSelection ℕ ℝ)
    (hR : Measurable R.select) (hgrowth : Measurable growth.select)
    (hRne : μ {ξ | (R ξ).Nonempty} = 1)
    (lower upper duration : ℕ) (hmLower : m ≤ lower) (hupper : 1 ≤ upper)
    (hbounded : growth.IsBoundedBy 2) (hcapacity : 1 + (duration + 1) * (2 * upper) ≤ N)
    (r : ℕ) :
    let τ := Completion.time R growth hR hgrowth lower upper duration r
    let hτ := Completion.time_isStoppingTime R growth hR hgrowth lower upper duration r
    let trials := SelectedPath.Population.leftBRWFamily_finiteSlices R growth hR hgrowth
      upper duration r
    let installed := RootIndexed.stoppedRankInstalledTrajectoryField N {r}
      (fun _ => 0) trials τ hτ
    let law := RootIndexed.stepFieldLaw (Root := ℕ ⊕ ℕ) μ
    ∃ roots : Ωf → Fin m → RootIndexed.TreeNode (ℕ ⊕ ℕ) ℕ,
      (∀ v, MeasurableSet[hτ.measurableSpace] {ω | roots ω = v}) ∧
      (∀ ω (n : ℕ), τ ω = n → ∀ i, (roots ω i).2.length = n) ∧
      (∀ ω, τ ω ≠ ⊤ → Function.Injective (roots ω)) ∧
      (∀ ω k, τ ω = ((k + 1 + duration : ℕ) : WithTop ℕ) →
        ∀ i, ∃ q ∈ capStoppedCandidate (lineages R hR) R growth upper r
            PUnit.unit (k + 1) duration (RootIndexed.StepField.left ω),
          roots ω i = (Sum.inl q.1, q.2)) ∧
      ∀ H x, law (installed ⁻¹'
        RootIndexed.selectedPopulationEndpointAtLeast (α := ℕ) N {r} (fun _ => 0) H x) ≤
        law (trialRestartEndpointAtLeast N R growth hR hgrowth lower upper duration r H roots x) := by
  intro τ hτ trials installed law
  classical
  obtain ⟨u, hUfiber, hUdepth, hUinj, hUmem⟩ := exists_firstSuccessfulTrialRoots
    R growth hR hgrowth m lower upper duration hmLower hupper r
  let τleft := firstSuccessfulCompletion R growth hR lower upper duration r
  let hτleft := firstSuccessfulCompletion_isStoppingTime R growth hR hgrowth lower upper duration r
  let lift : RootIndexed.TreeNode ℕ ℕ → RootIndexed.TreeNode (ℕ ⊕ ℕ) ℕ :=
    fun q => (Sum.inl q.1, q.2)
  have hlift : Function.Injective lift := by
    intro i j h
    exact Prod.ext (Sum.inl_injective (congrArg Prod.fst h)) (congrArg (fun q : RootIndexed.TreeNode (ℕ ⊕ ℕ) ℕ => q.2) h)
  let roots (ω : Ωf) (i : Fin m) := lift (u (RootIndexed.StepField.left ω) i)
  have hleft (n : ℕ) :
      @Measurable Ωf (RootIndexed.StepField ℕ ℕ ℝ) (𝔽 n)
        (RootIndexed.stepFiltration (Root := ℕ) (α := ℕ) (X := ℝ) n)
        RootIndexed.StepField.left :=
    RootIndexed.StepField.reindex_filtration_measurable Sum.inl n
  have hpull (A : Set (RootIndexed.StepField ℕ ℕ ℝ))
      (hA : MeasurableSet[hτleft.measurableSpace] A) :
      MeasurableSet[hτ.measurableSpace] (RootIndexed.StepField.left ⁻¹' A) := by
    refine ⟨?_, fun n => ?_⟩
    · apply (show @Measurable Ωf (RootIndexed.StepField ℕ ℕ ℝ) (⨆ n, 𝔽 n)
          (⨆ n, RootIndexed.stepFiltration (Root := ℕ) (α := ℕ) (X := ℝ) n)
          RootIndexed.StepField.left from by
        rw [measurable_iff_comap_le, MeasurableSpace.comap_iSup]
        exact iSup_le fun n => (measurable_iff_comap_le.mp (hleft n)).trans (le_iSup _ n))
      exact hA.1
    · exact hleft n (hA.2 n)
  have hfiber (v : Fin m → RootIndexed.TreeNode (ℕ ⊕ ℕ) ℕ) :
      MeasurableSet[hτ.measurableSpace] {ω | roots ω = v} := by
    by_cases hv : ∃ w : Fin m → RootIndexed.TreeNode ℕ ℕ, lift ∘ w = v
    · obtain ⟨w, rfl⟩ := hv
      have heq : {ω | roots ω = lift ∘ w} =
          RootIndexed.StepField.left ⁻¹' {ω | u ω = w} := by
        ext ω
        change (lift ∘ u (RootIndexed.StepField.left ω) = lift ∘ w) ↔
          u (RootIndexed.StepField.left ω) = w
        exact ⟨fun h => funext fun i => hlift (congrFun h i), fun h => congrArg (lift ∘ ·) h⟩
      rw [heq]
      exact hpull _ (hUfiber w)
    · have hempty : {ω | roots ω = v} = ∅ := Set.eq_empty_iff_forall_notMem.mpr
        fun ω hω => hv ⟨u (RootIndexed.StepField.left ω), hω⟩
      rw [hempty]
      exact @MeasurableSet.empty _ hτ.measurableSpace
  have hdepth (ω : Ωf) (n : ℕ) (ht : τ ω = n) (i : Fin m) :
      (roots ω i).2.length = n := hUdepth _ n ht i
  have hinj (ω : Ωf) (ht : τ ω ≠ ⊤) : Function.Injective (roots ω) :=
    hlift.comp (hUinj _ ht)
  refine ⟨roots, hfiber, hdepth, hinj, fun ω k ht i => ?_, ?_⟩
  · exact ⟨_, hUmem _ k ht i, rfl⟩
  intro H x
  let B := installed ⁻¹' RootIndexed.selectedPopulationEndpointAtLeast (α := ℕ) N {r} (fun _ => 0) H x
  let A := {ω | τ ω ≤ (H : WithTop ℕ)}
  let J := {ω | (H : WithTop ℕ) < τ ω ∧
      ∀ q ∈ trialRestartPopulationBeforeReset R growth hR lower upper duration r H
          (RootIndexed.StepField.left ω),
        x ≤ RootIndexed.position (fun _ => 0) id (RootIndexed.StepField.left ω) q.1 q.2}
  let D := {ω | ∃ n ≤ H, τ ω = n ∧
    RootIndexed.subtreeStepFieldVector (roots ω) ω ∈
      RootIndexed.selectedPopulationEndpointAtLeast N Finset.univ
        (fun _ => trialResetPositionAtGeneration R growth hR upper duration r n
          (RootIndexed.StepField.left ω)) (H - n) x}
  have hAeq : A = {ω | ∃ n ≤ H, ω ∈ (fun _ : ℕ => Set.univ) n ∧ τ ω = n} := by
    ext ω
    constructor
    · intro hw
      change τ ω ≤ (H : WithTop ℕ) at hw
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (fun he : τ ω = ⊤ => WithTop.coe_ne_top (top_le_iff.mp (he ▸ hw)))
      exact ⟨n, WithTop.coe_le_coe.mp (hn.trans_le hw), Set.mem_univ _, hn.symm⟩
    · rintro ⟨n, hn, _, ht⟩
      exact ht.le.trans (WithTop.coe_le_coe.mpr hn)
  have hAfter : law (A ∩ B) ≤ law D := by
    rw [hAeq]
    simpa only [D, Set.mem_univ, true_and] using
      measure_stoppedEndpointAtLeast_le_trialReset μ hnorm N hN hm R growth hR hgrowth
        lower upper duration hmLower hupper hbounded hcapacity r H x (fun _ => Set.univ)
        (fun _ => MeasurableSet.univ) roots hfiber hdepth hinj
  have hRmeas : MeasurableSet {ξ | (R ξ).Nonempty} := by
    rw [show {ξ | (R ξ).Nonempty} = (fun ξ => (R ξ).card) ⁻¹' Set.Ioi 0 by
      ext ξ
      exact Finset.card_pos.symm]
    exact ((measurable_of_countable fun s : Finset ℕ => s.card).comp hR) measurableSet_Ioi
  have hall : ∀ᵐ ω ∂law, ∀ u : TreeNode ℕ, (R (ω (Sum.inl r) u)).Nonempty := by
    apply ae_all_iff.2
    intro u
    let f : Ωf → Step ℕ ℝ := fun ω => ω (Sum.inl r) u
    have hf : Measurable f := (measurable_pi_apply u).comp (measurable_pi_apply _)
    apply (ae_mem_iff_measure_eq (hf hRmeas).nullMeasurableSet).2
    rw [← Measure.map_apply hf hRmeas, RootIndexed.stepFieldLaw_coordinate_marginal μ, hRne, measure_univ]
  have hBefore : Aᶜ ∩ B ≤ᵐ[law] J := by
    filter_upwards [hall, trialRestartEndpointAtLeast_beforeReset_ae μ hnorm N R growth hR hgrowth
      lower upper duration hupper hbounded hcapacity r H x] with ω hmarks hc hw
    have hlive : ∀ n, SelectedPath.isAlive R r n (RootIndexed.StepField.left ω) := by
      intro n
      induction n with
      | zero => trivial
      | succ n ih => exact ⟨ih, hmarks _⟩
    have hlt : (H : WithTop ℕ) < τ ω := lt_of_not_ge hw.1
    exact ⟨hlt, hc hlt.le (hlive H) hw.2⟩
  have hJ : MeasurableSet J := by
    -- Only this branch needs the whole pre-sampled field rather than the stopped past.
    let left : Ωf → RootIndexed.StepField ℕ ℕ ℝ := RootIndexed.StepField.left
    have hleftMeas : Measurable left := measurable_pi_iff.mpr fun i => measurable_pi_apply (Sum.inl i)
    have hpop : Measurable (trialRestartPopulationBeforeReset R growth hR lower upper duration r H ∘ left) := by
      let t := firstSuccessfulCompletion R growth hR lower upper duration r
      let ht := firstSuccessfulCompletion_isStoppingTime R growth hR hgrowth lower upper duration r
      let X (n : WithTop ℕ) (ω : RootIndexed.StepField ℕ ℕ ℝ) := match n with
        | ⊤ => ({(r, selectedPath R r H ω)} : Finset (RootIndexed.TreeNode ℕ ℕ))
        | (k : ℕ) => if H < k - duration then {(r, selectedPath R r H ω)}
          else if H ≤ k then capStoppedCandidate (lineages R hR) R growth upper r
            PUnit.unit (k - duration) (H - (k - duration)) ω else ∅
      have hX (n : WithTop ℕ) : Measurable (X n) := by
        have hpath : Measurable (fun ω : RootIndexed.StepField ℕ ℕ ℝ =>
            ({(r, selectedPath R r H ω)} : Finset (RootIndexed.TreeNode ℕ ℕ))) :=
          (measurable_of_countable (fun j : TreeNode ℕ => ({(r, j)} : Finset _))).comp
            ((SelectedPath.adapted R hR r H).mono (RootIndexed.stepFiltration.le H) le_rfl)
        cases n with
        | top => exact hpath
        | coe k =>
          by_cases hwait : H < k - duration
          · simpa only [X, ite_eq_left hwait] using hpath
          by_cases hH : H ≤ k
          · have h := capStoppedCandidate_adapted (lineages R hR) R growth hR hgrowth upper r
              PUnit.unit (k - duration) (H - (k - duration))
            simpa only [X, ite_eq_right hwait, ite_eq_left hH] using
              h.mono (RootIndexed.stepFiltration.le _) le_rfl
          · simp [X, hwait, hH]
      suffices h : Measurable (fun ω => X (t ω) ω) from h.comp hleftMeas
      intro B₀ hB₀
      rw [show (fun ω => X (t ω) ω) ⁻¹' B₀ = ⋃ n : WithTop ℕ,
        {ω | t ω = n} ∩ X n ⁻¹' B₀ by ext ω; simp [Set.mem_iUnion, Set.mem_preimage]]
      exact MeasurableSet.iUnion fun n =>
        (ht.measurableSpace_le _ (ht.measurable (measurableSet_singleton n))).inter (hX n hB₀)
    have hpos (q : RootIndexed.TreeNode ℕ ℕ) :
        Measurable (fun ω => RootIndexed.position (fun _ => 0) id (left ω) q.1 q.2) :=
      ((RootIndexed.position_measurable (fun _ => (0 : ℝ)) id measurable_id q.1 q.2).mono
        (RootIndexed.stepFiltration.le _) le_rfl).comp hleftMeas
    have hset : J = Aᶜ ∩ ⋂ q : RootIndexed.TreeNode ℕ ℕ,
      {ω | q ∈ trialRestartPopulationBeforeReset R growth hR lower upper duration r H (left ω) →
        x ≤ RootIndexed.position (fun _ => 0) id (left ω) q.1 q.2} := by
      ext ω
      simp [J, A, left, not_le]
    rw [hset]
    refine ((𝔽).le H _ (hτ.measurableSet_le H)).compl.inter (MeasurableSet.iInter fun q => ?_)
    exact (hpop (measurableSet_mem_finset q)).imp (hpos q measurableSet_Ici)
  have hdisj : Disjoint D J := by
    refine Set.disjoint_left.mpr fun ω hw hj => ?_
    obtain ⟨n, hn, htime, _⟩ := hw
    exact hj.1.not_ge (htime.le.trans (WithTop.coe_le_coe.mpr hn))
  change law B ≤ law (J ∪ D)
  rw [Set.union_comm, measure_union hdisj hJ]
  calc
    law B = law ((A ∩ B) ∪ (Aᶜ ∩ B)) := by
      congr 1
      simp [← Set.union_inter_distrib_right]
    _ ≤ law (A ∩ B) + law (Aᶜ ∩ B) := measure_union_le _ _
    _ ≤ law D + law J := add_le_add hAfter (measure_mono_ae hBefore)

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas
