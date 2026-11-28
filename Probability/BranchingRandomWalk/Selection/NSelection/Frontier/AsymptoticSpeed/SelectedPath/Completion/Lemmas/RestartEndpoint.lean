/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.StoppedComparison
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.Entrance
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.TrialRoots
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.Minimum.Basic
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Endpoint.PositiveMoment.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Probability.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.Roots.Nonempty
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.StoppingSubtrees.Vector.Factorization
import Probability.BranchingRandomWalk.Genealogy.Exploration.RootIndexed.SelectedSubtrees.FixedFamily
import Combinatorics.UlamHarris.Order

/-!
# Terminal comparison of the restart process

## Internal proof declarations

* `trialRestartEndpoint`: the minimum of the original growth-trial slice
  before the reset, and the reset position plus the centered endpoint after it.
* `measurable_trialRestartEndpoint`: the entire endpoint at generation $H$
  is measurable for a stopped-measurable root vector.
* `trialRestartEndpointAtLeast` is the terminal upper-tail event for the
  original growth-trial slice before completion and for the translated
  $N$-selection continuation after completion.
* `trialRestartEndpointAtLeast_ae_eq`: the event is almost surely
  $\{x\le M_H^{\mathrm b}\}$ for the real restart endpoint.
* `exists_trialRestartEndpoint_tail_comparison` chooses the stopped vector of
  distinct trial roots on the pre-sampled tree. With those roots, at every
  terminal generation $H$ and threshold $x$ the actual upper-tail probability
  is bounded by that of the restart process.
* `measure_firstNSelectedEndpointMinimum_ge_le_restart`: the upper tails
  of the real single-root endpoint are bounded by those of the restart
  endpoint for the same pre-sampled construction.
* `lintegral_exp_neg_trialRestartEndpoint_le`: the restart endpoint satisfies
  $\mathbb E[e^{-M_H^{\mathrm b}}]\le 1$ by the single-root endpoint order.
* `trialRestartEndpoint_pos_le`: the positive endpoint is bounded by the
  displacement envelope plus the centered positive continuation on $\{\tau\le H\}$.

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

private lemma trialRestartPopulationBeforeReset_measurable
    (R growth : Step.FiniteSelection ℕ ℝ)
    (hR : Measurable R.select) (hgrowth : Measurable growth.select)
    (lower upper duration r H : ℕ) :
    Measurable (trialRestartPopulationBeforeReset R growth hR lower upper duration r H) := by
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
  intro B₀ hB₀
  change MeasurableSet ((fun ω => X (t ω) ω) ⁻¹' B₀)
  rw [show (fun ω => X (t ω) ω) ⁻¹' B₀ = ⋃ n : WithTop ℕ,
    {ω | t ω = n} ∩ X n ⁻¹' B₀ by ext ω; simp [Set.mem_iUnion, Set.mem_preimage]]
  exact MeasurableSet.iUnion fun n =>
    (ht.measurableSpace_le _ (ht.measurable (measurableSet_singleton n))).inter (hX n hB₀)

private noncomputable def preResetMinimum
    (R growth : Step.FiniteSelection ℕ ℝ) (hR : Measurable R.select)
    (lower upper duration r H : ℕ) (ω : RootIndexed.StepField ℕ ℕ ℝ) : ℝ :=
  let s := trialRestartPopulationBeforeReset R growth hR lower upper duration r H ω
  if hs : s.Nonempty then s.inf' hs (fun p => RootIndexed.position (fun _ => 0) id ω p.1 p.2) else 0

private lemma preResetMinimum_measurable
    (R growth : Step.FiniteSelection ℕ ℝ)
    (hR : Measurable R.select) (hgrowth : Measurable growth.select)
    (lower upper duration r H : ℕ) :
    Measurable (preResetMinimum R growth hR lower upper duration r H) := by
  let Ω := RootIndexed.StepField ℕ ℕ ℝ
  let pop := trialRestartPopulationBeforeReset R growth hR lower upper duration r H
  let X (q : RootIndexed.TreeNode ℕ ℕ) (ω : Ω) :=
    RootIndexed.position (fun _ => 0) id ω q.1 q.2
  let f (s : Finset (RootIndexed.TreeNode ℕ ℕ)) (ω : Ω) :=
    if hs : s.Nonempty then s.inf' hs (fun q => X q ω) else 0
  have hvalue (q : RootIndexed.TreeNode ℕ ℕ) : Measurable (X q) :=
    (RootIndexed.position_measurable (fun _ => 0) id measurable_id q.1 q.2).mono
      (RootIndexed.stepFiltration.le _) le_rfl
  have hf (s : Finset (RootIndexed.TreeNode ℕ ℕ)) : Measurable (f s) := by
    by_cases hs : s.Nonempty
    · simp only [f, dite_eq_left hs]
      apply measurable_of_Ioi
      intro x
      rw [show (fun ω => s.inf' hs (fun q => X q ω)) ⁻¹' Set.Ioi x =
        ⋂ q : s, (X q.val) ⁻¹' Set.Ioi x by
        ext ω
        simp only [Set.mem_preimage, Set.mem_Ioi, Set.mem_iInter, Finset.lt_inf'_iff,
          Subtype.forall]]
      exact MeasurableSet.iInter fun q => hvalue q.val measurableSet_Ioi
    · simpa only [f, dite_eq_right hs] using (measurable_const (a := (0 : ℝ)))
  have hpop := trialRestartPopulationBeforeReset_measurable R growth hR hgrowth lower upper duration r H
  intro B hB
  change MeasurableSet ((fun ω => f (pop ω) ω) ⁻¹' B)
  rw [show (fun ω => f (pop ω) ω) ⁻¹' B =
      ⋃ s : Finset (RootIndexed.TreeNode ℕ ℕ), pop ⁻¹' {s} ∩ f s ⁻¹' B by
    ext ω
    simp]
  exact MeasurableSet.iUnion fun s => (hpop (measurableSet_singleton s)).inter (hf s hB)

private lemma resetDuration_le
    (R growth : Step.FiniteSelection ℕ ℝ)
    (hR : Measurable R.select) (hgrowth : Measurable growth.select)
    (lower upper duration r : ℕ) (ω : Ωf) {n : ℕ}
    (hn : Completion.time R growth hR hgrowth lower upper duration r ω = (n : WithTop ℕ)) :
    duration ≤ n := by
  let declared : ℕ → Set (RootIndexed.StepField ℕ ℕ ℝ) := fun s =>
    {field | ∃ k, ((k + 1 + duration : ℕ) : WithTop ℕ) = s ∧
      field ∈ successEvent R growth hR lower upper duration r k}
  have hfirst : firstDeclaredSuccess declared (RootIndexed.StepField.left ω) = (n : WithTop ℕ) := hn
  obtain ⟨k, hk, _⟩ := ((firstDeclaredSuccess_eq_iff declared _ n).mp hfirst).1
  have he : k + 1 + duration = n := WithTop.coe_injective hk
  omega

open EndpointDeviation in
/-- The minimum of the original pre-reset slice, or the reset displacement
plus the centered first-N endpoint on the original stopped subtrees. -/
noncomputable def trialRestartEndpoint
    {m : ℕ} [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (N : ℕ) (R growth : Step.FiniteSelection ℕ ℝ)
    (hR : Measurable R.select) (hgrowth : Measurable growth.select)
    (lower upper duration r H : ℕ) (roots : Ωf → Fin m → RootIndexed.TreeNode (ℕ ⊕ ℕ) ℕ)
    (ω : Ωf) : ℝ :=
  let τ := Completion.time R growth hR hgrowth lower upper duration r
  let left := RootIndexed.StepField.left ω
  if τ ω ≤ (H : WithTop ℕ) then
    trialResetPositionAtGeneration R growth hR upper duration r ((τ ω).untopD 0) left +
      firstNSelectedEndpointMinimum m N (H - (τ ω).untopD 0)
        (RootIndexed.selectedSubtreeStepFieldVector roots ω)
  else preResetMinimum R growth hR lower upper duration r H left

open EndpointDeviation in
lemma measurable_trialRestartEndpoint
    {m : ℕ} [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (N : ℕ) (R growth : Step.FiniteSelection ℕ ℝ)
    (hR : Measurable R.select) (hgrowth : Measurable growth.select)
    (lower upper duration r H : ℕ) (roots : Ωf → Fin m → RootIndexed.TreeNode (ℕ ⊕ ℕ) ℕ) :
    let hτ := Completion.time_isStoppingTime R growth hR hgrowth lower upper duration r
    (∀ v, MeasurableSet[hτ.measurableSpace] {ω | roots ω = v}) →
    Measurable (trialRestartEndpoint N R growth hR hgrowth lower upper duration r H roots) := by
  intro hτ hfiber
  let τ := Completion.time R growth hR hgrowth lower upper duration r
  let left : Ωf → RootIndexed.StepField ℕ ℕ ℝ := RootIndexed.StepField.left
  have hleft : Measurable left := measurable_pi_iff.mpr fun i => measurable_pi_apply (Sum.inl i)
  have hpre := (preResetMinimum_measurable R growth hR hgrowth lower upper duration r H).comp hleft
  have hfield : Measurable (RootIndexed.selectedSubtreeStepFieldVector roots) := by
    intro s hs
    rw [show RootIndexed.selectedSubtreeStepFieldVector roots ⁻¹' s =
      ⋃ v : (Fin m → RootIndexed.TreeNode (ℕ ⊕ ℕ) ℕ),
        {ω | roots ω = v} ∩ RootIndexed.subtreeStepFieldVector v ⁻¹' s by
      ext ω
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
      exact ⟨fun h => ⟨roots ω, rfl, h⟩, fun ⟨_, rfl, h⟩ => h⟩]
    exact MeasurableSet.iUnion fun v =>
      (hτ.measurableSpace_le _ (hfiber v)).inter (RootIndexed.subtreeStepFieldVector_measurable v hs)
  let after (n : ℕ) (ω : Ωf) :=
    trialResetPositionAtGeneration R growth hR upper duration r n (left ω) +
      firstNSelectedEndpointMinimum m N (H - n) (RootIndexed.selectedSubtreeStepFieldVector roots ω)
  let before := preResetMinimum R growth hR lower upper duration r H ∘ left
  let endpoint := trialRestartEndpoint N R growth hR hgrowth lower upper duration r H roots
  have hafter (n : ℕ) (hn : duration ≤ n) : Measurable (after n) := by
    have hc := ((trialResetPositionAtGeneration_measurable R growth hR hgrowth upper duration r n hn).mono
      (RootIndexed.stepFiltration.le n) le_rfl).comp hleft
    exact hc.add ((measurable_firstNSelectedEndpointMinimum m N (H - n)).comp hfield)
  have hclock (a : WithTop ℕ) : MeasurableSet {ω | τ ω = a} :=
    hτ.measurableSpace_le _ (hτ.measurable (measurableSet_singleton a))
  have hle : MeasurableSet {ω | τ ω ≤ (H : WithTop ℕ)} :=
    (𝔽).le H _ (hτ.measurableSet_le H)
  intro s hs
  change MeasurableSet (endpoint ⁻¹' s)
  rw [show endpoint ⁻¹' s = ({ω | τ ω ≤ (H : WithTop ℕ)}ᶜ ∩ before ⁻¹' s) ∪
      ⋃ n : ℕ, {ω | τ ω = (n : WithTop ℕ) ∧ n ≤ H ∧ duration ≤ n} ∩ after n ⁻¹' s by
    ext ω
    by_cases htime : τ ω ≤ (H : WithTop ℕ)
    · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top htime)
      have hnH := WithTop.coe_le_coe.mp (hn.trans_le htime)
      have hd := resetDuration_le R growth hR hgrowth lower upper duration r ω hn.symm
      have he : endpoint ω = after n ω := by
        change (if τ ω ≤ (H : WithTop ℕ) then _ else _) = _
        rw [ite_eq_left htime]
        have hidx : (Completion.time R growth hR hgrowth lower upper duration r ω).untopD 0 = n := by
          change (τ ω).untopD 0 = n
          rw [← hn, WithTop.untopD_coe]
        simp only [hidx, after, left]
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff,
        Set.mem_iUnion, Set.mem_ofPred_eq, htime, not_true_eq_false, false_and, false_or, he]
      constructor
      · intro hw
        exact ⟨n, ⟨hn.symm, hnH, hd⟩, hw⟩
      · rintro ⟨k, ⟨hk, _, _⟩, h⟩
        have hkn : k = n := WithTop.coe_injective (hk.symm.trans hn.symm)
        rwa [hkn] at h
    · have he : endpoint ω = before ω := by
        change (if τ ω ≤ (H : WithTop ℕ) then _ else _) = _
        rw [ite_eq_right htime]
        rfl
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff,
        Set.mem_iUnion, Set.mem_ofPred_eq, htime, not_false_eq_true, true_and, he]
      exact ⟨Or.inl, fun hw => hw.elim id (by
        rintro ⟨n, ⟨hn, hH, _⟩, _⟩
        exact (htime (hn.le.trans (WithTop.coe_le_coe.mpr hH))).elim)⟩]
  refine (hle.compl.inter (hpre hs)).union (MeasurableSet.iUnion fun n => ?_)
  by_cases hn : duration ≤ n
  · by_cases hnH : n ≤ H
    · simpa only [hn, hnH, and_true] using (hclock (n : WithTop ℕ)).inter (hafter n hn hs)
    · simp [hnH]
  · simp [hn]

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

private lemma preResetPopulation_nonempty
    {m : ℕ} (hm : 0 < m)
    (R growth : Step.FiniteSelection ℕ ℝ)
    (hR : Measurable R.select) (hgrowth : Measurable growth.select)
    (lower upper duration r H : ℕ) (roots : Ωf → Fin m → RootIndexed.TreeNode (ℕ ⊕ ℕ) ℕ)
    (hmem : ∀ ω k, Completion.time R growth hR hgrowth lower upper duration r ω =
        ((k + 1 + duration : ℕ) : WithTop ℕ) →
      ∀ i, ∃ q ∈ capStoppedCandidate (lineages R hR) R growth upper r
        PUnit.unit (k + 1) duration (RootIndexed.StepField.left ω),
        roots ω i = (Sum.inl q.1, q.2))
    (ω : Ωf) (hbefore : (H : WithTop ℕ) <
      Completion.time R growth hR hgrowth lower upper duration r ω) :
    (trialRestartPopulationBeforeReset R growth hR lower upper duration r H
      (RootIndexed.StepField.left ω)).Nonempty := by
  let left := RootIndexed.StepField.left ω
  let τ := firstSuccessfulCompletion R growth hR lower upper duration r
  change (H : WithTop ℕ) < τ left at hbefore
  change (trialRestartPopulationBeforeReset R growth hR lower upper duration r H left).Nonempty
  cases ht : firstSuccessfulCompletion R growth hR lower upper duration r left with
  | top => simp [trialRestartPopulationBeforeReset, ht]
  | coe n =>
    rw [show τ left = (n : WithTop ℕ) from ht] at hbefore
    have hH : H ≤ n := (WithTop.coe_lt_coe.mp hbefore : H < n).le
    by_cases he : H < n - duration
    · simp [trialRestartPopulationBeforeReset, ht, he]
    · let declared : ℕ → Set (RootIndexed.StepField ℕ ℕ ℝ) := fun s =>
        {field | ∃ k, ((k + 1 + duration : ℕ) : WithTop ℕ) = s ∧
          field ∈ successEvent R growth hR lower upper duration r k}
      have hfirst : firstDeclaredSuccess declared left = (n : WithTop ℕ) := ht
      obtain ⟨k, hk, _⟩ := ((firstDeclaredSuccess_eq_iff declared left n).mp hfirst).1
      have hk' : k + 1 + duration = n := WithTop.coe_injective hk
      have hbirth : n - duration = k + 1 := by omega
      have hborn : ¬ H < k + 1 := fun hp => he (by rwa [hbirth])
      have hage : H - (k + 1) ≤ duration := by omega
      have hterminal := hmem ω k (ht.trans hk.symm) ⟨0, hm⟩
      have hne : (capStoppedCandidate (lineages R hR) R growth upper r
        PUnit.unit (k + 1) duration left).Nonempty := by
        obtain ⟨q, hq, _⟩ := hterminal
        exact ⟨q, hq⟩
      have hnonemptyEarlier (j l : ℕ) (hl : j ≤ l) (field : Mark ℕ (Step ℕ ℝ))
          (hne : (capStoppedPopulation growth upper l field).Nonempty) :
          (capStoppedPopulation growth upper j field).Nonempty := by
        induction hl with
        | refl => exact hne
        | @step l _ ih =>
          obtain ⟨q, hq⟩ := hne
          obtain ⟨p, hp, _⟩ := capStoppedPopulation_succ_parent growth upper l field q hq
          exact ih ⟨p, hp⟩
      simp only [trialRestartPopulationBeforeReset, ht, hbirth, ite_eq_right hborn, ite_eq_left hH]
      unfold capStoppedCandidate rootedCapStoppedPopulation at hne ⊢
      simp only [Finset.map_nonempty] at hne ⊢
      exact hnonemptyEarlier _ _ hage _ hne

open EndpointDeviation in
set_option maxHeartbeats 650000 in
lemma trialRestartEndpointAtLeast_ae_eq
    {m : ℕ} [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ) (hne : μ nonemptySupport = 1)
    (N : ℕ) (hN : 0 < N) (hm : 0 < m)
    (R growth : Step.FiniteSelection ℕ ℝ)
    (hR : Measurable R.select) (hgrowth : Measurable growth.select)
    (lower upper duration r H : ℕ) (roots : Ωf → Fin m → RootIndexed.TreeNode (ℕ ⊕ ℕ) ℕ) :
    let τ := Completion.time R growth hR hgrowth lower upper duration r
    let hτ := Completion.time_isStoppingTime R growth hR hgrowth lower upper duration r
    (∀ v, MeasurableSet[hτ.measurableSpace] {ω | roots ω = v}) →
    (∀ ω (n : ℕ), τ ω = n → ∀ i, (roots ω i).2.length = n) →
    (∀ ω, τ ω ≠ ⊤ → Function.Injective (roots ω)) →
    (∀ ω k, τ ω = ((k + 1 + duration : ℕ) : WithTop ℕ) →
      ∀ i, ∃ q ∈ capStoppedCandidate (lineages R hR) R growth upper r
        PUnit.unit (k + 1) duration (RootIndexed.StepField.left ω),
        roots ω i = (Sum.inl q.1, q.2)) →
    ∀ᵐ ω ∂RootIndexed.stepFieldLaw μ, ∀ x : ℝ,
      ω ∈ trialRestartEndpointAtLeast N R growth hR hgrowth lower upper duration r H roots x ↔
        x ≤ trialRestartEndpoint N R growth hR hgrowth lower upper duration r H roots ω := by
  intro τ hτ hfiber hdepth hinj hmem
  let P := RootIndexed.stepFieldLaw (Root := ℕ ⊕ ℕ) μ
  let Q := RootIndexed.stepFieldLaw (Root := Fin m) μ
  let V := RootIndexed.selectedSubtreeStepFieldVector roots
  let B : Set (RootIndexed.StepField (Fin m) ℕ ℝ) :=
    {field | ∀ n, (firstNSelectedPopulation m N n field).Nonempty}ᶜ
  have hB : MeasurableSet B := by
    apply MeasurableSet.compl
    rw [show {field | ∀ n, (firstNSelectedPopulation m N n field).Nonempty} =
      ⋂ n : ℕ, {field | (firstNSelectedPopulation m N n field).Nonempty} by ext field; simp]
    apply MeasurableSet.iInter
    intro n
    have hpop := (RootIndexed.selectedPopulationTotalized_adapted (α := ℕ) N (Finset.univ : Finset (Fin m))
      (fun _ => (0 : ℝ)) id measurable_id id measurable_id n).mono (RootIndexed.stepFiltration.le _) le_rfl
    convert hpop (Set.to_countable
      {s : Finset (RootIndexed.TreeNode (Fin m) ℕ) | s.Nonempty}).measurableSet using 1
    ext field
    have he : firstNSelectedPopulation m N n field =
        RootIndexed.selectedPopulationTotalized N Finset.univ (fun _ => (0 : ℝ)) id id n field := by
      unfold firstNSelectedPopulation
      congr 1
      exact Subsingleton.elim _ _
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, he]
  have hnull : Q B = 0 := by
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [RootIndexed.selectedPopulationTotalized_nonempty_ae N
      (Finset.univ : Finset (Fin m)) ⟨⟨0, hm⟩, Finset.mem_univ _⟩ (fun _ => 0) hN μ hnorm hne]
      with ω hω
    change ¬ ¬ ∀ n, (firstNSelectedPopulation m N n ω).Nonempty
    apply not_not_intro
    intro n
    have he : firstNSelectedPopulation m N n ω =
        RootIndexed.selectedPopulationTotalized N Finset.univ (fun _ => (0 : ℝ)) id id n ω := by
      unfold firstNSelectedPopulation
      congr 1
      exact Subsingleton.elim _ _
    rw [he]
    exact hω n
  have hbad : P ({ω | τ ω ≠ ⊤} ∩ V ⁻¹' B) = 0 := by
    have h := RootIndexed.stopped_selectedSubtreeStepFieldVector_event_factorization_on_finite
      μ τ hτ roots (Set.to_countable _) hfiber hdepth hinj Set.univ B MeasurableSet.univ hB
    change P ((Set.univ ∩ {ω | τ ω ≠ ⊤}) ∩ V ⁻¹' B) =
      P (Set.univ ∩ {ω | τ ω ≠ ⊤}) * Q B at h
    simpa only [Set.univ_inter, hnull, mul_zero] using h
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hbad] with ω hgood
  intro x
  let left := RootIndexed.StepField.left ω
  let s := trialRestartPopulationBeforeReset R growth hR lower upper duration r H left
  by_cases ht : τ ω ≤ (H : WithTop ℕ)
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top ht)
    have hnH : n ≤ H := WithTop.coe_le_coe.mp (hn.trans_le ht)
    have hfin : τ ω ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top ht
    have hf : ∀ j, (firstNSelectedPopulation m N j (V ω)).Nonempty := by
      have h := fun hmem' : V ω ∈ B => hgood ⟨hfin, hmem'⟩
      change ¬ ¬ ∀ j, (firstNSelectedPopulation m N j (V ω)).Nonempty at h
      exact not_not.mp h
    let c := trialResetPositionAtGeneration R growth hR upper duration r n left
    have hreset :
        x ≤ trialRestartEndpoint N R growth hR hgrowth lower upper duration r H roots ω ↔
          x - c ≤ firstNSelectedEndpointMinimum m N (H - n) (V ω) := by
      change (x ≤ (if τ ω ≤ (H : WithTop ℕ) then _ else _)) ↔ _
      rw [ite_eq_left ht]
      have hidx : (Completion.time R growth hR hgrowth lower upper duration r ω).untopD 0 = n := by
        change (τ ω).untopD 0 = n
        rw [← hn, WithTop.untopD_coe]
      simp only [hidx, c, left, V]
      constructor <;> intro hh <;> linarith only [hh]
    have hfresh :
        V ω ∈ RootIndexed.selectedPopulationEndpointAtLeast N Finset.univ (fun _ => c) (H - n) x ↔
          x - c ≤ firstNSelectedEndpointMinimum m N (H - n) (V ω) := by
      have he := RootIndexed.selectedPopulationEndpointAtLeast_add_initial (α := ℕ) N
        (Finset.univ : Finset (Fin m)) (fun _ => (0 : ℝ)) (H - n) (x - c) c
      simp only [zero_add, sub_add_cancel] at he
      rw [he]
      rw [firstNSelectedEndpointMinimum_eq_inf'_of_nonempty m N (H - n) _ (hf _), Finset.le_inf'_iff]
      have hpopEq : firstNSelectedPopulation m N (H - n) (V ω) =
          RootIndexed.selectedPopulationTotalized N Finset.univ (fun _ => (0 : ℝ)) id id (H - n) (V ω) := by
        unfold firstNSelectedPopulation
        congr 1
        exact Subsingleton.elim _ _
      rw [hpopEq]
      rfl
    rw [hreset]
    change ((H : WithTop ℕ) < τ ω ∧ _) ∨ (∃ j ≤ H, τ ω = (j : WithTop ℕ) ∧ _) ↔ _
    constructor
    · rintro (⟨hlt, _⟩ | ⟨j, _, hj, hp⟩)
      · exact (hlt.not_ge ht).elim
      · have hnj : n = j := WithTop.coe_injective (hn.trans hj)
        subst j
        exact hfresh.mp hp
    · intro hx
      exact Or.inr ⟨n, hnH, hn.symm, hfresh.mpr hx⟩
  · have hl : (H : WithTop ℕ) < τ ω := lt_of_not_ge ht
    have hnonempty := preResetPopulation_nonempty hm R growth hR hgrowth lower upper duration r H
      roots hmem ω hl
    have hnothit : ¬ ∃ j ≤ H, τ ω = (j : WithTop ℕ) ∧
        RootIndexed.subtreeStepFieldVector (roots ω) ω ∈
          RootIndexed.selectedPopulationEndpointAtLeast N Finset.univ
            (fun _ => trialResetPositionAtGeneration R growth hR upper duration r j left) (H - j) x := by
      rintro ⟨j, hj, hc, _⟩
      exact ht (hc.le.trans (WithTop.coe_le_coe.mpr hj))
    change (((H : WithTop ℕ) < τ ω ∧ _) ∨ (∃ j ≤ H, τ ω = (j : WithTop ℕ) ∧ _)) ↔
      x ≤ (if τ ω ≤ (H : WithTop ℕ) then _ else _)
    rw [ite_eq_right ht, or_iff_left hnothit, and_iff_right hl]
    unfold preResetMinimum
    rw [dite_eq_left hnonempty, Finset.le_inf'_iff]

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
    have hpop := (trialRestartPopulationBeforeReset_measurable R growth hR hgrowth
      lower upper duration r H).comp hleftMeas
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

open EndpointDeviation in
/-- Compare both real-valued endpoints on the laws of their pre-sampled fields. -/
lemma measure_firstNSelectedEndpointMinimum_ge_le_restart
    {m : ℕ} [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ) (hne : μ nonemptySupport = 1)
    (N : ℕ) (hN : 0 < N) (hm : 0 < m)
    (R growth : Step.FiniteSelection ℕ ℝ)
    (hR : Measurable R.select) (hgrowth : Measurable growth.select)
    (lower upper duration : ℕ) (H : ℕ)
    (roots : Ωf → Fin m → RootIndexed.TreeNode (ℕ ⊕ ℕ) ℕ) :
    let τ := Completion.time R growth hR hgrowth lower upper duration (0 : ℕ)
    let hτ := Completion.time_isStoppingTime R growth hR hgrowth lower upper duration (0 : ℕ)
    let trials := SelectedPath.Population.leftBRWFamily_finiteSlices R growth hR hgrowth
      upper duration (0 : ℕ)
    let installed := RootIndexed.stoppedRankInstalledTrajectoryField N ({0} : Finset ℕ)
      (fun _ => 0) trials τ hτ
    let P := RootIndexed.stepFieldLaw (Root := ℕ ⊕ ℕ) μ
    let Q := RootIndexed.stepFieldLaw (Root := Fin 1) μ
    (∀ v, MeasurableSet[hτ.measurableSpace] {ω | roots ω = v}) →
    (∀ ω (n : ℕ), τ ω = n → ∀ i, (roots ω i).2.length = n) →
    (∀ ω, τ ω ≠ ⊤ → Function.Injective (roots ω)) →
    (∀ ω k, τ ω = ((k + 1 + duration : ℕ) : WithTop ℕ) →
      ∀ i, ∃ q ∈ capStoppedCandidate (lineages R hR) R growth upper (0 : ℕ)
        PUnit.unit (k + 1) duration (RootIndexed.StepField.left ω),
        roots ω i = (Sum.inl q.1, q.2)) →
    (∀ x, P (installed ⁻¹' RootIndexed.selectedPopulationEndpointAtLeast
      (α := ℕ) N ({0} : Finset ℕ) (fun _ => 0) H x) ≤
        P (trialRestartEndpointAtLeast N R growth hR hgrowth lower upper duration 0 H roots x)) →
    let order := RootIndexed.addressLinearOrder (Fin 1) ℕ
    ∀ x, Q {field | x ≤ @firstNSelectedEndpointMinimum 1 N H order field} ≤
      P {ω | x ≤ trialRestartEndpoint N R growth hR hgrowth lower upper duration 0 H roots ω} := by
  intro τ hτ trials installed P Q hfiber hdepth hinj hmember htail order x
  let _ : LinearOrder (RootIndexed.TreeNode (Fin 1) ℕ) := order
  let B := RootIndexed.selectedPopulationEndpointAtLeast (α := ℕ) N ({0} : Finset ℕ)
    (fun _ => 0) H x
  let B₁ := RootIndexed.selectedPopulationEndpointAtLeast (α := ℕ) N Finset.univ
    (fun _ : Fin 1 => (0 : ℝ)) H x
  have horder (u v : RootIndexed.TreeNode (Fin 1) ℕ) :
      @LT.lt _ order.toLT u v ↔
        @LT.lt _ natTreeOrder.toLT (u.1.val, u.2) (v.1.val, v.2) := by
    rw [RootIndexed.addressLinearOrder_lt_iff (Fin 1) ℕ, RootIndexed.addressLinearOrder_lt_iff ℕ ℕ]
    simp [Fin.ext_iff]
  have hrelabel : (RootIndexed.stepFieldLaw (Root := ℕ) μ) B = Q B₁ := by
    have hroots : Finset.univ.image (Fin.val : Fin 1 → ℕ) = {0} := by
      ext j
      simp [Fin.val_eq_zero]
    have h := RootIndexed.measure_selectedPopulationEndpointAtLeast_relabel
      μ (Fin.val : Fin 1 → ℕ) Fin.val_injective horder N (fun _ => 0) H x
    rw [hroots] at h
    exact h
  obtain ⟨hinst, hlaw⟩ := RootIndexed.stoppedRankInstalledTrajectoryField_measurable_law
    μ N ({0} : Finset ℕ) (fun _ => 0) trials τ hτ
  have hB : MeasurableSet B :=
    RootIndexed.measurableSet_selectedPopulationEndpointAtLeast N ({0} : Finset ℕ) (fun _ => 0) H x
  have hactual : Q B₁ = P (installed ⁻¹' B) := by
    rw [← hrelabel, ← Measure.map_apply hinst hB, hlaw]
  have hsame : B₁ =ᵐ[Q] {field | x ≤ @firstNSelectedEndpointMinimum 1 N H order field} := by
    filter_upwards [firstNSelectedEndpointMinimum_eq_population_inf'_ae
      1 N H (by decide) hN μ hnorm hne] with field hfield
    obtain ⟨hpop, hmin⟩ := hfield
    rw [hmin, Finset.le_inf'_iff]
    have heq : firstNSelectedPopulation 1 N H field =
        RootIndexed.selectedPopulationTotalized N Finset.univ
          (fun _ : Fin 1 => (0 : ℝ)) id id H field := by
      unfold firstNSelectedPopulation
      congr 1
      exact Subsingleton.elim _ _
    rw [heq]
    rfl
  have hrestart : trialRestartEndpointAtLeast N R growth hR hgrowth lower upper duration 0 H roots x
      =ᵐ[P] {ω | x ≤ trialRestartEndpoint N R growth hR hgrowth lower upper duration 0 H roots ω} := by
    filter_upwards [trialRestartEndpointAtLeast_ae_eq μ hnorm hne N hN hm R growth hR hgrowth
      lower upper duration 0 H roots hfiber hdepth hinj hmember] with ω hω
    exact hω x
  exact (measure_congr hsame).ge.trans (hactual.le.trans ((htail x).trans (measure_congr hrestart).le))

open EndpointDeviation in
/-- The negative exponential moment of the restart endpoint is bounded by
that of the actual single-root endpoint. -/
lemma lintegral_exp_neg_trialRestartEndpoint_le
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ]
    (hnorm : HasBoundaryNormalization realPotential μ) (hne : μ nonemptySupport = 1)
    (N : ℕ) (hN : 0 < N) (H : ℕ) (F : Ωf → ℝ) (hF : Measurable F)
    (horder : let order := RootIndexed.addressLinearOrder (Fin 1) ℕ
      ∀ x : ℝ, (RootIndexed.stepFieldLaw (Root := Fin 1) μ)
        {ω | x ≤ @firstNSelectedEndpointMinimum 1 N H order ω} ≤
        (RootIndexed.stepFieldLaw (Root := ℕ ⊕ ℕ) μ) {ω | x ≤ F ω}) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (-F ω))
      ∂RootIndexed.stepFieldLaw (Root := ℕ ⊕ ℕ) μ) ≤ ENNReal.ofReal 1 := by
  let _ : LinearOrder (RootIndexed.TreeNode (Fin 1) ℕ) := RootIndexed.addressLinearOrder (Fin 1) ℕ
  let P := RootIndexed.stepFieldLaw (Root := ℕ ⊕ ℕ) μ
  let Q := RootIndexed.stepFieldLaw (Root := Fin 1) μ
  let G := firstNSelectedEndpointMinimum 1 N H
  have hG : Measurable G := measurable_firstNSelectedEndpointMinimum 1 N H
  have hFe : Measurable (fun ω => Real.exp (-F ω)) := Real.continuous_exp.measurable.comp hF.neg
  have hGe : Measurable (fun ω => Real.exp (-G ω)) := Real.continuous_exp.measurable.comp hG.neg
  have hle : (∫⁻ ω, ENNReal.ofReal (Real.exp (-F ω)) ∂P) ≤
      ∫⁻ ω, ENNReal.ofReal (Real.exp (-G ω)) ∂Q := by
    rw [lintegral_eq_lintegral_meas_lt P (.of_forall fun _ => Real.exp_nonneg _) hFe.aemeasurable,
      lintegral_eq_lintegral_meas_lt Q (.of_forall fun _ => Real.exp_nonneg _) hGe.aemeasurable]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioi (a := (0 : ℝ)))] with x hx
    have hxpos : 0 < x := hx
    have hL : {ω | x < Real.exp (-F ω)} = {ω | -Real.log x ≤ F ω}ᶜ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, ← Real.log_lt_iff_lt_exp hxpos, lt_neg, not_le]
    have hR : {ω | x < Real.exp (-G ω)} = {ω | -Real.log x ≤ G ω}ᶜ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, ← Real.log_lt_iff_lt_exp hxpos, lt_neg, not_le]
    have hFs : MeasurableSet {ω | -Real.log x ≤ F ω} := hF measurableSet_Ici
    have hGs : MeasurableSet {ω | -Real.log x ≤ G ω} := hG measurableSet_Ici
    rw [hL, hR, prob_compl_eq_one_sub hFs, prob_compl_eq_one_sub hGs]
    exact tsub_le_tsub_left (horder (-Real.log x)) _
  have hb := ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.EndpointDeviation.finiteRootStepFieldLaw_lintegral_exp_neg_firstNSelectedEndpointMinimum_le
    1 N H (by decide) hN μ hnorm hne
  simpa only [Nat.cast_one] using hle.trans hb

open EndpointDeviation Combinatorics.Branching.Step.FiniteSelection in
/-- Bound the full positive endpoint by the displacement envelope and the
positive part of the centered continuation on the reset event. -/
lemma trialRestartEndpoint_pos_le
    {m : ℕ} [LinearOrder (RootIndexed.TreeNode (Fin m) ℕ)]
    (N : ℕ) (B growth : Step.FiniteSelection ℕ ℝ) (hB : B.IsBoundedBy 2)
    (hBmeas : Measurable B.select) (hgrowth : Measurable growth.select)
    (M : ℝ) (hM : 0 ≤ M)
    (hcutoff : ∀ ξ j, j ∈ growth ξ → ξ.potentialValue' realPotential j ≤ M)
    (lower upper duration r H : ℕ) (roots : Ωf → Fin m → RootIndexed.TreeNode (ℕ ⊕ ℕ) ℕ)
    (ω : Ωf) :
    let R := firstOrBelowPotential B realPotential M
    let hR := firstOrBelowPotential_measurable B hBmeas realPotential M
    let τ := Completion.time R growth hR hgrowth lower upper duration r
    let left := RootIndexed.StepField.left ω
    let mark j := left r (selectedPath R r j left)
    (∀ j, (mark j).IsOrderedBy realPotential) →
    (∀ j, (B (mark j)).Nonempty) →
    max (trialRestartEndpoint N R growth hR hgrowth lower upper duration r H roots ω) 0 ≤
      (M * H + ∑ j ∈ Finset.range H, firstSelectedSlotPositivePotential B realPotential (mark j)) +
      if τ ω ≤ (H : WithTop ℕ) then
        max (firstNSelectedEndpointMinimum m N (H - (τ ω).untopD 0)
          (RootIndexed.selectedSubtreeStepFieldVector roots ω)) 0
      else 0 := by
  intro R hR τ left mark hordered hne
  obtain ⟨hpre, hreset⟩ := trialRestart_beforeReset_and_shift_le B growth hB hBmeas M hM hcutoff
    lower upper duration r H left hordered hne
  let c := M * (H : ℝ) + ∑ j ∈ Finset.range H, firstSelectedSlotPositivePotential B realPotential (mark j)
  have hc : 0 ≤ c := by
    apply add_nonneg (mul_nonneg hM (Nat.cast_nonneg _))
    exact Finset.sum_nonneg fun _ _ => le_max_left _ _
  by_cases ht : τ ω ≤ (H : WithTop ℕ)
  · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_le_ne_top WithTop.coe_ne_top ht)
    have hnH : n ≤ H := WithTop.coe_le_coe.mp (hn.trans_le ht)
    have hn' : firstSuccessfulCompletion R growth hR lower upper duration r left = (n : WithTop ℕ) :=
      hn.symm
    have hshift := (le_max_right 0 _).trans (hreset n hnH hn')
    change max (if τ ω ≤ (H : WithTop ℕ) then _ else _) 0 ≤ c + _
    rw [ite_eq_left ht, ite_eq_left ht]
    have hidx : (Completion.time R growth hR hgrowth lower upper duration r ω).untopD 0 = n := by
      change (τ ω).untopD 0 = n
      rw [← hn, WithTop.untopD_coe]
    have hidx' : (τ ω).untopD 0 = n := hidx
    simp only [hidx, hidx']
    exact max_le (add_le_add hshift (le_max_left _ _)) (add_nonneg hc (le_max_right _ _))
  · change max (if τ ω ≤ (H : WithTop ℕ) then _ else _) 0 ≤ c + _
    rw [ite_eq_right ht, ite_eq_right ht, add_zero]
    change max (preResetMinimum R growth hR lower upper duration r H left) 0 ≤ c
    unfold preResetMinimum
    dsimp only
    split
    · rename_i hs
      obtain ⟨q, hq⟩ := hs
      exact (max_le_max_right 0 (Finset.inf'_le _ hq)).trans (by
        simpa only [max_comm] using hpre q hq)
    · simpa using hc

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas
