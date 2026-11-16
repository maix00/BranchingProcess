/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.FailureDisplacement
import all Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.TrialIndependence
import MeasureTheory.BranchingWalk.Step.Selection.Potential
import Probability.Sequence.IID.GeometricReward.Definitions

/-!
# First successful trial's split position

## Internal proof declarations

* `trialSplitParent` gives the address $\rho_k$ of the split parent in the
  pre-sampled tree, with the Lean index starting at zero.
* `trialGrowthRoot` gives the first child $v_k$ of that split parent.
* `splitCycle_first_success_at_completion` identifies the first successful
  trial in split order at the observable success completion.
* `trialGrowthRoot_eq_growthTrialRootAt_of_splitCount` identifies $v_k$
  with the generation-indexed candidate when $k$ splits precede its split mark.
* `lintegral_firstSuccessfulTrial_root_positive_le` bounds the positive
  position of the first successful root on ${kappale K}$ by
  $mathbb E[Y_+]/(p_0p_1)+KM$ in expectation.
* `exists_firstSuccessfulTrial_position_upperTail` bounds
  $e^{\lambda x}\mathbb P(\kappa\le K,
    V(\rho_\kappa)\ge x+(K-1)M)$ by $\sum_{k=1}^K m_\lambda^k$,
  where $m_\lambda=p_0/(1-A_\lambda)<\infty$. The same bound controls
  $V(v_\kappa)$ with threshold $x+KM$.

The position decomposition adds the signed waiting displacements and the
second-child displacements at the preceding splits, as in Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(Fudan University, 2026), Chapter 4, Theorem 1.1 at $a=0$.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas

open Combinatorics.Branching Combinatorics.UlamHarris
open Combinatorics.Branching.Step.FiniteSelection
open _root_.Combinatorics.Selection.NSelection
open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate)
open ProbabilityTheory.BranchingRandomWalk.Selection.Stepwise.SplitTime
open SelectedPath.GrowthTrial
open Combinatorics.Branching.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath

/-- Absolute address of the split parent, following the second child to each
subsequent candidate on the pre-sampled tree. -/
noncomputable def trialSplitParent (R : Step.FiniteSelection ℕ ℝ) :
    ℕ → Mark ℕ (Step ℕ ℝ) → TreeNode ℕ
  | 0, ω => (selectedPopulationFirstSplitRoots R ω 1).dropLast
  | k + 1, ω => selectedPopulationFirstSplitRoots R ω 1 ++
      trialSplitParent R k (selectedPopulationFirstSplitSubtrees R ω 1)

noncomputable def trialGrowthRoot (R : Step.FiniteSelection ℕ ℝ) :
    ℕ → Mark ℕ (Step ℕ ℝ) → TreeNode ℕ
  | 0, ω => selectedPopulationFirstSplitRoots R ω 0
  | k + 1, ω => selectedPopulationFirstSplitRoots R ω 1 ++
      trialGrowthRoot R k (selectedPopulationFirstSplitSubtrees R ω 1)

lemma trialGrowthRoot_eq_growthTrialRootAt_of_splitCount
    {Root : Type}
    (R : Step.FiniteSelection ℕ ℝ) (hR : Measurable R.select)
    (r : Root) (ω : RootIndexed.StepField Root ℕ ℝ)
    (hne : ∀ u, (R (ω r u)).Nonempty) (k n : ℕ)
    (hs : splitEvent R r n ω) (hcount : splitCount R r n ω = k) :
    trialGrowthRoot R k (ω r) =
      (growthTrialRootAt (lineages R hR) R r PUnit.unit (n + 1) ω).2 := by
  classical
  induction k generalizing Root r ω n with
  | zero =>
    have hbefore (j : ℕ) (hj : j < n) : ¬ splitEvent R r j ω := by
      intro hsplit
      have halive : ∀ i, isAlive R r i ω := by
        intro i
        induction i with
        | zero => trivial
        | succ i ih => exact ⟨ih, hne _⟩
      have hmem : j ∈ (Finset.range n).filter fun i => isAlive R r i ω ∧ splitEvent R r i ω :=
        Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, halive j, hsplit⟩
      exact (Nat.ne_of_gt (Finset.card_pos.mpr ⟨j, hmem⟩)) hcount
    have hraw := rawSplitTime_eq_of_first_sampled_split R r ω n hne hs hbefore
    have hroot := (firstSplitRoots_eq_of_rawSplitTime_eq R r ω n hne hraw).1
    rw [trialGrowthRoot, (root_at_split R hR r n ω hs).1]
    exact hroot
  | succ k ih =>
    have halive : ∀ i, isAlive R r i ω := by
      intro i
      induction i with
      | zero => trivial
      | succ i ih => exact ⟨ih, hne _⟩
    have hex : ∃ j, j < n ∧ splitEvent R r j ω := by
      have hpos : 0 < splitCount R r n ω := by omega
      change 0 < ((Finset.range n).filter fun j =>
        isAlive R r j ω ∧ splitEvent R r j ω).card at hpos
      obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
      simp only [Finset.mem_filter, Finset.mem_range] at hj
      exact ⟨j, hj.1, hj.2.2⟩
    let j := Nat.find hex
    have hj : j < n := (Nat.find_spec hex).1
    have ht : splitEvent R r j ω := (Nat.find_spec hex).2
    have hearly (i : ℕ) (hi : i < j) : ¬ splitEvent R r i ω :=
      fun hisplit => Nat.find_min hex hi ⟨hi.trans hj, hisplit⟩
    let m := n - (j + 1)
    have hn : j + 1 + m = n := by dsimp [m]; omega
    let tail := continuationFieldAtSplit R r j ω
    have htail : splitEvent R PUnit.unit m tail := by
      have hmark := mark_decompose_at_split_field R r j m ω ht
      rw [hn] at hmark
      change ω r (selectedPath R r n ω) ∈ splitBy R at hs
      change tail PUnit.unit (selectedPath R PUnit.unit m tail) ∈ splitBy R
      unfold tail
      rw [← hmark]
      exact hs
    have htailcount : splitCount R PUnit.unit m tail = k := by
      have heq := splitCount_add_after_first_split R r ω j m (halive j) ht hearly
      rw [hn, hcount] at heq
      change k + 1 = 1 + splitCount R PUnit.unit m tail at heq
      omega
    have htailalive : isAlive R PUnit.unit m tail :=
      (isAlive_decompose_at_split_field R r j ω (halive j) ht m).mp (hn ▸ halive n)
    have hraw := rawSplitTime_eq_of_first_sampled_split R r ω j hne ht hearly
    have hroot : selectedPopulationFirstSplitRoots R (ω r) 1 = continuationPrefix R r j ω :=
      (firstSplitRoots_eq_of_rawSplitTime_eq R r ω j hne hraw).2
    have hfield : selectedPopulationFirstSplitSubtrees R (ω r) 1 = tail PUnit.unit := by
      change subtreeStepField (selectedPopulationFirstSplitRoots R (ω r) 1) (ω r) = _
      rw [hroot]
      rfl
    have hrec := ih PUnit.unit tail (fun _ => hne _) m htail htailcount
    rw [trialGrowthRoot, hroot, hfield, hrec, (root_at_split R hR PUnit.unit m tail htail).1]
    rw [← hn, (root_at_recursive_split R hR r j m ω (halive j) ht htailalive htail).1]

private lemma splitCycle_trial_eq_subtree
    {D E : Type*} (R : Step.FiniteSelection ℕ ℝ)
    (F : Mark ℕ (Step ℕ ℝ) → D) (G : Mark ℕ (Step ℕ ℝ) → E)
    (k : ℕ) (ω : Mark ℕ (Step ℕ ℝ)) :
    (splitCycle R F G k ω).2 = G (subtreeStepField (trialGrowthRoot R k ω) ω) := by
  induction k generalizing ω with
  | zero => rfl
  | succ k ih =>
    rw [splitCycle, ih, trialGrowthRoot]
    congr 1
    funext u
    change ω (selectedPopulationFirstSplitRoots R ω 1 ++
        (trialGrowthRoot R k (selectedPopulationFirstSplitSubtrees R ω 1) ++ u)) =
      ω ((selectedPopulationFirstSplitRoots R ω 1 ++
        trialGrowthRoot R k (selectedPopulationFirstSplitSubtrees R ω 1)) ++ u)
    rw [List.append_assoc]

private lemma exists_split_before_of_lt_splitCount
    {Root : Type*} (R : Step.FiniteSelection ℕ ℝ) (r : Root)
    (ω : RootIndexed.StepField Root ℕ ℝ) (k n : ℕ)
    (hk : k < splitCount R r n ω) :
    ∃ j < n, splitEvent R r j ω ∧ splitCount R r j ω = k := by
  classical
  induction n with
  | zero => simp [splitCount_eq_sum_indicators] at hk
  | succ n ih =>
    by_cases hn : k < splitCount R r n ω
    · obtain ⟨j, hj, hs, hc⟩ := ih hn
      exact ⟨j, hj.trans (Nat.lt_succ_self n), hs, hc⟩
    · have heq : splitCount R r (n + 1) ω = splitCount R r n ω +
          (if isAlive R r n ω ∧ splitEvent R r n ω then 1 else 0) := by
        rw [splitCount_eq_sum_indicators R r (n + 1), Finset.sum_range_succ,
          ← splitCount_eq_sum_indicators]
      rw [heq] at hk
      split at hk
      · rename_i hs
        exact ⟨n, Nat.lt_succ_self n, hs.2, by omega⟩
      · omega

lemma splitCycle_first_success_at_completion
    {Root : Type}
    (R growth : Step.FiniteSelection ℕ ℝ) (hR : Measurable R.select)
    (lower upper duration : ℕ) (r : Root)
    (ω : RootIndexed.StepField Root ℕ ℝ) (hne : ∀ u, (R (ω r u)).Nonempty)
    (t : ℕ) (ht : firstSuccessfulCompletion R growth hR lower upper duration r ω = t) :
    let G := growthTrialSuccess growth lower upper duration
    ∃ n : ℕ, n + 1 + duration = t ∧
      splitEvent R r n ω ∧
      let k := splitCount R r n ω
      (splitCycle R (splitWaitingDisplacement R) G k (ω r)).2 ∧
      (∀ j < k, ¬ (splitCycle R (splitWaitingDisplacement R) G j (ω r)).2) ∧
      trialGrowthRoot R k (ω r) =
        (growthTrialRootAt (lineages R hR) R r PUnit.unit (n + 1) ω).2 := by
  intro G
  let declarations : ℕ → Set (RootIndexed.StepField Root ℕ ℝ) := fun i =>
    {field | ∃ n, ((n + 1 + duration : ℕ) : WithTop ℕ) = i ∧
      field ∈ successEvent R growth hR lower upper duration r n}
  have hfirst : firstDeclaredSuccess declarations ω = (t : WithTop ℕ) := ht
  obtain ⟨⟨n, hnt, hsuccess⟩, hbefore⟩ := (firstDeclaredSuccess_eq_iff declarations ω t).mp hfirst
  have hnt' : n + 1 + duration = t := WithTop.coe_injective hnt
  have halive : ∀ j, isAlive R r j ω := by
    intro j
    induction j with
    | zero => trivial
    | succ j ih => exact ⟨ih, hne _⟩
  have htrial (j : ℕ) (hs : splitEvent R r j ω) :
      (splitCycle R (splitWaitingDisplacement R) G (splitCount R r j ω) (ω r)).2 ↔
        ω ∈ successEvent R growth hR lower upper duration r j := by
    let u := growthTrialRootAt (lineages R hR) R r PUnit.unit (j + 1) ω
    have hu : u.1 = r := growthTrialRootAt_root (lineages R hR) R r PUnit.unit (j + 1) ω
    rw [splitCycle_trial_eq_subtree,
      trialGrowthRoot_eq_growthTrialRootAt_of_splitCount R hR r ω hne _ j hs rfl]
    change G (fun v => ω r (u.2 ++ v)) ↔
      isAlive R r j ω ∧ splitEvent R r j ω ∧ G (fun v => ω u.1 (u.2 ++ v))
    simp [hu, halive j, hs]
  refine ⟨n, hnt', hsuccess.2.1, (htrial n hsuccess.2.1).2 hsuccess, ?_, ?_⟩
  · intro k hk hc
    obtain ⟨j, hj, hs, hcount⟩ := exists_split_before_of_lt_splitCount R r ω k n hk
    apply hbefore (j + 1 + duration) (by omega)
    apply Exists.intro j
    refine ⟨rfl, (htrial j hs).mp ?_⟩
    rwa [hcount]
  · exact trialGrowthRoot_eq_growthTrialRootAt_of_splitCount R hR r ω hne _ n hsuccess.2.1 rfl

private lemma trialPositions_le
    {E : Type*} [MeasurableSpace E]
    (R : Step.FiniteSelection ℕ ℝ) (G : Mark ℕ (Step ℕ ℝ) → E)
    (M : ℝ) (hM : 0 ≤ M) (k : ℕ) (ω : Mark ℕ (Step ℕ ℝ))
    (hmarks : ∀ u, (R (ω u)).Nonempty ∧ firstSelectedSlot R (ω u) = 0 ∧
      (2 ≤ (R (ω u)).card → value' (ω u) (firstSelectedSlot R (ω u)) ≤ M ∧
        value' (ω u) (secondSelectedSlot R (ω u)) ≤ M)) :
    let S := ∑ i ∈ Finset.range (k + 1), (splitCycle R (splitWaitingDisplacement R) G i ω).1
    Spine.pathPotential realPotential ω (trialSplitParent R k ω) ≤ S + (k : ℝ) * M ∧
      Spine.pathPotential realPotential ω (trialGrowthRoot R k ω) ≤ S + (k + 1 : ℕ) * M := by
  induction k generalizing ω with
  | zero =>
    constructor
    · simpa [trialSplitParent, splitCycle, Finset.sum_range_succ] using
        (splitWaitingDisplacement_eq_parentPosition R ω
          (fun u => (hmarks u).1) (fun u => (hmarks u).2.1)).le
    · simpa [trialGrowthRoot, splitCycle, Finset.sum_range_succ] using
        splitChildPosition_le_splitWaitingDisplacement_add R ω
          (fun u => (hmarks u).1) (fun u => (hmarks u).2.1) M hM (fun u => (hmarks u).2.2) 0
  | succ k ih =>
    let v := selectedPopulationFirstSplitRoots R ω 1
    let tail := selectedPopulationFirstSplitSubtrees R ω 1
    have htail : tail = subtreeStepField v ω := rfl
    have hmarks' (u : TreeNode ℕ) :
        (R (tail u)).Nonempty ∧ firstSelectedSlot R (tail u) = 0 ∧
          (2 ≤ (R (tail u)).card → value' (tail u) (firstSelectedSlot R (tail u)) ≤ M ∧
            value' (tail u) (secondSelectedSlot R (tail u)) ≤ M) := by
      rw [htail]
      exact hmarks (v ++ u)
    have hstep := splitChildPosition_le_splitWaitingDisplacement_add R ω
      (fun u => (hmarks u).1) (fun u => (hmarks u).2.1) M hM (fun u => (hmarks u).2.2) 1
    obtain ⟨hparent, hroot⟩ := ih tail hmarks'
    dsimp only
    rw [Finset.sum_range_succ']
    simp only [splitCycle]
    constructor
    · change Spine.pathPotential realPotential ω (v ++ trialSplitParent R k tail) ≤ _
      rw [Spine.pathPotential_append, ← htail, Nat.cast_succ]
      linarith
    · change Spine.pathPotential realPotential ω (v ++ trialGrowthRoot R k tail) ≤ _
      rw [Spine.pathPotential_append, ← htail, Nat.cast_succ]
      linarith

lemma exists_firstSuccessfulTrial_position_upperTail
    {ι X : Type*} [MeasurableSpace X]
    (L : StepLaw ι ℕ X) [IsProbabilityMeasure L.raw]
    (hexp : HasLeftmostPositiveExponentialMoment L)
    (hnonempty : L.raw nonemptySupport = 1)
    (growth : Step.FiniteSelection ℕ ℝ) (hgrowth : Measurable growth.select)
    (M : ℝ) (hM : 0 ≤ M) :
    let μ := L.sortedPotentialImage
    let R := firstOrBelowPotential (firstNBySlotOrder (α := ℕ) (X := ℝ) 2) realPotential M
    0 < μ (splitBy R) →
    ∃ lam > (0 : ℝ), let A := ∫⁻ ξ, ENNReal.ofReal (Real.exp (lam * value' ξ 0)) *
          (splitBy R)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ξ ∂μ
      let m := μ (splitBy R) / (1 - A)
      μ {ξ | (R ξ).Nonempty} = 1 ∧ A < 1 ∧ m < ∞ ∧
      ∀ (lower upper duration : ℕ) (x : ℝ) (K : ℕ),
        let G := growthTrialSuccess growth lower upper duration
        ENNReal.ofReal (Real.exp (lam * x)) *
          offspringFieldLaw μ {ω | ∃ k < K,
            (splitCycle R (splitWaitingDisplacement R) G k ω).2 ∧
            (∀ j < k, ¬ (splitCycle R (splitWaitingDisplacement R) G j ω).2) ∧
            (x + ((K - 1 : ℕ) : ℝ) * M ≤
              Spine.pathPotential realPotential ω (trialSplitParent R k ω) ∨
              x + (K : ℝ) * M ≤ Spine.pathPotential realPotential ω (trialGrowthRoot R k ω))} ≤
          ∑ k ∈ Finset.range K, m ^ (k + 1) := by
  intro μ R hp
  let B := firstNBySlotOrder (α := ℕ) (X := ℝ) 2
  have hR : Measurable R.select :=
    firstOrBelowPotential_measurable B firstTwoBySlotOrder_measurable realPotential M
  have hordered : ∀ᵐ ξ ∂μ, ξ.IsOrderedBy realPotential := by
    apply (ae_mem_iff_measure_eq (orderedBySteps_measurable realPotential).nullMeasurableSet).2
    rw [show μ = L.sortedPotentialImage from rfl, L.sortedPotentialImage_orderedBy]
    simp
  have hsupport : ∀ᵐ ξ ∂μ, ξ ∈ nonemptySupport := by
    apply (ae_mem_iff_measure_eq nonemptySupport_measurable.nullMeasurableSet).2
    rw [show μ = L.sortedPotentialImage from rfl, L.sortedPotentialImage_nonemptySupport,
      L.sorted_nonemptySupport, hnonempty]
    exact measure_univ.symm
  have hzero : ∀ᵐ ξ ∂μ, 0 ∈ R ξ := by
    filter_upwards [hordered, hsupport] with ξ hord hs
    obtain ⟨i, hi⟩ := hs
    have hsurvive : survive ξ 0 :=
      (survive_map_iff realPotential ξ 0).mp
        (orderedSteps_survive_of_le (ξ.map realPotential) hord (Nat.zero_le i)
          ((survive_map_iff realPotential ξ i).mpr hi))
    have hless : {j : ℕ | j ∈ support ξ ∧
        valueKey (fun i : ℕ => i) j < valueKey (fun i : ℕ => i) 0} = ∅ := by
      ext j
      simp [valueKey, Prod.Lex.lt_iff]
    have hB0 : 0 ∈ B ξ := (firstNBySlotOrder_spec 2 ξ).mem_iff_ncard_lt 0 |>.mpr
      ⟨hsurvive, by simp [hless], by simp [hless]⟩
    have hBfirst : firstSelectedSlot B ξ = 0 := by
      have hb : (B ξ).Nonempty := ⟨0, hB0⟩
      unfold firstSelectedSlot
      rw [dite_eq_left hb]
      exact Nat.eq_zero_of_le_zero (Finset.min'_le _ _ hB0)
    have hz : 0 ∈ firstOnlySelectedChild B ξ := by
      rw [firstOnlySelectedChild, Step.FiniteSelection.mem_filter]
      exact ⟨hB0, hBfirst.symm⟩
    exact (@Finset.mem_union ℕ (Classical.decEq ℕ)
      (firstOnlySelectedChild B ξ) (B.belowPotential realPotential M ξ) 0).2 (Or.inl hz)
  have hfirst : ∀ᵐ ξ ∂μ, firstSelectedSlot R ξ = 0 := by
    filter_upwards [hzero] with ξ hξ
    have hr : (R ξ).Nonempty := ⟨0, hξ⟩
    unfold firstSelectedSlot
    rw [dite_eq_left hr]
    exact Nat.eq_zero_of_le_zero (Finset.min'_le _ _ hξ)
  have hcut : ∀ᵐ ξ ∂μ, 2 ≤ (R ξ).card →
      value' ξ (firstSelectedSlot R ξ) ≤ M ∧ value' ξ (secondSelectedSlot R ξ) ≤ M := by
    filter_upwards [hordered] with ξ hξ
    intro hs
    have hbound := firstOrBelowPotential_edgePotentials_le_of_ordered B
      (firstNBySlotOrder_isBoundedBy 2) realPotential M ξ hξ hs
    have heq (j : ℕ) : ξ.potentialValue' realPotential j = value' ξ j := by
      simp [Step.potentialValue', Step.potentialAt?, realPotential, value']
    rw [← heq, ← heq]
    exact hbound
  have hnonemptyR : ∀ᵐ ξ ∂μ, (R ξ).Nonempty :=
    hzero.mono fun _ hξ => ⟨0, hξ⟩
  have hne : μ {ξ | (R ξ).Nonempty} = 1 := by
    have heq : {ξ | (R ξ).Nonempty} =ᵐ[μ] Set.univ := by
      filter_upwards [hnonemptyR] with ξ hξ
      simp [hξ]
    rw [measure_congr heq, measure_univ]
  obtain ⟨lam, hlam, hA, hm, hfin⟩ :=
    exists_splitWaitingDisplacement_exponentialMoment L hexp R hR hne hp
  have hfinite := selectedPopulationSplitCompletion_ae_finite_of_nonempty_and_split_pos
    μ R hR hne (splitBy_measurable R hR) hp
  have hall : ∀ᵐ ω ∂offspringFieldLaw μ, ∀ u,
      (R (ω u)).Nonempty ∧ firstSelectedSlot R (ω u) = 0 ∧
        (2 ≤ (R (ω u)).card → value' (ω u) (firstSelectedSlot R (ω u)) ≤ M ∧
        value' (ω u) (secondSelectedSlot R (ω u)) ≤ M) := by
    apply ae_all_iff.2
    intro u
    have hmeas : Measurable (fun ω : Mark ℕ (Step ℕ ℝ) => ω u) := measurable_pi_apply u
    have hallμ : ∀ᵐ ξ ∂μ, (R ξ).Nonempty ∧ firstSelectedSlot R ξ = 0 ∧
        (2 ≤ (R ξ).card → value' ξ (firstSelectedSlot R ξ) ≤ M ∧
          value' ξ (secondSelectedSlot R ξ) ≤ M) := by
      filter_upwards [hnonemptyR, hfirst, hcut] with ξ h₁ h₂ h₃
      exact ⟨h₁, h₂, h₃⟩
    exact ae_of_ae_map hmeas.aemeasurable (by rwa [offspringFieldLaw_coordinate μ u])
  refine ⟨lam, hlam, hne, hA, hfin, ?_⟩
  intro lower upper duration x K G
  have htail := measure_firstSuccessfulSplitCycle_partialSum_ge_le
    μ R growth hR hgrowth hfinite (splitWaitingDisplacement R)
    (splitWaitingDisplacement_measurable R hR) lower upper duration lam x hlam K
  dsimp only at htail
  rw [hm] at htail
  refine (mul_le_mul_of_nonneg_left (measure_mono_ae ?_) zero_le).trans htail
  filter_upwards [hall] with ω hω
  rintro ⟨k, hk, hsucc, hbefore, hpos⟩
  refine ⟨k, hk, hsucc, hbefore, ?_⟩
  have hkm : (k : ℝ) * M ≤ ((K - 1 : ℕ) : ℝ) * M :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast (show k ≤ K - 1 by omega)) hM
  obtain ⟨hparent, hroot⟩ := trialPositions_le R G M hM k ω hω
  rcases hpos with hp | hv
  · linarith
  · have hkm' : ((k + 1 : ℕ) : ℝ) * M ≤ (K : ℝ) * M :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.succ_le_of_lt hk)) hM
    linarith

attribute [local instance] Classical.propDecidable

/-- The entrance root of the first successful trial, restricted to the
first $K$ trials, has positive mean at most the stopped positive waiting
sum plus $KM$. This is the entrance-position term in Wang Yiyang,
Theorem 1.2. -/
lemma lintegral_firstSuccessfulTrial_root_positive_le
    {ι X E : Type*} [Countable ι] [MeasurableSpace X] [MeasurableSpace E]
    (L : StepLaw ι ℕ X) [IsProbabilityMeasure L.raw]
    (hboundary : HasBoundaryNormalization L.potential L.raw) (hfirst : HasLeftmostFirstMoment L)
    (R : Step.FiniteSelection ℕ ℝ) (hR : Measurable R.select)
    (hne : L.sortedPotentialImage {ξ | (R ξ).Nonempty} = 1)
    (hp : 0 < L.sortedPotentialImage (splitBy R))
    (G : Mark ℕ (Step ℕ ℝ) → E) (hG : Measurable G)
    (success : Set E) (hsuccess : MeasurableSet success)
    (hprob : 0 < (offspringFieldLaw L.sortedPotentialImage).real (G ⁻¹' success))
    (M : ℝ) (hM : 0 ≤ M) (K : ℕ)
    (hmarks : ∀ᵐ ω ∂offspringFieldLaw L.sortedPotentialImage, ∀ u,
      (R (ω u)).Nonempty ∧ firstSelectedSlot R (ω u) = 0 ∧
        (2 ≤ (R (ω u)).card → value' (ω u) (firstSelectedSlot R (ω u)) ≤ M ∧
          value' (ω u) (secondSelectedSlot R (ω u)) ≤ M)) :
    let μ := L.sortedPotentialImage
    let ν := offspringFieldLaw μ
    let D := splitCycle R (splitWaitingDisplacement R) G
    (∫⁻ ω, ⨆ k : Fin K,
      (if (D k.val ω).2 ∈ success ∧ ∀ j < k.val, (D j ω).2 ∉ success
        then ENNReal.ofReal (max (Spine.pathPotential realPotential ω (trialGrowthRoot R k.val ω)) 0)
        else 0) ∂ν) ≤
      ENNReal.ofReal (((∫ ξ, max (value' ξ 0) 0 ∂μ) / μ.real (splitBy R)) /
        ν.real (G ⁻¹' success) + K * M) := by
  classical
  intro μ ν D
  let B : Set (ℝ × E) := Prod.snd ⁻¹' success
  let Y : ℝ × E → ℝ := fun z => max z.1 0
  let Z (ω : Mark ℕ (Step ℕ ℝ)) := ∑' j, geometricPrefixRewardTerm D B Y j ω
  have hpos : ∀ ω, 0 ≤ Z ω := by
    intro ω
    apply tsum_nonneg
    intro j
    unfold geometricPrefixRewardTerm
    apply mul_nonneg (le_max_right _ _)
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) ω
  have hfinite := selectedPopulationSplitCompletion_ae_finite_of_nonempty_and_split_pos
    μ R hR hne (splitBy_measurable R hR) hp
  obtain ⟨hX, _, hXpos⟩ := splitWaitingDisplacement_firstMoment L hboundary hfirst R hR hne hp
  obtain ⟨hZi, hZmean⟩ := integral_splitCycle_positiveDisplacement_through_success
    μ R hR hfinite (splitWaitingDisplacement R) (splitWaitingDisplacement_measurable R hR)
    hX G hG success hsuccess hprob
  change Integrable Z ν at hZi
  change (∫ ω, Z ω ∂ν) = _ at hZmean
  have hZbound : (∫ ω, Z ω ∂ν) ≤
      ((∫ ξ, max (value' ξ 0) 0 ∂μ) / μ.real (splitBy R)) / ν.real (G ⁻¹' success) := by
    rw [hZmean]
    exact div_le_div_of_nonneg_right hXpos hprob.le
  have hpoint : ∀ᵐ ω ∂ν, (⨆ k : Fin K,
      (if (D k.val ω).2 ∈ success ∧ ∀ j < k.val, (D j ω).2 ∉ success
        then ENNReal.ofReal (max (Spine.pathPotential realPotential ω (trialGrowthRoot R k.val ω)) 0)
        else 0)) ≤ ENNReal.ofReal (Z ω + K * M) := by
    filter_upwards [hmarks] with ω hω
    apply iSup_le
    intro k
    split_ifs with hk
    swap
    · exact bot_le
    have hsum : Z ω = ∑ j ∈ Finset.range (k.val + 1), Y (D j ω) := by
      unfold Z
      rw [tsum_eq_sum (s := Finset.range (k.val + 1))]
      · apply Finset.sum_congr rfl
        intro j hj
        have hj' := Finset.mem_range.mp hj
        have hprefix : ω ∈ geometricFailurePrefix D B j := by
          simp only [geometricFailurePrefix, Set.mem_iInter, Set.mem_preimage, Finset.mem_range]
          exact fun i hi => hk.2 i (by omega)
        simp [geometricPrefixRewardTerm, hprefix]
      · intro j hj
        have hprefix : ω ∉ geometricFailurePrefix D B j := by
          simp only [geometricFailurePrefix, Set.mem_iInter, Set.mem_preimage, Finset.mem_range]
          intro h
          exact h k.val (Nat.lt_of_succ_le (Nat.le_of_not_gt (Finset.mem_range.not.mp hj))) hk.1
        simp [geometricPrefixRewardTerm, hprefix]
    have hr := (trialPositions_le R G M hM k.val ω hω).2
    have hwaiting : (∑ j ∈ Finset.range (k.val + 1), (D j ω).1) ≤ Z ω := by
      rw [hsum]
      exact Finset.sum_le_sum fun j _ => le_max_left _ _
    apply ENNReal.ofReal_le_ofReal
    apply max_le
    · exact hr.trans (add_le_add hwaiting
        (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.succ_le_of_lt k.isLt) hM))
    · exact add_nonneg (hpos ω) (mul_nonneg (Nat.cast_nonneg K) hM)
  apply (lintegral_mono_ae hpoint).trans
  have hi : Integrable (fun ω => Z ω + K * M) ν := hZi.add (integrable_const _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun ω => add_nonneg (hpos ω) (by positivity)),
    integral_add hZi (integrable_const (K * M)), integral_const, probReal_univ, one_smul]
  exact ENNReal.ofReal_le_ofReal (add_le_add hZbound le_rfl)

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas
