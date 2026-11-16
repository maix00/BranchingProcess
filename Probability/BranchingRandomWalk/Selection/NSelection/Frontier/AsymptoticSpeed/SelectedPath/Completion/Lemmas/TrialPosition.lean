/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.FailureDisplacement
import Probability.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas.TrialIndependence
import MeasureTheory.BranchingWalk.Step.Selection.Potential

/-!
# First successful trial's split position

## Internal proof declarations

* `trialSplitParent` gives the address $\rho_k$ of the split parent in the
  pre-sampled tree, with the Lean index starting at zero.
* `trialGrowthRoot` gives the first child $v_k$ of that split parent.
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
    (M : ℝ) (hM : 0 ≤ M) (lower upper duration : ℕ) :
    let μ := L.sortedPotentialImage
    let R := firstOrBelowPotential (firstNBySlotOrder (α := ℕ) (X := ℝ) 2) realPotential M
    let G := growthTrialSuccess growth lower upper duration
    0 < μ (splitBy R) →
    ∃ lam > (0 : ℝ), let A := ∫⁻ ξ, ENNReal.ofReal (Real.exp (lam * value' ξ 0)) *
          (splitBy R)ᶜ.indicator (fun _ => (1 : ℝ≥0∞)) ξ ∂μ
      let m := μ (splitBy R) / (1 - A)
      A < 1 ∧ m < ∞ ∧ ∀ (x : ℝ) (K : ℕ),
        ENNReal.ofReal (Real.exp (lam * x)) *
          offspringFieldLaw μ {ω | ∃ k < K,
            (splitCycle R (splitWaitingDisplacement R) G k ω).2 ∧
            (∀ j < k, ¬ (splitCycle R (splitWaitingDisplacement R) G j ω).2) ∧
            (x + ((K - 1 : ℕ) : ℝ) * M ≤
              Spine.pathPotential realPotential ω (trialSplitParent R k ω) ∨
              x + (K : ℝ) * M ≤ Spine.pathPotential realPotential ω (trialGrowthRoot R k ω))} ≤
          ∑ k ∈ Finset.range K, m ^ (k + 1) := by
  intro μ R G hp
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
  refine ⟨lam, hlam, hA, hfin, ?_⟩
  intro x K
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

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas
