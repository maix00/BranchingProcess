/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Spine.Path.SecondMoment.Basic

/-!
# Prefix conditioning for MRCA pair contributions

This file lifts the root split-pair identity to a generation-measurable
ancestral prefix.  It is the conditioning interface used when a tube path is
split at a positive-depth MRCA.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.RandomWalk

private lemma pathGenerationChildObservable_joint_measurable
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (F : (Fin (n + 2) → ℝ) → ℝ≥0∞)
    (hF : Measurable F) (i : ℕ) :
    Measurable (fun p : ℝ × (Step ℕ X × StepField ℕ X) =>
      pathGenerationChildObservable φ n F p.1 i p.2.1 p.2.2) := by
  classical
  let localInitial : ℝ × (Step ℕ X × StepField ℕ X) → ℝ × StepField ℕ X :=
    fun p => (p.1 + p.2.1.potentialValue' φ i, p.2.2)
  have hlocalInitial : Measurable localInitial := by
    exact (measurable_fst.add
      ((Step.potentialValue'_measurable φ i).comp
        (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_snd)
  have hterm (v : TreeNode ℕ) :
      Measurable (fun p : ℝ × (Step ℕ X × StepField ℕ X) =>
        pathGenerationTerm φ n
          (fun tail => F (prependHistory p.1 tail))
          (localInitial p).1 v p.2.2) := by
    unfold pathGenerationTerm
    have hlocalHistory :
        Measurable (fun p : ℝ × (Step ℕ X × StepField ℕ X) =>
          pathHistory φ n (localInitial p).1 (localInitial p).2 v) := by
      exact (pathHistory_joint_measurable φ n v).comp
        (hlocalInitial.comp measurable_id)
    have hfullHistory :
        Measurable (fun p : ℝ × (Step ℕ X × StepField ℕ X) =>
          prependHistory p.1 (pathHistory φ n (localInitial p).1
            (localInitial p).2 v)) := by
      exact (prependHistory_joint_measurable n).comp
        (measurable_fst.prodMk hlocalHistory)
    have htest : Measurable (fun p : ℝ × (Step ℕ X × StepField ℕ X) =>
        F (prependHistory p.1
          (pathHistory φ n (localInitial p).1 (localInitial p).2 v))) :=
      hF.comp hfullHistory
    by_cases hv : v.length = n
    · simp only [Set.indicator_apply, hv, true_and]
      have hη : Measurable
          (fun p : ℝ × (Step ℕ X × StepField ℕ X) => p.2.2) :=
        measurable_snd.comp measurable_snd
      exact htest.ite
        ((measurableSet_surviveAlong (X := X) [] v).preimage hη)
        measurable_const
    · simp [hv, pathGenerationTerm]
  have hcount :
      Measurable (fun p : ℝ × (Step ℕ X × StepField ℕ X) =>
        ∑' v : TreeNode ℕ,
          pathGenerationTerm φ n
            (fun tail => F (prependHistory p.1 tail))
            (localInitial p).1 v p.2.2) := by
    apply Measurable.tsum
    intro v
    exact hterm v
  unfold pathGenerationChildObservable survivingPotentialTest
  simp only [localInitial]
  apply hcount.ite
  exact (survive_measurableSet i).preimage
    (measurable_fst.comp measurable_snd)
  exact measurable_const

private lemma pathGenerationChildMeanOffDiagonal_joint_measurable
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (F : (Fin (n + 2) → ℝ) → ℝ≥0∞)
    (hF : Measurable F) :
    Measurable (fun p : ℝ × Step ℕ X =>
      pathGenerationChildMeanOffDiagonal φ μ n F p.1 p.2) := by
  classical
  let childKernel (i : ℕ) (p : ℝ × Step ℕ X)
      (η : StepField ℕ X) : ℝ≥0∞ :=
    pathGenerationChildObservable φ n F p.1 i p.2 η
  let childMean (i : ℕ) (p : ℝ × Step ℕ X) : ℝ≥0∞ :=
    ∫⁻ η, childKernel i p η ∂stepFieldLaw μ
  have hchildMean (i : ℕ) : Measurable (childMean i) := by
    have hkernel : Measurable (Function.uncurry (childKernel i)) := by
      change Measurable
        (fun p : (ℝ × Step ℕ X) × StepField ℕ X =>
          pathGenerationChildObservable φ n F p.1.1 i p.1.2 p.2)
      exact (pathGenerationChildObservable_joint_measurable φ n F hF i).comp
        ((measurable_fst.comp measurable_fst).prodMk
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    apply Measurable.lintegral_prod_right
    exact hkernel
  have hterm (i j : ℕ) : Measurable (fun p : ℝ × Step ℕ X =>
      if i ≠ j then childMean i p * childMean j p else 0) := by
    by_cases hij : i ≠ j
    · simp only [if_pos hij]
      exact (hchildMean i).mul (hchildMean j)
    · have hEq : i = j := by
        by_contra hne
        exact hij hne
      simp [hEq]
  change Measurable (fun p : ℝ × Step ℕ X =>
    ∑' i : ℕ, ∑' j : ℕ,
      if i ≠ j then childMean i p * childMean j p else 0)
  apply Measurable.tsum
  intro i
  apply Measurable.tsum
  intro j
  exact hterm i j

private lemma pathGenerationRootMRCAContribution_joint_measurable
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ)
    (F : (Fin (n + 2) → ℝ) → ℝ≥0∞) (hF : Measurable F) :
    Measurable (fun p : ℝ × StepField ℕ X =>
      pathGenerationMRCAContribution φ 0 (n + 1) F p.1 p.2) := by
  classical
  let child (i : ℕ) : ℝ × StepField ℕ X → ℝ≥0∞ := fun p =>
    pathGenerationChildObservable φ n F p.1 i (p.2 [])
      (subtreeStepField [i] p.2)
  have hchild (i : ℕ) : Measurable (child i) := by
    change Measurable ((fun p : ℝ × (Step ℕ X × StepField ℕ X) =>
      pathGenerationChildObservable φ n F p.1 i p.2.1 p.2.2) ∘
        (fun p : ℝ × StepField ℕ X =>
          (p.1, (p.2 [], subtreeStepField [i] p.2))))
    have hchildField : Measurable
        (fun p : ℝ × StepField ℕ X =>
          (p.2 [], subtreeStepField [i] p.2)) := by
      exact (((measurable_pi_apply ([] : TreeNode ℕ) :
        Measurable (fun ω : StepField ℕ X => ω [] )).comp measurable_snd).prodMk
        ((subtreeStepField_measurable [i]).comp measurable_snd))
    exact (pathGenerationChildObservable_joint_measurable φ n F hF i).comp
      (measurable_fst.prodMk hchildField)
  have hterm (i j : ℕ) : Measurable (fun p : ℝ × StepField ℕ X =>
      if i ≠ j then child i p * child j p else 0) := by
    by_cases hij : i ≠ j
    · simp only [if_pos hij]
      exact (hchild i).mul (hchild j)
    · have hEq : i = j := by
        by_contra hne
        exact hij hne
      simp [hEq]
  have hsum : Measurable (fun p : ℝ × StepField ℕ X =>
      ∑' i : ℕ, ∑' j : ℕ,
        if i ≠ j then child i p * child j p else 0) := by
    apply Measurable.tsum
    intro i
    apply Measurable.tsum
    intro j
    exact hterm i j
  have hformula (p : ℝ × StepField ℕ X) :
      pathGenerationMRCAContribution φ 0 (n + 1) F p.1 p.2 =
        ∑' i : ℕ, ∑' j : ℕ,
          if i ≠ j then child i p * child j p else 0 := by
    simp [pathGenerationMRCAContribution, child]
  rw [show (fun p : ℝ × StepField ℕ X =>
      pathGenerationMRCAContribution φ 0 (n + 1) F p.1 p.2) =
      (fun p => ∑' i : ℕ, ∑' j : ℕ,
        if i ≠ j then child i p * child j p else 0) by
        funext p
        exact hformula p]
  exact hsum

/-- Integrating the actual root-split path pairs below each generation-`m`
ancestor is equivalent to integrating their conditional continuation-pair
mean against that ancestor's reproduction mark. The prefix weight and
position may depend measurably on the entire generation-`m` history. -/
theorem lintegral_generationPrefixRootMRCAContribution_eq_childMeanOffDiagonal
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (m n : ℕ) (F : (Fin (n + 2) → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (A : TreeNode ℕ → StepField ℕ X → ℝ≥0∞)
    (position : TreeNode ℕ → StepField ℕ X → ℝ)
    (hAgen : ∀ u, Measurable[generationFiltration (M := Step ℕ X) m]
      (A u))
    (hA : ∀ u, Measurable (A u))
    (hpositionGen : ∀ u,
      Measurable[generationFiltration (M := Step ℕ X) m] (position u))
    (hposition : ∀ u, Measurable (position u))
    (hsupport : ∀ u, u.length ≠ m → A u = fun _ => 0) :
    (∫⁻ ω, ∑' u : TreeNode ℕ,
      A u ω * pathGenerationMRCAContribution φ 0 (n + 1) F
        (position u ω) (subtreeStepField u ω) ∂stepFieldLaw μ) =
      (∫⁻ ω, ∑' u : TreeNode ℕ,
        A u ω * pathGenerationChildMeanOffDiagonal φ μ n F
          (position u ω) (ω u) ∂stepFieldLaw μ) := by
  classical
  let g : ℝ → Step ℕ X → ℝ≥0∞ := fun x ξ =>
    pathGenerationChildMeanOffDiagonal φ μ n F x ξ
  have hg : Measurable (Function.uncurry g) := by
    change Measurable (fun p : ℝ × Step ℕ X =>
      pathGenerationChildMeanOffDiagonal φ μ n F p.1 p.2)
    exact pathGenerationChildMeanOffDiagonal_joint_measurable φ μ n F hF
  have hmean : Measurable (fun x : ℝ => ∫⁻ ξ, g x ξ ∂μ) :=
    Measurable.lintegral_prod_right hg
  have hrootJoint := pathGenerationRootMRCAContribution_joint_measurable
    φ n F hF
  have hfactor (u : TreeNode ℕ) :
      (∫⁻ ω, A u ω * pathGenerationMRCAContribution φ 0 (n + 1) F
        (position u ω) (subtreeStepField u ω) ∂stepFieldLaw μ) =
      (∫⁻ ω, A u ω * (∫⁻ ξ, g (position u ω) ξ ∂μ)
        ∂stepFieldLaw μ) := by
    by_cases hu : u.length = m
    · let state : StepField ℕ X → ℝ≥0∞ × ℝ :=
        fun ω => (A u ω, position u ω)
      let tail : StepField ℕ X → StepField ℕ X :=
        fun ω => subtreeStepField u ω
      let pair : StepField ℕ X → (ℝ≥0∞ × ℝ) × StepField ℕ X :=
        fun ω => (state ω, tail ω)
      let H : (ℝ≥0∞ × ℝ) × StepField ℕ X → ℝ≥0∞ := fun p =>
        p.1.1 * pathGenerationMRCAContribution φ 0 (n + 1) F p.1.2 p.2
      have hstateGen : Measurable[generationFiltration
          (M := Step ℕ X) u.length] state := by
        rw [hu]
        exact (hAgen u).prodMk (hpositionGen u)
      have hstate : Measurable state :=
        (hA u).prodMk (hposition u)
      have htail : Measurable tail := subtreeStepField_measurable u
      have hpair : Measurable pair := hstate.prodMk htail
      have hH : Measurable H := by
        have hcoeff : Measurable
            (fun p : (ℝ≥0∞ × ℝ) × StepField ℕ X => p.1.1) :=
          measurable_fst.comp measurable_fst
        have hposition : Measurable
            (fun p : (ℝ≥0∞ × ℝ) × StepField ℕ X => p.1.2) :=
          measurable_snd.comp measurable_fst
        have hfield : Measurable
            (fun p : (ℝ≥0∞ × ℝ) × StepField ℕ X => p.2) :=
          measurable_snd
        exact hcoeff.mul (hrootJoint.comp (hposition.prodMk hfield))
      have hind : IndepFun state tail (stepFieldLaw μ) := by
        rw [IndepFun_iff_Indep]
        exact indep_of_indep_of_le_left
          (generation_subtreeStepField_independent μ u) hstateGen.comap_le
      have hmeanState : Measurable (fun p : ℝ≥0∞ × ℝ =>
          p.1 * (∫⁻ ξ, g p.2 ξ ∂μ)) :=
        measurable_fst.mul (hmean.comp measurable_snd)
      have hpoint (s : ℝ≥0∞ × ℝ) :
          (∫⁻ η, H (s, η) ∂stepFieldLaw μ) =
            s.1 * (∫⁻ ξ, g s.2 ξ ∂μ) := by
        change (∫⁻ η, s.1 *
          pathGenerationMRCAContribution φ 0 (n + 1) F s.2 η
          ∂stepFieldLaw μ) = _
        have hrootMeas : Measurable
            (pathGenerationMRCAContribution φ 0 (n + 1) F s.2) :=
          hrootJoint.comp (measurable_const.prodMk measurable_id)
        rw [lintegral_const_mul _ hrootMeas]
        congr 1
        simpa [g] using
          lintegral_pathGenerationMRCAContribution_zero_eq_childMeanOffDiagonal
            φ μ n F hF s.2
      calc
        (∫⁻ ω, A u ω * pathGenerationMRCAContribution φ 0 (n + 1) F
            (position u ω) (subtreeStepField u ω) ∂stepFieldLaw μ) =
            ∫⁻ p, H p ∂(stepFieldLaw μ).map pair := by
              exact (lintegral_map hH hpair).symm
        _ = ∫⁻ p, H p ∂((stepFieldLaw μ).map state).prod
              ((stepFieldLaw μ).map tail) := by
              rw [hind.map_prod_eq_prod_map_map
                hstate.aemeasurable htail.aemeasurable]
        _ = ∫⁻ s, ∫⁻ η, H (s, η) ∂((stepFieldLaw μ).map tail)
              ∂(stepFieldLaw μ).map state :=
              lintegral_prod (μ := (stepFieldLaw μ).map state)
                (ν := (stepFieldLaw μ).map tail) H hH.aemeasurable
        _ = ∫⁻ s, s.1 * (∫⁻ ξ, g s.2 ξ ∂μ)
              ∂(stepFieldLaw μ).map state := by
              rw [subtreeStepField_law μ u]
              apply lintegral_congr
              exact hpoint
        _ = ∫⁻ ω, A u ω * (∫⁻ ξ, g (position u ω) ξ ∂μ)
              ∂stepFieldLaw μ :=
              lintegral_map hmeanState hstate
    · have hzero : A u = fun _ => 0 := hsupport u hu
      rw [hzero]
      simp
  have hleftTerm (u : TreeNode ℕ) :
      Measurable (fun ω : StepField ℕ X =>
        A u ω * pathGenerationMRCAContribution φ 0 (n + 1) F
          (position u ω) (subtreeStepField u ω)) := by
    exact (hA u).mul (hrootJoint.comp
      ((hposition u).prodMk (subtreeStepField_measurable u)))
  have hrightTerm (u : TreeNode ℕ) :
      Measurable (fun ω : StepField ℕ X =>
        A u ω * (∫⁻ ξ, g (position u ω) ξ ∂μ)) :=
    (hA u).mul (hmean.comp (hposition u))
  have hleftSum :
      (∫⁻ ω, ∑' u : TreeNode ℕ,
        A u ω * pathGenerationMRCAContribution φ 0 (n + 1) F
          (position u ω) (subtreeStepField u ω) ∂stepFieldLaw μ) =
        ∑' u : TreeNode ℕ,
          ∫⁻ ω, A u ω * pathGenerationMRCAContribution φ 0 (n + 1) F
            (position u ω) (subtreeStepField u ω) ∂stepFieldLaw μ := by
    rw [lintegral_tsum]
    intro u
    exact (hleftTerm u).aemeasurable
  have hrightSum :
      (∫⁻ ω, ∑' u : TreeNode ℕ,
        A u ω * (∫⁻ ξ, g (position u ω) ξ ∂μ)
        ∂stepFieldLaw μ) =
        ∑' u : TreeNode ℕ,
          ∫⁻ ω, A u ω * (∫⁻ ξ, g (position u ω) ξ ∂μ)
            ∂stepFieldLaw μ := by
    rw [lintegral_tsum]
    intro u
    exact (hrightTerm u).aemeasurable
  calc
    _ = ∑' u : TreeNode ℕ,
          ∫⁻ ω, A u ω * pathGenerationMRCAContribution φ 0 (n + 1) F
            (position u ω) (subtreeStepField u ω) ∂stepFieldLaw μ := hleftSum
    _ = ∑' u : TreeNode ℕ,
          ∫⁻ ω, A u ω * (∫⁻ ξ, g (position u ω) ξ ∂μ)
            ∂stepFieldLaw μ := by
          apply tsum_congr
          exact hfactor
    _ = ∫⁻ ω, ∑' u : TreeNode ℕ,
          A u ω * (∫⁻ ξ, g (position u ω) ξ ∂μ)
          ∂stepFieldLaw μ := hrightSum.symm
    _ = ∫⁻ ω, ∑' u : TreeNode ℕ,
          A u ω * g (position u ω) (ω u) ∂stepFieldLaw μ := by
          symm
          exact lintegral_generationPrefixParameterizedObservableSum_eq
            μ m A position g hAgen hA hpositionGen hposition hsupport hg
    _ = _ := by rfl

end ProbabilityTheory.BranchingRandomWalk.Spine
