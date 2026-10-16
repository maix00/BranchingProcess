/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Spine.Tube.MRCA.ActualContribution
import Probability.BranchingRandomWalk.Spine.Tube.SecondMoment.MultiGeneration

/-!
# Pair bounds for affine corridor path counts

This file sums the actual affine-corridor MRCA contributions over their
possible generations.  Each fixed-depth term retains the corridor condition
at the birth generation and is measurable before the finite sum is integrated.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.RandomWalk

private theorem pathGenerationMRCAContribution_zeroTest
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (x : ℝ) (ω : StepField ℕ X) :
    pathGenerationMRCAContribution φ 0 (n + 1)
      (fun _ => (0 : ℝ≥0∞)) x ω = 0 := by
  simp [pathGenerationMRCAContribution, pathGenerationChildObservable,
    survivingPotentialTest, Spine.pathGeneration, pathGenerationTerm]

private theorem pathGenerationChildObservable_congr_prependHistory
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ)
    (F G : (Fin (n + 2) → ℝ) → ℝ≥0∞) (x : ℝ)
    (hFG : ∀ tail : Fin (n + 1) → ℝ,
      F (prependHistory x tail) = G (prependHistory x tail))
    (i : ℕ) (ξ : Step ℕ X) (η : StepField ℕ X) :
    pathGenerationChildObservable φ n F x i ξ η =
      pathGenerationChildObservable φ n G x i ξ η := by
  have htest : (fun tail : Fin (n + 1) → ℝ => F (prependHistory x tail)) =
      fun tail => G (prependHistory x tail) := funext hFG
  unfold pathGenerationChildObservable
  rw [htest]

private theorem pathGenerationMRCAContribution_congr_prependHistory
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ)
    (F G : (Fin (n + 2) → ℝ) → ℝ≥0∞) (x : ℝ)
    (ω : StepField ℕ X)
    (hFG : ∀ tail : Fin (n + 1) → ℝ,
      F (prependHistory x tail) = G (prependHistory x tail)) :
    pathGenerationMRCAContribution φ 0 (n + 1) F x ω =
      pathGenerationMRCAContribution φ 0 (n + 1) G x ω := by
  simp only [pathGenerationMRCAContribution]
  apply tsum_congr
  intro i
  apply tsum_congr
  intro j
  by_cases hij : i ≠ j
  · simp only [if_pos hij]
    rw [pathGenerationChildObservable_congr_prependHistory
        φ n F G x hFG i (ω []) (subtreeStepField [i] ω)]
    rw [pathGenerationChildObservable_congr_prependHistory
        φ n F G x hFG j (ω []) (subtreeStepField [j] ω)]
  · simp [hij]

private theorem pathGenerationMRCAContribution_ifTest
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (F : (Fin (n + 2) → ℝ) → ℝ≥0∞)
    (p : Prop) [Decidable p] (x : ℝ) (ω : StepField ℕ X) :
    pathGenerationMRCAContribution φ 0 (n + 1)
      (fun h => if p then F h else 0) x ω =
        if p then pathGenerationMRCAContribution φ 0 (n + 1) F x ω else 0 := by
  by_cases hp : p
  · simp [hp]
  · simp [hp, pathGenerationMRCAContribution_zeroTest]

private theorem pathGenerationChildObservable_joint_measurable
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

private theorem pathGenerationRootMRCAContribution_joint_measurable
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

theorem pathGenerationMRCAContribution_affineCorridor_measurable
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (m n : ℕ) (initial lower drift width endpointUpper : ℝ) :
    Measurable (pathGenerationMRCAContribution φ m ((n + 1) + m)
      ((affineCorridorThrough (n + 1 + m) lower drift width endpointUpper).indicator
        (fun _ => (1 : ℝ≥0∞))) initial) := by
  classical
  let prefixCorridor := affineCorridorPrefix m lower drift width
  let continuationCorridor := affineCorridorThrough (n + 1)
    (lower + drift * (m : ℝ)) drift width endpointUpper
  let globalTest : (Fin (((n + 1) + m) + 1) → ℝ) → ℝ≥0∞ :=
    (affineCorridorThrough (n + 1 + m) lower drift width endpointUpper).indicator
      (fun _ => (1 : ℝ≥0∞))
  let prefixTest : (Fin (m + 1) → ℝ) → ℝ≥0∞ :=
    prefixCorridor.indicator (fun _ => (1 : ℝ≥0∞))
  let continuationTest : (Fin (n + 2) → ℝ) → ℝ≥0∞ :=
    continuationCorridor.indicator (fun _ => (1 : ℝ≥0∞))
  let A : TreeNode ℕ → StepField ℕ X → ℝ≥0∞ := fun u ω =>
    pathGenerationTerm φ m prefixTest initial u ω
  let position : TreeNode ℕ → StepField ℕ X → ℝ := fun u ω =>
    initial + pathPotential φ ω u
  have hprefix : Measurable prefixTest := by
    exact measurable_const.indicator
      (measurableSet_affineCorridorPrefix m lower drift width)
  have hcontinuation : Measurable continuationTest := by
    exact measurable_const.indicator
      (measurableSet_affineCorridorThrough (n + 1)
        (lower + drift * (m : ℝ)) drift width endpointUpper)
  have hrootJoint := pathGenerationRootMRCAContribution_joint_measurable
    φ n continuationTest hcontinuation
  have hA (u : TreeNode ℕ) : Measurable (A u) := by
    exact pathGenerationTerm_measurable φ m hprefix initial u
  have hposition (u : TreeNode ℕ) : Measurable (position u) := by
    change Measurable (fun ω : StepField ℕ X =>
      initial + pathPotential φ ω u)
    exact measurable_const.add (pathPotential_measurable φ [] u)
  have hterm (u : TreeNode ℕ) (hu : u.length = m) (ω : StepField ℕ X) :
      pathGenerationSurvivingPrefixMRCAContribution φ m n globalTest
        initial ω ⟨u, hu⟩ =
      A u ω * pathGenerationMRCAContribution φ 0 (n + 1) continuationTest
        (position u ω) (subtreeStepField u ω) := by
    let prefixHit : Prop := pathHistory φ m initial ω u ∈ prefixCorridor
    have hsplit (tail : Fin (n + 1) → ℝ) :
        pathGenerationPrefixTest φ m n globalTest initial ω u
            (prependHistory (position u ω) tail) =
          (if prefixHit then continuationTest
            (prependHistory (position u ω) tail) else 0) := by
      have htail :
          (prependHistory (position u ω) tail) ⟨0, by omega⟩ =
            pathHistory φ m initial ω u ⟨m, Nat.lt_succ_self m⟩ := by
        simp [position, pathHistory_last, hu]
      simpa [globalTest, prefixHit, prefixCorridor, continuationCorridor,
        continuationTest] using
        (pathGenerationPrefixTest_affineCorridorThrough φ m n initial lower
          drift width endpointUpper ω u hu
          (prependHistory (position u ω) tail) htail)
    have hlocal :
        pathGenerationPrefixMRCAContribution φ m n globalTest initial ω u =
          if prefixHit then
            pathGenerationMRCAContribution φ 0 (n + 1) continuationTest
              (position u ω) (subtreeStepField u ω)
          else 0 := by
      unfold pathGenerationPrefixMRCAContribution
      have hroot :
          pathGenerationMRCAContribution φ 0 (n + 1)
            (pathGenerationPrefixTest φ m n globalTest initial ω u)
            (initial + pathPotential φ ω u) (subtreeStepField u ω) =
          pathGenerationMRCAContribution φ 0 (n + 1)
            (fun tail => if prefixHit then continuationTest tail else 0)
            (initial + pathPotential φ ω u) (subtreeStepField u ω) := by
        apply pathGenerationMRCAContribution_congr_prependHistory
        intro tail
        simpa [position] using hsplit tail
      rw [hroot]
      simpa [position] using
        (pathGenerationMRCAContribution_ifTest φ n continuationTest
          prefixHit (initial + pathPotential φ ω u) (subtreeStepField u ω))
    by_cases hsurvive : surviveAlong ω [] u
    · simp [pathGenerationSurvivingPrefixMRCAContribution, hlocal, A,
        pathGenerationTerm, prefixTest, prefixCorridor, prefixHit, hu,
        hsurvive, Set.indicator_apply]
    · simp [pathGenerationSurvivingPrefixMRCAContribution, A,
        pathGenerationTerm, hu, hsurvive]
  have hprefixExpansion :
      (pathGenerationMRCAContribution φ m ((n + 1) + m) globalTest initial) =
        fun ω : StepField ℕ X =>
          ∑' u : {u : TreeNode ℕ // u.length = m},
            pathGenerationSurvivingPrefixMRCAContribution φ m n globalTest
              initial ω u := by
    funext ω
    exact pathGenerationMRCAContribution_eq_sum_prefix φ m n globalTest initial ω
  change Measurable
    (pathGenerationMRCAContribution φ m ((n + 1) + m) globalTest initial)
  rw [hprefixExpansion]
  apply Measurable.tsum
  intro u
  have hu : u.1.length = m := u.2
  rw [show (fun ω : StepField ℕ X =>
      pathGenerationSurvivingPrefixMRCAContribution φ m n globalTest
        initial ω u) =
    fun ω => A u.1 ω * pathGenerationMRCAContribution φ 0 (n + 1)
        continuationTest (position u.1 ω) (subtreeStepField u.1 ω) by
    funext ω
    exact hterm u.1 hu ω]
  exact (hA u.1).mul (hrootJoint.comp
    ((hposition u.1).prodMk (subtreeStepField_measurable u.1)))

/-- The expected number of ordered distinct successful address pairs in an
affine corridor is the sum of its actual MRCA contributions. Each summand
retains the corridor and survival indicators along the ancestor prefix. -/
theorem lintegral_pathGenerationDistinctAddressPairCount_affineCorridor_eq_sum_MRCA
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (N : ℕ) (initial lower drift width endpointUpper : ℝ) :
    (∫⁻ ω, pathGenerationDistinctAddressPairCount φ N
      ((affineCorridorThrough N lower drift width endpointUpper).indicator
        (fun _ => (1 : ℝ≥0∞))) initial ω ∂stepFieldLaw μ) =
      ∑ m : Fin N,
        affineTubeMRCAPairContribution φ μ m.val (N - m.val - 1)
          initial lower drift width endpointUpper := by
  classical
  let corridor := affineCorridorThrough N lower drift width endpointUpper
  let F : (Fin (N + 1) → ℝ) → ℝ≥0∞ :=
    corridor.indicator (fun _ => (1 : ℝ≥0∞))
  have hcorridor : MeasurableSet corridor :=
    measurableSet_affineCorridorThrough N lower drift width endpointUpper
  have hF : Measurable F := measurable_const.indicator hcorridor
  have hterminalUpper : ∀ history ∈ corridor,
      history ⟨N, Nat.lt_succ_self N⟩ ≤ endpointUpper := by
    intro history hhistory
    exact hhistory.2
  have hpairIntegral :=
    lintegral_pathGenerationOffDiagonalPairs_eq_distinctAddressPairCount
      φ μ hboundary N initial endpointUpper corridor hcorridor hterminalUpper
  have hdecomp (ω : StepField ℕ X) :
      pathGenerationOffDiagonalPairs φ N F initial ω =
        ∑ m : Fin N, pathGenerationMRCAContribution φ m.val N F initial ω := by
    simpa [F, corridor] using
      pathGenerationOffDiagonalPairs_eq_sum_mrcaContribution φ N F initial ω
  have hmeas (m : Fin N) : Measurable
      (pathGenerationMRCAContribution φ m.val N F initial) := by
    have hm : m.val < N := m.isLt
    let n := N - m.val - 1
    have hN : (n + 1) + m.val = N := by
      dsimp [n]
      omega
    have hNat : N - m.val - 1 + 1 + m.val = N := by omega
    have hmeas' := pathGenerationMRCAContribution_affineCorridor_measurable
      φ m.val n initial lower drift width endpointUpper
    dsimp [n] at hmeas'
    rw [hNat] at hmeas'
    simpa [F, corridor] using hmeas'
  have hsumIntegral :
      (∫⁻ ω, ∑ m : Fin N,
        pathGenerationMRCAContribution φ m.val N F initial ω
        ∂stepFieldLaw μ) =
        ∑ m : Fin N, ∫⁻ ω,
          pathGenerationMRCAContribution φ m.val N F initial ω
          ∂stepFieldLaw μ := by
    simpa using
      (lintegral_finsetSum' Finset.univ
        (f := fun m ω =>
          pathGenerationMRCAContribution φ m.val N F initial ω)
        (fun m _ => (hmeas m).aemeasurable))
  have hterms :
      (∫⁻ ω, pathGenerationOffDiagonalPairs φ N F initial ω
        ∂stepFieldLaw μ) =
        ∑ m : Fin N,
          affineTubeMRCAPairContribution φ μ m.val (N - m.val - 1)
            initial lower drift width endpointUpper := by
    calc
      _ = ∫⁻ ω, ∑ m : Fin N,
            pathGenerationMRCAContribution φ m.val N F initial ω
            ∂stepFieldLaw μ := by
          apply lintegral_congr
          intro ω
          exact hdecomp ω
      _ = ∑ m : Fin N, ∫⁻ ω,
            pathGenerationMRCAContribution φ m.val N F initial ω
            ∂stepFieldLaw μ := hsumIntegral
      _ = ∑ m : Fin N,
            affineTubeMRCAPairContribution φ μ m.val
              (N - m.val - 1) initial lower drift width endpointUpper := by
          apply Finset.sum_congr rfl
          intro m hm
          let n := N - m.val - 1
          have hNat : N - m.val - 1 + 1 + m.val = N := by omega
          have hactual :=
            lintegral_pathGenerationMRCAContribution_affineCorridor_eq
              φ μ m.val n initial lower drift width endpointUpper
          dsimp [n] at hactual
          rw [hNat] at hactual
          simpa [F, corridor] using hactual
  calc
    _ = ∫⁻ ω, pathGenerationOffDiagonalPairs φ N F initial ω
        ∂stepFieldLaw μ := hpairIntegral.symm
    _ = _ := hterms

/-- The expected ordered distinct-pair count inside an affine corridor is
bounded by the drawdown sum of its actual MRCA contributions. -/
theorem lintegral_pathGenerationDistinctAddressPairCount_affineCorridor_le_of_drawdown
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (N : ℕ) (initial lower drift width endpointUpper : ℝ)
    (hdrift : 0 ≤ drift) (q : ℕ → ℝ≥0∞)
    (hdrawdown : ∀ n,
      (tiltedIncrementFieldLaw φ μ)
        (ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
          n width (width + drift * (n : ℝ))) ≤ q n) :
    (∫⁻ ω, pathGenerationDistinctAddressPairCount φ N
      ((affineCorridorThrough N lower drift width endpointUpper).indicator
        (fun _ => (1 : ℝ≥0∞))) initial ω ∂stepFieldLaw μ) ≤
      ∑ m : Fin N,
        ENNReal.ofReal (Real.exp (-(2 * initial))) *
          (ENNReal.ofReal (Real.exp (2 * endpointUpper)) *
            q (N - m.val - 1) ^ 2) *
          (∫⁻ ξ, crossChildWeight φ ξ ∂μ) *
          (ENNReal.ofReal
            (Real.exp (initial - (lower + drift * (m.val : ℝ)))) *
            (tiltedIncrementFieldLaw φ μ)
              {increment | ProbabilityTheory.RandomWalk.history m.val initial increment ∈
                affineCorridorPrefix m.val lower drift width}) := by
  have hterms :=
    lintegral_pathGenerationDistinctAddressPairCount_affineCorridor_eq_sum_MRCA
      φ μ hboundary N initial lower drift width endpointUpper
  have hdrawdownSum :=
    sum_affineTubeMRCAPairContribution_le_of_drawdown
      φ μ hboundary N initial lower drift width endpointUpper hdrift q hdrawdown
  calc
    _ = ∑ m : Fin N,
          affineTubeMRCAPairContribution φ μ m.val (N - m.val - 1)
            initial lower drift width endpointUpper := hterms
    _ ≤ _ := hdrawdownSum

end ProbabilityTheory.BranchingRandomWalk.Spine
