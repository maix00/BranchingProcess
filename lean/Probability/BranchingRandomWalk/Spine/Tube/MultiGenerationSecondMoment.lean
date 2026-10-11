/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Spine.Tube.RightTailOneGeneration
import Probability.BranchingRandomWalk.Spine.Tube.IndependentRootCorridor

/-!
# Multi-generation pair decomposition for corridor path counts

The one-generation second-moment recursion keeps a diagonal child-subtree
square.  This file iterates that recursion to all generations.  For a
zero-one path test, the diagonal is exactly the first moment, and the
remainder consists of ordered pairs of distinct successful paths, split at
their most recent common ancestor.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk

/-- The ordered distinct-pair remainder of a generation path count.  At the
first generation it is the sum of the remainders inside each surviving child
subtree and the ordered pairs that split between distinct first-generation
children. -/
noncomputable def pathGenerationOffDiagonalPairs
    {X : Type*} [MeasurableSpace X] (φ : Potential X) :
    (n : ℕ) → ((Fin (n + 1) → ℝ) → ℝ≥0∞) →
      ℝ → StepField ℕ X → ℝ≥0∞
  | 0, _, _, _ => 0
  | n + 1, F, x, ω =>
      (∑' i : ℕ, survivingPotentialTest φ
        (fun y => pathGenerationOffDiagonalPairs φ n
          (fun tail => F (prependHistory x tail)) (x + y)
          (subtreeStepField [i] ω)) (ω []) i) +
      (∑' i : ℕ, ∑' j : ℕ, if i ≠ j then
        (survivingPotentialTest φ
          (fun y => pathGeneration φ n
            (fun tail => F (prependHistory x tail)) (x + y)
            (subtreeStepField [i] ω)) (ω []) i) *
        (survivingPotentialTest φ
          (fun y => pathGeneration φ n
            (fun tail => F (prependHistory x tail)) (x + y)
            (subtreeStepField [j] ω)) (ω []) j)
        else 0)

/-- Ordered successful path pairs whose most recent common ancestor is at the
specified generation. `total` is the generation of the two endpoints; the
recursive case passes to one child subtree and slices the path test by its
known first coordinate. -/
noncomputable def pathGenerationMRCAContribution
    {X : Type*} [MeasurableSpace X] (φ : Potential X) :
    (depth total : ℕ) → ((Fin (total + 1) → ℝ) → ℝ≥0∞) →
      ℝ → StepField ℕ X → ℝ≥0∞
  | _, 0, _, _, _ => 0
  | 0, n + 1, F, x, ω =>
      ∑' i : ℕ, ∑' j : ℕ, if i ≠ j then
        pathGenerationChildObservable φ n F x i (ω [])
          (subtreeStepField [i] ω) *
        pathGenerationChildObservable φ n F x j (ω [])
          (subtreeStepField [j] ω)
        else 0
  | d + 1, n + 1, F, x, ω =>
      ∑' i : ℕ, survivingPotentialTest φ
        (fun y => pathGenerationMRCAContribution φ d n
          (fun tail => F (prependHistory x tail)) (x + y)
          (subtreeStepField [i] ω)) (ω []) i
termination_by depth _ _ _ _ => depth

/-- For a zero-one test, the square of the number of successful generation-n
paths is its diagonal contribution plus the ordered distinct-pair remainder.
This identity closes the diagonal branch of the MRCAs recursion at every
depth, rather than leaving a squared subtree observable behind. -/
theorem pathGeneration_sq_eq_self_add_offDiagonalPairs
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (F : (Fin (n + 1) → ℝ) → ℝ≥0∞)
    (hF : ∀ history, F history = 0 ∨ F history = 1)
    (x : ℝ) (ω : StepField ℕ X) :
    (pathGeneration φ n F x ω) ^ 2 =
      pathGeneration φ n F x ω +
        pathGenerationOffDiagonalPairs φ n F x ω := by
  classical
  induction n generalizing x ω with
  | zero =>
      rw [pathGeneration_zero, pathGenerationOffDiagonalPairs]
      rcases hF (fun _ => x) with hzero | hone
      · simp [hzero]
      · simp [hone]
  | succ n ih =>
      let tailTest : (Fin (n + 1) → ℝ) → ℝ≥0∞ :=
        fun tail => F (prependHistory x tail)
      have htailTest : ∀ tail, tailTest tail = 0 ∨ tailTest tail = 1 := by
        intro tail
        exact hF (prependHistory x tail)
      let childCount : ℕ → ℝ≥0∞ := fun i =>
        pathGenerationChildObservable φ n F x i (ω [])
          (subtreeStepField [i] ω)
      let childPairs : ℕ → ℝ≥0∞ := fun i =>
        survivingPotentialTest φ
          (fun y => pathGenerationOffDiagonalPairs φ n tailTest
            (x + y) (subtreeStepField [i] ω)) (ω []) i
      have hchild (i : ℕ) : childCount i ^ 2 = childCount i + childPairs i := by
        by_cases hi : survive (ω []) i
        · have hsub := ih tailTest htailTest
            (x + (ω []).potentialValue' φ i) (subtreeStepField [i] ω)
          simpa [childCount, childPairs, pathGenerationChildObservable,
            survivingPotentialTest, hi, tailTest] using hsub
        · simp [childCount, childPairs, pathGenerationChildObservable,
            survivingPotentialTest, hi]
      have hdiag : (∑' i : ℕ, childCount i ^ 2) =
          (∑' i : ℕ, childCount i) + (∑' i : ℕ, childPairs i) := by
        calc
          (∑' i : ℕ, childCount i ^ 2) =
              ∑' i : ℕ, (childCount i + childPairs i) := by
                apply tsum_congr
                intro i
                exact hchild i
          _ = (∑' i : ℕ, childCount i) +
              (∑' i : ℕ, childPairs i) := ENNReal.tsum_add
      have hsplit := pathGeneration_succ_sq_eq_diagonal_add_offDiagonal
        φ n F x ω
      change (pathGeneration φ (n + 1) F x ω) ^ 2 = _ at hsplit
      calc
        (pathGeneration φ (n + 1) F x ω) ^ 2 =
            (∑' i : ℕ, childCount i ^ 2) +
              (∑' i : ℕ, ∑' j : ℕ, if i ≠ j then
                childCount i * childCount j else 0) := by
              simpa [childCount, pathGenerationChildObservable] using hsplit
        _ = ((∑' i : ℕ, childCount i) +
              (∑' i : ℕ, childPairs i)) +
              (∑' i : ℕ, ∑' j : ℕ, if i ≠ j then
                childCount i * childCount j else 0) := by rw [hdiag]
        _ = pathGeneration φ (n + 1) F x ω +
              pathGenerationOffDiagonalPairs φ (n + 1) F x ω := by
              rw [pathGeneration_succ]
              simp only [pathGenerationOffDiagonalPairs, childPairs,
                childCount, tailTest, pathGenerationChildObservable]
              ac_rfl

/-- The recursive ordered-pair remainder is exactly the finite sum over
possible generations of the most recent common ancestor. -/
theorem pathGenerationOffDiagonalPairs_eq_sum_mrcaContribution
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (F : (Fin (n + 1) → ℝ) → ℝ≥0∞)
    (x : ℝ) (ω : StepField ℕ X) :
    pathGenerationOffDiagonalPairs φ n F x ω =
      ∑ depth : Fin n,
        pathGenerationMRCAContribution φ depth.val n F x ω := by
  classical
  induction n generalizing x ω with
  | zero => simp [pathGenerationOffDiagonalPairs]
  | succ n ih =>
      rw [pathGenerationOffDiagonalPairs, Fin.sum_univ_succ]
      let tailTest : (Fin (n + 1) → ℝ) → ℝ≥0∞ :=
        fun tail => F (prependHistory x tail)
      have hchild (i : ℕ) :
          survivingPotentialTest φ
              (fun y => pathGenerationOffDiagonalPairs φ n tailTest
                (x + y) (subtreeStepField [i] ω)) (ω []) i =
            ∑ depth : Fin n, survivingPotentialTest φ
              (fun y => pathGenerationMRCAContribution φ depth.val n
                tailTest (x + y) (subtreeStepField [i] ω)) (ω []) i := by
        unfold survivingPotentialTest
        by_cases hi : survive (ω []) i
        · simp [hi, ih]
        · simp [hi]
      have hchildren :
          (∑' i : ℕ, survivingPotentialTest φ
              (fun y => pathGenerationOffDiagonalPairs φ n tailTest
                (x + y) (subtreeStepField [i] ω)) (ω []) i) =
            ∑ depth : Fin n, ∑' i : ℕ, survivingPotentialTest φ
              (fun y => pathGenerationMRCAContribution φ depth.val n
                tailTest (x + y) (subtreeStepField [i] ω)) (ω []) i := by
        calc
          _ = ∑' i : ℕ, ∑ depth : Fin n, survivingPotentialTest φ
              (fun y => pathGenerationMRCAContribution φ depth.val n
                tailTest (x + y) (subtreeStepField [i] ω)) (ω []) i := by
                apply tsum_congr
                exact hchild
          _ = ∑' i : ℕ, ∑' depth : Fin n, survivingPotentialTest φ
              (fun y => pathGenerationMRCAContribution φ depth.val n
                tailTest (x + y) (subtreeStepField [i] ω)) (ω []) i := by
                simp
          _ = ∑' depth : Fin n, ∑' i : ℕ, survivingPotentialTest φ
              (fun y => pathGenerationMRCAContribution φ depth.val n
                tailTest (x + y) (subtreeStepField [i] ω)) (ω []) i :=
                ENNReal.tsum_comm
          _ = _ := by rw [tsum_fintype]
      rw [hchildren]
      simp [pathGenerationMRCAContribution, pathGenerationChildObservable,
        tailTest, add_comm]

/-- The same diagonal closure for a measurable or nonmeasurable path
corridor, represented by its indicator. -/
theorem pathGeneration_indicator_sq_eq_self_add_offDiagonalPairs
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (corridor : Set (Fin (n + 1) → ℝ))
    (x : ℝ) (ω : StepField ℕ X) :
    (pathGeneration φ n (corridor.indicator (fun _ => (1 : ℝ≥0∞)))
      x ω) ^ 2 =
      pathGeneration φ n (corridor.indicator (fun _ => (1 : ℝ≥0∞)))
        x ω +
      pathGenerationOffDiagonalPairs φ n
        (corridor.indicator (fun _ => (1 : ℝ≥0∞))) x ω := by
  apply pathGeneration_sq_eq_self_add_offDiagonalPairs
  intro history
  by_cases h : history ∈ corridor <;> simp [h]

/-- The ordered pairs of distinct generation-`n` addresses that both satisfy
the path test. Unlike the recursive MRCA remainder above, this presentation
is directly measurable and can be integrated as the off-diagonal term in a
second-moment estimate. -/
noncomputable def pathGenerationDistinctAddressPairCount
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (F : (Fin (n + 1) → ℝ) → ℝ≥0∞)
    (x : ℝ) (ω : StepField ℕ X) : ℝ≥0∞ :=
  ∑' p : TreeNode ℕ × TreeNode ℕ,
    if p.1 ≠ p.2 then
      pathGenerationTerm φ n F x p.1 ω * pathGenerationTerm φ n F x p.2 ω
    else 0

theorem pathGenerationDistinctAddressPairCount_measurable
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) {F : (Fin (n + 1) → ℝ) → ℝ≥0∞}
    (hF : Measurable F) (x : ℝ) :
    Measurable (pathGenerationDistinctAddressPairCount φ n F x) := by
  classical
  unfold pathGenerationDistinctAddressPairCount
  apply Measurable.tsum
  intro p
  by_cases hp : p.1 ≠ p.2
  · simp only [if_pos hp]
    change Measurable (fun ω =>
      pathGenerationTerm φ n F x p.1 ω * pathGenerationTerm φ n F x p.2 ω)
    exact (pathGenerationTerm_measurable φ n hF x p.1).mul
      (pathGenerationTerm_measurable φ n hF x p.2)
  · simp [hp]

/-- For a zero-one path test, the squared path count is the diagonal count
plus the ordered count of pairs of distinct successful addresses. -/
theorem pathGeneration_sq_eq_self_add_distinctAddressPairCount
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (F : (Fin (n + 1) → ℝ) → ℝ≥0∞)
    (hF : ∀ history, F history = 0 ∨ F history = 1)
    (x : ℝ) (ω : StepField ℕ X) :
    (pathGeneration φ n F x ω) ^ 2 =
      pathGeneration φ n F x ω +
        pathGenerationDistinctAddressPairCount φ n F x ω := by
  classical
  let f : TreeNode ℕ → ℝ≥0∞ := fun u => pathGenerationTerm φ n F x u ω
  have hf01 (u : TreeNode ℕ) : f u = 0 ∨ f u = 1 := by
    by_cases hu : u.length = n ∧ surviveAlong ω [] u
    · change pathGenerationTerm φ n F x u ω = 0 ∨
        pathGenerationTerm φ n F x u ω = 1
      have hmem : ω ∈
          {ω' : StepField ℕ X | u.length = n ∧ surviveAlong ω' [] u} := hu
      rw [pathGenerationTerm, Set.indicator_of_mem hmem]
      exact hF (pathHistory φ n x ω u)
    · change pathGenerationTerm φ n F x u ω = 0 ∨
        pathGenerationTerm φ n F x u ω = 1
      have hnot : ω ∉
          {ω' : StepField ℕ X | u.length = n ∧ surviveAlong ω' [] u} := hu
      rw [pathGenerationTerm, Set.indicator_of_notMem hnot]
      simp
  have hdiag : (∑' u : TreeNode ℕ, f u ^ 2) = ∑' u, f u := by
    apply tsum_congr
    intro u
    rcases hf01 u with hzero | hone
    · rw [hzero]
      simp
    · rw [hone]
      simp
  have hpair :
      (∑' p : TreeNode ℕ × TreeNode ℕ, f p.1 * f p.2) =
        (∑' u : TreeNode ℕ, f u ^ 2) +
          (∑' u : TreeNode ℕ, ∑' v : TreeNode ℕ,
            if u ≠ v then f u * f v else 0) :=
    ennreal_tsum_pair_eq_diagonal_add_offDiagonal f
  have hpairCount :
      pathGenerationDistinctAddressPairCount φ n F x ω =
        ∑' u : TreeNode ℕ, ∑' v : TreeNode ℕ,
          if u ≠ v then f u * f v else 0 := by
    unfold pathGenerationDistinctAddressPairCount
    change (∑' p : TreeNode ℕ × TreeNode ℕ,
      (fun u v : TreeNode ℕ => if u ≠ v then f u * f v else 0) p.1 p.2) = _
    exact ENNReal.tsum_prod
      (f := fun u v : TreeNode ℕ => if u ≠ v then f u * f v else 0)
  change (∑' u : TreeNode ℕ, f u) ^ 2 = _
  rw [pow_two]
  calc
    (∑' u : TreeNode ℕ, f u) * (∑' u : TreeNode ℕ, f u) =
        ∑' p : TreeNode ℕ × TreeNode ℕ, f p.1 * f p.2 := by
          calc
            _ = ∑' u : TreeNode ℕ, f u * (∑' v : TreeNode ℕ, f v) := by
              rw [← ENNReal.tsum_mul_right]
            _ = ∑' u : TreeNode ℕ, ∑' v : TreeNode ℕ, f u * f v := by
              apply tsum_congr
              intro u
              rw [← ENNReal.tsum_mul_left]
            _ = ∑' p : TreeNode ℕ × TreeNode ℕ, f p.1 * f p.2 :=
              ENNReal.tsum_prod.symm
    _ = (∑' u : TreeNode ℕ, f u ^ 2) +
          (∑' u : TreeNode ℕ, ∑' v : TreeNode ℕ,
            if u ≠ v then f u * f v else 0) := hpair
    _ = pathGeneration φ n F x ω +
          pathGenerationDistinctAddressPairCount φ n F x ω := by
          rw [hdiag, hpairCount]
          rfl

/-- Integrating the zero-one path-count identity separates its first moment
from its expected ordered distinct-pair count. This is the measurable
multi-generation interface for supplying the MRCA contribution in the
paper's corridor second-moment argument. -/
theorem lintegral_pathGeneration_sq_eq_add_distinctAddressPairCount
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) (n : ℕ)
    (F : (Fin (n + 1) → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (hF01 : ∀ history, F history = 0 ∨ F history = 1) (x : ℝ) :
    (∫⁻ ω, (pathGeneration φ n F x ω) ^ 2 ∂stepFieldLaw μ) =
      (∫⁻ ω, pathGeneration φ n F x ω ∂stepFieldLaw μ) +
        (∫⁻ ω, pathGenerationDistinctAddressPairCount φ n F x ω
          ∂stepFieldLaw μ) := by
  have hcount : Measurable (pathGeneration φ n F x) :=
    pathGeneration_measurable (ι := ℕ) φ n hF x
  have hpairs : Measurable (pathGenerationDistinctAddressPairCount φ n F x) :=
    pathGenerationDistinctAddressPairCount_measurable φ n hF x
  calc
    _ = ∫⁻ ω, pathGeneration φ n F x ω +
          pathGenerationDistinctAddressPairCount φ n F x ω ∂stepFieldLaw μ := by
      apply lintegral_congr
      intro ω
      exact pathGeneration_sq_eq_self_add_distinctAddressPairCount
        φ n F hF01 x ω
    _ = (∫⁻ ω, pathGeneration φ n F x ω ∂stepFieldLaw μ) +
          (∫⁻ ω, pathGenerationDistinctAddressPairCount φ n F x ω
            ∂stepFieldLaw μ) := by
      rw [lintegral_add_left' hcount.aemeasurable]

/-- If a corridor has a finite first moment, then the recursive
most-recent-common-ancestor remainder agrees almost everywhere with the
direct ordered-pair count.  The finite first moment rules out an infinite
diagonal count, so it is legitimate to cancel that diagonal from the two
second-moment decompositions. -/
theorem pathGenerationOffDiagonalPairs_ae_eq_distinctAddressPairCount
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (initial terminalUpper : ℝ)
    (corridor : Set (Fin (n + 1) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (hterminalUpper : ∀ history ∈ corridor,
      history ⟨n, Nat.lt_succ_self n⟩ ≤ terminalUpper) :
    pathGenerationOffDiagonalPairs φ n
        (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial =ᵐ[stepFieldLaw μ]
      pathGenerationDistinctAddressPairCount φ n
        (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial := by
  let F : (Fin (n + 1) → ℝ) → ℝ≥0∞ :=
    corridor.indicator (fun _ => (1 : ℝ≥0∞))
  have hF : Measurable F := measurable_const.indicator hcorridor
  have hF01 : ∀ history, F history = 0 ∨ F history = 1 := by
    intro history
    by_cases h : history ∈ corridor <;> simp [F, h]
  have hcount : Measurable (pathGeneration φ n F initial) :=
    pathGeneration_measurable (ι := ℕ) φ n hF initial
  letI : IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) :=
    Spine.tiltedIncrementFieldLaw_isProbability φ μ hboundary
  have hcountIntegral := lintegral_pathGeneration_le_exp_mul_spineProbability
    φ μ hboundary n initial terminalUpper corridor hcorridor hterminalUpper
  have hcountIntegral_ne_top :
      (∫⁻ ω, pathGeneration φ n F initial ω ∂stepFieldLaw μ) ≠ ∞ := by
    apply ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (measure_ne_top (tiltedIncrementFieldLaw φ μ) _))
    simpa [F] using hcountIntegral
  have hcount_ne_top : ∀ᵐ ω ∂stepFieldLaw μ,
      pathGeneration φ n F initial ω ≠ ∞ := by
    filter_upwards [ae_lt_top hcount hcountIntegral_ne_top] with ω hω
    exact hω.ne
  filter_upwards [hcount_ne_top] with ω hω
  have hrecursive := pathGeneration_sq_eq_self_add_offDiagonalPairs
    φ n F hF01 initial ω
  have hdirect := pathGeneration_sq_eq_self_add_distinctAddressPairCount
    φ n F hF01 initial ω
  apply (ENNReal.add_right_inj hω).mp
  calc
    pathGeneration φ n F initial ω + pathGenerationOffDiagonalPairs φ n F initial ω =
        (pathGeneration φ n F initial ω) ^ 2 := hrecursive.symm
    _ = pathGeneration φ n F initial ω +
        pathGenerationDistinctAddressPairCount φ n F initial ω := hdirect

/-- The expected recursive MRCA remainder can therefore be computed using
the measurable direct distinct-address pair count. -/
theorem lintegral_pathGenerationOffDiagonalPairs_eq_distinctAddressPairCount
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (initial terminalUpper : ℝ)
    (corridor : Set (Fin (n + 1) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (hterminalUpper : ∀ history ∈ corridor,
      history ⟨n, Nat.lt_succ_self n⟩ ≤ terminalUpper) :
    (∫⁻ ω, pathGenerationOffDiagonalPairs φ n
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω ∂stepFieldLaw μ) =
      (∫⁻ ω, pathGenerationDistinctAddressPairCount φ n
        (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω ∂stepFieldLaw μ) := by
  exact lintegral_congr_ae
    (pathGenerationOffDiagonalPairs_ae_eq_distinctAddressPairCount
      φ μ hboundary n initial terminalUpper corridor hcorridor hterminalUpper)

/-- Pair-moment input for a long corridor can be passed directly to the
independent-root survival estimate. The only missing probabilistic input is
the paper's estimate on the expected number of ordered distinct successful
path pairs; this theorem turns that input into the full second moment and
then applies the existing Paley--Zygmund/root-count adapter. -/
theorem measure_finiteRootCorridorCount_le_quarter_spineLower_of_pairMoment
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) (initial lower terminalUpper : ℝ)
    (corridor : Set (Fin (n + 1) → ℝ))
    (hcorridor : MeasurableSet corridor)
    (hterminalLower : ∀ history ∈ corridor,
      lower ≤ history ⟨n, Nat.lt_succ_self n⟩)
    (hterminalUpper : ∀ history ∈ corridor,
      history ⟨n, Nat.lt_succ_self n⟩ ≤ terminalUpper)
    (m : ℕ) (hm : 0 < m)
    (pairBound : ℝ≥0∞)
    (hpairBound : (∫⁻ ω,
      pathGenerationDistinctAddressPairCount φ n
        (corridor.indicator (fun _ => (1 : ℝ≥0∞))) initial ω
      ∂stepFieldLaw μ) ≤ pairBound)
    (hpairBound_top : pairBound ≠ ∞)
    (hspinePositive : 0 < (tiltedIncrementFieldLaw φ μ)
      {increment | RandomWalk.history n initial increment ∈ corridor}) :
    let spineEvent :=
      {increment | RandomWalk.history n initial increment ∈ corridor}
    let lowerMean := ENNReal.ofReal (Real.exp (lower - initial)) *
      (tiltedIncrementFieldLaw φ μ) spineEvent
    (finiteRootStepFieldLaw μ m)
        {field : FiniteRootStepField m ℕ X |
          (∑ r : Fin m,
            (hasPathHistoryIn (ι := ℕ) φ n initial corridor).indicator
              (fun _ => (1 : ℝ)) (field r)) ≤
            (m : ℝ) * (lowerMean ^ 2 /
              (ENNReal.ofReal (Real.exp (terminalUpper - initial)) *
                (tiltedIncrementFieldLaw φ μ) spineEvent + pairBound)).toReal / 4} ≤
      ENNReal.ofReal (Real.exp
        (-((m : ℝ) * (lowerMean ^ 2 /
          (ENNReal.ofReal (Real.exp (terminalUpper - initial)) *
            (tiltedIncrementFieldLaw φ μ) spineEvent + pairBound)).toReal / 4))) := by
  classical
  let F : (Fin (n + 1) → ℝ) → ℝ≥0∞ :=
    corridor.indicator (fun _ => (1 : ℝ≥0∞))
  let spineEvent : Set (ℕ → ℝ) :=
    {increment | RandomWalk.history n initial increment ∈ corridor}
  let upperMean : ℝ≥0∞ :=
    ENNReal.ofReal (Real.exp (terminalUpper - initial)) *
      (tiltedIncrementFieldLaw φ μ) spineEvent
  let second : ℝ≥0∞ := upperMean + pairBound
  have hF : Measurable F := measurable_const.indicator hcorridor
  have hF01 : ∀ history, F history = 0 ∨ F history = 1 := by
    intro history
    by_cases h : history ∈ corridor <;> simp [F, h]
  have hmeanUpper :
      (∫⁻ ω, pathGeneration φ n F initial ω ∂stepFieldLaw μ) ≤ upperMean := by
    simpa [F, spineEvent, upperMean] using
      lintegral_pathGeneration_le_exp_mul_spineProbability
        φ μ hboundary n initial terminalUpper corridor hcorridor hterminalUpper
  have htilted : IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) :=
    Spine.tiltedIncrementFieldLaw_isProbability φ μ hboundary
  letI : IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) := htilted
  have hpairs := lintegral_pathGeneration_sq_eq_add_distinctAddressPairCount
    φ μ n F hF hF01 initial
  have hsecond :
      (∫⁻ ω, (pathGeneration φ n F initial ω) ^ 2 ∂stepFieldLaw μ) ≤ second := by
    calc
      _ = (∫⁻ ω, pathGeneration φ n F initial ω ∂stepFieldLaw μ) +
          (∫⁻ ω, pathGenerationDistinctAddressPairCount φ n F initial ω
            ∂stepFieldLaw μ) := hpairs
      _ ≤ upperMean + pairBound := add_le_add hmeanUpper hpairBound
      _ = second := rfl
  have hupperMean_top : upperMean ≠ ∞ := by
    dsimp [upperMean]
    exact ENNReal.mul_ne_top (by simp) (measure_ne_top _ _)
  have hsecond_top : second ≠ ∞ := by
    dsimp [second]
    exact ENNReal.add_ne_top.mpr ⟨hupperMean_top, hpairBound_top⟩
  have hupperMean_pos : 0 < upperMean := by
    dsimp [upperMean, spineEvent]
    exact ENNReal.mul_pos (by positivity) (ne_of_gt hspinePositive)
  have hsecond_pos : 0 < second := by
    dsimp [second]
    exact lt_of_lt_of_le hupperMean_pos le_self_add
  have hresult :=
    measure_finiteRootCorridorCount_le_quarter_spineLowerPZ
      φ μ hboundary n initial lower corridor hcorridor hterminalLower m hm
      second hsecond hsecond_pos hsecond_top
  simpa [spineEvent, F, upperMean, second] using hresult

end ProbabilityTheory.BranchingRandomWalk.Spine
