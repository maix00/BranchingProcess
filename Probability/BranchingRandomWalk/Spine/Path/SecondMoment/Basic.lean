/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Spine.Path.Decomposition.Branching
import Probability.BranchingRandomWalk.Spine.Path.ManyToOne.Event
import Probability.BranchingRandomWalk.Spine.GenerationBranching.Decomposition
import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.JointSubtrees

/-!
# Second moments and ancestral pair decomposition

This BRW path module expands a zero-one generation count into its diagonal
first moment and ordered distinct-path pairs, then groups those pairs by the
generation of their most recent common ancestor. Corridor estimates and
selection-process applications live in their respective higher layers.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Spine
open ProbabilityTheory.RandomWalk

/-- The conditional ordered off-diagonal continuation-pair observable at a
fixed ancestor position and reproduction mark. The descendant fields below
distinct children have already been averaged independently. -/
noncomputable def pathGenerationChildMeanOffDiagonal
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) (n : ℕ)
    (F : (Fin (n + 2) → ℝ) → ℝ≥0∞) (x : ℝ)
    (ξ : Step ℕ X) : ℝ≥0∞ :=
  ∑' i : ℕ, ∑' j : ℕ, if i ≠ j then
    (∫⁻ η, pathGenerationChildObservable φ n F x i ξ η
      ∂stepFieldLaw μ) *
    (∫⁻ ζ, pathGenerationChildObservable φ n F x j ξ ζ
      ∂stepFieldLaw μ) else 0

/-- The conditional off-diagonal continuation-pair observable is measurable
in the ancestor reproduction mark whenever the path test is measurable. -/
theorem pathGenerationChildMeanOffDiagonal_measurable
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ] (n : ℕ)
    (F : (Fin (n + 2) → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (x : ℝ) :
    Measurable (pathGenerationChildMeanOffDiagonal φ μ n F x) := by
  classical
  let childMean (i : ℕ) (ξ : Step ℕ X) : ℝ≥0∞ :=
    ∫⁻ η, pathGenerationChildObservable φ n F x i ξ η
      ∂stepFieldLaw μ
  let offTerm (i j : ℕ) (ξ : Step ℕ X) : ℝ≥0∞ :=
    if i ≠ j then childMean i ξ * childMean j ξ else 0
  have hchildMean (i : ℕ) : Measurable (childMean i) := by
    apply Measurable.lintegral_prod_right
    simpa [childMean] using
      pathGenerationChildObservable_measurable φ n F hF x i
  have hoffTerm (i j : ℕ) : Measurable (offTerm i j) := by
    by_cases hij : i ≠ j
    · simp only [offTerm, if_pos hij]
      exact (hchildMean i).mul (hchildMean j)
    · have hEq : i = j := by
        by_contra hne
        exact hij hne
      simp [offTerm, hEq]
  have hoffInner (i : ℕ) : Measurable (fun ξ => ∑' j, offTerm i j ξ) := by
    apply Measurable.tsum
    intro j
    exact hoffTerm i j
  have hoffSum : Measurable (fun ξ => ∑' i, ∑' j, offTerm i j ξ) := by
    apply Measurable.tsum
    intro i
    exact hoffInner i
  change Measurable (fun ξ => ∑' i : ℕ, ∑' j : ℕ,
    if i ≠ j then childMean i ξ * childMean j ξ else 0)
  exact hoffSum

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

/-- For a zero-one path test, the second moment splits into its diagonal
first-moment term and the finite sum of ordered pairs grouped by the
generation of their most recent common ancestor. This is the combinatorial
decomposition used in the second-moment expansion of the long-corridor
argument; the probabilistic bounds on the individual layers are separate. -/
theorem pathGeneration_indicator_sq_eq_self_add_sum_mrcaContribution
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (n : ℕ) (corridor : Set (Fin (n + 1) → ℝ))
    (x : ℝ) (ω : StepField ℕ X) :
    (pathGeneration φ n
      (corridor.indicator (fun _ => (1 : ℝ≥0∞))) x ω) ^ 2 =
      pathGeneration φ n
          (corridor.indicator (fun _ => (1 : ℝ≥0∞))) x ω +
        ∑ depth : Fin n,
          pathGenerationMRCAContribution φ depth.val n
            (corridor.indicator (fun _ => (1 : ℝ≥0∞))) x ω := by
  rw [pathGeneration_indicator_sq_eq_self_add_offDiagonalPairs,
    pathGenerationOffDiagonalPairs_eq_sum_mrcaContribution]

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
the corridor second-moment argument. -/
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


/-- The descendant fields of two distinct first-generation children have the
product law. This is the subtree-independence input for the off-diagonal
terms in the second-moment decomposition. -/
theorem distinct_child_subtreeFields_joint_law
    {ι X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    (i j : ι) (hij : i ≠ j) :
    (stepFieldLaw μ).map
        (fun ω => (subtreeStepField [i] ω, subtreeStepField [j] ω)) =
      (stepFieldLaw μ).prod (stepFieldLaw μ) := by
  classical
  let roots : Bool → TreeNode ι := fun b => if b then [i] else [j]
  have hlen : ∀ b, (roots b).length = 1 := by
    intro b
    cases b <;> simp [roots]
  have hinj : Function.Injective roots := by
    intro b c h
    cases b <;> cases c <;> simp_all [roots]
  let pairEval : (Bool → StepField ι X) → StepField ι X × StepField ι X :=
    fun fields => (fields true, fields false)
  have hcomp :
      (fun ω : StepField ι X =>
        (subtreeStepField [i] ω, subtreeStepField [j] ω)) =
      pairEval ∘
        ProbabilityTheory.BranchingRandomWalk.subtreeStepFieldVector roots := by
    funext ω
    simp [pairEval, roots,
      ProbabilityTheory.BranchingRandomWalk.subtreeStepFieldVector]
  have hvector :=
    ProbabilityTheory.BranchingRandomWalk.fixed_subtreeStepFieldVector_law
      μ roots hlen hinj
  have hpair := Measure.infinitePi_map_eval_prod
    (P := fun _ : Bool => stepFieldLaw μ) (i := true) (j := false) (by decide)
  calc
    (stepFieldLaw μ).map
        (fun ω => (subtreeStepField [i] ω, subtreeStepField [j] ω)) =
        ((stepFieldLaw μ).map
          (ProbabilityTheory.BranchingRandomWalk.subtreeStepFieldVector roots)).map
            pairEval := by
      rw [Measure.map_map (by fun_prop)
        (ProbabilityTheory.BranchingRandomWalk.subtreeStepFieldVector_measurable roots)]
      rw [hcomp]
    _ = (Measure.infinitePi (fun _ : Bool => stepFieldLaw μ)).map pairEval := by
      rw [hvector]
    _ = (stepFieldLaw μ).prod (stepFieldLaw μ) := by
      simpa [pairEval] using hpair

/-- The root reproduction step is independent of the two descendant fields
below distinct children; their full joint law is the corresponding triple
product. This is the branching-property law used to average a split pair. -/
theorem root_two_distinct_childFields_joint_law
    {ι X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    (i j : ι) (hij : i ≠ j) :
    (stepFieldLaw μ).map
        (fun ω => (ω ([] : TreeNode ι),
          (subtreeStepField [i] ω, subtreeStepField [j] ω))) =
      μ.prod ((stepFieldLaw μ).prod (stepFieldLaw μ)) := by
  classical
  let roots : Bool → TreeNode ι := fun b => if b then [i] else [j]
  let vector : StepField ι X → Bool → StepField ι X :=
    ProbabilityTheory.BranchingRandomWalk.subtreeStepFieldVector roots
  let rootVector : StepField ι X → Step ι X × (Bool → StepField ι X) :=
    fun ω => (ω [], vector ω)
  let evalPair : (Bool → StepField ι X) → StepField ι X × StepField ι X :=
    fun fields => (fields true, fields false)
  let regroup : Step ι X × (Bool → StepField ι X) →
      Step ι X × (StepField ι X × StepField ι X) :=
    fun p => (p.1, evalPair p.2)
  have hvectorMeas : Measurable vector :=
    ProbabilityTheory.BranchingRandomWalk.subtreeStepFieldVector_measurable roots
  have hrootVectorMeas : Measurable rootVector :=
    (measurable_pi_apply ([] : TreeNode ι)).prodMk hvectorMeas
  have hevalPair : Measurable evalPair :=
    (measurable_pi_apply true).prodMk (measurable_pi_apply false)
  have hregroupMeas : Measurable regroup :=
    measurable_fst.prodMk (hevalPair.comp measurable_snd)
  have hlen : ∀ b, (roots b).length = 1 := by
    intro b
    cases b <;> simp [roots]
  have hinj : Function.Injective roots := by
    intro b c h
    cases b <;> cases c <;> simp_all [roots]
  have hvector :=
    ProbabilityTheory.BranchingRandomWalk.fixed_subtreeStepFieldVector_law
      μ roots hlen hinj
  have hrootPast : Measurable[generationFiltration
      (M := Step ι X) 1]
      (fun ω : StepField ι X => ω ([] : TreeNode ι)) :=
    mark_measurable_of_depth_lt [] 1 (by simp)
  have hind : IndepFun
      (fun ω : StepField ι X => ω ([] : TreeNode ι)) vector
      (stepFieldLaw μ) := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left
      (ProbabilityTheory.BranchingRandomWalk.fixed_subtreeStepFieldVector_independent
        μ roots hlen) hrootPast.comap_le
  have hrootVector :
      (stepFieldLaw μ).map rootVector =
        μ.prod (Measure.infinitePi (fun _ : Bool => stepFieldLaw μ)) := by
    unfold rootVector vector
    rw [hind.map_prod_eq_prod_map_map
      (measurable_pi_apply ([] : TreeNode ι)).aemeasurable
      (ProbabilityTheory.BranchingRandomWalk.subtreeStepFieldVector_measurable
        roots).aemeasurable,
      stepFieldLaw_coordinate μ ([] : TreeNode ι), hvector]
  have hinfinitePi := Measure.infinitePi_map_eval_prod
    (P := fun _ : Bool => stepFieldLaw μ) (i := true) (j := false) (by decide)
  have hregroup :
      (μ.prod (Measure.infinitePi (fun _ : Bool => stepFieldLaw μ))).map regroup =
        μ.prod ((stepFieldLaw μ).prod (stepFieldLaw μ)) := by
    change (μ.prod (Measure.infinitePi (fun _ : Bool => stepFieldLaw μ))).map
      (Prod.map id evalPair) = _
    have hprod := Measure.map_prod_map μ
      (Measure.infinitePi (fun _ : Bool => stepFieldLaw μ))
      measurable_id hevalPair
    rw [← hprod, Measure.map_id, hinfinitePi]
  have hcomp :
      (fun ω : StepField ι X => (ω ([] : TreeNode ι),
        (subtreeStepField [i] ω, subtreeStepField [j] ω))) =
      regroup ∘ rootVector := by
    funext ω
    simp [regroup, rootVector, vector, evalPair, roots,
      ProbabilityTheory.BranchingRandomWalk.subtreeStepFieldVector]
  calc
    (stepFieldLaw μ).map
        (fun ω => (ω ([] : TreeNode ι),
          (subtreeStepField [i] ω, subtreeStepField [j] ω))) =
        (stepFieldLaw μ).map (regroup ∘ rootVector) := by rw [hcomp]
    _ = ((stepFieldLaw μ).map rootVector).map regroup :=
      (Measure.map_map hregroupMeas hrootVectorMeas).symm
    _ = μ.prod ((stepFieldLaw μ).prod (stepFieldLaw μ)) := by
      rw [hrootVector, hregroup]




/-- Conditional on the root reproduction step, the two descendant observables
from distinct children factor under their independent subtree fields. -/
theorem lintegral_root_product_distinct_child_subtrees
    {ι X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    (i j : ι) (hij : i ≠ j)
    (F G : Step ι X → StepField ι X → ℝ≥0∞)
    (hF : Measurable (Function.uncurry F))
    (hG : Measurable (Function.uncurry G)) :
    (∫⁻ ω, F (ω []) (subtreeStepField [i] ω) *
      G (ω []) (subtreeStepField [j] ω) ∂stepFieldLaw μ) =
      ∫⁻ ξ, (∫⁻ η, F ξ η ∂stepFieldLaw μ) *
        (∫⁻ ζ, G ξ ζ ∂stepFieldLaw μ) ∂μ := by
  let triple : StepField ι X → Step ι X ×
      (StepField ι X × StepField ι X) := fun ω =>
    (ω [], (subtreeStepField [i] ω, subtreeStepField [j] ω))
  let H : Step ι X × (StepField ι X × StepField ι X) → ℝ≥0∞ :=
    fun p => F p.1 p.2.1 * G p.1 p.2.2
  have hTriple : Measurable triple :=
    (measurable_pi_apply ([] : TreeNode ι)).prodMk
      ((subtreeStepField_measurable [i]).prodMk
        (subtreeStepField_measurable [j]))
  have hH : Measurable H := by
    exact (hF.comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
        (hG.comp
          (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  calc
    (∫⁻ ω, F (ω []) (subtreeStepField [i] ω) *
        G (ω []) (subtreeStepField [j] ω) ∂stepFieldLaw μ) =
        ∫⁻ p, H p ∂(stepFieldLaw μ).map triple := by
      exact (lintegral_map hH hTriple).symm
    _ = ∫⁻ p, H p ∂μ.prod ((stepFieldLaw μ).prod (stepFieldLaw μ)) := by
      rw [root_two_distinct_childFields_joint_law μ i j hij]
    _ = ∫⁻ ξ, (∫⁻ η, F ξ η ∂stepFieldLaw μ) *
          (∫⁻ ζ, G ξ ζ ∂stepFieldLaw μ) ∂μ := by
      rw [lintegral_prod H hH.aemeasurable]
      apply lintegral_congr
      intro ξ
      change (∫⁻ p, F ξ p.1 * G ξ p.2 ∂
        (stepFieldLaw μ).prod (stepFieldLaw μ)) = _
      exact lintegral_prod_mul
        (hF.comp (measurable_const.prodMk measurable_id)).aemeasurable
        (hG.comp (measurable_const.prodMk measurable_id)).aemeasurable


/-- Specialization of the split-pair factorization to the path counts in the
first-generation decomposition. This is the off-diagonal term for the
generation-`n + 1` second moment. -/
theorem lintegral_pathGeneration_childProduct_eq
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (F : (Fin (n + 2) → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (x : ℝ) (i j : ℕ) (hij : i ≠ j) :
    (∫⁻ ω, survivingPotentialTest φ
        (fun y => Spine.pathGeneration φ n
          (fun tail => F (prependHistory x tail)) (x + y)
          (subtreeStepField [i] ω)) (ω []) i *
      survivingPotentialTest φ
        (fun y => Spine.pathGeneration φ n
          (fun tail => F (prependHistory x tail)) (x + y)
          (subtreeStepField [j] ω)) (ω []) j ∂stepFieldLaw μ) =
      ∫⁻ ξ, (∫⁻ η, survivingPotentialTest φ
          (fun y => Spine.pathGeneration φ n
            (fun tail => F (prependHistory x tail)) (x + y) η) ξ i
          ∂stepFieldLaw μ) *
        (∫⁻ ζ, survivingPotentialTest φ
          (fun y => Spine.pathGeneration φ n
            (fun tail => F (prependHistory x tail)) (x + y) ζ) ξ j
          ∂stepFieldLaw μ) ∂μ := by
  let tailTest : (Fin (n + 1) → ℝ) → ℝ≥0∞ :=
    fun tail => F (prependHistory x tail)
  have htailTest : Measurable tailTest :=
    hF.comp ((prependHistory_joint_measurable n).comp
      (measurable_const.prodMk measurable_id))
  let childObservable (k : ℕ) : Step ℕ X → StepField ℕ X → ℝ≥0∞ :=
    fun ξ η => survivingPotentialTest φ
      (fun y => Spine.pathGeneration φ n tailTest (x + y) η) ξ k
  have hchildObservable (k : ℕ) :
      Measurable (Function.uncurry (childObservable k)) := by
    unfold childObservable survivingPotentialTest
    exact ((Spine.pathGeneration_joint_measurable φ n htailTest).comp
      (((measurable_const.add
        ((Step.potentialValue'_measurable φ k).comp measurable_fst))).prodMk
          measurable_snd)).ite
      ((survive_measurableSet k).preimage measurable_fst)
      measurable_const
  have hfactor := lintegral_root_product_distinct_child_subtrees
    μ i j hij (childObservable i) (childObservable j)
    (hchildObservable i) (hchildObservable j)
  simpa [tailTest, childObservable] using hfactor

/-- The expected contribution of pairs that split at the root is the
offspring-law average of the conditional off-diagonal pair observable. This is
the depth-zero case of the conditional-prefix representation of MRCA terms. -/
theorem lintegral_pathGenerationMRCAContribution_zero_eq_childMeanOffDiagonal
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (F : (Fin (n + 2) → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (x : ℝ) :
    (∫⁻ ω, pathGenerationMRCAContribution φ 0 (n + 1) F x ω
      ∂stepFieldLaw μ) =
      ∫⁻ ξ, pathGenerationChildMeanOffDiagonal φ μ n F x ξ ∂μ := by
  classical
  let childObservable (i : ℕ) (ω : StepField ℕ X) : ℝ≥0∞ :=
    pathGenerationChildObservable φ n F x i (ω [])
      (subtreeStepField [i] ω)
  let childMean (i : ℕ) (ξ : Step ℕ X) : ℝ≥0∞ :=
    ∫⁻ η, pathGenerationChildObservable φ n F x i ξ η ∂stepFieldLaw μ
  let pairTerm (i j : ℕ) (ω : StepField ℕ X) : ℝ≥0∞ :=
    if i ≠ j then childObservable i ω * childObservable j ω else 0
  let meanPairTerm (i j : ℕ) (ξ : Step ℕ X) : ℝ≥0∞ :=
    if i ≠ j then childMean i ξ * childMean j ξ else 0
  have hchildObservable (i : ℕ) : Measurable (childObservable i) := by
    change Measurable
      (Function.uncurry (pathGenerationChildObservable φ n F x i) ∘
        fun ω : StepField ℕ X => (ω [], subtreeStepField [i] ω))
    exact (pathGenerationChildObservable_measurable φ n F hF x i).comp
      ((measurable_pi_apply ([] : TreeNode ℕ)).prodMk
        (subtreeStepField_measurable [i]))
  have hchildMean (i : ℕ) : Measurable (childMean i) := by
    apply Measurable.lintegral_prod_right
    simpa [childMean] using
      pathGenerationChildObservable_measurable φ n F hF x i
  have hpairTerm (i j : ℕ) : Measurable (pairTerm i j) := by
    by_cases hij : i ≠ j
    · simp only [pairTerm, if_pos hij]
      exact (hchildObservable i).mul (hchildObservable j)
    · have hEq : i = j := by
        by_contra hne
        exact hij hne
      simp [pairTerm, hEq]
  have hmeanPairTerm (i j : ℕ) : Measurable (meanPairTerm i j) := by
    by_cases hij : i ≠ j
    · simp only [meanPairTerm, if_pos hij]
      exact (hchildMean i).mul (hchildMean j)
    · have hEq : i = j := by
        by_contra hne
        exact hij hne
      simp [meanPairTerm, hEq]
  have hpairFactor (i j : ℕ) (hij : i ≠ j) :
      (∫⁻ ω, childObservable i ω * childObservable j ω
        ∂stepFieldLaw μ) =
      ∫⁻ ξ, childMean i ξ * childMean j ξ ∂μ := by
    change (∫⁻ ω, pathGenerationChildObservable φ n F x i
        (ω []) (subtreeStepField [i] ω) *
      pathGenerationChildObservable φ n F x j
        (ω []) (subtreeStepField [j] ω) ∂stepFieldLaw μ) =
      ∫⁻ ξ,
        (∫⁻ η, pathGenerationChildObservable φ n F x i ξ η
          ∂stepFieldLaw μ) *
        (∫⁻ ζ, pathGenerationChildObservable φ n F x j ξ ζ
          ∂stepFieldLaw μ) ∂μ
    exact lintegral_pathGeneration_childProduct_eq φ μ n F hF x i j hij
  have hterm (i j : ℕ) :
      (∫⁻ ω, pairTerm i j ω ∂stepFieldLaw μ) =
        ∫⁻ ξ, meanPairTerm i j ξ ∂μ := by
    by_cases hij : i ≠ j
    · simp only [pairTerm, meanPairTerm, if_pos hij]
      exact hpairFactor i j hij
    · have hEq : i = j := by
        by_contra hne
        exact hij hne
      simp [pairTerm, meanPairTerm, hEq]
  have hpairSum (i : ℕ) : Measurable (fun ω => ∑' j, pairTerm i j ω) := by
    apply Measurable.tsum
    intro j
    exact hpairTerm i j
  have hmeanPairSum (i : ℕ) : Measurable (fun ξ => ∑' j, meanPairTerm i j ξ) := by
    apply Measurable.tsum
    intro j
    exact hmeanPairTerm i j
  have hleftInner (i : ℕ) :
      (∫⁻ ω, ∑' j, pairTerm i j ω ∂stepFieldLaw μ) =
        ∑' j, ∫⁻ ω, pairTerm i j ω ∂stepFieldLaw μ := by
    rw [lintegral_tsum]
    intro j
    exact (hpairTerm i j).aemeasurable
  have hleft :
      (∫⁻ ω, ∑' i, ∑' j, pairTerm i j ω ∂stepFieldLaw μ) =
        ∑' i, ∑' j, ∫⁻ ω, pairTerm i j ω ∂stepFieldLaw μ := by
    rw [lintegral_tsum]
    · apply tsum_congr
      intro i
      exact hleftInner i
    · intro i
      exact (hpairSum i).aemeasurable
  have hrightInner (i : ℕ) :
      (∫⁻ ξ, ∑' j, meanPairTerm i j ξ ∂μ) =
        ∑' j, ∫⁻ ξ, meanPairTerm i j ξ ∂μ := by
    rw [lintegral_tsum]
    intro j
    exact (hmeanPairTerm i j).aemeasurable
  have hright :
      (∫⁻ ξ, ∑' i, ∑' j, meanPairTerm i j ξ ∂μ) =
        ∑' i, ∑' j, ∫⁻ ξ, meanPairTerm i j ξ ∂μ := by
    rw [lintegral_tsum]
    · apply tsum_congr
      intro i
      exact hrightInner i
    · intro i
      exact (hmeanPairSum i).aemeasurable
  calc
    (∫⁻ ω, pathGenerationMRCAContribution φ 0 (n + 1) F x ω
        ∂stepFieldLaw μ) =
        ∫⁻ ω, ∑' i, ∑' j, pairTerm i j ω ∂stepFieldLaw μ := by
          apply lintegral_congr
          intro ω
          simp [pathGenerationMRCAContribution, pairTerm, childObservable]
    _ = ∑' i, ∑' j, ∫⁻ ω, pairTerm i j ω ∂stepFieldLaw μ := hleft
    _ = ∑' i, ∑' j, ∫⁻ ξ, meanPairTerm i j ξ ∂μ := by
          apply tsum_congr
          intro i
          apply tsum_congr
          intro j
          exact hterm i j
    _ = ∫⁻ ξ, ∑' i, ∑' j, meanPairTerm i j ξ ∂μ := hright.symm
    _ = ∫⁻ ξ, pathGenerationChildMeanOffDiagonal φ μ n F x ξ ∂μ := by
          apply lintegral_congr
          intro ξ
          simp [pathGenerationChildMeanOffDiagonal, meanPairTerm, childMean]

/-- The diagonal term in the generation-`n + 1` second moment is the root-step
average of the squared generation-`n` child count. -/
theorem lintegral_pathGeneration_childSquare_eq
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (F : (Fin (n + 2) → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (x : ℝ) (i : ℕ) :
    (∫⁻ ω, (survivingPotentialTest φ
        (fun y => Spine.pathGeneration φ n
          (fun tail => F (prependHistory x tail)) (x + y)
          (subtreeStepField [i] ω)) (ω []) i) ^ 2 ∂stepFieldLaw μ) =
      ∫⁻ ξ, ∫⁻ η, (survivingPotentialTest φ
          (fun y => Spine.pathGeneration φ n
            (fun tail => F (prependHistory x tail)) (x + y) η) ξ i) ^ 2
        ∂stepFieldLaw μ ∂μ := by
  let tailTest : (Fin (n + 1) → ℝ) → ℝ≥0∞ :=
    fun tail => F (prependHistory x tail)
  have htailTest : Measurable tailTest :=
    hF.comp ((prependHistory_joint_measurable n).comp
      (measurable_const.prodMk measurable_id))
  let childObservable : Step ℕ X → StepField ℕ X → ℝ≥0∞ := fun ξ η =>
    survivingPotentialTest φ
      (fun y => Spine.pathGeneration φ n tailTest (x + y) η) ξ i
  have hchildObservable :
      Measurable (Function.uncurry childObservable) := by
    unfold childObservable survivingPotentialTest
    exact ((Spine.pathGeneration_joint_measurable φ n htailTest).comp
      (((measurable_const.add
        ((Step.potentialValue'_measurable φ i).comp measurable_fst))).prodMk
          measurable_snd)).ite
      ((survive_measurableSet i).preimage measurable_fst)
      measurable_const
  have hsquare : Measurable (fun p : Step ℕ X × StepField ℕ X =>
      childObservable p.1 p.2 ^ 2) := by
    exact hchildObservable.pow_const 2
  have hfactor := lintegral_root_subtreeFunction_eq μ i
    (fun p : Step ℕ X × StepField ℕ X => childObservable p.1 p.2 ^ 2)
    hsquare
  simpa [tailTest, childObservable] using hfactor

/-- Exact first-generation second-moment recursion for a corridor path
count. The diagonal term keeps a single child subtree; distinct children
factor into the product of their conditional first moments. -/
theorem lintegral_pathGeneration_succ_sq_eq_childPairRecursion
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (n : ℕ) (F : (Fin (n + 2) → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (x : ℝ) :
    (∫⁻ ω, (Spine.pathGeneration φ (n + 1) F x ω) ^ 2
      ∂stepFieldLaw μ) =
      (∑' i, ∫⁻ ξ, ∫⁻ η,
        (pathGenerationChildObservable φ n F x i ξ η) ^ 2
          ∂stepFieldLaw μ ∂μ) +
      ∑' i, ∑' j, if i ≠ j then
        ∫⁻ ξ, (∫⁻ η, pathGenerationChildObservable φ n F x i ξ η
              ∂stepFieldLaw μ) *
          (∫⁻ ζ, pathGenerationChildObservable φ n F x j ξ ζ
              ∂stepFieldLaw μ) ∂μ else 0 := by
  let childCount : ℕ → StepField ℕ X → ℝ≥0∞ := fun i ω =>
    pathGenerationChildObservable φ n F x i (ω [])
      (subtreeStepField [i] ω)
  have hchildCount (i : ℕ) : Measurable (childCount i) := by
    unfold childCount
    exact (pathGenerationChildObservable_measurable φ n F hF x i).comp
      ((measurable_pi_apply ([] : TreeNode ℕ)).prodMk
        (subtreeStepField_measurable [i]))
  have hdiagSum : Measurable (fun ω => ∑' i, (childCount i ω) ^ 2) := by
    apply Measurable.tsum
    intro i
    exact (hchildCount i).pow_const 2
  have hoffTerm (i j : ℕ) :
      Measurable (fun ω => if i ≠ j then childCount i ω * childCount j ω else 0) := by
    by_cases hij : i ≠ j
    · simp only [if_pos hij]
      change Measurable (childCount i * childCount j)
      exact (hchildCount i).mul (hchildCount j)
    · simp [hij]
  have hoffInner (i : ℕ) :
      Measurable (fun ω => ∑' j, if i ≠ j then
        childCount i ω * childCount j ω else 0) := by
    apply Measurable.tsum
    intro j
    exact hoffTerm i j
  have hoffSum : Measurable (fun ω => ∑' i, ∑' j, if i ≠ j then
      childCount i ω * childCount j ω else 0) := by
    apply Measurable.tsum
    intro i
    exact hoffInner i
  have hdiagIntegral :
      (∫⁻ ω, ∑' i, (childCount i ω) ^ 2 ∂stepFieldLaw μ) =
        ∑' i, ∫⁻ ω, (childCount i ω) ^ 2 ∂stepFieldLaw μ := by
    rw [lintegral_tsum]
    intro i
    exact ((hchildCount i).pow_const 2).aemeasurable
  have hoffInnerIntegral (i : ℕ) :
      (∫⁻ ω, ∑' j, if i ≠ j then
        childCount i ω * childCount j ω else 0 ∂stepFieldLaw μ) =
        ∑' j, ∫⁻ ω, if i ≠ j then
          childCount i ω * childCount j ω else 0 ∂stepFieldLaw μ := by
    rw [lintegral_tsum]
    intro j
    exact (hoffTerm i j).aemeasurable
  have hoffIntegral :
      (∫⁻ ω, ∑' i, ∑' j, if i ≠ j then
        childCount i ω * childCount j ω else 0 ∂stepFieldLaw μ) =
        ∑' i, ∑' j, ∫⁻ ω, if i ≠ j then
          childCount i ω * childCount j ω else 0 ∂stepFieldLaw μ := by
    rw [lintegral_tsum]
    · apply tsum_congr
      intro i
      exact hoffInnerIntegral i
    · intro i
      exact (hoffInner i).aemeasurable
  have hpoint (ω : StepField ℕ X) :
      (Spine.pathGeneration φ (n + 1) F x ω) ^ 2 =
        (∑' i, (childCount i ω) ^ 2) +
          ∑' i, ∑' j, if i ≠ j then
            childCount i ω * childCount j ω else 0 := by
    simpa [childCount, pathGenerationChildObservable] using
      (pathGeneration_succ_sq_eq_diagonal_add_offDiagonal φ n F x ω)
  calc
    (∫⁻ ω, (Spine.pathGeneration φ (n + 1) F x ω) ^ 2
        ∂stepFieldLaw μ) =
        ∫⁻ ω, (∑' i, (childCount i ω) ^ 2) +
          (∑' i, ∑' j, if i ≠ j then
            childCount i ω * childCount j ω else 0) ∂stepFieldLaw μ := by
      apply lintegral_congr
      intro ω
      exact hpoint ω
    _ = (∫⁻ ω, ∑' i, (childCount i ω) ^ 2 ∂stepFieldLaw μ) +
        ∫⁻ ω, ∑' i, ∑' j, if i ≠ j then
          childCount i ω * childCount j ω else 0 ∂stepFieldLaw μ := by
      rw [lintegral_add_left' hdiagSum.aemeasurable]
    _ = (∑' i, ∫⁻ ω, (childCount i ω) ^ 2 ∂stepFieldLaw μ) +
        ∑' i, ∑' j, ∫⁻ ω, if i ≠ j then
          childCount i ω * childCount j ω else 0 ∂stepFieldLaw μ := by
      rw [hdiagIntegral, hoffIntegral]
    _ = (∑' i, ∫⁻ ξ, ∫⁻ η,
          (pathGenerationChildObservable φ n F x i ξ η) ^ 2
            ∂stepFieldLaw μ ∂μ) +
        ∑' i, ∑' j, if i ≠ j then
          ∫⁻ ξ, (∫⁻ η, pathGenerationChildObservable φ n F x i ξ η
                ∂stepFieldLaw μ) *
            (∫⁻ ζ, pathGenerationChildObservable φ n F x j ξ ζ
                ∂stepFieldLaw μ) ∂μ else 0 := by
      congr 1
      · apply tsum_congr
        intro i
        simpa [childCount, pathGenerationChildObservable] using
          (lintegral_pathGeneration_childSquare_eq φ μ n F hF x i)
      · apply tsum_congr
        intro i
        apply tsum_congr
        intro j
        by_cases hij : i ≠ j
        · simpa [childCount, pathGenerationChildObservable, hij] using
            (lintegral_pathGeneration_childProduct_eq φ μ n F hF x i j hij)
        · simp [hij]


end ProbabilityTheory.BranchingRandomWalk.Spine
