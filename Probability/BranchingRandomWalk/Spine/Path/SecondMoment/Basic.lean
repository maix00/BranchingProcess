/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Path.Decomposition.Branching
public import Probability.BranchingRandomWalk.Spine.Path.ManyToOne.Event
public import Probability.BranchingRandomWalk.Spine.GenerationBranching.Decomposition
public import Probability.BranchingRandomWalk.Genealogy.Exploration.Abstract.JointSubtrees
import all Topology.Algebra.InfiniteSum.ENNReal.PairPartition


/-!
# Pathwise second-moment and ancestral-pair decompositions

Write $N_n(F,x,\omega)=\operatorname{pathGeneration}(\phi,n,F,x,\omega)$.
This module decomposes the square of a zero-one path count into its diagonal
count and the ordered pairs of distinct successful paths, then organizes the
pair remainder by most recent common ancestor. The integrated subtree laws and
second-moment recursion are stated in the sibling `SubtreeLaws` module.

## Public declarations

- `pathGenerationChildMeanOffDiagonal` is the ordered sum of products of
  continuation means in distinct root children.
- `pathGenerationOffDiagonalPairs` recursively records the off-diagonal
  ordered pairs; `pathGeneration_sq_eq_self_add_offDiagonalPairs` states
  $N_n^2=N_n+\operatorname{pathGenerationOffDiagonalPairs}$.
- `pathGenerationMRCAContribution` records ordered pairs by the depth of their
  most recent common ancestor, and
  `pathGenerationOffDiagonalPairs_eq_sum_mrcaContribution` sums those
  contributions over the finite generation range. The two indicator versions
  give these identities for a corridor event.
- `pathGenerationDistinctAddressPairCount` sums products over distinct
  addresses; its measurability theorem and
  `pathGeneration_sq_eq_self_add_distinctAddressPairCount` give the
  corresponding pointwise decomposition.
- `lintegral_pathGeneration_sq_eq_add_distinctAddressPairCount` integrates
  that identity as $\int N_n^2=\int N_n+\int\operatorname{pathGenerationDistinctAddressPairCount}$.

The path count and branching field semantics are owned by the imported
`Spine/Path` and `Genealogy/Exploration` modules.
-/


@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open ProbabilityTheory.BranchingProcess (offspringFieldLaw offspringFieldLaw_coordinate offspringFieldLaw_independent offspringFieldLaw_mapMarks)

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
      ∂offspringFieldLaw μ) *
    (∫⁻ ζ, pathGenerationChildObservable φ n F x j ξ ζ
      ∂offspringFieldLaw μ) else 0

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
      ∂offspringFieldLaw μ
  let offTerm (i j : ℕ) (ξ : Step ℕ X) : ℝ≥0∞ :=
    if i ≠ j then childMean i ξ * childMean j ξ else 0
  have hchildMean (i : ℕ) : Measurable (childMean i) := by
    apply Measurable.lintegral_prod_right
    simpa [childMean] using
      pathGenerationChildObservable_measurable φ n F hF x i
  have hoffTerm (i j : ℕ) : Measurable (offTerm i j) := by
    by_cases hij : i ≠ j
    · simp only [offTerm, ite_eq_left hij]
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
  · simp only [ite_eq_left hp]
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
            if u ≠ v then f u * f v else 0) := by
    simpa [pow_two] using
      ENNReal.tsum_prod_eq_tsum_diagonal_add_offDiagonal
        (fun p => f p.1 * f p.2)
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
    (∫⁻ ω, (pathGeneration φ n F x ω) ^ 2 ∂offspringFieldLaw μ) =
      (∫⁻ ω, pathGeneration φ n F x ω ∂offspringFieldLaw μ) +
        (∫⁻ ω, pathGenerationDistinctAddressPairCount φ n F x ω
          ∂offspringFieldLaw μ) := by
  have hcount : Measurable (pathGeneration φ n F x) :=
    pathGeneration_measurable (ι := ℕ) φ n hF x
  have hpairs : Measurable (pathGenerationDistinctAddressPairCount φ n F x) :=
    pathGenerationDistinctAddressPairCount_measurable φ n hF x
  calc
    _ = ∫⁻ ω, pathGeneration φ n F x ω +
          pathGenerationDistinctAddressPairCount φ n F x ω ∂offspringFieldLaw μ := by
      apply lintegral_congr
      intro ω
      exact pathGeneration_sq_eq_self_add_distinctAddressPairCount
        φ n F hF01 x ω
    _ = (∫⁻ ω, pathGeneration φ n F x ω ∂offspringFieldLaw μ) +
          (∫⁻ ω, pathGenerationDistinctAddressPairCount φ n F x ω
            ∂offspringFieldLaw μ) := by
      rw [lintegral_add_left' hcount.aemeasurable]

end ProbabilityTheory.BranchingRandomWalk.Spine

end
