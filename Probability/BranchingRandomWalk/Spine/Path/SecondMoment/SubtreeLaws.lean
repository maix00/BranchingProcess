/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Path.SecondMoment.Basic
import all Topology.Algebra.InfiniteSum.ENNReal.PairPartition

/-!
# Subtree laws and integrated second-moment identities

For distinct children $i\ne j$, their descendant fields are independent
under the branching field law. This gives product formulas for integrated
child observables and the exact integral recursion associated with the
pathwise pair decomposition in `SecondMoment.Basic`.

## Public declarations

- `distinct_child_subtreeFields_joint_law` states that the pair of descendant
  fields below distinct children has law
  $\operatorname{offspringFieldLaw}(\mu)\otimes\operatorname{offspringFieldLaw}(\mu)$.
  `lintegral_mul_distinct_child_subtrees_eq_product` gives the corresponding
  product formula for measurable nonnegative observables.
- `root_two_distinct_childFields_joint_law` adds the root reproduction step to
  this joint law, and `lintegral_root_product_distinct_child_subtrees` gives
  the conditional product integral.
- `lintegral_pathGeneration_childProduct_eq` specializes the factorization to
  two path-count observables.
- `lintegral_pathGenerationMRCAContribution_zero_eq_childMeanOffDiagonal`
  identifies the expected root-split contribution. The child-square integral
  and `lintegral_pathGeneration_succ_sq_eq_childPairRecursion` give the exact
  one-generation second-moment recursion.
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
/-- The descendant fields of two distinct first-generation children have the
product law. This is the subtree-independence input for the off-diagonal
terms in the second-moment decomposition. -/
theorem distinct_child_subtreeFields_joint_law
    {ι X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    (i j : ι) (hij : i ≠ j) :
    (offspringFieldLaw μ).map
        (fun ω => (subtreeStepField [i] ω, subtreeStepField [j] ω)) =
      (offspringFieldLaw μ).prod (offspringFieldLaw μ) := by
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
    (P := fun _ : Bool => offspringFieldLaw μ) (i := true) (j := false) (by decide)
  calc
    (offspringFieldLaw μ).map
        (fun ω => (subtreeStepField [i] ω, subtreeStepField [j] ω)) =
        ((offspringFieldLaw μ).map
          (ProbabilityTheory.BranchingRandomWalk.subtreeStepFieldVector roots)).map
            pairEval := by
      rw [Measure.map_map (by fun_prop)
        (ProbabilityTheory.BranchingRandomWalk.subtreeStepFieldVector_measurable roots)]
      rw [hcomp]
    _ = (Measure.infinitePi (fun _ : Bool => offspringFieldLaw μ)).map pairEval := by
      rw [hvector]
    _ = (offspringFieldLaw μ).prod (offspringFieldLaw μ) := by
      simpa [pairEval] using hpair

/-- Integrating a product of measurable observables in distinct child
subtrees gives the product of their integrals. This is the integral form of
`distinct_child_subtreeFields_joint_law`. -/
theorem lintegral_mul_distinct_child_subtrees_eq_product
    {ι X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    (i j : ι) (hij : i ≠ j)
    (f g : StepField ι X → ℝ≥0∞) (hf : Measurable f) (hg : Measurable g) :
    (∫⁻ ω, f (subtreeStepField [i] ω) * g (subtreeStepField [j] ω)
      ∂offspringFieldLaw μ) =
      (∫⁻ ω, f ω ∂offspringFieldLaw μ) * ∫⁻ ω, g ω ∂offspringFieldLaw μ := by
  let pair : StepField ι X → StepField ι X × StepField ι X := fun ω =>
    (subtreeStepField [i] ω, subtreeStepField [j] ω)
  have hpair : Measurable pair :=
    (subtreeStepField_measurable [i]).prodMk
      (subtreeStepField_measurable [j])
  have hproduct : Measurable (fun p : StepField ι X × StepField ι X =>
      f p.1 * g p.2) := (hf.comp measurable_fst).mul (hg.comp measurable_snd)
  calc
    (∫⁻ ω, f (subtreeStepField [i] ω) * g (subtreeStepField [j] ω)
        ∂offspringFieldLaw μ) =
        ∫⁻ p, f p.1 * g p.2 ∂(offspringFieldLaw μ).map pair := by
      exact (lintegral_map hproduct hpair).symm
    _ = (∫⁻ ω, f ω ∂offspringFieldLaw μ) *
          ∫⁻ ω, g ω ∂offspringFieldLaw μ := by
      rw [show pair = fun ω : StepField ι X =>
        (subtreeStepField [i] ω, subtreeStepField [j] ω) from rfl,
        distinct_child_subtreeFields_joint_law μ i j hij]
      exact lintegral_prod_mul hf.aemeasurable hg.aemeasurable

/-- The root reproduction step is independent of the two descendant fields
below distinct children; their full joint law is the corresponding triple
product. This is the branching-property law used to average a split pair. -/
theorem root_two_distinct_childFields_joint_law
    {ι X : Type*} [MeasurableSpace X]
    (μ : Measure (Step ι X)) [IsProbabilityMeasure μ]
    (i j : ι) (hij : i ≠ j) :
    (offspringFieldLaw μ).map
        (fun ω => (ω ([] : TreeNode ι),
          (subtreeStepField [i] ω, subtreeStepField [j] ω))) =
      μ.prod ((offspringFieldLaw μ).prod (offspringFieldLaw μ)) := by
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
      (offspringFieldLaw μ) := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left
      (ProbabilityTheory.BranchingRandomWalk.fixed_subtreeStepFieldVector_independent
        μ roots hlen) hrootPast.comap_le
  have hrootVector :
      (offspringFieldLaw μ).map rootVector =
        μ.prod (Measure.infinitePi (fun _ : Bool => offspringFieldLaw μ)) := by
    unfold rootVector vector
    rw [hind.map_prod_eq_prod_map_map
      (measurable_pi_apply ([] : TreeNode ι)).aemeasurable
      (ProbabilityTheory.BranchingRandomWalk.subtreeStepFieldVector_measurable
        roots).aemeasurable,
      offspringFieldLaw_coordinate μ ([] : TreeNode ι), hvector]
  have hinfinitePi := Measure.infinitePi_map_eval_prod
    (P := fun _ : Bool => offspringFieldLaw μ) (i := true) (j := false) (by decide)
  have hregroup :
      (μ.prod (Measure.infinitePi (fun _ : Bool => offspringFieldLaw μ))).map regroup =
        μ.prod ((offspringFieldLaw μ).prod (offspringFieldLaw μ)) := by
    change (μ.prod (Measure.infinitePi (fun _ : Bool => offspringFieldLaw μ))).map
      (Prod.map id evalPair) = _
    have hprod := Measure.map_prod_map μ
      (Measure.infinitePi (fun _ : Bool => offspringFieldLaw μ))
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
    (offspringFieldLaw μ).map
        (fun ω => (ω ([] : TreeNode ι),
          (subtreeStepField [i] ω, subtreeStepField [j] ω))) =
        (offspringFieldLaw μ).map (regroup ∘ rootVector) := by rw [hcomp]
    _ = ((offspringFieldLaw μ).map rootVector).map regroup :=
      (Measure.map_map hregroupMeas hrootVectorMeas).symm
    _ = μ.prod ((offspringFieldLaw μ).prod (offspringFieldLaw μ)) := by
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
      G (ω []) (subtreeStepField [j] ω) ∂offspringFieldLaw μ) =
      ∫⁻ ξ, (∫⁻ η, F ξ η ∂offspringFieldLaw μ) *
        (∫⁻ ζ, G ξ ζ ∂offspringFieldLaw μ) ∂μ := by
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
        G (ω []) (subtreeStepField [j] ω) ∂offspringFieldLaw μ) =
        ∫⁻ p, H p ∂(offspringFieldLaw μ).map triple := by
      exact (lintegral_map hH hTriple).symm
    _ = ∫⁻ p, H p ∂μ.prod ((offspringFieldLaw μ).prod (offspringFieldLaw μ)) := by
      rw [root_two_distinct_childFields_joint_law μ i j hij]
    _ = ∫⁻ ξ, (∫⁻ η, F ξ η ∂offspringFieldLaw μ) *
          (∫⁻ ζ, G ξ ζ ∂offspringFieldLaw μ) ∂μ := by
      rw [lintegral_prod H hH.aemeasurable]
      apply lintegral_congr
      intro ξ
      change (∫⁻ p, F ξ p.1 * G ξ p.2 ∂
        (offspringFieldLaw μ).prod (offspringFieldLaw μ)) = _
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
          (subtreeStepField [j] ω)) (ω []) j ∂offspringFieldLaw μ) =
      ∫⁻ ξ, (∫⁻ η, survivingPotentialTest φ
          (fun y => Spine.pathGeneration φ n
            (fun tail => F (prependHistory x tail)) (x + y) η) ξ i
          ∂offspringFieldLaw μ) *
        (∫⁻ ζ, survivingPotentialTest φ
          (fun y => Spine.pathGeneration φ n
            (fun tail => F (prependHistory x tail)) (x + y) ζ) ξ j
          ∂offspringFieldLaw μ) ∂μ := by
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
      ∂offspringFieldLaw μ) =
      ∫⁻ ξ, pathGenerationChildMeanOffDiagonal φ μ n F x ξ ∂μ := by
  classical
  let childObservable (i : ℕ) (ω : StepField ℕ X) : ℝ≥0∞ :=
    pathGenerationChildObservable φ n F x i (ω [])
      (subtreeStepField [i] ω)
  let childMean (i : ℕ) (ξ : Step ℕ X) : ℝ≥0∞ :=
    ∫⁻ η, pathGenerationChildObservable φ n F x i ξ η ∂offspringFieldLaw μ
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
    · simp only [pairTerm, ite_eq_left hij]
      exact (hchildObservable i).mul (hchildObservable j)
    · have hEq : i = j := by
        by_contra hne
        exact hij hne
      simp [pairTerm, hEq]
  have hmeanPairTerm (i j : ℕ) : Measurable (meanPairTerm i j) := by
    by_cases hij : i ≠ j
    · simp only [meanPairTerm, ite_eq_left hij]
      exact (hchildMean i).mul (hchildMean j)
    · have hEq : i = j := by
        by_contra hne
        exact hij hne
      simp [meanPairTerm, hEq]
  have hpairFactor (i j : ℕ) (hij : i ≠ j) :
      (∫⁻ ω, childObservable i ω * childObservable j ω
        ∂offspringFieldLaw μ) =
      ∫⁻ ξ, childMean i ξ * childMean j ξ ∂μ := by
    change (∫⁻ ω, pathGenerationChildObservable φ n F x i
        (ω []) (subtreeStepField [i] ω) *
      pathGenerationChildObservable φ n F x j
        (ω []) (subtreeStepField [j] ω) ∂offspringFieldLaw μ) =
      ∫⁻ ξ,
        (∫⁻ η, pathGenerationChildObservable φ n F x i ξ η
          ∂offspringFieldLaw μ) *
        (∫⁻ ζ, pathGenerationChildObservable φ n F x j ξ ζ
          ∂offspringFieldLaw μ) ∂μ
    exact lintegral_pathGeneration_childProduct_eq φ μ n F hF x i j hij
  have hterm (i j : ℕ) :
      (∫⁻ ω, pairTerm i j ω ∂offspringFieldLaw μ) =
        ∫⁻ ξ, meanPairTerm i j ξ ∂μ := by
    by_cases hij : i ≠ j
    · simp only [pairTerm, meanPairTerm, ite_eq_left hij]
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
      (∫⁻ ω, ∑' j, pairTerm i j ω ∂offspringFieldLaw μ) =
        ∑' j, ∫⁻ ω, pairTerm i j ω ∂offspringFieldLaw μ := by
    rw [lintegral_tsum]
    intro j
    exact (hpairTerm i j).aemeasurable
  have hleft :
      (∫⁻ ω, ∑' i, ∑' j, pairTerm i j ω ∂offspringFieldLaw μ) =
        ∑' i, ∑' j, ∫⁻ ω, pairTerm i j ω ∂offspringFieldLaw μ := by
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
        ∂offspringFieldLaw μ) =
        ∫⁻ ω, ∑' i, ∑' j, pairTerm i j ω ∂offspringFieldLaw μ := by
          apply lintegral_congr
          intro ω
          simp [pathGenerationMRCAContribution, pairTerm, childObservable]
    _ = ∑' i, ∑' j, ∫⁻ ω, pairTerm i j ω ∂offspringFieldLaw μ := hleft
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
          (subtreeStepField [i] ω)) (ω []) i) ^ 2 ∂offspringFieldLaw μ) =
      ∫⁻ ξ, ∫⁻ η, (survivingPotentialTest φ
          (fun y => Spine.pathGeneration φ n
            (fun tail => F (prependHistory x tail)) (x + y) η) ξ i) ^ 2
        ∂offspringFieldLaw μ ∂μ := by
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
      ∂offspringFieldLaw μ) =
      (∑' i, ∫⁻ ξ, ∫⁻ η,
        (pathGenerationChildObservable φ n F x i ξ η) ^ 2
          ∂offspringFieldLaw μ ∂μ) +
      ∑' i, ∑' j, if i ≠ j then
        ∫⁻ ξ, (∫⁻ η, pathGenerationChildObservable φ n F x i ξ η
              ∂offspringFieldLaw μ) *
          (∫⁻ ζ, pathGenerationChildObservable φ n F x j ξ ζ
              ∂offspringFieldLaw μ) ∂μ else 0 := by
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
    · simp only [ite_eq_left hij]
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
      (∫⁻ ω, ∑' i, (childCount i ω) ^ 2 ∂offspringFieldLaw μ) =
        ∑' i, ∫⁻ ω, (childCount i ω) ^ 2 ∂offspringFieldLaw μ := by
    rw [lintegral_tsum]
    intro i
    exact ((hchildCount i).pow_const 2).aemeasurable
  have hoffInnerIntegral (i : ℕ) :
      (∫⁻ ω, ∑' j, if i ≠ j then
        childCount i ω * childCount j ω else 0 ∂offspringFieldLaw μ) =
        ∑' j, ∫⁻ ω, if i ≠ j then
          childCount i ω * childCount j ω else 0 ∂offspringFieldLaw μ := by
    rw [lintegral_tsum]
    intro j
    exact (hoffTerm i j).aemeasurable
  have hoffIntegral :
      (∫⁻ ω, ∑' i, ∑' j, if i ≠ j then
        childCount i ω * childCount j ω else 0 ∂offspringFieldLaw μ) =
        ∑' i, ∑' j, ∫⁻ ω, if i ≠ j then
          childCount i ω * childCount j ω else 0 ∂offspringFieldLaw μ := by
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
        ∂offspringFieldLaw μ) =
        ∫⁻ ω, (∑' i, (childCount i ω) ^ 2) +
          (∑' i, ∑' j, if i ≠ j then
            childCount i ω * childCount j ω else 0) ∂offspringFieldLaw μ := by
      apply lintegral_congr
      intro ω
      exact hpoint ω
    _ = (∫⁻ ω, ∑' i, (childCount i ω) ^ 2 ∂offspringFieldLaw μ) +
        ∫⁻ ω, ∑' i, ∑' j, if i ≠ j then
          childCount i ω * childCount j ω else 0 ∂offspringFieldLaw μ := by
      rw [lintegral_add_left' hdiagSum.aemeasurable]
    _ = (∑' i, ∫⁻ ω, (childCount i ω) ^ 2 ∂offspringFieldLaw μ) +
        ∑' i, ∑' j, ∫⁻ ω, if i ≠ j then
          childCount i ω * childCount j ω else 0 ∂offspringFieldLaw μ := by
      rw [hdiagIntegral, hoffIntegral]
    _ = (∑' i, ∫⁻ ξ, ∫⁻ η,
          (pathGenerationChildObservable φ n F x i ξ η) ^ 2
            ∂offspringFieldLaw μ ∂μ) +
        ∑' i, ∑' j, if i ≠ j then
          ∫⁻ ξ, (∫⁻ η, pathGenerationChildObservable φ n F x i ξ η
                ∂offspringFieldLaw μ) *
            (∫⁻ ζ, pathGenerationChildObservable φ n F x j ξ ζ
                ∂offspringFieldLaw μ) ∂μ else 0 := by
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

end
