import Probability.BranchingRandomWalk.Spine.Path.Branching
import Probability.BranchingRandomWalk.Spine.Path.IncrementSplit
import Probability.BranchingRandomWalk.Spine.RandomWalk

/-!
# Path-functional many-to-one identities

The test function sees the complete ancestral position history at times
`0, ..., n`.  The two identities correspond to the exponentially weighted
and unweighted branching sums.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

/-- Weighted path-functional many-to-one identity for the pre-sampled
branching field. -/
theorem weightedPathManyToOneCore
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    [IsProbabilityMeasure μ] (hboundary : HasBoundaryNormalization φ μ) :
    ∀ (n : ℕ) {F : (Fin (n + 1) → ℝ) → ENNReal}, Measurable F → ∀ x : ℝ,
      (∫⁻ ω, weightedPathGeneration φ n F x ω ∂stepFieldLaw μ) =
        ∫⁻ increment, F (spineHistory n x increment)
          ∂tiltedIncrementFieldLaw φ μ := by
  intro n
  induction n with
  | zero =>
      intro F hF x
      let _ : IsProbabilityMeasure (tiltedIncrementFieldLaw φ μ) :=
        tiltedIncrementFieldLaw_isProbability φ μ hboundary
      have hhistory : ∀ increment : ℕ → ℝ,
          spineHistory 0 x increment = (fun _ : Fin 1 => x) := by
        intro increment
        funext k
        have hk : k = 0 := Fin.eq_zero k
        subst k
        exact spineHistory_zero 0 x increment
      simp_rw [hhistory]
      simp
  | succ n ih =>
      intro F hF x
      let ν : Measure ℝ := tiltedPotentialLaw φ (-1) μ
      let P : Measure (ℕ → ℝ) := tiltedIncrementFieldLaw φ μ
      let G : ℝ → ENNReal := fun y =>
        ∫⁻ tail, F (prependHistory x (spineHistory n (x + y) tail)) ∂P
      let _ : IsProbabilityMeasure ν :=
        tiltedPotentialLaw_isProbability φ μ hboundary
      let _ : IsProbabilityMeasure P :=
        tiltedIncrementFieldLaw_isProbability φ μ hboundary
      have htailF : Measurable
          (fun tail : Fin (n + 1) → ℝ => F (prependHistory x tail)) :=
        hF.comp ((prependHistory_joint_measurable n).comp
          (measurable_const.prodMk measurable_id))
      have hG : Measurable G := by
        apply Measurable.lintegral_prod_right
        apply hF.comp
        have hx : Measurable
            (fun _ : ℝ × (ℕ → ℝ) => x) := measurable_const
        have hcurrent : Measurable
            (fun z : ℝ × (ℕ → ℝ) => x + z.1) :=
          hx.add measurable_fst
        have hspine : Measurable (fun z : ℝ × (ℕ → ℝ) =>
            spineHistory n (x + z.1) z.2) :=
          (spineHistory_joint_measurable n).comp
            (hcurrent.prodMk measurable_snd)
        have h := (prependHistory_joint_measurable n).comp
          (hx.prodMk hspine)
        simpa [Function.comp_def] using h
      calc
        (∫⁻ ω, weightedPathGeneration φ (n + 1) F x ω
            ∂stepFieldLaw μ) =
            ∑' i : ι, ∫⁻ ω,
              realizedPotentialWeight φ (-1) (ω []) i *
                weightedPathGeneration φ n
                  (fun tail => F (prependHistory x tail))
                  (x + (ω []).potentialValue' φ i)
                  (subtreeStepField [i] ω) ∂stepFieldLaw μ := by
          simp_rw [weightedPathGeneration_succ]
          rw [lintegral_tsum]
          intro i
          exact (((realizedPotentialWeight_measurable φ (-1) i).comp
              (measurable_pi_apply ([] : TreeNode ι))).mul
            ((weightedPathGeneration_joint_measurable φ n htailF).comp
              (((measurable_const.add
                ((Step.potentialValue'_measurable φ i).comp
                  (measurable_pi_apply ([] : TreeNode ι)))).prodMk
                (subtreeStepField_measurable [i]))))).aemeasurable
        _ = ∑' i : ι, ∫⁻ ξ,
              realizedPotentialWeight φ (-1) ξ i *
                G (ξ.potentialValue' φ i) ∂μ := by
          apply tsum_congr
          intro i
          let H : (Combinatorics.Branching.Step ι X ×
              Combinatorics.Branching.StepField ι X) → ENNReal := fun z =>
            realizedPotentialWeight φ (-1) z.1 i *
              weightedPathGeneration φ n
                (fun tail => F (prependHistory x tail))
                (x + z.1.potentialValue' φ i) z.2
          have hH : Measurable H := by
            apply ((realizedPotentialWeight_measurable φ (-1) i).comp
              measurable_fst).mul
            exact (weightedPathGeneration_joint_measurable φ n htailF).comp
              (((measurable_const.add
                ((Step.potentialValue'_measurable φ i).comp measurable_fst))).prodMk
                measurable_snd)
          have hpair : Measurable
              (fun ω : Combinatorics.Branching.StepField ι X =>
                (ω ([] : TreeNode ι), subtreeStepField [i] ω)) :=
            (measurable_pi_apply ([] : TreeNode ι)).prodMk
              (subtreeStepField_measurable [i])
          calc
            (∫⁻ ω, realizedPotentialWeight φ (-1) (ω []) i *
                weightedPathGeneration φ n
                  (fun tail => F (prependHistory x tail))
                  (x + (ω []).potentialValue' φ i)
                  (subtreeStepField [i] ω) ∂stepFieldLaw μ) =
                ∫⁻ z, H z ∂(stepFieldLaw μ).map
                  (fun ω => (ω ([] : TreeNode ι),
                    subtreeStepField [i] ω)) := by
              exact (lintegral_map hH hpair).symm
            _ = ∫⁻ z, H z ∂μ.prod (stepFieldLaw μ) := by
              rw [root_subtreeStepField_joint_law μ i]
            _ = ∫⁻ ξ, ∫⁻ η, H (ξ, η) ∂stepFieldLaw μ ∂μ := by
              exact lintegral_prod H hH.aemeasurable
            _ = ∫⁻ ξ, realizedPotentialWeight φ (-1) ξ i *
                  G (ξ.potentialValue' φ i) ∂μ := by
              apply lintegral_congr
              intro ξ
              change (∫⁻ η, realizedPotentialWeight φ (-1) ξ i *
                  weightedPathGeneration φ n
                    (fun tail => F (prependHistory x tail))
                    (x + ξ.potentialValue' φ i) η ∂stepFieldLaw μ) = _
              rw [lintegral_const_mul _
                (weightedPathGeneration_measurable φ n htailF
                  (x + ξ.potentialValue' φ i))]
              rw [ih htailF (x + ξ.potentialValue' φ i)]
        _ = ∫⁻ ξ, ∑' i : ι,
              realizedPotentialWeight φ (-1) ξ i *
                G (ξ.potentialValue' φ i) ∂μ := by
          rw [lintegral_tsum]
          intro i
          exact ((realizedPotentialWeight_measurable φ (-1) i).mul
            (hG.comp (Step.potentialValue'_measurable φ i))).aemeasurable
        _ = ∫⁻ y, G y ∂ν := by
          exact (lintegral_tiltedPotentialLaw φ (-1) μ G hG).symm
        _ = ∫⁻ increment, F (spineHistory (n + 1) x increment) ∂P := by
          exact (lintegral_spineHistory_succ ν n x hF).symm

/-- Unweighted path-functional many-to-one identity, with the reciprocal
exponential weight determined by the terminal spine displacement. -/
theorem pathManyToOneCore
    {ι X : Type*} [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    [IsProbabilityMeasure μ] (hboundary : HasBoundaryNormalization φ μ)
    (n : ℕ) {F : (Fin (n + 1) → ℝ) → ENNReal} (hF : Measurable F)
    (x : ℝ) :
    (∫⁻ ω, pathGeneration φ n F x ω ∂stepFieldLaw μ) =
      ∫⁻ increment,
        ENNReal.ofReal (Real.exp (tiltedPosition n increment)) *
          F (spineHistory n x increment)
        ∂tiltedIncrementFieldLaw φ μ := by
  let weightedTest : (Fin (n + 1) → ℝ) → ENNReal := fun history =>
    ENNReal.ofReal
      (Real.exp (history ⟨n, Nat.lt_succ_self n⟩ - x)) * F history
  have hweightedTest : Measurable weightedTest := by
    exact ((measurable_pi_apply (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1))).sub
      measurable_const).exp.ennreal_ofReal.mul hF
  simp_rw [pathGeneration_eq_weightedPathGeneration]
  rw [weightedPathManyToOneCore φ μ hboundary n hweightedTest x]
  apply lintegral_congr
  intro increment
  unfold weightedTest
  rw [spineHistory_last]
  rw [show x + tiltedPosition n increment - x =
    tiltedPosition n increment by ring]

/-- Path-functional weighted many-to-one with separate mark and position
spaces.  The displacement map is only required to be measurable. -/
theorem weightedPathManyToOne
    {ι Mark Position : Type*} [Countable ι]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (d : Mark → Position) (hd : Measurable d)
    (potential : Potential Position)
    (μ : Measure (Combinatorics.Branching.Step ι Mark))
    [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization (potential.comp d hd) μ)
    (n : ℕ) {F : (Fin (n + 1) → ℝ) → ENNReal} (hF : Measurable F)
    (x : ℝ) :
    (∫⁻ ω, weightedPathGeneration (potential.comp d hd) n F x ω
        ∂stepFieldLaw μ) =
      ∫⁻ increment, F (spineHistory n x increment)
        ∂(spineRandomWalk (potential.comp d hd) μ hboundary).incrementLaw :=
  weightedPathManyToOneCore (potential.comp d hd) μ hboundary n hF x

/-- Path-functional unweighted many-to-one with separate mark and position
spaces. -/
theorem pathManyToOne
    {ι Mark Position : Type*} [Countable ι]
    [MeasurableSpace Mark] [MeasurableSpace Position]
    (d : Mark → Position) (hd : Measurable d)
    (potential : Potential Position)
    (μ : Measure (Combinatorics.Branching.Step ι Mark))
    [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization (potential.comp d hd) μ)
    (n : ℕ) {F : (Fin (n + 1) → ℝ) → ENNReal} (hF : Measurable F)
    (x : ℝ) :
    (∫⁻ ω, pathGeneration (potential.comp d hd) n F x ω
        ∂stepFieldLaw μ) =
      ∫⁻ increment,
        ENNReal.ofReal (Real.exp
          ((spineRandomWalk (potential.comp d hd) μ hboundary).positionAt
            id n increment)) *
          F (spineHistory n x increment)
        ∂(spineRandomWalk (potential.comp d hd) μ hboundary).incrementLaw := by
  rw [spineRandomWalk_incrementLaw]
  simpa only [spineRandomWalk_positionAt] using
    pathManyToOneCore (potential.comp d hd) μ hboundary n hF x

end ProbabilityTheory.BranchingRandomWalk.Spine
