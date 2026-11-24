/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Path.FamilySelection
public import Probability.BranchingRandomWalk.Spine.Tube.MRCA.PositiveDepth
public import Probability.BranchingRandomWalk.Spine.Tilted.FamilyCutoff
import Probability.BranchingRandomWalk.Spine.Tube.MRCA.Prefix

/-!
# MRCA estimates for whole-family selected path counts

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.Spine.affineTubeMRCAPairContribution_selectFamily_le`:
  let `μ_A = μ.map (Step.selectFamily A)` for a measurable family event `A`.
  If the original boundary-normalized spine has prefix mass at most `p` and shifted
  continuation mass at most `q`, then the actual selected-process MRCA term
  at depth `m` satisfies
  `C_(m,n)(μ_A) ≤ (∫_A crossWeight dμ) exp(2U-l-sm) q² p`.

Every selected ancestor and both selected descendant fields are retained in
`C_(m,n)(μ_A)`. Its continuations and weighted prefix are bounded by the
original process through the explicit whole-family selection coupling.
The spine law used for both probability bounds is that of `μ`, not a
renormalized or recentered selected increment law.

This is the family-cutoff second-moment step in B. Mallein,
*N-branching random walk with α-stable spine*, proof of Lemma 3.4,
arXiv:1503.03762v2, and *Necessary and sufficient conditions for the convergence
of the consistent maximal displacement of the branching random walk*, proof
of Lemma 3.4, arXiv:1510.00602v2.
-/

@[expose] public section
namespace ProbabilityTheory.BranchingRandomWalk.Spine
open MeasureTheory Combinatorics.Branching Combinatorics.UlamHarris
open BranchingProcess (offspringFieldLaw)
open ProbabilityTheory.RandomWalk
open scoped ENNReal Classical

set_option backward.isDefEq.respectTransparency false

private lemma childMeanOffDiagonal_selectFamily_le {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    {A : Set (Step ℕ X)} (hA : MeasurableSet A) (n : ℕ)
    {F : (Fin (n + 2) → ℝ) → ℝ≥0∞} (hF : Measurable F) (x : ℝ) (ξ : Step ℕ X) :
    pathGenerationChildMeanOffDiagonal φ (μ.map (Step.selectFamily A)) n F x ξ ≤
      pathGenerationChildMeanOffDiagonal φ μ n F x ξ := by
  have hchild (i : ℕ) :
      (∫⁻ η, pathGenerationChildObservable φ n F x i ξ η
        ∂offspringFieldLaw (μ.map (Step.selectFamily A))) ≤
      ∫⁻ η, pathGenerationChildObservable φ n F x i ξ η ∂offspringFieldLaw μ := by
    by_cases hi : survive ξ i
    · simp only [pathGenerationChildObservable, survivingPotentialTest, hi, ↓reduceIte]
      exact lintegral_pathGeneration_selectFamily_le φ μ hA n
        (hF.comp ((prependHistory_joint_measurable n).comp (measurable_const.prodMk measurable_id))) _
    · simp [pathGenerationChildObservable, survivingPotentialTest, hi]
  unfold pathGenerationChildMeanOffDiagonal
  apply tsum_le_tsum
  intro i
  apply tsum_le_tsum
  intro j
  dsimp only
  split_ifs with hij
  · exact mul_le_mul' (hchild i) (hchild j)
  · exact le_refl _

private lemma squarePrefixMass_eq_pathGeneration {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (m : ℕ) (F : (Fin (m + 1) → ℝ) → ℝ≥0∞)
    (x : ℝ) (ω : StepField ℕ X) :
    (∑' u : TreeNode ℕ, weightedPathGenerationTerm φ m F x u ω *
      ENNReal.ofReal (Real.exp (-pathPotential φ ω u))) =
      pathGeneration φ m (fun h => ENNReal.ofReal
        (Real.exp (-(2 * (h (Fin.last m) - x)))) * F h) x ω := by
  unfold pathGeneration
  apply tsum_congr
  intro u
  by_cases hu : u.length = m
  · by_cases hs : surviveAlong ω [] u
    · have hmem : ω ∈ {ω : StepField ℕ X | u.length = m ∧ surviveAlong ω [] u} := ⟨hu, hs⟩
      dsimp only [weightedPathGenerationTerm, pathGenerationTerm]
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
      have hend : pathHistory φ m x ω u (Fin.last m) = x + pathPotential φ ω u := by
        simpa only [Fin.last] using pathHistory_last φ m x ω u hu
      have hexp : -(2 * (pathHistory φ m x ω u (Fin.last m) - x)) =
          -pathPotential φ ω u + -pathPotential φ ω u := by
        rw [hend]
        ring
      rw [hexp, Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _)]
      ac_rfl
    · simp [weightedPathGenerationTerm, pathGenerationTerm, hu, hs]
  · simp [weightedPathGenerationTerm, pathGenerationTerm, hu]

private lemma squarePrefixMass_selectFamily_le {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    {A : Set (Step ℕ X)} (hA : MeasurableSet A) (m : ℕ)
    {F : (Fin (m + 1) → ℝ) → ℝ≥0∞} (hF : Measurable F) (x : ℝ) :
    (∫⁻ ω, ∑' u : TreeNode ℕ, weightedPathGenerationTerm φ m F x u ω *
      ENNReal.ofReal (Real.exp (-pathPotential φ ω u))
      ∂offspringFieldLaw (μ.map (Step.selectFamily A))) ≤
    ∫⁻ ω, ∑' u : TreeNode ℕ, weightedPathGenerationTerm φ m F x u ω *
      ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) ∂offspringFieldLaw μ := by
  simp_rw [squarePrefixMass_eq_pathGeneration]
  exact lintegral_pathGeneration_selectFamily_le φ μ hA m
    (by fun_prop) x

/-- Family selection is kept on the actual counted paths. Original-process
continuation and prefix bounds yield the restricted cross coefficient.
This is the all-ancestor family-cutoff estimate in B. Mallein,
*N-branching random walk with α-stable spine*, proof of Lemma 3.4
(arXiv:1503.03762v2). -/
theorem affineTubeMRCAPairContribution_selectFamily_le
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hboundary : HasBoundaryNormalization φ μ)
    {A : Set (Step ℕ X)} (hA : MeasurableSet A)
    (m n : ℕ) (lower drift width U : ℝ) (p q : ℝ≥0∞)
    (hprefix : tiltedIncrementFieldLaw φ μ
      {increment | history m 0 increment ∈ affineCorridorPrefix m lower drift width} ≤ p)
    (hcont : ∀ x y : ℝ, x + y ∈
        affineCorridorFirstWindow (lower + drift * (m : ℝ)) drift width →
      tiltedIncrementFieldLaw φ μ {increment | prependHistory x
        (history n (x + y) increment) ∈ affineCorridorHistoryEndpointCutoff n
          (lower + drift * (m : ℝ)) drift width U} ≤ q) :
    affineTubeMRCAPairContribution φ (μ.map (Step.selectFamily A)) m n
      0 lower drift width U ≤
      (∫⁻ ξ in A, crossPotentialWeight φ (-1) ξ ∂μ) *
        ENNReal.ofReal (Real.exp (2 * U - (lower + drift * (m : ℝ)))) * q ^ 2 * p := by
  let μA := μ.map (Step.selectFamily A)
  let F := (affineCorridorPrefix m lower drift width).indicator
    (fun _ => (1 : ℝ≥0∞))
  let G := (affineCorridorHistoryEndpointCutoff n
    (lower + drift * (m : ℝ)) drift width U).indicator (fun _ => (1 : ℝ≥0∞))
  let C := ENNReal.ofReal (Real.exp (2 * U)) * q ^ 2
  have hF : Measurable F := measurable_const.indicator
    (measurableSet_affineCorridorPrefix m lower drift width)
  have hG : Measurable G := measurable_const.indicator
    (measurableSet_affineCorridorHistoryEndpointCutoff n _ _ _ _)
  have hbound (x : ℝ) (ξ : Step ℕ X) :
      ENNReal.ofReal (Real.exp (2 * x)) * pathGenerationChildMeanOffDiagonal φ μA n G x ξ ≤
        C * crossPotentialWeight φ (-1) ξ := by
    refine (mul_le_mul' le_rfl (childMeanOffDiagonal_selectFamily_le φ μ hA n hG x ξ)).trans ?_
    exact pathGenerationChildMeanOffDiagonal_normalized_le_of_shiftedProbability
      φ μ hboundary n x U _
      (measurableSet_affineCorridorHistoryEndpointCutoff n _ _ _ _)
      (fun h hh => affineCorridorHistoryEndpointCutoff_terminalUpper n _ _ _ _ h hh)
      (affineCorridorFirstWindow (lower + drift * (m : ℝ)) drift width) q
      (fun h hh => affineCorridorHistoryEndpointCutoff_firstWindow n _ _ _ _ h hh)
      (hcont x) ξ
  rw [affineTubeMRCAPairContribution_eq_normalized]
  simp only [mul_zero, neg_zero, Real.exp_zero, ENNReal.ofReal_one, one_mul, zero_add]
  have hmajor :
      (∫⁻ ω, ∑' u : TreeNode ℕ, weightedPathGenerationTerm φ m F 0 u ω *
        ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) *
        ENNReal.ofReal (Real.exp (2 * pathPotential φ ω u)) *
        pathGenerationChildMeanOffDiagonal φ μA n G (pathPotential φ ω u) (ω u)
        ∂offspringFieldLaw μA) ≤
      C * ∫⁻ ω, weightedPrefixSquareCrossChildWeightSum φ m F 0 ω ∂offspringFieldLaw μA := by
    rw [← lintegral_const_mul C
      (show Measurable (weightedPrefixSquareCrossChildWeightSum φ m F 0) from by
        unfold weightedPrefixSquareCrossChildWeightSum
        exact Measurable.tsum fun u =>
          ((weightedPathGenerationTerm_measurable φ m hF 0 u).mul
            (pathPotential_measurable φ [] u).neg.exp.ennreal_ofReal).mul
              ((crossPotentialWeight_measurable φ (-1)).comp (measurable_pi_apply u)))]
    apply lintegral_mono
    intro ω
    unfold weightedPrefixSquareCrossChildWeightSum
    dsimp only
    rw [← ENNReal.tsum_mul_left]
    apply tsum_le_tsum
    intro u
    have h := mul_le_mul'
      (le_refl (weightedPathGenerationTerm φ m F 0 u ω *
        ENNReal.ofReal (Real.exp (-pathPotential φ ω u))))
      (hbound (pathPotential φ ω u) (ω u))
    simpa only [weightedPrefixSquareCrossChildWeightSum, mul_assoc, mul_left_comm,
      mul_comm] using h
  refine hmajor.trans ?_
  rw [lintegral_weightedPrefixSquareCrossChildWeightSum_eq_crossMoment_mul φ μA m F hF 0]
  have hmass := (squarePrefixMass_selectFamily_le φ μ hA m hF 0).trans
    (lintegral_weightedPrefixSquareMass_indicator_le_spineProbability φ μ hboundary m
      (affineCorridorPrefix m lower drift width)
      (measurableSet_affineCorridorPrefix m lower drift width) 0
      (lower + drift * (m : ℝ))
      (fun h hh => (hh (Fin.last m)).1))
  have hmass' :
      (∫⁻ ω, ∑' u : TreeNode ℕ, weightedPathGenerationTerm φ m F 0 u ω *
        ENNReal.ofReal (Real.exp (-pathPotential φ ω u)) ∂offspringFieldLaw μA) ≤
      ENNReal.ofReal (Real.exp (-(lower + drift * (m : ℝ)))) * p := by
    exact hmass.trans (by simpa only [zero_sub] using mul_le_mul' le_rfl hprefix)
  refine (mul_le_mul' le_rfl (mul_le_mul' le_rfl hmass')).trans_eq ?_
  rw [lintegral_crossPotentialWeight_selectFamily_eq_restrict φ (-1) μ hA]
  dsimp [C]
  rw [show 2 * U - (lower + drift * (m : ℝ)) =
      2 * U + -(lower + drift * (m : ℝ)) by ring,
    Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _)]
  ac_rfl

end ProbabilityTheory.BranchingRandomWalk.Spine
