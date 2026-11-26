import Probability.BranchingRandomWalk.Assumptions.SpinalWeightTail
import Probability.BranchingRandomWalk.Examples.SpinalWeight
import Probability.BranchingRandomWalk.Spine.Tilted.Marked
import Probability.BranchingRandomWalk.Spine.Path.ManyToOne.Marked
import Probability.BranchingRandomWalk.Spine.Tilted.FamilyCutoff
import Probability.BranchingRandomWalk.Spine.Tube.Corridor.SecondMoment.FiniteVariance
import Probability.Sequence.Maximal.QuadraticTail
import Probability.Sequence.IID.Basic
import Probability.BranchingProcess.Spine.LocalBias.Path

open MeasureTheory ProbabilityTheory
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.BranchingRandomWalk.Spine
open Combinatorics.Branching
open Filter
open scoped ENNReal Topology Classical

-- Perfectly correlated displacement and mark: the joint law is supported
-- on the diagonal, rather than constructed as a product of marginal laws.
example (μ : Measure (Step ℕ ℝ)) :
    tiltedMarkedPotentialLaw realPotential (-1) μ
      (fun p => p.1.potentialValue' realPotential p.2) =
      (tiltedPotentialLaw realPotential (-1) μ).map (fun x => (x, x)) := by
  have hr : Measurable (fun p : Step ℕ ℝ × ℕ =>
      p.1.potentialValue' realPotential p.2) :=
    measurable_from_prod_countable_left (fun i => Step.potentialValue'_measurable _ i)
  rw [← tiltedFamilyChildLaw_map_potential realPotential (-1) μ,
    Measure.map_map (by fun_prop) hr]
  rfl

-- The cutoff bound requires neither a finite untruncated cross weight nor
-- normalization of the cutoff offspring distribution.
example {X : Type*} [MeasurableSpace X] (φ : Potential X)
    (μ : Measure (Step ℕ X)) (hb : HasBoundaryNormalization φ μ) (α L : ℝ) :
    (∫⁻ ξ in {ξ | totalPotentialWeight φ (-1) ξ ≤ ENNReal.ofReal (Real.exp (α * L))},
      crossPotentialWeight φ (-1) ξ ∂μ) ≤ ENNReal.ofReal (Real.exp (α * L)) :=
  lintegral_crossPotentialWeight_on_totalWeight_le_of_boundary φ μ hb _

-- The weak tail hypothesis remains a tail hypothesis, not a log-moment
-- assumption. Only the displacement's ordinary second moment is supplied.
example {X : Type*} [MeasurableSpace X] (φ : Potential X)
    (μ : Measure (Step ℕ X)) (hb : HasBoundaryNormalization φ μ)
    (hsq : Integrable (fun x : ℝ => x ^ 2) (tiltedPotentialLaw φ (-1) μ)) :
    HasSpinalWeightTail φ μ ↔
      HasVanishingQuadraticTail (μ.withDensity (totalPotentialWeight φ (-1)))
        (logTotalPotentialWeight φ) :=
  hasSpinalWeightTail_iff_totalWeightTail φ μ hb hsq

-- On an IID sequence of *joint* increments, the path event A may depend
-- arbitrarily on the displacement and mark coordinates. No independence
-- between the two coordinates of one increment is used.
example (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν]
    (ht : HasVanishingQuadraticTail ν Prod.snd)
    {scale : ℕ → ℝ} (hs : Tendsto scale atTop atTop)
    {length : ℕ → ℕ} {C α p : ℝ} (hα : 0 < α) (hp : 0 < p)
    (hl : ∀ᶠ n in atTop, (length n : ℝ) ≤ C * scale n ^ 2) :
    ∀ᶠ n in atTop, ∀ A : Set (ℕ → ℝ × ℝ), p ≤ (iidSequenceLaw ν).real A →
      p / 2 ≤ (iidSequenceLaw ν).real
        (A ∩ {ω | ∀ j < length n, (ω j).2 ≤ α * scale n}) := by
  have hlaw (j : ℕ) : HasLaw (fun ω : ℕ → ℝ × ℝ => (ω j).2)
      (ν.map Prod.snd) (iidSequenceLaw ν) := by
    constructor
    · exact (measurable_snd.comp (measurable_pi_apply j)).aemeasurable
    · rw [show (fun ω : ℕ → ℝ × ℝ => (ω j).2) = Prod.snd ∘ (fun ω => ω j) from rfl,
        ← Measure.map_map measurable_snd (measurable_pi_apply j), iidSequenceLaw_map_apply]
  have htail : HasVanishingQuadraticTail (ν.map Prod.snd) id :=
    (hasVanishingQuadraticTail_map_iff Prod.snd measurable_snd id measurable_id).2 ht
  exact eventually_measureReal_inter_marks_ge hlaw htail hs hα hp hl

-- The general compensation retains complete generation histories, including
-- the families at every strict ancestor, instead of only ancestral states.
example {S ι : Type*} [MeasurableSpace S] [MeasurableSpace ι] [Countable ι]
    [MeasurableSingletonClass ι] (Q : Kernel S (Step ι S)) [IsMarkovKernel Q]
    (B : BranchingProcess.Spine.LocalBias S ι) (hB : B.IsAdmissible Q)
    (s : B.domain) (defaultChild : ι) (n : ℕ)
    (G : List ι → (List ι → Option S) → ℝ≥0∞)
    (hG : ∀ u, u.length = n → Measurable[BranchingProcess.State.treeFiltration n] (G u)) :
    (∫⁻ t, ∑' u : List ι, if u.length = n then
      B.addressWeight u.length u.get (BranchingProcess.State.treeHistory u.length t) *
        G u t else 0 ∂BranchingProcess.State.treeKernel Q (some s.1)) =
    ∫⁻ t, G (List.ofFn (BranchingProcess.Spine.spinePrefix defaultChild t n))
      (fun v => (t v).map (Sum.elim id Subtype.val))
      ∂BranchingProcess.Spine.LocalBias.treeKernel Q B hB (some (Sum.inr s)) :=
  BranchingProcess.Spine.LocalBias.lintegral_generationPayoff_eq Q B hB s defaultChild n G
    (fun u hu => by subst n; exact hG u rfl)

-- This is the actual count of surviving addresses whose *every* parent
-- family satisfies the logarithmic cutoff. It uses the original centered
-- spine, not a renormalized or recentered cutoff offspring law.
example {X : Type*} [MeasurableSpace X] (φ : Potential X)
    (μ : Measure (Step ℕ X)) [IsProbabilityMeasure μ]
    (hb : HasBoundaryNormalization φ μ) (n : ℕ) (a : ℝ) :
    (∫⁻ field, ∑' z : Fin n → ℕ,
      if Combinatorics.Branching.surviveAlong field [] (List.ofFn z) ∧
        ∀ j : Fin n, logTotalPotentialWeight φ
          (field ((List.ofFn z).take j)) ≤ a then (1 : ℝ≥0∞) else 0
      ∂BranchingProcess.offspringFieldLaw μ) =
      ∫⁻ sequence, ENNReal.ofReal (Real.exp (∑ j : Fin n, (sequence j).1)) *
        (if ∀ j : Fin n, (sequence j).2 ≤ a then 1 else 0)
        ∂iidSequenceLaw (tiltedMarkedPotentialLaw φ (-1) μ
          (fun p => logTotalPotentialWeight φ p.1)) := by
  classical
  have hm : Measurable (fun p : Step ℕ X × ℕ => logTotalPotentialWeight φ p.1) :=
    (logTotalPotentialWeight_measurable φ).comp measurable_fst
  have hs : MeasurableSet {records : Fin n → ℝ × ℝ | ∀ j, (records j).2 ≤ a} :=
    by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter fun j => measurableSet_le
        (show Measurable (fun records : Fin n → ℝ × ℝ => (records j).2) from
          measurable_snd.comp (measurable_pi_apply j)) measurable_const
  have hF : Measurable (fun records : Fin n → ℝ × ℝ =>
      if ∀ j, (records j).2 ≤ a then (1 : ℝ≥0∞) else 0) :=
    measurable_const.ite hs measurable_const
  have hi := markedPathManyToOne φ μ hb hm n hF
  refine Eq.trans ?_ hi
  apply lintegral_congr
  intro field
  apply tsum_congr
  intro z
  by_cases hs : surviveAlong field [] (List.ofFn z)
  · by_cases hc : ∀ j : Fin n, logTotalPotentialWeight φ
        (field ((List.ofFn z).take j)) ≤ a
    · simp [hs, hc, Combinatorics.UlamHarris.Mark.pathRecords]
    · simp [hs, hc, Combinatorics.UlamHarris.Mark.pathRecords]
  · simp [hs]


-- The empty path has one record vector, including when there are no child
-- labels. There is no hidden nonempty-slot or positive-time hypothesis.
example (μ : Measure (Step Empty ℝ)) [IsProbabilityMeasure μ] :
    (∫⁻ field, ∑' z : Fin 0 → Empty,
      if surviveAlong field [] (List.ofFn z) then (1 : ℝ≥0∞) else 0
      ∂BranchingProcess.offspringFieldLaw μ) = 1 := by
  simp [surviveAlong]

#print axioms ProbabilityTheory.BranchingProcess.Spine.LocalBias.lintegral_generationPayoff_eq
#print axioms ProbabilityTheory.BranchingProcess.Spine.LocalBias.lintegral_pathPayoff_eq
#print axioms MeasureTheory.HasVanishingQuadraticTail.scale_threshold
#print axioms MeasureTheory.hasVanishingQuadraticTail_map_iff
#print axioms MeasureTheory.hasVanishingQuadraticTail_max_const_iff
#print axioms MeasureTheory.HasVanishingQuadraticTail.mono
#print axioms MeasureTheory.HasVanishingQuadraticTail.add
#print axioms MeasureTheory.hasVanishingQuadraticTail_abs_of_integrable_sq
#print axioms MeasureTheory.hasVanishingQuadraticTail_add_iff_of_integrable_sq
#print axioms ProbabilityTheory.measureReal_exists_lt_le_of_hasLaw
#print axioms ProbabilityTheory.tendsto_measureReal_exists_lt_of_vanishingQuadraticTail
#print axioms ProbabilityTheory.eventually_measureReal_inter_marks_ge
#print axioms Combinatorics.Branching.crossPotentialWeight_le_totalPotentialWeight_sq
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_tiltedFamilyChildLaw
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_tiltedFamilyChildLaw_cancel
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.ae_tiltedFamilyChildLaw_survive
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.tiltedFamilyChildLaw_fst
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.tiltedFamilyChildLaw_apply_univ
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.tiltedFamilyChildLaw_isProbability
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.tiltedPotentialLaw_eq_sum
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.tiltedFamilyChildLaw_map_potential
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_tiltedPotentialLaw_cancel
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.tiltedMarkedPotentialLaw_fst
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.tiltedMarkedPotentialLaw_isProbability
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_tiltedMarkedPotentialLaw
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_tiltedMarkedPotentialLaw_cancel
#print axioms ProbabilityTheory.BranchingRandomWalk.relativeSpinalWeight_nonneg
#print axioms ProbabilityTheory.BranchingRandomWalk.ae_relativeSpinalWeight_nonneg
#print axioms ProbabilityTheory.BranchingRandomWalk.hasSpinalWeightTail_iff_totalWeightTail
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_crossPotentialWeight_on_totalWeight_le
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_crossPotentialWeight_on_totalWeight_le_of_boundary
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.tiltedFamilyChildLaw_restrict_family
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.exists_lintegral_pathGeneration_affineCorridor_sq_le_crossWeight_mul_exp_sum_of_finiteVariance
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.exists_lintegral_pathGeneration_affineCorridor_sq_le_exp_sum_of_finiteVariance

#print axioms MeasureTheory.Measure.pi_sum_map_withDensity
#print axioms MeasureTheory.Measure.lintegral_pi_sum_map_withDensity
#print axioms ProbabilityTheory.Tree.measurable_pathRecords
#print axioms ProbabilityTheory.Tree.lintegral_sum_weighted_pathRecords
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.familyPathManyToOne
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.markedPathManyToOne
#print axioms ProbabilityTheory.BranchingRandomWalk.Spine.pathHistory_eq_finitePrefix_records

#print axioms ProbabilityTheory.BranchingRandomWalk.Examples.exists_boundaryLaw_spinalWeightTail_not_finiteCrossWeight
#print axioms MeasureTheory.optionMeasurableSingletonClass
