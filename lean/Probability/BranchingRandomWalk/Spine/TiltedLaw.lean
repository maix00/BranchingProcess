module

public import Probability.BranchingRandomWalk.Spine.TiltedSlot
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# The integrated tilted potential law

The conditional slot kernel is integrated against the raw branching law by
summing the pushforwards of its exponentially weighted slot measures.  Under
the boundary normalization this measure has total mass one.  This is the
one-step real increment law used by the many-to-one construction.
-/

open MeasureTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching MeasureTheory

/-- The unnormalized exponentially tilted law of the real potential of one
child, integrated over the raw branching-step law. -/
noncomputable def tiltedPotentialLaw {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (μ : Measure (Combinatorics.Branching.Step ι X)) : Measure ℝ :=
  Measure.sum fun i : ι =>
    Measure.map (fun ξ : Combinatorics.Branching.Step ι X => ξ.potentialValue' φ i)
      (μ.withDensity (fun ξ => realizedPotentialWeight φ θ ξ i))

/-- Evaluation of the integrated tilted law on a measurable set.  Slot
multiplicity is retained by the outer countable sum. -/
theorem tiltedPotentialLaw_apply {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (μ : Measure (Combinatorics.Branching.Step ι X))
    (s : Set ℝ) (hs : MeasurableSet s) :
    tiltedPotentialLaw φ θ μ s =
      ∑' i : ι, ∫⁻ ξ in
        (fun ξ : Combinatorics.Branching.Step ι X => ξ.potentialValue' φ i) ⁻¹' s,
        realizedPotentialWeight φ θ ξ i ∂μ := by
  rw [tiltedPotentialLaw, Measure.sum_apply _ hs]
  apply tsum_congr
  intro i
  rw [Measure.map_apply (Step.potentialValue'_measurable φ i) hs,
    withDensity_apply _
      (hs.preimage (Step.potentialValue'_measurable φ i))]

/-- The total mass is the expected total exponential child weight. -/
theorem tiltedPotentialLaw_apply_univ {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (μ : Measure (Combinatorics.Branching.Step ι X)) :
    tiltedPotentialLaw φ θ μ Set.univ =
      ∫⁻ ξ, totalPotentialWeight φ θ ξ ∂μ := by
  rw [tiltedPotentialLaw_apply φ θ μ Set.univ MeasurableSet.univ]
  simp only [Set.preimage_univ, Measure.restrict_univ]
  symm
  unfold totalPotentialWeight
  rw [lintegral_tsum]
  intro i
  exact (realizedPotentialWeight_measurable φ θ i).aemeasurable

/-- One-generation weighted many-to-one identity for nonnegative measurable
tests.  It is stated before normalization, so the same formula applies at
arbitrary tilt parameters. -/
theorem lintegral_tiltedPotentialLaw {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (μ : Measure (Combinatorics.Branching.Step ι X))
    (f : ℝ → ENNReal) (hf : Measurable f) :
    ∫⁻ y, f y ∂tiltedPotentialLaw φ θ μ =
      ∫⁻ ξ, ∑' i : ι,
        realizedPotentialWeight φ θ ξ i * f (ξ.potentialValue' φ i) ∂μ := by
  rw [tiltedPotentialLaw, lintegral_sum_measure]
  have hslot : ∀ i : ι,
      (∫⁻ y, f y ∂Measure.map
          (fun ξ : Combinatorics.Branching.Step ι X =>
            ξ.potentialValue' φ i)
          (μ.withDensity (fun ξ => realizedPotentialWeight φ θ ξ i))) =
        ∫⁻ ξ, realizedPotentialWeight φ θ ξ i *
          f (ξ.potentialValue' φ i) ∂μ := by
    intro i
    rw [lintegral_map hf (Step.potentialValue'_measurable φ i)]
    simpa [Function.comp_def] using
      (lintegral_withDensity_eq_lintegral_mul μ
        (realizedPotentialWeight_measurable φ θ i)
        (hf.comp (Step.potentialValue'_measurable φ i)))
  simp_rw [hslot]
  symm
  rw [lintegral_tsum]
  intro i
  exact ((realizedPotentialWeight_measurable φ θ i).mul
    (hf.comp (Step.potentialValue'_measurable φ i))).aemeasurable

noncomputable def survivingPotentialTest {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (f : ℝ → ENNReal)
    (ξ : Combinatorics.Branching.Step ι X) (i : ι) : ENNReal := by
  classical
  exact if survive ξ i then f (ξ.potentialValue' φ i) else 0

/-- Reverse one-generation identity: the reciprocal exponential factor
cancels the tilt and leaves the unweighted sum over surviving children. -/
theorem lintegral_tiltedPotentialLaw_cancel {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (μ : Measure (Combinatorics.Branching.Step ι X))
    (f : ℝ → ENNReal) (hf : Measurable f) :
    (∫⁻ y, ENNReal.ofReal (Real.exp (-θ * y)) * f y
        ∂tiltedPotentialLaw φ θ μ) =
      ∫⁻ ξ, ∑' i : ι,
        survivingPotentialTest φ f ξ i ∂μ := by
  classical
  have htest : Measurable
      (fun y : ℝ => ENNReal.ofReal (Real.exp (-θ * y)) * f y) :=
    by fun_prop
  rw [lintegral_tiltedPotentialLaw φ θ μ _ htest]
  congr 1
  funext ξ
  apply tsum_congr
  intro i
  unfold survivingPotentialTest
  by_cases hi : survive ξ i
  · simp only [realizedPotentialWeight, hi, ↓reduceIte]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (le_of_lt (Real.exp_pos _)),
      ← Real.exp_add]
    have hzero : θ * ξ.potentialValue' φ i +
        -θ * ξ.potentialValue' φ i = 0 := by ring
    rw [hzero]
    simp
  · simp [realizedPotentialWeight, hi]

/-- Boundary normalization makes the integrated tilted potential law a
probability measure. -/
theorem tiltedPotentialLaw_isProbability {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X))
    (hboundary : HasBoundaryNormalization φ μ) :
    IsProbabilityMeasure (tiltedPotentialLaw φ (-1) μ) := by
  apply IsProbabilityMeasure.mk
  rw [tiltedPotentialLaw_apply_univ]
  exact hboundary

end ProbabilityTheory.BranchingRandomWalk.Spine
