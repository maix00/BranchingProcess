/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Tilted.FamilyChild
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# The integrated tilted potential law

The conditional slot kernel is integrated against the raw branching law by
summing the pushforwards of its exponentially weighted slot measures.  Under
the boundary normalization this measure has total mass one.  This is the
one-step real increment law used by the many-to-one construction.

Write `w_{φ,θ}(ξ,i) = realizedPotentialWeight φ θ ξ i`,
`V_φ(ξ,i) = ξ.potentialValue' φ i`, and
`\widetilde μ_{φ,θ} = tiltedPotentialLaw φ θ μ`.  For measurable
`f : ℝ → [0,∞]`, its integral is

\[
\int^- f(y)\,\partial\widetilde\mu_{\varphi,\theta}(y)
=\int^-_{\xi}\sum'_{i:\iota}
  w_{\varphi,\theta}(\xi,i)f(V_\varphi(\xi,i))\,\partial\mu(\xi).
\]

On a measurable set `A`, the same measure is the sum of the weighted slot
pushforwards,

\[
\widetilde\mu_{\varphi,\theta}(A)
=\sum'_{i:\iota}\int^-_{\xi}
  \mathbf 1_A(V_\varphi(\xi,i))w_{\varphi,\theta}(\xi,i)\,
  \partial\mu(\xi).
\]

Its total mass is the expected total slot weight.  Thus the boundary
normalization \(\int^- W_{\varphi,-1}(\xi)\,\partial\mu(\xi)=1\), where
`W_{φ,θ}(ξ) = totalPotentialWeight φ θ ξ`, makes
`\widetilde μ_{φ,-1}` a probability measure.

## Public declarations

- `tiltedPotentialLaw`: the unnormalized measure on real potential increments
  obtained by integrating each surviving slot's exponential weight against
  the branching-step law.
- `tiltedFamilyChildLaw_map_potential` identifies the displacement marginal
  of the joint family/child measure with the scalar law.
- `tiltedPotentialLaw_eq_sum` gives its slot-sum expression;
  `tiltedPotentialLaw_apply`, `tiltedPotentialLaw_apply_univ`,
  `lintegral_tiltedPotentialLaw`, and `survivingPotentialTest`: setwise,
  total-mass, and nonnegative-integral formulas for that measure.
- `lintegral_tiltedPotentialLaw_cancel` and
  `tiltedPotentialLaw_isProbability`: boundary normalization cancels the
  exponential weight and makes the tilted potential law a probability measure.
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
    (φ : Potential X) (θ : ℝ) (μ : Measure (Combinatorics.Branching.Step ι X)) : Measure ℝ := by
  letI : MeasurableSpace ι := ⊤
  exact (tiltedFamilyChildLaw φ θ μ).map (fun p => p.1.potentialValue' φ p.2)

/-- The scalar increment law is the displacement marginal of the joint
family/child bias, expressed in its original sum-of-slot form. -/
theorem tiltedPotentialLaw_eq_sum {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (μ : Measure (Step ι X)) :
    tiltedPotentialLaw φ θ μ =
      Measure.sum fun i : ι => Measure.map
        (fun ξ : Step ι X => ξ.potentialValue' φ i)
        (μ.withDensity (fun ξ => realizedPotentialWeight φ θ ξ i)) := by
  let : MeasurableSpace ι := ⊤
  have : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  have hm : Measurable (fun p : Step ι X × ι => p.1.potentialValue' φ p.2) :=
    measurable_from_prod_countable_left (fun i => Step.potentialValue'_measurable φ i)
  unfold tiltedPotentialLaw tiltedFamilyChildLaw
  rw [Measure.map_sum hm.aemeasurable]
  congr 1
  funext i
  rw [Measure.map_map hm (show Measurable (fun ξ : Step ι X => (ξ, i)) from by fun_prop)]
  rfl

/-- The original increment measure is obtained by reading the selected potential
from the joint family/child law, for any discrete measurable slot space. -/
theorem tiltedFamilyChildLaw_map_potential {ι X : Type*}
    [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (μ : Measure (Step ι X)) :
    (tiltedFamilyChildLaw φ θ μ).map (fun p => p.1.potentialValue' φ p.2) =
      tiltedPotentialLaw φ θ μ := by
  have hm : Measurable (fun p : Step ι X × ι => p.1.potentialValue' φ p.2) :=
    measurable_from_prod_countable_left (fun i => Step.potentialValue'_measurable φ i)
  rw [tiltedFamilyChildLaw, Measure.map_sum hm.aemeasurable, tiltedPotentialLaw_eq_sum]
  congr 1
  funext i
  rw [Measure.map_map hm (show Measurable (fun ξ : Step ι X => (ξ, i)) from by fun_prop)]
  rfl

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
  rw [tiltedPotentialLaw_eq_sum, Measure.sum_apply _ hs]
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
  rw [tiltedPotentialLaw_eq_sum, lintegral_sum_measure]
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
  let : MeasurableSpace ι := ⊤
  have : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  have hr : Measurable (fun p : Step ι X × ι => p.1.potentialValue' φ p.2) :=
    measurable_from_prod_countable_left (fun i => Step.potentialValue'_measurable φ i)
  have htest : Measurable (fun y : ℝ =>
      ENNReal.ofReal (Real.exp (-θ * y)) * f y) := by fun_prop
  rw [tiltedPotentialLaw, lintegral_map htest hr]
  simpa only [survivingPotentialTest, Function.comp_def] using
    lintegral_tiltedFamilyChildLaw_cancel φ θ μ (hf.comp hr)

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
