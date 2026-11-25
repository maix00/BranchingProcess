/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Spine.Tilted.Slot
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# The joint tilted offspring family and child

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.Spine.lintegral_tiltedFamilyChildLaw_otherWeight`:
  `∫∑_(j≠i)wⱼ d μ̂(ξ,i)=∫∑_(i≠j)wᵢwⱼ dμ(ξ)` at every real tilt,
  without normalization or moment hypotheses.

In `ProbabilityTheory.BranchingRandomWalk.Spine`:

* `tiltedFamilyChildLaw φ θ μ` is the native weighted measure
  `μ̂(dξ, i) = w_(φ,θ)(ξ,i) μ(dξ)`, retaining the whole offspring family.
* `lintegral_tiltedFamilyChildLaw` gives
  `∫ F dμ̂ = ∫ ∑ᵢ wᵢ F(ξ,i) dμ`.
* `lintegral_tiltedFamilyChildLaw_cancel` gives the marked compensation
  `∫ exp(-θ X) F dμ̂ = ∫ ∑_(i surviving) F(ξ,i) dμ`.
* `ae_tiltedFamilyChildLaw_survive` gives existence of the selected child almost surely.
* `tiltedFamilyChildLaw_fst` identifies the family marginal with
  `μ.withDensity (totalPotentialWeight φ θ)`.
* `tiltedFamilyChildLaw_apply_univ` gives `μ̂(univ) = ∫ W dμ`.
* `tiltedFamilyChildLaw_isProbability` uses boundary normalization to give
  `μ̂(univ) = 1` at exponent `-1`.

This is the one-generation joint spinal law used by B. Mallein,
*N-branching random walk with α-stable spine* (2015), §2.1 and Theorem 1.1,
condition (1.9), arXiv:1503.03762. Keeping `ξ` is necessary: a reproduction
mark can depend on the entire family and be correlated with the chosen
displacement. The real increment law is its pushforward in `Tilted/Law.lean`;
there is a single underlying weighted family/child measure. No offspring
truncation or renormalization is made here.
-/

@[expose] public section
namespace ProbabilityTheory.BranchingRandomWalk.Spine
open MeasureTheory Combinatorics.Branching
open scoped ENNReal Classical

/-- The unnormalized exponential bias retains both the family and the selected slot. -/
noncomputable def tiltedFamilyChildLaw {ι X : Type*}
    [Countable ι] [MeasurableSpace ι] [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (μ : Measure (Step ι X)) : Measure (Step ι X × ι) :=
  Measure.sum fun i => (μ.withDensity (fun ξ => realizedPotentialWeight φ θ ξ i)).map
    (fun ξ => (ξ, i))

theorem lintegral_tiltedFamilyChildLaw {ι X : Type*}
    [Countable ι] [MeasurableSpace ι] [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (μ : Measure (Step ι X))
    {F : Step ι X × ι → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p, F p ∂tiltedFamilyChildLaw φ θ μ) =
      ∫⁻ ξ, ∑' i, realizedPotentialWeight φ θ ξ i * F (ξ, i) ∂μ := by
  rw [tiltedFamilyChildLaw, lintegral_sum_measure]
  have hslot (i : ι) :
      (∫⁻ p, F p ∂(μ.withDensity (fun ξ => realizedPotentialWeight φ θ ξ i)).map
        (fun ξ => (ξ, i))) =
        ∫⁻ ξ, realizedPotentialWeight φ θ ξ i * F (ξ, i) ∂μ := by
    rw [lintegral_map hF (show Measurable (fun ξ : Step ι X => (ξ, i)) from by fun_prop)]
    exact lintegral_withDensity_eq_lintegral_mul μ
      (realizedPotentialWeight_measurable φ θ i)
      (hF.comp (measurable_id.prodMk measurable_const))
  simp_rw [hslot]
  exact (lintegral_tsum (fun i => ((realizedPotentialWeight_measurable φ θ i).mul
    (hF.comp (measurable_id.prodMk measurable_const))).aemeasurable)).symm

/-- Compensation for a test of the whole family and selected slot. This is the
one-generation marked many-to-one formula, without normalizing the biased law. -/
theorem lintegral_tiltedFamilyChildLaw_cancel {ι X : Type*}
    [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (μ : Measure (Step ι X))
    {F : Step ι X × ι → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ p, ENNReal.ofReal (Real.exp (-θ * p.1.potentialValue' φ p.2)) * F p
      ∂tiltedFamilyChildLaw φ θ μ) =
      ∫⁻ ξ, ∑' i, if survive ξ i then F (ξ, i) else 0 ∂μ := by
  classical
  have hr : Measurable (fun p : Step ι X × ι => p.1.potentialValue' φ p.2) :=
    measurable_from_prod_countable_left (fun i => Step.potentialValue'_measurable φ i)
  have hG : Measurable (fun p : Step ι X × ι =>
      ENNReal.ofReal (Real.exp (-θ * p.1.potentialValue' φ p.2)) * F p) := by
    fun_prop
  rw [lintegral_tiltedFamilyChildLaw φ θ μ hG]
  apply lintegral_congr
  intro ξ
  apply tsum_congr
  intro i
  by_cases hi : survive ξ i
  · simp only [realizedPotentialWeight, hi, ↓reduceIte]
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    simp
  · simp [realizedPotentialWeight, hi]

/-- A selected slot is present almost everywhere under the biased law,
including before boundary normalization. -/
theorem ae_tiltedFamilyChildLaw_survive {ι X : Type*}
    [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι] [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (μ : Measure (Step ι X)) :
    ∀ᵐ p ∂tiltedFamilyChildLaw φ θ μ, survive p.1 p.2 := by
  have heval : Measurable (fun p : Step ι X × ι => p.1 p.2) :=
    measurable_from_prod_countable_left (fun i => measurable_pi_apply i)
  have hm : MeasurableSet {p : Step ι X × ι | survive p.1 p.2} := by
    convert heval measurableSet_option_none.compl using 1
    ext p
    simp [survive_iff_ne_none]
  rw [tiltedFamilyChildLaw, Measure.ae_sum_iff]
  intro i
  apply (ae_map_iff (by fun_prop) hm).mpr
  rw [ae_withDensity_iff (realizedPotentialWeight_measurable φ θ i)]
  apply Filter.Eventually.of_forall
  intro ξ hξ
  by_contra hs
  exact hξ (by simp [realizedPotentialWeight, hs])

theorem tiltedFamilyChildLaw_fst {ι X : Type*}
    [Countable ι] [MeasurableSpace ι] [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (μ : Measure (Step ι X)) :
    (tiltedFamilyChildLaw φ θ μ).map Prod.fst =
      μ.withDensity (totalPotentialWeight φ θ) := by
  apply Measure.ext
  intro A hA
  rw [Measure.map_apply measurable_fst hA, ← lintegral_indicator_one (hA.preimage measurable_fst),
    withDensity_apply _ hA]
  change (∫⁻ p, (Prod.fst ⁻¹' A).indicator (fun _ => (1 : ℝ≥0∞)) p
    ∂tiltedFamilyChildLaw φ θ μ) = _
  rw [lintegral_tiltedFamilyChildLaw φ θ μ
      (measurable_const.indicator (hA.preimage measurable_fst))]
  rw [← lintegral_indicator hA]
  apply lintegral_congr
  intro ξ
  by_cases hξ : ξ ∈ A <;> simp [hξ, totalPotentialWeight]

theorem tiltedFamilyChildLaw_apply_univ {ι X : Type*}
    [Countable ι] [MeasurableSpace ι] [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (μ : Measure (Step ι X)) :
    tiltedFamilyChildLaw φ θ μ Set.univ = ∫⁻ ξ, totalPotentialWeight φ θ ξ ∂μ := by
  have h := lintegral_tiltedFamilyChildLaw φ θ μ (F := fun _ => 1) measurable_const
  simpa only [lintegral_one, mul_one, totalPotentialWeight] using h

theorem tiltedFamilyChildLaw_isProbability {ι X : Type*}
    [Countable ι] [MeasurableSpace ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Step ι X)) (h : HasBoundaryNormalization φ μ) :
    IsProbabilityMeasure (tiltedFamilyChildLaw φ (-1) μ) :=
  ⟨(tiltedFamilyChildLaw_apply_univ φ (-1) μ).trans h⟩

/-- Under the family/child exponential bias, the expected weight of the other
children is the original off-diagonal pair weight. This identity holds at any
tilt and before normalization, as in the spinal decomposition of B. Mallein,
*N-branching random walk with α-stable spine*, §2.1, arXiv:1503.03762v2. -/
theorem lintegral_tiltedFamilyChildLaw_otherWeight
    {ι X : Type*} [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace X] (φ : Potential X) (θ : ℝ) (μ : Measure (Step ι X)) :
    (∫⁻ p : Step ι X × ι, ∑' j : ι,
      if j ≠ p.2 then realizedPotentialWeight φ θ p.1 j else 0
      ∂tiltedFamilyChildLaw φ θ μ) =
      ∫⁻ ξ, crossPotentialWeight φ θ ξ ∂μ := by
  have hm : Measurable (fun p : Step ι X × ι => ∑' j : ι,
      if j ≠ p.2 then realizedPotentialWeight φ θ p.1 j else 0) := by
    apply Measurable.tsum
    intro j
    apply Measurable.ite
    · exact by
        convert (measurable_snd (measurableSet_singleton j)).compl using 1
        ext p
        simp [ne_comm]
    · exact (realizedPotentialWeight_measurable φ θ j).comp measurable_fst
    · exact measurable_const
  rw [lintegral_tiltedFamilyChildLaw φ θ μ hm]
  apply lintegral_congr
  intro ξ
  unfold crossPotentialWeight
  apply tsum_congr
  intro i
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro j
  by_cases h : i = j <;> simp [h, Ne.symm]

end ProbabilityTheory.BranchingRandomWalk.Spine
