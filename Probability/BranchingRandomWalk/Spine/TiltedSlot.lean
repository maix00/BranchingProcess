/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.ExponentialWeight
public import Combinatorics.BranchingWalk.Step.Measurability
public import Probability.BranchingRandomWalk.Assumptions.Structural
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Combinatorics.BranchingWalk.Step.Basic

/-!
# The normalized spine kernel

For a countable child-slot type `ι`, a measurable mark space `X`, and a real
potential `φ : X → ℝ`, exponential weights define a probability mass function
on the surviving slots whenever their total weight is finite and nonzero.  The
potential of the selected mark gives the corresponding real spine increment.
No ordering of the raw branching law is used here.
-/

open MeasureTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching MeasureTheory
open scoped Classical

noncomputable def tiltedSlotPMF {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (ξ : Combinatorics.Branching.Step ι X)
    (hzero : totalPotentialWeight φ θ ξ ≠ 0)
    (hfinite : totalPotentialWeight φ θ ξ ≠ ∞) : PMF ι :=
  PMF.normalize (realizedPotentialWeight φ θ ξ) hzero hfinite

instance tiltedSlotPMF_isProbability {ι X : Type*}
    [MeasurableSpace ι] [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (ξ : Combinatorics.Branching.Step ι X)
    (hzero : totalPotentialWeight φ θ ξ ≠ 0)
    (hfinite : totalPotentialWeight φ θ ξ ≠ ∞) :
    IsProbabilityMeasure (tiltedSlotPMF φ θ ξ hzero hfinite).toMeasure := by
  infer_instance

theorem tiltedSlotPMF_apply {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (ξ : Combinatorics.Branching.Step ι X)
    (hzero : totalPotentialWeight φ θ ξ ≠ 0)
    (hfinite : totalPotentialWeight φ θ ξ ≠ ∞) (i : ι) :
    tiltedSlotPMF φ θ ξ hzero hfinite i =
      realizedPotentialWeight φ θ ξ i * (totalPotentialWeight φ θ ξ)⁻¹ := by
  exact PMF.normalize_apply hzero hfinite i

/-- A total measurable version of the normalized coordinate.  Outside the
finite positive normalizer domain it is set to zero. -/
noncomputable def measurableTiltedWeight {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (i : ι) (ξ : Combinatorics.Branching.Step ι X) : ENNReal :=
  if totalPotentialWeight φ θ ξ = 0 ∨ totalPotentialWeight φ θ ξ = ∞ then 0
  else realizedPotentialWeight φ θ ξ i * (totalPotentialWeight φ θ ξ)⁻¹

def finitePositiveWeightDomain {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) : Set (Combinatorics.Branching.Step ι X) :=
  {ξ | totalPotentialWeight φ θ ξ ≠ 0 ∧
    totalPotentialWeight φ θ ξ ≠ ∞}

theorem finitePositiveWeightDomain_measurable {ι X : Type*}
    [Countable ι] [MeasurableSpace X] (φ : Potential X) (θ : ℝ) :
    MeasurableSet (finitePositiveWeightDomain (ι := ι) φ θ) := by
  exact (totalPotentialWeight_measurable φ θ
    (measurableSet_singleton 0)).compl.inter
      (totalPotentialWeight_measurable φ θ
        (measurableSet_singleton ∞)).compl

theorem measurableTiltedWeight_measurable {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (i : ι) :
    Measurable (measurableTiltedWeight φ θ i) := by
  classical
  unfold measurableTiltedWeight
  apply Measurable.ite
  · exact (totalPotentialWeight_measurable φ θ
      (measurableSet_singleton 0)).union
      (totalPotentialWeight_measurable φ θ
        (measurableSet_singleton ∞))
  · exact measurable_const
  · exact (realizedPotentialWeight_measurable φ θ i).mul
      (totalPotentialWeight_measurable φ θ).inv

theorem measurableTiltedWeight_eq_pmf {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (i : ι) (ξ : Combinatorics.Branching.Step ι X)
    (hzero : totalPotentialWeight φ θ ξ ≠ 0)
    (hfinite : totalPotentialWeight φ θ ξ ≠ ∞) :
    measurableTiltedWeight φ θ i ξ =
      tiltedSlotPMF φ θ ξ hzero hfinite i := by
  simp [measurableTiltedWeight, hzero, hfinite,
    tiltedSlotPMF_apply]

theorem tiltedSlotPMF_sum {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (ξ : Combinatorics.Branching.Step ι X)
    (hzero : totalPotentialWeight φ θ ξ ≠ 0)
    (hfinite : totalPotentialWeight φ θ ξ ≠ ∞) :
    ∑' i : ι, tiltedSlotPMF φ θ ξ hzero hfinite i = 1 := by
  simp

theorem tiltedSlotPMF_tsum_weighted {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (ξ : Combinatorics.Branching.Step ι X)
    (hzero : totalPotentialWeight φ θ ξ ≠ 0)
    (hfinite : totalPotentialWeight φ θ ξ ≠ ∞)
    (g : ι → ENNReal) :
    (∑' i : ι, tiltedSlotPMF φ θ ξ hzero hfinite i * g i) =
      (totalPotentialWeight φ θ ξ)⁻¹ *
        ∑' i : ι, realizedPotentialWeight φ θ ξ i * g i := by
  simp_rw [tiltedSlotPMF_apply φ θ ξ hzero hfinite]
  have hcomm : ∀ i : ι,
      realizedPotentialWeight φ θ ξ i *
          (totalPotentialWeight φ θ ξ)⁻¹ * g i =
        (totalPotentialWeight φ θ ξ)⁻¹ *
          (realizedPotentialWeight φ θ ξ i * g i) := by
    intro i
    ac_rfl
  simp_rw [hcomm]
  rw [ENNReal.tsum_mul_left]

/-- Conditional law of the real potential of the selected child mark. -/
noncomputable def tiltedPotentialPMF {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (ξ : Combinatorics.Branching.Step ι X)
    (hzero : totalPotentialWeight φ θ ξ ≠ 0)
    (hfinite : totalPotentialWeight φ θ ξ ≠ ∞) : PMF ℝ :=
  PMF.map (fun i => ξ.potentialValue' φ i)
    (tiltedSlotPMF φ θ ξ hzero hfinite)

theorem tiltedPotentialPMF_toMeasure_map {ι X : Type*}
    [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (ξ : Combinatorics.Branching.Step ι X)
    (hzero : totalPotentialWeight φ θ ξ ≠ 0)
    (hfinite : totalPotentialWeight φ θ ξ ≠ ∞) :
    (tiltedPotentialPMF φ θ ξ hzero hfinite).toMeasure =
      Measure.map (fun i => ξ.potentialValue' φ i)
        (tiltedSlotPMF φ θ ξ hzero hfinite).toMeasure := by
  symm
  exact PMF.toMeasure_map _ _ (measurable_of_countable _)

instance tiltedPotentialPMF_isProbability {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (ξ : Combinatorics.Branching.Step ι X)
    (hzero : totalPotentialWeight φ θ ξ ≠ 0)
    (hfinite : totalPotentialWeight φ θ ξ ≠ ∞) :
    IsProbabilityMeasure
      (tiltedPotentialPMF φ θ ξ hzero hfinite).toMeasure := by
  infer_instance

theorem tiltedPotentialPMF_apply {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (ξ : Combinatorics.Branching.Step ι X)
    (hzero : totalPotentialWeight φ θ ξ ≠ 0)
    (hfinite : totalPotentialWeight φ θ ξ ≠ ∞) (y : ℝ) :
    tiltedPotentialPMF φ θ ξ hzero hfinite y =
      ∑' i : ι, if y = ξ.potentialValue' φ i then
        tiltedSlotPMF φ θ ξ hzero hfinite i else 0 := by
  unfold tiltedPotentialPMF
  exact PMF.map_apply _ _ _

theorem tiltedPotentialPMF_apply_set {ι X : Type*}
    [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (ξ : Combinatorics.Branching.Step ι X)
    (hzero : totalPotentialWeight φ θ ξ ≠ 0)
    (hfinite : totalPotentialWeight φ θ ξ ≠ ∞)
    (s : Set ℝ) (hs : MeasurableSet s) :
    (tiltedPotentialPMF φ θ ξ hzero hfinite).toMeasure s =
      ∑' i : ι, if ξ.potentialValue' φ i ∈ s then
        tiltedSlotPMF φ θ ξ hzero hfinite i else 0 := by
  classical
  rw [tiltedPotentialPMF_toMeasure_map φ θ ξ hzero hfinite,
    Measure.map_apply (measurable_of_countable _) hs]
  rw [PMF.toMeasure_apply]
  · exact tsum_congr (fun i => by
      by_cases hi : ξ.potentialValue' φ i ∈ s <;> simp [hi])
  · exact measurable_of_countable _ hs

theorem totalPotentialWeight_ne_zero_of_nonempty {ι X : Type*}
    [MeasurableSpace X] (φ : Potential X) (θ : ℝ) (ξ : Combinatorics.Branching.Step ι X)
    (hnonempty : ∃ i : ι, survive ξ i) :
    totalPotentialWeight φ θ ξ ≠ 0 := by
  intro hzero
  obtain ⟨i, hi⟩ := hnonempty
  have hterm : realizedPotentialWeight φ θ ξ i ≠ 0 := by
    rw [realizedPotentialWeight]
    simp only [hi, ↓reduceIte]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hle : realizedPotentialWeight φ θ ξ i ≤
      totalPotentialWeight φ θ ξ := by
    unfold totalPotentialWeight
    exact ENNReal.le_tsum i
  rw [hzero] at hle
  exact hterm (bot_unique hle)

theorem finitePositiveWeightDomain_ae {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (μ : Measure (Combinatorics.Branching.Step ι X))
    [IsProbabilityMeasure μ]
    (hnonempty : μ nonemptySupport = 1)
    (hmoment : (∫⁻ ξ, totalPotentialWeight φ θ ξ ∂μ) ≠ ∞) :
    ∀ᵐ ξ ∂μ, ξ ∈ finitePositiveWeightDomain φ θ := by
  have hae_nonempty : ∀ᵐ ξ ∂μ, ξ ∈ nonemptySupport := by
    apply (ae_mem_iff_measure_eq nonemptySupport_measurable.nullMeasurableSet).2
    simpa using hnonempty
  have hae_finite : ∀ᵐ ξ ∂μ,
      totalPotentialWeight φ θ ξ ≠ ∞ := by
    filter_upwards [ae_lt_top (totalPotentialWeight_measurable φ θ) hmoment]
      with ξ hξ
    exact ne_of_lt hξ
  filter_upwards [hae_nonempty, hae_finite] with ξ hne hfin
  exact ⟨totalPotentialWeight_ne_zero_of_nonempty φ θ ξ (by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, hi⟩), hfin⟩

theorem finitePositiveWeightDomain_ae_of_boundary {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X)) [IsProbabilityMeasure μ]
    (hnonempty : HasAtLeastOneChild μ)
    (hboundary : HasBoundaryNormalization φ μ) :
    ∀ᵐ ξ ∂μ, ξ ∈ finitePositiveWeightDomain φ (-1) := by
  apply finitePositiveWeightDomain_ae φ (-1) μ hnonempty
  rw [show (∫⁻ ξ, totalPotentialWeight φ (-1) ξ ∂μ) = 1 by
    simpa [HasBoundaryNormalization] using hboundary]
  simp

theorem tiltedPotentialPMF_apply_set_ae {ι X : Type*}
    [Countable ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (μ : Measure (Combinatorics.Branching.Step ι X))
    [IsProbabilityMeasure μ]
    (hnonempty : μ nonemptySupport = 1)
    (hmoment : (∫⁻ ξ, totalPotentialWeight φ θ ξ ∂μ) ≠ ∞)
    (s : Set ℝ) (hs : MeasurableSet s) :
    ∀ᵐ ξ ∂μ, ∃ hzero : totalPotentialWeight φ θ ξ ≠ 0,
      ∃ hfinite : totalPotentialWeight φ θ ξ ≠ ∞,
        (tiltedPotentialPMF φ θ ξ hzero hfinite).toMeasure s =
          ∑' i : ι, if ξ.potentialValue' φ i ∈ s then
            tiltedSlotPMF φ θ ξ hzero hfinite i else 0 := by
  filter_upwards [finitePositiveWeightDomain_ae φ θ μ hnonempty hmoment]
    with ξ hξ
  exact ⟨hξ.1, hξ.2,
    tiltedPotentialPMF_apply_set φ θ ξ hξ.1 hξ.2 s hs⟩

theorem measurableTiltedWeight_tsum_one_ae {ι X : Type*}
    [Countable ι] [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (μ : Measure (Combinatorics.Branching.Step ι X))
    [IsProbabilityMeasure μ]
    (hnonempty : μ nonemptySupport = 1)
    (hmoment : (∫⁻ ξ, totalPotentialWeight φ θ ξ ∂μ) ≠ ∞) :
    ∀ᵐ ξ ∂μ, ∑' i : ι, measurableTiltedWeight φ θ i ξ = 1 := by
  filter_upwards [finitePositiveWeightDomain_ae φ θ μ hnonempty hmoment]
    with ξ hξ
  calc
    (∑' i : ι, measurableTiltedWeight φ θ i ξ) =
        ∑' i : ι, tiltedSlotPMF φ θ ξ hξ.1 hξ.2 i := by
      apply tsum_congr
      intro i
      exact measurableTiltedWeight_eq_pmf φ θ i ξ hξ.1 hξ.2
    _ = 1 := tiltedSlotPMF_sum φ θ ξ hξ.1 hξ.2

end ProbabilityTheory.BranchingRandomWalk.Spine
