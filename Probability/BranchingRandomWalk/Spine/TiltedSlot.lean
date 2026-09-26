import Probability.BranchingRandomWalk.PointProcess.Enumeration.FirstAtom.Displacement
import Combinatorics.BranchingWalk.Step.Measurability
import Probability.BranchingRandomWalk.Assumptions.Structural
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Combinatorics.BranchingWalk.Step.Basic

/-!
# The normalized spine law

The normalized law is defined on raw slot indices.  It is only introduced
when the total exponential weight is finite and nonzero; no survival or
ordered-support assumption is hidden in this definition.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory


open scoped Classical

noncomputable def tiltedSlotPMF (ξ : NatRealStep)
    (hzero : totalChildWeight ξ ≠ 0)
    (hfinite : totalChildWeight ξ ≠ ∞) : PMF ℕ :=
  PMF.normalize (realizedChildWeight ξ) hzero hfinite

instance tiltedSlotPMF_isProbability (ξ : NatRealStep)
    (hzero : totalChildWeight ξ ≠ 0)
    (hfinite : totalChildWeight ξ ≠ ∞) :
    IsProbabilityMeasure (tiltedSlotPMF ξ hzero hfinite).toMeasure := by
  infer_instance

theorem tiltedSlotPMF_apply (ξ : NatRealStep)
    (hzero : totalChildWeight ξ ≠ 0)
    (hfinite : totalChildWeight ξ ≠ ∞) (i : ℕ) :
    tiltedSlotPMF ξ hzero hfinite i =
      realizedChildWeight ξ i * (totalChildWeight ξ)⁻¹ := by
  exact PMF.normalize_apply hzero hfinite i

noncomputable def measurableTiltedWeight (i : ℕ) (ξ : NatRealStep) : ENNReal :=
  if totalChildWeight ξ = 0 ∨ totalChildWeight ξ = ∞ then 0
  else realizedChildWeight ξ i * (totalChildWeight ξ)⁻¹

def finitePositiveWeightDomain : Set NatRealStep :=
  {ξ | totalChildWeight ξ ≠ 0 ∧ totalChildWeight ξ ≠ ∞}

theorem finitePositiveWeightDomain_measurable :
    MeasurableSet finitePositiveWeightDomain := by
  exact (totalChildWeight_measurable
    (measurableSet_singleton 0)).compl.inter
      (totalChildWeight_measurable
        (measurableSet_singleton ∞)).compl

theorem measurableTiltedWeight_measurable (i : ℕ) :
    Measurable (measurableTiltedWeight i) := by
  classical
  unfold measurableTiltedWeight
  apply Measurable.ite
  · exact (totalChildWeight_measurable (measurableSet_singleton 0)).union
      (totalChildWeight_measurable (measurableSet_singleton ∞))
  · exact measurable_const
  · exact (realizedChildWeight_measurable i).mul
      (totalChildWeight_measurable.inv)

theorem measurableTiltedWeight_eq_pmf (i : ℕ) (ξ : NatRealStep)
    (hzero : totalChildWeight ξ ≠ 0)
    (hfinite : totalChildWeight ξ ≠ ∞) :
    measurableTiltedWeight i ξ = tiltedSlotPMF ξ hzero hfinite i := by
  simp [measurableTiltedWeight, hzero, hfinite, tiltedSlotPMF_apply]

theorem tiltedSlotPMF_sum (ξ : NatRealStep)
    (hzero : totalChildWeight ξ ≠ 0)
    (hfinite : totalChildWeight ξ ≠ ∞) :
    ∑' i : ℕ, tiltedSlotPMF ξ hzero hfinite i = 1 := by
  simpa using (tiltedSlotPMF ξ hzero hfinite).tsum_coe

theorem tiltedSlotPMF_tsum_weighted (ξ : NatRealStep)
    (hzero : totalChildWeight ξ ≠ 0)
    (hfinite : totalChildWeight ξ ≠ ∞)
    (g : ℕ → ENNReal) :
    (∑' i : ℕ, tiltedSlotPMF ξ hzero hfinite i * g i) =
      (totalChildWeight ξ)⁻¹ *
        ∑' i : ℕ, realizedChildWeight ξ i * g i := by
  simp_rw [tiltedSlotPMF_apply ξ hzero hfinite]
  have hcomm : ∀ i : ℕ,
      realizedChildWeight ξ i * (totalChildWeight ξ)⁻¹ * g i =
        (totalChildWeight ξ)⁻¹ * (realizedChildWeight ξ i * g i) := by
    intro i
    ac_rfl
  simp_rw [hcomm]
  rw [ENNReal.tsum_mul_left]

noncomputable def tiltedDisplacementPMF (ξ : NatRealStep)
    (hzero : totalChildWeight ξ ≠ 0)
    (hfinite : totalChildWeight ξ ≠ ∞) : PMF ℝ :=
  PMF.map (fun i => value' ξ i)
    (tiltedSlotPMF ξ hzero hfinite)

theorem tiltedDisplacementPMF_toMeasure_map (ξ : NatRealStep)
    (hzero : totalChildWeight ξ ≠ 0)
    (hfinite : totalChildWeight ξ ≠ ∞) :
    (tiltedDisplacementPMF ξ hzero hfinite).toMeasure =
      Measure.map (fun i => value' ξ i)
        (tiltedSlotPMF ξ hzero hfinite).toMeasure := by
  symm
  exact PMF.toMeasure_map _ _ (measurable_of_countable _)

instance tiltedDisplacementPMF_isProbability (ξ : NatRealStep)
    (hzero : totalChildWeight ξ ≠ 0)
    (hfinite : totalChildWeight ξ ≠ ∞) :
    IsProbabilityMeasure (tiltedDisplacementPMF ξ hzero hfinite).toMeasure := by
  infer_instance

theorem tiltedDisplacementPMF_apply (ξ : NatRealStep)
    (hzero : totalChildWeight ξ ≠ 0)
    (hfinite : totalChildWeight ξ ≠ ∞) (y : ℝ) :
    tiltedDisplacementPMF ξ hzero hfinite y =
      ∑' i : ℕ, if y = value' ξ i then
        tiltedSlotPMF ξ hzero hfinite i else 0 := by
  unfold tiltedDisplacementPMF
  exact PMF.map_apply _ _ _

theorem tiltedDisplacementPMF_apply_set (ξ : NatRealStep)
    (hzero : totalChildWeight ξ ≠ 0)
    (hfinite : totalChildWeight ξ ≠ ∞) (s : Set ℝ)
    (hs : MeasurableSet s) :
    (tiltedDisplacementPMF ξ hzero hfinite).toMeasure s =
      ∑' i : ℕ, if value' ξ i ∈ s then
        tiltedSlotPMF ξ hzero hfinite i else 0 := by
  classical
  rw [tiltedDisplacementPMF_toMeasure_map ξ hzero hfinite,
      Measure.map_apply (measurable_of_countable _) hs]
  rw [PMF.toMeasure_apply]
  · exact tsum_congr (fun i => by
      by_cases hi : value' ξ i ∈ s <;> simp [hi])
  · exact measurable_of_countable _ hs


theorem totalChildWeight_ne_zero_of_nonempty (ξ : NatRealStep)
    (hnonempty : ∃ i : ℕ, survive ξ i) :
    totalChildWeight ξ ≠ 0 := by
  intro hzero
  obtain ⟨i, hi⟩ := hnonempty
  have hterm : realizedChildWeight ξ i ≠ 0 := by
    rw [realizedChildWeight]
    simp only [hi, ↓reduceIte]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))
  have hle : realizedChildWeight ξ i ≤ totalChildWeight ξ := by
    unfold totalChildWeight
    exact ENNReal.le_tsum i
  rw [hzero] at hle
  exact hterm (bot_unique hle)

theorem finitePositiveWeightDomain_ae
    (μ : Measure NatRealStep) [IsProbabilityMeasure μ]
    (hnonempty : μ nonemptySupport = 1)
    (hmoment : (∫⁻ ξ, totalChildWeight ξ ∂μ) ≠ ∞) :
    ∀ᵐ ξ ∂μ, ξ ∈ finitePositiveWeightDomain := by
  have hae_nonempty : ∀ᵐ ξ ∂μ, ξ ∈ nonemptySupport := by
    apply (ae_mem_iff_measure_eq nonemptySupport_measurable.nullMeasurableSet).2
    simpa using hnonempty
  have hae_finite : ∀ᵐ ξ ∂μ, totalChildWeight ξ ≠ ∞ := by
    filter_upwards [ae_lt_top totalChildWeight_measurable hmoment] with ξ hξ
    exact ne_of_lt hξ
  filter_upwards [hae_nonempty, hae_finite] with ξ hne hfin
  exact ⟨totalChildWeight_ne_zero_of_nonempty ξ (by
    obtain ⟨i, hi⟩ := hne
    exact ⟨i, hi⟩), hfin⟩

theorem finitePositiveWeightDomain_ae_of_boundary
    (μ : Measure NatRealStep) [IsProbabilityMeasure μ]
    (hnonempty : HasAtLeastOneChild μ)
    (hboundary : HasBoundaryNormalization μ) :
    ∀ᵐ ξ ∂μ, ξ ∈ finitePositiveWeightDomain := by
  apply finitePositiveWeightDomain_ae μ hnonempty
  rw [hboundary]
  simp

theorem tiltedDisplacementPMF_apply_set_ae
    (μ : Measure NatRealStep) [IsProbabilityMeasure μ]
    (hnonempty : μ nonemptySupport = 1)
    (hmoment : (∫⁻ ξ, totalChildWeight ξ ∂μ) ≠ ∞)
    (s : Set ℝ) (hs : MeasurableSet s) :
    ∀ᵐ ξ ∂μ, ∃ hzero : totalChildWeight ξ ≠ 0,
      ∃ hfinite : totalChildWeight ξ ≠ ∞,
        (tiltedDisplacementPMF ξ hzero hfinite).toMeasure s =
          ∑' i : ℕ, if value' ξ i ∈ s then
            tiltedSlotPMF ξ hzero hfinite i else 0 := by
  filter_upwards [finitePositiveWeightDomain_ae μ hnonempty hmoment] with ξ hξ
  exact ⟨hξ.1, hξ.2, tiltedDisplacementPMF_apply_set ξ hξ.1 hξ.2 s hs⟩

theorem measurableTiltedWeight_tsum_one_ae
    (μ : Measure NatRealStep) [IsProbabilityMeasure μ]
    (hnonempty : μ nonemptySupport = 1)
    (hmoment : (∫⁻ ξ, totalChildWeight ξ ∂μ) ≠ ∞) :
    ∀ᵐ ξ ∂μ, ∑' i : ℕ, measurableTiltedWeight i ξ = 1 := by
  filter_upwards [finitePositiveWeightDomain_ae μ hnonempty hmoment] with ξ hξ
  have hzero : totalChildWeight ξ ≠ 0 := hξ.1
  have hfinite : totalChildWeight ξ ≠ ∞ := hξ.2
  calc
    (∑' i : ℕ, measurableTiltedWeight i ξ) =
        ∑' i : ℕ, tiltedSlotPMF ξ hzero hfinite i := by
      apply tsum_congr
      intro i
      exact measurableTiltedWeight_eq_pmf i ξ hzero hfinite
    _ = 1 := tiltedSlotPMF_sum ξ hzero hfinite

end ProbabilityTheory.BranchingRandomWalk.Spine
