import ThesisSpeed.Probability.PointProcess.Enumeration.FirstAtom
import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# The normalized offspring spine law

The normalized law is defined on raw slot indices.  It is only introduced
when the total exponential weight is finite and nonzero; no survival or
ordered-support assumption is hidden in this definition.
-/

open MeasureTheory
open scoped ENNReal

namespace ThesisSpeed.Spine

noncomputable def tiltedOffspringPMF (ξ : OffspringMark)
    (hzero : totalChildWeight ξ ≠ 0)
    (hfinite : totalChildWeight ξ ≠ ∞) : PMF ℕ :=
  PMF.normalize (realizedChildWeight ξ) hzero hfinite

instance tiltedOffspringPMF_isProbability (ξ : OffspringMark)
    (hzero : totalChildWeight ξ ≠ 0)
    (hfinite : totalChildWeight ξ ≠ ∞) :
    IsProbabilityMeasure (tiltedOffspringPMF ξ hzero hfinite).toMeasure := by
  infer_instance

theorem tiltedOffspringPMF_apply (ξ : OffspringMark)
    (hzero : totalChildWeight ξ ≠ 0)
    (hfinite : totalChildWeight ξ ≠ ∞) (i : ℕ) :
    tiltedOffspringPMF ξ hzero hfinite i =
      realizedChildWeight ξ i * (totalChildWeight ξ)⁻¹ := by
  exact PMF.normalize_apply hzero hfinite i

noncomputable def measurableTiltedWeight (i : ℕ) (ξ : OffspringMark) : ENNReal :=
  if totalChildWeight ξ = 0 ∨ totalChildWeight ξ = ∞ then 0
  else realizedChildWeight ξ i * (totalChildWeight ξ)⁻¹

def finitePositiveWeightDomain : Set OffspringMark :=
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

theorem measurableTiltedWeight_eq_pmf (i : ℕ) (ξ : OffspringMark)
    (hzero : totalChildWeight ξ ≠ 0)
    (hfinite : totalChildWeight ξ ≠ ∞) :
    measurableTiltedWeight i ξ = tiltedOffspringPMF ξ hzero hfinite i := by
  simp [measurableTiltedWeight, hzero, hfinite, tiltedOffspringPMF_apply]

theorem tiltedOffspringPMF_sum (ξ : OffspringMark)
    (hzero : totalChildWeight ξ ≠ 0)
    (hfinite : totalChildWeight ξ ≠ ∞) :
    ∑' i : ℕ, tiltedOffspringPMF ξ hzero hfinite i = 1 := by
  simpa using (tiltedOffspringPMF ξ hzero hfinite).tsum_coe

theorem tiltedOffspringPMF_tsum_weighted (ξ : OffspringMark)
    (hzero : totalChildWeight ξ ≠ 0)
    (hfinite : totalChildWeight ξ ≠ ∞)
    (g : ℕ → ENNReal) :
    (∑' i : ℕ, tiltedOffspringPMF ξ hzero hfinite i * g i) =
      (totalChildWeight ξ)⁻¹ *
        ∑' i : ℕ, realizedChildWeight ξ i * g i := by
  simp_rw [tiltedOffspringPMF_apply ξ hzero hfinite]
  have hcomm : ∀ i : ℕ,
      realizedChildWeight ξ i * (totalChildWeight ξ)⁻¹ * g i =
        (totalChildWeight ξ)⁻¹ * (realizedChildWeight ξ i * g i) := by
    intro i
    ac_rfl
  simp_rw [hcomm]
  rw [ENNReal.tsum_mul_left]

theorem totalChildWeight_ne_zero_of_nonempty (ξ : OffspringMark)
    (hnonempty : ∃ i : ℕ, ξ ∈ childRealized i) :
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

end ThesisSpeed.Spine
