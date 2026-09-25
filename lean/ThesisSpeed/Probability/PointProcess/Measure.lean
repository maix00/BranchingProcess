import ThesisSpeed.Probability.PointProcess.Enumeration.Coverage
import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Offspring point measure

The raw slot encoding induces a counting measure on displacement space.
The standard mathlib `Measure.sum` and `Measure.dirac` retain multiplicity
when several slots have the same displacement. No new measure type is needed.
-/

open MeasureTheory
open scoped ENNReal

namespace ThesisSpeed

/-- The Dirac mass of a realized child, zero for an absent raw slot. -/
noncomputable def childAtomMeasure (ξ : OffspringMark) (i : ℕ) :
    Measure ℝ := by
  classical
  exact if ξ ∈ childRealized i then
    Measure.dirac (childDisplacement ξ i) else 0

theorem childAtomMeasure_measurable (i : ℕ) :
    Measurable (fun ξ : OffspringMark => childAtomMeasure ξ i) := by
  classical
  unfold childAtomMeasure
  exact (Measure.measurable_dirac.comp
    (childDisplacement_measurable i)).ite
      (childRealized_measurable i) measurable_const

/-- The random offspring point measure, with multiplicities. -/
noncomputable def offspringPointMeasure (ξ : OffspringMark) :
    Measure ℝ :=
  Measure.sum (childAtomMeasure ξ)

theorem offspringPointMeasure_measurable :
    Measurable offspringPointMeasure := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  change Measurable
    (fun ξ : OffspringMark => (Measure.sum (childAtomMeasure ξ)) s)
  simp_rw [Measure.sum_apply _ hs]
  exact Measurable.tsum (fun i =>
    (Measure.measurable_coe hs).comp (childAtomMeasure_measurable i))

/-- Evaluation counts raw slots, so equal positions retain multiplicity. -/
theorem offspringPointMeasure_apply (ξ : OffspringMark)
    (s : Set ℝ) (hs : MeasurableSet s) :
    offspringPointMeasure ξ s =
      ∑' i : ℕ, (childRealized i ∩
        {ξ | childDisplacement ξ i ∈ s}).indicator
          (fun _ => (1 : ENNReal)) ξ := by
  classical
  rw [offspringPointMeasure, Measure.sum_apply _ hs]
  congr 1
  funext i
  by_cases hi : ξ ∈ childRealized i
  · by_cases hmem : childDisplacement ξ i ∈ s
    · simp [childAtomMeasure, hi, hmem,
        Measure.dirac_apply' _ hs]
    · simp [childAtomMeasure, hi, hmem,
        Measure.dirac_apply' _ hs]
  · simp [childAtomMeasure, hi]

/-- Integration of the exponential test against the point measure is
exactly the slotwise total exponential weight used in the thesis. -/
theorem lintegral_offspringPointMeasure_exp (ξ : OffspringMark) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-x))
      ∂offspringPointMeasure ξ) = totalChildWeight ξ := by
  rw [offspringPointMeasure, lintegral_sum_measure]
  unfold totalChildWeight
  congr 1
  funext i
  by_cases hi : ξ ∈ childRealized i
  · simp [childAtomMeasure, hi, realizedChildWeight,
      lintegral_dirac]
  · simp [childAtomMeasure, hi, realizedChildWeight]

end ThesisSpeed
