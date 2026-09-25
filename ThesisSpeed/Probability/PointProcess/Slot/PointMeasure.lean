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
noncomputable def childAtomMeasure (ξ : NatRealBranchingStep) (i : ℕ) :
    Measure ℝ := by
  classical
  exact if ξ ∈ childRealized i then
    Measure.dirac (childDisplacement ξ i) else 0

theorem childAtomMeasure_measurable (i : ℕ) :
    Measurable (fun ξ : NatRealBranchingStep => childAtomMeasure ξ i) := by
  classical
  unfold childAtomMeasure
  exact (Measure.measurable_dirac.comp
    (childDisplacement_measurable i)).ite
      (childRealized_measurable i) measurable_const

/-- The random offspring point measure, with multiplicities. -/
noncomputable def offspringPointMeasure (ξ : NatRealBranchingStep) :
    Measure ℝ :=
  Measure.sum (childAtomMeasure ξ)

theorem offspringPointMeasure_measurable :
    Measurable offspringPointMeasure := by
  apply Measure.measurable_of_measurable_coe
  intro s hs
  change Measurable
    (fun ξ : NatRealBranchingStep => (Measure.sum (childAtomMeasure ξ)) s)
  simp_rw [Measure.sum_apply _ hs]
  exact Measurable.tsum (fun i =>
    (Measure.measurable_coe hs).comp (childAtomMeasure_measurable i))

/-- Evaluation counts raw slots, so equal positions retain multiplicity. -/
theorem offspringPointMeasure_apply (ξ : NatRealBranchingStep)
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

/-- The Dirac-sum point measure is zero exactly for an all-absent mark. -/
theorem offspringPointMeasure_eq_zero_iff (ξ : NatRealBranchingStep) :
    offspringPointMeasure ξ = 0 ↔ ξ ∉ offspringNonempty := by
  constructor
  · intro hzero hnonempty
    obtain ⟨i, hi⟩ := hnonempty
    have hmass := offspringPointMeasure_apply ξ Set.univ MeasurableSet.univ
    rw [hzero] at hmass
    have hterm : (childRealized i ∩
        {ξ | childDisplacement ξ i ∈ Set.univ}).indicator
          (fun _ => (1 : ENNReal)) ξ = 1 := by
      simp [childRealized, hi]
    have hall : ∀ j : ℕ, (childRealized j ∩
        {ξ | childDisplacement ξ j ∈ Set.univ}).indicator
          (fun _ => (1 : ENNReal)) ξ = 0 := by
      exact ENNReal.tsum_eq_zero.mp (by simpa using hmass.symm)
    have halli := hall i
    rw [hterm] at halli
    exact one_ne_zero halli
  · intro hempty
    apply Measure.ext
    intro s hs
    rw [offspringPointMeasure_apply ξ s hs]
    have habsent : ∀ i : ℕ, ξ ∉ childRealized i := by
      intro i hi
      exact hempty ⟨i, hi⟩
    simp [habsent]

/-- Integration of the exponential test against the point measure is
exactly the slotwise total exponential weight used in the thesis. -/
theorem lintegral_offspringPointMeasure_exp (ξ : NatRealBranchingStep) :
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
