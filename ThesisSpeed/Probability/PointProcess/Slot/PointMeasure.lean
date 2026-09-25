import ThesisSpeed.Probability.PointProcess.Enumeration.Coverage
import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Branching-step point measure in slot coordinates

The raw slot encoding induces a counting measure on displacement space. The
generic `branchingStepPointMeasure` is reused directly; this file records its
evaluation, support, and exponential-integral formulas in the child-slot
vocabulary of the thesis. The standard mathlib `Measure.sum` and
`Measure.dirac` retain multiplicity when several slots share a displacement.
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

/-- The generic branching-step point measure is the sum of the child atoms. -/
theorem branchingStepPointMeasure_eq_sum_childAtomMeasure
    (ξ : NatRealBranchingStep) :
    branchingStepPointMeasure ξ = Measure.sum (childAtomMeasure ξ) := by
  unfold branchingStepPointMeasure
  congr 1
  funext i
  classical
  by_cases hi : ξ ∈ childRealized i
  · have hex : ∃ x, ξ i = some x := by
      simpa [childRealized, childPresent, branchingStepPresent] using hi
    obtain ⟨x, hx⟩ := hex
    simp [branchingStepAtomMeasure, childAtomMeasure, hi, hx,
      childDisplacement, branchingStepIncrement]
  · have hnone : ξ i = none := by
      cases h : ξ i with
      | none => rfl
      | some x => exact False.elim (hi ⟨x, h⟩)
    simp [branchingStepAtomMeasure, childAtomMeasure, hi, hnone]

theorem branchingStepPointMeasure_measurable :
    Measurable (fun ξ : NatRealBranchingStep => branchingStepPointMeasure ξ) := by
  have hfun : (fun ξ : NatRealBranchingStep => branchingStepPointMeasure ξ) =
      fun ξ => Measure.sum (childAtomMeasure ξ) := by
    funext ξ
    exact branchingStepPointMeasure_eq_sum_childAtomMeasure ξ
  rw [hfun]
  apply Measure.measurable_of_measurable_coe
  intro s hs
  change Measurable
    (fun ξ : NatRealBranchingStep => (Measure.sum (childAtomMeasure ξ)) s)
  simp_rw [Measure.sum_apply _ hs]
  exact Measurable.tsum (fun i =>
    (Measure.measurable_coe hs).comp (childAtomMeasure_measurable i))

/-- Evaluation counts raw slots, so equal positions retain multiplicity. -/
theorem branchingStepPointMeasure_apply_children (ξ : NatRealBranchingStep)
    (s : Set ℝ) (hs : MeasurableSet s) :
    branchingStepPointMeasure ξ s =
      ∑' i : ℕ, (childRealized i ∩
        {ξ | childDisplacement ξ i ∈ s}).indicator
          (fun _ => (1 : ENNReal)) ξ := by
  classical
  rw [branchingStepPointMeasure_eq_sum_childAtomMeasure, Measure.sum_apply _ hs]
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
theorem branchingStepPointMeasure_eq_zero_iff (ξ : NatRealBranchingStep) :
    branchingStepPointMeasure ξ = 0 ↔ ξ ∉ childNonempty := by
  constructor
  · intro hzero hnonempty
    obtain ⟨i, hi⟩ := hnonempty
    have hmass :=
      branchingStepPointMeasure_apply_children ξ Set.univ MeasurableSet.univ
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
    rw [branchingStepPointMeasure_apply_children ξ s hs]
    have habsent : ∀ i : ℕ, ξ ∉ childRealized i := by
      intro i hi
      exact hempty ⟨i, hi⟩
    simp [habsent]

/-- Integration of the exponential test against the point measure is
exactly the slotwise total exponential weight used in the thesis. -/
theorem lintegral_branchingStepPointMeasure_exp (ξ : NatRealBranchingStep) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-x))
      ∂branchingStepPointMeasure ξ) = totalChildWeight ξ := by
  rw [branchingStepPointMeasure_eq_sum_childAtomMeasure, lintegral_sum_measure]
  unfold totalChildWeight
  congr 1
  funext i
  by_cases hi : ξ ∈ childRealized i
  · simp [childAtomMeasure, hi, realizedChildWeight,
      lintegral_dirac]
  · simp [childAtomMeasure, hi, realizedChildWeight]

end ThesisSpeed
