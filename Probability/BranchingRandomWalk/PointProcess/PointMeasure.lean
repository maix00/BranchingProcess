import Probability.BranchingRandomWalk.PointProcess.Enumeration.Coverage
import Combinatorics.BranchingStep.Position.Increment
import Combinatorics.BranchingStep.Slot.Basic
import Probability.BranchingRandomWalk.PointProcess.Basic
import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# Branching-step point measure in slot coordinates

The raw slot encoding induces a counting measure on displacement space. The
generic `stepPointMeasure` is reused directly; this file records its
evaluation, support, and exponential-integral formulas in the child-slot
vocabulary of the thesis. The standard mathlib `Measure.sum` and
`Measure.dirac` retain multiplicity when several slots share a displacement.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk

open UlamHarris BranchingStep MeasureTheory



/-- The Dirac mass of a realized child, zero for an absent raw slot. -/
noncomputable def childAtomMeasure (ξ : NatRealStep) (i : ℕ) :
    Measure ℝ := by
  classical
  exact if ξ ∈ childRealized i then
    Measure.dirac (childDisplacement ξ i) else 0

theorem childAtomMeasure_measurable (i : ℕ) :
    Measurable (fun ξ : NatRealStep => childAtomMeasure ξ i) := by
  classical
  unfold childAtomMeasure
  exact (Measure.measurable_dirac.comp
    (childDisplacement_measurable i)).ite
      (childRealized_measurable i) measurable_const

/-- The generic branching-step point measure is the sum of the child atoms. -/
theorem stepPointMeasure_eq_sum_childAtomMeasure
    (ξ : NatRealStep) :
    stepPointMeasure ξ = Measure.sum (childAtomMeasure ξ) := by
  unfold stepPointMeasure
  congr 1
  funext i
  classical
  by_cases hi : ξ ∈ childRealized i
  · have hex : ∃ x, ξ i = some x := by
      simpa [childRealized, childPresent, present] using hi
    obtain ⟨x, hx⟩ := hex
    simp [stepAtomMeasure, childAtomMeasure, hi, hx,
      childDisplacement, value]
  · have hnone : ξ i = none := by
      cases h : ξ i with
      | none => rfl
      | some x => exact False.elim (hi ⟨x, h⟩)
    simp [stepAtomMeasure, childAtomMeasure, hi, hnone]

theorem stepPointMeasure_measurable :
    Measurable (fun ξ : NatRealStep => stepPointMeasure ξ) := by
  have hfun : (fun ξ : NatRealStep => stepPointMeasure ξ) =
      fun ξ => Measure.sum (childAtomMeasure ξ) := by
    funext ξ
    exact stepPointMeasure_eq_sum_childAtomMeasure ξ
  rw [hfun]
  apply Measure.measurable_of_measurable_coe
  intro s hs
  change Measurable
    (fun ξ : NatRealStep => (Measure.sum (childAtomMeasure ξ)) s)
  simp_rw [Measure.sum_apply _ hs]
  exact Measurable.tsum (fun i =>
    (Measure.measurable_coe hs).comp (childAtomMeasure_measurable i))

/-- Evaluation counts raw slots, so equal positions retain multiplicity. -/
theorem stepPointMeasure_apply_children (ξ : NatRealStep)
    (s : Set ℝ) (hs : MeasurableSet s) :
    stepPointMeasure ξ s =
      ∑' i : ℕ, (childRealized i ∩
        {ξ | childDisplacement ξ i ∈ s}).indicator
          (fun _ => (1 : ENNReal)) ξ := by
  classical
  rw [stepPointMeasure_eq_sum_childAtomMeasure, Measure.sum_apply _ hs]
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
theorem stepPointMeasure_eq_zero_iff (ξ : NatRealStep) :
    stepPointMeasure ξ = 0 ↔ ξ ∉ childNonempty := by
  constructor
  · intro hzero hnonempty
    obtain ⟨i, hi⟩ := hnonempty
    have hmass :=
      stepPointMeasure_apply_children ξ Set.univ MeasurableSet.univ
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
    rw [stepPointMeasure_apply_children ξ s hs]
    have habsent : ∀ i : ℕ, ξ ∉ childRealized i := by
      intro i hi
      exact hempty ⟨i, hi⟩
    simp [habsent]

/-- Integration of the exponential test against the point measure is
exactly the slotwise total exponential weight used in the thesis. -/
theorem lintegral_stepPointMeasure_exp (ξ : NatRealStep) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (-x))
      ∂stepPointMeasure ξ) = totalChildWeight ξ := by
  rw [stepPointMeasure_eq_sum_childAtomMeasure, lintegral_sum_measure]
  unfold totalChildWeight
  congr 1
  funext i
  by_cases hi : ξ ∈ childRealized i
  · simp [childAtomMeasure, hi, realizedChildWeight,
      lintegral_dirac]
  · simp [childAtomMeasure, hi, realizedChildWeight]

end ProbabilityTheory.BranchingRandomWalk
