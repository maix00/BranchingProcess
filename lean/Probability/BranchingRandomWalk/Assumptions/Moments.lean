import Probability.BranchingRandomWalk.Assumptions.Structural
import Combinatorics.BranchingStep.Slot.Basic

/-!
# Moment assumptions on the child law

The definitions use the ordered slot representation. Their theorem bundles
also require ordered support and nonempty child set, which is what makes slot
zero the thesis variable `Ξ₁`.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk

open UlamHarris BranchingStep MeasureTheory



def leftmostPositivePart (ξ : NatRealStep) : ℝ :=
  max (firstDisplacement ξ) 0

theorem leftmostPositivePart_measurable :
    Measurable leftmostPositivePart :=
  (step_measurable (X := ℝ) 0).max measurable_const

def HasLeftmostFirstMoment (μ : Measure NatRealStep) : Prop :=
  Integrable leftmostPositivePart μ

def HasLeftmostFourthMoment (μ : Measure NatRealStep) : Prop :=
  Integrable (fun ξ => (leftmostPositivePart ξ) ^ 4) μ

def HasLeftmostPositiveExponentialMoment
    (μ : Measure NatRealStep) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    Integrable (fun ξ => Real.exp (c * firstDisplacement ξ)) μ

/-- The cross term `∑_{i ≠ j} exp(-(Ξᵢ+Ξⱼ))`, with absent slots contributing
zero. The value is allowed to be infinite before imposing the assumption. -/
noncomputable def crossChildWeight (ξ : NatRealStep) : ENNReal := by
  classical
  exact ∑' i : ℕ, ∑' j : ℕ,
    if i ≠ j ∧ ξ ∈ childRealized i ∧ ξ ∈ childRealized j then
      ENNReal.ofReal
        (Real.exp (-(childDisplacement ξ i + childDisplacement ξ j)))
    else 0

theorem crossChildWeight_measurable :
    Measurable crossChildWeight := by
  classical
  unfold crossChildWeight
  apply Measurable.tsum
  intro i
  apply Measurable.tsum
  intro j
  by_cases hij : i = j
  · subst j
    simp
  · have hset : MeasurableSet
        (childRealized i ∩ childRealized j) :=
      (childRealized_measurable i).inter (childRealized_measurable j)
    have hvalue : Measurable (fun ξ : NatRealStep =>
        ENNReal.ofReal
          (Real.exp (-(childDisplacement ξ i + childDisplacement ξ j)))) :=
      ENNReal.measurable_ofReal.comp
        (((childDisplacement_measurable i).add
          (childDisplacement_measurable j)).neg.exp)
    simp only [hij, ne_eq, not_false_eq_true, true_and]
    change Measurable (fun ξ : NatRealStep =>
      if ξ ∈ childRealized i ∩ childRealized j then
        ENNReal.ofReal
          (Real.exp (-(childDisplacement ξ i + childDisplacement ξ j)))
      else 0)
    exact hvalue.ite hset measurable_const

def HasFiniteCrossWeight (μ : Measure NatRealStep) : Prop :=
  (∫⁻ ξ, crossChildWeight ξ ∂μ) ≠ ∞

theorem fourthMoment_implies_firstMoment
    (μ : Measure NatRealStep) [IsFiniteMeasure μ]
    (h : HasLeftmostFourthMoment μ) :
    HasLeftmostFirstMoment μ := by
  have hmeas : AEStronglyMeasurable leftmostPositivePart μ := by
    exact leftmostPositivePart_measurable.aestronglyMeasurable
  apply ((integrable_const (1 : ℝ)).add h).mono hmeas
  filter_upwards [] with ξ
  have hx : 0 ≤ leftmostPositivePart ξ := le_max_right _ _
  change |leftmostPositivePart ξ| ≤ |1 + leftmostPositivePart ξ ^ 4|
  rw [abs_of_nonneg hx,
    abs_of_nonneg (by positivity : 0 ≤ (1 : ℝ) + leftmostPositivePart ξ ^ 4)]
  by_cases hle : leftmostPositivePart ξ ≤ 1
  · nlinarith [pow_nonneg hx 4]
  · have hone : 1 ≤ leftmostPositivePart ξ := le_of_not_ge hle
    have hquad : 0 ≤ leftmostPositivePart ξ ^ 2 +
        leftmostPositivePart ξ + 1 := by nlinarith [sq_nonneg (leftmostPositivePart ξ)]
    have hprod : 0 ≤ leftmostPositivePart ξ *
        (leftmostPositivePart ξ - 1) *
        (leftmostPositivePart ξ ^ 2 + leftmostPositivePart ξ + 1) :=
      mul_nonneg (mul_nonneg hx (sub_nonneg.mpr hone)) hquad
    nlinarith

end ProbabilityTheory.BranchingRandomWalk
