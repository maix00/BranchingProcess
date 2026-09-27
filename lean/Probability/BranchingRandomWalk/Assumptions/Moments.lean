import Probability.BranchingRandomWalk.Assumptions.Structural
import Combinatorics.BranchingWalk.Step.Measurability
import Combinatorics.BranchingWalk.Step.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# Moment assumptions on the child law

The definitions use the ordered slot enumeration. Their theorem bundles
also require ordered support and nonempty child set, which is what makes slot
zero the thesis variable `Ξ₁`.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching MeasureTheory



def leftmostPositivePart (ξ : Step ℕ ℝ) : ℝ :=
  max (value' ξ 0) 0

theorem leftmostPositivePart_measurable :
    Measurable leftmostPositivePart :=
  (value'_measurable (X := ℝ) 0).max measurable_const

def HasLeftmostFirstMoment (μ : Measure (Step ℕ ℝ)) : Prop :=
  Integrable leftmostPositivePart μ

def HasLeftmostFourthMoment (μ : Measure (Step ℕ ℝ)) : Prop :=
  Integrable (fun ξ => (leftmostPositivePart ξ) ^ 4) μ

def HasLeftmostPositiveExponentialMoment
    (μ : Measure (Step ℕ ℝ)) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    Integrable (fun ξ => Real.exp (c * value' ξ 0)) μ

/-- The cross term `∑_{i ≠ j} exp(-(Ξᵢ+Ξⱼ))`, with absent slots contributing
zero. The value is allowed to be infinite before imposing the assumption. -/
noncomputable def crossChildWeight (ξ : Step ℕ ℝ) : ENNReal := by
  classical
  exact ∑' i : ℕ, ∑' j : ℕ,
    if i ≠ j ∧ survive ξ i ∧ survive ξ j then
      ENNReal.ofReal
        (Real.exp (-(value' ξ i + value' ξ j)))
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
        ({ξ | survive ξ i} ∩ {ξ | survive ξ j}) :=
      (survive_measurableSet (X := ℝ) i).inter
        (survive_measurableSet (X := ℝ) j)
    have hvalue : Measurable (fun ξ : Step ℕ ℝ =>
        ENNReal.ofReal
          (Real.exp (-(value' ξ i + value' ξ j)))) :=
      ENNReal.measurable_ofReal.comp
        (((value'_measurable i).add
          (value'_measurable j)).neg.exp)
    simp only [hij, ne_eq, not_false_eq_true, true_and]
    change Measurable (fun ξ : Step ℕ ℝ =>
      if ξ ∈ ({ξ | survive ξ i} ∩ {ξ | survive ξ j}) then
        ENNReal.ofReal
          (Real.exp (-(value' ξ i + value' ξ j)))
      else 0)
    exact hvalue.ite hset measurable_const

def HasFiniteCrossWeight (μ : Measure (Step ℕ ℝ)) : Prop :=
  (∫⁻ ξ, crossChildWeight ξ ∂μ) ≠ ∞

theorem fourthMoment_implies_firstMoment
    (μ : Measure (Step ℕ ℝ)) [IsFiniteMeasure μ]
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
