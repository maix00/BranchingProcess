import Probability.BranchingRandomWalk.Assumptions.Structural
import Combinatorics.BranchingWalk.Step.Measurability
import Combinatorics.BranchingWalk.Step.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# Moment assumptions on the child law

The leftmost-child assumptions use a `StepLaw` ordering rule before reading
slot zero. Symmetric sums such as the cross term are evaluated directly on the
raw law because they are invariant under slot relabelling.
-/

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching MeasureTheory



def StepLaw.leftmostPositivePart {ι α : Type*} [PartialOrder α] [OrderBot α]
    (L : StepLaw ι α ℝ) (ξ : Combinatorics.Branching.Step ι ℝ) : ℝ :=
  max (L.displacement ⊥ ξ) 0

theorem StepLaw.leftmostPositivePart_measurable
    {ι α : Type*} [PartialOrder α] [OrderBot α]
    (L : StepLaw ι α ℝ) :
    Measurable L.leftmostPositivePart :=
  (L.displacement_measurable ⊥).max measurable_const

def HasLeftmostFirstMoment {ι α : Type*} [PartialOrder α] [OrderBot α]
    (L : StepLaw ι α ℝ) : Prop :=
  Integrable L.leftmostPositivePart L.raw

def HasLeftmostFourthMoment {ι α : Type*} [PartialOrder α] [OrderBot α]
    (L : StepLaw ι α ℝ) : Prop :=
  Integrable (fun ξ => (L.leftmostPositivePart ξ) ^ 4) L.raw

def HasLeftmostPositiveExponentialMoment
    {ι α : Type*} [PartialOrder α] [OrderBot α]
    (L : StepLaw ι α ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    Integrable (fun ξ => Real.exp (c * L.displacement ⊥ ξ)) L.raw

/-- The cross term `∑_{i ≠ j} exp(-(Ξᵢ+Ξⱼ))`, with absent slots contributing
zero. The value is allowed to be infinite before imposing the assumption. -/
noncomputable def crossChildWeight {ι : Type*}
    (ξ : Combinatorics.Branching.Step ι ℝ) : ENNReal := by
  classical
  exact ∑' i : ι, ∑' j : ι,
    if i ≠ j ∧ survive ξ i ∧ survive ξ j then
      ENNReal.ofReal
        (Real.exp (-(value' ξ i + value' ξ j)))
    else 0

theorem crossChildWeight_measurable {ι : Type*} [Countable ι] :
    Measurable (crossChildWeight :
      Combinatorics.Branching.Step ι ℝ → ENNReal) := by
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
    have hvalue : Measurable (fun ξ : Combinatorics.Branching.Step ι ℝ =>
        ENNReal.ofReal
          (Real.exp (-(value' ξ i + value' ξ j)))) :=
      ENNReal.measurable_ofReal.comp
        (((value'_measurable i).add
          (value'_measurable j)).neg.exp)
    simp only [hij, ne_eq, not_false_eq_true, true_and]
    change Measurable (fun ξ : Combinatorics.Branching.Step ι ℝ =>
      if ξ ∈ ({ξ | survive ξ i} ∩ {ξ | survive ξ j}) then
        ENNReal.ofReal
          (Real.exp (-(value' ξ i + value' ξ j)))
      else 0)
    exact hvalue.ite hset measurable_const

def HasFiniteCrossWeight {ι : Type*}
    (μ : Measure (Combinatorics.Branching.Step ι ℝ)) : Prop :=
  (∫⁻ ξ, crossChildWeight ξ ∂μ) ≠ ∞

theorem fourthMoment_implies_firstMoment
    {ι α : Type*} [PartialOrder α] [OrderBot α]
    (L : StepLaw ι α ℝ) [IsFiniteMeasure L.raw]
    (h : HasLeftmostFourthMoment L) :
    HasLeftmostFirstMoment L := by
  have hmeas : AEStronglyMeasurable L.leftmostPositivePart L.raw := by
    exact L.leftmostPositivePart_measurable.aestronglyMeasurable
  apply ((integrable_const (1 : ℝ)).add h).mono hmeas
  filter_upwards [] with ξ
  have hx : 0 ≤ L.leftmostPositivePart ξ := le_max_right _ _
  change |L.leftmostPositivePart ξ| ≤ |1 + L.leftmostPositivePart ξ ^ 4|
  rw [abs_of_nonneg hx,
    abs_of_nonneg (by positivity : 0 ≤ (1 : ℝ) + L.leftmostPositivePart ξ ^ 4)]
  by_cases hle : L.leftmostPositivePart ξ ≤ 1
  · nlinarith [pow_nonneg hx 4]
  · have hone : 1 ≤ L.leftmostPositivePart ξ := le_of_not_ge hle
    have hquad : 0 ≤ L.leftmostPositivePart ξ ^ 2 +
        L.leftmostPositivePart ξ + 1 := by
      nlinarith [sq_nonneg (L.leftmostPositivePart ξ)]
    have hprod : 0 ≤ L.leftmostPositivePart ξ *
        (L.leftmostPositivePart ξ - 1) *
        (L.leftmostPositivePart ξ ^ 2 + L.leftmostPositivePart ξ + 1) :=
      mul_nonneg (mul_nonneg hx (sub_nonneg.mpr hone)) hquad
    nlinarith

end ProbabilityTheory.BranchingRandomWalk
