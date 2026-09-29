module

public import Probability.BranchingRandomWalk.Assumptions.Structural
public import Combinatorics.BranchingWalk.Step.Measurability
public import Combinatorics.BranchingWalk.Step.Basic
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

/-!
# Moment assumptions on the child law

The leftmost-child assumptions use a `StepLaw` ordering rule before reading
slot zero. Symmetric sums such as the cross term are evaluated directly on the
raw law because they are invariant under slot relabelling.
-/

open MeasureTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching MeasureTheory



def StepLaw.leftmostPositivePart {ι α X : Type*} [MeasurableSpace X] [PartialOrder α] [OrderBot α]
    (L : StepLaw ι α X) (ξ : Combinatorics.Branching.Step ι X) : ℝ :=
  max (L.displacement ⊥ ξ) 0

theorem StepLaw.leftmostPositivePart_measurable
    {ι α X : Type*} [MeasurableSpace X] [PartialOrder α] [OrderBot α]
    (L : StepLaw ι α X) :
    Measurable L.leftmostPositivePart :=
  (L.displacement_measurable ⊥).max measurable_const

def HasLeftmostFirstMoment {ι α X : Type*} [MeasurableSpace X] [PartialOrder α] [OrderBot α]
    (L : StepLaw ι α X) : Prop :=
  Integrable L.leftmostPositivePart L.raw

def HasLeftmostFourthMoment {ι α X : Type*} [MeasurableSpace X] [PartialOrder α] [OrderBot α]
    (L : StepLaw ι α X) : Prop :=
  Integrable (fun ξ => (L.leftmostPositivePart ξ) ^ 4) L.raw

def HasLeftmostPositiveExponentialMoment
    {ι α X : Type*} [MeasurableSpace X] [PartialOrder α] [OrderBot α]
    (L : StepLaw ι α X) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    Integrable (fun ξ => Real.exp (c * L.displacement ⊥ ξ)) L.raw

/-- The cross term `∑_{i ≠ j} exp(-(Ξᵢ+Ξⱼ))`, with absent slots contributing
zero. The value is allowed to be infinite before imposing the assumption. -/
noncomputable def crossChildWeight {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (ξ : Combinatorics.Branching.Step ι X) : ENNReal := by
  classical
  exact ∑' i : ι, ∑' j : ι,
    if i ≠ j ∧ survive ξ i ∧ survive ξ j then
      ENNReal.ofReal
        (Real.exp (-(ξ.potentialValue' φ i + ξ.potentialValue' φ j)))
    else 0

theorem crossChildWeight_measurable {ι X : Type*} [Countable ι]
    [MeasurableSpace X] (φ : Potential X) :
    Measurable (crossChildWeight (ι := ι) φ :
      Combinatorics.Branching.Step ι X → ENNReal) := by
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
      (survive_measurableSet (X := X) i).inter
        (survive_measurableSet (X := X) j)
    have hvalue : Measurable (fun ξ : Combinatorics.Branching.Step ι X =>
        ENNReal.ofReal
          (Real.exp (-(ξ.potentialValue' φ i + ξ.potentialValue' φ j)))) :=
      ENNReal.measurable_ofReal.comp
        (((Step.potentialValue'_measurable φ i).add
          (Step.potentialValue'_measurable φ j)).neg.exp)
    simp only [hij, ne_eq, not_false_eq_true, true_and]
    change Measurable (fun ξ : Combinatorics.Branching.Step ι X =>
      if ξ ∈ ({ξ | survive ξ i} ∩ {ξ | survive ξ j}) then
        ENNReal.ofReal
          (Real.exp (-(ξ.potentialValue' φ i + ξ.potentialValue' φ j)))
      else 0)
    exact hvalue.ite hset measurable_const

def HasFiniteCrossWeight {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (μ : Measure (Combinatorics.Branching.Step ι X)) : Prop :=
  (∫⁻ ξ, crossChildWeight φ ξ ∂μ) ≠ ∞

theorem fourthMoment_implies_firstMoment
    {ι α X : Type*} [MeasurableSpace X] [PartialOrder α] [OrderBot α]
    (L : StepLaw ι α X) [IsFiniteMeasure L.raw]
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
