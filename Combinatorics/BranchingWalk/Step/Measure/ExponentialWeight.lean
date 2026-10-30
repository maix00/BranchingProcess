/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Step.Potential
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Exponential weights of a deterministic branching step

Weights are functions of a step. Their measurability is proved here once and
is inherited by every random step by composition.

## Public declarations

- `realizedPotentialWeight φ θ ξ i` is the `ENNReal` weight
  `exp (θ * ξ.potentialValue' φ i)` on surviving slots and `0` otherwise;
  `realizedPotentialWeight_measurable` proves coordinate measurability.
- `totalPotentialWeight φ θ ξ = ∑' i, realizedPotentialWeight φ θ ξ i`,
  and `totalPotentialWeight_measurable` proves its measurability for
  countable slot types.
- `crossPotentialWeight φ θ ξ` is the ordered off-diagonal pair sum
  \(\sum_{i\ne j}w_iw_j\), where
  \(w_i=\operatorname{realizedPotentialWeight}(\varphi,\theta,\xi,i)\).
  `crossPotentialWeight_measurable` proves measurability for countable slots;
  `crossPotentialWeight_real_neg_one_eq_sum` identifies its `θ = -1`
  specialization with the summed-potential exponential formula.
- `realizedChildWeight ξ i` specializes this weight to real marks and
  `θ = -1`; `realizedPotentialWeight_real_neg_one` identifies the two
  definitions, and `realizedChildWeight_measurable` proves measurability.
- `totalChildWeight ξ = ∑' i, realizedChildWeight ξ i`;
  `totalPotentialWeight_real_neg_one` identifies it with the potential sum,
  and `totalChildWeight_measurable` proves measurability for countable slots.
- `finite_realized_children_potential_below` states that finite total
  negative exponential potential weight makes every lower potential level
  finite; `finite_realized_children_below` is its real-valued specialization.
- `finite_realized_children_potential_above` states that finite total
  positive exponential potential weight makes every upper potential level
  finite.
-/

open MeasureTheory Classical
open scoped ENNReal

@[expose] public section

namespace Combinatorics.Branching

noncomputable def realizedPotentialWeight {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (ξ : Step ι X) (i : ι) : ENNReal := by
  classical
  exact if survive ξ i then
    ENNReal.ofReal (Real.exp (θ * ξ.potentialValue' φ i)) else 0

theorem realizedPotentialWeight_measurable {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (i : ι) :
    Measurable (fun ξ : Step ι X => realizedPotentialWeight φ θ ξ i) := by
  classical
  unfold realizedPotentialWeight
  exact (ENNReal.measurable_ofReal.comp
    (measurable_const.mul (Step.potentialValue'_measurable φ i)).exp).ite
    (survive_measurableSet i) measurable_const

noncomputable def totalPotentialWeight {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (ξ : Step ι X) : ENNReal :=
  ∑' i, realizedPotentialWeight φ θ ξ i

theorem totalPotentialWeight_measurable {ι X : Type*} [MeasurableSpace X]
    [Countable ι] (φ : Potential X) (θ : ℝ) :
    Measurable (totalPotentialWeight (ι := ι) φ θ) :=
  Measurable.tsum (realizedPotentialWeight_measurable φ θ)

/-- The ordered off-diagonal pair weight of a deterministic branching step.
For each surviving slot, use its exponential potential weight; absent slots
contribute zero through `realizedPotentialWeight`. Each ordered pair of
distinct slots contributes once. -/
noncomputable def crossPotentialWeight {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (θ : ℝ) (ξ : Step ι X) : ENNReal := by
  classical
  exact ∑' i, ∑' j, if i ≠ j then
    realizedPotentialWeight φ θ ξ i * realizedPotentialWeight φ θ ξ j else 0

/-- The off-diagonal pair weight is measurable for countable slot types. -/
theorem crossPotentialWeight_measurable {ι X : Type*} [MeasurableSpace X]
    [Countable ι] (φ : Potential X) (θ : ℝ) :
    Measurable (crossPotentialWeight (ι := ι) φ θ) := by
  classical
  unfold crossPotentialWeight
  apply Measurable.tsum
  intro i
  apply Measurable.tsum
  intro j
  by_cases hij : i = j
  · subst j
    simp
  · have hprod : Measurable
        ((fun ξ : Step ι X => realizedPotentialWeight φ θ ξ i) *
          fun ξ => realizedPotentialWeight φ θ ξ j) :=
      (realizedPotentialWeight_measurable φ θ i).mul
        (realizedPotentialWeight_measurable φ θ j)
    have heq :
        (fun ξ : Step ι X =>
          realizedPotentialWeight φ θ ξ i * realizedPotentialWeight φ θ ξ j) =
        (fun ξ : Step ι X => realizedPotentialWeight φ θ ξ i) *
          (fun ξ => realizedPotentialWeight φ θ ξ j) := by
      funext ξ
      rfl
    simp only [ite_eq_left hij]
    rw [heq]
    exact hprod

/-- At exponent `-1`, the product of the individual child weights is the
exponential of the sum of the two observed potentials. This formula exposes
the off-diagonal observable in the form used by second-moment estimates. -/
theorem crossPotentialWeight_real_neg_one_eq_sum
    {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (ξ : Step ι X) :
    crossPotentialWeight φ (-1) ξ =
      ∑' i, ∑' j, if i ≠ j ∧ survive ξ i ∧ survive ξ j then
        ENNReal.ofReal (Real.exp
          (-(ξ.potentialValue' φ i + ξ.potentialValue' φ j))) else 0 := by
  classical
  unfold crossPotentialWeight
  apply tsum_congr
  intro i
  apply tsum_congr
  intro j
  by_cases hij : i = j
  · simp [hij]
  · by_cases hi : survive ξ i
    · by_cases hj : survive ξ j
      · simp [hij, hi, hj, realizedPotentialWeight]
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), Real.exp_add]
        congr 1
        ac_rfl
      · simp [hij, hi, hj, realizedPotentialWeight]
    · simp [hij, hi, realizedPotentialWeight]

noncomputable def realizedChildWeight {ι : Type*} (ξ : Step ι ℝ) (i : ι) : ENNReal := by
  classical
  exact if survive ξ i then
    ENNReal.ofReal (Real.exp (-value' ξ i)) else 0

@[simp] theorem realizedPotentialWeight_real_neg_one {ι : Type*}
    (ξ : Step ι ℝ) (i : ι) :
    realizedPotentialWeight realPotential (-1) ξ i = realizedChildWeight ξ i := by
  classical
  cases h : ξ i <;>
    simp [realizedPotentialWeight, realizedChildWeight, survive,
      Step.potentialValue', Step.potentialAt?, value', h]

theorem realizedChildWeight_measurable {ι : Type*} (i : ι) :
    Measurable (fun ξ : Step ι ℝ => realizedChildWeight ξ i) := by
  classical
  unfold realizedChildWeight
  exact (ENNReal.measurable_ofReal.comp
    ((value'_measurable i).neg.exp)).ite
    (survive_measurableSet i) measurable_const

noncomputable def totalChildWeight {ι : Type*} (ξ : Step ι ℝ) : ENNReal :=
  ∑' i, realizedChildWeight ξ i

@[simp] theorem totalPotentialWeight_real_neg_one {ι : Type*}
    (ξ : Step ι ℝ) :
    totalPotentialWeight realPotential (-1) ξ = totalChildWeight ξ := by
  unfold totalPotentialWeight totalChildWeight
  apply tsum_congr
  intro i
  exact realizedPotentialWeight_real_neg_one ξ i

theorem totalChildWeight_measurable {ι : Type*} [Countable ι] :
    Measurable (totalChildWeight : Step ι ℝ → ENNReal) := by
  unfold totalChildWeight
  exact Measurable.tsum realizedChildWeight_measurable

/-- A finite negative exponential weight implies that every lower potential
level contains only finitely many surviving slots.  This statement is about
an abstract mark space observed through `φ`. -/
theorem finite_realized_children_potential_below
    {ι X : Type*} [MeasurableSpace X]
    (φ : Potential X) (ξ : Step ι X)
    (hsum : totalPotentialWeight φ (-1) ξ ≠ ∞) (R : ℝ) :
    {i : ι | survive ξ i ∧ ξ.potentialValue' φ i ≤ R}.Finite := by
  classical
  have hlarge :
      {i | ENNReal.ofReal (Real.exp (-R)) ≤
        realizedPotentialWeight φ (-1) ξ i}.Finite :=
    ENNReal.finite_const_le_of_tsum_ne_top hsum
      (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))
  exact hlarge.subset fun i hi => by
    have hle := ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.mpr (neg_le_neg hi.2))
    simpa [realizedPotentialWeight, hi.1] using hle

/-- A finite positive exponential weight implies that every upper potential
level contains only finitely many surviving slots. This statement is about an
arbitrary real-valued potential. -/
theorem finite_realized_children_potential_above
    {ι : Type*} (φ : Potential ℝ) (ξ : Step ι ℝ)
    (hsum : totalPotentialWeight φ 1 ξ ≠ ∞) (R : ℝ) :
    {i : ι | survive ξ i ∧ R ≤ ξ.potentialValue' φ i}.Finite := by
  classical
  have hlarge :
      {i | ENNReal.ofReal (Real.exp R) ≤
        realizedPotentialWeight φ 1 ξ i}.Finite :=
    ENNReal.finite_const_le_of_tsum_ne_top hsum
      (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))
  exact hlarge.subset fun i hi => by
    have hle := ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.mpr hi.2)
    simpa [realizedPotentialWeight, hi.1] using hle

theorem finite_realized_children_below {ι : Type*} (ξ : Step ι ℝ)
    (hsum : totalChildWeight ξ ≠ ∞) (R : ℝ) :
    {i : ι | survive ξ i ∧ value' ξ i ≤ R}.Finite := by
  classical
  have hlarge :
      {i | ENNReal.ofReal (Real.exp (-R)) ≤ realizedChildWeight ξ i}.Finite :=
    ENNReal.finite_const_le_of_tsum_ne_top hsum
      (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))
  exact hlarge.subset fun i hi => by
    have hle := ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.mpr (neg_le_neg hi.2))
    simpa [realizedChildWeight, hi.1] using hle

end Combinatorics.Branching
