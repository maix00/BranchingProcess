/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Assumptions.CrossWeight
public import Probability.BranchingRandomWalk.Spine.ManyToOne.GenerationManyToOne
public import Probability.BranchingRandomWalk.Spine.Tilted.Law

import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# One-step tube mass and its second moment

The cross-child exponential moment controls the off-diagonal terms in the
second moment of the exponentially weighted number of children in a bounded
position window.  The diagonal terms are controlled by the lower endpoint of
the window.  This is the one-generation estimate used to start a two-stage
branching tube argument.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching
open ProbabilityTheory.BranchingRandomWalk.Spine

/-- Exponentially weighted number of children whose potential lies in `I`.
Absent slots contribute zero even when zero belongs to `I`. -/
noncomputable def weightedOffspringWindowMass {ι X : Type*}
    [MeasurableSpace X] [Countable ι]
    (φ : Potential X) (I : Set ℝ) (ξ : Step ι X) : ℝ≥0∞ :=
  ∑' i, realizedPotentialWeight φ (-1) ξ i *
    I.indicator (fun _ => (1 : ℝ≥0∞)) (ξ.potentialValue' φ i)

theorem weightedOffspringWindowMass_measurable {ι X : Type*}
    [MeasurableSpace X] [Countable ι]
    (φ : Potential X) (I : Set ℝ) (hI : MeasurableSet I) :
    Measurable (weightedOffspringWindowMass φ I : Step ι X → ℝ≥0∞) := by
  unfold weightedOffspringWindowMass
  apply Measurable.tsum
  intro i
  exact (realizedPotentialWeight_measurable φ (-1) i).mul
    ((measurable_const.indicator hI).comp
      (Step.potentialValue'_measurable φ i))

/-- Integrating the weighted offspring mass in a measurable window gives the
mass of that window under the one-step tilted law. -/
theorem lintegral_weightedOffspringWindowMass_eq_tiltedLaw
    {ι X : Type*} [MeasurableSpace X] [Countable ι]
    (φ : Potential X) (I : Set ℝ) (hI : MeasurableSet I)
    (μ : Measure (Step ι X)) :
    (∫⁻ ξ, weightedOffspringWindowMass φ I ξ ∂μ) =
      tiltedPotentialLaw φ (-1) μ I := by
  unfold weightedOffspringWindowMass
  rw [← lintegral_tiltedPotentialLaw φ (-1) μ
    (I.indicator (fun _ => (1 : ℝ≥0∞)))
    (measurable_const.indicator hI)]
  have hfun : (fun y : ℝ => I.indicator (fun _ => (1 : ℝ≥0∞)) y) =
      I.indicator 1 := by
    rfl
  rw [hfun]
  exact lintegral_indicator_one hI

/-- The weighted window mass is nonzero exactly when the step has a child
whose potential lies in the window. -/
theorem weightedOffspringWindowMass_ne_zero_iff
    {ι X : Type*} [MeasurableSpace X] [Countable ι]
    (φ : Potential X) (I : Set ℝ) (ξ : Step ι X) :
    weightedOffspringWindowMass φ I ξ ≠ 0 ↔
      ∃ i, survive ξ i ∧ ξ.potentialValue' φ i ∈ I := by
  classical
  constructor
  · intro hW
    by_contra hno
    have hterms (i : ι) :
        realizedPotentialWeight φ (-1) ξ i *
          I.indicator (fun _ => (1 : ℝ≥0∞))
            (ξ.potentialValue' φ i) = 0 := by
      by_cases hi : survive ξ i
      · have hnot : ξ.potentialValue' φ i ∉ I := by
          intro hxi
          exact hno ⟨i, hi, hxi⟩
        simp [realizedPotentialWeight, hi, hnot]
      · simp [realizedPotentialWeight, hi]
    apply hW
    unfold weightedOffspringWindowMass
    rw [ENNReal.tsum_eq_zero]
    exact hterms
  · rintro ⟨i, hi, hxi⟩ hW
    have hterm :
        realizedPotentialWeight φ (-1) ξ i *
          I.indicator (fun _ => (1 : ℝ≥0∞))
            (ξ.potentialValue' φ i) ≠ 0 := by
      simp [realizedPotentialWeight, hi, hxi]
      exact Real.exp_pos _
    unfold weightedOffspringWindowMass at hW
    have hterms := (ENNReal.tsum_eq_zero.mp hW)
    exact hterm (hterms i)

/-- Pointwise second-moment bound for the weighted offspring mass in a window
whose lower endpoint is `a`.  The diagonal contribution costs `exp(-a)`;
the off-diagonal contribution is bounded by the cross-child weight. -/
theorem weightedOffspringWindowMass_sq_le
    {ι X : Type*} [MeasurableSpace X] [Countable ι]
    (φ : Potential X) (I : Set ℝ) (a : ℝ)
    (hI : ∀ x ∈ I, a ≤ x) (ξ : Step ι X) :
    weightedOffspringWindowMass φ I ξ ^ 2 ≤
      ENNReal.ofReal (Real.exp (-a)) * weightedOffspringWindowMass φ I ξ +
        crossChildWeight φ ξ := by
  classical
  let w : ι → ℝ≥0∞ := fun i =>
    realizedPotentialWeight φ (-1) ξ i *
      I.indicator (fun _ => (1 : ℝ≥0∞)) (ξ.potentialValue' φ i)
  have hprod : (∑' i, w i) * (∑' i, w i) =
      ∑' p : ι × ι, w p.1 * w p.2 := by
    calc
      (∑' i, w i) * (∑' i, w i) =
          ∑' i, w i * (∑' j, w j) := by
        rw [← ENNReal.tsum_mul_right]
      _ = ∑' i, ∑' j, w i * w j := by
        apply tsum_congr
        intro i
        rw [← ENNReal.tsum_mul_left]
      _ = ∑' p : (ι × ι), w p.1 * w p.2 := by
        exact ENNReal.tsum_prod.symm
  have hpair (i j : ι) :
      w i * w j ≤
        (if i = j then ENNReal.ofReal (Real.exp (-a)) * w i else 0) +
          (if i ≠ j ∧ survive ξ i ∧ survive ξ j then
            ENNReal.ofReal (Real.exp
              (-(ξ.potentialValue' φ i + ξ.potentialValue' φ j))) else 0) := by
    by_cases hij : i = j
    · subst j
      by_cases hi : survive ξ i
      · by_cases hxi : ξ.potentialValue' φ i ∈ I
        · have hlow : a ≤ ξ.potentialValue' φ i := hI _ hxi
          have hw : w i = ENNReal.ofReal
              (Real.exp (-(ξ.potentialValue' φ i))) := by
            simp [w, realizedPotentialWeight, hi, hxi]
          rw [hw]
          simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte,
            add_zero]
          gcongr
        · have hw : w i = 0 := by simp [w, hxi]
          simp [hw]
      · have hw : w i = 0 := by simp [w, realizedPotentialWeight, hi]
        simp [hw]
    · have hdiag : (if i = j then ENNReal.ofReal (Real.exp (-a)) * w i else 0) = 0 :=
        if_neg hij
      rw [hdiag]
      by_cases hi : survive ξ i
      · by_cases hj : survive ξ j
        · by_cases hxi : ξ.potentialValue' φ i ∈ I
          · by_cases hxj : ξ.potentialValue' φ j ∈ I
            · have hwi : w i = ENNReal.ofReal
                  (Real.exp (-(ξ.potentialValue' φ i))) := by
                simp [w, realizedPotentialWeight, hi, hxi]
              have hwj : w j = ENNReal.ofReal
                  (Real.exp (-(ξ.potentialValue' φ j))) := by
                simp [w, realizedPotentialWeight, hj, hxj]
              rw [hwi, hwj]
              have hexp : Real.exp (-(ξ.potentialValue' φ i)) *
                    Real.exp (-(ξ.potentialValue' φ j)) =
                  Real.exp (-(ξ.potentialValue' φ i + ξ.potentialValue' φ j)) := by
                rw [← Real.exp_add]
                congr 1
                ring
              simp only [if_pos (show i ≠ j ∧ survive ξ i ∧ survive ξ j from
                ⟨hij, hi, hj⟩), zero_add]
              rw [← ENNReal.ofReal_mul
                (Real.exp_nonneg (-(ξ.potentialValue' φ i))), hexp]
            · have hwj : w j = 0 := by simp [w, hxj]
              simp [hwj]
          · have hwi : w i = 0 := by simp [w, hxi]
            simp [hwi]
        · have hwj : w j = 0 := by simp [w, realizedPotentialWeight, hj]
          simp [hwj]
      · have hwi : w i = 0 := by simp [w, realizedPotentialWeight, hi]
        simp [hwi]
  calc
    weightedOffspringWindowMass φ I ξ ^ 2 =
        (∑' i, w i) * (∑' i, w i) := by
          simp [weightedOffspringWindowMass, w, pow_two]
    _ = ∑' p : ι × ι, w p.1 * w p.2 := hprod
    _ ≤ ∑' p : (ι × ι),
        ((if p.1 = p.2 then ENNReal.ofReal (Real.exp (-a)) * w p.1 else 0) +
          (if p.1 ≠ p.2 ∧ survive ξ p.1 ∧ survive ξ p.2 then
            ENNReal.ofReal (Real.exp
              (-(ξ.potentialValue' φ p.1 + ξ.potentialValue' φ p.2))) else 0)) :=
      ENNReal.tsum_le_tsum (fun p => hpair p.1 p.2)
    _ = ENNReal.ofReal (Real.exp (-a)) * (∑' i, w i) +
        crossChildWeight φ ξ := by
      have hdiagProd :
          (∑' p : (ι × ι),
            if p.1 = p.2 then ENNReal.ofReal (Real.exp (-a)) * w p.1 else 0) =
          ∑' i, ∑' j,
            if i = j then ENNReal.ofReal (Real.exp (-a)) * w i else 0 := by
        exact ENNReal.tsum_prod
          (f := fun i j => if i = j then ENNReal.ofReal (Real.exp (-a)) * w i else 0)
      have hcrossProd :
          (∑' p : (ι × ι),
            if p.1 ≠ p.2 ∧ survive ξ p.1 ∧ survive ξ p.2 then
              ENNReal.ofReal (Real.exp
                (-(ξ.potentialValue' φ p.1 + ξ.potentialValue' φ p.2))) else 0) =
          ∑' i, ∑' j,
            if i ≠ j ∧ survive ξ i ∧ survive ξ j then
              ENNReal.ofReal (Real.exp
                (-(ξ.potentialValue' φ i + ξ.potentialValue' φ j))) else 0 := by
        exact ENNReal.tsum_prod
          (f := fun i j => if i ≠ j ∧ survive ξ i ∧ survive ξ j then
            ENNReal.ofReal (Real.exp
              (-(ξ.potentialValue' φ i + ξ.potentialValue' φ j))) else 0)
      rw [ENNReal.tsum_add, hdiagProd, hcrossProd]
      have hdiag : (∑' i, ∑' j,
          if i = j then ENNReal.ofReal (Real.exp (-a)) * w i else 0) =
            ENNReal.ofReal (Real.exp (-a)) * (∑' i, w i) := by
        calc
          (∑' i, ∑' j,
              if i = j then ENNReal.ofReal (Real.exp (-a)) * w i else 0) =
              ∑' i, ENNReal.ofReal (Real.exp (-a)) * w i := by
                apply tsum_congr
                intro i
                rw [tsum_eq_single i]
                · simp
                · intro j hj
                  simp [Ne.symm hj]
          _ = ENNReal.ofReal (Real.exp (-a)) * (∑' i, w i) :=
            ENNReal.tsum_mul_left
      rw [hdiag]
      rfl

/-- The integrated second moment of the weighted offspring mass is bounded
by the lower window endpoint and the cross-child exponential moment. -/
theorem lintegral_weightedOffspringWindowMass_sq_le
    {ι X : Type*} [MeasurableSpace X] [Countable ι]
    (φ : Potential X) (I : Set ℝ) (a : ℝ)
    (hI : MeasurableSet I) (hlower : ∀ x ∈ I, a ≤ x)
    (μ : Measure (Step ι X)) :
    (∫⁻ ξ, weightedOffspringWindowMass φ I ξ ^ 2 ∂μ) ≤
      ENNReal.ofReal (Real.exp (-a)) * tiltedPotentialLaw φ (-1) μ I +
        (∫⁻ ξ, crossChildWeight φ ξ ∂μ) := by
  let W : Step ι X → ℝ≥0∞ := weightedOffspringWindowMass φ I
  have hW : Measurable W := weightedOffspringWindowMass_measurable φ I hI
  calc
    (∫⁻ ξ, W ξ ^ 2 ∂μ) ≤
        ∫⁻ ξ, ENNReal.ofReal (Real.exp (-a)) * W ξ +
          crossChildWeight φ ξ ∂μ :=
      lintegral_mono fun ξ => weightedOffspringWindowMass_sq_le
        φ I a hlower ξ
    _ = ENNReal.ofReal (Real.exp (-a)) * (∫⁻ ξ, W ξ ∂μ) +
          (∫⁻ ξ, crossChildWeight φ ξ ∂μ) := by
      rw [lintegral_add_left' ((hW.const_mul _).aemeasurable),
        lintegral_const_mul _ hW]
    _ = ENNReal.ofReal (Real.exp (-a)) * tiltedPotentialLaw φ (-1) μ I +
          (∫⁻ ξ, crossChildWeight φ ξ ∂μ) := by
      rw [lintegral_weightedOffspringWindowMass_eq_tiltedLaw φ I hI μ]

/-- One-step Paley--Zygmund bound for entering a position window.  It is
stated in square-root form, so it remains valid for extended-valued moments;
when the cross-child moment is finite it gives the usual positive lower
bound on the probability of a successful tube step. -/
theorem tiltedWindowProbability_le_sqrt_success_mul_secondMoment
    {ι X : Type*} [MeasurableSpace X] [Countable ι]
    (φ : Potential X) (I : Set ℝ) (a : ℝ)
    (hI : MeasurableSet I) (hlower : ∀ x ∈ I, a ≤ x)
    (μ : Measure (Step ι X)) :
    tiltedPotentialLaw φ (-1) μ I ≤
      (μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0}) ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal (Real.exp (-a)) * tiltedPotentialLaw φ (-1) μ I +
          (∫⁻ ξ, crossChildWeight φ ξ ∂μ)) ^ (1 / 2 : ℝ) := by
  let W : Step ι X → ℝ≥0∞ := weightedOffspringWindowMass φ I
  let A : Set (Step ι X) := {ξ | W ξ ≠ 0}
  let indicator : Step ι X → ℝ≥0∞ := A.indicator fun _ => 1
  have hW : Measurable W := weightedOffspringWindowMass_measurable φ I hI
  have hA : MeasurableSet A := by
    change MeasurableSet (W ⁻¹' ({0}ᶜ))
    exact (measurableSet_singleton 0).compl.preimage hW
  have hindicator : Measurable indicator := measurable_const.indicator hA
  have h22 : (2 : ℝ).HolderConjugate 2 := by
    convert Real.HolderConjugate.conjExponent
      (show 1 < (2 : ℝ) by norm_num) using 1 <;>
      norm_num [Real.conjExponent]
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ h22
    hindicator.aemeasurable hW.aemeasurable
  have hindicator_sq : (fun ξ => indicator ξ ^ (2 : ℝ)) = indicator := by
    funext ξ
    by_cases hξ : ξ ∈ A <;> simp [indicator, hξ]
  have hindicator_integral :
      (∫⁻ ξ, indicator ξ ^ (2 : ℝ) ∂μ) = μ A := by
    rw [hindicator_sq]
    exact lintegral_indicator_one hA
  have hW_on_A : ∀ ξ, indicator ξ * W ξ = W ξ := by
    intro ξ
    by_cases hξ : ξ ∈ A
    · simp [indicator, hξ]
    · have hWzero : W ξ = 0 := by
        by_contra hne
        exact hξ hne
      simp [indicator, hξ, hWzero]
  have hmean : (∫⁻ ξ, W ξ ∂μ) = tiltedPotentialLaw φ (-1) μ I :=
    lintegral_weightedOffspringWindowMass_eq_tiltedLaw φ I hI μ
  have hsecond := lintegral_weightedOffspringWindowMass_sq_le
    φ I a hI hlower μ
  calc
    tiltedPotentialLaw φ (-1) μ I = ∫⁻ ξ, indicator ξ * W ξ ∂μ := by
      rw [lintegral_congr fun ξ => hW_on_A ξ, hmean]
    _ ≤ (∫⁻ ξ, indicator ξ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) *
        (∫⁻ ξ, W ξ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) := hHolder
    _ ≤ (μ A) ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal (Real.exp (-a)) * tiltedPotentialLaw φ (-1) μ I +
          (∫⁻ ξ, crossChildWeight φ ξ ∂μ)) ^ (1 / 2 : ℝ) := by
      rw [hindicator_integral]
      gcongr
      simpa [W] using hsecond

/-- A positive tilted mass of a measurable window implies positive
probability that at least one child enters it. -/
theorem measure_hasPotentialChildIn_pos_of_tiltedWindow_pos
    {ι X : Type*} [MeasurableSpace X] [Countable ι]
    (φ : Potential X) (I : Set ℝ) (a : ℝ)
    (hI : MeasurableSet I) (hlower : ∀ x ∈ I, a ≤ x)
    (μ : Measure (Step ι X))
    (hpositive : 0 < tiltedPotentialLaw φ (-1) μ I) :
    0 < μ {ξ | ∃ i, survive ξ i ∧ ξ.potentialValue' φ i ∈ I} := by
  have hholder := tiltedWindowProbability_le_sqrt_success_mul_secondMoment
    φ I a hI hlower μ
  have hwindow : 0 < μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0} := by
    by_contra h
    have hzero : μ {ξ | weightedOffspringWindowMass φ I ξ ≠ 0} = 0 :=
      le_antisymm (not_lt.mp h) bot_le
    have hle : tiltedPotentialLaw φ (-1) μ I ≤ 0 := by
      simpa [hzero] using hholder
    exact (not_lt_of_ge hle) hpositive
  apply lt_of_lt_of_le hwindow
  exact measure_mono fun ξ hξ =>
    (weightedOffspringWindowMass_ne_zero_iff φ I ξ).mp hξ

end ProbabilityTheory.BranchingRandomWalk.Spine
