/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Entrance.NormalDomain

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Exponential error budget for the entrance block

The cyclic-rotation entrance estimate loses a polynomial factor in the width.
This file shows that the factor is absorbed by the exponential error budget
when the full horizon is longer than a diffusive block by a positive power.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- Exponential decay in any positive power eventually dominates the inverse
quadratic width. This is an application of Mathlib's exponential-versus-power
little-o theorem. -/
private theorem eventually_exp_neg_rpow_le_div_sq
    {a b q : ℝ} (ha : 0 < a) (hb : 0 < b) (hq : 0 < q) :
    ∀ᶠ x : ℝ in atTop, Real.exp (-a * x ^ b) ≤ q / x ^ (2 : ℝ) := by
  have hlittleBase :=
    (isLittleO_exp_neg_mul_rpow_atTop ha (-2 / b)).comp_tendsto
      (_root_.tendsto_rpow_atTop hb)
  have hpow : (fun x : ℝ => (x ^ b) ^ (-2 / b)) =ᶠ[atTop]
      fun x => x ^ (-2 : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [← Real.rpow_mul (le_of_lt hx)]
    congr 1
    field_simp [ne_of_gt hb]
  have hlittle : (fun x : ℝ => Real.exp (-a * x ^ b)) =o[atTop]
      fun x => x ^ (-2 : ℝ) :=
    hlittleBase.congr' EventuallyEq.rfl hpow
  have hratio := hlittle.tendsto_div_nhds_zero
  have hsmall := hratio.eventually (Iio_mem_nhds hq)
  filter_upwards [eventually_gt_atTop (0 : ℝ), hsmall] with x hx hsmall
  have hdenom : x ^ (-2 : ℝ) = (x ^ (2 : ℝ))⁻¹ :=
    Real.rpow_neg (le_of_lt hx) 2
  have hratioEq : Real.exp (-a * x ^ b) / x ^ (-2 : ℝ) =
      Real.exp (-a * x ^ b) * x ^ (2 : ℝ) := by
    rw [hdenom]
    simp
  rw [hratioEq] at hsmall
  rw [le_div_iff₀ (Real.rpow_pos_of_pos hx 2)]
  exact le_of_lt hsmall

/-- If the horizon is at least `floor (width^(2+epsilon))`, the polynomial
entrance loss is bounded by any prescribed positive exponential error rate,
for all sufficiently large widths. -/
private theorem eventually_exp_neg_horizon_le_div_floor_sq
    {q δ ε : ℝ} (hq : 0 < q) (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ Delta : ℝ in atTop,
      ∀ L : ℕ, Nat.floor (Delta ^ (2 + ε)) ≤ L →
        Real.exp (-δ * (L : ℝ) / Delta ^ (2 : ℝ)) ≤
          q / (Nat.floor (Delta ^ 2) : ℝ) := by
  have hsmallExp := eventually_exp_neg_rpow_le_div_sq
    (q := q) (a := δ / 2) (b := ε) (by linarith) hε hq
  have hlargePower :=
    (_root_.tendsto_rpow_atTop (by linarith : 0 < 2 + ε)).eventually
      (eventually_ge_atTop (2 : ℝ))
  filter_upwards [hsmallExp, eventually_ge_atTop (2 : ℝ), hlargePower]
    with Delta hsmallExp hDelta hlargePower
  intro L hL
  have hDeltaPos : 0 < Delta := by linarith
  have hwidthPower : Delta ^ (2 + ε) = Delta ^ (2 : ℝ) * Delta ^ ε :=
    Real.rpow_add hDeltaPos 2 ε
  have hfloorLower : Delta ^ (2 + ε) / 2 ≤ (Nat.floor (Delta ^ (2 + ε)) : ℝ) := by
    have hfloor : Delta ^ (2 + ε) < (Nat.floor (Delta ^ (2 + ε)) : ℝ) + 1 :=
      Nat.lt_floor_add_one _
    nlinarith [hlargePower]
  have hfloorLeL : (Nat.floor (Delta ^ (2 + ε)) : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast hL
  have htime : Delta ^ ε / 2 ≤ (L : ℝ) / Delta ^ (2 : ℝ) := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2)
      (Real.rpow_pos_of_pos hDeltaPos 2)]
    nlinarith [hfloorLower.trans hfloorLeL, hwidthPower]
  have hexponent : -δ * (L : ℝ) / Delta ^ (2 : ℝ) ≤
      -(δ / 2) * Delta ^ ε := by
    have hmul := mul_le_mul_of_nonneg_left htime hδ.le
    calc
      -δ * (L : ℝ) / Delta ^ (2 : ℝ) =
          -(δ * ((L : ℝ) / Delta ^ (2 : ℝ))) := by
        field_simp [ne_of_gt (Real.rpow_pos_of_pos hDeltaPos 2)]
      _ ≤ -(δ * (Delta ^ ε / 2)) := neg_le_neg hmul
      _ = -(δ / 2) * Delta ^ ε := by ring
  have hfirst : Real.exp (-δ * (L : ℝ) / Delta ^ (2 : ℝ)) ≤
      Real.exp (-(δ / 2) * Delta ^ ε) := Real.exp_le_exp.mpr hexponent
  have hfloorSqPos : 0 < (Nat.floor (Delta ^ 2) : ℝ) := by
    have hfloorPos : 1 ≤ Nat.floor (Delta ^ 2) := by
      rw [Nat.one_le_floor_iff]
      nlinarith [sq_nonneg (Delta - 2)]
    exact_mod_cast (show (0 : ℕ) < Nat.floor (Delta ^ 2) by omega)
  have hfloorSqLe : (Nat.floor (Delta ^ 2) : ℝ) ≤ Delta ^ (2 : ℝ) := by
    calc
      (Nat.floor (Delta ^ 2) : ℝ) ≤ Delta ^ 2 :=
        Nat.floor_le (by positivity : (0 : ℝ) ≤ Delta ^ 2)
      _ = Delta ^ (2 : ℝ) := (Real.rpow_natCast Delta 2).symm
  have hdiv : q / Delta ^ (2 : ℝ) ≤ q / (Nat.floor (Delta ^ 2) : ℝ) := by
    rw [div_le_div_iff₀ (Real.rpow_pos_of_pos hDeltaPos 2) hfloorSqPos]
    nlinarith [mul_le_mul_of_nonneg_left hfloorSqLe hq.le]
  exact hfirst.trans (hsmallExp.trans hdiv)

/-- The finite-variance cyclic-rotation entrance estimate absorbs its
`1 / floor (Delta²)` loss into the exponential error used by the paper's
long-horizon corridor argument. The event itself is unchanged: the theorem
only converts its lower bound into the form consumed by that argument. -/
theorem exists_eventually_iidSequenceLaw_finiteMovingEntranceEvent_ge_exp_of_centeredSecondMoment
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2)) (hsigma : 0 < sigma)
    (c : ℝ) (hc : 0 ≤ c) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ Delta₀ : ℝ, ∀ Delta ≥ Delta₀, ∀ L : ℕ,
      Nat.floor (Delta ^ (2 + ε)) ≤ L →
      ∀ r₀ ∈ Set.Icc (-Delta) 0,
        Real.exp (-δ * (L : ℝ) / Delta ^ (2 : ℝ)) ≤
          (iidSequenceLaw ν
            {increment | finitePrefixVector (n := ⌊Delta ^ 2⌋₊) increment ∈
              finiteMovingEntranceEvent (n := ⌊Delta ^ 2⌋₊)
                Delta (c / Delta ^ 3) (-r₀ / Delta)}).toReal := by
  obtain ⟨q, hq, DeltaE, hEntrance⟩ :=
    exists_eventually_iidSequenceLaw_finiteMovingEntranceEvent_ge_div_of_centeredSecondMoment
      hν hsigma c hc
  let DeltaQ : ℝ := max DeltaE 2
  have hDeltaQE : DeltaE ≤ DeltaQ := by
    dsimp [DeltaQ]
    exact le_max_left _ _
  have hDeltaQ2 : 2 ≤ DeltaQ := by
    dsimp [DeltaQ]
    exact le_max_right _ _
  have hDeltaQPos : 0 < DeltaQ := by linarith
  have hrQ : -DeltaQ ∈ Set.Icc (-DeltaQ) 0 := by
    exact Set.mem_Icc.mpr ⟨le_rfl, by linarith⟩
  have hqBoundQ := hEntrance DeltaQ hDeltaQE (-DeltaQ) hrQ
  have hmeasureQ : iidSequenceLaw ν
      {increment | finitePrefixVector (n := ⌊DeltaQ ^ 2⌋₊) increment ∈
        finiteMovingEntranceEvent (n := ⌊DeltaQ ^ 2⌋₊)
          DeltaQ (c / DeltaQ ^ 3) (DeltaQ / DeltaQ)} ≤ 1 := by
    calc
      iidSequenceLaw ν
          {increment | finitePrefixVector (n := ⌊DeltaQ ^ 2⌋₊) increment ∈
            finiteMovingEntranceEvent (n := ⌊DeltaQ ^ 2⌋₊)
              DeltaQ (c / DeltaQ ^ 3) (DeltaQ / DeltaQ)} ≤
        iidSequenceLaw ν Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hqBoundQ' : q / (⌊DeltaQ ^ 2⌋₊ : ℝ≥0∞) ≤
      iidSequenceLaw ν
        {increment | finitePrefixVector (n := ⌊DeltaQ ^ 2⌋₊) increment ∈
          finiteMovingEntranceEvent (n := ⌊DeltaQ ^ 2⌋₊)
            DeltaQ (c / DeltaQ ^ 3) (DeltaQ / DeltaQ)} := by
    simpa only [neg_neg] using hqBoundQ
  have hqDivOne : q / (⌊DeltaQ ^ 2⌋₊ : ℝ≥0∞) ≤ 1 := hqBoundQ'.trans hmeasureQ
  have hqfinite : q ≠ ⊤ := by
    intro htop
    have hdenom : (⌊DeltaQ ^ 2⌋₊ : ℝ≥0∞) ≠ ⊤ := by simp
    rw [htop, ENNReal.top_div_of_ne_top hdenom] at hqDivOne
    exact (not_le_of_gt ENNReal.one_lt_top) hqDivOne
  have hqReal : 0 < q.toReal := ENNReal.toReal_pos (ne_of_gt hq) hqfinite
  have hlarge := eventually_exp_neg_horizon_le_div_floor_sq
    (q := q.toReal) (δ := δ) (ε := ε) hqReal hδ hε
  obtain ⟨DeltaA, hDeltaA⟩ := Filter.eventually_atTop.1 hlarge
  refine ⟨max (max DeltaE DeltaA) 2, ?_⟩
  intro Delta hDelta L hL r₀ hr₀
  have hDeltaE : DeltaE ≤ Delta :=
    (le_max_left _ _).trans ((le_max_left _ _).trans hDelta)
  have hDeltaA' : DeltaA ≤ Delta :=
    (le_max_right _ _).trans ((le_max_left _ _).trans hDelta)
  have hDelta2 : 2 ≤ Delta := (le_max_right _ _).trans hDelta
  have hEntranceBound := hEntrance Delta hDeltaE r₀ hr₀
  have hLowerReal := ENNReal.toReal_mono (measure_lt_top _ _).ne hEntranceBound
  have hLowerReal' : q.toReal / (⌊Delta ^ 2⌋₊ : ℝ) ≤
      (iidSequenceLaw ν
        {increment | finitePrefixVector (n := ⌊Delta ^ 2⌋₊) increment ∈
          finiteMovingEntranceEvent (n := ⌊Delta ^ 2⌋₊)
            Delta (c / Delta ^ 3) (-r₀ / Delta)}).toReal := by
    simpa [ENNReal.toReal_div] using hLowerReal
  have hExp := hDeltaA Delta hDeltaA' L hL
  exact hExp.trans hLowerReal'

end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end
