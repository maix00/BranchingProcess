/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Drawdown.FiniteVarianceUpper

/-!
# Small deviations in a tube with positive linear drift

The public theorem in this file is:

- `driftedTubeEvent_subset_noLargeDropEndpointBelowEvent`:
  for `a ∈ [-Δ,0]` and nonnegative drift `c`, a path in
  `a + cj/Δ² ≤ Y_j ≤ a + cj/Δ² + Δ` for `1 ≤ j ≤ L` has drawdowns at most
  `Δ` and endpoint at most `Δ + cL/Δ²`.
- `exists_driftedTubeBlockProbability_le_exp_of_finiteVariance`:
  for `0<η<1`, a block of length `⌊Δ^(2+η)⌋` inside the tilted tube has
  probability at most `exp(-d⌊Δ^(2+η)⌋/Δ²)` for all large `Δ`.

These are the event inclusion and complete-block estimate in the proof of Wang Yiyang,
*Asymptotic speed of the $N$-branching random walk with infinite offspring*,
Chapter 3, Lemma 3.4.
-/

open Filter MeasureTheory
open scoped Topology

namespace ProbabilityTheory.RandomWalk.SmallDeviation

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

/-- The path event for a linearly rising tube of width `width`. -/
def driftedTubeEvent (horizon : ℕ) (width drift lower : ℝ) :
    Set (ℕ → ℝ) :=
  {increment | ∀ j : ℕ, 1 ≤ j → j ≤ horizon →
    lower + drift * (j : ℝ) / width ^ 2 ≤
        AdditivePath.displacement j increment ∧
      AdditivePath.displacement j increment ≤
        lower + drift * (j : ℝ) / width ^ 2 + width}

/-- On a tube with nonnegative drift, the upper constraint at time `i`
and lower constraint at time `j ≥ i` bound the drawdown by its width. -/
theorem driftedTubeEvent_subset_noLargeDropEndpointBelowEvent
    (horizon : ℕ) {width drift lower : ℝ}
    (hwidth : 0 < width) (hdrift : 0 ≤ drift)
    (hlower : -width ≤ lower) (hupper : lower ≤ 0) :
    driftedTubeEvent horizon width drift lower ⊆
      noLargeDropEndpointBelowEvent horizon width
        (width + drift * (horizon : ℝ) / width ^ 2) := by
  intro increment hpath
  have hslope : 0 ≤ drift / width ^ 2 := div_nonneg hdrift (sq_nonneg width)
  have htube (j : ℕ) (hj : 1 ≤ j) (horizonBound : j ≤ horizon) :=
    hpath j hj horizonBound
  constructor
  · intro i j hij hj
    by_cases hjzero : j = 0
    · have hizero : i = 0 := by omega
      subst i
      subst j
      simp [AdditivePath.displacement_zero, hwidth.le]
    have hjpos : 1 ≤ j := by omega
    have hjtube := htube j hjpos hj
    by_cases hi : i = 0
    · subst i
      have hterm : 0 ≤ drift * (j : ℝ) / width ^ 2 := by positivity
      simpa [AdditivePath.displacement_zero] using
        (show (0 : ℝ) - AdditivePath.displacement j increment ≤ width by
          linarith [hjtube.1])
    · have hipos : 1 ≤ i := by omega
      have hitube := htube i hipos (by omega)
      have htime : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      have hnonneg :
          drift * (i : ℝ) / width ^ 2 ≤
            drift * (j : ℝ) / width ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_left htime hslope
        simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hmul
      linarith [hitube.2, hjtube.1]
  · by_cases hzero : horizon = 0
    · subst horizon
      simp [AdditivePath.displacement_zero]
      linarith
    · have hpos : 1 ≤ horizon := by omega
      have hend := htube horizon hpos le_rfl
      linarith [hend.2]

/-- The single complete-block estimate in Wang Yiyang, Chapter 3, proof of
Lemma 3.4. The drifted tube is included in the no-large-drop event of
Chapter 3, Lemma 3.3 with endpoint parameter `η/2`. -/
theorem exists_driftedTubeBlockProbability_le_exp_of_finiteVariance
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {variance drift eta d : ℝ}
    (hν : ProbabilityTheory.IsCenteredSecondMoment ν variance)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < variance) (hdrift : 0 ≤ drift)
    (heta : 0 < eta) (hetaOne : eta < 1)
    (hd : 0 < d) (hcritical : d < Real.pi ^ 2 / 2 * variance) :
    ∃ Delta₀ : ℝ, 1 ≤ Delta₀ ∧
      ∀ Delta ≥ Delta₀, ∀ lower : ℝ,
        -Delta ≤ lower → lower ≤ 0 →
        (iidSequenceLaw ν).real
          (driftedTubeEvent ⌊Delta ^ (2 + eta)⌋₊ Delta drift lower) ≤
          Real.exp (-d * ((⌊Delta ^ (2 + eta)⌋₊ : ℝ) / Delta ^ 2)) := by
  have hetaHalf : 0 < eta / 2 := by linarith
  obtain ⟨DeltaMain, hDeltaMain, hmain⟩ :=
    Drawdown.measureReal_noLargeDropEndpointBelowEvent_le_exp_of_finiteVariance
      ν hν hsquare hvariance hetaHalf hd hcritical
  have hfloor := Drawdown.eventually_drawdownFloorBlockLength_bounds heta
  have hgrowth : ∀ᶠ Delta : ℝ in atTop,
      drift ≤ Delta ^ (1 - eta) :=
    (_root_.tendsto_rpow_atTop (by linarith : 0 < 1 - eta)).eventually
      (eventually_ge_atTop drift)
  obtain ⟨DeltaBound, hDeltaBound⟩ :=
    Filter.eventually_atTop.1 (hfloor.and hgrowth)
  let Delta₀ := max DeltaMain (max DeltaBound 1)
  refine ⟨Delta₀, le_max_of_le_right (le_max_right _ _), ?_⟩
  intro Delta hDelta lower hlower hupper
  have hDeltaMain' : DeltaMain ≤ Delta :=
    (le_max_left _ _).trans hDelta
  have hDeltaBound' : DeltaBound ≤ Delta :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hDelta)
  have hDeltaOne : 1 ≤ Delta :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hDelta)
  have hDeltaPos : 0 < Delta := by linarith
  rcases hDeltaBound Delta hDeltaBound' with
    ⟨⟨hfloorPos, _, hfloorLower, hfloorUpper⟩, hgrowthAt⟩
  let length : ℕ := ⌊Delta ^ (2 + eta)⌋₊
  have hlengthLower : Delta ^ (2 + eta / 2) ≤ (length : ℝ) := hfloorLower
  have hlengthUpper : (length : ℝ) ≤ Delta ^ (2 + eta) := hfloorUpper
  have hpower : Delta ^ (2 + eta) = Delta ^ 2 * Delta ^ eta := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_add hDeltaPos 2 eta
  have hpowerOne : Delta ^ eta * Delta ^ (1 - eta) = Delta := by
    rw [← Real.rpow_add hDeltaPos]
    simp
  have hdriftTerm : drift * (length : ℝ) / Delta ^ 2 ≤ Delta := by
    have hle : drift * (length : ℝ) ≤ drift * (Delta ^ 2 * Delta ^ eta) :=
      mul_le_mul_of_nonneg_left (hlengthUpper.trans_eq hpower) hdrift
    have hbound : drift * Delta ^ eta ≤ Delta := by
      calc
        drift * Delta ^ eta ≤ Delta ^ (1 - eta) * Delta ^ eta :=
          mul_le_mul_of_nonneg_right hgrowthAt (by positivity)
        _ = Delta := by simpa [mul_comm] using hpowerOne
    apply (div_le_iff₀ (sq_pos_of_pos hDeltaPos)).2
    nlinarith [hle, hbound, sq_nonneg Delta]
  have hthreshold :
      Delta + drift * (length : ℝ) / Delta ^ 2 ≤ Delta / (eta / 2) := by
    have htwo : 2 * Delta ≤ Delta / (eta / 2) := by
      apply (le_div_iff₀ hetaHalf).2
      nlinarith [hetaOne.le, hDeltaPos.le]
    linarith
  have hsubset :
      driftedTubeEvent length Delta drift lower ⊆
        Drawdown.noLargeDropEndpointBelowEvent length Delta (Delta / (eta / 2)) := by
    intro increment hpath
    have hbasic := driftedTubeEvent_subset_noLargeDropEndpointBelowEvent
      length hDeltaPos hdrift hlower hupper hpath
    exact ⟨hbasic.1, hbasic.2.trans hthreshold⟩
  have hmainAt := hmain Delta hDeltaMain' length hlengthLower
  exact (measureReal_mono hsubset (measure_ne_top (iidSequenceLaw ν) _)).trans hmainAt

end ProbabilityTheory.RandomWalk.SmallDeviation
