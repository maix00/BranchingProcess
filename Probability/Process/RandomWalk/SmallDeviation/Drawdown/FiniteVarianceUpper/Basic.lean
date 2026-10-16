/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Distributions.Moments.Real
public import Probability.Process.RandomWalk.SmallDeviation.Drawdown.Event
public import Probability.Sequence.IID.Basic
import Probability.Process.RandomWalk.SmallDeviation.Drawdown.FiniteVarianceUpper.Lemmas.Rate.Endpoint

/-!
# Finite-variance drawdown upper bounds

The public theorems in this file are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.measureReal_noLargeDropEndpointBelowEvent_le_exp_of_finiteVariance`:
  for centered increments of variance $\sigma^2>0$ and
  $0<d<\pi^2\sigma^2/2$, sufficiently large $\Delta$ and
  $L\ge\Delta^{2+c}$ give
  $\mathbb P(\forall i\le j\le L,\ Y_i-Y_j\le\Delta,\ Y_L\le\Delta/c)
  \le e^{-dL/\Delta^2}$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.exists_uniform_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_of_centeredSecondMoment`:
  a uniform version for all large widths and superquadratic horizons.

The probability estimate formalizes Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.3,
following its discretized-maximum and conditional-block proof. It extends
Elie Aïdékon and Yueyun Hu, *Average-weight percolation on the complete
graph*, Lemma 2.3 (2025, arXiv:2512.23266). The one-block estimate uses
Aïdékon and Hu's Lemma 4.1 together with Theorem 3, Section 4, p. 764 of
A. A. Mogul'skii, “Small deviations in the sample function space,” *Teoriya
Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; English translation,
“Small Deviations in a Space of Trajectories,” *Theory of Probability and Its
Applications* 19(1) (1975), 726--736, DOI 10.1137/1119081.
-/

open Filter MeasureTheory Topology
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- Finite-variance no-large-drawdown estimate in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3,
Lemma 3.3. It extends Elie Aïdékon and Yueyun Hu, *Average-weight percolation
on the complete graph*, Lemma 2.3 (2025, arXiv:2512.23266). The block proof
follows Wang Yiyang's Lemma 3.3: discretize the running maximum, encode its
jump blocks, and apply Chapter 3, Lemma 3.2. The one-block estimate uses
Aïdékon and Hu's Lemma 4.1 and Theorem 3, Section 4, p. 764 of A. A.
Mogul'skii, “Small deviations in the sample function space,” *Teoriya
Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; English translation,
“Small Deviations in a Space of Trajectories,” *Theory of Probability and Its
Applications* 19(1) (1975), 726--736, DOI 10.1137/1119081.

For
\[
  B_{L,\Delta,c}:=\left\{Y_L\leq\frac{\Delta}{c},\quad
    \min_{0\leq i\leq j\leq L}(Y_j-Y_i)\geq-\Delta\right\},
\]
the conclusion is `P(B_{L,Δ,c}) ≤ exp(-d L / Δ²)` whenever `Δ` is large
enough and `L ≥ Δ^(2+c)`. -/
theorem measureReal_noLargeDropEndpointBelowEvent_le_exp_of_finiteVariance
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {variance c d : ℝ}
    (hν : ProbabilityTheory.IsCenteredSecondMoment ν variance)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < variance) (hc : 0 < c) (hd : 0 < d)
    (hcritical : d < (Real.pi ^ 2 / 2) * variance) :
    ∃ Delta₀ : ℝ, 1 ≤ Delta₀ ∧
      ∀ Delta ≥ Delta₀, ∀ horizon : ℕ,
        Delta ^ (2 + c) ≤ (horizon : ℝ) →
        (iidSequenceLaw ν).real
          (noLargeDropEndpointBelowEvent horizon Delta (Delta / c)) ≤
          Real.exp (-d * ((horizon : ℝ) / Delta ^ 2)) := by
  by_cases hcSmall : c < 1 / 2
  · obtain ⟨Delta₀, hDelta₀, hbound⟩ :=
      exists_eventually_measureReal_noLargeDropEvent_le_exp_of_endpointAndHorizonPowers
        ν hν hsquare hvariance hc hc hd hcritical
    refine ⟨Delta₀, hDelta₀, ?_⟩
    intro Delta hDelta horizon hhorizon
    exact hbound Delta hDelta horizon hhorizon
  · let c' : ℝ := 1 / 2 - 1 / (2 + c)
    have hcHalf : 1 / 2 ≤ c := le_of_not_gt hcSmall
    have hcPlus : 0 < 2 + c := by linarith
    have hc'Form : c' = c / (2 * (2 + c)) := by
      dsimp [c']
      field_simp [ne_of_gt hcPlus]
      ring
    have hc'Pos : 0 < c' := by
      rw [hc'Form]
      positivity
    have hc'LtHalf : c' < 1 / 2 := by
      dsimp [c']
      have hreciprocal : 0 < 1 / (2 + c) := by positivity
      linarith
    have hc'LeC : c' ≤ c := le_trans hc'LtHalf.le hcHalf
    have htransformedExponent : 2 / (1 - 2 * c') = 2 + c := by
      have hdenominator : 1 - 2 * c' = 2 / (2 + c) := by
        dsimp [c']
        field_simp [ne_of_gt hcPlus]
        ring
      rw [hdenominator]
      field_simp [ne_of_gt hcPlus]
    have hhorizonPowerPos : 0 < 2 / (1 - 2 * c') - 2 := by
      rw [htransformedExponent]
      linarith
    obtain ⟨Delta₀, hDelta₀, hbound⟩ :=
      exists_eventually_measureReal_noLargeDropEvent_le_exp_of_endpointAndHorizonPowers
        (endpointPower := c') (horizonPower := 2 / (1 - 2 * c') - 2)
        ν hν hsquare hvariance hc'Pos hhorizonPowerPos hd hcritical
    refine ⟨Delta₀, hDelta₀, ?_⟩
    intro Delta hDelta horizon hhorizon
    have hhorizon' :
        Delta ^ (2 + (2 / (1 - 2 * c') - 2)) ≤ (horizon : ℝ) := by
      have hexponent : 2 + (2 / (1 - 2 * c') - 2) = 2 + c := by
        rw [htransformedExponent]
        ring
      rw [hexponent]
      exact hhorizon
    have htransformedBound := hbound Delta hDelta horizon hhorizon'
    have hthreshold : Delta / c ≤ Delta / c' := by
      apply (div_le_div_iff₀ hc hc'Pos).2
      exact mul_le_mul_of_nonneg_left hc'LeC (by linarith : 0 ≤ Delta)
    have heventSubset :
        noLargeDropEndpointBelowEvent horizon Delta (Delta / c) ⊆
          noLargeDropEndpointBelowEvent horizon Delta (Delta / c') := by
      intro increment hevent
      exact ⟨hevent.1, le_trans hevent.2 hthreshold⟩
    calc
      (iidSequenceLaw ν).real
          (noLargeDropEndpointBelowEvent horizon Delta (Delta / c)) ≤
        (iidSequenceLaw ν).real
          (noLargeDropEndpointBelowEvent horizon Delta (Delta / c')) :=
        measureReal_mono heventSubset
          (measure_ne_top (iidSequenceLaw ν) _)
      _ ≤ Real.exp (-d * ((horizon : ℝ) / Delta ^ 2)) := by
        simpa using htransformedBound

/-- The finite-variance endpoint estimate is uniform over all horizons that
dominate a prescribed power of the width. This is a direct scaling of Wang
Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.3: choose the smaller of the requested horizon
exponent and the endpoint exponent, then apply the drawdown estimate above.
-/
theorem exists_uniform_iidSequenceLaw_measure_noLargeDropEndpointBelowEvent_le_of_centeredSecondMoment
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : ProbabilityTheory.IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    (endpointRatio target p : ℝ)
    (hEndpointRatio : 0 < endpointRatio)
    (htarget : 0 < target)
    (htargetCritical : target < Real.pi ^ 2 / 2)
    (hp : 0 < p) :
    ∃ delta0 : ℝ, 0 < delta0 ∧
      ∀ delta : ℝ, delta0 ≤ delta → ∀ horizon : ℕ,
        delta ^ (2 + p) ≤ (horizon : ℝ) →
          iidSequenceLaw ν (noLargeDropEndpointBelowEvent
            horizon delta (delta / endpointRatio)) ≤
            ENNReal.ofReal (Real.exp
              (-target * sigma ^ 2 * (horizon : ℝ) / delta ^ 2)) := by
  have hsquare : Integrable (fun x : ℝ => x ^ 2) ν :=
    Integrable.of_integral_ne_zero (by
      rw [hν.2]
      exact ne_of_gt (sq_pos_of_pos hsigma))
  have hvariance : 0 < sigma ^ 2 := sq_pos_of_pos hsigma
  have htargetRate : 0 < target * sigma ^ 2 := mul_pos htarget hvariance
  have hcritical : target * sigma ^ 2 < (Real.pi ^ 2 / 2) * sigma ^ 2 :=
    mul_lt_mul_of_pos_right htargetCritical hvariance
  let endpointPower : ℝ := min p endpointRatio
  have hendpointPowerPos : 0 < endpointPower := by
    dsimp [endpointPower]
    exact lt_min hp hEndpointRatio
  have hendpointPowerLeP : endpointPower ≤ p := min_le_left _ _
  have hendpointPowerLeRatio : endpointPower ≤ endpointRatio :=
    min_le_right _ _
  obtain ⟨Delta0, hDelta0, hbound⟩ :=
    measureReal_noLargeDropEndpointBelowEvent_le_exp_of_finiteVariance
      ν hν hsquare hvariance hendpointPowerPos htargetRate hcritical
  refine ⟨Delta0, lt_of_lt_of_le (by norm_num) hDelta0, ?_⟩
  intro delta hdelta horizon hlarge
  have hdeltaOne : 1 ≤ delta := hDelta0.trans hdelta
  have hdeltaPos : 0 < delta := lt_of_lt_of_le (by norm_num) hdeltaOne
  have hpower : delta ^ (2 + endpointPower) ≤ delta ^ (2 + p) :=
    Real.rpow_le_rpow_of_exponent_le hdeltaOne (by linarith)
  have hlarge' : delta ^ (2 + endpointPower) ≤ (horizon : ℝ) :=
    hpower.trans hlarge
  have hbound' := hbound delta hdelta horizon hlarge'
  have hthreshold : delta / endpointRatio ≤ delta / endpointPower :=
    (div_le_div_iff₀ hEndpointRatio hendpointPowerPos).2
      (mul_le_mul_of_nonneg_left hendpointPowerLeRatio hdeltaPos.le)
  have hsubset :
      noLargeDropEndpointBelowEvent horizon delta
          (delta / endpointRatio) ⊆
        noLargeDropEndpointBelowEvent horizon delta
          (delta / endpointPower) := by
    intro increment hevent
    exact ⟨hevent.1, hevent.2.trans hthreshold⟩
  have hrealBound :
      (iidSequenceLaw ν).real
          (noLargeDropEndpointBelowEvent horizon delta
            (delta / endpointRatio)) ≤
        Real.exp (-target * sigma ^ 2 * (horizon : ℝ) / delta ^ 2) := by
    calc
      _ ≤ (iidSequenceLaw ν).real
          (noLargeDropEndpointBelowEvent horizon delta
            (delta / endpointPower)) :=
        measureReal_mono hsubset (measure_ne_top (iidSequenceLaw ν) _)
      _ ≤ Real.exp (-target * sigma ^ 2 * (horizon : ℝ) / delta ^ 2) := by
        have hexponent : -(target * sigma ^ 2) *
            ((horizon : ℝ) / delta ^ 2) =
            -target * sigma ^ 2 * (horizon : ℝ) / delta ^ 2 := by ring
        rw [← hexponent]
        exact hbound'
  let event := noLargeDropEndpointBelowEvent horizon delta
    (delta / endpointRatio)
  let q : ℝ≥0∞ := iidSequenceLaw ν event
  have hqle : q ≤ 1 := by
    calc
      q ≤ iidSequenceLaw ν Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  have hqtop : q ≠ ∞ := ne_of_lt (lt_of_le_of_lt hqle ENNReal.one_lt_top)
  have hrealQ : q.toReal ≤
      Real.exp (-target * sigma ^ 2 * (horizon : ℝ) / delta ^ 2) := by
    simpa [q, event, Measure.real] using hrealBound
  change q ≤ ENNReal.ofReal
    (Real.exp (-target * sigma ^ 2 * (horizon : ℝ) / delta ^ 2))
  rw [← ENNReal.ofReal_toReal hqtop]
  exact (ENNReal.ofReal_le_ofReal_iff (Real.exp_nonneg _)).2 hrealQ

end ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

end
