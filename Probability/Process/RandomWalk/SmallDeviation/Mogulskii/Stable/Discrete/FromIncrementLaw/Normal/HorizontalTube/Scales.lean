/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.Scale.Inverse.Superquadratic
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.FromIncrementLaw.Normal.HorizontalTube.Basic
import Analysis.Asymptotics.Scale.Sampling
/-!
# Sampled and inverse-scale forms of the horizontal-tube rate



## Public declarations

Write $S_j=\sum_{i=1}^j X_i$ for the partial sums of centered i.i.d.
increments with finite variance $\sigma^2>0$. In each limit below,
$0<a<1$ and $\mathbb P$ is the law of the increment sequence.

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.centeredFiniteVariance_closedHorizontalTubeProbabilityRate_along`: for increasing times $t_k$ and integer widths $w_k\to\infty$ with $w_k^2/t_k\to0$, $\frac{w_k^2}{t_k-1}\log\mathbb P(S_j\in[-aw_k,(1-a)w_k],\ 0\le j<t_k)\to-\frac{\pi^2}{2}\sigma^2$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.centeredFiniteVariance_closedHorizontalTubeProbabilityRate_realWidthAlong`: the same limit for positive real widths $w_k\to\infty$ with $w_k^2/t_k\to0$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.centeredFiniteVariance_closedHorizontalTubeProbabilityRate_realWidth`: for positive real $D\to\infty$ and integer horizons $L(D)\to\infty$ with $D^2/L(D)\to0$, $\frac{D^2}{L(D)}\log\mathbb P(S_j\in[-aD,(1-a)D],\ 0\le j<L(D))\to-\frac{\pi^2}{2}\sigma^2$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.inverseScale_closedHorizontalTubeProbabilityRate` and `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.upperInverseScale_closedHorizontalTubeProbabilityRate`: the same closed-tube rate along the lower and upper generalized inverses of a superquadratic time scale.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.centeredFiniteVariance_horizontalTubeProbabilityRate`: for a superquadratic integer horizon $L(\Delta)$, $\frac{\Delta^2}{L(\Delta)}\log\mathbb P(S_j\in[-a\Delta,(1-a)\Delta],\ 0\le j<L(\Delta))\to-\frac{\pi^2}{2}\sigma^2$.

Each result is a scale specialization or subsequence consequence of the
core closed-tube rate in `HorizontalTube.Basic.lean`, formalizing Wang
Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring*, Chapter 3, Lemma 3.1(i). Its small-deviation input is Theorem 3,
Section 4, p. 764 of A. A. Mogul'skii, “Small deviations in the sample
function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974),
755--765; English translation, “Small Deviations in a Space of
Trajectories,” *Theory of Probability and Its Applications* 19(4) (1975),
726--736, DOI 10.1137/1119081.
-/

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Measure
open ProbabilityTheory.RandomWalk
open Asymptotics
open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability
open Skorokhod.PathClass.StepCorridor
open scoped ENNReal NNReal Topology


@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- Sampling consequence of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1(i), under its
width-time relation. The sampled statement follows from the real-width rate
proved above. Its rate input is A. A. Mogul'skii, “Small deviations in the
sample function space,” Theorem 3, Section 4, p. 764 (1974); English
translation, “Small Deviations in a Space of Trajectories,” DOI 10.1137/1119081. -/
theorem centeredFiniteVariance_closedHorizontalTubeProbabilityRate_along
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {time width : ℕ → ℕ} (htime : StrictMono time)
    (htimePos : ∀ k, 0 < time k)
    (hwidth : Tendsto (fun k : ℕ => (width k : ℝ)) atTop atTop)
    (hwidthSq : Tendsto (fun k : ℕ => (width k : ℝ) ^ 2 / (time k : ℝ))
      atTop (𝓝 0))
    (hcentered : ∫ x, x ∂ν = 0)
    (hvariance : 0 < ∫ x, x ^ 2 ∂ν)
    {a : ℝ} (ha : 0 < a) (haOne : a < 1) :
    Tendsto
      (fun k : ℕ => (width k : ℝ) ^ 2 / ((time k - 1 : ℕ) : ℝ) * Real.log
        (horizontalTubeProbability (iidSequenceLaw ν) a (width k) (time k - 1)).toReal)
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν))) := by
  let scale := sampledIntegerWidthScale time width htime
  have hsmall := sampledIntegerWidthScale_isSmallDeviationScale
    htime htimePos hwidth hwidthSq
  have hrate := (centeredFiniteVariance_closedHorizontalTubeProbabilityRate
    hsmall hcentered hvariance ha haOne).comp htime.tendsto_atTop
  have hscaleEq : ∀ k : ℕ, scale (time k) = (width k : ℝ) := by
    intro k
    simp [scale, sampledIntegerWidthScale, sampledTimeIntervalIndex_at_time htime]
  have hsourceRate : Tendsto
      (fun k : ℕ => (width k : ℝ) ^ 2 / (time k : ℝ) * Real.log
        (horizontalTubeProbability (iidSequenceLaw ν) a (width k) (time k - 1)).toReal)
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν))) := by
    have heq : (fun k : ℕ => scale (time k) ^ 2 / (time k : ℝ) * Real.log
        (horizontalTubeProbability (iidSequenceLaw ν) a (scale (time k)) (time k - 1)).toReal) =
        (fun k : ℕ => (width k : ℝ) ^ 2 / (time k : ℝ) * Real.log
          (horizontalTubeProbability (iidSequenceLaw ν) a (width k) (time k - 1)).toReal) := by
      funext k
      rw [hscaleEq]
    have heq' : (fun k : ℕ => scale (time k) ^ 2 / (time k : ℝ) * Real.log
        (horizontalTubeProbability (iidSequenceLaw ν) a (scale (time k)) (time k - 1)).toReal) =ᶠ[atTop]
        (fun k : ℕ => (width k : ℝ) ^ 2 / (time k : ℝ) * Real.log
          (horizontalTubeProbability (iidSequenceLaw ν) a (width k) (time k - 1)).toReal) := by
      filter_upwards with k
      exact congrFun heq k
    simpa only [Function.comp_def] using hrate.congr' heq'
  have hratioNat : Tendsto (fun n : ℕ => (n : ℝ) / ((n - 1 : ℕ) : ℝ))
      atTop (𝓝 (1 : ℝ)) := by
    have hratioBase : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) - 1))
        atTop (𝓝 (1 : ℝ)) := by
      simpa [sub_eq_add_neg] using tendsto_natCast_div_add_atTop (-1 : ℝ)
    have hratioEq : (fun n : ℕ => (n : ℝ) / ((n - 1 : ℕ) : ℝ)) =ᶠ[atTop]
        fun n : ℕ => (n : ℝ) / ((n : ℝ) - 1) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hn1 : 1 ≤ n := by omega
      simp [Nat.cast_sub hn1]
    exact hratioBase.congr' hratioEq.symm
  have hfactor := hratioNat.comp htime.tendsto_atTop
  have hproduct := hfactor.mul hsourceRate
  have hproductEq : (fun k : ℕ =>
      ((time k : ℝ) / ((time k - 1 : ℕ) : ℝ)) *
        ((width k : ℝ) ^ 2 / (time k : ℝ) * Real.log
          (horizontalTubeProbability (iidSequenceLaw ν) a (width k) (time k - 1)).toReal)) =ᶠ[atTop]
      (fun k : ℕ => (width k : ℝ) ^ 2 / ((time k - 1 : ℕ) : ℝ) * Real.log
        (horizontalTubeProbability (iidSequenceLaw ν) a (width k) (time k - 1)).toReal) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with k hk
    have htimeNe : (time k : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast (htimePos k))
    have hpredNat : 0 < time k - 1 := by
      have hk' : 1 < k := by omega
      have htimeStep : time 1 < time k := htime hk'
      have htimeOne : 0 < time 1 := htimePos 1
      omega
    have hpredPos : 0 < ((time k - 1 : ℕ) : ℝ) := by exact_mod_cast hpredNat
    have hpredNe : ((time k - 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hpredPos
    field_simp [htimeNe, hpredNe]
  simpa only [one_mul] using hproduct.congr' hproductEq



/-- For strictly increasing integer times $t_k$ and positive real widths
$w_k\to\infty$ with $w_k^2/t_k\to0$, centered increments of finite positive
variance satisfy
$\frac{w_k^2}{t_k-1}\log\mathbb P(S_j\in[-aw_k,(1-a)w_k],\ 0\le j<t_k)
\to-\frac{\pi^2}{2}\sigma^2$. This is the real-width sampled form of Wang
Yiyang's Chapter 3, Lemma 3.1(i), with the rate input from A. A. Mogul'skii's
Theorem 3, Section 4, p. 764. -/
theorem centeredFiniteVariance_closedHorizontalTubeProbabilityRate_realWidthAlong
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {time : ℕ → ℕ} {width : ℕ → ℝ} (htime : StrictMono time)
    (htimePos : ∀ k, 0 < time k) (hwidthPos : ∀ k, 0 < width k)
    (hwidth : Tendsto width atTop atTop)
    (hwidthSq : Tendsto (fun k : ℕ => width k ^ 2 / (time k : ℝ))
      atTop (𝓝 0))
    (hcentered : ∫ x, x ∂ν = 0)
    (hvariance : 0 < ∫ x : ℝ, x ^ 2 ∂ν)
    {a : ℝ} (ha : 0 < a) (haOne : a < 1) :
    Tendsto
      (fun k : ℕ => width k ^ 2 / ((time k - 1 : ℕ) : ℝ) * Real.log
        (horizontalTubeProbability (iidSequenceLaw ν) a (width k)
          (time k - 1)).toReal)
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * (∫ x : ℝ, x ^ 2 ∂ν))) := by
  let scale := sampledRealWidthScale time width htime
  have hsmall := sampledRealWidthScale_isSmallDeviationScale
    htime htimePos hwidthPos hwidth hwidthSq
  have hrate := (centeredFiniteVariance_closedHorizontalTubeProbabilityRate
    hsmall hcentered hvariance ha haOne).comp htime.tendsto_atTop
  have hscaleEq : ∀ k : ℕ, scale (time k) = width k := by
    intro k
    simp [scale, sampledRealWidthScale,
      sampledTimeIntervalIndex_at_time htime]
  have hsourceRate : Tendsto
      (fun k : ℕ => width k ^ 2 / (time k : ℝ) * Real.log
        (horizontalTubeProbability (iidSequenceLaw ν) a (width k)
          (time k - 1)).toReal)
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * (∫ x : ℝ, x ^ 2 ∂ν))) := by
    have heq : (fun k : ℕ => scale (time k) ^ 2 / (time k : ℝ) *
        Real.log (horizontalTubeProbability (iidSequenceLaw ν) a
          (scale (time k)) (time k - 1)).toReal) =
        (fun k : ℕ => width k ^ 2 / (time k : ℝ) * Real.log
          (horizontalTubeProbability (iidSequenceLaw ν) a (width k)
            (time k - 1)).toReal) := by
      funext k
      rw [hscaleEq]
    exact hrate.congr' (Filter.Eventually.of_forall
      fun k => congrFun heq k)
  have hratioNat : Tendsto
      (fun n : ℕ => (n : ℝ) / ((n - 1 : ℕ) : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    have hratioBase : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) - 1))
        atTop (𝓝 (1 : ℝ)) := by
      simpa [sub_eq_add_neg] using tendsto_natCast_div_add_atTop (-1 : ℝ)
    have hratioEq : (fun n : ℕ => (n : ℝ) / ((n - 1 : ℕ) : ℝ)) =ᶠ[atTop]
        fun n : ℕ => (n : ℝ) / ((n : ℝ) - 1) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hn1 : 1 ≤ n := by omega
      simp [Nat.cast_sub hn1]
    exact hratioBase.congr' hratioEq.symm
  have hfactor := hratioNat.comp htime.tendsto_atTop
  have hproduct := hfactor.mul hsourceRate
  have hproductEq : (fun k : ℕ =>
      ((time k : ℝ) / ((time k - 1 : ℕ) : ℝ)) *
        (width k ^ 2 / (time k : ℝ) *
          Real.log (horizontalTubeProbability (iidSequenceLaw ν) a
            (width k) (time k - 1)).toReal)) =ᶠ[atTop]
      (fun k : ℕ => width k ^ 2 / ((time k - 1 : ℕ) : ℝ) *
        Real.log (horizontalTubeProbability (iidSequenceLaw ν) a
          (width k) (time k - 1)).toReal) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with k hk
    have htimeNe : (time k : ℝ) ≠ 0 :=
      ne_of_gt (by exact_mod_cast (htimePos k))
    have hpredNat : 0 < time k - 1 := by
      have hk' : 1 < k := by omega
      have htimeStep : time 1 < time k := htime hk'
      have htimeOne : 0 < time 1 := htimePos 1
      omega
    have hpredPos : 0 < ((time k - 1 : ℕ) : ℝ) := by exact_mod_cast hpredNat
    have hpredNe : ((time k - 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hpredPos
    field_simp [htimeNe, hpredNe]
  simpa only [one_mul] using hproduct.congr' hproductEq

/-- For $D\to\infty$ and an integer horizon $L(D)\to\infty$ satisfying
$D^2/L(D)\to0$, centered increments of finite positive variance satisfy
$\frac{D^2}{L(D)}\log\mathbb P(S_j\in[-aD,(1-a)D],\ 0\le j<L(D))
\to-\frac{\pi^2}{2}\sigma^2$. This is the real-width form of Wang Yiyang's
Chapter 3, Lemma 3.1(i), using A. A. Mogul'skii's Theorem 3, Section 4,
p. 764. -/
theorem centeredFiniteVariance_closedHorizontalTubeProbabilityRate_realWidth
    {L : ℝ → ℕ} (hL : Tendsto L atTop atTop)
    (hquadratic : Tendsto (fun D : ℝ => D ^ 2 / (L D : ℝ)) atTop (𝓝 0))
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hvariance : 0 < ∫ x, x ^ 2 ∂ν)
    {a : ℝ} (ha : 0 < a) (haOne : a < 1) :
    Tendsto
      (fun D : ℝ => D ^ 2 / (L D : ℝ) * Real.log
        (horizontalTubeProbability (iidSequenceLaw ν) a D (L D)).toReal)
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν))) := by
  apply tendsto_realWidthRate_of_sampledTime
    (rate := fun D n => D ^ 2 / (n : ℝ) * Real.log
      (horizontalTubeProbability (iidSequenceLaw ν) a D n).toReal)
    (limit := -(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν)) hL hquadratic
  intro time width htime htimePos hwidthPos hwidth hwidthSq
  simpa using
    centeredFiniteVariance_closedHorizontalTubeProbabilityRate_realWidthAlong
      htime htimePos hwidthPos hwidth hwidthSq
      hcentered hvariance ha haOne

/-- Along the generalized inverse width of a superquadratic horizon,
$\frac{(\operatorname{inverseScale}L(n))^2}{n-1}
\log\mathbb P(S_j\in[-a\operatorname{inverseScale}L(n),
(1-a)\operatorname{inverseScale}L(n)],\ 1\le j<n)\to-\frac{\pi^2}{2}\sigma^2$.
This is the inverse-scale form of Wang Yiyang's Chapter 3, Lemma 3.1(i),
with rate input from A. A. Mogul'skii's Theorem 3, Section 4, p. 764. -/
theorem inverseScale_closedHorizontalTubeProbabilityRate
    {L : ℕ → ℕ}
    (hL : Tendsto L atTop atTop)
    (hquadratic : Asymptotics.IsSuperquadraticScale L)
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hvariance : 0 < ∫ x, x ^ 2 ∂ν)
    {a : ℝ} (ha : 0 < a) (haOne : a < 1) :
    Tendsto (fun n : ℕ => (Asymptotics.inverseScale L n : ℝ) ^ 2 /
      ((n - 1 : ℕ) : ℝ) * Real.log
        (horizontalTubeProbability (iidSequenceLaw ν) a
          (Asymptotics.inverseScale L n) (n - 1)).toReal)
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν))) := by
  apply tendsto_scaledRate_div_predTime (time := fun n : ℕ => n) tendsto_id
  exact centeredFiniteVariance_closedHorizontalTubeProbabilityRate
    (Asymptotics.isSmallDeviationScale_inverseScale hL hquadratic)
    hcentered hvariance ha haOne

/-- Along the upper generalized inverse width of a superquadratic horizon,
$\frac{(\operatorname{upperInverseScale}L(n))^2}{n-1}
\log\mathbb P(S_j\in[-a\operatorname{upperInverseScale}L(n),
(1-a)\operatorname{upperInverseScale}L(n)],\ 1\le j<n)\to-\frac{\pi^2}{2}\sigma^2$.
This is the upper-inverse form of Wang Yiyang's Chapter 3, Lemma 3.1(i),
with rate input from A. A. Mogul'skii's Theorem 3, Section 4, p. 764. -/
theorem upperInverseScale_closedHorizontalTubeProbabilityRate
    {L : ℕ → ℕ}
    (hL : Tendsto L atTop atTop)
    (hquadratic : Asymptotics.IsSuperquadraticScale L)
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hvariance : 0 < ∫ x, x ^ 2 ∂ν)
    {a : ℝ} (ha : 0 < a) (haOne : a < 1) :
    Tendsto (fun n : ℕ => (Asymptotics.upperInverseScale L n : ℝ) ^ 2 /
      ((n - 1 : ℕ) : ℝ) * Real.log
        (horizontalTubeProbability (iidSequenceLaw ν) a
          (Asymptotics.upperInverseScale L n) (n - 1)).toReal)
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν))) := by
  apply tendsto_scaledRate_div_predTime (time := fun n : ℕ => n) tendsto_id
  exact centeredFiniteVariance_closedHorizontalTubeProbabilityRate
    (Asymptotics.isSmallDeviationScale_upperInverseScale hL hquadratic)
    hcentered hvariance ha haOne

/-- Integer-width form of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1(i). The proof
interpolates along a subsequence of strictly increasing times. Its rate is
Mogul'skii, Theorem 3, Section 4, p. 764, in “Small deviations in the sample
function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974),
755–765; English translation, “Small Deviations in a Space of Trajectories,”
*Theory of Probability and Its Applications* 19(4) (1975), 726–736, DOI
10.1137/1119081. -/
theorem centeredFiniteVariance_horizontalTubeProbabilityRate
    {L : ℕ → ℕ} (hL : Tendsto L atTop atTop)
    (hquadratic : Asymptotics.IsSuperquadraticScale L)
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hcentered : ∫ x, x ∂ν = 0)
    (hvariance : 0 < ∫ x, x ^ 2 ∂ν)
    {a : ℝ} (ha : 0 < a) (haOne : a < 1) :
    Tendsto
      (fun Δ : ℕ => (Δ : ℝ) ^ 2 / (L Δ : ℝ) * Real.log
        (horizontalTubeProbability (iidSequenceLaw ν) a Δ (L Δ)).toReal)
      atTop (𝓝 (-(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν))) := by
  let rate : ℕ → ℝ := fun Δ => (Δ : ℝ) ^ 2 / (L Δ : ℝ) * Real.log
    (horizontalTubeProbability (iidSequenceLaw ν) a Δ (L Δ)).toReal
  let c : ℝ := -(Real.pi ^ 2) / 2 * (∫ x, x ^ 2 ∂ν)
  apply Metric.tendsto_atTop.2
  intro ε hε
  by_contra hnot
  have hbad : ∀ N : ℕ, ∃ Δ > N, ε ≤ dist (rate Δ) c := by
    intro N
    by_contra hN
    apply hnot
    refine ⟨N + 1, ?_⟩
    intro Δ hΔ
    by_contra hdist
    apply hN
    refine ⟨Δ, lt_of_lt_of_le (Nat.lt_succ_self N) hΔ,
      le_of_not_gt hdist⟩
  obtain ⟨widthSeq, hwidthStrict, hwidthBad⟩ :=
    Nat.exists_strictMono_subsequence hbad
  let rawTime : ℕ → ℕ := fun k => L (widthSeq k) + 1
  have hLwidth : Tendsto (fun k => L (widthSeq k)) atTop atTop :=
    hL.comp hwidthStrict.tendsto_atTop
  have hrawTime : Tendsto rawTime atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [hLwidth.eventually (eventually_ge_atTop b)] with k hk
    dsimp [rawTime]
    omega
  obtain ⟨φ, hφ, hφtime⟩ := strictMono_subseq_of_tendsto_atTop hrawTime
  let widthSub : ℕ → ℕ := fun k => widthSeq (φ k)
  let timeSub : ℕ → ℕ := fun k => rawTime (φ k)
  have htimeSub : StrictMono timeSub := by
    simpa [timeSub, rawTime, Function.comp_def] using hφtime
  have hwidthSubTop : Tendsto widthSub atTop atTop :=
    hwidthStrict.tendsto_atTop.comp hφ.tendsto_atTop
  have hwidthSubRealTop : Tendsto (fun k => (widthSub k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hwidthSubTop
  have hwidthSqRaw : Tendsto
      (fun k => (widthSeq k : ℝ) ^ 2 / ((L (widthSeq k) : ℝ) + 1))
      atTop (𝓝 0) :=
    (Asymptotics.tendsto_width_sq_div_shiftedScale_of_superquadratic hquadratic).comp
      hwidthStrict.tendsto_atTop
  have hwidthSqSub : Tendsto
      (fun k => (widthSub k : ℝ) ^ 2 / (timeSub k : ℝ))
      atTop (𝓝 0) := by
    simpa [widthSub, timeSub, rawTime, Function.comp_def] using
      hwidthSqRaw.comp hφ.tendsto_atTop
  have hrateSub :=
    centeredFiniteVariance_closedHorizontalTubeProbabilityRate_along
      htimeSub (fun k => by dsimp [timeSub, rawTime]; omega)
      hwidthSubRealTop hwidthSqSub hcentered hvariance ha haOne
  have hrateOnWidths : Tendsto (fun k => rate (widthSub k)) atTop (𝓝 c) := by
    simpa [rate, widthSub, timeSub, rawTime, Function.comp_def,
      Nat.add_sub_cancel_right] using hrateSub
  have hclose : ∀ᶠ k : ℕ in atTop, dist (rate (widthSub k)) c < ε :=
    hrateOnWidths.eventually (Metric.ball_mem_nhds c hε)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hclose
  have hlt := hN N le_rfl
  have hge : ε ≤ dist (rate (widthSub N)) c := hwidthBad (φ N)
  exact (not_lt_of_ge hge) hlt


end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

end
