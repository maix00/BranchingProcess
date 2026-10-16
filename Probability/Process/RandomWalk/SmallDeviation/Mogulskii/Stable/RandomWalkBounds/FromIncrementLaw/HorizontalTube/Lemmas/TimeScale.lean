/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.Scale.InverseScale
public import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.RandomWalkBounds.FromIncrementLaw.Normal.ContinuousBoundary
/-!
# Proof lemmas for sampled horizontal-tube scales

The proof-support declarations in this module serve the real-width and sampled-width forms of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1:

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.HorizontalTube.Lemmas.exists_later_time_index`, `increasingTimeIntervalIndex_spec`, and `increasingTimeIntervalIndex_le_of_mem`: existence of an interval $k$ with $n<t_{k+1}$, the defining inequality for the least such index, and minimality $k(n)\le k$ whenever $n<t_{k+1}$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.HorizontalTube.Lemmas.increasingTimeIntervalIndex`: the least $k$ with $n< t_{k+1}$ for a strictly increasing time sequence $t$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.HorizontalTube.Lemmas.increasingTimeIntervalIndex_lower_bound`: if $t_0\le n$, then $t_{k(n)}\le n$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.HorizontalTube.Lemmas.increasingTimeIntervalIndex_tendsto`: if $t$ is strictly increasing, then $k(n)\to\infty$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.HorizontalTube.Lemmas.increasingTimeIntervalIndex_at_time`: at a sampled time, the interval index is exact: $k(t_j)=j$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.HorizontalTube.Lemmas.increasingTimeAuxiliaryScale`: the piecewise-constant integer width $w_{k(n)}$ for integer-valued width sequences.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.HorizontalTube.Lemmas.increasingTimeAuxiliaryScale_isSmallDeviationScale`: if $w_k\to\infty$ and $w_k^2/t_k\to0$, then the integer-width interpolation is a small-deviation scale against $\sqrt n$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.HorizontalTube.Lemmas.increasingTimeRealAuxiliaryScale`: the piecewise-constant real width $w_{k(n)}$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.HorizontalTube.Lemmas.increasingTimeRealAuxiliaryScale_isSmallDeviationScale`: if $w_k\to\infty$ and $w_k^2/t_k\to0$, then $w_{k(n)}$ is a small-deviation scale against $\sqrt n$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.HorizontalTube.Lemmas.tendsto_realWidthRate_of_sampledTime`: convergence of $R(w_k,t_k-1)$ along every increasing sampled pair implies convergence of $R(D,L(D))$ when $L(D)\to\infty$ and $D^2/L(D)\to0$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.HorizontalTube.Lemmas.tendsto_scaledLog_div_predTime`: replacing the normalization $w_k^2/t_k$ by $w_k^2/(t_k-1)$ preserves a finite limiting rate.

These are theorem-family proof steps, not independent results in the public small-deviation API.
-/

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.Measure
open ProbabilityTheory.RandomWalk
open ProbabilityTheory.Process.Path.PathClass.StepCorridor.Probability
open Skorokhod.PathClass.StepCorridor
open scoped ENNReal NNReal Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.HorizontalTube.Lemmas

theorem exists_later_time_index {time : ℕ → ℕ}
    (htime : StrictMono time) (n : ℕ) : ∃ k, n < time (k + 1) := by
  obtain ⟨k, hk⟩ := (htime.tendsto_atTop.eventually_gt_atTop n).exists
  exact ⟨k, lt_of_lt_of_le hk (Nat.le_of_lt (htime (Nat.lt_succ_self k)))⟩

/-- The index of the half-open time interval `[time k, time (k + 1))`
containing `n`. -/
noncomputable def increasingTimeIntervalIndex (time : ℕ → ℕ)
    (htime : StrictMono time) (n : ℕ) : ℕ :=
  Nat.find (exists_later_time_index htime n)

theorem increasingTimeIntervalIndex_spec {time : ℕ → ℕ}
    (htime : StrictMono time) (n : ℕ) :
    n < time (increasingTimeIntervalIndex time htime n + 1) :=
  by
  change n < time (Nat.find (exists_later_time_index htime n) + 1)
  exact Nat.find_spec (exists_later_time_index htime n)

theorem increasingTimeIntervalIndex_le_of_mem {time : ℕ → ℕ}
    (htime : StrictMono time) (n k : ℕ) (hnk : n < time (k + 1)) :
    increasingTimeIntervalIndex time htime n ≤ k := by
  change Nat.find (exists_later_time_index htime n) ≤ k
  exact Nat.find_min' (exists_later_time_index htime n) hnk

theorem increasingTimeIntervalIndex_lower_bound {time : ℕ → ℕ}
    (htime : StrictMono time) {n : ℕ} (hstart : time 0 ≤ n) :
    time (increasingTimeIntervalIndex time htime n) ≤ n := by
  by_contra hnot
  have hlt : n < time (increasingTimeIntervalIndex time htime n) := Nat.lt_of_not_ge hnot
  by_cases hzero : increasingTimeIntervalIndex time htime n = 0
  · rw [hzero] at hlt
    exact (not_lt_of_ge hstart) hlt
  · have hindexPos : 0 < increasingTimeIntervalIndex time htime n :=
      Nat.pos_of_ne_zero hzero
    let k := increasingTimeIntervalIndex time htime n - 1
    have hk : k + 1 = increasingTimeIntervalIndex time htime n := by
      dsimp [k]
      omega
    have hmin := increasingTimeIntervalIndex_le_of_mem htime n k (by simpa [hk] using hlt)
    omega

theorem increasingTimeIntervalIndex_tendsto {time : ℕ → ℕ}
    (htime : StrictMono time) :
    Tendsto (increasingTimeIntervalIndex time htime) atTop atTop := by
  rw [tendsto_atTop]
  intro k
  filter_upwards [eventually_ge_atTop (time k)] with n hn
  by_contra hnot
  have hindex : increasingTimeIntervalIndex time htime n < k := Nat.lt_of_not_ge hnot
  have hindexTime : time (increasingTimeIntervalIndex time htime n + 1) ≤ time k :=
    htime.monotone (by omega)
  have hspec := increasingTimeIntervalIndex_spec htime n
  omega

theorem increasingTimeIntervalIndex_at_time {time : ℕ → ℕ}
    (htime : StrictMono time) (k : ℕ) :
    increasingTimeIntervalIndex time htime (time k) = k := by
  apply le_antisymm
  · exact increasingTimeIntervalIndex_le_of_mem htime (time k) k
      (htime (Nat.lt_succ_self k))
  · by_contra hnot
    have hindex : increasingTimeIntervalIndex time htime (time k) < k :=
      Nat.lt_of_not_ge hnot
    have hindexTime : time (increasingTimeIntervalIndex time htime (time k) + 1) ≤ time k :=
      htime.monotone (by omega)
    have hspec := increasingTimeIntervalIndex_spec htime (time k)
    omega

noncomputable def increasingTimeAuxiliaryScale (time width : ℕ → ℕ)
    (htime : StrictMono time) : ℕ → ℝ := fun n =>
  (width (increasingTimeIntervalIndex time htime n) : ℝ)

theorem increasingTimeAuxiliaryScale_isSmallDeviationScale
    {time width : ℕ → ℕ} (htime : StrictMono time)
    (htimePos : ∀ k, 0 < time k)
    (hwidth : Tendsto (fun k : ℕ => (width k : ℝ)) atTop atTop)
    (hwidthSq : Tendsto (fun k : ℕ => (width k : ℝ) ^ 2 / (time k : ℝ))
      atTop (𝓝 0)) :
    Asymptotics.IsSmallDeviationScale
      (increasingTimeAuxiliaryScale time width htime)
      (fun n => Real.sqrt (n : ℝ)) := by
  have hindex := increasingTimeIntervalIndex_tendsto htime
  have hscaleTop : Tendsto (increasingTimeAuxiliaryScale time width htime) atTop atTop :=
    hwidth.comp hindex
  have hwidthSqComp := hwidthSq.comp hindex
  have hscaleSqNonneg (n : ℕ) :
      0 ≤ (increasingTimeAuxiliaryScale time width htime n) ^ 2 / (n : ℝ) :=
    div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have hscaleSqUpper :
      (fun n : ℕ => (increasingTimeAuxiliaryScale time width htime n) ^ 2 / (n : ℝ)) ≤ᶠ[atTop]
        (fun n => (width (increasingTimeIntervalIndex time htime n) : ℝ) ^ 2 /
          (time (increasingTimeIntervalIndex time htime n) : ℝ)) := by
    filter_upwards [eventually_ge_atTop (time 0)] with n hn
    let k := increasingTimeIntervalIndex time htime n
    have hkn := increasingTimeIntervalIndex_lower_bound htime hn
    have hkpos : 0 < (time k : ℝ) := by exact_mod_cast htimePos k
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (htimePos 0) hn)
    have hdenom : (time k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
    have hnum : 0 ≤ (width k : ℝ) ^ 2 := sq_nonneg _
    have hcross : (width k : ℝ) ^ 2 * (time k : ℝ) ≤
        (width k : ℝ) ^ 2 * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hdenom hnum
    have hdiv : (width k : ℝ) ^ 2 / (n : ℝ) ≤
        (width k : ℝ) ^ 2 / (time k : ℝ) :=
      (div_le_div_iff₀ hnpos hkpos).2 (by simpa [mul_comm] using hcross)
    simpa [k, increasingTimeAuxiliaryScale] using hdiv
  have hscaleSq : Tendsto
      (fun n : ℕ => (increasingTimeAuxiliaryScale time width htime n) ^ 2 / (n : ℝ))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hwidthSqComp
      (Filter.Eventually.of_forall hscaleSqNonneg) hscaleSqUpper
  have hscaleRatio := Asymptotics.tendsto_div_sqrt_atTop_zero_of_tendsto_sq_div_atTop_zero
    (fun n => Nat.cast_nonneg (width (increasingTimeIntervalIndex time htime n))) hscaleSq
  exact Asymptotics.IsSmallDeviationScale.of_tendsto hscaleTop hscaleRatio

noncomputable def increasingTimeRealAuxiliaryScale
    (time : ℕ → ℕ) (width : ℕ → ℝ) (htime : StrictMono time) : ℕ → ℝ :=
  fun n => width (increasingTimeIntervalIndex time htime n)

theorem increasingTimeRealAuxiliaryScale_isSmallDeviationScale
    {time : ℕ → ℕ} {width : ℕ → ℝ} (htime : StrictMono time)
    (htimePos : ∀ k, 0 < time k) (hwidthPos : ∀ k, 0 < width k)
    (hwidth : Tendsto width atTop atTop)
    (hwidthSq : Tendsto (fun k => width k ^ 2 / (time k : ℝ))
      atTop (𝓝 0)) :
    Asymptotics.IsSmallDeviationScale
      (increasingTimeRealAuxiliaryScale time width htime)
      (fun n => Real.sqrt (n : ℝ)) := by
  have hindex := increasingTimeIntervalIndex_tendsto htime
  have hscaleTop : Tendsto
      (increasingTimeRealAuxiliaryScale time width htime) atTop atTop :=
    hwidth.comp hindex
  have hwidthSqComp := hwidthSq.comp hindex
  have hscaleSqNonneg (n : ℕ) :
      0 ≤ (increasingTimeRealAuxiliaryScale time width htime n) ^ 2 /
        (n : ℝ) := div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have hscaleSqUpper :
      (fun n : ℕ =>
        (increasingTimeRealAuxiliaryScale time width htime n) ^ 2 / (n : ℝ)) ≤ᶠ[atTop]
        (fun n => width (increasingTimeIntervalIndex time htime n) ^ 2 /
          (time (increasingTimeIntervalIndex time htime n) : ℝ)) := by
    filter_upwards [eventually_ge_atTop (time 0)] with n hn
    let k := increasingTimeIntervalIndex time htime n
    have hkn := increasingTimeIntervalIndex_lower_bound htime hn
    have hkpos : 0 < (time k : ℝ) := by exact_mod_cast htimePos k
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (htimePos 0) hn)
    have hdenom : (time k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
    have hnum : 0 ≤ width k ^ 2 := sq_nonneg _
    have hcross : width k ^ 2 * (time k : ℝ) ≤
        width k ^ 2 * (n : ℝ) := mul_le_mul_of_nonneg_left hdenom hnum
    have hdiv : width k ^ 2 / (n : ℝ) ≤ width k ^ 2 / (time k : ℝ) :=
      (div_le_div_iff₀ hnpos hkpos).2 (by simpa [mul_comm] using hcross)
    simpa [k, increasingTimeRealAuxiliaryScale] using hdiv
  have hscaleSq : Tendsto
      (fun n : ℕ =>
        (increasingTimeRealAuxiliaryScale time width htime n) ^ 2 / (n : ℝ))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hwidthSqComp
      (Filter.Eventually.of_forall hscaleSqNonneg) hscaleSqUpper
  have hscaleNonneg (n : ℕ) :
      0 ≤ increasingTimeRealAuxiliaryScale time width htime n :=
    (hwidthPos (increasingTimeIntervalIndex time htime n)).le
  have hscaleRatio := Asymptotics.tendsto_div_sqrt_atTop_zero_of_tendsto_sq_div_atTop_zero
    hscaleNonneg hscaleSq
  exact Asymptotics.IsSmallDeviationScale.of_tendsto hscaleTop hscaleRatio

theorem tendsto_realWidthRate_of_sampledTime
    {L : ℝ → ℕ} (hL : Tendsto L atTop atTop)
    (hquadratic : Tendsto (fun D : ℝ => D ^ 2 / (L D : ℝ)) atTop (𝓝 0))
    {rate : ℝ → ℕ → ℝ} {limit : ℝ}
    (hsampled : ∀ {time : ℕ → ℕ} {width : ℕ → ℝ},
      StrictMono time → (∀ k, 0 < time k) → (∀ k, 0 < width k) →
      Tendsto width atTop atTop →
      Tendsto (fun k => width k ^ 2 / (time k : ℝ)) atTop (𝓝 0) →
      Tendsto (fun k => rate (width k) (time k - 1)) atTop (𝓝 limit)) :
    Tendsto (fun D : ℝ => rate D (L D)) atTop (𝓝 limit) := by
  let f : ℝ → ℝ := fun D => rate D (L D)
  apply Metric.tendsto_atTop.2
  intro ε hε
  by_contra hnot
  have hbad (n : ℕ) : ∃ D : ℝ, max 1 (n : ℝ) ≤ D ∧
      ε ≤ dist (f D) limit := by
    by_contra hN
    apply hnot
    refine ⟨max 1 (n : ℝ), ?_⟩
    intro D hD
    by_contra hdist
    exact hN ⟨D, hD, le_of_not_gt hdist⟩
  let widthSeq : ℕ → ℝ := fun n => Classical.choose (hbad n)
  have hwidthPos (n : ℕ) : 0 < widthSeq n :=
    lt_of_lt_of_le (by norm_num) ((le_max_left _ _).trans
      (Classical.choose_spec (hbad n)).1)
  have hwidthTop : Tendsto widthSeq atTop atTop := by
    rw [tendsto_atTop]
    intro bound
    obtain ⟨N, hN⟩ := exists_nat_ge bound
    filter_upwards [eventually_ge_atTop N] with n hn
    exact hN.trans ((by exact_mod_cast hn : (N : ℝ) ≤ (n : ℝ)).trans
      ((le_max_right _ _).trans (Classical.choose_spec (hbad n)).1))
  let rawTime : ℕ → ℕ := fun k => L (widthSeq k) + 1
  have hLwidth : Tendsto (fun k => L (widthSeq k)) atTop atTop :=
    hL.comp hwidthTop
  have hrawTime : Tendsto rawTime atTop atTop := by
    rw [tendsto_atTop]
    intro bound
    filter_upwards [hLwidth.eventually (eventually_ge_atTop bound)] with k hk
    dsimp [rawTime]
    omega
  obtain ⟨φ, hφ, hφtime⟩ := strictMono_subseq_of_tendsto_atTop hrawTime
  let widthSub : ℕ → ℝ := fun k => widthSeq (φ k)
  let timeSub : ℕ → ℕ := fun k => rawTime (φ k)
  have htimeSub : StrictMono timeSub := by
    simpa [timeSub, Function.comp_def] using hφtime
  have hwidthSubTop : Tendsto widthSub atTop atTop :=
    hwidthTop.comp hφ.tendsto_atTop
  have hwidthSqRaw : Tendsto
      (fun k => widthSeq k ^ 2 / ((L (widthSeq k) : ℝ) + 1))
      atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun k =>
        div_nonneg (sq_nonneg _) (by positivity)
    · filter_upwards [hLwidth.eventually (eventually_ge_atTop 1)] with k hk
      have hLpos : (0 : ℝ) < L (widthSeq k) := by exact_mod_cast hk
      have hLle : (L (widthSeq k) : ℝ) ≤ (L (widthSeq k) : ℝ) + 1 := by
        linarith
      exact div_le_div_of_nonneg_left (sq_nonneg _) hLpos hLle
    · exact hquadratic.comp hwidthTop
  have hwidthSqSub : Tendsto
      (fun k => widthSub k ^ 2 / (timeSub k : ℝ)) atTop (𝓝 0) := by
    simpa [widthSub, timeSub, rawTime, Nat.cast_add, Nat.cast_one,
      Function.comp_def] using hwidthSqRaw.comp hφ.tendsto_atTop
  have hrateSub := hsampled htimeSub
    (fun k => by dsimp [timeSub, rawTime]; omega)
    (fun k => hwidthPos (φ k)) hwidthSubTop hwidthSqSub
  have hrateOnWidths : Tendsto (fun k => f (widthSub k)) atTop (𝓝 limit) := by
    simpa [f, widthSub, timeSub, rawTime, Function.comp_def,
      Nat.add_sub_cancel_right] using hrateSub
  have hclose : ∀ᶠ k : ℕ in atTop, dist (f (widthSub k)) limit < ε :=
    hrateOnWidths.eventually (Metric.ball_mem_nhds limit hε)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hclose
  have hlt := hN N le_rfl
  have hge : ε ≤ dist (f (widthSub N)) limit :=
    (Classical.choose_spec (hbad (φ N))).2
  exact (not_lt_of_ge hge) hlt

/-- Real-width form of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1(i). For every
integer horizon $L_D\to\infty$ with $D^2/L_D\to0$, the closed horizontal-tube
probability has logarithmic rate $-\pi^2\sigma^2/2$ as real $D\to\infty$.
The rate is A. A. Mogul'skii, “Small deviations in the sample function
space,” Theorem 3, Section 4, p. 764 (1974); English translation, “Small
Deviations in a Space of Trajectories,” DOI 10.1137/1119081. -/
theorem tendsto_scaledLog_div_predTime
    {time : ℕ → ℕ} {width : ℕ → ℝ} {logProbability : ℕ → ℝ} {limit : ℝ}
    (htime : StrictMono time) (htimePos : ∀ k, 0 < time k)
    (hrate : Tendsto
      (fun k : ℕ => width k ^ 2 / (time k : ℝ) * logProbability k)
      atTop (𝓝 limit)) :
    Tendsto
      (fun k : ℕ => width k ^ 2 / ((time k - 1 : ℕ) : ℝ) * logProbability k)
      atTop (𝓝 limit) := by
  let horizonRatio : ℕ → ℝ := fun k => (time k : ℝ) / ((time k - 1 : ℕ) : ℝ)
  have hratioBase : Tendsto (fun n : ℕ => (n : ℝ) / ((n - 1 : ℕ) : ℝ))
      atTop (𝓝 (1 : ℝ)) := by
    have hratioReal : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) - 1))
        atTop (𝓝 (1 : ℝ)) := by
      simpa [sub_eq_add_neg] using tendsto_natCast_div_add_atTop (-1 : ℝ)
    have hratioEq : (fun n : ℕ => (n : ℝ) / ((n - 1 : ℕ) : ℝ)) =ᶠ[atTop]
        fun n : ℕ => (n : ℝ) / ((n : ℝ) - 1) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      have hn1 : 1 ≤ n := by omega
      simp [Nat.cast_sub hn1]
    exact hratioReal.congr' hratioEq.symm
  have hratio : Tendsto horizonRatio atTop (𝓝 (1 : ℝ)) := by
    change Tendsto (fun k : ℕ => (time k : ℝ) / ((time k - 1 : ℕ) : ℝ))
      atTop (𝓝 (1 : ℝ))
    exact hratioBase.comp htime.tendsto_atTop
  have hproduct := hratio.mul hrate
  have hEq : (fun k : ℕ => horizonRatio k *
      (width k ^ 2 / (time k : ℝ) * logProbability k)) =ᶠ[atTop]
      (fun k : ℕ => width k ^ 2 /
        ((time k - 1 : ℕ) : ℝ) * logProbability k) := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with k hk
    have hk' : 1 < k := by omega
    have htimeStep : time 1 < time k := htime hk'
    have htimeOne : 0 < time 1 := htimePos 1
    have hpredNat : 0 < time k - 1 := by omega
    have htimeNe : (time k : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast htimePos k)
    have hpredNe : ((time k - 1 : ℕ) : ℝ) ≠ 0 :=
      ne_of_gt (by exact_mod_cast hpredNat)
    dsimp [horizonRatio]
    field_simp [htimeNe, hpredNe]
  simpa only [one_mul] using hproduct.congr' hEq


end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete.HorizontalTube.Lemmas

end
