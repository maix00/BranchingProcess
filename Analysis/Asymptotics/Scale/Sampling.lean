/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.Scale.InverseScale
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Instances.Nat
import Mathlib.Tactic

/-!
# Sampling along increasing time scales

The public declarations in this module are deterministic scale tools:

- For $t_k=\mathrm{time}(k)$, `Asymptotics.sampledTimeIntervalIndex` is the
  least $k(n)$ such that $n<t_{k(n)+1}$;
  `Asymptotics.exists_sampledTimeIntervalIndex`,
  `Asymptotics.sampledTimeIntervalIndex_spec`, and
  `Asymptotics.sampledTimeIntervalIndex_le_of_mem` establish existence, the
  defining inequality, and minimality.
- `Asymptotics.sampledTimeIntervalIndex_lower_bound`, `Asymptotics.sampledTimeIntervalIndex_tendsto`, and `Asymptotics.sampledTimeIntervalIndex_at_time`: when t₀ ≤ n, the selected interval satisfies t[k(n)] ≤ n < t[k(n)+1]; also k(n) → ∞ and k(tⱼ) = j.
- `Asymptotics.sampledIntegerWidthScale` and `Asymptotics.sampledRealWidthScale`: the piecewise constant width w[k(n)].
- `Asymptotics.sampledIntegerWidthScale_isSmallDeviationScale` and `Asymptotics.sampledRealWidthScale_isSmallDeviationScale`: if wₖ → ∞ and wₖ²/tₖ → 0, then w[k(n)] → ∞ and w[k(n)]²/n → 0.
- `Asymptotics.tendsto_realWidthRate_of_sampledTime`: if R(wₖ,tₖ−1) → c along every strictly increasing sampled pair with wₖ → ∞ and wₖ²/tₖ → 0, then R(D,L(D)) → c whenever L(D) → ∞ and D²/L(D) → 0.
- `Asymptotics.tendsto_scaledRate_div_predTime`: if tₖ → ∞ and wₖ²rₖ/tₖ → c, then wₖ²rₖ/(tₖ−1) → c.
-/

open Filter
open scoped Topology

@[expose] public section

namespace Asymptotics

theorem exists_sampledTimeIntervalIndex {time : ℕ → ℕ}
    (htime : StrictMono time) (n : ℕ) : ∃ k, n < time (k + 1) := by
  obtain ⟨k, hk⟩ := (htime.tendsto_atTop.eventually_gt_atTop n).exists
  exact ⟨k, lt_of_lt_of_le hk (Nat.le_of_lt (htime (Nat.lt_succ_self k)))⟩

/-- The index of the half-open time interval `[time k, time (k + 1))`
containing `n`. -/
noncomputable def sampledTimeIntervalIndex (time : ℕ → ℕ)
    (htime : StrictMono time) (n : ℕ) : ℕ :=
  Nat.find (exists_sampledTimeIntervalIndex htime n)

theorem sampledTimeIntervalIndex_spec {time : ℕ → ℕ}
    (htime : StrictMono time) (n : ℕ) :
    n < time (sampledTimeIntervalIndex time htime n + 1) :=
  by
  change n < time (Nat.find (exists_sampledTimeIntervalIndex htime n) + 1)
  exact Nat.find_spec (exists_sampledTimeIntervalIndex htime n)

theorem sampledTimeIntervalIndex_le_of_mem {time : ℕ → ℕ}
    (htime : StrictMono time) (n k : ℕ) (hnk : n < time (k + 1)) :
    sampledTimeIntervalIndex time htime n ≤ k := by
  change Nat.find (exists_sampledTimeIntervalIndex htime n) ≤ k
  exact Nat.find_min' (exists_sampledTimeIntervalIndex htime n) hnk

theorem sampledTimeIntervalIndex_lower_bound {time : ℕ → ℕ}
    (htime : StrictMono time) {n : ℕ} (hstart : time 0 ≤ n) :
    time (sampledTimeIntervalIndex time htime n) ≤ n := by
  by_contra hnot
  have hlt : n < time (sampledTimeIntervalIndex time htime n) := Nat.lt_of_not_ge hnot
  by_cases hzero : sampledTimeIntervalIndex time htime n = 0
  · rw [hzero] at hlt
    exact (not_lt_of_ge hstart) hlt
  · have hindexPos : 0 < sampledTimeIntervalIndex time htime n :=
      Nat.pos_of_ne_zero hzero
    let k := sampledTimeIntervalIndex time htime n - 1
    have hk : k + 1 = sampledTimeIntervalIndex time htime n := by
      dsimp [k]
      omega
    have hmin := sampledTimeIntervalIndex_le_of_mem htime n k (by simpa [hk] using hlt)
    omega

theorem sampledTimeIntervalIndex_tendsto {time : ℕ → ℕ}
    (htime : StrictMono time) :
    Tendsto (sampledTimeIntervalIndex time htime) atTop atTop := by
  rw [tendsto_atTop]
  intro k
  filter_upwards [eventually_ge_atTop (time k)] with n hn
  by_contra hnot
  have hindex : sampledTimeIntervalIndex time htime n < k := Nat.lt_of_not_ge hnot
  have hindexTime : time (sampledTimeIntervalIndex time htime n + 1) ≤ time k :=
    htime.monotone (by omega)
  have hspec := sampledTimeIntervalIndex_spec htime n
  omega

theorem sampledTimeIntervalIndex_at_time {time : ℕ → ℕ}
    (htime : StrictMono time) (k : ℕ) :
    sampledTimeIntervalIndex time htime (time k) = k := by
  apply le_antisymm
  · exact sampledTimeIntervalIndex_le_of_mem htime (time k) k
      (htime (Nat.lt_succ_self k))
  · by_contra hnot
    have hindex : sampledTimeIntervalIndex time htime (time k) < k :=
      Nat.lt_of_not_ge hnot
    have hindexTime : time (sampledTimeIntervalIndex time htime (time k) + 1) ≤ time k :=
      htime.monotone (by omega)
    have hspec := sampledTimeIntervalIndex_spec htime (time k)
    omega

noncomputable def sampledIntegerWidthScale (time width : ℕ → ℕ)
    (htime : StrictMono time) : ℕ → ℝ := fun n =>
  (width (sampledTimeIntervalIndex time htime n) : ℝ)

theorem sampledIntegerWidthScale_isSmallDeviationScale
    {time width : ℕ → ℕ} (htime : StrictMono time)
    (htimePos : ∀ k, 0 < time k)
    (hwidth : Tendsto (fun k : ℕ => (width k : ℝ)) atTop atTop)
    (hwidthSq : Tendsto (fun k : ℕ => (width k : ℝ) ^ 2 / (time k : ℝ))
      atTop (𝓝 0)) :
    Asymptotics.IsSmallDeviationScale
      (sampledIntegerWidthScale time width htime)
      (fun n => Real.sqrt (n : ℝ)) := by
  have hindex := sampledTimeIntervalIndex_tendsto htime
  have hscaleTop : Tendsto (sampledIntegerWidthScale time width htime) atTop atTop :=
    hwidth.comp hindex
  have hwidthSqComp := hwidthSq.comp hindex
  have hscaleSqNonneg (n : ℕ) :
      0 ≤ (sampledIntegerWidthScale time width htime n) ^ 2 / (n : ℝ) :=
    div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have hscaleSqUpper :
      (fun n : ℕ => (sampledIntegerWidthScale time width htime n) ^ 2 / (n : ℝ)) ≤ᶠ[atTop]
        (fun n => (width (sampledTimeIntervalIndex time htime n) : ℝ) ^ 2 /
          (time (sampledTimeIntervalIndex time htime n) : ℝ)) := by
    filter_upwards [eventually_ge_atTop (time 0)] with n hn
    let k := sampledTimeIntervalIndex time htime n
    have hkn := sampledTimeIntervalIndex_lower_bound htime hn
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
    simpa [k, sampledIntegerWidthScale] using hdiv
  have hscaleSq : Tendsto
      (fun n : ℕ => (sampledIntegerWidthScale time width htime n) ^ 2 / (n : ℝ))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hwidthSqComp
      (Filter.Eventually.of_forall hscaleSqNonneg) hscaleSqUpper
  have hscaleRatio := Asymptotics.tendsto_div_sqrt_atTop_zero_of_tendsto_sq_div_atTop_zero
    (fun n => Nat.cast_nonneg (width (sampledTimeIntervalIndex time htime n))) hscaleSq
  exact Asymptotics.IsSmallDeviationScale.of_tendsto hscaleTop hscaleRatio

noncomputable def sampledRealWidthScale
    (time : ℕ → ℕ) (width : ℕ → ℝ) (htime : StrictMono time) : ℕ → ℝ :=
  fun n => width (sampledTimeIntervalIndex time htime n)

theorem sampledRealWidthScale_isSmallDeviationScale
    {time : ℕ → ℕ} {width : ℕ → ℝ} (htime : StrictMono time)
    (htimePos : ∀ k, 0 < time k) (hwidthPos : ∀ k, 0 < width k)
    (hwidth : Tendsto width atTop atTop)
    (hwidthSq : Tendsto (fun k => width k ^ 2 / (time k : ℝ))
      atTop (𝓝 0)) :
    Asymptotics.IsSmallDeviationScale
      (sampledRealWidthScale time width htime)
      (fun n => Real.sqrt (n : ℝ)) := by
  have hindex := sampledTimeIntervalIndex_tendsto htime
  have hscaleTop : Tendsto
      (sampledRealWidthScale time width htime) atTop atTop :=
    hwidth.comp hindex
  have hwidthSqComp := hwidthSq.comp hindex
  have hscaleSqNonneg (n : ℕ) :
      0 ≤ (sampledRealWidthScale time width htime n) ^ 2 /
        (n : ℝ) := div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)
  have hscaleSqUpper :
      (fun n : ℕ =>
        (sampledRealWidthScale time width htime n) ^ 2 / (n : ℝ)) ≤ᶠ[atTop]
        (fun n => width (sampledTimeIntervalIndex time htime n) ^ 2 /
          (time (sampledTimeIntervalIndex time htime n) : ℝ)) := by
    filter_upwards [eventually_ge_atTop (time 0)] with n hn
    let k := sampledTimeIntervalIndex time htime n
    have hkn := sampledTimeIntervalIndex_lower_bound htime hn
    have hkpos : 0 < (time k : ℝ) := by exact_mod_cast htimePos k
    have hnpos : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (htimePos 0) hn)
    have hdenom : (time k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
    have hnum : 0 ≤ width k ^ 2 := sq_nonneg _
    have hcross : width k ^ 2 * (time k : ℝ) ≤
        width k ^ 2 * (n : ℝ) := mul_le_mul_of_nonneg_left hdenom hnum
    have hdiv : width k ^ 2 / (n : ℝ) ≤ width k ^ 2 / (time k : ℝ) :=
      (div_le_div_iff₀ hnpos hkpos).2 (by simpa [mul_comm] using hcross)
    simpa [k, sampledRealWidthScale] using hdiv
  have hscaleSq : Tendsto
      (fun n : ℕ =>
        (sampledRealWidthScale time width htime n) ^ 2 / (n : ℝ))
      atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hwidthSqComp
      (Filter.Eventually.of_forall hscaleSqNonneg) hscaleSqUpper
  have hscaleNonneg (n : ℕ) :
      0 ≤ sampledRealWidthScale time width htime n :=
    (hwidthPos (sampledTimeIntervalIndex time htime n)).le
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

/-- If $w_k^2 r_k/t_k → c$ and $t_k → ∞$, then replacing $t_k$ by
$t_k-1$ in the denominator preserves the limit. -/
theorem tendsto_scaledRate_div_predTime
    {time : ℕ → ℕ} {width value : ℕ → ℝ} {limit : ℝ}
    (htime : Tendsto time atTop atTop)
    (hrate : Tendsto
      (fun k : ℕ => width k ^ 2 / (time k : ℝ) * value k)
      atTop (𝓝 limit)) :
    Tendsto
      (fun k : ℕ => width k ^ 2 / ((time k - 1 : ℕ) : ℝ) * value k)
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
    exact hratioBase.comp htime
  have hproduct := hratio.mul hrate
  have hEq : (fun k : ℕ => horizonRatio k *
      (width k ^ 2 / (time k : ℝ) * value k)) =ᶠ[atTop]
      (fun k : ℕ => width k ^ 2 /
        ((time k - 1 : ℕ) : ℝ) * value k) := by
    filter_upwards [htime.eventually (eventually_gt_atTop (1 : ℕ))] with k hk
    have htimeNe : (time k : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (by omega : 0 < time k))
    have hpredNe : ((time k - 1 : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (by omega : 0 < time k - 1))
    dsimp [horizonRatio]
    field_simp [htimeNe, hpredNe]
  simpa only [one_mul] using hproduct.congr' hEq

end Asymptotics

end
