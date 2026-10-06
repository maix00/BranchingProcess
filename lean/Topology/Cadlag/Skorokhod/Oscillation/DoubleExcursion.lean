/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.Oscillation.Partition.Measurability
public import Topology.Cadlag.Skorokhod.Oscillation.Partition.Existence
public import Topology.Cadlag.Jump
public import Order.Interval.UniformGrid

/-!
# Billingsley's double-excursion modulus

This module records the deterministic double-excursion condition used in the
Skorokhod compactness criterion. The condition is stated without taking
suprema: on two adjacent time intervals, every pair of excursions has one
side bounded by the prescribed tolerance. This is the metric-space form of
Billingsley's `w''` condition.

The endpoint controls are stated separately. Double-excursion control alone
does not control a single large jump moving to either endpoint.
With both endpoint controls, this module also proves a pathwise converse by
constructing a finite oscillation partition from a filtered uniform grid.
-/

@[expose] public section

open Set
open Filter
open scoped Topology

namespace Skorokhod

private theorem OscillationPartition.consecutiveValueDistance_le
    {E : Type*} [PseudoMetricSpace E]
    (partition : OscillationPartition) (path : CadlagPath unitInterval E)
    {bound jumpBound : ℝ}
    (hosc : OscillationBoundedOnPartition partition path bound)
    (i : Fin partition.size)
    (hjump : dist
      (Function.leftLim (fun t : unitInterval => path t)
        (partition.points i.succ)) (path (partition.points i.succ)) ≤ jumpBound) :
    dist (path (partition.points i.castSucc)) (path (partition.points i.succ)) ≤
      bound + jumpBound := by
  let leftPoint := partition.points i.castSucc
  let rightPoint := partition.points i.succ
  have htime : leftPoint < rightPoint := by
    dsimp [leftPoint, rightPoint]
    exact partition.strictMono_points i.castSucc_lt_succ
  have hleftTop : leftPoint ≠ ⊤ := ne_of_lt (lt_of_lt_of_le htime le_top)
  have hleftLimitBall : Function.leftLim (fun t : unitInterval => path t) rightPoint ∈
      Metric.closedBall (path leftPoint) bound := by
    have hfilter : (𝓝[<] rightPoint).NeBot :=
      nhdsLT_neBot_of_exists_lt ⟨leftPoint, htime⟩
    have hev : ∀ᶠ t in 𝓝[<] rightPoint,
        path t ∈ Metric.closedBall (path leftPoint) bound := by
      filter_upwards [Ico_mem_nhdsLT htime] with t ht
      have hindex : partition.index t = i :=
        partition.index_eq_of_cell i t ht.1 (Or.inl ht.2)
      have hstart : partition.index leftPoint = i := by
        dsimp [leftPoint]
        exact partition.index_start i
      have hbound := hosc leftPoint t hleftTop (ne_of_lt (lt_of_lt_of_le ht.2 le_top))
        (hstart.trans hindex.symm)
      exact Metric.mem_closedBall.mpr (by simpa [dist_comm] using hbound)
    have hlim : Filter.Tendsto (fun t : unitInterval => path t)
        (𝓝[<] rightPoint)
        (𝓝 (Function.leftLim (fun t : unitInterval => path t) rightPoint)) :=
      tendsto_leftLim_of_tendsto (path.isCadlag_toFun.tendsto_nhdsLT rightPoint)
    exact Metric.isClosed_closedBall.mem_of_tendsto hlim hev
  have hleft : dist (path leftPoint)
      (Function.leftLim (fun t : unitInterval => path t) rightPoint) ≤ bound := by
    simpa [Metric.mem_closedBall, dist_comm] using hleftLimitBall
  calc
    dist (path leftPoint) (path rightPoint) ≤
      dist (path leftPoint) (Function.leftLim (fun t : unitInterval => path t) rightPoint) +
        dist (Function.leftLim (fun t : unitInterval => path t) rightPoint) (path rightPoint) :=
      dist_triangle _ _ _
    _ ≤ bound + jumpBound := add_le_add hleft hjump

/-- Every pair of excursions on the two sides of any split in an interval
shorter than `delta` has one side of size at most `epsilon`. The two
excursions are measured by arbitrary pairs of points in their respective
closed subintervals. -/
def HasDoubleExcursionBound {E : Type*} [PseudoMetricSpace E]
    (path : CadlagPath unitInterval E) (delta epsilon : ℝ) : Prop :=
  ∀ s t u : unitInterval, s < t → t < u → u ≠ ⊤ → dist s u < delta →
    ∀ x y z w : unitInterval,
      s ≤ x → x ≤ y → y ≤ t →
      t ≤ z → z ≤ w → w ≤ u →
      min (dist (path x) (path y)) (dist (path z) (path w)) ≤ epsilon

/-- Uniform control of the path oscillation near both endpoints. The terminal
value is excluded from the right endpoint control because the partition
criterion treats it as a separate coordinate. -/
def HasEndpointOscillationBound {E : Type*} [PseudoMetricSpace E]
    (path : CadlagPath unitInterval E) (delta epsilon : ℝ) : Prop :=
  (∀ s t : unitInterval, (s : ℝ) < delta → (t : ℝ) < delta →
      dist (path s) (path t) ≤ epsilon) ∧
  (∀ s t : unitInterval, s ≠ ⊤ → t ≠ ⊤ →
      1 - delta < (s : ℝ) → 1 - delta < (t : ℝ) →
      dist (path s) (path t) ≤ epsilon)

private theorem jump_le_of_left_eventually_bound
    {E : Type*} [PseudoMetricSpace E] (path : CadlagPath unitInterval E)
    {t : unitInterval} {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hevent : ∀ᶠ s in 𝓝[<] t, dist (path s) (path t) ≤ epsilon) :
    dist (Function.leftLim (fun s : unitInterval => path s) t) (path t) ≤ epsilon := by
  rcases eq_or_neBot (𝓝[<] t) with hbot | hnebot
  · rw [leftLim_eq_of_eq_bot (fun s : unitInterval => path s) hbot]
    simpa using (le_of_lt hepsilon)
  · have hlim : Filter.Tendsto (fun s : unitInterval => path s)
        (𝓝[<] t) (𝓝 (Function.leftLim (fun s : unitInterval => path s) t)) :=
      tendsto_leftLim_of_tendsto (path.isCadlag_toFun.tendsto_nhdsLT t)
    have hclosed : ∀ᶠ s in 𝓝[<] t,
        path s ∈ Metric.closedBall (path t) epsilon := by
      filter_upwards [hevent] with s hs
      exact Metric.mem_closedBall.mpr hs
    have hmem : Function.leftLim (fun s : unitInterval => path s) t ∈
        Metric.closedBall (path t) epsilon :=
      Metric.isClosed_closedBall.mem_of_tendsto hlim hclosed
    simpa [Metric.mem_closedBall, dist_comm] using hmem

private theorem exists_left_sample_dist_gt
    {E : Type*} [PseudoMetricSpace E] (path : CadlagPath unitInterval E)
    {t a : unitInterval} {epsilon eta : ℝ}
    (hjump : epsilon <
      dist (Function.leftLim (fun s : unitInterval => path s) t) (path t))
    (hat : a < t) (heta : 0 < eta) :
    ∃ s, a ≤ s ∧ s < t ∧ dist s t < eta ∧ epsilon < dist (path s) (path t) := by
  let margin := dist (Function.leftLim (fun s : unitInterval => path s) t) (path t) - epsilon
  have hmargin : 0 < margin := sub_pos.mpr hjump
  have hlim : Filter.Tendsto (fun s : unitInterval => path s)
      (𝓝[<] t) (𝓝 (Function.leftLim (fun s : unitInterval => path s) t)) :=
    tendsto_leftLim_of_tendsto (path.isCadlag_toFun.tendsto_nhdsLT t)
  have hvalue : ∀ᶠ s in 𝓝[<] t,
      dist (path s) (Function.leftLim (fun s : unitInterval => path s) t) < margin := by
    filter_upwards [hlim (Metric.ball_mem_nhds _ hmargin)] with s hs
    simpa [Metric.mem_ball, dist_comm] using hs
  have htime : ∀ᶠ s in 𝓝[<] t, dist s t < eta := by
    filter_upwards [Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (Metric.ball_mem_nhds t heta)] with s hs
    exact Metric.mem_ball.mp hs
  have hinterval : Set.Ico a t ∈ 𝓝[<] t := Ico_mem_nhdsLT hat
  have hfilter : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨a, hat⟩
  obtain ⟨s, ⟨hsvalue, hstime⟩, hsinterval⟩ :=
    (hvalue.and htime).and hinterval |>.exists
  have htri := dist_triangle
    (Function.leftLim (fun s : unitInterval => path s) t) (path s) (path t)
  refine ⟨s, hsinterval.1, hsinterval.2, hstime, ?_⟩
  have hsvalue' : dist
      (Function.leftLim (fun s : unitInterval => path s) t) (path s) < margin := by
    simpa [dist_comm] using hsvalue
  dsimp [margin] at hsvalue'
  linarith

private theorem HasEndpointOscillationBound.leftJump_le
    {E : Type*} [PseudoMetricSpace E]
    {path : CadlagPath unitInterval E} {delta epsilon : ℝ}
    (hend : HasEndpointOscillationBound path delta epsilon)
    (hepsilon : 0 < epsilon) {t : unitInterval}
    (htdelta : (t : ℝ) < delta) :
    dist (Function.leftLim (fun s : unitInterval => path s) t) (path t) ≤ epsilon := by
  have htime : ∀ᶠ s : unitInterval in 𝓝[<] (t : unitInterval), (s : ℝ) < delta := by
    have hopen : {s : unitInterval | (s : ℝ) < delta} ∈ 𝓝 t :=
      (isOpen_Iio.preimage continuous_subtype_val).mem_nhds htdelta
    filter_upwards [Filter.Eventually.filter_mono
      (nhdsWithin_le_nhds : 𝓝[<] (t : unitInterval) ≤ 𝓝 t) hopen] with s hs
    exact hs
  have hevent : ∀ᶠ s in 𝓝[<] t, dist (path s) (path t) ≤ epsilon := by
    filter_upwards [htime, self_mem_nhdsWithin] with s hs hst
    exact hend.1 s t hs htdelta
  exact jump_le_of_left_eventually_bound path hepsilon hevent

private theorem HasEndpointOscillationBound.rightJump_le
    {E : Type*} [PseudoMetricSpace E]
    {path : CadlagPath unitInterval E} {delta epsilon : ℝ}
    (hend : HasEndpointOscillationBound path delta epsilon)
    (hepsilon : 0 < epsilon) {t : unitInterval}
    (httop : t ≠ ⊤) (htdelta : 1 - delta < (t : ℝ)) :
    dist (Function.leftLim (fun s : unitInterval => path s) t) (path t) ≤ epsilon := by
  have ht : t < ⊤ := lt_top_iff_ne_top.mpr httop
  have htime : ∀ᶠ s : unitInterval in 𝓝[<] (t : unitInterval), 1 - delta < (s : ℝ) := by
    have hopen : {s : unitInterval | 1 - delta < (s : ℝ)} ∈ 𝓝 t :=
      (isOpen_Ioi.preimage continuous_subtype_val).mem_nhds htdelta
    filter_upwards [Filter.Eventually.filter_mono
      (nhdsWithin_le_nhds : 𝓝[<] (t : unitInterval) ≤ 𝓝 t) hopen] with s hs
    exact hs
  have hevent : ∀ᶠ s in 𝓝[<] t, dist (path s) (path t) ≤ epsilon := by
    filter_upwards [htime, self_mem_nhdsWithin] with s hs hst
    have hstop : s ≠ ⊤ := ne_of_lt (hst.trans ht)
    exact hend.2 s t hstop httop hs htdelta
  exact jump_le_of_left_eventually_bound path hepsilon hevent

private theorem HasEndpointOscillationBound.largeJump_awayFromEndpoints
    {E : Type*} [PseudoMetricSpace E]
    {path : CadlagPath unitInterval E} {delta epsilon : ℝ}
    (hend : HasEndpointOscillationBound path delta epsilon)
    (hepsilon : 0 < epsilon) {t : unitInterval}
    (httop : t ≠ ⊤)
    (hjump : 2 * epsilon <
      dist (Function.leftLim (fun s : unitInterval => path s) t) (path t)) :
    delta ≤ (t : ℝ) ∧ (t : ℝ) ≤ 1 - delta := by
  constructor
  · by_contra hnot
    have htdelta : (t : ℝ) < delta := lt_of_not_ge hnot
    have hsmall := hend.leftJump_le hepsilon htdelta
    linarith
  · by_contra hnot
    have htdelta : 1 - delta < (t : ℝ) := lt_of_not_ge hnot
    have hsmall := hend.rightJump_le hepsilon httop htdelta
    linarith

private theorem exists_right_time_close
    {t : unitInterval} {eta : ℝ} (htop : t < ⊤) (heta : 0 < eta) :
    ∃ u : unitInterval, t < u ∧ u < ⊤ ∧ dist t u < eta := by
  obtain ⟨v, htv, hvtop⟩ := exists_between htop
  let : (𝓝[>] t).NeBot := nhdsGT_neBot_of_exists_gt ⟨v, htv⟩
  have htime : ∀ᶠ u : unitInterval in 𝓝[>] t, dist u t < eta := by
    filter_upwards [Filter.Eventually.filter_mono
      (nhdsWithin_le_nhds : 𝓝[>] (t : unitInterval) ≤ 𝓝 t)
      (Metric.ball_mem_nhds t heta)] with u hu
    exact Metric.mem_ball.mp hu
  have hbelow : ∀ᶠ u : unitInterval in 𝓝[>] t, u < ⊤ := by
    filter_upwards [Filter.Eventually.filter_mono
      (nhdsWithin_le_nhds : 𝓝[>] (t : unitInterval) ≤ 𝓝 t)
      (isOpen_Iio.mem_nhds htop)] with u hu
    exact hu
  obtain ⟨u, ⟨htime, hbelow⟩, hright⟩ :=
    (htime.and hbelow).and self_mem_nhdsWithin |>.exists
  exact ⟨u, hright, hbelow, by simpa [dist_comm] using htime⟩

private theorem largeJumps_separated_of_lt
    {E : Type*} [PseudoMetricSpace E]
    {path : CadlagPath unitInterval E} {delta epsilon : ℝ}
    (hdouble : HasDoubleExcursionBound path delta epsilon)
    (hepsilon : 0 < epsilon)
    {t₁ t₂ : unitInterval} (ht₁bot : t₁ ≠ ⊥) (ht₂top : t₂ ≠ ⊤)
    (ht₁₂ : t₁ < t₂)
    (hjump₁ : 2 * epsilon <
      dist (Function.leftLim (fun s : unitInterval => path s) t₁) (path t₁))
    (hjump₂ : 2 * epsilon <
      dist (Function.leftLim (fun s : unitInterval => path s) t₂) (path t₂)) :
    delta ≤ dist t₁ t₂ := by
  by_contra hnot
  have hdist : dist t₁ t₂ < delta := lt_of_not_ge hnot
  let eta := (delta - dist t₁ t₂) / 3
  have heta : 0 < eta := by dsimp [eta]; linarith
  obtain ⟨m, hm₁, hm₂⟩ := exists_between ht₁₂
  obtain ⟨s, -, hst₁, hsclose, hsjump⟩ :=
    exists_left_sample_dist_gt (path := path) (t := t₁) (a := ⊥)
      (epsilon := epsilon) (eta := eta) (by linarith [hepsilon, hjump₁])
      (bot_lt_iff_ne_bot.mpr ht₁bot) heta
  obtain ⟨z, hmz, hzt₂, hzclose, hzjump⟩ :=
    exists_left_sample_dist_gt (path := path) (t := t₂) (a := m)
      (epsilon := epsilon) (eta := eta) (by linarith [hepsilon, hjump₂]) hm₂ heta
  obtain ⟨u, ht₂u, huTop, huclose⟩ :=
    exists_right_time_close (t := t₂) (lt_top_iff_ne_top.mpr ht₂top) heta
  have hsu : dist s u < delta := by
    have htri₁ := dist_triangle s t₁ u
    have htri₂ := dist_triangle t₁ t₂ u
    have heta_eq : 3 * eta = delta - dist t₁ t₂ := by
      dsimp [eta]
      ring
    linarith
  have hmu : m < u := lt_of_le_of_lt hmz (lt_trans hzt₂ ht₂u)
  have hresult := hdouble s m u (lt_trans hst₁ hm₁) hmu (ne_of_lt huTop) hsu
    s t₁ z t₂ le_rfl hst₁.le hm₁.le hmz hzt₂.le ht₂u.le
  rw [min_le_iff] at hresult
  rcases hresult with hleft | hright
  · exact (not_lt_of_ge hleft) hsjump
  · exact (not_lt_of_ge hright) hzjump

private theorem largeJumps_separated
    {E : Type*} [PseudoMetricSpace E]
    {path : CadlagPath unitInterval E} {delta epsilon : ℝ}
    (hdouble : HasDoubleExcursionBound path delta epsilon)
    (hepsilon : 0 < epsilon)
    {t₁ t₂ : unitInterval} (ht₁bot : t₁ ≠ ⊥) (ht₁top : t₁ ≠ ⊤)
    (ht₂bot : t₂ ≠ ⊥) (ht₂top : t₂ ≠ ⊤) (hne : t₁ ≠ t₂)
    (hjump₁ : 2 * epsilon <
      dist (Function.leftLim (fun s : unitInterval => path s) t₁) (path t₁))
    (hjump₂ : 2 * epsilon <
      dist (Function.leftLim (fun s : unitInterval => path s) t₂) (path t₂)) :
    delta ≤ dist t₁ t₂ := by
  rcases lt_or_gt_of_ne hne with h12 | h21
  · exact largeJumps_separated_of_lt hdouble hepsilon ht₁bot ht₂top h12 hjump₁ hjump₂
  · have hsep := largeJumps_separated_of_lt hdouble hepsilon ht₂bot ht₁top h21 hjump₂ hjump₁
    simpa [dist_comm] using hsep

private theorem HasDoubleExcursionBound.oscillation_le_of_jumpBound
    {E : Type*} [PseudoMetricSpace E]
    {path : CadlagPath unitInterval E} {delta epsilon : ℝ}
    (hdouble : HasDoubleExcursionBound path delta epsilon)
    (hepsilon : 0 < epsilon)
    {a b : unitInterval} (hb : b ≠ ⊤)
    (hspan : dist a b < delta)
    (hjump : ∀ t, a < t → t < b →
      dist (Function.leftLim (fun s : unitInterval => path s) t) (path t) ≤ 2 * epsilon) :
    ∀ x y, a ≤ x → x ≤ y → y < b → dist (path x) (path y) ≤ 5 * epsilon := by
  intro x y hax hxy hyb
  by_contra hnot
  have hfar : 5 * epsilon < dist (path x) (path y) := lt_of_not_ge hnot
  obtain ⟨partition, bound, hbound, hosc⟩ :=
    IsCadlag.exists_oscillation_partition path.isCadlag_toFun hepsilon
  have hbound_nonneg : 0 ≤ bound := by
    have hbotTop : (⊥ : unitInterval) ≠ ⊤ := ne_of_lt bot_lt_top
    have h := hosc ⊥ ⊥ hbotTop hbotTop rfl
    simpa using h
  let i := partition.index x
  let j := partition.index y
  have hyTop : y < ⊤ := lt_of_lt_of_le hyb le_top
  have hxTop : x < ⊤ := lt_of_le_of_lt hxy hyTop
  have hindexMono : i ≤ j := by
    dsimp [i, j]
    exact partition.index_monotone hxy
  by_cases hij : i = j
  · have hxTop' : x ≠ ⊤ := ne_of_lt hxTop
    have hyTop' : y ≠ ⊤ := ne_of_lt hyTop
    have hoscxy := hosc x y hxTop' hyTop' (by simpa [i, j] using hij)
    linarith
  · have hij' : i < j := lt_of_le_of_ne hindexMono hij
    let q (k : Fin partition.size) := partition.points k.castSucc
    have hqj_le : q j ≤ y := by
      exact partition.index_lower y
    have hqjTop : q j ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hqj_le hyTop)
    have hqjIndex : partition.index (q j) = j := by
      dsimp [q]
      exact partition.index_start j
    have hqjOsc : dist (path (q j)) (path y) ≤ bound := by
      apply hosc (q j) y hqjTop (ne_of_lt hyTop)
      rw [hqjIndex]
    let candidates : Finset (Fin partition.size) :=
      Finset.univ.filter fun k => i < k ∧ k ≤ j ∧ epsilon < dist (path x) (path (q k))
    have hfinalCandidate : epsilon < dist (path x) (path (q j)) := by
      have htriangle := dist_triangle (path x) (path (q j)) (path y)
      linarith
    have hnonempty : candidates.Nonempty := by
      refine ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hij', le_rfl, hfinalCandidate⟩⟩⟩
    let k := candidates.min' hnonempty
    have hk : k ∈ candidates := Finset.min'_mem _ _
    rcases Finset.mem_filter.mp hk with ⟨_, ⟨hik, hkj, hcross⟩⟩
    let prev : Fin partition.size := ⟨k.val - 1, by omega⟩
    have hprev_lt : prev < k := by
      apply Fin.lt_def.mpr
      simp only [prev]
      omega
    have hi_prev : i ≤ prev := by
      apply Fin.le_iff_val_le_val.mpr
      have hikVal := Fin.lt_def.mp hik
      simp only [prev]
      omega
    have hprev_j : prev ≤ j := le_trans (le_of_lt hprev_lt) hkj
    have hprevDistance : dist (path x) (path (q prev)) ≤ epsilon := by
      by_cases hiprev : i = prev
      · have hqprev_le : q prev ≤ x := by
          change partition.points prev.castSucc ≤ x
          rw [← hiprev]
          exact partition.index_lower x
        have hqprevTop : q prev ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hqprev_le hxTop)
        have hqxIndex : partition.index (q prev) = partition.index x := by
          dsimp [q]
          rw [← hiprev]
          rw [partition.index_start]
        have hosc' := hosc x (q prev) (ne_of_lt hxTop)
          hqprevTop hqxIndex.symm
        have hle := hosc'.trans (le_of_lt hbound)
        simpa [dist_comm] using hle
      · have hiltprev : i < prev := lt_of_le_of_ne hi_prev hiprev
        by_contra hnot
        have hlarge : epsilon < dist (path x) (path (q prev)) := by
          exact lt_of_not_ge hnot
        have hprevCandidate : prev ∈ candidates :=
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hiltprev, hprev_j, hlarge⟩⟩
        have hmin : k ≤ prev := Finset.min'_le candidates prev hprevCandidate
        exact (not_le_of_gt hprev_lt) hmin
    have hqk_eq : q k = partition.points prev.succ := by
      apply congrArg partition.points
      apply Fin.ext
      simp [prev]
      omega
    have hxi_upper : x < partition.points i.succ := by
      rcases partition.index_upper x with h | hlast
      · simpa [i] using h
      · have hlastContr : i.succ = Fin.last partition.size := by
          apply Fin.ext
          simp only [Fin.val_succ, Fin.val_last]
          omega
        have hiLtJ : i.succ ≤ j.castSucc := by
          apply Fin.le_iff_val_le_val.mpr
          have hijVal := Fin.lt_def.mp hij'
          simp only [Fin.val_succ, Fin.val_castSucc]
          omega
        have htopPoint : partition.points i.succ ≤ q j := by
          dsimp [q]
          exact partition.strictMono_points.monotone hiLtJ
        have htop : partition.points i.succ = ⊤ := by
          rw [hlastContr]
          simpa [Fin.last] using partition.last
        have hfalse : (⊤ : unitInterval) ≤ y := by
          rw [← htop]
          exact htopPoint.trans hqj_le
        exact (not_le_of_gt hyTop hfalse).elim
    have hqSucc_le : partition.points i.succ ≤ q k := by
      rw [hqk_eq]
      exact partition.strictMono_points.monotone (Fin.succ_le_succ_iff.mpr hi_prev)
    have hqk_le_y : q k ≤ y := by
      calc
        q k = partition.points prev.succ := hqk_eq
        _ ≤ q j := by
          dsimp [q]
          apply partition.strictMono_points.monotone
          apply Fin.le_iff_val_le_val.mpr
          simp only [Fin.val_succ, Fin.val_castSucc]
          omega
        _ ≤ y := hqj_le
    have hqk_interior : a < q k ∧ q k < b := by
      exact ⟨lt_of_le_of_lt hax (lt_of_lt_of_le hxi_upper hqSucc_le),
        lt_of_le_of_lt hqk_le_y hyb⟩
    have hjumpk : dist
        (Function.leftLim (fun s : unitInterval => path s) (q k)) (path (q k)) ≤
          2 * epsilon := by
      apply hjump (q k) hqk_interior.1 hqk_interior.2
    have hjumpPrev : dist
        (Function.leftLim (fun s : unitInterval => path s) (partition.points prev.succ))
          (path (partition.points prev.succ)) ≤ 2 * epsilon := by
      rw [← hqk_eq]
      exact hjumpk
    have htransition :=
      partition.consecutiveValueDistance_le path hosc prev hjumpPrev
    have htransition' :
        dist (path (q prev)) (path (q k)) ≤ bound + 2 * epsilon := by
      rw [hqk_eq]
      exact htransition
    have hfxqk : dist (path x) (path (q k)) ≤ 3 * epsilon + bound := by
      calc
        dist (path x) (path (q k)) ≤
            dist (path x) (path (q prev)) + dist (path (q prev)) (path (q k)) :=
          dist_triangle _ _ _
        _ ≤ epsilon + (bound + 2 * epsilon) := add_le_add hprevDistance htransition'
        _ = 3 * epsilon + bound := by ring
    have hrightExcursion : epsilon < dist (path (q k)) (path y) := by
      have htriangle := dist_triangle (path x) (path (q k)) (path y)
      linarith
    have hxqk : x ≤ q k := le_of_lt (lt_of_lt_of_le hxi_upper hqSucc_le)
    have hdoubleResult := hdouble a (q k) b hqk_interior.1 hqk_interior.2 hb hspan
      x (q k) (q k) y hax hxqk le_rfl le_rfl hqk_le_y (le_of_lt hyb)
    have hminContr : min (dist (path x) (path (q k)))
        (dist (path (q k)) (path y)) ≤ epsilon := hdoubleResult
    rw [min_le_iff] at hminContr
    rcases hminContr with hleft | hright
    · exact (not_lt_of_ge hleft) hcross
    · exact (not_lt_of_ge hright) hrightExcursion

private theorem unitInterval_dist_le_of_subintervals
    {a b c d : unitInterval} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    dist b c ≤ dist a d := by
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  have hbc' : (b : ℝ) ≤ c := by exact_mod_cast hbc
  have hcd' : (c : ℝ) ≤ d := by exact_mod_cast hcd
  rw [Subtype.dist_eq, Subtype.dist_eq, Real.dist_eq, Real.dist_eq]
  rw [abs_of_nonpos (sub_nonpos.mpr hbc'), abs_of_nonpos (sub_nonpos.mpr
    (hab'.trans (hbc'.trans hcd')))]
  linarith

private theorem unitInterval_dist_eq_coe_sub {a b : unitInterval} (hab : a ≤ b) :
    dist a b = (b : ℝ) - (a : ℝ) := by
  have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
  rw [Subtype.dist_eq, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hab')]
  ring

private theorem unitInterval_dist_bot_eq (t : unitInterval) :
    dist (⊥ : unitInterval) t = (t : ℝ) := by
  rw [unitInterval_dist_eq_coe_sub bot_le]
  simp

private theorem unitInterval_dist_top_eq (t : unitInterval) :
    dist (⊤ : unitInterval) t = 1 - (t : ℝ) := by
  rw [dist_comm, unitInterval_dist_eq_coe_sub (le_top : t ≤ ⊤)]
  simp

private noncomputable def unitGridTime (blocks : ℕ) (hblocks : 0 < blocks)
    (i : Fin (blocks + 1)) : unitInterval := by
  let grid : UniformGrid ℝ := UniformGrid.unit (K := ℝ) blocks hblocks
  exact ⟨grid.point i, by simpa [grid] using UniformGrid.point_mem_Icc grid i⟩

private theorem unitGridTime_coe (blocks : ℕ) (hblocks : 0 < blocks)
    (i : Fin (blocks + 1)) :
    (unitGridTime blocks hblocks i : ℝ) = (i : ℝ) / blocks := by
  change (UniformGrid.unit (K := ℝ) blocks hblocks).point i = (i : ℝ) / blocks
  exact UniformGrid.unit_point (K := ℝ) blocks hblocks i

private theorem unitGridTime_strictMono (blocks : ℕ) (hblocks : 0 < blocks) :
    StrictMono (unitGridTime blocks hblocks) := by
  intro i j hij
  apply Subtype.coe_lt_coe.mpr
  let grid : UniformGrid ℝ := UniformGrid.unit (K := ℝ) blocks hblocks
  change grid.point i < grid.point j
  exact UniformGrid.strictMono_point (grid := grid) (by norm_num [grid]) hij

private theorem unitGridTime_step_distance (blocks : ℕ) (hblocks : 0 < blocks)
    (i : Fin blocks) :
    dist (unitGridTime blocks hblocks i.castSucc)
      (unitGridTime blocks hblocks i.succ) = 1 / (blocks : ℝ) := by
  rw [Subtype.dist_eq, Real.dist_eq]
  have hmono : (unitGridTime blocks hblocks i.castSucc : ℝ) ≤
      (unitGridTime blocks hblocks i.succ : ℝ) :=
    (unitGridTime_strictMono blocks hblocks i.castSucc_lt_succ).le
  rw [abs_of_nonpos (sub_nonpos.mpr hmono)]
  rw [unitGridTime_coe, unitGridTime_coe]
  have hsucc : (i.succ : ℝ) = (i.castSucc : ℝ) + 1 := by
    norm_num [Fin.val_succ, Fin.val_castSucc]
  rw [hsucc]
  have hblocksR : (blocks : ℝ) ≠ 0 := by exact_mod_cast hblocks.ne'
  field_simp
  ring

private theorem unitGridTime_pair_distance_lower
    (blocks : ℕ) (hblocks : 0 < blocks) {i j : Fin (blocks + 1)} (hij : i ≠ j) :
    1 / (blocks : ℝ) ≤ dist (unitGridTime blocks hblocks i)
      (unitGridTime blocks hblocks j) := by
  have hforward {i j : Fin (blocks + 1)} (hij : i < j) :
      1 / (blocks : ℝ) ≤ dist (unitGridTime blocks hblocks i)
        (unitGridTime blocks hblocks j) := by
    let k : Fin blocks := ⟨i.val, by omega⟩
    have hk : k.castSucc = i := by apply Fin.ext; rfl
    have hks : k.succ ≤ j := by
      apply Fin.le_iff_val_le_val.mpr
      simp only [Fin.val_succ]
      exact Fin.lt_def.mp hij
    have hstep := unitGridTime_step_distance blocks hblocks k
    rw [hk] at hstep
    have hmono1 : unitGridTime blocks hblocks i ≤
        unitGridTime blocks hblocks k.succ := by
      rw [← hk]
      exact (unitGridTime_strictMono blocks hblocks k.castSucc_lt_succ).le
    have hmono2 : unitGridTime blocks hblocks k.succ ≤ unitGridTime blocks hblocks j :=
      (unitGridTime_strictMono blocks hblocks).monotone hks
    calc
      1 / (blocks : ℝ) = dist (unitGridTime blocks hblocks i)
          (unitGridTime blocks hblocks k.succ) := hstep.symm
      _ ≤ dist (unitGridTime blocks hblocks i) (unitGridTime blocks hblocks j) :=
        unitInterval_dist_le_of_subintervals le_rfl hmono1 hmono2
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact hforward hij
  · simpa [dist_comm] using hforward hji

private theorem exists_unitGridTime_between
    {blocks : ℕ} (hblocks : 0 < blocks) {p q : unitInterval} {c : ℝ}
    (hc : 0 ≤ c)
    (hwidth : 2 * (c + 1 / (blocks : ℝ)) < (q : ℝ) - (p : ℝ)) :
    ∃ j : Fin (blocks + 1), (p : ℝ) + c < unitGridTime blocks hblocks j ∧
      (unitGridTime blocks hblocks j : ℝ) < (q : ℝ) - c := by
  have hblocksR : 0 < (blocks : ℝ) := by exact_mod_cast hblocks
  let raw := (p : ℝ) + c
  let k := Nat.floor (raw * (blocks : ℝ)) + 1
  have hraw : 0 ≤ raw := by dsimp [raw]; linarith [(p : unitInterval).property.1]
  have hmul_nonneg : 0 ≤ raw * (blocks : ℝ) := mul_nonneg hraw hblocksR.le
  have hfloor_le : (Nat.floor (raw * (blocks : ℝ)) : ℝ) ≤ raw * (blocks : ℝ) :=
    Nat.floor_le hmul_nonneg
  have hfloor_lt : raw * (blocks : ℝ) <
      (Nat.floor (raw * (blocks : ℝ)) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hk_lower : raw * (blocks : ℝ) < (k : ℝ) := by
    dsimp [k]
    push_cast
    exact hfloor_lt
  have hk_upper : (k : ℝ) ≤ (raw + 1 / (blocks : ℝ)) * (blocks : ℝ) := by
    have hkcast : (k : ℝ) =
        (Nat.floor (raw * (blocks : ℝ)) : ℝ) + 1 := by simp [k]
    have hmul : (raw + 1 / (blocks : ℝ)) * (blocks : ℝ) =
        raw * (blocks : ℝ) + 1 := by
      field_simp [hblocksR.ne']
    rw [hkcast, hmul]
    linarith [hfloor_le]
  have hleft : raw < (k : ℝ) / (blocks : ℝ) :=
    (lt_div_iff₀ hblocksR).2 (by simpa [raw, mul_comm] using hk_lower)
  have hright : (k : ℝ) / (blocks : ℝ) ≤
      raw + 1 / (blocks : ℝ) := (div_le_iff₀ hblocksR).2 hk_upper
  have hlast : (k : ℝ) / (blocks : ℝ) < (q : ℝ) - c := by
    dsimp [raw] at hleft hright
    linarith [hwidth, hblocksR]
  have hltOne : (k : ℝ) / (blocks : ℝ) < 1 :=
    lt_of_lt_of_le hlast (by linarith [(q : unitInterval).property.2])
  have hk_real : (k : ℝ) < (blocks : ℝ) :=
    by simpa using (div_lt_iff₀ hblocksR).mp hltOne
  have hk_nat : k < blocks := by exact_mod_cast hk_real
  let j : Fin (blocks + 1) := ⟨k, by omega⟩
  have hjval : (unitGridTime blocks hblocks j : ℝ) = (k : ℝ) / (blocks : ℝ) := by
    rw [unitGridTime_coe]
  refine ⟨j, ?_, ?_⟩
  · rw [hjval]
    exact hleft
  · rw [hjval]
    exact hlast

private theorem exists_partition_enumerating_finset
    (pointsSet : Finset unitInterval)
    (hbottom : (⊥ : unitInterval) ∈ pointsSet)
    (htop : (⊤ : unitInterval) ∈ pointsSet) :
    ∃ partition : OscillationPartition, Set.range partition.points = pointsSet ∧
      partition.mesh = OscillationPartition.finitePointMesh partition.size_pos partition.points := by
  classical
  have hendpoints : ({(⊥ : unitInterval), ⊤} : Finset unitInterval) ⊆ pointsSet := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · exact hbottom
    · exact htop
  have hcard : 2 ≤ pointsSet.card := by
    have hpair : ({(⊥ : unitInterval), ⊤} : Finset unitInterval).card = 2 :=
      Finset.card_pair bot_ne_top
    exact hpair ▸ Finset.card_le_card hendpoints
  let size := pointsSet.card - 1
  have hsizeCard : size + 1 = pointsSet.card :=
    Nat.sub_add_cancel (by omega : 1 ≤ pointsSet.card)
  let orderedPoints : Fin pointsSet.card → unitInterval :=
    pointsSet.orderEmbOfFin rfl
  let points : Fin (size + 1) → unitInterval := fun i =>
    orderedPoints (Fin.cast hsizeCard i)
  have hpointsStrict : StrictMono points := by
    apply StrictMono.comp (pointsSet.orderEmbOfFin rfl).strictMono
    intro i j hij
    apply Fin.lt_def.mpr
    simpa [Fin.val_cast] using (Fin.lt_def.mp hij)
  have hpointsBottom : points ⟨0, by omega⟩ = ⊥ := by
    have hmem : (⊥ : unitInterval) ∈ (pointsSet : Set unitInterval) := hbottom
    rw [← pointsSet.range_orderEmbOfFin rfl] at hmem
    obtain ⟨i, hi⟩ := hmem
    let zeroIndex : Fin pointsSet.card := ⟨0, by omega⟩
    have hzero : zeroIndex ≤ i := Fin.le_iff_val_le_val.mpr (by simp [zeroIndex])
    have hle := (pointsSet.orderEmbOfFin rfl).monotone hzero
    have hraw : (pointsSet.orderEmbOfFin rfl) zeroIndex ≤ ⊥ := by
      simpa [hi] using hle
    change orderedPoints (Fin.cast hsizeCard ⟨0, by omega⟩) = ⊥
    have hcast : Fin.cast hsizeCard (⟨0, by omega⟩ : Fin (size + 1)) = zeroIndex := by
      apply Fin.ext
      simp [zeroIndex, Fin.val_cast]
    rw [hcast]
    exact le_antisymm hraw bot_le
  have hpointsTop : points ⟨size, by omega⟩ = ⊤ := by
    have hmem : (⊤ : unitInterval) ∈ (pointsSet : Set unitInterval) := htop
    rw [← pointsSet.range_orderEmbOfFin rfl] at hmem
    obtain ⟨i, hi⟩ := hmem
    let hlast : Fin pointsSet.card := ⟨size, by omega⟩
    have hiSize : i.val < size + 1 := by simp [hsizeCard]
    have hlastVal : hlast.val = size := rfl
    have hle : i ≤ hlast := Fin.le_iff_val_le_val.mpr (by
      rw [hlastVal]
      exact Nat.le_of_lt_succ hiSize)
    have hmono := (pointsSet.orderEmbOfFin rfl).monotone hle
    have htop' : (pointsSet.orderEmbOfFin rfl) i = ⊤ := hi
    have hraw : ⊤ ≤ (pointsSet.orderEmbOfFin rfl) hlast := by
      simpa [htop'] using hmono
    have hupper : (pointsSet.orderEmbOfFin rfl) hlast ≤ ⊤ := le_top
    have hlastEq : (pointsSet.orderEmbOfFin rfl) hlast = ⊤ :=
      le_antisymm hupper hraw
    change orderedPoints (Fin.cast hsizeCard ⟨size, by omega⟩) = ⊤
    have hlastCast :
        Fin.cast hsizeCard (⟨size, by omega⟩ : Fin (size + 1)) = hlast := by
      apply Fin.ext
      simp [hlast]
    rw [hlastCast]
    exact hlastEq
  have hsizePos : 0 < size := by omega
  let partition := OscillationPartition.ofFinitePoints hsizePos points
    hpointsBottom hpointsTop hpointsStrict
  have hrangePoints : Set.range points = pointsSet := by
    rw [← pointsSet.range_orderEmbOfFin rfl]
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨Fin.cast hsizeCard i, rfl⟩
    · rintro ⟨i, hi⟩
      refine ⟨Fin.cast hsizeCard.symm i, ?_⟩
      change orderedPoints (Fin.cast hsizeCard (Fin.cast hsizeCard.symm i)) = z
      have hcast : Fin.cast hsizeCard (Fin.cast hsizeCard.symm i) = i := by
        apply Fin.ext
        simp
      rw [hcast]
      exact hi
  refine ⟨partition, ?_, ?_⟩
  · change Set.range points = pointsSet
    exact hrangePoints
  · rfl

private theorem OscillationPartition.mesh_le_coe_of_positive_index
    (partition : OscillationPartition) (i : Fin partition.size)
    (hi : 0 < i.val) :
    partition.mesh ≤ (partition.points i.castSucc : ℝ) := by
  let firstCell : Fin partition.size := ⟨0, partition.size_pos⟩
  have hfirstLe : firstCell.succ ≤ i.castSucc := by
    apply Fin.le_iff_val_le_val.mpr
    simp [firstCell]
    exact hi
  have hpoints := partition.strictMono_points.monotone hfirstLe
  have hfirstPoint : partition.points firstCell.castSucc = ⊥ := by
    simpa [firstCell] using partition.first
  have hdist : dist (⊥ : unitInterval) (partition.points firstCell.succ) =
      (partition.points firstCell.succ : ℝ) := by
    rw [Subtype.dist_eq, Real.dist_eq]
    have hnonneg : 0 ≤ (partition.points firstCell.succ : ℝ) :=
      (partition.points firstCell.succ).property.1
    simp [abs_of_nonpos, hnonneg]
  have hgap := partition.gap_lower firstCell
  rw [hfirstPoint, hdist] at hgap
  exact hgap.trans (by exact_mod_cast hpoints)

private theorem OscillationPartition.coe_le_one_sub_mesh
    (partition : OscillationPartition) (i : Fin partition.size) :
    (partition.points i.castSucc : ℝ) ≤ 1 - partition.mesh := by
  let lastCell : Fin partition.size :=
    ⟨partition.size - 1, Nat.sub_lt partition.size_pos (by decide)⟩
  have hindexLe : i.castSucc ≤ lastCell.castSucc := by
    apply Fin.le_iff_val_le_val.mpr
    change i.val ≤ partition.size - 1
    omega
  have hpointsLe := partition.strictMono_points.monotone hindexLe
  have hlastSucc : lastCell.succ = Fin.last partition.size := by
    apply Fin.ext
    simp only [Fin.val_succ, Fin.val_last]
    dsimp [lastCell]
    have hsize : 1 ≤ partition.size := Nat.succ_le_iff.mpr partition.size_pos
    omega
  have hlastPoint : partition.points lastCell.succ = ⊤ := by
    rw [hlastSucc]
    simpa [Fin.last] using partition.last
  have hdist : dist (partition.points lastCell.castSucc) (⊤ : unitInterval) =
      1 - (partition.points lastCell.castSucc : ℝ) := by
    rw [Subtype.dist_eq, Real.dist_eq]
    have hleOne : (partition.points lastCell.castSucc : ℝ) ≤ 1 :=
      (partition.points lastCell.castSucc).property.2
    change |(partition.points lastCell.castSucc : ℝ) - 1| = _
    rw [abs_of_nonpos (by linarith)]
    ring
  have hgap := partition.gap_lower lastCell
  rw [hlastPoint, hdist] at hgap
  have hle : (partition.points i.castSucc : ℝ) ≤
      (partition.points lastCell.castSucc : ℝ) := by exact_mod_cast hpointsLe
  linarith

private theorem unitInterval_ne_top_of_coe_lt_one {t : unitInterval}
    (ht : (t : ℝ) < 1) : t ≠ ⊤ := by
  intro heq
  have hval : (t : ℝ) = 1 := by simp [heq]
  linarith

private theorem OscillationPartition.mesh_le_one
    (partition : OscillationPartition) : partition.mesh ≤ 1 := by
  have hsize : 1 ≤ (partition.size : ℝ) := by
    exact_mod_cast partition.size_pos
  have hmul := partition.size_mul_mesh_le_one
  have hmesh := partition.mesh_pos
  nlinarith

private theorem OscillationPartition.leftEndpoint_dist_le
    {E : Type*} [PseudoMetricSpace E]
    (partition : OscillationPartition) (path : CadlagPath unitInterval E)
    {delta epsilon : ℝ} (hmesh : delta ≤ partition.mesh)
    (hosc : OscillationBoundedOnPartition partition path epsilon)
    {s t : unitInterval} (hst : s ≤ t)
    (hsδ : (s : ℝ) < delta) (htδ : (t : ℝ) < delta) :
    dist (path s) (path t) ≤ epsilon := by
  have hδOne : delta ≤ 1 := hmesh.trans partition.mesh_le_one
  have hsTop : s ≠ ⊤ :=
    unitInterval_ne_top_of_coe_lt_one (lt_of_lt_of_le hsδ hδOne)
  have htTop : t ≠ ⊤ :=
    unitInterval_ne_top_of_coe_lt_one (lt_of_lt_of_le htδ hδOne)
  by_cases hindex : partition.index s = partition.index t
  · exact hosc s t hsTop htTop hindex
  · have hidx : partition.index s < partition.index t :=
      lt_of_le_of_ne (partition.index_monotone hst) hindex
    let j := partition.index t
    have hjpos : 0 < j.val := by
      dsimp [j]
      have hval := Fin.lt_def.mp hidx
      omega
    let q := partition.points j.castSucc
    have hstart : partition.index q = partition.index t := by
      dsimp [q, j]
      exact partition.index_start (partition.index t)
    have hsltq : s < q := by
      by_contra hnot
      have hqs : q ≤ s := le_of_not_gt hnot
      have hidxqs := partition.index_monotone hqs
      rw [hstart] at hidxqs
      exact (not_lt_of_ge hidxqs) hidx
    have hqt : q ≤ t := partition.index_lower t
    have hmeshQ := partition.mesh_le_coe_of_positive_index j hjpos
    have hqδ : (q : ℝ) < delta := lt_of_le_of_lt (by exact_mod_cast hqt) htδ
    have hδq : delta ≤ (q : ℝ) := hmesh.trans hmeshQ
    linarith

private theorem OscillationPartition.rightEndpoint_dist_le
    {E : Type*} [PseudoMetricSpace E]
    (partition : OscillationPartition) (path : CadlagPath unitInterval E)
    {delta epsilon : ℝ} (hmesh : delta ≤ partition.mesh)
    (hosc : OscillationBoundedOnPartition partition path epsilon)
    {s t : unitInterval} (hst : s ≤ t) (hsTop : s ≠ ⊤) (htTop : t ≠ ⊤)
    (hsδ : 1 - delta < (s : ℝ)) (_htδ : 1 - delta < (t : ℝ)) :
    dist (path s) (path t) ≤ epsilon := by
  by_cases hindex : partition.index s = partition.index t
  · exact hosc s t hsTop htTop hindex
  · have hidx : partition.index s < partition.index t :=
      lt_of_le_of_ne (partition.index_monotone hst) hindex
    let j := partition.index t
    let q := partition.points j.castSucc
    have hstart : partition.index q = partition.index t := by
      dsimp [q, j]
      exact partition.index_start (partition.index t)
    have hsltq : s < q := by
      by_contra hnot
      have hqs : q ≤ s := le_of_not_gt hnot
      have hidxqs := partition.index_monotone hqs
      rw [hstart] at hidxqs
      exact (not_lt_of_ge hidxqs) hidx
    have hqt : q ≤ t := partition.index_lower t
    have hqUpper := partition.coe_le_one_sub_mesh j
    have hsUpper : (s : ℝ) ≤ 1 - partition.mesh :=
      le_trans (by exact_mod_cast hsltq.le) hqUpper
    have hmeshDelta : delta ≤ partition.mesh := hmesh
    have hsLower : 1 - delta < (s : ℝ) := hsδ
    have hcontr : (s : ℝ) ≤ 1 - delta := by linarith
    exact (not_lt_of_ge hcontr hsLower).elim

/-- A partition with cell oscillation at most `epsilon` bounds the
double-excursion modulus at every time scale no larger than its minimum gap.
The terminal time is excluded, consistently with the separate terminal
coordinate in `OscillationBoundedOnPartition`. -/
theorem OscillationBoundedOnPartition.hasDoubleExcursionBound
    {E : Type*} [PseudoMetricSpace E]
    (partition : OscillationPartition) (path : CadlagPath unitInterval E)
    {delta epsilon : ℝ} (hmesh : delta ≤ partition.mesh)
    (hosc : OscillationBoundedOnPartition partition path epsilon) :
    HasDoubleExcursionBound path delta epsilon := by
  intro s t u hst htu huTop hdist x y z w hsx hxyTime hyt htz hzwTime hwu
  have hu_lt_top : u < ⊤ := lt_top_iff_ne_top.mpr huTop
  have hx_lt_top : x < ⊤ :=
    lt_of_le_of_lt (hxyTime.trans hyt) (htu.trans hu_lt_top)
  have hy_lt_top : y < ⊤ := lt_of_le_of_lt hyt (htu.trans hu_lt_top)
  have hz_lt_top : z < ⊤ := lt_of_le_of_lt (hzwTime.trans hwu) hu_lt_top
  have hw_lt_top : w < ⊤ := lt_of_le_of_lt hwu hu_lt_top
  by_cases hxy : partition.index x = partition.index y
  · exact (min_le_left _ _).trans
      (hosc x y (ne_of_lt hx_lt_top) (ne_of_lt hy_lt_top) hxy)
  · by_cases hzw : partition.index z = partition.index w
    · exact (min_le_right _ _).trans
        (hosc z w (ne_of_lt hz_lt_top) (ne_of_lt hw_lt_top) hzw)
    · have hixy : partition.index x ≤ partition.index y :=
        partition.index_monotone hxyTime
      have hixy' : partition.index x < partition.index y :=
        lt_of_le_of_ne hixy hxy
      have hizw : partition.index z ≤ partition.index w :=
        partition.index_monotone hzwTime
      have hizw' : partition.index z < partition.index w :=
        lt_of_le_of_ne hizw hzw
      have hiyz : partition.index y ≤ partition.index z :=
        partition.index_monotone (hyt.trans htz)
      let i := partition.index y
      let j := partition.index w
      let q := partition.points i.castSucc
      let r := partition.points j.castSucc
      have hqle : q ≤ y := by
        exact partition.index_lower y
      have hrle : r ≤ w := by
        exact partition.index_lower w
      have hxq : x < q := by
        by_contra hnot
        have hqx : q ≤ x := le_of_not_gt hnot
        have hindex := partition.index_monotone hqx
        have hstart : partition.index q = partition.index y := by
          dsimp [q, i]
          exact partition.index_start (partition.index y)
        rw [hstart] at hindex
        exact (not_lt_of_ge hindex) hixy'
      have hzr : z < r := by
        by_contra hnot
        have hrz : r ≤ z := le_of_not_gt hnot
        have hindex := partition.index_monotone hrz
        have hstart : partition.index r = partition.index w := by
          dsimp [r, j]
          exact partition.index_start (partition.index w)
        rw [hstart] at hindex
        exact (not_lt_of_ge hindex) hizw'
      have hij : i < j := by
        dsimp [i, j]
        exact lt_of_le_of_lt hiyz hizw'
      have hqr : q < r := by
        dsimp [q, r, i, j]
        apply partition.strictMono_points
        apply Fin.lt_def.mpr
        simpa using (Fin.lt_def.mp hij)
      have hsuccLe : i.succ ≤ j.castSucc := by
        apply Fin.le_iff_val_le_val.mpr
        rw [Fin.val_succ, Fin.val_castSucc]
        exact Nat.succ_le_of_lt (Fin.lt_def.mp hij)
      have hqNext : q ≤ partition.points i.succ := by
        dsimp [q]
        exact le_of_lt (partition.strictMono_points i.castSucc_lt_succ)
      have hnextR : partition.points i.succ ≤ r := by
        dsimp [r, j]
        exact partition.strictMono_points.monotone hsuccLe
      have hmeshQr : partition.mesh ≤ dist q r := by
        calc
          partition.mesh ≤ dist (partition.points i.castSucc)
              (partition.points i.succ) := partition.gap_lower i
          _ = dist q (partition.points i.succ) := by rfl
          _ ≤ dist q r := unitInterval_dist_le_of_subintervals le_rfl hqNext hnextR
      have hsQ : s ≤ q := le_trans hsx hxq.le
      have hrU : r ≤ u := le_trans hrle hwu
      have hqrSu : dist q r ≤ dist s u :=
        unitInterval_dist_le_of_subintervals hsQ (le_of_lt hqr) hrU
      have hmeshLt : partition.mesh < delta :=
        lt_of_le_of_lt (hmeshQr.trans hqrSu) hdist
      exact (not_lt_of_ge hmesh hmeshLt).elim

/-- Cellwise oscillation control and a common cell-gap lower bound imply the
corresponding oscillation controls at both endpoints. -/
theorem OscillationBoundedOnPartition.hasEndpointOscillationBound
    {E : Type*} [PseudoMetricSpace E]
    (partition : OscillationPartition) (path : CadlagPath unitInterval E)
    {delta epsilon : ℝ} (hmesh : delta ≤ partition.mesh)
    (hosc : OscillationBoundedOnPartition partition path epsilon) :
    HasEndpointOscillationBound path delta epsilon := by
  constructor
  · intro s t hsδ htδ
    rcases le_total s t with hst | hts
    · exact partition.leftEndpoint_dist_le path hmesh hosc hst hsδ htδ
    · simpa [dist_comm] using
        partition.leftEndpoint_dist_le path hmesh hosc hts htδ hsδ
  · intro s t hsTop htTop hsδ htδ
    rcases le_total s t with hst | hts
    · exact partition.rightEndpoint_dist_le path hmesh hosc hst hsTop htTop hsδ htδ
    · simpa [dist_comm] using
        partition.rightEndpoint_dist_le path hmesh hosc hts htTop hsTop htδ hsδ

/-- A uniform oscillation-partition criterion supplies uniform double-
excursion and endpoint controls with the same mesh and oscillation scales.
This is the necessary direction; `w''` alone does not encode the endpoint
controls needed for the converse. -/
theorem forall_mem_admitsOscillationPartition_hasBillingsleyControls
    {E : Type*} [MetricSpace E] {K : Set (CadlagPath unitInterval E)}
    {minimumGap maximumOscillation : ℝ}
    (hpart : ∀ path ∈ K,
      path ∈ admitsOscillationPartition minimumGap maximumOscillation) :
    ∀ path ∈ K,
      HasDoubleExcursionBound path minimumGap maximumOscillation ∧
      HasEndpointOscillationBound path minimumGap maximumOscillation := by
  intro path hpath
  obtain ⟨partition, hgap, bound, hbound, hosc⟩ := hpart path hpath
  have hosc' : OscillationBoundedOnPartition partition path maximumOscillation := by
    intro s t hs ht hindex
    exact (hosc s t hs ht hindex).trans (le_of_lt hbound)
  have hmesh : minimumGap ≤ partition.mesh := le_of_lt hgap
  exact ⟨OscillationBoundedOnPartition.hasDoubleExcursionBound
      partition path hmesh hosc',
    OscillationBoundedOnPartition.hasEndpointOscillationBound
      partition path hmesh hosc'⟩

/-- The pathwise converse to the double-excursion criterion, with endpoint
oscillation controlled separately. For `0 < delta ≤ 1`, a path satisfying
the double-excursion bound and both endpoint bounds admits a finite
oscillation partition with mesh at least `delta / 16` and cell oscillation
at most `5 * epsilon`.

The construction retains every interior jump larger than `2 * epsilon`, then
keeps only those points of a uniform grid that stay at least `delta / 16`
from these jumps. This gives a uniform mesh lower bound and cell lengths
smaller than `delta`; the crossing estimate handles nonterminal cells, and
the right endpoint control handles the final cell. -/
theorem HasDoubleExcursionBound.exists_oscillation_partition
    {E : Type*} [PseudoMetricSpace E]
    {path : CadlagPath unitInterval E} {delta epsilon : ℝ}
    (hdouble : HasDoubleExcursionBound path delta epsilon)
    (hend : HasEndpointOscillationBound path delta epsilon)
    (hdelta : 0 < delta) (hdelta_le_one : delta ≤ 1)
    (hepsilon : 0 < epsilon) :
    ∃ partition : OscillationPartition,
      delta / 16 ≤ partition.mesh ∧
        OscillationBoundedOnPartition partition path (5 * epsilon) := by
  classical
  let large : Set unitInterval := {t | t ≠ ⊥ ∧ t ≠ ⊤ ∧
    2 * epsilon < dist (Function.leftLim (fun s : unitInterval => path s) t) (path t)}
  have hlargeFinite : large.Finite := by
    apply (path.isCadlag_toFun.finite_jumpTimesAbove
      (epsilon := 2 * epsilon) (by positivity)).subset
    intro t ht
    exact ⟨ht.1, ht.2.2⟩
  let largePoints : Finset unitInterval := hlargeFinite.toFinset
  have mem_largePoints {t : unitInterval} : t ∈ largePoints ↔ t ∈ large := by
    simp [largePoints]
  have hlargeAway {t : unitInterval} (ht : t ∈ large) :
      delta ≤ (t : ℝ) ∧ (t : ℝ) ≤ 1 - delta := by
    rcases ht with ⟨_, httop, hjump⟩
    exact hend.largeJump_awayFromEndpoints hepsilon httop hjump
  have hlargeSeparated {s t : unitInterval} (hs : s ∈ large) (ht : t ∈ large)
      (hne : s ≠ t) : delta ≤ dist s t := by
    rcases hs with ⟨hsbot, hstop, hsjump⟩
    rcases ht with ⟨htbot, httop, htjump⟩
    exact largeJumps_separated hdouble hepsilon hsbot hstop htbot httop hne hsjump htjump
  let blocks : ℕ := Nat.floor (4 / delta)
  have hfloor_nonneg : 0 ≤ 4 / delta := by positivity
  have hfloor_le : (blocks : ℝ) ≤ 4 / delta := by
    dsimp [blocks]
    exact Nat.floor_le hfloor_nonneg
  have hfloor_lt : 4 / delta < (blocks : ℝ) + 1 := by
    dsimp [blocks]
    exact Nat.lt_floor_add_one _
  have hdeltaInv : 1 ≤ 1 / delta := by
    apply (le_div_iff₀ hdelta).2
    nlinarith [hdelta_le_one]
  have hfour : 4 ≤ 4 / delta := by
    apply (le_div_iff₀ hdelta).2
    nlinarith [hdelta_le_one]
  have hblocksLarge : 3 < (blocks : ℝ) := by linarith
  have hblocks : 0 < blocks := by exact_mod_cast (by linarith : (0 : ℝ) < blocks)
  have hblocksR : 0 < (blocks : ℝ) := by exact_mod_cast hblocks
  have hblocksDeltaUpper : (blocks : ℝ) * delta ≤ 4 :=
    (le_div_iff₀ hdelta).mp hfloor_le
  have hblocksDeltaLower : 3 < (blocks : ℝ) * delta := by
    have hfourEq : 4 / delta = 3 / delta + 1 / delta := by
      field_simp [hdelta.ne']
      ring
    have hthree : 3 / delta ≤ 4 / delta - 1 := by
      rw [hfourEq]
      linarith [hdeltaInv]
    have hfloorLower : 4 / delta - 1 < (blocks : ℝ) := by linarith [hfloor_lt]
    have hblocksLower : 3 / delta < (blocks : ℝ) := lt_of_le_of_lt hthree hfloorLower
    exact (div_lt_iff₀ hdelta).mp hblocksLower
  have hstepLower : delta / 4 ≤ 1 / (blocks : ℝ) := by
    have hdeltaN : delta ≤ 4 / (blocks : ℝ) :=
      (le_div_iff₀ hblocksR).2 (by nlinarith [hblocksDeltaUpper])
    calc
      delta / 4 ≤ (4 / (blocks : ℝ)) / 4 :=
        div_le_div_of_nonneg_right hdeltaN (by norm_num)
      _ = 1 / (blocks : ℝ) := by field_simp [hblocksR.ne']
  have hstepUpper : 1 / (blocks : ℝ) < delta / 3 := by
    apply (div_lt_iff₀ hblocksR).2
    nlinarith [hblocksDeltaLower]
  let gap := delta / 16
  have hgap_nonneg : 0 ≤ gap := by dsimp [gap]; linarith
  have hgap_pos : 0 < gap := by dsimp [gap]; positivity
  have hgap_le_delta : gap ≤ delta := by dsimp [gap]; linarith
  have hgap_le_step : gap ≤ 1 / (blocks : ℝ) := by
    dsimp [gap]
    linarith
  have hgridWindow : 2 * (gap + 1 / (blocks : ℝ)) < delta := by
    dsimp [gap]
    nlinarith [hstepUpper, hdelta]
  let goodIndices : Finset (Fin (blocks + 1)) := Finset.univ.filter fun j =>
    ∀ t ∈ large, gap ≤ dist (unitGridTime blocks hblocks j) t
  let goodPoints : Finset unitInterval := goodIndices.image (unitGridTime blocks hblocks)
  let zero : Fin (blocks + 1) := ⟨0, by omega⟩
  let last : Fin (blocks + 1) := ⟨blocks, by omega⟩
  have hzeroTime : unitGridTime blocks hblocks zero = ⊥ := by
    apply Subtype.ext
    rw [unitGridTime_coe]
    simp [zero]
  have hlastTime : unitGridTime blocks hblocks last = ⊤ := by
    apply Subtype.ext
    rw [unitGridTime_coe]
    change (blocks : ℝ) / (blocks : ℝ) = 1
    field_simp [hblocksR.ne']
  have hzeroGood : zero ∈ goodIndices := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro t ht
    have haway := hlargeAway ht
    rw [hzeroTime, unitInterval_dist_bot_eq]
    exact hgap_le_delta.trans haway.1
  have hlastGood : last ∈ goodIndices := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro t ht
    have haway := hlargeAway ht
    rw [hlastTime, unitInterval_dist_top_eq]
    have hdist : delta ≤ 1 - (t : ℝ) := by linarith [haway.2]
    exact hgap_le_delta.trans hdist
  have hbottomGood : (⊥ : unitInterval) ∈ goodPoints :=
    Finset.mem_image.mpr ⟨zero, hzeroGood, hzeroTime⟩
  have htopGood : (⊤ : unitInterval) ∈ goodPoints :=
    Finset.mem_image.mpr ⟨last, hlastGood, hlastTime⟩
  let pointsSet := largePoints ∪ goodPoints
  have hbottomSet : (⊥ : unitInterval) ∈ pointsSet :=
    Finset.mem_union.mpr (Or.inr hbottomGood)
  have htopSet : (⊤ : unitInterval) ∈ pointsSet :=
    Finset.mem_union.mpr (Or.inr htopGood)
  have hgoodDistance {x : unitInterval} (hx : x ∈ goodPoints)
      {t : unitInterval} (ht : t ∈ large) : gap ≤ dist x t := by
    obtain ⟨j, hj, hjx⟩ := Finset.mem_image.mp hx
    have hjgood := (Finset.mem_filter.mp hj).2
    rw [← hjx]
    exact hjgood t ht
  have hremovedGrid {j : Fin (blocks + 1)}
      (hnot : unitGridTime blocks hblocks j ∉ goodPoints) :
      ∃ t ∈ large, dist (unitGridTime blocks hblocks j) t < gap := by
    by_contra hnone
    push Not at hnone
    have hgood : ∀ t ∈ large, gap ≤ dist (unitGridTime blocks hblocks j) t := by
      intro t ht
      exact hnone t ht
    have hj : j ∈ goodIndices := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgood⟩
    exact hnot (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
  have hpointSeparated {x y : unitInterval} (hx : x ∈ pointsSet)
      (hy : y ∈ pointsSet) (hne : x ≠ y) : gap ≤ dist x y := by
    rcases Finset.mem_union.mp hx with hxLarge | hxGood
    · rcases Finset.mem_union.mp hy with hyLarge | hyGood
      · exact hgap_le_delta.trans (hlargeSeparated
          (mem_largePoints.mp hxLarge) (mem_largePoints.mp hyLarge) hne)
      · have h := hgoodDistance hyGood (mem_largePoints.mp hxLarge)
        simpa [dist_comm] using h
    · rcases Finset.mem_union.mp hy with hyLarge | hyGood
      · have h := hgoodDistance hxGood (mem_largePoints.mp hyLarge)
        simpa [dist_comm] using h
      · obtain ⟨i, hi, hix⟩ := Finset.mem_image.mp hxGood
        obtain ⟨j, hj, hjy⟩ := Finset.mem_image.mp hyGood
        have hij : i ≠ j := by
          intro heq
          apply hne
          calc
            x = unitGridTime blocks hblocks i := hix.symm
            _ = unitGridTime blocks hblocks j := by rw [heq]
            _ = y := hjy
        have hgrid := unitGridTime_pair_distance_lower blocks hblocks hij
        calc
          gap ≤ 1 / (blocks : ℝ) := hgap_le_step
          _ ≤ dist (unitGridTime blocks hblocks i) (unitGridTime blocks hblocks j) := hgrid
          _ = dist x y := by rw [hix, hjy]

  obtain ⟨partition, hpartitionRange, hpartitionMesh⟩ :=
    exists_partition_enumerating_finset pointsSet hbottomSet htopSet
  have hnoPointBetween {i : Fin partition.size} {z : unitInterval}
      (hz : z ∈ pointsSet)
      (hpz : partition.points i.castSucc < z)
      (hzq : z < partition.points i.succ) : False := by
    have hzRange : z ∈ Set.range partition.points := by
      rw [hpartitionRange]
      exact hz
    obtain ⟨j, hj⟩ := hzRange
    have hleft : i.castSucc.val < j.val := by
      by_contra hnot
      have hjle : j ≤ i.castSucc := Fin.le_iff_val_le_val.mpr (Nat.le_of_not_gt hnot)
      have hmono := partition.strictMono_points.monotone hjle
      have hzle : z ≤ partition.points i.castSucc := by rw [← hj]; exact hmono
      exact (not_le_of_gt hpz) hzle
    have hright : j.val < i.succ.val := by
      by_contra hnot
      have hle : i.succ ≤ j := Fin.le_iff_val_le_val.mpr (Nat.le_of_not_gt hnot)
      have hmono := partition.strictMono_points.monotone hle
      have hqle : partition.points i.succ ≤ z := by rw [← hj]; exact hmono
      exact (not_le_of_gt hzq) hqle
    have hleftVal : i.castSucc.val = i.val := by simp
    have hrightVal : i.succ.val = i.val + 1 := by simp
    omega
  have hgapLower (i : Fin partition.size) :
      gap ≤ dist (partition.points i.castSucc) (partition.points i.succ) := by
    have hleftSet : partition.points i.castSucc ∈ pointsSet := by
      have hrange : partition.points i.castSucc ∈ Set.range partition.points :=
        ⟨i.castSucc, rfl⟩
      rw [hpartitionRange] at hrange
      exact hrange
    have hrightSet : partition.points i.succ ∈ pointsSet := by
      have hrange : partition.points i.succ ∈ Set.range partition.points :=
        ⟨i.succ, rfl⟩
      rw [hpartitionRange] at hrange
      exact hrange
    have hne : partition.points i.castSucc ≠ partition.points i.succ :=
      ne_of_lt (partition.strictMono_points i.castSucc_lt_succ)
    exact hpointSeparated hleftSet hrightSet hne
  have hgapUpper (i : Fin partition.size) :
      dist (partition.points i.castSucc) (partition.points i.succ) < delta := by
    let p := partition.points i.castSucc
    let q := partition.points i.succ
    have hpq : p < q := by dsimp [p, q]; exact partition.strictMono_points i.castSucc_lt_succ
    have hdistEq : dist p q = (q : ℝ) - (p : ℝ) :=
      unitInterval_dist_eq_coe_sub hpq.le
    by_contra hnot
    have hdeltaDist : delta ≤ dist p q := le_of_not_gt hnot
    have hwidth : 2 * (gap + 1 / (blocks : ℝ)) < (q : ℝ) - (p : ℝ) := by
      rw [← hdistEq]
      exact hgridWindow.trans_le hdeltaDist
    obtain ⟨j, hpr, hrq⟩ := exists_unitGridTime_between hblocks hgap_nonneg hwidth
    let r := unitGridTime blocks hblocks j
    have hprCoord : (p : ℝ) + gap < (r : ℝ) := by
      simpa [r, unitGridTime_coe] using hpr
    have hrqCoord : (r : ℝ) < (q : ℝ) - gap := by
      simpa [r, unitGridTime_coe] using hrq
    have hpr' : p < r := by
      apply Subtype.coe_lt_coe.mpr
      exact (le_add_of_nonneg_right hgap_nonneg).trans_lt hprCoord
    have hrq' : r < q := by
      apply Subtype.coe_lt_coe.mpr
      exact hrqCoord.trans (sub_lt_self _ hgap_pos)
    have hrNotGood : r ∉ goodPoints := by
      intro hrGood
      have hrSet : r ∈ pointsSet := Finset.mem_union.mpr (Or.inr hrGood)
      exact hnoPointBetween hrSet hpr' hrq'
    obtain ⟨t, htLarge, hrt⟩ := hremovedGrid hrNotGood
    have hpt : p < t := by
      by_contra hnot
      have htp : t ≤ p := le_of_not_gt hnot
      have hprLower : gap < dist p r := by
        rw [unitInterval_dist_eq_coe_sub hpr'.le]
        linarith [hprCoord]
      have hdistMono : dist p r ≤ dist t r :=
        unitInterval_dist_le_of_subintervals htp hpr'.le le_rfl
      have : dist t r < gap := by simpa [dist_comm] using hrt
      linarith
    have htq : t < q := by
      by_contra hnot
      have hqt : q ≤ t := le_of_not_gt hnot
      have hrqLower : gap < dist r q := by
        rw [unitInterval_dist_eq_coe_sub hrq'.le]
        linarith [hrqCoord]
      have hdistMono : dist r q ≤ dist r t :=
        unitInterval_dist_le_of_subintervals le_rfl hrq'.le hqt
      have : dist r t < gap := by simpa [dist_comm] using hrt
      linarith
    have htSet : t ∈ pointsSet :=
      Finset.mem_union.mpr (Or.inl (mem_largePoints.mpr htLarge))
    exact hnoPointBetween htSet hpt htq
  have hmesh : gap ≤ partition.mesh := by
    rw [hpartitionMesh]
    change gap ≤ (OscillationPartition.finitePointGaps partition.points).min'
      (OscillationPartition.finitePointGaps_nonempty partition.size_pos partition.points)
    apply Finset.le_min'
    intro d hd
    obtain ⟨i, -, hdist⟩ := Finset.mem_image.mp hd
    rw [← hdist]
    exact hgapLower i
  have hosc : OscillationBoundedOnPartition partition path (5 * epsilon) := by
    intro s t hsTop htTop hindex
    let i := partition.index s
    let p := partition.points i.castSucc
    let q := partition.points i.succ
    have htIndex : partition.index t = i := by simpa [i] using hindex.symm
    have hps : p ≤ s := partition.index_lower s
    have hpt : p ≤ t := by
      change partition.points i.castSucc ≤ t
      rw [← htIndex]
      exact partition.index_lower t
    have hsq : s < q := by
      rcases partition.index_upper s with hnext | hlast
      · simpa [i, q] using hnext
      · have hqtop : q = ⊤ := by
          have hsucc : (partition.index s).succ = Fin.last partition.size := by
            apply Fin.ext
            simp only [Fin.val_succ, Fin.val_last]
            omega
          dsimp [q, i]
          rw [hsucc]
          simpa [Fin.last] using partition.last
        rw [hqtop]
        exact lt_top_iff_ne_top.mpr hsTop
    have htq : t < q := by
      rcases partition.index_upper t with hnext | hlast
      · simpa [i, q, htIndex] using hnext
      · have hqtop : q = ⊤ := by
          have hsucc : (partition.index t).succ = Fin.last partition.size := by
            apply Fin.ext
            simp only [Fin.val_succ, Fin.val_last]
            omega
          dsimp [q, i]
          rw [hindex]
          rw [hsucc]
          simpa [Fin.last] using partition.last
        rw [hqtop]
        exact lt_top_iff_ne_top.mpr htTop
    have hpq : p < q := by dsimp [p, q]; exact partition.strictMono_points i.castSucc_lt_succ
    have hspan : dist p q < delta := by
      dsimp [p, q]
      exact hgapUpper i
    have hordered : ∀ x y : unitInterval, p ≤ x → x ≤ y → y < q →
        dist (path x) (path y) ≤ 5 * epsilon := by
      intro x y hpx hxy hyq
      by_cases hqtop : q = ⊤
      · have hpcoord : 1 - delta < (p : ℝ) := by
          have hdist : dist p q = 1 - (p : ℝ) := by
            rw [hqtop]
            simpa [dist_comm] using unitInterval_dist_top_eq p
          rw [hdist] at hspan
          linarith
        have hyTopLt : y < ⊤ := by simpa [hqtop] using hyq
        have hxTop : x ≠ ⊤ := ne_of_lt (lt_of_le_of_lt hxy hyTopLt)
        have hyTop : y ≠ ⊤ := ne_of_lt hyTopLt
        have hxRight : 1 - delta < (x : ℝ) := lt_of_lt_of_le hpcoord (by exact_mod_cast hpx)
        have hyRight : 1 - delta < (y : ℝ) := lt_of_lt_of_le hpcoord (by exact_mod_cast (hpx.trans hxy))
        have hbound := hend.2 x y hxTop hyTop hxRight hyRight
        exact hbound.trans (by nlinarith [hepsilon])
      · have hjump : ∀ z, p < z → z < q →
            dist (Function.leftLim (fun v : unitInterval => path v) z) (path z) ≤ 2 * epsilon := by
          intro z hpz hzq
          by_contra hnot
          have hj : 2 * epsilon <
              dist (Function.leftLim (fun v : unitInterval => path v) z) (path z) :=
            lt_of_not_ge hnot
          have hbot : z ≠ ⊥ := ne_of_gt (lt_of_le_of_lt bot_le hpz)
          have htop' : z ≠ ⊤ := ne_of_lt (lt_of_lt_of_le hzq le_top)
          have hlarge : z ∈ large := ⟨hbot, htop', hj⟩
          have hzSet : z ∈ pointsSet :=
            Finset.mem_union.mpr (Or.inl (mem_largePoints.mpr hlarge))
          exact hnoPointBetween hzSet hpz hzq
        exact hdouble.oscillation_le_of_jumpBound hepsilon hqtop hspan hjump
          x y hpx hxy hyq
    rcases le_total s t with hst | hts
    · exact hordered s t hps hst htq
    · simpa [dist_comm] using hordered t s hpt hts hsq
  exact ⟨partition, by simpa [gap] using hmesh, hosc⟩

end Skorokhod

end
