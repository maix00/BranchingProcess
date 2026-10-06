/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.Oscillation.DoubleExcursion
import Topology.Cadlag.Skorokhod.Oscillation.Partition.Existence

/-!
# Jump estimates for the double-excursion condition

Endpoint oscillation controls locate large jumps away from the endpoints.
The double-excursion condition separates such jumps and bounds path
oscillation on intervals containing no large jumps.
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

/-- Endpoint oscillation control forces every jump larger than `2 * epsilon`
away from both endpoints. -/
theorem HasEndpointOscillationBound.largeJump_awayFromEndpoints
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

/-- Two distinct interior jumps larger than `2 * epsilon` must be at least
`delta` apart under the double-excursion bound. -/
theorem HasDoubleExcursionBound.largeJumpsSeparated
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

/-- On an interval shorter than `delta`, a path with no jumps exceeding
`2 * epsilon` has oscillation at most `5 * epsilon` under the
double-excursion bound. -/
theorem HasDoubleExcursionBound.oscillation_le_of_jumpBound
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

end Skorokhod

end
