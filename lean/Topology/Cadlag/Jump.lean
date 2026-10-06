/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Oscillation
public import Mathlib.Topology.Order.LeftRightLim
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Compactness.Compact

/-!
# Large jumps of càdlàg functions

A càdlàg function on a compact linearly ordered pseudometric space with its
order topology and a bottom element has only finitely many noninitial jumps
larger than any fixed positive threshold. The proof uses local one-sided
oscillation bounds and a finite subcover.
-/

@[expose] public section

open Filter Set
open scoped Topology

private noncomputable def selectedLeftOscillationRadius
    {T E : Type*} [LinearOrder T] [PseudoMetricSpace T] [PseudoMetricSpace E]
    {f : T → E}
    (hf : IsCadlag f) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (t : T) : ℝ :=
  Classical.choose (hf.exists_left_oscillation_radius t hepsilon)

private theorem selectedLeftOscillationRadius_pos
    {T E : Type*} [LinearOrder T] [PseudoMetricSpace T] [PseudoMetricSpace E]
    {f : T → E}
    (hf : IsCadlag f) {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (t : T) : 0 < selectedLeftOscillationRadius hf epsilon hepsilon t :=
  (Classical.choose_spec (hf.exists_left_oscillation_radius t hepsilon)).1

private theorem selectedLeftOscillationRadius_spec
    {T E : Type*} [LinearOrder T] [PseudoMetricSpace T] [PseudoMetricSpace E]
    {f : T → E}
    (hf : IsCadlag f) {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (t s u : T) (hst : s < t) (hut : u < t)
    (hds : dist s t < selectedLeftOscillationRadius hf epsilon hepsilon t)
    (hdu : dist u t < selectedLeftOscillationRadius hf epsilon hepsilon t) :
    dist (f s) (f u) ≤ epsilon :=
  (Classical.choose_spec
    (hf.exists_left_oscillation_radius t hepsilon)).2 s u hst hut hds hdu

private noncomputable def selectedRightOscillationRadius
    {T E : Type*} [LinearOrder T] [PseudoMetricSpace T] [PseudoMetricSpace E]
    {f : T → E}
    (hf : IsCadlag f) (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (t : T) : ℝ :=
  Classical.choose (hf.exists_right_oscillation_radius t hepsilon)

private theorem selectedRightOscillationRadius_pos
    {T E : Type*} [LinearOrder T] [PseudoMetricSpace T] [PseudoMetricSpace E]
    {f : T → E}
    (hf : IsCadlag f) {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (t : T) : 0 < selectedRightOscillationRadius hf epsilon hepsilon t :=
  (Classical.choose_spec (hf.exists_right_oscillation_radius t hepsilon)).1

private theorem selectedRightOscillationRadius_spec
    {T E : Type*} [LinearOrder T] [PseudoMetricSpace T] [PseudoMetricSpace E]
    {f : T → E}
    (hf : IsCadlag f) {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (t s u : T) (hts : t ≤ s) (htu : t ≤ u)
    (hds : dist s t < selectedRightOscillationRadius hf epsilon hepsilon t)
    (hdu : dist u t < selectedRightOscillationRadius hf epsilon hepsilon t) :
    dist (f s) (f u) ≤ epsilon :=
  (Classical.choose_spec
    (hf.exists_right_oscillation_radius t hepsilon)).2 s u hts htu hds hdu

private theorem Ico_mem_nhdsLT_of_lt_general
    {T : Type*} [LinearOrder T] [TopologicalSpace T] [OrderTopology T]
    {a b : T} (hab : a < b) : Ico a b ∈ 𝓝[<] b := by
  rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
  refine ⟨Ioi a, isOpen_Ioi.mem_nhds hab, ?_⟩
  intro x hx
  exact ⟨hx.1.le, hx.2⟩

private theorem jump_le_of_left_local_oscillation
    {T E : Type*} [LinearOrder T] [PseudoMetricSpace T]
    [OrderTopology T] [PseudoMetricSpace E] {f : T → E}
    (hf : IsCadlag f) {epsilon radius : ℝ} (hepsilon : 0 < epsilon)
    {c t : T}
    (hosc : ∀ x y : T, x < c → y < c →
      dist x c < radius → dist y c < radius → dist (f x) (f y) ≤ epsilon)
    (htc : t < c) (htdist : dist t c < radius) :
  dist (Function.leftLim f t) (f t) ≤ epsilon := by
  rcases eq_or_neBot (𝓝[<] t) with hbot | hnebot
  · rw [leftLim_eq_of_eq_bot f hbot]
    simpa using le_of_lt hepsilon
  · have hnebot' : (𝓝[<] t).NeBot := hnebot
    let margin := radius - dist t c
    have hmargin : 0 < margin := sub_pos.mpr htdist
    have hballEvent : ∀ᶠ x in 𝓝[<] t, dist x t < margin := by
      filter_upwards
        [Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (Metric.ball_mem_nhds t hmargin)]
        with x hx
      exact Metric.mem_ball.mp hx
    have hev : ∀ᶠ x in 𝓝[<] t, f x ∈ Metric.closedBall (f t) epsilon := by
      filter_upwards [hballEvent, self_mem_nhdsWithin] with x hball hleft
      have hxt : x < t := hleft
      have hxc : x < c := hxt.trans htc
      have hball' : dist x t < margin := by
        simpa [Metric.mem_ball, dist_comm] using hball
      have hdistxc : dist x c < radius := by
        have htri := dist_triangle x t c
        dsimp [margin] at hball'
        linarith
      have hosc' := hosc x t hxc htc hdistxc htdist
      exact Metric.mem_closedBall.mpr (by simpa [dist_comm] using hosc')
    have hlim : Tendsto f (𝓝[<] t) (𝓝 (Function.leftLim f t)) :=
      tendsto_leftLim_of_tendsto (hf.tendsto_nhdsLT t)
    have hmem : Function.leftLim f t ∈ Metric.closedBall (f t) epsilon :=
      Metric.isClosed_closedBall.mem_of_tendsto hlim hev
    simpa [Metric.mem_closedBall, dist_comm] using hmem

private theorem jump_le_of_right_local_oscillation
    {T E : Type*} [LinearOrder T] [PseudoMetricSpace T]
    [OrderTopology T] [PseudoMetricSpace E] {f : T → E}
    (hf : IsCadlag f) {epsilon radius : ℝ} (hepsilon : 0 < epsilon)
    {c t : T}
    (hosc : ∀ x y : T, c ≤ x → c ≤ y →
      dist x c < radius → dist y c < radius → dist (f x) (f y) ≤ epsilon)
    (hct : c < t) (htdist : dist t c < radius) :
  dist (Function.leftLim f t) (f t) ≤ epsilon := by
  rcases eq_or_neBot (𝓝[<] t) with hbot | hnebot
  · rw [leftLim_eq_of_eq_bot f hbot]
    simpa using le_of_lt hepsilon
  · have hnebot' : (𝓝[<] t).NeBot := hnebot
    let margin := radius - dist t c
    have hmargin : 0 < margin := sub_pos.mpr htdist
    have hballEvent : ∀ᶠ x in 𝓝[<] t, dist x t < margin := by
      filter_upwards
        [Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (Metric.ball_mem_nhds t hmargin)]
        with x hx
      exact Metric.mem_ball.mp hx
    have hev : ∀ᶠ x in 𝓝[<] t, f x ∈ Metric.closedBall (f t) epsilon := by
      filter_upwards [hballEvent, Ico_mem_nhdsLT_of_lt_general hct]
        with x hball hleft
      have hxt : x < t := hleft.2
      have hcx : c ≤ x := hleft.1
      have hball' : dist x t < margin := by
        simpa [Metric.mem_ball, dist_comm] using hball
      have hdistxc : dist x c < radius := by
        have htri := dist_triangle x t c
        dsimp [margin] at hball'
        linarith
      have hosc' := hosc x t hcx hct.le hdistxc htdist
      exact Metric.mem_closedBall.mpr (by simpa [dist_comm] using hosc')
    have hlim : Tendsto f (𝓝[<] t) (𝓝 (Function.leftLim f t)) :=
      tendsto_leftLim_of_tendsto (hf.tendsto_nhdsLT t)
    have hmem : Function.leftLim f t ∈ Metric.closedBall (f t) epsilon :=
      Metric.isClosed_closedBall.mem_of_tendsto hlim hev
    simpa [Metric.mem_closedBall, dist_comm] using hmem

/-- For a càdlàg function on a compact linearly ordered pseudometric space
with its order topology and an order bottom, only finitely many noninitial
times have a jump larger than a fixed positive threshold. This holds for
pseudometric state spaces as well as metric spaces. -/
theorem IsCadlag.finite_jumpTimesAbove
    {T E : Type*} [LinearOrder T] [PseudoMetricSpace T] [OrderBot T]
    [OrderTopology T] [CompactSpace T] [PseudoMetricSpace E] {f : T → E}
    (hf : IsCadlag f) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    {t : T | t ≠ ⊥ ∧
      dist (Function.leftLim f t) (f t) > epsilon}.Finite := by
  classical
  let radius : T → ℝ := fun c =>
    min (selectedLeftOscillationRadius hf epsilon hepsilon c)
      (selectedRightOscillationRadius hf epsilon hepsilon c)
  have hradius (c : T) : 0 < radius c := by
    dsimp [radius]
    exact lt_min (selectedLeftOscillationRadius_pos hf hepsilon c)
      (selectedRightOscillationRadius_pos hf hepsilon c)
  let neighborhood : T → Set T := fun c =>
    Metric.ball c (radius c)
  have hdistLeft (c t : T) (h : dist t c < radius c) :
      dist t c < selectedLeftOscillationRadius hf epsilon hepsilon c := by
    have h' : dist t c < min
        (selectedLeftOscillationRadius hf epsilon hepsilon c)
        (selectedRightOscillationRadius hf epsilon hepsilon c) := by
      simpa [radius] using h
    exact h'.trans_le (min_le_left _ _)
  have hdistRight (c t : T) (h : dist t c < radius c) :
      dist t c < selectedRightOscillationRadius hf epsilon hepsilon c := by
    have h' : dist t c < min
        (selectedLeftOscillationRadius hf epsilon hepsilon c)
        (selectedRightOscillationRadius hf epsilon hepsilon c) := by
      simpa [radius] using h
    exact h'.trans_le (min_le_right _ _)
  have hneighborhoodOpen (c : T) : IsOpen (neighborhood c) :=
    Metric.isOpen_ball
  have hneighborhoodCover : (Set.univ : Set T) ⊆
      ⋃ c, neighborhood c := by
    intro c _
    exact Set.mem_iUnion.mpr ⟨c, Metric.mem_ball_self (hradius c)⟩
  obtain ⟨centers, hcenters⟩ :=
    isCompact_univ.elim_finite_subcover neighborhood hneighborhoodOpen
      hneighborhoodCover
  let finiteNeighborhood : centers → Set T := fun c => neighborhood c.1
  have hfiniteCover : (Set.univ : Set T) ⊆
      ⋃ c : centers, finiteNeighborhood c := by
    intro x _
    obtain ⟨c, hc, hx⟩ := Set.mem_iUnion₂.mp (hcenters (Set.mem_univ x))
    exact Set.mem_iUnion.mpr ⟨⟨c, hc⟩, hx⟩
  have hlocal (c t : T) (ht : t ∈ neighborhood c)
      (htc : t ≠ c) : dist (Function.leftLim f t) (f t) ≤ epsilon := by
    have hdist : dist t c < radius c := Metric.mem_ball.mp ht
    by_cases htc' : t < c
    · exact jump_le_of_left_local_oscillation hf hepsilon
        (fun x y hx hy hdx hdy =>
          selectedLeftOscillationRadius_spec hf hepsilon c x y hx hy
            hdx hdy)
        htc' (hdistLeft c t hdist)
    · have hct : c < t := lt_of_le_of_ne (le_of_not_gt htc') (Ne.symm htc)
      exact jump_le_of_right_local_oscillation hf hepsilon
        (fun x y hcx hcy hdx hdy =>
          selectedRightOscillationRadius_spec hf hepsilon c x y hcx hcy
            hdx hdy)
        hct (hdistRight c t hdist)
  have hsubset :
      {t : T | t ≠ ⊥ ∧
        dist (Function.leftLim f t) (f t) > epsilon} ⊆ (centers : Set T) := by
    intro t ht
    obtain ⟨c, hc, htc⟩ := Set.mem_iUnion₂.mp (hcenters (Set.mem_univ t))
    have htcne : t = c := by
      by_contra hne
      have hsmall := hlocal c t htc hne
      exact (not_lt_of_ge hsmall) ht.2
    simpa [htcne] using hc
  exact centers.finite_toSet.subset hsubset

end
