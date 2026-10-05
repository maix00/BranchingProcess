/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.RegularVariation
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Compact-uniform ratios for monotone regularly varying functions

Pointwise ratio limits alone do not imply uniform convergence on compact
multiplier sets. This file proves the compact-uniform conclusion under the
additional, explicit assumption that the function is eventually monotone.
-/

open Filter Set
open scoped Topology

@[expose] public section

namespace Asymptotics.IsRegularlyVaryingAtTop

/-- For an eventually nondecreasing regularly varying function, the ratio
`f (c * x) / f x` converges uniformly in `c` on every compact interval of
positive multipliers. Eventual monotonicity is the regularity hypothesis that
upgrades the pointwise ratio limits to a uniform limit. -/
theorem tendstoUniformlyOn_ratio_of_eventuallyMonotone
    {f : ℝ → ℝ} {ρ a b : ℝ}
    (hreg : IsRegularlyVaryingAtTop f ρ)
    (hmono : IsEventuallyMonotoneAtTop f)
    (ha : 0 < a) (hab : a ≤ b) :
    TendstoUniformlyOn (fun x c => f (c * x) / f x)
      (fun c => c ^ ρ) atTop (Set.Icc a b) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let g : ℝ → ℝ := fun c => c ^ ρ
  have hg : ContinuousOn g (Set.Icc a b) := by
    change ContinuousOn (fun c : ℝ => c ^ ρ) (Set.Icc a b)
    exact continuousOn_id.rpow_const fun c hc =>
      Or.inl (ne_of_gt (lt_of_lt_of_le ha hc.1))
  have hcompact : IsCompact (Set.Icc a b) := isCompact_Icc
  have huc : UniformContinuousOn g (Set.Icc a b) :=
    hcompact.uniformContinuousOn_of_continuous hg
  obtain ⟨η, hη, hηclose⟩ :=
    Metric.uniformContinuousOn_iff.mp huc (ε / 4) (by positivity)
  obtain ⟨Rmono, hRmono⟩ := hmono
  let d : ℝ := min (η / 2) (a / 2)
  have hd : 0 < d := by dsimp [d]; positivity
  have hdη : d < η := by
    dsimp [d]
    have hmin : min (η / 2) (a / 2) ≤ η / 2 := min_le_left _ _
    linarith
  have hda : d < a := by
    dsimp [d]
    have hmin : min (η / 2) (a / 2) ≤ a / 2 := min_le_right _ _
    linarith
  let Center := {c : ℝ // c ∈ Set.Icc a b}
  let W : Center → Set ℝ := fun c => Set.Ioo (c.1 - d / 2) (c.1 + d / 2)
  let lower : Center → ℝ := fun c => max a (c.1 - d)
  let upper : Center → ℝ := fun c => min b (c.1 + d)
  have hopen : ∀ c : Center, IsOpen (W c) := fun _ => isOpen_Ioo
  have hcover : Set.Icc a b ⊆ ⋃ c : Center, W c := by
    intro y hy
    refine Set.mem_iUnion.mpr ⟨⟨y, hy⟩, ?_⟩
    change y - d / 2 < y ∧ y < y + d / 2
    constructor <;> linarith
  obtain ⟨F, hFcover⟩ := hcompact.elim_finite_subcover W hopen hcover
  have hlmem (c : Center) : lower c ∈ Set.Icc a b := by
    constructor
    · exact le_max_left _ _
    · apply max_le
      · exact hab
      · linarith [c.2.2, hd]
  have humem (c : Center) : upper c ∈ Set.Icc a b := by
    constructor
    · apply le_min
      · exact hab
      · linarith [c.2.1, hd]
    · exact min_le_left _ _
  have hlpos (c : Center) : 0 < lower c :=
    lt_of_lt_of_le ha (hlmem c).1
  have huPos (c : Center) : 0 < upper c :=
    lt_of_lt_of_le ha (humem c).1
  have hlCenter (c : Center) : |lower c - c.1| ≤ d := by
    unfold lower
    by_cases h : a ≤ c.1 - d
    · rw [max_eq_right h, abs_of_nonpos (by linarith)]
      linarith
    · rw [max_eq_left (le_of_not_ge h)]
      have hca : 0 ≤ c.1 - a := sub_nonneg.mpr c.2.1
      rw [abs_of_nonpos (by linarith)]
      linarith
  have huCenter (c : Center) : |upper c - c.1| ≤ d := by
    unfold upper
    by_cases h : c.1 + d ≤ b
    · rw [min_eq_right h, abs_of_nonneg (by linarith)]
      linarith
    · rw [min_eq_left (le_of_not_ge h)]
      have hbc : 0 ≤ b - c.1 := sub_nonneg.mpr c.2.2
      rw [abs_of_nonneg hbc]
      linarith
  have hlocal (c : Center) : ∀ᶠ x : ℝ in atTop,
      ∀ y ∈ Set.Icc a b, y ∈ W c →
        |f (y * x) / f x - g y| < ε := by
    have hfx : ∀ᶠ x : ℝ in atTop, 0 < f x := hreg.eventually_pos
    have hxpos : ∀ᶠ x : ℝ in atTop, 0 < x := eventually_gt_atTop 0
    have hbase : ∀ᶠ x : ℝ in atTop, Rmono ≤ lower c * x := by
      have h := (tendsto_id.const_mul_atTop (hlpos c)).eventually
        (eventually_ge_atTop Rmono)
      simpa [mul_comm] using h
    have hlratio : ∀ᶠ x : ℝ in atTop,
        |f (lower c * x) / f x - g (lower c)| < ε / 4 := by
      have ht := hreg.ratio_tendsto (hlpos c)
      have hevent := ht.eventually (Metric.ball_mem_nhds _ (by positivity : 0 < ε / 4))
      filter_upwards [hevent] with x hx
      simpa [Real.dist_eq, g, abs_sub_comm] using hx
    have huratio : ∀ᶠ x : ℝ in atTop,
        |f (upper c * x) / f x - g (upper c)| < ε / 4 := by
      have ht := hreg.ratio_tendsto (huPos c)
      have hevent := ht.eventually (Metric.ball_mem_nhds _ (by positivity : 0 < ε / 4))
      filter_upwards [hevent] with x hx
      simpa [Real.dist_eq, g, abs_sub_comm] using hx
    filter_upwards [hfx, hxpos, hbase, hlratio, huratio] with x hfx hxpos hbase hlratio huratio
    intro y hy hyW
    have hylo : lower c ≤ y := by
      apply max_le
      · exact hy.1
      · have hyW' : c.1 - d / 2 < y := hyW.1
        linarith [hd]
    have hyhi : y ≤ upper c := by
      apply le_min
      · exact hy.2
      · have hyW' : y < c.1 + d / 2 := hyW.2
        linarith [hd]
    have hleft : lower c * x ≤ y * x :=
      mul_le_mul_of_nonneg_right hylo hxpos.le
    have hright : y * x ≤ upper c * x :=
      mul_le_mul_of_nonneg_right hyhi hxpos.le
    have hmonoLeft : f (lower c * x) ≤ f (y * x) :=
      hRmono hbase hleft
    have hmonoRight : f (y * x) ≤ f (upper c * x) :=
      hRmono (le_trans hbase hleft) hright
    have hratioLeft : f (lower c * x) / f x ≤ f (y * x) / f x :=
      div_le_div_of_nonneg_right hmonoLeft hfx.le
    have hratioRight : f (y * x) / f x ≤ f (upper c * x) / f x :=
      div_le_div_of_nonneg_right hmonoRight hfx.le
    have hlowClose : |g (lower c) - g c.1| < ε / 4 := by
      have hdist : dist (lower c) c.1 < η := by
        rw [Real.dist_eq]
        exact lt_of_le_of_lt (hlCenter c) hdη
      have hc := hηclose (lower c) (hlmem c) c.1 c.2 hdist
      simpa [Real.dist_eq, g, abs_sub_comm] using hc
    have huClose : |g (upper c) - g c.1| < ε / 4 := by
      have hdist : dist (upper c) c.1 < η := by
        rw [Real.dist_eq]
        exact lt_of_le_of_lt (huCenter c) hdη
      have hc := hηclose (upper c) (humem c) c.1 c.2 hdist
      simpa [Real.dist_eq, g, abs_sub_comm] using hc
    have hyClose : |g y - g c.1| < ε / 4 := by
      have hdist : |y - c.1| < d := by
        rw [abs_lt]
        constructor <;> linarith [hyW.1, hyW.2]
      have hdist' : dist y c.1 < η := by
        rw [Real.dist_eq]
        exact lt_trans hdist hdη
      have hc := hηclose y hy c.1 c.2 hdist'
      simpa [Real.dist_eq, g, abs_sub_comm] using hc
    have hleftAbs := abs_lt.mp hlratio
    have hrightAbs := abs_lt.mp huratio
    have hlcAbs := abs_lt.mp hlowClose
    have hucAbs := abs_lt.mp huClose
    have hycAbs := abs_lt.mp hyClose
    rw [abs_lt]
    constructor
    · linarith
    · linarith
  have hfinite_aux : ∀ s : Finset Center, ∀ᶠ x : ℝ in atTop,
      ∀ c ∈ s, ∀ y ∈ Set.Icc a b,
        y ∈ W c → |f (y * x) / f x - g y| < ε := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact Filter.Eventually.of_forall (by simp)
    | @insert c s hnot ih =>
        filter_upwards [hlocal c, ih] with x hc hF
        intro c' hc' y hy hyW
        simp only [Finset.mem_insert] at hc'
        rcases hc' with rfl | hc'
        · exact hc y hy hyW
        · exact hF c' hc' y hy hyW
  have hfinite := hfinite_aux F
  filter_upwards [hfinite] with x hx y hy
  obtain ⟨c, hrest⟩ := Set.mem_iUnion.mp (hFcover hy)
  obtain ⟨hcF, hyW⟩ := Set.mem_iUnion.mp hrest
  simpa [Real.dist_eq, abs_sub_comm] using hx c hcF y hy hyW

end Asymptotics.IsRegularlyVaryingAtTop

end
