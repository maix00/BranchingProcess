/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.UnitInterval
public import Topology.Cadlag.Skorokhod.EDistance

/-!
# Separation for the Skorokhod `J₁` distance

The proof uses right continuity directly.  At a nonterminal time, compare at
a slightly later time and choose a time change whose clock distortion keeps
the changed time inside the same right neighbourhood.  At the terminal time,
every increasing self-homeomorphism of `[0, 1]` fixes the endpoint.
-/

@[expose] public section

open Filter Set
open scoped ENNReal Topology

namespace Skorokhod

theorem exists_timeChange_j1Cost_lt {E : Type*} [EMetricSpace E]
    {f g : CadlagPath unitInterval E} {ε : ℝ≥0∞}
    (h : j1EDist f g < ε) :
    ∃ change : TimeChange, j1Cost f g change < ε := by
  simpa only [j1EDist, iInf_lt_iff] using h

theorem j1EDist_eq_zero_imp {E : Type*} [MetricSpace E]
    {f g : CadlagPath unitInterval E} (hzero : j1EDist f g = 0) :
    f = g := by
  apply CadlagPath.ext
  intro t
  apply eq_of_forall_dist_le
  intro ε hε
  by_cases ht : t = ⊤
  · obtain ⟨change, hchange⟩ := exists_timeChange_j1Cost_lt
      (f := f) (g := g) (ε := ENNReal.ofReal ε) (by
        rw [hzero]
        exact ENNReal.ofReal_pos.2 hε)
    have huniform : uniformEDist (change.act f) g < ENNReal.ofReal ε :=
      (le_max_right _ _).trans_lt hchange
    have hpoint :=
      (edist_apply_le_uniformEDist (change.act f) g ⊤).trans_lt huniform
    rw [TimeChange.act_apply, TimeChange.apply_top, edist_dist,
      ENNReal.ofReal_lt_ofReal_iff hε] at hpoint
    simpa [ht] using hpoint.le
  · have htTop : t < ⊤ := lt_top_iff_ne_top.2 ht
    have hthird : 0 < ε / 3 := by positivity
    have hfmem : {s : unitInterval | dist (f s) (f t) < ε / 3} ∈
        nhdsWithin t (Set.Ioi t) :=
      (Metric.tendsto_nhds.mp (f.isCadlag_toFun.isRightContinuous t))
        (ε / 3) hthird
    have hgmem : {s : unitInterval | dist (g s) (g t) < ε / 3} ∈
        nhdsWithin t (Set.Ioi t) :=
      (Metric.tendsto_nhds.mp (g.isCadlag_toFun.isRightContinuous t))
        (ε / 3) hthird
    obtain ⟨uf, huf, hf⟩ :=
      (mem_nhdsGT_iff_exists_Ioo_subset' htTop).1 hfmem
    obtain ⟨ug, hug, hg⟩ :=
      (mem_nhdsGT_iff_exists_Ioo_subset' htTop).1 hgmem
    have htMin : t < min uf ug := lt_min huf hug
    obtain ⟨s, hts, hsMin⟩ := exists_between htMin
    let r : ℝ := min (ε / 3)
      (min ((s : ℝ) - (t : ℝ)) ((min uf ug : unitInterval) - s))
    have hstReal : (t : ℝ) < s := by exact_mod_cast hts
    have hsMinReal : (s : ℝ) < min uf ug := by exact_mod_cast hsMin
    have hr : 0 < r := by
      dsimp [r]
      exact lt_min hthird (lt_min (sub_pos.2 hstReal) (sub_pos.2 hsMinReal))
    obtain ⟨change, hchange⟩ := exists_timeChange_j1Cost_lt
      (f := f) (g := g) (ε := ENNReal.ofReal r) (by
        rw [hzero]
        exact ENNReal.ofReal_pos.2 hr)
    have hclockENN : ENNReal.ofReal change.distortion < ENNReal.ofReal r :=
      (le_max_left _ _).trans_lt hchange
    have hclock : change.distortion < r :=
      (ENNReal.ofReal_lt_ofReal_iff hr).1 hclockENN
    have hclockDist : dist (change s) s < r :=
      (change.dist_apply_le_distortion s).trans_lt hclock
    have hclockAbs : |((change s : unitInterval) : ℝ) - (s : ℝ)| < r := by
      simpa [Subtype.dist_eq, Real.dist_eq] using hclockDist
    have hrLeft : r ≤ (s : ℝ) - (t : ℝ) := by
      exact (min_le_right _ _).trans (min_le_left _ _)
    have hrRight : r ≤ ((min uf ug : unitInterval) : ℝ) - (s : ℝ) := by
      exact (min_le_right _ _).trans (min_le_right _ _)
    have htChange : t < change s := by
      apply Subtype.coe_lt_coe.mp
      have := (abs_lt.1 hclockAbs).1
      linarith
    have hChangeMin : change s < min uf ug := by
      apply Subtype.coe_lt_coe.mp
      have := (abs_lt.1 hclockAbs).2
      linarith
    have hfClose : dist (f (change s)) (f t) < ε / 3 :=
      hf ⟨htChange, hChangeMin.trans_le (min_le_left _ _)⟩
    have hgClose : dist (g s) (g t) < ε / 3 :=
      hg ⟨hts, hsMin.trans_le (min_le_right _ _)⟩
    have huniform : uniformEDist (change.act f) g < ENNReal.ofReal r :=
      (le_max_right _ _).trans_lt hchange
    have hcrossENN :=
      (edist_apply_le_uniformEDist (change.act f) g s).trans_lt huniform
    have hcross : dist (f (change s)) (g s) < r := by
      rw [TimeChange.act_apply, edist_dist,
        ENNReal.ofReal_lt_ofReal_iff hr] at hcrossENN
      exact hcrossENN
    have hrThird : r ≤ ε / 3 := min_le_left _ _
    calc
      dist (f t) (g t) ≤
          dist (f t) (f (change s)) +
            dist (f (change s)) (g s) + dist (g s) (g t) :=
        dist_triangle4 _ _ _ _
      _ ≤ ε := by
        rw [dist_comm (f t) (f (change s))]
        linarith

@[simp]
theorem j1EDist_eq_zero {E : Type*} [MetricSpace E]
    {f g : CadlagPath unitInterval E} :
    j1EDist f g = 0 ↔ f = g := by
  constructor
  · exact j1EDist_eq_zero_imp
  · rintro rfl
    exact j1EDist_self f

end Skorokhod
