/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.EDistance.Logarithmic

/-!
# Separation for the logarithmic Skorokhod distance

The clock bound transfers small logarithmic distance to small usual `J₁`
distance. Right continuity then identifies the paths, including at jump times
by comparing at a slightly later time.
-/

@[expose] public section

open Filter Set
open scoped ENNReal Topology

namespace Skorokhod

theorem exists_timeChange_billingsleyCost_lt {E : Type*} [EMetricSpace E]
    {f g : CadlagPath unitInterval E} {ε : ℝ≥0∞}
    (h : billingsleyEDist f g < ε) :
    ∃ change : TimeChange, billingsleyCost f g change < ε := by
  simpa only [billingsleyEDist, iInf_lt_iff] using h

/-- Choose a positive logarithmic cost threshold below a prescribed tolerance
whose `J₁` conversion modulus is also below that tolerance. -/
theorem exists_small_logarithmicJ1_bound {tolerance : ℝ}
    (htolerance : 0 < tolerance) :
    ∃ bound : ℝ, 0 < bound ∧ bound < tolerance ∧
      logarithmicJ1Modulus bound < tolerance := by
  have hnear :
      {x : ℝ | logarithmicJ1Modulus x ∈ Metric.ball (0 : ℝ) tolerance} ∈
        𝓝 (0 : ℝ) := by
    have hcont : ∀ᶠ x : ℝ in 𝓝 (0 : ℝ),
        logarithmicJ1Modulus x ∈ Metric.ball (0 : ℝ) tolerance := by
      simpa [logarithmicJ1Modulus_zero] using
        continuous_logarithmicJ1Modulus.continuousAt.eventually
          (Metric.ball_mem_nhds (logarithmicJ1Modulus 0) htolerance)
    filter_upwards [hcont] with x hx
    exact hx
  obtain ⟨radius, hradius, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let bound : ℝ := min (radius / 2) (tolerance / 2)
  have hbound : 0 < bound := by
    dsimp [bound]
    exact lt_min (by positivity) (by positivity)
  refine ⟨bound, hbound, ?_, ?_⟩
  · dsimp [bound]
    exact (min_le_right _ _).trans_lt (half_lt_self htolerance)
  · have hbound_radius : bound ∈ Metric.ball (0 : ℝ) radius := by
      rw [Metric.mem_ball, Real.dist_eq]
      simp only [sub_zero, abs_of_pos hbound]
      dsimp [bound]
      exact (min_le_left _ _).trans_lt (half_lt_self hradius)
    have hmod_ball := hball hbound_radius
    change logarithmicJ1Modulus bound ∈ Metric.ball (0 : ℝ) tolerance at hmod_ball
    rw [Metric.mem_ball, Real.dist_eq] at hmod_ball
    exact (le_abs_self _).trans_lt (by simpa [sub_zero] using hmod_ball)

theorem billingsleyEDist_eq_zero_imp {E : Type*} [MetricSpace E]
    {f g : CadlagPath unitInterval E} (hzero : billingsleyEDist f g = 0) :
    f = g := by
  apply CadlagPath.ext
  intro t
  apply eq_of_forall_dist_le
  intro ε hε
  by_cases ht : t = ⊤
  · obtain ⟨bound, hbound, hboundε, _⟩ := exists_small_logarithmicJ1_bound hε
    obtain ⟨change, hchange⟩ := exists_timeChange_billingsleyCost_lt
      (f := f) (g := g) (ε := ENNReal.ofReal bound) (by
        rw [hzero]
        exact ENNReal.ofReal_pos.2 hbound)
    have huniform : uniformEDist (change.act f) g < ENNReal.ofReal bound :=
      (le_max_right _ _).trans_lt (by simpa [billingsleyCost] using hchange)
    have hpoint :=
      (edist_apply_le_uniformEDist (change.act f) g ⊤).trans_lt huniform
    rw [TimeChange.act_apply, TimeChange.apply_top, edist_dist,
      ENNReal.ofReal_lt_ofReal_iff hbound] at hpoint
    simpa [ht] using hpoint.le.trans (le_of_lt hboundε)
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
    let tolerance : ℝ := min (ε / 3)
      (min ((s : ℝ) - (t : ℝ)) ((min uf ug : unitInterval) - s))
    have hstReal : (t : ℝ) < s := by exact_mod_cast hts
    have hsMinReal : (s : ℝ) < min uf ug := by exact_mod_cast hsMin
    have htolerance : 0 < tolerance := by
      dsimp [tolerance]
      exact lt_min hthird (lt_min (sub_pos.2 hstReal) (sub_pos.2 hsMinReal))
    obtain ⟨bound, hbound, hboundTolerance, hmodTolerance⟩ :=
      exists_small_logarithmicJ1_bound htolerance
    have hchangeExists : billingsleyEDist f g < ENNReal.ofReal bound := by
      rw [hzero]
      exact ENNReal.ofReal_pos.2 hbound
    obtain ⟨change, hchange⟩ := exists_timeChange_billingsleyCost_lt hchangeExists
    have hlog : change.logDistortion ≤ ENNReal.ofReal bound := by
      exact (le_max_left _ _).trans (by simpa [billingsleyCost] using hchange.le)
    have hclockBound : change.distortion ≤ Real.exp bound - Real.exp (-bound) :=
      TimeChange.distortion_le_exp_sub_exp_neg_of_logDistortion_le
        change hbound.le hlog
    have hclock : change.distortion < tolerance := by
      calc
        change.distortion ≤ Real.exp bound - Real.exp (-bound) := hclockBound
        _ ≤ logarithmicJ1Modulus bound := le_max_left _ _
        _ < tolerance := hmodTolerance
    have hclockDist : dist (change s) s < tolerance :=
      (change.dist_apply_le_distortion s).trans_lt hclock
    have hclockAbs : |((change s : unitInterval) : ℝ) - (s : ℝ)| < tolerance := by
      simpa [Subtype.dist_eq, Real.dist_eq] using hclockDist
    have htoleranceLeft : tolerance ≤ (s : ℝ) - (t : ℝ) :=
      (min_le_right _ _).trans (min_le_left _ _)
    have htoleranceRight : tolerance ≤ ((min uf ug : unitInterval) : ℝ) - (s : ℝ) :=
      (min_le_right _ _).trans (min_le_right _ _)
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
    have huniform : uniformEDist (change.act f) g < ENNReal.ofReal bound :=
      (le_max_right _ _).trans_lt (by simpa [billingsleyCost] using hchange)
    have hcrossENN :=
      (edist_apply_le_uniformEDist (change.act f) g s).trans_lt huniform
    have hcross : dist (f (change s)) (g s) < bound := by
      rw [TimeChange.act_apply, edist_dist,
        ENNReal.ofReal_lt_ofReal_iff hbound] at hcrossENN
      exact hcrossENN
    have hcrossThird : bound < ε / 3 :=
      hboundTolerance.trans_le (min_le_left _ _)
    calc
      dist (f t) (g t) ≤
          dist (f t) (f (change s)) +
            dist (f (change s)) (g s) + dist (g s) (g t) :=
        dist_triangle4 _ _ _ _
      _ ≤ ε := by
        rw [dist_comm (f t) (f (change s))]
        linarith

@[simp]
theorem billingsleyEDist_eq_zero {E : Type*} [MetricSpace E]
    {f g : CadlagPath unitInterval E} :
    billingsleyEDist f g = 0 ↔ f = g := by
  constructor
  · exact billingsleyEDist_eq_zero_imp
  · rintro rfl
    exact billingsleyEDist_self f

end Skorokhod
