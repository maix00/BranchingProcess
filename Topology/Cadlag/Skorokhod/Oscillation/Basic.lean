/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.Topology
public import Topology.Cadlag.Skorokhod.Corridor.Basic
public import Topology.Cadlag.Skorokhod.Path.Scaling
public import Topology.MetricSpace.Oscillation

/-!
# Oscillation tubes in Skorokhod path space

The oscillation of a path is invariant under time changes in the Skorokhod
`J₁` metric. A strict bound is represented with an explicit uniform margin,
which makes its openness visible in the definition.

## Public declarations

- `Metric.OscillationBounded f b` means `dist (f s) (f t) ≤ b` for every pair
  of times; `oscillationInOpenTube b` imposes this bound with a positive
  margin below `b`. Positive spatial scaling rescales the width, and the set
  is open and Borel.
- rangeOscillationLe b is the non-strict bound on the diameter of the path
  range; this set is closed and lies in every strictly wider oscillation tube.
- A path with range in a closed interval of length less than b belongs to
  oscillationInOpenTube b.

The weak oscillation bound is
\(\forall s,t,\ d(f(s),f(t))\le b\); the open tube is
\(\{f:\exists\delta>0,\ \forall s,t,\ d(f(s),f(t))\le b-\delta\}\).
For real paths, positive scaling by \(c\) pulls width \(b\) back to
\(b/c\) when \(c>0\).
-/

open scoped ENNReal

@[expose] public section

namespace Skorokhod

/-- The strict oscillation tube of width `width`, represented by a positive
uniform margin below that width. -/
def oscillationInOpenTube (width : ℝ) : Set (CadlagPath unitInterval ℝ) :=
  {path | ∃ margin > 0, Metric.OscillationBounded path (width - margin)}

/-- Positive spatial scaling pulls an oscillation tube back to the tube with
width divided by the scale. -/
theorem mem_oscillationInOpenTube_scalePath_iff
    {width scale : ℝ} (hscale : 0 < scale)
    (path : CadlagPath unitInterval ℝ) :
    scalePath scale path ∈ oscillationInOpenTube width ↔
      path ∈ oscillationInOpenTube (width / scale) := by
  rw [oscillationInOpenTube, oscillationInOpenTube]
  constructor
  · rintro ⟨margin, hmargin, hosc⟩
    refine ⟨margin / scale, div_pos hmargin hscale, ?_⟩
    intro s t
    have hdist := hosc s t
    have h : |scale * path s - scale * path t| ≤ width - margin := by
      simpa [Real.dist_eq] using hdist
    have habs : |scale * path s - scale * path t| =
        scale * |path s - path t| := by
      rw [show scale * path s - scale * path t =
        scale * (path s - path t) by ring, abs_mul, abs_of_pos hscale]
    rw [habs] at h
    have hscaled : |path s - path t| ≤ (width - margin) / scale :=
      (le_div_iff₀ hscale).2 (by nlinarith [h])
    have hscaled' : dist (path s) (path t) ≤ (width - margin) / scale := by
      simpa [Real.dist_eq] using hscaled
    simpa [sub_div] using hscaled'
  · rintro ⟨margin, hmargin, hosc⟩
    refine ⟨scale * margin, mul_pos hscale hmargin, ?_⟩
    intro s t
    have h : dist (path s) (path t) ≤ width / scale - margin := hosc s t
    have hscaleDist : dist (scale * path s) (scale * path t) =
        scale * dist (path s) (path t) := by
      simp [Real.dist_eq, abs_mul, abs_of_pos hscale,
        show scale * path s - scale * path t = scale * (path s - path t) by ring]
    calc
      dist (scale * path s) (scale * path t) =
          scale * dist (path s) (path t) := hscaleDist
      _ ≤ scale * (width / scale - margin) :=
          mul_le_mul_of_nonneg_left h hscale.le
      _ = width - scale * margin := by field_simp [ne_of_gt hscale]

theorem isOpen_oscillationInOpenTube (width : ℝ) :
    IsOpen (oscillationInOpenTube width) := by
  rw [isOpen_iff_forall_mem_open]
  intro path hpath
  obtain ⟨margin, hmargin, hosc⟩ := hpath
  let radius := margin / 4
  have hradius : 0 < radius := by dsimp [radius]; positivity
  refine ⟨Metric.ball path radius, ?_, Metric.isOpen_ball,
    Metric.mem_ball_self hradius⟩
  intro other hother
  have hj1 : j1EDist path other < ENNReal.ofReal radius := by
    rw [← edist_cadlagPath_eq_j1EDist, edist_dist,
      ENNReal.ofReal_lt_ofReal_iff hradius]
    simpa [dist_comm] using hother
  obtain ⟨change, hchange⟩ := exists_timeChange_j1Cost_lt hj1
  have huniform : uniformEDist (change.act path) other < ENNReal.ofReal radius :=
    (le_max_right _ _).trans_lt hchange
  refine ⟨margin / 2, half_pos hmargin, fun s t => ?_⟩
  have hs := (edist_apply_le_uniformEDist (change.act path) other s).trans_lt huniform
  have ht := (edist_apply_le_uniformEDist (change.act path) other t).trans_lt huniform
  rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff hradius,
    TimeChange.act_apply, Real.dist_eq, abs_lt] at hs
  rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff hradius,
    TimeChange.act_apply, Real.dist_eq, abs_lt] at ht
  have hpathDist := hosc (change s) (change t)
  have hpath : |path (change s) - path (change t)| ≤ width - margin := by
    simpa [Real.dist_eq] using hpathDist
  have htri := abs_sub_le (other s) (path (change s)) (path (change t))
  have htri' := abs_sub_le (other s) (path (change t)) (other t)
  have hs' : |other s - path (change s)| < margin / 4 := by
    rcases hs with ⟨hs₁, hs₂⟩
    dsimp [radius] at hs₁ hs₂
    rw [abs_lt]
    constructor <;> linarith
  have ht' : |path (change t) - other t| < margin / 4 := by
    rcases ht with ⟨ht₁, ht₂⟩
    dsimp [radius] at ht₁ ht₂
    rw [abs_lt]
    constructor <;> linarith
  have hsum : |other s - other t| ≤
      |other s - path (change s)| +
        |path (change s) - path (change t)| +
        |path (change t) - other t| := by
    calc
      _ ≤ |other s - path (change t)| +
            |path (change t) - other t| := htri'
      _ ≤ |other s - path (change s)| +
            |path (change s) - path (change t)| +
            |path (change t) - other t| := by linarith [htri]
  have hoscOther : |other s - other t| ≤ width - margin / 2 := by
    nlinarith [hsum, hs', hpath, ht']
  simpa [Real.dist_eq] using hoscOther

theorem measurableSet_oscillationInOpenTube (width : ℝ) :
    MeasurableSet (oscillationInOpenTube width) :=
  (isOpen_oscillationInOpenTube width).measurableSet

/-- Paths whose range has diameter at most `width`. -/
def rangeOscillationLe (width : ℝ) : Set (CadlagPath unitInterval ℝ) :=
  {path | Metric.OscillationBounded path width}

/-- The non-strict range-oscillation event is closed for the Skorokhod `J₁`
topology. -/
theorem isClosed_rangeOscillationLe (width : ℝ) :
    IsClosed (rangeOscillationLe width) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro path hpath
  change ¬ Metric.OscillationBounded path width at hpath
  change ¬ ∀ s t, dist (path s) (path t) ≤ width at hpath
  push Not at hpath
  obtain ⟨s, t, hbad⟩ := hpath
  have hbadAbs : width < |path s - path t| := by
    simpa [Real.dist_eq] using hbad
  let ε : ℝ := (|path s - path t| - width) / 3
  have hε : 0 < ε := by
    dsimp [ε]
    linarith [hbadAbs]
  refine ⟨Metric.ball path ε, ?_, Metric.isOpen_ball,
    Metric.mem_ball_self hε⟩
  intro other hother
  have hdist : dist path other < ε := by
    simpa [dist_comm] using Metric.mem_ball.mp hother
  have hj1 : j1EDist path other < ENNReal.ofReal ε := by
    rw [← edist_cadlagPath_eq_j1EDist, edist_dist]
    exact (ENNReal.ofReal_lt_ofReal_iff hε).2 hdist
  obtain ⟨change, hchange⟩ := exists_timeChange_j1Cost_lt hj1
  have huniform : uniformEDist (change.act path) other < ENNReal.ofReal ε :=
    (le_max_right _ _).trans_lt hchange
  let s' : unitInterval := change.symm s
  let t' : unitInterval := change.symm t
  have hcloseS : |path s - other s'| < ε := by
    have hpoint :=
      (edist_apply_le_uniformEDist (change.act path) other s').trans_lt huniform
    rw [edist_dist, TimeChange.act_apply, change.apply_symm_apply,
      ENNReal.ofReal_lt_ofReal_iff hε] at hpoint
    simpa [Real.dist_eq] using hpoint
  have hcloseT : |path t - other t'| < ε := by
    have hpoint :=
      (edist_apply_le_uniformEDist (change.act path) other t').trans_lt huniform
    rw [edist_dist, TimeChange.act_apply, change.apply_symm_apply,
      ENNReal.ofReal_lt_ofReal_iff hε] at hpoint
    simpa [Real.dist_eq] using hpoint
  have hnot : other ∉ rangeOscillationLe width := by
    intro hosc
    have hmiddle : |other s' - other t'| ≤ width := by
      simpa [Metric.OscillationBounded, Real.dist_eq] using hosc s' t'
    have htriangle :
        |path s - path t| ≤
          |path s - other s'| + |other s' - other t'| +
            |other t' - path t| := by
      calc
        |path s - path t| =
            |(path s - other s') +
              ((other s' - other t') + (other t' - path t))| := by
                congr 1; ring
        _ ≤ |path s - other s'| +
              |(other s' - other t') + (other t' - path t)| := abs_add_le _ _
        _ ≤ |path s - other s'| +
              (|other s' - other t'| + |other t' - path t|) :=
          add_le_add_right (abs_add_le (other s' - other t')
            (other t' - path t)) _
        _ = |path s - other s'| + |other s' - other t'| +
              |other t' - path t| := by ring
    have hcloseT' : |other t' - path t| < ε := by
      simpa [abs_sub_comm] using hcloseT
    have hle : |path s - path t| ≤ 2 * ε + width := by
      calc
        |path s - path t| ≤
            |path s - other s'| + |other s' - other t'| +
              |other t' - path t| := htriangle
        _ ≤ ε + width + ε := by
          gcongr
        _ = 2 * ε + width := by ring
    dsimp [ε] at hle
    linarith [hbadAbs]
  exact hnot

/-- A path confined to a closed interval has oscillation at most the
interval's width. Adding any positive margin turns this into membership in
the corresponding open oscillation tube. -/
theorem rangeInClosedInterval_subset_oscillationInOpenTube
    (lower upper margin : ℝ) (hmargin : 0 < margin) :
    rangeInClosedInterval lower upper ⊆
      oscillationInOpenTube (upper - lower + margin) := by
  intro path hpath
  refine ⟨margin, hmargin, ?_⟩
  intro s t
  have hs := hpath s
  have ht := hpath t
  have hosc : |path s - path t| ≤ upper - lower := by
    rw [abs_le]
    constructor <;> linarith
  have hosc' : dist (path s) (path t) ≤ upper - lower := by
    simpa [Real.dist_eq] using hosc
  change dist (path s) (path t) ≤ upper - lower + margin - margin
  linarith

/-- A closed range-oscillation bound is contained in every strictly wider
open oscillation tube. -/
theorem rangeOscillationLe_subset_oscillationInOpenTube
    (width margin : ℝ) (hmargin : 0 < margin) :
    rangeOscillationLe width ⊆ oscillationInOpenTube (width + margin) := by
  intro path hpath
  refine ⟨margin, hmargin, ?_⟩
  intro s t
  have h : dist (path s) (path t) ≤ width := hpath s t
  change dist (path s) (path t) ≤ width + margin - margin
  linarith

end Skorokhod
