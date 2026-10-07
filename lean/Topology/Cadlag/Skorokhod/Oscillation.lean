/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.Topology
public import Topology.Cadlag.Skorokhod.Corridor

/-!
# Oscillation tubes in Skorokhod path space

The oscillation of a path is invariant under time changes in the Skorokhod
`J₁` metric. A strict bound is represented with an explicit uniform margin,
which makes its openness visible in the definition.
-/

open scoped ENNReal

@[expose] public section

namespace Skorokhod

/-- A path has oscillation at most `bound` if every pair of its values differs
by at most `bound`. -/
def OscillationBounded (path : CadlagPath unitInterval ℝ) (bound : ℝ) : Prop :=
  ∀ s t, |path s - path t| ≤ bound

/-- The strict oscillation tube of width `width`, represented by a positive
uniform margin below that width. -/
def oscillationInOpenTube (width : ℝ) : Set (CadlagPath unitInterval ℝ) :=
  {path | ∃ margin > 0, OscillationBounded path (width - margin)}

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
  have hpath := hosc (change s) (change t)
  have htri := abs_sub_le (other s) (path (change s)) (path (change t))
  have htri' := abs_sub_le (other s) (path (change t)) (other t)
  change _ ≤ width - margin / 2
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
  nlinarith [hsum, hs', hpath, ht']

theorem measurableSet_oscillationInOpenTube (width : ℝ) :
    MeasurableSet (oscillationInOpenTube width) :=
  (isOpen_oscillationInOpenTube width).measurableSet

/-- Paths whose range has diameter at most `width`. -/
def rangeOscillationLe (width : ℝ) : Set (CadlagPath unitInterval ℝ) :=
  {path | OscillationBounded path width}

/-- The non-strict range-oscillation event is closed for the Skorokhod `J₁`
topology. -/
theorem isClosed_rangeOscillationLe (width : ℝ) :
    IsClosed (rangeOscillationLe width) := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro path hpath
  change ¬ ∀ s t, |path s - path t| ≤ width at hpath
  push Not at hpath
  obtain ⟨s, t, hbad⟩ := hpath
  let ε : ℝ := (|path s - path t| - width) / 3
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
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
    have hmiddle := hosc s' t'
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
    linarith
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
  change |path s - path t| ≤ upper - lower + margin - margin
  linarith

/-- A closed range-oscillation bound is contained in every strictly wider
open oscillation tube. -/
theorem rangeOscillationLe_subset_oscillationInOpenTube
    (width margin : ℝ) (hmargin : 0 < margin) :
    rangeOscillationLe width ⊆ oscillationInOpenTube (width + margin) := by
  intro path hpath
  refine ⟨margin, hmargin, ?_⟩
  intro s t
  linarith [hpath s t]

end Skorokhod
