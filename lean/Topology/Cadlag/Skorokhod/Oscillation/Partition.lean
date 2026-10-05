/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.Topology

/-!
# Oscillation partitions for the Skorokhod topology

A finite partition records the cells used to bound within-cell path
oscillation. Pulling a partition back by a Skorokhod time change changes each
cell length by at most twice the time-change distortion and preserves its
cellwise oscillation up to the spatial error.
-/

@[expose] public section

open Set
open scoped ENNReal Topology

namespace Skorokhod

/-- A partition of the unit time interval into finitely many half-open cells,
with the final cell containing the terminal point. The `index` field assigns
each time to its unique cell. -/
structure OscillationPartition where
  size : ℕ
  size_pos : 0 < size
  points : Fin (size + 1) → unitInterval
  first : points ⟨0, by omega⟩ = ⊥
  last : points ⟨size, by omega⟩ = ⊤
  strictMono_points : StrictMono points
  index : unitInterval → Fin size
  index_lower : ∀ t, points (Fin.castSucc (index t)) ≤ t
  index_upper : ∀ t, t < points (index t).succ ∨ (index t).val + 1 = size
  mesh : ℝ
  mesh_pos : 0 < mesh
  gap_lower : ∀ i : Fin size,
    mesh ≤ dist (points i.castSucc) (points i.succ)

/-- The path oscillates by at most `bound` on each cell of a given finite
partition. -/
def OscillationBoundedOnPartition {E : Type*} [MetricSpace E]
    (partition : OscillationPartition) (path : CadlagPath unitInterval E)
    (bound : ℝ) : Prop :=
  ∀ s t, partition.index s = partition.index t →
    dist (path s) (path t) ≤ bound

private theorem symm_le_iff_apply_le (change : TimeChange) (a b : unitInterval) :
    change.symm a ≤ b ↔ a ≤ change b := by
  constructor
  · intro h
    calc
      a = change (change.symm a) := (change.apply_symm_apply a).symm
      _ ≤ change b := change.strictMono_toHomeomorph.monotone h
  · intro h
    calc
      change.symm a ≤ change.symm (change b) :=
        change.symm.strictMono_toHomeomorph.monotone h
      _ = b := change.symm_apply_apply b

private theorem lt_symm_iff_apply_lt (change : TimeChange) (a b : unitInterval) :
    a < change.symm b ↔ change a < b := by
  constructor
  · intro h
    calc
      change a < change (change.symm b) := change.strictMono_toHomeomorph h
      _ = b := change.apply_symm_apply b
  · intro h
    calc
      a = change.symm (change a) := (change.symm_apply_apply a).symm
      _ < change.symm b := change.symm.strictMono_toHomeomorph h

private theorem dist_symm_apply_le (change : TimeChange) {error : ℝ}
    (herror : ∀ t, dist (change t) t ≤ error) (t : unitInterval) :
    dist (change.symm t) t ≤ error := by
  calc
    dist (change.symm t) t = dist (change.symm t) (change (change.symm t)) := by
      rw [change.apply_symm_apply]
    _ = dist (change (change.symm t)) (change.symm t) := dist_comm _ _
    _ ≤ error := herror (change.symm t)

/-- Pull an oscillation partition back along a time change whose uniform
distortion is at most `error`. The new mesh loses at most `2 * error`. -/
def OscillationPartition.pullback (partition : OscillationPartition)
    (change : TimeChange) (error : ℝ)
    (hmesh : 2 * error < partition.mesh)
    (herror : ∀ t, dist (change t) t ≤ error) : OscillationPartition where
  size := partition.size
  size_pos := partition.size_pos
  points := fun i => change.symm (partition.points i)
  first := by
    change change.symm (partition.points ⟨0, by omega⟩) = ⊥
    rw [partition.first]
    exact TimeChange.apply_bot _
  last := by
    change change.symm (partition.points ⟨partition.size, by omega⟩) = ⊤
    rw [partition.last]
    exact TimeChange.apply_top _
  strictMono_points := change.symm.strictMono_toHomeomorph.comp
    partition.strictMono_points
  index := fun t => partition.index (change t)
  index_lower := by
    intro t
    apply (symm_le_iff_apply_le change _ _).2
    exact partition.index_lower (change t)
  index_upper := by
    intro t
    rcases partition.index_upper (change t) with h | h
    · exact Or.inl ((lt_symm_iff_apply_lt change _ _).2 h)
    · exact Or.inr h
  mesh := partition.mesh - 2 * error
  mesh_pos := by linarith
  gap_lower := by
    intro i
    have hgap := partition.gap_lower i
    have hleft := dist_symm_apply_le change herror (partition.points i.castSucc)
    have hright := dist_symm_apply_le change herror (partition.points i.succ)
    have htriangle :
        dist (partition.points i.castSucc) (partition.points i.succ) ≤
          dist (partition.points i.castSucc)
              (change.symm (partition.points i.castSucc)) +
            dist (change.symm (partition.points i.castSucc))
              (change.symm (partition.points i.succ)) +
            dist (change.symm (partition.points i.succ))
              (partition.points i.succ) := by
      have hmiddle := dist_triangle
        (change.symm (partition.points i.castSucc))
        (change.symm (partition.points i.succ))
        (partition.points i.succ)
      calc
        dist (partition.points i.castSucc) (partition.points i.succ) ≤
            dist (partition.points i.castSucc)
              (change.symm (partition.points i.castSucc)) +
            dist (change.symm (partition.points i.castSucc))
              (partition.points i.succ) := dist_triangle _ _ _
        _ ≤ dist (partition.points i.castSucc)
              (change.symm (partition.points i.castSucc)) +
            (dist (change.symm (partition.points i.castSucc))
                (change.symm (partition.points i.succ)) +
              dist (change.symm (partition.points i.succ))
                (partition.points i.succ)) := by
          exact add_le_add_right hmiddle _
        _ = dist (partition.points i.castSucc)
              (change.symm (partition.points i.castSucc)) +
            dist (change.symm (partition.points i.castSucc))
              (change.symm (partition.points i.succ)) +
            dist (change.symm (partition.points i.succ))
              (partition.points i.succ) := by ring
    have hleft' :
        dist (partition.points i.castSucc)
            (change.symm (partition.points i.castSucc)) ≤ error := by
      simpa [dist_comm] using hleft
    have hright' :
        dist (change.symm (partition.points i.succ))
            (partition.points i.succ) ≤ error := by
      exact hright
    change partition.mesh - 2 * error ≤
      dist (change.symm (partition.points i.castSucc))
        (change.symm (partition.points i.succ))
    linarith

/-- Cellwise oscillation survives a Skorokhod time change, with twice the
uniform spatial error added to the oscillation bound. -/
theorem OscillationBoundedOnPartition.pullback
    {E : Type*} [MetricSpace E]
    (partition : OscillationPartition) (change : TimeChange) (error spatial : ℝ)
    (hmesh : 2 * error < partition.mesh)
    (herror : ∀ t, dist (change t) t ≤ error)
    (path other : CadlagPath unitInterval E)
    (hspatial : ∀ t, dist (change.act path t) (other t) ≤ spatial)
    {bound : ℝ}
    (hosc : OscillationBoundedOnPartition partition path bound) :
    OscillationBoundedOnPartition
      (partition.pullback change error hmesh herror) other
      (bound + 2 * spatial) := by
  intro s t hindex
  have hindex' : partition.index (change s) = partition.index (change t) := hindex
  have hpath := hosc (change s) (change t) hindex'
  have hs := hspatial s
  have ht := hspatial t
  have hdist :
      dist (other s) (other t) ≤
        dist (other s) (change.act path s) +
          dist (change.act path s) (change.act path t) +
          dist (change.act path t) (other t) := by
    have hmiddle := dist_triangle (other s) (change.act path s)
      (change.act path t)
    calc
      dist (other s) (other t) ≤ dist (other s) (change.act path t) +
          dist (change.act path t) (other t) := dist_triangle _ _ _
      _ ≤ dist (other s) (change.act path s) +
          dist (change.act path s) (change.act path t) +
          dist (change.act path t) (other t) := by
        exact add_le_add_left hmiddle _
  have hs' : dist (other s) (change.act path s) ≤ spatial := by
    simpa [dist_comm] using hs
  have hact : dist (change.act path s) (change.act path t) ≤ bound := by
    simpa [TimeChange.act_apply] using hpath
  have htotal : dist (other s) (other t) ≤ spatial + bound + spatial := by
    calc
      _ ≤ dist (other s) (change.act path s) +
          dist (change.act path s) (change.act path t) +
          dist (change.act path t) (other t) := hdist
      _ ≤ spatial + bound + spatial := by
        linarith [hs', hact, ht]
  linarith

/-- Paths admitting a finite partition with a strict lower bound on cell
length and a strict upper bound on within-cell oscillation. -/
def admitsOscillationPartition (minimumGap maximumOscillation : ℝ) :
    Set (CadlagPath unitInterval ℝ) :=
  {path | ∃ partition : OscillationPartition,
    minimumGap < partition.mesh ∧
      ∃ bound < maximumOscillation,
        OscillationBoundedOnPartition partition path bound}

/-- Admitting a partition with strict mesh and oscillation margins is an open
property for the Skorokhod `J₁` topology. -/
theorem isOpen_admitsOscillationPartition (minimumGap maximumOscillation : ℝ) :
    IsOpen (admitsOscillationPartition minimumGap maximumOscillation) := by
  rw [isOpen_iff_forall_mem_open]
  intro path hpath
  obtain ⟨partition, hgap, bound, hbound, hosc⟩ := hpath
  have hmeshPos := partition.mesh_pos
  let error := min (partition.mesh / 4)
    (min ((partition.mesh - minimumGap) / 4)
      ((maximumOscillation - bound) / 4))
  have hgapMargin : 0 < partition.mesh - minimumGap := sub_pos.mpr hgap
  have hboundMargin : 0 < maximumOscillation - bound := sub_pos.mpr hbound
  have herror : 0 < error := by
    dsimp [error]
    positivity
  refine ⟨Metric.ball path error, ?_, Metric.isOpen_ball,
    Metric.mem_ball_self herror⟩
  intro other hother
  have hj1 : j1EDist path other < ENNReal.ofReal error := by
    rw [← edist_cadlagPath_eq_j1EDist, edist_dist,
      ENNReal.ofReal_lt_ofReal_iff herror]
    simpa [dist_comm] using Metric.mem_ball.mp hother
  obtain ⟨change, hcost⟩ := exists_timeChange_j1Cost_lt hj1
  have hdistortion : change.distortion < error := by
    have hpart : ENNReal.ofReal change.distortion < ENNReal.ofReal error :=
      (le_max_left _ _).trans_lt hcost
    exact (ENNReal.ofReal_lt_ofReal_iff herror).1 hpart
  have huniform : uniformEDist (change.act path) other < ENNReal.ofReal error :=
    (le_max_right _ _).trans_lt hcost
  have htime (t : unitInterval) : dist (change t) t ≤ error :=
    (TimeChange.dist_apply_le_distortion change t).trans hdistortion.le
  have hspace (t : unitInterval) : dist (change.act path t) (other t) ≤ error := by
    have hpoint :=
      (edist_apply_le_uniformEDist (change.act path) other t).trans_lt huniform
    rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff herror] at hpoint
    exact hpoint.le
  have herrorMesh : error ≤ partition.mesh / 4 := min_le_left _ _
  have herrorGap : error ≤ (partition.mesh - minimumGap) / 4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have herrorOsc : error ≤ (maximumOscillation - bound) / 4 :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hmesh : 2 * error < partition.mesh := by
    nlinarith [partition.mesh_pos]
  let pulled := partition.pullback change error hmesh htime
  have hgap' : minimumGap < pulled.mesh := by
    dsimp [pulled, OscillationPartition.pullback]
    nlinarith
  have hbound' : bound + 2 * error < maximumOscillation := by
    nlinarith
  exact ⟨pulled, hgap', bound + 2 * error, hbound',
    OscillationBoundedOnPartition.pullback partition change error error hmesh
      htime path other hspace hosc⟩

theorem measurableSet_admitsOscillationPartition
    (minimumGap maximumOscillation : ℝ) :
    MeasurableSet (admitsOscillationPartition minimumGap maximumOscillation) :=
  (isOpen_admitsOscillationPartition minimumGap maximumOscillation).measurableSet

end Skorokhod

end
