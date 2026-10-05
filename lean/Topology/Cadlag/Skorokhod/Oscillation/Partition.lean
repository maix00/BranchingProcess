/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.TimeChange

/-!
# Oscillation partitions for the Skorokhod topology

A finite partition records the cells used to bound within-cell path
oscillation. Pulling a partition back by a Skorokhod time change changes each
cell length by at most twice the time-change distortion and preserves its
cellwise oscillation up to the spatial error.
-/

@[expose] public section

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

end Skorokhod

end
