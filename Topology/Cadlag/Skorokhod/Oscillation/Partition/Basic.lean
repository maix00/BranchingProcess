/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.Topology

/-!
# Basic oscillation partitions

Finite partitions record half-open time cells, their assignment map, and a lower bound on cell lengths. This module proves the cell-assignment laws and constructs càdlàg step approximations controlled by within-cell oscillation.
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
  index_start : ∀ i, index (points (Fin.castSucc i)) = i
  mesh : ℝ
  mesh_pos : 0 < mesh
  gap_lower : ∀ i : Fin size,
    mesh ≤ dist (points i.castSucc) (points i.succ)

/-- A time satisfying the endpoint inequalities of cell `i` is assigned to
that cell. -/
theorem OscillationPartition.index_eq_of_cell (partition : OscillationPartition)
    (i : Fin partition.size) (t : unitInterval)
    (hlower : partition.points i.castSucc ≤ t)
    (hupper : t < partition.points i.succ ∨ i.val + 1 = partition.size) :
    partition.index t = i := by
  apply Fin.ext
  by_contra hval
  have hne : partition.index t ≠ i := by
    intro h
    exact hval (congrArg Fin.val h)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hltVal : (partition.index t).val < i.val := hlt
    have hmono : partition.points (partition.index t).succ ≤
        partition.points i.castSucc := by
      apply partition.strictMono_points.monotone
      apply Fin.le_iff_val_le_val.mpr
      rw [Fin.val_succ, Fin.val_castSucc]
      exact Nat.succ_le_iff.mpr hltVal
    rcases partition.index_upper t with hindex | hlast
    · have hfalse : t < t := hindex.trans_le (hmono.trans hlower)
      exact (lt_irrefl t hfalse).elim
    · omega
  · have hgtVal : i.val < (partition.index t).val := hgt
    have hmono : partition.points i.succ ≤
        partition.points (partition.index t).castSucc := by
      apply partition.strictMono_points.monotone
      apply Fin.le_iff_val_le_val.mpr
      rw [Fin.val_succ, Fin.val_castSucc]
      exact Nat.succ_le_of_lt hgtVal
    have hindex := partition.index_lower t
    rcases hupper with hcell | hlast
    · have hfalse : t < t := hcell.trans_le (hmono.trans hindex)
      exact (lt_irrefl t hfalse).elim
    · omega

/-- The cell assignment is monotone in time. -/
theorem OscillationPartition.index_monotone (partition : OscillationPartition)
    {s t : unitInterval} (hst : s ≤ t) :
    partition.index s ≤ partition.index t := by
  by_contra hnot
  have hgt : partition.index t < partition.index s := lt_of_not_ge hnot
  have hmono : partition.points (partition.index t).succ ≤
      partition.points (partition.index s).castSucc := by
    apply partition.strictMono_points.monotone
    apply Fin.le_iff_val_le_val.mpr
    rw [Fin.val_succ, Fin.val_castSucc]
    exact Nat.succ_le_of_lt hgt
  have hsLower := partition.index_lower s
  rcases partition.index_upper t with hnext | hlast
  · have hfalse : t < t := hnext.trans_le (hmono.trans (hsLower.trans hst))
    exact (lt_irrefl t hfalse).elim
  · omega

/-- A function constant on each partition cell is càdlàg. -/
theorem OscillationPartition.isCadlag_stepFunction
    {E : Type*} [TopologicalSpace E] (partition : OscillationPartition)
    (value : Fin partition.size → E) :
    IsCadlag (fun t => value (partition.index t)) := by
  refine ⟨?_, ?_⟩
  · intro t
    change Filter.Tendsto (fun s => value (partition.index s))
      (nhdsWithin t (Ioi t)) (nhds (value (partition.index t)))
    classical
    by_cases ht : t = ⊤
    · have hfilter : nhdsWithin (⊤ : unitInterval) (Ioi ⊤) = ⊥ := by
        simp [nhdsWithin]
      rw [ht, hfilter]
      exact Filter.tendsto_bot
    · let i := partition.index t
      have hright : t < partition.points i.succ := by
        rcases partition.index_upper t with hnext | hlast
        · exact hnext
        · have hidx : i.succ = Fin.last partition.size := by
            apply Fin.ext
            rw [Fin.val_succ, Fin.val_last]
            exact hlast
          have hpoint : partition.points i.succ = ⊤ := by
            rw [hidx]
            simpa [Fin.last] using partition.last
          rw [hpoint]
          exact lt_top_iff_ne_top.mpr ht
      have hset : {s : unitInterval | partition.index s = i} ∈
          nhdsWithin t (Ioi t) := by
        rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
        refine ⟨Iio (partition.points i.succ), isOpen_Iio.mem_nhds hright, ?_⟩
        intro s hs
        rcases (Set.mem_inter_iff s _ _).mp hs with ⟨hsright, hts⟩
        have hlower : partition.points i.castSucc ≤ s :=
          (partition.index_lower t).trans hts.le
        exact partition.index_eq_of_cell i s hlower (Or.inl hsright)
      have hlocal : (fun s => value (partition.index s)) =ᶠ[nhdsWithin t (Ioi t)]
          fun _ => value i := by
        filter_upwards [hset] with s hs
        rw [hs]
      exact tendsto_const_nhds.congr' hlocal.symm
  · intro t
    change ∃ l, Filter.Tendsto (fun s => value (partition.index s))
      (nhdsWithin t (Iio t)) (nhds l)
    classical
    by_cases ht : t = ⊥
    · refine ⟨value (partition.index t), ?_⟩
      have hfilter : nhdsWithin (⊥ : unitInterval) (Iio ⊥) = ⊥ := by
        simp [nhdsWithin]
      rw [ht, hfilter]
      exact Filter.tendsto_bot
    · have hbot : ⊥ < t := bot_lt_iff_ne_bot.mpr ht
      let visited : Finset (Fin partition.size) :=
        Finset.univ.filter fun i => ∃ s < t, partition.index s = i
      obtain ⟨s₀, hs₀bot, hs₀t⟩ := exists_between hbot
      have hvisited : visited.Nonempty := by
        refine ⟨partition.index s₀, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
        exact ⟨s₀, hs₀t, rfl⟩
      let i := visited.max' hvisited
      have hi : i ∈ visited := visited.max'_mem hvisited
      have himax (j : Fin partition.size) (hj : j ∈ visited) : j ≤ i := by
        exact visited.le_max' j hj
      have hi' : ∃ s < t, partition.index s = i := by
        simpa [visited] using (Finset.mem_filter.mp hi).2
      obtain ⟨s₁, hs₁t, hs₁i⟩ := hi'
      have hset : {s : unitInterval | value (partition.index s) = value i} ∈
          nhdsWithin t (Iio t) := by
        rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
        refine ⟨Ioi s₁, isOpen_Ioi.mem_nhds hs₁t, ?_⟩
        intro s hs
        rcases (Set.mem_inter_iff s _ _).mp hs with ⟨hs₁, hst⟩
        have hs₁s : s₁ < s := hs₁
        have hst' : s < t := hst
        have hj : partition.index s ∈ visited := by
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨s, hst', rfl⟩⟩
        have hlow : i ≤ partition.index s := by
          rw [← hs₁i]
          exact partition.index_monotone hs₁s.le
        have hhigh := himax (partition.index s) hj
        have hindex : partition.index s = i := le_antisymm hhigh hlow
        change value (partition.index s) = value i
        rw [hindex]
      have hlocal : (fun s => value (partition.index s)) =ᶠ[nhdsWithin t (Iio t)]
          fun _ => value i := by
        filter_upwards [hset] with s hs
        exact hs
      exact ⟨value i, tendsto_const_nhds.congr' hlocal.symm⟩

/-- A step function attached to a finite partition, with a separate value at
the terminal time. The terminal coordinate is separate because a càdlàg path
may jump at that time. -/
noncomputable def OscillationPartition.stepPath {E : Type*} [TopologicalSpace E]
    (partition : OscillationPartition)
    (value : Fin (partition.size + 1) → E) : CadlagPath unitInterval E := by
  classical
  letI : DecidableEq (↥unitInterval) := inferInstance
  refine ⟨fun t => if t = ⊤ then value (Fin.last partition.size)
    else value (partition.index t).castSucc, ?_⟩
  exact (partition.isCadlag_stepFunction (fun i => value i.castSucc)).updateTop
    (value (Fin.last partition.size))

/-- A positive lower bound on partition cell lengths bounds the number of
cells, since their lengths telescope to the length of the unit interval. -/
theorem OscillationPartition.size_mul_mesh_le_one
    (partition : OscillationPartition) :
    (partition.size : ℝ) * partition.mesh ≤ 1 := by
  let point : ℕ → ℝ := fun i =>
    (partition.points ⟨min i partition.size,
      Nat.lt_succ_of_le (Nat.min_le_right i partition.size)⟩ : ℝ)
  have hpointZero : point 0 = 0 := by
    have hpoint : point 0 = (partition.points ⟨0, by omega⟩ : ℝ) := by
      dsimp [point]
      simp
    rw [hpoint]
    have hfirst := congrArg (fun t : unitInterval => (t : ℝ)) partition.first
    simpa using hfirst
  have hpointSize : point partition.size = 1 := by
    have hpoint :
        point partition.size = (partition.points ⟨partition.size, by omega⟩ : ℝ) := by
      dsimp [point]
      simp
    rw [hpoint]
    have hlast := congrArg (fun t : unitInterval => (t : ℝ)) partition.last
    simpa using hlast
  have hsum :
      (∑ i ∈ Finset.range partition.size, (point (i + 1) - point i)) = 1 := by
    calc
      _ = point partition.size - point 0 := Finset.sum_range_sub _ _
      _ = 1 := by rw [hpointSize, hpointZero]; norm_num
  have hgap (i : Fin partition.size) :
      partition.mesh ≤ point (i.val + 1) - point i.val := by
    have hmono : partition.points i.castSucc < partition.points i.succ :=
      partition.strictMono_points i.castSucc_lt_succ
    have hpointLeft : point i.val = (partition.points i.castSucc : ℝ) := by
      dsimp [point]
      apply congrArg (fun x : unitInterval => (x : ℝ))
      apply congrArg partition.points
      apply Fin.ext
      simp
    have hpointRight : point (i.val + 1) = (partition.points i.succ : ℝ) := by
      dsimp [point]
      apply congrArg (fun x : unitInterval => (x : ℝ))
      apply congrArg partition.points
      apply Fin.ext
      simp
    have hmono' : point i.val < point (i.val + 1) := by
      rw [hpointLeft, hpointRight]
      exact_mod_cast hmono
    have hdist :
        dist (partition.points i.castSucc) (partition.points i.succ) =
          point (i.val + 1) - point i.val := by
      rw [Subtype.dist_eq, Real.dist_eq, ← hpointLeft, ← hpointRight,
        abs_of_nonpos (sub_nonpos.mpr hmono'.le)]
      ring
    calc
      partition.mesh ≤ dist (partition.points i.castSucc) (partition.points i.succ) :=
        partition.gap_lower i
      _ = point (i.val + 1) - point i.val := hdist
  calc
    (partition.size : ℝ) * partition.mesh =
        ∑ _i ∈ Finset.range partition.size, partition.mesh := by simp
    _ ≤ ∑ i ∈ Finset.range partition.size, (point (i + 1) - point i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hgap ⟨i, Finset.mem_range.mp hi⟩
    _ = 1 := hsum

/-- The path oscillates by at most `bound` on each cell of a given finite
partition. -/
def OscillationBoundedOnPartition {E : Type*} [PseudoMetricSpace E]
    (partition : OscillationPartition) (path : CadlagPath unitInterval E)
    (bound : ℝ) : Prop :=
  ∀ s t, s ≠ ⊤ → t ≠ ⊤ → partition.index s = partition.index t →
    dist (path s) (path t) ≤ bound

/-- The step function obtained by sampling a path at the left endpoint of the
partition cell containing each time, with its actual value retained at the
terminal point. -/
noncomputable def OscillationPartition.stepApproximation
    {E : Type*} [TopologicalSpace E]
    (partition : OscillationPartition) (path : CadlagPath unitInterval E) :
    CadlagPath unitInterval E :=
  partition.stepPath
    (Fin.lastCases (path ⊤) (fun i => path (partition.points i.castSucc)))

/-- A path with small oscillation on each partition cell is uniformly close
to its left-endpoint step approximation. -/
theorem OscillationPartition.dist_stepApproximation_le
    {E : Type*} [PseudoMetricSpace E]
    (partition : OscillationPartition) (path : CadlagPath unitInterval E)
    {bound : ℝ} (hosc : OscillationBoundedOnPartition partition path bound)
    (t : unitInterval) :
    dist (path t) (partition.stepApproximation path t) ≤ bound := by
  have hbot : (⊥ : unitInterval) ≠ ⊤ := ne_of_lt bot_lt_top
  have hbound_nonneg : 0 ≤ bound := by
    have h := hosc ⊥ ⊥ hbot hbot rfl
    simpa [dist_self] using h
  by_cases ht : t = ⊤
  · subst t
    simpa [stepApproximation, stepPath] using hbound_nonneg
  · let i := partition.index t
    have hi : i.castSucc < Fin.last partition.size := by
      apply Fin.lt_def.mpr
      simp [i]
    have hlast : partition.points (Fin.last partition.size) = ⊤ := by
      simpa [Fin.last] using partition.last
    have hsamplelt : partition.points i.castSucc < ⊤ := by
      rw [← hlast]
      exact partition.strictMono_points hi
    have hidx : partition.index t =
        partition.index (partition.points i.castSucc) := by
      dsimp [i]
      exact (partition.index_start (partition.index t)).symm
    have hbound' := hosc t (partition.points i.castSucc) ht
      (ne_of_lt hsamplelt) hidx
    simpa [stepApproximation, stepPath, ht, i] using hbound'

/-- The uniform distance from a path to its partition step approximation is
bounded by its cellwise oscillation. -/
theorem OscillationPartition.uniformEDist_stepApproximation_le
    {E : Type*} [MetricSpace E]
    (partition : OscillationPartition) (path : CadlagPath unitInterval E)
    {bound : ℝ} (hosc : OscillationBoundedOnPartition partition path bound) :
    uniformEDist path (partition.stepApproximation path) ≤ ENNReal.ofReal bound := by
  rw [uniformEDist_eq_edist, UniformFun.edist_def]
  apply iSup_le
  intro t
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal
    (partition.dist_stepApproximation_le path hosc t)

/-- The step approximation also bounds the `J₁` distance by the original
within-cell oscillation. -/
theorem OscillationPartition.j1EDist_stepApproximation_le
    {E : Type*} [MetricSpace E]
    (partition : OscillationPartition) (path : CadlagPath unitInterval E)
    {bound : ℝ} (hosc : OscillationBoundedOnPartition partition path bound) :
    j1EDist path (partition.stepApproximation path) ≤ ENNReal.ofReal bound :=
  (j1EDist_le_uniformEDist _ _).trans
    (partition.uniformEDist_stepApproximation_le path hosc)

end Skorokhod

end
