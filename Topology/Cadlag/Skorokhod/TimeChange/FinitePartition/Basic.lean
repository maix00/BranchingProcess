/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.TimeChange.FinitePartition.Affine
public import Topology.Cadlag.Skorokhod.Oscillation.Partition.Finite

/-!
# Piecewise-affine maps for finite partitions

Construct the map that sends each source cell to the corresponding target
cell and preserves partition indices.
-/

@[expose] public section

namespace Skorokhod.TimeChange.FinitePartition

/-- Convert an ordered list of finite time points into the partition
structure used by the càdlàg path API. -/
noncomputable def ofPoints {n : ℕ} (hn : 0 < n)
    (points : Fin (n + 1) → unitInterval)
    (hfirst : points ⟨0, by omega⟩ = ⊥)
    (hlast : points ⟨n, by omega⟩ = ⊤)
    (hstrict : StrictMono points) : Skorokhod.OscillationPartition :=
  Skorokhod.OscillationPartition.ofFinitePoints hn points hfirst hlast hstrict

/-- The real-valued piecewise-affine interpolation determined by matching the
cells of two finite partitions. -/
noncomputable def interpolationValue {n : ℕ} (hn : 0 < n)
    (source target : Fin (n + 1) → unitInterval)
    (hsourceFirst : source ⟨0, by omega⟩ = ⊥)
    (hsourceLast : source ⟨n, by omega⟩ = ⊤)
    (hsourceStrict : StrictMono source) (t : unitInterval) : ℝ := by
  let p := ofPoints hn source hsourceFirst hsourceLast hsourceStrict
  let i := p.index t
  exact affineInterpolate
    (source i.castSucc) (source i.succ)
    (target i.castSucc) (target i.succ) t

/-- The interpolation value lies in the target cell corresponding to the
source cell containing the input time. -/
theorem interpolationValue_bounds {n : ℕ} (hn : 0 < n)
    (source target : Fin (n + 1) → unitInterval)
    (hsourceFirst : source ⟨0, by omega⟩ = ⊥)
    (hsourceLast : source ⟨n, by omega⟩ = ⊤)
    (hsourceStrict : StrictMono source)
    (htargetStrict : StrictMono target) (t : unitInterval) :
    (target ((ofPoints hn source hsourceFirst hsourceLast hsourceStrict).index t).castSucc : ℝ) ≤
        interpolationValue hn source target hsourceFirst hsourceLast hsourceStrict t ∧
      interpolationValue hn source target hsourceFirst hsourceLast hsourceStrict t ≤
          (target ((ofPoints hn source hsourceFirst hsourceLast hsourceStrict).index t).succ : ℝ) := by
  let p := ofPoints hn source hsourceFirst hsourceLast hsourceStrict
  let i := p.index t
  have hsourceLeft : (source i.castSucc : ℝ) ≤ t := by
    exact_mod_cast p.index_lower t
  have hsourceRight : t ≤ (source i.succ : ℝ) := by
    rcases p.index_upper t with hnext | hlast
    · exact_mod_cast hnext.le
    · change i.val + 1 = n at hlast
      have hi : i.succ = Fin.last n := by
        apply Fin.ext
        simpa [Fin.val_succ, Fin.val_last] using hlast
      have hsourceTop : source (Fin.last n) = ⊤ := by
        simpa [Fin.last] using hsourceLast
      rw [hi, hsourceTop]
      exact t.2.2
  have hsourceGap : (source i.castSucc : ℝ) < (source i.succ : ℝ) := by
    exact_mod_cast p.strictMono_points i.castSucc_lt_succ
  have htargetGap : (target i.castSucc : ℝ) < (target i.succ : ℝ) := by
    exact_mod_cast htargetStrict i.castSucc_lt_succ
  change (target i.castSucc : ℝ) ≤
      affineInterpolate (source i.castSucc) (source i.succ)
        (target i.castSucc) (target i.succ) t ∧
      affineInterpolate (source i.castSucc) (source i.succ)
        (target i.castSucc) (target i.succ) t ≤ (target i.succ : ℝ)
  exact affineInterpolate_mem hsourceGap htargetGap hsourceLeft hsourceRight

/-- The piecewise-affine interpolation as a map of unit intervals. -/
noncomputable def map {n : ℕ} (hn : 0 < n)
    (source target : Fin (n + 1) → unitInterval)
    (hsourceFirst : source ⟨0, by omega⟩ = ⊥)
    (hsourceLast : source ⟨n, by omega⟩ = ⊤)
    (hsourceStrict : StrictMono source)
    (htargetStrict : StrictMono target) (t : unitInterval) : unitInterval := by
  refine ⟨interpolationValue hn source target hsourceFirst hsourceLast hsourceStrict
    t, ?_⟩
  obtain ⟨hleft, hright⟩ := interpolationValue_bounds hn source target
    hsourceFirst hsourceLast hsourceStrict htargetStrict t
  constructor
  · exact (target _).property.1.trans hleft
  · exact hright.trans (target _).property.2

/-- Coercing the finite-partition map to `ℝ` recovers its interpolation
formula. -/
theorem coe_map {n : ℕ} (hn : 0 < n)
    (source target : Fin (n + 1) → unitInterval)
    (hsourceFirst : source ⟨0, by omega⟩ = ⊥)
    (hsourceLast : source ⟨n, by omega⟩ = ⊤)
    (hsourceStrict : StrictMono source)
    (htargetStrict : StrictMono target) (t : unitInterval) :
    (map hn source target hsourceFirst hsourceLast hsourceStrict htargetStrict t : ℝ) =
      interpolationValue hn source target hsourceFirst hsourceLast hsourceStrict t := rfl

/-- Mapping a time preserves its corresponding partition index. -/
theorem map_index {n : ℕ} (hn : 0 < n)
    (source target : Fin (n + 1) → unitInterval)
    (hsourceFirst : source ⟨0, by omega⟩ = ⊥)
    (hsourceLast : source ⟨n, by omega⟩ = ⊤)
    (hsourceStrict : StrictMono source)
    (htargetFirst : target ⟨0, by omega⟩ = ⊥)
    (htargetLast : target ⟨n, by omega⟩ = ⊤)
    (htargetStrict : StrictMono target) (t : unitInterval) :
    (ofPoints hn target htargetFirst htargetLast htargetStrict).index
      (map hn source target hsourceFirst hsourceLast hsourceStrict htargetStrict t) =
      (ofPoints hn source hsourceFirst hsourceLast hsourceStrict).index t := by
  let p := ofPoints hn source hsourceFirst hsourceLast hsourceStrict
  let q := ofPoints hn target htargetFirst htargetLast htargetStrict
  let i := p.index t
  have hbounds := interpolationValue_bounds hn source target hsourceFirst hsourceLast
    hsourceStrict htargetStrict t
  have hleftReal : (target i.castSucc : ℝ) ≤
      interpolationValue hn source target hsourceFirst hsourceLast hsourceStrict t := by
    have hbound := hbounds.1
    change (target i.castSucc : ℝ) ≤ _ at hbound
    exact hbound
  have hleft : q.points i.castSucc ≤
      map hn source target hsourceFirst hsourceLast hsourceStrict htargetStrict t := by
    change target i.castSucc ≤ _
    exact_mod_cast hleftReal
  have hright :
      map hn source target hsourceFirst hsourceLast hsourceStrict htargetStrict t < q.points i.succ ∨
        i.val + 1 = q.size := by
    rcases p.index_upper t with hnext | hlast
    · left
      have hsourceGap : (source i.castSucc : ℝ) < (source i.succ : ℝ) := by
        exact_mod_cast p.strictMono_points i.castSucc_lt_succ
      have htargetGap : (target i.castSucc : ℝ) < (target i.succ : ℝ) := by
        exact_mod_cast htargetStrict i.castSucc_lt_succ
      have hnext' : (t : ℝ) < (source i.succ : ℝ) := by
        exact_mod_cast hnext
      have hltReal :
          (map hn source target hsourceFirst hsourceLast hsourceStrict htargetStrict t : ℝ) <
            (target i.succ : ℝ) := by
        rw [coe_map]
        change affineInterpolate (source i.castSucc) (source i.succ)
          (target i.castSucc) (target i.succ) t < (target i.succ : ℝ)
        exact affineInterpolate_lt_right hsourceGap htargetGap hnext'
      exact_mod_cast hltReal
    · change i.val + 1 = n at hlast
      right
      change i.val + 1 = n
      exact hlast
  exact q.index_eq_of_cell i _ hleft hright

/-- On each source cell, the interpolation uses that cell's affine formula. -/
theorem interpolationValue_eq_affine {n : ℕ} (hn : 0 < n)
    (source target : Fin (n + 1) → unitInterval)
    (hsourceFirst : source ⟨0, by omega⟩ = ⊥)
    (hsourceLast : source ⟨n, by omega⟩ = ⊤)
    (hsourceStrict : StrictMono source) (t : unitInterval) (i : Fin n)
    (hi : (ofPoints hn source hsourceFirst hsourceLast hsourceStrict).index t = i) :
    interpolationValue hn source target hsourceFirst hsourceLast hsourceStrict t =
      affineInterpolate (source i.castSucc) (source i.succ)
        (target i.castSucc) (target i.succ) t := by
  simp [interpolationValue, hi]; rfl

end Skorokhod.TimeChange.FinitePartition

end
