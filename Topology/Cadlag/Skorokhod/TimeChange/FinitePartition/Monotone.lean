/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.TimeChange.FinitePartition.Basic

/-!
# Order properties of finite-partition maps

Prove strict monotonicity, inverse identities, and the action on partition
points.
-/

@[expose] public section

namespace Skorokhod.TimeChange.FinitePartition

/-- Swapping the source and target partitions gives the inverse map. -/
theorem map_comp_swapped {n : ℕ} (hn : 0 < n)
    (source target : Fin (n + 1) → unitInterval)
    (hsourceFirst : source ⟨0, by omega⟩ = ⊥)
    (hsourceLast : source ⟨n, by omega⟩ = ⊤)
    (hsourceStrict : StrictMono source)
    (htargetFirst : target ⟨0, by omega⟩ = ⊥)
    (htargetLast : target ⟨n, by omega⟩ = ⊤)
    (htargetStrict : StrictMono target) (t : unitInterval) :
    map hn target source htargetFirst htargetLast htargetStrict hsourceStrict
      (map hn source target hsourceFirst hsourceLast hsourceStrict htargetStrict t) = t := by
  apply Subtype.ext
  let p := ofPoints hn source hsourceFirst hsourceLast hsourceStrict
  let q := ofPoints hn target htargetFirst htargetLast htargetStrict
  let i : Fin n := p.index t
  have hindex : q.index
      (map hn source target hsourceFirst hsourceLast hsourceStrict htargetStrict t) = i := by
    change (ofPoints hn target htargetFirst htargetLast htargetStrict).index
        (map hn source target hsourceFirst hsourceLast hsourceStrict htargetStrict t) =
      (ofPoints hn source hsourceFirst hsourceLast hsourceStrict).index t
    exact map_index hn source target hsourceFirst hsourceLast hsourceStrict
      htargetFirst htargetLast htargetStrict t
  rw [coe_map hn target source htargetFirst htargetLast htargetStrict hsourceStrict]
  rw [interpolationValue_eq_affine hn target source htargetFirst htargetLast
    htargetStrict (map hn source target hsourceFirst hsourceLast hsourceStrict
      htargetStrict t) i hindex]
  rw [coe_map hn source target hsourceFirst hsourceLast hsourceStrict htargetStrict t]
  rw [interpolationValue_eq_affine hn source target hsourceFirst hsourceLast
    hsourceStrict t i rfl]
  have hsourceGap : (source i.castSucc : ℝ) < (source i.succ : ℝ) := by
    exact_mod_cast p.strictMono_points i.castSucc_lt_succ
  have htargetGap : (target i.castSucc : ℝ) < (target i.succ : ℝ) := by
    exact_mod_cast htargetStrict i.castSucc_lt_succ
  exact affineInterpolate_swapped hsourceGap htargetGap

/-- Matching finite strictly ordered partitions gives a strictly increasing
map of the unit interval. -/
theorem map_strictMono {n : ℕ} (hn : 0 < n)
    (source target : Fin (n + 1) → unitInterval)
    (hsourceFirst : source ⟨0, by omega⟩ = ⊥)
    (hsourceLast : source ⟨n, by omega⟩ = ⊤)
    (hsourceStrict : StrictMono source)
    (htargetStrict : StrictMono target) :
    StrictMono (map hn source target hsourceFirst hsourceLast hsourceStrict htargetStrict) := by
  intro x y hxy
  let p := ofPoints hn source hsourceFirst hsourceLast hsourceStrict
  let i := p.index x
  let j := p.index y
  have hij : i ≤ j := by
    exact p.index_monotone hxy.le
  by_cases heq : i = j
  · have hiY : p.index y = i := by
      change j = i
      exact heq.symm
    have hsourceGap : (source i.castSucc : ℝ) < (source i.succ : ℝ) := by
      exact_mod_cast p.strictMono_points i.castSucc_lt_succ
    have htargetGap : (target i.castSucc : ℝ) < (target i.succ : ℝ) := by
      exact_mod_cast htargetStrict i.castSucc_lt_succ
    change
      (map hn source target hsourceFirst hsourceLast hsourceStrict htargetStrict x : ℝ) <
        (map hn source target hsourceFirst hsourceLast hsourceStrict htargetStrict y : ℝ)
    rw [coe_map hn source target hsourceFirst hsourceLast hsourceStrict htargetStrict x,
      coe_map hn source target hsourceFirst hsourceLast hsourceStrict htargetStrict y]
    rw [interpolationValue_eq_affine hn source target hsourceFirst hsourceLast
      hsourceStrict x i rfl,
      interpolationValue_eq_affine hn source target hsourceFirst hsourceLast
        hsourceStrict y i hiY]
    exact affineInterpolate_strictMono hsourceGap htargetGap hxy
  · have hij' : i < j := lt_of_le_of_ne hij heq
    have hxright : (x : ℝ) < (source i.succ : ℝ) := by
      rcases p.index_upper x with hcell | hlast
      · exact_mod_cast hcell
      · change i.val + 1 = n at hlast
        have hpSize : p.size = n := rfl
        have hlast' : i.val + 1 = n := hlast.trans hpSize
        have hiNat : i.val < j.val := Fin.lt_def.mp hij'
        have hjNat : j.val < n := by simpa [hpSize] using j.isLt
        omega
    have hsourceGap : (source i.castSucc : ℝ) < (source i.succ : ℝ) := by
      exact_mod_cast p.strictMono_points i.castSucc_lt_succ
    have htargetGapLeft : (target i.castSucc : ℝ) < (target i.succ : ℝ) := by
      exact_mod_cast htargetStrict i.castSucc_lt_succ
    have htargetGapRight : (target j.castSucc : ℝ) < (target j.succ : ℝ) := by
      exact_mod_cast htargetStrict j.castSucc_lt_succ
    have hleft :
        (map hn source target hsourceFirst hsourceLast hsourceStrict htargetStrict x : ℝ) <
          (target i.succ : ℝ) := by
      rw [coe_map hn source target hsourceFirst hsourceLast hsourceStrict htargetStrict x]
      rw [interpolationValue_eq_affine hn source target hsourceFirst hsourceLast
        hsourceStrict x i rfl]
      exact affineInterpolate_lt_right hsourceGap htargetGapLeft hxright
    have htargetOrder : target i.succ ≤ target j.castSucc := by
      apply_mod_cast htargetStrict.monotone
      apply Fin.le_iff_val_le_val.mpr
      rw [Fin.val_succ, Fin.val_castSucc]
      omega
    have hright :
        (target j.castSucc : ℝ) ≤
          (map hn source target hsourceFirst hsourceLast hsourceStrict htargetStrict y : ℝ) := by
      have hbounds := interpolationValue_bounds hn source target hsourceFirst hsourceLast
        hsourceStrict htargetStrict y
      have hbound := hbounds.1
      change (target j.castSucc : ℝ) ≤ _ at hbound
      rw [coe_map hn source target hsourceFirst hsourceLast hsourceStrict htargetStrict y]
      exact hbound
    exact hleft.trans_le (htargetOrder.trans hright)

/-- The finite-partition map matches every left endpoint of a source cell to
the corresponding target endpoint. -/
theorem map_apply_cellStart {n : ℕ} (hn : 0 < n)
    (source target : Fin (n + 1) → unitInterval)
    (hsourceFirst : source ⟨0, by omega⟩ = ⊥)
    (hsourceLast : source ⟨n, by omega⟩ = ⊤)
    (hsourceStrict : StrictMono source)
    (htargetStrict : StrictMono target) (i : Fin n) :
    map hn source target hsourceFirst hsourceLast hsourceStrict htargetStrict
      (source i.castSucc) = target i.castSucc := by
  let p := ofPoints hn source hsourceFirst hsourceLast hsourceStrict
  have hindex : p.index (source i.castSucc) = i := p.index_start i
  apply Subtype.ext
  rw [coe_map hn source target hsourceFirst hsourceLast hsourceStrict htargetStrict]
  rw [interpolationValue_eq_affine hn source target hsourceFirst hsourceLast
    hsourceStrict (source i.castSucc) i hindex]
  exact affineInterpolate_left

end Skorokhod.TimeChange.FinitePartition

end
