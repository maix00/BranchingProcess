/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Topology.Order.MonotoneContinuity
public import Topology.Cadlag.Skorokhod.TimeChange.FinitePartition.Monotone
public import Topology.Cadlag.Skorokhod.TimeChange

/-!
# Time changes matching finite partitions

An increasing piecewise-affine time change maps one strictly ordered finite
partition of `[0, 1]` onto another partition with the same number of cells.
-/

@[expose] public section

namespace Skorokhod.TimeChange.FinitePartition

/-- The increasing homeomorphism between two finite partitions with the same
number of cells. -/
noncomputable def homeomorph {n : ℕ} (hn : 0 < n)
    (source target : Fin (n + 1) → unitInterval)
    (hsourceFirst : source ⟨0, by omega⟩ = ⊥)
    (hsourceLast : source ⟨n, by omega⟩ = ⊤)
    (hsourceStrict : StrictMono source)
    (htargetFirst : target ⟨0, by omega⟩ = ⊥)
    (htargetLast : target ⟨n, by omega⟩ = ⊤)
    (htargetStrict : StrictMono target) : unitInterval ≃ₜ unitInterval where
  toEquiv :=
    { toFun := map hn source target hsourceFirst hsourceLast hsourceStrict htargetStrict
      invFun := map hn target source htargetFirst htargetLast htargetStrict hsourceStrict
      left_inv := by
        intro t
        exact map_comp_swapped hn source target hsourceFirst hsourceLast hsourceStrict
          htargetFirst htargetLast htargetStrict t
      right_inv := by
        intro t
        exact map_comp_swapped hn target source htargetFirst htargetLast htargetStrict
          hsourceFirst hsourceLast hsourceStrict t }
  continuous_toFun := by
    have hsurj : Function.Surjective
        (map hn source target hsourceFirst hsourceLast hsourceStrict htargetStrict) := by
      intro y
      refine ⟨map hn target source htargetFirst htargetLast htargetStrict hsourceStrict y, ?_⟩
      exact map_comp_swapped hn target source htargetFirst htargetLast htargetStrict
        hsourceFirst hsourceLast hsourceStrict y
    exact (map_strictMono hn source target hsourceFirst hsourceLast hsourceStrict
      htargetStrict).monotone.continuous_of_surjective hsurj
  continuous_invFun := by
    have hsurj : Function.Surjective
        (map hn target source htargetFirst htargetLast htargetStrict hsourceStrict) := by
      intro y
      refine ⟨map hn source target hsourceFirst hsourceLast hsourceStrict htargetStrict y, ?_⟩
      exact map_comp_swapped hn source target hsourceFirst hsourceLast hsourceStrict
        htargetFirst htargetLast htargetStrict y
    exact (map_strictMono hn target source htargetFirst htargetLast htargetStrict
      hsourceStrict).monotone.continuous_of_surjective hsurj

/-- Regard the finite-partition homeomorphism as a Skorokhod time change. -/
noncomputable def ofMatchingPartitions {n : ℕ} (hn : 0 < n)
    (source target : Fin (n + 1) → unitInterval)
    (hsourceFirst : source ⟨0, by omega⟩ = ⊥)
    (hsourceLast : source ⟨n, by omega⟩ = ⊤)
    (hsourceStrict : StrictMono source)
    (htargetFirst : target ⟨0, by omega⟩ = ⊥)
    (htargetLast : target ⟨n, by omega⟩ = ⊤)
    (htargetStrict : StrictMono target) : TimeChange where
  toHomeomorph := homeomorph hn source target hsourceFirst hsourceLast hsourceStrict
    htargetFirst htargetLast htargetStrict
  strictMono_toHomeomorph := map_strictMono hn source target hsourceFirst hsourceLast
    hsourceStrict htargetStrict

/-- The time change matching two finite partitions moves each time by at most
the largest displacement bound assumed for their partition points. -/
theorem ofMatchingPartitions_distortion_le {n : ℕ} (hn : 0 < n)
    (source target : Fin (n + 1) → unitInterval)
    (hsourceFirst : source ⟨0, by omega⟩ = ⊥)
    (hsourceLast : source ⟨n, by omega⟩ = ⊤)
    (hsourceStrict : StrictMono source)
    (htargetFirst : target ⟨0, by omega⟩ = ⊥)
    (htargetLast : target ⟨n, by omega⟩ = ⊤)
    (htargetStrict : StrictMono target) (ε : ℝ)
    (hpoints : ∀ j, dist (source j) (target j) ≤ ε) :
    (ofMatchingPartitions hn source target hsourceFirst hsourceLast hsourceStrict
      htargetFirst htargetLast htargetStrict).distortion ≤ ε := by
  rw [TimeChange.distortion, ContinuousMap.dist_le_iff_of_nonempty]
  intro t
  change dist
    (map hn source target hsourceFirst hsourceLast hsourceStrict htargetStrict t) t ≤ _
  rw [Subtype.dist_eq, Real.dist_eq, coe_map]
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
  rw [interpolationValue_eq_affine hn source target hsourceFirst hsourceLast
    hsourceStrict t i rfl]
  have hleftPoint :
      |(target i.castSucc : ℝ) - (source i.castSucc : ℝ)| ≤ ε := by
    simpa only [Subtype.dist_eq, Real.dist_eq, abs_sub_comm] using hpoints i.castSucc
  have hrightPoint :
      |(target i.succ : ℝ) - (source i.succ : ℝ)| ≤ ε := by
    simpa only [Subtype.dist_eq, Real.dist_eq, abs_sub_comm] using hpoints i.succ
  calc
    |affineInterpolate (source i.castSucc) (source i.succ)
        (target i.castSucc) (target i.succ) t - t|
        ≤ max |(target i.castSucc : ℝ) - (source i.castSucc : ℝ)|
            |(target i.succ : ℝ) - (source i.succ : ℝ)| :=
      affineInterpolate_distortion_le_max hsourceGap hsourceLeft hsourceRight
    _ ≤ ε := max_le hleftPoint hrightPoint

end Skorokhod.TimeChange.FinitePartition

end
