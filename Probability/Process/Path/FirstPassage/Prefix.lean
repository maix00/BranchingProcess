/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.FirstPassage.Basic

/-!
# Prefix dependence of continuous-path first passage

## Public declarations

- `ProbabilityTheory.firstPassageBelow_le_congr_of_agreeOn` states that if
  two paths agree on $[0,t]$, then either both first passages below $a$ occur
  by $t$ or neither does.
- `ProbabilityTheory.firstPassageBelow_eq_of_agreeOn` states that two paths
  agreeing on $[0,t]$ have the same first-passage time whenever it occurs by
  $t$.

These pathwise locality properties support restarting, freezing, and
approximating a path at a first-passage time.
-/

@[expose] public section

open scoped NNReal Classical

namespace ProbabilityTheory

/-- The event that first passage occurs by `t` is determined by the
path through `t`. -/
theorem firstPassageBelow_le_congr_of_agreeOn
    (f g : C(ℝ≥0, ℝ)) (a : ℝ) (t : ℝ≥0)
    (hprefix : ∀ u : ℝ≥0, u ≤ t → f u = g u) :
    firstPassageBelow f a ≤ t ↔ firstPassageBelow g a ≤ t := by
  rw [firstPassageBelow_le_iff, firstPassageBelow_le_iff]
  constructor
  · rintro ⟨u, hu, hfu⟩
    exact ⟨u, hu, by rw [← hprefix u hu]; exact hfu⟩
  · rintro ⟨u, hu, hgu⟩
    exact ⟨u, hu, by rw [hprefix u hu]; exact hgu⟩

/-- If the passage occurs by `t`, the first-passage time itself is
determined by the path through `t`. -/
theorem firstPassageBelow_eq_of_agreeOn
    (f g : C(ℝ≥0, ℝ)) (a : ℝ) (t : ℝ≥0)
    (hprefix : ∀ u : ℝ≥0, u ≤ t → f u = g u)
    (hf : firstPassageBelow f a ≤ t) :
    firstPassageBelow f a = firstPassageBelow g a := by
  let τf : ℝ≥0 := sInf {u : ℝ≥0 | f u ≤ a}
  let τg : ℝ≥0 := sInf {u : ℝ≥0 | g u ≤ a}
  obtain ⟨u, hu, hfu⟩ := (firstPassageBelow_le_iff f a t).mp hf
  have hexists_f : ∃ v : ℝ≥0, f v ≤ a := ⟨u, hfu⟩
  have hfirst_f : firstPassageBelow f a = τf := by
    simp only [firstPassageBelow, firstPassageLE_eq_sInf, ite_eq_left hexists_f]
    rfl
  have hτf_le : τf ≤ t := by
    rw [hfirst_f] at hf
    exact WithTop.coe_le_coe.mp hf
  have hexists_g : ∃ v : ℝ≥0, g v ≤ a :=
    ⟨u, by rw [← hprefix u hu]; exact hfu⟩
  have hfirst_g : firstPassageBelow g a = τg := by
    simp only [firstPassageBelow, firstPassageLE_eq_sInf, ite_eq_left hexists_g]
    rfl
  have hg : firstPassageBelow g a ≤ t :=
    (firstPassageBelow_le_congr_of_agreeOn f g a t hprefix).mp hf
  have hτg_le : τg ≤ t := by
    rw [hfirst_g] at hg
    exact WithTop.coe_le_coe.mp hg
  have hτf_mem : f τf ≤ a := firstPassageBelow_attained f a hexists_f
  have hτg_mem : g τg ≤ a := firstPassageBelow_attained g a hexists_g
  have hτf_mem_g : g τf ≤ a := by
    rw [← hprefix τf hτf_le]
    exact hτf_mem
  have hτg_mem_f : f τg ≤ a := by
    rw [hprefix τg hτg_le]
    exact hτg_mem
  have hτg_le_τf : τg ≤ τf :=
    csInf_le ⟨0, fun _ _ => bot_le⟩ hτf_mem_g
  have hτf_le_τg : τf ≤ τg :=
    csInf_le ⟨0, fun _ _ => bot_le⟩ hτg_mem_f
  rw [hfirst_f, hfirst_g, le_antisymm hτf_le_τg hτg_le_τf]

end ProbabilityTheory

end
