/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Topology.Cadlag.Skorokhod.TimeChange

/-!
# Piecewise-affine time changes

`linearBreakpoint target source` is the increasing piecewise-affine homeomorphism
of `[0,1]` that sends `source` to `target` and fixes the two endpoints. Its
uniform distortion is bounded by the displacement of the breakpoint.
-/

@[expose] public section

open Set

namespace Skorokhod.TimeChange

/-- The piecewise-affine map on `ℝ` that sends `source` to `target` and fixes
the two endpoints of `[0, 1]`. -/
noncomputable def breakpointMap (target source x : ℝ) : ℝ :=
  target / source * min x source + (1 - target) / (1 - source) * max (x - source) 0

/-- The breakpoint map is affine to the left of its source breakpoint. -/
theorem breakpointMap_left {target source x : ℝ} (hx : x ≤ source) :
    breakpointMap target source x = target / source * x := by
  simp [breakpointMap, min_eq_left hx, max_eq_right (sub_nonpos.mpr hx)]

/-- The breakpoint map is affine to the right of its source breakpoint. -/
theorem breakpointMap_right {target source x : ℝ}
    (hx : source ≤ x) (hsource : source ≠ 0) :
    breakpointMap target source x =
      target + (1 - target) / (1 - source) * (x - source) := by
  rw [breakpointMap, min_eq_right hx, max_eq_left (sub_nonneg.mpr hx)]
  rw [div_mul_cancel₀ target hsource]

/-- The breakpoint map sends the unit interval into itself when both
breakpoints are interior points. -/
theorem breakpointMap_mem_unitInterval {target source x : ℝ}
    (htarget : 0 < target) (htarget_one : target < 1)
    (hsource : 0 < source) (hsource_one : source < 1)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    breakpointMap target source x ∈ Set.Icc (0 : ℝ) 1 := by
  rcases le_total x source with hleft | hright
  · rw [breakpointMap_left hleft]
    constructor
    · exact mul_nonneg (div_nonneg htarget.le hsource.le) hx.1
    · calc
        target / source * x ≤ target / source * source :=
          mul_le_mul_of_nonneg_left hleft (le_of_lt (div_pos htarget hsource))
        _ = target := by rw [div_mul_cancel₀ target (ne_of_gt hsource)]
        _ ≤ 1 := htarget_one.le
  · rw [breakpointMap_right hright (ne_of_gt hsource)]
    constructor
    · have hratio : 0 ≤ (1 - target) / (1 - source) :=
        div_nonneg (by linarith) (by linarith)
      have hinc : 0 ≤ x - source := sub_nonneg.mpr hright
      positivity
    · have hratio : 0 ≤ (1 - target) / (1 - source) :=
        div_nonneg (by linarith) (by linarith)
      have hcancel : (1 - target) / (1 - source) * (1 - source) = 1 - target := by
        exact div_mul_cancel₀ (1 - target) (sub_ne_zero.mpr (ne_of_gt hsource_one))
      calc
        target + (1 - target) / (1 - source) * (x - source) ≤
            target + (1 - target) / (1 - source) * (1 - source) :=
          add_le_add (le_rfl : target ≤ target)
            (mul_le_mul_of_nonneg_left (sub_le_sub_right hx.2 source) hratio)
        _ = 1 := by rw [hcancel]; ring

/-- Swapping source and target gives the inverse breakpoint map. -/
theorem breakpointMap_comp_swapped {target source x : ℝ}
    (htarget : 0 < target) (htarget_one : target < 1)
    (hsource : 0 < source) (hsource_one : source < 1) :
    breakpointMap source target (breakpointMap target source x) = x := by
  rcases le_total x source with hleft | hright
  · rw [breakpointMap_left hleft]
    have hy : target / source * x ≤ target := by
      calc
        target / source * x ≤ target / source * source :=
          mul_le_mul_of_nonneg_left hleft (le_of_lt (div_pos htarget hsource))
        _ = target := by rw [div_mul_cancel₀ target (ne_of_gt hsource)]
    rw [breakpointMap_left hy]
    field_simp
  · have hright' : source ≤ x := hright
    rw [breakpointMap_right hright' (ne_of_gt hsource)]
    have hy : target ≤ target + (1 - target) / (1 - source) * (x - source) := by
      have hratio : 0 ≤ (1 - target) / (1 - source) :=
        div_nonneg (by linarith) (by linarith)
      have hinc : 0 ≤ x - source := sub_nonneg.mpr hright'
      nlinarith [mul_nonneg hratio hinc]
    rw [breakpointMap_right hy (ne_of_gt htarget)]
    have hratio :
        (1 - source) / (1 - target) * ((1 - target) / (1 - source)) = 1 := by
      have hs : 1 - source ≠ 0 := sub_ne_zero.mpr (ne_of_gt hsource_one)
      have ht : 1 - target ≠ 0 := sub_ne_zero.mpr (ne_of_gt htarget_one)
      field_simp [hs, ht]
    calc
      source + (1 - source) / (1 - target) *
          (target + (1 - target) / (1 - source) * (x - source) - target) =
          source + ((1 - source) / (1 - target) * ((1 - target) / (1 - source))) *
            (x - source) := by ring
      _ = source + 1 * (x - source) := by rw [hratio]
      _ = x := by ring

/-- The breakpoint map is strictly increasing when its breakpoints are
interior. -/
theorem breakpointMap_strictMono {target source : ℝ}
    (htarget : 0 < target) (htarget_one : target < 1)
    (hsource : 0 < source) (hsource_one : source < 1) :
    StrictMono (breakpointMap target source) := by
  intro x y hxy
  by_cases hx : x ≤ source
  · by_cases hy : y ≤ source
    · rw [breakpointMap_left hx, breakpointMap_left hy]
      exact mul_lt_mul_of_pos_left hxy (div_pos htarget hsource)
    · have hy' : source ≤ y := le_of_lt (lt_of_not_ge hy)
      rw [breakpointMap_left hx,
        breakpointMap_right hy' (ne_of_gt hsource)]
      have hxle : target / source * x ≤ target := by
        calc
          target / source * x ≤ target / source * source :=
            mul_le_mul_of_nonneg_left hx (le_of_lt (div_pos htarget hsource))
          _ = target := by rw [div_mul_cancel₀ _ (ne_of_gt hsource)]
      have hgt : target < target + (1 - target) / (1 - source) * (y - source) := by
        have hratio : 0 < (1 - target) / (1 - source) :=
          div_pos (by linarith) (by linarith)
        have hinc : 0 < y - source := sub_pos.mpr (lt_of_not_ge hy)
        nlinarith
      exact hxle.trans_lt hgt
  · have hx' : source < x := lt_of_not_ge hx
    have hy' : source < y := hx'.trans hxy
    rw [breakpointMap_right hx'.le (ne_of_gt hsource),
      breakpointMap_right hy'.le (ne_of_gt hsource)]
    have hratio : 0 < (1 - target) / (1 - source) :=
      div_pos (by linarith) (by linarith)
    have hmul := mul_lt_mul_of_pos_left (sub_lt_sub_right hxy source) hratio
    simpa [add_comm] using add_lt_add_left hmul target

/-- The restriction of `breakpointMap` to the unit interval. -/
noncomputable def breakpointMapInterval (target source : ℝ)
    (htarget : 0 < target) (htarget_one : target < 1)
    (hsource : 0 < source) (hsource_one : source < 1) :
    unitInterval → unitInterval := fun x =>
      ⟨breakpointMap target source x,
        breakpointMap_mem_unitInterval htarget htarget_one hsource hsource_one x.2⟩

/-- The interval maps with source and target swapped are inverses. -/
theorem breakpointMapInterval_left_inv (target source : ℝ)
    (htarget : 0 < target) (htarget_one : target < 1)
    (hsource : 0 < source) (hsource_one : source < 1) (x : unitInterval) :
    breakpointMapInterval source target hsource hsource_one htarget htarget_one
      (breakpointMapInterval target source htarget htarget_one hsource hsource_one x) = x := by
  apply Subtype.ext
  exact breakpointMap_comp_swapped htarget htarget_one hsource hsource_one

/-- The homeomorphism of the unit interval induced by `breakpointMap`. -/
noncomputable def breakpointHomeomorph (target source : ℝ)
    (htarget : 0 < target) (htarget_one : target < 1)
    (hsource : 0 < source) (hsource_one : source < 1) : unitInterval ≃ₜ unitInterval where
  toEquiv :=
    { toFun := breakpointMapInterval target source htarget htarget_one hsource hsource_one
      invFun := breakpointMapInterval source target hsource hsource_one htarget htarget_one
      left_inv := breakpointMapInterval_left_inv target source htarget htarget_one hsource hsource_one
      right_inv := by
        intro x
        exact breakpointMapInterval_left_inv source target hsource hsource_one htarget htarget_one x }
  continuous_toFun := by
    have hmin : Continuous fun x : unitInterval => min (x : ℝ) source :=
      continuous_subtype_val.min continuous_const
    have hmax : Continuous fun x : unitInterval => max ((x : ℝ) - source) 0 :=
      (continuous_subtype_val.sub continuous_const).max continuous_const
    have hcont : Continuous (fun x : unitInterval => breakpointMap target source x) := by
      change Continuous (fun x : unitInterval =>
        target / source * min (x : ℝ) source +
          (1 - target) / (1 - source) * max ((x : ℝ) - source) 0)
      exact (continuous_const.mul hmin).add (continuous_const.mul hmax)
    exact hcont.subtype_mk fun x =>
      breakpointMap_mem_unitInterval htarget htarget_one hsource hsource_one x.2
  continuous_invFun := by
    have hmin : Continuous fun x : unitInterval => min (x : ℝ) target :=
      continuous_subtype_val.min continuous_const
    have hmax : Continuous fun x : unitInterval => max ((x : ℝ) - target) 0 :=
      (continuous_subtype_val.sub continuous_const).max continuous_const
    have hcont : Continuous (fun x : unitInterval => breakpointMap source target x) := by
      change Continuous (fun x : unitInterval =>
        source / target * min (x : ℝ) target +
          (1 - source) / (1 - target) * max ((x : ℝ) - target) 0)
      exact (continuous_const.mul hmin).add (continuous_const.mul hmax)
    exact hcont.subtype_mk fun x =>
      breakpointMap_mem_unitInterval hsource hsource_one htarget htarget_one x.2

/-- The piecewise-affine time change sending an interior time `source` to
`target` and fixing `0` and `1`. -/
noncomputable def linearBreakpoint (target source : ℝ)
    (htarget : 0 < target) (htarget_one : target < 1)
    (hsource : 0 < source) (hsource_one : source < 1) : TimeChange where
  toHomeomorph := breakpointHomeomorph target source htarget htarget_one hsource hsource_one
  strictMono_toHomeomorph := by
    intro x y hxy
    exact breakpointMap_strictMono htarget htarget_one hsource hsource_one hxy

@[simp]
theorem linearBreakpoint_apply_source (target source : ℝ)
    (htarget : 0 < target) (htarget_one : target < 1)
    (hsource : 0 < source) (hsource_one : source < 1) :
    linearBreakpoint target source htarget htarget_one hsource hsource_one
      ⟨source, ⟨hsource.le, hsource_one.le⟩⟩ = ⟨target, ⟨htarget.le, htarget_one.le⟩⟩ := by
  apply Subtype.ext
  change breakpointMap target source source = target
  rw [breakpointMap_right le_rfl (ne_of_gt hsource)]
  simp

/-- A linear breakpoint fixes the initial endpoint. -/
@[simp]
theorem linearBreakpoint_apply_bot (target source : ℝ)
    (htarget : 0 < target) (htarget_one : target < 1)
    (hsource : 0 < source) (hsource_one : source < 1) :
    linearBreakpoint target source htarget htarget_one hsource hsource_one ⊥ = ⊥ :=
  TimeChange.apply_bot _

/-- A linear breakpoint fixes the terminal endpoint. -/
@[simp]
theorem linearBreakpoint_apply_top (target source : ℝ)
    (htarget : 0 < target) (htarget_one : target < 1)
    (hsource : 0 < source) (hsource_one : source < 1) :
    linearBreakpoint target source htarget htarget_one hsource hsource_one ⊤ = ⊤ :=
  TimeChange.apply_top _

/-- Moving one breakpoint by `ε` requires at most `ε` uniform time distortion. -/
theorem linearBreakpoint_distortion_le_abs (target source : ℝ)
    (htarget : 0 < target) (htarget_one : target < 1)
    (hsource : 0 < source) (hsource_one : source < 1) :
    (linearBreakpoint target source htarget htarget_one hsource hsource_one).distortion ≤
      |target - source| := by
  rw [distortion, ContinuousMap.dist_le_iff_of_nonempty]
  intro t
  simp only [ContinuousMap.id_apply, Subtype.dist_eq, Real.dist_eq]
  by_cases ht : (t : ℝ) ≤ source
  · change |breakpointMap target source t - t| ≤ |target - source|
    rw [breakpointMap_left ht]
    have hratio : 0 ≤ (t : ℝ) / source ∧ (t : ℝ) / source ≤ 1 := by
      constructor
      · exact div_nonneg t.2.1 (le_of_lt hsource)
      · exact (div_le_one hsource).2 ht
    have hrewrite : target / source * (t : ℝ) - t =
        (target - source) * ((t : ℝ) / source) := by
      field_simp [ne_of_gt hsource]
    rw [hrewrite, abs_mul, abs_of_nonneg hratio.1]
    calc
      |target - source| * ((t : ℝ) / source) ≤ |target - source| * 1 :=
        mul_le_mul_of_nonneg_left hratio.2 (abs_nonneg _)
      _ = |target - source| := mul_one _
  · have ht' : source ≤ (t : ℝ) := le_of_not_ge ht
    change |breakpointMap target source t - t| ≤ |target - source|
    rw [breakpointMap_right ht' (ne_of_gt hsource)]
    have hratio : 0 ≤ (1 - (t : ℝ)) / (1 - source) ∧
        (1 - (t : ℝ)) / (1 - source) ≤ 1 := by
      constructor
      · exact div_nonneg (by linarith [t.2.2]) (by linarith)
      · apply (div_le_one (by linarith : 0 < 1 - source)).2
        linarith [t.2.2]
    have hrewrite :
        target + (1 - target) / (1 - source) * ((t : ℝ) - source) - t =
          (target - source) * ((1 - (t : ℝ)) / (1 - source)) := by
      field_simp [sub_ne_zero.mpr (ne_of_gt hsource_one)]; ring
    rw [hrewrite, abs_mul, abs_of_nonneg hratio.1]
    calc
      |target - source| * ((1 - (t : ℝ)) / (1 - source)) ≤
          |target - source| * 1 := mul_le_mul_of_nonneg_left hratio.2 (abs_nonneg _)
      _ = |target - source| := mul_one _

end Skorokhod.TimeChange

end
