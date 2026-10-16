/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Interpolation.Limit.Unbounded
public import Probability.Process.RandomWalk.Path.Interpolation.Finite.Block
public import Probability.Process.RandomWalk.Path.Corridor.Interpolation.Basic
public import Probability.Process.RandomWalk.Path.Survival.Basic
public import Probability.Process.Path.AboveStart.Continuous
public import Probability.Process.Path.Scaling.FiniteHorizon

/-!
# First-window conditions for polygonal random-walk paths

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.survivesNonnegative_of_isNonnegativeWindowStart_grid`:
  if the polygonal path's unit window beginning at $j/n$ lies above
  its starting height, then $S_{j+k}\ge S_j$ for $1\le k\le n$.
- `ProbabilityTheory.RandomWalk.restrictPathToUnitInterval_shiftToZero_grid`:
  the rebased polygonal path from $j/n$ to $(j+n)/n$ is exactly the
  interpolation of the finite increment block beginning at $j$.
- `ProbabilityTheory.RandomWalk.isNonnegativeWindowStart_grid_iff_survivesNonnegative`:
  the polygonal unit window at $j/n$ is eligible exactly when its
  discrete length-$n$ increment block survives.
- `ProbabilityTheory.RandomWalk.isNonnegativeWindowStart_grid_of_between`:
  an eligible polygonal unit window beginning between two grid times
  can be moved to the left grid time.

This is the grid restriction of the path transform in
Erwin Bolthausen, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Lemma 3.1 and Theorem 3.2,
Ann. Probab. 4(3) (1976), 480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open ProbabilityTheory
open scoped NNReal

/-- An eligible unit window can be moved left across a segment on which
the path is nondecreasing. -/
private theorem isNonnegativeWindowStart_of_leftSegment
    (f : C(ℝ≥0, ℝ)) (a t : ℝ≥0)
    (hat : a ≤ t)
    (hmono : ∀ x : ℝ≥0, a ≤ x → x ≤ t → f a ≤ f x)
    (ht : IsNonnegativeWindowStart f t) :
    IsNonnegativeWindowStart f a := by
  intro u
  by_cases hbefore : a + u.1 ≤ t
  · exact hmono (a + u.1) (le_add_of_nonneg_right bot_le) hbefore
  · have hafter : t ≤ a + u.1 := le_of_not_ge hbefore
    have hwithin : a + u.1 ≤ 1 + t := by
      calc
        a + u.1 = u.1 + a := add_comm _ _
        _ ≤ u.1 + t := add_le_add_right hat _
        _ ≤ 1 + t := add_le_add_left u.property.2 _
    let v : Set.Icc (0 : ℝ≥0) 1 :=
      ⟨a + u.1 - t, ⟨bot_le, (tsub_le_iff_right).2 hwithin⟩⟩
    have hreturn : t + v.1 = a + u.1 :=
      add_tsub_cancel_of_le hafter
    calc
      f a ≤ f t := hmono t hat le_rfl
      _ ≤ f (t + v.1) := ht v
      _ = f (a + u.1) := congrArg f hreturn

/-- An eligible unit window of a polygonal random walk can be moved
to the left endpoint of the interpolation segment containing its start. -/
theorem isNonnegativeWindowStart_grid_of_between
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    (hscale : 0 < scale n) (j : ℕ) (increment : ℕ → ℝ)
    (t : ℝ≥0)
    (hlo : (j : ℝ) ≤ (n : ℝ) * (t : ℝ))
    (hhi : (n : ℝ) * (t : ℝ) < (j : ℝ) + 1)
    (ht : IsNonnegativeWindowStart
      (normalizedLinearContinuousPathUnbounded scale n increment) t) :
    IsNonnegativeWindowStart
      (normalizedLinearContinuousPathUnbounded scale n increment)
      (⟨(j : ℝ) / n, div_nonneg (Nat.cast_nonneg j)
        (Nat.cast_nonneg n)⟩ : ℝ≥0) := by
  let left : ℝ≥0 :=
    ⟨(j : ℝ) / n, div_nonneg (Nat.cast_nonneg j) (Nat.cast_nonneg n)⟩
  let right : ℝ≥0 :=
    ⟨((j : ℝ) + 1) / n,
      div_nonneg (by positivity) (Nat.cast_nonneg n)⟩
  have hnreal : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hleft : (n : ℝ) * (left : ℝ) = j := by
    change (n : ℝ) * ((j : ℝ) / n) = j
    field_simp [ne_of_gt hnreal]
  have hright : (n : ℝ) * (right : ℝ) = (j : ℝ) + 1 := by
    change (n : ℝ) * (((j : ℝ) + 1) / n) = (j : ℝ) + 1
    field_simp [ne_of_gt hnreal]
  have hlt : left ≤ t := by
    apply NNReal.coe_le_coe.mp
    dsimp [left]
    exact (div_le_iff₀ hnreal).2 (by nlinarith [hlo])
  have htr : t < right := by
    apply NNReal.coe_lt_coe.mp
    dsimp [right]
    exact (lt_div_iff₀ hnreal).2 (by nlinarith [hhi])
  have hwithin : right ≤ t + 1 := by
    apply NNReal.coe_le_coe.mp
    dsimp [right]
    apply (div_le_iff₀ hnreal).2
    have hone : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [hlo]
  let f := normalizedLinearContinuousPathUnbounded scale n increment
  let u : Set.Icc (0 : ℝ≥0) 1 :=
    ⟨right - t, ⟨bot_le, (tsub_le_iff_right).2 (by
      simpa only [add_comm] using hwithin)⟩⟩
  have hpath_right : f t ≤ f right := by
    have hineq := ht u
    have hreturn : t + u.1 = right := add_tsub_cancel_of_le htr.le
    change f t ≤ f (t + u.1) at hineq
    rwa [hreturn] at hineq
  have hseg_t := normalizedLinearPathUnbounded_segment scale n j
    increment t hlo hhi.le
  have hseg_right := normalizedLinearPathUnbounded_segment scale n j
    increment right (by rw [hright]; linarith) (by rw [hright])
  have hineq :
      (scale n)⁻¹ *
          (AdditivePath.displacement j increment +
            ((n : ℝ) * (t : ℝ) - j) * increment j) ≤
        (scale n)⁻¹ *
          (AdditivePath.displacement j increment + increment j) := by
    change normalizedLinearPathUnbounded scale n increment t ≤
      normalizedLinearPathUnbounded scale n increment right at hpath_right
    rw [hseg_t, hseg_right, hright] at hpath_right
    simpa only [add_sub_cancel_left, one_mul] using hpath_right
  have hc : 0 < (scale n)⁻¹ := inv_pos.mpr hscale
  have hred := (mul_le_mul_iff_of_pos_left hc).mp hineq
  have hcoef : 0 < 1 - ((n : ℝ) * (t : ℝ) - j) := by linarith
  have hproduct : 0 ≤
      (1 - ((n : ℝ) * (t : ℝ) - j)) * increment j := by
    nlinarith [hred]
  have hinc : 0 ≤ increment j := by
    by_contra hnonneg
    have hneg : increment j < 0 := lt_of_not_ge hnonneg
    exact (not_le_of_gt (mul_neg_of_pos_of_neg hcoef hneg)) hproduct
  apply isNonnegativeWindowStart_of_leftSegment f left t hlt
  intro x hlx hxt
  have hxlo : (j : ℝ) ≤ (n : ℝ) * (x : ℝ) := by
    have hcast : (left : ℝ) ≤ x := NNReal.coe_le_coe.mpr hlx
    nlinarith [hleft]
  have hxhi : (n : ℝ) * (x : ℝ) ≤ (j : ℝ) + 1 := by
    have hcast : (x : ℝ) ≤ t := NNReal.coe_le_coe.mpr hxt
    nlinarith [hhi]
  have hseg_x := normalizedLinearPathUnbounded_segment scale n j
    increment x hxlo hxhi
  have hseg_left := normalizedLinearPathUnbounded_segment scale n j
    increment left (by rw [hleft]) (by rw [hleft]; linarith)
  have hterm : 0 ≤ ((n : ℝ) * (x : ℝ) - j) * increment j :=
    mul_nonneg (by linarith [hxlo]) hinc
  have hsum : AdditivePath.displacement j increment ≤
      AdditivePath.displacement j increment +
        ((n : ℝ) * (x : ℝ) - j) * increment j :=
    le_add_of_nonneg_right hterm
  have hscaled := mul_le_mul_of_nonneg_left hsum hc.le
  change normalizedLinearPathUnbounded scale n increment left ≤
    normalizedLinearPathUnbounded scale n increment x
  rw [hseg_left, hseg_x, hleft]
  simpa only [sub_self, zero_mul, add_zero] using hscaled
  exact ht

/-- An eligible polygonal window at a lattice start yields a surviving
discrete block at the same index. -/
theorem survivesNonnegative_of_isNonnegativeWindowStart_grid
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    (hscale : 0 < scale n) (start : ℕ)
    (increment : ℕ → ℝ)
    (hwindow : IsNonnegativeWindowStart
      (normalizedLinearContinuousPathUnbounded scale n increment)
      (⟨(start : ℝ) / n, div_nonneg (Nat.cast_nonneg start)
        (Nat.cast_nonneg n)⟩ : ℝ≥0)) :
    SurvivesNonnegative n (fun k => increment (start + k)) := by
  rw [SurvivesNonnegative.shift_iff]
  intro k
  let gridTime (j : ℕ) : ℝ≥0 :=
    ⟨(j : ℝ) / n, div_nonneg (Nat.cast_nonneg j) (Nat.cast_nonneg n)⟩
  have hkn : (k : ℕ) + 1 ≤ n := by omega
  have hu : gridTime ((k : ℕ) + 1) ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    change (((k : ℕ) + 1 : ℕ) : ℝ) / n ≤ 1
    exact (div_le_one (Nat.cast_pos.mpr hn)).mpr
      (by exact_mod_cast hkn)
  let u : Set.Icc (0 : ℝ≥0) 1 :=
    ⟨gridTime ((k : ℕ) + 1), ⟨bot_le, hu⟩⟩
  have hadd : gridTime start + gridTime ((k : ℕ) + 1) =
      gridTime (start + ((k : ℕ) + 1)) := by
    apply NNReal.eq
    change (start : ℝ) / n + (((k : ℕ) + 1 : ℕ) : ℝ) / n =
      ((start + ((k : ℕ) + 1) : ℕ) : ℝ) / n
    push_cast
    ring
  have hineq := hwindow u
  change normalizedLinearPathUnbounded scale n increment
      (gridTime start) ≤
    normalizedLinearPathUnbounded scale n increment
      (gridTime start + gridTime ((k : ℕ) + 1)) at hineq
  rw [hadd, normalizedLinearPathUnbounded_grid scale hn,
    normalizedLinearPathUnbounded_grid scale hn] at hineq
  exact (mul_le_mul_iff_of_pos_left (inv_pos.mpr hscale)).mp hineq

/-- The unit-time increment path starting at lattice index `start`
is the polygonal interpolation of that finite increment block. -/
theorem restrictPathToUnitInterval_shiftToZero_grid
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    (start : ℕ) (increment : ℕ → ℝ) :
    restrictPathToUnitInterval
        (shiftToZero
          (normalizedLinearContinuousPathUnbounded scale n increment)
          (⟨(start : ℝ) / n, div_nonneg (Nat.cast_nonneg start)
            (Nat.cast_nonneg n)⟩ : ℝ≥0)) =
      normalizedLinearContinuousPathFromBlock scale n
        (Combinatorics.Sequence.blockCoordinates start n increment) := by
  ext t
  rw [normalizedLinearContinuousPathFromBlock_blockCoordinates]
  exact shiftToZero_normalizedLinearContinuousPathUnbounded_eq_bounded
    scale hn start increment t

/-- Grid-start eligibility of a polygonal unit window is equivalent
to survival of the corresponding discrete length-`n` walk block. -/
theorem isNonnegativeWindowStart_grid_iff_survivesNonnegative
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    (hscale : 0 < scale n) (start : ℕ)
    (increment : ℕ → ℝ) :
    IsNonnegativeWindowStart
        (normalizedLinearContinuousPathUnbounded scale n increment)
        (⟨(start : ℝ) / n, div_nonneg (Nat.cast_nonneg start)
          (Nat.cast_nonneg n)⟩ : ℝ≥0) ↔
      SurvivesNonnegative n (fun k => increment (start + k)) := by
  constructor
  · exact survivesNonnegative_of_isNonnegativeWindowStart_grid
      scale hn hscale start increment
  · intro hsurv u
    let shifted : ℕ → ℝ := fun k => increment (start + k)
    have hgrid : ∀ k : Fin n,
        (scale n)⁻¹ * AdditivePath.displacement (k + 1) shifted ∈
          Set.Ici 0 := by
      intro k
      exact mul_nonneg (inv_nonneg.mpr hscale.le) (hsurv k)
    have hRange : Set.range
        (normalizedLinearContinuousPathIcc scale n shifted) ⊆
          Set.Ici 0 :=
      (normalizedLinearContinuousPathIcc_range_subset_iff
        scale hn (convex_Ici 0) (le_refl 0) shifted).2 hgrid
    let t : unitInterval :=
      ⟨(u.1 : ℝ), ⟨NNReal.coe_nonneg _,
        NNReal.coe_le_coe.mpr u.property.2⟩⟩
    have hnonneg : 0 ≤ normalizedLinearContinuousPathIcc
        scale n shifted t := hRange ⟨t, rfl⟩
    have hshift := shiftToZero_normalizedLinearContinuousPathUnbounded_eq_bounded
      scale hn start increment t
    rw [← hshift] at hnonneg
    have htEq : (⟨(t : ℝ), t.property.1⟩ : ℝ≥0) = u.1 := by
      apply NNReal.eq
      rfl
    rw [htEq] at hnonneg
    simpa [shiftToZero, sub_nonneg] using hnonneg

end ProbabilityTheory.RandomWalk

end
