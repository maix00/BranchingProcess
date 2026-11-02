/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.LinearAlgebra.AffineSpace.AffineMap
public import Mathlib.Topology.UnitInterval

/-!
# Affine time coordinates on the unit interval

This module builds on Mathlib's `unitInterval.toNNReal` coordinate. It adds
the normalized affine parametrization of nonnegative time intervals, the
identity real-valued coordinate when the unit interval is used as a time
domain, and the clamped coordinate for a decomposition into unit-time blocks.

## Public declarations

* `unitInterval.exists_mul_eq`: if `0 < length` and `t ≤ length`, then
  `length * unitInterval.toNNReal u = t` for some `u : unitInterval`.
* `unitInterval.exists_add_mul_eq`: if `start ≤ t ≤ start + length` and
  `0 < length`, then `start + length * unitInterval.toNNReal u = t` for some
  `u : unitInterval`.
* `unitInterval.clock`: the identity real-valued time coordinate
  `unitInterval → ℝ`, with `unitInterval.clock t = (t : ℝ)`.
* `unitInterval.terminalSegmentParameter`: the affine map
  `(start,t) ↦ start + (1-start)t` from the unit square to the terminal
  segment `[start,1]`; `coe_terminalSegmentParameter_eq_lineMap` identifies
  its real coordinate with Mathlib's `AffineMap.lineMap`,
  `terminalSegmentParameter_zero` and `terminalSegmentParameter_top` give its
  endpoint values, and `continuous_terminalSegmentParameter` and
  `continuous_terminalSegmentParameter_left` give continuity in each input.
* `unitInterval.blockParameter`: the clamped coordinate of time `t` in the
  unit block beginning at integer `n`, defined by projection of `t - n` onto
  `[0,1]` (equivalently, `max 0 (min 1 (t - n))`).
* `unitInterval.coe_blockParameter`: the real-valued formula for this
  projected coordinate.
* `unitInterval.monotone_blockParameter` and
  `unitInterval.continuous_blockParameter`: for each `n`, the block coordinate
  is monotone and continuous in `t`.
* `unitInterval.blockParameter_eq_sub`: if `floor t = n`, then its value is
  `t - n`; if `n < floor t`, its value is `⊤`; if `floor t < n`, its value
  is `⊥`.
* `unitInterval.sum_blockParameter_eq_time` and
  `unitInterval.sum_blockParameter_increment_eq_time_sub`: the block lengths
  satisfy
  `∑_{n=0}^{floor t} (blockParameter n t : ℝ) = t` and
  `∑_{n=0}^{floor t} ((blockParameter n t : ℝ) - (blockParameter n s : ℝ))
  = t - s` when `s ≤ t`.

The affine and clamped coordinates, together with their finite-sum identity,
are
\[
  \tau_a(u):=a+(1-a)u,\qquad
  \theta_n(t):=\max\{0,\min\{1,t-n\}\},
\]
\[
  \sum_{n=0}^{\lfloor t\rfloor}\theta_n(t)=t,
  \qquad
  \sum_{n=0}^{\lfloor t\rfloor}
    \bigl(\theta_n(t)-\theta_n(s)\bigr)=t-s\quad(0\le s\le t),
  \qquad s,t\in\mathbb R_{\ge0}.
\]
-/

@[expose] public section

namespace unitInterval

open scoped NNReal

/-- Every point of a nonnegative interval is reached by the normalized
unit-interval clock when the interval has positive length. -/
theorem exists_mul_eq (length t : NNReal)
    (hlength : 0 < length) (ht : t ≤ length) :
    ∃ u : unitInterval, length * toNNReal u = t := by
  have hreal : 0 < (length : ℝ) := NNReal.coe_pos.mpr hlength
  have htle : (t : ℝ) ≤ (length : ℝ) := NNReal.coe_le_coe.mpr ht
  let u : unitInterval := ⟨(t : ℝ) / length, by
    constructor
    · positivity
    · exact (div_le_one hreal).mpr htle⟩
  refine ⟨u, ?_⟩
  apply NNReal.coe_injective
  change (length : ℝ) * ((t : ℝ) / length) = t
  field_simp

/-- Every point of a translated nonnegative interval is reached by its
normalized affine clock. -/
theorem exists_add_mul_eq (start length t : NNReal)
    (hlength : 0 < length) (hstart : start ≤ t)
    (hend : t ≤ start + length) :
    ∃ u : unitInterval, start + length * toNNReal u = t := by
  have hdelta : t - start ≤ length := by
    exact tsub_le_iff_left.mpr hend
  obtain ⟨u, hu⟩ := exists_mul_eq length (t - start)
    hlength hdelta
  refine ⟨u, ?_⟩
  rw [hu]
  simpa [add_comm] using tsub_add_cancel_of_le hstart

/-- The identity real-valued clock on the unit interval. -/
def clock (t : unitInterval) : ℝ := t

/-- Reparametrize the terminal interval `[start,1]` by the unit interval.
This is the affine line map from `start` to the top endpoint. -/
def terminalSegmentParameter (start t : unitInterval) : unitInterval :=
  ⟨(start : ℝ) + (1 - (start : ℝ)) * (t : ℝ), by
    constructor
    · have hs := start.property.1
      have ht := t.property.1
      have hsu := start.property.2
      nlinarith
    · have hs := start.property.1
      have hsu := start.property.2
      have ht := t.property.1
      have htu := t.property.2
      nlinarith⟩

theorem coe_terminalSegmentParameter_eq_lineMap (start t : unitInterval) :
    (terminalSegmentParameter start t : ℝ) =
      AffineMap.lineMap (start : ℝ) 1 (t : ℝ) := by
  simp only [terminalSegmentParameter, AffineMap.lineMap_apply_ring]
  ring_nf

@[simp] theorem terminalSegmentParameter_zero (start : unitInterval) :
    terminalSegmentParameter start 0 = start := by
  apply Subtype.ext
  simp [terminalSegmentParameter]

@[simp] theorem terminalSegmentParameter_top (start : unitInterval) :
    terminalSegmentParameter start ⊤ = ⊤ := by
  apply Subtype.ext
  simp [terminalSegmentParameter]

/-- For fixed `start`, the terminal-segment parameter is continuous in `t`. -/
theorem continuous_terminalSegmentParameter (start : unitInterval) :
    Continuous (terminalSegmentParameter start) := by
  have hreal : Continuous
      (fun t : unitInterval =>
        (start : ℝ) + (1 - (start : ℝ)) * (t : ℝ)) := by
    fun_prop
  exact hreal.subtype_mk _

/-- For fixed `t`, the terminal-segment parameter is continuous in `start`. -/
theorem continuous_terminalSegmentParameter_left (t : unitInterval) :
    Continuous (fun start : unitInterval => terminalSegmentParameter start t) := by
  have hreal : Continuous
      (fun start : unitInterval =>
        (start : ℝ) + (1 - (start : ℝ)) * (t : ℝ)) := by
    fun_prop
  exact hreal.subtype_mk _

/-- The coordinate in the unit interval of time `t` relative to the block
beginning at the integer `n`; blocks before `n` have coordinate `1`, and
blocks after `n` have coordinate `0`. -/
noncomputable def blockParameter (n : ℕ) (t : ℝ≥0) : unitInterval :=
  Set.projIcc 0 1 (by norm_num) ((t : ℝ) - n)

@[simp] theorem coe_blockParameter (n : ℕ) (t : ℝ≥0) :
    (blockParameter n t : ℝ) = max 0 (min 1 ((t : ℝ) - n)) := rfl

theorem monotone_blockParameter (n : ℕ) :
    Monotone (blockParameter n) := by
  intro s t hst
  apply Subtype.coe_le_coe.mpr
  have hsub : Monotone (fun t : ℝ≥0 => (t : ℝ) - n) := by
    intro s t hst
    exact sub_le_sub_right (show (s : ℝ) ≤ t from by exact_mod_cast hst) _
  exact ((Set.monotone_projIcc (a := 0) (b := 1) (by norm_num)).comp hsub) hst

theorem continuous_blockParameter (n : ℕ) :
    Continuous (blockParameter n) := by
  exact Continuous.subtype_mk (by fun_prop)
    (fun t => (blockParameter n t).property)

theorem blockParameter_eq_sub {t : ℝ≥0} {n : ℕ}
    (hfloor : Nat.floor (t : ℝ) = n) :
    blockParameter n t = ⟨(t : ℝ) - n, by
      constructor
      · have h := Nat.floor_le (show (0 : ℝ) ≤ (t : ℝ) from t.2)
        rw [hfloor] at h
        linarith
      · have h := Nat.lt_floor_add_one (t : ℝ)
        rw [hfloor] at h
        linarith⟩ := by
  apply Subtype.ext
  dsimp [blockParameter]
  have hfloorle : (n : ℝ) ≤ (t : ℝ) := by
    have h := Nat.floor_le (show (0 : ℝ) ≤ (t : ℝ) from t.2)
    rw [hfloor] at h
    exact h
  have hfloorlt : (t : ℝ) < n + 1 := by
    have h := Nat.lt_floor_add_one (t : ℝ)
    rw [hfloor] at h
    exact h
  change (blockParameter n t : ℝ) = (t : ℝ) - n
  rw [coe_blockParameter, min_eq_right (show (t : ℝ) - n ≤ 1 by linarith),
    max_eq_right (show 0 ≤ (t : ℝ) - n by linarith)]

theorem blockParameter_eq_top_of_lt_floor {t : ℝ≥0} {n : ℕ}
    (h : n < Nat.floor (t : ℝ)) :
    blockParameter n t = ⊤ := by
  apply Subtype.ext
  have hfloor : (n : ℝ) + 1 ≤ (t : ℝ) := by
    have hn : n + 1 ≤ Nat.floor (t : ℝ) := Nat.succ_le_of_lt h
    have hle := Nat.floor_le (show (0 : ℝ) ≤ (t : ℝ) from t.2)
    exact le_trans (by exact_mod_cast hn) hle
  change (blockParameter n t : ℝ) = 1
  rw [coe_blockParameter,
    min_eq_left (show 1 ≤ (t : ℝ) - n by linarith)]
  norm_num

theorem blockParameter_eq_bot_of_floor_lt {t : ℝ≥0} {n : ℕ}
    (h : Nat.floor (t : ℝ) < n) :
    blockParameter n t = ⊥ := by
  apply Subtype.ext
  have hupper : (t : ℝ) < (n : ℝ) := by
    have hfloor := Nat.lt_floor_add_one (t : ℝ)
    have hn : Nat.floor (t : ℝ) + 1 ≤ n := Nat.succ_le_of_lt h
    have hn' : (Nat.floor (t : ℝ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  change (blockParameter n t : ℝ) = 0
  rw [coe_blockParameter, min_eq_right (show (t : ℝ) - n ≤ 1 by linarith),
    max_eq_left (show (t : ℝ) - n ≤ 0 by linarith)]

/-- The lengths of the clamped pieces of `[0,t]` add to `t`. -/
theorem sum_blockParameter_eq_time (t : ℝ≥0) :
    (∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1),
      (blockParameter n t : ℝ)) = (t : ℝ) := by
  have hfull :
      (∑ n ∈ Finset.range (Nat.floor (t : ℝ)),
        (blockParameter n t : ℝ)) = (Nat.floor (t : ℝ) : ℝ) := by
    calc
      (∑ n ∈ Finset.range (Nat.floor (t : ℝ)),
          (blockParameter n t : ℝ)) =
          ∑ n ∈ Finset.range (Nat.floor (t : ℝ)), (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro n hn
            have hn' : n < Nat.floor (t : ℝ) := Finset.mem_range.mp hn
            rw [blockParameter_eq_top_of_lt_floor hn']
            rfl
      _ = (Nat.floor (t : ℝ) : ℝ) := by simp
  have hcurrent :
      (blockParameter (Nat.floor (t : ℝ)) t : ℝ) =
        (t : ℝ) - (Nat.floor (t : ℝ) : ℝ) := by
    exact congrArg Subtype.val
      (blockParameter_eq_sub (t := t) (n := Nat.floor (t : ℝ)) rfl)
  rw [Finset.sum_range_succ, hfull, hcurrent]
  ring

/-- For `s ≤ t`, all block-coordinate differences up to `floor t` sum to the
elapsed time `t - s`. -/
theorem sum_blockParameter_increment_eq_time_sub
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1),
      ((blockParameter n t : ℝ) - (blockParameter n s : ℝ))) =
        (t : ℝ) - (s : ℝ) := by
  have hfloor : Nat.floor (s : ℝ) ≤ Nat.floor (t : ℝ) := by
    apply Nat.floor_mono
    exact_mod_cast hst
  have hs : Nat.floor (s : ℝ) < Nat.floor (t : ℝ) + 1 :=
    lt_of_le_of_lt hfloor (Nat.lt_succ_self _)
  have hsumS := sum_blockParameter_eq_time s
  have hsumT := sum_blockParameter_eq_time t
  have hsumS' :
      (∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1),
        (blockParameter n s : ℝ)) = (s : ℝ) := by
    calc
      (∑ n ∈ Finset.range (Nat.floor (t : ℝ) + 1),
          (blockParameter n s : ℝ)) =
          ∑ n ∈ Finset.range (Nat.floor (s : ℝ) + 1),
            (blockParameter n s : ℝ) := by
              symm
              apply Finset.sum_subset
                (Finset.range_mono (Nat.succ_le_of_lt hs))
              intro n hn hnnot
              have hn' : Nat.floor (s : ℝ) < n := by
                by_contra h
                have hnle : n ≤ Nat.floor (s : ℝ) := Nat.le_of_not_gt h
                exact hnnot (Finset.mem_range.mpr (Nat.lt_succ_of_le hnle))
              rw [blockParameter_eq_bot_of_floor_lt hn']
              simp
      _ = (s : ℝ) := hsumS
  rw [Finset.sum_sub_distrib, hsumT, hsumS']

end unitInterval

end
