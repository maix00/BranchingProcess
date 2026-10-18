/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Process.HittingTime

/-!
# Ceiling a time by a finite grid

The public definition and theorems in this file are:

- `ProbabilityTheory.timeGridCeiling`: for any type `X`, time functional
  $T : X \to \overline{\mathbb R}_{\ge 0}$, and finite grid
  $(r_i)_{i=0}^N$, select the least index with $T(x) \le r_i$, using $N$
  if no grid point satisfies this inequality. It is the time-threshold
  specialization of Mathlib's `MeasureTheory.hittingBtwn`.
- `ProbabilityTheory.time_le_timeGridCeiling`: if the last grid point reaches
  $T(x)$, the selected grid time is at or after $T(x)$.
- `ProbabilityTheory.timeGridCeiling_le_of_time_le`: every grid point at or
  after $T(x)$ bounds the selected index from above.
- `ProbabilityTheory.timeGridCeiling_eq_last_of_not_le`: if the grid is
  monotone and its last point is before $T(x)$, the selected index is $N$.
- `ProbabilityTheory.tendsto_timeGridCeiling_time_of_finite`: for any such
  time functional, if the grids eventually cover its finite value and have
  points arbitrarily close above it, the selected grid times converge to it.
- `ProbabilityTheory.measurable_timeGridCeiling`: measurability of the
  selected index follows from measurability of the time functional.

The statements are independent of path spaces and probability laws. The grid
selector itself uses Mathlib's general finite hitting-time construction.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal Classical

namespace ProbabilityTheory

/-- The first grid index whose time is at or after `T x`, or the last index
if no grid time reaches `T x`. This specializes `hittingBtwn` to the
threshold predicate `T x ≤ r i`. -/
noncomputable def timeGridCeiling {X : Type*} (N : ℕ)
    (r : Fin (N + 1) → ℝ≥0) (T : X → WithTop ℝ≥0) (x : X) : Fin (N + 1) :=
  hittingBtwn
    (fun i y => if T y ≤ r i then true else false)
    {true} 0 (Fin.last N) x

/-- If the final grid time reaches `T x`, the selected grid time is at or
after `T x`. -/
theorem time_le_timeGridCeiling {X : Type*} (N : ℕ)
    (r : Fin (N + 1) → ℝ≥0) (T : X → WithTop ℝ≥0) (x : X)
    (hlast : T x ≤ r (Fin.last N)) :
    T x ≤ r (timeGridCeiling N r T x) := by
  let u : Fin (N + 1) → X → Bool :=
    fun i y => if T y ≤ r i then true else false
  have hexists : ∃ i ∈ Set.Icc (0 : Fin (N + 1)) (Fin.last N),
      u i x ∈ ({true} : Set Bool) := by
    refine ⟨Fin.last N, ⟨bot_le, le_rfl⟩, ?_⟩
    change (if T x ≤ r (Fin.last N) then true else false) = true
    split_ifs
    rfl
  have hmem := hittingBtwn_mem_set (u := u) (s := ({true} : Set Bool))
    (n := (0 : Fin (N + 1))) (m := Fin.last N) (ω := x) hexists
  change (if T x ≤ r (timeGridCeiling N r T x) then true else false) = true at hmem
  split_ifs at hmem with h
  · exact h

/-- Every grid point at or after `T x` bounds the selected index from above. -/
theorem timeGridCeiling_le_of_time_le {X : Type*} (N : ℕ)
    (r : Fin (N + 1) → ℝ≥0) (T : X → WithTop ℝ≥0) (x : X)
    (i : Fin (N + 1)) (hi : T x ≤ r i) :
    timeGridCeiling N r T x ≤ i := by
  let u : Fin (N + 1) → X → Bool :=
    fun j y => if T y ≤ r j then true else false
  have hmem : u i x ∈ ({true} : Set Bool) := by
    change (if T x ≤ r i then true else false) = true
    split_ifs
    rfl
  exact hittingBtwn_le_of_mem (u := u) (s := ({true} : Set Bool))
    (n := (0 : Fin (N + 1))) (m := Fin.last N) (ω := x) (i := i)
    bot_le (Fin.le_last i) hmem

/-- If a monotone grid ends before `T x`, the selector uses its last index. -/
theorem timeGridCeiling_eq_last_of_not_le {X : Type*} (N : ℕ)
    (r : Fin (N + 1) → ℝ≥0) (hr : Monotone r)
    (T : X → WithTop ℝ≥0) (x : X)
    (hnot : ¬ T x ≤ r (Fin.last N)) :
    timeGridCeiling N r T x = Fin.last N := by
  have hnone : ¬ ∃ j ∈ Set.Icc (0 : Fin (N + 1)) (Fin.last N),
      (if T x ≤ r j then true else false) ∈ ({true} : Set Bool) := by
    rintro ⟨j, _, hj⟩
    have hjhit : T x ≤ r j := by
      change (if T x ≤ r j then true else false) = true at hj
      split_ifs at hj with hp
      exact hp
    exact hnot (hjhit.trans (WithTop.coe_le_coe.mpr (hr (Fin.le_last j))))
  unfold timeGridCeiling hittingBtwn
  simp only [ite_eq_right hnone]

/-- If monotone finite grids eventually cover a finite time and have
points arbitrarily close above it, their selected grid times converge to
that time. The time functional may be defined on any type. -/
theorem tendsto_timeGridCeiling_time_of_finite
    {X : Type*} (N : ℕ → ℕ)
    (r : ∀ n, Fin (N n + 1) → ℝ≥0) (hr : ∀ n, Monotone (r n))
    (T : X → WithTop ℝ≥0) (x : X) (τ : ℝ≥0)
    (hT : T x = τ)
    (hcover : ∀ᶠ n in Filter.atTop, τ ≤ r n (Fin.last (N n)))
    (hdense : ∀ b : ℝ≥0, τ < b →
      ∀ᶠ n in Filter.atTop, ∃ i : Fin (N n + 1), τ ≤ r n i ∧ r n i < b) :
    Filter.Tendsto (fun n => r n (timeGridCeiling (N n) (r n) T x))
      Filter.atTop (nhds τ) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    filter_upwards [hcover] with n hn
    have hlast : T x ≤ r n (Fin.last (N n)) := by
      rw [hT]
      exact WithTop.coe_le_coe.mpr hn
    have hle := time_le_timeGridCeiling (N n) (r n) T x hlast
    rw [hT] at hle
    exact lt_of_lt_of_le hb (WithTop.coe_le_coe.mp hle)
  · intro b hb
    filter_upwards [hdense b hb] with n ⟨i, hi, hib⟩
    have htime : T x ≤ r n i := by
      rw [hT]
      exact WithTop.coe_le_coe.mpr hi
    have hidx := timeGridCeiling_le_of_time_le (N n) (r n) T x i htime
    exact lt_of_le_of_lt (hr n hidx) hib

/-- The finite-grid ceiling index is measurable whenever the time functional
is measurable. -/
theorem measurable_timeGridCeiling {X : Type*} [MeasurableSpace X]
    (N : ℕ) (r : Fin (N + 1) → ℝ≥0) (T : X → WithTop ℝ≥0)
    (hT : Measurable T) : Measurable (timeGridCeiling N r T) := by
  let u : Fin (N + 1) → X → Bool :=
    fun i x => if T x ≤ r i then true else false
  have hum (i : Fin (N + 1)) : StronglyMeasurable (u i) := by
    have hset : MeasurableSet {x : X | T x ≤ r i} := hT measurableSet_Iic
    exact (Measurable.ite hset measurable_const measurable_const).stronglyMeasurable
  let ℱ := Filtration.natural u hum
  have hu : Adapted ℱ u := (Filtration.stronglyAdapted_natural hum).adapted
  have hτ : IsStoppingTime ℱ
      (fun x : X => (timeGridCeiling N r T x : WithTop (Fin (N + 1)))) := by
    exact hu.isStoppingTime_hittingBtwn (measurableSet_singleton true)
  have hfiber (i : Fin (N + 1)) :
      MeasurableSet {x : X | timeGridCeiling N r T x = i} := by
    have hi : MeasurableSet[ℱ i] {x : X | timeGridCeiling N r T x = i} := by
      simpa using hτ.measurableSet_eq i
    exact (ℱ.le i) _ hi
  intro s hs
  have heq : (timeGridCeiling N r T) ⁻¹' s =
      ⋃ i : s, {x : X | timeGridCeiling N r T x = i} := by
    ext x
    simp
  rw [heq]
  exact MeasurableSet.iUnion (fun i => hfiber i)

end ProbabilityTheory

end
