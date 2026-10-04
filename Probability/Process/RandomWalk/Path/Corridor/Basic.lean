/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Scaling

/-!
# Corridors for scaled walk paths

Corridor membership, grid restriction, and corridor energy are deterministic
properties of real-valued paths.
-/

open MeasureTheory Set

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- A path stays strictly between two boundaries at every time in `times`. -/
def InOpenCorridorOn (times : Set ℝ) (lower upper path : ℝ → ℝ) : Prop :=
  ∀ t ∈ times, lower t < path t ∧ path t < upper t

/-- A path stays weakly between two boundaries at every time in `times`. -/
def InClosedCorridorOn (times : Set ℝ) (lower upper path : ℝ → ℝ) : Prop :=
  ∀ t ∈ times, lower t ≤ path t ∧ path t ≤ upper t

/-- The open corridor on the unit time interval used in the original
Mogulskii statement. -/
abbrev InOpenCorridor := InOpenCorridorOn (Icc (0 : ℝ) 1)

/-- Closed corridor membership on the unit time interval. -/
abbrev InClosedCorridor := InClosedCorridorOn (Icc (0 : ℝ) 1)

/-- Open corridor membership checked at the positive points of the `n`-step
grid. -/
def InOpenCorridorOnGrid (scale : ℕ → ℝ) (n : ℕ)
    (lower upper : ℝ → ℝ) (increment : ℕ → ℝ) : Prop :=
  ∀ k : Fin n,
    let t := ((k.val + 1 : ℕ) : ℝ) / n
    lower t < normalizedStepPath scale n increment t ∧
      normalizedStepPath scale n increment t < upper t

/-- Closed corridor membership checked at the positive points of the `n`-step
grid.  Unlike full path-space membership, this is a finite predicate. -/
def InClosedCorridorOnGrid (scale : ℕ → ℝ) (n : ℕ)
    (lower upper : ℝ → ℝ) (increment : ℕ → ℝ) : Prop :=
  ∀ k : Fin n,
    let t := ((k.val + 1 : ℕ) : ℝ) / n
    lower t ≤ normalizedStepPath scale n increment t ∧
      normalizedStepPath scale n increment t ≤ upper t

theorem InOpenCorridorOn.closed {times : Set ℝ} {lower upper path : ℝ → ℝ}
    (h : InOpenCorridorOn times lower upper path) :
    InClosedCorridorOn times lower upper path := by
  intro t ht
  exact ⟨(h t ht).1.le, (h t ht).2.le⟩

/-- If two corridors have pointwise ordered boundaries, `lower' ≤ lower` and
`upper ≤ upper'`, then an open excursion in the `lower, upper` corridor is an
open excursion in the `lower', upper'` corridor. -/
theorem InOpenCorridorOn.mono {times : Set ℝ} {lower upper lower' upper' path : ℝ → ℝ}
    (hlower : ∀ t, lower' t ≤ lower t) (hupper : ∀ t, upper t ≤ upper' t)
    (h : InOpenCorridorOn times lower upper path) :
    InOpenCorridorOn times lower' upper' path := by
  intro t ht
  exact ⟨(hlower t).trans_lt (h t ht).1, (h t ht).2.trans_le (hupper t)⟩

/-- If two closed corridors have pointwise ordered boundaries, `lower' ≤ lower`
and `upper ≤ upper'`, then a closed excursion in the `lower, upper` corridor is
a closed excursion in the `lower', upper'` corridor. -/
theorem InClosedCorridorOn.mono {times : Set ℝ} {lower upper lower' upper' path : ℝ → ℝ}
    (hlower : ∀ t, lower' t ≤ lower t) (hupper : ∀ t, upper t ≤ upper' t)
    (h : InClosedCorridorOn times lower upper path) :
    InClosedCorridorOn times lower' upper' path := by
  intro t ht
  exact ⟨(hlower t).trans (h t ht).1, (h t ht).2.trans (hupper t)⟩

/-- For `0 < ε`, a strict excursion of the shrunk corridor `[f + ε, g - ε]` is a
strict excursion of `[f, g]`. -/
theorem InOpenCorridorOn.of_shrunk {times : Set ℝ} {lower upper path : ℝ → ℝ} {ε : ℝ}
    (hε : 0 < ε)
    (h : InOpenCorridorOn times (fun t => lower t + ε) (fun t => upper t - ε) path) :
    InOpenCorridorOn times lower upper path :=
  h.mono (fun _ => by linarith) (fun _ => by linarith)

/-- For `0 < ε`, a closed excursion of `[f, g]` is a strict excursion of the
relaxed corridor `[f - ε, g + ε]`. -/
theorem InOpenCorridorOn.relax {times : Set ℝ} {lower upper path : ℝ → ℝ} {ε : ℝ}
    (hε : 0 < ε) (h : InClosedCorridorOn times lower upper path) :
    InOpenCorridorOn times (fun t => lower t - ε) (fun t => upper t + ε) path := by
  intro t ht
  obtain ⟨hleft, hright⟩ := h t ht
  exact ⟨by linarith, by linarith⟩

/-- For a step path and constant boundaries, checking the positive grid is
equivalent to checking the whole unit interval. Time zero contributes exactly
the requirement that the constant interval contain zero. -/
theorem inClosedCorridor_const_iff_grid
    (scale : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    {lower upper : ℝ} (hlower : lower ≤ 0) (hupper : 0 ≤ upper)
    (increment : ℕ → ℝ) :
    InClosedCorridor (fun _ => lower) (fun _ => upper)
        (normalizedStepPath scale n increment) ↔
      InClosedCorridorOnGrid scale n (fun _ => lower) (fun _ => upper)
        increment := by
  constructor
  · intro h k
    apply h
    constructor
    · positivity
    · rw [div_le_one (by positivity)]
      exact_mod_cast Nat.succ_le_iff.2 k.isLt
  · intro h t ht
    have hnt : (n : ℝ) * t ≤ n := by
      calc
        (n : ℝ) * t ≤ (n : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left ht.2 (Nat.cast_nonneg n)
        _ = n := by ring
    have hfloor : ⌊(n : ℝ) * t⌋₊ ≤ n := by
      exact Nat.floor_le_of_le hnt
    generalize hm : ⌊(n : ℝ) * t⌋₊ = m at hfloor ⊢
    cases m with
    | zero =>
        simpa [normalizedStepPath, hm] using And.intro hlower hupper
    | succ k =>
        have hk : k < n := Nat.succ_le_iff.1 hfloor
        have hg := h ⟨k, hk⟩
        dsimp only at hg
        rw [normalizedStepPath_grid scale hn] at hg
        rw [normalizedStepPath, hm]
        exact hg

end ProbabilityTheory.RandomWalk
