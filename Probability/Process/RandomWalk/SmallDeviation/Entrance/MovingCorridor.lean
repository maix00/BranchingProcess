/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Donsker.Entrance.InteriorDiffusive
/-!
# Moving-boundary entrance corridors

The public declarations in this file are:

For increments $\xi=(\xi_i)_{i\ge0}$, put $S_j=\sum_{i=0}^{j-1}\xi_i$.

- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.movingCorridorEvent`:
  the paths satisfying $cj/\Delta^2\le x+S_j\le\Delta+cj/\Delta^2$
  for every $1\le j\le n$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Entrance.finiteInteriorEvent_subset_movingCorridorEvent`:
  if $\Delta>0$, $c\ge0$, and $n\le\Delta^2$, the constant interior
  corridor event is contained in the moving-boundary corridor event.

The event and deterministic inclusion are the corridor part of Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*
(master's thesis, Fudan University, 2026), Appendix A.2, Lemma A.7, used in
Chapter 3, Lemma 3.5. The terminal-window condition is specified separately
by the result that needs it.
-/

@[expose] public section

open ProbabilityTheory

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

/-- The finite moving-boundary corridor with no terminal-window restriction. -/
def movingCorridorEvent (n : ℕ) (width drift start : ℝ) :
    Set (ℕ → ℝ) :=
  {increment |
    ∀ k : Fin n,
      drift * ((k.val + 1 : ℕ) : ℝ) / width ^ 2 ≤
        start + AdditivePath.displacement (k + 1) increment ∧
      start + AdditivePath.displacement (k + 1) increment ≤
        width + drift * ((k.val + 1 : ℕ) : ℝ) / width ^ 2}

/-- The constant interior corridor used by the Donsker argument satisfies
the moving-boundary path constraints whenever its horizon is at most
the square of the width. -/
theorem finiteInteriorEvent_subset_movingCorridorEvent
    {n : ℕ} {width drift start : ℝ}
    (hwidth : 0 < width) (hdrift : 0 ≤ drift)
    (hn : (n : ℝ) ≤ width ^ 2) :
    FunctionalLimit.Donsker.Entrance.finiteInteriorEvent n width drift start ⊆
      movingCorridorEvent n width drift start := by
  intro increment hinc
  have hwidthSq : 0 < width ^ 2 := sq_pos_of_pos hwidth
  unfold movingCorridorEvent
  intro k
  have hkNat : k.val + 1 ≤ n := Nat.succ_le_of_lt k.isLt
  have hk : (((k.val + 1 : ℕ) : ℝ)) ≤ width ^ 2 :=
    (Nat.cast_le.mpr hkNat).trans hn
  have hshiftNonneg :
      0 ≤ drift * ((k.val + 1 : ℕ) : ℝ) / width ^ 2 :=
    div_nonneg (mul_nonneg hdrift (Nat.cast_nonneg _)) hwidthSq.le
  have hshiftLe :
      drift * ((k.val + 1 : ℕ) : ℝ) / width ^ 2 ≤ drift := by
    apply (div_le_iff₀ hwidthSq).2
    exact mul_le_mul_of_nonneg_left hk hdrift
  have hgrid := hinc.1 k
  exact ⟨hshiftLe.trans hgrid.1,
    hgrid.2.trans (le_add_of_nonneg_right hshiftNonneg)⟩

end ProbabilityTheory.RandomWalk.SmallDeviation.Entrance

end
