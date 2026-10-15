/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Data.ZMod.Basic
public import Algebra.BigOperators.PartialSum
public import Mathlib.Tactic.Ring

/-!
# Cyclic reindexing of finite vectors

The public declarations in this file are:

- `Fin.cyclicCoordinateReindex`: the equivalence $i\mapsto(k+i)\bmod n$
  of `Fin n` for $n>0$.
- `Fin.cyclicCoordinateReindex_val`: its value is $(k+i)\bmod n$.
- `Fin.cyclicCoordinateReindex_eq_of_add_lt`: before wraparound it is $k+i$.
- `Fin.cyclicCoordinateReindex_eq_of_le_add`: after wraparound it is $k+i-n$.
- `Fin.cyclicPartialSum_succ_eq_add_reindexedIncrement`: the next rotated
  partial sum adds the cyclically reindexed increment.
- `Fin.partialSum_cyclicCoordinateReindex`: the partial sums of reindexed
  increments equal the cyclic rotation of the original partial-sum path.

The same reindexing is used for finite random-walk path rotations in
M. Bauer, C. Godrèche, and J.-M. Luck, *Statistics of persistent events
in the binomial random walk: Will the drunken sailor hit the sober man?*,
Appendix A, equation (A.3) (arXiv:cond-mat/9905252).
-/

@[expose] public section

namespace Fin

/-- The cyclic coordinate permutation starting at increment `k`: addition
by `k` on `ZMod n`, transported to `Fin n`. -/
noncomputable def cyclicCoordinateReindex {n : ℕ} (hn : 0 < n)
    (k : Fin n) : Fin n ≃ Fin n := by
  letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let e : Fin n ≃+* ZMod n := ZMod.finEquiv n
  exact e.toEquiv.trans ((Equiv.addLeft (e k)).trans e.toEquiv.symm)

/-- The value of cyclic reindexing is addition modulo `n`. -/
theorem cyclicCoordinateReindex_val {n : ℕ} (hn : 0 < n)
    (k i : Fin n) :
    (cyclicCoordinateReindex hn k i).val = (k.val + i.val) % n := by
  cases n with
  | zero => omega
  | succ n =>
    change (((ZMod.finEquiv (n + 1)).symm
        ((ZMod.finEquiv (n + 1)) k + (ZMod.finEquiv (n + 1)) i)).val) = _
    rw [← (ZMod.finEquiv (n + 1)).map_add,
      RingEquiv.symm_apply_apply]
    exact Fin.val_add k i

/-- Before wrapping around, cyclic reindexing is ordinary addition. -/
theorem cyclicCoordinateReindex_eq_of_add_lt {n : ℕ} (hn : 0 < n)
    (k i : Fin n) (h : k.val + i.val < n) :
    cyclicCoordinateReindex hn k i = ⟨k.val + i.val, h⟩ := by
  apply Fin.ext
  rw [cyclicCoordinateReindex_val]
  exact Nat.mod_eq_of_lt h

/-- After wrapping around, cyclic reindexing subtracts `n`. -/
theorem cyclicCoordinateReindex_eq_of_le_add {n : ℕ} (hn : 0 < n)
    (k i : Fin n) (h : n ≤ k.val + i.val) :
    cyclicCoordinateReindex hn k i = ⟨k.val + i.val - n, by omega⟩ := by
  apply Fin.ext
  rw [cyclicCoordinateReindex_val]
  rw [Nat.mod_eq_sub_mod h]
  exact Nat.mod_eq_of_lt (by omega)

/-- One more increment in the cyclic partial-sum path is the increment at
the corresponding cyclic coordinate. This keeps the `n` increment indices
separate from the `n + 1` path knots. -/
theorem cyclicPartialSum_succ_eq_add_reindexedIncrement {n : ℕ}
    (hn : 0 < n) (x : Fin n → ℝ) (k : Fin n) (j : Fin n) :
    cyclicPartialSum (Fin.partialSum x) k j.succ =
      cyclicPartialSum (Fin.partialSum x) k j.castSucc +
        x (cyclicCoordinateReindex hn k j) := by
  rcases lt_trichotomy (k.val + j.val) n with hlt | heq | hgt
  · have hcurr : k.val + j.val ≤ n := Nat.le_of_lt hlt
    have hnext : k.val + j.succ.val ≤ n := by
      rw [Fin.val_succ]
      omega
    let a : Fin n := ⟨k.val + j.val, hlt⟩
    have hstart : (⟨k.val + j.val, Nat.lt_succ_of_le hcurr⟩ : Fin (n + 1)) =
        a.castSucc := by
      apply Fin.ext
      rfl
    have hend : (⟨k.val + j.succ.val, Nat.lt_succ_of_le hnext⟩ : Fin (n + 1)) =
        a.succ := by
      apply Fin.ext
      simp [a, Fin.val_succ]
      omega
    have hrot : cyclicCoordinateReindex hn k j = a := by
      apply Fin.ext
      simp [a, cyclicCoordinateReindex_val, Nat.mod_eq_of_lt hlt]
    have hp := Fin.partialSum_succ x a
    simp only [cyclicPartialSum, Fin.val_castSucc, dite_eq_left hnext,
      dite_eq_left hcurr]
    rw [hend, hstart, hrot, hp]
    ring
  · have hcurr : k.val + j.val ≤ n := by omega
    have hnext : ¬ k.val + j.succ.val ≤ n := by
      rw [Fin.val_succ]
      omega
    let zero : Fin n := ⟨0, hn⟩
    have hcurrIdx :
        (⟨k.val + j.val, Nat.lt_succ_of_le hcurr⟩ : Fin (n + 1)) = Fin.last n := by
      apply Fin.ext
      simp [heq]
    have hnextIdx :
        (⟨k.val + j.succ.val - n, by omega⟩ : Fin (n + 1)) =
          zero.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      simp [zero]
      omega
    have hrot : cyclicCoordinateReindex hn k j = zero := by
      apply Fin.ext
      simp [cyclicCoordinateReindex_val, heq, zero]
    have hone : Fin.partialSum x zero.succ = x zero := by
      simpa [zero] using Fin.partialSum_succ x zero
    simp only [cyclicPartialSum, Fin.val_castSucc, dite_eq_right hnext,
      dite_eq_left hcurr]
    rw [hnextIdx, hcurrIdx, hrot, hone]
  · have hcurr : ¬ k.val + j.val ≤ n := by omega
    have hnext : ¬ k.val + j.succ.val ≤ n := by
      rw [Fin.val_succ]
      omega
    let m : ℕ := k.val + j.val - n
    have hm : m < n := by
      dsimp [m]
      have hkn := k.isLt
      have hjn := j.isLt
      omega
    let a : Fin n := ⟨m, hm⟩
    have hcurrIdx :
        (⟨k.val + j.val - n, by omega⟩ : Fin (n + 1)) = a.castSucc := by
      apply Fin.ext
      simp [a, m]
    have hnextIdx :
        (⟨k.val + j.succ.val - n, by omega⟩ : Fin (n + 1)) = a.succ := by
      apply Fin.ext
      simp only [Fin.val_succ]
      dsimp [a, m]
      omega
    have hmod : (k.val + j.val) % n = m := by
      have hmodle : n ≤ k.val % n + j.val % n := by
        rw [Nat.mod_eq_of_lt k.isLt, Nat.mod_eq_of_lt j.isLt]
        omega
      have hsum := Nat.add_mod_add_of_le_add_mod hmodle
      rw [Nat.mod_eq_of_lt k.isLt, Nat.mod_eq_of_lt j.isLt] at hsum
      dsimp [m]
      omega
    have hrot : cyclicCoordinateReindex hn k j = a := by
      apply Fin.ext
      simp [a, cyclicCoordinateReindex_val, hmod]
    have hp := Fin.partialSum_succ x a
    simp only [cyclicPartialSum, Fin.val_castSucc, dite_eq_right hnext,
      dite_eq_right hcurr]
    rw [hnextIdx, hcurrIdx, hrot, hp]
    ring

/-- Partial sums of a cyclically reindexed finite vector are the cyclic
rotation of its original partial-sum path. -/
theorem partialSum_cyclicCoordinateReindex {n : ℕ}
    (hn : 0 < n) (x : Fin n → ℝ) (k : Fin n) (j : Fin (n + 1)) :
    Fin.partialSum (fun i => x (cyclicCoordinateReindex hn k i)) j =
      cyclicPartialSum (Fin.partialSum x) k j := by
  induction j using Fin.induction with
  | zero =>
    have hk : k.val ≤ n := Nat.le_of_lt k.isLt
    have hidx : (⟨k.val, Nat.lt_succ_of_le hk⟩ : Fin (n + 1)) = k.castSucc := by
      apply Fin.ext
      rfl
    simp [cyclicPartialSum, Fin.partialSum_zero, hk, hidx]
  | succ j ih =>
    rw [Fin.partialSum_succ, ih,
      cyclicPartialSum_succ_eq_add_reindexedIncrement hn x k j]


end Fin

end
