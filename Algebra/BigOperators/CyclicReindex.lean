/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Algebra.BigOperators.PartialSum
public import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.Abel

/-!
# Cyclic reindexing of finite vectors

## Public declarations

- `Fin.finCycle_val`: Mathlib's permutation satisfies
  $(\operatorname{finCycle}(k)(i)).\mathrm{val}=(k+i)\bmod n$.
- `Fin.cyclicPartialSum_succ_eq_add_finCycleIncrement`: one more increment
  in a cyclic partial-sum path.
- `Fin.partialSum_finCycle`: partial sums after reindexing by Mathlib's
  `finCycle` satisfy
  $\sum_{r<j}x_{\operatorname{finCycle}(k)(r)}=
  \operatorname{cyclicPartialSum}(\operatorname{partialSum}(x),k,j)$.
- `Fin.partialSum_finCycleBlock`: the partial sum over a consecutive block
  is the difference between the cyclic path at that block's endpoints.
- `Fin.removeLinearDrift` and `Fin.cyclicPartialSum_removeLinearDrift`:
  for $D_d(s)_j=s_j-j\cdot d$, cyclic partial sums satisfy
  $\operatorname{cyclicPartialSum}(D_d(s),k,j)=
  \operatorname{cyclicPartialSum}(s,k,j)-j\cdot d$.

The cyclic path rotation is used in the event decomposition in Appendix A,
equation (A.3) and the argument immediately following it, of M. Bauer,
C. Godrèche, and J.-M. Luck, *Statistics of persistent events in the binomial
random walk: Will the drunken sailor hit the sober man?*, *Journal of
Statistical Physics* 96 (1999), 963--1019, arXiv:cond-mat/9905252.
-/

@[expose] public section

namespace Fin

variable {G : Type*} [AddCommGroup G]

/-- The value of Mathlib's cyclic permutation is addition modulo `n`. -/
theorem finCycle_val {n : ℕ} (k i : Fin n) :
    (finCycle k i).val = (k.val + i.val) % n := by
  rw [finCycle_apply, Fin.val_add]
  rw [Nat.add_comm i.val k.val]

/-- One more increment in the cyclic partial-sum path is the increment at
the corresponding cyclic coordinate. This keeps the `n` increment indices
separate from the `n + 1` path knots. -/
theorem cyclicPartialSum_succ_eq_add_finCycleIncrement {n : ℕ}
    (x : Fin n → G) (k : Fin n) (j : Fin n) :
    cyclicPartialSum (Fin.partialSum x) k j.succ =
      cyclicPartialSum (Fin.partialSum x) k j.castSucc +
        x (finCycle k j) := by
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le k.val) k.isLt
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
    have hrot : finCycle k j = a := by
      apply Fin.ext
      rw [finCycle_val]
      simp [a, Nat.mod_eq_of_lt hlt]
    have hp := Fin.partialSum_succ x a
    simp only [cyclicPartialSum, Fin.val_castSucc, dite_eq_left hnext,
      dite_eq_left hcurr]
    rw [hend, hstart, hrot, hp]
    abel
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
    have hrot : finCycle k j = zero := by
      apply Fin.ext
      rw [finCycle_val]
      simp [heq, zero]
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
      rw [Nat.mod_eq_sub_mod (by omega : n ≤ k.val + j.val)]
      dsimp [m]
      exact Nat.mod_eq_of_lt (by
        have hkn := k.isLt
        have hjn := j.isLt
        omega)
    have hrot : finCycle k j = a := by
      apply Fin.ext
      rw [finCycle_val]
      simp [a, hmod]
    have hp := Fin.partialSum_succ x a
    simp only [cyclicPartialSum, Fin.val_castSucc, dite_eq_right hnext,
      dite_eq_right hcurr]
    rw [hnextIdx, hcurrIdx, hrot, hp]
    abel

/-- Partial sums of a cyclically reindexed finite vector are the cyclic
rotation of its original partial-sum path. -/
theorem partialSum_finCycle {n : ℕ}
    (x : Fin n → G) (k : Fin n) (j : Fin (n + 1)) :
    Fin.partialSum (fun i => x (finCycle k i)) j =
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
      cyclicPartialSum_succ_eq_add_finCycleIncrement x k j]

/-- A block of the rotated increment vector has partial sums given by
differences of the rotated path. -/
theorem partialSum_finCycleBlock {n : ℕ}
    (x : Fin n → G) (k : Fin n)
    (start length : ℕ) (hbound : start + length ≤ n)
    (t : Fin (length + 1)) :
    Fin.partialSum
      (fun i : Fin length =>
        x (finCycle k ⟨start + i.val, by omega⟩)) t =
      cyclicPartialSum (Fin.partialSum x) k
        ⟨start + t.val, by omega⟩ -
        cyclicPartialSum (Fin.partialSum x) k ⟨start, by omega⟩ := by
  let y : Fin n → G := fun i => x (finCycle k i)
  change Fin.partialSum (fun i : Fin length => y ⟨start + i.val, by omega⟩) t = _
  rw [Fin.partialSum_offset y start length hbound t,
    Fin.partialSum_finCycle x k,
    Fin.partialSum_finCycle x k]

/-- Subtract the elapsed-time multiple of a fixed increment from a finite
partial-sum path. -/
def removeLinearDrift {n : ℕ} (drift : G) (s : Fin (n + 1) → G) :
    Fin (n + 1) → G :=
  fun j => s j - j.val • drift

/-- Cyclic partial sums commute with removing a constant increment from the
path. The wrapped case uses the wrapped prefix length, so the elapsed-time
correction remains `j.val` in both cases. -/
theorem cyclicPartialSum_removeLinearDrift {n : ℕ}
    (s : Fin (n + 1) → G) (drift : G) (k : Fin n)
    (j : Fin (n + 1)) :
    cyclicPartialSum (removeLinearDrift drift s) k j =
      cyclicPartialSum s k j - j.val • drift := by
  unfold cyclicPartialSum removeLinearDrift
  split_ifs with h
  · simp only [Fin.val_castSucc]
    rw [add_nsmul]
    abel
  · have hp : n + (k.val + j.val - n) = k.val + j.val := by omega
    have hmul : n • drift + (k.val + j.val - n) • drift =
        k.val • drift + j.val • drift := by
      calc
        n • drift + (k.val + j.val - n) • drift =
            (n + (k.val + j.val - n)) • drift := (add_nsmul _ _ _).symm
        _ = (k.val + j.val) • drift := by rw [hp]
        _ = k.val • drift + j.val • drift := add_nsmul _ _ _
    have hscalar : n • drift - k.val • drift +
        (k.val + j.val - n) • drift = j.val • drift := by
      calc
        _ = (n • drift + (k.val + j.val - n) • drift) - k.val • drift := by
          abel
        _ = (k.val • drift + j.val • drift) - k.val • drift := by rw [hmul]
        _ = _ := by abel
    simp only [Fin.val_castSucc, Fin.val_last]
    calc
      s (Fin.last n) - n • drift -
          (s k.castSucc - k.val • drift) +
          (s ⟨k.val + j.val - n, by omega⟩ -
            (k.val + j.val - n) • drift) =
        (s (Fin.last n) - s k.castSucc +
          s ⟨k.val + j.val - n, by omega⟩) -
          (n • drift - k.val • drift +
            (k.val + j.val - n) • drift) := by abel
      _ = s (Fin.last n) - s k.castSucc +
          s ⟨k.val + j.val - n, by omega⟩ - j.val • drift := by
        rw [hscalar]


end Fin

end
