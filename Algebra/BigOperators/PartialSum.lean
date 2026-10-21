/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Finite partial-sum identities

The public declarations in this file are:

- `Fin.partialSum_differences`: consecutive differences telescope to
  $s_j-s_0$.
- `Fin.partialSum_smul`: scalar multiplication commutes with partial sums.
- `Fin.partialSum_offset`: the sum of a consecutive subvector equals the
  difference of its endpoint partial sums.
- `Fin.cyclicPartialSum`: the partial sum after rotating a finite path at
  one of its increment positions.
- `Fin.cyclicPartialSum_last_eq_of_zero`: when $s_0=0$, every rotation
  has terminal displacement $s_n$.
- `Fin.exists_cyclicPartialSum_nonneg_of_last_nonneg`: if $s_0=0$ and
  $s_n\ge0$, one cyclic rotation has all partial sums nonnegative.

The final result is the minimum-prefix construction in M. Bauer,
C. Godrèche, and J.-M. Luck, *Statistics of persistent events in the
binomial random walk: Will the drunken sailor hit the sober man?*,
Appendix A, equation (A.3) and the paragraph following it
(arXiv:cond-mat/9905252).
-/

open scoped BigOperators

@[expose] public section

namespace Fin

variable {G : Type*} [AddCommGroup G] {n : ℕ}

/-- Partial sums of consecutive differences recover the endpoint displacement. -/
theorem partialSum_differences (f : Fin (n + 1) → G) (i : Fin (n + 1)) :
    partialSum (fun j : Fin n => f j.succ - f j.castSucc) i = f i - f 0 := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    rw [partialSum_succ, ih]
    simp only [sub_eq_add_neg]
    calc
      f i.castSucc + -f 0 + (f i.succ + -f i.castSucc) =
          (f i.castSucc + -f i.castSucc) + (f i.succ + -f 0) := by ac_rfl
      _ = f i.succ + -f 0 := by simp

/-- The partial sum of a consecutive block is the difference of the
corresponding partial sums of the full vector. -/
theorem partialSum_offset (x : Fin n → G) (start length : ℕ)
    (hbound : start + length ≤ n) (t : Fin (length + 1)) :
    partialSum
      (fun k : Fin length => x ⟨start + k.val, by omega⟩) t =
      partialSum x ⟨start + t.val, by omega⟩ -
        partialSum x ⟨start, by omega⟩ := by
  induction t using Fin.induction with
  | zero => simp
  | succ t ih =>
      rw [partialSum_succ, ih]
      have hstep := partialSum_succ x
        (⟨start + t.val, by omega⟩ : Fin n)
      have hstep' :
          partialSum x ⟨start + t.val + 1, by omega⟩ =
            partialSum x ⟨start + t.val, by omega⟩ +
              x ⟨start + t.val, by omega⟩ := by
        simpa only [Fin.succ_mk, Fin.castSucc_mk, Nat.add_assoc] using hstep
      have hidx :
          (⟨start + t.succ.val, by omega⟩ : Fin (n + 1)) =
            ⟨start + t.val + 1, by omega⟩ := Fin.ext rfl
      rw [hidx, hstep']
      simp only [sub_eq_add_neg]
      ac_rfl

end Fin

namespace Fin

variable {G : Type*} [AddGroup G] {n : ℕ}

/-- The partial sum after cyclically starting at `k`, expressed using the
original partial-sum path. -/
def cyclicPartialSum (s : Fin (n + 1) → G)
    (k : Fin n) (j : Fin (n + 1)) : G :=
  if h : k.val + j.val ≤ n then
    s ⟨k.val + j.val, Nat.lt_succ_of_le h⟩ - s k.castSucc
  else
    s (Fin.last n) - s k.castSucc +
      s ⟨k.val + j.val - n, by omega⟩

/-- Cyclic rotation preserves the total displacement of a path starting at
zero. -/
theorem cyclicPartialSum_last_eq_of_zero
    (s : Fin (n + 1) → G) (hzero : s 0 = 0) (k : Fin n) :
    cyclicPartialSum s k (Fin.last n) = s (Fin.last n) := by
  by_cases hk : k.val = 0
  · have h : k.val + (Fin.last n).val ≤ n := by simp [Fin.val_last, hk]
    have hkzero : k.castSucc = (0 : Fin (n + 1)) := Fin.ext hk
    have hindex :
        (⟨k.val + (Fin.last n).val, Nat.lt_succ_of_le h⟩ : Fin (n + 1)) =
          Fin.last n := Fin.ext (by simp [Fin.val_last, hk])
    simp only [cyclicPartialSum, dite_eq_left h, hindex, hkzero, hzero, sub_zero]
  · have h : ¬ k.val + (Fin.last n).val ≤ n := by
      simp [Fin.val_last]
      omega
    have hindex :
        (⟨k.val + (Fin.last n).val - n, by omega⟩ : Fin (n + 1)) =
          k.castSucc := by
      ext
      simp [Fin.val_last]
    simp only [cyclicPartialSum, dite_eq_right h, hindex, sub_add_cancel]

/-- A nonnegative terminal displacement admits a cyclic rotation with every
partial displacement nonnegative. This is the first event-covering step of
Bauer--Godrèche--Luck, Appendix A, immediately after (A.3)
(arXiv:cond-mat/9905252). -/
theorem exists_cyclicPartialSum_nonneg_of_last_nonneg
    {G : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    {n : ℕ} (hn : 0 < n) (s : Fin (n + 1) → G)
    (hzero : s 0 = 0) (hlast : 0 ≤ s (Fin.last n)) :
    ∃ k : Fin n, ∀ j : Fin (n + 1), 0 ≤ cyclicPartialSum s k j := by
  have huniv : (Finset.univ : Finset (Fin n)).Nonempty :=
    ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨k, _, hk⟩ := Finset.exists_min_image Finset.univ
    (fun i : Fin n => s i.castSucc) huniv
  refine ⟨k, fun j => ?_⟩
  have hkzero : s k.castSucc ≤ 0 := by
    simpa [hzero] using hk ⟨0, hn⟩ (Finset.mem_univ _)
  by_cases h : k.val + j.val ≤ n
  · by_cases hlt : k.val + j.val < n
    · have hmin := hk ⟨k.val + j.val, hlt⟩ (Finset.mem_univ _)
      simpa [cyclicPartialSum, h] using (sub_nonneg.mpr hmin)
    · have heq : k.val + j.val = n := by omega
      have hlastIndex :
          (⟨k.val + j.val, Nat.lt_succ_of_le h⟩ : Fin (n + 1)) =
            Fin.last n := by
        ext
        exact heq
      simp only [cyclicPartialSum, dite_eq_left h, hlastIndex]
      exact sub_nonneg.mpr (le_trans hkzero hlast)
  · have hindex : k.val + j.val - n < n := by omega
    have hmin := hk ⟨k.val + j.val - n, hindex⟩ (Finset.mem_univ _)
    let q : Fin (n + 1) := ⟨k.val + j.val - n, by omega⟩
    let i : Fin n := ⟨k.val + j.val - n, hindex⟩
    have hindexEq :
        q = i.castSucc := by
      ext
      rfl
    have hdiff : 0 ≤ s i.castSucc - s k.castSucc :=
      sub_nonneg.mpr hmin
    have hsum : 0 ≤ s (Fin.last n) + (s i.castSucc - s k.castSucc) :=
      add_nonneg hlast hdiff
    have hgoal : 0 ≤ s (Fin.last n) - s k.castSucc + s q := by
      rw [hindexEq]
      calc
        0 ≤ s (Fin.last n) + (s i.castSucc - s k.castSucc) := hsum
        _ = s (Fin.last n) - s k.castSucc + s i.castSucc := by abel
    simpa [cyclicPartialSum, h] using hgoal

end Fin

namespace Fin

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M] {n : ℕ}

/-- Scalar multiplication commutes with finite partial summation. -/
theorem partialSum_smul (a : R) (f : Fin n → M) (i : Fin (n + 1)) :
    partialSum (fun j => a • f j) i = a • partialSum f i := by
  induction i using Fin.induction with
  | zero => simp
  | succ i ih =>
    rw [partialSum_succ, ih, partialSum_succ, smul_add]

end Fin

end
