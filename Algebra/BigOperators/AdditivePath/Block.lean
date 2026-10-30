/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Algebra.BigOperators.AdditivePath.Basic
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Basic
public import Combinatorics.Sequence.Block

/-!
# Blocks of additive paths

## Public declarations

For increments $ξ : ℕ → E$, let $D_n(ξ)=AdditivePath.displacement(n,ξ)$.

- `AdditivePath.blockSum` defines
  $B(s,ℓ,ξ)=∑_{s≤k<s+ℓ}ξ_k$.
- `AdditivePath.blockSum_zero` and `AdditivePath.blockSum_zero_start` give
  $B(s,0,ξ)=0$ and $B(0,ℓ,ξ)=D_ℓ(ξ)$.
- `AdditivePath.blockSum_eq_displacement_natAdd` gives
  $B(s,ℓ,ξ)=D_ℓ(k↦ξ_{s+k})$.
  `AdditivePath.partialSum_block_eq_displacement` gives
  $Fin.partialSum(k↦ξ_{s+k},i)=D_{i.val}(k↦ξ_{s+k})$ for $i : Fin(ℓ+1)$.
- `AdditivePath.blockSum_add` and
  `AdditivePath.displacement_add_eq_add_blockSum` give
  $B(s,m+n,ξ)=B(s,m,ξ)+B(s+m,n,ξ)$ and
  $D_{s+ℓ}(ξ)=D_s(ξ)+B(s,ℓ,ξ)$.
- `AdditivePath.displacement_blockStart_eq_sum_blockSum` gives
  $D_{b_j}(ξ)=∑_{i<j}B(b_i,ℓ_i,ξ)$, where
  $b_j=∑_{i<j}ℓ_i$ is defined by `Combinatorics.Sequence.blockStart`.
- `AdditivePath.blockSum_sub_const` gives
  $B(s,ℓ,k↦ξ_k-c)=B(s,ℓ,ξ)-ℓ•c$ in an additive commutative group.
- `AdditivePath.norm_displacement_sub_le_length_mul_of_forall_norm_le` bounds
  the norm of a displacement difference by the number of increments times a
  common norm bound on those increments.
-/

open scoped BigOperators

@[expose] public section

namespace AdditivePath


variable {E : Type*} [AddCommMonoid E]

/-- Sum of `length` consecutive increments starting at `start`. -/
def blockSum (start length : ℕ) (increment : ℕ → E) : E :=
  ∑ k ∈ Finset.Ico start (start + length), increment k

@[simp] theorem blockSum_zero (start : ℕ) (increment : ℕ → E) :
    blockSum start 0 increment = 0 := by
  simp [blockSum]

@[simp] theorem blockSum_zero_start (length : ℕ) (increment : ℕ → E) :
    blockSum 0 length increment = displacement length increment := by
  simp [blockSum, displacement]

/-- A block sum is the displacement of the increment sequence after dropping
its first `start` coordinates. -/
theorem blockSum_eq_displacement_natAdd (start length : ℕ)
    (increment : ℕ → E) :
    blockSum start length increment =
      displacement length (fun k => increment (start + k)) := by
  simp only [blockSum, displacement, Finset.sum_Ico_eq_sum_range,
    Nat.add_sub_cancel_left]

/-- A partial sum of a finite consecutive block is the corresponding
displacement of the underlying increment sequence. -/
theorem partialSum_block_eq_displacement (start length : ℕ)
    (increment : ℕ → E) (i : Fin (length + 1)) :
    Fin.partialSum (fun k : Fin length => increment (start + k)) i =
      displacement i.val (fun k => increment (start + k)) := by
  induction i using Fin.induction with
  | zero => simp [displacement, Fin.partialSum]
  | succ j hj =>
      rw [Fin.partialSum_succ, hj]
      simp [displacement_succ]

/-- Consecutive blocks concatenate. -/
theorem blockSum_add (start m n : ℕ) (increment : ℕ → E) :
    blockSum start (m + n) increment =
      blockSum start m increment + blockSum (start + m) n increment := by
  rw [blockSum_eq_displacement_natAdd start (m + n),
    blockSum_eq_displacement_natAdd start m,
    blockSum_eq_displacement_natAdd (start + m) n,
    displacement_add]
  congr 1
  apply congrArg (fun f : ℕ → E => displacement n f)
  funext k
  congr 1
  omega

/-- The displacement through a block is the prefix displacement plus its
block sum. -/
theorem displacement_add_eq_add_blockSum (start length : ℕ)
    (increment : ℕ → E) :
    displacement (start + length) increment =
      displacement start increment + blockSum start length increment := by
  rw [displacement_add, blockSum_eq_displacement_natAdd]

section SeminormedAddCommGroup

variable {G : Type*} [SeminormedAddCommGroup G]

/-- The displacement difference over an interval is bounded by its length
times a common norm bound for the increments in that interval. -/
theorem norm_displacement_sub_le_length_mul_of_forall_norm_le
    {left right : ℕ} {increment : ℕ → G} {bound : ℝ}
    (hle : left ≤ right)
    (hbound : ∀ k ∈ Finset.Ico left right, ‖increment k‖ ≤ bound) :
    ‖displacement right increment - displacement left increment‖ ≤
      ((right - left : ℕ) : ℝ) * bound := by
  have hright : right = left + (right - left) := by omega
  have hbound' : ∀ k ∈ Finset.Ico left (left + (right - left)),
      ‖increment k‖ ≤ bound := by
    intro k hk
    have hk' : k ∈ Finset.Ico left right := by
      rcases Finset.mem_Ico.mp hk with ⟨hleftk, hklt⟩
      refine Finset.mem_Ico.mpr ⟨hleftk, ?_⟩
      omega
    exact hbound k hk'
  conv_lhs =>
    rw [hright, displacement_add_eq_add_blockSum, add_sub_cancel_left]
  unfold blockSum
  calc
    ‖∑ k ∈ Finset.Ico left (left + (right - left)), increment k‖ ≤
        ∑ k ∈ Finset.Ico left (left + (right - left)), ‖increment k‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.Ico left (left + (right - left)), bound := by
      apply Finset.sum_le_sum
      intro k hk
      exact hbound' k hk
    _ = ((right - left : ℕ) : ℝ) * bound := by
      simp only [Finset.sum_const, Nat.card_Ico, Nat.add_sub_cancel_left, nsmul_eq_mul]

end SeminormedAddCommGroup

/-- A finite sequence of variable length blocks reconstructs the additive
path displacement at its final endpoint. -/
theorem displacement_blockStart_eq_sum_blockSum (length : ℕ → ℕ)
    (blocks : ℕ) (increment : ℕ → E) :
    displacement (Combinatorics.Sequence.blockStart length blocks) increment =
      ∑ j ∈ Finset.range blocks,
        blockSum (Combinatorics.Sequence.blockStart length j) (length j) increment := by
  induction blocks with
  | zero => simp [Combinatorics.Sequence.blockStart]
  | succ blocks ih =>
      rw [Combinatorics.Sequence.blockStart_succ,
        displacement_add_eq_add_blockSum, ih,
        Finset.sum_range_succ]

section AddCommGroup

variable {G : Type*} [AddCommGroup G]

/-- Subtracting a constant from each increment subtracts its repeated sum from
the block. -/
theorem blockSum_sub_const (start length : ℕ) (increment : ℕ → G) (c : G) :
    blockSum start length (fun k => increment k - c) =
      blockSum start length increment - length • c := by
  simp [blockSum, Finset.sum_sub_distrib]

end AddCommGroup

end AdditivePath

end
