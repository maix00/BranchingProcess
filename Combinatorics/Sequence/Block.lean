/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Data.Fin.Basic

/-!
# Finite blocks of sequences

The public declarations in `Combinatorics.Sequence` are:

- `blockCoordinates`: the block $k\mapsto f(s+k)$, for $k<\ell$.
- `paddedBlockCoordinates`: the sequence equal to $f(s+k)$ when $k<\ell$
  and to a chosen default otherwise.
- `paddedBlockCoordinates_of_lt` and `paddedBlockCoordinates_of_not_lt`:
  $\operatorname{paddedBlock}(s,\ell,d,f)(k)=f(s+k)$ for $k<\ell$, and
  equals $d$ when $\ell\le k$.

Extract a finite consecutive block from an arbitrary sequence. This operation
is independent of any algebraic, probabilistic, or process structure on the
sequence values.
-/

@[expose] public section

namespace Combinatorics.Sequence

/-- The finite block of length `length` starting at `start`. -/
def blockCoordinates {E : Type*} (start length : ℕ)
    (sequence : ℕ → E) : Fin length → E :=
  fun k => sequence (start + k)

/-- Extend a finite consecutive block to a sequence using a fixed default
outside the block. -/
def paddedBlockCoordinates {E : Type*} (start length : ℕ) (default : E)
    (sequence : ℕ → E) : ℕ → E :=
  fun k => if k < length then sequence (start + k) else default

@[simp] theorem paddedBlockCoordinates_of_lt {E : Type*}
    (start length : ℕ) (default : E) (sequence : ℕ → E) {k : ℕ}
    (hk : k < length) :
    paddedBlockCoordinates start length default sequence k = sequence (start + k) := by
  simp [paddedBlockCoordinates, hk]

@[simp] theorem paddedBlockCoordinates_of_not_lt {E : Type*}
    (start length : ℕ) (default : E) (sequence : ℕ → E) {k : ℕ}
    (hk : ¬ k < length) :
    paddedBlockCoordinates start length default sequence k = default := by
  simp [paddedBlockCoordinates, hk]

end Combinatorics.Sequence

end
