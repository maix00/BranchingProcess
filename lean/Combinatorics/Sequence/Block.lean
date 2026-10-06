/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Data.Fin.Basic

/-!
# Finite blocks of sequences

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

end Combinatorics.Sequence

end
