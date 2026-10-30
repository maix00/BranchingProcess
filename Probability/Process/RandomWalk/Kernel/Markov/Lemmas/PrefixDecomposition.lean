/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.Process.RandomWalk.Kernel.Basic
import Probability.Process.RandomWalk.Path.Adapted.Filtration

/-!
# Prefix decomposition for the random-walk Markov proof

## Internal proof declarations

For increments $\xi_0,\xi_1,\ldots$ and initial state $x_0$, these lemmas
identify the position recovered from the first $m$ coordinates and split a
later position into its prefix and the following block:
\[
  X_m=x_0+\sum_{j=0}^{m-1}\xi_j,
  \qquad
  X_n=X_m+\sum_{j=m}^{n-1}\xi_j\quad(m\le n).
\]
The finite-coordinate measurability statement and these identities support
only `ProbabilityTheory.RandomWalk.iidSequenceLaw_isMarkovChain` in the
sibling `Basic.lean` module.
-/

open MeasureTheory
open scoped BigOperators MeasureTheory ProbabilityTheory

section

namespace ProbabilityTheory.RandomWalk

variable {E : Type*} [MeasurableSpace E] [AddCommMonoid E]
  [MeasurableAdd₂ E] [StandardBorelSpace E]

/-- Recover the current position from a finite increment prefix. -/
def positionFromPrefix (initial : E) {n : ℕ} (increments : Fin n → E) : E :=
  initial + ∑ k, increments k

omit [StandardBorelSpace E] in
lemma positionFromPrefix_measurable (initial : E) (n : ℕ) :
    Measurable (positionFromPrefix initial : (Fin n → E) → E) := by
  exact measurable_const.add
    (Finset.measurable_sum Finset.univ fun k _ ↦ measurable_pi_apply k)

omit [MeasurableSpace E] [MeasurableAdd₂ E] [StandardBorelSpace E] in
@[simp] lemma positionFromPrefix_blockCoordinates_zero
    (initial : E) (n : ℕ) (increment : ℕ → E) :
    positionFromPrefix initial (Combinatorics.Sequence.blockCoordinates 0 n increment) =
      positionProcess initial n increment := by
  simp only [positionFromPrefix, Combinatorics.Sequence.blockCoordinates, positionProcess,
    Nat.zero_add, AdditivePath.fromIncrements, AdditivePath.displacement]
  rw [Fin.sum_univ_eq_sum_range]

omit [MeasurableSpace E] [MeasurableAdd₂ E] [StandardBorelSpace E] in
lemma positionProcess_eq_prefix_add_blockSum
    (initial : E) {m n : ℕ} (hmn : m ≤ n) (increment : ℕ → E) :
    positionProcess initial n increment =
      positionFromPrefix initial (Combinatorics.Sequence.blockCoordinates 0 m increment) +
        AdditivePath.blockSum m (n - m) increment := by
  rw [positionFromPrefix_blockCoordinates_zero]
  simp only [positionProcess]
  have hn : m + (n - m) = n := Nat.add_sub_of_le hmn
  calc
    initial + AdditivePath.displacement n increment =
        initial + AdditivePath.displacement (m + (n - m)) increment := by rw [hn]
    _ = initial + (AdditivePath.displacement m increment +
        AdditivePath.blockSum m (n - m) increment) := by
      rw [AdditivePath.displacement_add_eq_add_blockSum]
    _ = initial + AdditivePath.displacement m increment +
        AdditivePath.blockSum m (n - m) increment :=
      (add_assoc initial (AdditivePath.displacement m increment)
        (AdditivePath.blockSum m (n - m) increment)).symm

end ProbabilityTheory.RandomWalk

end
