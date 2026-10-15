/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Algebra.BigOperators.AdditivePath
public import Algebra.BigOperators.PartialSum

/-!
# Cyclic rotation cover for a random-walk path

The public theorem in this file is:

- `ProbabilityTheory.RandomWalk.nonnegative_finitePartialSum_eq_iUnion_cyclic_survival`:
  the finite-vector event $\{S_n\ge0\}$ equals the union of all $n$
  cyclic survival events.
- `ProbabilityTheory.RandomWalk.nonnegative_displacement_iff_exists_cyclic_survival`:
  for $n\ge1$, $S_n\ge0$ if and only if one cyclic rotation of the first
  $n$ increments has every partial sum nonnegative.

This is the event equality $A_n=\bigcup_{i=1}^n B_n^i$ in M. Bauer,
C. Godrèche, and J.-M. Luck, *Statistics of persistent events in the
binomial random walk: Will the drunken sailor hit the sober man?*,
Appendix A, immediately after equation (A.3) (arXiv:cond-mat/9905252).
It is the first combinatorial step of their proof of the Sparre--Andersen
identity (A.2).
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

/-- The finite-product event-covering identity in Bauer--Godrèche--Luck,
Appendix A, after (A.3). Its finite-vector form allows the IID-prefix law
to be represented by `Measure.pi`. -/
theorem nonnegative_finitePartialSum_eq_iUnion_cyclic_survival
    {n : ℕ} (hn : 0 < n) :
    {x : Fin n → ℝ | 0 ≤ Fin.partialSum x (Fin.last n)} =
      ⋃ k : Fin n,
        {x : Fin n → ℝ |
          ∀ j : Fin (n + 1),
            0 ≤ Fin.cyclicPartialSum (Fin.partialSum x) k j} := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · intro hlast
    exact Fin.exists_cyclicPartialSum_nonneg_of_last_nonneg
      hn (Fin.partialSum x) (Fin.partialSum_zero x) hlast
  · rintro ⟨k, hk⟩
    have hlast := hk (Fin.last n)
    rwa [Fin.cyclicPartialSum_last_eq_of_zero
      (Fin.partialSum x) (Fin.partialSum_zero x) k] at hlast

/-- The event-covering step of Bauer--Godrèche--Luck, Appendix A: a
nonnegative final displacement admits a cyclic rotation whose entire path
is nonnegative, and every such rotation has the same final displacement. -/
theorem nonnegative_displacement_iff_exists_cyclic_survival
    {n : ℕ} (hn : 0 < n) (increment : ℕ → ℝ) :
    0 ≤ AdditivePath.displacement n increment ↔
      ∃ k : Fin n, ∀ j : Fin (n + 1),
        0 ≤ Fin.cyclicPartialSum
          (fun i : Fin (n + 1) =>
            AdditivePath.displacement i.val increment) k j := by
  let s : Fin (n + 1) → ℝ :=
    fun i => AdditivePath.displacement i.val increment
  have hzero : s 0 = 0 := by simp [s]
  constructor
  · intro hlast
    exact Fin.exists_cyclicPartialSum_nonneg_of_last_nonneg
      hn s hzero (by simpa [s, Fin.val_last] using hlast)
  · rintro ⟨k, hk⟩
    have hlast := hk (Fin.last n)
    rw [Fin.cyclicPartialSum_last_eq_of_zero s hzero k] at hlast
    simpa [s, Fin.val_last] using hlast

end ProbabilityTheory.RandomWalk

end
