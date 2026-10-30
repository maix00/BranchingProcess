/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Algebra.BigOperators.PartialSum

/-!
# Cyclic rotation cover for a random-walk path

## Public declarations

`ProbabilityTheory.RandomWalk.nonnegative_finitePartialSum_eq_iUnion_cyclic_survival`
states that for every increment vector $x\in G^n$, a nonnegative total sum
$S_n(x)$ is equivalent to the existence of a cyclic rotation whose partial
sums are all nonnegative. In event notation,
$\{x:S_n(x)\ge0\}=\bigcup_{k<n}\{x:\text{the rotation at }k\text{ survives}\}$.
This is the event equality $A_n=\bigcup_{i=1}^n B_n^i$ in M. Bauer,
C. Godrèche, and J.-M. Luck, *Statistics of persistent events in the
binomial random walk: Will the drunken sailor hit the sober man?*,
Appendix A, immediately after equation (A.3), *Journal of Statistical
Physics* 96 (1999), 963--1019, DOI 10.1023/A:1004636216365,
arXiv:cond-mat/9905252. It is the first combinatorial step of their proof
of the Sparre--Andersen identity (A.2).
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

variable {G : Type*} [AddCommGroup G] [LinearOrder G]
  [IsOrderedAddMonoid G]

/-- The finite-product event-covering identity in Bauer--Godrèche--Luck,
Appendix A, after (A.3). Its finite-vector form allows the IID-prefix law
to be represented by `Measure.pi`. -/
theorem nonnegative_finitePartialSum_eq_iUnion_cyclic_survival
    {n : ℕ} (hn : 0 < n) :
    {x : Fin n → G | 0 ≤ Fin.partialSum x (Fin.last n)} =
      ⋃ k : Fin n,
        {x : Fin n → G |
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

end ProbabilityTheory.RandomWalk

end
