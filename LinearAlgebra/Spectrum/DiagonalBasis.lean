/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Eigenspace.Basic

public section

/-!
# Powers of an operator in an eigenvector basis

## Public declarations

* For a finite basis `b` over a commutative ring,
  `Module.End.pow_apply_eq_sum_repr_smul` states that if `b i` is an
  eigenvector of `f` with eigenvalue `eigenvalue i` for every `i`, then
  `(f ^ n) x = ∑ i, (b.repr x i * eigenvalue i ^ n) • b i`.

This finite expansion is independent of probability and of any particular
matrix realization.
-/

open scoped BigOperators

namespace Module.End

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι]

/-- Expand a power of an endomorphism in a finite eigenvector basis. -/
theorem pow_apply_eq_sum_repr_smul
    (f : Module.End R M) (b : Module.Basis ι R M) (eigenvalue : ι → R)
    (heigen : ∀ i, f.HasEigenvector (eigenvalue i) (b i))
    (n : ℕ) (x : M) :
    (f ^ n) x =
      ∑ i, (b.repr x i * eigenvalue i ^ n) • b i := by
  conv_lhs => rw [← b.sum_repr x]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, (heigen i).pow_apply, smul_smul]

end Module.End
