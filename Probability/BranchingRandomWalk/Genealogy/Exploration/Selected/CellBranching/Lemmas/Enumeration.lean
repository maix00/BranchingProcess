/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Population.Candidates.Prefix

/-!
# Enumerating finite selected populations

For every finite labelled population $s$, the proof-only lemma
`finiteRootAddress_enumeration s` chooses an injective map
$u:\mathrm{Fin}(|s|)\to\operatorname{RootAddress}(m,\mathbb N)$ such that
\[
  s=\{u_i:i\in\mathrm{Fin}(|s|)\}.
\]
It packages Mathlib's finite-type equivalence with `Fin` for the selected-
population proof chain.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory

lemma finiteRootAddress_enumeration {m : ℕ}
    (s : Finset (RootAddress m ℕ)) :
    ∃ roots : Fin s.card → RootAddress m ℕ,
      s = Finset.univ.image roots ∧ Function.Injective roots := by
  classical
  let e : {p : RootAddress m ℕ // p ∈ s} ≃ Fin s.card :=
    Fintype.equivFinOfCardEq (by simp)
  let roots : Fin s.card → RootAddress m ℕ := fun j => (e.symm j).1
  refine ⟨roots, ?_, ?_⟩
  · ext p
    constructor
    · intro hp
      apply Finset.mem_image.mpr
      refine ⟨e ⟨p, hp⟩, Finset.mem_univ _, ?_⟩
      simp [roots]
    · intro hp
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hp
      exact (e.symm j).2
  · intro i j hij
    apply e.symm.injective
    exact Subtype.ext hij

end ProbabilityTheory.BranchingRandomWalk
