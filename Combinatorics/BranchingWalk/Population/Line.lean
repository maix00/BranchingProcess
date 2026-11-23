/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Population.Basic
public import Combinatorics.UlamHarris.Line.Coverage

/-!
# Generations of a population as lines

## Public declarations

* `Combinatorics.Branching.Population.isLine` states that `P n` is an ancestry
  line for every population `P` and generation `n`.
* `Combinatorics.Branching.Population.meetsEveryRay` states that `P n` meets
  every infinite path realized in `{p | ∃ k, p ∈ P k}`.

These statements use the generation-depth invariant of `Population`. They
require neither a probability law, finite populations, nor a selection rule.
Combined with `RootIndexed.IsLine.meetsEveryRay_iff_existsUnique`, the second
statement gives exactly one meeting on each realized infinite path.
-/

@[expose] public section

namespace Combinatorics.Branching.Population

open Combinatorics.UlamHarris

variable {Root α Mark : Type*} {stepField : Root → StepField α Mark}

theorem isLine (P : Population stepField) (n : ℕ) : RootIndexed.IsLine (P n) :=
  RootIndexed.isLine_of_depth (P.depth n)

theorem meetsEveryRay (P : Population stepField) (n : ℕ) :
    RootIndexed.MeetsEveryRay {p | ∃ k, p ∈ P k} (P n) := by
  intro r f hf
  obtain ⟨k, hk⟩ := hf n
  have hkn : k = n := (P.depth k _ hk).symm.trans (length_lineagePrefix f n)
  subst k
  exact ⟨n, hk⟩

end Combinatorics.Branching.Population

end
