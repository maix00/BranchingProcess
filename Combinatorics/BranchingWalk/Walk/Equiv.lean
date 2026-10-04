/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Walk.Basic
public import Mathlib.Logic.Equiv.Basic

/-!
# Singleton walks as optional increment sequences

A singleton branching walk is completely described by its initial position
and the optional mark on each generation edge. The option value preserves
extinction and does not assume that every generation has a child.
-/

@[expose] public section

namespace Combinatorics.Branching.Walk

variable {Mark Position : Type*}

/-- Addresses in a singleton-slot tree are indexed by their generation. -/
def nodeEquivNat : Combinatorics.UlamHarris.TreeNode PUnit ≃ ℕ where
  toFun := List.length
  invFun := lineNode
  left_inv := fun u => (eq_lineNode_length u).symm
  right_inv := lineNode_length

/-- A singleton walk is equivalent to its initial position and its sequence
of possibly absent increments. -/
def equivInitialOptionalIncrements :
    Walk Mark Position ≃ Position × (ℕ → Option Mark) where
  toFun walk := (walk.initial PUnit.unit, increments walk)
  invFun data := ofOptionalIncrements data.1 data.2
  left_inv walk := ofOptionalIncrements_initial_increments walk
  right_inv data := by
    rcases data with ⟨initial, increment⟩
    simp

end Combinatorics.Branching.Walk

end
