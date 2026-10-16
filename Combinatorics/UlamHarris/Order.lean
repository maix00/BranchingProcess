/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.UlamHarris.Basic
public import Mathlib.Data.List.Lex
public import Mathlib.Data.Prod.Lex

/-!
# Lexicographic order on root-indexed addresses

A root-indexed address is ordered first by its root label and then by its
Ulam--Harris word. This is the canonical label order used to break ties when
positions agree.
-/

@[expose] public section

namespace Combinatorics.UlamHarris.RootIndexed

/-- Order root-indexed addresses by the root label and then by the child word.
The root labels and child labels carry their usual linear orders. -/
@[instance_reducible] noncomputable def addressLinearOrder
    (Root α : Type*) [LinearOrder Root] [LinearOrder α] :
    LinearOrder (TreeNode Root α) := by
  letI : LinearOrder (Root ×ₗ List α) := inferInstance
  exact LinearOrder.lift'
    (fun x : TreeNode Root α => toLex (x.1, x.2))
    (by
      intro x y h
      exact toLex.injective h)

/-- Strict comparison in `addressLinearOrder` is root-label comparison first,
then lexicographic comparison of the child words. -/
theorem addressLinearOrder_lt_iff
    (Root α : Type*) [LinearOrder Root] [LinearOrder α]
    (x y : TreeNode Root α) :
    @LT.lt (TreeNode Root α)
        ((addressLinearOrder Root α).toPartialOrder.toPreorder.toLT) x y ↔
      x.1 < y.1 ∨ x.1 = y.1 ∧ x.2 < y.2 := by
  letI : LinearOrder (TreeNode Root α) := addressLinearOrder Root α
  letI : Preorder (TreeNode Root α) :=
    (addressLinearOrder Root α).toPartialOrder.toPreorder
  change toLex (x.1, x.2) < toLex (y.1, y.2) ↔ _
  exact Prod.Lex.toLex_lt_toLex

end Combinatorics.UlamHarris.RootIndexed

end
