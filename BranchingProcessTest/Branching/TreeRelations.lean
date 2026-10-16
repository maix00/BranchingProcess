import Combinatorics.UlamHarris.Relation
import Combinatorics.UlamHarris.Tree.Graph.IsTree

/-!
# Address-level tree relation regression checks

These examples record the parent-to-child direction and the graph projection
contract independently of any historical relation name.
-/

open Combinatorics.UlamHarris

example {α : Type*} (parent : TreeNode α) (i : α) :
    TreeNode.IsChild parent (parent ++ [i]) :=
  ⟨i, rfl⟩

example {α : Type*} (address : TreeNode α) :
    ¬ TreeNode.IsChild address address :=
  TreeNode.IsChild.irrefl address

example {α : Type*} {parent₁ parent₂ child : TreeNode α}
    (h₁ : TreeNode.IsChild parent₁ child)
    (h₂ : TreeNode.IsChild parent₂ child) : parent₁ = parent₂ :=
  TreeNode.IsChild.parent_unique h₁ h₂

example {α : Type*} [LT α] (T : Tree α) (a b : ↥T.carrier) :
    (Tree.childDigraph T).Adj a b ↔ TreeNode.IsChild a.1 b.1 :=
  Tree.childDigraph_adj_iff
