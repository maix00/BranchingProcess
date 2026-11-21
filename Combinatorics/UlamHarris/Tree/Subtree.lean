/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module
public import Combinatorics.UlamHarris.Tree.Defs

/-!
# Rooted subtrees

## Public declarations

In namespace `Combinatorics.UlamHarris.Tree`:

* `subtree T u hu` is the rooted tree with carrier $\{v:uv\in T\}$ for $u\in T$.
* `mem_subtree` states $v\in T_u\iff uv\in T$.
* `subtree_root` and `subtree_subtree` give $T_\varnothing=T$ and
  $(T_u)_v=T_{uv}$.

This is the subtree operation of J. Neveu, "Arbres et processus de
Galton--Watson", Section 2, *Annales de l'I.H.P. Probabilités et statistiques*
22(2) (1986), 199--207, https://www.numdam.org/item/AIHPB_1986__22_2_199_0/.
-/
@[expose] public section
namespace Combinatorics.UlamHarris.Tree
variable {α : Type*} [LT α]

/-- The descendant tree rerooted at a node belonging to the original tree. -/
def subtree (T : Tree α) (u : List α) (hu : u ∈ T.carrier) : Tree α where
  carrier := {v | u ++ v ∈ T.carrier}
  root_mem := by
    change u ++ [] ∈ T.carrier
    simpa using hu
  parent_closed := by
    intro v w h
    change u ++ (v ++ w) ∈ T.carrier at h
    change u ++ v ∈ T.carrier
    exact T.parent_closed (by simpa [List.append_assoc] using h)
  sibling_closed := by
    intro v i j h hij
    change u ++ (v ++ [j]) ∈ T.carrier at h
    change u ++ (v ++ [i]) ∈ T.carrier
    have hj : (u ++ v) ++ [j] ∈ T.carrier := by
      simpa only [List.append_assoc] using h
    simpa only [List.append_assoc] using T.sibling_closed (u := u ++ v) hj hij

@[simp] theorem mem_subtree (T : Tree α) (u : List α) (hu : u ∈ T.carrier) (v : List α) :
    v ∈ (T.subtree u hu).carrier ↔ u ++ v ∈ T.carrier := Iff.rfl

@[simp] theorem subtree_root (T : Tree α) : T.subtree [] T.root_mem = T := by
  apply Tree.ext
  ext u
  simp

/-- Rerooting twice is rerooting at the concatenated address. -/
theorem subtree_subtree (T : Tree α) (u v : List α) (hu : u ∈ T.carrier)
    (hv : v ∈ (T.subtree u hu).carrier) :
    (T.subtree u hu).subtree v hv = T.subtree (u ++ v) hv := by
  apply Tree.ext
  ext w
  change (u ++ (v ++ w) ∈ T.carrier) ↔ ((u ++ v) ++ w ∈ T.carrier)
  rw [List.append_assoc]

end Combinatorics.UlamHarris.Tree
