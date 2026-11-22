/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module
public import Combinatorics.UlamHarris.Tree.Truncation.Basic

/-!
# Limits of eventually stable tree truncations

## Public declarations

In namespace `Combinatorics.UlamHarris.Tree`:

* `liminf s` has carrier $\{u:\exists N,\forall m\ge N,\ u\in s_m\}$;
  `mem_liminf` states this identity. Parent and sibling closure are preserved.
* `truncate_liminf_eq_of_stable` states that if all truncations of $s_m$ at
  height $n$ equal the truncation of $s_N$ for $m\ge N$, the same truncation
  belongs to `liminf s`.

The construction uses the rooted-tree conditions of J. Neveu, "Arbres et
processus de Galton--Watson", Section 2, *Annales de l'I.H.P. Probabilités
et statistiques* 22(2) (1986), 199--207,
https://www.numdam.org/item/AIHPB_1986__22_2_199_0/.
-/
@[expose] public section
namespace Combinatorics.UlamHarris.Tree
variable {α : Type*} [LT α]

/-- The tree of nodes present eventually throughout a sequence. -/
def liminf (s : ℕ → Tree α) : Tree α where
  carrier := {u | ∃ N, ∀ m ≥ N, u ∈ (s m).carrier}
  root_mem := ⟨0, fun m _ ↦ (s m).root_mem⟩
  parent_closed := by
    rintro u v ⟨N, hN⟩
    exact ⟨N, fun m hm ↦ (s m).parent_closed (hN m hm)⟩
  sibling_closed := by
    rintro u i j ⟨N, hN⟩ hij
    exact ⟨N, fun m hm ↦ (s m).sibling_closed (hN m hm) hij⟩

@[simp] theorem mem_liminf (s : ℕ → Tree α) (u : List α) :
    u ∈ (liminf s).carrier ↔ ∃ N, ∀ m ≥ N, u ∈ (s m).carrier := Iff.rfl

/-- Eventually stable finite-height observations are preserved in the limit tree. -/
theorem truncate_liminf_eq_of_stable (s : ℕ → Tree α) (n N : ℕ)
    (h : ∀ m ≥ N, (s m).truncate n = (s N).truncate n) :
    (liminf s).truncate n = (s N).truncate n := by
  ext u
  simp only [mem_truncate, mem_liminf]
  constructor
  · rintro ⟨hu, M, hM⟩
    have he := congrArg (fun T : Tree α ↦ u ∈ T.carrier) (h (max M N) (le_max_right _ _))
    exact ⟨hu, ((Iff.of_eq he).mp ⟨hu, hM _ (le_max_left _ _)⟩).2⟩
  · rintro ⟨hu, huN⟩
    refine ⟨hu, N, ?_⟩
    intro m hm
    have he := congrArg (fun T : Tree α ↦ u ∈ T.carrier) (h m hm)
    exact ((Iff.of_eq he).mpr ⟨hu, huN⟩).2

end Combinatorics.UlamHarris.Tree
