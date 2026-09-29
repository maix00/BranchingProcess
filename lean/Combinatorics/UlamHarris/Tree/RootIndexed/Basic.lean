module

public import Combinatorics.UlamHarris.Tree.Basic

/-!
# Root-indexed Ulam--Harris trees

`RootIndexed.Tree Root α` is the family of deterministic trees indexed by the
initial ancestors: one rooted tree over the addresses `TreeNode α` for each
`r : Root`. Each initial individual grows its own labelled tree.

The roots are *not* glued into a single tree. Gluing them would put the initial
ancestors inside one address space and would change the generation filtration,
whereas trees belonging to distinct roots are separate, simultaneously
observed objects. A root-indexed tree is therefore
defined as an indexed family of `Tree α`, exactly parallel to `Tree α` itself
but with an extra index type.

`FiniteRootTree m α` and `CountableRootTree α` are the instances used by the
population arguments, corresponding to the finite and countable root-indexed
step fields of the probability layer.

The one-element case is the single tree: for `[Unique Root]` the family
`RootIndexed.Tree Root α` is `Tree α` up to the identification of `Singleton.lean`,
so `Tree α` is the `Root := Unit` (equivalently `Fin 1`) instance of this
construction.
-/

@[expose] public section

namespace Combinatorics

namespace UlamHarris

namespace RootIndexed

/-- One Ulam--Harris tree for each initial ancestor. -/
abbrev Tree (Root α : Type*) [LT α] := Root → UlamHarris.Tree α

namespace Tree

variable {Root NewRoot α : Type*} [LT α]

/-- The root is realized in every one of the trees. -/
theorem root_mem (T : RootIndexed.Tree Root α) (r : Root) :
    [] ∈ (T r).carrier :=
  (T r).root_mem

/-- Every tree of the family is parent closed. -/
theorem mem_parent (T : RootIndexed.Tree Root α) (r : Root)
    {u v : List α} (h : u ++ v ∈ (T r).carrier) : u ∈ (T r).carrier :=
  UlamHarris.Tree.mem_parent (T r) h

/-- Every tree of the family contains the smaller siblings of a survive child,
using the child-label order of each tree. -/
theorem sibling_closed (T : RootIndexed.Tree Root α) (r : Root)
    {u : List α} {i j : α} (h : u ++ [j] ∈ (T r).carrier) (hij : i < j) :
    u ++ [i] ∈ (T r).carrier :=
  (T r).sibling_closed h hij

/-- Two root-indexed trees are equal as soon as their trees agree at every
index. -/
@[ext]
theorem ext {S T : RootIndexed.Tree Root α} (h : ∀ r, S r = T r) : S = T :=
  funext h

/-- Reindexing the initial ancestors along a map of index types. -/
def reindex (f : NewRoot → Root) (T : RootIndexed.Tree Root α) :
    RootIndexed.Tree NewRoot α :=
  fun r => T (f r)

@[simp]
theorem reindex_apply (f : NewRoot → Root) (T : RootIndexed.Tree Root α)
    (r : NewRoot) : T.reindex f r = T (f r) := rfl

@[simp]
theorem reindex_id (T : RootIndexed.Tree Root α) : T.reindex id = T := rfl

theorem reindex_comp (f : NewRoot → Root) {NewerRoot : Type*}
    (g : NewerRoot → NewRoot) (T : RootIndexed.Tree Root α) :
    (T.reindex f).reindex g = T.reindex (f ∘ g) := rfl

/-- Root-indexed trees over finitely many initial ancestors. -/
abbrev FiniteRootTree (m : ℕ) (α : Type*) [LT α] := RootIndexed.Tree (Fin m) α

/-- Root-indexed trees over countably many initial ancestors. -/
abbrev CountableRootTree (α : Type*) [LT α] := RootIndexed.Tree ℕ α

theorem finiteRootTree_ext {m : ℕ} {S T : FiniteRootTree m α}
    (h : ∀ r, S r = T r) : S = T :=
  ext h

end Tree

end RootIndexed

end UlamHarris

end Combinatorics

end
