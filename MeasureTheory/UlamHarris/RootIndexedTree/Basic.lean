import MeasureTheory.UlamHarris.Tree.Basic

/-!
# Root-indexed Ulam--Harris trees

`RootIndexedTree Root α` is the family of deterministic trees indexed by the
initial ancestors: one rooted tree over the addresses `TreeNode α` for each
`r : Root`. It is the multi-root object of the paper, where `N` initial
individuals each grow their own `N`-ary tree.

The roots are *not* glued into a single tree. Gluing them would put the initial
ancestors inside one address space and would change the generation filtration,
whereas the paper treats the trees of different initial individuals as
separate, simultaneously observed objects. A root-indexed tree is therefore
defined as an indexed family of `Tree α`, exactly parallel to `Tree α` itself
but with an extra index type.

`FiniteRootTree m α` and `CountableRootTree α` are the instances used by the
population arguments, corresponding to the finite and countable root-indexed
step fields of the probability layer.
-/

namespace MeasureTheory

namespace UlamHarris

/-- One Ulam--Harris tree for each initial ancestor. -/
abbrev RootIndexedTree (Root α : Type*) [LT α] := Root → Tree α

namespace RootIndexedTree

variable {Root NewRoot α : Type*} [LT α]

/-- The root is realized in every one of the trees. -/
theorem root_mem (T : RootIndexedTree Root α) (r : Root) :
    [] ∈ (T r).carrier :=
  (T r).root_mem

/-- Every tree of the family is prefix closed. -/
theorem mem_prefix (T : RootIndexedTree Root α) (r : Root)
    {u v : List α} (h : u ++ v ∈ (T r).carrier) : u ∈ (T r).carrier :=
  Tree.mem_prefix (T r) h

/-- Every tree of the family contains the smaller siblings of a present child,
which is the paper's numbering convention, applied tree by tree. -/
theorem sibling_closed (T : RootIndexedTree Root α) (r : Root)
    {u : List α} {i j : α} (h : u ++ [j] ∈ (T r).carrier) (hij : i < j) :
    u ++ [i] ∈ (T r).carrier :=
  (T r).sibling_closed h hij

/-- Two root-indexed trees are equal as soon as their trees agree at every
index. -/
@[ext]
theorem ext {S T : RootIndexedTree Root α} (h : ∀ r, S r = T r) : S = T :=
  funext h

/-- Reindexing the initial ancestors along a map of index types. -/
def reindex (f : NewRoot → Root) (T : RootIndexedTree Root α) :
    RootIndexedTree NewRoot α :=
  fun r => T (f r)

@[simp]
theorem reindex_apply (f : NewRoot → Root) (T : RootIndexedTree Root α)
    (r : NewRoot) : T.reindex f r = T (f r) := rfl

@[simp]
theorem reindex_id (T : RootIndexedTree Root α) : T.reindex id = T := rfl

theorem reindex_comp (f : NewRoot → Root) {NewerRoot : Type*}
    (g : NewerRoot → NewRoot) (T : RootIndexedTree Root α) :
    (T.reindex f).reindex g = T.reindex (f ∘ g) := rfl

/-- Root-indexed trees over finitely many initial ancestors. -/
abbrev FiniteRootTree (m : ℕ) (α : Type*) [LT α] := RootIndexedTree (Fin m) α

/-- Root-indexed trees over countably many initial ancestors. -/
abbrev CountableRootTree (α : Type*) [LT α] := RootIndexedTree ℕ α

theorem finiteRootTree_ext {m : ℕ} {S T : FiniteRootTree m α}
    (h : ∀ r, S r = T r) : S = T :=
  ext h

end RootIndexedTree

end UlamHarris

end MeasureTheory
