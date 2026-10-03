module

public import Combinatorics.UlamHarris.Tree.Defs
public import Mathlib.Data.Set.Basic

/-!
# Truncation of Ulam--Harris trees

The truncation `T.truncate n` keeps only the addresses of length at most `n`.
These truncations are the basic sets of the locally finite topology used for
the Borel structure on trees; the topology is in `Tree/Topology.lean`.
-/

@[expose] public section

namespace Combinatorics

namespace UlamHarris

namespace Tree

variable {α : Type*} [LT α]

/-- The tree consisting of the addresses of `T` of generation at most `n`. -/
def truncate (T : Tree α) (n : ℕ) : Tree α where
  carrier := {u | u.length ≤ n ∧ u ∈ T.carrier}
  root_mem := ⟨by simp, T.root_mem⟩
  parent_closed := by
    rintro u v ⟨huv, hm⟩
    refine ⟨?_, T.parent_closed hm⟩
    have h : u.length ≤ (u ++ v).length := by simp [List.length_append]
    omega
  sibling_closed := by
    rintro u i j ⟨hlen, hm⟩ hij
    refine ⟨?_, T.sibling_closed hm hij⟩
    simp only [List.length_append, List.length_cons, List.length_nil] at hlen ⊢
    omega

@[simp] theorem mem_truncate {T : Tree α} {n : ℕ} {u : List α} :
    u ∈ (T.truncate n).carrier ↔ u.length ≤ n ∧ u ∈ T.carrier := Iff.rfl

theorem truncate_subset (T : Tree α) (n : ℕ) :
    (T.truncate n).carrier ⊆ T.carrier := fun _ hu => hu.2

@[simp] theorem truncate_truncate (T : Tree α) (n m : ℕ) :
    (T.truncate n).truncate m = T.truncate (min n m) := by
  ext u
  simp only [mem_truncate]
  constructor
  · rintro ⟨hm, hn, hu⟩
    exact ⟨Nat.le_min.2 ⟨hn, hm⟩, hu⟩
  · rintro ⟨hmin, hu⟩
    exact ⟨(Nat.le_min.1 hmin).2, (Nat.le_min.1 hmin).1, hu⟩

/-- The truncation ball around `T` of height `n`: the trees with the same
truncation as `T` up to generation `n`. -/
def truncationBall (T : Tree α) (n : ℕ) : Set (Tree α) :=
  {S | S.truncate n = T.truncate n}

@[simp] theorem mem_truncationBall {S T : Tree α} {n : ℕ} :
    S ∈ truncationBall T n ↔ S.truncate n = T.truncate n := Iff.rfl

/-- Truncation balls of the same height with different centers are disjoint. -/
theorem truncationBall_disjoint {S T : Tree α} {n : ℕ}
    (h : S.truncate n ≠ T.truncate n) :
    truncationBall S n ∩ truncationBall T n = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro X hX
  rw [Set.mem_inter_iff, mem_truncationBall, mem_truncationBall] at hX
  exact h (hX.1.symm.trans hX.2)

end Tree

end UlamHarris

end Combinatorics

end
