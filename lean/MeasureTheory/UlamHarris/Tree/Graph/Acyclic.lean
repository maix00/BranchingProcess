import MeasureTheory.UlamHarris.Tree.Graph.Basic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Max

/-!
# The projected graph of a tree is acyclic

The underlying undirected graph of a tree has no cycles. The proof uses the
address length as a height on the cycle: adjacent nodes have different lengths,
and every node has at most one parent (`Tree.parentRel_left_unique`). A cycle
contains a node of maximal length, whose two neighbours along the cycle are
both shorter, hence both are its parents, hence equal. This contradicts the
injectivity of the vertex sequence of a cycle.
-/

namespace MeasureTheory

namespace UlamHarris

namespace Tree

variable {α : Type*} [LT α]

/-- Adjacent nodes of the child graph have different address lengths. -/
theorem childGraph_adj_length_ne {T : Tree α} {a b : ↥T.carrier}
    (h : (childGraph T).Adj a b) : a.1.length ≠ b.1.length := by
  rcases childGraph_adj.mp h with h | h
  · exact (parentRel_length_lt h).ne
  · exact (parentRel_length_lt h).ne'

/-- The first endpoint of an edge of smaller length is the parent. -/
theorem parentRel_of_childGraph_adj_of_length_lt {T : Tree α} {a b : ↥T.carrier}
    (h : (childGraph T).Adj a b) (hlt : a.1.length < b.1.length) : parentRel a.1 b.1 := by
  rcases childGraph_adj.mp h with h' | h'
  · exact h'
  · exact absurd (parentRel_length_lt h') (not_lt.mpr hlt.le)

/-- The underlying undirected graph of a tree is acyclic. -/
theorem childGraph_isAcyclic (T : Tree α) : (childGraph T).IsAcyclic := by
  classical
  intro v c hc
  -- A node of maximal length has two neighbours of smaller length, both of
  -- which are its parents, so they coincide.
  have key : ∀ (m x y : ↥T.carrier), (childGraph T).Adj x m → (childGraph T).Adj y m →
      x.1.length ≤ m.1.length → y.1.length ≤ m.1.length → x = y := by
    intro m x y hx hy hxl hyl
    have hxlt : x.1.length < m.1.length :=
      lt_of_le_of_ne hxl (childGraph_adj_length_ne hx)
    have hylt : y.1.length < m.1.length :=
      lt_of_le_of_ne hyl (childGraph_adj_length_ne hy)
    exact Subtype.ext (parentRel_left_unique
      (parentRel_of_childGraph_adj_of_length_lt hx hxlt)
      (parentRel_of_childGraph_adj_of_length_lt hy hylt))
  obtain ⟨k, hk_mem, hk_max⟩ := Finset.exists_max_image (Finset.Icc 0 c.length)
    (fun i => (c.getVert i).1.length) ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩⟩
  have hk_le : k ≤ c.length := (Finset.mem_Icc.mp hk_mem).2
  have hmax : ∀ i ≤ c.length,
      (c.getVert i).1.length ≤ (c.getVert k).1.length :=
    fun i hi => hk_max i (Finset.mem_Icc.mpr ⟨Nat.zero_le _, hi⟩)
  have hlen3 : 3 ≤ c.length := hc.three_le_length
  have hadj₁ : (childGraph T).Adj (c.getVert (c.length - 1)) (c.getVert 0) := by
    have h := c.adj_getVert_succ (show c.length - 1 < c.length by omega)
    rw [Nat.sub_add_cancel (show 1 ≤ c.length by omega)] at h
    rw [c.getVert_length] at h
    simpa [c.getVert_zero] using h
  have hadj₂ : (childGraph T).Adj (c.getVert 1) (c.getVert 0) := by
    have h : (childGraph T).Adj (c.getVert 0) (c.getVert 1) :=
      c.adj_getVert_succ (show 0 < c.length by omega)
    exact h.symm
  by_cases hk_end : k = 0 ∨ k = c.length
  · -- the maximum is attained at the base vertex, at one of the two copies
    have hmax0 : ∀ i ≤ c.length,
        (c.getVert i).1.length ≤ (c.getVert 0).1.length := by
      intro i hi
      have h := hmax i hi
      rcases hk_end with hk | hk
      · simpa [hk] using h
      · rw [hk, c.getVert_length] at h
        simpa [c.getVert_zero] using h
    have heq := key _ _ _ hadj₁ hadj₂ (hmax0 _ (by omega)) (hmax0 _ (by omega))
    have hne : c.length - 1 = 1 :=
      hc.getVert_injOn (by simp only [Set.mem_ofPred_eq]; omega)
        (by simp only [Set.mem_ofPred_eq]; omega) heq
    omega
  · -- the maximum is attained strictly inside the cycle
    have hk0 : k ≠ 0 := fun h => hk_end (Or.inl h)
    have hklen : k ≠ c.length := fun h => hk_end (Or.inr h)
    have hklt : k < c.length := lt_of_le_of_ne hk_le hklen
    have hidx₁ : (childGraph T).Adj (c.getVert (k - 1)) (c.getVert k) := by
      have h := c.adj_getVert_succ (show k - 1 < c.length by omega)
      rwa [Nat.sub_add_cancel (show 1 ≤ k by omega)] at h
    have hidx₂ : (childGraph T).Adj (c.getVert (k + 1)) (c.getVert k) :=
      (c.adj_getVert_succ hklt).symm
    have heq := key _ _ _ hidx₁ hidx₂ (hmax _ (by omega)) (hmax _ (by omega))
    exact (hc.getVert_sub_one_ne_getVert_add_one hk_le) heq

end Tree

end UlamHarris

end MeasureTheory
