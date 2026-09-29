module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.Finset.Max

/-!
# Acyclicity from a height function

A simple graph is acyclic as soon as it carries a height function in which every
vertex has at most one neighbour of height not exceeding its own. A cycle would
contain a vertex of maximal height, whose two neighbours on the cycle both have
height at most its own, hence both are that unique neighbour.

This file is a mathlib candidate: `Mathlib.Combinatorics.SimpleGraph.Acyclic`
has no height criterion, and this statement is independent of any application. It
lives at the mathlib path so that it can be upstreamed; the package root mirrors
the mathlib root without the `Mathlib.` prefix, which is reserved for the
dependency.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*}

/-- A simple graph in which every vertex has at most one neighbour of height not
exceeding its own is acyclic. -/
theorem isAcyclic_of_height (G : SimpleGraph V) (height : V → ℕ)
    (huniq : ∀ ⦃a b c⦄, G.Adj a c → G.Adj b c →
      height a ≤ height c → height b ≤ height c → a = b) :
    G.IsAcyclic := by
  intro v c hc
  have key : ∀ (m x y : V), G.Adj x m → G.Adj y m →
      height x ≤ height m → height y ≤ height m → x = y :=
    fun m x y hx hy hxl hyl => huniq hx hy hxl hyl
  obtain ⟨k, hk_mem, hk_max⟩ := Finset.exists_max_image (Finset.Icc 0 c.length)
    (fun i => height (c.getVert i)) ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩⟩
  have hk_le : k ≤ c.length := (Finset.mem_Icc.mp hk_mem).2
  have hmax : ∀ i ≤ c.length, height (c.getVert i) ≤ height (c.getVert k) :=
    fun i hi => hk_max i (Finset.mem_Icc.mpr ⟨Nat.zero_le _, hi⟩)
  have hlen3 : 3 ≤ c.length := hc.three_le_length
  have hadj₁ : G.Adj (c.getVert (c.length - 1)) (c.getVert 0) := by
    have h := c.adj_getVert_succ (show c.length - 1 < c.length by omega)
    rw [Nat.sub_add_cancel (show 1 ≤ c.length by omega)] at h
    rw [c.getVert_length] at h
    simpa [c.getVert_zero] using h
  have hadj₂ : G.Adj (c.getVert 1) (c.getVert 0) := by
    have h : G.Adj (c.getVert 0) (c.getVert 1) :=
      c.adj_getVert_succ (show 0 < c.length by omega)
    exact h.symm
  by_cases hk_end : k = 0 ∨ k = c.length
  · -- the maximum is attained at the base vertex, at one of the two copies
    have hmax0 : ∀ i ≤ c.length, height (c.getVert i) ≤ height (c.getVert 0) := by
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
    have hidx₁ : G.Adj (c.getVert (k - 1)) (c.getVert k) := by
      have h := c.adj_getVert_succ (show k - 1 < c.length by omega)
      rwa [Nat.sub_add_cancel (show 1 ≤ k by omega)] at h
    have hidx₂ : G.Adj (c.getVert (k + 1)) (c.getVert k) :=
      (c.adj_getVert_succ hklt).symm
    have heq := key _ _ _ hidx₁ hidx₂ (hmax _ (by omega)) (hmax _ (by omega))
    exact (hc.getVert_sub_one_ne_getVert_add_one hk_le) heq

end SimpleGraph

end
