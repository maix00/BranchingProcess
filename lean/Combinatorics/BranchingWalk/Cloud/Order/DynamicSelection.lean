import Combinatorics.BranchingWalk.Cloud.Order.Matching
import Combinatorics.BranchingWalk.Selection.NSelection.Matching

/-!
# Address-order-free domination under dynamic leftmost selection

This is the deterministic one-generation selection step used in the coupling.
The target candidates are sorted by their observed positions at the current
slice, with particle labels only breaking ties.  Hall's theorem turns the
resulting threshold comparison into one coherent injective particle matching.
-/

open Combinatorics.UlamHarris

namespace Combinatorics.Branching

open Selection.NSelection

variable {Time Root α Position Value : Type*}

/-- An injective spatial matching bounds every finite lower-tail count. -/
theorem Cloud.filter_card_le_of_injectivelyDominatesBy
    [Preorder Value] [DecidableRel (· ≤ · : Value → Value → Prop)]
    (φ : Position → Value) {C D : Cloud Time Root α Position} (t : Time)
    (hCfinite : (C.particles t).Finite)
    (hDfinite : (D.particles t).Finite)
    (hdom : C.InjectivelyDominatesBy φ D t) (a : Value) :
    (hCfinite.toFinset.filter fun p => φ (C.position p.1 p.2) ≤ a).card ≤
      (hDfinite.toFinset.filter fun q => φ (D.position q.1 q.2) ≤ a).card := by
  classical
  obtain ⟨f, hfmem, hfinj, hfle⟩ := hdom
  apply Finset.card_le_card_of_injOn f
  · intro p hp
    obtain ⟨hpC, hpvalue⟩ := Finset.mem_filter.mp hp
    apply Finset.mem_filter.mpr
    exact ⟨hDfinite.mem_toFinset.mpr (hfmem (hCfinite.mem_toFinset.mp hpC)),
      (hfle p (hCfinite.mem_toFinset.mp hpC)).trans hpvalue⟩
  · intro p hp q hq hpq
    exact hfinj
      (hCfinite.mem_toFinset.mp (Finset.mem_filter.mp hp).1)
      (hCfinite.mem_toFinset.mp (Finset.mem_filter.mp hq).1) hpq

/-- A retained subpopulation of at most `N` particles is injectively dominated
by the dynamic leftmost `N` selection from a dominating target candidate
cloud.  No order compatibility for Ulam--Harris addresses is assumed. -/
theorem Cloud.injectivelyDominatesBy_keepFirstBy_of_subset
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (φ : Position → Value) (N : ℕ)
    (C D : Cloud Time Root α Position) (t : Time)
    (hCfinite : (C.particles t).Finite)
    (hDfinite : (D.particles t).Finite)
    (retained : Finset (RootIndexed.TreeNode Root α))
    (hretained : ↑retained ⊆ C.particles t)
    (hcard : retained.card ≤ N)
    (hdom : C.InjectivelyDominatesBy φ D t) :
    (C.withFinsetParticles (fun _ => retained)).InjectivelyDominatesBy φ
      (D.withFinsetParticles (fun _ =>
        keepFirstBy N (fun q => φ (D.position q.1 q.2)) hDfinite.toFinset)) t := by
  classical
  let selected := keepFirstBy N (fun q => φ (D.position q.1 q.2)) hDfinite.toFinset
  have hretainedFinset : retained ⊆ hCfinite.toFinset := by
    intro p hp
    exact hCfinite.mem_toFinset.mpr (hretained hp)
  have hthreshold : ∀ a : Value,
      (hCfinite.toFinset.filter fun p => φ (C.position p.1 p.2) ≤ a).card ≤
        (hDfinite.toFinset.filter fun q => φ (D.position q.1 q.2) ≤ a).card :=
    fun a => C.filter_card_le_of_injectivelyDominatesBy φ t
      hCfinite hDfinite hdom a
  obtain ⟨f, hfmem, hfle, hfinj⟩ :=
    exists_injective_le_keepFirstBy N
      (fun p => φ (C.position p.1 p.2))
      (fun q => φ (D.position q.1 q.2))
      retained hCfinite.toFinset hDfinite.toFinset
      hretainedFinset hcard hthreshold
  let matchParticle : RootIndexed.TreeNode Root α → RootIndexed.TreeNode Root α :=
    fun p => if hp : p ∈ retained then f p hp else p
  refine ⟨matchParticle, ?_, ?_, ?_⟩
  · intro p hp
    have hpr : p ∈ retained := by simpa using hp
    change matchParticle p ∈ selected
    simpa [matchParticle, selected, hpr] using hfmem p hpr
  · intro p hp q hq heq
    have hpr : p ∈ retained := by simpa using hp
    have hqr : q ∈ retained := by simpa using hq
    apply hfinj p hpr q hqr
    simpa only [matchParticle, dite_eq_left hpr, dite_eq_left hqr] using heq
  · intro p hp
    have hpr : p ∈ retained := by simpa using hp
    simpa only [Cloud.withFinsetParticles_position, matchParticle,
      dite_eq_left hpr] using hfle p hpr

end Combinatorics.Branching
