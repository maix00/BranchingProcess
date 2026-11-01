/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Cloud.Order.SliceDominatingMap
public import Combinatorics.Selection.NSelection.Matching.Hall

/-!
# Address-order-free domination under dynamic leftmost selection

The target candidates are ordered by their observed positions at the current
slice, with particle labels breaking ties. The finite lower-level-set count
bound follows from `Order.DominatingMap.card_filter_le`; Hall's theorem then
produces one injective matching into the selected target population.

## Public declarations

If the cloud \(C\) injectively dominates \(D\) at time \(t\), then every
retained source set \(R_t\subseteq C_t\) of size at most \(N\) injectively dominates the
target's first \(N\) particles ordered by observed position, with particle
labels breaking ties:

\[R_t\subseteq C_t,\quad |R_t|\le N,\quad
  C\succeq_{\mathrm{inj},\phi}D
  \Longrightarrow
  C_R\succeq_{\mathrm{inj},\phi}D^{[N]}_{\phi,t}.\]

Here \(C_R\) is \(C\) restricted to \(R_t\), and
\(D^{[N]}_{\phi,t}:=\operatorname{selectFirstNBy}
(N,q\mapsto\phi(\operatorname{position}_D(q)),D_t)\).
The relation \(\succeq_{\mathrm{inj},\phi}\) denotes injective domination
after observing positions through \(\phi\).

- `Cloud.injectivelyDominatesBy_selectFirstNBy_of_subset` says that a retained
  source set `R ⊆ C.particles t` with `card(R) ≤ N` is injectively dominated by
  the target set selected by `selectFirstNBy N`, whenever `C` injectively
  dominates `D`. No compatibility between address order and observed values
  is required.
-/

open Combinatorics.UlamHarris

@[expose] public section

namespace Combinatorics.Branching

open Selection.NSelection

variable {Time Root α Position Value : Type*}

/-- A retained subpopulation of at most `N` particles is injectively dominated
by the dynamic leftmost `N` selection from a dominating target candidate
cloud. No order compatibility for Ulam--Harris addresses is assumed. -/
theorem Cloud.injectivelyDominatesBy_selectFirstNBy_of_subset
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
        selectFirstNBy N (fun q => φ (D.position q.1 q.2)) hDfinite.toFinset)) t := by
  classical
  let selected := selectFirstNBy N (fun q => φ (D.position q.1 q.2)) hDfinite.toFinset
  obtain ⟨g, hgmem, hginj, hgle⟩ := hdom
  let dominatingMap : Order.DominatingMap (C.particles t) (D.particles t)
      (fun p => φ (C.position p.1 p.2))
      (fun q => φ (D.position q.1 q.2)) := ⟨g, hgmem, hginj, hgle⟩
  have hretainedFinset : retained ⊆ hCfinite.toFinset := by
    intro p hp
    exact hCfinite.mem_toFinset.mpr (hretained hp)
  have hthreshold : ∀ a : Value,
      (hCfinite.toFinset.filter fun p => φ (C.position p.1 p.2) ≤ a).card ≤
        (hDfinite.toFinset.filter fun q => φ (D.position q.1 q.2) ≤ a).card := by
    intro a
    exact dominatingMap.card_filter_le hCfinite hDfinite a
  obtain ⟨f, hfmem, hfle, hfinj⟩ :=
    exists_injective_le_selectFirstNBy N
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

end
