/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Population.Processes.Causal.RelativePosition.Real
public import Probability.BranchingRandomWalk.Spine.Path.Basic
public import Probability.BranchingRandomWalk.Walk.Path.Window
public import Probability.Process.Path.Restart.Basic

public import Mathlib.Basic.Countable.Defs
public import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-!
# Causal populations and path-window events

## Public declarations

* `ProbabilityTheory.BranchingRandomWalk.RootIndexed.CausalPopulation.pathHistory_eq_positionAtGeneration` identifies the spine path history at
  generation `k` with the selected particle's position at generation `k`.
* `ProbabilityTheory.BranchingRandomWalk.RootIndexed.CausalPopulation.mem_ofRestartedRealPositionSets_inRestartedWindows` shows that membership
  in the restarted selected population implies that every restarted path window
  condition holds.
* `ProbabilityTheory.BranchingRandomWalk.RootIndexed.CausalPopulation.mem_ofRestartedRealPositionSets_of_path` proves the converse from a
  surviving path with finite strict-ancestor weights and all prescribed window
  conditions.

This file connects the genealogical selection-process representation to the
finite-history events consumed by path-functional many-to-one identities.

For a path history `H_n` and restart anchor `a_c(k)`, the path event and its
relation to the selected population are

\[\begin{aligned}
\operatorname{InRestartedWindows}(c,W,H_n)
&\Longleftrightarrow
  \forall k\le n,\ H_n(k)-H_n(a_c(k))\in W_k,\\
q\in P_n(\omega)
&\Longrightarrow
  \operatorname{InRestartedWindows}
    \bigl(c,W,\operatorname{pathHistory}(q,\omega)\bigr),\\
\operatorname{pathHistory}(q,\omega)(k)
&=\operatorname{positionAtGeneration}(q_{\le k},\omega).
\end{aligned}\]
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching.Walk
open ProbabilityTheory.RandomWalk
open scoped ENNReal
open ProbabilityTheory.Process.Path
namespace RootIndexed.CausalPopulation

open Combinatorics.UlamHarris Combinatorics.Branching
open ProbabilityTheory.BranchingRandomWalk.Spine

theorem pathHistory_eq_positionAtGeneration
    {Root α Mark : Type*} [MeasurableSpace Mark]
    (initialPosition : Root → ℝ) (d : Mark → ℝ) (hd : Measurable d)
    (n : ℕ) (field : RootIndexed.StepField Root α Mark)
    (q : RootIndexed.TreeNode Root α) (hqdepth : q.2.length = n)
    (k : Fin (n + 1)) :
    pathHistory (⟨d, hd⟩ : Potential Mark) n (initialPosition q.1)
        (field q.1) q.2 k =
      RootIndexed.positionAtGeneration initialPosition d k q.1
        (q.2.take k) field := by
  have htake : (q.2.take k).length = k := by
    simp [List.length_take, hqdepth, Nat.min_eq_left (Nat.le_of_lt_succ k.2)]
  simp [pathHistory, Spine.pathPotential, RootIndexed.positionAtGeneration,
    RootIndexed.position, RootIndexed.displace, htake]

/-- A particle retained by the restarted selected process determines a path in
the corresponding measurable restarted-window event. -/
theorem mem_ofRestartedRealPositionSets_inRestartedWindows
    {Root α Mark : Type*} [Countable α] [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    (initialPosition : Root → ℝ) (d : Mark → ℝ)
    (hd : Measurable d) (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (cutoff : ℕ)
    (window : ℕ → Set ℝ) (hwindow : ∀ n, MeasurableSet (window n))
    (hzero : 0 ∈ window 0)
    (upper : ℕ → ℝ) (hupper : ∀ n, window n ⊆ Set.Iic (upper n))
    {n : ℕ} {field : RootIndexed.StepField Root α Mark}
    {q : RootIndexed.TreeNode Root α}
    (hq : q ∈ ofRestartedRealPositionSets initialPosition d hd initial
      hinitialDepth cutoff window hwindow upper hupper n field) :
    InRestartedWindows cutoff window
      (pathHistory (⟨d, hd⟩ : Potential Mark) n (initialPosition q.1)
        (field q.1) q.2) := by
  have hqdepth : q.2.length = n :=
    (ofRestartedRealPositionSets initialPosition d hd initial hinitialDepth
      cutoff window hwindow upper hupper).depth n field q hq
  intro k
  let anchor : Fin (n + 1) :=
    ⟨restartAnchor cutoff k,
      (restartAnchor_le cutoff k).trans_lt k.2⟩
  rw [pathHistory_eq_positionAtGeneration initialPosition d hd n field q
      hqdepth k,
    pathHistory_eq_positionAtGeneration initialPosition d hd n field q
      hqdepth anchor]
  by_cases hk : k.val = 0
  · have hanchor : anchor.val = 0 := by simp [anchor, hk, restartAnchor]
    have hkeq : k = anchor := Fin.ext (hk.trans hanchor.symm)
    rw [hkeq, sub_self]
    simpa [hanchor] using hzero
  · have hkpos : 0 < k.val := Nat.pos_of_ne_zero hk
    have hwindowPath := mem_ofRestartedRealPositionSets_all_windows
      initialPosition d hd initial hinitialDepth cutoff window hwindow upper
      hupper hq hkpos (Nat.le_of_lt_succ k.2)
    simpa [RootIndexed.relativePositionAtGeneration, anchor,
      List.take_take, Nat.min_eq_left
        (restartAnchor_le cutoff k)] using hwindowPath

/-- A surviving finite path whose restarted positions remain in the prescribed
windows is retained by the corresponding restarted population, provided its
strict ancestral exponential weights are finite. This is the path-to-population
direction complementary to `mem_ofRestartedRealPositionSets_inRestartedWindows`.
-/
theorem mem_ofRestartedRealPositionSets_of_path
    {Root α Mark : Type*} [Countable α] [MeasurableSpace Mark]
    [MeasurableSpace (RootIndexed.TreeNode Root α)]
    (initialPosition : Root → ℝ) (d : Mark → ℝ) (hd : Measurable d)
    (initial : Finset (RootIndexed.TreeNode Root α))
    (hinitialDepth : ∀ p ∈ initial, p.2.length = 0)
    (cutoff n : ℕ) (window : ℕ → Set ℝ)
    (hwindow : ∀ k, MeasurableSet (window k)) (upper : ℕ → ℝ)
    (hupper : ∀ k, window k ⊆ Set.Iic (upper k))
    (field : RootIndexed.StepField Root α Mark) (r : Root) (u : List α)
    (hu : u.length = n)
    (hroot : (r, []) ∈ initial)
    (hsurvive : surviveAlong (field r) [] u)
    (hweight : ∀ v, v.length < n →
      totalPotentialWeight (⟨d, hd⟩ : Potential Mark) (-1)
        (field r v) ≠ ∞)
    (hwindowPath : ∀ k ≤ n,
      RootIndexed.relativePositionAtGeneration initialPosition d
        (restartAnchor cutoff k) k (r, u.take k) field ∈ window k) :
    (r, u) ∈ RootIndexed.CausalPopulation.ofRestartedRealPositionSets
      initialPosition d hd initial hinitialDepth cutoff window
      hwindow upper hupper n field := by
  classical
  let potential : Potential Mark := ⟨d, hd⟩
  let keep : ℕ → RootIndexed.StepField Root α Mark →
      RootIndexed.TreeNode Root α → Prop := fun k sample q =>
    (k = 0 ∨ q.2.length ≠ k ∨
      totalPotentialWeight potential (-1)
        (sample (RootIndexed.parent q).1 (RootIndexed.parent q).2) ≠ ∞) ∧
      RootIndexed.relativePositionAtGeneration initialPosition d
        (restartAnchor cutoff k) k q sample ∈ window k
  let finite : ∀ (k : ℕ) (parents : Finset (RootIndexed.TreeNode Root α))
      (sample : RootIndexed.StepField Root α Mark),
      {q | q ∈ Combinatorics.Branching.Population.childrenAtGeneration k parents sample ∧
        keep (k + 1) sample q}.Finite := by
    intro k parents sample
    let goodParents := parents.filter fun p =>
      totalPotentialWeight potential (-1) (sample p.1 p.2) ≠ ∞
    have hfinite :
        {q | q ∈ Combinatorics.Branching.Population.childrenAtGeneration k goodParents sample ∧
          RootIndexed.relativePositionAtGeneration initialPosition d
            (restartAnchor cutoff (k + 1)) (k + 1) q sample ∈
              window (k + 1)}.Finite := by
      apply Combinatorics.Branching.Population.childrenAtGeneration_filter_finite_of_upperBound
        k goodParents sample
        (fun q => RootIndexed.relativePositionAtGeneration initialPosition d
          (restartAnchor cutoff (k + 1)) (k + 1) q sample)
        (window (k + 1)) (upper (k + 1)) (hupper (k + 1))
      intro p hp hpdepth a
      have hpweight : totalPotentialWeight potential (-1)
          (sample p.1 p.2) ≠ ∞ := (Finset.mem_filter.mp hp).2
      let parentRelative := RootIndexed.relativePositionAtGeneration
        initialPosition d (restartAnchor cutoff (k + 1)) k p sample
      have hstep := finite_realized_children_potential_below
        (φ := potential) (sample p.1 p.2) hpweight (a - parentRelative)
      apply hstep.subset
      intro j hj
      refine ⟨hj.1, ?_⟩
      have hpotential :
          (sample p.1 p.2).potentialValue' potential j =
            value' ((sample p.1 p.2).map d) j := by
        cases hslot : sample p.1 p.2 j <;>
          simp [Step.map, value', Step.potentialValue', Step.potentialAt?,
            potential, hslot]
      rw [hpotential]
      apply le_sub_iff_add_le.mpr
      rw [add_comm]
      rw [← RootIndexed.relativePositionAtGeneration_child initialPosition d
        sample (restartAnchor_succ_le_parent cutoff k) p hpdepth j]
      exact hj.2
    apply hfinite.subset
    intro q hq
    obtain ⟨p, hp, hpdepth, j, hj, rfl⟩ :=
      (Combinatorics.Branching.Population.mem_childrenAtGeneration_iff k parents sample q).mp hq.1
    have hpweight : totalPotentialWeight potential (-1)
        (sample p.1 p.2) ≠ ∞ := by
      have hguard := hq.2.1
      simp [hpdepth] at hguard
      exact hguard
    refine ⟨Combinatorics.Branching.Population.childAddress_mem_childrenAtGeneration k goodParents
      sample p (Finset.mem_filter.mpr ⟨hp, hpweight⟩) hpdepth j hj, ?_⟩
    exact hq.2.2
  change (r, u) ∈ RootIndexed.CausalPopulation.ofRestartedRealPositionSets
      initialPosition d hd initial hinitialDepth cutoff window
      hwindow upper hupper n field
  induction n generalizing u with
  | zero =>
      have hu0 : u = [] := List.eq_nil_of_length_eq_zero hu
      subst u
      change (r, []) ∈ initial
      exact hroot
  | succ n ih =>
      have hne : u ≠ [] := by
        intro hu'
        simp [hu'] at hu
      let i : α := u.getLast hne
      let v : List α := u.dropLast
      have happend : u = v ++ [i] := by
        dsimp [v, i]
        exact (List.dropLast_append_getLast hne).symm
      have hvlen : v.length = n := by
        dsimp [v]
        rw [List.length_dropLast, hu]
        omega
      have hsurviveSplit : surviveAlong (field r) [] v ∧
          survive (field r v) i := by
        rw [happend] at hsurvive
        exact (surviveAlong_append_singleton (field r) [] v i).mp hsurvive
      have hwindowParent : ∀ k ≤ n,
          RootIndexed.relativePositionAtGeneration initialPosition d
            (restartAnchor cutoff k) k (r, v.take k) field ∈ window k := by
        intro k hk
        have hk' : k ≤ n + 1 := by omega
        have htake : u.take k = v.take k := by
          rw [happend]
          exact List.take_append_of_le_length (by simpa [v, hvlen] using hk)
        rw [← htake]
        exact hwindowPath k hk'
      have hweightParent : ∀ w, w.length < n →
          totalPotentialWeight potential (-1) (field r w) ≠ ∞ := by
        intro w hw
        exact hweight w (by omega)
      have hparent : (r, v) ∈
          RootIndexed.CausalPopulation.ofRestartedRealPositionSets
            initialPosition d hd initial hinitialDepth cutoff
            window hwindow upper hupper n field := by
        exact ih v hvlen hsurviveSplit.1 hweightParent hwindowParent
      have hparentSelected : (r, v) ∈
          RootIndexed.CausalPopulation.selectedBy initial keep finite n field := by
        change (r, v) ∈
          RootIndexed.CausalPopulation.selectedBy initial keep finite n field at hparent
        exact hparent
      change (r, u) ∈ RootIndexed.CausalPopulation.ofRestartedRealPositionSets
        initialPosition d hd initial hinitialDepth cutoff window
        hwindow upper hupper (n + 1) field
      change (r, u) ∈ RootIndexed.CausalPopulation.selectedBy
        initial keep finite (n + 1) field
      rw [RootIndexed.CausalPopulation.mem_selectedBy_succ
        (initial := initial) (keep := keep) (hfinite := finite)
        (n := n) (field := field) (q := (r, u))]
      refine ⟨?_, ?_⟩
      · exact (Combinatorics.Branching.Population.mem_childrenAtGeneration_iff n
          (RootIndexed.CausalPopulation.selectedBy initial keep finite n field)
          field (r, u)).2
          ⟨(r, v), hparentSelected, hvlen, i, hsurviveSplit.2,
            congrArg (fun address => (r, address)) happend⟩
      · refine ⟨?_, ?_⟩
        · right
          right
          simpa [potential, RootIndexed.parent, happend, hu] using
            hweight v (by rw [hvlen]; exact Nat.lt_succ_self n)
        · have htakeEnd : u.take (n + 1) = u :=
            List.take_of_length_le (Nat.le_of_eq hu)
          simpa [htakeEnd] using hwindowPath (n + 1) (Nat.le_refl _)


end RootIndexed.CausalPopulation
end ProbabilityTheory.BranchingRandomWalk

end
