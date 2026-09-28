import Probability.BranchingRandomWalk.Population.Processes.Causal.RelativePosition
import Probability.BranchingRandomWalk.Spine.Path.Window

/-!
# Causal populations and path-window events

This file connects the genealogical killed-process representation to the
finite-history events consumed by path-functional many-to-one identities.
-/

namespace ProbabilityTheory.BranchingRandomWalk
namespace RootIndexed.CausalFinitePopulation

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

/-- A particle retained by the restarted killed process determines a path in
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
    ⟨RootIndexed.restartAnchor cutoff k,
      (RootIndexed.restartAnchor_le cutoff k).trans_lt k.2⟩
  rw [pathHistory_eq_positionAtGeneration initialPosition d hd n field q
      hqdepth k,
    pathHistory_eq_positionAtGeneration initialPosition d hd n field q
      hqdepth anchor]
  by_cases hk : k.val = 0
  · have hanchor : anchor.val = 0 := by simp [anchor, hk, RootIndexed.restartAnchor]
    have hkeq : k = anchor := Fin.ext (hk.trans hanchor.symm)
    rw [hkeq, sub_self]
    simpa [hanchor] using hzero
  · have hkpos : 0 < k.val := Nat.pos_of_ne_zero hk
    have hwindowPath := mem_ofRestartedRealPositionSets_all_windows
      initialPosition d hd initial hinitialDepth cutoff window hwindow upper
      hupper hq hkpos (Nat.le_of_lt_succ k.2)
    simpa [RootIndexed.relativePositionAtGeneration, anchor,
      List.take_take, Nat.min_eq_left
        (RootIndexed.restartAnchor_le cutoff k)] using hwindowPath

end RootIndexed.CausalFinitePopulation
end ProbabilityTheory.BranchingRandomWalk
