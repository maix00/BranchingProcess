/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module
public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Selection.InfiniteOffspring.Array.Basic
import all Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Selection.InfiniteOffspring.Array.Lemmas.Subadditivity

/-!
# Subadditive array for infinite-offspring selection

## Public declarations

`infiniteSelectionSubadditiveArray_subadditive` proves
\[A_b(s,m+n)\le A_b(s,m)+A_b(s+m,n).\]
`infiniteSelectionSubadditiveArray_abs_le` bounds its absolute value at the
origin by the sum of the generation-wise leftmost-child envelopes.
`infiniteSelectionSubadditiveArray_shift_covariant` gives covariance under
shifting the deterministic offspring sequence. The endpoint-indexed array
satisfies the corresponding ordered-endpoint subadditivity and shift identity
through `infiniteSelectionEndpointArray_subadditive` and
`infiniteSelectionEndpointArray_shift_covariant`.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection
open scoped ENNReal

/-- Under an increasing slot enumeration with one leftmost child for every
parent, the absolute displacement of the left endpoint is controlled by the
sum of the generation-wise leftmost-child envelopes. -/
theorem infiniteSelectionSubadditiveArray_abs_le {N : ℕ}
    (hN : 0 < N) (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (hordered : ∀ t i, (offspring t i).IsOrderedBy realPotential)
    (hfirst : ∀ t i, survive (offspring t i) 0) (n : ℕ) :
    |infiniteSelectionSubadditiveArray hN offspring hgood 0 n| ≤
      ∑ t ∈ Finset.range n, infiniteOffspringBatchSlotZeroNorm hN (offspring t) := by
  unfold infiniteSelectionSubadditiveArray infiniteSelectionBlockMinimum
  have hrun := infiniteOffspringRun_stateNorm_le hN offspring hgood
    hordered hfirst (fun _ => 0) n
  have hcoord : |infiniteOffspringRun offspring hgood (fun _ => 0) n ⟨0, hN⟩| ≤
      infiniteSelectionStateNorm hN
        (infiniteOffspringRun offspring hgood (fun _ => 0) n) :=
    abs_position_le_infiniteSelectionStateNorm hN _ ⟨0, hN⟩
  have hinitialNorm : infiniteSelectionStateNorm hN (fun _ : Fin N => (0 : ℝ)) = 0 := by
    unfold infiniteSelectionStateNorm
    rw [Finset.sup'_const]
    simp
  rw [hinitialNorm] at hrun
  simpa [infiniteSelectionStateNorm] using hcoord.trans hrun

theorem infiniteSelectionSubadditiveArray_subadditive
    {N : ℕ} (hN : 0 < N)
    (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (start firstLength secondLength : ℕ) :
    infiniteSelectionSubadditiveArray hN offspring hgood start
        (firstLength + secondLength) ≤
      infiniteSelectionSubadditiveArray hN offspring hgood start firstLength +
        infiniteSelectionSubadditiveArray hN offspring hgood (start + firstLength)
          secondLength := by
  unfold infiniteSelectionSubadditiveArray
  linarith [infiniteSelectionBlockMinimum_subadditive hN offspring hgood
    start firstLength secondLength]

theorem infiniteSelectionSubadditiveArray_shift_covariant
    {N : ℕ} (hN : 0 < N)
    (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (shift start length : ℕ) :
    infiniteSelectionSubadditiveArray hN
        (fun t => offspring (shift + t)) (fun t => hgood (shift + t))
        start length =
      infiniteSelectionSubadditiveArray hN offspring hgood (shift + start) length := by
  simp only [infiniteSelectionSubadditiveArray,
    infiniteSelectionBlockMinimum_shift_covariant]

theorem infiniteSelectionEndpointArray_subadditive
    {N : ℕ} (hN : 0 < N)
    (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (start firstLength secondLength : ℕ) :
    infiniteSelectionEndpointArray hN offspring hgood 0 (start + firstLength + secondLength) ≤
      infiniteSelectionEndpointArray hN offspring hgood 0 start +
        infiniteSelectionEndpointArray hN offspring hgood start
          (start + firstLength + secondLength) := by
  simpa [infiniteSelectionEndpointArray, Nat.add_assoc,
    Nat.add_sub_cancel_left] using
    infiniteSelectionSubadditiveArray_subadditive hN offspring hgood
      0 start (firstLength + secondLength)

theorem infiniteSelectionEndpointArray_shift_covariant
    {N : ℕ} (hN : 0 < N)
    (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (shift start endpoint : ℕ) (horder : start ≤ endpoint) :
    infiniteSelectionEndpointArray hN
        (fun t => offspring (shift + t)) (fun t => hgood (shift + t))
        start endpoint =
      infiniteSelectionEndpointArray hN offspring hgood
        (shift + start) (shift + endpoint) := by
  have hlength : (shift + endpoint) - (shift + start) = endpoint - start := by
    omega
  simp only [infiniteSelectionEndpointArray]
  rw [hlength, infiniteSelectionSubadditiveArray_shift_covariant]


end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

end
