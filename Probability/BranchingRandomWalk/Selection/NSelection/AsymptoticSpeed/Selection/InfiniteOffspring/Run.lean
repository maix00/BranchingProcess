/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module
public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Selection.InfiniteOffspring.Transition

/-!
# Finite runs of optional-slot selection

## Public declarations

In ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed,
infiniteOffspringRun iterates the optional-slot transition over a finite
sequence of generation batches. infiniteOffspringBatchSlotZeroNorm is the
leftmost-child envelope for one batch.

infiniteOffspringRun_stateNorm_le bounds the run's state norm by the sum of
generation envelopes. infiniteOffspringRun_mono_initial and
infiniteOffspringRun_monotone give monotonicity in the initial state and
between ordered runs. infiniteOffspringRun_shift is translation covariance,
infiniteOffspringRun_split decomposes a run at a time split, and
infiniteOffspringRun_congr gives invariance under pointwise-equal batches.

If the generation batches are ordered and every parent has slot zero, then
for the zero initial state the run satisfies
\[
  \|R_n(0)\|_\infty
  \le \sum_{t<n}\max_{i<N}|\mathrm{value}'(b_{t,i},0)|.
\]
For \(R(b,x,n)=\texttt{infiniteOffspringRun}(b,hgood,x,n)\), the
split identity is
\[
  R(b,x,m+n)
  =R(t\mapsto b(m+t),R(b,x,m),n),
\]
with the corresponding shifted goodness proof on the right.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.Branching
open _root_.Combinatorics.Selection.NSelection
open scoped ENNReal

/-- Iterate the actual countable-offspring ranked transition in a fixed
environment indexed by generation and current rank. -/
noncomputable def infiniteOffspringRun
    {N : ℕ} (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (initial : Fin N → ℝ) : ℕ → Fin N → ℝ
  | 0 => initial
  | n + 1 => infiniteOffspringTransition
      (infiniteOffspringRun offspring hgood initial n) (offspring n) (hgood n)

@[simp] theorem infiniteOffspringRun_zero
    {N : ℕ} (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (initial : Fin N → ℝ) :
    infiniteOffspringRun offspring hgood initial 0 = initial := rfl

@[simp] theorem infiniteOffspringRun_succ
    {N : ℕ} (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (initial : Fin N → ℝ) (n : ℕ) :
    infiniteOffspringRun offspring hgood initial (n + 1) =
      infiniteOffspringTransition (infiniteOffspringRun offspring hgood initial n)
        (offspring n) (hgood n) := rfl

/-- The maximal absolute slot-zero displacement in one generation. -/
noncomputable def infiniteOffspringBatchSlotZeroNorm {N : ℕ} (hN : 0 < N)
    (offspring : Fin N → Step ℕ ℝ) : ℝ :=
  Finset.univ.sup' (Finset.univ_nonempty_iff.mpr ⟨⟨0, hN⟩⟩)
    (fun i => |value' (offspring i) 0|)

/-- A deterministic trajectory bound: the sup norm of the population after
`n` generations is at most its initial norm plus the sum of the one-generation
leftmost-child envelopes. -/
theorem infiniteOffspringRun_stateNorm_le {N : ℕ} (hN : 0 < N)
    (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (hordered : ∀ t i, (offspring t i).IsOrderedBy realPotential)
    (hfirst : ∀ t i, survive (offspring t i) 0)
    (initial : Fin N → ℝ) (n : ℕ) :
    infiniteSelectionStateNorm hN (infiniteOffspringRun offspring hgood initial n) ≤
      infiniteSelectionStateNorm hN initial +
        ∑ t ∈ Finset.range n, infiniteOffspringBatchSlotZeroNorm hN (offspring t) := by
  induction n with
  | zero => simp [infiniteOffspringRun, infiniteSelectionStateNorm]
  | succ n ih =>
      rw [infiniteOffspringRun_succ]
      calc
        infiniteSelectionStateNorm hN
            (infiniteOffspringTransition (infiniteOffspringRun offspring hgood initial n)
              (offspring n) (hgood n)) ≤
            infiniteSelectionStateNorm hN (infiniteOffspringRun offspring hgood initial n) +
              infiniteOffspringBatchSlotZeroNorm hN (offspring n) := by
                exact infiniteOffspringTransition_stateNorm_le hN _ _ (hgood n)
                  (hordered n) (hfirst n)
        _ ≤ infiniteSelectionStateNorm hN initial +
              (∑ t ∈ Finset.range n, infiniteOffspringBatchSlotZeroNorm hN (offspring t)) +
              infiniteOffspringBatchSlotZeroNorm hN (offspring n) := by
                linarith [ih]
        _ = infiniteSelectionStateNorm hN initial +
              ∑ t ∈ Finset.range (n + 1), infiniteOffspringBatchSlotZeroNorm hN (offspring t) := by
                simp [Finset.sum_range_succ, add_assoc]

theorem infiniteOffspringRun_mono_initial
    {N : ℕ} (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (initialLow initialHigh : Fin N → ℝ)
    (hinitial : ∀ i, initialLow i ≤ initialHigh i) :
    ∀ n i, infiniteOffspringRun offspring hgood initialLow n i ≤
      infiniteOffspringRun offspring hgood initialHigh n i := by
  intro n
  induction n with
  | zero => exact hinitial
  | succ n ih =>
      intro i
      rw [infiniteOffspringRun_succ, infiniteOffspringRun_succ]
      exact infiniteOffspringTransition_mono _ _ _ (hgood n) ih i

theorem infiniteOffspringRun_monotone
    {N : ℕ} (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (initial : Fin N → ℝ) (hinitial : Monotone initial) :
    ∀ n, Monotone (infiniteOffspringRun offspring hgood initial n) := by
  intro n
  induction n with
  | zero => simpa using hinitial
  | succ n _ =>
      rw [infiniteOffspringRun_succ]
      exact infiniteOffspringFirstN_rank_monotone
        (infiniteOffspringRun offspring hgood initial n) (offspring n) (hgood n)

theorem infiniteOffspringRun_shift
    {N : ℕ} (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (initial : Fin N → ℝ) (c : ℝ) :
    ∀ n, infiniteOffspringRun offspring hgood (fun i => initial i + c) n =
      fun i => infiniteOffspringRun offspring hgood initial n i + c := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [infiniteOffspringRun_succ, infiniteOffspringRun_succ, ih,
        infiniteOffspringTransition_shift]

theorem infiniteOffspringRun_split
    {N : ℕ} (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (initial : Fin N → ℝ) (m n : ℕ) :
    infiniteOffspringRun offspring hgood initial (m + n) =
      infiniteOffspringRun (fun t => offspring (m + t))
        (fun t => hgood (m + t))
        (infiniteOffspringRun offspring hgood initial m) n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ, infiniteOffspringRun_succ, ih, infiniteOffspringRun_succ]

theorem infiniteOffspringRun_congr
    {N : ℕ} (offspring offspring' : ℕ → Fin N → Step ℕ ℝ)
    (hmarks : offspring = offspring')
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (hgood' : ∀ t, IsGoodInfiniteOffspringBatch (offspring' t))
    (initial : Fin N → ℝ) (n : ℕ) :
    infiniteOffspringRun offspring hgood initial n =
      infiniteOffspringRun offspring' hgood' initial n := by
  cases hmarks
  have hgoodEq : hgood = hgood' := by
    funext t
    exact Subsingleton.elim _ _
  rw [hgoodEq]


end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

end
