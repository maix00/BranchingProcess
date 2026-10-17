/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.BranchingRandomWalk.Spine.Path.SecondMoment.MRCAExpansion
import Probability.BranchingRandomWalk.Spine.Tube.MRCA.PairContribution

/-!
# Corridor tests across an ancestral prefix

Affine corridor indicators split into a prefix condition and a shifted
continuation condition.  This is the bridge from the path-level MRCA
expansion to the conditional pair contributions used in the tube estimate.
-/

open MeasureTheory
open scoped ENNReal
open Classical

namespace ProbabilityTheory.BranchingRandomWalk.Spine

open Combinatorics.Branching
open Combinatorics.UlamHarris
open ProbabilityTheory.BranchingRandomWalk
open ProbabilityTheory.RandomWalk

/-- Histories through a fixed endpoint that remain in an affine corridor. -/
def affineCorridorThrough (horizon : ℕ) (lower drift width endpointUpper : ℝ) :
    Set (Fin (horizon + 1) → ℝ) :=
  {history | (∀ k, lower + drift * (k.val : ℝ) ≤ history k ∧
      history k ≤ lower + drift * (k.val : ℝ) + width) ∧
    history ⟨horizon, Nat.lt_succ_self horizon⟩ ≤ endpointUpper}

/-- The time-zero window of an affine corridor. -/
def affineCorridorInitialWindow (lower width : ℝ) : Set ℝ :=
  {x | lower ≤ x ∧ x ≤ lower + width}

/-- Splitting off the first coordinate shifts the affine corridor by one
time unit. -/
theorem affineCorridorThrough_prependHistory_iff
    (horizon : ℕ) (lower drift width endpointUpper x : ℝ)
    (tail : Fin (horizon + 1) → ℝ) :
    prependHistory x tail ∈
        affineCorridorThrough (horizon + 1) lower drift width endpointUpper ↔
      x ∈ affineCorridorInitialWindow lower width ∧
        tail ∈ affineCorridorThrough horizon (lower + drift) drift width
          endpointUpper := by
  constructor
  · intro h
    have hx := h.1 0
    have hx' : x ∈ affineCorridorInitialWindow lower width := by
      simpa [affineCorridorInitialWindow, affineCorridorThrough,
        prependHistory] using hx
    refine ⟨hx', ?_⟩
    constructor
    · intro k
      have hk := h.1 k.succ
      simp only [prependHistory_succ] at hk
      have hshift : lower + drift * ((k.succ).val : ℝ) =
          lower + drift + drift * (k.val : ℝ) := by simp; ring
      constructor
      · calc
          lower + drift + drift * (k.val : ℝ) =
              lower + drift * ((k.succ).val : ℝ) := hshift.symm
          _ ≤ tail k := hk.1
      · calc
          tail k ≤ lower + drift * ((k.succ).val : ℝ) + width := hk.2
          _ = lower + drift + drift * (k.val : ℝ) + width := by rw [hshift]
    · have hlast :
          (⟨horizon + 1, Nat.lt_succ_self (horizon + 1)⟩ :
            Fin ((horizon + 1) + 1)) =
          (⟨horizon, Nat.lt_succ_self horizon⟩ : Fin (horizon + 1)).succ := rfl
      have hEnd : (prependHistory x tail)
          (⟨horizon + 1, Nat.lt_succ_self (horizon + 1)⟩ :
            Fin ((horizon + 1) + 1)) ≤ endpointUpper := h.2
      simpa only [hlast, prependHistory_succ] using hEnd
  · rintro ⟨hx, htail⟩
    constructor
    · intro k
      refine Fin.cases ?_ ?_ k
      · simpa [affineCorridorThrough, affineCorridorInitialWindow,
          prependHistory] using hx
      · intro j
        have hj := htail.1 j
        simp only [prependHistory_succ]
        constructor
        · calc
            lower + drift * ((j.succ).val : ℝ) =
                lower + drift + drift * (j.val : ℝ) := by simp; ring
            _ ≤ tail j := hj.1
        · calc
            tail j ≤ lower + drift + drift * (j.val : ℝ) + width := hj.2
            _ = lower + drift * ((j.succ).val : ℝ) + width := by simp; ring
    · have hlast :
          (⟨horizon + 1, Nat.lt_succ_self (horizon + 1)⟩ :
            Fin ((horizon + 1) + 1)) =
          (⟨horizon, Nat.lt_succ_self horizon⟩ : Fin (horizon + 1)).succ := rfl
      have hEnd : tail
          (⟨horizon, Nat.lt_succ_self horizon⟩ : Fin (horizon + 1)) ≤
          endpointUpper := htail.2
      simpa only [hlast, prependHistory_succ] using hEnd

/-- The same splitting identity for a prefix with no extra endpoint. -/
theorem affineCorridorPrefix_prependHistory_iff
    (horizon : ℕ) (lower drift width x : ℝ)
    (tail : Fin (horizon + 1) → ℝ) :
    prependHistory x tail ∈ affineCorridorPrefix (horizon + 1) lower drift width ↔
      x ∈ affineCorridorInitialWindow lower width ∧
        tail ∈ affineCorridorPrefix horizon (lower + drift) drift width := by
  constructor
  · intro h
    have hx := h 0
    have hx' : x ∈ affineCorridorInitialWindow lower width := by
      simpa [affineCorridorInitialWindow, affineCorridorPrefix,
        prependHistory] using hx
    refine ⟨hx', ?_⟩
    intro k
    have hk := h k.succ
    simp only [prependHistory_succ] at hk
    constructor
    · calc
        lower + drift + drift * (k.val : ℝ) =
            lower + drift * ((k.succ).val : ℝ) := by simp; ring
        _ ≤ tail k := hk.1
    · calc
        tail k ≤ lower + drift * ((k.succ).val : ℝ) + width := hk.2
        _ = lower + drift + drift * (k.val : ℝ) + width := by simp; ring
  · rintro ⟨hx, htail⟩ k
    refine Fin.cases ?_ ?_ k
    · simpa [affineCorridorPrefix, affineCorridorInitialWindow,
        prependHistory] using hx
    · intro j
      have hj := htail j
      simp only [prependHistory_succ]
      constructor
      · calc
          lower + drift * ((j.succ).val : ℝ) =
              lower + drift + drift * (j.val : ℝ) := by simp; ring
          _ ≤ tail j := hj.1
      · calc
          tail j ≤ lower + drift + drift * (j.val : ℝ) + width := hj.2
          _ = lower + drift * ((j.succ).val : ℝ) + width := by simp; ring

/-- Restricting the full tube indicator to a fixed ancestral address gives
the prefix test times the shifted continuation test. The continuation path
starts at the endpoint of that address. -/
private lemma pathGenerationPrefixTest_zero
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (m n : ℕ) (x : ℝ)
    (ω : StepField ℕ X) (u : TreeNode ℕ) :
    pathGenerationPrefixTest φ m n (fun _ => 0) x ω u = fun _ => 0 := by
  induction m generalizing x ω u with
  | zero =>
      cases u <;> rfl
  | succ m ih =>
      cases u with
      | nil => rfl
      | cons i u =>
          simpa [pathGenerationPrefixTest] using
            ih (x + (ω []).potentialValue' φ i) (subtreeStepField [i] ω) u

theorem pathGenerationPrefixTest_affineCorridorThrough
    {X : Type*} [MeasurableSpace X]
    (φ : Potential X) (m n : ℕ) (initial lower drift width endpointUpper : ℝ)
    (ω : StepField ℕ X) (u : TreeNode ℕ) (hu : u.length = m)
    (tail : Fin (n + 2) → ℝ)
    (htail : tail ⟨0, by omega⟩ =
      pathHistory φ m initial ω u ⟨m, Nat.lt_succ_self m⟩) :
    pathGenerationPrefixTest φ m n
      ((affineCorridorThrough (n + 1 + m) lower drift width endpointUpper).indicator
        (fun _ => (1 : ℝ≥0∞))) initial ω u tail =
      if pathHistory φ m initial ω u ∈
          affineCorridorPrefix m lower drift width then
        (affineCorridorThrough (n + 1)
          (lower + drift * (m : ℝ)) drift width endpointUpper).indicator
            (fun _ => (1 : ℝ≥0∞)) tail
      else 0 := by
  classical
  induction m generalizing n initial lower ω u tail with
  | zero =>
      cases u with
      | nil =>
          let k₀ : Fin (n + 2) := ⟨0, by omega⟩
          have htail0 : tail k₀ = initial := by
            simpa [k₀, pathHistory, pathPotential] using htail
          have hpref : pathHistory φ 0 initial ω [] ∈
              affineCorridorPrefix 0 lower drift width ↔
                initial ∈ affineCorridorInitialWindow lower width := by
            simp [pathHistory, pathPotential, affineCorridorPrefix,
              affineCorridorInitialWindow]
          change (affineCorridorThrough (n + 1) lower drift width endpointUpper).indicator
              (fun _ => (1 : ℝ≥0∞)) tail =
            if pathHistory φ 0 initial ω [] ∈
                affineCorridorPrefix 0 lower drift width then
              (affineCorridorThrough (n + 1)
                (lower + drift * (0 : ℕ)) drift width endpointUpper).indicator
                  (fun _ => (1 : ℝ≥0∞)) tail
            else 0
          by_cases hx : initial ∈ affineCorridorInitialWindow lower width
          · have hmem : pathHistory φ 0 initial ω [] ∈
                affineCorridorPrefix 0 lower drift width := hpref.mpr hx
            rw [if_pos hmem]
            simp only [Nat.cast_zero, mul_zero, add_zero]
          · have hnot : tail ∉
                affineCorridorThrough (n + 1) lower drift width endpointUpper := by
              intro ht
              have hcoord := ht.1 k₀
              have hlow : lower ≤ tail k₀ := by
                simpa [k₀] using hcoord.1
              have hupp : tail k₀ ≤ lower + width := by
                simpa [k₀] using hcoord.2
              apply hx
              exact ⟨by simpa [htail0] using hlow,
                by simpa [htail0] using hupp⟩
            have hprefixFalse : pathHistory φ 0 initial ω [] ∉
                affineCorridorPrefix 0 lower drift width := mt hpref.mp hx
            rw [if_neg hprefixFalse]
            simp [Set.indicator_apply, hnot]
      | cons i u => simp at hu
  | succ m ih =>
      cases u with
      | nil => simp at hu
      | cons i u =>
          have hu' : u.length = m := by simpa using hu
          let x' := initial + (ω []).potentialValue' φ i
          let ω' := subtreeStepField [i] ω
          have htail' : tail ⟨0, by omega⟩ =
              pathHistory φ m x' ω' u ⟨m, Nat.lt_succ_self m⟩ := by
            calc
              tail ⟨0, by omega⟩ =
                  pathHistory φ (m + 1) initial ω (i :: u)
                    ⟨m + 1, Nat.lt_succ_self (m + 1)⟩ := htail
              _ = initial + pathPotential φ ω (i :: u) :=
                pathHistory_last φ (m + 1) initial ω (i :: u) hu
              _ = x' + pathPotential φ ω' u := by
                rw [pathPotential_cons]
                ring
              _ = pathHistory φ m x' ω' u ⟨m, Nat.lt_succ_self m⟩ :=
                (pathHistory_last φ m x' ω' u hu').symm
          let tailCorridor : Set (Fin ((n + 1 + m) + 1) → ℝ) :=
            affineCorridorThrough (n + 1 + m) (lower + drift) drift width endpointUpper
          have houter (tail' : Fin ((n + 1 + m) + 1) → ℝ) :
              ((affineCorridorThrough (n + 1 + (m + 1)) lower drift width
                endpointUpper).indicator (fun _ => (1 : ℝ≥0∞))
                (prependHistory initial tail')) =
              if initial ∈ affineCorridorInitialWindow lower width then
                tailCorridor.indicator (fun _ => (1 : ℝ≥0∞)) tail' else 0 := by
            rw [Set.indicator_apply, Set.indicator_apply]
            rw [show prependHistory initial tail' ∈
                affineCorridorThrough (n + 1 + (m + 1)) lower drift width endpointUpper ↔
                  initial ∈ affineCorridorInitialWindow lower width ∧
                    tail' ∈ tailCorridor by
                  simpa only [Nat.add_succ, tailCorridor] using
                    (affineCorridorThrough_prependHistory_iff
                      (n + 1 + m) lower drift width endpointUpper initial tail')]
            by_cases hx : initial ∈ affineCorridorInitialWindow lower width <;>
              simp [hx, tailCorridor]
          have houterFun :
              (fun tail' : Fin ((n + 1 + m) + 1) → ℝ =>
                (affineCorridorThrough (n + 1 + (m + 1)) lower drift width
                  endpointUpper).indicator (fun _ => (1 : ℝ≥0∞))
                  (prependHistory initial tail')) =
              (fun tail' => if initial ∈ affineCorridorInitialWindow lower width then
                tailCorridor.indicator (fun _ => (1 : ℝ≥0∞)) tail' else 0) := by
            funext tail'
            exact houter tail'
          have htest := ih n x' (lower + drift) ω' u hu' tail htail'
          dsimp [pathGenerationPrefixTest]
          change pathGenerationPrefixTest φ m n
            (fun tail' : Fin ((n + 1 + m) + 1) → ℝ =>
              (affineCorridorThrough (n + 1 + (m + 1)) lower drift width
                endpointUpper).indicator (fun _ => (1 : ℝ≥0∞))
                (prependHistory initial tail'))
            x' ω' u tail = _
          rw [houterFun]
          by_cases hx : initial ∈ affineCorridorInitialWindow lower width
          · simp only [hx, if_pos]
            rw [htest]
            have hprefix :
                pathHistory φ (m + 1) initial ω (i :: u) ∈
                    affineCorridorPrefix (m + 1) lower drift width ↔
                  pathHistory φ m x' ω' u ∈
                    affineCorridorPrefix m (lower + drift) drift width := by
              rw [pathHistory_cons]
              simpa [affineCorridorPrefix_prependHistory_iff, hx, x', ω']
            have hshift :
                lower + drift + drift * (m : ℝ) =
                  lower + drift * ((m + 1 : ℕ) : ℝ) := by push_cast; ring
            rw [← hprefix, hshift]
          · have hprefixFalse :
                pathHistory φ (m + 1) initial ω (i :: u) ∉
                    affineCorridorPrefix (m + 1) lower drift width := by
              rw [pathHistory_cons]
              intro hmem
              exact hx ((affineCorridorPrefix_prependHistory_iff m lower drift width
                initial (pathHistory φ m x' ω' u)).mp hmem).1
            simp only [hx, hprefixFalse]
            simp [pathGenerationPrefixTest_zero]

end ProbabilityTheory.BranchingRandomWalk.Spine
