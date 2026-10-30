/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Basic
public import Probability.Process.RandomWalk.SmallDeviation.Drawdown.Event

/-!
# Affine corridor events on finite random-walk histories

For a finite real history x : Fin (n + 2) → ℝ, the affine corridor with
lower edge a, slope v, and width Δ is given by
a + v k ≤ x k ≤ a + v k + Δ at every coordinate. This module defines the
full-history event, its prefix and endpoint-cutoff variants, and the
corresponding through-horizon event. It proves the first-step restart
identities, measurability, endpoint bounds, and the deterministic inclusion
from a corridor continuation into a drawdown-and-endpoint event.

The endpoint-cutoff event is the finite-history event used in Wang Yiyang,
Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring
(master's thesis, Fudan University, 2026), Chapter 4, Lemma 4.5. Its event
geometry depends only on finite real paths; probability laws on tilted spines
are handled by the branching-random-walk layer.

## Public declarations

ProbabilityTheory.RandomWalk.affineCorridorHistory,
affineCorridorPrefix, affineCorridorFirstWindow,
affineCorridorHistoryEndpointCutoff, affineCorridorThrough,
affineCorridorInitialWindow,
affineCorridorThrough_prependHistory_iff,
affineCorridorPrefix_prependHistory_iff,
measurableSet_affineCorridorThrough,
affineCorridorThrough_succ_eq_endpointCutoff,
measurableSet_affineCorridorHistory,
measurableSet_affineCorridorPrefix,
affineCorridorHistory_firstWindow,
affineCorridorHistory_terminalUpper,
measurableSet_affineCorridorHistoryEndpointCutoff,
affineCorridorHistoryEndpointCutoff_firstWindow,
affineCorridorHistoryEndpointCutoff_terminalUpper,
affineTubeIncrement_mem_noLargeDropEndpointBelowEvent, and
affineCorridorHistory_continuation_mem_noLargeDropEndpointBelowEvent.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.RandomWalk

def affineCorridorHistory (n : ℕ) (lower drift width : ℝ) :
    Set (Fin (n + 2) → ℝ) :=
  {history | ∀ k, lower + drift * (k.val : ℝ) ≤ history k ∧
    history k ≤ lower + drift * (k.val : ℝ) + width}

/-- Histories through time `n` that stay in a fixed-width affine corridor.
Unlike `affineCorridorHistory`, this prefix has no extra terminal time. -/
def affineCorridorPrefix (n : ℕ) (lower drift width : ℝ) :
    Set (Fin (n + 1) → ℝ) :=
  {history | ∀ k, lower + drift * (k.val : ℝ) ≤ history k ∧
    history k ≤ lower + drift * (k.val : ℝ) + width}

/-- The corridor window at its first positive time coordinate. -/
def affineCorridorFirstWindow (lower drift width : ℝ) : Set ℝ :=
  {y | lower + drift ≤ y ∧ y ≤ lower + drift + width}

/-- The affine corridor in Wang Yiyang, *Asymptotic Speed of the N-Branching
Random Walk with Infinite Offspring* (master's thesis, Fudan University,
2026), Chapter 4, Lemma 4.5, with its terminal endpoint restricted by the
additional cutoff. -/
def affineCorridorHistoryEndpointCutoff (n : ℕ) (lower drift width endpointUpper : ℝ) :
    Set (Fin (n + 2) → ℝ) :=
  {history | history ∈ affineCorridorHistory n lower drift width ∧
    history ⟨n + 1, by omega⟩ ≤ endpointUpper}

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

/-- The affine corridor with an endpoint upper bound is measurable. -/
theorem measurableSet_affineCorridorThrough
    (horizon : ℕ) (lower drift width endpointUpper : ℝ) :
    MeasurableSet (affineCorridorThrough horizon lower drift width endpointUpper) := by
  rw [show affineCorridorThrough horizon lower drift width endpointUpper =
      (⋂ k : Fin (horizon + 1),
        {history | lower + drift * (k.val : ℝ) ≤ history k ∧
          history k ≤ lower + drift * (k.val : ℝ) + width}) ∩
        {history | history ⟨horizon, Nat.lt_succ_self horizon⟩ ≤ endpointUpper} by
        ext history
        simp [affineCorridorThrough]]
  exact (MeasurableSet.iInter fun k =>
    (measurableSet_le measurable_const (measurable_pi_apply k)).inter
      (measurableSet_le (measurable_pi_apply k) measurable_const)).inter
    (measurableSet_le
      (measurable_pi_apply (⟨horizon, Nat.lt_succ_self horizon⟩ : Fin (horizon + 1)))
      measurable_const)

/-- The corridor through time `n + 1` equals the history corridor with its
terminal endpoint cutoff. -/
theorem affineCorridorThrough_succ_eq_endpointCutoff
    (n : ℕ) (lower drift width endpointUpper : ℝ) :
    affineCorridorThrough (n + 1) lower drift width endpointUpper =
      affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper := by
  ext history
  simp [affineCorridorThrough, affineCorridorHistoryEndpointCutoff,
    affineCorridorHistory]

theorem measurableSet_affineCorridorHistory
    (n : ℕ) (lower drift width : ℝ) :
    MeasurableSet (affineCorridorHistory n lower drift width) := by
  rw [show affineCorridorHistory n lower drift width =
      ⋂ k : Fin (n + 2), {history | lower + drift * (k.val : ℝ) ≤ history k ∧
        history k ≤ lower + drift * (k.val : ℝ) + width} by
        ext history
        simp [affineCorridorHistory]]
  apply MeasurableSet.iInter
  intro k
  exact MeasurableSet.inter
    (measurableSet_le measurable_const (measurable_pi_apply k))
    (measurableSet_le (measurable_pi_apply k) measurable_const)

theorem measurableSet_affineCorridorPrefix
    (n : ℕ) (lower drift width : ℝ) :
    MeasurableSet (affineCorridorPrefix n lower drift width) := by
  rw [show affineCorridorPrefix n lower drift width =
      ⋂ k : Fin (n + 1), {history | lower + drift * (k.val : ℝ) ≤ history k ∧
        history k ≤ lower + drift * (k.val : ℝ) + width} by
        ext history
        simp [affineCorridorPrefix]]
  apply MeasurableSet.iInter
  intro k
  exact MeasurableSet.inter
    (measurableSet_le measurable_const (measurable_pi_apply k))
    (measurableSet_le (measurable_pi_apply k) measurable_const)

theorem affineCorridorHistory_firstWindow
    (n : ℕ) (lower drift width : ℝ)
    (history : Fin (n + 2) → ℝ)
    (h : history ∈ affineCorridorHistory n lower drift width) :
    history ⟨1, by omega⟩ ∈ affineCorridorFirstWindow lower drift width := by
  have hcoord := h ⟨1, by omega⟩
  simpa [affineCorridorHistory, affineCorridorFirstWindow] using hcoord

theorem affineCorridorHistory_terminalUpper
    (n : ℕ) (lower drift width : ℝ)
    (history : Fin (n + 2) → ℝ)
    (h : history ∈ affineCorridorHistory n lower drift width) :
    history ⟨n + 1, by omega⟩ ≤
      lower + drift * ((n + 1 : ℕ) : ℝ) + width := by
  have hcoord := (h ⟨n + 1, by omega⟩).2
  simpa [affineCorridorHistory] using hcoord

theorem measurableSet_affineCorridorHistoryEndpointCutoff
    (n : ℕ) (lower drift width endpointUpper : ℝ) :
    MeasurableSet
      (affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper) := by
  rw [show affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper =
      affineCorridorHistory n lower drift width ∩
        {history | history ⟨n + 1, by omega⟩ ≤ endpointUpper} by
        ext history
        simp [affineCorridorHistoryEndpointCutoff]]
  exact (measurableSet_affineCorridorHistory n lower drift width).inter
    (measurableSet_le
      (measurable_pi_apply (⟨n + 1, by omega⟩ : Fin (n + 2)))
      measurable_const)

theorem affineCorridorHistoryEndpointCutoff_firstWindow
    (n : ℕ) (lower drift width endpointUpper : ℝ)
    (history : Fin (n + 2) → ℝ)
    (h : history ∈
      affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper) :
    history ⟨1, by omega⟩ ∈ affineCorridorFirstWindow lower drift width :=
  affineCorridorHistory_firstWindow n lower drift width history h.1

theorem affineCorridorHistoryEndpointCutoff_terminalUpper
    (n : ℕ) (lower drift width endpointUpper : ℝ)
    (history : Fin (n + 2) → ℝ)
    (h : history ∈
      affineCorridorHistoryEndpointCutoff n lower drift width endpointUpper) :
    history ⟨n + 1, by omega⟩ ≤ endpointUpper := h.2

/-- On a nondecreasing affine tube, every earlier position is at most one
width above every later position. The terminal increment is bounded by the
width plus the total tube drift. This is the deterministic reduction used to
apply the drawdown estimate to one block in Wang Yiyang, *Asymptotic Speed of
the N-Branching Random Walk with Infinite Offspring* (master's thesis, Fudan
University, 2026), Chapter 4, Lemma 4.2. -/
theorem affineTubeIncrement_mem_noLargeDropEndpointBelowEvent
    (n : ℕ) (lower drift width start : ℝ) (hdrift : 0 ≤ drift)
    (increment : ℕ → ℝ)
    (htube : ∀ k : Fin (n + 1),
      lower + drift * (k.val : ℝ) ≤
          start + AdditivePath.displacement k.val increment ∧
        start + AdditivePath.displacement k.val increment ≤
          lower + drift * (k.val : ℝ) + width) :
    increment ∈
      ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
        n width (width + drift * (n : ℝ)) := by
  change (∀ i j : ℕ, i ≤ j → j ≤ n →
      AdditivePath.displacement i increment -
        AdditivePath.displacement j increment ≤ width) ∧
    AdditivePath.displacement n increment ≤ width + drift * (n : ℝ)
  refine ⟨?_, ?_⟩
  · intro i j hij hj
    let i' : Fin (n + 1) := ⟨i, by omega⟩
    let j' : Fin (n + 1) := ⟨j, by omega⟩
    have hi := (htube i').2
    have hj' := (htube j').1
    have hpositions :
        AdditivePath.displacement i increment -
            AdditivePath.displacement j increment ≤
          width + drift * (i : ℝ) - drift * (j : ℝ) := by
      calc
        _ = (start + AdditivePath.displacement i increment) -
            (start + AdditivePath.displacement j increment) := by ring
        _ ≤ (lower + drift * (i : ℝ) + width) -
            (lower + drift * (j : ℝ)) := sub_le_sub hi hj'
        _ = _ := by ring
    have hijReal : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
    have hdriftMono : drift * (i : ℝ) ≤ drift * (j : ℝ) :=
      mul_le_mul_of_nonneg_left hijReal hdrift
    linarith
  · have hstart : lower ≤ start := by
      simpa using (htube (⟨0, by omega⟩ : Fin (n + 1))).1
    have hend := (htube (⟨n, by omega⟩ : Fin (n + 1))).2
    have hdisp : AdditivePath.displacement n increment ≤
        width + drift * (n : ℝ) := by
      have hn : start + AdditivePath.displacement n increment ≤
          lower + drift * (n : ℝ) + width := by
        simpa using hend
      linarith
    exact hdisp

/-- A continuation below an affine history tube is itself a tube path whose
lower boundary starts one drift step later. -/
theorem affineCorridorHistory_continuation_mem_noLargeDropEndpointBelowEvent
    (n : ℕ) (x lower drift width y : ℝ) (hdrift : 0 ≤ drift)
    (increment : ℕ → ℝ)
    (htube : prependHistory x
        (ProbabilityTheory.RandomWalk.history n (x + y) increment) ∈
          affineCorridorHistory n lower drift width) :
    increment ∈
      ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown.noLargeDropEndpointBelowEvent
        n width (width + drift * (n : ℝ)) := by
  change (∀ k : Fin (n + 2),
      lower + drift * (k.val : ℝ) ≤
          prependHistory x
            (ProbabilityTheory.RandomWalk.history n (x + y) increment) k ∧
        prependHistory x
            (ProbabilityTheory.RandomWalk.history n (x + y) increment) k ≤
          lower + drift * (k.val : ℝ) + width) at htube
  apply affineTubeIncrement_mem_noLargeDropEndpointBelowEvent
    n (lower + drift) drift width (x + y) hdrift increment
  intro k
  have hcoord := htube k.succ
  have hcoord' :
      lower + drift * ((k.val : ℝ) + 1) ≤
          (x + y) + AdditivePath.displacement k.val increment ∧
        (x + y) + AdditivePath.displacement k.val increment ≤
          lower + drift * ((k.val : ℝ) + 1) + width := by
    simpa [Fin.val_succ, ProbabilityTheory.RandomWalk.history_eq_fromIncrements,
      AdditivePath.fromIncrements] using hcoord
  constructor
  · convert hcoord'.1 using 1 <;> ring
  · convert hcoord'.2 using 1 <;> ring

end ProbabilityTheory.RandomWalk

end
