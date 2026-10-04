/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Levy.Jump.Entrance
public import Probability.Process.Path.Skorokhod.Corridor.Segment
public import Mathlib.Tactic.Linarith

/-!
# A one-jump model enters a complete segment corridor

This converts the generic marked-Poisson entrance theorem to the exact
complete-path event used in small-deviation arguments. The jump-sum
decomposition remains an explicit hypothesis; no stable-process
representation is asserted here.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

theorem measure_fullSegmentCorridorReturn_pos_of_oneJumpDecomposition
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (S : unitInterval → Ω → ℝ)
    (jumpTime : Ω → unitInterval) (N : Ω → ℕ)
    (W : Ω → ℝ) (V : Ω → ENNReal)
    (rate : ℝ≥0) (ν : Measure ℝ)
    (b c ε ρ : ℝ) (hρ : 0 < ρ)
    (hroomBLower : 4 * ρ < 1 + b)
    (hroomBUpper : 4 * ρ < 1 - b)
    (hroomCLower : 4 * ρ < 1 + c)
    (hroomCUpper : 4 * ρ < 1 - c)
    (hroomEndpoint : 4 * ρ < ε)
    (hrate : 0 < rate)
    (hν : 0 < ν (Set.Ioo (c - b - ρ) (c - b + ρ)))
    (hN : HasLaw N (poissonMeasure rate) P)
    (hW : HasLaw W ν P)
    (hNW : IndepFun N W P)
    (hVNW : IndepFun V (fun ω => (N ω, W ω)) P)
    (hV : Measurable V)
    (hE : (∫⁻ ω, V ω ∂P) < ENNReal.ofReal ρ)
    (hsmall : ∀ ω, V ω < ENNReal.ofReal ρ →
      ∀ t, |S t ω| ≤ ρ)
    (hdecomp : ∀ ω, V ω < ENNReal.ofReal ρ → N ω = 1 →
      ∀ t, segmentIncrement X 0 1 ω t = S t ω +
        (if jumpTime ω ≤ t then W ω else 0)) :
    0 < P (fullSegmentCorridorReturnEvent X 0 1
      (c - 1) (c + 1) (c - b - ε) (c - b + ε)) := by
  have hmain := measure_oneJumpEntrance_pos P
    (fun t ω => segmentIncrement X 0 1 ω t) S jumpTime N W V rate ν
    (c - 1) (c + 1) (c - b) ρ ε (3 * ρ)
    (by linarith [hroomEndpoint, hρ])
    (by linarith [hroomCUpper]) (by linarith [hroomCLower])
    (by linarith [hroomBUpper]) (by linarith [hroomBLower])
    hrate hν hN hW hNW hVNW hV hE hsmall hdecomp
  apply hmain.trans_le
  apply measure_mono
  rintro ω ⟨hcorridor, hendLower, hendUpper⟩
  refine ⟨⟨ρ, hρ, ?_⟩, hendLower, hendUpper⟩
  intro t
  simpa only [show 3 * ρ - 2 * ρ = ρ by ring] using hcorridor t

/-- The full-path entrance event remains positive when the jump-sum identity
and residual variation bound hold only almost surely.  The almost-sure
statements quantify over all times on one common event. -/
theorem measure_fullSegmentCorridorReturn_pos_of_oneJumpDecomposition_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (S : unitInterval → Ω → ℝ)
    (jumpTime : Ω → unitInterval) (N : Ω → ℕ)
    (W : Ω → ℝ) (V : Ω → ENNReal)
    (rate : ℝ≥0) (ν : Measure ℝ)
    (b c ε ρ : ℝ) (hρ : 0 < ρ)
    (hroomBLower : 4 * ρ < 1 + b)
    (hroomBUpper : 4 * ρ < 1 - b)
    (hroomCLower : 4 * ρ < 1 + c)
    (hroomCUpper : 4 * ρ < 1 - c)
    (hroomEndpoint : 4 * ρ < ε)
    (hrate : 0 < rate)
    (hν : 0 < ν (Set.Ioo (c - b - ρ) (c - b + ρ)))
    (hN : HasLaw N (poissonMeasure rate) P)
    (hW : HasLaw W ν P)
    (hNW : IndepFun N W P)
    (hVNW : IndepFun V (fun ω => (N ω, W ω)) P)
    (hV : Measurable V)
    (hE : (∫⁻ ω, V ω ∂P) < ENNReal.ofReal ρ)
    (hsmall : ∀ᵐ ω ∂P, V ω < ENNReal.ofReal ρ →
      ∀ t, |S t ω| ≤ ρ)
    (hdecomp : ∀ᵐ ω ∂P, V ω < ENNReal.ofReal ρ → N ω = 1 →
      ∀ t, segmentIncrement X 0 1 ω t = S t ω +
        (if jumpTime ω ≤ t then W ω else 0)) :
    0 < P (fullSegmentCorridorReturnEvent X 0 1
      (c - 1) (c + 1) (c - b - ε) (c - b + ε)) := by
  have hmain := measure_oneJumpSourceEntrance_pos_ae P
    (fun t ω => segmentIncrement X 0 1 ω t) S jumpTime N W V rate ν
    b c ε ρ hρ hroomBLower hroomBUpper hroomCLower hroomCUpper
    hroomEndpoint hrate hν hN hW hNW hVNW hV hE hsmall hdecomp
  exact hmain

/-- When the target displacement is zero, no large jump is needed. -/
theorem measure_fullSegmentCorridorReturn_pos_of_noJumpDecomposition
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ) (S : unitInterval → Ω → ℝ)
    (N : Ω → ℕ) (V : Ω → ENNReal)
    (rate : ℝ≥0) (c ε ρ : ℝ)
    (hρ : 0 < ρ) (hroomLower : 2 * ρ < 1 - c)
    (hroomUpper : 2 * ρ < 1 + c) (hε : ρ < ε)
    (hN : HasLaw N (poissonMeasure rate) P)
    (hVN : IndepFun V N P)
    (hV : Measurable V)
    (hE : (∫⁻ ω, V ω ∂P) < ENNReal.ofReal ρ)
    (hsmall : ∀ ω, V ω < ENNReal.ofReal ρ →
      ∀ t, |S t ω| ≤ ρ)
    (hdecomp : ∀ ω, V ω < ENNReal.ofReal ρ → N ω = 0 →
      ∀ t, segmentIncrement X 0 1 ω t = S t ω) :
    0 < P (fullSegmentCorridorReturnEvent X 0 1
      (c - 1) (c + 1) (-ε) ε) := by
  have hgood := measure_noJump_and_smallVariation_pos P N V rate
    (ENNReal.ofReal ρ) hN hVN hV hE
  apply hgood.trans_le
  apply measure_mono
  rintro ω ⟨hvariation, hcount⟩
  refine ⟨⟨ρ, hρ, ?_⟩, ?_, ?_⟩
  · intro t
    rw [hdecomp ω hvariation hcount t]
    have hs := abs_le.mp (hsmall ω hvariation t)
    constructor <;> linarith
  · rw [hdecomp ω hvariation hcount ⊤]
    have hs := abs_le.mp (hsmall ω hvariation ⊤)
    linarith
  · rw [hdecomp ω hvariation hcount ⊤]
    have hs := abs_le.mp (hsmall ω hvariation ⊤)
    linarith

end ProbabilityTheory

end
