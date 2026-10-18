/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Basic
public import Probability.Process.StationaryIncrements.Basic
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Probability.Process.IndepIncrements.FiniteDimensional

/-!
# Stationary laws of uniform block paths

For a real-valued process with stationary independent increments, the
translated process restricted to any two blocks of the same length has the
same law on rational times. The conclusion uses only those increment
properties and coordinate measurability; it does not require càdlàg paths or
stable scaling.

The public declaration is
`ProbabilityTheory.HasIndepIncrements.rationalUniformBlockProcess_identDistrib`:
for any blocks `j` and `j'`, the two translated rational block paths have the
same distribution,
`\mathrm{Law}(q \mapsto X(\tau_j(q))-X(\tau_j(0))) =
\mathrm{Law}(q \mapsto X(\tau_{j'}(q))-X(\tau_{j'}(0)))`,
assuming stationary increments and almost-everywhere measurability of every
process coordinate. Here `\tau_j` is the rational-time embedding of block `j`.
-/

open MeasureTheory
open scoped NNReal

@[expose] public section

namespace ProbabilityTheory

/-- Translated restrictions of a real-valued process to two blocks of a
uniform rational partition have the same law. Only stationary independent
increments and measurability of the individual process coordinates are used.
-/
theorem HasIndepIncrements.rationalUniformBlockProcess_identDistrib
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (h : HasIndepIncrements X P)
    (hstationary : HasStationaryIncrements X P)
    (hXmeas : ∀ t : ℝ≥0, AEMeasurable (fun ω => X t ω) P)
    (blocks : ℕ) (hblocks : 0 < blocks) (j j' : Fin blocks) :
    IdentDistrib
      (fun ω q => rationalUniformBlockProcessFromTime X hblocks j q ω)
      (fun ω q => rationalUniformBlockProcessFromTime X hblocks j' q ω) P P := by
  let τ : Fin blocks → ↑RationalCoordinate.UnitInterval → ℝ≥0 :=
    fun k q => rationalUniformBlockAbsoluteTime hblocks k q
  let B : Fin blocks → ↑RationalCoordinate.UnitInterval → Ω → ℝ :=
    fun k => rationalUniformBlockProcessFromTime X hblocks k
  have hτmono (k : Fin blocks) : Monotone (τ k) :=
    monotone_rationalUniformBlockAbsoluteTime hblocks k
  have hblockSpan (k : Fin blocks) (q r : ↑RationalCoordinate.UnitInterval) :
      ((τ k r : ℝ) - τ k q) = ((r : ℝ) - q) / (blocks : ℝ) := by
    have hr := rationalUniformBlockClock_eq hblocks k r
    have hq := rationalUniformBlockClock_eq hblocks k q
    dsimp [rationalUniformBlockClock] at hr hq
    have hcancel : ((τ k r : ℝ) - τ k q) =
        ((τ k r : ℝ) - τ k ⊥) - ((τ k q : ℝ) - τ k ⊥) := by ring
    rw [hcancel, hr, hq]
    ring
  have hBIndep (k : Fin blocks) : HasIndepIncrements (B k) P := by
    intro n grid hgrid
    have hgrid' : Monotone (τ k ∘ grid) := (hτmono k).comp hgrid
    simpa [B, τ, rationalUniformBlockProcessFromTime,
      sub_sub_sub_cancel_right] using h n (τ k ∘ grid) hgrid'
  have hBStart (k : Fin blocks) : ∀ᵐ ω ∂P, B k ⊥ ω = 0 := by
    filter_upwards [] with ω
    simp [B, rationalUniformBlockProcessFromTime]
  have hBMeas (k : Fin blocks) :
      AEMeasurable (fun ω q => B k q ω) P := by
    exact AEMeasurable.of_eval fun q =>
      (hXmeas (τ k q)).sub (hXmeas (τ k ⊥))
  have hBInc (q r : ↑RationalCoordinate.UnitInterval) (hqr : q ≤ r) :
      IdentDistrib (fun ω => B j r ω - B j q ω)
        (fun ω => B j' r ω - B j' q ω) P P := by
    let d : ℝ≥0 := τ j r - τ j q
    let d' : ℝ≥0 := τ j' r - τ j' q
    have hd : d = d' := by
      apply NNReal.coe_injective
      rw [NNReal.coe_sub (hτmono j hqr), NNReal.coe_sub (hτmono j' hqr)]
      rw [hblockSpan j q r, hblockSpan j' q r]
    have hsum : τ j q + d = τ j r := add_tsub_cancel_of_le (hτmono j hqr)
    have hsum' : τ j' q + d' = τ j' r :=
      add_tsub_cancel_of_le (hτmono j' hqr)
    have hleft := hstationary (τ j q) d
    have hright := hstationary (τ j' q) d'
    have hleft' : IdentDistrib (fun ω => B j r ω - B j q ω)
        (fun ω => X d ω - X 0 ω) P P := by
      simpa [B, rationalUniformBlockProcessFromTime, d, hsum] using hleft
    have hright' : IdentDistrib (fun ω => B j' r ω - B j' q ω)
        (fun ω => X d ω - X 0 ω) P P := by
      simpa [B, rationalUniformBlockProcessFromTime, d', hd, hsum'] using hright
    exact hleft'.trans hright'.symm
  exact HasIndepIncrements.process_identDistrib_of_aemeasurable
    (hBIndep j) (hBIndep j') (hBStart j) (hBStart j')
    hBInc (hBMeas j) (hBMeas j')

end ProbabilityTheory

end
