/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.Skorokhod.Corridor.UniformBlocks.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
public import Probability.Process.StationaryIncrements.Basic
import Probability.Process.IndepIncrements.PathLaw.StationaryTimeChange

/-!
# Stationary laws of uniform block paths

The public result `ProbabilityTheory.HasIndepIncrements.rationalUniformBlockProcess_identDistrib`
states that, for every pair of blocks $j,j'$ in a finite uniform rational
partition,
\[
  (X_{\tau_j(q)}-X_{\tau_j(0)})_{q\in[0,1]}
  \stackrel{d}{=}
  (X_{\tau_{j'}(q)}-X_{\tau_{j'}(0)})_{q\in[0,1]},
\]
assuming independent and stationary increments. It is an instance of the
more general equal-duration time-change theorem in
`Probability.Process.IndepIncrements.PathLaw.StationaryTimeChange`.
-/

open MeasureTheory
open scoped NNReal

@[expose] public section

namespace ProbabilityTheory

/-- Translated restrictions of a process with stationary independent
increments to two blocks of a uniform rational partition have the same law.
Coordinate measurability follows from stationary increments. -/
theorem HasIndepIncrements.rationalUniformBlockProcess_identDistrib
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (h : HasIndepIncrements X P)
    (hstationary : HasStationaryIncrements X P)
    (blocks : ℕ) (hblocks : 0 < blocks) (j j' : Fin blocks) :
    IdentDistrib
      (fun ω q => rationalUniformBlockProcessFromTime X hblocks j q ω)
      (fun ω q => rationalUniformBlockProcessFromTime X hblocks j' q ω) P P := by
  let τ : Fin blocks → ↑RationalCoordinate.UnitInterval → ℝ≥0 :=
    fun k q => rationalUniformBlockAbsoluteTime hblocks k q
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
  have hpathMeas (k : Fin blocks) :
      AEMeasurable
        (fun ω q => rationalUniformBlockProcessFromTime X hblocks k q ω) P :=
    AEMeasurable.of_eval fun q => by
      let d := τ k q - τ k ⊥
      have hsum : τ k ⊥ + d = τ k q :=
        add_tsub_cancel_of_le (hτmono k bot_le)
      have hq := hstationary (τ k ⊥) d
      simpa [rationalUniformBlockProcessFromTime, d, hsum] using
        hq.aemeasurable_fst
  exact h.process_identDistrib_of_sameDuration_timeChanges hstationary
    (τ j) (τ j') (hτmono j) (hτmono j')
    (fun q r hqr => by
      apply NNReal.coe_injective
      rw [NNReal.coe_sub (hτmono j hqr), NNReal.coe_sub (hτmono j' hqr)]
      rw [hblockSpan j q r, hblockSpan j' q r])
    (hpathMeas j) (hpathMeas j')

end ProbabilityTheory

end
