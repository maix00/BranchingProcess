/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Stable.FiniteDimensional

/-!
# Deterministic time shifts of stable Lévy processes

Subtracting the position at a deterministic time produces another process
with the same stable increment specification. This is the full finite-
dimensional stationarity needed by corridor probabilities.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

theorem IsStableLevyProcess.shifted_increments
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (start : ℝ≥0) :
    HasStableClockIncrements α μ (fun t : ℝ≥0 => (t : ℝ))
      (fun t ω => X (start + t) ω - X start ω) P := by
  let hX := h.increments
  refine ⟨hX.strictlyStable, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun _ _ hst => hst
  · simp
  · exact ae_of_all _ fun ω => by simp
  · intro n grid hgrid
    let shiftedGrid : Fin (n + 1) → ℝ≥0 := fun i => start + grid i
    have hshifted : Monotone shiftedGrid := by
      intro i j hij
      simpa [shiftedGrid, add_comm] using add_le_add_left (hgrid hij) start
    have hbase := hX.indepIncrements n shiftedGrid hshifted
    convert hbase using 1
    funext i ω
    dsimp [shiftedGrid]
    ring
  · intro s t hst
    have htime : start + s ≤ start + t := by
      simpa [add_comm] using add_le_add_left hst start
    have hlaw := hX.increment_hasLaw (start + s) (start + t) htime
    have hscale : ((↑(start + t) : ℝ) - ↑(start + s)) =
        (t : ℝ) - (s : ℝ) := by
      simp
    convert hlaw using 1
    · funext ω
      ring
    · simp

theorem IsStableLevyProcess.shifted_ae_cadlag
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (start : ℝ≥0) :
    ∀ᵐ ω ∂P, IsCadlag (fun t : ℝ≥0 => X (start + t) ω - X start ω) := by
  filter_upwards [h.ae_cadlag] with ω hω
  have hclockMono : Monotone (fun t : ℝ≥0 => start + t) := by
    intro s t hst
    simpa [add_comm] using add_le_add_left hst start
  have hclockCont : Continuous (fun t : ℝ≥0 => start + t) := by
    fun_prop
  have hshift := hω.comp_monotone_continuous hclockMono hclockCont
  exact hshift.continuous_comp
    (g := fun x : ℝ => x - X start ω) (by fun_prop)

/-- A deterministic time shift, recentered at its initial position, is a
stable Lévy process with the same exponent and increment law. -/
theorem IsStableLevyProcess.shifted
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (start : ℝ≥0) :
    IsStableLevyProcess α μ
      (fun t ω => X (start + t) ω - X start ω) P :=
  ⟨h.shifted_increments start, h.shifted_ae_cadlag start⟩

end ProbabilityTheory

end
