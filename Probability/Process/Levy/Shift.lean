/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Levy.Basic

/-!
# Deterministic shifts of Lévy processes

## Public declarations

- `ProbabilityTheory.IsLevyProcess.shift` states that for every deterministic
  $s\geq 0$, the recentered process $Y_t=X_{s+t}-X_s$ is again a Lévy process.
  It starts at zero, has stationary independent increments, and has càdlàg
  paths almost surely.

This result uses only the defining properties of a Lévy process. Stable-law
specializations follow from this generic process-level theorem.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

/-- Recenter a Lévy process at a deterministic time. The shifted process has
stationary independent increments, starts at zero, and has càdlàg paths. -/
theorem IsLevyProcess.shift
    {Ω : Type*} [MeasurableSpace Ω]
    {E : Type*} [AddCommGroup E] [MeasurableSpace E]
      [TopologicalSpace E] [IsTopologicalAddGroup E] [BorelSpace E]
    {X : ℝ≥0 → Ω → E} {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsLevyProcess X P) (start : ℝ≥0) :
    IsLevyProcess (fun t ω => X (start + t) ω - X start ω) P := by
  let Y : ℝ≥0 → Ω → E := fun t ω => X (start + t) ω - X start ω
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [] with ω
    simp
  · intro n grid hgrid
    let shiftedGrid : Fin (n + 1) → ℝ≥0 := fun i => start + grid i
    have hshifted : Monotone shiftedGrid := by
      intro i j hij
      simpa [shiftedGrid, add_comm] using add_le_add_left (hgrid hij) start
    have hbase := h.indepIncrements n shiftedGrid hshifted
    convert hbase using 1
    funext i ω
    simp [shiftedGrid, sub_sub_sub_cancel_right]
  · intro s t
    have hstart := h.stationaryIncrements start t
    have hshift := h.stationaryIncrements (start + s) t
    simpa [Y, add_assoc, sub_sub_sub_cancel_right] using hshift.trans hstart.symm
  · filter_upwards [h.ae_cadlag] with ω hω
    have hclockMono : Monotone (fun t : ℝ≥0 => start + t) := by
      intro s t hst
      simpa [add_comm] using add_le_add_left hst start
    have hclockCont : Continuous (fun t : ℝ≥0 => start + t) := by
      fun_prop
    have hshift := hω.comp_monotone_continuous hclockMono hclockCont
    exact hshift.continuous_comp (g := fun x => x - X start ω) (by fun_prop)

end ProbabilityTheory

end
