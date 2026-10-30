/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Levy.Shift
public import Probability.Process.Stable.Levy

/-!
# Deterministic shifts of stable Lévy processes

## Public declarations

- `ProbabilityTheory.IsStableLevyProcess.shift` states that for every
  deterministic $s\geq 0$, the recentered process $Y_t=X_{s+t}-X_s$ remains a
  stable Lévy process with the same stable law. Its generic Lévy-process path
  properties follow from `ProbabilityTheory.IsLevyProcess.shift`.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace ProbabilityTheory

/-- Recenter a stable Lévy process at a deterministic time. The translated
stable clock is again the identity clock, and the generic path properties
follow from `IsLevyProcess.shift`. -/
theorem IsStableLevyProcess.shift
    {Ω : Type*} [MeasurableSpace Ω]
    {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsStableLevyProcess α μ X P) (start : ℝ≥0) :
    IsStableLevyProcess α μ
      (fun t ω => X (start + t) ω - X start ω) P := by
  change HasStableClockIncrements α μ (fun t : ℝ≥0 => (t : ℝ)) X P ∧ _ at h
  let φ : ℝ≥0 → ℝ≥0 := fun t => start + t
  have hφ : Monotone φ := by
    intro s t hst
    simpa [φ, add_comm] using add_le_add_left hst start
  have hinc := h.1.translate_comp_time φ hφ
  have hshiftInc : HasStableClockIncrements α μ (fun t : ℝ≥0 => (t : ℝ))
      (fun t ω => X (start + t) ω - X start ω) P := by
    simpa [φ] using hinc
  let hstable : IsStableLevyProcess α μ X P := ⟨h.1, h.2⟩
  exact ⟨hshiftInc, (hstable.toIsLevyProcess.shift start).ae_cadlag⟩

end ProbabilityTheory

end
