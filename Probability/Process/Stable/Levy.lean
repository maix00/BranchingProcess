/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Stable.Process
public import Probability.Process.Levy.Basic

/-!
# Stable Lévy processes

The identity clock on nonnegative real time makes the stable increment laws
stationary. This file contains the Lévy specialization and its connection to
the general `IsLevyProcess` interface.
-/

open MeasureTheory
open scoped NNReal

@[expose] public section

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A real-valued stable Lévy process on nonnegative real time. Its identity
clock makes the stable increment laws stationary in time. -/
def IsStableLevyProcess (α : ℝ) (μ : Measure ℝ)
    (X : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] : Prop :=
  IsStableClockProcess α μ (fun t : ℝ≥0 => (t : ℝ)) X P

namespace IsStableLevyProcess

variable {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- Positive spatial scaling changes the reference stable law by the same
pushforward, while preserving the identity-clock Lévy process structure. -/
theorem spatialScale (h : IsStableLevyProcess α μ X P)
    (scale : ℝ) (hscale : 0 < scale) :
    IsStableLevyProcess α (μ.map fun x => scale * x)
      (fun t ω => scale * X t ω) P := by
  change HasStableClockIncrements α μ (fun t : ℝ≥0 => (t : ℝ)) X P ∧ _ at h
  refine ⟨h.1.map_spaceScale_measure scale hscale, ?_⟩
  filter_upwards [h.2] with ω hω
  exact hω.continuous_comp (g := fun x : ℝ => scale * x) (by fun_prop)

/-- A stable Lévy process remains in the same process class after the
canonical time-space rescaling. The theorem asserts the defining increment
laws and càdlàg paths; path-law equality is a separate finite-dimensional
distribution argument. -/
theorem timeSpaceScale (h : IsStableLevyProcess α μ X P)
    (r : ℝ≥0) (hr : 0 < r) :
    IsStableLevyProcess α μ
      (fun t ω => (r : ℝ) ^ (-(1 / α)) * X (r * t) ω) P := by
  change HasStableClockIncrements α μ (fun t : ℝ≥0 => (t : ℝ)) X P ∧ _ at h
  refine ⟨h.1.timeSpaceScale r hr, ?_⟩
  let scale : ℝ := (r : ℝ) ^ (-(1 / α))
  let timeChange : ℝ≥0 → ℝ≥0 := fun t => r * t
  have htimeMonotone : Monotone timeChange := by
    intro s t hst
    exact mul_le_mul_of_nonneg_left hst r.2
  have htimeContinuous : Continuous timeChange := by
    fun_prop
  filter_upwards [h.2] with ω hω
  have htime : IsCadlag (fun t : ℝ≥0 => X (timeChange t) ω) :=
    hω.comp_monotone_continuous htimeMonotone htimeContinuous
  have hstate : IsCadlag (fun t : ℝ≥0 => scale * X (timeChange t) ω) :=
    htime.continuous_comp (g := fun x : ℝ => scale * x) (by fun_prop)
  simpa [scale, timeChange] using hstate

/-- The canonical time-space scaling preserves the joint law of every finite
family of consecutive increments. This is a finite-dimensional consequence
of strict stability; it does not identify laws of whole càdlàg paths. -/
theorem timeSpaceScale_increments_identDistrib
    (h : IsStableLevyProcess α μ X P) (r : ℝ≥0) (hr : 0 < r)
    (n : ℕ) (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t) :
    IdentDistrib
      (fun ω (i : Fin n) => X (t i.succ) ω - X (t i.castSucc) ω)
      (fun ω (i : Fin n) =>
        (r : ℝ) ^ (-(1 / α)) * X (r * t i.succ) ω -
          (r : ℝ) ^ (-(1 / α)) * X (r * t i.castSucc) ω) P P := by
  exact h.1.increments_identDistrib (h.timeSpaceScale r hr).1 n t ht

/-- The stable increment specification of a Lévy process. -/
theorem increments (h : IsStableLevyProcess α μ X P) :
    HasStableClockIncrements α μ (fun t : ℝ≥0 => (t : ℝ)) X P := by
  change HasStableClockIncrements α μ (fun t : ℝ≥0 => (t : ℝ)) X P ∧ _ at h
  exact h.1

/-- Lévy process sample paths are càdlàg almost surely. -/
theorem ae_cadlag (h : IsStableLevyProcess α μ X P) :
    ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω) := by
  change HasStableClockIncrements α μ (fun t : ℝ≥0 => (t : ℝ)) X P ∧ _ at h
  exact h.2

/-- A stable Lévy process is, in particular, a Lévy process. Its stationary
increments follow from the stable increment law depending only on elapsed
time. -/
theorem toIsLevyProcess (h : IsStableLevyProcess α μ X P) :
    IsLevyProcess X P := by
  change HasStableClockIncrements α μ (fun t : ℝ≥0 => (t : ℝ)) X P ∧ _ at h
  let hinc := h.1
  refine ⟨hinc.ae_start_eq_zero, hinc.indepIncrements, ?_, h.2⟩
  intro s t
  have hst : s ≤ s + t := by simp
  have hfirst := hinc.increment_hasLaw s (s + t) hst
  have hsecond := hinc.increment_hasLaw 0 t (by simp)
  have hduration : ((↑(s + t) : ℝ) - ↑s) = (↑t - (0 : ℝ)) := by
    simp
  have hscale :
      (fun x : ℝ => ((↑(s + t) : ℝ) - ↑s) ^ (1 / α) * x) =
        fun x : ℝ => (↑t - (0 : ℝ)) ^ (1 / α) * x := by
    funext x
    rw [hduration]
  have hmeasure :
      μ.map (fun x : ℝ => ((↑(s + t) : ℝ) - ↑s) ^ (1 / α) * x) =
        μ.map (fun x : ℝ => (↑t - (0 : ℝ)) ^ (1 / α) * x) := by
    rw [hscale]
  have hsecond' : HasLaw (fun ω => X t ω - X 0 ω)
      (μ.map fun x : ℝ => ((↑(s + t) : ℝ) - ↑s) ^ (1 / α) * x) P := by
    rw [hmeasure]
    exact hsecond
  exact hfirst.identDistrib hsecond'

end IsStableLevyProcess

end ProbabilityTheory

end
