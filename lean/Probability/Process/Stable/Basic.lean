/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
public import Probability.Process.IndepIncrements
public import Probability.Distributions.Stable.Basic
public import Probability.Distributions.Stable.Scaling

/-!
# Stable clock increments

The core process interface uses Mathlib's convention `Time → Ω → State`.
`HasStableClockIncrements` is deliberately valid on a general ordered time
type. A non-additive clock gives a time-changed stable process and need not
give stationary increments. Càdlàg process classes and path laws are defined
in the neighboring `Process.lean` and `PathLaw.lean` modules.
-/

open MeasureTheory Set
open scoped NNReal

@[expose] public section

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Stable increment laws on an ordered time axis equipped with a monotone
real clock that vanishes at the least time. The process starts at zero almost
surely, has independent increments, and an increment over `s ≤ t` has law
`μ` scaled by the elapsed clock time to the power `1 / α`. -/
def HasStableClockIncrements {Time : Type*} [Preorder Time] [OrderBot Time]
    (α : ℝ) (μ : Measure ℝ) (clock : Time → ℝ)
    (X : Time → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] : Prop :=
  IsStrictlyAlphaStable α μ ∧
    Monotone clock ∧
    clock ⊥ = 0 ∧
    (∀ᵐ ω ∂P, X ⊥ ω = 0) ∧
    HasIndepIncrements X P ∧
    ∀ s t : Time, s ≤ t →
      HasLaw (fun ω => X t ω - X s ω)
        (μ.map fun x => (clock t - clock s) ^ (1 / α) * x) P

namespace HasStableClockIncrements

variable {Time : Type*} [Preorder Time] [OrderBot Time]
variable {α : ℝ} {μ : Measure ℝ} {clock : Time → ℝ}
variable {X : Time → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]

/-- The reference increment law is strictly stable. -/
theorem strictlyStable (h : HasStableClockIncrements α μ clock X P) :
    IsStrictlyAlphaStable α μ := h.1

/-- The elapsed-time clock is monotone. -/
theorem monotone_clock (h : HasStableClockIncrements α μ clock X P) :
    Monotone clock := h.2.1

/-- The clock is normalized to zero at the initial time. -/
theorem clock_bot (h : HasStableClockIncrements α μ clock X P) :
    clock ⊥ = 0 := h.2.2.1

/-- The process starts at the origin almost surely. -/
theorem ae_start_eq_zero (h : HasStableClockIncrements α μ clock X P) :
    ∀ᵐ ω ∂P, X ⊥ ω = 0 := h.2.2.2.1

/-- The process has independent increments, using Mathlib's process-level
definition. -/
theorem indepIncrements (h : HasStableClockIncrements α μ clock X P) :
    HasIndepIncrements X P := h.2.2.2.2.1

/-- The increment over `[s,t]` has the stable law scaled by the elapsed clock
time. -/
theorem increment_hasLaw (h : HasStableClockIncrements α μ clock X P)
    (s t : Time) (hst : s ≤ t) :
    HasLaw (fun ω => X t ω - X s ω)
      (μ.map fun x => (clock t - clock s) ^ (1 / α) * x) P :=
  h.2.2.2.2.2 s t hst

/-- On any finite monotone time grid, the vector of consecutive increments has
the product of its stable increment laws. This packages Mathlib's independent
increments field together with the one-increment scaling law. -/
theorem increments_hasLaw_pi (h : HasStableClockIncrements α μ clock X P)
    (n : ℕ) (t : Fin (n + 1) → Time) (ht : Monotone t) :
    HasLaw
      (fun ω (i : Fin n) => X (t i.succ) ω - X (t i.castSucc) ω)
      (Measure.pi fun i : Fin n =>
        μ.map fun x => (clock (t i.succ) - clock (t i.castSucc)) ^ (1 / α) * x) P := by
  apply (h.indepIncrements n t ht).hasLaw_pi
  intro i
  exact h.increment_hasLaw (t i.castSucc) (t i.succ) (ht (Fin.castSucc_le_succ i))

/-- Two processes with the same stable clock-increment specification have
identically distributed increment vectors on every finite monotone time grid.
-/
theorem increments_identDistrib
    {X Y : Time → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (hX : HasStableClockIncrements α μ clock X P)
    (hY : HasStableClockIncrements α μ clock Y P)
    (n : ℕ) (t : Fin (n + 1) → Time) (ht : Monotone t) :
    IdentDistrib
      (fun ω (i : Fin n) => X (t i.succ) ω - X (t i.castSucc) ω)
      (fun ω (i : Fin n) => Y (t i.succ) ω - Y (t i.castSucc) ω) P P := by
  exact (hX.increments_hasLaw_pi n t ht).identDistrib
    (hY.increments_hasLaw_pi n t ht)

/-- A monotone deterministic time change fixing the initial time preserves
stable clock increments, with the clock composed by the same map. -/
theorem comp_time
    {Time' : Type*} [Preorder Time'] [OrderBot Time']
    (h : HasStableClockIncrements α μ clock X P)
    (φ : Time' → Time) (hφ : Monotone φ) (hbot : φ ⊥ = ⊥) :
    HasStableClockIncrements α μ (fun t => clock (φ t))
      (fun t ω => X (φ t) ω) P := by
  refine ⟨h.1, h.monotone_clock.comp hφ, ?_, ?_, ?_, ?_⟩
  · simp [hbot, h.clock_bot]
  · filter_upwards [h.ae_start_eq_zero] with ω hω
    simpa [hbot] using hω
  · exact h.indepIncrements.comp_time φ hφ
  · intro s t hst
    simpa using h.increment_hasLaw (φ s) (φ t) (hφ hst)

/-- Translate a time-changed process to start at its initial time.  The clock
is translated by the same amount, so the increment specification is
preserved even when the time change does not send the bottom time to the
original bottom time.  This is the basic interface for laws of translated
path segments. -/
theorem translate_comp_time
    {Time' : Type*} [Preorder Time'] [OrderBot Time']
    (h : HasStableClockIncrements α μ clock X P)
    (φ : Time' → Time) (hφ : Monotone φ) :
    HasStableClockIncrements α μ
      (fun t => clock (φ t) - clock (φ ⊥))
      (fun t ω => X (φ t) ω - X (φ ⊥) ω) P := by
  let τ : Time' → ℝ := fun t => clock (φ t) - clock (φ ⊥)
  let Y : Time' → Ω → ℝ := fun t ω => X (φ t) ω - X (φ ⊥) ω
  have hτmono : Monotone τ := by
    intro s t hst
    exact sub_le_sub_right (h.monotone_clock (hφ hst)) _
  have hτbot : τ ⊥ = 0 := by simp [τ]
  have hYstart : ∀ᵐ ω ∂P, Y ⊥ ω = 0 := by
    filter_upwards [] with ω
    simp [Y]
  have hYindep : HasIndepIncrements Y P := by
    have hcomp := h.indepIncrements.comp_time φ hφ
    intro n t ht
    convert hcomp n t ht using 1
    ext i ω
    simp [Y]
  refine ⟨h.strictlyStable, hτmono, hτbot, hYstart, hYindep, ?_⟩
  intro s t hst
  have hlaw := h.increment_hasLaw (φ s) (φ t) (hφ hst)
  have hprocess : (fun ω => Y t ω - Y s ω) =
      fun ω => X (φ t) ω - X (φ s) ω := by
    funext ω
    simp [Y]
  have hclock : τ t - τ s = clock (φ t) - clock (φ s) := by
    dsimp [τ]
    ring
  rw [hprocess, hclock]
  exact hlaw

/-- Multiplying the state by a scalar changes the stable clock by the matching
power. The `power_compat` hypothesis records the exact relation needed for
the increment laws; concrete time dilations discharge it with real-power
identities. -/
theorem map_spaceScale
    (h : HasStableClockIncrements α μ clock X P)
    (scale : ℝ) (newClock : Time → ℝ) (hnewClock : Monotone newClock)
    (hnewBot : newClock ⊥ = 0)
    (power_compat : ∀ s t, s ≤ t →
      (newClock t - newClock s) ^ (1 / α) =
        scale * (clock t - clock s) ^ (1 / α)) :
    HasStableClockIncrements α μ newClock
      (fun t ω => scale * X t ω) P := by
  refine ⟨h.1, hnewClock, hnewBot, ?_, ?_, ?_⟩
  · filter_upwards [h.ae_start_eq_zero] with ω hω
    simp [hω]
  · exact h.indepIncrements.smul scale
  · intro s t hst
    let oldFactor := (clock t - clock s) ^ (1 / α)
    let newFactor := (newClock t - newClock s) ^ (1 / α)
    let oldScale : ℝ → ℝ := fun x => oldFactor * x
    let stateScale : ℝ → ℝ := fun x => scale * x
    have hIncrement := h.increment_hasLaw s t hst
    have hStateScale : MeasurePreserving stateScale (μ.map oldScale)
        ((μ.map oldScale).map stateScale) :=
      ⟨by fun_prop, rfl⟩
    have hScaledIncrement : HasLaw
        (fun ω => scale * (X t ω - X s ω))
        ((μ.map oldScale).map stateScale) P := by
      simpa [stateScale, oldScale, oldFactor, Function.comp_def] using
        hStateScale.hasLaw.fun_comp hIncrement
    have hSubtractScale :
        (fun ω => scale * X t ω - scale * X s ω) =
          fun ω => scale * (X t ω - X s ω) := by
      funext ω
      ring
    have hMap : (μ.map oldScale).map stateScale =
        μ.map (fun x => newFactor * x) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext x
      dsimp [stateScale, oldScale, oldFactor, newFactor]
      calc
        scale * ((clock t - clock s) ^ (1 / α) * x) =
            (scale * (clock t - clock s) ^ (1 / α)) * x := by ring
        _ = (newClock t - newClock s) ^ (1 / α) * x := by
          rw [power_compat s t hst]
    rw [hSubtractScale]
    rw [hMap] at hScaledIncrement
    simpa [newFactor] using hScaledIncrement

/-- Strictly stable increment laws are invariant under the canonical
time-space rescaling at the level of the process specification:
`X_t` is replaced by `r^(-1/α) X_(r t)`. This is the finite-dimensional
scaling input to the path self-similarity used in the stable small-deviation
argument. It does not by itself assert equality of path laws. -/
theorem timeSpaceScale
    {X : ℝ≥0 → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (h : HasStableClockIncrements α μ (fun t : ℝ≥0 => (t : ℝ)) X P)
    (r : ℝ≥0) (hr : 0 < r) :
    HasStableClockIncrements α μ (fun t : ℝ≥0 => (t : ℝ))
      (fun t ω => (r : ℝ) ^ (-(1 / α)) * X (r * t) ω) P := by
  let timeChange : ℝ≥0 → ℝ≥0 := fun t => r * t
  have htimeMonotone : Monotone timeChange := by
    intro s t hst
    exact mul_le_mul_of_nonneg_left hst r.2
  have htimeBot : timeChange ⊥ = ⊥ := by
    simp [timeChange]
  have hchanged := h.comp_time timeChange htimeMonotone htimeBot
  have hclockMonotone : Monotone (fun t : ℝ≥0 => (t : ℝ)) := fun _ _ hst => hst
  have hclockBot : (fun t : ℝ≥0 => (t : ℝ)) ⊥ = 0 := by simp
  have hresult := hchanged.map_spaceScale ((r : ℝ) ^ (-(1 / α)))
    (fun t : ℝ≥0 => (t : ℝ)) hclockMonotone hclockBot (by
      intro s t hst
      have hdiff : ((r * t : ℝ≥0) : ℝ) - ((r * s : ℝ≥0) : ℝ) =
          (r : ℝ) * ((t : ℝ) - (s : ℝ)) := by
        rw [NNReal.coe_mul, NNReal.coe_mul]
        ring
      rw [hdiff]
      have hd : 0 ≤ (t : ℝ) - (s : ℝ) :=
        sub_nonneg.mpr (NNReal.coe_le_coe.mpr hst)
      rw [Real.mul_rpow (le_of_lt (NNReal.coe_pos.mpr hr)) hd]
      rw [Real.rpow_neg (le_of_lt (NNReal.coe_pos.mpr hr))]
      have hp : 0 < (r : ℝ) ^ (1 / α) :=
        Real.rpow_pos_of_pos (NNReal.coe_pos.mpr hr) _
      field_simp)
  simpa [timeChange] using hresult

set_option linter.style.haveILetI false in
/-- Multiplying a stable-clock process by a positive scalar pushes its
reference stable law forward by the same scalar and leaves the clock
unchanged. -/
theorem map_spaceScale_measure
    (h : HasStableClockIncrements α μ clock X P)
    (scale : ℝ) (hscale : 0 < scale) :
    HasStableClockIncrements α (μ.map fun x => scale * x) clock
      (fun t ω => scale * X t ω) P := by
  let stateScale : ℝ → ℝ := fun x => scale * x
  letI : IsProbabilityMeasure μ := h.strictlyStable.isProbabilityMeasure
  have hμ : IsStrictlyAlphaStable α (μ.map stateScale) :=
    IsStrictlyAlphaStable.map_mul h.strictlyStable scale hscale
  letI : IsProbabilityMeasure (μ.map stateScale) := hμ.isProbabilityMeasure
  refine ⟨hμ, h.monotone_clock, h.clock_bot, ?_, ?_, ?_⟩
  · filter_upwards [h.ae_start_eq_zero] with ω hω
    simp [hω]
  · exact h.indepIncrements.smul scale
  · intro s t hst
    let oldScale : ℝ → ℝ := fun x => (clock t - clock s) ^ (1 / α) * x
    let newScale : ℝ → ℝ := fun x => (clock t - clock s) ^ (1 / α) * x
    have hIncrement := h.increment_hasLaw s t hst
    have hStateScale : MeasurePreserving stateScale (μ.map oldScale)
        ((μ.map oldScale).map stateScale) := ⟨by fun_prop, rfl⟩
    have hScaledIncrement : HasLaw
        (fun ω => stateScale (X t ω - X s ω))
        ((μ.map oldScale).map stateScale) P :=
      hStateScale.hasLaw.fun_comp hIncrement
    have hProcessScale : (fun ω => scale * X t ω - scale * X s ω) =
        (fun ω => stateScale (X t ω - X s ω)) := by
      funext ω
      dsimp [stateScale]
      ring
    rw [hProcessScale]
    have hMap : (μ.map oldScale).map stateScale =
        (μ.map stateScale).map newScale := by
      rw [Measure.map_map (by fun_prop) (by fun_prop),
        Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext x
      dsimp [oldScale, newScale, stateScale, Function.comp]
      ring
    rw [hMap] at hScaledIncrement
    simpa only [stateScale, newScale] using hScaledIncrement

end HasStableClockIncrements
