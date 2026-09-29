module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
public import Probability.Process.IndepIncrements
public import Probability.Distributions.Stable.Basic
public import Probability.Process.Levy.Basic
public import Topology.Cadlag.Basic

/-!
# Stable processes

The process-level interfaces use Mathlib's convention `Time → Ω → State`.
`HasStableClockIncrements` is deliberately valid on a general ordered time
type. A non-additive clock gives a time-changed stable process and need not
give stationary increments. `IsStableLevyProcess` is reserved for the usual
nonnegative-real time axis with its identity clock. A path law on a bounded
time interval uses the general clock-process interface, since a finite
interval is only a restriction of the full process.
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

end HasStableClockIncrements

/-- A stable independent-increment process on an arbitrary ordered time axis
with almost-surely càdlàg sample paths. For a general clock this need not be a
Lévy process. -/
def IsStableClockProcess {Time : Type*} [PartialOrder Time] [OrderBot Time]
    [TopologicalSpace Time]
    (α : ℝ) (μ : Measure ℝ) (clock : Time → ℝ)
    (X : Time → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] : Prop :=
  HasStableClockIncrements α μ clock X P ∧
    ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω)

namespace IsStableClockProcess

variable {Time : Type*} [PartialOrder Time] [OrderBot Time] [TopologicalSpace Time]
variable {α : ℝ} {μ : Measure ℝ} {clock : Time → ℝ}
variable {X : Time → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]

/-- The stable increment specification of a clock process. -/
theorem increments (h : IsStableClockProcess α μ clock X P) :
    HasStableClockIncrements α μ clock X P := h.1

/-- Clock-process sample paths are càdlàg almost surely. -/
theorem ae_cadlag (h : IsStableClockProcess α μ clock X P) :
    ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω) := h.2

end IsStableClockProcess

/-- A real-valued stable Lévy process on nonnegative real time. Its identity
clock makes the stable increment laws stationary in time. -/
def IsStableLevyProcess (α : ℝ) (μ : Measure ℝ)
    (X : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] : Prop :=
  IsStableClockProcess α μ (fun t : ℝ≥0 => (t : ℝ)) X P

namespace IsStableLevyProcess

variable {α : ℝ} {μ : Measure ℝ} {X : ℝ≥0 → Ω → ℝ}
variable {P : Measure Ω} [IsProbabilityMeasure P]

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

/-- The canonical coordinate process on càdlàg paths over an ordered
topological time axis. -/
def cadlagPathProcess {Time : Type*} [PartialOrder Time] [TopologicalSpace Time] :
    Time → CadlagPath Time ℝ → ℝ := fun t f => f t

@[simp]
theorem cadlagPathProcess_apply {Time : Type*} [PartialOrder Time] [TopologicalSpace Time]
    (t : Time) (f : CadlagPath Time ℝ) :
    cadlagPathProcess t f = f t := rfl

/-- A path law with stable increment distributions for an arbitrary ordered
time axis and clock. This also covers finite-horizon restrictions such as
`unitInterval`. -/
def IsStableClockProcessLaw {Time : Type*} [PartialOrder Time] [OrderBot Time]
    [TopologicalSpace Time] [MeasurableSpace (CadlagPath Time ℝ)]
    (α : ℝ) (μ : Measure ℝ) (clock : Time → ℝ)
    (P : Measure (CadlagPath Time ℝ)) [IsProbabilityMeasure P] : Prop :=
  HasStableClockIncrements α μ clock cadlagPathProcess P

namespace IsStableClockProcessLaw

variable {Time : Type*} [PartialOrder Time] [OrderBot Time] [TopologicalSpace Time]
variable [MeasurableSpace (CadlagPath Time ℝ)]
variable {α : ℝ} {μ : Measure ℝ} {clock : Time → ℝ}
variable {P : Measure (CadlagPath Time ℝ)} [IsProbabilityMeasure P]

/-- The reference increment law of a stable clock-process law is strictly
stable. -/
theorem strictlyStable (h : IsStableClockProcessLaw α μ clock P) :
    IsStrictlyAlphaStable α μ :=
  HasStableClockIncrements.strictlyStable h

/-- The canonical paths start at the origin almost surely. -/
theorem ae_start_eq_zero (h : IsStableClockProcessLaw α μ clock P) :
    ∀ᵐ f ∂P, f ⊥ = 0 := by
  simpa [IsStableClockProcessLaw, cadlagPathProcess] using
    HasStableClockIncrements.ae_start_eq_zero h

/-- The canonical process has independent increments. -/
theorem indepIncrements (h : IsStableClockProcessLaw α μ clock P) :
    HasIndepIncrements cadlagPathProcess P :=
  HasStableClockIncrements.indepIncrements h

/-- The increment of the canonical process over `[s,t]` has the stable law
scaled by the elapsed clock time. -/
theorem increment_hasLaw (h : IsStableClockProcessLaw α μ clock P)
    (s t : Time) (hst : s ≤ t) :
    HasLaw (fun f => f t - f s)
      (μ.map fun x => (clock t - clock s) ^ (1 / α) * x) P := by
  simpa [IsStableClockProcessLaw, cadlagPathProcess] using
    HasStableClockIncrements.increment_hasLaw h s t hst

/-- A stable clock-process law on càdlàg path space gives an actual process
with almost-surely càdlàg paths. -/
theorem isStableClockProcess (h : IsStableClockProcessLaw α μ clock P) :
    IsStableClockProcess α μ clock cadlagPathProcess P := by
  refine ⟨h, ae_of_all _ fun f => ?_⟩
  change IsCadlag (fun t => f t)
  exact f.isCadlag_toFun

end IsStableClockProcessLaw

end ProbabilityTheory
