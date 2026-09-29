import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Probability.Distributions.Stable.Basic
import Topology.Cadlag.Basic

/-!
# Stable processes and Lévy processes

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
