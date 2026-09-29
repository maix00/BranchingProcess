import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Probability.Distributions.Stable.Basic
import Topology.Cadlag.Basic

/-!
# Stable Lévy processes on abstract time axes

The process-level interface follows Mathlib and the BrownianMotion supplement:
a stochastic process is a function `Time → Ω → State`.  The increment
specification below accepts any ordered time type with a least element and an
order-preserving real clock.  In particular it applies to `ℝ≥0` with its usual
clock, while `unitInterval` is only a finite-horizon specialization.

Independent increments are expressed with Mathlib's `HasIndepIncrements`, and
increment laws with `HasLaw`.  `IsStableLevyProcess` additionally asks for
almost-sure càdlàg paths.  These are specifications, not existence theorems.
The generic path-law predicate only requires a measurable structure on the
càdlàg path space; the repository's Skorokhod `J₁` topology is currently
implemented for `unitInterval` paths.
-/

open MeasureTheory Set

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Stable increment laws on an abstract ordered time axis.  `clock` embeds
time into nonnegative real time: it is monotone and sends the least time to
zero.  The process starts at zero almost surely, has independent increments,
and an increment over `s ≤ t` has law `μ` scaled by the elapsed clock time to
the power `1 / α`. -/
def HasStableLevyIncrements {Time : Type*} [Preorder Time] [OrderBot Time]
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

namespace HasStableLevyIncrements

variable {Time : Type*} [Preorder Time] [OrderBot Time]
variable {α : ℝ} {μ : Measure ℝ} {clock : Time → ℝ}
variable {X : Time → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]

/-- The reference increment law is strictly stable. -/
theorem strictlyStable (h : HasStableLevyIncrements α μ clock X P) :
    IsStrictlyAlphaStable α μ := h.1

/-- The elapsed-time clock is monotone. -/
theorem monotone_clock (h : HasStableLevyIncrements α μ clock X P) :
    Monotone clock := h.2.1

/-- The clock is normalized to zero at the initial time. -/
theorem clock_bot (h : HasStableLevyIncrements α μ clock X P) :
    clock ⊥ = 0 := h.2.2.1

/-- A stable Lévy process starts at the origin almost surely. -/
theorem ae_start_eq_zero (h : HasStableLevyIncrements α μ clock X P) :
    ∀ᵐ ω ∂P, X ⊥ ω = 0 := h.2.2.2.1

/-- A stable Lévy process has independent increments, using Mathlib's process-level definition. -/
theorem indepIncrements (h : HasStableLevyIncrements α μ clock X P) :
    HasIndepIncrements X P := h.2.2.2.2.1

/-- The increment over `[s,t]` has the stable law scaled by the elapsed clock time. -/
theorem increment_hasLaw (h : HasStableLevyIncrements α μ clock X P)
    (s t : Time) (hst : s ≤ t) :
    HasLaw (fun ω => X t ω - X s ω)
      (μ.map fun x => (clock t - clock s) ^ (1 / α) * x) P :=
  h.2.2.2.2.2 s t hst

end HasStableLevyIncrements

/-- A stable Lévy process on a topological ordered time axis has the stable
independent-increment specification and almost-surely càdlàg sample paths. -/
def IsStableLevyProcess {Time : Type*} [PartialOrder Time] [OrderBot Time]
    [TopologicalSpace Time]
    (α : ℝ) (μ : Measure ℝ) (clock : Time → ℝ)
    (X : Time → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] : Prop :=
  HasStableLevyIncrements α μ clock X P ∧
    ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω)

namespace IsStableLevyProcess

variable {Time : Type*} [PartialOrder Time] [OrderBot Time] [TopologicalSpace Time]
variable {α : ℝ} {μ : Measure ℝ} {clock : Time → ℝ}
variable {X : Time → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]

/-- The increment specification of a stable Lévy process. -/
theorem increments (h : IsStableLevyProcess α μ clock X P) :
    HasStableLevyIncrements α μ clock X P := h.1

/-- Stable Lévy process sample paths are càdlàg almost surely. -/
theorem ae_cadlag (h : IsStableLevyProcess α μ clock X P) :
    ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω) := h.2

end IsStableLevyProcess

/-- The canonical coordinate process on càdlàg paths over any ordered
topological time axis. -/
def cadlagPathProcess {Time : Type*} [PartialOrder Time] [TopologicalSpace Time] :
    Time → CadlagPath Time ℝ → ℝ := fun t f => f t

@[simp]
theorem cadlagPathProcess_apply {Time : Type*} [PartialOrder Time] [TopologicalSpace Time]
    (t : Time) (f : CadlagPath Time ℝ) :
    cadlagPathProcess t f = f t := rfl

/-- `P` is a stable Lévy-process law on càdlàg paths over an abstract time
axis, expressed through the canonical coordinate process.  The measurable
space on the path type is supplied by the chosen path topology. -/
def IsStableLevyProcessLaw {Time : Type*} [PartialOrder Time] [OrderBot Time]
    [TopologicalSpace Time] [MeasurableSpace (CadlagPath Time ℝ)]
    (α : ℝ) (μ : Measure ℝ) (clock : Time → ℝ)
    (P : Measure (CadlagPath Time ℝ)) [IsProbabilityMeasure P] : Prop :=
  HasStableLevyIncrements α μ clock cadlagPathProcess P

namespace IsStableLevyProcessLaw

variable {Time : Type*} [PartialOrder Time] [OrderBot Time] [TopologicalSpace Time]
variable [MeasurableSpace (CadlagPath Time ℝ)]
variable {α : ℝ} {μ : Measure ℝ} {clock : Time → ℝ}
variable {P : Measure (CadlagPath Time ℝ)} [IsProbabilityMeasure P]

/-- The reference increment law of a stable Lévy-process law is strictly stable. -/
theorem strictlyStable (h : IsStableLevyProcessLaw α μ clock P) :
    IsStrictlyAlphaStable α μ :=
  HasStableLevyIncrements.strictlyStable h

/-- The canonical paths start at the origin almost surely. -/
theorem ae_start_eq_zero (h : IsStableLevyProcessLaw α μ clock P) :
    ∀ᵐ f ∂P, f ⊥ = 0 := by
  simpa [IsStableLevyProcessLaw, cadlagPathProcess] using
    HasStableLevyIncrements.ae_start_eq_zero h

/-- The canonical path process has independent increments. -/
theorem indepIncrements (h : IsStableLevyProcessLaw α μ clock P) :
    HasIndepIncrements cadlagPathProcess P :=
  HasStableLevyIncrements.indepIncrements h

/-- The increment of the canonical process over `[s,t]` has the stable law
scaled by the elapsed clock time. -/
theorem increment_hasLaw (h : IsStableLevyProcessLaw α μ clock P)
    (s t : Time) (hst : s ≤ t) :
    HasLaw (fun f => f t - f s)
      (μ.map fun x => (clock t - clock s) ^ (1 / α) * x) P := by
  simpa [IsStableLevyProcessLaw, cadlagPathProcess] using
    HasStableLevyIncrements.increment_hasLaw h s t hst

/-- A stable law on càdlàg path space gives an actual stable Lévy process by
taking the canonical coordinate process. -/
theorem isStableLevyProcess (h : IsStableLevyProcessLaw α μ clock P) :
    IsStableLevyProcess α μ clock cadlagPathProcess P := by
  refine ⟨h, ae_of_all _ fun f => ?_⟩
  change IsCadlag (fun t => f t)
  exact f.isCadlag_toFun

end IsStableLevyProcessLaw

end ProbabilityTheory
