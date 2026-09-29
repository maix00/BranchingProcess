import Mathlib.Probability.HasLaw
import Mathlib.Probability.Independence.Process.HasIndepIncrements.Basic
import Mathlib.Topology.UnitInterval
import Probability.Distributions.Stable.Basic
import Topology.Cadlag.Skorokhod.TimeChange
import Topology.Cadlag.Skorokhod.Topology

/-!
# Stable Lévy processes on the unit time interval

The process-level interface follows Mathlib and the BrownianMotion supplement: a process is a function
`Time → Ω → State`.  Independent increments are expressed by Mathlib's `HasIndepIncrements`, and the law of
each increment is expressed by `HasLaw`.  This avoids encoding independence a second time as an equality of
finite-dimensional product measures.

`HasStableLevyIncrements` specifies the finite-dimensional increment structure: it starts at zero almost
surely, has independent increments, and an increment over `[s,t]` has the law of `(t-s)^(1/α) X`, where `X`
has unit-time law `μ`.  `IsStableLevyProcess` adds almost-sure càdlàg paths.  These are specifications, not
existence theorems.

`IsStableLevyProcessLaw` specializes this interface to the canonical coordinate process on the càdlàg
Skorokhod path space.  It is useful for tube probabilities, but it does not construct such a path-space law.
Constructing a projective family with these increment laws and proving that it has a càdlàg realization remain
separate obligations.  The pinned Mathlib tree does not provide a stable Lévy-process construction.
-/

open MeasureTheory Set

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The stable increment laws of a process on the unit interval, in the standard `Time → Ω → State`
representation.  Increments are independent and stationary, with scaling determined by the unit-time law `μ`.
This finite-dimensional specification alone does not assert càdlàg paths. -/
def HasStableLevyIncrements (α : ℝ) (μ : Measure ℝ)
    (X : unitInterval → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] : Prop :=
  IsStrictlyAlphaStable α μ ∧
    (∀ᵐ ω ∂P, X ⟨0, mem_Icc.mpr ⟨le_rfl, zero_le_one⟩⟩ ω = 0) ∧
    HasIndepIncrements X P ∧
    ∀ s t : unitInterval, s ≤ t →
      HasLaw (fun ω => X t ω - X s ω)
        (μ.map fun x => ((t : ℝ) - (s : ℝ)) ^ (1 / α) * x) P

namespace HasStableLevyIncrements

variable {α : ℝ} {μ : Measure ℝ} {X : unitInterval → Ω → ℝ} {P : Measure Ω}
variable [IsProbabilityMeasure P]

/-- The unit-time law of a strictly stable Lévy process is strictly stable. -/
theorem strictlyStable (h : HasStableLevyIncrements α μ X P) : IsStrictlyAlphaStable α μ := h.1

/-- A stable Lévy process starts at the origin almost surely. -/
theorem ae_start_eq_zero (h : HasStableLevyIncrements α μ X P) :
    ∀ᵐ ω ∂P, X ⟨0, mem_Icc.mpr ⟨le_rfl, zero_le_one⟩⟩ ω = 0 := h.2.1

/-- A stable Lévy process has independent increments, using Mathlib's process-level definition. -/
theorem indepIncrements (h : HasStableLevyIncrements α μ X P) : HasIndepIncrements X P := h.2.2.1

/-- The increment over `[s,t]` has the stable law scaled by `(t-s)^(1/α)`. -/
theorem increment_hasLaw (h : HasStableLevyIncrements α μ X P)
    (s t : unitInterval) (hst : s ≤ t) :
    HasLaw (fun ω => X t ω - X s ω)
      (μ.map fun x => ((t : ℝ) - (s : ℝ)) ^ (1 / α) * x) P :=
  h.2.2.2 s t hst

end HasStableLevyIncrements

/-- A stable Lévy process on the unit interval is a process with the stable independent stationary increments
above and almost-surely càdlàg sample paths. -/
def IsStableLevyProcess (α : ℝ) (μ : Measure ℝ)
    (X : unitInterval → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] : Prop :=
  HasStableLevyIncrements α μ X P ∧ ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω)

namespace IsStableLevyProcess

variable {α : ℝ} {μ : Measure ℝ} {X : unitInterval → Ω → ℝ} {P : Measure Ω}
variable [IsProbabilityMeasure P]

/-- The increment specification of a stable Lévy process. -/
theorem increments (h : IsStableLevyProcess α μ X P) : HasStableLevyIncrements α μ X P := h.1

/-- Stable Lévy process sample paths are càdlàg almost surely. -/
theorem ae_cadlag (h : IsStableLevyProcess α μ X P) :
    ∀ᵐ ω ∂P, IsCadlag (fun t => X t ω) := h.2

end IsStableLevyProcess

/-- The canonical process on the càdlàg path space. -/
def cadlagPathProcess : unitInterval → CadlagPath unitInterval ℝ → ℝ := fun t f => f t

@[simp]
theorem cadlagPathProcess_apply (t : unitInterval) (f : CadlagPath unitInterval ℝ) :
    cadlagPathProcess t f = f t := rfl

/-- `P` is a stable Lévy-process law on càdlàg paths over `[0,1]`, expressed through the canonical
coordinate process.  This predicate does not assert that such a measure has been constructed. -/
def IsStableLevyProcessLaw (α : ℝ) (μ : Measure ℝ)
    (P : Measure (CadlagPath unitInterval ℝ)) [IsProbabilityMeasure P] : Prop :=
  HasStableLevyIncrements α μ cadlagPathProcess P

namespace IsStableLevyProcessLaw

variable {α : ℝ} {μ : Measure ℝ} {P : Measure (CadlagPath unitInterval ℝ)}
variable [IsProbabilityMeasure P]

/-- The unit-time law of a stable Lévy-process law is strictly stable. -/
theorem strictlyStable (h : IsStableLevyProcessLaw α μ P) : IsStrictlyAlphaStable α μ :=
  HasStableLevyIncrements.strictlyStable h

/-- The canonical paths start at the origin almost surely. -/
theorem ae_start_eq_zero (h : IsStableLevyProcessLaw α μ P) :
    ∀ᵐ f ∂P, f ⟨0, mem_Icc.mpr ⟨le_rfl, zero_le_one⟩⟩ = 0 := by
  simpa [IsStableLevyProcessLaw, cadlagPathProcess] using HasStableLevyIncrements.ae_start_eq_zero h

/-- The canonical path process has independent increments. -/
theorem indepIncrements (h : IsStableLevyProcessLaw α μ P) :
    HasIndepIncrements cadlagPathProcess P := HasStableLevyIncrements.indepIncrements h

/-- The increment of the canonical process over `[s,t]` has the stable law scaled by `(t-s)^(1/α)`. -/
theorem increment_hasLaw (h : IsStableLevyProcessLaw α μ P)
    (s t : unitInterval) (hst : s ≤ t) :
    HasLaw (fun f => f t - f s)
      (μ.map fun x => ((t : ℝ) - (s : ℝ)) ^ (1 / α) * x) P := by
  simpa [IsStableLevyProcessLaw, cadlagPathProcess] using
    HasStableLevyIncrements.increment_hasLaw h s t hst

/-- A stable law on càdlàg path space gives an actual stable Lévy process by taking the canonical
coordinate process.  The càdlàg property is immediate from the sample-space type. -/
theorem isStableLevyProcess (h : IsStableLevyProcessLaw α μ P) :
    IsStableLevyProcess α μ cadlagPathProcess P := by
  refine ⟨h, ae_of_all _ fun f => ?_⟩
  change IsCadlag (fun t : unitInterval => f t)
  exact f.isCadlag_toFun

end IsStableLevyProcessLaw

end ProbabilityTheory
