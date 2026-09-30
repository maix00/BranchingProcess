module

public import Probability.Process.Stable.Process
public import Probability.Process.Path.Skorokhod

/-!
# Stable process laws on càdlàg path space

This file packages the canonical coordinate process on `CadlagPath` and its
stable clock-increment law. The finite-horizon path laws used by small
deviation arguments are instances of this general interface.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω]

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

end
