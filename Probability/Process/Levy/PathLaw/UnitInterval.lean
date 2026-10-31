/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.HasLaw
public import Probability.Process.Levy.Basic
public import Probability.Process.Levy.FiniteDimensional
public import Probability.Process.Path.Representation.Cadlag
public import Topology.Order.UnitInterval.Time

import Probability.Process.IndepIncrements.FiniteDimensional

/-!
# Unit-interval path laws of Lévy processes

## Public declarations

- `ProbabilityTheory.IsLevyProcess.unitIntervalPathLaw h T` is the law on
  `CadlagPath unitInterval ℝ` of the rescaled-time path
  \[t\longmapsto X_{Tt},\qquad 0\le t\le1.\]
  It is constructed from the process coordinates and the almost-surely
  càdlàg path realization.
- `ProbabilityTheory.IsLevyProcess.unitIntervalPathLaw_ae_cadlag h T` proves
  that this time-restricted process is almost surely càdlàg.
- `ProbabilityTheory.IsLevyProcess.unitIntervalPathLaw_eval_hasLaw h T t`
  proves that evaluation at `t` under this path law has the law of `X_(Tt)`.

The construction is the real-valued Lévy-process specialization of the
canonical rational-coordinate realization in
`Probability.Process.Path.Representation.Cadlag`. It is useful when a
process-level argument needs the entire path on a finite time interval.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace ProbabilityTheory.IsLevyProcess

variable {Ω : Type*} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {X : ℝ≥0 → Ω → ℝ}

/-- The law of the complete Lévy-process path on `[0,horizon]`, linearly
reparameterized as a càdlàg path on `[0,1]`. -/
noncomputable def unitIntervalPathLaw
    (h : IsLevyProcess X P) (horizon : ℝ≥0) :
    ProbabilityMeasure (CadlagPath unitInterval ℝ) :=
  ⟨Process.Path.Cadlag.pathLaw P
      (fun t ω => X (horizon * unitInterval.toNNReal t) ω)
      (fun _ => h.aemeasurable_eval _),
    inferInstance⟩

/-- Restricting an almost-surely càdlàg Lévy path to `[0,horizon]` and
reparameterizing time preserves the càdlàg property. -/
theorem unitIntervalPathLaw_ae_cadlag
    (h : IsLevyProcess X P) (horizon : ℝ≥0) :
    ∀ᵐ ω ∂P,
      IsCadlag (fun t : unitInterval =>
        X (horizon * unitInterval.toNNReal t) ω) := by
  let timeChange : unitInterval → ℝ≥0 :=
    fun t => horizon * unitInterval.toNNReal t
  have htimeMonotone : Monotone timeChange := by
    intro s t hst
    exact mul_le_mul_of_nonneg_left hst horizon.2
  have htimeContinuous : Continuous timeChange := by
    exact continuous_const.mul unitInterval.toNNReal_continuous
  filter_upwards [h.ae_cadlag] with ω hω
  exact hω.comp_monotone_continuous htimeMonotone htimeContinuous

/-- Evaluation at `t` under the canonical path law has the distribution of
the original process at time `horizon * t`. -/
theorem unitIntervalPathLaw_eval_hasLaw
    (h : IsLevyProcess X P) (horizon : ℝ≥0) (t : unitInterval) :
    HasLaw (fun ω => X (horizon * unitInterval.toNNReal t) ω)
      ((h.unitIntervalPathLaw horizon : Measure (CadlagPath unitInterval ℝ)).map
        (fun f => f t)) P := by
  let process : unitInterval → Ω → ℝ :=
    fun s ω => X (horizon * unitInterval.toNNReal s) ω
  have hprocessMeasurable : ∀ s, AEMeasurable (process s) P := by
    intro s
    exact h.aemeasurable_eval _
  have hpath : HasLaw (Process.Path.Cadlag.pathMap process)
      (h.unitIntervalPathLaw horizon : Measure (CadlagPath unitInterval ℝ)) P := by
    exact Process.Path.Cadlag.hasLaw_pathMap process hprocessMeasurable
  have heval : (fun ω => Process.Path.Cadlag.pathMap process ω t) =ᵐ[P]
      fun ω => process t ω :=
    Process.Path.Cadlag.pathMap_ae_eval_eq process
      (h.unitIntervalPathLaw_ae_cadlag horizon) t
  have hevaluationLaw : HasLaw (fun f : CadlagPath unitInterval ℝ => f t)
      ((h.unitIntervalPathLaw horizon : Measure (CadlagPath unitInterval ℝ)).map
        (fun f => f t))
      (h.unitIntervalPathLaw horizon : Measure (CadlagPath unitInterval ℝ)) :=
    hasLaw_map (Skorokhod.measurable_apply t).aemeasurable
  have hprocessLaw : HasLaw (fun ω => Process.Path.Cadlag.pathMap process ω t)
      ((h.unitIntervalPathLaw horizon : Measure (CadlagPath unitInterval ℝ)).map
        (fun f => f t)) P := by
    simpa only [Function.comp_def] using hevaluationLaw.comp hpath
  simpa [process] using hprocessLaw.congr heval.symm

end ProbabilityTheory.IsLevyProcess

end
