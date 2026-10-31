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

/-!
# Unit-interval path laws of Lévy processes

## Public declarations

- `ProbabilityTheory.IsLevyProcess.unitIntervalPathLaw h T` is the law on
  `CadlagPath unitInterval ℝ` of the rescaled-time path
  \[t\longmapsto X_{Tt},\qquad 0\le t\le1.\]
  It is constructed from the process coordinates and the almost-surely
  càdlàg path realization.
- `ProbabilityTheory.IsLevyProcess.unitIntervalPathLaw_finite_eval_hasLaw`
  proves the joint-law identity for every finite family of evaluation times.
- `ProbabilityTheory.IsLevyProcess.unitIntervalPathLaw_smul` identifies the
  law of $t\mapsto qX_{Tt}$ as the pushforward of the law of $t\mapsto X_{Tt}$
  by the path map $f\mapsto qf$.

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

/-- Every finite vector of evaluations under the canonical path law has the
joint distribution of the corresponding process coordinates. -/
theorem unitIntervalPathLaw_finite_eval_hasLaw
    (h : IsLevyProcess X P) (horizon : ℝ≥0) (n : ℕ)
    (times : Fin n → unitInterval) :
    HasLaw (fun ω i => X (horizon * unitInterval.toNNReal (times i)) ω)
      ((h.unitIntervalPathLaw horizon : Measure (CadlagPath unitInterval ℝ)).map
        (fun f i => f (times i))) P := by
  let process : unitInterval → Ω → ℝ :=
    fun t ω => X (horizon * unitInterval.toNNReal t) ω
  let evaluate : CadlagPath unitInterval ℝ → Fin n → ℝ :=
    fun f i => f (times i)
  have hevaluate : Measurable evaluate := by
    apply Measurable.of_eval
    intro i
    exact Skorokhod.measurable_apply (times i)
  have hpath : HasLaw (Process.Path.Cadlag.pathMap process)
      (h.unitIntervalPathLaw horizon : Measure (CadlagPath unitInterval ℝ)) P := by
    apply Process.Path.Cadlag.hasLaw_pathMap
    intro t
    exact h.aemeasurable_eval _
  have hcadlag : ∀ᵐ ω ∂P, IsCadlag (fun t : unitInterval => process t ω) := by
    let timeChange : unitInterval → ℝ≥0 :=
      fun t => horizon * unitInterval.toNNReal t
    have htimeMonotone : Monotone timeChange := by
      intro s t hst
      exact mul_le_mul_of_nonneg_left hst horizon.2
    have htimeContinuous : Continuous timeChange := by
      exact continuous_const.mul unitInterval.toNNReal_continuous
    filter_upwards [h.ae_cadlag] with ω hω
    exact hω.comp_monotone_continuous htimeMonotone htimeContinuous
  have heach (i : Fin n) :
      (fun ω => Process.Path.Cadlag.pathMap process ω (times i)) =ᵐ[P]
        fun ω => process (times i) ω :=
    Process.Path.Cadlag.pathMap_ae_eval_eq process
      hcadlag (times i)
  have heval : (fun ω i => Process.Path.Cadlag.pathMap process ω (times i)) =ᵐ[P]
      fun ω i => process (times i) ω := by
    filter_upwards [ae_all_iff.mpr heach] with ω hω
    funext i
    exact hω i
  have hevaluationLaw : HasLaw evaluate
      ((h.unitIntervalPathLaw horizon : Measure (CadlagPath unitInterval ℝ)).map
        evaluate)
      (h.unitIntervalPathLaw horizon : Measure (CadlagPath unitInterval ℝ)) :=
    hasLaw_map hevaluate.aemeasurable
  have hprocessLaw : HasLaw
      (fun ω i => Process.Path.Cadlag.pathMap process ω (times i))
      ((h.unitIntervalPathLaw horizon : Measure (CadlagPath unitInterval ℝ)).map
        evaluate) P := by
    simpa only [Function.comp_def, evaluate] using hevaluationLaw.comp hpath
  simpa [process] using hprocessLaw.congr heval.symm

/-- Spatially scaling a Lévy process scales its complete unit-interval path
law by the corresponding deterministic map on càdlàg paths. -/
theorem unitIntervalPathLaw_smul
    (h : IsLevyProcess X P) (horizon : ℝ≥0) (q : ℝ) :
    (((h.map (AddMonoidHom.mulLeft q)
        (by change Measurable (fun x : ℝ => q * x); fun_prop)
        (by change Continuous (fun x : ℝ => q * x); fun_prop)).unitIntervalPathLaw
        horizon : ProbabilityMeasure (CadlagPath unitInterval ℝ)) :
      Measure (CadlagPath unitInterval ℝ)) =
      ((h.unitIntervalPathLaw horizon : Measure (CadlagPath unitInterval ℝ)).map
        (Skorokhod.scalePath q)) := by
  let process : unitInterval → Ω → ℝ :=
    fun t ω => X (horizon * unitInterval.toNNReal t) ω
  have hcoordinates (t : unitInterval) : AEMeasurable (process t) P := by
    exact h.aemeasurable_eval _
  have htimeMonotone :
      Monotone (fun t : unitInterval => horizon * unitInterval.toNNReal t) := by
    intro s t hst
    exact mul_le_mul_of_nonneg_left hst horizon.2
  have htimeContinuous :
      Continuous (fun t : unitInterval => horizon * unitInterval.toNNReal t) := by
    exact continuous_const.mul unitInterval.toNNReal_continuous
  have hcadlag : ∀ᵐ ω ∂P, IsCadlag (fun t : unitInterval => process t ω) := by
    filter_upwards [h.ae_cadlag] with ω hω
    exact hω.comp_monotone_continuous htimeMonotone htimeContinuous
  simpa [process, IsLevyProcess.unitIntervalPathLaw,
    MeasureTheory.ProbabilityMeasure.coe_mk] using
      Process.Path.Cadlag.pathLaw_smul process hcoordinates hcadlag q

end ProbabilityTheory.IsLevyProcess

end
