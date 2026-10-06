/-
Copyright (c) 2026 WANG Yiyang.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Combinatorics.BranchingWalk.Step.PointMeasure
public import Probability.BranchingProcess.Offspring.PointMeasure

/-!
# Offspring-count laws

Child counts are the `ℕ∞` projection of a complete offspring configuration.
For countable slot types, their law is a pushforward of the configuration
law. Taking total mass after the point-measure projection gives the same law,
after the canonical embedding of `ℕ∞` into `ℝ≥0∞`.
-/

@[expose] public section

namespace ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw

open MeasureTheory
open scoped ENNReal

/-- The law of the possibly infinite number of children in an offspring
configuration. -/
noncomputable def childCountLaw {ι Mark : Type*} [Countable ι]
    [MeasurableSpace Mark]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark) :
    ProbabilityMeasure ℕ∞ :=
  μ.map Combinatorics.Branching.Step.childCount

@[simp] theorem childCountLaw_toMeasure {ι Mark : Type*} [Countable ι]
    [MeasurableSpace Mark]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark) :
    (μ.childCountLaw : Measure ℕ∞) =
      (μ : Measure (Combinatorics.Branching.Step ι Mark)).map
        Combinatorics.Branching.Step.childCount := rfl

/-- Child-count laws are unchanged when child marks are mapped. -/
theorem childCountLaw_mapMarks {ι Mark Mark' : Type*} [Countable ι]
    [MeasurableSpace Mark] [MeasurableSpace Mark']
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark)
    (f : Mark → Mark') (hf : Measurable f) :
    (μ.mapMarks f hf).childCountLaw = μ.childCountLaw := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [childCountLaw_toMeasure, mapMarks_toMeasure]
  rw [Measure.map_map Combinatorics.Branching.Step.childCount_measurable
    (Combinatorics.Branching.Step.map_measurable hf)]
  congr 1
  funext ξ
  simp

/-- Total mass of the point-measure law is the child-count law mapped into
`ℝ≥0∞`. -/
theorem pointMeasureLaw_totalMass {ι Mark : Type*} [Countable ι]
    [MeasurableSpace Mark]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark) :
    μ.pointMeasureLaw.map (fun η : Measure Mark => η Set.univ) =
      μ.childCountLaw.map (fun n : ℕ∞ => (n : ℝ≥0∞)) := by
  have htotal : Measurable (fun η : Measure Mark => η Set.univ) :=
    Measure.measurable_coe MeasurableSet.univ
  have hcast : Measurable (fun n : ℕ∞ => (n : ℝ≥0∞)) := by
    fun_prop
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map, pointMeasureLaw_toMeasure,
    childCountLaw_toMeasure]
  rw [Measure.map_map htotal Combinatorics.Branching.stepPointMeasure_measurable,
    Measure.map_map hcast Combinatorics.Branching.Step.childCount_measurable]
  congr 1
  funext ξ
  exact Combinatorics.Branching.stepPointMeasure_univ ξ

/-- The expected extended child count under an offspring configuration law.
The value may be infinite; no finiteness assumption is built in. -/
noncomputable def expectedChildCount {ι Mark : Type*} [Countable ι]
    [MeasurableSpace Mark]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark) :
    ℝ≥0∞ :=
  ∫⁻ n : ℕ∞, (n : ℝ≥0∞) ∂μ.childCountLaw

/-- An offspring configuration law has at least one child almost surely. -/
def HasAtLeastOneChild {ι Mark : Type*} [Countable ι]
    [MeasurableSpace Mark]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark) :
    Prop :=
  (μ : Measure (Combinatorics.Branching.Step ι Mark))
    Combinatorics.Branching.nonemptySupport = 1

/-- The offspring law is supercritical when its expected extended child count
is greater than one. -/
def IsSupercritical {ι Mark : Type*} [Countable ι]
    [MeasurableSpace Mark]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark) :
    Prop :=
  1 < μ.expectedChildCount

/-- A mass-one nonempty event gives an almost-surely nonempty configuration. -/
theorem hasAtLeastOneChild_ae {ι Mark : Type*} [Countable ι]
    [MeasurableSpace Mark]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark)
    (h : μ.HasAtLeastOneChild) :
    ∀ᵐ ξ ∂(μ : Measure (Combinatorics.Branching.Step ι Mark)),
      ξ ∈ Combinatorics.Branching.nonemptySupport := by
  exact (ae_mem_iff_measure_eq
    Combinatorics.Branching.nonemptySupport_measurable.nullMeasurableSet).2
      (by simpa [HasAtLeastOneChild] using h)

/-- Expected child count can equivalently be computed as the expected total
mass of the offspring point-measure law. -/
theorem expectedChildCount_eq_lintegral_pointMeasureLaw_totalMass
    {ι Mark : Type*} [Countable ι] [MeasurableSpace Mark]
    (μ : ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw ι Mark) :
    μ.expectedChildCount =
      ∫⁻ η : Measure Mark, η Set.univ ∂μ.pointMeasureLaw := by
  have hcast : Measurable (fun n : ℕ∞ => (n : ℝ≥0∞)) := by
    fun_prop
  have htotal : Measurable (fun η : Measure Mark => η Set.univ) :=
    Measure.measurable_coe MeasurableSet.univ
  calc
    μ.expectedChildCount =
        ∫⁻ z : ℝ≥0∞, z ∂μ.childCountLaw.map
          (fun n : ℕ∞ => (n : ℝ≥0∞)) := by
      rw [expectedChildCount]
      exact (lintegral_map measurable_id hcast).symm
    _ = ∫⁻ η : Measure Mark, η Set.univ ∂μ.pointMeasureLaw := by
      rw [← pointMeasureLaw_totalMass]
      exact lintegral_map measurable_id htotal

end ProbabilityTheory.BranchingProcess.OffspringConfigurationLaw

end
