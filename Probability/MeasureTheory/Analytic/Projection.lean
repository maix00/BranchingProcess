/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Probability.Process.SmallDeviation.Mogulskii.PathClass.Measurable
public import Topology.Cadlag.Skorokhod.Separable

/-!
# Analyticity of projections of Borel path-time relations

Mathlib's Polish-space API gives an axiom-clean intermediate result for
projections of Borel relations: their projections are analytic.  Analyticity
alone is not used here as a substitute for null-measurability; the latter
requires the separate Choquet-capacitability theorem for arbitrary finite
Borel measures.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.MeasureTheory.Analytic

/-- A continuous image of a Borel subset of a Polish space is analytic. -/
theorem analyticSet_image_of_measurableSet
    {α β : Type*} [TopologicalSpace α] [PolishSpace α]
    [MeasurableSpace α] [BorelSpace α] [TopologicalSpace β]
    {s : Set α} (hs : MeasurableSet s) {f : α → β} (hf : Continuous f) :
    AnalyticSet (f '' s) :=
  hs.analyticSet.image_of_continuous hf

/-- The projection of a Borel subset of a product of Polish spaces is
analytic. -/
theorem analyticSet_fst_image_of_measurableSet
    {α β : Type*} [TopologicalSpace α] [PolishSpace α]
    [MeasurableSpace α] [BorelSpace α] [TopologicalSpace β]
    [PolishSpace β] [MeasurableSpace β] [BorelSpace β]
    {s : Set (α × β)} (hs : MeasurableSet s) :
    AnalyticSet (Prod.fst '' s) := by
  exact analyticSet_image_of_measurableSet hs continuous_fst

/-- The second projection of the exact path-time violation relation for an
`M₂` corridor is analytic.  The event remains the projection of the actual
pointwise violation relation. -/
theorem M2Corridor.analyticSet_violationSet
    (c : ProbabilityTheory.Process.SmallDeviation.Mogulskii.M2Corridor) :
    AnalyticSet c.violationSet := by
  have hproj : c.violationSet = Prod.snd '' c.violationAt := by
    ext path
    simp only [ProbabilityTheory.Process.SmallDeviation.Mogulskii.M2Corridor.violationSet,
      Set.mem_ofPred_eq, Set.mem_image, Prod.exists, exists_eq_right]
  rw [hproj]
  exact analyticSet_image_of_measurableSet c.measurableSet_violationAt continuous_snd

end ProbabilityTheory.MeasureTheory.Analytic

end
