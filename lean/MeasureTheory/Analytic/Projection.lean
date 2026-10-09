/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Analytic projections

General facts about continuous images of Borel sets in Polish spaces. These
results are independent of stochastic-process path models.
-/

@[expose] public section

open MeasureTheory

namespace MeasureTheory.Analytic

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
    AnalyticSet (Prod.fst '' s) :=
  analyticSet_image_of_measurableSet hs continuous_fst

end MeasureTheory.Analytic

end
