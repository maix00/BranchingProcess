/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Measure.NullMeasurable
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Measure bounds from finite covers

These estimates turn finite covers and eventwise product lower bounds into a
global measure inequality. They do not require the cover to be disjoint.
-/

@[expose] public section

namespace MeasureTheory

/-- A finite cover whose cells can each be extended into one target event
gives a measure bound with the cardinality of the cover as loss. -/
theorem measure_mul_le_card_mul_of_finite_cover
    {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (F : Finset ι) (U T : Set Ω)
    (A B : ι → Set Ω) (c : ENNReal)
    (hcover : U ⊆ ⋃ i ∈ F, A i)
    (hfactor : ∀ i ∈ F, c * P (A i) ≤ P (A i ∩ B i))
    (hsubset : ∀ i ∈ F, A i ∩ B i ⊆ T) :
    c * P U ≤ (F.card : ENNReal) * P T := by
  have hcoverMeasure : P U ≤ ∑ i ∈ F, P (A i) := by
    calc
      P U ≤ P (⋃ i ∈ F, A i) := measure_mono hcover
      _ ≤ ∑ i ∈ F, P (A i) := measure_biUnion_finset_le F A
  have hfactorSum :
      ∑ i ∈ F, c * P (A i) ≤ ∑ i ∈ F, P (A i ∩ B i) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hfactor i hi
  have hsubsetSum :
      ∑ i ∈ F, P (A i ∩ B i) ≤ ∑ i ∈ F, P T := by
    apply Finset.sum_le_sum
    intro i hi
    exact measure_mono (hsubset i hi)
  calc
    c * P U ≤ c * ∑ i ∈ F, P (A i) :=
      mul_le_mul_of_nonneg_left hcoverMeasure bot_le
    _ = ∑ i ∈ F, c * P (A i) := by rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ F, P (A i ∩ B i) := hfactorSum
    _ ≤ ∑ i ∈ F, P T := hsubsetSum
    _ = (F.card : ENNReal) * P T := by simp

end MeasureTheory

end
