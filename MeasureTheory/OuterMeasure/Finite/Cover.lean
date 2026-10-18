/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.OuterMeasure.Basic

/-!
# Outer measure bounds from finite covers

The public theorems in this file are:

- `measure_mul_le_card_mul_of_finite_cover`: for an outer measure `μ`, if each
  cell `A i` of a finite cover `F` has a target extension with
  `c · μ(A i) ≤ μ(A i ∩ B i)` and `A i ∩ B i ⊆ T`, then
  `c · μ(U) ≤ F.card · μ(T)`.
- `measure_le_card_smul_of_finite_cover_invariant`: if a finite family indexed
  by `F : Finset ι` of `μ`-invariant preimages of `safe` covers `event`, then
  `μ(event) ≤ F.card · μ(safe)`.

These estimates turn finite covers and eventwise product lower bounds into a
global measure inequality. They do not require the cover to be disjoint.
-/

@[expose] public section

namespace MeasureTheory

/-- A finite cover by outer-measure-preserving preimages gives a bound with
the cardinality of the cover. The maps need only preserve the outer measure
of `safe`. -/
theorem measure_le_card_smul_of_finite_cover_invariant
    {Ω ι F : Type*} [FunLike F (Set Ω) ENNReal] [OuterMeasureClass F Ω]
    (μ : F)
    (cover : Finset ι) (event safe : Set Ω) (rotate : ι → Ω → Ω)
    (hcover : event ⊆ ⋃ k ∈ cover, (rotate k) ⁻¹' safe)
    (hinvariant : ∀ k ∈ cover, μ ((rotate k) ⁻¹' safe) = μ safe) :
    μ event ≤ cover.card • μ safe := by
  calc
    μ event ≤ μ (⋃ k ∈ cover, (rotate k) ⁻¹' safe) := measure_mono hcover
    _ ≤ ∑ k ∈ cover, μ ((rotate k) ⁻¹' safe) := measure_biUnion_finset_le cover _
    _ = ∑ _k ∈ cover, μ safe := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hinvariant k hk
    _ = cover.card • μ safe := by simp

/-- A finite cover whose cells can each be extended into one target event
gives an outer-measure bound with the cardinality of the cover as loss. -/
theorem measure_mul_le_card_mul_of_finite_cover
    {Ω ι E : Type*} [FunLike E (Set Ω) ENNReal] [OuterMeasureClass E Ω]
    (P : E) (F : Finset ι) (U T : Set Ω)
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
