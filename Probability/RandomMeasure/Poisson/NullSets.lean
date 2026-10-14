/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.RandomMeasure.Poisson.PointFamily

/-!
# Null sets for Poisson point families

The public theorem in this file is:

- `ProbabilityTheory.IsPoissonPointFamily.ae_thinnedCount_eq_zero_of_null`:
  if the intensity assigns zero mass to $A$, every partition piece
  almost surely has zero Poisson points in $A$.
- `ProbabilityTheory.IsPoissonPointFamily.ae_point_not_mem_of_null`:
  almost surely no active point in any partition piece belongs to $A$.

This is the null-set consequence of the Poisson thinning theorem.
It applies to atomless jump-size sets in a Lévy decomposition once the
corresponding point-family representation has been established.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

/-- A set of zero intensity contains no points of the Poisson family
in any partition piece, almost surely. -/
theorem IsPoissonPointFamily.ae_thinnedCount_eq_zero_of_null
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ)
    {A : Set E} (hA : MeasurableSet A) (hnull : m A = 0) :
    ∀ᵐ ω ∂μ, ∀ k : ℕ, thinnedCount K X A k ω = 0 := by
  apply ae_all_iff.2
  intro k
  have hpiece : m (prmPiece m k ∩ A) = 0 :=
    measure_mono_null Set.inter_subset_right hnull
  have hmeas : MeasurableSet {ω | thinnedCount K X A k ω = 0} :=
    (measurable_thinnedCount (hd.measurable_count k)
      (hd.measurable_point k) hA) (measurableSet_singleton 0)
  apply (mem_ae_iff_prob_eq_one hmeas).2
  calc
    μ {ω | thinnedCount K X A k ω = 0} =
        (μ.map (thinnedCount K X A k)) {0} := by
          rw [Measure.map_apply (measurable_thinnedCount
            (hd.measurable_count k) (hd.measurable_point k) hA)
            (measurableSet_singleton 0)]
          rfl
    _ = (poissonMeasure (m (prmPiece m k ∩ A)).toNNReal) {0} := by
      rw [map_thinnedCount hd hA]
    _ = 1 := by simp [hpiece, poissonMeasure_singleton]

/-- Every active Poisson point avoids a measurable set of zero
intensity, almost surely. -/
theorem IsPoissonPointFamily.ae_point_not_mem_of_null
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    (hd : IsPoissonPointFamily K X m μ)
    {A : Set E} (hA : MeasurableSet A) (hnull : m A = 0) :
    ∀ᵐ ω ∂μ, ∀ k n : ℕ, n < K k ω → X k n ω ∉ A := by
  classical
  filter_upwards [hd.ae_thinnedCount_eq_zero_of_null hA hnull]
    with ω hcount
  intro k n hn hmem
  have hmember : n ∈ (Finset.range (K k ω)).filter
      (fun i => X k i ω ∈ A) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hn, hmem⟩
  have hpositive : 0 < thinnedCount K X A k ω := by
    unfold thinnedCount
    exact Finset.card_pos.mpr ⟨n, hmember⟩
  rw [hcount k] at hpositive
  exact (Nat.not_lt_zero 0) hpositive

end ProbabilityTheory

end
