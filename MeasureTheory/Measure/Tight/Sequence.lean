/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Measure.Tight
public import MeasureTheory.Measure.Tight.FiniteFamily

/-!
# Tightness of sequential families of measures

This file records a generic finite-prefix principle for tightness. It only
uses the compact-complement characterization of `IsTightMeasureSet`; no
separability, completeness, or regularity assumptions on the underlying
space are needed when tightness of individual measures is supplied directly.

## Public declarations

Individual tightness together with one compact tail bound uniform over all
sufficiently late indices implies tightness of the full sequence range:

\[
\left[\forall n,\ \{\mu_n\}\text{ is tight}\right]
\land
\left[\forall\varepsilon>0,\ \exists N,K\text{ compact},\
\forall n\ge N,\ \mu_n(K^{\complement})\le\varepsilon\right]
\Longrightarrow \{\mu_n:n\in\mathbb N\}\text{ is tight}.
\]

* `MeasureTheory.isTightMeasureSet_image_Iio_of_singletons` states
  `(∀ n, IsTightMeasureSet {μ n}) → IsTightMeasureSet (μ '' Iio N)`.
* `MeasureTheory.isTightMeasureSet_range_of_eventually_uniform_compact_mass_bound`
  states that individual tightness and `∀ ε > 0, ∃ N K` compact with
  `∀ n ≥ N, μ n (Kᶜ) ≤ ε` imply `IsTightMeasureSet (range μ)`.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace MeasureTheory

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X]

/-- A finite image of individually tight measures is tight. -/
theorem isTightMeasureSet_image_Iio_of_singletons
    (μ : ℕ → Measure X)
    (hsingle : ∀ n, IsTightMeasureSet {μ n}) (N : ℕ) :
    IsTightMeasureSet (μ '' Iio N) :=
  isTightMeasureSet_image_of_finite μ (Set.finite_Iio N) hsingle

/-- If every measure in a sequence is tight, and for each error tolerance a
single compact set controls all sufficiently late measures, then the range of
the sequence is tight. The finitely many earlier measures are handled by
`isTightMeasureSet_image_Iio_of_singletons`. -/
theorem isTightMeasureSet_range_of_eventually_uniform_compact_mass_bound
    (μ : ℕ → Measure X)
    (hsingle : ∀ n, IsTightMeasureSet {μ n})
    (htail : ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ N : ℕ, ∃ K : Set X, IsCompact K ∧ ∀ n, N ≤ n → μ n Kᶜ ≤ ε) :
    IsTightMeasureSet (Set.range μ) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  have hhalf : 0 < ε / 2 := ENNReal.div_pos (ne_of_gt hε) (by norm_num)
  obtain ⟨N, tailK, htailCompact, htailMass⟩ := htail (ε / 2) hhalf
  have hprefix : IsTightMeasureSet (μ '' Iio N) :=
    isTightMeasureSet_image_Iio_of_singletons μ hsingle N
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le] at hprefix
  obtain ⟨prefixK, hprefixCompact, hprefixMass⟩ := hprefix (ε / 2) hhalf
  refine ⟨tailK ∪ prefixK, htailCompact.union hprefixCompact, ?_⟩
  intro ν hν
  obtain ⟨n, rfl⟩ := hν
  by_cases hn : n < N
  · calc
      μ n (tailK ∪ prefixK)ᶜ ≤ μ n prefixKᶜ :=
        measure_mono (by simp only [compl_union]; exact inter_subset_right)
      _ ≤ ε / 2 := hprefixMass (μ n) ⟨n, hn, rfl⟩
      _ ≤ ε := ENNReal.div_le_of_le_mul <|
        le_mul_of_one_le_right (by positivity) (by norm_num)
  · have hn' : N ≤ n := Nat.le_of_not_gt hn
    calc
      μ n (tailK ∪ prefixK)ᶜ ≤ μ n tailKᶜ :=
        measure_mono (by simp only [compl_union]; exact inter_subset_left)
      _ ≤ ε / 2 := htailMass n hn'
      _ ≤ ε := ENNReal.div_le_of_le_mul <|
        le_mul_of_one_le_right (by positivity) (by norm_num)

end MeasureTheory
