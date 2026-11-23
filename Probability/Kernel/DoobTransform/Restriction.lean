/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Kernel.DoobTransform.Basic
public import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Doob transforms on the finite positive-weight region

## Public declarations

* `ProbabilityTheory.Kernel.doobTransformOnPositive`: restricts the input
  and output of the same Doob kernel to `E = {x | 0 < h(x) < ∞}`.
* `ProbabilityTheory.Kernel.doobTransformOnPositive_isMarkovKernel`:
  harmonicity on `E` alone makes this restricted kernel Markov.
* `ProbabilityTheory.Kernel.doobTransformOnPositive_map`: erasing the
  subtype recovers the original Doob transition at every state in `E`.

This is the eligible-state form of Zhan Shi, *Branching Random Walks*,
LNM 2151 (2015), Chapter 4, §4.2, (4.3)–(4.4),
DOI 10.1007/978-3-319-25372-5. It uses native kernel input and output comaps.
-/

@[expose] public section

namespace ProbabilityTheory.Kernel

open MeasureTheory
open scoped ENNReal

variable {S : Type*} [MeasurableSpace S]

/-- Restrict the same weighted transition to its finite positive-weight states. -/
noncomputable def doobTransformOnPositive (K : Kernel S S) [IsSFiniteKernel K]
    {h : S → ℝ≥0∞} (hh : Measurable h) :
    Kernel {x // h x ≠ 0 ∧ h x ≠ ∞} {x // h x ≠ 0 ∧ h x ≠ ∞} :=
  ((doobTransform K h).comap Subtype.val measurable_subtype_coe).comapRight
    (MeasurableEmbedding.subtype_coe
      (show MeasurableSet {x | h x ≠ 0 ∧ h x ≠ ∞} from
        (hh (MeasurableSet.singleton 0).compl).inter
          (hh (MeasurableSet.singleton ∞).compl)))

/-- Harmonicity on the eligible region normalizes the restricted transition. -/
theorem doobTransformOnPositive_isMarkovKernel (K : Kernel S S) [IsSFiniteKernel K]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ x, h x ≠ 0 → h x ≠ ∞ → (∫⁻ y, h y ∂K x) = h x) :
    IsMarkovKernel (doobTransformOnPositive K hh) := by
  constructor
  intro x
  let := doobTransform_isProbabilityMeasure K hh x.1 x.2.1 x.2.2
    (harmonic x.1 x.2.1 x.2.2)
  have hs : ∀ᵐ y ∂doobTransform K h x.1, h y ≠ 0 ∧ h y ≠ ∞ :=
    (ae_doobTransform_weight_ne_zero K hh x.1).and
      (ae_doobTransform_weight_ne_top K hh x.1
        ((harmonic x.1 x.2.1 x.2.2).trans_ne x.2.2))
  constructor
  rw [doobTransformOnPositive, comapRight_apply' _ _ _ MeasurableSet.univ,
    comap_apply, Set.image_univ, Subtype.range_coe]
  exact (measure_congr (by filter_upwards [hs] with y hy; simp [hy])).trans (measure_univ)

/-- Forgetting the state restriction recovers the weighted transition. -/
theorem doobTransformOnPositive_map (K : Kernel S S) [IsSFiniteKernel K]
    {h : S → ℝ≥0∞} (hh : Measurable h)
    (harmonic : ∀ x, h x ≠ 0 → h x ≠ ∞ → (∫⁻ y, h y ∂K x) = h x)
    (x : {x // h x ≠ 0 ∧ h x ≠ ∞}) :
    (doobTransformOnPositive K hh x).map Subtype.val = doobTransform K h x.1 := by
  have he : MeasurableEmbedding (Subtype.val : {x // h x ≠ 0 ∧ h x ≠ ∞} → S) :=
    MeasurableEmbedding.subtype_coe (show MeasurableSet {x | h x ≠ 0 ∧ h x ≠ ∞} from
      (hh (MeasurableSet.singleton 0).compl).inter
        (hh (MeasurableSet.singleton ∞).compl))
  rw [doobTransformOnPositive, comapRight_apply, comap_apply]
  refine (he.map_comap _).trans ?_
  apply Measure.restrict_eq_self_of_ae_mem
  have hs := (ae_doobTransform_weight_ne_zero K hh x.1).and
    (ae_doobTransform_weight_ne_top K hh x.1
      ((harmonic x.1 x.2.1 x.2.2).trans_ne x.2.2))
  filter_upwards [hs] with y hy
  exact ⟨⟨y, hy⟩, rfl⟩


end ProbabilityTheory.Kernel

end
