/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Kernel.Step
public import Mathlib.Basic.ENNReal.BigOperators
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Finite partial-step kernels

This file contains the finite-branch constructor for an option-valued step.
A branch returning `none` kills the corresponding mass; a branch returning
`some b` sends it to `b`.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace ProbabilityTheory

namespace Kernel

section PartialStep

variable {α β ξ : Type*} [Countable α] [MeasurableSpace α]
  [MeasurableSingletonClass α] [MeasurableSpace β] [Fintype ξ]

/-- A finite family of weighted partial steps. -/
noncomputable def ofFinitePartialStep
    (weight : ξ → ENNReal) (next : α → ξ → Option β) : Kernel α β where
  toFun a := ∑ k, weight k • (next a k).elim 0 Measure.dirac
  measurable' := measurable_of_countable _

theorem ofFinitePartialStep_apply
    (weight : ξ → ENNReal) (next : α → ξ → Option β)
    (a : α) (s : Set β) (hs : MeasurableSet s) :
    ofFinitePartialStep weight next a s =
      ∑ k, weight k * (next a k).elim 0 (fun b => s.indicator 1 b) := by
  change (∑ k, weight k • (next a k).elim 0 Measure.dirac) s = _
  rw [Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro k _
  cases hnext : next a k with
  | none => simp
  | some b => simp [Measure.dirac_apply' _ hs]

theorem lintegral_ofFinitePartialStep
    [MeasurableSingletonClass β]
    (weight : ξ → ENNReal) (next : α → ξ → Option β)
    (a : α) (f : β → ENNReal) :
    ∫⁻ b, f b ∂ofFinitePartialStep weight next a =
      ∑ k, weight k * (next a k).elim 0 f := by
  change ∫⁻ b, f b ∂(∑ k, weight k • (next a k).elim 0 Measure.dirac) = _
  rw [lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro k _
  rw [lintegral_smul_measure]
  cases next a k <;> simp

/-- A partial step is sub-Markov if the total available weight is at
most one.  Killing can only decrease its mass. -/
theorem isSubMarkovKernel_ofFinitePartialStep
    (weight : ξ → ENNReal) (next : α → ξ → Option β)
    (hweight : ∑ k, weight k ≤ 1) :
    IsSubMarkovKernel (ofFinitePartialStep weight next) where
  measure_univ_le_one a := by
    rw [ofFinitePartialStep_apply _ _ _ _ MeasurableSet.univ]
    calc
      (∑ k, weight k * (next a k).elim 0 (fun b => univ.indicator 1 b)) ≤
          ∑ k, weight k := by
        apply Finset.sum_le_sum
        intro k _
        cases next a k <;> simp
      _ ≤ 1 := hweight

/-- The explicit finite sum is the computational form of the general
partial-step constructor when `weight` records the singleton masses of the
noise law. -/
theorem ofFinitePartialStep_eq_ofPartialStep
    [MeasurableSpace ξ] [MeasurableSingletonClass ξ]
    (nu : Measure ξ) [IsProbabilityMeasure nu]
    (weight : ξ → ENNReal) (next : α → ξ → Option β)
    (hnext : Measurable (Function.uncurry next))
    (hsingleton : ∀ k, nu {k} = weight k) :
    ofFinitePartialStep weight next = ofPartialStep nu next hnext := by
  classical
  ext a s hs
  rw [ofFinitePartialStep_apply _ _ _ _ hs,
    ofPartialStep_apply _ _ hnext _ _ hs]
  have hset : {z | next a z ∈ some '' s} =
      ↑(Finset.univ.filter fun k => next a k ∈ some '' s) := by
    ext k
    simp
  rw [hset]
  rw [← MeasureTheory.sum_measure_singleton
    (μ := nu)
    (s := Finset.univ.filter fun k => next a k ∈ some '' s)]
  simp_rw [hsingleton]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  cases h : next a k with
  | none => simp
  | some b =>
      by_cases hb : b ∈ s <;> simp [hb]

end PartialStep

end Kernel

end ProbabilityTheory

end
