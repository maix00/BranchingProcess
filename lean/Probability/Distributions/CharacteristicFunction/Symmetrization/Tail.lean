/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Probability.Distributions.CharacteristicFunction.Symmetrization
public import Mathlib.MeasureTheory.Measure.Interval
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Two-sided tails under symmetrization

This file records elementary probability bounds relating the tail of a law to
the tail of the difference of two independent variables with that law. These
bounds are the measure-theoretic input for transferring regular variation
from a symmetrized law back to the original law.
-/

open MeasureTheory Set Filter
open scoped Topology

@[expose] public section

namespace ProbabilityTheory

/-- The two-sided tail of a real-valued measure. -/
noncomputable def twoSidedTail (μ : Measure ℝ) (x : ℝ) : ℝ :=
  μ.real {z : ℝ | x < |z|}

/-- The probability mass in the closed symmetric interval of radius `x`. -/
noncomputable def absBallMass (μ : Measure ℝ) (x : ℝ) : ℝ :=
  μ.real {z : ℝ | |z| ≤ x}

/-- The symmetrized law is the pushforward of the product law by subtraction. -/
theorem symmetrizedMeasure_eq_map_sub_prod (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    symmetrizedMeasure μ =
      (μ.prod μ).map (fun p : ℝ × ℝ => p.1 - p.2) := by
  rw [symmetrizedMeasure, Measure.conv]
  have hprod : μ.prod (μ.map Neg.neg) =
      (μ.prod μ).map (Prod.map id Neg.neg) := by
    rw [← Measure.map_prod_map μ μ measurable_id measurable_neg]
    simp
  rw [hprod, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1

/-- The closed absolute-value interval and its two-sided tail partition the
whole probability mass. -/
theorem measureReal_abs_le_add_twoSidedTail (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (x : ℝ) :
    μ.real {z : ℝ | |z| ≤ x} + twoSidedTail μ x = 1 := by
  let μabs : Measure ℝ := μ.map abs
  have hprob : IsProbabilityMeasure μabs := by
    dsimp [μabs]
    infer_instance
  have hmap₁ : μabs.real (Iic x) = μ.real {z : ℝ | |z| ≤ x} := by
    dsimp [μabs]
    rw [map_measureReal_apply (by fun_prop) measurableSet_Iic]
    rfl
  have hmap₂ : μabs.real (Ioi x) = twoSidedTail μ x := by
    dsimp [μabs, twoSidedTail]
    rw [map_measureReal_apply (by fun_prop) measurableSet_Ioi]
    rfl
  have hcomp : Ioi x = (Iic x)ᶜ := by
    ext z
    simp
  have hfinite : IsFiniteMeasure μabs := ⟨by
    rw [hprob.measure_univ]
    norm_num⟩
  have h := @measureReal_add_measureReal_compl ℝ _ μabs (Iic x) hfinite measurableSet_Iic
  rw [hmap₁, ← hcomp, hmap₂] at h
  have htotal : μabs.real univ = 1 := by simp [Measure.real]
  rw [htotal] at h
  exact h

/-- Closed interval mass is one minus the two-sided tail. -/
theorem absBallMass_eq_one_sub_twoSidedTail (μ : Measure ℝ)
    [IsProbabilityMeasure μ] (x : ℝ) :
    absBallMass μ x = 1 - twoSidedTail μ x := by
  have h := measureReal_abs_le_add_twoSidedTail μ x
  dsimp [absBallMass]
  linarith

/-- A probability measure has vanishing two-sided tails. -/
theorem twoSidedTail_tendsto_zero (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    Tendsto (twoSidedTail μ) atTop (nhds 0) := by
  let μabs : Measure ℝ := μ.map abs
  have hprob : IsProbabilityMeasure μabs := by
    dsimp [μabs]
    infer_instance
  have htotal : μabs univ = 1 := hprob.measure_univ
  have hfinite : IsFiniteMeasure μabs := ⟨by
    rw [htotal]
    norm_num⟩
  have hIic : Tendsto (fun x : ℝ => μabs (Iic x)) atTop (nhds (μabs univ)) :=
    tendsto_measure_Iic_atTop μabs
  have hreal : Tendsto (fun x : ℝ => μabs.real (Iic x)) atTop (nhds 1) := by
    have hcont : ContinuousAt ENNReal.toReal (μabs univ) := by
      rw [htotal]
      exact ENNReal.continuousAt_toReal (by norm_num)
    have h := hcont.tendsto.comp hIic
    rw [htotal] at h
    simpa only [Function.comp_def, Measure.real, ENNReal.toReal_one] using h
  have heq : twoSidedTail μ =ᶠ[atTop]
      fun x => 1 - μabs.real (Iic x) := by
    filter_upwards [] with x
    have hmap : μabs.real (Ioi x) = twoSidedTail μ x := by
      dsimp [μabs, twoSidedTail]
      rw [map_measureReal_apply (by fun_prop) measurableSet_Ioi]
      rfl
    have hc := @measureReal_add_measureReal_compl ℝ _ μabs (Iic x) hfinite measurableSet_Iic
    have htotal : μabs.real univ = 1 := by simp [Measure.real, hprob.measure_univ]
    have hIoi : Ioi x = (Iic x)ᶜ := by ext z; simp
    have hcomp : μabs.real (Iic x)ᶜ = twoSidedTail μ x := by
      calc
        μabs.real (Iic x)ᶜ = μabs.real (Ioi x) := by rw [← hIoi]
        _ = twoSidedTail μ x := hmap
    rw [hcomp, htotal] at hc
    dsimp [twoSidedTail]
    dsimp [twoSidedTail] at hc
    linarith
  have hsub : Tendsto (fun x : ℝ => 1 - μabs.real (Iic x)) atTop (nhds (1 - 1)) :=
    tendsto_const_nhds.sub hreal
  simpa using hsub.congr' heq.symm

/-- Two disjoint rectangles in the product space give a lower bound for the
absolute tail of the difference of two iid variables. -/
theorem twoSidedTail_symmetrized_lower_bound {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {x ε : ℝ} (hx : 0 < x) (hε : 0 < ε) :
    2 * twoSidedTail μ ((1 + ε) * x) * μ.real {z : ℝ | |z| ≤ ε * x} ≤
      twoSidedTail (symmetrizedMeasure μ) x := by
  let A : Set ℝ := {z | (1 + ε) * x < |z|}
  let B : Set ℝ := {z | |z| ≤ ε * x}
  let E : Set (ℝ × ℝ) := {p | x < |p.1 - p.2|}
  have hmap : twoSidedTail (symmetrizedMeasure μ) x = (μ.prod μ).real E := by
    rw [twoSidedTail, symmetrizedMeasure_eq_map_sub_prod,
      map_measureReal_apply (by fun_prop) (by measurability)]
    rfl
  have hsubset : A ×ˢ B ∪ B ×ˢ A ⊆ E := by
    intro p hp
    rcases hp with hp | hp
    · have ha : (1 + ε) * x < |p.1| := hp.1
      have hb : |p.2| ≤ ε * x := hp.2
      have hab : |p.1| ≤ |p.1 - p.2| + |p.2| := by
        calc
          |p.1| = |(p.1 - p.2) + p.2| := by congr 1; ring
          _ ≤ |p.1 - p.2| + |p.2| := abs_add_le _ _
      dsimp [E]
      have hcancel : (1 + ε) * x - ε * x = x := by ring
      linarith
    · have hb : |p.1| ≤ ε * x := hp.1
      have ha : (1 + ε) * x < |p.2| := hp.2
      have hab : |p.2| ≤ |p.1 - p.2| + |p.1| := by
        calc
          |p.2| = |(p.2 - p.1) + p.1| := by congr 1; ring
          _ ≤ |p.2 - p.1| + |p.1| := abs_add_le _ _
          _ = |p.1 - p.2| + |p.1| := by rw [abs_sub_comm]
      dsimp [E]
      have hcancel : (1 + ε) * x - ε * x = x := by ring
      linarith
  have hdisj : Disjoint (A ×ˢ B) (B ×ˢ A) := by
    rw [Set.disjoint_left]
    intro p hp₁ hp₂
    have ha : (1 + ε) * x < |p.1| := hp₁.1
    have hb : |p.1| ≤ ε * x := hp₂.1
    have hcancel : (1 + ε) * x - ε * x = x := by ring
    have hpos : 0 < ε * x := mul_pos hε hx
    linarith
  have hrect₁ : (μ.prod μ).real (A ×ˢ B) = μ.real A * μ.real B :=
    measureReal_prod_prod A B
  have hrect₂ : (μ.prod μ).real (B ×ˢ A) = μ.real B * μ.real A :=
    measureReal_prod_prod B A
  rw [hmap]
  calc
    2 * twoSidedTail μ ((1 + ε) * x) * μ.real {z : ℝ | |z| ≤ ε * x} =
        (μ.prod μ).real (A ×ˢ B ∪ B ×ˢ A) := by
          rw [measureReal_union hdisj (by measurability)]
          simp only [twoSidedTail, A, B, hrect₁, hrect₂]
          ring
    _ ≤ (μ.prod μ).real E := measureReal_mono hsubset

/-- An upper bound for the difference tail: either one variable is large, or
both variables have magnitude above the small threshold. -/
theorem twoSidedTail_symmetrized_upper_bound {μ : Measure ℝ}
    [IsProbabilityMeasure μ] {x ε : ℝ} (hx : 0 < x) (hε : 0 < ε) (hε1 : ε < 1) :
    twoSidedTail (symmetrizedMeasure μ) x ≤
      2 * twoSidedTail μ ((1 - ε) * x) + (twoSidedTail μ (ε * x)) ^ 2 := by
  let A : Set ℝ := {z | (1 - ε) * x < |z|}
  let B : Set ℝ := {z | ε * x < |z|}
  let E : Set (ℝ × ℝ) := {p | x < |p.1 - p.2|}
  let C₁ : Set (ℝ × ℝ) := A ×ˢ Set.univ
  let C₂ : Set (ℝ × ℝ) := Set.univ ×ˢ A
  let C₃ : Set (ℝ × ℝ) := B ×ˢ B
  have hmap : twoSidedTail (symmetrizedMeasure μ) x = (μ.prod μ).real E := by
    rw [twoSidedTail, symmetrizedMeasure_eq_map_sub_prod,
      map_measureReal_apply (by fun_prop) (by measurability)]
    rfl
  have hsubset : E ⊆ C₁ ∪ (C₂ ∪ C₃) := by
    intro p hp
    by_cases hA₁ : p.1 ∈ A
    · exact Or.inl ⟨hA₁, Set.mem_univ _⟩
    by_cases hA₂ : p.2 ∈ A
    · exact Or.inr (Or.inl ⟨Set.mem_univ _, hA₂⟩)
    have hboundA₁ : |p.1| ≤ (1 - ε) * x := le_of_not_gt hA₁
    have hboundA₂ : |p.2| ≤ (1 - ε) * x := le_of_not_gt hA₂
    have hsum : |p.1 - p.2| ≤ |p.1| + |p.2| := by
      calc
        |p.1 - p.2| = |p.1 + -p.2| := by rw [sub_eq_add_neg]
        _ ≤ |p.1| + |-p.2| := abs_add_le _ _
        _ = |p.1| + |p.2| := by simp
    have hεx : 0 ≤ ε * x := (mul_pos hε hx).le
    have honeεx : 0 ≤ (1 - ε) * x := (mul_pos (by linarith) hx).le
    have hcancel : (1 - ε) * x + ε * x = x := by ring
    refine Or.inr (Or.inr ?_)
    change p.1 ∈ B ∧ p.2 ∈ B
    constructor
    · by_contra hn
      have hlow : |p.1| ≤ ε * x := le_of_not_gt hn
      dsimp [E] at hp
      nlinarith
    · by_contra hn
      have hlow : |p.2| ≤ ε * x := le_of_not_gt hn
      dsimp [E] at hp
      nlinarith
  have hrect₁ : (μ.prod μ).real C₁ = μ.real A := by
    dsimp [C₁]
    rw [measureReal_prod_prod]
    simp
  have hrect₂ : (μ.prod μ).real C₂ = μ.real A := by
    dsimp [C₂]
    rw [measureReal_prod_prod]
    simp
  have hrect₃ : (μ.prod μ).real C₃ = (μ.real B) ^ 2 := by
    dsimp [C₃]
    rw [measureReal_prod_prod]
    ring
  rw [hmap]
  calc
    (μ.prod μ).real E ≤ (μ.prod μ).real (C₁ ∪ (C₂ ∪ C₃)) :=
      measureReal_mono hsubset
    _ ≤ (μ.prod μ).real C₁ + (μ.prod μ).real C₂ + (μ.prod μ).real C₃ := by
      calc
        _ ≤ (μ.prod μ).real C₁ + (μ.prod μ).real (C₂ ∪ C₃) :=
          measureReal_union_le (μ := μ.prod μ) _ _
        _ ≤ _ := by nlinarith [measureReal_union_le (μ := μ.prod μ) C₂ C₃]
    _ = 2 * twoSidedTail μ ((1 - ε) * x) +
        (twoSidedTail μ (ε * x)) ^ 2 := by
      rw [hrect₁, hrect₂, hrect₃]
      simp only [twoSidedTail, A, B]
      ring

end ProbabilityTheory

end
