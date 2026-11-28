/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# Vanishing quadratic upper tails

## Public declarations

In `MeasureTheory`:

* `HasVanishingQuadraticTail μ f` means `x² μ{f > x} → 0` as `x → ∞`.
* `HasVanishingQuadraticTail.scale_threshold` gives
  `x² μ{f > c x} → 0` for every `c > 0`.
* `hasVanishingQuadraticTail_max_const_iff` preserves tails when clipping below any constant.
* `hasVanishingQuadraticTail_map_iff` transports the condition through a measurable map.
* `HasVanishingQuadraticTail.mono` transfers the condition along pointwise order.
* `HasVanishingQuadraticTail.add` preserves it under addition, allowing dependence.
* `hasVanishingQuadraticTail_abs_of_integrable_sq` derives
  `x² μ{|f| > x} → 0` from an integrable square.
* `hasVanishingQuadraticTail_add_iff_of_integrable_sq` states
  `Tail₂(f + g) ↔ Tail₂(f)` when `g²` is integrable.

The perturbation argument uses two half-threshold union bounds. It is the
finite-second-moment comparison of the relative offspring mark and the total
offspring log-weight in B. Mallein, *N-branching random walk with α-stable spine*
(2015), Theorem 1.1, condition (1.9), arXiv:1503.03762, specialized to α = 2.
These lemmas concern arbitrary finite measures and dependent real observations;
no random walk, branching law or independence appears in their statements.
-/

@[expose] public section

namespace MeasureTheory

open Filter
open scoped Topology

/-- A strict upper tail which is little-o of the inverse squared threshold. -/
def HasVanishingQuadraticTail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (f : Ω → ℝ) : Prop :=
  Tendsto (fun x : ℝ => x ^ 2 * μ.real {ω | x < f ω}) atTop (𝓝 0)

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {f g : Ω → ℝ}

theorem HasVanishingQuadraticTail.scale_threshold
    (hf : HasVanishingQuadraticTail μ f) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => x ^ 2 * μ.real {ω | c * x < f ω}) atTop (𝓝 0) := by
  have ht := (hf.comp ((tendsto_const_mul_atTop_of_pos hc).2 tendsto_id)).const_mul (c ^ 2)⁻¹
  simpa only [Function.comp_def, id_eq, mul_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hc.ne'), one_mul,
    mul_zero] using ht

/-- Pushforward invariance of the tail condition. -/
theorem hasVanishingQuadraticTail_map_iff {E : Type*} [MeasurableSpace E]
    (T : Ω → E) (hT : Measurable T) (F : E → ℝ) (hF : Measurable F) :
    HasVanishingQuadraticTail (μ.map T) F ↔
      HasVanishingQuadraticTail μ (fun ω => F (T ω)) := by
  unfold HasVanishingQuadraticTail
  simp only [Measure.real, Measure.map_apply hT
    (measurableSet_lt measurable_const hF), Set.preimage_ofPred_eq]

/-- Clipping below a fixed constant leaves the upper-tail condition unchanged. -/
theorem hasVanishingQuadraticTail_max_const_iff (c : ℝ) :
    HasVanishingQuadraticTail μ (fun ω => max (f ω) c) ↔
      HasVanishingQuadraticTail μ f := by
  unfold HasVanishingQuadraticTail
  apply tendsto_congr'
  filter_upwards [eventually_gt_atTop c] with x hx
  congr 2
  ext ω
  simp only [Set.mem_ofPred_eq, lt_max_iff]
  exact or_iff_left (not_lt.mpr hx.le)

variable [IsFiniteMeasure μ]

theorem HasVanishingQuadraticTail.mono
    (hg : HasVanishingQuadraticTail μ g) (hfg : ∀ ω, f ω ≤ g ω) :
    HasVanishingQuadraticTail μ f := by
  apply squeeze_zero (fun x => mul_nonneg (sq_nonneg x) measureReal_nonneg) _ hg
  intro x
  exact mul_le_mul_of_nonneg_left (measureReal_mono (fun ω h => h.trans_le (hfg ω)))
    (sq_nonneg x)

theorem HasVanishingQuadraticTail.add
    (hf : HasVanishingQuadraticTail μ f) (hg : HasVanishingQuadraticTail μ g) :
    HasVanishingQuadraticTail μ (fun ω => f ω + g ω) := by
  have ht := (hf.scale_threshold (by norm_num : (0 : ℝ) < 1 / 2)).add
    (hg.scale_threshold (by norm_num : (0 : ℝ) < 1 / 2))
  simp only [zero_add] at ht
  apply squeeze_zero (fun x => mul_nonneg (sq_nonneg x) measureReal_nonneg) _ ht
  intro x
  have hset : {ω | x < f ω + g ω} ⊆
      {ω | (1 / 2 : ℝ) * x < f ω} ∪ {ω | (1 / 2 : ℝ) * x < g ω} := by
    intro ω hω
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at h
    change x < f ω + g ω at hω
    linarith
  calc
    _ ≤ x ^ 2 * (μ.real {ω | (1 / 2 : ℝ) * x < f ω} +
        μ.real {ω | (1 / 2 : ℝ) * x < g ω}) :=
      mul_le_mul_of_nonneg_left
        ((measureReal_mono hset).trans (measureReal_union_le _ _)) (sq_nonneg x)
    _ = _ := mul_add _ _ _

/-- Finite second moments give vanishing quadratic tails, rather than just
a bounded Markov quotient. The dominating tail integral tends to zero. -/
theorem hasVanishingQuadraticTail_abs_of_integrable_sq
    (hf : Measurable f) (hfi : Integrable (fun ω => f ω ^ 2) μ) :
    HasVanishingQuadraticTail μ (fun ω => |f ω|) := by
  have hfa : Measurable (fun ω => |f ω|) := by
    simpa only [Real.norm_eq_abs] using hf.norm
  let F (x : ℝ) := {ω | x < |f ω|}.indicator (fun ω => f ω ^ 2)
  have hFm (x : ℝ) : Measurable (F x) :=
    (hf.pow_const 2).indicator (measurableSet_lt measurable_const hfa)
  have ht : Tendsto (fun x : ℝ => ∫ ω, F x ω ∂μ) atTop (𝓝 0) := by
    simpa using tendsto_integral_filter_of_dominated_convergence
      (f := fun _ => (0 : ℝ)) (fun ω => f ω ^ 2) (Filter.Eventually.of_forall fun x => (hFm x).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => Filter.Eventually.of_forall fun ω => by
        by_cases h : x < |f ω|
        · simp [F, h, Real.norm_eq_abs]
        · simp [F, h, sq_nonneg])
      hfi (Filter.Eventually.of_forall fun ω => by
        apply tendsto_const_nhds.congr'
        filter_upwards [eventually_gt_atTop |f ω|] with x hx
        simp [F, hx.not_gt])
  apply squeeze_zero' (Filter.Eventually.of_forall
    fun x => mul_nonneg (sq_nonneg x) measureReal_nonneg) _ ht
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  have hs : MeasurableSet {ω | x < |f ω|} := measurableSet_lt measurable_const hfa
  calc
    _ ≤ ∫ ω in {ω | x < |f ω|}, f ω ^ 2 ∂μ :=
      setIntegral_ge_of_const_le_real hs (measure_ne_top _ _)
        (fun ω hω => by nlinarith [sq_abs (f ω),
          (sq_le_sq₀ hx (abs_nonneg (f ω))).mpr hω.le])
        (hfi.mono_measure Measure.restrict_le_self)
    _ = ∫ ω, F x ω ∂μ := (integral_indicator hs).symm

/-- Adding any finite-second-moment perturbation preserves exactly the same
vanishing upper-tail condition; no independence is required. -/
theorem hasVanishingQuadraticTail_add_iff_of_integrable_sq
    (hg : Measurable g) (hgi : Integrable (fun ω => g ω ^ 2) μ) :
    HasVanishingQuadraticTail μ (fun ω => f ω + g ω) ↔
      HasVanishingQuadraticTail μ f := by
  have ha := hasVanishingQuadraticTail_abs_of_integrable_sq hg hgi
  constructor
  · intro h
    exact (h.add ha).mono (fun ω => by linarith [neg_le_abs (g ω)])
  · intro h
    exact (h.add ha).mono (fun ω => add_le_add_right (le_abs_self _) _)

end MeasureTheory
