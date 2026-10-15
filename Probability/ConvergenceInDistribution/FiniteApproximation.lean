/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.ConvergenceInDistribution.AsymptoticEquivalence

/-!
# Convergence in distribution through finite approximations

The public theorem in this file is:

- `MeasureTheory.tendstoInDistribution_of_finite_approximations`:
  if each fixed approximation converges in distribution, its limiting
  laws converge to the target law, and the probabilities of disagreement
  between the original and approximating variables admit bounds tending
  to zero as the approximation is refined, then the original variables
  converge in distribution.

The proof compares bounded Lipschitz observables using the coupling
bound for their expectations. It is reusable for cutoff arguments in
functional limit theorems.
-/

@[expose] public section

namespace MeasureTheory

open Filter
open scoped Topology

set_option backward.isDefEq.respectTransparency.types false in
/-- A converging-together principle for random variables coupled to
finite approximations on the same probability spaces. -/
theorem tendstoInDistribution_of_finite_approximations
    {Ω Ω' E : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace E] [PseudoEMetricSpace E] [BorelSpace E]
    [MeasurableEq E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (μ' : Measure Ω') [IsProbabilityMeasure μ']
    (X : ℕ → Ω → E) (Y : ℕ → ℕ → Ω → E)
    (Z : Ω' → E) (W : ℕ → Ω' → E)
    (hX : ∀ n, Measurable (X n))
    (hY : ∀ k n, Measurable (Y k n))
    (hZ : Measurable Z)
    (hfinite : ∀ k, TendstoInDistribution (Y k) atTop (W k)
      (fun _ => μ) μ')
    (hlimit : TendstoInDistribution W atTop Z (fun _ => μ') μ')
    (b : ℕ → ℕ → ℝ) (c : ℕ → ℝ)
    (hbound : ∀ k n, μ.real {ω | X n ω ≠ Y k n ω} ≤ b k n)
    (hb : ∀ k, Tendsto (b k) atTop (nhds (c k)))
    (hc : Tendsto c atTop (nhds 0)) :
    TendstoInDistribution X atTop Z (fun _ => μ) μ' := by
  refine ⟨fun n => (hX n).aemeasurable, hZ.aemeasurable, ?_⟩
  suffices htest : ∀ (F : E → ℝ)
      (_hF_bounded : ∃ C : ℝ, ∀ x y, dist (F x) (F y) ≤ C)
      (_hF_lip : ∃ L, LipschitzWith L F),
      Tendsto (fun n => ∫ x, F x ∂(μ.map (X n))) atTop
        (nhds (∫ x, F x ∂(μ'.map Z))) by
    rwa [tendsto_iff_forall_lipschitz_integral_tendsto]
  intro F ⟨M, hM⟩ ⟨L, hL⟩
  have hFcont : Continuous F := hL.continuous
  let A : ℕ → ℝ := fun n => ∫ x, F x ∂(μ.map (X n))
  let D : ℝ := ∫ x, F x ∂(μ'.map Z)
  let B : ℕ → ℕ → ℝ := fun k n => ∫ x, F x ∂(μ.map (Y k n))
  let C : ℕ → ℝ := fun k => ∫ x, F x ∂(μ'.map (W k))
  have hB (k : ℕ) : Tendsto (B k) atTop (nhds (C k)) :=
    (tendsto_iff_forall_lipschitz_integral_tendsto.mp
      (hfinite k).tendsto) F ⟨M, hM⟩ ⟨L, hL⟩
  have hC : Tendsto C atTop (nhds D) :=
    (tendsto_iff_forall_lipschitz_integral_tendsto.mp
      hlimit.tendsto) F ⟨M, hM⟩ ⟨L, hL⟩
  let ω₀ : Ω := (nonempty_of_isProbabilityMeasure μ).some
  have hM_nonneg : 0 ≤ M :=
    (dist_nonneg : 0 ≤ dist (F (X 0 ω₀)) (F (X 0 ω₀))).trans (hM _ _)
  have hgap (k n : ℕ) : |A n - B k n| ≤ M * b k n := by
    have hcoupling :
        |∫ ω, F (X n ω) ∂μ - ∫ ω, F (Y k n ω) ∂μ| ≤
          M * μ.real {ω | X n ω ≠ Y k n ω} :=
      abs_integral_sub_le_oscillation_mul_disagreement
        (hX n) (hY k n) hFcont hM
    rw [← integral_map (hX n).aemeasurable
      hFcont.aestronglyMeasurable,
      ← integral_map (hY k n).aemeasurable
      hFcont.aestronglyMeasurable] at hcoupling
    exact hcoupling.trans
      (mul_le_mul_of_nonneg_left (hbound k n) hM_nonneg)
  change Tendsto A atTop (nhds D)
  apply (Metric.tendsto_nhds).mpr
  intro ε hε
  have hsmall : Tendsto (fun k => M * c k + |C k - D|)
      atTop (nhds 0) := by
    convert ((hc.const_mul M).add
      (tendsto_iff_dist_tendsto_zero.mp hC)) using 1 <;>
      simp [Real.dist_eq]
  obtain ⟨k, hk⟩ : ∃ k, M * c k + |C k - D| < ε / 2 :=
    (hsmall.eventually (isOpen_Iio.mem_nhds (half_pos hε))).exists
  have hnear : Tendsto (fun n => M * b k n + |B k n - C k|)
      atTop (nhds (M * c k)) := by
    convert (((hb k).const_mul M).add
      (tendsto_iff_dist_tendsto_zero.mp (hB k))) using 1 <;>
      simp [Real.dist_eq]
  have htarget : M * c k < ε - |C k - D| := by linarith
  filter_upwards [hnear.eventually (isOpen_Iio.mem_nhds htarget)]
    with n hn
  rw [Real.dist_eq]
  have htriangle : |A n - D| ≤
      |A n - B k n| + |B k n - C k| + |C k - D| := by
    have h₁ := abs_sub_le (A n) (B k n) D
    have h₂ := abs_sub_le (B k n) (C k) D
    linarith
  have hbound' := hgap k n
  linarith

end MeasureTheory

end
