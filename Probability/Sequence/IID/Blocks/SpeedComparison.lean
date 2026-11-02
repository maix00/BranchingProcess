/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.StrongLaw

/-!
# IID block bounds for an asymptotic slope

Let $P_n$ be a real-valued random position with $P_n/n\to v$ almost surely,
and let $(X_k)_{k\ge0}$ be pairwise independent, identically distributed,
integrable increments. If at block boundaries $kL$ the position is bounded
by the partial sums of these increments, the strong law compares $v$ with
$\mathbb E[X_0]/L$. The position process need not itself be a random walk.

## Public declarations

- `limit_le_expectedBlockMean_of_blockUpperBound` proves
  $v\le\mathbb E[X_0]/L$ when $P_{kL}\le\sum_{i<k}X_i$ almost surely.
- `expectedBlockMean_le_limit_of_blockLowerBound` proves the reverse bound
  when $\sum_{i<k}X_i\le P_{kL}$ almost surely.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

@[expose] public section

namespace ProbabilityTheory

private lemma blockIndex_tendsto_atTop (L : ℕ) (hL : 0 < L) :
    Tendsto (fun k : ℕ => k * L) atTop atTop := by
  exact tendsto_atTop_mono
    (fun k => Nat.le_mul_of_pos_right k (by omega)) tendsto_id

private lemma blockCompare_le_of_limits
    {f g : ℕ → ℝ} {a b : ℝ}
    (hf : Tendsto f atTop (𝓝 a)) (hg : Tendsto g atTop (𝓝 b))
    (hfg : ∀ᶠ n : ℕ in atTop, f n ≤ g n) :
    a ≤ b :=
  le_of_tendsto_of_tendsto hf hg hfg

/-- If the position at each block boundary is at most the sum of iid block
increments, the limit of the normalized position is at most the expected
increment divided by the block length. -/
theorem limit_le_expectedBlockMean_of_blockUpperBound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (L : ℕ) (hL : 0 < L)
    (position : Ω → ℕ → ℝ) (v : ℝ)
    (increment : ℕ → Ω → ℝ)
    (hint : Integrable (increment 0) μ)
    (hindep : Pairwise (fun i j => IndepFun (increment i) (increment j) μ))
    (hident : ∀ i, IdentDistrib (increment i) (increment 0) μ μ)
    (hposition : ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => ((n : ℝ)⁻¹) • position ω n) atTop (𝓝 v))
    (hblock : ∀ᵐ ω ∂μ, ∀ k,
      position ω (k * L) ≤ ∑ i ∈ Finset.range k, increment i ω) :
    v ≤ (∫ ω, increment 0 ω ∂μ) / (L : ℝ) := by
  have hindex := blockIndex_tendsto_atTop L hL
  have hsum := ProbabilityTheory.strong_law_ae increment hint hindep hident
  have hboth : ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => ((n : ℝ)⁻¹) • position ω n) atTop (𝓝 v) ∧
      Tendsto (fun k : ℕ => (k : ℝ)⁻¹ •
        (∑ i ∈ Finset.range k, increment i ω)) atTop
        (𝓝 (∫ ω, increment 0 ω ∂μ)) ∧
      ∀ k, position ω (k * L) ≤
        ∑ i ∈ Finset.range k, increment i ω :=
    hposition.and (hsum.and hblock)
  obtain ⟨ω, hbothω⟩ := hboth.exists
  rcases hbothω with ⟨hpositionω, hsumω, hblockω⟩
  have hposition : Tendsto
      (fun k : ℕ => ((k * L : ℕ) : ℝ)⁻¹ * position ω (k * L))
      atTop (𝓝 v) := by
    have h := hpositionω.comp hindex
    change Tendsto
      (fun k : ℕ => ((k * L : ℕ) : ℝ)⁻¹ * position ω (k * L))
      atTop (𝓝 v)
    exact h
  have hincrements : Tendsto
      (fun k : ℕ => ((k : ℝ)⁻¹ *
        ∑ i ∈ Finset.range k, increment i ω) / (L : ℝ))
      atTop (𝓝 ((∫ ω, increment 0 ω ∂μ) / (L : ℝ))) := by
    have h := hsumω.div_const (L : ℝ)
    simpa [smul_eq_mul] using h
  have hcompare : ∀ᶠ k : ℕ in atTop,
      ((k * L : ℕ) : ℝ)⁻¹ * position ω (k * L) ≤
        ((k : ℝ)⁻¹ *
          ∑ i ∈ Finset.range k, increment i ω) / (L : ℝ) := by
    filter_upwards [eventually_gt_atTop 0] with k hk
    have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
    have hLR : 0 < (L : ℝ) := by exact_mod_cast hL
    have hblock' := hblockω k
    calc
      ((k * L : ℕ) : ℝ)⁻¹ * position ω (k * L) ≤
          ((k * L : ℕ) : ℝ)⁻¹ *
            ∑ i ∈ Finset.range k, increment i ω :=
        mul_le_mul_of_nonneg_left hblock' (inv_nonneg.mpr (by positivity))
      _ = ((k : ℝ)⁻¹ *
          ∑ i ∈ Finset.range k, increment i ω) / (L : ℝ) := by
        push_cast
        field_simp [hkR.ne', hLR.ne']
  exact blockCompare_le_of_limits hposition hincrements hcompare

/-- If the sum of iid block increments is at most the position at each block
boundary, the expected increment divided by block length is at most the limit
of the normalized position. -/
theorem expectedBlockMean_le_limit_of_blockLowerBound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (L : ℕ) (hL : 0 < L)
    (position : Ω → ℕ → ℝ) (v : ℝ)
    (increment : ℕ → Ω → ℝ)
    (hint : Integrable (increment 0) μ)
    (hindep : Pairwise (fun i j => IndepFun (increment i) (increment j) μ))
    (hident : ∀ i, IdentDistrib (increment i) (increment 0) μ μ)
    (hposition : ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => ((n : ℝ)⁻¹) • position ω n) atTop (𝓝 v))
    (hblock : ∀ᵐ ω ∂μ, ∀ k,
      ∑ i ∈ Finset.range k, increment i ω ≤ position ω (k * L)) :
    (∫ ω, increment 0 ω ∂μ) / (L : ℝ) ≤ v := by
  have hindex := blockIndex_tendsto_atTop L hL
  have hsum := ProbabilityTheory.strong_law_ae increment hint hindep hident
  have hboth : ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => ((n : ℝ)⁻¹) • position ω n) atTop (𝓝 v) ∧
      Tendsto (fun k : ℕ => (k : ℝ)⁻¹ •
        (∑ i ∈ Finset.range k, increment i ω)) atTop
        (𝓝 (∫ ω, increment 0 ω ∂μ)) ∧
      ∀ k, ∑ i ∈ Finset.range k, increment i ω ≤ position ω (k * L) :=
    hposition.and (hsum.and hblock)
  obtain ⟨ω, hbothω⟩ := hboth.exists
  rcases hbothω with ⟨hpositionω, hsumω, hblockω⟩
  have hposition : Tendsto
      (fun k : ℕ => ((k * L : ℕ) : ℝ)⁻¹ * position ω (k * L))
      atTop (𝓝 v) := by
    have h := hpositionω.comp hindex
    change Tendsto
      (fun k : ℕ => ((k * L : ℕ) : ℝ)⁻¹ * position ω (k * L))
      atTop (𝓝 v)
    exact h
  have hincrements : Tendsto
      (fun k : ℕ => ((k : ℝ)⁻¹ *
        ∑ i ∈ Finset.range k, increment i ω) / (L : ℝ))
      atTop (𝓝 ((∫ ω, increment 0 ω ∂μ) / (L : ℝ))) := by
    have h := hsumω.div_const (L : ℝ)
    simpa [smul_eq_mul] using h
  have hcompare : ∀ᶠ k : ℕ in atTop,
      ((k : ℝ)⁻¹ *
        ∑ i ∈ Finset.range k, increment i ω) / (L : ℝ) ≤
          ((k * L : ℕ) : ℝ)⁻¹ * position ω (k * L) := by
    filter_upwards [eventually_gt_atTop 0] with k hk
    have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
    have hLR : 0 < (L : ℝ) := by exact_mod_cast hL
    have hblock' := hblockω k
    calc
      ((k : ℝ)⁻¹ *
          ∑ i ∈ Finset.range k, increment i ω) / (L : ℝ) =
          ((k * L : ℕ) : ℝ)⁻¹ *
            ∑ i ∈ Finset.range k, increment i ω := by
        rw [Nat.cast_mul]
        field_simp [hkR.ne', hLR.ne']
      _ ≤ ((k * L : ℕ) : ℝ)⁻¹ * position ω (k * L) :=
        mul_le_mul_of_nonneg_left hblock'
          (inv_nonneg.mpr (by positivity))
  exact blockCompare_le_of_limits hincrements hposition hcompare

end ProbabilityTheory

end
