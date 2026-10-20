/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.BranchingWalk.Selection.NSelection.Walk.Speed
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.StrongLaw

/-!
# Speed bounds from independent blocks

These lemmas finish the analytic part of a block comparison. Once a coupling
has shown that the frontier at block times is bounded by sums of independent,
identically distributed block displacements, the strong law turns that
pathwise comparison into a bound on the asymptotic speed. Constructing the
branching-process couplings is a separate step.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

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
increments, its asymptotic speed is at most the expected increment divided by
the block length. -/
theorem hasAsymptoticSpeed_le_expectedBlock
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (L : ℕ) (hL : 0 < L)
    (position : Ω → ℕ → ℝ) (v : ℝ)
    (increment : ℕ → Ω → ℝ)
    (hint : Integrable (increment 0) μ)
    (hindep : Pairwise (fun i j => IndepFun (increment i) (increment j) μ))
    (hident : ∀ i, IdentDistrib (increment i) (increment 0) μ μ)
    (hspeed : ∀ᵐ ω ∂μ,
      Combinatorics.Branching.Selection.NSelection.HasAsymptoticSpeed
        (𝕜 := ℝ) (position ω) v)
    (hblock : ∀ᵐ ω ∂μ, ∀ k,
      position ω (k * L) ≤ ∑ i ∈ Finset.range k, increment i ω) :
    v ≤ (∫ ω, increment 0 ω ∂μ) / (L : ℝ) := by
  have hindex := blockIndex_tendsto_atTop L hL
  have hsum := ProbabilityTheory.strong_law_ae increment hint hindep hident
  have hboth : ∀ᵐ ω ∂μ,
      Combinatorics.Branching.Selection.NSelection.HasAsymptoticSpeed
        (𝕜 := ℝ) (position ω) v ∧
      Tendsto (fun k : ℕ => (k : ℝ)⁻¹ •
        (∑ i ∈ Finset.range k, increment i ω)) atTop
        (𝓝 (∫ ω, increment 0 ω ∂μ)) ∧
      ∀ k, position ω (k * L) ≤
        ∑ i ∈ Finset.range k, increment i ω :=
    hspeed.and (hsum.and hblock)
  obtain ⟨ω, hbothω⟩ := hboth.exists
  rcases hbothω with ⟨hspeedω, hsumω, hblockω⟩
  have hposition : Tendsto
      (fun k : ℕ => ((k * L : ℕ) : ℝ)⁻¹ * position ω (k * L))
      atTop (𝓝 v) := by
    have h := hspeedω.comp hindex
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
boundary, its expected increment divided by block length is at most the
asymptotic speed. -/
theorem expectedBlock_le_of_hasAsymptoticSpeed
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (L : ℕ) (hL : 0 < L)
    (position : Ω → ℕ → ℝ) (v : ℝ)
    (increment : ℕ → Ω → ℝ)
    (hint : Integrable (increment 0) μ)
    (hindep : Pairwise (fun i j => IndepFun (increment i) (increment j) μ))
    (hident : ∀ i, IdentDistrib (increment i) (increment 0) μ μ)
    (hspeed : ∀ᵐ ω ∂μ,
      Combinatorics.Branching.Selection.NSelection.HasAsymptoticSpeed
        (𝕜 := ℝ) (position ω) v)
    (hblock : ∀ᵐ ω ∂μ, ∀ k,
      ∑ i ∈ Finset.range k, increment i ω ≤ position ω (k * L)) :
    (∫ ω, increment 0 ω ∂μ) / (L : ℝ) ≤ v := by
  have hindex := blockIndex_tendsto_atTop L hL
  have hsum := ProbabilityTheory.strong_law_ae increment hint hindep hident
  have hboth : ∀ᵐ ω ∂μ,
      Combinatorics.Branching.Selection.NSelection.HasAsymptoticSpeed
        (𝕜 := ℝ) (position ω) v ∧
      Tendsto (fun k : ℕ => (k : ℝ)⁻¹ •
        (∑ i ∈ Finset.range k, increment i ω)) atTop
        (𝓝 (∫ ω, increment 0 ω ∂μ)) ∧
      ∀ k, ∑ i ∈ Finset.range k, increment i ω ≤ position ω (k * L) :=
    hspeed.and (hsum.and hblock)
  obtain ⟨ω, hbothω⟩ := hboth.exists
  rcases hbothω with ⟨hspeedω, hsumω, hblockω⟩
  have hposition : Tendsto
      (fun k : ℕ => ((k * L : ℕ) : ℝ)⁻¹ * position ω (k * L))
      atTop (𝓝 v) := by
    have h := hspeedω.comp hindex
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

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

end
