/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Corridor
public import Analysis.Asymptotics.SlowDiagonal

/-!
# Block counts at the stable small-deviation scale

The partition step of Mogulskii's stable proof splits `[0, 1]` into finitely
many intervals and compares the two-sided corridor probability with the
product of the per-block corridor probabilities. The comparison itself is
scale-free and lives in `Walk/Path/Block/Partition/Basic.lean` and
`Walk/Path/Block/Partition/Normalized.lean`; this module only supplies the stable block-length
bookkeeping that turns the block length into the block count those statements take as a parameter.

The count is the largest number of complete blocks of the stable block length
that fit in `n` steps. Its asymptotic form, which is what the rate statement
consumes, additionally needs the stable block length to vanish relative to
`n`, and
`tendsto_stableBlockCount_mul_stableBlockLength_div_nat` derives it from that single hypothesis.
-/

@[expose] public section

open Filter MeasureTheory

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii


/-! ## The number of complete blocks -/

/-- The largest number of complete blocks of the stable block length that fit in
`n` steps. -/
noncomputable def stableBlockCount (α : ℝ) (ν : Measure ℝ) (constant : ℝ)
    (scale : ℕ → ℝ) (n : ℕ) : ℕ :=
  n / stableBlockLength α ν constant scale n

/-- The complete blocks fit in `n` steps. -/
theorem stableBlockCount_mul_stableBlockLength_le
    (α : ℝ) (ν : Measure ℝ) (constant : ℝ) (scale : ℕ → ℝ) (n : ℕ) :
    stableBlockCount α ν constant scale n *
        stableBlockLength α ν constant scale n ≤ n := by
  simpa [stableBlockCount, Asymptotics.blockCount] using
    Asymptotics.blockCount_mul_blockLength_le
      (fun n => stableBlockLength α ν constant scale n) n

/-- Under the source two-scale condition, retain any fixed-parameter
eventual property along a parameter tending to infinity, while making its
product with `scale n / normalization n` tend to zero. In Lemma 4 this is the
diagonal constraint `a(n) * x(n) / B(n) → 0`; the fixed-parameter probability
limits and the regular-variation transfer of `B*` remain separate inputs. -/
theorem exists_slowDiagonal_within_stableScale
    {α : ℝ} {ν : Measure ℝ} {normalization scale : ℕ → ℝ}
    {P : ℕ → ℕ → Prop}
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hfixed : ∀ k, ∀ᶠ n : ℕ in atTop, P k n) :
    ∃ d : ℕ → ℕ, Monotone d ∧ Tendsto d atTop atTop ∧
      (∀ᶠ n : ℕ in atTop, P (d n) n) ∧
      Tendsto (fun n => (d n : ℝ) * (scale n / normalization n))
        atTop (nhds 0) := by
  have hratio := hscale.scale_div_normalization_tendsto_zero
  have hratio_nonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ scale n / normalization n := by
    filter_upwards [hscale.eventually_scale_pos,
      hscale.eventually_normalization_pos] with n hs hn
    exact le_of_lt (div_pos hs hn)
  exact Asymptotics.exists_tendsto_slowDiagonal_mul_tendsto_zero
    hfixed hratio hratio_nonneg

/-- A block length that fits in `n` gives at least one complete block. -/
theorem stableBlockCount_pos_of_stableBlockLength_le
    {α : ℝ} {ν : Measure ℝ} {constant : ℝ} {scale : ℕ → ℝ} {n : ℕ}
    (hpos : 0 < stableBlockLength α ν constant scale n)
    (hle : stableBlockLength α ν constant scale n ≤ n) :
    0 < stableBlockCount α ν constant scale n :=
  Nat.div_pos hle hpos

/-- The block count brackets `n`: the complete blocks fit in the available `n`
steps, and one further block would not. This is the deterministic bracket that the
block asymptotics and the partition argument both rest on. -/
theorem stableBlockCount_mul_stableBlockLength_le_lt_succ
    (α : ℝ) (ν : Measure ℝ) (constant : ℝ) (scale : ℕ → ℝ) (n : ℕ)
    (hpos : 0 < stableBlockLength α ν constant scale n) :
    stableBlockCount α ν constant scale n *
          stableBlockLength α ν constant scale n ≤ n ∧
      n < (stableBlockCount α ν constant scale n + 1) *
          stableBlockLength α ν constant scale n := by
  simpa [stableBlockCount, Asymptotics.blockCount] using
    Asymptotics.blockCount_mul_blockLength_le_lt_succ
      (fun n => stableBlockLength α ν constant scale n) n hpos

/-- The complete blocks cover all but at most one block length: the total
covered by the block count is above `n` minus one block length. Together with
`stableBlockCount_mul_stableBlockLength_le`, this brackets the covered steps
inside the last block, which is the form used by the partition argument. -/
theorem sub_stableBlockLength_lt_stableBlockCount_mul_stableBlockLength
    (α : ℝ) (ν : Measure ℝ) (constant : ℝ) (scale : ℕ → ℝ) (n : ℕ)
    (hpos : 0 < stableBlockLength α ν constant scale n) :
    (n : ℝ) - stableBlockLength α ν constant scale n <
      (stableBlockCount α ν constant scale n : ℝ) *
        stableBlockLength α ν constant scale n := by
  simpa [stableBlockCount, Asymptotics.blockCount] using
    Asymptotics.sub_blockLength_lt_blockCount_mul_blockLength
      (fun n => stableBlockLength α ν constant scale n) n hpos


/-- The block count and the block length bracket `n` in relative terms: for a positive
block length `L`, `|count * L / n - 1| ≤ L / n`. This is the cast form of
`stableBlockCount_mul_stableBlockLength_le_lt_succ`, so it is the form in which the block
count is asymptotic to `n / L`: it converges to `1` as soon as `L / n` converges to `0`. -/
theorem stableBlockCount_mul_stableBlockLength_div_sub_one_abs_le
    (α : ℝ) (ν : Measure ℝ) (constant : ℝ) (scale : ℕ → ℝ) (n : ℕ)
    (hpos : 0 < stableBlockLength α ν constant scale n) (hn : 0 < n) :
    |((stableBlockCount α ν constant scale n *
        stableBlockLength α ν constant scale n : ℕ) : ℝ) / n - 1| ≤
      (stableBlockLength α ν constant scale n : ℝ) / n := by
  simpa [stableBlockCount, Asymptotics.blockCount] using
    Asymptotics.blockCount_mul_blockLength_div_sub_one_abs_le
      (fun n => stableBlockLength α ν constant scale n) n hpos hn

/-- The block count is asymptotic to `n` divided by the block length: once the block length is
`o(n)`, the complete blocks fill the `n` steps up to a vanishing fraction. This is the form of the
block asymptotics that the rate statement of the theorem consumes. -/
theorem tendsto_stableBlockCount_mul_stableBlockLength_div_nat
    {α : ℝ} {ν : Measure ℝ} {constant : ℝ} {scale : ℕ → ℝ}
    (hpos : ∀ᶠ n in atTop, 0 < stableBlockLength α ν constant scale n)
    (hscale : Tendsto (fun n => (stableBlockLength α ν constant scale n : ℝ) / n)
      atTop (nhds 0)) :
    Tendsto (fun n => ((stableBlockCount α ν constant scale n *
        stableBlockLength α ν constant scale n : ℕ) : ℝ) / n) atTop (nhds 1) := by
  simpa [stableBlockCount, Asymptotics.blockCount] using
    Asymptotics.tendsto_blockCount_mul_blockLength_div_nat
      (blockLength := fun n => stableBlockLength α ν constant scale n) hpos hscale

/-- If the stable time scale is negligible relative to the full horizon, the
number of full blocks satisfies the source's fourth block relation:
`B*(aₙ) / n * ⌊n / mₙ⌋ → 1 / constant`, where
`mₙ = ⌊constant · B*(aₙ)⌋₊`.  This is pure scale and floor arithmetic; it does
not assume the missing regular-variation relation `B(mₙ) / aₙ →
constant^(1/α)`. -/
theorem tendsto_stableScaleTime_div_nat_mul_stableBlockCount
    {α : ℝ} {ν : Measure ℝ} {constant K : ℝ} {scale : ℕ → ℝ}
    (hα : 0 < α) (hconstant : 0 < constant) (hK : 0 < K)
    (hscale : Tendsto scale atTop atTop)
    (hvariation : ∀ᶠ n in atTop,
      0 < stableSlowVariation α ν (scale n) ∧ stableSlowVariation α ν (scale n) ≤ K)
    (hrate : Tendsto (stableSmallDeviationRate α ν scale) atTop (nhds 0)) :
    Tendsto (fun n => stableScaleTime α ν (scale n) / (n : ℝ) *
      (stableBlockCount α ν constant scale n : ℝ)) atTop (nhds constant⁻¹) := by
  have hlengthPos := eventually_stableBlockLength_pos
    hα hconstant hK hscale hvariation
  have hlengthRate := tendsto_stableBlockLength_div_nat_zero
    hα hconstant hK hscale hvariation hrate
  have hcountProduct := tendsto_stableBlockCount_mul_stableBlockLength_div_nat
    hlengthPos hlengthRate
  have hlengthScale := tendsto_stableBlockLength_div_stableScaleTime
    hα hconstant hK hscale hvariation
  have hscaleTimePos : ∀ᶠ n in atTop,
      0 < stableScaleTime α ν (scale n) := by
    filter_upwards [hscale.eventually (eventually_gt_atTop 0), hvariation]
      with n hscalePos hvar
    exact div_pos (Real.rpow_pos_of_pos hscalePos α) hvar.1
  have hinverse := hlengthScale.inv₀ hconstant.ne'
  have hscaleOverLength : Tendsto
      (fun n => stableScaleTime α ν (scale n) /
        (stableBlockLength α ν constant scale n : ℝ))
      atTop (nhds constant⁻¹) := by
    apply hinverse.congr'
    filter_upwards [hscaleTimePos, hlengthPos] with n htime hlength
    have htimeNe : stableScaleTime α ν (scale n) ≠ 0 := htime.ne'
    have hlengthNe : (stableBlockLength α ν constant scale n : ℝ) ≠ 0 := by
      exact_mod_cast hlength.ne'
    field_simp [htimeNe, hlengthNe]
  have hproduct := hscaleOverLength.mul hcountProduct
  have heq : (fun n => stableScaleTime α ν (scale n) / (n : ℝ) *
      (stableBlockCount α ν constant scale n : ℝ)) =ᶠ[atTop]
      fun n => stableScaleTime α ν (scale n) /
        (stableBlockLength α ν constant scale n : ℝ) *
          (((stableBlockCount α ν constant scale n *
            stableBlockLength α ν constant scale n : ℕ) : ℝ) / (n : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), hlengthPos] with n hn hlength
    have hnNe : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hlengthNe : (stableBlockLength α ν constant scale n : ℝ) ≠ 0 := by
      exact_mod_cast hlength.ne'
    change stableScaleTime α ν (scale n) / (n : ℝ) *
        (stableBlockCount α ν constant scale n : ℝ) =
      stableScaleTime α ν (scale n) /
        (stableBlockLength α ν constant scale n : ℝ) *
          (((stableBlockCount α ν constant scale n *
            stableBlockLength α ν constant scale n : ℕ) : ℝ) / (n : ℝ))
    push_cast
    field_simp [hnNe, hlengthNe]
  have hres := hproduct.congr' heq.symm
  simpa using hres

/-- The block-count scale relation follows from the paper's two-scale
condition once `L*` is known to converge to a positive finite limit.  This
packages the rate and boundedness consequences without adding them as separate
assumptions. -/
theorem tendsto_stableScaleTime_div_nat_mul_stableBlockCount_of_slowVariation_limit
    {α ell : ℝ} {ν : Measure ℝ} {normalization scale : ℕ → ℝ}
    {constant : ℝ}
    (hα : 0 < α) (hconstant : 0 < constant) (hell : 0 < ell)
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hslow : Tendsto (stableSlowVariation α ν) atTop (nhds ell)) :
    Tendsto (fun n => stableScaleTime α ν (scale n) / (n : ℝ) *
      (stableBlockCount α ν constant scale n : ℝ)) atTop (nhds constant⁻¹) := by
  have hwindow : ∀ᶠ u in atTop,
      0 < stableSlowVariation α ν u ∧ stableSlowVariation α ν u ≤ ell + 1 := by
    have hmem : Set.Ioo (ell / 2) (ell + 1) ∈ nhds ell := by
      exact isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
    filter_upwards [hslow.eventually hmem]
      with u hu
    exact ⟨by linarith, by linarith⟩
  have hvariation : ∀ᶠ n in atTop,
      0 < stableSlowVariation α ν (scale n) ∧
        stableSlowVariation α ν (scale n) ≤ ell + 1 :=
    (_root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsStableMogulskiiScale.scale_tendsto_atTop hscale).eventually hwindow
  have hrate := IsStableMogulskiiScale.tendsto_stableSmallDeviationRate_zero_of_slowVariation_limit
    hα hell hscale hslow
  exact tendsto_stableScaleTime_div_nat_mul_stableBlockCount
    hα hconstant (by linarith : 0 < ell + 1)
    (_root_.ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsStableMogulskiiScale.scale_tendsto_atTop hscale) hvariation hrate

/-- The stable block count has the expected asymptotic under slow variation
alone. In particular, no boundedness assumption is imposed on `L*` along the
small-deviation scale. -/
theorem tendsto_stableScaleTime_div_nat_mul_stableBlockCount_of_slowVariation
    {α : ℝ} {ν : Measure ℝ} [IsFiniteMeasure ν]
    {normalization scale : ℕ → ℝ} {constant : ℝ}
    (hα : 0 < α) (hα₂ : α ≤ 2) (hconstant : 0 < constant)
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop (stableSlowVariation α ν))
    (hrate : Tendsto (stableSmallDeviationRate α ν scale) atTop (nhds 0)) :
    Tendsto (fun n => stableScaleTime α ν (scale n) / (n : ℝ) *
      (stableBlockCount α ν constant scale n : ℝ))
      atTop (nhds constant⁻¹) := by
  have hscaleTop := hscale.scale_tendsto_atTop
  have hlengthPos := eventually_stableBlockLength_pos_of_slowVariation
    hα hα₂ hslow hconstant hscaleTop
  have hlengthRate := tendsto_stableBlockLength_div_nat_zero_of_slowVariation
    hα hα₂ hslow hconstant hscaleTop hrate
  have hcountProduct := tendsto_stableBlockCount_mul_stableBlockLength_div_nat
    hlengthPos hlengthRate
  have hlengthScale := tendsto_stableBlockLength_div_stableScaleTime_of_slowVariation
    hα hα₂ hslow hconstant hscaleTop
  have hscaleTimePos : ∀ᶠ n in atTop,
      0 < stableScaleTime α ν (scale n) := by
    have htop := stableScaleTime_tendsto_atTop_of_stableSlowVariation
      hα hα₂ hslow
    exact (htop.comp hscaleTop).eventually (eventually_gt_atTop 0)
  have hinverse := hlengthScale.inv₀ hconstant.ne'
  have hscaleOverLength : Tendsto
      (fun n => stableScaleTime α ν (scale n) /
        (stableBlockLength α ν constant scale n : ℝ))
      atTop (nhds constant⁻¹) := by
    apply hinverse.congr'
    filter_upwards [hscaleTimePos, hlengthPos] with n htime hlength
    have htimeNe : stableScaleTime α ν (scale n) ≠ 0 := htime.ne'
    have hlengthNe : (stableBlockLength α ν constant scale n : ℝ) ≠ 0 := by
      exact_mod_cast hlength.ne'
    field_simp [htimeNe, hlengthNe]
  have hproduct := hscaleOverLength.mul hcountProduct
  have heq : (fun n => stableScaleTime α ν (scale n) / (n : ℝ) *
      (stableBlockCount α ν constant scale n : ℝ)) =ᶠ[atTop]
      fun n => stableScaleTime α ν (scale n) /
        (stableBlockLength α ν constant scale n : ℝ) *
          (((stableBlockCount α ν constant scale n *
            stableBlockLength α ν constant scale n : ℕ) : ℝ) / (n : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), hlengthPos] with n hn hlength
    have hnNe : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have hlengthNe : (stableBlockLength α ν constant scale n : ℝ) ≠ 0 := by
      exact_mod_cast hlength.ne'
    change stableScaleTime α ν (scale n) / (n : ℝ) *
        (stableBlockCount α ν constant scale n : ℝ) =
      stableScaleTime α ν (scale n) /
        (stableBlockLength α ν constant scale n : ℝ) *
          (((stableBlockCount α ν constant scale n *
            stableBlockLength α ν constant scale n : ℕ) : ℝ) / (n : ℝ))
    push_cast
    field_simp [hnNe, hlengthNe]
  simpa using hproduct.congr' heq.symm

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
