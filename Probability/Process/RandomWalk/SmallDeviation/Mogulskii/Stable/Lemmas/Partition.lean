/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Corridor
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Scale.Rate

/-!
# Block counts at the stable small-deviation scale

Write $b_n$ for `stableBlockLength α ν constant scale n`, $q_n$ for its
complete-block count, $T_n$ for `stableScaleTime α ν (scale n)`, and $r_n$
for `stableSmallDeviationRate α ν scale n`. The complete-block count
$q_n=n\mathbin{/}b_n$ is defined beside the stable block length in
`Stable/Scale/Core.lean`. This module proves its stable-scale asymptotics and
the corresponding segment and endpoint-core count limits:

- `tendsto_stableScaleTime_div_nat_mul_stableBlockCount`,
  `tendsto_stableScaleTime_div_nat_mul_stableBlockCount_of_slowVariation_limit`,
  and `tendsto_stableScaleTime_div_nat_mul_stableBlockCount_of_slowVariation`:
  $T_nq_n/n\to1/\operatorname{constant}$ under their respective stable
  scale and slow-variation hypotheses.
- `tendsto_stableScaleTime_div_nat_mul_segmentBlockCount`:
  a segment of relative duration $\tau$ has block cost
  $r_n\lfloor\operatorname{length}_n/b_n\rfloor\to\tau/\operatorname{constant}$;
  the horizon may be any sequence whose proportion of the full time tends to
  $\tau$.
- `tendsto_stableSmallDeviationRate_mul_balancedCoreBridgeCount`:
  reserving one bridge block in a core of relative duration $\tau$ gives
  cost $r_n(q_n^{\mathrm{core}}+1)\to\tau/\operatorname{amplitude}^{\alpha}$.

These are the block-length relations in Mogul'skii, *Small Deviations in a
Space of Trajectories*, Theorem 3, Section 4. The path-event partition
comparison is scale-free and lives in
`Probability/Process/RandomWalk/Path/Block/Partition/Basic.lean` and
`Probability/Process/RandomWalk/Path/Block/Partition/Normalized.lean`.
These stable-scale consequences are internal proof interfaces for Mogul'skii's
theorem; reusable quotient/remainder arithmetic and diagonal selection are
owned by `Analysis/Asymptotics/Scale/BlockScale.lean` and
`Analysis/Asymptotics/Scale/SlowDiagonal.lean`.


The original bibliography is A. A. Mogul'skii, “Small deviations in the sample function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765; English translation, “Small Deviations in a Space of Trajectories,” *Theory of Probability and Its Applications* 19(4) (1975), 726--736, DOI 10.1137/1119081. -/

@[expose] public section

open Filter MeasureTheory

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- If the stable time scale is negligible relative to the full horizon, the
number of full blocks satisfies the source's fourth block relation:
`B*(aₙ) / n * ⌊n / mₙ⌋ → 1 / constant`, where
`mₙ = ⌊constant · B*(aₙ)⌋₊`.  This is pure scale and floor arithmetic; it does
not assume the missing regular-variation relation `B(mₙ) / aₙ →
constant^(1/α)`. -/
lemma tendsto_stableScaleTime_div_nat_mul_stableBlockCount
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
  have hhorizon : Tendsto (fun n : ℕ => (n : ℝ) / (n : ℝ))
      atTop (nhds 1) := by
    have heq : (fun n : ℕ => (n : ℝ) / (n : ℝ)) =ᶠ[atTop]
        fun _ => (1 : ℝ) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      exact div_self (by exact_mod_cast hn.ne')
    exact (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).congr' heq.symm
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
  simpa [stableBlockCount] using
    Asymptotics.tendsto_div_nat_mul_quotientBlockCount
      (horizon := fun n : ℕ => n) hhorizon hlengthPos hlengthRate hscaleOverLength

/-- The block-count scale relation follows from the two-scale hypothesis in
Mogul'skii, *Small Deviations in a Space of Trajectories*, Theorem 3,
Section 4, once `L*` is known to converge to a positive finite limit. This
packages the rate and boundedness consequences without adding them as separate
assumptions. -/
lemma tendsto_stableScaleTime_div_nat_mul_stableBlockCount_of_slowVariation_limit
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
lemma tendsto_stableScaleTime_div_nat_mul_stableBlockCount_of_slowVariation
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
  have hhorizon : Tendsto (fun n : ℕ => (n : ℝ) / (n : ℝ))
      atTop (nhds 1) := by
    have heq : (fun n : ℕ => (n : ℝ) / (n : ℝ)) =ᶠ[atTop]
        fun _ => (1 : ℝ) := by
      filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
      exact div_self (by exact_mod_cast hn.ne')
    exact (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).congr' heq.symm
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
  simpa [stableBlockCount] using
    Asymptotics.tendsto_div_nat_mul_quotientBlockCount
      (horizon := fun n : ℕ => n) hhorizon hlengthPos hlengthRate hscaleOverLength

/-- A fixed macroscopic subinterval of relative length `τ` contains the
asymptotic cost `τ / constant` in stable blocks. The block length is chosen
from the common small-deviation scale at the full horizon; only the horizon
of the subinterval varies. This is the block-count input for each cell of a
finite step-corridor partition. -/
lemma tendsto_stableScaleTime_div_nat_mul_segmentBlockCount
    {α τ : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization scale : ℕ → ℝ} {constant : ℝ}
    {horizon : ℕ → ℕ}
    (hα : 0 < α) (hα₂ : α ≤ 2) (hconstant : 0 < constant)
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop (stableSlowVariation α ν))
    (hhorizon : Tendsto (fun n => (horizon n : ℝ) / n)
      atTop (nhds τ)) :
    Tendsto (fun n => stableSmallDeviationRate α ν scale n *
      ((horizon n / stableBlockLength α ν constant scale n : ℕ) : ℝ))
      atTop (nhds (τ / constant)) := by
  let blockLength : ℕ → ℕ := stableBlockLength α ν constant scale
  have hscaleTop := hscale.scale_tendsto_atTop
  have hrate := tendsto_stableSmallDeviationRate_zero_of_slowVariation
    hscale.stableNorming hscaleTop hscale.scale_div_normalization_tendsto_zero
    hα hα₂ hslow
  have hblockPos : ∀ᶠ n in atTop, 0 < blockLength n := by
    simpa [blockLength] using eventually_stableBlockLength_pos_of_slowVariation
      hα hα₂ hslow hconstant hscaleTop
  have hblockOverN : Tendsto (fun n => (blockLength n : ℝ) / n)
      atTop (nhds 0) := by
    simpa [blockLength] using tendsto_stableBlockLength_div_nat_zero_of_slowVariation
      hα hα₂ hslow hconstant hscaleTop hrate
  have hlengthScale : Tendsto (fun n => (blockLength n : ℝ) /
      stableScaleTime α ν (scale n)) atTop (nhds constant) := by
    simpa [blockLength] using tendsto_stableBlockLength_div_stableScaleTime_of_slowVariation
      hα hα₂ hslow hconstant hscaleTop
  have hκPos : ∀ᶠ n in atTop, 0 < stableScaleTime α ν (scale n) := by
    have hκTop := stableScaleTime_tendsto_atTop_of_stableSlowVariation
      hα hα₂ hslow
    exact (hκTop.comp hscaleTop).eventually (eventually_gt_atTop 0)
  have hκOverLength : Tendsto
      (fun n => stableScaleTime α ν (scale n) / (blockLength n : ℝ))
      atTop (nhds constant⁻¹) := by
    have hinv := hlengthScale.inv₀ hconstant.ne'
    apply hinv.congr'
    filter_upwards [hκPos, hblockPos] with n hκ hlength
    have hκne : stableScaleTime α ν (scale n) ≠ 0 := hκ.ne'
    have hlengthNe : (blockLength n : ℝ) ≠ 0 := by
      exact_mod_cast hlength.ne'
    field_simp [hκne, hlengthNe]
  have hrateEq : stableSmallDeviationRate α ν scale =ᶠ[atTop]
      fun n => stableScaleTime α ν (scale n) / (n : ℝ) := by
    have hslowPos : ∀ᶠ n in atTop, 0 < stableSlowVariation α ν (scale n) :=
      hscaleTop.eventually hslow.eventually_pos
    filter_upwards [eventually_gt_atTop (0 : ℕ), hslowPos] with n hn hL
    have hnNe : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [stableSmallDeviationRate, stableScaleTime]
    field_simp [hnNe, hL.ne']
  have hscaledCount := Asymptotics.tendsto_div_nat_mul_quotientBlockCount
    hhorizon hblockPos hblockOverN hκOverLength
  have heq : (fun n => stableSmallDeviationRate α ν scale n *
      ((horizon n / blockLength n : ℕ) : ℝ)) =ᶠ[atTop]
      fun n => stableScaleTime α ν (scale n) / (n : ℝ) *
        ((horizon n / blockLength n : ℕ) : ℝ) := by
    filter_upwards [hrateEq] with n hrateN
    rw [hrateN]
  have hlimit := hscaledCount.congr' heq.symm
  convert hlimit using 1
  field_simp [hconstant.ne']

/-- A balanced endpoint-core construction uses the quotient count on the
remaining horizon after reserving one stable block for the final bridge. The
extra bridge block is asymptotically negligible, so the normalized count is
still the cell duration divided by the stable block parameter. -/
lemma tendsto_stableSmallDeviationRate_mul_balancedCoreBridgeCount
    {α duration amplitude : ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {normalization scale : ℕ → ℝ}
    (hα : 0 < α) (hα₂ : α ≤ 2) (hamplitude : 0 < amplitude)
    (hscale : IsStableMogulskiiScale α ν normalization scale)
    (hslow : Asymptotics.IsSlowlyVaryingAtTop (stableSlowVariation α ν))
    (hduration : 0 < duration)
    (total : ℕ → ℕ)
    (htotal : Tendsto (fun n => (total n : ℝ) / (n : ℝ))
      atTop (nhds duration)) :
    Tendsto
      (fun n => stableSmallDeviationRate α ν scale n *
        (((Asymptotics.balancedBlockCount
          (total n - stableBlockLength α ν (amplitude ^ α) scale n)
          (stableBlockLength α ν (amplitude ^ α) scale n) + 1 : ℕ) : ℝ)))
      atTop (nhds (duration / amplitude ^ α)) := by
  let reference : ℕ → ℕ := fun n =>
    stableBlockLength α ν (amplitude ^ α) scale n
  let mainLength : ℕ → ℕ := fun n => total n - reference n
  have hscaleTop : Tendsto scale atTop atTop := hscale.scale_tendsto_atTop
  have hrate : Tendsto (stableSmallDeviationRate α ν scale) atTop (nhds 0) :=
    tendsto_stableSmallDeviationRate_zero_of_slowVariation
      hscale.stableNorming hscaleTop hscale.scale_div_normalization_tendsto_zero
      hα hα₂ hslow
  have hreferenceTop : Tendsto reference atTop atTop := by
    simpa [reference] using tendsto_stableBlockLength_atTop_of_slowVariation
      hα hα₂ hslow (Real.rpow_pos_of_pos hamplitude α) hscaleTop
  have hreferencePos : ∀ᶠ n : ℕ in atTop, 0 < reference n :=
    hreferenceTop.eventually (eventually_gt_atTop 0)
  have hreferenceOverN : Tendsto (fun n => (reference n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
    simpa [reference] using tendsto_stableBlockLength_div_nat_zero_of_slowVariation
      hα hα₂ hslow (Real.rpow_pos_of_pos hamplitude α) hscaleTop hrate
  have hreferenceLe : ∀ᶠ n : ℕ in atTop, reference n ≤ total n :=
    Asymptotics.eventually_block_le_horizon_of_positive_density
      htotal hreferenceOverN hduration
  have hmainDuration : Tendsto (fun n => (mainLength n : ℝ) / (n : ℝ))
      atTop (nhds duration) := by
    have hsub := htotal.sub hreferenceOverN
    have heq : (fun n => (mainLength n : ℝ) / (n : ℝ)) =ᶠ[atTop]
        fun n => (total n : ℝ) / (n : ℝ) - (reference n : ℝ) / (n : ℝ) := by
      filter_upwards [hreferenceLe] with n hn
      change ((total n - reference n : ℕ) : ℝ) / (n : ℝ) = _
      rw [Nat.cast_sub hn, sub_div]
    simpa using hsub.congr' heq.symm
  have hcountCovered := Asymptotics.tendsto_quotientBlockCount_mul_blockLength_div_nat
    hmainDuration hreferenceOverN hreferencePos
  have hreferenceOverScaleTime : Tendsto
      (fun n => (reference n : ℝ) / stableScaleTime α ν (scale n))
      atTop (nhds (amplitude ^ α)) := by
    simpa [reference] using tendsto_stableBlockLength_div_stableScaleTime_of_slowVariation
      hα hα₂ hslow (Real.rpow_pos_of_pos hamplitude α) hscaleTop
  have hscaleTimePos : ∀ᶠ n : ℕ in atTop,
      0 < stableScaleTime α ν (scale n) := by
    have hκTop :=
      (stableScaleTime_tendsto_atTop_of_stableSlowVariation hα hα₂ hslow).comp hscaleTop
    exact hκTop.eventually (eventually_gt_atTop 0)
  have hscaleTimeOverReference : Tendsto
      (fun n => stableScaleTime α ν (scale n) / (reference n : ℝ))
      atTop (nhds (amplitude ^ α)⁻¹) := by
    have hinv := hreferenceOverScaleTime.inv₀ (Real.rpow_pos_of_pos hamplitude α).ne'
    apply hinv.congr'
    filter_upwards [hscaleTimePos, hreferencePos] with n hκ href
    have hκne : stableScaleTime α ν (scale n) ≠ 0 := hκ.ne'
    have hrefNe : (reference n : ℝ) ≠ 0 := by exact_mod_cast href.ne'
    field_simp [hκne, hrefNe]
  have hcoveredFactor : Tendsto
      (fun n =>
        ((Asymptotics.balancedBlockCount (mainLength n) (reference n) *
          reference n : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds duration) := by
    simpa [Asymptotics.balancedBlockCount, Asymptotics.blockCount] using hcountCovered
  have hmainCount : Tendsto
      (fun n => stableSmallDeviationRate α ν scale n *
        (Asymptotics.balancedBlockCount (mainLength n) (reference n) : ℝ))
      atTop (nhds (duration / amplitude ^ α)) := by
    have hmul := hscaleTimeOverReference.mul hcoveredFactor
    have hrateEq : stableSmallDeviationRate α ν scale =ᶠ[atTop]
        fun n => stableScaleTime α ν (scale n) / (n : ℝ) := by
      have hslowPos : ∀ᶠ n in atTop, 0 < stableSlowVariation α ν (scale n) :=
        hscaleTop.eventually hslow.eventually_pos
      filter_upwards [eventually_gt_atTop (0 : ℕ), hslowPos] with n hn hL
      have hnNe : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      rw [stableSmallDeviationRate, stableScaleTime]
      field_simp [hnNe, hL.ne']
    have heq : (fun n => stableSmallDeviationRate α ν scale n *
        (Asymptotics.balancedBlockCount (mainLength n) (reference n) : ℝ)) =ᶠ[atTop]
        fun n => (stableScaleTime α ν (scale n) / (reference n : ℝ)) *
          ((((Asymptotics.balancedBlockCount (mainLength n) (reference n) *
            reference n : ℕ) : ℝ) / (n : ℝ))) := by
      filter_upwards [hrateEq, hreferencePos, hscaleTimePos,
        eventually_gt_atTop (0 : ℕ)] with n hrateN href hκ hn
      have hrefNe : (reference n : ℝ) ≠ 0 := by exact_mod_cast href.ne'
      have hκNe : stableScaleTime α ν (scale n) ≠ 0 := hκ.ne'
      have hnNe : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      rw [hrateN]
      push_cast
      field_simp [hrefNe, hκNe, hnNe]
    have hmain := hmul.congr' heq.symm
    simpa [div_eq_mul_inv, mul_comm] using hmain
  have hbridgeCount : Tendsto
      (fun n => stableSmallDeviationRate α ν scale n *
        (((Asymptotics.balancedBlockCount (mainLength n) (reference n) + 1 : ℕ) : ℝ)))
      atTop (nhds (duration / amplitude ^ α)) := by
    have hsum := hmainCount.add hrate
    have heq : (fun n => stableSmallDeviationRate α ν scale n *
        (((Asymptotics.balancedBlockCount (mainLength n) (reference n) + 1 : ℕ) : ℝ))) =ᶠ[atTop]
        fun n => stableSmallDeviationRate α ν scale n *
          (Asymptotics.balancedBlockCount (mainLength n) (reference n) : ℝ) +
          stableSmallDeviationRate α ν scale n := by
      filter_upwards [] with n
      push_cast
      ring
    convert hsum.congr' heq.symm using 1
    ring_nf
  simpa [mainLength, reference] using hbridgeCount

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
