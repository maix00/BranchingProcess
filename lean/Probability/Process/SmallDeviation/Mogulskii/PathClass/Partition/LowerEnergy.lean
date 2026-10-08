/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

import Probability.Process.SmallDeviation.Mogulskii.PathClass.Partition.LowerApproximation

/-!
# The stable-process lower rate converges to corridor energy

Finite inner corridors approximate every finite-width partition cell from
inside. Cells with an infinite boundary trace admit inner widths tending to
infinity, so their contribution to the rate tends to zero. This identifies
the finite-partition lower rate with the `Hα` energy.
-/

open Filter
open MeasureTheory
open scoped NNReal Topology

namespace ProbabilityTheory.Process.SmallDeviation.Mogulskii

/-- A finite inner width for each cell of a step corridor. Finite widths
increase to the full corridor width; infinite-width cells increase without
bound. -/
noncomputable def commonPartitionApproxWidth (upper lower : StepBoundary)
    (n : ℕ) (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) : ℝ :=
  if upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) = ⊤ ∨
      lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) = ⊥ then
    (n : ℝ) + 1
  else
    ((upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)).toReal -
      (lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)).toReal) *
        (1 - 1 / ((n : ℝ) + 2))

/-- Trace separation implies strict separation of the outgoing traces on every
common partition cell. -/
theorem rightTrace_lt_of_traceSeparated (upper lower : StepBoundary)
    (hsep : TraceSeparated upper lower) (t : unitInterval) :
    lower.rightTrace t < upper.rightTrace t := by
  exact lt_of_le_of_lt (le_max_right _ _)
    (lt_of_lt_of_le (hsep t) (min_le_right _ _))

private theorem commonPartitionTraceWidth_pos (upper lower : StepBoundary)
    (hsep : TraceSeparated upper lower)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1))
    (hinf : ¬ (upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) = ⊤ ∨
      lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) = ⊥)) :
    0 < (upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)).toReal -
      (lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)).toReal := by
  let U := upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)
  let L := lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)
  have htrace : L < U := rightTrace_lt_of_traceSeparated upper lower hsep _
  have hLbot : L ≠ ⊥ := by
    intro h
    exact hinf (Or.inr (by simpa [L] using h))
  have hLtop : L ≠ ⊤ := by
    intro h
    rw [h] at htrace
    exact (not_lt_of_ge le_top) htrace
  have hUbot : U ≠ ⊥ := by
    intro h
    rw [h] at htrace
    exact (not_lt_of_ge bot_le) htrace
  have hUtop : U ≠ ⊤ := by
    intro h
    exact hinf (Or.inl (by simpa [U] using h))
  have hLcoe : (L.toReal : EReal) = L := EReal.coe_toReal hLtop hLbot
  have hUcoe : (U.toReal : EReal) = U := EReal.coe_toReal hUtop hUbot
  have hreal : L.toReal < U.toReal := by
    apply EReal.coe_lt_coe_iff.mp
    rw [hLcoe, hUcoe]
    exact htrace
  dsimp [U, L] at hreal ⊢
  exact sub_pos.mpr hreal

theorem commonPartitionApproxWidth_pos (upper lower : StepBoundary)
    (hsep : TraceSeparated upper lower) (n : ℕ)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) :
    0 < commonPartitionApproxWidth upper lower n i := by
  by_cases hinf : upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) = ⊤ ∨
      lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) = ⊥
  · rw [commonPartitionApproxWidth, ite_eq_left hinf]
    positivity
  · have hwidth := commonPartitionTraceWidth_pos upper lower hsep i hinf
    have hn : 1 < (n : ℝ) + 2 := by
      have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
      linarith
    have hfactor : 0 < 1 - 1 / ((n : ℝ) + 2) := by
      have hrec : 1 / ((n : ℝ) + 2) < 1 := by
        rw [one_div]
        exact inv_lt_one_of_one_lt₀ hn
      linarith
    rw [commonPartitionApproxWidth, ite_eq_right hinf]
    exact mul_pos hwidth hfactor

theorem commonPartitionApproxWidth_lt_traceWidth (upper lower : StepBoundary)
    (hsep : TraceSeparated upper lower) (n : ℕ)
    (i : Fin ((StepBoundary.commonKnots upper lower).card - 1)) :
    lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) = ⊥ ∨
      upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) = ⊤ ∨
      commonPartitionApproxWidth upper lower n i <
        (upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)).toReal -
          (lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)).toReal := by
  by_cases hinf : upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) = ⊤ ∨
      lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) = ⊥
  · rcases hinf with hU | hL
    · exact Or.inr (Or.inl hU)
    · exact Or.inl hL
  · have hwidth := commonPartitionTraceWidth_pos upper lower hsep i hinf
    have hn : 1 < (n : ℝ) + 2 := by
      have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
      linarith
    have hfactor_pos : 0 < 1 - 1 / ((n : ℝ) + 2) := by
      have hrec : 1 / ((n : ℝ) + 2) < 1 := by
        rw [one_div]
        exact inv_lt_one_of_one_lt₀ hn
      linarith
    have hfactor_lt : 1 - 1 / ((n : ℝ) + 2) < 1 := by
      have hrec : 0 < 1 / ((n : ℝ) + 2) := div_pos one_pos (by positivity)
      linarith
    have hlt :
        ((upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)).toReal -
          (lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)).toReal) *
            (1 - 1 / ((n : ℝ) + 2)) <
          (upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)).toReal -
            (lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)).toReal :=
      by
        simpa only [mul_one] using mul_lt_mul_of_pos_left hfactor_lt hwidth
    right
    right
    rw [commonPartitionApproxWidth, ite_eq_right hinf]
    exact hlt

private theorem tendsto_commonPartitionApproxWidth_finite
    (upper lower : StepBoundary) (i : Fin ((StepBoundary.commonKnots upper lower).card - 1))
    (hinf : ¬ (upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) = ⊤ ∨
      lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) = ⊥)) :
    Tendsto (fun n : ℕ => commonPartitionApproxWidth upper lower n i) atTop
      (𝓝 ((upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)).toReal -
        (lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)).toReal)) := by
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hden
  have hfactor : Tendsto (fun n : ℕ => 1 - ((n : ℝ) + 2)⁻¹) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hinv
  have hwidth : Tendsto (fun n : ℕ =>
      ((upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)).toReal -
        (lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)).toReal) *
      (1 - ((n : ℝ) + 2)⁻¹)) atTop
      (𝓝 ((upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)).toReal -
        (lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val)).toReal)) := by
    simpa using (tendsto_const_nhds.mul hfactor)
  refine hwidth.congr' ?_
  filter_upwards [] with n
  rw [commonPartitionApproxWidth, ite_eq_right hinf]
  simp [one_div]

private theorem tendsto_commonPartitionApproxWidth_infinite
    (upper lower : StepBoundary) (i : Fin ((StepBoundary.commonKnots upper lower).card - 1))
    (hinf : upper.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) = ⊤ ∨
      lower.rightTrace (StepBoundary.commonPartitionGrid upper lower i.val) = ⊥) :
    Tendsto (fun n : ℕ => commonPartitionApproxWidth upper lower n i) atTop atTop := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  refine h.congr' ?_
  filter_upwards [] with n
  rw [commonPartitionApproxWidth, ite_eq_left hinf]

/-- The finite-partition lower-rate sum converges to the source coefficient
times the exact `Hα` energy. The factor `2^α` comes from using corridor
half-widths in the unit stable-process escape rate. -/
theorem M2Corridor.tendsto_commonPartitionApproxRate
    (C α : ℝ) (c : M2Corridor)
    (hsep : TraceSeparated c.upper c.lower) (hα : 0 < α) :
    Tendsto
      (fun n : ℕ => ∑ i : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1),
        C * commonPartitionCellLength c.upper c.lower i /
          ((commonPartitionApproxWidth c.upper c.lower n i / 2) ^ α))
      atTop (𝓝 (C * 2 ^ α * (c.energy α).toReal)) := by
  classical
  let rateTerm : ℕ → Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1) → ℝ :=
    fun n i => C * commonPartitionCellLength c.upper c.lower i /
      ((commonPartitionApproxWidth c.upper c.lower n i / 2) ^ α)
  let limitTerm : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1) → ℝ :=
    fun i => C * 2 ^ α *
      (widthCost α
        (c.upper.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val))
        (c.lower.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val))).toReal *
          commonPartitionCellLength c.upper c.lower i
  have hcell (i : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1)) :
      Tendsto (fun n : ℕ => rateTerm n i) atTop (𝓝 (limitTerm i)) := by
    let U := c.upper.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val)
    let L := c.lower.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val)
    let length := commonPartitionCellLength c.upper c.lower i
    by_cases hinf : U = ⊤ ∨ L = ⊥
    · have hwidthAtTop : Tendsto (fun n : ℕ =>
          commonPartitionApproxWidth c.upper c.lower n i) atTop atTop :=
        tendsto_commonPartitionApproxWidth_infinite c.upper c.lower i (by simpa [U, L] using hinf)
      have hhalfAtTop : Tendsto (fun n : ℕ =>
          commonPartitionApproxWidth c.upper c.lower n i / 2) atTop atTop := by
        convert hwidthAtTop.atTop_mul_const (by norm_num : 0 < (2 : ℝ)⁻¹) using 1
        simp [div_eq_mul_inv]
      have hpowAtTop : Tendsto (fun n : ℕ =>
          (commonPartitionApproxWidth c.upper c.lower n i / 2) ^ α) atTop atTop :=
        (tendsto_rpow_atTop hα).comp hhalfAtTop
      have hrate : Tendsto (fun n : ℕ =>
          C * length / ((commonPartitionApproxWidth c.upper c.lower n i / 2) ^ α))
          atTop (𝓝 0) := tendsto_const_nhds.div_atTop hpowAtTop
      have hcost : (widthCost α U L).toReal = 0 := by
        rcases hinf with hU | hL
        · simp [widthCost, hU]
        · simp [widthCost, hL]
      change Tendsto (fun n : ℕ => C * length /
        ((commonPartitionApproxWidth c.upper c.lower n i / 2) ^ α)) atTop
        (𝓝 (C * 2 ^ α * (widthCost α U L).toReal * length))
      rw [hcost]
      simpa [length] using hrate
    · have hgap : 0 < U.toReal - L.toReal := by
        exact commonPartitionTraceWidth_pos c.upper c.lower hsep i
          (by simpa [U, L] using hinf)
      have hwidth : Tendsto (fun n : ℕ => commonPartitionApproxWidth c.upper c.lower n i)
          atTop (𝓝 (U.toReal - L.toReal)) :=
        tendsto_commonPartitionApproxWidth_finite c.upper c.lower i
          (by simpa [U, L] using hinf)
      have hhalf : Tendsto (fun n : ℕ => commonPartitionApproxWidth c.upper c.lower n i / 2)
          atTop (𝓝 ((U.toReal - L.toReal) / 2)) := by
        simpa using hwidth.div_const 2
      have hhalfPos : 0 < (U.toReal - L.toReal) / 2 := by linarith
      have hpow : Tendsto (fun n : ℕ =>
          (commonPartitionApproxWidth c.upper c.lower n i / 2) ^ α) atTop
          (𝓝 (((U.toReal - L.toReal) / 2) ^ α)) :=
        (Real.continuousAt_rpow_const ((U.toReal - L.toReal) / 2) α
          (Or.inl hhalfPos.ne')).tendsto.comp hhalf
      have hpowPos : 0 < ((U.toReal - L.toReal) / 2) ^ α :=
        Real.rpow_pos_of_pos hhalfPos α
      have hrate : Tendsto (fun n : ℕ =>
          C * length / ((commonPartitionApproxWidth c.upper c.lower n i / 2) ^ α)) atTop
          (𝓝 ((C * length) / (((U.toReal - L.toReal) / 2) ^ α))) :=
        tendsto_const_nhds.div hpow (ne_of_gt hpowPos)
      have hcost : (widthCost α U L).toReal = (U.toReal - L.toReal) ^ (-α) := by
        have hUtop : U ≠ ⊤ := fun h => hinf (Or.inl (by simpa [U] using h))
        have hLbot : L ≠ ⊥ := fun h => hinf (Or.inr (by simpa [L] using h))
        have hLtop : L ≠ ⊤ := by
          intro h
          have htrace : L < U := by
            exact rightTrace_lt_of_traceSeparated c.upper c.lower hsep
              (StepBoundary.commonPartitionGrid c.upper c.lower i.val)
          rw [h] at htrace
          exact (not_lt_of_ge le_top) htrace
        have hUbot : U ≠ ⊥ := by
          intro h
          have htrace : L < U := by
            exact rightTrace_lt_of_traceSeparated c.upper c.lower hsep
              (StepBoundary.commonPartitionGrid c.upper c.lower i.val)
          rw [h] at htrace
          exact (not_lt_of_ge bot_le) htrace
        have hnonneg : 0 ≤ (U.toReal - L.toReal) ^ (-α) :=
          Real.rpow_nonneg hgap.le _
        simp [widthCost, hUtop, hLbot, hgap, hnonneg]
      have hrateLimit :
          (C * length) / (((U.toReal - L.toReal) / 2) ^ α) =
            C * 2 ^ α * (widthCost α U L).toReal * length := by
        have hdiv := Real.div_rpow (le_of_lt hgap) (by norm_num : (0 : ℝ) ≤ 2) α
        rw [hdiv, hcost, Real.rpow_neg hgap.le α]
        field_simp [ne_of_gt (Real.rpow_pos_of_pos hgap α)]
      change Tendsto (fun n : ℕ => C * length /
        ((commonPartitionApproxWidth c.upper c.lower n i / 2) ^ α)) atTop
        (𝓝 (C * 2 ^ α * (widthCost α U L).toReal * length))
      rw [← hrateLimit]
      simpa [length] using hrate
  have hsum : Tendsto (fun n : ℕ => ∑ i, rateTerm n i) atTop
      (𝓝 (∑ i, limitTerm i)) := by
    apply tendsto_finsetSum
    intro i hi
    exact hcell i
  have henergy := c.energy_toReal_eq_commonPartitionCellFinSum α
  have hlimit : (∑ i, limitTerm i) = C * 2 ^ α * (c.energy α).toReal := by
    rw [henergy, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [limitTerm, commonPartitionCellLength]
    ring
  rw [hlimit] at hsum
  simpa [rateTerm] using hsum

/-- Passing the finite inner widths to their limit gives the stable-process
lower bound with the exact corridor energy. This is the `M₂` lower-rate
bridge; it does not assume a finite-valued boundary on any partition cell. -/
theorem HasStableProcessEscapeRate.eventually_scaledCorridorLog_ge_energyRate
    {α C : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hEscape : HasStableProcessEscapeRate α μ P C)
    {Ω : Type*} [MeasurableSpace Ω]
    {X : ℝ≥0 → Ω → ℝ} {Q : Measure Ω} [IsProbabilityMeasure Q]
    (hX : IsStableLevyProcess α μ X Q)
    (hcdf : 0 < cdf μ 0 ∧ cdf μ 0 < 1)
    (c : M2Corridor)
    (hstart : StartAdmissible c.upper c.lower)
    (hsep : TraceSeparated c.upper c.lower)
    (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ scale : ℝ in atTop,
      C * 2 ^ α * (c.energy α).toReal - ε ≤
        scale⁻¹ ^ α * Real.log
          ((P ((Skorokhod.scalePath scale) ⁻¹' corridorSet c.upper c.lower)).toReal) := by
  let rate := fun n : ℕ =>
    ∑ i : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1),
      C * commonPartitionCellLength c.upper c.lower i /
        ((commonPartitionApproxWidth c.upper c.lower n i / 2) ^ α)
  let limit := C * 2 ^ α * (c.energy α).toReal
  have hrate := c.tendsto_commonPartitionApproxRate C α hsep hα
  have hnear : ∀ᶠ n : ℕ in atTop, dist (rate n) limit < ε / 2 := by
    exact hrate.eventually (Metric.ball_mem_nhds limit (by linarith))
  obtain ⟨n, hn⟩ := hnear.exists
  have hrateLower : limit - ε / 2 < rate n := by
    have habs : |rate n - limit| < ε / 2 := by
      simpa [Real.dist_eq] using hn
    rcases abs_lt.mp habs with ⟨hlo, hhi⟩
    linarith
  let target : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1) → ℝ :=
    fun i => commonPartitionApproxWidth c.upper c.lower n i
  have htarget : ∀ i, 0 < target i := by
    intro i
    exact commonPartitionApproxWidth_pos c.upper c.lower hsep n i
  have hwidth : ∀ i : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1),
      c.lower.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val) = ⊥ ∨
      c.upper.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val) = ⊤ ∨
      target i <
        (c.upper.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val)).toReal -
          (c.lower.rightTrace (StepBoundary.commonPartitionGrid c.upper c.lower i.val)).toReal := by
    intro i
    exact commonPartitionApproxWidth_lt_traceWidth c.upper c.lower hsep n i
  have htargetLower :=
    HasStableProcessEscapeRate.eventually_scaledCorridorLog_ge_targetPartitionRate
    hEscape
    hX hcdf c.upper c.lower hstart hsep target htarget hwidth hα
      (ε := ε / 2) (by linarith)
  have hrateLower' : limit - ε / 2 <
      ∑ i : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1),
        C * commonPartitionCellLength c.upper c.lower i /
          ((target i / 2) ^ α) := by
    simpa [rate, target, limit] using hrateLower
  filter_upwards [htargetLower] with scale hscale
  have hscale' :
      (∑ i : Fin ((StepBoundary.commonKnots c.upper c.lower).card - 1),
        C * commonPartitionCellLength c.upper c.lower i /
          ((target i / 2) ^ α)) - ε / 2 ≤
        scale⁻¹ ^ α * Real.log
          ((P ((Skorokhod.scalePath scale) ⁻¹' corridorSet c.upper c.lower)).toReal) := by
    simpa [target] using hscale
  linarith

end ProbabilityTheory.Process.SmallDeviation.Mogulskii
