/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Stable.PathLaw
public import Mathlib.Topology.UnitInterval
public import Topology.Cadlag.Skorokhod.Oscillation
public import Topology.Cadlag.Skorokhod.Endpoint
public import Topology.Cadlag.Skorokhod.SmallDeviation.PathSets

/-!
# Path-space formulation of the stable-process escape rate

This file defines the càdlàg path-space events and specification predicate for
the escape rate. The process-level limits corresponding to Lemma 1 (18)--(20),
including their common finite negative constant, are proved on the original
sample space in `Probability.Process.Stable.SmallDeviation.EscapeRate`. The
bridge from that process result to this path-space packaging remains separate.
The path law on `unitInterval` is a finite-horizon restriction, not a full
Lévy-process object.

The set `J_a` in Lemma 1(I) consists of paths starting at zero whose range
has diameter less than `2 * a`. This is translation invariant in space: the
range need not lie in `(-a, a)`. We encode the strict diameter bound with a
positive uniform margin below `2 * a`; that is an open event in the Skorokhod
`J₁` topology.
-/

open Filter MeasureTheory
open scoped Topology

@[expose] public section

namespace ProbabilityTheory

/-- The strict range-diameter tube of width `2 * a` from Lemma 1(I), encoded
by a positive uniform margin below that diameter. -/
def stableProcessRangeTube (a : ℝ) : Set (CadlagPath unitInterval ℝ) :=
  Skorokhod.oscillationInOpenTube (2 * a)

/-- The path event `a J₁` from Lemma 1(I), including the process's zero
starting value. -/
def stableProcessTube (a : ℝ) : Set (CadlagPath unitInterval ℝ) :=
  Skorokhod.rangeTubeStartingAtZero a

/-- Initial evaluation is continuous in `J₁`, and the range condition is the open Skorokhod corridor. -/
theorem measurableSet_stableProcessTube (a : ℝ) :
    MeasurableSet (stableProcessTube a) := by
  exact Skorokhod.measurableSet_rangeTubeStartingAtZero a

/-- For a process law started at zero almost surely, adding the explicit
starting-value condition to the source's range tube does not change its
probability. -/
theorem measure_stableProcessTube_eq_rangeTube
    {α : ℝ} {μ : Measure ℝ} {P : Measure (CadlagPath unitInterval ℝ)}
    [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw α μ UnitInterval.clock P) (a : ℝ) :
    P (stableProcessTube a) = P (stableProcessRangeTube a) := by
  have heq : stableProcessTube a =ᵐ[P] stableProcessRangeTube a := by
    filter_upwards [hP.ae_start_eq_zero] with f hf
    simp [stableProcessTube, Skorokhod.rangeTubeStartingAtZero,
      stableProcessRangeTube, hf]
  exact measure_congr heq

/-- The paper's constant `C` of Lemma 1 I, stated as the limit of
`a ^ α * log P(stableProcessTube a)` as `a ↓ 0`. -/
def IsStableEscapeRate (α C : ℝ) (tubeProbability : ℝ → ℝ) : Prop :=
  C < 0 ∧
    (∀ᶠ a in 𝓝[>] (0 : ℝ), 0 < tubeProbability a) ∧
    Tendsto (fun a => a ^ α * Real.log (tubeProbability a))
      (𝓝[>] (0 : ℝ)) (𝓝 C)

namespace IsStableEscapeRate

variable {α C : ℝ} {tubeProbability : ℝ → ℝ}

theorem negative (h : IsStableEscapeRate α C tubeProbability) : C < 0 := h.1

theorem eventually_tubeProbability_pos (h : IsStableEscapeRate α C tubeProbability) :
    ∀ᶠ a in 𝓝[>] (0 : ℝ), 0 < tubeProbability a := h.2.1

theorem tendsto (h : IsStableEscapeRate α C tubeProbability) :
    Tendsto (fun a => a ^ α * Real.log (tubeProbability a))
      (𝓝[>] (0 : ℝ)) (𝓝 C) := h.2.2

end IsStableEscapeRate

/-- Lemma 1 I for a stable process path law: the probabilities of its strict range-diameter tubes decay at rate `C`,
that is `a ^ α * log P(stableProcessTube a) → C` as `a ↓ 0`. -/
def HasStableProcessEscapeRate (α : ℝ) (μ : Measure ℝ)
    (P : Measure (CadlagPath unitInterval ℝ)) (C : ℝ) [IsProbabilityMeasure P] : Prop :=
  IsStableClockProcessLaw α μ UnitInterval.clock P ∧
    IsStableEscapeRate α C fun a => (P (stableProcessTube a)).toReal

namespace HasStableProcessEscapeRate

variable {α : ℝ} {μ : Measure ℝ} {P : Measure (CadlagPath unitInterval ℝ)} {C : ℝ}
variable [IsProbabilityMeasure P]

/-- The path law underlying the finite-horizon tube estimate. -/
theorem isStableClockProcessLaw (h : HasStableProcessEscapeRate α μ P C) :
    IsStableClockProcessLaw α μ UnitInterval.clock P := h.1

/-- The defining limit of the escape rate: `a ^ α * log P (ξ (·) ∈ tube a) → C` as `a ↓ 0`. -/
theorem tendsto (h : HasStableProcessEscapeRate α μ P C) :
    Tendsto (fun a => a ^ α * Real.log ((P (stableProcessTube a)).toReal))
      (𝓝[>] (0 : ℝ)) (𝓝 C) := h.2.tendsto

/-- The range-tube event has positive probability for all sufficiently small
positive widths. This is part of the finite escape-rate statement: `ENNReal.toReal`
must not turn a zero probability into the real number zero before taking a
logarithm. -/
theorem eventually_tubeProbability_pos (h : HasStableProcessEscapeRate α μ P C) :
    ∀ᶠ a in 𝓝[>] (0 : ℝ), 0 < (P (stableProcessTube a)).toReal :=
  h.2.eventually_tubeProbability_pos

/-- The escape exponent is strictly negative, as in Lemma 1 I. -/
theorem negative (h : HasStableProcessEscapeRate α μ P C) : C < 0 := h.2.negative

end HasStableProcessEscapeRate

/-- Rescaling the tube radius by a diverging spatial factor converts the
small-radius escape rate into a logarithmic rate in that factor. For any
fixed `r > 0`, the probability of the tube of radius `r / c` satisfies
`c⁻ᵅ log P(tube (r / c)) → C / r^α` as `c → ∞`. This is the scale conversion
used when the stable block parameter is `c^α`. -/
theorem HasStableProcessEscapeRate.tendsto_inv_rpow_mul_log_stableProcessTube
    {α C : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (h : HasStableProcessEscapeRate α μ P C) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun c : ℝ => c⁻¹ ^ α *
      Real.log ((P (stableProcessTube (r / c))).toReal))
      atTop (𝓝 (C / r ^ α)) := by
  have hzero : Tendsto (fun c : ℝ => r / c) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul tendsto_inv_atTop_zero :
        Tendsto (fun c : ℝ => r * c⁻¹) atTop (𝓝 (r * 0)))
  have hpos : ∀ᶠ c : ℝ in atTop, 0 < r / c := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
    exact div_pos hr hc
  have hwithin : Tendsto (fun c : ℝ => r / c) atTop
      (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩
  have hcomp := h.tendsto.comp hwithin
  have hquot : Tendsto (fun c : ℝ =>
      ((r / c) ^ α * Real.log ((P (stableProcessTube (r / c))).toReal)) /
        r ^ α) atTop (𝓝 (C / r ^ α)) := by
    simpa using hcomp.div_const (r ^ α)
  apply hquot.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  have hrc : (r / c) ^ α = r ^ α / c ^ α :=
    Real.div_rpow hr.le hc.le α
  have hcInv : (c⁻¹) ^ α = (c ^ α)⁻¹ := Real.inv_rpow hc.le α
  rw [hrc, hcInv]
  have hrpow : r ^ α ≠ 0 := (Real.rpow_pos_of_pos hr α).ne'
  have hcpow : c ^ α ≠ 0 := (Real.rpow_pos_of_pos hc α).ne'
  field_simp

/-- A negative escape rate gives an explicit strict exponential upper bound
on the tube probability at every sufficiently large spatial scale. The
`2 * ε` slack makes the bound strict while preserving the limiting rate. -/
theorem HasStableProcessEscapeRate.eventually_tubeProbability_lt_exp
    {α C : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (h : HasStableProcessEscapeRate α μ P C) {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hnegative : C / r ^ α + 2 * ε < 0) :
    ∀ᶠ c : ℝ in atTop,
      (P (stableProcessTube (r / c))).toReal <
          Real.exp ((C / r ^ α + 2 * ε) * c ^ α) ∧
        Real.exp ((C / r ^ α + 2 * ε) * c ^ α) < 1 := by
  let rate : ℝ := C / r ^ α
  have hlimit := h.tendsto_inv_rpow_mul_log_stableProcessTube hr
  have hlogEventually : ∀ᶠ c : ℝ in atTop,
      c⁻¹ ^ α * Real.log ((P (stableProcessTube (r / c))).toReal) <
        rate + ε := by
    filter_upwards [hlimit.eventually
      (Iio_mem_nhds (by linarith : C / r ^ α < C / r ^ α + ε))]
      with c hc
    exact hc
  have hprobPos : ∀ᶠ c : ℝ in atTop,
      0 < (P (stableProcessTube (r / c))).toReal := by
    have hsmall := h.2.eventually_tubeProbability_pos
    have harg : Tendsto (fun c : ℝ => r / c) atTop (nhdsWithin 0 (Set.Ioi 0)) := by
      have hzero : Tendsto (fun c : ℝ => r / c) atTop (𝓝 0) := by
        simpa [div_eq_mul_inv] using
          (tendsto_const_nhds.mul tendsto_inv_atTop_zero :
            Tendsto (fun c : ℝ => r * c⁻¹) atTop (𝓝 (r * 0)))
      have hpos : ∀ᶠ c : ℝ in atTop, 0 < r / c := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
        exact div_pos hr hc
      exact tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩
    exact harg.eventually hsmall
  filter_upwards [hlogEventually, hprobPos,
    eventually_gt_atTop (0 : ℝ)] with c hlog hprob hc
  have hcα : 0 < c ^ α := Real.rpow_pos_of_pos hc α
  have hinvPow : c⁻¹ ^ α = (c ^ α)⁻¹ := Real.inv_rpow hc.le α
  have hlog' : Real.log ((P (stableProcessTube (r / c))).toReal) <
      (rate + ε) * c ^ α := by
    rw [hinvPow] at hlog
    have hlogDiv : Real.log ((P (stableProcessTube (r / c))).toReal) /
        c ^ α < rate + ε := by
      simpa [div_eq_mul_inv, mul_comm] using hlog
    exact (div_lt_iff₀ hcα).mp hlogDiv
  have hlog'' : Real.log ((P (stableProcessTube (r / c))).toReal) <
      (rate + 2 * ε) * c ^ α := by
    apply hlog'.trans
    exact mul_lt_mul_of_pos_right (by linarith) hcα
  refine ⟨?_, ?_⟩
  · rw [← Real.exp_log hprob]
    exact Real.exp_lt_exp.mpr hlog''
  rw [← Real.exp_zero]
  apply Real.exp_lt_exp.mpr
  exact mul_neg_of_neg_of_pos (by simpa [rate] using hnegative) hcα

/-- The eventual exponential bound packaged as a strict probability base in
`ENNReal`. This is the form consumed by the stable random-walk block
estimate. -/
theorem HasStableProcessEscapeRate.eventually_tube_lt_of_exp_rate
    {α C : ℝ} {μ : Measure ℝ}
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (h : HasStableProcessEscapeRate α μ P C) {r ε : ℝ}
    (hr : 0 < r) (hε : 0 < ε) (hnegative : C / r ^ α + 2 * ε < 0) :
    ∀ᶠ c : ℝ in atTop,
      P (stableProcessTube (r / c)) <
          ENNReal.ofReal (Real.exp ((C / r ^ α + 2 * ε) * c ^ α)) ∧
        Real.exp ((C / r ^ α + 2 * ε) * c ^ α) < 1 := by
  filter_upwards [h.eventually_tubeProbability_lt_exp hr hε hnegative]
    with c hbound
  have htop : P (stableProcessTube (r / c)) ≠ ⊤ :=
    (measure_lt_top P _).ne
  refine ⟨(ENNReal.toReal_lt_toReal htop ENNReal.ofReal_ne_top).mp ?_, hbound.2⟩
  simpa [ENNReal.toReal_ofReal (Real.exp_pos _).le] using hbound.1

end ProbabilityTheory
