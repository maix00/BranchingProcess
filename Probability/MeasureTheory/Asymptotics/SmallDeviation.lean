/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Power-law small-deviation rates

For a real-valued function $p(\varepsilon)$, in applications a small-event
probability, the predicate
`HasPowerLawSmallDeviationRate α C p` records
\[
  0 < \alpha,\qquad C < 0,\qquad
  \varepsilon^\alpha \log p(\varepsilon) \longrightarrow C
  \quad (\varepsilon \downarrow 0),
\]
with $p(\varepsilon)>0$ for all sufficiently small positive
$\varepsilon$. It is independent of the process and the event that define
$p$.

## Public declarations

The declarations are:

* `HasPowerLawSmallDeviationRate`: the scalar power-law logarithmic
  small-deviation property above.
* `HasPowerLawSmallDeviationRate.exponent_pos`,
  `HasPowerLawSmallDeviationRate.negative`,
  `HasPowerLawSmallDeviationRate.eventually_probability_pos`, and
  `HasPowerLawSmallDeviationRate.tendsto`: projections of its assumptions.
* `HasPowerLawSmallDeviationRate.spatialScale`: for $q>0$, replacing
  $p(\varepsilon)$ by $p(\varepsilon/q)$ changes the limiting constant to
  $q^\alpha C$.
* `smallDeviationEnergyCoefficient α C = -2^α C`: the positive energy
  coefficient obtained from a negative rate constant after converting the
  radius parameter to the full diameter convention.

This is the scalar form of small-deviation asymptotics studied through
$-\log \mathbb P(\|X\|\leq\varepsilon)$; see F. Aurzada, “Path regularity of
Gaussian processes via small deviations,” *Probability and Mathematical
Statistics* 31(1) (2011), 61–78, equation (1.1) and Section 2
(arXiv:0905.3358). The stable-process application is A. A. Mogul'skii,
“Small deviations in the sample function space,” *Teoriya Veroyatnostei i ee
Primeneniya* 19(4) (1974), 755–765; English translation, “Small Deviations in
a Space of Trajectories,” *Theory of Probability and Its Applications* 19(4)
(1975), 726–736, DOI 10.1137/1119081, Lemma 1(I), equations (18)–(20), and is owned by
`Probability.Process.Stable.SmallDeviation.EscapeRate.PathLaw.Basic`.
-/

open Filter
open scoped Topology

@[expose] public section

namespace ProbabilityTheory

/-- A real-valued function has power-law small-deviation rate `C` and exponent
`α` if `α > 0`, `C < 0`, the values are eventually positive, and
`ε ^ α * log (p ε) → C` as positive `ε` tends to zero. In probability
applications, `p` is the real-valued probability of a small event. -/
def HasPowerLawSmallDeviationRate (α C : ℝ) (p : ℝ → ℝ) : Prop :=
  0 < α ∧ C < 0 ∧
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < p ε) ∧
    Tendsto (fun ε => ε ^ α * Real.log (p ε))
      (𝓝[>] (0 : ℝ)) (𝓝 C)

namespace HasPowerLawSmallDeviationRate

variable {α C : ℝ} {p : ℝ → ℝ}

theorem exponent_pos (h : HasPowerLawSmallDeviationRate α C p) : 0 < α := h.1

theorem negative (h : HasPowerLawSmallDeviationRate α C p) : C < 0 := h.2.1

theorem eventually_probability_pos
    (h : HasPowerLawSmallDeviationRate α C p) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < p ε := h.2.2.1

theorem tendsto (h : HasPowerLawSmallDeviationRate α C p) :
    Tendsto (fun ε => ε ^ α * Real.log (p ε))
      (𝓝[>] (0 : ℝ)) (𝓝 C) := h.2.2.2

/-- Rescaling the radius by `q > 0` multiplies the power-law logarithmic
small-deviation constant by `q ^ α`. -/
theorem spatialScale {q : ℝ} (h : HasPowerLawSmallDeviationRate α C p)
    (hq : 0 < q) :
    HasPowerLawSmallDeviationRate α (q ^ α * C) (fun ε => p (ε / q)) := by
  have hqα : 0 < q ^ α := Real.rpow_pos_of_pos hq _
  have hratioNhd : Tendsto (fun ε : ℝ => ε / q)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simpa using
      ((by fun_prop : ContinuousAt (fun ε : ℝ => ε / q) 0).tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ)))
  have hratioPos : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε / q := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact div_pos hε hq
  have hratio : Tendsto (fun ε : ℝ => ε / q)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hratioNhd hratioPos
  have hscaledPos : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < p (ε / q) :=
    hratio.eventually h.eventually_probability_pos
  have hcomp := h.tendsto.comp hratio
  have hproduct :=
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => q ^ α)
      (𝓝[>] (0 : ℝ)) (𝓝 (q ^ α))).mul hcomp
  have hpow : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
      ε ^ α = q ^ α * (ε / q) ^ α := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε_nonneg : 0 ≤ ε := le_of_lt hε
    have hdiv_nonneg : 0 ≤ ε / q := div_nonneg hε_nonneg hq.le
    have hmul : q * (ε / q) = ε := by field_simp [ne_of_gt hq]
    calc
      ε ^ α = (q * (ε / q)) ^ α :=
        congrArg (fun x : ℝ => x ^ α) hmul.symm
      _ = q ^ α * (ε / q) ^ α := Real.mul_rpow hq.le hdiv_nonneg
  have heq : (fun ε : ℝ => ε ^ α * Real.log (p (ε / q))) =ᶠ[
      𝓝[>] (0 : ℝ)]
      (fun ε => q ^ α * ((ε / q) ^ α * Real.log (p (ε / q)))) := by
    filter_upwards [hpow] with ε hε
    rw [hε]
    ring
  refine ⟨h.exponent_pos, mul_neg_of_pos_of_neg hqα h.negative, hscaledPos, ?_⟩
  exact hproduct.congr' heq.symm

end HasPowerLawSmallDeviationRate

/-- Convert a negative power-law small-deviation rate to the positive energy
coefficient associated with the full-diameter convention. If the original
rate is `C < 0` at radius `a`, the coefficient is `-2^α C`. -/
noncomputable def smallDeviationEnergyCoefficient (α C : ℝ) : ℝ :=
  -(C * (2 : ℝ) ^ α)

/-- The energy coefficient associated with a negative rate constant is
positive. -/
theorem smallDeviationEnergyCoefficient_pos {α C : ℝ} (hC : C < 0) :
    0 < smallDeviationEnergyCoefficient α C := by
  rw [smallDeviationEnergyCoefficient]
  have hpow : 0 < (2 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) α
  exact neg_pos.mpr (mul_neg_of_neg_of_pos hC hpow)

end ProbabilityTheory

end
