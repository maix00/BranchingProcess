/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.RandomMeasure.Poisson.Integration.Campbell
import Probability.RandomMeasure.Poisson.Integration.Integral
import MeasureTheory.Integral.Lebesgue.RestrictLimit
import Probability.MeasureTheory.SmallValue.Basic

/-!
# Positive probability of a small Poisson integral

Campbell's identity and a finite first moment give a deterministic cutoff
whose realized Poisson integral is small with positive probability.

## Public declarations

* `exists_poissonSmallIntegral_pos` shows that if
  $\int w\,dm<\infty$ and almost every point eventually leaves the measurable
  sets $A_n$, then some $n$ satisfies
  $\mathbb P(\int_{A_n}w\,dN<\rho)>0$.

-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open Filter

/-- A finite intensity integral and eventual exclusion of almost every point
from the sets `band n` yield positive probability of a small restricted
Poisson integral for some `n`. -/
theorem exists_poissonSmallIntegral_pos
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : IsPoissonPointFamily K X m P)
    (weight : E → ENNReal) (band : ℕ → Set E)
    (hweight : Measurable weight)
    (hband : ∀ n, MeasurableSet (band n))
    (hfinite : (∫⁻ x, weight x ∂m) ≠ ⊤)
    (haway : ∀ᵐ x ∂m, ∀ᶠ n in atTop, x ∉ band n)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ n, 0 < P {ω | (∫⁻ x in band n, weight x ∂(poissonRandomMeasure K X ω)) <
      ENNReal.ofReal ρ} := by
  obtain ⟨n, hn⟩ :=
    MeasureTheory.exists_lintegral_restrict_lt_of_eventually_not_mem
      m weight band hweight hband hfinite haway ρ hρ
  let V : Ω → ENNReal := fun ω =>
    ∫⁻ x in band n, weight x ∂(poissonRandomMeasure K X ω)
  have hV : Measurable V := by
    dsimp [V]
    have hm := measurable_lintegral_poissonRandomMeasure
      hd.measurable_count hd.measurable_point (hweight.indicator (hband n))
    simpa only [lintegral_indicator (hband n)] using hm
  have hE : (∫⁻ ω, V ω ∂P) < ENNReal.ofReal ρ := by
    change (∫⁻ ω, ∫⁻ x in band n, weight x
      ∂(poissonRandomMeasure K X ω) ∂P) < ENNReal.ofReal ρ
    rw [lintegral_poissonRandomMeasure_restrict hd (band n) (hband n)
      weight hweight]
    exact hn
  exact ⟨n, measure_pos_of_lintegral_lt P V hV (ENNReal.ofReal ρ) hE⟩

end ProbabilityTheory
