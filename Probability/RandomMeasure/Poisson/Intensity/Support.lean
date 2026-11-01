/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Measure.Prod
public import Probability.RandomMeasure.Poisson.RandomMeasure.Basic
import Probability.RandomMeasure.Poisson.RandomMeasure.Evaluation

/-!
# Almost-sure support properties of a Poisson random measure

The fixed-mark assertion is the zero-intensity step for the Lévy
decomposition of descending Brownian hitting times cited in Lemma 2.3,
equation (2.2), of Erwin Bolthausen, *On a Functional Central Limit Theorem
for Random Walks Conditioned to Stay Positive*, Ann. Probab. 4(3) (1976),
480--485 ([DOI](https://doi.org/10.1214/aop/1176996098)).

## Public declarations

* `IsPoissonPointFamily.ae_poissonRandomMeasure_apply_eq_zero` and
  `ae_restrict_poissonRandomMeasure_eq_self` transfer intensity-null sets and
  intensity-full sets to almost-sure statements about the realized measure.
* `IsPoissonPointFamily.ae_no_jump_at_time` excludes points on a zero-mass
  time singleton for any product intensity; `ae_no_mark_at_value` gives the
  corresponding result for a zero-mass mark singleton.
* `IsPoissonPointFamily.ae_integral_nonpos_of_no_positive_intensity` and
  `ae_integral_nonneg_of_no_negative_intensity` give the corresponding signs
  of realized integrals from the support of the intensity measure.

For product intensity `\tau\otimes\nu` on time space `\mathsf T` and mark
space `\mathsf E`, write `\mathcal N_\omega` for the realized Poisson measure.
Intensity-null sets and product-intensity null singletons are absent almost
surely, and an intensity supported on one side forces the same sign for
realized integrals:

\[\begin{aligned}
m(A)=0&\Longrightarrow\mathcal N_\omega(A)=0\quad\text{almost surely},\\
m(A^c)=0&\Longrightarrow\mathcal N_\omega|_A=\mathcal N_\omega
  \quad\text{almost surely},\\
\tau\{t\}=0&\Longrightarrow\mathcal N_\omega(\{t\}\times\mathsf E)=0
  \quad\text{almost surely},\\
\nu\{a\}=0&\Longrightarrow\mathcal N_\omega(\mathsf T\times\{a\})=0
  \quad\text{almost surely},\\
m\{x:f(x)>0\}=0&\Longrightarrow
  \int f\,d\mathcal N_\omega\le0\quad\text{almost surely},\\
m\{x:f(x)<0\}=0&\Longrightarrow
  0\le\int f\,d\mathcal N_\omega\quad\text{almost surely}.
\end{aligned}\]
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

/-- Zero intensity forces zero realized Poisson mass almost surely. -/
theorem IsPoissonPointFamily.ae_poissonRandomMeasure_apply_eq_zero
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : IsPoissonPointFamily K X m P)
    {A : Set E} (hA : MeasurableSet A) (hzero : m A = 0) :
    ∀ᵐ ω ∂P, poissonRandomMeasure K X ω A = 0 := by
  apply (lintegral_eq_zero_iff
    (measurable_poissonRandomMeasure_apply hd.measurable_count
      hd.measurable_point hA)).mp
  exact (lintegral_poissonRandomMeasure_apply hd hA).trans hzero

theorem IsPoissonPointFamily.ae_restrict_poissonRandomMeasure_eq_self
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : IsPoissonPointFamily K X m P)
    {A : Set E} (hA : MeasurableSet A) (hcarrier : m Aᶜ = 0) :
    ∀ᵐ ω ∂P, (poissonRandomMeasure K X ω).restrict A =
      poissonRandomMeasure K X ω := by
  have hzero := hd.ae_poissonRandomMeasure_apply_eq_zero hA.compl hcarrier
  filter_upwards [hzero] with ω hω
  apply Measure.restrict_eq_self_of_ae_mem
  change A ∈ ae (poissonRandomMeasure K X ω)
  exact mem_ae_iff.mpr hω

/-- A product-intensity Poisson source has no point at a fixed time. -/
theorem IsPoissonPointFamily.ae_no_jump_at_time
    {Ω T E : Type} [MeasurableSpace Ω] [MeasurableSpace T] [MeasurableSpace E]
    [MeasurableSingletonClass T]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → T × E}
    {τ : Measure T} [SigmaFinite τ] [Nonempty T]
    {ν : Measure E} [SigmaFinite ν] [Nonempty E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : IsPoissonPointFamily K X (τ.prod ν) P)
    (t : T) (ht : τ {t} = 0) :
    ∀ᵐ ω ∂P,
      poissonRandomMeasure K X ω ({t} ×ˢ Set.univ) = 0 := by
  exact hd.ae_poissonRandomMeasure_apply_eq_zero
    (MeasurableSet.prod (measurableSet_singleton (x := t)) MeasurableSet.univ)
    (by rw [Measure.prod_prod]; simp [ht])

/-- A product-intensity Poisson source whose mark law has no atom at
`a` almost surely has no point carrying that mark. -/
theorem IsPoissonPointFamily.ae_no_mark_at_value
    {Ω T E : Type} [MeasurableSpace Ω] [MeasurableSpace T] [MeasurableSpace E]
    [MeasurableSingletonClass E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → T × E}
    {τ : Measure T} [SigmaFinite τ] [Nonempty T]
    {ν : Measure E} [SigmaFinite ν] [Nonempty E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : IsPoissonPointFamily K X (τ.prod ν) P)
    (a : E) (hν : ν {a} = 0) :
    ∀ᵐ ω ∂P,
      poissonRandomMeasure K X ω (Set.univ ×ˢ {a}) = 0 := by
  apply hd.ae_poissonRandomMeasure_apply_eq_zero
    (MeasurableSet.prod MeasurableSet.univ (measurableSet_singleton (x := a)))
  rw [Measure.prod_prod]
  simp [hν]

/-- If the intensity has no positive values of a real mark observable,
the realized Poisson integral is nonpositive almost surely. -/
theorem IsPoissonPointFamily.ae_integral_nonpos_of_no_positive_intensity
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : IsPoissonPointFamily K X m P)
    {f : E → ℝ} (hf : Measurable f)
    (hzero : m {x | 0 < f x} = 0) :
    ∀ᵐ ω ∂P, (∫ x, f x ∂(poissonRandomMeasure K X ω)) ≤ 0 := by
  have hpos := hd.ae_poissonRandomMeasure_apply_eq_zero
    (measurableSet_lt measurable_const hf) hzero
  filter_upwards [hpos] with ω hω
  apply integral_nonpos_of_ae
  have hmem : {x | f x ≤ 0} ∈ ae (poissonRandomMeasure K X ω) := by
    apply mem_ae_iff.mpr
    have hset : ({x | f x ≤ 0} : Set E)ᶜ = {x | 0 < f x} := by
      ext x
      simp
    rwa [hset]
  exact hmem

/-- An intensity with no negative values yields a nonnegative realized
Poisson integral almost surely. -/
theorem IsPoissonPointFamily.ae_integral_nonneg_of_no_negative_intensity
    {Ω E : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E}
    {m : Measure E} [SigmaFinite m] [Nonempty E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (hd : IsPoissonPointFamily K X m P)
    {f : E → ℝ} (hf : Measurable f)
    (hzero : m {x | f x < 0} = 0) :
    ∀ᵐ ω ∂P, 0 ≤ (∫ x, f x ∂(poissonRandomMeasure K X ω)) := by
  have hneg := hd.ae_poissonRandomMeasure_apply_eq_zero
    (measurableSet_lt hf measurable_const) hzero
  filter_upwards [hneg] with ω hω
  apply integral_nonneg_of_ae
  apply mem_ae_iff.mpr
  have hset : ({x | 0 ≤ f x} : Set E)ᶜ = {x | f x < 0} := by
    ext x
    simp
  change (poissonRandomMeasure K X ω) ({x | 0 ≤ f x} : Set E)ᶜ = 0
  rwa [hset]

end ProbabilityTheory
