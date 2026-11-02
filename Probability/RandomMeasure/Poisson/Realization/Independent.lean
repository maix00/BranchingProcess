/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.RandomMeasure.Poisson.Integration.SmallValue
import Probability.RandomMeasure.Poisson.Realization.FiniteJump

/-!
# Independent small and large Poisson sources

On a product probability space, a small-jump Poisson random measure and an
independent large-jump Poisson random measure can realize a small residual
variation and an exact one-jump configuration simultaneously. This avoids a
separate independence assumption about restrictions of one random measure.

Under the finite-integral and eventual-exclusion hypotheses on the small
source, and the finite, disjoint measurable large-region hypotheses on $J,B$
with $m_b(J)>0$, let $w$ be the measurable weight and set
$A_n=\operatorname{band}(n)$ for the measurable small-source sets. Write
$N_s(\omega_s)=\operatorname{poissonRandomMeasure}(K_s,X_s,\omega_s)$ and
$N_b(\omega_b)=\operatorname{poissonRandomMeasure}(K_b,X_b,\omega_b)$. Then,
for every $\rho>0$, some $n$ satisfies
$$
(P_s\otimes P_b)\!\left\{(\omega_s,\omega_b):
  \int_{A_n}^- w(x)\,N_s(\omega_s)(dx)<\operatorname{ofReal}(\rho),\quad
  N_b(\omega_b)(J)=1,\quad N_b(\omega_b)(B)=0
\right\}>0,
$$
and the model-existence theorem constructs such families from their
intensity measures.

## Public declarations

* `exists_independent_poissonSmallVariation_oneJump_pos` constructs a product
  model with positive probability of small-jump variation below $\rho$, one
  point in $J$, and no points in disjoint $B$.
* `exists_poissonSmallVariation_oneJump_model` packages that construction as
  two independent Poisson point families with their respective intensities.

-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory Filter

theorem exists_independent_poissonSmallVariation_oneJump_pos
    {Ωs Ωb E : Type} [MeasurableSpace Ωs] [MeasurableSpace Ωb]
    [MeasurableSpace E]
    {Ks : ℕ → Ωs → ℕ} {Xs : ℕ → ℕ → Ωs → E}
    {Kb : ℕ → Ωb → ℕ} {Xb : ℕ → ℕ → Ωb → E}
    {ms mb : Measure E} [SigmaFinite ms] [SigmaFinite mb] [Nonempty E]
    {Ps : Measure Ωs} {Pb : Measure Ωb}
    [IsProbabilityMeasure Ps] [IsProbabilityMeasure Pb]
    (hds : IsPoissonPointFamily Ks Xs ms Ps)
    (hdb : IsPoissonPointFamily Kb Xb mb Pb)
    (weight : E → ENNReal) (band : ℕ → Set E)
    (hweight : Measurable weight)
    (hband : ∀ n, MeasurableSet (band n))
    (hfinite : (∫⁻ x, weight x ∂ms) ≠ ⊤)
    (haway : ∀ᵐ x ∂ms, ∀ᶠ n in atTop, x ∉ band n)
    {J B : Set E} (hJ : MeasurableSet J) (hB : MeasurableSet B)
    (hfinJ : mb J < ⊤) (hfinB : mb B < ⊤)
    (hJpos : 0 < mb J) (hdisj : Disjoint J B)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ n, 0 < (Ps.prod Pb) {ω : Ωs × Ωb |
      (∫⁻ x in band n, weight x ∂(poissonRandomMeasure Ks Xs ω.1)) <
          ENNReal.ofReal ρ ∧
      poissonRandomMeasure Kb Xb ω.2 J = 1 ∧
      poissonRandomMeasure Kb Xb ω.2 B = 0} := by
  obtain ⟨n, hsmall⟩ := exists_poissonSmallIntegral_pos hds weight band
    hweight hband hfinite haway ρ hρ
  have hbig := measure_poissonRandomMeasure_one_and_zero_pos
    hdb hJ hB hfinJ hfinB hJpos hdisj
  refine ⟨n, ?_⟩
  let small : Set Ωs := {ω | (∫⁻ x in band n, weight x
    ∂(poissonRandomMeasure Ks Xs ω)) < ENNReal.ofReal ρ}
  let big : Set Ωb := {ω | poissonRandomMeasure Kb Xb ω J = 1 ∧
    poissonRandomMeasure Kb Xb ω B = 0}
  have hset : {ω : Ωs × Ωb |
      (∫⁻ x in band n, weight x ∂(poissonRandomMeasure Ks Xs ω.1)) <
          ENNReal.ofReal ρ ∧
      poissonRandomMeasure Kb Xb ω.2 J = 1 ∧
      poissonRandomMeasure Kb Xb ω.2 B = 0} = small ×ˢ big := by
    ext ω
    rfl
  rw [hset, Measure.prod_prod]
  exact ENNReal.mul_pos hsmall.ne' hbig.ne'

/-- The independent small/large Poisson sources required above exist on a
canonical product probability space; their point-family laws are constructed,
not postulated. -/
theorem exists_poissonSmallVariation_oneJump_model
    {E : Type} [MeasurableSpace E] [Nonempty E]
    (ms mb : Measure E) [SigmaFinite ms] [SigmaFinite mb]
    (weight : E → ENNReal) (band : ℕ → Set E)
    (hweight : Measurable weight)
    (hband : ∀ n, MeasurableSet (band n))
    (hfinite : (∫⁻ x, weight x ∂ms) ≠ ⊤)
    (haway : ∀ᵐ x ∂ms, ∀ᶠ n in atTop, x ∉ band n)
    {J B : Set E} (hJ : MeasurableSet J) (hB : MeasurableSet B)
    (hfinJ : mb J < ⊤) (hfinB : mb B < ⊤)
    (hJpos : 0 < mb J) (hdisj : Disjoint J B)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ (Ωs Ωb : Type) (_ : MeasurableSpace Ωs) (_ : MeasurableSpace Ωb)
      (Ps : Measure Ωs) (Pb : Measure Ωb)
      (Ks : ℕ → Ωs → ℕ) (Xs : ℕ → ℕ → Ωs → E)
      (Kb : ℕ → Ωb → ℕ) (Xb : ℕ → ℕ → Ωb → E),
      IsProbabilityMeasure Ps ∧ IsProbabilityMeasure Pb ∧
      IsPoissonPointFamily Ks Xs ms Ps ∧
      IsPoissonPointFamily Kb Xb mb Pb ∧
      ∃ n, 0 < (Ps.prod Pb) {ω : Ωs × Ωb |
        (∫⁻ x in band n, weight x ∂(poissonRandomMeasure Ks Xs ω.1)) <
            ENNReal.ofReal ρ ∧
        poissonRandomMeasure Kb Xb ω.2 J = 1 ∧
        poissonRandomMeasure Kb Xb ω.2 B = 0} := by
  obtain ⟨Ωs, mΩs, Ps, Ks, Xs, hPs, hds⟩ := exists_isPoissonPointFamily ms
  obtain ⟨Ωb, mΩb, Pb, Kb, Xb, hPb, hdb⟩ := exists_isPoissonPointFamily mb
  let := mΩs
  let := mΩb
  let := hPs
  let := hPb
  refine ⟨Ωs, Ωb, mΩs, mΩb, Ps, Pb, Ks, Xs, Kb, Xb,
    hPs, hPb, hds, hdb, ?_⟩
  exact exists_independent_poissonSmallVariation_oneJump_pos hds hdb
    weight band hweight hband hfinite haway hJ hB hfinJ hfinB
    hJpos hdisj ρ hρ

end ProbabilityTheory
