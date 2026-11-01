/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.RandomMeasure.Poisson.JumpPath.Entrance.Basic
import Probability.MeasureTheory.SmallValue.Basic
import Probability.RandomMeasure.Poisson.Integration.Campbell
import Probability.RandomMeasure.Poisson.Integration.Integral
import Probability.RandomMeasure.Poisson.Realization.FiniteJump

/-!
# Entrance after a fixed Lévy-intensity cutoff

For fixed small- and large-jump intensities $m_s,m_b$, assume
$\int |z_2|\,m_s(dz)<\rho$, $m_b(J),m_b(B)<\infty$,
$m_b(J)>0$, $J\cap B=\varnothing$, and
$|z_2-\mathrm{target}|<\rho$ on $J$. If $\rho>0$ and $2\rho<\varepsilon$,
with the stated corridor-margin conditions, the theorem constructs
independent Poisson sources. Under their product law, their entrance path $E$
satisfies
$$
\mathbb P\!\left\{
  \forall t\in[0,1],\quad
  \mathrm{lower}+\mathrm{margin}-2\rho\le E(t)
    \le\mathrm{upper}-\mathrm{margin}+2\rho,
  \quad
  \mathrm{target}-\varepsilon<E(1)<\mathrm{target}+\varepsilon
\right\}>0.
$$
Here $E(t)$ is the entrance path with small-jump region $[0,1]\times\mathbb R$
and large-jump region $J\cup B$.

## Public declarations

- `ProbabilityTheory.exists_poissonEntrancePath_model_of_smallMoment`: for
  fixed small- and large-jump intensity measures, if the small-jump first
  absolute moment is below \(\rho\) and the large-jump measure assigns
  positive mass to a target window, then there are independent Poisson point
  families whose complete path has positive probability to stay in the
  shrunken corridor and end in the target window.

Here the small and large Poisson sources already carry the two restricted
intensities. A strict first-moment bound on the small source yields the
positive entrance event without a further truncation of its realized path.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

theorem exists_poissonEntrancePath_model_of_smallMoment
    (ms mb : Measure (unitInterval × ℝ))
    [SigmaFinite ms] [SigmaFinite mb]
    {J B : Set (unitInterval × ℝ)}
    (hJ : MeasurableSet J) (hB : MeasurableSet B)
    (hfinJ : mb J < ⊤) (hfinB : mb B < ⊤)
    (hJpos : 0 < mb J) (hdisj : Disjoint J B)
    (lower upper target ρ ε margin : ℝ)
    (hsmallMoment :
      (∫⁻ z, ENNReal.ofReal |z.2| ∂ms) < ENNReal.ofReal ρ)
    (hρ : 0 < ρ) (hε : 2 * ρ < ε)
    (hl0 : lower + margin ≤ 0) (hu0 : 0 ≤ upper - margin)
    (hly : lower + margin ≤ target) (huy : target ≤ upper - margin)
    (hJwindow : ∀ z ∈ J, |z.2 - target| < ρ) :
    ∃ (Ωs Ωb : Type) (_ : MeasurableSpace Ωs) (_ : MeasurableSpace Ωb)
      (Ps : Measure Ωs) (Pb : Measure Ωb)
      (Ks : ℕ → Ωs → ℕ)
      (Xs : ℕ → ℕ → Ωs → unitInterval × ℝ)
      (Kb : ℕ → Ωb → ℕ)
      (Xb : ℕ → ℕ → Ωb → unitInterval × ℝ),
      IsProbabilityMeasure Ps ∧ IsProbabilityMeasure Pb ∧
      IsPoissonPointFamily Ks Xs ms Ps ∧
      IsPoissonPointFamily Kb Xb mb Pb ∧
      0 < (Ps.prod Pb) {ω : Ωs × Ωb |
        (∀ t, lower + (margin - 2 * ρ) ≤
            poissonEntrancePath Ks Xs Kb Xb Set.univ (J ∪ B) t ω ∧
          poissonEntrancePath Ks Xs Kb Xb Set.univ (J ∪ B) t ω ≤
            upper - (margin - 2 * ρ)) ∧
        target - ε < poissonEntrancePath Ks Xs Kb Xb Set.univ (J ∪ B) ⊤ ω ∧
        poissonEntrancePath Ks Xs Kb Xb Set.univ (J ∪ B) ⊤ ω < target + ε} := by
  obtain ⟨Ωs, mΩs, Ps, Ks, Xs, hPs, hds⟩ := exists_isPoissonPointFamily ms
  obtain ⟨Ωb, mΩb, Pb, Kb, Xb, hPb, hdb⟩ := exists_isPoissonPointFamily mb
  let := mΩs
  let := mΩb
  let := hPs
  let := hPb
  let V : Ωs → ENNReal := fun ω =>
    ∫⁻ z, ENNReal.ofReal |z.2| ∂(poissonRandomMeasure Ks Xs ω)
  have hV : Measurable V :=
    measurable_lintegral_poissonRandomMeasure
      hds.measurable_count hds.measurable_point (by fun_prop)
  have hE : (∫⁻ ω, V ω ∂Ps) < ENNReal.ofReal ρ := by
    rw [lintegral_lintegral_poissonRandomMeasure hds (by fun_prop)]
    exact hsmallMoment
  have hsmall : 0 < Ps {ω | V ω < ENNReal.ofReal ρ} :=
    measure_pos_of_lintegral_lt Ps V hV (ENNReal.ofReal ρ) hE
  have hbig := measure_poissonRandomMeasure_one_and_zero_pos
    hdb hJ hB hfinJ hfinB hJpos hdisj
  have hgood : 0 < (Ps.prod Pb) {ω : Ωs × Ωb |
      (∫⁻ z in Set.univ, ENNReal.ofReal |z.2|
        ∂(poissonRandomMeasure Ks Xs ω.1)) < ENNReal.ofReal ρ ∧
      (poissonRandomMeasure Kb Xb ω.2 : Measure (unitInterval × ℝ)) J = 1 ∧
      (poissonRandomMeasure Kb Xb ω.2 : Measure (unitInterval × ℝ)) B = 0} := by
    have hset : {ω : Ωs × Ωb |
        (∫⁻ z in Set.univ, ENNReal.ofReal |z.2|
          ∂(poissonRandomMeasure Ks Xs ω.1)) < ENNReal.ofReal ρ ∧
        poissonRandomMeasure Kb Xb ω.2 J = 1 ∧
        poissonRandomMeasure Kb Xb ω.2 B = 0} =
        {ω : Ωs | V ω < ENNReal.ofReal ρ} ×ˢ
        {ω : Ωb | poissonRandomMeasure Kb Xb ω J = 1 ∧
          poissonRandomMeasure Kb Xb ω B = 0} := by
      ext ω
      simp [V]
    rw [hset, Measure.prod_prod]
    exact ENNReal.mul_pos hsmall.ne' hbig.ne'
  refine ⟨Ωs, Ωb, mΩs, mΩb, Ps, Pb, Ks, Xs, Kb, Xb,
    hPs, hPb, hds, hdb, ?_⟩
  exact measure_poissonEntrancePath_pos_of_one_zero
    (mb := mb) Ps Pb Set.univ J B hJ hB
    lower upper target ρ ε margin hρ hε hl0 hu0 hly huy
    hJwindow hgood

end ProbabilityTheory
