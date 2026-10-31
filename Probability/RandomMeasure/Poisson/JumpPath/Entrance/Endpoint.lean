/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.RandomMeasure.Poisson.JumpPath.Entrance.Basic
public import Probability.RandomMeasure.Poisson.Integration.Integral
import Mathlib.MeasureTheory.Measure.Prod
import Probability.RandomMeasure.Poisson.Intensity.Support
import Probability.RandomMeasure.Poisson.Intensity.TimeMark
import Probability.RandomMeasure.Poisson.RandomMeasure.Evaluation

/-!
# Endpoint identities for Poisson entrance paths

For supported small- and large-jump sources, the entrance path at the final
time equals the sum of the two realized mark integrals. The almost-sure
version follows when each source intensity is carried by its selected region.

For $\omega=(\omega_s,\omega_b)$, set
$\mu_s=\operatorname{poissonRandomMeasure}(K_s,X_s,\omega_s)$ and
$\mu_b=\operatorname{poissonRandomMeasure}(K_b,X_b,\omega_b)$. For selected
regions $A$ and $H$, define the entrance path $E_\omega$ by
$$
E_\omega(t)=\int_{A\cap\{z:z_1\le t\}}z_2\,\mu_s(dz)
  +\int_{H\cap\{z:z_1\le t\}}z_2\,\mu_b(dz).
$$
If $\mu_s\!\restriction_A=\mu_s$ and
$\mu_b\!\restriction_H=\mu_b$, then
$$
E_\omega(\top)=\int z_2\,\mu_s(dz)+\int z_2\,\mu_b(dz).
$$
If the intensity measures assign zero mass to $A^c$ and $H^c$, respectively,
then this endpoint identity holds almost surely under the product law of the
two independent source families.

## Public declarations

- `ProbabilityTheory.poissonEntrancePath_top_eq_integral` gives the endpoint
  identity for any supported pair of realized Poisson measures.
- `ProbabilityTheory.ae_poissonEntrancePath_top_eq_integral` gives the same
  identity almost surely from intensity support.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory

theorem poissonEntrancePath_top_eq_integral
    {Ωs Ωb : Type} [MeasurableSpace Ωs] [MeasurableSpace Ωb]
    (Ks : ℕ → Ωs → ℕ) (Xs : ℕ → ℕ → Ωs → unitInterval × ℝ)
    (Kb : ℕ → Ωb → ℕ) (Xb : ℕ → ℕ → Ωb → unitInterval × ℝ)
    (A H : Set (unitInterval × ℝ)) (ω : Ωs × Ωb)
    (hs : (poissonRandomMeasure Ks Xs ω.1).restrict A =
      poissonRandomMeasure Ks Xs ω.1)
    (hb : (poissonRandomMeasure Kb Xb ω.2).restrict H =
      poissonRandomMeasure Kb Xb ω.2) :
    poissonEntrancePath Ks Xs Kb Xb A H ⊤ ω =
      (∫ z, z.2 ∂(poissonRandomMeasure Ks Xs ω.1)) +
      (∫ z, z.2 ∂(poissonRandomMeasure Kb Xb ω.2)) := by
  simp only [poissonEntrancePath, poissonJumpPath, le_top, and_true, ite_true]
  change (∫ z, z.2 ∂((poissonRandomMeasure Ks Xs ω.1).restrict A)) +
    (∫ z, z.2 ∂((poissonRandomMeasure Kb Xb ω.2).restrict H)) = _
  rw [hs, hb]

/-- The selected endpoint agrees almost surely with the unrestricted sum
when each source intensity is carried by its selected region. -/
theorem ae_poissonEntrancePath_top_eq_integral
    {Ωs Ωb : Type} [MeasurableSpace Ωs] [MeasurableSpace Ωb]
    {Ks : ℕ → Ωs → ℕ} {Xs : ℕ → ℕ → Ωs → unitInterval × ℝ}
    {Kb : ℕ → Ωb → ℕ} {Xb : ℕ → ℕ → Ωb → unitInterval × ℝ}
    {ms mb : Measure (unitInterval × ℝ)} [SigmaFinite ms] [SigmaFinite mb]
    {Ps : Measure Ωs} {Pb : Measure Ωb}
    [IsProbabilityMeasure Ps] [IsProbabilityMeasure Pb]
    (hds : IsPoissonPointFamily Ks Xs ms Ps)
    (hdb : IsPoissonPointFamily Kb Xb mb Pb)
    {A H : Set (unitInterval × ℝ)}
    (hA : MeasurableSet A) (hH : MeasurableSet H)
    (hAs : ms Aᶜ = 0) (hHb : mb Hᶜ = 0) :
    ∀ᵐ ω ∂(Ps.prod Pb),
      poissonEntrancePath Ks Xs Kb Xb A H ⊤ ω =
        (∫ z, z.2 ∂(poissonRandomMeasure Ks Xs ω.1)) +
        (∫ z, z.2 ∂(poissonRandomMeasure Kb Xb ω.2)) := by
  have hs0 : ∀ᵐ ω ∂Ps, poissonRandomMeasure Ks Xs ω Aᶜ = 0 := by
    apply (lintegral_eq_zero_iff
      (measurable_poissonRandomMeasure_apply hds.measurable_count
        hds.measurable_point hA.compl)).mp
    exact (lintegral_poissonRandomMeasure_apply hds hA.compl).trans hAs
  have hb0 : ∀ᵐ ω ∂Pb, poissonRandomMeasure Kb Xb ω Hᶜ = 0 := by
    apply (lintegral_eq_zero_iff
      (measurable_poissonRandomMeasure_apply hdb.measurable_count
        hdb.measurable_point hH.compl)).mp
    exact (lintegral_poissonRandomMeasure_apply hdb hH.compl).trans hHb
  have hmeas : MeasurableSet {ω : Ωs × Ωb |
      poissonRandomMeasure Ks Xs ω.1 Aᶜ = 0 ∧
      poissonRandomMeasure Kb Xb ω.2 Hᶜ = 0} := by
    exact ((measurableSet_singleton (x := (0 : ENNReal))).preimage
      ((measurable_poissonRandomMeasure_apply hds.measurable_count
        hds.measurable_point hA.compl).comp measurable_fst)).inter
      ((measurableSet_singleton (x := (0 : ENNReal))).preimage
        ((measurable_poissonRandomMeasure_apply hdb.measurable_count
          hdb.measurable_point hH.compl).comp measurable_snd))
  have hboth : ∀ᵐ ω ∂(Ps.prod Pb),
      poissonRandomMeasure Ks Xs ω.1 Aᶜ = 0 ∧
      poissonRandomMeasure Kb Xb ω.2 Hᶜ = 0 :=
    (Measure.ae_prod_iff_ae_ae hmeas).2 (hs0.mono fun ω hω =>
      hb0.mono fun _ hη => ⟨hω, hη⟩)
  filter_upwards [hboth] with ω hω
  apply poissonEntrancePath_top_eq_integral Ks Xs Kb Xb A H ω
  · apply Measure.restrict_eq_self_of_ae_mem
    change A ∈ ae (poissonRandomMeasure Ks Xs ω.1)
    exact mem_ae_iff.mpr hω.1
  · apply Measure.restrict_eq_self_of_ae_mem
    change H ∈ ae (poissonRandomMeasure Kb Xb ω.2)
    exact mem_ae_iff.mpr hω.2

end ProbabilityTheory

end
