/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Path.Scaling.FiniteHorizon
public import Probability.Process.Brownian.PathLaw.ContinuousPathLaw

/-!
# Brownian scaling on a finite path interval

The public theorem in this file is:

- `ProbabilityTheory.rescaleUnitPath_restrictPathToUnitInterval_eq_restrict_brownianPathScaling`:
  for $s>0$ and a continuous path $f$,
  $\sqrt{s}\,f(t/s)$ on $[0,s]$ is the restriction of the
  Brownian scaling map with parameter $s^{-1}$.
- `ProbabilityTheory.IsBrownianReal.measure_rescaleUnitPath_eq_finiteHorizonPathLaw`:
  the law of the rescaled unit-time Brownian path is $P^s$.

This is the deterministic path identity used to identify the
finite-horizon Brownian limit in Erwin Bolthausen,
*On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Section 3, Ann. Probab. 4(3) (1976), 480--485,
DOI 10.1214/aop/1176996098. Brownian scaling itself is the result
cited there to Paul Lévy, *Processus Stochastique et Mouvement
Brownien* (1945), p. 246.
-/

@[expose] public section

namespace ProbabilityTheory

open MeasureTheory
open scoped NNReal

/-- The rescaled unit-time path agrees pointwise with inverse-time
Brownian scaling of the whole path. -/
theorem rescaleUnitPath_restrictPathToUnitInterval_eq_restrict_brownianPathScaling
    (m : ℝ≥0) (hm : 0 < m) (f : C(ℝ≥0, ℝ)) :
    rescaleUnitPath m hm (Real.sqrt m) (restrictPathToUnitInterval f) =
      restrictPathTo m (brownianPathScaling m⁻¹ f) := by
  ext t
  have htime :
      UnitInterval.toNNReal (unitTimeOfFiniteTime m hm t) = m⁻¹ * t.1 := by
    apply NNReal.eq
    change (t.1 : ℝ) / (m : ℝ) = ((m⁻¹ : ℝ≥0) : ℝ) * (t.1 : ℝ)
    rw [NNReal.coe_inv]
    ring
  have hamp : (Real.sqrt (((m⁻¹ : ℝ≥0) : ℝ)))⁻¹ = Real.sqrt m := by
    rw [NNReal.coe_inv, Real.sqrt_inv]
    simp
  change Real.sqrt m * f (UnitInterval.toNNReal
      (unitTimeOfFiniteTime m hm t)) =
      (Real.sqrt (((m⁻¹ : ℝ≥0) : ℝ)))⁻¹ * f (m⁻¹ * t.1)
  rw [htime, hamp]

/-- Brownian scaling identifies the rescaled unit-time path law with
the projected whole-time Brownian path law. -/
theorem IsBrownianReal.measure_rescaleUnitPath_eq_finiteHorizonPathLaw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    (m : ℝ≥0) (hm : 0 < m) :
    P.map (fun ω => rescaleUnitPath m hm (Real.sqrt m)
      (continuousunitIntervalPath B hcontinuous ω)) =
      finiteHorizonPathLaw
        (P.map (hB.continuousPathMap hmeasurable)) m := by
  let path := hB.continuousPathMap hmeasurable
  have hae :
      (fun ω => continuousunitIntervalPath B hcontinuous ω) =ᵐ[P]
        fun ω => restrictPathToUnitInterval (path ω) := by
    filter_upwards [hB.continuousPathMap_ae_eq hmeasurable] with ω hω
    ext t
    exact (hω (UnitInterval.toNNReal t)).symm
  have hscale :
      P.map (brownianPathScaling m⁻¹ ∘ path) = P.map path :=
    hB.measure_continuousPathMap_scale_eq hmeasurable (inv_ne_zero hm.ne')
  calc
    P.map (fun ω => rescaleUnitPath m hm (Real.sqrt m)
        (continuousunitIntervalPath B hcontinuous ω)) =
        P.map (fun ω => rescaleUnitPath m hm (Real.sqrt m)
          (restrictPathToUnitInterval (path ω))) := by
            apply Measure.map_congr
            filter_upwards [hae] with ω hω
            rw [hω]
    _ = P.map (fun ω => restrictPathTo m
          (brownianPathScaling m⁻¹ (path ω))) := by
            congr 1
            funext ω
            exact rescaleUnitPath_restrictPathToUnitInterval_eq_restrict_brownianPathScaling
              m hm (path ω)
    _ = (P.map (brownianPathScaling m⁻¹ ∘ path)).map
          (restrictPathTo m) := by
            rw [Measure.map_map]
            · rfl
            · exact (continuous_restrictPathTo m).measurable
            · exact (measurable_brownianPathScaling m⁻¹).comp
                (hB.measurable_continuousPathMap hmeasurable)
    _ = finiteHorizonPathLaw (P.map path) m := by
          rw [hscale]
          rfl

end ProbabilityTheory

end
