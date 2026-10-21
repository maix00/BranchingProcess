/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Target.EndpointBand

/-!
# Seven-window geometry for endpoint-band estimates

The public declarations in this module are:

- `centralEndpointWindowLo`: the left endpoint
  $4m-(3s+e)+js$ of window $j\in\{0,\ldots,6\}$.
- `centralEndpointWindowLo_fits`: if $3s+e\le2m$, all seven windows lie in
  the central lattice region $[2m,6m]$.
- `eventually_forall_sevenCentralEndpointWindowTargetMass_lower`: under the
  stated diffusive scaling and spectral threshold, one common positive lower
  bound holds for the target mass in every one of the seven windows.

This finite assembly uses the general target-band estimate from
`Spectral/Target/EndpointBand.lean` and is specific to the endpoint choice in
Lemma 3(d) of A. A. Mogul'skii, “Small Deviations in the Sample Function
Space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4) (1974), 755--765;
English translation, “Small Deviations in a Space of Trajectories,” *Theory
of Probability and Its Applications* 19(4) (1975), 726--736, DOI
10.1137/1119081.
-/

open MeasureTheory
open scoped BigOperators ENNReal
open Filter Topology

open ProbabilityTheory.RandomWalk.Rademacher.FiniteInterval

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- The left lattice boundary of one of seven endpoint windows.  `spacing`
sets the displacement of consecutive window centers; `windowRadius` is their
independent half-width. -/
def centralEndpointWindowLo (m spacing windowRadius : ℕ) (j : Fin 7) : ℕ :=
  4 * m - (3 * spacing + windowRadius) + j.val * spacing

lemma centralEndpointWindowLo_fits (m spacing windowRadius : ℕ)
    (hfit : 3 * spacing + windowRadius ≤ 2 * m) (j : Fin 7) :
    2 * m ≤ centralEndpointWindowLo m spacing windowRadius j ∧
      centralEndpointWindowLo m spacing windowRadius j + 2 * windowRadius ≤ 6 * m := by
  have hbase : 3 * spacing + windowRadius ≤ 4 * m := by omega
  have hj : j.val ≤ 6 := by omega
  have hjmul : j.val * spacing ≤ 6 * spacing :=
    Nat.mul_le_mul_right spacing hj
  unfold centralEndpointWindowLo
  constructor <;> omega

/-- Uniform spectral lower bounds for seven endpoint windows whose center
spacing and half-width are independent.  Their relative window width may
shrink with the block size, as long as it has a positive limit at each fixed
diffusive parameter. -/
lemma eventually_forall_sevenCentralEndpointWindowTargetMass_lower
    (scale time spacing windowRadius : ℕ → ℕ) {c p lowerBound : ℝ}
    (hscale : ∀ n, 0 < scale n) (htime : ∀ n, 0 < time n)
    (hwindow : ∀ n, 2 ≤ windowRadius n)
    (hfit : ∀ n, 3 * spacing n + windowRadius n ≤ 2 * scale n)
    (hwidth : Tendsto (fun n => ((8 * scale n : ℕ) : ℝ)) atTop atTop)
    (hratio : Tendsto (fun n => (time n : ℝ) /
        ((8 * scale n : ℕ) : ℝ) ^ 2) atTop (nhds c))
    (hproportion : Tendsto (fun n => ((windowRadius n - 1 : ℕ) : ℝ) /
        ((8 * scale n : ℕ) : ℝ)) atTop (nhds p))
    (hp : 0 < p)
    (hsmallLimit : Real.exp (c * (-(Real.pi ^ 2) / 2)) <
      (4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) * p) /
        (4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) * p + 8))
    (hlowerBound : lowerBound <
      p * Real.exp (c * (-(Real.pi ^ 2) / 2))) :
    ∀ᶠ n in atTop, ∀ j : Fin 7,
      lowerBound ≤
        ∑ finish ∈ centralEndpointBandTarget (scale n) (time n)
            (centralEndpointWindowLo (scale n) (spacing n) (windowRadius n) j)
            (windowRadius n) (hscale n)
            (centralEndpointWindowLo_fits (scale n) (spacing n)
              (windowRadius n) (hfit n) j).2,
          (intervalKernel (8 * scale n - 1) ^ time n)
            (centralIntervalStart (scale n) (hscale n)) finish := by
  have hloFit : ∀ n j,
      2 * scale n ≤ centralEndpointWindowLo (scale n) (spacing n)
        (windowRadius n) j := by
    intro n j
    exact (centralEndpointWindowLo_fits (scale n) (spacing n)
      (windowRadius n) (hfit n) j).1
  have hhiFit : ∀ n j,
      centralEndpointWindowLo (scale n) (spacing n) (windowRadius n) j +
        2 * windowRadius n ≤ 6 * scale n := by
    intro n j
    exact (centralEndpointWindowLo_fits (scale n) (spacing n)
      (windowRadius n) (hfit n) j).2
  have hfinite : ∀ᶠ n in atTop, ∀ j ∈ (Finset.univ : Finset (Fin 7)),
      lowerBound ≤
        ∑ finish ∈ centralEndpointBandTarget (scale n) (time n)
            (centralEndpointWindowLo (scale n) (spacing n)
              (windowRadius n) j) (windowRadius n)
            (hscale n) (hhiFit n j),
          (intervalKernel (8 * scale n - 1) ^ time n)
            (centralIntervalStart (scale n) (hscale n)) finish := by
    apply (Finset.univ : Finset (Fin 7)).eventually_all.2
    intro j _
    exact eventually_lowerBound_le_centralEndpointBandTargetMass_of_diffusiveRatio
      scale time (fun n => centralEndpointWindowLo (scale n) (spacing n)
        (windowRadius n) j) windowRadius
      hscale htime hwindow (hloFit · j) (hhiFit · j) hwidth hratio hproportion hp
      hsmallLimit hlowerBound
  filter_upwards [hfinite] with n hn
  intro j
  have hj := hn j (Finset.mem_univ j)
  simpa using hj


end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

end
