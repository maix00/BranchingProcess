/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Rademacher.FiniteInterval.Spectral.Target.LowerBound
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Diffusive.Lower

/-!
# Diffusive lower bounds for finite-interval target mass

For intervals of $N_n=2r_n+1$ interior sites, write $W_n=N_n+1$, let
$K_{N_n}$ be the killed Rademacher transition matrix, and let $T_n$ be a
finite target with start $x_n$. If $r_n,m_n>0$, $W_n\to\infty$,
$m_n/W_n^2\to c$, and positive constants $a,b,p$ uniformly bound the start
and parity-compatible target ground-state weights below and the compatible
target density below, then
`eventually_realBound_le_centeredDiffusiveTargetMass` gives
\[
  \forall^{\mathrm{ev}} n,\qquad
  \texttt{lowerBound}\le\sum_{y\in T_n}K_{N_n}^{m_n}(x_n,y),
\]
for every $\texttt{lowerBound}<2abp\,e^{-\pi^2c/2}$, provided also that
$e^{-\pi^2c/2}<\frac{4abp}{4abp+8}$. It combines the finite-interval
target-mass estimate with the diffusive limit of the principal eigenvalue
power.
-/

open Filter Topology
open scoped BigOperators Matrix
open ProbabilityTheory.RandomWalk.Rademacher.FiniteInterval

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

theorem eventually_realBound_le_centeredDiffusiveTargetMass
    (radius time : ℕ → ℕ) (target : ∀ n, Finset (Fin (2 * radius n + 1)))
    (start : ∀ n, Fin (2 * radius n + 1))
    {startWeight targetWeight proportion c lowerBound : ℝ}
    (hradius : ∀ n, 0 < radius n) (htime : ∀ n, 0 < time n)
    (hwidth : Tendsto
      (fun n => ((2 * (radius n + 1) : ℕ) : ℝ)) atTop atTop)
    (hratio : Tendsto (fun n => (time n : ℝ) /
      ((2 * (radius n + 1) : ℕ) : ℝ) ^ 2) atTop (nhds c))
    (hstartWeight : 0 < startWeight)
    (htargetWeight : 0 < targetWeight) (hproportion : 0 < proportion)
    (hstart : ∀ n, startWeight ≤
      intervalSineWeight (2 * radius n + 1) (start n))
    (htarget : ∀ n finish,
      finish ∈ intervalParityCompatibleTarget (time n) (start n) (target n) →
      targetWeight ≤ intervalSineWeight (2 * radius n + 1) finish)
    (hcard : ∀ n, proportion * ((2 * (radius n + 1) : ℕ) : ℝ) ≤
      (intervalParityCompatibleTarget (time n) (start n) (target n)).card)
    (hsmallLimit : Real.exp (c * (-(Real.pi ^ 2) / 2)) <
      (4 * startWeight * targetWeight * proportion) /
        (4 * startWeight * targetWeight * proportion + 8))
    (hlowerBound : lowerBound <
      (2 * startWeight * targetWeight * proportion) *
        Real.exp (c * (-(Real.pi ^ 2) / 2))) :
    ∀ᶠ n in atTop, lowerBound ≤
      ∑ finish ∈ target n,
        (intervalKernel (2 * radius n + 1) ^ time n) (start n) finish := by
  let width : ℕ → ℝ := fun n => ((2 * (radius n + 1) : ℕ) : ℝ)
  let qpow : ℕ → ℝ := fun n =>
    Real.cos (Real.pi / width n) ^ time n
  let coefficient : ℝ := 4 * startWeight * targetWeight * proportion
  have hpower : Tendsto qpow atTop
      (nhds (Real.exp (c * (-(Real.pi ^ 2) / 2)))) := by
    simpa [qpow, width] using
      tendsto_centeredPrincipalPower_of_diffusiveRatio
        radius time c hradius hwidth hratio
  have hcoefficient : 0 < coefficient := by
    dsimp [coefficient]
    positivity
  have hsmallEventually : ∀ᶠ n in atTop,
      qpow n ≤ coefficient / (coefficient + 8) := by
    have hthreshold :
        ∀ᶠ n in atTop, qpow n < coefficient / (coefficient + 8) :=
      hpower.eventually (eventually_lt_nhds (by simpa [coefficient] using hsmallLimit))
    exact hthreshold.mono fun _ h => h.le
  have hlowerEventually : ∀ᶠ n in atTop,
      lowerBound < coefficient / 2 * qpow n := by
    have hscaled : Tendsto (fun n => coefficient / 2 * qpow n)
        atTop (nhds (coefficient / 2 *
          Real.exp (c * (-(Real.pi ^ 2) / 2)))) :=
      (tendsto_const_nhds.mul hpower)
    have hstrict : lowerBound < coefficient / 2 *
        Real.exp (c * (-(Real.pi ^ 2) / 2)) := by
      dsimp [coefficient]
      nlinarith [hlowerBound]
    exact hscaled.eventually (eventually_gt_nhds hstrict)
  filter_upwards [hsmallEventually, hlowerEventually] with n hsmallN hlowerN
  have hwidthEq : width n =
      ((2 * radius n + 1 + 1 : ℕ) : ℝ) := by
    dsimp [width]
    push_cast
    ring
  have hcount : 1 < 2 * radius n + 1 := by
    have := hradius n
    omega
  have hcardN : proportion * ((2 * radius n + 1 + 1 : ℕ) : ℝ) ≤
      (intervalParityCompatibleTarget (time n) (start n) (target n)).card := by
    convert hcard n using 1
  have hsmallN' : Real.cos
        (Real.pi / ((2 * radius n + 1 + 1 : ℕ) : ℝ)) ^ time n ≤
      (4 * startWeight * targetWeight * proportion) /
        (4 * startWeight * targetWeight * proportion + 8) := by
    rw [← hwidthEq]
    simpa [qpow, width, coefficient] using hsmallN
  have hmass := half_principalScale_le_targetMass
    hcount
    (htime n) (target n) (start n)
    (startWeight := startWeight)
    (targetWeight := targetWeight) (proportion := proportion)
    hstartWeight htargetWeight hproportion (hstart n)
    (htarget n) hcardN hsmallN'
  have hmass' : 2 * startWeight * targetWeight * proportion * qpow n ≤
      ∑ finish ∈ target n,
        (intervalKernel (2 * radius n + 1) ^ time n) (start n) finish := by
    change 2 * startWeight * targetWeight * proportion *
        Real.cos (Real.pi / width n) ^ time n ≤ _
    rw [hwidthEq]
    exact hmass
  have hlowerN' : lowerBound ≤
      2 * startWeight * targetWeight * proportion * qpow n :=
    (le_of_lt hlowerN).trans_eq (by dsimp [coefficient]; ring)
  exact hlowerN'.trans hmass'


end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
