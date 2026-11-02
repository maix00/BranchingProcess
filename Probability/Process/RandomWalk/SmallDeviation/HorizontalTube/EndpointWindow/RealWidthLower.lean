/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.FiniteVarianceLower
import all Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.Lemmas.RealWidthFloor

/-!
# Real-width horizontal-tube endpoint-window lower bounds

## Public declarations

For increments $\xi=(\xi_i)_{i\ge0}$, let
$S_j=\sum_{i=0}^{j-1}\xi_i$ and
\[
 E_{a,D,L,U,V}:=\{\xi:-aD\le S_j\le(1-a)D\ (1\le j\le L),\;
 S_L\in[(U-a)D,(V-a)D]\}.
\]

The public declarations in this file are:

- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.exists_uniform_realWidthHorizontalTubeEndpointWindowProbability_ge_exp`:
  for centered variance-$\sigma^2$ increments, $a\in(0,1)$,
  $0<u<v<1$, and $d>\pi^2\sigma^2/2$, there
  exist $D_0,q_0\in\mathbb N$ such that whenever $D,\gamma>0$,
  $D_0\le\lfloor D\rfloor$, $1/\gamma\le D$,
  $U+\gamma\le u<v\le V-\gamma$, and
  $q_0\lfloor D\rfloor^2\le L$, then
  $\exp\!\left(-\frac{dL}{\lfloor D\rfloor^2}\right)
  \le\mathbb P_\nu(E_{a,D,L,U,V})$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube.exists_uniform_finiteRealWidthTubeProbability_ge_exp`:
  for centered variance-$\sigma^2$ increments, a finite family
  $a_\ell\in(0,1)$, $0<u_\ell<v_\ell<1$, and
  $d>\pi^2\sigma^2/2$, there are common thresholds so that the same bound
  holds simultaneously for every $\ell$ whenever $D,\gamma>0$ and
  $D_0\le\lfloor D\rfloor$, $1/\gamma\le D$,
  $U+\gamma\le u_\ell$ and $v_\ell+\gamma\le V$, and
  $q_0\lfloor D\rfloor^2\le L$:
  $\exp\!\left(-\frac{dL}{\lfloor D\rfloor^2}\right)
  \le\mathbb P_\nu(E_{a_\ell,D,L,U,V})$.

The exponential rate specializes Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.1(ii),
using Theorem 3, Section 4, p. 764 of A. A. Mogul'skii, “Small deviations in
the sample function space,” *Teoriya Veroyatnostei i ee Primeneniya* 19(4)
(1974), 755--765; English translation, “Small Deviations in a Space of
Trajectories,” *Theory of Probability and Its Applications* 19(4) (1975),
726--736, DOI 10.1137/1119081.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

open ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.Stable.Discrete

/-- Uniform exponential lower bound for a real-width tube, with an endpoint
interval containing a fixed strict interior interval. If
$\mathbb E[\xi_0]=0$, $\mathbb E[\xi_0^2]=\sigma^2>0$, and
$d>\pi^2\sigma^2/2$, then there are $D_0,q_0\in\mathbb N$ such that for
$a\in(0,1)$, $0<u<v<1$, and $D,\gamma>0$ with
$D_0\le\lfloor D\rfloor$ and $1/\gamma\le D$, and
$U+\gamma\le u<v\le V-\gamma$ and $q_0\lfloor D\rfloor^2\le L$,
$\exp\!\left(-\frac{dL}{\lfloor D\rfloor^2}\right)
\le\mathbb P_\nu(E_{a,D,L,U,V})$, uniformly
over those widths, endpoints, and horizons. -/
theorem exists_uniform_realWidthHorizontalTubeEndpointWindowProbability_ge_exp
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {sigma d a u v : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2)) (hsigma : 0 < sigma)
    (ha : 0 < a) (haOne : a < 1)
    (hu : 0 < u) (huv : u < v) (hv : v < 1)
    (hd : (Real.pi ^ 2 / 2) * sigma ^ 2 < d) :
    ∃ width₀ ratio₀ : ℕ, ∀ width U V margin : ℝ,
      0 < width → 0 < margin →
      width₀ ≤ ⌊width⌋₊ → 1 / margin ≤ width →
      U + margin ≤ u → v + margin ≤ V →
      ∀ horizon : ℕ,
        ratio₀ * (⌊width⌋₊) ^ 2 ≤ horizon →
        ENNReal.ofReal (Real.exp
          (-d * (horizon : ℝ) / (⌊width⌋₊ : ℝ) ^ 2)) ≤
        horizontalTubeEndpointWindowProbability
          (iidSequenceLaw ν) a width horizon U V := by
  obtain ⟨width₀, ratio₀, hinteger⟩ :=
    HorizontalTube.exists_eventually_horizontalTubeEndpointWindowProbability_ge_exp_uniform
      hν hsigma ha haOne hu huv hv hd
  refine ⟨width₀, ratio₀, ?_⟩
  intro width U V margin hwidth hmargin hwidthFloor hwidthMargin
    hmarginLower hmarginUpper horizon hratio
  have hsource := hinteger ⌊width⌋₊ hwidthFloor horizon hratio
  have hsubset :=
    horizontalTubeEndpointWindowEvent_floor_subset_of_endpointMargins
      hwidth.le ha.le haOne.le hu.le huv.le hv.le
      hmargin hwidthMargin hmarginLower hmarginUpper
      (horizon := horizon)
  exact hsource.trans (measure_mono hsubset)

/-- A maximum of the finitely many integer-width and time-ratio thresholds
works for all spatial bins. Given finitely many $a_\ell\in(0,1)$,
$0<u_\ell<v_\ell<1$, centered variance-$\sigma^2$ increments with
$\sigma>0$, and $d>\pi^2\sigma^2/2$, one pair
$D_0,q_0\in\mathbb N$ gives
$\exp\!\left(-\frac{dL}{\lfloor D\rfloor^2}\right)
\le\mathbb P_\nu(E_{a_\ell,D,L,U,V})$
simultaneously for every $\ell$ whenever $D_0\le\lfloor D\rfloor$,
$1/\gamma\le D$, $U+\gamma\le u_\ell$,
$v_\ell+\gamma\le V$, and $q_0\lfloor D\rfloor^2\le L$. -/
theorem exists_uniform_finiteRealWidthTubeProbability_ge_exp
    {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {sigma d : ℝ} (hν : IsCenteredSecondMoment ν (sigma ^ 2))
    (hsigma : 0 < sigma)
    {m : ℕ} (a u v : Fin m → ℝ)
    (ha : ∀ l, 0 < a l) (haOne : ∀ l, a l < 1)
    (hu : ∀ l, 0 < u l) (huv : ∀ l, u l < v l)
    (hv : ∀ l, v l < 1)
    (hd : (Real.pi ^ 2 / 2) * sigma ^ 2 < d) :
    ∃ width₀ ratio₀ : ℕ,
      ∀ l : Fin m, ∀ width U V margin : ℝ,
        0 < width → 0 < margin →
        width₀ ≤ ⌊width⌋₊ → 1 / margin ≤ width →
        U + margin ≤ u l → v l + margin ≤ V →
        ∀ horizon : ℕ,
          ratio₀ * (⌊width⌋₊) ^ 2 ≤ horizon →
          ENNReal.ofReal (Real.exp
            (-d * (horizon : ℝ) / (⌊width⌋₊ : ℝ) ^ 2)) ≤
          horizontalTubeEndpointWindowProbability
            (iidSequenceLaw ν) (a l) width horizon U V := by
  classical
  have hperBin (l : Fin m) : ∃ width₀ ratio₀ : ℕ,
      ∀ width U V margin : ℝ,
        0 < width → 0 < margin →
        width₀ ≤ ⌊width⌋₊ → 1 / margin ≤ width →
        U + margin ≤ u l → v l + margin ≤ V →
        ∀ horizon : ℕ,
          ratio₀ * (⌊width⌋₊) ^ 2 ≤ horizon →
          ENNReal.ofReal (Real.exp
            (-d * (horizon : ℝ) / (⌊width⌋₊ : ℝ) ^ 2)) ≤
          horizontalTubeEndpointWindowProbability
            (iidSequenceLaw ν) (a l) width horizon U V :=
    exists_uniform_realWidthHorizontalTubeEndpointWindowProbability_ge_exp
      hν hsigma (ha l) (haOne l) (hu l) (huv l) (hv l) hd
  choose widthAt ratioAt hAt using hperBin
  let width₀ := Finset.univ.sup widthAt
  let ratio₀ := Finset.univ.sup ratioAt
  refine ⟨width₀, ratio₀, ?_⟩
  intro l width U V margin hwidth hmargin hwidth₀ hwidthMargin
    hmarginLower hmarginUpper horizon hratio
  have hwidthAt : widthAt l ≤ width₀ :=
    Finset.le_sup (Finset.mem_univ l)
  have hratioAt : ratioAt l ≤ ratio₀ :=
    Finset.le_sup (Finset.mem_univ l)
  apply hAt l width U V margin hwidth hmargin
    (hwidthAt.trans hwidth₀) hwidthMargin
    hmarginLower hmarginUpper horizon
  exact (Nat.mul_le_mul_right _ hratioAt).trans hratio


end ProbabilityTheory.RandomWalk.SmallDeviation.HorizontalTube

end
