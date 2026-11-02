/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.Process.RandomWalk.Rademacher.FiniteInterval.Spectral.Target.LowerBound
import Probability.Process.RandomWalk.Rademacher.FiniteInterval.Spectral.Survival.Lower

/-!
# Spectral mass bounds for central endpoint bands

For an interval kernel on $\{0,\ldots,8m-2\}$, this module constructs the
parity-compatible sites inside a lattice endpoint band and estimates their
transition mass from the center. The band may be placed anywhere in the
central region; its location and width need not come from a fixed finite
window family.

## Internal proof declarations

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.centralIntervalStart` defines the midpoint $4m-1$ of the interval with
  $8m-1$ interior sites, and `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.IsCentralCoreStart` records the central
  region $2m\le x.val+1\le6m$. The theorem
  `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.centralIntervalStart_isCentralCoreStart` places the midpoint there, and
  `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.sqrt_two_div_two_le_intervalSineWeight_of_isCentralCoreStart` gives
  $\sqrt{2}/2\le\phi_m(x)$ for every site in the region, where
  $\phi_m(x)=\sin(\pi(x.val+1)/(8m))$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.centralEndpointBandTarget`: the $e-1$ sites in $(\ell,\ell+2e)$ with
  parity reachable from the center after $n$ steps.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.centralEndpointBandTarget_card` and `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.centralEndpointBandTarget_coordinate_mem`:
  the target has cardinality $e-1$ and lies strictly inside its prescribed
  endpoint band.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.centralEndpointBandTarget_isCentralCoreStart` and
  `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.centralEndpointBandTarget_parityCompatible`: under the central-region
  bounds, its sites lie in the central core and are already parity-compatible.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.centralEndpointBandTargetMass_lower`: writing $K_m=\texttt{intervalKernel}(8m-1)$,
  $x_m=\texttt{centralIntervalStart}(m)$, and
  $p=(e-1)/(8m)$, the spectral condition
  $\cos^n(\pi/(8m))\le p/(p+4)$ gives
  $p\cos^n(\pi/(8m))\le\sum_{y\in B}K_m^n(x_m,y)$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.eventually_lowerBound_le_centralEndpointBandTargetMass_of_diffusiveRatio`:
  if the interval width tends to infinity, $n/W_n^2\to c$, and the target
  proportion tends to $p>0$, every strict lower constant below
  $p e^{-c\pi^2/2}$ eventually bounds the target mass.
The finite-target spectral estimate used here is the general
`half_principalScale_le_targetMass` in
`Probability.Process.RandomWalk.Rademacher.FiniteInterval.Spectral.Target.LowerBound`.
The endpoint-band specialization supplies the finite-block input for the
seven-window argument used in Lemma 3(d) of A. A. Mogul'skii, “Small
Deviations in the Sample Function Space,” *Teoriya Veroyatnostei i ee
Primeneniya* 19(4) (1974), 755--765; English translation, “Small Deviations
in a Space of Trajectories,” *Theory of Probability and Its Applications*
19(4) (1975), 726--736, DOI 10.1137/1119081.
-/

open scoped BigOperators
open Filter Topology

open ProbabilityTheory.RandomWalk.Rademacher.FiniteInterval

section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

open ProbabilityTheory.RandomWalk.Rademacher

/-- A central starting site in an interval with Dirichlet width `8 * m`. -/
def centralIntervalStart (m : ℕ) (hm : 0 < m) : Fin (8 * m - 1) :=
  ⟨4 * m - 1, by omega⟩

/-- A starting site belongs to the central core when its physical lattice
coordinate lies between one quarter and three quarters of the interval. -/
def IsCentralCoreStart (m : ℕ) (start : Fin (8 * m - 1)) : Prop :=
  2 * m ≤ start.val + 1 ∧ start.val + 1 ≤ 6 * m

/-- Sine on the middle half of the Dirichlet interval is bounded below by
the value at a quarter turn. -/
private lemma sqrt_two_div_two_le_sin_of_mem_middle_thirds {x : ℝ}
    (hx₁ : Real.pi / 4 ≤ x) (hx₂ : x ≤ 3 * Real.pi / 4) :
    Real.sqrt 2 / 2 ≤ Real.sin x := by
  rcases le_total x (Real.pi / 2) with hx | hx
  · rw [← Real.sin_pi_div_four]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos]) hx hx₁
  · calc
      Real.sqrt 2 / 2 = Real.sin (Real.pi / 4) := Real.sin_pi_div_four.symm
      _ ≤ Real.sin (Real.pi - x) :=
        Real.sin_le_sin_of_le_of_le_pi_div_two
          (by linarith [Real.pi_pos]) (by linarith) (by linarith)
      _ = Real.sin x := Real.sin_pi_sub x

/-- Every central-core starting site has a uniformly positive ground-state
weight. -/
lemma sqrt_two_div_two_le_intervalSineWeight_of_isCentralCoreStart
    (m : ℕ) (hm : 0 < m) (start : Fin (8 * m - 1))
    (hcore : IsCentralCoreStart m start) :
    Real.sqrt 2 / 2 ≤ intervalSineWeight (8 * m - 1) start := by
  rw [intervalSineWeight, dirichletSine]
  have hwidth : ((8 * m - 1 + 1 : ℕ) : ℝ) = 8 * (m : ℝ) := by
    have hNat : 8 * m - 1 + 1 = 8 * m := by omega
    exact_mod_cast hNat
  have hlow : (Real.pi / 4) ≤
      (Real.pi / (8 * (m : ℝ))) * ((start.val + 1 : ℕ) : ℝ) := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * (m : ℝ))).2
    have hlowCast : (2 * m : ℕ) ≤ start.val + 1 := hcore.1
    have hmul := mul_le_mul_of_nonneg_left
      (show (2 * (m : ℝ)) ≤ ((start.val + 1 : ℕ) : ℝ) by exact_mod_cast hlowCast)
      Real.pi_pos.le
    nlinarith [hmul]
  have hupp :
      (Real.pi / (8 * (m : ℝ))) * ((start.val + 1 : ℕ) : ℝ) ≤
        3 * Real.pi / 4 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * (m : ℝ))).2
    have huppCast : ((start.val + 1 : ℕ) : ℝ) ≤ 6 * (m : ℝ) := by
      exact_mod_cast hcore.2
    have hmul := mul_le_mul_of_nonneg_left huppCast Real.pi_pos.le
    nlinarith [hmul]
  rw [hwidth]
  exact sqrt_two_div_two_le_sin_of_mem_middle_thirds hlow hupp

/-- The central lattice site is itself in the central core. -/
lemma centralIntervalStart_isCentralCoreStart (m : ℕ) (hm : 0 < m) :
    IsCentralCoreStart m (centralIntervalStart m hm) := by
  unfold IsCentralCoreStart centralIntervalStart
  change 2 * m ≤ (4 * m - 1) + 1 ∧ (4 * m - 1) + 1 ≤ 6 * m
  constructor <;> omega


/-- A parity-compatible window of `e - 1` terminal sites strictly between
the lattice coordinates `lo` and `lo + 2e`.  The fit hypothesis places the
entire window inside the middle half of the killed interval. -/
def centralEndpointBandTarget (m n lo e : ℕ) (hm : 0 < m)
    (hhi : lo + 2 * e ≤ 6 * m) :
    Finset (Fin (8 * m - 1)) :=
  let start := centralIntervalStart m hm
  let offset := if Even (n + start.val + lo) then 0 else 1
  Finset.univ.image fun j : Fin (e - 1) =>
    (⟨lo + offset + 2 * j.val, by
      have hj := j.isLt
      have hoff : offset ≤ 1 := by dsimp [offset]; split <;> omega
      have hroom : lo + 2 * e ≤ 6 * m := hhi
      omega⟩ : Fin (8 * m - 1))

lemma centralEndpointBandTarget_card (m n lo e : ℕ) (hm : 0 < m)
    (hhi : lo + 2 * e ≤ 6 * m) :
    (centralEndpointBandTarget m n lo e hm hhi).card = e - 1 := by
  classical
  unfold centralEndpointBandTarget
  rw [Finset.card_image_of_injOn]
  · simp
  · intro i _ j _ hij
    apply Fin.ext
    have hval := congrArg Fin.val hij
    dsimp at hval
    omega

/-- Coordinates of a target site lie strictly inside the prescribed real
lattice window. -/
lemma centralEndpointBandTarget_coordinate_mem (m n lo e : ℕ)
    (hm : 0 < m) (hhi : lo + 2 * e ≤ 6 * m)
    {finish : Fin (8 * m - 1)}
    (hfinish : finish ∈ centralEndpointBandTarget m n lo e hm hhi) :
    lo < finish.val + 1 ∧ finish.val + 1 < lo + 2 * e := by
  classical
  unfold centralEndpointBandTarget at hfinish
  simp only [Finset.mem_image, Finset.mem_univ, true_and] at hfinish
  obtain ⟨j, hfinish⟩ := hfinish
  have hval := congrArg Fin.val hfinish
  dsimp at hval
  have hj := j.isLt
  have hoff : (if Even (n + (centralIntervalStart m hm).val + lo)
      then 0 else 1) ≤ 1 := by split <;> omega
  constructor
  · rw [← hval]
    omega
  · rw [← hval]
    omega

lemma centralEndpointBandTarget_isCentralCoreStart (m n lo e : ℕ)
    (hm : 0 < m) (hlo : 2 * m ≤ lo)
    (hhi : lo + 2 * e ≤ 6 * m)
    {finish : Fin (8 * m - 1)}
    (hfinish : finish ∈ centralEndpointBandTarget m n lo e hm hhi) :
    IsCentralCoreStart m finish := by
  have hcoord := centralEndpointBandTarget_coordinate_mem
    m n lo e hm hhi hfinish
  constructor
  · exact le_trans hlo hcoord.1.le
  · exact le_trans hcoord.2.le hhi

lemma centralEndpointBandTarget_parityCompatible (m n lo e : ℕ)
    (hm : 0 < m) (hhi : lo + 2 * e ≤ 6 * m) :
    intervalParityCompatibleTarget n (centralIntervalStart m hm)
      (centralEndpointBandTarget m n lo e hm hhi) =
        centralEndpointBandTarget m n lo e hm hhi := by
  classical
  ext finish
  simp only [intervalParityCompatibleTarget, Finset.mem_filter]
  constructor
  · exact And.left
  · intro hfinish
    refine ⟨hfinish, ?_⟩
    unfold centralEndpointBandTarget at hfinish
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hfinish
    obtain ⟨j, hfinish⟩ := hfinish
    have hval := congrArg Fin.val hfinish
    dsimp at hval
    rw [← hval]
    change Even (n + (4 * m - 1) +
      (lo + (if Even (n + (4 * m - 1) + lo) then 0 else 1) + 2 * j.val))
    by_cases heven : Even (n + (4 * m - 1) + lo)
    · simp [heven]
      rcases heven with ⟨k, hk⟩
      refine ⟨k + j.val, ?_⟩
      omega
    · have hodd : Odd (n + (4 * m - 1) + lo) := Nat.not_even_iff_odd.mp heven
      simp [heven]
      rcases hodd with ⟨k, hk⟩
      refine ⟨k + j.val + 1, ?_⟩
      omega

/-- Spectral lower bound for a narrow, parity-compatible endpoint window
inside the central part of the interval.  Its prefactor is the window's
relative lattice width, so it remains large enough when the relative width
shrinks subexponentially in the block parameter. -/
lemma centralEndpointBandTargetMass_lower
    (m n lo e : ℕ) (hm : 0 < m) (hn : 0 < n) (he : 2 ≤ e)
    (hlo : 2 * m ≤ lo) (hhi : lo + 2 * e ≤ 6 * m)
    (hsmall : Real.cos (Real.pi / ((8 * m - 1 + 1 : ℕ) : ℝ)) ^ n ≤
      (4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) *
        (((e - 1 : ℕ) : ℝ) / ((8 * m - 1 + 1 : ℕ) : ℝ))) /
      (4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) *
        (((e - 1 : ℕ) : ℝ) / ((8 * m - 1 + 1 : ℕ) : ℝ)) + 8)) :
    (((e - 1 : ℕ) : ℝ) / ((8 * m - 1 + 1 : ℕ) : ℝ)) *
        Real.cos (Real.pi / ((8 * m - 1 + 1 : ℕ) : ℝ)) ^ n ≤
        ∑ finish ∈ centralEndpointBandTarget m n lo e hm hhi,
        (intervalKernel (8 * m - 1) ^ n)
          (centralIntervalStart m hm) finish := by
  let start := centralIntervalStart m hm
  let target := centralEndpointBandTarget m n lo e hm hhi
  let weight : ℝ := Real.sqrt 2 / 2
  let proportion : ℝ := ((e - 1 : ℕ) : ℝ) / ((8 * m - 1 + 1 : ℕ) : ℝ)
  have hcount : 1 < 8 * m - 1 := by omega
  have hwidth : ((8 * m - 1 + 1 : ℕ) : ℝ) = 8 * (m : ℝ) := by
    have hNat : 8 * m - 1 + 1 = 8 * m := by omega
    exact_mod_cast hNat
  have hstartCore : IsCentralCoreStart m start :=
    centralIntervalStart_isCentralCoreStart m hm
  have hstartWeight : weight ≤ intervalSineWeight (8 * m - 1) start :=
    sqrt_two_div_two_le_intervalSineWeight_of_isCentralCoreStart
      m hm start hstartCore
  have htargetWeight : ∀ finish ∈ intervalParityCompatibleTarget n start target,
      weight ≤ intervalSineWeight (8 * m - 1) finish := by
    intro finish hfinish
    have hfinishTarget : finish ∈ target :=
      (Finset.mem_filter.mp hfinish).1
    have hfinishCore := centralEndpointBandTarget_isCentralCoreStart
      m n lo e hm hlo hhi hfinishTarget
    exact sqrt_two_div_two_le_intervalSineWeight_of_isCentralCoreStart
      m hm finish hfinishCore
  have hproportion : 0 < proportion := by
    dsimp [proportion]
    apply div_pos
    · exact_mod_cast (Nat.sub_pos_of_lt (by omega : 1 < e))
    · positivity
  have hcard : proportion * ((8 * m - 1 + 1 : ℕ) : ℝ) ≤
      (intervalParityCompatibleTarget n start target).card := by
    rw [centralEndpointBandTarget_parityCompatible m n lo e hm hhi,
      centralEndpointBandTarget_card m n lo e hm hhi]
    calc
      proportion * ((8 * m - 1 + 1 : ℕ) : ℝ) = ((e - 1 : ℕ) : ℝ) := by
        dsimp [proportion]
        field_simp
      _ ≤ ((e - 1 : ℕ) : ℝ) := le_rfl
  have hsmall' : Real.cos
      (Real.pi / ((8 * m - 1 + 1 : ℕ) : ℝ)) ^ n ≤
      (4 * weight * weight * proportion) / (4 * weight * weight * proportion + 8) := by
    simpa [weight, proportion] using hsmall
  have hprincipal := half_principalScale_le_targetMass hcount hn
    target start (startWeight := weight) (targetWeight := weight)
    (proportion := proportion) (by positivity) (by positivity)
    hproportion hstartWeight htargetWeight hcard hsmall'
  have hsquare : (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) = 1 / 2 := by
    have hsquare' : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
    nlinarith [hsquare']
  have hcoef : 2 * weight * weight = 1 := by
    calc
      2 * weight * weight = 2 * (weight * weight) := by ring
      _ = 2 * (1 / 2) := by rw [show weight * weight = 1 / 2 by
        dsimp [weight]
        exact hsquare]
      _ = 1 := by norm_num
  rw [hcoef] at hprincipal
  simpa [proportion, target] using hprincipal

/-- A shrinking endpoint window still has a uniform spectral lower bound when
its relative width converges to a positive value.  The only asymptotic input
is the diffusive time-to-width ratio and the strict inequality saying that
the principal eigenvalue limit is below the limiting spectral threshold. -/
lemma eventually_lowerBound_le_centralEndpointBandTargetMass_of_diffusiveRatio
    (scale time lo e : ℕ → ℕ) {c p lowerBound : ℝ}
    (hscale : ∀ n, 0 < scale n) (htime : ∀ n, 0 < time n)
    (he : ∀ n, 2 ≤ e n)
    (hlo : ∀ n, 2 * scale n ≤ lo n)
    (hhi : ∀ n, lo n + 2 * e n ≤ 6 * scale n)
    (hwidth : Tendsto (fun n => ((8 * scale n : ℕ) : ℝ)) atTop atTop)
    (hratio : Tendsto (fun n => (time n : ℝ) /
        ((8 * scale n : ℕ) : ℝ) ^ 2) atTop (nhds c))
    (hproportion : Tendsto (fun n => ((e n - 1 : ℕ) : ℝ) /
        ((8 * scale n : ℕ) : ℝ)) atTop (nhds p))
    (hp : 0 < p)
    (hsmallLimit : Real.exp (c * (-(Real.pi ^ 2) / 2)) <
      (4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) * p) /
        (4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) * p + 8))
    (hlowerBound : lowerBound < p *
      Real.exp (c * (-(Real.pi ^ 2) / 2))) :
    ∀ᶠ n in atTop, lowerBound ≤
      ∑ finish ∈ centralEndpointBandTarget (scale n) (time n) (lo n)
          (e n) (hscale n) (hhi n),
        (intervalKernel (8 * scale n - 1) ^ time n)
          (centralIntervalStart (scale n) (hscale n)) finish := by
  let radius : ℕ → ℕ := fun n => 4 * scale n - 1
  have hradius : ∀ n, 0 < radius n := by
    intro n
    have hm := hscale n
    dsimp [radius]
    omega
  have hwidthEqNat (n : ℕ) : 2 * (radius n + 1) = 8 * scale n := by
    have hm := hscale n
    dsimp [radius]
    omega
  have hwidthRadius : Tendsto
      (fun n => ((2 * (radius n + 1) : ℕ) : ℝ)) atTop atTop := by
    refine hwidth.congr' ?_
    filter_upwards with n
    exact_mod_cast (hwidthEqNat n).symm
  have hratioRadius : Tendsto
      (fun n => (time n : ℝ) /
        ((2 * (radius n + 1) : ℕ) : ℝ) ^ 2) atTop (nhds c) := by
    refine hratio.congr' ?_
    filter_upwards with n
    rw [show ((2 * (radius n + 1) : ℕ) : ℝ) =
      ((8 * scale n : ℕ) : ℝ) by exact_mod_cast hwidthEqNat n]
  let power : ℕ → ℝ := fun n =>
    Real.cos (Real.pi / ((8 * scale n : ℕ) : ℝ)) ^ time n
  have hpower : Tendsto power atTop
      (nhds (Real.exp (c * (-(Real.pi ^ 2) / 2)))) := by
    have h := tendsto_centeredPrincipalPower_of_diffusiveRatio
      radius time c hradius hwidthRadius hratioRadius
    have hwidthEq (n : ℕ) : ((2 * (radius n + 1) : ℕ) : ℝ) =
        ((8 * scale n : ℕ) : ℝ) := by exact_mod_cast hwidthEqNat n
    simpa [power, hwidthEq] using h
  let proportion : ℕ → ℝ := fun n =>
    ((e n - 1 : ℕ) : ℝ) / ((8 * scale n : ℕ) : ℝ)
  let weight : ℝ := Real.sqrt 2 / 2
  let threshold : ℝ → ℝ := fun x =>
    (4 * weight * weight * x) / (4 * weight * weight * x + 8)
  have hthresholdTendsto : Tendsto (fun n => threshold (proportion n))
      atTop (nhds (threshold p)) := by
    have hnum : Tendsto (fun n => 4 * weight * weight * proportion n)
        atTop (nhds (4 * weight * weight * p)) := by
      have hconst : Tendsto (fun _ : ℕ => (4 * weight * weight)) atTop
          (nhds (4 * weight * weight)) := tendsto_const_nhds
      exact hconst.mul hproportion
    have hden : Tendsto (fun n => 4 * weight * weight * proportion n + 8)
        atTop (nhds (4 * weight * weight * p + 8)) := by
      simpa using (hnum.add_const 8)
    have hquot := hnum.div hden (by positivity)
    change Tendsto (fun n =>
      (4 * weight * weight * proportion n) /
        (4 * weight * weight * proportion n + 8)) atTop _
    exact hquot
  have hthresholdLimit :
      Real.exp (c * (-(Real.pi ^ 2) / 2)) < threshold p := by
    simpa [threshold, weight] using hsmallLimit
  let midpoint : ℝ :=
    (Real.exp (c * (-(Real.pi ^ 2) / 2)) + threshold p) / 2
  have hpowerEventually : ∀ᶠ n in atTop, power n < midpoint := by
    exact hpower.eventually
      (eventually_lt_nhds (by dsimp [midpoint]; linarith))
  have hthresholdEventually : ∀ᶠ n in atTop, midpoint < threshold (proportion n) := by
    exact hthresholdTendsto.eventually
      (eventually_gt_nhds (by dsimp [midpoint]; linarith))
  have hproduct : Tendsto (fun n => proportion n * power n) atTop
      (nhds (p * Real.exp (c * (-(Real.pi ^ 2) / 2)))) :=
    hproportion.mul hpower
  have hlowerEventually : ∀ᶠ n in atTop,
      lowerBound < proportion n * power n :=
    hproduct.eventually (eventually_gt_nhds hlowerBound)
  filter_upwards [hpowerEventually, hthresholdEventually, hlowerEventually]
      with n hpow hthreshold hlower
  have hden : ((8 * scale n - 1 + 1 : ℕ) : ℝ) =
      ((8 * scale n : ℕ) : ℝ) := by
    have hn : 8 * scale n - 1 + 1 = 8 * scale n := by
      have hm := hscale n
      omega
    exact_mod_cast hn
  have hdenExpr : ((8 * scale n : ℕ) : ℝ) =
      ((8 * scale n - 1 : ℕ) : ℝ) + 1 := by
    rw [Nat.cast_sub (by have hm := hscale n; omega : 1 ≤ 8 * scale n)]
    push_cast
    norm_num
  have hproportionEq :
      (((e n - 1 : ℕ) : ℝ) / ((8 * scale n : ℕ) : ℝ)) =
        ((e n - 1 : ℕ) : ℝ) /
          (((8 * scale n - 1 : ℕ) : ℝ) + 1) := by
    rw [hdenExpr]
  have hproportionEq' :
      (((e n - 1 : ℕ) : ℝ) / ((8 * scale n : ℕ) : ℝ)) =
        ((e n - 1 : ℕ) : ℝ) /
          ((8 * scale n - 1 + 1 : ℕ) : ℝ) := by
    rw [hden]
  have hsmallN : Real.cos
      (Real.pi / ((8 * scale n - 1 + 1 : ℕ) : ℝ)) ^ time n ≤
      (4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) * proportion n) /
        (4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) * proportion n + 8) := by
    have hsmallProportion : power n ≤ threshold (proportion n) := by
      dsimp [threshold]
      exact le_of_lt (hpow.trans hthreshold)
    have hsmallProportion : power n ≤
        (4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) * proportion n) /
          (4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) * proportion n + 8) := by
      simpa [weight] using hsmallProportion
    rw [hden]
    simpa [power, proportion] using hsmallProportion
  have hsmallN' : Real.cos
      (Real.pi / ((8 * scale n - 1 + 1 : ℕ) : ℝ)) ^ time n ≤
      (4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) *
        (((e n - 1 : ℕ) : ℝ) / ((8 * scale n - 1 + 1 : ℕ) : ℝ))) /
      (4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) *
        (((e n - 1 : ℕ) : ℝ) / ((8 * scale n - 1 + 1 : ℕ) : ℝ)) + 8) := by
    calc
      _ ≤ (4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) *
          (((e n - 1 : ℕ) : ℝ) / ((8 * scale n : ℕ) : ℝ))) /
          (4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) *
          (((e n - 1 : ℕ) : ℝ) / ((8 * scale n : ℕ) : ℝ)) + 8) := by
        simpa [proportion] using hsmallN
      _ = _ := by
        exact congrArg (fun x : ℝ =>
          (4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) * x) /
            (4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) * x + 8))
          hproportionEq'
  have hmass := centralEndpointBandTargetMass_lower
    (scale n) (time n) (lo n) (e n) (hscale n) (htime n) (he n)
    (hlo n) (hhi n) hsmallN'
  have hmass' : proportion n * power n ≤
      ∑ finish ∈ centralEndpointBandTarget (scale n) (time n) (lo n)
          (e n) (hscale n) (hhi n),
        (intervalKernel (8 * scale n - 1) ^ time n)
          (centralIntervalStart (scale n) (hscale n)) finish := by
    simpa [proportion, power, hden] using hmass
  exact hlower.le.trans hmass'

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

end
