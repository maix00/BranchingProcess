/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Target.Central
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Target.Path
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Diffusive.Lower

/-!
# Narrow central endpoint windows

The paired principal modes give a lower bound for each parity-compatible
endpoint window contained in the middle half of a killed interval.  This is
the spectral input needed for the finitely many endpoint bands in the return
argument; a lower bound for the whole central core alone would not imply it.
-/

open MeasureTheory
open scoped BigOperators ENNReal
open Filter Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- A parity-compatible window of `e - 1` terminal sites strictly between
the lattice coordinates `lo` and `lo + 2e`.  The fit hypothesis places the
entire window inside the middle half of the killed interval. -/
def centralEndpointBandTarget (m n lo e : ℕ) (hm : 0 < m)
    (he : 2 ≤ e) (_hlo : 2 * m ≤ lo) (hhi : lo + 2 * e ≤ 6 * m) :
    Finset (Fin (8 * m - 1)) :=
  let start := centralIntervalStart m hm
  let offset := if Even (n + start.val + lo) then 0 else 1
  Finset.univ.image fun j : Fin (e - 1) =>
    (⟨lo + offset + 2 * j.val, by
      have hj := j.isLt
      have hoff : offset ≤ 1 := by dsimp [offset]; split <;> omega
      have hroom : lo + 2 * e ≤ 6 * m := hhi
      omega⟩ : Fin (8 * m - 1))

/-- The left lattice boundary of one of seven endpoint windows.  `spacing`
sets the displacement of consecutive window centers; `windowRadius` is their
independent half-width. -/
def centralEndpointWindowLo (m spacing windowRadius : ℕ) (j : Fin 7) : ℕ :=
  4 * m - (3 * spacing + windowRadius) + j.val * spacing

theorem centralEndpointWindowLo_fits (m spacing windowRadius : ℕ)
    (hfit : 3 * spacing + windowRadius ≤ 2 * m) (j : Fin 7) :
    2 * m ≤ centralEndpointWindowLo m spacing windowRadius j ∧
      centralEndpointWindowLo m spacing windowRadius j + 2 * windowRadius ≤ 6 * m := by
  have hbase : 3 * spacing + windowRadius ≤ 4 * m := by omega
  have hj : j.val ≤ 6 := by omega
  have hjmul : j.val * spacing ≤ 6 * spacing :=
    Nat.mul_le_mul_right spacing hj
  unfold centralEndpointWindowLo
  constructor <;> omega

theorem centralEndpointBandTarget_card (m n lo e : ℕ) (hm : 0 < m)
    (he : 2 ≤ e) (hlo : 2 * m ≤ lo) (hhi : lo + 2 * e ≤ 6 * m) :
    (centralEndpointBandTarget m n lo e hm he hlo hhi).card = e - 1 := by
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
theorem centralEndpointBandTarget_coordinate_mem (m n lo e : ℕ)
    (hm : 0 < m) (he : 2 ≤ e) (hlo : 2 * m ≤ lo)
    (hhi : lo + 2 * e ≤ 6 * m)
    {finish : Fin (8 * m - 1)}
    (hfinish : finish ∈ centralEndpointBandTarget m n lo e hm he hlo hhi) :
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

theorem centralEndpointBandTarget_isCentralCoreStart (m n lo e : ℕ)
    (hm : 0 < m) (he : 2 ≤ e) (hlo : 2 * m ≤ lo)
    (hhi : lo + 2 * e ≤ 6 * m)
    {finish : Fin (8 * m - 1)}
    (hfinish : finish ∈ centralEndpointBandTarget m n lo e hm he hlo hhi) :
    IsCentralCoreStart m finish := by
  have hcoord := centralEndpointBandTarget_coordinate_mem
    m n lo e hm he hlo hhi hfinish
  constructor
  · exact le_trans hlo hcoord.1.le
  · exact le_trans hcoord.2.le hhi

theorem centralEndpointBandTarget_parityCompatible (m n lo e : ℕ)
    (hm : 0 < m) (he : 2 ≤ e) (hlo : 2 * m ≤ lo)
    (hhi : lo + 2 * e ≤ 6 * m) :
    intervalParityCompatibleTarget n (centralIntervalStart m hm)
      (centralEndpointBandTarget m n lo e hm he hlo hhi) =
        centralEndpointBandTarget m n lo e hm he hlo hhi := by
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
theorem centralEndpointBandTargetMass_lower
    (m n lo e : ℕ) (hm : 0 < m) (hn : 0 < n) (he : 2 ≤ e)
    (hlo : 2 * m ≤ lo) (hhi : lo + 2 * e ≤ 6 * m)
    (hsmall : Real.cos (Real.pi / ((8 * m - 1 + 1 : ℕ) : ℝ)) ^ n ≤
      (4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) *
        (((e - 1 : ℕ) : ℝ) / ((8 * m - 1 + 1 : ℕ) : ℝ))) /
      (4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) *
        (((e - 1 : ℕ) : ℝ) / ((8 * m - 1 + 1 : ℕ) : ℝ)) + 8)) :
    (((e - 1 : ℕ) : ℝ) / ((8 * m - 1 + 1 : ℕ) : ℝ)) *
        Real.cos (Real.pi / ((8 * m - 1 + 1 : ℕ) : ℝ)) ^ n ≤
      ∑ finish ∈ centralEndpointBandTarget m n lo e hm he hlo hhi,
        (intervalKernel (8 * m - 1) ^ n)
          (centralIntervalStart m hm) finish := by
  let start := centralIntervalStart m hm
  let target := centralEndpointBandTarget m n lo e hm he hlo hhi
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
      m n lo e hm he hlo hhi hfinishTarget
    exact sqrt_two_div_two_le_intervalSineWeight_of_isCentralCoreStart
      m hm finish hfinishCore
  have hproportion : 0 < proportion := by
    dsimp [proportion]
    apply div_pos
    · exact_mod_cast (Nat.sub_pos_of_lt (by omega : 1 < e))
    · positivity
  have hcard : proportion * ((8 * m - 1 + 1 : ℕ) : ℝ) ≤
      (intervalParityCompatibleTarget n start target).card := by
    rw [centralEndpointBandTarget_parityCompatible m n lo e hm he hlo hhi,
      centralEndpointBandTarget_card m n lo e hm he hlo hhi]
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
theorem eventually_lowerBound_le_centralEndpointBandTargetMass_of_diffusiveRatio
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
          (e n) (hscale n) (he n) (hlo n) (hhi n),
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
          (e n) (hscale n) (he n) (hlo n) (hhi n),
        (intervalKernel (8 * scale n - 1) ^ time n)
          (centralIntervalStart (scale n) (hscale n)) finish := by
    simpa [proportion, power, hden] using hmass
  exact hlower.le.trans hmass'

/-- Uniform spectral lower bounds for seven endpoint windows whose center
spacing and half-width are independent.  Their relative window width may
shrink with the block size, as long as it has a positive limit at each fixed
diffusive parameter. -/
theorem eventually_forall_sevenCentralEndpointWindowTargetMass_lower
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
            (windowRadius n) (hscale n) (hwindow n)
            (centralEndpointWindowLo_fits (scale n) (spacing n)
              (windowRadius n) (hfit n) j).1
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
            (hscale n) (hwindow n) (hloFit n j) (hhiFit n j),
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

/-- The narrow spectral target mass is an actual Rademacher path event. -/
theorem ofReal_centralEndpointBandTargetMass_le_rademacherPathEvent
    (m n lo e : ℕ) (hm : 0 < m) (hn : 0 < n) (he : 2 ≤ e)
    (hlo : 2 * m ≤ lo) (hhi : lo + 2 * e ≤ 6 * m)
    (hsmall : Real.cos (Real.pi / ((8 * m - 1 + 1 : ℕ) : ℝ)) ^ n ≤
      (4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) *
        (((e - 1 : ℕ) : ℝ) / ((8 * m - 1 + 1 : ℕ) : ℝ))) /
      (4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) *
        (((e - 1 : ℕ) : ℝ) / ((8 * m - 1 + 1 : ℕ) : ℝ)) + 8)) :
    ENNReal.ofReal ((((e - 1 : ℕ) : ℝ) / ((8 * m - 1 + 1 : ℕ) : ℝ)) *
        Real.cos (Real.pi / ((8 * m - 1 + 1 : ℕ) : ℝ)) ^ n) ≤
      iidSequenceLaw rademacherMeasure
        {increment : ℕ → ℝ |
          InClosedInterval 1 (8 * (m : ℝ) - 1) n (4 * (m : ℝ)) increment ∧
            4 * (m : ℝ) + AdditivePath.displacement n increment ∈
              intervalSite ''
                (centralEndpointBandTarget m n lo e hm he hlo hhi :
                  Set (Fin (8 * m - 1)))} := by
  let target := centralEndpointBandTarget m n lo e hm he hlo hhi
  have hmass := centralEndpointBandTargetMass_lower
    m n lo e hm hn he hlo hhi hsmall
  have hpath := ofReal_intervalKernel_pow_apply_finset_eq_iidPathEvent
    (8 * m - 1) n (centralIntervalStart m hm) target
  calc
    _ ≤ ENNReal.ofReal
        (∑ finish ∈ target,
          (intervalKernel (8 * m - 1) ^ n)
            (centralIntervalStart m hm) finish) :=
      ENNReal.ofReal_le_ofReal hmass
    _ = iidSequenceLaw rademacherMeasure
        {increment : ℕ → ℝ |
          InClosedInterval 1 (8 * (m : ℝ) - 1) n (4 * (m : ℝ)) increment ∧
            4 * (m : ℝ) + AdditivePath.displacement n increment ∈
              intervalSite '' (target : Set (Fin (8 * m - 1)))} := by
      have hstart : intervalSite (centralIntervalStart m hm) = 4 * (m : ℝ) := by
        dsimp [centralIntervalStart, intervalSite]
        have hNat : 4 * m - 1 + 1 = 4 * m := by omega
        exact_mod_cast hNat
      have hcast : ((8 * m - 1 : ℕ) : ℝ) = 8 * (m : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 8 * m)]
        norm_num
      have hpath' := hpath
      rw [hstart] at hpath'
      rw [← hcast]
      exact hpath'

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

end
