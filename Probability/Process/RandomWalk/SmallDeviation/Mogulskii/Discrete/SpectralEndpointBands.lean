/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Target.Bands
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Discrete.EndpointWindows
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Discrete.DonskerEndpointWindowSequence

/-!
# Spectral estimates for discrete endpoint windows

The finite interval kernel lower bound gives the Rademacher probability of a
strict tube event with an endpoint in a translated open window.  The mesh
spacing and window half-width are kept independent for the later Portmanteau
slack.
-/

open MeasureTheory Filter Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- A central spectral target mass is bounded by the Rademacher tube event
whose endpoint window has the prescribed mesh center and half-width. -/
theorem ofReal_centralEndpointWindowTargetMassSum_le_endpointWindowBlockEvent
    (m n spacing windowRadius : ℕ) (hm : 0 < m) (hwindow : 2 ≤ windowRadius)
    (hfit : 3 * spacing + windowRadius ≤ 2 * m) (j : Fin 7) :
    ENNReal.ofReal
        (∑ finish ∈ centralEndpointBandTarget m n
            (centralEndpointWindowLo m spacing windowRadius j) windowRadius hm
            hwindow (centralEndpointWindowLo_fits m spacing windowRadius hfit j).1
            (centralEndpointWindowLo_fits m spacing windowRadius hfit j).2,
          (intervalKernel (8 * m - 1) ^ n)
            (centralIntervalStart m hm) finish) ≤
      iidSequenceLaw rademacherMeasure
        (endpointWindowBlockEvent (4 * (m : ℝ)) (spacing : ℝ)
          (windowRadius : ℝ) ((j.val : ℤ) - 3) n) := by
  let lo := centralEndpointWindowLo m spacing windowRadius j
  have hfitLo := centralEndpointWindowLo_fits m spacing windowRadius hfit j
  have hstart : intervalSite (centralIntervalStart m hm) = 4 * (m : ℝ) := by
    dsimp [centralIntervalStart, intervalSite]
    have hnat : 4 * m - 1 + 1 = 4 * m := by omega
    exact_mod_cast hnat
  have hsubset :
      {increment : ℕ → ℝ |
        InClosedInterval 1 (8 * (m : ℝ) - 1) n
            (intervalSite (centralIntervalStart m hm)) increment ∧
          intervalSite (centralIntervalStart m hm) +
              AdditivePath.displacement n increment ∈
            intervalSite ''
              (centralEndpointBandTarget m n lo windowRadius hm hwindow
                hfitLo.1 hfitLo.2 : Set (Fin (8 * m - 1)))} ⊆
      endpointWindowBlockEvent (4 * (m : ℝ)) (spacing : ℝ)
        (windowRadius : ℝ) ((j.val : ℤ) - 3) n := by
    intro increment hevent
    let radius : ℕ := 4 * m - 1
    have hradiusReal : (radius : ℝ) + 1 =
        intervalSite (centralIntervalStart m hm) := by
      dsimp [radius]
      rw [hstart]
      have hm4 : 1 ≤ 4 * m := by omega
      rw [Nat.cast_sub hm4]
      push_cast
      ring
    have hupperReal : 2 * (radius : ℝ) + 1 = 8 * (m : ℝ) - 1 := by
      dsimp [radius]
      have hm4 : 1 ≤ 4 * m := by omega
      rw [Nat.cast_sub hm4]
      push_cast
      ring
    have hclosed : InClosedInterval 1 (2 * (radius : ℝ) + 1) n
        ((radius : ℝ) + 1) increment := by
      rw [hupperReal, hradiusReal]
      exact hevent.1
    have htubeSmall :=
      (inClosedInterval_centered_iff_inHorizontalTube radius n increment).mp hclosed
    have hradiusWidth : 2 * (radius : ℝ) = 8 * (m : ℝ) - 2 := by
      dsimp [radius]
      have hm4 : 1 ≤ 4 * m := by omega
      rw [Nat.cast_sub hm4]
      push_cast
      ring
    have htube : InOpenHorizontalTube (1 / 2 : ℝ)
        (8 * (m : ℝ)) n increment := by
      intro k
      have hk := htubeSmall k
      change -(1 / 2 : ℝ) * (2 * (radius : ℝ)) ≤
          AdditivePath.displacement (k + 1) increment ∧
        AdditivePath.displacement (k + 1) increment ≤
          (1 - (1 / 2 : ℝ)) * (2 * (radius : ℝ)) at hk
      change -(1 / 2 : ℝ) * (8 * (m : ℝ)) <
          AdditivePath.displacement (k + 1) increment ∧
        AdditivePath.displacement (k + 1) increment <
          (1 - (1 / 2 : ℝ)) * (8 * (m : ℝ))
      rw [hradiusWidth] at hk
      norm_num at hk ⊢
      constructor <;> linarith
    obtain ⟨finish, hfinish, hend⟩ := hevent.2
    have hcoordinate := centralEndpointBandTarget_coordinate_mem
      m n lo windowRadius hm hwindow hfitLo.1 hfitLo.2 hfinish
    have hfinishSite : intervalSite finish = (finish.val : ℝ) + 1 := by
      simp [intervalSite]
    have hend' : 4 * (m : ℝ) + AdditivePath.displacement n increment =
        (finish.val : ℝ) + 1 := by
      rw [hfinishSite, hstart] at hend
      exact hend.symm
    have hloReal : (lo : ℝ) - 4 * (m : ℝ) =
        ((j.val : ℝ) - 3) * (spacing : ℝ) - (windowRadius : ℝ) := by
      dsimp [lo, centralEndpointWindowLo]
      push_cast
      rw [Nat.cast_sub (by omega : 3 * spacing + windowRadius ≤ 4 * m)]
      push_cast
      ring
    have hhiReal : (lo : ℝ) + 2 * (windowRadius : ℝ) - 4 * (m : ℝ) =
        ((j.val : ℝ) - 3) * (spacing : ℝ) + (windowRadius : ℝ) := by
      calc
        (lo : ℝ) + 2 * (windowRadius : ℝ) - 4 * (m : ℝ) =
            ((lo : ℝ) - 4 * (m : ℝ)) + 2 * (windowRadius : ℝ) := by ring
        _ = (((j.val : ℝ) - 3) * (spacing : ℝ) - (windowRadius : ℝ)) +
            2 * (windowRadius : ℝ) := by rw [hloReal]
        _ = ((j.val : ℝ) - 3) * (spacing : ℝ) + (windowRadius : ℝ) := by ring
    have hcoordinateRealLower : (lo : ℝ) < (finish.val : ℝ) + 1 := by
      exact_mod_cast hcoordinate.1
    have hcoordinateRealUpper : (finish.val : ℝ) + 1 < (lo : ℝ) +
        2 * (windowRadius : ℝ) := by
      exact_mod_cast hcoordinate.2
    have hband : AdditivePath.displacement n increment ∈
        Set.Ioo (((j.val : ℝ) - 3) * (spacing : ℝ) - (windowRadius : ℝ))
          (((j.val : ℝ) - 3) * (spacing : ℝ) + (windowRadius : ℝ)) := by
      constructor
      · linarith [hend', hcoordinateRealLower, hloReal]
      · linarith [hend', hcoordinateRealUpper, hhiReal]
    have hindex : (((j.val : ℤ) - 3 : ℤ) : ℝ) =
        (j.val : ℝ) - 3 := by push_cast; ring
    refine ⟨?_, ?_⟩
    · have hwidth : 2 * (4 * (m : ℝ)) = 8 * (m : ℝ) := by ring
      simpa only [hwidth] using htube
    · simpa only [hindex] using hband
  have hpath := ofReal_intervalKernel_pow_apply_finset_eq_iidPathEvent
    (8 * m - 1) n (centralIntervalStart m hm)
    (centralEndpointBandTarget m n lo windowRadius hm hwindow hfitLo.1 hfitLo.2)
  have hcast : ((8 * m - 1 : ℕ) : ℝ) = 8 * (m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ 8 * m)]
    norm_num
  calc
    _ = iidSequenceLaw rademacherMeasure
        {increment : ℕ → ℝ |
          InClosedInterval 1 (8 * (m : ℝ) - 1) n
              (intervalSite (centralIntervalStart m hm)) increment ∧
            intervalSite (centralIntervalStart m hm) +
                AdditivePath.displacement n increment ∈
              intervalSite ''
                (centralEndpointBandTarget m n lo windowRadius hm hwindow
                  hfitLo.1 hfitLo.2 : Set (Fin (8 * m - 1)))} := by
      have hpath' := hpath
      rw [hcast] at hpath'
      simpa [hstart] using hpath'
    _ ≤ iidSequenceLaw rademacherMeasure
        (endpointWindowBlockEvent (4 * (m : ℝ)) (spacing : ℝ)
          (windowRadius : ℝ) ((j.val : ℤ) - 3) n) := measure_mono hsubset

/-- The seven spectral windows yield a common eventual lower bound for the
Rademacher endpoint-window block probabilities. -/
theorem eventually_forall_sevenRademacherEndpointWindowBlockEvent_ge_of_diffusiveRatio
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
      ENNReal.ofReal lowerBound ≤
        iidSequenceLaw rademacherMeasure
          (endpointWindowBlockEvent (4 * (scale n : ℝ)) (spacing n : ℝ)
            (windowRadius n : ℝ) ((j.val : ℤ) - 3) (time n)) := by
  have hmass := eventually_forall_sevenCentralEndpointWindowTargetMass_lower
    scale time spacing windowRadius hscale htime hwindow hfit hwidth hratio
    hproportion hp hsmallLimit hlowerBound
  filter_upwards [hmass] with n hmass
  intro j
  have hpath := ofReal_centralEndpointWindowTargetMassSum_le_endpointWindowBlockEvent
    (scale n) (time n) (spacing n) (windowRadius n) (hscale n)
    (hwindow n) (hfit n) j
  have hreal : ENNReal.ofReal lowerBound ≤
      ENNReal.ofReal
        (∑ finish ∈ centralEndpointBandTarget (scale n) (time n)
            (centralEndpointWindowLo (scale n) (spacing n) (windowRadius n) j)
            (windowRadius n) (hscale n) (hwindow n)
            (centralEndpointWindowLo_fits (scale n) (spacing n)
              (windowRadius n) (hfit n) j).1
            (centralEndpointWindowLo_fits (scale n) (spacing n)
              (windowRadius n) (hfit n) j).2,
          (intervalKernel (8 * scale n - 1) ^ time n)
            (centralIntervalStart (scale n) (hscale n)) finish) :=
    ENNReal.ofReal_le_ofReal (hmass j)
  exact hreal.trans hpath

/-- The seven raw Rademacher block estimates, expressed in normalized
endpoint-window coordinates along the supplied block-length sequence. -/
theorem eventually_forall_sevenRademacherNormalizedEndpointWindowProbability_ge_of_diffusiveRatio
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
      ENNReal.ofReal lowerBound ≤
        normalizedEndpointWindowProbabilityAlong rademacherMeasure
          (fun n => 4 * (scale n : ℝ) / Real.sqrt (time n))
          (fun n => (spacing n : ℝ) / Real.sqrt (time n))
          (fun n => (windowRadius n : ℝ) / Real.sqrt (time n))
          ((j.val : ℤ) - 3) (fun n => Real.sqrt (time n)) time n := by
  have hraw := eventually_forall_sevenRademacherEndpointWindowBlockEvent_ge_of_diffusiveRatio
    scale time spacing windowRadius hscale htime hwindow hfit hwidth hratio
    hproportion hp hsmallLimit hlowerBound
  filter_upwards [hraw, eventually_gt_atTop 0] with n hrawN hn
  intro j
  have hroot : 0 < Real.sqrt (time n : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast htime n)
  have heq := normalizedEndpointWindowProbabilityAlong_eq_endpointWindowBlockEvent_of_scale
    rademacherMeasure (4 * (scale n : ℝ)) (spacing n : ℝ)
    (windowRadius n : ℝ) ((j.val : ℤ) - 3)
    (fun _ => Real.sqrt (time n : ℝ)) time n hroot
  have heq' : normalizedEndpointWindowProbabilityAlong rademacherMeasure
      (fun k => 4 * (scale k : ℝ) / Real.sqrt (time k))
      (fun k => (spacing k : ℝ) / Real.sqrt (time k))
      (fun k => (windowRadius k : ℝ) / Real.sqrt (time k))
      ((j.val : ℤ) - 3) (fun k => Real.sqrt (time k)) time n =
        iidSequenceLaw rademacherMeasure
          (endpointWindowBlockEvent (4 * (scale n : ℝ)) (spacing n : ℝ)
            (windowRadius n : ℝ) ((j.val : ℤ) - 3) (time n)) := by
    simpa [normalizedEndpointWindowProbabilityAlong] using heq
  rw [heq']
  exact hrawN j

/-- The normalized spectral lower bound indexed by the seven integer return
bands used by the return kernel. -/
theorem eventually_forall_integer_sevenRademacherNormalizedEndpointWindowProbability_ge_of_diffusiveRatio
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
    ∀ᶠ n in atTop, ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      ENNReal.ofReal lowerBound ≤
        normalizedEndpointWindowProbabilityAlong rademacherMeasure
          (fun n => 4 * (scale n : ℝ) / Real.sqrt (time n))
          (fun n => (spacing n : ℝ) / Real.sqrt (time n))
          (fun n => (windowRadius n : ℝ) / Real.sqrt (time n))
          i (fun n => Real.sqrt (time n)) time n := by
  have hseven := eventually_forall_sevenRademacherNormalizedEndpointWindowProbability_ge_of_diffusiveRatio
    scale time spacing windowRadius hscale htime hwindow hfit hwidth hratio
    hproportion hp hsmallLimit hlowerBound
  filter_upwards [hseven] with n hseven
  intro i hi
  have hi' : i ∈ Finset.Icc (-3 : ℤ) 3 := hi
  rcases Finset.mem_Icc.mp hi' with ⟨hiLower, hiUpper⟩
  have hnonneg : 0 ≤ i + 3 := by omega
  have hnat : ((i + 3).toNat : ℤ) = i + 3 :=
    Int.toNat_of_nonneg hnonneg
  let j : Fin 7 := ⟨(i + 3).toNat, by
    have hlt : i + 3 < 7 := by omega
    exact_mod_cast (show (i + 3).toNat < 7 by omega)⟩
  have hj : (j.val : ℤ) - 3 = i := by
    dsimp [j]
    rw [hnat]
    omega
  simpa [hj] using hseven j

/-- Convert the seven Rademacher spectral lower bounds into seven
endpoint-window lower bounds for any centered unit-variance increment law.
The limiting closed/open corridor margins are explicit hypotheses, so this
adapter does not assume that the Brownian corridor boundary is null. -/
theorem eventually_forall_sevenCenteredUnitVarianceEndpointWindowProbability_ge_of_spectralBands
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : IsCenteredUnitSecondMoment ν)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : NNReal → Ω → ℝ}
    (hB : IsPreBrownianReal B P)
    (hcontinuous : ∀ ω, Continuous (B · ω))
    (hmeasurable : ∀ t, Measurable (B t))
    (latticeScale time spacing windowRadius : ℕ → ℕ)
    (hlatticeScale : ∀ n, 0 < latticeScale n)
    (htime : ∀ n, 0 < time n)
    (htimeTop : Tendsto time atTop atTop)
    (hwindow : ∀ n, 2 ≤ windowRadius n)
    (hfit : ∀ n, 3 * spacing n + windowRadius n ≤ 2 * latticeScale n)
    {c p spectralLower applicationLower : ℝ}
    (hwidth : Tendsto (fun n => ((8 * latticeScale n : ℕ) : ℝ)) atTop atTop)
    (hratio : Tendsto (fun n => (time n : ℝ) /
        ((8 * latticeScale n : ℕ) : ℝ) ^ 2) atTop (nhds c))
    (hproportion : Tendsto (fun n => ((windowRadius n - 1 : ℕ) : ℝ) /
        ((8 * latticeScale n : ℕ) : ℝ)) atTop (nhds p))
    (hp : 0 < p)
    (hsmallLimit : Real.exp (c * (-(Real.pi ^ 2) / 2)) <
      (4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) * p) /
        (4 * (Real.sqrt 2 / 2) * (Real.sqrt 2 / 2) * p + 8))
    (hspectralLower : spectralLower <
      p * Real.exp (c * (-(Real.pi ^ 2) / 2)))
    (hlower : 0 ≤ applicationLower)
    (hlowerStrict : applicationLower < spectralLower)
    {closedRadius closedWindow openRadius openWindow meshLimit : ℝ}
    (hclosedRadius : 0 ≤ closedRadius)
    (hclosedOpenRadius : closedRadius < openRadius)
    (hclosedOpenWindow : closedWindow < openWindow)
    (applicationRadius applicationWindow : ℕ → ℝ)
    (hwindowLimit : ∀ i ∈ Finset.Icc (-3 : ℤ) 3, ∀ᶠ n in atTop,
      4 * (latticeScale n : ℝ) / Real.sqrt (time n) ≤ closedRadius ∧
        (i : ℝ) * ((spacing n : ℝ) / Real.sqrt (time n)) -
            (windowRadius n : ℝ) / Real.sqrt (time n) ≥
          (i : ℝ) * meshLimit - closedWindow ∧
        (i : ℝ) * ((spacing n : ℝ) / Real.sqrt (time n)) +
            (windowRadius n : ℝ) / Real.sqrt (time n) ≤
          (i : ℝ) * meshLimit + closedWindow)
    (happlicationContainsOpen : ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      ∀ᶠ n in atTop,
        openRadius ≤ applicationRadius n ∧
          (i : ℝ) * ((spacing n : ℝ) / Real.sqrt (time n)) -
              applicationWindow n ≤
            (i : ℝ) * meshLimit - openWindow ∧
          (i : ℝ) * meshLimit + openWindow ≤
          (i : ℝ) * ((spacing n : ℝ) / Real.sqrt (time n)) +
              applicationWindow n) :
    ∀ᶠ n in atTop, ∀ i ∈ Finset.Icc (-3 : ℤ) 3,
      ENNReal.ofReal applicationLower ≤
        normalizedEndpointWindowProbabilityAlong ν applicationRadius
          (fun n => (spacing n : ℝ) / Real.sqrt (time n)) applicationWindow
          i (fun n => Real.sqrt (time n)) time n := by
  have hrademacher : IsCenteredUnitSecondMoment rademacherMeasure := by
    constructor <;> rw [integral_rademacherMeasure] <;> norm_num
  let limit : Ω → CadlagPath unitInterval ℝ :=
    Skorokhod.ofContinuousMap ∘ continuousunitIntervalPath B hcontinuous
  have hscalePositive : ∀ n, 0 < Real.sqrt (time n : ℝ) := by
    intro n
    exact Real.sqrt_pos.2 (by exact_mod_cast htime n)
  have hRademacher := tendstoInDistribution_normalizedStepCadlagPathIcc_brownian_along
    rademacherMeasure hrademacher hB hcontinuous hmeasurable time htimeTop
  have hνDonsker := tendstoInDistribution_normalizedStepCadlagPathIcc_brownian_along
    ν hν hB hcontinuous hmeasurable time htimeTop
  have hspectral :=
    eventually_forall_integer_sevenRademacherNormalizedEndpointWindowProbability_ge_of_diffusiveRatio
      latticeScale time spacing windowRadius hlatticeScale htime hwindow hfit
      hwidth hratio hproportion hp hsmallLimit hspectralLower
  exact eventually_forall_seven_ofReal_le_normalizedEndpointWindowProbabilityAlong_of_spectralLower
    P ν (fun n => Real.sqrt (time n)) time
    (Filter.Eventually.of_forall hscalePositive)
    (htimeTop.eventually_gt_atTop 0) limit hRademacher hνDonsker
    (fun n => 4 * (latticeScale n : ℝ) / Real.sqrt (time n))
    (fun n => (spacing n : ℝ) / Real.sqrt (time n))
    (fun n => (windowRadius n : ℝ) / Real.sqrt (time n))
    applicationRadius applicationWindow hlower hlowerStrict hclosedRadius
    hclosedOpenRadius hclosedOpenWindow hwindowLimit happlicationContainsOpen
    hspectral

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

end
