/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Target.Central
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Target.Path

/-!
# Central spectral targets as horizontal-tube events

The finite Dirichlet target mass for a centered Rademacher walk is a lower
bound for the corresponding closed horizontal tube with its endpoint in the
central core. This is the discrete event needed before applying closed-set
Portmanteau to obtain Brownian endpoint-band mass.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- The central spectral target mass is a lower bound for the Rademacher
walk's closed-interval return event, uniformly over every starting site in
the central core. This is the row estimate needed before taking a diffusive
limit; the centered horizontal-tube estimate below is its special case. -/
theorem ofReal_centralCoreTarget_le_rademacherCoreReturnProbability
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (start : Fin (8 * m - 1))
    (hcore : IsCentralCoreStart m start)
    (hsmall : Real.cos (Real.pi / (8 * (m : ℝ))) ^ n ≤ 1 / 17) :
    ENNReal.ofReal ((1 / 4 : ℝ) *
        Real.cos (Real.pi / (8 * (m : ℝ))) ^ n) ≤
      iidSequenceLaw rademacherMeasure
        {increment : ℕ → ℝ |
          InClosedInterval 1 (8 * (m : ℝ) - 1) n
              (intervalSite start) increment ∧
            intervalSite start + AdditivePath.displacement n increment ∈
              intervalSite ''
                (centralParityTarget m n hm start : Set (Fin (8 * m - 1)))} := by
  have hmass := centralCoreTargetMass_lower m n hm hn start hcore hsmall
  have hpath := ofReal_intervalKernel_pow_apply_finset_eq_iidPathEvent
    (8 * m - 1) n start (centralParityTarget m n hm start)
  calc
    _ ≤ ENNReal.ofReal
        (∑ finish ∈ centralParityTarget m n hm start,
          (intervalKernel (8 * m - 1) ^ n) start finish) :=
      ENNReal.ofReal_le_ofReal hmass
    _ = iidSequenceLaw rademacherMeasure
        {increment : ℕ → ℝ |
          InClosedInterval 1 (8 * (m : ℝ) - 1) n
              (intervalSite start) increment ∧
            intervalSite start + AdditivePath.displacement n increment ∈
              intervalSite ''
                (centralParityTarget m n hm start : Set (Fin (8 * m - 1)))} := by
      have hcast : ((8 * m - 1 : ℕ) : ℝ) = 8 * (m : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 8 * m)]
        norm_num
      rw [← hcast]
      exact hpath

/-- The centered-core spectral target is contained in the width-`8m`
horizontal tube and has normalized endpoint in the central quarter. -/
theorem ofReal_centralCoreTarget_le_rademacherTubeEndpointProbability
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (hsmall : Real.cos (Real.pi / (8 * (m : ℝ))) ^ n ≤ 1 / 17) :
    ENNReal.ofReal ((1 / 4 : ℝ) *
        Real.cos (Real.pi / (8 * (m : ℝ))) ^ n) ≤
      iidSequenceLaw rademacherMeasure
        {increment | InHorizontalTube (1 / 2) (8 * (m : ℝ)) n increment ∧
          AdditivePath.displacement n increment / (8 * (m : ℝ)) ∈
            Set.Icc (-(1 / 4 : ℝ)) (1 / 4)} := by
  let start := centralIntervalStart m hm
  let target := centralParityTarget m n hm start
  have hmass := centralCoreTargetMass_lower m n hm hn start
    (centralIntervalStart_isCentralCoreStart m hm) hsmall
  have hpath := ofReal_intervalKernel_pow_apply_finset_eq_iidPathEvent
    (8 * m - 1) n start target
  have hsubset :
      {increment : ℕ → ℝ |
        InClosedInterval 1 (8 * (m : ℝ) - 1) n
          (intervalSite start) increment ∧
          intervalSite start + AdditivePath.displacement n increment ∈
            intervalSite '' (target : Set (Fin (8 * m - 1)))} ⊆
      {increment : ℕ → ℝ |
        InHorizontalTube (1 / 2) (8 * (m : ℝ)) n increment ∧
          AdditivePath.displacement n increment / (8 * (m : ℝ)) ∈
            Set.Icc (-(1 / 4 : ℝ)) (1 / 4)} := by
    intro increment h
    have hstartSite : intervalSite start = 4 * (m : ℝ) := by
      dsimp [start, centralIntervalStart, intervalSite]
      have hnat : 4 * m - 1 + 1 = 4 * m := by omega
      exact_mod_cast hnat
    let radius : ℕ := 4 * m - 1
    have hradiusReal : (radius : ℝ) = 4 * (m : ℝ) - 1 := by
      dsimp [radius]
      have hm4 : 1 ≤ 4 * m := by omega
      rw [Nat.cast_sub hm4]
      push_cast
      ring
    have hupperReal : 2 * (radius : ℝ) + 1 = 8 * (m : ℝ) - 1 := by
      rw [hradiusReal]
      ring
    have hinitial : (radius : ℝ) + 1 = intervalSite start := by
      rw [hradiusReal, hstartSite]
      ring
    have hclosed : InClosedInterval 1 (2 * (radius : ℝ) + 1) n
        ((radius : ℝ) + 1) increment := by
      rw [hupperReal, hinitial]
      exact h.1
    have htubeSmall :=
      (inClosedInterval_centered_iff_inHorizontalTube radius n
        increment).mp hclosed
    have htube : InHorizontalTube (1 / 2) (8 * (m : ℝ)) n increment := by
      have hwidth : (2 * (radius : ℝ)) ≤ 8 * (m : ℝ) := by
        rw [hradiusReal]
        linarith
      exact (inHorizontalTube_mono_width (by norm_num) (by norm_num)
        hwidth) htubeSmall
    have htargetMem : intervalSite start + AdditivePath.displacement n increment ∈
        intervalSite '' (target : Set (Fin (8 * m - 1))) := h.2
    obtain ⟨finish, hfinish, hfinishEq⟩ := htargetMem
    have hfinishCore := isCentralCoreStart_of_mem_centralParityTarget
      m n hm start finish (by simpa [target] using hfinish)
    have hfinishBounds :
        2 * (m : ℝ) ≤ intervalSite finish ∧
          intervalSite finish ≤ 6 * (m : ℝ) := by
      constructor
      · dsimp [intervalSite]
        exact_mod_cast hfinishCore.1
      · dsimp [intervalSite]
        exact_mod_cast hfinishCore.2
    have hdisplacement :
        -(2 * (m : ℝ)) ≤ AdditivePath.displacement n increment ∧
          AdditivePath.displacement n increment ≤ 2 * (m : ℝ) := by
      rw [hstartSite] at hfinishEq
      constructor <;> nlinarith [hfinishEq, hfinishBounds.1, hfinishBounds.2]
    have hden : 0 < 8 * (m : ℝ) := by positivity
    refine ⟨htube, ?_⟩
    constructor
    · apply (le_div_iff₀ hden).2
      nlinarith [hdisplacement.1]
    · apply (div_le_iff₀ hden).2
      nlinarith [hdisplacement.2]
  calc
    _ ≤ ENNReal.ofReal
        (∑ finish ∈ target,
          (intervalKernel (8 * m - 1) ^ n) start finish) :=
      ENNReal.ofReal_le_ofReal hmass
    _ = iidSequenceLaw rademacherMeasure
        {increment : ℕ → ℝ |
          InClosedInterval 1 (8 * (m : ℝ) - 1) n
            (intervalSite start) increment ∧
            intervalSite start + AdditivePath.displacement n increment ∈
            intervalSite '' (target : Set (Fin (8 * m - 1)))} := by
      have hcast : ((8 * m - 1 : ℕ) : ℝ) = 8 * (m : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ 8 * m)]
        norm_num
      rw [← hcast]
      exact hpath
    _ ≤ _ := measure_mono hsubset

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

end
