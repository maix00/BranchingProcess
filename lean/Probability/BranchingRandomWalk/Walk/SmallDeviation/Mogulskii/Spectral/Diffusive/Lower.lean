module

public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.Scaling.Lower
public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.PathSurvival

/-!
# Diffusive-scale lower bounds for the centered symmetric walk

The principal Dirichlet eigenfunction has value one at the center of an odd
interval.  Consequently its lower bound has no boundary prefactor.  This file
records the resulting lower bound when elapsed time is comparable with the
squared interval width.  It is the spectral input for passing from Donsker's
theorem to fixed Brownian corridor estimates.
-/

open Filter Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.Mogulskii

/-- The centered principal Dirichlet mode is a pointwise lower bound for the
survival mass.  The absence of a sine prefactor is specific to the center of
an odd interval. -/
theorem ofReal_centeredPrincipalPower_le_remainingMass
    (radius time : ℕ) (hradius : 0 < radius) :
    ENNReal.ofReal (Real.cos
        (Real.pi / ((2 * (radius + 1) : ℕ) : ℝ)) ^ time) ≤
      Kernel.remainingMass
        (intervalRademacherKernel (2 * radius + 1)) time
        (⟨radius, by omega⟩ : Fin (2 * radius + 1)) := by
  obtain ⟨_lower, _hlowerPos, hlower, _hupper⟩ :=
    intervalKernel_pow_rowSum_bounds (by omega : 0 < 2 * radius + 1)
      time (⟨radius, by omega⟩ : Fin (2 * radius + 1))
  have hmass : Kernel.remainingMass
      (intervalRademacherKernel (2 * radius + 1)) time
      (⟨radius, by omega⟩ : Fin (2 * radius + 1)) =
      ENNReal.ofReal (∑ finish,
        (intervalKernel (2 * radius + 1) ^ time)
          (⟨radius, by omega⟩ : Fin (2 * radius + 1)) finish) := by
    unfold Kernel.remainingMass
    rw [intervalRademacherKernel_eq_ofRealMatrix,
      intervalKernel_pow_apply_univ]
  rw [hmass]
  apply ENNReal.ofReal_le_ofReal
  have hwidthEq : ((2 * (radius + 1) : ℕ) : ℝ) =
      ((2 * radius + 1 + 1 : ℕ) : ℝ) := by
    push_cast
    ring
  rw [hwidthEq]
  simpa [intervalSineWeight_center] using hlower

/-- Under a finite diffusive time-to-width ratio, the centered principal
Dirichlet eigenvalue power has the expected exponential limit. -/
theorem tendsto_centeredPrincipalPower_of_diffusiveRatio
    (radius time : ℕ → ℕ) (c : ℝ)
    (hradius : ∀ n, 0 < radius n)
    (hwidth : Tendsto (fun n => ((2 * (radius n + 1) : ℕ) : ℝ))
      atTop atTop)
    (hratio : Tendsto (fun n => (time n : ℝ) /
      ((2 * (radius n + 1) : ℕ) : ℝ) ^ 2) atTop (nhds c)) :
    Tendsto (fun n => Real.cos
        (Real.pi / ((2 * (radius n + 1) : ℕ) : ℝ)) ^ time n)
      atTop (nhds (Real.exp (c * (-(Real.pi ^ 2) / 2)))) := by
  let width : ℕ → ℝ := fun n => ((2 * (radius n + 1) : ℕ) : ℝ)
  let main : ℕ → ℝ := fun n =>
    width n ^ 2 * Real.log (Real.cos (Real.pi / width n))
  have hmain : Tendsto main atTop (nhds (-(Real.pi ^ 2) / 2)) := by
    convert tendsto_sq_mul_log_cos_pi_div.comp hwidth using 1
    funext n
    simp [main, width, Function.comp_apply]
  have hratio' : Tendsto (fun n => (time n : ℝ) / width n ^ 2)
      atTop (nhds c) := by simpa [width] using hratio
  have hexponent : Tendsto (fun n =>
      (time n : ℝ) * Real.log (Real.cos (Real.pi / width n)))
      atTop (nhds (c * (-(Real.pi ^ 2) / 2))) := by
    have hproduct := hratio'.mul hmain
    convert hproduct using 1
    funext n
    have hwidthNe : width n ≠ 0 := by
      dsimp [width]
      positivity
    simp only [main]
    field_simp [hwidthNe]
  have hexp := Real.continuous_exp.continuousAt.tendsto.comp hexponent
  apply hexp.congr'
  filter_upwards with n
  have heigenPos : 0 < Real.cos (Real.pi / width n) := by
    have hradiusPos := hradius n
    have h := intervalEigenvalue_pos
      (show 1 < 2 * radius n + 1 by omega)
    have hwidthEq : width n = ((2 * radius n + 1 + 1 : ℕ) : ℝ) := by
      dsimp [width]
      push_cast
      ring
    rw [hwidthEq]
    exact h
  simp only [Function.comp_apply]
  calc
    Real.exp ((time n : ℝ) *
        Real.log (Real.cos (Real.pi / width n))) =
        Real.exp (Real.log (Real.cos (Real.pi / width n))) ^ time n := by
      rw [Real.exp_nat_mul]
    _ = Real.cos (Real.pi / width n) ^ time n := by
      rw [Real.exp_log heigenPos]


/-- At the center of an odd interval, the logarithm of the survival mass is
bounded below by the elapsed time times the logarithm of the principal
Dirichlet eigenvalue. -/
theorem time_mul_logCos_le_log_centeredRemainingMass
    (radius time : ℕ) (hradius : 0 < radius) (htime : 0 < time) :
    (time : ℝ) * Real.log (Real.cos
        (Real.pi / ((2 * (radius + 1) : ℕ) : ℝ))) ≤
      Real.log (Kernel.remainingMass
        (intervalRademacherKernel (2 * radius + 1)) time
        (⟨radius, by omega⟩ : Fin (2 * radius + 1))).toReal := by
  let width : ℝ := ((2 * (radius + 1) : ℕ) : ℝ)
  let mass : ENNReal := Kernel.remainingMass
    (intervalRademacherKernel (2 * radius + 1)) time
    (⟨radius, by omega⟩ : Fin (2 * radius + 1))
  have hcount : 1 < 2 * radius + 1 := by omega
  have hscaled :=
    main_add_logSineWeight_le_scaledLog_remainingMass hcount htime
      (⟨radius, by omega⟩ : Fin (2 * radius + 1))
  have hwidthPos : 0 < width := by
    dsimp [width]
    positivity
  have htimeReal : (time : ℝ) ≠ 0 := by exact_mod_cast htime.ne'
  have hscaled' : width ^ 2 *
        Real.log (Real.cos (Real.pi / width)) ≤
      width ^ 2 / (time : ℝ) * Real.log mass.toReal := by
    simp only [intervalSineWeight_center, Real.log_one, mul_zero, add_zero]
      at hscaled
    have hwidthEq : width = ((2 * radius + 1 + 1 : ℕ) : ℝ) := by
      dsimp [width]
      push_cast
      ring
    rw [hwidthEq]
    exact hscaled
  calc
    (time : ℝ) * Real.log (Real.cos (Real.pi / width)) =
        ((time : ℝ) / width ^ 2) *
          (width ^ 2 * Real.log (Real.cos (Real.pi / width))) := by
            field_simp [hwidthPos.ne']
    _ ≤ ((time : ℝ) / width ^ 2) *
          (width ^ 2 / (time : ℝ) * Real.log mass.toReal) :=
      mul_le_mul_of_nonneg_left hscaled' (by positivity)
    _ = Real.log mass.toReal := by
      field_simp [hwidthPos.ne', htimeReal]

/-- If centered interval widths diverge and elapsed time divided by squared
width tends to `c`, the limiting logarithmic survival probability is at least
`-c · π² / 2`. -/
theorem neg_pi_sq_mul_ratio_div_two_le_liminf_log_centeredRemainingMass
    (radius time : ℕ → ℕ) (c : ℝ)
    (hradius : ∀ n, 0 < radius n)
    (htime : ∀ n, 0 < time n)
    (hwidth : Tendsto (fun n => ((2 * (radius n + 1) : ℕ) : ℝ))
      atTop atTop)
    (hratio : Tendsto (fun n => (time n : ℝ) /
      ((2 * (radius n + 1) : ℕ) : ℝ) ^ 2) atTop (nhds c)) :
    c * (-(Real.pi ^ 2) / 2) ≤ atTop.liminf (fun n =>
      Real.log (Kernel.remainingMass
        (intervalRademacherKernel (2 * radius n + 1)) (time n)
        (⟨radius n, by omega⟩ : Fin (2 * radius n + 1))).toReal) := by
  let width : ℕ → ℝ := fun n => ((2 * (radius n + 1) : ℕ) : ℝ)
  let mass : ℕ → ENNReal := fun n => Kernel.remainingMass
    (intervalRademacherKernel (2 * radius n + 1)) (time n)
    (⟨radius n, by omega⟩ : Fin (2 * radius n + 1))
  have hleft : Tendsto (fun n =>
      (time n : ℝ) * Real.log (Real.cos (Real.pi / width n)))
      atTop (nhds (c * (-(Real.pi ^ 2) / 2))) := by
    have hpower := tendsto_centeredPrincipalPower_of_diffusiveRatio
      radius time c hradius hwidth hratio
    have hlogPower := (Real.continuousAt_log
      (Real.exp_ne_zero (c * (-(Real.pi ^ 2) / 2)))).tendsto.comp hpower
    convert hlogPower using 1
    · funext n
      change (time n : ℝ) * Real.log (Real.cos (Real.pi / width n)) =
        Real.log (Real.cos
          (Real.pi / ((2 * (radius n + 1) : ℕ) : ℝ)) ^ time n)
      rw [Real.log_pow]
    · rw [Real.log_exp]
  have hlog : ∀ n,
      (time n : ℝ) * Real.log (Real.cos (Real.pi / width n)) ≤
        Real.log (mass n).toReal := by
    intro n
    simpa [width, mass] using
      time_mul_logCos_le_log_centeredRemainingMass
        (radius n) (time n) (hradius n) (htime n)
  have hmassTop : ∀ n, mass n ≠ ⊤ := by
    intro n
    exact ne_of_lt ((Kernel.remainingMass_le_one
      (intervalRademacherKernel (2 * radius n + 1)) (time n)
      (⟨radius n, by omega⟩ : Fin (2 * radius n + 1))).trans_lt
        ENNReal.one_lt_top)
  have hrightUpper : ∀ᶠ n in atTop, Real.log (mass n).toReal ≤ 0 :=
    Eventually.of_forall fun n => by
      have hmassOne := Kernel.remainingMass_le_one
        (intervalRademacherKernel (2 * radius n + 1)) (time n)
        (⟨radius n, by omega⟩ : Fin (2 * radius n + 1))
      have hrealOne : (mass n).toReal ≤ 1 :=
        (ENNReal.toReal_le_toReal (hmassTop n) ENNReal.one_ne_top).2
          (by simpa [mass] using hmassOne)
      exact Real.log_nonpos ENNReal.toReal_nonneg hrealOne
  calc
    c * (-(Real.pi ^ 2) / 2) = atTop.liminf (fun n =>
        (time n : ℝ) * Real.log (Real.cos (Real.pi / width n))) :=
      hleft.liminf_eq.symm
    _ ≤ atTop.liminf (fun n => Real.log (mass n).toReal) := by
      exact Filter.liminf_le_liminf (Eventually.of_forall hlog)
        hleft.isBoundedUnder_ge
        (Filter.isCoboundedUnder_ge_of_eventually_le atTop hrightUpper)
    _ = _ := rfl

/-- The diffusive lower bound stated using the public centered horizontal
tube probability. -/
theorem neg_pi_sq_mul_ratio_div_two_le_liminf_log_centeredHorizontalTubeProbability
    (radius time : ℕ → ℕ) (c : ℝ)
    (hradius : ∀ n, 0 < radius n)
    (htime : ∀ n, 0 < time n)
    (hwidth : Tendsto (fun n => ((2 * (radius n + 1) : ℕ) : ℝ))
      atTop atTop)
    (hratio : Tendsto (fun n => (time n : ℝ) /
      ((2 * (radius n + 1) : ℕ) : ℝ) ^ 2) atTop (nhds c)) :
    c * (-(Real.pi ^ 2) / 2) ≤ atTop.liminf (fun n =>
      Real.log (horizontalTubeProbability
        (independentIncrementLaw rademacherMeasure)
        (1 / 2) (2 * radius n) (time n)).toReal) := by
  have h := neg_pi_sq_mul_ratio_div_two_le_liminf_log_centeredRemainingMass
    radius time c hradius htime hwidth hratio
  convert h using 1
  apply congrArg (fun f => atTop.liminf f)
  funext n
  congr 2
  simpa [Kernel.remainingMass] using
    (centeredIntervalRademacherKernel_pow_apply_univ_eq_horizontalTubeProbability
      (radius n) (time n)).symm

end ProbabilityTheory.RandomWalk.Mogulskii
