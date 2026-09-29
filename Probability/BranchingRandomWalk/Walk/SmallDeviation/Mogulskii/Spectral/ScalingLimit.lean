import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.ScalingLower
import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.Asymptotics

/-!
# Variable-scale spectral limit with negligible endpoint prefactor

The available uniform ground-state bounds lose one endpoint sine weight.
When its normalized logarithm vanishes, those bounds squeeze the full
variable-scale Rademacher survival rate to `-π² / 2`.
-/

open Filter Topology

namespace ProbabilityTheory.RandomWalk.Mogulskii

/-- Sharp variable-scale spectral asymptotics under the explicit condition
that the logarithmic endpoint-weight prefactor is negligible. -/
theorem tendsto_scaledLog_remainingMass
    (interiorCount time : ℕ → ℕ)
    (start : ∀ n, Fin (interiorCount n))
    (hcount : ∀ n, 1 < interiorCount n)
    (htime : ∀ n, 0 < time n)
    (hwidth : Tendsto (fun n => ((interiorCount n + 1 : ℕ) : ℝ))
      atTop atTop)
    (hprefactor : Tendsto (fun n =>
      ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ) *
        Real.log (Real.sin
          (Real.pi / ((interiorCount n + 1 : ℕ) : ℝ))))
      atTop (nhds 0)) :
    Tendsto (fun n =>
      ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ) *
        Real.log (Kernel.remainingMass
          (intervalRademacherKernel (interiorCount n))
          (time n) (start n)).toReal)
      atTop (nhds (-(Real.pi ^ 2) / 2)) := by
  let width : ℕ → ℝ := fun n => ((interiorCount n + 1 : ℕ) : ℝ)
  let ratio : ℕ → ℝ := fun n => width n ^ 2 / (time n : ℝ)
  let eigenvalue : ℕ → ℝ := fun n =>
    Real.cos (Real.pi / width n)
  let endpointWeight : ℕ → ℝ := fun n =>
    Real.sin (Real.pi / width n)
  let mass : ℕ → ENNReal := fun n => Kernel.remainingMass
    (intervalRademacherKernel (interiorCount n)) (time n) (start n)
  have heigenvalue : ∀ n, 0 < eigenvalue n := by
    intro n
    simpa [eigenvalue, width] using intervalEigenvalue_pos (hcount n)
  have hendpointWeight : ∀ n, 0 < endpointWeight n := by
    intro n
    dsimp [endpointWeight, width]
    apply Real.sin_pos_of_pos_of_lt_pi
    · positivity
    · have hden : (1 : ℝ) < (interiorCount n + 1 : ℕ) := by
        exact_mod_cast Nat.succ_lt_succ (Nat.zero_lt_of_lt (hcount n))
      rw [div_lt_iff₀ (by positivity :
        (0 : ℝ) < (interiorCount n + 1 : ℕ))]
      nlinarith [Real.pi_pos]
  have hbounds : ∀ n,
      ENNReal.ofReal
          (endpointWeight n * eigenvalue n ^ time n) ≤ mass n ∧
        mass n ≤ ENNReal.ofReal
          (eigenvalue n ^ time n / endpointWeight n) := by
    intro n
    simpa [endpointWeight, eigenvalue, width, mass] using
      intervalRademacherKernel_remainingMass_uniform_bounds
        (hcount n) (time n) (start n)
  have hmassTop : ∀ n, mass n ≠ ⊤ := by
    intro n
    exact ne_of_lt ((Kernel.remainingMass_le_one
      (intervalRademacherKernel (interiorCount n)) (time n) (start n)).trans_lt
        ENNReal.one_lt_top)
  have hratioNonneg : ∀ n, 0 ≤ ratio n := by
    intro n
    dsimp [ratio, width]
    positivity
  have hlower : ∀ n,
      width n ^ 2 * Real.log (eigenvalue n) +
          ratio n * Real.log (endpointWeight n) ≤
        ratio n * Real.log (mass n).toReal := by
    intro n
    have hproductPos : 0 < endpointWeight n * eigenvalue n ^ time n :=
      mul_pos (hendpointWeight n) (pow_pos (heigenvalue n) _)
    have hreal : endpointWeight n * eigenvalue n ^ time n ≤
        (mass n).toReal := by
      have := (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (hmassTop n)).2
        (hbounds n).1
      simpa [ENNReal.toReal_ofReal hproductPos.le] using this
    have hlog := Real.log_le_log hproductPos hreal
    rw [Real.log_mul (hendpointWeight n).ne'
      (pow_pos (heigenvalue n) _).ne', Real.log_pow] at hlog
    have hscaled := mul_le_mul_of_nonneg_left hlog (hratioNonneg n)
    calc
      width n ^ 2 * Real.log (eigenvalue n) +
          ratio n * Real.log (endpointWeight n) =
        ratio n * (Real.log (endpointWeight n) +
          (time n : ℝ) * Real.log (eigenvalue n)) := by
            dsimp [ratio]
            field_simp [(Nat.cast_ne_zero.mpr (htime n).ne')]
            ring
      _ ≤ _ := hscaled
  have hupper : ∀ n,
      ratio n * Real.log (mass n).toReal ≤
        width n ^ 2 * Real.log (eigenvalue n) -
          ratio n * Real.log (endpointWeight n) := by
    intro n
    have hquotientPos : 0 < eigenvalue n ^ time n / endpointWeight n :=
      div_pos (pow_pos (heigenvalue n) _) (hendpointWeight n)
    have hreal : (mass n).toReal ≤
        eigenvalue n ^ time n / endpointWeight n := by
      have := (ENNReal.toReal_le_toReal (hmassTop n) ENNReal.ofReal_ne_top).2
        (hbounds n).2
      simpa [ENNReal.toReal_ofReal hquotientPos.le] using this
    have hproductPos : 0 < endpointWeight n * eigenvalue n ^ time n :=
      mul_pos (hendpointWeight n) (pow_pos (heigenvalue n) _)
    have hmassPosENN : 0 < mass n :=
      (ENNReal.ofReal_pos.2 hproductPos).trans_le (hbounds n).1
    have hmassPos : 0 < (mass n).toReal :=
      ENNReal.toReal_pos hmassPosENN.ne' (hmassTop n)
    have hlog := Real.log_le_log hmassPos hreal
    rw [Real.log_div (pow_pos (heigenvalue n) _).ne'
      (hendpointWeight n).ne', Real.log_pow] at hlog
    have hscaled := mul_le_mul_of_nonneg_left hlog (hratioNonneg n)
    calc
      ratio n * Real.log (mass n).toReal ≤
          ratio n * ((time n : ℝ) * Real.log (eigenvalue n) -
            Real.log (endpointWeight n)) := hscaled
      _ = width n ^ 2 * Real.log (eigenvalue n) -
          ratio n * Real.log (endpointWeight n) := by
            dsimp [ratio]
            field_simp [(Nat.cast_ne_zero.mpr (htime n).ne')]
  have hmain : Tendsto (fun n =>
      width n ^ 2 * Real.log (eigenvalue n)) atTop
      (nhds (-(Real.pi ^ 2) / 2)) := by
    convert tendsto_sq_mul_log_cos_pi_div.comp hwidth using 1
    funext n
    simp [width, eigenvalue, Function.comp_apply, Nat.cast_add, Nat.cast_one]
  have hprefactor' : Tendsto (fun n =>
      ratio n * Real.log (endpointWeight n)) atTop (nhds 0) := by
    simpa [ratio, width, endpointWeight] using hprefactor
  have hlowerTendsto : Tendsto (fun n =>
      width n ^ 2 * Real.log (eigenvalue n) +
        ratio n * Real.log (endpointWeight n)) atTop
      (nhds (-(Real.pi ^ 2) / 2)) := by
    simpa using hmain.add hprefactor'
  have hupperTendsto : Tendsto (fun n =>
      width n ^ 2 * Real.log (eigenvalue n) -
        ratio n * Real.log (endpointWeight n)) atTop
      (nhds (-(Real.pi ^ 2) / 2)) := by
    simpa using hmain.sub hprefactor'
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    hlowerTendsto hupperTendsto hlower hupper

/-- Process-law form of `tendsto_scaledLog_remainingMass`. -/
theorem tendsto_scaledLog_rademacherProcess
    (interiorCount time : ℕ → ℕ)
    (start : ∀ n, Fin (interiorCount n))
    (hcount : ∀ n, 1 < interiorCount n)
    (htime : ∀ n, 0 < time n)
    (hwidth : Tendsto (fun n => ((interiorCount n + 1 : ℕ) : ℝ))
      atTop atTop)
    (hprefactor : Tendsto (fun n =>
      ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ) *
        Real.log (Real.sin
          (Real.pi / ((interiorCount n + 1 : ℕ) : ℝ))))
      atTop (nhds 0)) :
    Tendsto (fun n =>
      ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ) *
        Real.log (ENNReal.toReal
          ((rademacher (intervalSite (start n))).law
            {walk | ProcessInClosedInterval id 1 (interiorCount n)
              (time n) walk})))
      atTop (nhds (-(Real.pi ^ 2) / 2)) := by
  have h := tendsto_scaledLog_remainingMass interiorCount time start
    hcount htime hwidth hprefactor
  convert h using 1
  funext n
  congr 2
  exact congrArg ENNReal.toReal
    (intervalRademacherKernel_pow_apply_univ_eq_rademacherProcess
      (interiorCount n) (time n) (start n)).symm

/-- The elementary endpoint prefactor is negligible under a directly
checkable logarithmic scale condition.  This condition is sufficient for the
present spectral bounds; it is stronger than the scale assumption in the
general Mogulskii theorem. -/
theorem tendsto_scaledLog_remainingMass_of_logWidth
    (interiorCount time : ℕ → ℕ)
    (start : ∀ n, Fin (interiorCount n))
    (hcount : ∀ n, 1 < interiorCount n)
    (htime : ∀ n, 0 < time n)
    (hwidth : Tendsto (fun n => ((interiorCount n + 1 : ℕ) : ℝ))
      atTop atTop)
    (hratio : Tendsto (fun n =>
      ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ))
      atTop (nhds 0))
    (hratioLogWidth : Tendsto (fun n =>
      ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ) *
        Real.log ((interiorCount n + 1 : ℕ) : ℝ))
      atTop (nhds 0)) :
    Tendsto (fun n =>
      ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ) *
        Real.log (Kernel.remainingMass
          (intervalRademacherKernel (interiorCount n))
          (time n) (start n)).toReal)
      atTop (nhds (-(Real.pi ^ 2) / 2)) := by
  let width : ℕ → ℝ := fun n => ((interiorCount n + 1 : ℕ) : ℝ)
  let ratio : ℕ → ℝ := fun n => width n ^ 2 / (time n : ℝ)
  have hcorrection : Tendsto (fun n =>
      Real.log (Real.sin (Real.pi / width n)) + Real.log (width n))
      atTop (nhds (Real.log Real.pi)) := by
    change Tendsto
      ((fun length : ℝ =>
          Real.log (Real.sin (Real.pi / length)) + Real.log length) ∘
        fun n => ((interiorCount n + 1 : ℕ) : ℝ))
      atTop (nhds (Real.log Real.pi))
    exact tendsto_log_sin_pi_div_add_log.comp hwidth
  have hscaledCorrection : Tendsto (fun n => ratio n *
      (Real.log (Real.sin (Real.pi / width n)) + Real.log (width n)))
      atTop (nhds 0) := by
    simpa [ratio, width] using hratio.mul hcorrection
  have hprefactor : Tendsto (fun n => ratio n *
      Real.log (Real.sin (Real.pi / width n))) atTop (nhds 0) := by
    have hdiff := hscaledCorrection.sub hratioLogWidth
    convert hdiff using 1
    · funext n
      dsimp [ratio, width]
      ring
    · simp
  exact tendsto_scaledLog_remainingMass interiorCount time start hcount htime
    hwidth (by simpa [ratio, width] using hprefactor)

/-- Process-law form of
`tendsto_scaledLog_remainingMass_of_logWidth`. -/
theorem tendsto_scaledLog_rademacherProcess_of_logWidth
    (interiorCount time : ℕ → ℕ)
    (start : ∀ n, Fin (interiorCount n))
    (hcount : ∀ n, 1 < interiorCount n)
    (htime : ∀ n, 0 < time n)
    (hwidth : Tendsto (fun n => ((interiorCount n + 1 : ℕ) : ℝ))
      atTop atTop)
    (hratio : Tendsto (fun n =>
      ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ))
      atTop (nhds 0))
    (hratioLogWidth : Tendsto (fun n =>
      ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ) *
        Real.log ((interiorCount n + 1 : ℕ) : ℝ))
      atTop (nhds 0)) :
    Tendsto (fun n =>
      ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ) *
        Real.log (ENNReal.toReal
          ((rademacher (intervalSite (start n))).law
            {walk | ProcessInClosedInterval id 1 (interiorCount n)
              (time n) walk})))
      atTop (nhds (-(Real.pi ^ 2) / 2)) := by
  have h := tendsto_scaledLog_remainingMass_of_logWidth
    interiorCount time start hcount htime hwidth hratio hratioLogWidth
  convert h using 1
  funext n
  congr 2
  exact congrArg ENNReal.toReal
    (intervalRademacherKernel_pow_apply_univ_eq_rademacherProcess
      (interiorCount n) (time n) (start n)).symm

/-- Sharp spectral asymptotics expressed through the public symmetric
horizontal-tube probability.  The effective Dirichlet width is
`2 * (radius + 1)` while the permitted displacement interval is
`[-radius, radius]`. -/
theorem tendsto_scaledLog_centeredHorizontalTubeProbability_of_logWidth
    (radius time : ℕ → ℕ)
    (hradius : ∀ n, 0 < radius n)
    (htime : ∀ n, 0 < time n)
    (hwidth : Tendsto (fun n => ((2 * (radius n + 1) : ℕ) : ℝ))
      atTop atTop)
    (hratio : Tendsto (fun n =>
      ((2 * (radius n + 1) : ℕ) : ℝ) ^ 2 / (time n : ℝ))
      atTop (nhds 0))
    (hratioLogWidth : Tendsto (fun n =>
      ((2 * (radius n + 1) : ℕ) : ℝ) ^ 2 / (time n : ℝ) *
        Real.log ((2 * (radius n + 1) : ℕ) : ℝ))
      atTop (nhds 0)) :
    Tendsto (fun n =>
      ((2 * (radius n + 1) : ℕ) : ℝ) ^ 2 / (time n : ℝ) *
        Real.log (horizontalTubeProbability
          (independentIncrementLaw rademacherMeasure)
          (1 / 2) (2 * radius n) (time n)).toReal)
      atTop (nhds (-(Real.pi ^ 2) / 2)) := by
  let interiorCount : ℕ → ℕ := fun n => 2 * radius n + 1
  let start : ∀ n, Fin (interiorCount n) := fun n =>
    ⟨radius n, by dsimp [interiorCount]; omega⟩
  have hcount : ∀ n, 1 < interiorCount n := by
    intro n
    have := hradius n
    dsimp [interiorCount]
    omega
  have hcountWidth : ∀ n, interiorCount n + 1 = 2 * (radius n + 1) := by
    intro n
    dsimp [interiorCount]
    omega
  have h := tendsto_scaledLog_remainingMass_of_logWidth
    interiorCount time start hcount htime
    (by simpa only [hcountWidth] using hwidth)
    (by simpa only [hcountWidth] using hratio)
    (by simpa only [hcountWidth] using hratioLogWidth)
  convert h using 1
  funext n
  rw [show ((interiorCount n + 1 : ℕ) : ℝ) =
      ((2 * (radius n + 1) : ℕ) : ℝ) by rw [hcountWidth]]
  congr 2
  apply congrArg ENNReal.toReal
  simpa [Kernel.remainingMass, interiorCount, start] using
    (centeredIntervalRademacherKernel_pow_apply_univ_eq_horizontalTubeProbability
      (radius n) (time n)).symm

/-- The same result normalized by the actual tube width `2 * radius`.
The two missing boundary sites in the finite Dirichlet model contribute the
factor `(radius / (radius + 1))²`, which tends to one. -/
theorem tendsto_tubeWidth_scaledLog_centeredHorizontalTubeProbability_of_logWidth
    (radius time : ℕ → ℕ)
    (hradius : ∀ n, 0 < radius n)
    (htime : ∀ n, 0 < time n)
    (hradiusTop : Tendsto (fun n => (radius n : ℝ)) atTop atTop)
    (hwidth : Tendsto (fun n => ((2 * (radius n + 1) : ℕ) : ℝ))
      atTop atTop)
    (hratio : Tendsto (fun n =>
      ((2 * (radius n + 1) : ℕ) : ℝ) ^ 2 / (time n : ℝ))
      atTop (nhds 0))
    (hratioLogWidth : Tendsto (fun n =>
      ((2 * (radius n + 1) : ℕ) : ℝ) ^ 2 / (time n : ℝ) *
        Real.log ((2 * (radius n + 1) : ℕ) : ℝ))
      atTop (nhds 0)) :
    Tendsto (fun n =>
      ((2 * radius n : ℕ) : ℝ) ^ 2 / (time n : ℝ) *
        Real.log (horizontalTubeProbability
          (independentIncrementLaw rademacherMeasure)
          (1 / 2) (2 * radius n) (time n)).toReal)
      atTop (nhds (-(Real.pi ^ 2) / 2)) := by
  have hmain :=
    tendsto_scaledLog_centeredHorizontalTubeProbability_of_logWidth
      radius time hradius htime hwidth hratio hratioLogWidth
  have hdenom : Tendsto (fun n => (radius n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 hradiusTop
  have hinv : Tendsto (fun n => ((radius n : ℝ) + 1)⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hdenom
  have hfactor : Tendsto (fun n =>
      ((radius n : ℝ) / (radius n + 1)) ^ 2) atTop (nhds 1) := by
    have hbase : Tendsto (fun n =>
        1 - ((radius n : ℝ) + 1)⁻¹) atTop (nhds 1) := by
      simpa using tendsto_const_nhds.sub hinv
    convert hbase.pow 2 using 1
    · funext n
      have hne : (radius n : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      ring
    · norm_num
  have hproduct := hfactor.mul hmain
  convert hproduct using 1
  · funext n
    have htimeNe : (time n : ℝ) ≠ 0 := by
      exact_mod_cast (htime n).ne'
    have hradiusSuccNe : (radius n : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
  · ring_nf

end ProbabilityTheory.RandomWalk.Mogulskii
