module

public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.ScalingLower
public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.Asymptotics
public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.UpperBound

/-!
# Variable-scale spectral limits

The complete sine spectrum gives the sharp upper rate under the sole
diffusive-scale condition.  For starting sites whose principal sine weight
stays uniformly positive, the positive ground state supplies the matching
lower rate.  Separate endpoint-prefactor results record the stronger scale
condition needed when starting sites approach a killing boundary.
-/

open Filter Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.Mogulskii

/-- When elapsed time dominates squared interval width, the elapsed-time
power of the principal Dirichlet eigenvalue tends to zero. -/
theorem tendsto_principalEigenvalue_pow_zero
    (interiorCount time : ℕ → ℕ)
    (hcount : ∀ n, 1 < interiorCount n)
    (htime : ∀ n, 0 < time n)
    (hwidth : Tendsto (fun n => ((interiorCount n + 1 : ℕ) : ℝ))
      atTop atTop)
    (hratio : Tendsto (fun n =>
      ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ))
      atTop (nhds 0)) :
    Tendsto (fun n =>
      Real.cos (Real.pi / ((interiorCount n + 1 : ℕ) : ℝ)) ^ time n)
      atTop (nhds 0) := by
  let width : ℕ → ℝ := fun n => ((interiorCount n + 1 : ℕ) : ℝ)
  let ratio : ℕ → ℝ := fun n => width n ^ 2 / (time n : ℝ)
  let eigenvalue : ℕ → ℝ := fun n => Real.cos (Real.pi / width n)
  let main : ℕ → ℝ := fun n => width n ^ 2 * Real.log (eigenvalue n)
  have hmain : Tendsto main atTop (nhds (-(Real.pi ^ 2) / 2)) := by
    convert tendsto_sq_mul_log_cos_pi_div.comp hwidth using 1
    funext n
    simp [main, width, eigenvalue, Function.comp_apply, Nat.cast_add,
      Nat.cast_one]
  have hratio' : Tendsto ratio atTop (nhds 0) := by
    simpa [ratio, width] using hratio
  have hratioPos : ∀ n, 0 < ratio n := by
    intro n
    dsimp [ratio, width]
    apply div_pos
    · positivity
    · exact_mod_cast htime n
  have hratioGT : Tendsto ratio atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hratio', Eventually.of_forall hratioPos⟩
  have hinv : Tendsto ratio⁻¹ atTop atTop :=
    hratioGT.inv_tendsto_nhdsGT_zero
  have hconstantNeg : -(Real.pi ^ 2) / 2 < 0 := by
    nlinarith [sq_pos_of_pos Real.pi_pos]
  have hexponent : Tendsto (fun n => main n * (ratio n)⁻¹)
      atTop atBot := hmain.neg_mul_atTop hconstantNeg hinv
  have hexp : Tendsto (fun n => Real.exp (main n * (ratio n)⁻¹))
      atTop (nhds 0) := Real.tendsto_exp_atBot.comp hexponent
  apply hexp.congr'
  filter_upwards with n
  have heigenvalue : 0 < eigenvalue n := by
    simpa [eigenvalue, width] using intervalEigenvalue_pos (hcount n)
  have htimeReal : ((time n : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (htime n).ne'
  have hwidthReal : width n ≠ 0 := by
    dsimp [width]
    positivity
  have hexponentEq : main n * (ratio n)⁻¹ =
      (time n : ℝ) * Real.log (eigenvalue n) := by
    dsimp [main, ratio]
    rw [inv_div]
    field_simp
  rw [hexponentEq, ← Real.log_pow]
  simpa [eigenvalue, width] using
    (Real.exp_log (pow_pos heigenvalue (time n)))

/-- The logarithmic correction in the geometric spectral upper bound is
negligible on the diffusive scale. -/
theorem tendsto_scaledLog_geometricCorrection
    (interiorCount time : ℕ → ℕ)
    (hcount : ∀ n, 1 < interiorCount n)
    (htime : ∀ n, 0 < time n)
    (hwidth : Tendsto (fun n => ((interiorCount n + 1 : ℕ) : ℝ))
      atTop atTop)
    (hratio : Tendsto (fun n =>
      ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ))
      atTop (nhds 0)) :
    Tendsto (fun n =>
      ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ) *
        Real.log (4 / (1 -
          Real.cos (Real.pi / ((interiorCount n + 1 : ℕ) : ℝ)) ^
            time n))) atTop (nhds 0) := by
  let eigenvaluePower : ℕ → ℝ := fun n =>
    Real.cos (Real.pi / ((interiorCount n + 1 : ℕ) : ℝ)) ^ time n
  have heigenvaluePower : Tendsto eigenvaluePower atTop (nhds 0) := by
    simpa [eigenvaluePower] using tendsto_principalEigenvalue_pow_zero
      interiorCount time hcount htime hwidth hratio
  have hdenominator : Tendsto (fun n => 1 - eigenvaluePower n)
      atTop (nhds 1) := by
    simpa using tendsto_const_nhds.sub heigenvaluePower
  have hquotient : Tendsto (fun n => 4 / (1 - eigenvaluePower n))
      atTop (nhds 4) := by
    have hfour : Tendsto (fun _ : ℕ => (4 : ℝ)) atTop (nhds 4) :=
      tendsto_const_nhds
    convert hfour.div hdenominator one_ne_zero using 1
    · norm_num
  have hlog : Tendsto (fun n => Real.log (4 / (1 - eigenvaluePower n)))
      atTop (nhds (Real.log 4)) := by
    exact (Real.continuousAt_log (by norm_num : (4 : ℝ) ≠ 0)).tendsto.comp
      hquotient
  have hratio' : Tendsto (fun n =>
      ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ))
      atTop (nhds 0) := hratio
  simpa [eigenvaluePower] using hratio'.mul hlog

/-- Pointwise logarithmic upper bound furnished by the complete sine
spectrum.  Unlike the ground-state comparison, its correction has no
interval-width prefactor. -/
theorem scaledLog_remainingMass_le_main_add_geometricCorrection
    {interiorCount time : ℕ} (hcount : 1 < interiorCount)
    (htime : 0 < time) (start : Fin interiorCount) :
    ((interiorCount + 1 : ℕ) : ℝ) ^ 2 / (time : ℝ) *
        Real.log (Kernel.remainingMass
          (intervalRademacherKernel interiorCount) time start).toReal ≤
      ((interiorCount + 1 : ℕ) : ℝ) ^ 2 *
          Real.log (Real.cos
            (Real.pi / ((interiorCount + 1 : ℕ) : ℝ))) +
        ((interiorCount + 1 : ℕ) : ℝ) ^ 2 / (time : ℝ) *
          Real.log (4 / (1 -
            Real.cos (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) ^ time)) := by
  let q : ℝ := Real.cos (Real.pi / ((interiorCount + 1 : ℕ) : ℝ))
  let mass : ENNReal := Kernel.remainingMass
    (intervalRademacherKernel interiorCount) time start
  have hqPos : 0 < q := by
    simpa [q] using intervalEigenvalue_pos hcount
  have hwidth : (2 : ℝ) ≤ ((interiorCount + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_lt_of_lt hcount)
  have hanglePos : 0 < Real.pi / ((interiorCount + 1 : ℕ) : ℝ) := by
    positivity
  have hangleLeHalf : Real.pi / ((interiorCount + 1 : ℕ) : ℝ) ≤
      Real.pi / 2 :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hwidth
  have hqLtOne : q < 1 := by
    have hanti := Real.strictAntiOn_cos
      (show (0 : ℝ) ∈ Set.Icc 0 Real.pi by
        constructor <;> linarith [Real.pi_pos])
      (show Real.pi / ((interiorCount + 1 : ℕ) : ℝ) ∈
          Set.Icc 0 Real.pi by
        constructor
        · exact hanglePos.le
        · exact hangleLeHalf.trans (by linarith [Real.pi_pos]))
      hanglePos
    simpa [q] using hanti
  have hqPowLtOne : q ^ time < 1 :=
    pow_lt_one₀ hqPos.le hqLtOne htime.ne'
  have hmassEq : mass.toReal =
      ∑ finish, (intervalKernel interiorCount ^ time) start finish := by
    dsimp [mass, Kernel.remainingMass]
    rw [intervalRademacherKernel_eq_ofRealMatrix,
      intervalKernel_pow_apply_univ, ENNReal.toReal_ofReal]
    exact Finset.sum_nonneg fun _ _ =>
      Matrix.pow_apply_nonneg (intervalKernel_nonneg interiorCount) _ _ _
  have hmassUpper : mass.toReal ≤ 4 * (q ^ time / (1 - q ^ time)) := by
    rw [hmassEq]
    simpa [q] using intervalKernel_pow_rowSum_le_four_mul_div_one_sub
      (Nat.zero_lt_of_lt hcount) htime start
  have hmassTop : mass ≠ ⊤ := by
    exact ne_of_lt ((Kernel.remainingMass_le_one
      (intervalRademacherKernel interiorCount) time start).trans_lt
        ENNReal.one_lt_top)
  have hendpointPos : 0 < Real.sin
      (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact hanglePos
    · exact hangleLeHalf.trans_lt (by linarith [Real.pi_pos])
  have hlower := (intervalRademacherKernel_remainingMass_uniform_bounds
    hcount time start).1
  have hproductPos : 0 < Real.sin
      (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) * q ^ time :=
    mul_pos hendpointPos (pow_pos hqPos _)
  have hmassPos : 0 < mass.toReal := by
    have hmassENN : 0 < mass := by
      apply (ENNReal.ofReal_pos.2 hproductPos).trans_le
      simpa [mass, q] using hlower
    exact ENNReal.toReal_pos hmassENN.ne' hmassTop
  have hlog := Real.log_le_log hmassPos hmassUpper
  have hfactorPos : 0 < 4 / (1 - q ^ time) := by
    positivity
  have hupperRewrite : 4 * (q ^ time / (1 - q ^ time)) =
      q ^ time * (4 / (1 - q ^ time)) := by ring
  rw [hupperRewrite, Real.log_mul (pow_pos hqPos _).ne' hfactorPos.ne',
    Real.log_pow] at hlog
  have hratioNonneg : 0 ≤
      ((interiorCount + 1 : ℕ) : ℝ) ^ 2 / (time : ℝ) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hlog hratioNonneg
  calc
    ((interiorCount + 1 : ℕ) : ℝ) ^ 2 / (time : ℝ) *
        Real.log mass.toReal ≤
      ((interiorCount + 1 : ℕ) : ℝ) ^ 2 / (time : ℝ) *
        ((time : ℝ) * Real.log q +
          Real.log (4 / (1 - q ^ time))) := hscaled
    _ = ((interiorCount + 1 : ℕ) : ℝ) ^ 2 * Real.log q +
        ((interiorCount + 1 : ℕ) : ℝ) ^ 2 / (time : ℝ) *
          Real.log (4 / (1 - q ^ time)) := by
      field_simp [(Nat.cast_ne_zero.mpr htime.ne')]
    _ = _ := by rfl

/-- Sharp spectral upper estimate under the sole diffusive-scale condition
`width² / time → 0`. -/
theorem eventually_scaledLog_remainingMass_lt_neg_pi_sq_div_two_add
    (interiorCount time : ℕ → ℕ)
    (start : ∀ n, Fin (interiorCount n))
    (hcount : ∀ n, 1 < interiorCount n)
    (htime : ∀ n, 0 < time n)
    (hwidth : Tendsto (fun n => ((interiorCount n + 1 : ℕ) : ℝ))
      atTop atTop)
    (hratio : Tendsto (fun n =>
      ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ))
      atTop (nhds 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ) *
          Real.log (Kernel.remainingMass
            (intervalRademacherKernel (interiorCount n))
            (time n) (start n)).toReal <
        -(Real.pi ^ 2) / 2 + ε := by
  let main : ℕ → ℝ := fun n =>
    ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 *
      Real.log (Real.cos
        (Real.pi / ((interiorCount n + 1 : ℕ) : ℝ)))
  let correction : ℕ → ℝ := fun n =>
    ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ) *
      Real.log (4 / (1 -
        Real.cos (Real.pi / ((interiorCount n + 1 : ℕ) : ℝ)) ^ time n))
  have hmain : Tendsto main atTop (nhds (-(Real.pi ^ 2) / 2)) := by
    convert tendsto_sq_mul_log_cos_pi_div.comp hwidth using 1
    funext n
    simp [main, Function.comp_apply, Nat.cast_add, Nat.cast_one]
  have hcorrection : Tendsto correction atTop (nhds 0) := by
    simpa [correction] using tendsto_scaledLog_geometricCorrection
      interiorCount time hcount htime hwidth hratio
  have hupperTendsto : Tendsto (fun n => main n + correction n)
      atTop (nhds (-(Real.pi ^ 2) / 2)) := by
    simpa using hmain.add hcorrection
  have heventuallyUpper : ∀ᶠ n in atTop,
      main n + correction n < -(Real.pi ^ 2) / 2 + ε :=
    (tendsto_order.1 hupperTendsto).2 _ (by linarith)
  filter_upwards [heventuallyUpper] with n hn
  exact (scaledLog_remainingMass_le_main_add_geometricCorrection
    (hcount n) (htime n) (start n)).trans_lt (by
      simpa [main, correction] using hn)

/-- Process-law form of the sharp spectral upper estimate. -/
theorem eventually_scaledLog_rademacherProcess_lt_neg_pi_sq_div_two_add
    (interiorCount time : ℕ → ℕ)
    (start : ∀ n, Fin (interiorCount n))
    (hcount : ∀ n, 1 < interiorCount n)
    (htime : ∀ n, 0 < time n)
    (hwidth : Tendsto (fun n => ((interiorCount n + 1 : ℕ) : ℝ))
      atTop atTop)
    (hratio : Tendsto (fun n =>
      ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ))
      atTop (nhds 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ) *
          Real.log (ENNReal.toReal
            ((rademacher (intervalSite (start n))).law
              {walk | ProcessInClosedInterval id 1 (interiorCount n)
                (time n) walk})) <
        -(Real.pi ^ 2) / 2 + ε := by
  filter_upwards [eventually_scaledLog_remainingMass_lt_neg_pi_sq_div_two_add
    interiorCount time start hcount htime hwidth hratio hε] with n hn
  rw [← intervalRademacherKernel_pow_apply_univ_eq_rademacherProcess]
  exact hn

/-- Complete sharp limit for starting sites that stay uniformly inside the
Dirichlet ground state.  It needs only the diffusive scale condition and no
logarithmic width hypothesis. -/
theorem tendsto_scaledLog_remainingMass_of_sineWeight
    (interiorCount time : ℕ → ℕ)
    (start : ∀ n, Fin (interiorCount n))
    (hcount : ∀ n, 1 < interiorCount n)
    (htime : ∀ n, 0 < time n)
    (hwidth : Tendsto (fun n => ((interiorCount n + 1 : ℕ) : ℝ))
      atTop atTop)
    (hratio : Tendsto (fun n =>
      ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ))
      atTop (nhds 0))
    (c : ℝ) (hc : 0 < c)
    (hstart : ∀ n, c ≤ intervalSineWeight (interiorCount n) (start n)) :
    Tendsto (fun n =>
      ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ) *
        Real.log (Kernel.remainingMass
          (intervalRademacherKernel (interiorCount n))
          (time n) (start n)).toReal)
      atTop (nhds (-(Real.pi ^ 2) / 2)) := by
  let width : ℕ → ℝ := fun n => ((interiorCount n + 1 : ℕ) : ℝ)
  let ratio : ℕ → ℝ := fun n => width n ^ 2 / (time n : ℝ)
  let eigenvalue : ℕ → ℝ := fun n => Real.cos (Real.pi / width n)
  let weight : ℕ → ℝ := fun n =>
    intervalSineWeight (interiorCount n) (start n)
  let lower : ℕ → ℝ := fun n =>
    width n ^ 2 * Real.log (eigenvalue n) +
      ratio n * Real.log (weight n)
  let upper : ℕ → ℝ := fun n =>
    width n ^ 2 * Real.log (eigenvalue n) +
      ratio n * Real.log (4 / (1 - eigenvalue n ^ time n))
  have hmain : Tendsto (fun n =>
      width n ^ 2 * Real.log (eigenvalue n)) atTop
      (nhds (-(Real.pi ^ 2) / 2)) := by
    convert tendsto_sq_mul_log_cos_pi_div.comp hwidth using 1
    funext n
    simp [width, eigenvalue, Function.comp_apply, Nat.cast_add, Nat.cast_one]
  have hratio' : Tendsto ratio atTop (nhds 0) := by
    simpa [ratio, width] using hratio
  have hratioNonneg : ∀ n, 0 ≤ ratio n := by
    intro n
    dsimp [ratio, width]
    positivity
  have hlogWeightLower : ∀ n, Real.log c ≤ Real.log (weight n) := by
    intro n
    exact Real.log_le_log hc (by simpa [weight] using hstart n)
  have hlogWeightUpper : ∀ n, Real.log (weight n) ≤ 0 := by
    intro n
    apply Real.log_nonpos
    · exact (intervalSineWeight_pos
        (Nat.zero_lt_of_lt (hcount n)) (start n)).le
    · exact intervalSineWeight_le_one _ _
  have hweightCorrection : Tendsto (fun n =>
      ratio n * Real.log (weight n)) atTop (nhds 0) := by
    have hlower : Tendsto (fun n => ratio n * Real.log c)
        atTop (nhds 0) := by
      simpa using hratio'.mul_const (Real.log c)
    have hupper : Tendsto (fun _n : ℕ => (0 : ℝ)) atTop (nhds 0) :=
      tendsto_const_nhds
    apply hlower.squeeze' hupper
    · exact Eventually.of_forall fun n => mul_le_mul_of_nonneg_left
        (hlogWeightLower n) (hratioNonneg n)
    · exact Eventually.of_forall fun n => mul_nonpos_of_nonneg_of_nonpos
        (hratioNonneg n) (hlogWeightUpper n)
  have hlowerTendsto : Tendsto lower atTop
      (nhds (-(Real.pi ^ 2) / 2)) := by
    simpa [lower] using hmain.add hweightCorrection
  have hupperCorrection : Tendsto (fun n =>
      ratio n * Real.log (4 / (1 - eigenvalue n ^ time n)))
      atTop (nhds 0) := by
    simpa [ratio, width, eigenvalue] using
      tendsto_scaledLog_geometricCorrection interiorCount time
        hcount htime hwidth hratio
  have hupperTendsto : Tendsto upper atTop
      (nhds (-(Real.pi ^ 2) / 2)) := by
    simpa [upper] using hmain.add hupperCorrection
  have hlower : ∀ n, lower n ≤
      ratio n * Real.log (Kernel.remainingMass
        (intervalRademacherKernel (interiorCount n))
        (time n) (start n)).toReal := by
    intro n
    simpa [lower, ratio, width, eigenvalue, weight] using
      main_add_logSineWeight_le_scaledLog_remainingMass
        (hcount n) (htime n) (start n)
  have hupper : ∀ n,
      ratio n * Real.log (Kernel.remainingMass
          (intervalRademacherKernel (interiorCount n))
          (time n) (start n)).toReal ≤ upper n := by
    intro n
    simpa [upper, ratio, width, eigenvalue] using
      scaledLog_remainingMass_le_main_add_geometricCorrection
        (hcount n) (htime n) (start n)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    hlowerTendsto hupperTendsto hlower hupper

/-- Process-law form of the complete sharp interior-start limit. -/
theorem tendsto_scaledLog_rademacherProcess_of_sineWeight
    (interiorCount time : ℕ → ℕ)
    (start : ∀ n, Fin (interiorCount n))
    (hcount : ∀ n, 1 < interiorCount n)
    (htime : ∀ n, 0 < time n)
    (hwidth : Tendsto (fun n => ((interiorCount n + 1 : ℕ) : ℝ))
      atTop atTop)
    (hratio : Tendsto (fun n =>
      ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ))
      atTop (nhds 0))
    (c : ℝ) (hc : 0 < c)
    (hstart : ∀ n, c ≤ intervalSineWeight (interiorCount n) (start n)) :
    Tendsto (fun n =>
      ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ) *
        Real.log (ENNReal.toReal
          ((rademacher (intervalSite (start n))).law
            {walk | ProcessInClosedInterval id 1 (interiorCount n)
              (time n) walk})))
      atTop (nhds (-(Real.pi ^ 2) / 2)) := by
  have h := tendsto_scaledLog_remainingMass_of_sineWeight
    interiorCount time start hcount htime hwidth hratio c hc hstart
  convert h using 1
  funext n
  congr 2
  exact congrArg ENNReal.toReal
    (intervalRademacherKernel_pow_apply_univ_eq_rademacherProcess
      (interiorCount n) (time n) (start n)).symm

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

end ProbabilityTheory.RandomWalk.Mogulskii
