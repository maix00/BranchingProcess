module

public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.Asymptotics
public import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.Modes

/-!
# Principal spectral scale

These lemmas isolate the two scale corrections used by the variable-scale
spectral bounds: the principal eigenvalue power and the geometric tail
prefactor.
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

end ProbabilityTheory.RandomWalk.Mogulskii
