/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Scaling.Interior
public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Scaling.Endpoint

/-!
# Centered horizontal-tube spectral limits

This file specializes the variable-scale Dirichlet spectrum to a symmetric
Rademacher walk started at the center of its interval.  Centering keeps the
principal sine weight equal to one, so the sharp limit only needs the
diffusive-scale condition.  Write
\[
  p_n=\mathbb P\bigl(|S_j|\le r_n\text{ for }1\le j\le t_n\bigr),
  \qquad W_n=2(r_n+1),
\]
where $(S_j)$ is the simple symmetric walk.  The public results are:

* `tendsto_scaledLog_centeredHorizontalTubeProbability` proves
  $\frac{W_n^2}{t_n}\log p_n\to-\frac{\pi^2}{2}$ when
  $r_n,t_n>0$, $W_n\to\infty$, and $W_n^2/t_n\to0$.
* `tendsto_scaledLog_centeredHorizontalTubeProbability_of_logWidth` proves
  the same limit assuming also
  $\frac{W_n^2}{t_n}\log W_n\to0$; this is the interface used when that
  stronger rate hypothesis is already available.
* `tendsto_tubeWidth_scaledLog_centeredHorizontalTubeProbability` and
  `tendsto_tubeWidth_scaledLog_centeredHorizontalTubeProbability_of_logWidth`
  give the same respective conclusions with the normalizing width $2r_n$
  in place of $W_n$; these require $r_n\to\infty$.
* `tendsto_scaledLog_centeredHorizontalTubeProbability_of_asymptoticWidth`
  replaces $2r_n$ in the normalization by any real scale $a_n$ satisfying
  $a_n/(2r_n)\to1$, while retaining $W_n^2/t_n\to0$.
-/

open Filter Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- Sharp spectral asymptotics for the public symmetric horizontal-tube
probability under the sole diffusive-scale condition. -/
theorem tendsto_scaledLog_centeredHorizontalTubeProbability
    (radius time : ℕ → ℕ)
    (hradius : ∀ n, 0 < radius n)
    (htime : ∀ n, 0 < time n)
    (hwidth : Tendsto (fun n => ((2 * (radius n + 1) : ℕ) : ℝ))
      atTop atTop)
    (hratio : Tendsto (fun n =>
      ((2 * (radius n + 1) : ℕ) : ℝ) ^ 2 / (time n : ℝ))
      atTop (nhds 0)) :
    Tendsto (fun n =>
      ((2 * (radius n + 1) : ℕ) : ℝ) ^ 2 / (time n : ℝ) *
        Real.log (horizontalTubeProbability
          (iidSequenceLaw rademacherMeasure)
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
  have hweight : ∀ n,
      (1 : ℝ) ≤ intervalSineWeight (interiorCount n) (start n) := by
    intro n
    have heq : intervalSineWeight (interiorCount n) (start n) = 1 := by
      simp [interiorCount, start]
    rw [heq]
  have h := tendsto_scaledLog_remainingMass_of_sineWeight
    interiorCount time start hcount htime
    (by simpa only [hcountWidth] using hwidth)
    (by simpa only [hcountWidth] using hratio)
    1 zero_lt_one hweight
  convert h using 1
  funext n
  rw [show ((interiorCount n + 1 : ℕ) : ℝ) =
      ((2 * (radius n + 1) : ℕ) : ℝ) by rw [hcountWidth]]
  congr 2
  apply congrArg ENNReal.toReal
  simpa [Kernel.remainingMass, interiorCount, start] using
    (centeredIntervalRademacherKernel_pow_apply_univ_eq_horizontalTubeProbability
      (radius n) (time n)).symm

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
          (iidSequenceLaw rademacherMeasure)
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

/-- Sharp centered-tube limit normalized by the actual tube width
`2 * radius`, under the sole diffusive-scale condition. -/
theorem tendsto_tubeWidth_scaledLog_centeredHorizontalTubeProbability
    (radius time : ℕ → ℕ)
    (hradius : ∀ n, 0 < radius n)
    (htime : ∀ n, 0 < time n)
    (hradiusTop : Tendsto (fun n => (radius n : ℝ)) atTop atTop)
    (hwidth : Tendsto (fun n => ((2 * (radius n + 1) : ℕ) : ℝ))
      atTop atTop)
    (hratio : Tendsto (fun n =>
      ((2 * (radius n + 1) : ℕ) : ℝ) ^ 2 / (time n : ℝ))
      atTop (nhds 0)) :
    Tendsto (fun n =>
      ((2 * radius n : ℕ) : ℝ) ^ 2 / (time n : ℝ) *
        Real.log (horizontalTubeProbability
          (iidSequenceLaw rademacherMeasure)
          (1 / 2) (2 * radius n) (time n)).toReal)
      atTop (nhds (-(Real.pi ^ 2) / 2)) := by
  have hmain := tendsto_scaledLog_centeredHorizontalTubeProbability
    radius time hradius htime hwidth hratio
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
          (iidSequenceLaw rademacherMeasure)
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


/-- The centered spectral limit is unchanged when its exact lattice width is
replaced by an asymptotically equivalent positive real scale.  This is the
interface used to pass from integer interval radii to the spatial scale in a
Mogulskii statement. -/
theorem tendsto_scaledLog_centeredHorizontalTubeProbability_of_asymptoticWidth
    (radius time : ℕ → ℕ) (scale : ℕ → ℝ)
    (hradius : ∀ n, 0 < radius n)
    (htime : ∀ n, 0 < time n)
    (hradiusTop : Tendsto (fun n => (radius n : ℝ)) atTop atTop)
    (hwidth : Tendsto (fun n => ((2 * (radius n + 1) : ℕ) : ℝ))
      atTop atTop)
    (hratio : Tendsto (fun n =>
      ((2 * (radius n + 1) : ℕ) : ℝ) ^ 2 / (time n : ℝ))
      atTop (nhds 0))
    (hscale : Tendsto (fun n =>
      scale n / ((2 * radius n : ℕ) : ℝ)) atTop (nhds 1)) :
    Tendsto (fun n =>
      scale n ^ 2 / (time n : ℝ) *
        Real.log (horizontalTubeProbability
          (iidSequenceLaw rademacherMeasure)
          (1 / 2) (2 * radius n) (time n)).toReal)
      atTop (nhds (-(Real.pi ^ 2) / 2)) := by
  have hmain :=
    tendsto_tubeWidth_scaledLog_centeredHorizontalTubeProbability
      radius time hradius htime hradiusTop hwidth hratio
  have hproduct := (hscale.pow 2).mul hmain
  convert hproduct using 1
  · funext n
    have hradiusNe : ((2 * radius n : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.mul_pos (by omega) (hradius n)).ne'
    have htimeNe : (time n : ℝ) ≠ 0 := by
      exact_mod_cast (htime n).ne'
    field_simp
  · ring_nf

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
