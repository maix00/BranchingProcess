/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Probability.Process.RandomWalk.SmallDeviation.Marked.Basic
import Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.RealWidthLower
import Analysis.Asymptotics.Scale.Block.Diffusive
import all Probability.Process.RandomWalk.SmallDeviation.Marked.Lemmas.Bands
import all Probability.Process.RandomWalk.SmallDeviation.HorizontalTube.EndpointWindow.Lemmas.IndexSelection

/-!
# Finite-variance return blocks in the marked-corridor proof

## Internal proof declarations

* `ProbabilityTheory.RandomWalk.SmallDeviation.Marked.exists_eventually_returnBlock_ge`:
  for a centered displacement marginal of variance `σ²>0`, `1/2<w<1`
  and `d>π²σ²/2`, there is `T₀` such that every `T>T₀` gives, at
  block length `⌊T Lₙ²⌋`, a uniform unmarked return mass at least `p`
  whenever `p<exp(-dT/w²)`, eventually as `Lₙ→∞`.
  The allowed interval has width `Lₙ`, its return core has radius
  `3(1-w)Lₙ/100`, and the per-step drift is `c/Lₙ²`, `c≥0`.

The original displacement law is used throughout. The seven endpoint-window
bounds come from the already proved finite-variance Mogul'skii theorem.
The finite-band selection and deterministic drift containment are proof
support for Mallein's enriched-walk concatenation, §2.2, Theorem 2.3 and
proof of Lemma 2.5, arXiv:1510.00602v2.
-/

open MeasureTheory Filter
open scoped ENNReal Topology
namespace ProbabilityTheory.RandomWalk.SmallDeviation.Marked
open HorizontalTube HorizontalTube.EndpointWindow

set_option backward.isDefEq.respectTransparency false

lemma exists_eventually_returnBlock_ge
    (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν]
    {sigma w d : ℝ} (hν : IsCenteredSecondMoment (ν.map Prod.fst) (sigma ^ 2))
    (hσ : 0 < sigma) (hw : (1 / 2 : ℝ) < w) (hw1 : w < 1)
    (hd : (Real.pi ^ 2 / 2) * sigma ^ 2 < d) :
    ∃ T₀ : ℝ, 0 ≤ T₀ ∧ ∀ T > T₀, ∀ {scale : ℕ → ℝ},
      Tendsto scale atTop atTop → ∀ c ≥ 0, ∀ p : ℝ,
      p < Real.exp (-d * T / w ^ 2) →
      ∀ᶠ n in atTop, ∀ x : Set.Icc (-3 * ((1 - w) / 100) * scale n)
          (3 * ((1 - w) / 100) * scale n),
        ENNReal.ofReal p ≤ Kernel.returnKernel
          (Kernel.ofPartialStep ν
            (killedMarkedStep (-(scale n / 2)) (scale n / 2) (c / scale n ^ 2))
            (killedMarkedStep_measurable _ _ _))
          (Set.Icc (-3 * ((1 - w) / 100) * scale n)
            (3 * ((1 - w) / 100) * scale n)) measurableSet_Icc
          (Asymptotics.diffusiveBlockLength T scale n) x Set.univ := by
  let incrementLaw := ν.map Prod.fst
  let : IsProbabilityMeasure incrementLaw := inferInstance
  let e := (1 - w) / 100
  have hw0 : 0 < w := by linarith
  have he : 0 < e := by dsimp [e]; positivity
  have hew : 10 * e < w := by dsimp [e]; linarith
  let u (l : Fin 7) := (w / 2 + ((l.val : ℝ) - 3 - 1 / 8) * e) / w
  let v (l : Fin 7) := (w / 2 + ((l.val : ℝ) - 3 + 1 / 8) * e) / w
  have hl (l : Fin 7) : 0 ≤ (l.val : ℝ) ∧ (l.val : ℝ) ≤ 6 := by
    constructor
    · positivity
    · exact_mod_cast (show l.val ≤ 6 by omega)
  obtain ⟨D₀, Q₀, hbound⟩ := exists_uniform_finiteRealWidthTubeProbability_ge_exp
    hν hσ (fun _ : Fin 7 => (1 / 2 : ℝ)) u v (by intro; norm_num)
    (by intro; norm_num)
    (by intro l; exact div_pos (by nlinarith [(hl l).1]) hw0)
    (by intro l; apply (div_lt_div_iff_of_pos_right hw0).2; nlinarith)
    (by intro l; apply (div_lt_one hw0).2; nlinarith [(hl l).2]) hd
  refine ⟨Q₀ + 1, by positivity, ?_⟩
  intro T hT scale hscale c hc p hp
  have hT0 : 0 < T := by linarith only [hT, (show (0 : ℝ) ≤ (Q₀ : ℝ) from Nat.cast_nonneg _)]
  have hsp := hscale.eventually_gt_atTop 0
  have hD := hscale.const_mul_atTop hw0
  have hfloorTop : Tendsto (fun n => ⌊w * scale n⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp hD
  have hratio : Tendsto (fun n => w * scale n / scale n) atTop (𝓝 w) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hsp] with n hn
    field_simp
  have hfloor : Tendsto (fun n => (⌊w * scale n⌋₊ : ℝ) / scale n) atTop (𝓝 w) := by
    simpa only [Nat.add_zero, Asymptotics.floorBlockLength] using
      Asymptotics.tendsto_floorBlockLength_add_nat_div_of_argument_ratio 0 hD hscale hratio
  have hlen : Tendsto (fun n => (Asymptotics.diffusiveBlockLength T scale n : ℝ) /
      scale n ^ 2) atTop (𝓝 T) :=
    Asymptotics.tendsto_floorBlockLength_div_sq_of_tendsto_atTop hscale hT0
  have hquot : Tendsto (fun n =>
      (Asymptotics.diffusiveBlockLength T scale n : ℝ) / (⌊w * scale n⌋₊ : ℝ) ^ 2)
      atTop (𝓝 (T / w ^ 2)) := by
    have hh := hlen.div (hfloor.pow 2) (pow_ne_zero 2 hw0.ne')
    apply hh.congr'
    filter_upwards [hsp] with n hn
    change ((Asymptotics.diffusiveBlockLength T scale n : ℝ) / scale n ^ 2) /
      ((⌊w * scale n⌋₊ : ℝ) / scale n) ^ 2 = _
    field_simp
  have hprob : Tendsto (fun n => Real.exp
      (-d * (Asymptotics.diffusiveBlockLength T scale n : ℝ) / (⌊w * scale n⌋₊ : ℝ) ^ 2))
      atTop (𝓝 (Real.exp (-d * T / w ^ 2))) := by
    simpa only [Function.comp_def, mul_div_assoc] using
      (Real.continuous_exp.tendsto (-d * (T / w ^ 2))).comp (hquot.const_mul (-d))
  have hprob' : ∀ᶠ n in atTop,
      p < Real.exp (-d * (Asymptotics.diffusiveBlockLength T scale n : ℝ) /
        (⌊w * scale n⌋₊ : ℝ) ^ 2) := by
    exact hprob.eventually (Ioi_mem_nhds hp)
  have hmargin := hD.eventually_ge_atTop (1 / (e / (8 * w)))
  have hsmallDrift : ∀ᶠ n in atTop,
      c / scale n ^ 2 * (Asymptotics.diffusiveBlockLength T scale n : ℝ) ≤ e * scale n := by
    filter_upwards [hsp, hscale.eventually_ge_atTop (c * T / e)] with n hn hlarge
    have hfl : (Asymptotics.diffusiveBlockLength T scale n : ℝ) ≤ T * scale n ^ 2 :=
      Nat.floor_le (by positivity)
    have hleft := mul_le_mul_of_nonneg_left hfl (show 0 ≤ c / scale n ^ 2 by positivity)
    have heq : c / scale n ^ 2 * (T * scale n ^ 2) = c * T := by field_simp
    rw [heq] at hleft
    exact hleft.trans (by simpa only [mul_comm] using (div_le_iff₀ he).1 hlarge)
  filter_upwards [hsp, hprob', hmargin, hsmallDrift,
    hfloorTop.eventually_ge_atTop D₀] with n hn hpn hmarg hsd hD₀
  let L := scale n
  let b := Asymptotics.diffusiveBlockLength T scale n
  have hratioBound : Q₀ * ⌊w * L⌋₊ ^ 2 ≤ b := by
    apply Nat.le_floor
    have hfl : (⌊w * L⌋₊ : ℝ) ≤ L :=
      (Nat.floor_le (by positivity)).trans (by nlinarith)
    have hfl0 : (0 : ℝ) ≤ (⌊w * L⌋₊ : ℝ) := Nat.cast_nonneg _
    have hsq : (⌊w * L⌋₊ : ℝ) ^ 2 ≤ L ^ 2 := by nlinarith
    push_cast
    exact (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg Q₀)).trans
      (mul_le_mul_of_nonneg_right (by linarith : (Q₀ : ℝ) ≤ T) (sq_nonneg L))
  intro x
  have hx : (x : ℝ) ∈ Set.Icc (-3 * (e * L)) (3 * (e * L)) := by
    simpa only [mul_assoc] using x.property
  obtain ⟨i, hi, hnear⟩ := exists_nearbyEndpointWindowIndex (mul_pos he hn) hx
  let l : Fin 7 := ⟨(i + 3).toNat, by simp only [Finset.mem_Icc] at hi; omega⟩
  have hil : (l.val : ℝ) - 3 = (i : ℝ) := by
    exact_mod_cast (show (l.val : ℤ) - 3 = i by dsimp [l]; simp only [Finset.mem_Icc] at hi; omega)
  let U := (w / 2 + ((l.val : ℝ) - 3 - 1 / 4) * e) / w
  let V := (w / 2 + ((l.val : ℝ) - 3 + 1 / 4) * e) / w
  have hsrc := hbound l (w * L) U V (e / (8 * w)) (mul_pos hw0 hn)
    (by positivity) hD₀ hmarg
    (le_of_eq (by dsimp [U, u]; field_simp; ring))
    (le_of_eq (by dsimp [V, v]; field_simp; ring)) b hratioBound
  let A := horizontalTubeEndpointWindowEvent (1 / 2) (w * L) b U V
  have hA : MeasurableSet A := by
    exact (measurableSet_inHorizontalTube _ _ _).inter
      (measurableSet_Icc.preimage (displacement_measurable b))
  have hproject : (iidSequenceLaw ν) {ω | (fun j => (ω j).1) ∈ A} =
      iidSequenceLaw incrementLaw A := by
    rw [← iidSequenceLaw_map_coordinatewise ν Prod.fst measurable_fst]
    exact (Measure.map_apply (show Measurable (fun ω : ℕ → ℝ × ℝ =>
      fun j => (ω j).1) from by fun_prop) hA).symm
  rw [Kernel.returnKernel_apply_univ,
    Kernel.pow_apply_ofPartialStep_eq_iidSequenceLaw ν _ _ measurableSet_Icc]
  refine ((ENNReal.ofReal_le_ofReal hpn.le).trans hsrc).trans ?_
  change iidSequenceLaw incrementLaw A ≤ _
  rw [← hproject]
  apply measure_mono
  intro ω hω
  change Kernel.EndsInPrefix _ _ _ _ ω
  rw [endsInPrefix_killedMarkedStep_iff]
  have hends : AdditivePath.displacement b (fun j => (ω j).1) ∈
      Set.Icc ((i : ℝ) * (e * L) - (e * L) / 4)
        ((i : ℝ) * (e * L) + (e * L) / 4) := by
    have hlower : (U - 1 / 2) * (w * L) = (i : ℝ) * (e * L) - (e * L) / 4 := by
      dsimp [U]; rw [← hil]; field_simp; ring
    have hupper : (V - 1 / 2) * (w * L) = (i : ℝ) * (e * L) + (e * L) / 4 := by
      dsimp [V]; rw [← hil]; field_simp; ring
    simpa only [hlower, hupper] using hω.2
  have hfit : (w * L) / 2 + 4 * (e * L) ≤ L / 2 := by
    dsimp [e]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hw1.le) hn.le]
  have hgeom := band_subset_driftedReturn (D := w * L) (radius := L / 2)
    (drift := c / L ^ 2) (mul_pos he hn) (by positivity) hsd hfit hx hnear _ hω.1 hends
  simpa only [e, L, b, mul_assoc] using hgeom

end ProbabilityTheory.RandomWalk.SmallDeviation.Marked
