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
# Finite-variance transition blocks in the marked-corridor proof

## Internal proof declarations

* `ProbabilityTheory.RandomWalk.SmallDeviation.Marked.exists_eventually_transitionBlock_ge`:
  for centered finite-variance increments and internal source and target
  centers `a,b`, unmarked transitions from `(a±3e)Lₙ` to `(b±3e)Lₙ`
  in a width-`Lₙ` drifted corridor have probability at least `p`,
  uniformly over block lengths between `⌊TLₙ²⌋` and `M⌊TLₙ²⌋`,
  whenever `p<exp(-dMT/w²)`, for sufficiently large fixed `T` and
  eventually as `Lₙ→∞`. Here `d>π²σ²/2`; the statement supplies the
  explicit source, target and wall margins for the seven-band construction.

The original displacement law is used throughout. The seven endpoint-window
bounds call the existing real-width form of Wang Yiyang, *Asymptotic Speed
of the N-Branching Random Walk with Infinite Offspring* (Fudan University,
2026), Chapter 3, Lemma 3.1(ii). Its source is A. A. Mogul'skii,
*Small deviations in the sample function space*, Theorem 3, Section 4,
p. 764 (1974); English translation *Small Deviations in a Space of
Trajectories*, DOI 10.1137/1119081.
The finite-band selection and deterministic drift containment support the
zero-tail-constant concatenation in B. Mallein, *Necessary and sufficient
conditions for the convergence of the consistent maximal displacement of
the branching random walk*, §2.2, Theorem 2.3 and proof of Lemma 2.5,
arXiv:1510.00602v2.
-/

open MeasureTheory Filter
open scoped ENNReal Topology
namespace ProbabilityTheory.RandomWalk.SmallDeviation.Marked
open HorizontalTube HorizontalTube.EndpointWindow

set_option backward.isDefEq.respectTransparency false

lemma exists_eventually_transitionBlock_ge
    (ν : Measure (ℝ × ℝ)) [IsProbabilityMeasure ν]
    {sigma w e a b d : ℝ}
    (hν : IsCenteredSecondMoment (ν.map Prod.fst) (sigma ^ 2))
    (hσ : 0 < sigma) (hw : 0 < w) (he : 0 < e)
    (ha : -w / 2 < a) (ha' : a < w / 2)
    (hb : -w / 2 + 4 * e < b) (hb' : b < w / 2 - 4 * e)
    (hfit : w / 2 + 4 * e ≤ 1 / 2)
    (hd : (Real.pi ^ 2 / 2) * sigma ^ 2 < d) :
    ∃ T₀ : ℝ, 0 ≤ T₀ ∧ ∀ T > T₀, ∀ M : ℕ, 1 ≤ M → ∀ {scale : ℕ → ℝ},
      Tendsto scale atTop atTop → ∀ c ≥ 0, ∀ p : ℝ,
      p < Real.exp (-d * (M : ℝ) * T / w ^ 2) →
      ∀ᶠ n in atTop, ∀ length : ℕ,
        Asymptotics.diffusiveBlockLength T scale n ≤ length →
        length ≤ M * Asymptotics.diffusiveBlockLength T scale n →
        ∀ x : ℝ, x ∈ Set.Icc ((a - 3 * e) * scale n) ((a + 3 * e) * scale n) →
        ENNReal.ofReal p ≤
          (Kernel.ofPartialStep ν
            (killedMarkedStep (-(scale n / 2)) (scale n / 2) (c / scale n ^ 2))
            (killedMarkedStep_measurable _ _ _) ^ length) x
          (Set.Icc ((b - 3 * e) * scale n) ((b + 3 * e) * scale n)) := by
  let incrementLaw := ν.map Prod.fst
  let : IsProbabilityMeasure incrementLaw := inferInstance
  have hw0 := hw
  let aTube := (1 / 2 : ℝ) + a / w
  let u (l : Fin 7) := (w / 2 + b + ((l.val : ℝ) - 3 - 1 / 8) * e) / w
  let v (l : Fin 7) := (w / 2 + b + ((l.val : ℝ) - 3 + 1 / 8) * e) / w
  have hl (l : Fin 7) : 0 ≤ (l.val : ℝ) ∧ (l.val : ℝ) ≤ 6 := by
    constructor
    · positivity
    · exact_mod_cast (show l.val ≤ 6 by omega)
  obtain ⟨D₀, Q₀, hbound⟩ := exists_uniform_finiteRealWidthTubeProbability_ge_exp
    hν hσ (fun _ : Fin 7 => aTube) u v
    (by intro; dsimp [aTube]; have hh : -(1 / 2 : ℝ) < a / w := (lt_div_iff₀ hw).2 (by linarith); linarith)
    (by intro; dsimp [aTube]; have hh : a / w < (1 / 2 : ℝ) := (div_lt_iff₀ hw).2 (by linarith); linarith)
    (by intro l; exact div_pos (by nlinarith [(hl l).1]) hw0)
    (by intro l; apply (div_lt_div_iff_of_pos_right hw0).2; nlinarith)
    (by intro l; apply (div_lt_one hw0).2; nlinarith [(hl l).2]) hd
  refine ⟨Q₀ + 1, by positivity, ?_⟩
  intro T hT M hM scale hscale c hc p hp
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
      (-d * (M : ℝ) * (Asymptotics.diffusiveBlockLength T scale n : ℝ) / (⌊w * scale n⌋₊ : ℝ) ^ 2))
      atTop (𝓝 (Real.exp (-d * (M : ℝ) * T / w ^ 2))) := by
    simpa only [Function.comp_def, mul_div_assoc] using
      (Real.continuous_exp.tendsto (-d * (M : ℝ) * (T / w ^ 2))).comp (hquot.const_mul (-d * (M : ℝ)))
  have hprob' : ∀ᶠ n in atTop,
      p < Real.exp (-d * (M : ℝ) * (Asymptotics.diffusiveBlockLength T scale n : ℝ) /
        (⌊w * scale n⌋₊ : ℝ) ^ 2) := by
    exact hprob.eventually (Ioi_mem_nhds hp)
  have hmargin := hD.eventually_ge_atTop (1 / (e / (8 * w)))
  have hsmallDrift : ∀ᶠ n in atTop,
      c / scale n ^ 2 * ((M : ℝ) * (Asymptotics.diffusiveBlockLength T scale n : ℝ)) ≤ e * scale n := by
    filter_upwards [hsp, hscale.eventually_ge_atTop (c * (M : ℝ) * T / e)] with n hn hlarge
    have hfl : (Asymptotics.diffusiveBlockLength T scale n : ℝ) ≤ T * scale n ^ 2 :=
      Nat.floor_le (by positivity)
    have hflM := mul_le_mul_of_nonneg_left hfl (Nat.cast_nonneg M)
    have hleft := mul_le_mul_of_nonneg_left hflM (show 0 ≤ c / scale n ^ 2 by positivity)
    have heq : c / scale n ^ 2 * ((M : ℝ) * (T * scale n ^ 2)) = c * (M : ℝ) * T := by field_simp
    rw [heq] at hleft
    exact hleft.trans (by simpa only [mul_comm] using (div_le_iff₀ he).1 hlarge)
  filter_upwards [hsp, hprob', hmargin, hsmallDrift,
    hfloorTop.eventually_ge_atTop D₀] with n hn hpn hmarg hsd hD₀
  let L := scale n
  let block := Asymptotics.diffusiveBlockLength T scale n
  intro length hmin hmax x hx
  have hmaxR : (length : ℝ) ≤ (M : ℝ) * block := by exact_mod_cast hmax
  have hsdLen : c / L ^ 2 * (length : ℝ) ≤ e * L :=
    (mul_le_mul_of_nonneg_left hmaxR (by positivity)).trans hsd
  have hratioBound : Q₀ * ⌊w * L⌋₊ ^ 2 ≤ block := by
    apply Nat.le_floor
    have hfl : (⌊w * L⌋₊ : ℝ) ≤ L :=
      (Nat.floor_le (by positivity)).trans (by nlinarith [hfit])
    have hfl0 : (0 : ℝ) ≤ (⌊w * L⌋₊ : ℝ) := Nat.cast_nonneg _
    have hsq : (⌊w * L⌋₊ : ℝ) ^ 2 ≤ L ^ 2 := by nlinarith
    push_cast
    exact (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg Q₀)).trans
      (mul_le_mul_of_nonneg_right (by linarith : (Q₀ : ℝ) ≤ T) (sq_nonneg L))
  have hxNear : x - a * L ∈ Set.Icc (-3 * (e * L)) (3 * (e * L)) := by
    constructor <;> nlinarith [hx.1, hx.2]
  obtain ⟨i, hi, hnear⟩ := exists_nearbyEndpointWindowIndex (mul_pos he hn) hxNear
  let l : Fin 7 := ⟨(i + 3).toNat, by simp only [Finset.mem_Icc] at hi; omega⟩
  have hil : (l.val : ℝ) - 3 = (i : ℝ) := by
    exact_mod_cast (show (l.val : ℤ) - 3 = i by dsimp [l]; simp only [Finset.mem_Icc] at hi; omega)
  let U := (w / 2 + b + ((l.val : ℝ) - 3 - 1 / 4) * e) / w
  let V := (w / 2 + b + ((l.val : ℝ) - 3 + 1 / 4) * e) / w
  have hsrc := hbound l (w * L) U V (e / (8 * w)) (mul_pos hw0 hn)
    (by positivity) hD₀ hmarg
    (le_of_eq (by dsimp [U, u]; field_simp; ring))
    (le_of_eq (by dsimp [V, v]; field_simp; ring)) length (hratioBound.trans hmin)
  let A := horizontalTubeEndpointWindowEvent aTube (w * L) length U V
  have hA : MeasurableSet A := by
    exact (measurableSet_inHorizontalTube _ _ _).inter
      (measurableSet_Icc.preimage (displacement_measurable length))
  have hproject : (iidSequenceLaw ν) {ω | (fun j => (ω j).1) ∈ A} =
      iidSequenceLaw incrementLaw A := by
    rw [← iidSequenceLaw_map_coordinatewise ν Prod.fst measurable_fst]
    exact (Measure.map_apply (show Measurable (fun ω : ℕ → ℝ × ℝ =>
      fun j => (ω j).1) from by fun_prop) hA).symm
  rw [Kernel.pow_apply_ofPartialStep_eq_iidSequenceLaw ν _ _ measurableSet_Icc]
  have hrate : p ≤ Real.exp (-d * (length : ℝ) / (⌊w * L⌋₊ : ℝ) ^ 2) := by
    refine hpn.le.trans (Real.exp_le_exp.mpr ?_)
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    have hd0 : 0 < d := lt_of_le_of_lt (by positivity) hd
    nlinarith [hmaxR]
  refine ((ENNReal.ofReal_le_ofReal hrate).trans hsrc).trans ?_
  change iidSequenceLaw incrementLaw A ≤ _
  rw [← hproject]
  apply measure_mono
  intro ω hω
  change Kernel.EndsInPrefix _ _ _ _ ω
  rw [endsInPrefix_killedMarkedStep_iff]
  have hends : AdditivePath.displacement length (fun j => (ω j).1) ∈
      Set.Icc (b * L - a * L + (i : ℝ) * (e * L) - (e * L) / 4)
        (b * L - a * L + (i : ℝ) * (e * L) + (e * L) / 4) := by
    have hlower : (U - aTube) * (w * L) = b * L - a * L + (i : ℝ) * (e * L) - (e * L) / 4 := by
      dsimp [U, aTube]; rw [← hil]; field_simp; ring
    have hupper : (V - aTube) * (w * L) = b * L - a * L + (i : ℝ) * (e * L) + (e * L) / 4 := by
      dsimp [V, aTube]; rw [← hil]; field_simp; ring
    simpa only [hlower, hupper] using hω.2
  have hfitL : (w * L) / 2 + 4 * (e * L) ≤ L / 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hfit hn.le]
  have hpath : StaysIn (Set.Icc (-(w * L) / 2 - a * L)
      ((w * L) / 2 - a * L)) length 0 (fun j => (ω j).1) := by
    intro k
    have hk := hω.1 k
    have hlo : -aTube * (w * L) = -(w * L) / 2 - a * L := by
      dsimp [aTube]; field_simp; ring
    have hhi : (1 - aTube) * (w * L) = (w * L) / 2 - a * L := by
      dsimp [aTube]; field_simp; ring
    simpa only [hlo, hhi, zero_add, Set.mem_Icc] using hk
  have hgeom := band_subset_driftedTransition (D := w * L) (radius := L / 2)
    (drift := c / L ^ 2) (mul_pos he hn) (by positivity) hsdLen hfitL hxNear hnear _ hpath hends
  simpa only [sub_mul, add_mul, mul_assoc, L] using hgeom

end ProbabilityTheory.RandomWalk.SmallDeviation.Marked
