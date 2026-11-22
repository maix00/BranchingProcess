/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Path.Corridor.Horizontal.Core
public import Probability.Sequence.IID.Basic
public import Mathlib.Probability.Process.HittingTime
public import Mathlib.Basic.Real.ENatENNReal
public import Probability.Distributions.Moments.Real
import Probability.Sequence.IID.Blocks.Consecutive
import Probability.Distributions.Moments.Signs
import Mathlib.Basic.ENNReal.BigOperators
import Mathlib.Data.Fin.Rev
import MeasureTheory.Function.FinPartialSum

/-!
# Mean exit time from the upper boundary of a horizontal corridor

## Public declarations

* `ProbabilityTheory.RandomWalk.tsum_horizontalTubeProbability_upperBoundary_le`:
  if $p=\nu(({-\infty},-\delta])>0$ and $\delta>0$, then
  $\sum_{n\ge0}\mathbb P_\nu(S_1,\ldots,S_n\in[-w,0])
    \le (w+\delta)/(\delta p)$ for $w\ge0$.

* `upperBoundaryExitTime` is $\tau_w=\inf\{j\ge1:S_j\notin[-w,0]\}$.
* `lintegral_upperBoundaryExitTime_eq_tsum` gives
  $\mathbb E_\nu[\tau_w]=\sum_{n\ge0}\mathbb P_\nu(\tau_w>n)$.
* `exists_lintegral_upperBoundaryExitTime_le_linear` gives
  $\mathbb E_\nu[\tau_w]\le Cw$ for all $w\ge1$ when $\nu$ has zero mean
  and finite positive variance.

Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring* (Fudan University, 2026), Chapter 3, Lemma 3.8, uses the linear
mean exit time from the boundary in the proof of equation (3.11).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.RandomWalk

private lemma partialSum_rev_eq {n : ℕ} (x : Fin n → ℝ) (i : Fin (n + 1)) :
    Fin.partialSum (fun j => x (Fin.rev j)) i =
      Fin.partialSum x (Fin.last n) - Fin.partialSum x i.rev := by
  induction i using Fin.induction with
  | zero =>
      rw [Fin.partialSum_zero]
      have h : (0 : Fin (n + 1)).rev = Fin.last n := Fin.ext (by simp)
      rw [h, sub_self]
  | succ j ih =>
      rw [Fin.partialSum_succ, ih]
      have h₁ : j.rev.castSucc = j.succ.rev := Fin.ext (by simp [Fin.val_rev])
      have h₂ : j.rev.succ = j.castSucc.rev := Fin.ext (by simp [Fin.val_rev]; omega)
      have hstep := Fin.partialSum_succ x j.rev
      rw [h₁, h₂] at hstep
      rw [hstep]
      ring

private def upperBoundaryRecord (width : ℝ) (n : ℕ) : Set (Fin n → ℝ) :=
  {x | -width ≤ Fin.partialSum x (Fin.last n) ∧
    ∀ i : Fin (n + 1), Fin.partialSum x (Fin.last n) ≤ Fin.partialSum x i}

private lemma measurableSet_upperBoundaryRecord (width : ℝ) (n : ℕ) :
    MeasurableSet (upperBoundaryRecord width n) := by
  rw [show upperBoundaryRecord width n = ({x | -width ≤ Fin.partialSum x (Fin.last n)} ∩
    ⋂ i : Fin (n + 1), {x | Fin.partialSum x (Fin.last n) ≤ Fin.partialSum x i}) by ext x; simp [upperBoundaryRecord]]
  exact (measurableSet_le measurable_const (Fin.measurable_partialSum _)).inter
    (MeasurableSet.iInter fun _ =>
      measurableSet_le (Fin.measurable_partialSum _) (Fin.measurable_partialSum _))

private lemma tubeProbability_le_record (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {width : ℝ} (hw : 0 ≤ width) (n : ℕ) :
    horizontalTubeProbability (iidSequenceLaw ν) 1 width n ≤
      (Measure.pi (fun _ : Fin n => ν)) (upperBoundaryRecord width n) := by
  let initialVector (z : ℕ → ℝ) (i : Fin n) := z i.val
  let reverse (x : Fin n → ℝ) (i : Fin n) := x i.rev
  have hp : Measurable initialVector := measurable_pi_iff.mpr fun i => measurable_pi_apply i.val
  have hr : MeasurePreserving reverse (Measure.pi (fun _ : Fin n => ν))
      (Measure.pi (fun _ : Fin n => ν)) := by
    have heq : reverse = MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℝ) Fin.revPerm := by
      funext x i
      rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast, cast_eq,
        Fin.revPerm_symm]
      rfl
    rw [heq]
    exact measurePreserving_piCongrLeft (fun _ : Fin n => ν) Fin.revPerm
  have he : MeasurableSet (upperBoundaryRecord width n) := measurableSet_upperBoundaryRecord _ _
  calc
    _ ≤ iidSequenceLaw ν (initialVector ⁻¹' (reverse ⁻¹' upperBoundaryRecord width n)) := by
      apply measure_mono
      intro z hz
      have hpath (j : ℕ) (hj : j ≤ n) :
          -width ≤ AdditivePath.displacement j z ∧ AdditivePath.displacement j z ≤ 0 := by
        cases j with
        | zero => simpa using hw
        | succ j =>
          have h := hz ⟨j, by omega⟩
          simpa using h
      change reverse (initialVector z) ∈ upperBoundaryRecord width n
      refine ⟨?_, fun i => ?_⟩
      · change -width ≤ Fin.partialSum (fun j => initialVector z j.rev) (Fin.last n)
        rw [partialSum_rev_eq (initialVector z), Fin.rev_last, Fin.partialSum_zero, sub_zero]
        exact (hpath n le_rfl).1.trans_eq
          (AdditivePath.partialSum_eq_displacement z (Fin.last n)).symm
      · change Fin.partialSum (fun j => initialVector z j.rev) (Fin.last n) ≤
          Fin.partialSum (fun j => initialVector z j.rev) i
        rw [partialSum_rev_eq (initialVector z), partialSum_rev_eq (initialVector z),
          Fin.rev_last, Fin.partialSum_zero, sub_zero]
        have hi := (hpath i.rev.val (by omega)).2
        rw [← AdditivePath.partialSum_eq_displacement z i.rev] at hi
        linarith
    _ = (Measure.pi (fun _ : Fin n => ν)) (reverse ⁻¹' upperBoundaryRecord width n) := by
      rw [← Measure.map_apply hp (hr.measurable he)]
      exact congrArg (fun μ : Measure (Fin n → ℝ) => μ _) (iidSequenceLaw_map_finPrefix ν n)
    _ = _ := by rw [← Measure.map_apply hr.measurable he, hr.map_eq]

private def runningDepth (z : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => max (runningDepth z n) (-AdditivePath.displacement (n + 1) z)

private lemma runningDepth_le (z : ℕ → ℝ) (n : ℕ) (r : ℝ) (hr : 0 ≤ r)
    (h : ∀ i ≤ n, -AdditivePath.displacement i z ≤ r) : runningDepth z n ≤ r := by
  induction n with
  | zero => exact hr
  | succ n ih =>
    exact max_le (ih fun i hi => h i (by omega)) (h (n + 1) le_rfl)

open Combinatorics.Sequence in
/-- After reversal, the terminal minimum is at depth at most the corridor
width. A next downward step of size at least δ increases the running
depth capped at width + δ by at least δ. Summing the capped increases
bounds the expected number of record opportunities. -/
theorem tsum_horizontalTubeProbability_upperBoundary_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {width δ : ℝ}
    (hw : 0 ≤ width) (hδ : 0 < δ) (hjump : 0 < ν (Set.Iic (-δ))) :
    (∑' n : ℕ, horizontalTubeProbability (iidSequenceLaw ν) 1 width n) ≤
      ENNReal.ofReal (width + δ) / (ENNReal.ofReal δ * ν (Set.Iic (-δ))) := by
  classical
  let P := iidSequenceLaw ν
  let A (n : ℕ) := (blockCoordinates 0 n) ⁻¹' upperBoundaryRecord width n
  let E (n : ℕ) := A n ∩ {z : ℕ → ℝ | z n ≤ -δ}
  let p := ν (Set.Iic (-δ))
  have hA (n : ℕ) : MeasurableSet (A n) :=
    (measurableSet_upperBoundaryRecord _ _).preimage (measurable_blockCoordinates _ _)
  have hE (n : ℕ) : MeasurableSet (E n) :=
    (hA n).inter (measurableSet_Iic.preimage (measurable_pi_apply n))
  have hfactors (n : ℕ) : P (E n) = P (A n) * p := by
    have hindep := indepFun_blockCoordinates_blockCoordinates ν 0 n 1
    have h := hindep.measure_inter_preimage_eq_mul (upperBoundaryRecord width n)
        ((fun x : Fin 1 → ℝ => x 0) ⁻¹' Set.Iic (-δ))
        (measurableSet_upperBoundaryRecord _ _)
        (measurableSet_Iic.preimage (measurable_pi_apply 0))
    have heq : blockCoordinates (0 + n) 1 ⁻¹' ((fun x : Fin 1 → ℝ => x 0) ⁻¹' Set.Iic (-δ)) =
        (fun z : ℕ → ℝ => z n) ⁻¹' Set.Iic (-δ) := by
      ext z
      simp [blockCoordinates]
    rw [heq] at h
    change P (E n) = P (A n) *
      (iidSequenceLaw ν) ((fun z : ℕ → ℝ => z n) ⁻¹' Set.Iic (-δ)) at h
    rw [← Measure.map_apply (measurable_pi_apply n) measurableSet_Iic,
      iidSequenceLaw_map_apply] at h
    exact h
  have hprob (n : ℕ) : horizontalTubeProbability P 1 width n ≤ P (A n) := by
    refine (tubeProbability_le_record ν hw n).trans_eq ?_
    change _ = P ((blockCoordinates 0 n) ⁻¹' upperBoundaryRecord width n)
    rw [← Measure.map_apply (measurable_blockCoordinates 0 n)
      (measurableSet_upperBoundaryRecord _ _)]
    have hmap : blockCoordinates (E := ℝ) 0 n = (fun z i => z i.val) := by
      funext z i
      simp [blockCoordinates]
    rw [hmap, iidSequenceLaw_map_finPrefix]
  let depth (z : ℕ → ℝ) (n : ℕ) := min (width + δ) (runningDepth z n)
  have hmono (z : ℕ → ℝ) (n : ℕ) : depth z n ≤ depth z (n + 1) :=
    min_le_min_left _ (le_max_left _ _)
  have hstep (z : ℕ → ℝ) (n : ℕ) (hz : z ∈ E n) : δ ≤ depth z (n + 1) - depth z n := by
    have hrec := hz.1
    change blockCoordinates 0 n z ∈ upperBoundaryRecord width n at hrec
    have hcoords : blockCoordinates 0 n z = (fun i : Fin n => z i.val) := by
      funext i
      simp [blockCoordinates]
    rw [hcoords] at hrec
    have hterminal : -width ≤ AdditivePath.displacement n z := by
      simpa only [blockCoordinates, Nat.zero_add, AdditivePath.partialSum_eq_displacement,
        Fin.val_last] using hrec.1
    have hminimum (i : ℕ) (hi : i ≤ n) :
        AdditivePath.displacement n z ≤ AdditivePath.displacement i z := by
      simpa only [blockCoordinates, Nat.zero_add, AdditivePath.partialSum_eq_displacement,
        Fin.val_last] using (hrec.2 ⟨i, by omega⟩)
    have hprev : depth z n ≤ -AdditivePath.displacement n z :=
      (min_le_right _ _).trans
        (runningDepth_le z n _ (by simpa using hminimum 0 (Nat.zero_le n))
          (fun i hi => neg_le_neg (hminimum i hi)))
    have hj : z n ≤ -δ := hz.2
    have hnext : -AdditivePath.displacement n z + δ ≤ depth z (n + 1) := by
      apply le_min
      · linarith
      · apply le_trans _ (le_max_right (runningDepth z n) _)
        rw [AdditivePath.displacement_succ]
        linarith
    linarith
  let f (n : ℕ) : (ℕ → ℝ) → ℝ≥0∞ := (E n).indicator fun _ => ENNReal.ofReal δ
  have hsum (N : ℕ) (z : ℕ → ℝ) :
      (∑ n ∈ Finset.range N, f n z) ≤ ENNReal.ofReal (depth z N) := by
    induction N with
    | zero => simp
    | succ N ih =>
      have hinc : f N z ≤ ENNReal.ofReal (depth z (N + 1) - depth z N) := by
        by_cases hz : z ∈ E N
        · simpa only [f, Set.indicator_of_mem hz] using ENNReal.ofReal_le_ofReal (hstep z N hz)
        · simp [f, Set.indicator_of_notMem hz]
      have hn : 0 ≤ depth z N := by
        have hzero : depth z 0 = 0 := by
          change min (width + δ) 0 = 0
          exact min_eq_right (add_nonneg hw hδ.le)
        have hm : Monotone (depth z) := monotone_nat_of_le_succ (hmono z)
        exact hzero ▸ hm (Nat.zero_le N)
      rw [Finset.sum_range_succ]
      refine (add_le_add ih hinc).trans_eq ?_
      rw [← ENNReal.ofReal_add hn (sub_nonneg.mpr (hmono z N))]
      congr 1
      ring
  have hfinite (N : ℕ) :
      (∑ n ∈ Finset.range N, horizontalTubeProbability P 1 width n) *
        (ENNReal.ofReal δ * p) ≤ ENNReal.ofReal (width + δ) := by
    rw [Finset.sum_mul]
    calc
      _ ≤ ∑ n ∈ Finset.range N, ENNReal.ofReal δ * P (E n) := by
        apply Finset.sum_le_sum
        intro n _
        rw [hfactors]
        calc
          _ ≤ P (A n) * (ENNReal.ofReal δ * p) := mul_le_mul_left (hprob n) _
          _ = _ := by ac_rfl
      _ = ∫⁻ z, ∑ n ∈ Finset.range N, f n z ∂P := by
        rw [lintegral_finsetSum _ (fun n _ => measurable_const.indicator (hE n))]
        apply Finset.sum_congr rfl
        intro n _
        change _ = ∫⁻ z, (E n).indicator (fun _ => ENNReal.ofReal δ) z ∂P
        rw [lintegral_indicator (hE n), lintegral_const, Measure.restrict_apply_univ]
      _ ≤ ∫⁻ _ : ℕ → ℝ, ENNReal.ofReal (width + δ) ∂P :=
        lintegral_mono fun z => (hsum N z).trans (ENNReal.ofReal_le_ofReal (min_le_left _ _))
      _ = _ := by simp [P]
  rw [ENNReal.tsum_eq_iSup_nat]
  apply iSup_le
  intro N
  have hden : ENNReal.ofReal δ * p ≠ 0 := mul_ne_zero (ENNReal.ofReal_pos.mpr hδ).ne' hjump.ne'
  exact (ENNReal.le_div_iff_mul_le (Or.inl hden)
    (Or.inl (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)))).2 (hfinite N)

/-- First positive time at which the walk leaves the closed interval
`[-width, 0]`, with infinity for a path that never exits. -/
noncomputable def upperBoundaryExitTime (width : ℝ) (z : ℕ → ℝ) : ℕ∞ :=
  hittingAfter AdditivePath.displacement (Set.Icc (-width) 0)ᶜ 1 z

private lemma upperBoundaryExitTime_gt_iff (width : ℝ) (z : ℕ → ℝ) (n : ℕ) :
    (n : ℕ∞) < upperBoundaryExitTime width z ↔ InHorizontalTube 1 width n z := by
  have heq : (n : ℕ∞) < upperBoundaryExitTime width z ↔
      ¬ ∃ j ∈ Set.Icc (1 : ℕ) n, AdditivePath.displacement j z ∉ Set.Icc (-width) 0 := by
    rw [lt_iff_not_ge]
    exact not_congr (hittingAfter_le_iff (u := AdditivePath.displacement (E := ℝ))
      (s := (Set.Icc (-width) 0)ᶜ) (n := 1) (i := n) (ω := z))
  rw [heq]
  simp only [not_exists, not_and, not_not]
  constructor
  · intro h i
    have hj : (i.val + 1) ∈ Set.Icc (1 : ℕ) n := ⟨by omega, by omega⟩
    simpa only [Set.mem_Icc, neg_one_mul, sub_self, zero_mul] using h (i.val + 1) hj
  · intro h j hj
    have hj' : j - 1 + 1 = j := by have := hj.1; omega
    have hi := h ⟨j - 1, by have := hj.2; omega⟩
    simpa only [hj', Set.mem_Icc, neg_one_mul, sub_self, zero_mul] using hi

private lemma tsum_indicator_nat_lt (m : ℕ∞) :
    (∑' n : ℕ, if (n : ℕ∞) < m then (1 : ℝ≥0∞) else 0) = (m : ℝ≥0∞) := by
  cases m using ENat.recTopCoe with
  | top =>
    simp only [ENat.natCast_lt_top, ite_true, ENat.toENNReal_top, ENNReal.tsum_eq_iSup_nat,
      Finset.sum_const, Finset.card_range, nsmul_one, ENNReal.iSup_natCast]
  | coe k =>
    rw [tsum_eq_sum (s := Finset.range k)]
    · simp only [ENat.toENNReal_coe, ENat.natCast_lt_natCast]
      calc
        _ = ∑ _n ∈ Finset.range k, (1 : ℝ≥0∞) := by
          apply Finset.sum_congr rfl
          intro n hn
          simp [Finset.mem_range.mp hn]
        _ = _ := by simp
    · intro n hn
      simp [show ¬ n < k from fun h => hn (Finset.mem_range.mpr h)]

/-- Integrate the sum of the indicators of surviving each finite horizon. -/
theorem lintegral_upperBoundaryExitTime_eq_tsum (P : Measure (ℕ → ℝ)) (width : ℝ) :
    (∫⁻ z, (upperBoundaryExitTime width z : ℝ≥0∞) ∂P) =
      ∑' n : ℕ, horizontalTubeProbability P 1 width n := by
  let T (n : ℕ) : Set (ℕ → ℝ) := {z | InHorizontalTube 1 width n z}
  let f (n : ℕ) : (ℕ → ℝ) → ℝ≥0∞ := (T n).indicator (fun _ => 1)
  have hT (n : ℕ) : MeasurableSet (T n) := measurableSet_inHorizontalTube ..
  have hpoint (z : ℕ → ℝ) : (upperBoundaryExitTime width z : ℝ≥0∞) = ∑' n, f n z := by
    rw [← tsum_indicator_nat_lt (upperBoundaryExitTime width z)]
    apply tsum_congr
    intro n
    classical
    by_cases hn : InHorizontalTube 1 width n z
    · simp [f, T, hn, (upperBoundaryExitTime_gt_iff width z n).2 hn]
    · have hnot := mt (upperBoundaryExitTime_gt_iff width z n).1 hn
      simp [f, T, hn, hnot]
  simp_rw [hpoint]
  rw [lintegral_tsum (fun n => (measurable_const.indicator (hT n)).aemeasurable)]
  apply tsum_congr
  intro n
  exact lintegral_indicator_one (hT n)

private lemma exists_neg_jump (ν : Measure ℝ) (h : 0 < ν (Set.Iio 0)) :
    ∃ δ : ℝ, 0 < δ ∧ 0 < ν (Set.Iic (-δ)) := by
  let δ (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hδ (n : ℕ) : 0 < δ n := by dsimp [δ]; positivity
  by_contra! hnone
  have hcover : Set.Iio (0 : ℝ) = ⋃ n : ℕ, Set.Iic (-δ n) := by
    ext x
    simp only [Set.mem_Iio, Set.mem_iUnion, Set.mem_Iic]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (neg_pos.mpr hx)
      exact ⟨n, by linarith [show δ n < -x from hn]⟩
    · rintro ⟨n, hn⟩
      linarith [hδ n]
  rw [hcover, pos_iff_ne_zero] at h
  exact h (measure_iUnion_null_iff.mpr fun n => le_antisymm (hnone _ (hδ n)) bot_le)

/-- Linear mean exit time for the centered finite-variance spine in Wang
Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring* (Fudan University, 2026), Chapter 3, Lemma 3.8, equation (3.11).
The variance hypothesis supplies positive mass of downward steps. -/
theorem exists_lintegral_upperBoundaryExitTime_le_linear
    (ν : Measure ℝ) [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2)) (hsigma : 0 < sigma) :
    ∃ C : ℝ, 0 < C ∧ ∀ width : ℝ, 1 ≤ width →
      (∫⁻ z, (upperBoundaryExitTime width z : ℝ≥0∞) ∂iidSequenceLaw ν) ≤
        ENNReal.ofReal (C * width) := by
  obtain ⟨δ, hδ, hjump⟩ := exists_neg_jump ν (hν.measure_Iio_zero_pos hsigma)
  let p := (ν (Set.Iic (-δ))).toReal
  have hp : 0 < p := ENNReal.toReal_pos hjump.ne' (measure_ne_top _ _)
  have hp' : ENNReal.ofReal p = ν (Set.Iic (-δ)) :=
    ENNReal.ofReal_toReal (measure_ne_top _ _)
  refine ⟨(1 + δ) / (δ * p), by positivity, fun width hw => ?_⟩
  rw [lintegral_upperBoundaryExitTime_eq_tsum]
  refine (tsum_horizontalTubeProbability_upperBoundary_le ν
    (zero_le_one.trans hw) hδ hjump).trans ?_
  rw [← hp', ← ENNReal.ofReal_mul hδ.le, ← ENNReal.ofReal_div_of_pos (mul_pos hδ hp)]
  apply ENNReal.ofReal_le_ofReal
  rw [div_mul_eq_mul_div]
  apply div_le_div_of_nonneg_right _ (mul_nonneg hδ.le hp.le)
  nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hw)]

end ProbabilityTheory.RandomWalk

end
