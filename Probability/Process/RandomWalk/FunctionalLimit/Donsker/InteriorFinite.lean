/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.FunctionalLimit.Donsker.InteriorCorridor
public import Probability.Process.RandomWalk.Path.Skorokhod.Corridor.Endpoint.Closed

/-!
# Finite-grid form of the middle-start entrance event

The public definitions and theorems in this file are:

- `ProbabilityTheory.RandomWalk.FunctionalLimit.Donsker.finiteInteriorEvent`:
  $c\le x+S_j\le\Delta$ for $1\le j\le n$, with
  $x+S_n\in[5\Delta/12,7\Delta/12]$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Donsker.mem_finiteInteriorEvent_iff_scaledPath`:
  this event equals the normalized path corridor at
  $z=x/\Delta$, $r=\sqrt n/\Delta$, and $o=c/\Delta$.
- `ProbabilityTheory.RandomWalk.FunctionalLimit.Donsker.eventually_finiteInteriorProbability_pos_uniform`:
  Donsker's theorem gives one positive lower bound for this finite event,
  uniformly over middle starting points.

This is the exact finite-grid identification for the middle starting
interval in Wang Yiyang, *Asymptotic speed of the $N$-branching random walk
with infinite offspring*, Appendix A.2, proof of the meander transition
lemma used in Chapter 3, Lemma 3.5.
-/

@[expose] public section

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace ProbabilityTheory.RandomWalk.FunctionalLimit.Donsker

/-- The finite random-walk event used for starts in the middle twelfths
of the entrance corridor. -/
def finiteInteriorEvent (n : ℕ) (width drift start : ℝ) :
    Set (ℕ → ℝ) :=
  {increment |
    (∀ k : Fin n,
      drift ≤ start + AdditivePath.displacement (k + 1) increment ∧
      start + AdditivePath.displacement (k + 1) increment ≤ width) ∧
    5 / 12 * width ≤ start + AdditivePath.displacement n increment ∧
    start + AdditivePath.displacement n increment ≤ 7 / 12 * width}

/-- A normalized translated corridor is an ordinary closed Skorokhod
endpoint corridor after solving the affine inequalities. -/
theorem scaledInteriorPathEvent_eq_closedCorridor
    {sigma ratio : ℝ} (hprod : 0 < ratio * sigma)
    (z offset : ℝ) :
    scaledInteriorPathEvent sigma z ratio offset =
      Skorokhod.rangeInClosedIntervalEndsIn
        ((offset - z) / (ratio * sigma))
        ((1 - z) / (ratio * sigma))
        ((5 / 12 - z) / (ratio * sigma))
        ((7 / 12 - z) / (ratio * sigma)) := by
  ext path
  simp only [scaledInteriorPathEvent, Set.mem_ofPred_eq,
    Skorokhod.mem_rangeInClosedIntervalEndsIn_iff]
  constructor
  · rintro ⟨hall, hlow, hhigh⟩
    constructor
    · intro t
      obtain ⟨hlo, hhi⟩ := hall t
      constructor
      · apply (div_le_iff₀ hprod).2
        nlinarith
      · apply (le_div_iff₀ hprod).2
        nlinarith
    · constructor
      · apply (div_le_iff₀ hprod).2
        nlinarith
      · apply (le_div_iff₀ hprod).2
        nlinarith
  · rintro ⟨hall, ⟨hlow, hhigh⟩⟩
    constructor
    · intro t
      obtain ⟨hlo, hhi⟩ := hall t
      constructor
      · have h := (div_le_iff₀ hprod).1 hlo
        nlinarith
      · have h := (le_div_iff₀ hprod).1 hhi
        nlinarith
    · constructor
      · have h := (div_le_iff₀ hprod).1 hlow
        nlinarith
      · have h := (le_div_iff₀ hprod).1 hhigh
        nlinarith

/-- The path-space corridor is exactly the finite-grid event in the
original random-walk coordinates. The initial value `start` lies in the
closed corridor, so the time-zero path value introduces no extra condition. -/
theorem mem_finiteInteriorEvent_iff_scaledPath
    {n : ℕ} (hn : 0 < n)
    {sigma width drift start : ℝ}
    (hsigma : 0 < sigma) (hwidth : 0 < width)
    (hstartLower : drift ≤ start) (hstartUpper : start ≤ width)
    (increment : ℕ → ℝ) :
    increment ∈ finiteInteriorEvent n width drift start ↔
      normalizedStepCadlagPathIcc
          (fun _ => sigma * Real.sqrt n) n increment ∈
        scaledInteriorPathEvent sigma (start / width)
          (Real.sqrt n / width) (drift / width) := by
  have hroot : 0 < Real.sqrt n := Real.sqrt_pos.2 (Nat.cast_pos.mpr hn)
  have hnorm : 0 < sigma * Real.sqrt n := mul_pos hsigma hroot
  have hratio : 0 < Real.sqrt n / width := div_pos hroot hwidth
  have hprod : 0 < Real.sqrt n / width * sigma := mul_pos hratio hsigma
  have hlower :
      (drift / width - start / width) /
          (Real.sqrt n / width * sigma) ≤ 0 := by
    apply div_nonpos_of_nonpos_of_nonneg
    · exact sub_nonpos.mpr (div_le_div_of_nonneg_right hstartLower hwidth.le)
    · exact hprod.le
  have hupper : 0 ≤
      (1 - start / width) / (Real.sqrt n / width * sigma) := by
    apply div_nonneg
    · exact sub_nonneg.mpr ((div_le_one hwidth).2 hstartUpper)
    · exact hprod.le
  have hlowerEq :
      (drift / width - start / width) /
          (Real.sqrt n / width * sigma) =
        (drift - start) / (sigma * Real.sqrt n) := by
    field_simp [hwidth.ne', hroot.ne', hsigma.ne']
  have honeEq :
      (1 - start / width) / (Real.sqrt n / width * sigma) =
        (width - start) / (sigma * Real.sqrt n) := by
    field_simp [hwidth.ne', hroot.ne', hsigma.ne']
  have hendpointEq (a : ℝ) :
      (a - start / width) / (Real.sqrt n / width * sigma) =
        (a * width - start) / (sigma * Real.sqrt n) := by
    field_simp [hwidth.ne', hroot.ne', hsigma.ne']
  rw [scaledInteriorPathEvent_eq_closedCorridor hprod]
  rw [normalizedStepCadlagPathIcc_mem_rangeInClosedIntervalEndsIn_iff_grid
    (fun _ => sigma * Real.sqrt n) hn hlower hupper]
  rw [hlowerEq, honeEq, hendpointEq (5 / 12),
    hendpointEq (7 / 12)]
  unfold finiteInteriorEvent InClosedCorridorOnGrid
  constructor
  · rintro ⟨hgrid, hendpointLower, hendpointUpper⟩
    constructor
    · intro k
      obtain ⟨hlo, hhi⟩ := hgrid k
      dsimp only
      rw [normalizedStepPath_grid (fun _ => sigma * Real.sqrt n) hn,
        inv_mul_eq_div]
      constructor
      · apply (div_le_div_iff_of_pos_right hnorm).2
        linarith
      · apply (div_le_div_iff_of_pos_right hnorm).2
        linarith
    · constructor
      · apply (div_le_div_iff_of_pos_right hnorm).2
        linarith
      · apply (div_le_div_iff_of_pos_right hnorm).2
        linarith
  · rintro ⟨hgrid, hendpointLower, hendpointUpper⟩
    constructor
    · intro k
      have hk := hgrid k
      dsimp only at hk
      rw [normalizedStepPath_grid (fun _ => sigma * Real.sqrt n) hn,
        inv_mul_eq_div] at hk
      obtain ⟨hlo, hhi⟩ := hk
      constructor
      · have h := (div_le_div_iff_of_pos_right hnorm).1 hlo
        linarith
      · have h := (div_le_div_iff_of_pos_right hnorm).1 hhi
        linarith
    · constructor
      · have h := (div_le_div_iff_of_pos_right hnorm).1 hendpointLower
        linarith
      · have h := (div_le_div_iff_of_pos_right hnorm).1 hendpointUpper
        linarith

/-- The middle-start finite event has one positive lower bound for all
sufficiently large diffusive horizons. The scale and boundary limits are
the ones used in Wang Yiyang, Appendix A.2. -/
theorem eventually_finiteInteriorProbability_pos_uniform
    {ν : Measure ℝ} [IsProbabilityMeasure ν] {sigma : ℝ}
    (hν : IsCenteredSecondMoment ν (sigma ^ 2)) (hsigma : 0 < sigma)
    {P : Measure (CadlagPath unitInterval ℝ)} [IsProbabilityMeasure P]
    (hP : IsStableClockProcessLaw 2 (gaussianReal 0 1)
      UnitInterval.clock P)
    {length : ℕ → ℕ} (hlength : Tendsto length atTop atTop)
    {width : ℕ → ℝ}
    (hwidth : ∀ᶠ n : ℕ in atTop, 0 < width n)
    {drift : ℝ}
    (hstart : ∀ᶠ n : ℕ in atTop, drift ≤ width n / 12)
    (hratio : Tendsto (fun n => Real.sqrt (length n) / width n)
      atTop (𝓝 1))
    (hoffset : Tendsto (fun n => drift / width n) atTop (𝓝 0)) :
    ∃ q : ℝ≥0∞, 0 < q ∧ ∀ᶠ n : ℕ in atTop,
      ∀ start ∈ Set.Icc (width n / 12) (11 / 12 * width n),
        q ≤ iidSequenceLaw ν
          (finiteInteriorEvent (length n) (width n) drift start) := by
  obtain ⟨q, hq, hbase⟩ :=
    eventually_interiorPathProbability_pos_uniform hν hsigma hP
  have hbaseLength : ∀ᶠ n : ℕ in atTop,
      ∀ z ∈ Set.Icc (1 / 12) (11 / 12),
        q ≤ iidSequenceLaw ν
          {increment | normalizedStepCadlagPathIcc
            (fun _ => sigma * Real.sqrt (length n)) (length n) increment ∈
              interiorPathEvent sigma z} :=
    hlength.eventually hbase
  have hratioLower : ∀ᶠ n : ℕ in atTop,
      99 / 100 ≤ Real.sqrt (length n) / width n := by
    filter_upwards [hratio.eventually (Ioi_mem_nhds (by norm_num :
      (99 / 100 : ℝ) < 1))] with n hn
    exact hn.le
  have hratioUpper : ∀ᶠ n : ℕ in atTop,
      Real.sqrt (length n) / width n ≤ 101 / 100 := by
    filter_upwards [hratio.eventually (Iio_mem_nhds (by norm_num :
      (1 : ℝ) < 101 / 100))] with n hn
    exact hn.le
  have hoffsetUpper : ∀ᶠ n : ℕ in atTop,
      drift / width n ≤ 1 / 100 := by
    filter_upwards [hoffset.eventually (Iio_mem_nhds (by norm_num :
      (0 : ℝ) < 1 / 100))] with n hn
    exact hn.le
  refine ⟨q, hq, ?_⟩
  filter_upwards [hbaseLength, hratioLower, hratioUpper, hoffsetUpper,
    hwidth, hstart, hlength.eventually (eventually_gt_atTop 0)] with
    n hn hrlo hrhi ho hw hs hlen
  intro start hstartRange
  have hz : start / width n ∈ Set.Icc (1 / 12) (11 / 12) := by
    constructor
    · exact (le_div_iff₀ hw).2 (by nlinarith [hstartRange.1])
    · exact (div_le_iff₀ hw).2 (by nlinarith [hstartRange.2])
  have hstartLower : drift ≤ start :=
    hs.trans hstartRange.1
  have hstartUpper : start ≤ width n := by
    nlinarith [hstartRange.2, hw.le]
  exact (hn (start / width n) hz).trans (measure_mono (by
    intro increment hinc
    have hscaled := interiorPathEvent_subset_scaledInteriorPathEvent
      hz hrlo hrhi ho hinc
    exact (mem_finiteInteriorEvent_iff_scaledPath hlen hsigma hw
      hstartLower hstartUpper increment).2 hscaled))

end ProbabilityTheory.RandomWalk.FunctionalLimit.Donsker

end
