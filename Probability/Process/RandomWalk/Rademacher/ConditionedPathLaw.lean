/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Rademacher.TerminalPathLaw
public import Probability.Process.RandomWalk.FunctionalLimit.Conditioned.Survival.Conditioning

/-!
# Boolean and real forms of the conditioned Rademacher path law

The public theorems in this file are:

- `ProbabilityTheory.RandomWalk.measure_booleanSurvival_eq_realSurvival`:
  the survival mass of a Boolean $\pm1$ block equals the mass of
  $C_r^+$ under the real Rademacher IID law.
- `ProbabilityTheory.RandomWalk.measure_booleanAbsolutePath_inter_survival_eq_realPath`:
  for $r>0$, the joint probability of positive survival and an
  absolute-path event equals that of survival and the ordinary
  normalized polygonal path under the real Rademacher law.
- `ProbabilityTheory.RandomWalk.booleanAbsoluteBlock_conditionalProbability_eq_survivalConditionedPath`:
  the normalized Boolean absolute-block probability equals the path law
  of the real Rademacher walk conditioned to survive nonnegatively.
- `ProbabilityTheory.RandomWalk.measure_terminalAbsolutePath_atIndex_eq_conditionedPath`:
  for every $0\le m<n$ and Borel path set $A$,
  $\mathbb P(\mu_n=m,\widetilde Y_n\in A)
   =\mathbb P(\mu_n=m)\mathbb P(Y_{n-m}^{+}\in A)$.
- `ProbabilityTheory.RandomWalk.measure_terminalAbsolutePath_atLength_eq_conditionedPath`:
  for $1\le r\le n$,
  $\mathbb P(\nu_n=r,\widetilde Y_n\in A)
   =\mathbb P(\nu_n=r)\mathbb P(Y_r^{+}\in A)$.

These identities connect the simple-symmetric-walk argument on page 484
of Erwin Bolthausen, *On a functional central limit theorem for random
walks conditioned to stay positive*, Ann. Probab. 4(3) (1976), 480--485, DOI 10.1214/aop/1176996098,
Theorem 3.2, to its nonnegative-survival conditional law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk

open FunctionalLimit.Conditioned

/-- The Boolean and real encodings of the simple symmetric walk give
the same probability to finite nonnegative survival. -/
theorem measure_booleanSurvival_eq_realSurvival (length : ℕ) :
    (iidSequenceLaw fairBoolMeasure)
        ((Combinatorics.Sequence.blockCoordinates 0 length) ⁻¹'
          positiveSurvivesBlock length) =
      (iidSequenceLaw rademacherMeasure)
        {increment : ℕ → ℝ | SurvivesNonnegative length increment} := by
  let survival : Set (ℕ → ℝ) :=
    {increment | SurvivesNonnegative length increment}
  have hpre : rademacherIncrementPath ⁻¹' survival =
      (Combinatorics.Sequence.blockCoordinates 0 length) ⁻¹'
        positiveSurvivesBlock length := by
    ext branch
    simp only [Set.mem_preimage, survival, Set.mem_ofPred_eq]
    simpa only [Nat.zero_add] using
      (positiveSurvivesBlock_shift_iff branch 0 length).symm
  rw [← map_iidSequenceLaw_rademacherIncrementPath,
    Measure.map_apply measurable_rademacherIncrementPath
      (measurableSet_survivesNonnegative length)]
  exact congrArg (iidSequenceLaw fairBoolMeasure) hpre.symm

/-- On the positive survival event, the absolute Boolean-block path
is exactly the ordinary normalized real Rademacher polygonal path. -/
theorem measure_booleanAbsolutePath_inter_survival_eq_realPath
    (length : ℕ) (hlength : 0 < length)
    (pathEvent : Set C(unitInterval, ℝ)) (hpathEvent : MeasurableSet pathEvent) :
    (iidSequenceLaw fairBoolMeasure)
        ((Combinatorics.Sequence.blockCoordinates 0 length) ⁻¹'
          ({block | absoluteRademacherBlockPath length block ∈ pathEvent} ∩
            positiveSurvivesBlock length)) =
      (iidSequenceLaw rademacherMeasure)
        {increment : ℕ → ℝ |
          SurvivesNonnegative length increment ∧
          normalizedLinearContinuousPathIcc
            (fun j => Real.sqrt j) length increment ∈ pathEvent} := by
  let realEvent : Set (ℕ → ℝ) :=
    {increment | SurvivesNonnegative length increment ∧
      normalizedLinearContinuousPathIcc
        (fun j => Real.sqrt j) length increment ∈ pathEvent}
  have hrealEvent : MeasurableSet realEvent :=
    (measurableSet_survivesNonnegative length).inter
      (hpathEvent.preimage
        (measurable_normalizedLinearContinuousPathIcc
          (fun j => Real.sqrt j) length))
  have hpre : rademacherIncrementPath ⁻¹' realEvent =
      (Combinatorics.Sequence.blockCoordinates 0 length) ⁻¹'
        ({block | absoluteRademacherBlockPath length block ∈ pathEvent} ∩
          positiveSurvivesBlock length) := by
    ext branch
    let block := Combinatorics.Sequence.blockCoordinates 0 length branch
    have hsurvive : block ∈ positiveSurvivesBlock length ↔
        SurvivesNonnegative length (rademacherIncrementPath branch) := by
      simpa only [Nat.zero_add] using
        positiveSurvivesBlock_shift_iff branch 0 length
    have hpath : normalizedLinearContinuousPathIcc
        (fun j => Real.sqrt j) length
        (rademacherIncrementPath branch) =
      normalizedLinearContinuousPathFromBlock
        (fun j => Real.sqrt j) length
        (fun j => rademacherOfBool (block j)) := by
      have h := normalizedLinearContinuousPathFromBlock_blockCoordinates
        (fun j => Real.sqrt j) length 0 (rademacherIncrementPath branch)
      have hblock : Combinatorics.Sequence.blockCoordinates 0 length
          (rademacherIncrementPath branch) =
          (fun j => rademacherOfBool (block j)) := by
        funext j
        rfl
      rw [hblock] at h
      simpa only [Nat.zero_add] using h.symm
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq,
      realEvent]
    constructor
    · rintro ⟨hsurv, hmem⟩
      have hblockSurv := hsurvive.mpr hsurv
      refine ⟨?_, hblockSurv⟩
      rw [absoluteRademacherBlockPath_eq_linear_of_survives
        length hlength block hblockSurv, ← hpath]
      exact hmem
    · rintro ⟨hmem, hblockSurv⟩
      refine ⟨hsurvive.mp hblockSurv, ?_⟩
      rw [hpath, ← absoluteRademacherBlockPath_eq_linear_of_survives
        length hlength block hblockSurv]
      exact hmem
  rw [← map_iidSequenceLaw_rademacherIncrementPath,
    Measure.map_apply measurable_rademacherIncrementPath hrealEvent]
  exact congrArg (iidSequenceLaw fairBoolMeasure) hpre.symm

/-- The positive-survival-conditioned absolute Boolean-block path has
the ordinary survival-conditioned real Rademacher path law. -/
theorem booleanAbsoluteBlock_conditionalProbability_eq_survivalConditionedPath
    (length : ℕ) (hlength : 0 < length)
    (pathEvent : Set C(unitInterval, ℝ)) (hpathEvent : MeasurableSet pathEvent) :
    (iidSequenceLaw fairBoolMeasure)
        ((Combinatorics.Sequence.blockCoordinates 0 length) ⁻¹'
          ({block | absoluteRademacherBlockPath length block ∈ pathEvent} ∩
            positiveSurvivesBlock length)) /
      (iidSequenceLaw fairBoolMeasure)
        ((Combinatorics.Sequence.blockCoordinates 0 length) ⁻¹'
          positiveSurvivesBlock length) =
    ((survivalConditionedLaw rademacherMeasure length).map
      (normalizedLinearContinuousPathIcc
        (fun j => Real.sqrt j) length)) pathEvent := by
  rw [measure_booleanAbsolutePath_inter_survival_eq_realPath
      length hlength pathEvent hpathEvent,
    measure_booleanSurvival_eq_realSurvival]
  rw [Measure.map_apply
    (measurable_normalizedLinearContinuousPathIcc
      (fun j => Real.sqrt j) length) hpathEvent,
    survivalConditionedLaw,
    ProbabilityTheory.cond_apply (measurableSet_survivesNonnegative length)]
  change (iidSequenceLaw rademacherMeasure)
      {increment : ℕ → ℝ |
        SurvivesNonnegative length increment ∧
        normalizedLinearContinuousPathIcc
          (fun j => Real.sqrt j) length increment ∈ pathEvent} /
      (iidSequenceLaw rademacherMeasure)
        {increment : ℕ → ℝ | SurvivesNonnegative length increment} =
    ((iidSequenceLaw rademacherMeasure)
      {increment : ℕ → ℝ | SurvivesNonnegative length increment})⁻¹ *
      (iidSequenceLaw rademacherMeasure)
        {increment : ℕ → ℝ |
          SurvivesNonnegative length increment ∧
          normalizedLinearContinuousPathIcc
            (fun j => Real.sqrt j) length increment ∈ pathEvent}
  rw [div_eq_mul_inv]
  ac_rfl

/-- Bolthausen's finite-length law identity: conditional on the
last-sign-change index, the terminal absolute path has the same law
as an independent walk conditioned to remain nonnegative for the
corresponding number of steps. -/
theorem measure_terminalAbsolutePath_atIndex_eq_conditionedPath
    (n start : ℕ) (hstart : start < n)
    (pathEvent : Set C(unitInterval, ℝ)) (hpathEvent : MeasurableSet pathEvent) :
    (iidSequenceLaw fairBoolMeasure)
        {branch : ℕ → Bool |
          lastSignChangeIndex n (rademacherIncrementPath branch) = start ∧
          rademacherTerminalAbsolutePath branch n ∈ pathEvent} =
      (iidSequenceLaw fairBoolMeasure)
        {branch : ℕ → Bool |
          lastSignChangeIndex n (rademacherIncrementPath branch) = start} *
        ((survivalConditionedLaw rademacherMeasure (n - start)).map
          (normalizedLinearContinuousPathIcc
            (fun j => Real.sqrt j) (n - start))) pathEvent := by
  rw [measure_terminalAbsolutePath_conditional_formula
      n start hstart pathEvent hpathEvent,
    booleanAbsoluteBlock_conditionalProbability_eq_survivalConditionedPath
      (n - start) (by omega) pathEvent hpathEvent]

/-- The same joint-law identity indexed by the terminal length
`νₙ = n - μₙ`, exactly as used in Bolthausen's final paragraph. -/
theorem measure_terminalAbsolutePath_atLength_eq_conditionedPath
    (n length : ℕ) (hlength : 0 < length) (hlen : length ≤ n)
    (pathEvent : Set C(unitInterval, ℝ)) (hpathEvent : MeasurableSet pathEvent) :
    (iidSequenceLaw fairBoolMeasure)
        {branch : ℕ → Bool |
          terminalSignStableLength n (rademacherIncrementPath branch) = length ∧
          rademacherTerminalAbsolutePath branch n ∈ pathEvent} =
      (iidSequenceLaw fairBoolMeasure)
        {branch : ℕ → Bool |
          terminalSignStableLength n (rademacherIncrementPath branch) = length} *
        ((survivalConditionedLaw rademacherMeasure length).map
          (normalizedLinearContinuousPathIcc
            (fun j => Real.sqrt j) length)) pathEvent := by
  have hstart : n - length < n := by omega
  have hcell (branch : ℕ → Bool) :
      terminalSignStableLength n (rademacherIncrementPath branch) = length ↔
      lastSignChangeIndex n (rademacherIncrementPath branch) = n - length := by
    unfold terminalSignStableLength
    have hindex := lastSignChangeIndex_le n (rademacherIncrementPath branch)
    omega
  have hjoinSet : {branch : ℕ → Bool |
      terminalSignStableLength n (rademacherIncrementPath branch) = length ∧
      rademacherTerminalAbsolutePath branch n ∈ pathEvent} =
      {branch : ℕ → Bool |
        lastSignChangeIndex n (rademacherIncrementPath branch) = n - length ∧
        rademacherTerminalAbsolutePath branch n ∈ pathEvent} := by
    ext branch
    simp only [Set.mem_ofPred_eq, hcell]
  have hcellSet : {branch : ℕ → Bool |
      terminalSignStableLength n (rademacherIncrementPath branch) = length} =
      {branch : ℕ → Bool |
        lastSignChangeIndex n (rademacherIncrementPath branch) = n - length} := by
    ext branch
    exact hcell branch
  rw [hjoinSet, hcellSet]
  simpa only [Nat.sub_sub_self hlen] using
    measure_terminalAbsolutePath_atIndex_eq_conditionedPath
      n (n - length) hstart pathEvent hpathEvent

end ProbabilityTheory.RandomWalk

end
