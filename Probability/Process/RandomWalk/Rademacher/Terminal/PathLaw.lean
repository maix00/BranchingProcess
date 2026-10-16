/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Rademacher.Terminal.Law
public import Probability.Process.RandomWalk.Path.Interpolation.Finite.Block

/-!
# Absolute polygonal paths from finite Rademacher blocks

The public definitions and theorems in this file are:

- `ProbabilityTheory.RandomWalk.absoluteRademacherBlockPath`:
  $b\mapsto\left|\widetilde S_b(t)/\sqrt r\right|$ in
  $C([0,1],\mathbb R)$, where $\widetilde S_b$ is the polygonal
  interpolation of a length-$r$ Boolean $\pm1$ block.
- `ProbabilityTheory.RandomWalk.measurable_absoluteRademacherBlockPath`:
  this finite-block path map is Borel measurable.
- `ProbabilityTheory.RandomWalk.absoluteRademacherBlockPath_flip`:
  simultaneous reversal of all steps leaves this absolute path unchanged.
- `ProbabilityTheory.RandomWalk.absoluteRademacherBlockPath_eq_linear_of_survives`:
  on $C_r^+$, the absolute path equals the ordinary nonnegative
  polygonal interpolation.
- `ProbabilityTheory.RandomWalk.rademacherTerminalAbsolutePath_eq_blockPath`:
  on $\{\mu_n=m\}$, Bolthausen's terminal path is the absolute path
  of the block of the next $n-m$ increments.
- `ProbabilityTheory.RandomWalk.measure_terminalAbsolutePath_conditioned_identity`:
  for a Borel path event $A$ and $0<m<n$,
  $\mathbb P(\mu_n=m,\widetilde Y_n\in A)\mathbb P(C_{n-m}^+)
   =\mathbb P(\mu_n=m)\mathbb P(Y_{n-m}\in A,C_{n-m}^+)$.
- `ProbabilityTheory.RandomWalk.measure_initialTerminalAbsolutePath_conditioned_identity`:
  the same identity for $m=0$ and $n>0$.
- `ProbabilityTheory.RandomWalk.measure_terminalAbsolutePath_conditioned_identity_of_lt`:
  the identity holds for every $0\le m<n$.
- `ProbabilityTheory.RandomWalk.measure_terminalAbsolutePath_conditional_formula`:
  for every $0\le m<n$, the joint path probability is the mass of
  $\{\mu_n=m\}$ times the positive-survival-conditioned block probability.

These are the path-level consequences of the definition of
$\widetilde Y_n$ on page 484 of Erwin Bolthausen,
*On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Ann. Probab. 4(3) (1976), 480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

namespace ProbabilityTheory.RandomWalk

open MeasureTheory
open scoped ENNReal

/-- The absolute normalized polygonal path of a finite fair-Boolean
increment block. -/
noncomputable def absoluteRademacherBlockPath
    (length : ℕ) (block : Fin length → Bool) : C(unitInterval, ℝ) where
  toFun t := |normalizedLinearContinuousPathFromBlock
    (fun j => Real.sqrt j) length
    (fun j => rademacherOfBool (block j)) t|
  continuous_toFun := continuous_abs.comp
    (normalizedLinearContinuousPathFromBlock
      (fun j => Real.sqrt j) length
      (fun j => rademacherOfBool (block j))).continuous

/-- Every function on a finite Boolean block space is measurable. -/
theorem measurable_absoluteRademacherBlockPath (length : ℕ) :
    Measurable (absoluteRademacherBlockPath length) :=
  measurable_of_countable _

private lemma normalizedLinearContinuousPathFromBlock_neg
    (scale : ℕ → ℝ) (length : ℕ) (block : Fin length → ℝ) :
    normalizedLinearContinuousPathFromBlock scale length
        (fun j => -block j) =
      -normalizedLinearContinuousPathFromBlock scale length block := by
  have hext : extendFiniteIncrementBlock length (fun j => -block j) =
      fun k => -extendFiniteIncrementBlock length block k := by
    funext k
    by_cases hk : k < length <;> simp [extendFiniteIncrementBlock, hk]
  ext t
  change normalizedLinearPath scale length
      (extendFiniteIncrementBlock length (fun j => -block j)) t =
    -normalizedLinearPath scale length
      (extendFiniteIncrementBlock length block) t
  rw [hext, normalizedLinearPath_neg]

/-- Reflection changes the sign of the polygonal path and hence
preserves its absolute value at every time. -/
theorem absoluteRademacherBlockPath_flip
    (length : ℕ) (block : Fin length → Bool) :
    absoluteRademacherBlockPath length (fun j => !block j) =
      absoluteRademacherBlockPath length block := by
  have hneg : (fun j : Fin length => rademacherOfBool (!block j)) =
      (fun j => -rademacherOfBool (block j)) := by
    funext j
    cases block j <;> simp [rademacherOfBool]
  ext t
  change |normalizedLinearContinuousPathFromBlock
      (fun j => Real.sqrt j) length
      (fun j => rademacherOfBool (!block j)) t| =
    |normalizedLinearContinuousPathFromBlock
      (fun j => Real.sqrt j) length
      (fun j => rademacherOfBool (block j)) t|
  rw [hneg, normalizedLinearContinuousPathFromBlock_neg, ContinuousMap.neg_apply,
    abs_neg]

/-- A surviving finite block has a nonnegative polygonal path, so
absolute value leaves that path unchanged. -/
theorem absoluteRademacherBlockPath_eq_linear_of_survives
    (length : ℕ) (hlength : 0 < length) (block : Fin length → Bool)
    (hsurvive : block ∈ positiveSurvivesBlock length) :
    absoluteRademacherBlockPath length block =
      normalizedLinearContinuousPathFromBlock
        (fun j => Real.sqrt j) length
        (fun j => rademacherOfBool (block j)) := by
  let realBlock : Fin length → ℝ := fun j => rademacherOfBool (block j)
  have hblock : Combinatorics.Sequence.blockCoordinates 0 length
      (extendFiniteIncrementBlock length realBlock) = realBlock := by
    funext j
    simp [Combinatorics.Sequence.blockCoordinates,
      extendFiniteIncrementBlock, j.isLt]
  have hsurviveReal : SurvivesNonnegative length
      (extendFiniteIncrementBlock length realBlock) := by
    have h := (finiteSurvivesNonnegative_blockCoordinates_iff
      length 0 (extendFiniteIncrementBlock length realBlock)).1
    rw [hblock] at h
    simpa only [Nat.zero_add] using h hsurvive
  have hscale : 0 < Real.sqrt (length : ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast hlength)
  have hnonneg := hsurviveReal.normalizedLinearCadlagPathIcc_nonnegative
    (fun j => Real.sqrt j) hlength hscale
  ext t
  change |normalizedLinearContinuousPathIcc
      (fun j => Real.sqrt j) length
      (extendFiniteIncrementBlock length realBlock) t| =
    normalizedLinearContinuousPathIcc
      (fun j => Real.sqrt j) length
      (extendFiniteIncrementBlock length realBlock) t
  exact abs_of_nonneg (hnonneg t)

/-- Once the last-sign-change index is fixed, the terminal path is
the absolute path generated by exactly that following finite block. -/
theorem rademacherTerminalAbsolutePath_eq_blockPath
    (branch : ℕ → Bool) (n start : ℕ)
    (hμ : lastSignChangeIndex n (rademacherIncrementPath branch) = start) :
    rademacherTerminalAbsolutePath branch n =
      absoluteRademacherBlockPath (n - start)
        (Combinatorics.Sequence.blockCoordinates start (n - start) branch) := by
  have hlength : terminalSignStableLength n
      (rademacherIncrementPath branch) = n - start := by
    simp [terminalSignStableLength, hμ]
  have hblock : (fun j : Fin (n - start) =>
      rademacherOfBool
        (Combinatorics.Sequence.blockCoordinates start (n - start) branch j)) =
      Combinatorics.Sequence.blockCoordinates start (n - start)
        (rademacherIncrementPath branch) := by
    funext j
    rfl
  ext t
  change |normalizedLinearContinuousPathIcc
      (fun j => Real.sqrt j)
      (terminalSignStableLength n (rademacherIncrementPath branch))
      (fun j => rademacherIncrementPath branch
        (lastSignChangeIndex n (rademacherIncrementPath branch) + j)) t| =
    |normalizedLinearContinuousPathFromBlock
      (fun j => Real.sqrt j) (n - start)
      (fun j => rademacherOfBool
        (Combinatorics.Sequence.blockCoordinates start (n - start) branch j)) t|
  rw [hμ, hlength, hblock,
    normalizedLinearContinuousPathFromBlock_blockCoordinates]

/-- For each positive last-sign-change index, the absolute terminal
path has the nonnegative-survival-conditioned finite-block law.
The identity is cross-multiplied, so it does not require a division
or a separately chosen conditional-probability construction. -/
theorem measure_terminalAbsolutePath_conditioned_identity
    (n start : ℕ) (hstart : 0 < start) (hbefore : start < n)
    (pathEvent : Set C(unitInterval, ℝ)) (hpathEvent : MeasurableSet pathEvent) :
    (iidSequenceLaw fairBoolMeasure)
        {branch : ℕ → Bool |
          lastSignChangeIndex n (rademacherIncrementPath branch) = start ∧
          rademacherTerminalAbsolutePath branch n ∈ pathEvent} *
      (iidSequenceLaw fairBoolMeasure)
        ((Combinatorics.Sequence.blockCoordinates 0 (n - start)) ⁻¹'
          positiveSurvivesBlock (n - start)) =
    (iidSequenceLaw fairBoolMeasure)
        {branch : ℕ → Bool |
          lastSignChangeIndex n (rademacherIncrementPath branch) = start} *
      (iidSequenceLaw fairBoolMeasure)
        ((Combinatorics.Sequence.blockCoordinates 0 (n - start)) ⁻¹'
          ({block | absoluteRademacherBlockPath (n - start) block ∈ pathEvent} ∩
            positiveSurvivesBlock (n - start))) := by
  let event : Set (Fin (n - start) → Bool) :=
    {block | absoluteRademacherBlockPath (n - start) block ∈ pathEvent}
  have hevent : MeasurableSet event :=
    hpathEvent.preimage (measurable_absoluteRademacherBlockPath (n - start))
  have hinvariant (block : Fin (n - start) → Bool) :
      (fun j => !block j) ∈ event ↔ block ∈ event := by
    simp only [event, Set.mem_ofPred_eq, absoluteRademacherBlockPath_flip]
  have h := measure_terminalBlock_conditioned_identity
    n start hstart hbefore event hevent hinvariant
  have hset : {branch : ℕ → Bool |
      lastSignChangeIndex n (rademacherIncrementPath branch) = start ∧
      rademacherTerminalAbsolutePath branch n ∈ pathEvent} =
      {branch : ℕ → Bool |
        lastSignChangeIndex n (rademacherIncrementPath branch) = start} ∩
        (Combinatorics.Sequence.blockCoordinates start (n - start)) ⁻¹' event := by
    ext branch
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      event]
    constructor
    · rintro ⟨hμ, hpath⟩
      exact ⟨hμ, (rademacherTerminalAbsolutePath_eq_blockPath
        branch n start hμ) ▸ hpath⟩
    · rintro ⟨hμ, hpath⟩
      exact ⟨hμ, (rademacherTerminalAbsolutePath_eq_blockPath
        branch n start hμ).symm ▸ hpath⟩
  rw [hset]
  exact h

/-- The same finite-path conditional-law identity when the entire
walk, starting at time zero, is the selected one-sided segment. -/
theorem measure_initialTerminalAbsolutePath_conditioned_identity
    (n : ℕ) (hn : 0 < n)
    (pathEvent : Set C(unitInterval, ℝ)) (hpathEvent : MeasurableSet pathEvent) :
    (iidSequenceLaw fairBoolMeasure)
        {branch : ℕ → Bool |
          lastSignChangeIndex n (rademacherIncrementPath branch) = 0 ∧
          rademacherTerminalAbsolutePath branch n ∈ pathEvent} *
      (iidSequenceLaw fairBoolMeasure)
        ((Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹'
          positiveSurvivesBlock n) =
    (iidSequenceLaw fairBoolMeasure)
        {branch : ℕ → Bool |
          lastSignChangeIndex n (rademacherIncrementPath branch) = 0} *
      (iidSequenceLaw fairBoolMeasure)
        ((Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹'
          ({block | absoluteRademacherBlockPath n block ∈ pathEvent} ∩
            positiveSurvivesBlock n)) := by
  let event : Set (Fin n → Bool) :=
    {block | absoluteRademacherBlockPath n block ∈ pathEvent}
  have hevent : MeasurableSet event :=
    hpathEvent.preimage (measurable_absoluteRademacherBlockPath n)
  have hinvariant (block : Fin n → Bool) :
      (fun j => !block j) ∈ event ↔ block ∈ event := by
    simp only [event, Set.mem_ofPred_eq, absoluteRademacherBlockPath_flip]
  have h := measure_initialTerminalBlock_conditioned_identity
    n hn event hevent hinvariant
  have hset : {branch : ℕ → Bool |
      lastSignChangeIndex n (rademacherIncrementPath branch) = 0 ∧
      rademacherTerminalAbsolutePath branch n ∈ pathEvent} =
      {branch : ℕ → Bool |
        lastSignChangeIndex n (rademacherIncrementPath branch) = 0} ∩
        (Combinatorics.Sequence.blockCoordinates 0 n) ⁻¹' event := by
    ext branch
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      event]
    constructor
    · rintro ⟨hμ, hpath⟩
      exact ⟨hμ, (rademacherTerminalAbsolutePath_eq_blockPath
        branch n 0 hμ) ▸ hpath⟩
    · rintro ⟨hμ, hpath⟩
      exact ⟨hμ, (rademacherTerminalAbsolutePath_eq_blockPath
        branch n 0 hμ).symm ▸ hpath⟩
  rw [hset]
  exact h

/-- The finite conditional-law identity for every possible last-sign-change
index strictly before the terminal time. -/
theorem measure_terminalAbsolutePath_conditioned_identity_of_lt
    (n start : ℕ) (hstart : start < n)
    (pathEvent : Set C(unitInterval, ℝ)) (hpathEvent : MeasurableSet pathEvent) :
    (iidSequenceLaw fairBoolMeasure)
        {branch : ℕ → Bool |
          lastSignChangeIndex n (rademacherIncrementPath branch) = start ∧
          rademacherTerminalAbsolutePath branch n ∈ pathEvent} *
      (iidSequenceLaw fairBoolMeasure)
        ((Combinatorics.Sequence.blockCoordinates 0 (n - start)) ⁻¹'
          positiveSurvivesBlock (n - start)) =
    (iidSequenceLaw fairBoolMeasure)
        {branch : ℕ → Bool |
          lastSignChangeIndex n (rademacherIncrementPath branch) = start} *
      (iidSequenceLaw fairBoolMeasure)
        ((Combinatorics.Sequence.blockCoordinates 0 (n - start)) ⁻¹'
          ({block | absoluteRademacherBlockPath (n - start) block ∈ pathEvent} ∩
            positiveSurvivesBlock (n - start))) := by
  by_cases hzero : start = 0
  · subst start
    simpa using measure_initialTerminalAbsolutePath_conditioned_identity
      n (by omega) pathEvent hpathEvent
  · exact measure_terminalAbsolutePath_conditioned_identity
      n start (Nat.pos_of_ne_zero hzero) hstart pathEvent hpathEvent

/-- The explicit finite conditional distribution of the terminal
absolute path, with the positive survival probability in the
denominator. -/
theorem measure_terminalAbsolutePath_conditional_formula
    (n start : ℕ) (hstart : start < n)
    (pathEvent : Set C(unitInterval, ℝ)) (hpathEvent : MeasurableSet pathEvent) :
    (iidSequenceLaw fairBoolMeasure)
        {branch : ℕ → Bool |
          lastSignChangeIndex n (rademacherIncrementPath branch) = start ∧
          rademacherTerminalAbsolutePath branch n ∈ pathEvent} =
      (iidSequenceLaw fairBoolMeasure)
        {branch : ℕ → Bool |
          lastSignChangeIndex n (rademacherIncrementPath branch) = start} *
        ((iidSequenceLaw fairBoolMeasure)
          ((Combinatorics.Sequence.blockCoordinates 0 (n - start)) ⁻¹'
            ({block | absoluteRademacherBlockPath (n - start) block ∈ pathEvent} ∩
              positiveSurvivesBlock (n - start))) /
          (iidSequenceLaw fairBoolMeasure)
            ((Combinatorics.Sequence.blockCoordinates 0 (n - start)) ⁻¹'
              positiveSurvivesBlock (n - start))) := by
  let survivalMass : ℝ≥0∞ := (iidSequenceLaw fairBoolMeasure)
    ((Combinatorics.Sequence.blockCoordinates 0 (n - start)) ⁻¹'
      positiveSurvivesBlock (n - start))
  have hpositive : survivalMass ≠ 0 :=
    ne_of_gt (positiveSurvivesBlock_probability_pos (n - start))
  have hfinite : survivalMass ≠ ∞ := measure_ne_top _ _
  have hcross := measure_terminalAbsolutePath_conditioned_identity_of_lt
    n start hstart pathEvent hpathEvent
  change _ * survivalMass = _ * _ at hcross
  rw [mul_comm _ survivalMass] at hcross
  have hdiv := (ENNReal.eq_div_iff hpositive hfinite).2 hcross
  rw [mul_div_assoc] at hdiv
  exact hdiv

end ProbabilityTheory.RandomWalk

end
