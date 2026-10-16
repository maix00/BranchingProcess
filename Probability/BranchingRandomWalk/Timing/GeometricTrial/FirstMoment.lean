/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Probability.Independence.Integration

/-!
# First moments of marked geometric trials

The mark of a trial is generally dependent on whether that same trial splits.
For a cycle, failed trials contribute a failure mark `Y`, while the successful
trial may contribute a different mark `Z`. The lemmas here keep those marks
inside their own trial events and use independence only between the current
trial and the preceding failure prefix.
-/

open MeasureTheory
open scoped BigOperators ENNReal

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- The event that the first `n` trials all fail. The current trial at index
`n` is not included, so this event is independent of its mark for an iid
sequence. -/
def geometricFailurePrefix (X : ℕ → Ω → α) (B : Set α) (n : ℕ) : Set Ω :=
  ⋂ i ∈ Finset.range n, X i ⁻¹' Bᶜ

theorem measurableSet_geometricFailurePrefix
    {X : ℕ → Ω → α} {B : Set α}
    (hX : ∀ i, Measurable (X i)) (hB : MeasurableSet B) (n : ℕ) :
    MeasurableSet (geometricFailurePrefix X B n) := by
  unfold geometricFailurePrefix
  exact MeasurableSet.biInter (Finset.countable_toSet (Finset.range n)) fun i hi =>
    MeasurableSet.preimage hB.compl (hX i)

/-- A reward on trial `n` is counted exactly when all earlier trials failed. -/
noncomputable def geometricPrefixRewardTerm
    (X : ℕ → Ω → α) (B : Set α) (R : α → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => R (X n ω) *
    (geometricFailurePrefix X B n).indicator (fun _ => (1 : ℝ)) ω

private lemma indep_geometricFailurePrefix_current
    (μ : Measure Ω) (X : ℕ → Ω → α)
    (hX : ∀ i, Measurable (X i)) (hXi : iIndepFun X μ)
    (B : Set α) (hB : MeasurableSet B) (R : α → ℝ) (hR : Measurable R)
    (n : ℕ) :
    IndepFun (fun ω => R (X n ω))
      ((geometricFailurePrefix X B n).indicator (fun _ => (1 : ℝ))) μ := by
  classical
  let past : Finset ℕ := Finset.range n
  let current : Finset ℕ := {n}
  let pastTuple : Ω → (∀ i : past, α) := fun ω i => X i.1 ω
  let currentTuple : Ω → (∀ i : current, α) := fun ω i => X i.1 ω
  let pastGood : Set (∀ i : past, α) := {x | ∀ i, x i ∉ B}
  let pastGoodIndicator : (∀ i : past, α) → ℝ :=
    pastGood.indicator (fun _ => (1 : ℝ))
  have hnCurrent : n ∈ current := by simp [current]
  let currentValue : (∀ i : current, α) → α :=
    fun x => x (⟨n, hnCurrent⟩ : current)
  have hdisj : Disjoint past current := by
    rw [Finset.disjoint_singleton_right]
    simp [past, Finset.mem_range]
  have htuple := hXi.indepFun_finset past current hdisj hX
  have hpastGood : MeasurableSet pastGood := by
    rw [show pastGood = ⋂ i : past,
        {v : (∀ j : past, α) | v i ∈ Bᶜ} by
      ext v
      simp [pastGood]]
    exact MeasurableSet.iInter fun i =>
      MeasurableSet.preimage hB.compl (measurable_pi_apply i)
  have hpastGoodMeas : Measurable pastGoodIndicator :=
    measurable_const.indicator hpastGood
  have hcurrentMeas : Measurable (R ∘ currentValue) :=
    hR.comp (measurable_pi_apply (⟨n, hnCurrent⟩ : ↥current))
  have hcomp := htuple.comp hpastGoodMeas hcurrentMeas
  have hpastEq :
      (pastGoodIndicator ∘ pastTuple) =
        (geometricFailurePrefix X B n).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    have hmem : pastTuple ω ∈ pastGood ↔
        ω ∈ geometricFailurePrefix X B n := by
      simp [pastGood, pastTuple, geometricFailurePrefix, past, Finset.mem_range]
    by_cases hω : ω ∈ geometricFailurePrefix X B n
    · have hpast : pastTuple ω ∈ pastGood := hmem.mpr hω
      simp [pastGoodIndicator, hω, hpast]
    · have hpast : pastTuple ω ∉ pastGood := fun hm => hω (hmem.mp hm)
      simp [pastGoodIndicator, hω, hpast]
  have hcurrentEq : (R ∘ currentValue) ∘ currentTuple =
      fun ω => R (X n ω) := by
    funext ω
    simp [currentValue, currentTuple]
  rw [hpastEq, hcurrentEq] at hcomp
  exact hcomp.symm

private lemma integral_geometricPrefixRewardTerm
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure α) [IsProbabilityMeasure ν]
    (X : ℕ → Ω → α) (hX : ∀ i, Measurable (X i))
    (hXi : iIndepFun X μ) (hLaw : ∀ i, μ.map (X i) = ν)
    (B : Set α) (hB : MeasurableSet B) (R : α → ℝ)
    (hR : Measurable R) (hRi : Integrable R ν) (n : ℕ) :
    ∫ ω, geometricPrefixRewardTerm X B R n ω ∂μ =
      (∫ x, R x ∂ν) * (ν.real Bᶜ) ^ n := by
  let pastIndicator :=
    (geometricFailurePrefix X B n).indicator (fun _ => (1 : ℝ))
  have hprefixMeas := measurableSet_geometricFailurePrefix hX hB n
  have hprefixInt : Integrable pastIndicator μ :=
    (integrable_const (1 : ℝ)).indicator hprefixMeas
  have hRcompInt : Integrable (fun ω => R (X n ω)) μ :=
    (show Integrable R (μ.map (X n)) by rw [hLaw n]; exact hRi).comp_measurable (hX n)
  have hInd := indep_geometricFailurePrefix_current μ X hX hXi B hB R hR n
  have hfactor := hInd.integral_fun_mul_eq_mul_integral
    hRcompInt.aestronglyMeasurable hprefixInt.aestronglyMeasurable
  have hprefixIntegral : ∫ ω, pastIndicator ω ∂μ = (ν.real Bᶜ) ^ n := by
    have hprob := hXi.measure_inter_preimage_eq_mul (Finset.range n)
      (sets := fun _ : ℕ => Bᶜ) (by intro i hi; exact hB.compl)
    have hsets : geometricFailurePrefix X B n =
        ⋂ i ∈ Finset.range n, X i ⁻¹' Bᶜ := rfl
    rw [show pastIndicator =
      (geometricFailurePrefix X B n).indicator (fun _ => (1 : ℝ)) by rfl,
      integral_indicator_const (1 : ℝ) hprefixMeas]
    have hmap : ∀ i ∈ Finset.range n, μ.real (X i ⁻¹' Bᶜ) = ν.real Bᶜ := by
      intro i hi
      rw [← hLaw i, map_measureReal_apply_of_aemeasurable
        (hX i).aemeasurable hB.compl]
    have hprobReal : μ.real (⋂ i ∈ Finset.range n, X i ⁻¹' Bᶜ) =
        ∏ i ∈ Finset.range n, μ.real (X i ⁻¹' Bᶜ) := by
      calc
        μ.real (⋂ i ∈ Finset.range n, X i ⁻¹' Bᶜ) =
            (μ (⋂ i ∈ Finset.range n, X i ⁻¹' Bᶜ)).toReal := rfl
        _ = (∏ i ∈ Finset.range n, μ (X i ⁻¹' Bᶜ)).toReal :=
          congrArg ENNReal.toReal hprob
        _ = ∏ i ∈ Finset.range n, (μ (X i ⁻¹' Bᶜ)).toReal :=
          ENNReal.toReal_prod _ _
        _ = ∏ i ∈ Finset.range n, μ.real (X i ⁻¹' Bᶜ) := rfl
    rw [hsets, hprobReal]
    have hprod :
        (∏ i ∈ Finset.range n, μ.real (X i ⁻¹' Bᶜ)) =
          (ν.real Bᶜ) ^ n := by
      calc
        (∏ i ∈ Finset.range n, μ.real (X i ⁻¹' Bᶜ)) =
            ∏ i ∈ Finset.range n, ν.real Bᶜ := by
              apply Finset.prod_congr rfl
              intro i hi
              exact hmap i hi
        _ = (ν.real Bᶜ) ^ n := by simp
    rw [hprod]
    simp
  calc
    ∫ ω, geometricPrefixRewardTerm X B R n ω ∂μ =
        (∫ ω, pastIndicator ω ∂μ) *
          (∫ ω, R (X n ω) ∂μ) := by
            change ∫ ω, R (X n ω) * pastIndicator ω ∂μ = _
            rw [hfactor]
            ring
    _ = (ν.real Bᶜ) ^ n * (∫ x, R x ∂ν) := by
          rw [hprefixIntegral, ← integral_map (hX n).aemeasurable
            hR.aestronglyMeasurable, hLaw n]
    _ = _ := by ring

/-- First moment of a reward accumulated through the first successful trial.
The marks are iid, but the reward may depend on whether the *same* trial
succeeds. Only the previous-failure prefix is factored from the current mark. -/
theorem iidGeometricReward_integral
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure α) [IsProbabilityMeasure ν]
    (X : ℕ → Ω → α) (hX : ∀ i, Measurable (X i))
    (hXi : iIndepFun X μ) (hLaw : ∀ i, μ.map (X i) = ν)
    (B : Set α) (hB : MeasurableSet B)
    (R : α → ℝ) (hR : Measurable R) (hRi : Integrable R ν)
    (p : ℝ) (hp : 0 < p) (hprob : ν.real B = p) :
    ∫ ω, ∑' n, geometricPrefixRewardTerm X B R n ω ∂μ =
      (∫ x, R x ∂ν) / p := by
  have hq : ν.real Bᶜ = 1 - p := by
    rw [← hprob, measureReal_compl hB, probReal_univ]
  have hq_nonneg : 0 ≤ ν.real Bᶜ := measureReal_nonneg
  have hq_lt : ν.real Bᶜ < 1 := by
    rw [hq]
    linarith
  have hnormTerm (n : ℕ) :
      ∫ ω, |geometricPrefixRewardTerm X B R n ω| ∂μ =
        (∫ x, |R x| ∂ν) * (ν.real Bᶜ) ^ n := by
    have hAbsInt : Integrable (fun x => |R x|) ν := hRi.abs
    have hAbsMeas : Measurable fun x => |R x| := continuous_abs.measurable.comp hR
    have hterm := integral_geometricPrefixRewardTerm μ ν X hX hXi hLaw B hB
      (fun x => |R x|) hAbsMeas hAbsInt n
    have hpoint : (fun ω => |geometricPrefixRewardTerm X B R n ω|) =
        geometricPrefixRewardTerm X B (fun x => |R x|) n := by
      funext ω
      by_cases hω : ω ∈ geometricFailurePrefix X B n <;>
        simp [geometricPrefixRewardTerm, hω, abs_mul]
    rw [hpoint, hterm]
  have hsumNorm : Summable fun n =>
      ∫ ω, |geometricPrefixRewardTerm X B R n ω| ∂μ := by
    rw [show (fun n => ∫ ω,
      |geometricPrefixRewardTerm X B R n ω| ∂μ) =
        fun n => (∫ x, |R x| ∂ν) * (ν.real Bᶜ) ^ n by
          funext n; exact hnormTerm n]
    exact (summable_geometric_of_lt_one hq_nonneg hq_lt).mul_left _
  have htermsInt : ∀ n, Integrable (geometricPrefixRewardTerm X B R n) μ := by
    intro n
    have hprefixMeas := measurableSet_geometricFailurePrefix hX hB n
    have hprefixInt : Integrable
        ((geometricFailurePrefix X B n).indicator (fun _ => (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator hprefixMeas
    have hRcomp : Integrable (fun ω => R (X n ω)) μ :=
      (show Integrable R (μ.map (X n)) by rw [hLaw n]; exact hRi).comp_measurable (hX n)
    have hind := indep_geometricFailurePrefix_current μ X hX hXi B hB R hR n
    exact hind.integrable_mul hRcomp hprefixInt
  have hsum := integral_tsum_of_summable_integral_norm htermsInt hsumNorm
  rw [← hsum]
  rw [show (fun n => ∫ ω, geometricPrefixRewardTerm X B R n ω ∂μ) =
      fun n => (∫ x, R x ∂ν) * (ν.real Bᶜ) ^ n by
        funext n
        exact integral_geometricPrefixRewardTerm μ ν X hX hXi hLaw B hB R hR hRi n]
  have hgeom := tsum_geometric_of_lt_one hq_nonneg hq_lt
  rw [tsum_mul_left, hgeom, hq]
  field_simp [hp.ne'] <;> ring

/-- Exact first-moment formula for positive rewards accumulated only on
failed trials. The mark on a successful trial contributes zero. -/
theorem iidGeometricFailurePositiveReward_integral
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure α) [IsProbabilityMeasure ν]
    (X : ℕ → Ω → α) (hX : ∀ i, Measurable (X i))
    (hXi : iIndepFun X μ) (hLaw : ∀ i, μ.map (X i) = ν)
    (B : Set α) (hB : MeasurableSet B)
    (Y : α → ℝ) (hY : Measurable Y)
    (hYint : Integrable (fun x => max (Y x) 0) ν)
    (p : ℝ) (hp : 0 < p) (hprob : ν.real B = p) :
    ∫ ω, ∑' n, geometricPrefixRewardTerm X B
      (fun x => max (Y x) 0 * Bᶜ.indicator (fun _ => (1 : ℝ)) x) n ω ∂μ =
      (∫ x, max (Y x) 0 * Bᶜ.indicator (fun _ => (1 : ℝ)) x ∂ν) / p := by
  have hRint : Integrable (fun x => max (Y x) 0 *
      Bᶜ.indicator (fun _ => (1 : ℝ)) x) ν := by
    have h := hYint.indicator hB.compl
    convert h using 1 <;> ext x <;> by_cases hx : x ∈ B <;> simp [hx]
  have hRmeas : Measurable (fun x => max (Y x) 0 *
      Bᶜ.indicator (fun _ => (1 : ℝ)) x) :=
    (hY.max measurable_const).mul (measurable_const.indicator hB.compl)
  exact iidGeometricReward_integral μ ν X hX hXi hLaw B hB
    (fun x => max (Y x) 0 * Bᶜ.indicator (fun _ => (1 : ℝ)) x)
    hRmeas hRint p hp hprob

/-- A failure mark `Y` and a distinct success mark `Z` can occur on the same
trial. The expected signed full-cycle increment is the sum of their
event-restricted means, divided by the split probability. -/
theorem iidGeometricSplitCycle_integral
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure α) [IsProbabilityMeasure ν]
    (X : ℕ → Ω → α) (hX : ∀ i, Measurable (X i))
    (hXi : iIndepFun X μ) (hLaw : ∀ i, μ.map (X i) = ν)
    (B : Set α) (hB : MeasurableSet B)
    (Y Z : α → ℝ) (hY : Measurable Y) (hZ : Measurable Z)
    (hYint : Integrable (fun x => Y x * Bᶜ.indicator (fun _ => (1 : ℝ)) x) ν)
    (hZint : Integrable (fun x => Z x * B.indicator (fun _ => (1 : ℝ)) x) ν)
    (p : ℝ) (hp : 0 < p) (hprob : ν.real B = p) :
    ∫ ω, ∑' n, geometricPrefixRewardTerm X B
      (fun x => Y x * Bᶜ.indicator (fun _ => (1 : ℝ)) x +
        Z x * B.indicator (fun _ => (1 : ℝ)) x) n ω ∂μ =
      ((∫ x, Y x * Bᶜ.indicator (fun _ => (1 : ℝ)) x ∂ν) +
        (∫ x, Z x * B.indicator (fun _ => (1 : ℝ)) x ∂ν)) / p := by
  have hRewardMeas : Measurable (fun x =>
      Y x * Bᶜ.indicator (fun _ => (1 : ℝ)) x +
        Z x * B.indicator (fun _ => (1 : ℝ)) x) :=
    (hY.mul (measurable_const.indicator hB.compl)).add
      (hZ.mul (measurable_const.indicator hB))
  calc
    ∫ ω, ∑' n, geometricPrefixRewardTerm X B
        (fun x => Y x * Bᶜ.indicator (fun _ => (1 : ℝ)) x +
          Z x * B.indicator (fun _ => (1 : ℝ)) x) n ω ∂μ =
      (∫ x, Y x * Bᶜ.indicator (fun _ => (1 : ℝ)) x +
        Z x * B.indicator (fun _ => (1 : ℝ)) x ∂ν) / p :=
          iidGeometricReward_integral μ ν X hX hXi hLaw B hB
            (fun x => Y x * Bᶜ.indicator (fun _ => (1 : ℝ)) x +
              Z x * B.indicator (fun _ => (1 : ℝ)) x) hRewardMeas
            (hYint.add hZint) p hp hprob
    _ = ((∫ x, Y x * Bᶜ.indicator (fun _ => (1 : ℝ)) x ∂ν) +
        (∫ x, Z x * B.indicator (fun _ => (1 : ℝ)) x ∂ν)) / p := by
          rw [integral_add hYint hZint]

/-- Nonnegative first-moment bound for the accumulated positive rewards in a
split cycle. Failed generations use the first-child mark `Y`, while a success
uses the distinct reserve mark `Z`. -/
theorem iidGeometricSplitCycle_positiveReward_le
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure α) [IsProbabilityMeasure ν]
    (X : ℕ → Ω → α) (hX : ∀ i, Measurable (X i))
    (hXi : iIndepFun X μ) (hLaw : ∀ i, μ.map (X i) = ν)
    (B : Set α) (hB : MeasurableSet B)
    (Y Z : α → ℝ) (hY : Measurable Y) (hZ : Measurable Z)
    (hYint : Integrable (fun x => max (Y x) 0) ν)
    (hZint : Integrable (fun x => max (Z x) 0) ν)
    (p : ℝ) (hp : 0 < p) (hprob : ν.real B = p) :
    ∫ ω, ∑' n, geometricPrefixRewardTerm X B
      (fun x => max (Y x) 0 * Bᶜ.indicator (fun _ => (1 : ℝ)) x +
        max (Z x) 0 * B.indicator (fun _ => (1 : ℝ)) x) n ω ∂μ ≤
      ((∫ x, max (Y x) 0 ∂ν) + (∫ x, max (Z x) 0 *
        B.indicator (fun _ => (1 : ℝ)) x ∂ν)) / p := by
  have hYres : Integrable (fun x => max (Y x) 0 *
      Bᶜ.indicator (fun _ => (1 : ℝ)) x) ν := by
    have h := hYint.indicator hB.compl
    convert h using 1 <;> ext x <;> by_cases hx : x ∈ B <;> simp [hx]
  have hZres : Integrable (fun x => max (Z x) 0 *
      B.indicator (fun _ => (1 : ℝ)) x) ν := by
    have h := hZint.indicator hB
    convert h using 1 <;> ext x <;> by_cases hx : x ∈ B <;> simp [hx]
  have hRewardInt : Integrable (fun x =>
      max (Y x) 0 * Bᶜ.indicator (fun _ => (1 : ℝ)) x +
        max (Z x) 0 * B.indicator (fun _ => (1 : ℝ)) x) ν :=
    hYres.add hZres
  have hRewardMeas : Measurable (fun x =>
      max (Y x) 0 * Bᶜ.indicator (fun _ => (1 : ℝ)) x +
        max (Z x) 0 * B.indicator (fun _ => (1 : ℝ)) x) :=
    ((hY.max measurable_const).mul (measurable_const.indicator hB.compl)).add
      ((hZ.max measurable_const).mul (measurable_const.indicator hB))
  have hEq := iidGeometricReward_integral μ ν X hX hXi hLaw B hB
    (fun x => max (Y x) 0 * Bᶜ.indicator (fun _ => (1 : ℝ)) x +
      max (Z x) 0 * B.indicator (fun _ => (1 : ℝ)) x)
    hRewardMeas
    hRewardInt p hp hprob
  rw [hEq, integral_add hYres hZres]
  have hYbound :
      ∫ x, max (Y x) 0 * Bᶜ.indicator (fun _ => (1 : ℝ)) x ∂ν ≤
        ∫ x, max (Y x) 0 ∂ν := by
    apply integral_mono_ae hYres hYint
    filter_upwards [] with x
    by_cases hx : x ∈ B <;> simp [hx]
  have hnumerator :
      (∫ x, max (Y x) 0 * Bᶜ.indicator (fun _ => (1 : ℝ)) x ∂ν) +
          (∫ x, max (Z x) 0 * B.indicator (fun _ => (1 : ℝ)) x ∂ν) ≤
        (∫ x, max (Y x) 0 ∂ν) +
          (∫ x, max (Z x) 0 * B.indicator (fun _ => (1 : ℝ)) x ∂ν) :=
    add_le_add hYbound (le_refl _)
  exact (div_le_div_of_nonneg_right hnumerator hp.le)

/-- The `n`th term in the exponential expansion of a failure-only cycle:
each of the first `n` trials contributes the exponential weight on failure,
and trial `n` contributes the success indicator. -/
noncomputable def geometricFailureExponentialTerm
    (X : ℕ → Ω → α) (B : Set α) (Y : α → ℝ) (θ : ℝ) (n : ℕ) :
    Ω → ℝ≥0∞ :=
  fun ω => ∏ i ∈ Finset.range (n + 1),
    (if i < n then
      ENNReal.ofReal (Real.exp (θ * Y (X i ω))) *
        Bᶜ.indicator (fun _ => (1 : ℝ≥0∞)) (X i ω)
    else B.indicator (fun _ => (1 : ℝ≥0∞)) (X i ω))

/-- Geometric exponential-transform identity for the failure-only cycle.
The left side sums over the disjoint events “the first success occurs at `n`”;
the first `n` marks carry `exp (λY)` only on failure, and the `n`th mark
contributes only the success indicator. Thus the numerator is the success
probability `p`, while the geometric ratio is
`Aλ = E[exp (λY) 1_{Bᶜ}]`.

The theorem is stated in `ENNReal`, so finiteness is expressed by the explicit
assumption `Aλ < 1`. Under the usual positive success probability, these terms
are exactly the exponential-moment expansion of the sum of failed marks up
to the first success. -/
theorem iidGeometricFailureExponentialTransform
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ν : Measure α) [IsProbabilityMeasure ν]
    (X : ℕ → Ω → α) (hX : ∀ i, Measurable (X i))
    (hXi : iIndepFun X μ) (hLaw : ∀ i, μ.map (X i) = ν)
    (B : Set α) (hB : MeasurableSet B)
    (Y : α → ℝ) (hY : Measurable Y) (θ : ℝ)
    (p : ℝ≥0∞) (hp : 0 < p) (hprob : ν B = p)
    (A : ℝ≥0∞)
    (hA : ∫⁻ x, ENNReal.ofReal (Real.exp (θ * Y x)) *
      Bᶜ.indicator (fun _ => (1 : ℝ≥0∞)) x ∂ν = A)
    (hA_lt : A < 1) :
    ∫⁻ ω, ∑' n, geometricFailureExponentialTerm X B Y θ n ω ∂μ =
      p / (1 - A) := by
  let failWeight : α → ℝ≥0∞ := fun x =>
    ENNReal.ofReal (Real.exp (θ * Y x)) *
      Bᶜ.indicator (fun _ => (1 : ℝ≥0∞)) x
  let successWeight : α → ℝ≥0∞ := fun x =>
    B.indicator (fun _ => (1 : ℝ≥0∞)) x
  have hfailMeas : Measurable failWeight := by
    dsimp [failWeight]
    exact (by fun_prop : Measurable fun x => ENNReal.ofReal (Real.exp (θ * Y x))).mul
      (measurable_const.indicator hB.compl)
  have hsuccessMeas : Measurable successWeight := by
    dsimp [successWeight]
    exact measurable_const.indicator hB
  have hfailMap (i : ℕ) :
      ∫⁻ ω, failWeight (X i ω) ∂μ = A := by
    rw [← lintegral_map hfailMeas (hX i), hLaw i]
    exact hA
  have hsuccessMap (i : ℕ) :
      ∫⁻ ω, successWeight (X i ω) ∂μ = p := by
    rw [← lintegral_map hsuccessMeas (hX i), hLaw i]
    rw [show successWeight = B.indicator (fun _ => (1 : ℝ≥0∞)) by rfl,
      lintegral_indicator_const hB]
    simp [hprob]
  have htermMeas (n : ℕ) :
      Measurable (geometricFailureExponentialTerm X B Y θ n) := by
    let factor : ℕ → Ω → ℝ≥0∞ := fun i ω =>
      if i < n then failWeight (X i ω) else successWeight (X i ω)
    have hfactorMeas (i : ℕ) : Measurable (factor i) := by
      by_cases hi : i < n
      · simp [factor, hi]
        exact hfailMeas.comp (hX i)
      · simp [factor, hi]
        exact hsuccessMeas.comp (hX i)
    have hprodMeas (s : Finset ℕ) :
        Measurable (fun ω => ∏ i ∈ s, factor i ω) := by
      classical
      induction s using Finset.induction_on with
      | empty => simp
      | @insert i s hi ih =>
        simp only [Finset.prod_insert hi]
        exact (hfactorMeas i).mul ih
    have htermEq : geometricFailureExponentialTerm X B Y θ n =
        fun ω => ∏ i ∈ Finset.range (n + 1), factor i ω := by
      funext ω
      unfold geometricFailureExponentialTerm
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hin : i < n
      · simp [factor, hin, failWeight]
      · have hlast : i = n := by
          have hi' := Finset.mem_range.mp hi
          omega
        subst i
        simp [factor, successWeight]
    rw [htermEq]
    exact hprodMeas _
  have htermIntegral (n : ℕ) :
      ∫⁻ ω, geometricFailureExponentialTerm X B Y θ n ω ∂μ = A ^ n * p := by
    let factor : ℕ → α → ℝ≥0∞ := fun i x =>
      if i < n then failWeight x else successWeight x
    have hfactorMeas : ∀ i, Measurable (factor i) := by
      intro i
      by_cases hi : i < n
      · simp [factor, hi]
        exact hfailMeas
      · simp [factor, hi]
        exact hsuccessMeas
    have hfactorInd : iIndepFun (fun i ω => factor i (X i ω)) μ :=
      hXi.comp factor hfactorMeas
    have hprod := lintegral_prod_eq_prod_lintegral_of_indepFun
      (Finset.range (n + 1)) (fun i ω => factor i (X i ω))
      hfactorInd (fun i => (hfactorMeas i).comp (hX i))
    have hfactorIntegral (i : ℕ) (hi : i < n) :
        ∫⁻ ω, factor i (X i ω) ∂μ = A := by
      simp [factor, hi, hfailMap]
    have hlastIntegral :
        ∫⁻ ω, factor n (X n ω) ∂μ = p := by
      simp [factor, hsuccessMap]
    have hprefix :
        (∏ i ∈ Finset.range n, ∫⁻ ω, factor i (X i ω) ∂μ) = A ^ n := by
      calc
        (∏ i ∈ Finset.range n, ∫⁻ ω, factor i (X i ω) ∂μ) =
            ∏ i ∈ Finset.range n, A := by
              apply Finset.prod_congr rfl
              intro i hi
              exact hfactorIntegral i (Finset.mem_range.mp hi)
        _ = A ^ n := by simp
    have htermEq : geometricFailureExponentialTerm X B Y θ n =
        fun ω => ∏ i ∈ Finset.range (n + 1), factor i (X i ω) := by
      funext ω
      unfold geometricFailureExponentialTerm
      apply Finset.prod_congr rfl
      intro i hi
      by_cases hin : i < n
      · simp [factor, hin, failWeight]
      · have hlast : i = n := by
          have hi' := Finset.mem_range.mp hi
          omega
        subst i
        simp [factor, successWeight]
    rw [htermEq, hprod, Finset.prod_range_succ, hprefix, hlastIntegral]
  have hsum :
      ∫⁻ ω, ∑' n, geometricFailureExponentialTerm X B Y θ n ω ∂μ =
        ∑' n, (A ^ n * p) := by
    rw [lintegral_tsum (fun n => (htermMeas n).aemeasurable)]
    congr 1
    funext n
    exact htermIntegral n
  rw [hsum]
  calc
    ∑' n, (A ^ n * p) = ∑' n, (p * A ^ n) := by
      congr 1
      funext n
      exact mul_comm _ _
    _ = p * ∑' n, A ^ n := ENNReal.tsum_mul_left
    _ = p / (1 - A) := by rw [ENNReal.tsum_geometric]; simp [div_eq_mul_inv]

end ProbabilityTheory.BranchingRandomWalk

end
