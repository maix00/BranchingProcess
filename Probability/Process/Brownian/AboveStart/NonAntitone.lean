/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.BrownianMotion.Basic
public import Probability.Distributions.Gaussian.Sign
public import Probability.Process.Path.AboveStart.LocalMinimum

/-!
# Brownian paths increase somewhere on every time interval

The public theorem in this file is:

- `ProbabilityTheory.IsPreBrownianReal.measure_antitoneOn_unit_eq_zero`:
  a Brownian path has probability zero of being nonincreasing on $[0,1]$.
- `ProbabilityTheory.IsBrownianReal.ae_exists_positiveWindowBeforeUnit`:
  almost every Brownian path has a positive-duration window inside $[0,1]$
  on which it stays above its value at the window's start.

The proof uses independent increments on equal subdivisions and the fact
that every nondegenerate centered Gaussian increment has a fixed positive
probability of being positive. This is the probabilistic step in Erwin
Bolthausen, *On a Functional Central Limit Theorem for Random Walks Conditioned to Stay Positive*, Lemma 2.2, p. 481, Ann. Probab. 4(3)
(1976), 480--485, DOI 10.1214/aop/1176996098.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace ProbabilityTheory

private noncomputable def uniformBrownianPartition (n : ℕ) :
    Fin (n + 1) → ℝ≥0 :=
  fun i => (i.val : ℝ≥0) / (n : ℝ≥0)

private lemma gaussianReal_Iic_zero_lt_one :
    gaussianReal 0 (1 : ℝ≥0) (Iic 0) < 1 := by
  have hpos : 0 < gaussianReal 0 (1 : ℝ≥0) (Ioi 0) :=
    gaussianReal_Ioi_zero_pos
  have hlt : gaussianReal 0 (1 : ℝ≥0) (Iic 0) < 1 := by
    rw [← Set.compl_Ioi, measure_compl measurableSet_Ioi (by finiteness), measure_univ]
    exact ENNReal.sub_lt_self ENNReal.one_ne_top (by norm_num) hpos.ne'
  exact hlt

/-- On any finite equal subdivision of $[0,1]$, the probability that
all Brownian increments are nonpositive decays geometrically. -/
private lemma IsPreBrownianReal.measure_all_partitionIncrements_nonpos_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (n : ℕ) (hn : 0 < n) :
    P {ω | ∀ i : Fin n,
      B (uniformBrownianPartition n i.succ) ω -
        B (uniformBrownianPartition n i.castSucc) ω ≤ 0} ≤
      (gaussianReal 0 (1 : ℝ≥0) (Iic 0)) ^ n := by
  classical
  let t := uniformBrownianPartition n
  let X : Fin n → Ω → ℝ := fun i ω => B (t i.succ) ω - B (t i.castSucc) ω
  have hden : (0 : ℝ≥0) < (n : ℝ≥0) := by exact_mod_cast hn
  have htStrict : StrictMono t := by
    intro i j hij
    change (i.val : ℝ≥0) / (n : ℝ≥0) <
      (j.val : ℝ≥0) / (n : ℝ≥0)
    exact (strictMono_div_right_of_pos hden) (by exact_mod_cast hij)
  have htMono : Monotone t := htStrict.monotone
  have hInd : iIndepFun X P := by
    exact hB.hasIndepIncrements n t htMono
  let q : ℝ≥0∞ := gaussianReal 0 (1 : ℝ≥0) (Iic 0)
  have hq : q < 1 := gaussianReal_Iic_zero_lt_one
  have hqpow := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq
  have hvar (i : Fin n) : 0 < nndist (t i.succ : ℝ) (t i.castSucc : ℝ) := by
    apply pos_iff_ne_zero.mpr
    intro hz
    have hlt : (t i.castSucc : ℝ) < (t i.succ : ℝ) := by
      exact_mod_cast htStrict Fin.castSucc_lt_succ
    exact (ne_of_gt hlt) (nndist_eq_zero.mp hz)
  have hmass (i : Fin n) : P (X i ⁻¹' Iic 0) = q := by
    have hLaw := hB.hasLaw_sub (t i.succ) (t i.castSucc)
    have hLawprob := hLaw.measure_eq
      (p := fun x : ℝ => x ∈ Iic (0 : ℝ)) measurableSet_Iic
    change P {ω | (B (t i.succ) - B (t i.castSucc)) ω ∈ Iic 0} = q
    rw [hLawprob]
    dsimp [q]
    exact gaussianReal_Iic_zero_eq_standard (hvar i)
  have hfactor := hInd.measure_inter_preimage_eq_mul Finset.univ
    (sets := fun _ : Fin n => Iic (0 : ℝ))
    (by intro i hi; exact measurableSet_Iic)
  have hbound :
      P {ω | ∀ i : Fin n, X i ω ≤ 0} ≤ q ^ n := by
    calc
      P {ω | ∀ i : Fin n, X i ω ≤ 0} =
          P (⋂ i ∈ Finset.univ, X i ⁻¹' Iic (0 : ℝ)) := by
            congr 1
            ext ω
            simp
      _ = ∏ i ∈ Finset.univ, P (X i ⁻¹' Iic (0 : ℝ)) := by
            simpa using hfactor
      _ = q ^ n := by
            simp_rw [hmass]
            simp
      _ ≤ q ^ n := le_rfl
  simpa [X, t, q, uniformBrownianPartition] using hbound

/-- A Brownian path is almost surely not nonincreasing on $[0,1]$. -/
theorem IsPreBrownianReal.measure_antitoneOn_unit_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P) :
    P {ω | AntitoneOn (fun t : ℝ≥0 => B t ω) (Icc (0 : ℝ≥0) 1)} = 0 := by
  classical
  let A : Set Ω :=
    {ω | AntitoneOn (fun t : ℝ≥0 => B t ω) (Icc (0 : ℝ≥0) 1)}
  have hq : (gaussianReal 0 (1 : ℝ≥0) (Iic 0)) < 1 :=
    gaussianReal_Iic_zero_lt_one
  have hqpow := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq
  have hbound (n : ℕ) (hn : 0 < n) : P A ≤
      (gaussianReal 0 (1 : ℝ≥0) (Iic 0)) ^ n := by
    have hden : (0 : ℝ≥0) < (n : ℝ≥0) := by exact_mod_cast hn
    calc
      P A ≤ P {ω | ∀ i : Fin n,
          B (uniformBrownianPartition n i.succ) ω -
            B (uniformBrownianPartition n i.castSucc) ω ≤ 0} := by
              apply measure_mono
              intro ω hω i
              change AntitoneOn (fun t : ℝ≥0 => B t ω) (Icc (0 : ℝ≥0) 1) at hω
              have htStrict : StrictMono (uniformBrownianPartition n) := by
                intro i j hij
                change (i.val : ℝ≥0) / (n : ℝ≥0) <
                  (j.val : ℝ≥0) / (n : ℝ≥0)
                exact (strictMono_div_right_of_pos hden) (by exact_mod_cast hij)
              have htimes :
                  uniformBrownianPartition n i.castSucc ≤
                    uniformBrownianPartition n i.succ :=
                htStrict.monotone (Fin.castSucc_le_succ i)
              have hunit (j : Fin (n + 1)) :
                  uniformBrownianPartition n j ∈ Icc (0 : ℝ≥0) 1 := by
                change (j.val : ℝ≥0) / (n : ℝ≥0) ∈ Icc (0 : ℝ≥0) 1
                constructor
                · exact div_nonneg (by positivity) (by positivity)
                · rw [div_le_one hden]
                  exact_mod_cast j.is_le
              have hdecr := hω (hunit i.castSucc) (hunit i.succ) htimes
              exact sub_nonpos.mpr hdecr
      _ ≤ (gaussianReal 0 (1 : ℝ≥0) (Iic 0)) ^ n := by
            exact IsPreBrownianReal.measure_all_partitionIncrements_nonpos_le
              hB n hn
  have hboundAll (n : ℕ) : P A ≤
      (gaussianReal 0 (1 : ℝ≥0) (Iic 0)) ^ n := by
    by_cases hn : 0 < n
    · exact hbound n hn
    · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      rw [hn0, pow_zero]
      calc
        P A ≤ P Set.univ := measure_mono (subset_univ A)
        _ = 1 := measure_univ
  have hzero : P A = 0 := by
    apply le_antisymm
    · exact le_of_tendsto_of_tendsto' tendsto_const_nhds hqpow hboundAll
    · exact bot_le
  simpa [A] using hzero

/-- Almost every Brownian path has a positive-duration interval on which
it stays above its value at the interval's left endpoint. The proof uses
the preceding nonincreasing-path estimate and the deterministic local
minimum argument. -/
theorem IsBrownianReal.ae_exists_positiveWindowBeforeUnit
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∃ f : C(ℝ≥0, ℝ), (∀ t, f t = B t ω) ∧
      ∃ duration : ℝ≥0, 0 < duration ∧
        HasNonnegativeWindowBeforeUnit f duration := by
  have hnotanti : ∀ᵐ ω ∂P,
      ¬ AntitoneOn (fun t : ℝ≥0 => B t ω) (Icc (0 : ℝ≥0) 1) := by
    have hzero := hB.toIsPreBrownianReal.measure_antitoneOn_unit_eq_zero
    apply ae_iff.mpr
    simpa only [not_not] using hzero
  filter_upwards [hnotanti, hB.cont] with ω hnotanti hcont
  let f : C(ℝ≥0, ℝ) := ⟨fun t => B t ω, hcont⟩
  have hwindow : ∃ duration : ℝ≥0, 0 < duration ∧
      HasNonnegativeWindowBeforeUnit f duration := by
    by_contra h
    apply hnotanti
    apply antitoneOn_of_no_nonnegativeWindow f
    intro duration hduration hwindow
    exact h ⟨duration, hduration, hwindow⟩
  exact ⟨f, fun _ => rfl, hwindow⟩

end ProbabilityTheory

end
