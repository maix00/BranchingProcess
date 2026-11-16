/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Logarithmic scales for entrance from one initial particle

## Internal proof declarations

* `trialDuration_le` gives $d_N\le\alpha\log N/\log\rho$ for the
  original duration $d_N=\lfloor\alpha\log N/\log\rho\rfloor-1$.
* `eventually_two_rpow_le_pow_trialDuration`: if $\beta<\alpha$, then
  $2N^\beta\le\rho^{d_N}$ eventually.
* `logarithmicEntrance_scales`: the logarithmic clock and split count
  bounds give the population and displacement budgets for a duration below
  $\alpha\log N/\log\rho$. The total entrance horizon is $o(\log^3N)$.
* `eventually_geometric_and_exponential_entrance_bound`: when $0<q<1$,
  the clock error and the first-$K$ failure terms are bounded by a common
  polynomial rate. The weighted trial-root term
  $K\exp(K\log B-\lambda v\delta\log N)$ has a polynomial rate when
  $\lambda v=\log B+1$ and $B\ge1$.

These are the logarithmic scales of Wang Yiyang, *Asymptotic Speed of
the N-Branching Random Walk with Infinite Offspring* (Fudan University,
2026), Chapter 4, Theorem 1.1 for $a=0$.
-/

open Filter
open scoped Topology BigOperators

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas

private lemma eventually_affine_le_exp_mul (A B b : ℝ) (hb : 0 < b) :
    ∀ᶠ x : ℝ in atTop, A * x + B ≤ Real.exp (b * x) := by
  have hlinear : Tendsto (fun x : ℝ => x / Real.exp (b * x)) atTop (𝓝 0) := by
    have h := (Real.tendsto_div_pow_mul_exp_add_atTop 1 0 1 (by norm_num)).comp
      (tendsto_id.const_mul_atTop hb)
    have h' := h.div_const b
    convert h' using 1
    · ext x
      simp only [Function.comp_apply, id_eq, pow_one, one_mul, add_zero]
      field_simp
    · simp
  have hconstant : Tendsto (fun x : ℝ => B / Real.exp (b * x)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hb))
  have hlim : Tendsto (fun x : ℝ => (A * x + B) / Real.exp (b * x)) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add, add_div, mul_div_assoc] using
      (hlinear.const_mul A).add hconstant
  filter_upwards [hlim (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with x hx
  exact ((div_lt_iff₀ (Real.exp_pos _)).mp hx).le.trans_eq (one_mul _)

/-- The original floor duration uses no more than its real logarithmic bound. -/
lemma trialDuration_le {ρ : ℝ} (hρ : 1 < ρ) {α : ℝ} (ha : 0 ≤ α) (N : ℕ) :
    ((⌊α * Real.log (N : ℝ) / Real.log ρ⌋₊ - 1 : ℕ) : ℝ) ≤
      α * Real.log (N : ℝ) / Real.log ρ := by
  have hnonneg := div_nonneg (mul_nonneg ha (Real.log_natCast_nonneg N)) (Real.log_pos hρ).le
  exact (Nat.cast_le.mpr (Nat.sub_le _ _)).trans (Nat.floor_le hnonneg)

/-- With the original duration, any smaller exponent gives a target below
half the mean for all sufficiently large populations. -/
lemma eventually_two_rpow_le_pow_trialDuration
    {ρ α β : ℝ} (hρ : 1 < ρ) (hβα : β < α)
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop) :
    ∀ᶠ i in atTop, 2 * (N i : ℝ) ^ β ≤ ρ ^ (⌊α * Real.log (N i : ℝ) / Real.log ρ⌋₊ - 1) := by
  have hρlog := Real.log_pos hρ
  let d i := ⌊α * Real.log (N i : ℝ) / Real.log ρ⌋₊ - 1
  have hlog : Tendsto (fun i => Real.log (N i : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)
  have hgap : ∀ᶠ i in atTop,
      Real.log 2 + 2 * Real.log ρ ≤ (α - β) * Real.log (N i : ℝ) :=
    (hlog.const_mul_atTop (sub_pos.mpr hβα)).eventually_ge_atTop _
  filter_upwards [hN.eventually_ge_atTop 1, hgap] with i hi hgi
  let x := α * Real.log (N i : ℝ) / Real.log ρ
  have hNpos : 0 < (N i : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hi
  have hfloor : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hfd : (⌊x⌋₊ : ℝ) ≤ (d i : ℝ) + 1 := by
    have hn : ⌊x⌋₊ ≤ d i + 1 := by dsimp [d, x]; omega
    exact_mod_cast hn
  have hduration : α * Real.log (N i : ℝ) < ((d i : ℝ) + 2) * Real.log ρ := by
    have hx : x < (d i : ℝ) + 2 := by linarith
    exact (div_lt_iff₀ hρlog).mp hx
  have hmean : 2 * (N i : ℝ) ^ β ≤ ρ ^ d i := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2),
      Real.rpow_def_of_pos hNpos, ← Real.exp_add]
    have hpow : ρ ^ d i = Real.exp ((d i : ℝ) * Real.log ρ) := by
      rw [Real.exp_nat_mul, Real.exp_log (by linarith : 0 < ρ)]
    rw [hpow]
    apply Real.exp_le_exp.mpr
    nlinarith only [hduration, hgi]
  exact hmean

lemma logarithmicEntrance_scales
    {ρ p α δ M v η : ℝ}
    (hρ : 1 < ρ) (hp : 0 < p) (ha : 0 < α) (hδ : 0 < δ)
    (hM : 0 ≤ M)
    (hsmall : α / Real.log ρ < 1 / (2 * Real.log 2))
    (hbudget : (v + M) * δ + M * (α / Real.log ρ) < η)
    {N H : ℕ → ℕ} (hN : Tendsto N atTop atTop) {t : ℝ} (ht : 0 < t)
    (hH : Tendsto (fun n => (H n : ℝ) / Real.log (N n : ℝ) ^ 3) atTop (𝓝 t))
    (d : ℕ → ℕ) (hduration : ∀ i,
      (d i : ℝ) ≤ α * Real.log (N i : ℝ) / Real.log ρ) :
    let L := fun i => Real.log (N i : ℝ)
    let K := fun i => ⌊δ * L i⌋₊
    let n := fun i => ⌈(4 * δ / p) * L i⌉₊
    let T := fun i => n i + d i
    (∀ᶠ i in atTop,
      0 < n i ∧ (K i : ℝ) ≤ (n i : ℝ) * p / 4 ∧
      δ * L i / 2 ≤ (K i : ℝ) ∧ (K i : ℝ) ≤ δ * L i ∧
      1 + (d i + 1) * (2 * 2 ^ d i) ≤ N i ∧
      v * (δ * L i) + (K i : ℝ) * M + M * d i ≤ η * L i) ∧
    Tendsto (fun i => (T i : ℝ) / L i ^ 3) atTop (𝓝 0) ∧
    (∀ᶠ i in atTop, T i ≤ H i) := by
  intro L K n T
  have hL : Tendsto L atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)
  have hρlog : 0 < Real.log ρ := Real.log_pos hρ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let A := α / Real.log ρ
  let C := 4 * δ / p
  have hA : 0 < A := div_pos ha hρlog
  have hC : 0 < C := div_pos (by positivity) hp
  have hduration' (i : ℕ) : (d i : ℝ) ≤ A * L i := by
    simpa [A, div_eq_mul_inv, mul_right_comm] using hduration i
  have hclock (i : ℕ) (hi : 0 ≤ L i) : (n i : ℝ) ≤ C * L i + 1 :=
    (Nat.ceil_lt_add_one (mul_nonneg hC.le hi)).le
  have hA' : A < 1 / (2 * Real.log 2) := hsmall
  have hcapEventually : ∀ᶠ i in atTop, 1 + (d i + 1) * (2 * 2 ^ d i) ≤ N i := by
    filter_upwards [hL.eventually_ge_atTop 0,
      hL.eventually (eventually_affine_le_exp_mul (4 * A) 4 (1 / 2) (by norm_num)),
      hN.eventually_ge_atTop 2] with i hlog hfactor hN2
    have hd := hduration' i
    have hsmall' : (d i : ℝ) ≤ L i / (2 * Real.log 2) := by
      exact hd.trans (by simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using
        mul_le_mul_of_nonneg_right hA'.le hlog)
    have hpow : (2 : ℝ) ^ d i ≤ Real.exp (L i / 2) := by
      calc
        (2 : ℝ) ^ d i = Real.exp ((d i : ℝ) * Real.log 2) := by
          rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
        _ ≤ _ := Real.exp_le_exp.mpr (by
          have hh := (le_div_iff₀ (by positivity : 0 < 2 * Real.log 2)).mp hsmall'
          nlinarith)
    have hnreal : (0 : ℝ) < N i := by exact_mod_cast (by omega : 0 < N i)
    have hfac : (4 * ((d i : ℝ) + 1)) ≤ Real.exp (L i / 2) := by
      have heq : 1 / 2 * L i = L i / 2 := by ring
      rw [heq] at hfactor
      linarith
    have hmul := mul_le_mul hfac hpow (by positivity) (Real.exp_nonneg _)
    rw [← Real.exp_add, show L i / 2 + L i / 2 = L i by ring,
      show Real.exp (L i) = (N i : ℝ) from Real.exp_log hnreal] at hmul
    have hf : (2 : ℝ) ≤ N i := by exact_mod_cast hN2
    have hcast : (1 : ℝ) + ((d i : ℝ) + 1) * (2 * 2 ^ d i) ≤ N i := by
      linarith only [hmul, hf,
        show 4 * ((d i : ℝ) + 1) * 2 ^ d i = 2 * (((d i : ℝ) + 1) * (2 * 2 ^ d i)) by ring]
    exact_mod_cast hcast
  have hall : ∀ᶠ i in atTop,
      0 < n i ∧ (K i : ℝ) ≤ (n i : ℝ) * p / 4 ∧
      δ * L i / 2 ≤ (K i : ℝ) ∧ (K i : ℝ) ≤ δ * L i ∧
      1 + (d i + 1) * (2 * 2 ^ d i) ≤ N i ∧
      v * (δ * L i) + (K i : ℝ) * M + M * d i ≤ η * L i := by
    filter_upwards [hL.eventually_ge_atTop 1, hL.eventually_ge_atTop (2 / δ),
      hcapEventually] with i hlog hlogK hcap
    have hLpos : 0 < L i := by linarith
    have hnpos : 0 < n i := Nat.ceil_pos.mpr (mul_pos hC hLpos)
    have hnlo : C * L i ≤ (n i : ℝ) := Nat.le_ceil _
    have hKhi : (K i : ℝ) ≤ δ * L i := Nat.floor_le (mul_nonneg hδ.le hLpos.le)
    have hKlo : δ * L i / 2 ≤ (K i : ℝ) := by
      have hlo : δ * L i < (K i : ℝ) + 1 := Nat.lt_floor_add_one _
      have hh : 2 ≤ L i * δ := (div_le_iff₀ hδ).mp hlogK
      nlinarith
    have hnK : (K i : ℝ) ≤ (n i : ℝ) * p / 4 := by
      have hh := mul_le_mul_of_nonneg_right hnlo hp.le
      have heq : C * L i * p = 4 * (δ * L i) := by
        dsimp [C]; field_simp
      rw [heq] at hh
      linarith
    refine ⟨hnpos, hnK, hKlo, hKhi, hcap, ?_⟩
    have hdle := mul_le_mul_of_nonneg_left (hduration' i) hM
    have hKle := mul_le_mul_of_nonneg_right hKhi hM
    exact (by nlinarith only [hdle, hKle] :
      v * (δ * L i) + (K i : ℝ) * M + M * d i ≤ ((v + M) * δ + M * A) * L i).trans
      (mul_le_mul_of_nonneg_right hbudget.le hLpos.le)
  have hT : Tendsto (fun i => (T i : ℝ) / L i ^ 3) atTop (𝓝 0) := by
    have hzero : Tendsto (fun i => (C + A + 1) / L i ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hL)
    apply squeeze_zero' _ _ hzero
    · exact Eventually.of_forall fun _ => by
        positivity
    · filter_upwards [hL.eventually_ge_atTop 1] with i hi
      have hpos : 0 < L i := by linarith
      have hupper : (T i : ℝ) ≤ (C + A + 1) * L i := by
        change ((n i + d i : ℕ) : ℝ) ≤ _
        push_cast
        nlinarith [hclock i hpos.le, hduration' i]
      apply (div_le_div_iff₀ (pow_pos hpos _) (pow_pos hpos _)).mpr
      simpa only [pow_succ' (L i) 2, mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_right hupper (sq_nonneg (L i))
  refine ⟨hall, hT, ?_⟩
  filter_upwards [hL.eventually_ge_atTop 1,
    hT (gt_mem_nhds (show 0 < t / 2 by positivity)),
    hH (lt_mem_nhds (show t / 2 < t by linarith))] with i hi hTi hHi
  have hp : 0 < L i ^ 3 := pow_pos (by linarith) _
  have hle : (T i : ℝ) ≤ H i :=
    (div_le_div_iff_of_pos_right hp).mp (hTi.le.trans hHi.le)
  exact_mod_cast hle

lemma eventually_geometric_and_exponential_entrance_bound
    {p δ q B lam v : ℝ}
    (hδ : 0 < δ) (hq : 0 < q) (hq1 : q < 1)
    (hB : 1 ≤ B) (hv : lam * v = Real.log B + 1)
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) (K n : ℕ → ℕ)
    (hK : ∀ᶠ i in atTop,
      δ * L i / 2 ≤ (K i : ℝ) ∧ (K i : ℝ) ≤ δ * L i ∧
        (K i : ℝ) ≤ (n i : ℝ) * p / 4) :
    ∃ b : ℝ, 0 < b ∧ ∀ᶠ i in atTop,
      Real.exp (-((n i : ℝ) * p / 4)) ≤ Real.exp (-b * L i) ∧
      q ^ K i ≤ Real.exp (-b * L i) ∧
      (∑ k ∈ Finset.range (K i), B ^ (k + 1)) ≤
        Real.exp (lam * (v * (δ * L i))) * Real.exp (-b * L i) := by
  let b := min (δ / 2) (-(Real.log q) * δ / 2)
  have hqlog : Real.log q < 0 := Real.log_neg hq hq1
  have hb : 0 < b := lt_min (by positivity) (by positivity [neg_pos.mpr hqlog])
  have hb₁ : b ≤ δ / 2 := min_le_left _ _
  have hb₂ : b ≤ -(Real.log q) * δ / 2 := min_le_right _ _
  refine ⟨b, hb, ?_⟩
  filter_upwards [hK, hL.eventually_ge_atTop 0,
    hL.eventually (eventually_affine_le_exp_mul δ 0 (δ / 2) (by positivity))]
    with i hi hLi hfactor
  obtain ⟨hlo, hhi, hclock⟩ := hi
  have hclock' : Real.exp (-((n i : ℝ) * p / 4)) ≤ Real.exp (-b * L i) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right hb₁ hLi]
  have hgeom : q ^ K i ≤ Real.exp (-b * L i) := by
    calc
      q ^ K i = Real.exp ((K i : ℝ) * Real.log q) := by
        rw [Real.exp_nat_mul, Real.exp_log hq]
      _ ≤ _ := Real.exp_le_exp.mpr (by
        nlinarith [mul_le_mul_of_nonpos_right hlo hqlog.le,
          mul_le_mul_of_nonneg_right hb₂ hLi])
  have hsum : (∑ k ∈ Finset.range (K i), B ^ (k + 1)) ≤ (K i : ℝ) * B ^ K i := by
    calc
      _ ≤ ∑ _k ∈ Finset.range (K i), B ^ K i := by
        apply Finset.sum_le_sum
        intro k hk
        exact pow_le_pow_right₀ hB (Nat.succ_le_of_lt (Finset.mem_range.mp hk))
      _ = _ := by simp
  have hpow : B ^ K i ≤ Real.exp (δ * L i * Real.log B) := by
    calc
      B ^ K i = Real.exp ((K i : ℝ) * Real.log B) := by
        rw [Real.exp_nat_mul, Real.exp_log (by linarith : 0 < B)]
      _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hhi (Real.log_nonneg hB))
  have hcount : (K i : ℝ) ≤ Real.exp (δ / 2 * L i) :=
    hhi.trans (by simpa using hfactor)
  refine ⟨hclock', hgeom, hsum.trans ?_⟩
  calc
    _ ≤ Real.exp (δ / 2 * L i) * Real.exp (δ * L i * Real.log B) :=
      mul_le_mul hcount hpow (by positivity) (by positivity)
    _ ≤ Real.exp (lam * (v * (δ * L i))) * Real.exp (-b * L i) := by
      rw [← Real.exp_add, ← Real.exp_add]
      apply Real.exp_le_exp.mpr
      rw [← mul_assoc, hv]
      nlinarith [mul_le_mul_of_nonneg_right hb₁ hLi]

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas
