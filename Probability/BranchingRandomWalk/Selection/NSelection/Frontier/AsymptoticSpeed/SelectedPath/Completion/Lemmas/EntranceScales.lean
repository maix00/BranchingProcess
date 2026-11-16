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

* `trialDuration_le` gives $d_N\le\alpha\log N/\log\rho+2$ for
  $d_N=\lfloor\alpha\log N/\log\rho\rfloor+2$.
* `rpow_mul_mean_le_pow_trialDuration` gives $\rho N^\alpha\le\rho^{d_N}$.
* `logarithmicEntrance_scales` bounds $K_N=\lfloor\delta\log N\rfloor$,
  parallel population capacity, and displacement.
* `logarithmicEntrance_deadline`: for $\gamma>0$, the deadline
  $T_N=\lfloor\gamma\log N\rfloor$ is $o(\log^3N)$ and eventually below
  the terminal generation.
* `eventually_exponential_trialRoot_bound`: for $B\ge1$ and
  $\lambda v=\log B+1$, the weighted trial-root bound
  $e^{-\lambda v\delta\log N}\sum_{k=1}^{K_N} B^k$ is at most
  $N^{-\delta/2}$ eventually.

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

/-- The growth trial uses $d_N=\ell-1$ generations, with a bounded rounding term. -/
lemma trialDuration_le {ρ : ℝ} (hρ : 1 < ρ) {α : ℝ} (ha : 0 ≤ α) (N : ℕ) :
    ((⌊α * Real.log (N : ℝ) / Real.log ρ⌋₊ + 2 : ℕ) : ℝ) ≤
      α * Real.log (N : ℝ) / Real.log ρ + 2 := by
  rw [Nat.cast_add]
  exact add_le_add_left (Nat.floor_le
    (div_nonneg (mul_nonneg ha (Real.log_natCast_nonneg N)) (Real.log_pos hρ).le)) _

/-- The mean at the corrected duration exceeds the target by a factor of at least $\rho$. -/
lemma rpow_mul_mean_le_pow_trialDuration {ρ : ℝ} (hρ : 1 < ρ)
    (N : ℕ) (α : ℝ) (hN : 1 ≤ N) :
    ρ * (N : ℝ) ^ α ≤ ρ ^ (⌊α * Real.log (N : ℝ) / Real.log ρ⌋₊ + 2) := by
  have hρlog := Real.log_pos hρ
  have hρpos : 0 < ρ := by positivity
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast Nat.zero_lt_of_lt hN
  let x := α * Real.log (N : ℝ) / Real.log ρ
  let d := ⌊x⌋₊ + 2
  have hfloor : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hbound : α * Real.log (N : ℝ) < ((⌊x⌋₊ : ℝ) + 1) * Real.log ρ :=
    (div_lt_iff₀ hρlog).mp hfloor
  have heq : ρ ^ d = Real.exp ((d : ℝ) * Real.log ρ) := by
    rw [Real.exp_nat_mul, Real.exp_log hρpos]
  change ρ * (N : ℝ) ^ α ≤ ρ ^ d
  rw [heq, ← Real.exp_log hρpos, Real.rpow_def_of_pos hNpos, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [Real.log_exp]
  simp only [d, Nat.cast_add, Nat.cast_ofNat]
  linarith

lemma logarithmicEntrance_scales
    {ρ α δ M v η : ℝ}
    (hρ : 1 < ρ) (ha : 0 < α) (hδ : 0 < δ)
    (hM : 0 ≤ M)
    (hsmall : α / Real.log ρ < 1 / (2 * Real.log 2))
    (hbudget : (v + M) * δ + M * (α / Real.log ρ) < η)
    {N : ℕ → ℕ} (hN : Tendsto N atTop atTop)
    (d : ℕ → ℕ) (hduration : ∀ i,
      (d i : ℝ) ≤ α * Real.log (N i : ℝ) / Real.log ρ + 2) :
    let L := fun i => Real.log (N i : ℝ)
    let K := fun i => ⌊δ * L i⌋₊
    ∀ᶠ i in atTop,
      δ * L i / 2 ≤ (K i : ℝ) ∧ (K i : ℝ) ≤ δ * L i ∧
      1 + (d i + 1) * (2 * 2 ^ d i) ≤ N i ∧
      v * (δ * L i) + (K i : ℝ) * M + M * d i ≤ η * L i := by
  intro L K
  have hL : Tendsto L atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)
  have hρlog : 0 < Real.log ρ := Real.log_pos hρ
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let A := α / Real.log ρ
  have hA : 0 < A := div_pos ha hρlog
  have hduration' (i : ℕ) : (d i : ℝ) ≤ A * L i + 2 := by
    simpa [A, div_eq_mul_inv, mul_right_comm] using hduration i
  have hA' : A < 1 / (2 * Real.log 2) := hsmall
  have hcapEventually : ∀ᶠ i in atTop, 1 + (d i + 1) * (2 * 2 ^ d i) ≤ N i := by
    filter_upwards [hL.eventually_ge_atTop (2 / (1 / (2 * Real.log 2) - A)),
      hL.eventually (eventually_affine_le_exp_mul (4 * A) 12 (1 / 2) (by norm_num)),
      hN.eventually_ge_atTop 2] with i hlog hfactor hN2
    have hd := hduration' i
    have hsmall' : (d i : ℝ) ≤ L i / (2 * Real.log 2) := by
      have hh := (div_le_iff₀ (sub_pos.mpr hA')).mp hlog
      rw [mul_sub, div_eq_mul_inv, one_mul] at hh
      rw [div_eq_mul_inv]
      linarith [mul_comm (L i) A]
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
  filter_upwards [hL.eventually_ge_atTop 1, hL.eventually_ge_atTop (2 / δ),
    hL.eventually_ge_atTop (2 * M / (η - ((v + M) * δ + M * A))),
    hcapEventually] with i hlog hlogK hlogc hcap
  have hLpos : 0 < L i := by linarith
  have hKhi : (K i : ℝ) ≤ δ * L i := Nat.floor_le (mul_nonneg hδ.le hLpos.le)
  have hKlo : δ * L i / 2 ≤ (K i : ℝ) := by
    have hlo : δ * L i < (K i : ℝ) + 1 := Nat.lt_floor_add_one _
    have hh : 2 ≤ L i * δ := (div_le_iff₀ hδ).mp hlogK
    nlinarith
  refine ⟨hKlo, hKhi, hcap, ?_⟩
  have hdle := mul_le_mul_of_nonneg_left (hduration' i) hM
  have hKle := mul_le_mul_of_nonneg_right hKhi hM
  have hc := (div_le_iff₀ (sub_pos.mpr hbudget)).mp hlogc
  nlinarith only [hdle, hKle, hc]

/-- For an integer generation $s$, the deadline $s\le\gamma\log N$
in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring* (Fudan University, 2026), Chapter 4, Theorems 1.1 and 1.2, is
equivalent to $s\le\lfloor\gamma\log N\rfloor$. -/
lemma logarithmicEntrance_deadline
    {γ : ℝ} (hγpos : 0 < γ)
    {N H : ℕ → ℕ} (hN : Tendsto N atTop atTop) {t : ℝ} (ht : 0 < t)
    (hH : Tendsto (fun i => (H i : ℝ) / Real.log (N i : ℝ) ^ 3) atTop (𝓝 t)) :
    let L := fun i => Real.log (N i : ℝ)
    let T := fun i => ⌊γ * L i⌋₊
    Tendsto (fun i => (T i : ℝ) / L i ^ 3) atTop (𝓝 0) ∧
    (∀ᶠ i in atTop, T i ≤ H i) := by
  intro L T
  have hL : Tendsto L atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hN)
  have hT : Tendsto (fun i => (T i : ℝ) / L i ^ 3) atTop (𝓝 0) := by
    have hzero : Tendsto (fun i => γ / L i ^ 2) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hL)
    apply squeeze_zero' (Eventually.of_forall fun i => by positivity) _ hzero
    filter_upwards [hL.eventually_ge_atTop 1] with i hi
    have hpos : 0 < L i := one_pos.trans_le hi
    have hup : (T i : ℝ) ≤ γ * L i := Nat.floor_le (mul_nonneg hγpos.le hpos.le)
    apply (div_le_div_iff₀ (pow_pos hpos _) (pow_pos hpos _)).mpr
    simpa only [pow_succ' (L i) 2, mul_assoc, mul_left_comm, mul_comm] using
      mul_le_mul_of_nonneg_right hup (sq_nonneg (L i))
  refine ⟨hT, ?_⟩
  filter_upwards [hL.eventually_ge_atTop 1,
    hT (gt_mem_nhds (show 0 < t / 2 by positivity)),
    hH (lt_mem_nhds (show t / 2 < t by linarith))] with i hi hTi hHi
  have hpos : 0 < L i ^ 3 := pow_pos (one_pos.trans_le hi) _
  have hle : (T i : ℝ) ≤ H i :=
    (div_le_div_iff_of_pos_right hpos).mp (hTi.le.trans hHi.le)
  exact_mod_cast hle

lemma eventually_exponential_trialRoot_bound
    {δ B lam v : ℝ} (hδ : 0 < δ)
    (hB : 1 ≤ B) (hv : lam * v = Real.log B + 1)
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) (K : ℕ → ℕ)
    (hK : ∀ᶠ i in atTop, (K i : ℝ) ≤ δ * L i) :
    ∀ᶠ i in atTop, (∑ k ∈ Finset.range (K i), B ^ (k + 1)) ≤
      Real.exp (lam * (v * (δ * L i))) * Real.exp (-(δ / 2) * L i) := by
  filter_upwards [hK,
    hL.eventually (eventually_affine_le_exp_mul δ 0 (δ / 2) (by positivity))]
    with i hhi hfactor
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
  refine hsum.trans ?_
  calc
    _ ≤ Real.exp (δ / 2 * L i) * Real.exp (δ * L i * Real.log B) :=
      mul_le_mul hcount hpow (by positivity) (by positivity)
    _ = Real.exp (lam * (v * (δ * L i))) * Real.exp (-(δ / 2) * L i) := by
      rw [← Real.exp_add, ← Real.exp_add, ← mul_assoc, hv]
      congr 1
      ring

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Frontier.AsymptoticSpeed.SelectedPath.Completion.Lemmas
