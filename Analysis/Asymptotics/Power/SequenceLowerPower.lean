/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.Power.SumLower
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Lower power bounds from prefix sums

The public theorem in this file is:

- `Asymptotics.lower_power_of_prefix`: if $F_n>0$, $0<\gamma<\beta$,
  $\gamma\le1$, and $\beta\sum_{k=0}^{n-N}F_k\le nF_n$ for
  all $n\ge N$, then $F_n\ge C(n+1)^{\gamma-1}$ for a constant $C>0$.

The proof uses induction and the lower Riemann-sum bound for
$\sum_{k=0}^{m}(k+1)^{\gamma-1}$.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Asymptotics

private theorem initial_lower
    (F : ℕ → ℝ) (hF : ∀ n, 0 < F n) (γ : ℝ) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ k < N,
      C * (((k + 1 : ℕ) : ℝ) ^ (γ - 1)) ≤ F k := by
  induction N with
  | zero =>
      exact ⟨1, by positivity, by intros k hk; omega⟩
  | succ N ih =>
      obtain ⟨C, hC, hbound⟩ := ih
      let w : ℝ := (((N + 1 : ℕ) : ℝ) ^ (γ - 1))
      have hw : 0 < w := by dsimp [w]; positivity
      refine ⟨min C (F N / w), lt_min hC (div_pos (hF N) hw), ?_⟩
      intro k hk
      by_cases h : k < N
      · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)).trans
          (hbound k h)
      · have hkN : k = N := by omega
        subst k
        calc
          min C (F N / w) * (((N + 1 : ℕ) : ℝ) ^ (γ - 1)) ≤
              (F N / w) * (((N + 1 : ℕ) : ℝ) ^ (γ - 1)) := by
                exact mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
          _ = F N := by dsimp [w]; field_simp [ne_of_gt hw]

private theorem eventual_margin {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ)
    (hγβ : γ < β) (hγ1 : γ ≤ 1) (N : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      γ * (((n + 1 : ℕ) : ℝ) ^ γ) ≤
        β * ((((n - N + 2 : ℕ) : ℝ) ^ γ) - 1) := by
  let δ : ℝ := (β - γ) / (4 * β)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ2 : 2 * δ < 1 := by dsimp [δ]; field_simp; linarith
  have hcoeff : γ < β * (1 - 2 * δ) := by dsimp [δ]; field_simp; linarith
  have hcastTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hpowTop : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ γ)) atTop atTop := by
    exact (tendsto_rpow_atTop hγ).comp
      (hcastTop.comp (tendsto_add_atTop_nat 1))
  have hlarge : ∀ᶠ n : ℕ in atTop,
      (N : ℝ) / δ ≤ (n : ℝ) := tendsto_atTop.1 hcastTop _
  have hpowlarge : ∀ᶠ n : ℕ in atTop,
      1 / δ ≤ (((n + 1 : ℕ) : ℝ) ^ γ) := tendsto_atTop.1 hpowTop _
  filter_upwards [eventually_ge_atTop N, hlarge, hpowlarge] with n hn hlarge hpowlarge
  have hnreal : (N : ℝ) ≤ δ * ((n + 1 : ℕ) : ℝ) := by
    apply (div_le_iff₀ hδ).mp at hlarge
    push_cast at *
    nlinarith
  have hbase : (1 - δ) * ((n + 1 : ℕ) : ℝ) ≤ ((n - N + 2 : ℕ) : ℝ) := by
    have hsub : n - N + N = n := Nat.sub_add_cancel hn
    have hsubR : ((n - N : ℕ) : ℝ) + (N : ℝ) = (n : ℝ) := by
      exact_mod_cast hsub
    push_cast at hnreal ⊢
    nlinarith
  have hδle : 0 ≤ 1 - δ := by linarith
  have hbasepos : 0 ≤ ((n - N + 2 : ℕ) : ℝ) := by positivity
  have hprod : ((1 - δ) * ((n + 1 : ℕ) : ℝ)) ^ γ =
      (1 - δ) ^ γ * (((n + 1 : ℕ) : ℝ) ^ γ) := by
    rw [Real.mul_rpow hδle (by positivity)]
  have hpowmono : ((1 - δ) * ((n + 1 : ℕ) : ℝ)) ^ γ ≤
      (((n - N + 2 : ℕ) : ℝ) ^ γ) :=
    Real.rpow_le_rpow (by positivity) hbase hγ.le
  have hδpow : 1 - δ ≤ (1 - δ) ^ γ := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge (by linarith) (by linarith) hγ1)
  have hpowbound : (1 - δ) * (((n + 1 : ℕ) : ℝ) ^ γ) ≤
      (((n - N + 2 : ℕ) : ℝ) ^ γ) := by
    calc
      _ ≤ (1 - δ) ^ γ * (((n + 1 : ℕ) : ℝ) ^ γ) :=
        mul_le_mul_of_nonneg_right hδpow (by positivity)
      _ = ((1 - δ) * ((n + 1 : ℕ) : ℝ)) ^ γ := hprod.symm
      _ ≤ _ := hpowmono
  have hpowpos : 0 < (((n + 1 : ℕ) : ℝ) ^ γ) := by positivity
  have hsmall : 1 ≤ δ * (((n + 1 : ℕ) : ℝ) ^ γ) := by
    simpa [mul_comm] using (div_le_iff₀ hδ).mp hpowlarge
  nlinarith [mul_le_mul_of_nonneg_left hpowbound hβ.le]

/-- A positive sequence whose prefix sum feeds back into its next value
has a polynomial lower bound. -/
theorem lower_power_of_prefix
    (F : ℕ → ℝ) (hF : ∀ n, 0 < F n)
    {β γ : ℝ} (hβ : 0 < β) (hγ : 0 < γ) (hγβ : γ < β)
    (hγ1 : γ ≤ 1) (N : ℕ) (hN : 1 ≤ N)
    (hprefix : ∀ n, N ≤ n →
      β * ∑ k ∈ Finset.range (n - N + 1), F k ≤ (n : ℝ) * F n) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      C * (((n + 1 : ℕ) : ℝ) ^ (γ - 1)) ≤ F n := by
  obtain ⟨n₀, hlimit⟩ := Filter.eventually_atTop.1
    ((eventual_margin hβ hγ hγβ hγ1 N).and
      (eventually_ge_atTop N))
  obtain ⟨C, hC, hbase⟩ := initial_lower F hF γ n₀
  refine ⟨C, hC, ?_⟩
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < n₀
    · exact hbase n hn
    · have hn₀ : n₀ ≤ n := by omega
      have hNn : N ≤ n := (hlimit n hn₀).2
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le hN hNn)
      have hk_lt : ∀ k ∈ Finset.range (n - N + 1), k < n := by
        intro k hk
        have := Finset.mem_range.mp hk
        omega
      have hsum : C * ∑ k ∈ Finset.range (n - N + 1),
          (((k + 1 : ℕ) : ℝ) ^ (γ - 1)) ≤
          ∑ k ∈ Finset.range (n - N + 1), F k := by
        rw [Finset.mul_sum]
        apply Finset.sum_le_sum
        intro k hk
        exact ih k (hk_lt k hk)
      have hpow := Asymptotics.rpow_sum_lower hγ hγ1 (n - N)
      have hmargin := (hlimit n hn₀).1
      have htarget : C * (((n + 1 : ℕ) : ℝ) ^ γ) ≤ (n : ℝ) * F n := by
        calc
          C * (((n + 1 : ℕ) : ℝ) ^ γ) ≤
              C * ((β * ((((n - N + 2 : ℕ) : ℝ) ^ γ) - 1)) / γ) := by
                exact mul_le_mul_of_nonneg_left ((le_div_iff₀ hγ).2 (by simpa only [mul_comm] using hmargin)) hC.le
          _ ≤ β * (C * ∑ k ∈ Finset.range (n - N + 1),
                (((k + 1 : ℕ) : ℝ) ^ (γ - 1))) := by
                  have h := mul_le_mul_of_nonneg_left hpow (mul_nonneg hβ.le hC.le)
                  convert h using 1 <;> ring
          _ ≤ β * ∑ k ∈ Finset.range (n - N + 1), F k :=
              mul_le_mul_of_nonneg_left hsum hβ.le
          _ ≤ (n : ℝ) * F n := hprefix n hNn
      have hcast : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
      have hpowpos : 0 < (((n + 1 : ℕ) : ℝ) ^ (γ - 1)) := by positivity
      have hpoweq : (((n + 1 : ℕ) : ℝ) ^ γ) =
          ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) ^ (γ - 1)) := by
        calc
          _ = (((n + 1 : ℕ) : ℝ) ^ (1 + (γ - 1))) := by congr 1; ring
          _ = (((n + 1 : ℕ) : ℝ) ^ (1 : ℝ)) *
              (((n + 1 : ℕ) : ℝ) ^ (γ - 1)) := by
                rw [Real.rpow_add (by positivity)]
          _ = _ := by rw [Real.rpow_one]
      rw [hpoweq] at htarget
      have hnonneg : 0 ≤ C * (((n + 1 : ℕ) : ℝ) ^ (γ - 1)) :=
        mul_nonneg hC.le hpowpos.le
      nlinarith

end Asymptotics

end
