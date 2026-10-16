/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Slow diagonal selection

If each fixed natural parameter eventually satisfies a predicate, one can let
the parameter grow to infinity slowly enough that the predicate still holds
along the diagonal. This is a general order/filter construction and does not
depend on asymptotic growth theory.
-/

@[expose] public section

namespace Filter

open Filter
open scoped BigOperators

/-- Choose a nondecreasing natural parameter tending to infinity while
retaining any property that holds eventually for each fixed parameter. -/
theorem exists_tendsto_slowDiagonal {P : ℕ → ℕ → Prop}
    (hP : ∀ k, ∀ᶠ n : ℕ in atTop, P k n) :
    ∃ d : ℕ → ℕ, Monotone d ∧ Tendsto d atTop atTop ∧
      ∀ᶠ n : ℕ in atTop, P (d n) n := by
  classical
  have hthreshold_exists : ∀ k, ∃ N, ∀ n, N ≤ n → P k n := by
    intro k
    rcases Filter.eventually_atTop.1 (hP k) with ⟨N, hN⟩
    exact ⟨N, hN⟩
  let threshold : ℕ → ℕ := fun k => Classical.choose (hthreshold_exists k)
  have hthreshold (k n : ℕ) (hn : threshold k ≤ n) : P k n :=
    Classical.choose_spec (hthreshold_exists k) n hn
  let envelope : ℕ → ℕ :=
    fun k => k + ∑ j ∈ Finset.range (k + 1), threshold j
  have henvelope_ge (k : ℕ) : k ≤ envelope k := by
    simp [envelope]
  have hthreshold_le_envelope (k : ℕ) : threshold k ≤ envelope k := by
    have hmem : k ∈ Finset.range (k + 1) := by simp
    have hsum : threshold k ≤ ∑ j ∈ Finset.range (k + 1), threshold j :=
      Finset.single_le_sum (s := Finset.range (k + 1))
        (f := threshold) (fun j hj => Nat.zero_le _) hmem
    dsimp [envelope]
    omega
  let candidates (n : ℕ) : Finset ℕ :=
    (Finset.range (n + 1)).filter fun k => envelope k ≤ n
  let d : ℕ → ℕ := fun n => (candidates n).sup id
  have hcandidates_mono {n m : ℕ} (hnm : n ≤ m) :
      candidates n ⊆ candidates m := by
    intro k hk
    simp only [candidates, Finset.mem_filter, Finset.mem_range] at hk ⊢
    exact ⟨by omega, hk.2.trans hnm⟩
  have hdmono : Monotone d := by
    intro n m hnm
    exact Finset.sup_mono (hcandidates_mono hnm)
  have hd_le (n : ℕ) : d n ≤ n := by
    apply Finset.sup_le
    intro k hk
    simp only [candidates, Finset.mem_filter, Finset.mem_range] at hk
    exact Nat.lt_succ_iff.mp hk.1
  have hle_d (n b : ℕ) (hb : b ∈ candidates n) : b ≤ d n := by
    exact Finset.le_sup (f := id) hb
  have hd_tendsto : Tendsto d atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop (envelope b)] with n hn
    have hb : b ∈ candidates n := by
      simp only [candidates, Finset.mem_filter, Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le ((henvelope_ge b).trans hn), hn⟩
    exact hle_d n b hb
  have hdiag : ∀ᶠ n : ℕ in atTop, envelope (d n) ≤ n := by
    filter_upwards [eventually_ge_atTop (envelope 0)] with n hn
    have hnonempty : (candidates n).Nonempty := by
      refine ⟨0, ?_⟩
      simp only [candidates, Finset.mem_filter, Finset.mem_range]
      exact ⟨by simp, hn⟩
    have hsup_mem : d n ∈ id '' (↑(candidates n) : Set ℕ) := by
      change (candidates n).sup id ∈ id '' (↑(candidates n) : Set ℕ)
      exact Finset.sup_mem_of_nonempty hnonempty
    obtain ⟨k, hk, hkd⟩ := (Set.mem_image id (↑(candidates n) : Set ℕ) (d n)).mp hsup_mem
    change k = d n at hkd
    subst k
    exact (Finset.mem_filter.mp hk).2
  refine ⟨d, hdmono, hd_tendsto, ?_⟩
  filter_upwards [hdiag] with n hn
  exact hthreshold (d n) n ((hthreshold_le_envelope (d n)).trans hn)

end Filter

end
