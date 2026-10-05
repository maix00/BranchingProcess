/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Analysis.Asymptotics.InverseScale

/-!
# Slow diagonal selection

If each fixed natural parameter eventually satisfies a predicate, one can let
the parameter grow to infinity slowly enough that the predicate still holds
along the diagonal. The construction uses the generalized inverse of an
increasing envelope of the eventual thresholds.
-/

@[expose] public section

namespace Asymptotics

open Filter

/-- Choose a parameter tending to infinity while retaining any property that
holds eventually for each fixed parameter. -/
theorem exists_tendsto_slowDiagonal {P : ℕ → ℕ → Prop}
    (hP : ∀ k, ∀ᶠ n : ℕ in atTop, P k n) :
    ∃ d : ℕ → ℕ, Tendsto d atTop atTop ∧ ∀ᶠ n : ℕ in atTop, P (d n) n := by
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
  have henvelope : Tendsto envelope atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with k hk
    exact hk.trans (henvelope_ge k)
  have hd : Tendsto (upperInverseScale envelope) atTop atTop :=
    tendsto_upperInverseScale_atTop henvelope
  have hinverse_pos :
      ∀ᶠ n : ℕ in atTop, 0 < inverseScale envelope (n + 1) := by
    obtain ⟨N, hN⟩ :=
      Filter.eventually_atTop.1 (tendsto_atTop.1
        (tendsto_inverseScale_atTop henvelope) 1)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hbound := hN (n + 1) (by omega)
    omega
  have htime : ∀ᶠ n : ℕ in atTop,
      envelope (upperInverseScale envelope n) < n := by
    filter_upwards [hinverse_pos] with n hn
    have hpred := scale_pred_inverseScale_add_one_lt
      (L := envelope) (n := n + 1) hn
    rw [upperInverseScale_apply]
    omega
  refine ⟨upperInverseScale envelope, hd, ?_⟩
  filter_upwards [htime] with n hn
  exact hthreshold (upperInverseScale envelope n) n
    ((hthreshold_le_envelope (upperInverseScale envelope n)).trans
      (Nat.le_of_lt hn))

end Asymptotics

end
