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
  have hmono : Monotone (upperInverseScale envelope) := by
    intro n m hnm
    rw [upperInverseScale_apply, upperInverseScale_apply]
    apply Nat.sub_le_sub_right
    exact inverseScale_mono henvelope (by omega)
  refine ⟨upperInverseScale envelope, hmono, hd, ?_⟩
  filter_upwards [htime] with n hn
  exact hthreshold (upperInverseScale envelope n) n
    ((hthreshold_le_envelope (upperInverseScale envelope n)).trans
      (Nat.le_of_lt hn))

/-- Along any sequence of nonnegative errors tending to zero, choose the
fixed-parameter diagonal slowly enough that the parameter times the error
also tends to zero. This is the quantitative form used when the source scale
requires a growing parameter to remain negligible relative to the norming. -/
theorem exists_tendsto_slowDiagonal_mul_tendsto_zero
    {P : ℕ → ℕ → Prop} {r : ℕ → ℝ}
    (hP : ∀ k, ∀ᶠ n : ℕ in atTop, P k n)
    (hr : Tendsto r atTop (nhds 0))
    (hr_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ r n) :
    ∃ d : ℕ → ℕ, Monotone d ∧ Tendsto d atTop atTop ∧
      (∀ᶠ n : ℕ in atTop, P (d n) n) ∧
      Tendsto (fun n => (d n : ℝ) * r n) atTop (nhds 0) := by
  have hcombined : ∀ k, ∀ᶠ n : ℕ in atTop,
      P k n ∧ (k : ℝ) * r n ≤ 1 / ((k : ℝ) + 1) := by
    intro k
    have hmul : Tendsto (fun n => (k : ℝ) * r n) atTop (nhds 0) := by
      simpa using tendsto_const_nhds.mul hr
    have hbound : ∀ᶠ n : ℕ in atTop,
        (k : ℝ) * r n < 1 / ((k : ℝ) + 1) :=
      hmul.eventually (Iio_mem_nhds (by positivity))
    exact (hP k).and (hbound.mono fun n hn => le_of_lt hn)
  obtain ⟨d, hmono, hd, hdiag⟩ := exists_tendsto_slowDiagonal hcombined
  have hproperty : ∀ᶠ n : ℕ in atTop, P (d n) n :=
    hdiag.mono fun n hn => hn.1
  have hbound : ∀ᶠ n : ℕ in atTop,
      (d n : ℝ) * r n ≤ 1 / ((d n : ℝ) + 1) :=
    hdiag.mono fun n hn => hn.2
  have hdcast : Tendsto (fun n => (d n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hd
  have hdplus : Tendsto (fun n => (d n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 hdcast
  have hdenomInv : Tendsto (fun n => ((d n : ℝ) + 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hdplus
  have hdenom : Tendsto (fun n => 1 / ((d n : ℝ) + 1)) atTop (nhds 0) := by
    simpa only [one_div] using hdenomInv
  have hproduct_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ (d n : ℝ) * r n :=
    hr_nonneg.mono fun n hn => mul_nonneg (Nat.cast_nonneg _) hn
  exact ⟨d, hmono, hd, hproperty,
    squeeze_zero' hproduct_nonneg hbound hdenom⟩

end Asymptotics

end
