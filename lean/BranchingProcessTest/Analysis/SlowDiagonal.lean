import Analysis.Asymptotics.SlowDiagonal
import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Stable.Partition

open Filter

example : ∃ d : ℕ → ℕ, Monotone d ∧ Tendsto d atTop atTop ∧
    (∀ᶠ n : ℕ in atTop, d n ≤ n) ∧
    Tendsto (fun n => (d n : ℝ) * (1 / ((n : ℝ) + 1)))
      atTop (nhds 0) := by
  have hfixed : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop, k ≤ n := by
    intro k
    exact Filter.eventually_atTop.2 ⟨k, fun n hn => hn⟩
  have hnplus : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hrInv : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hnplus
  have hr : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) := by
    simpa only [one_div] using hrInv
  have hr_nonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ 1 / ((n : ℝ) + 1) :=
    Filter.Eventually.of_forall fun _ => by positivity
  obtain ⟨d, hmono, hd, hP, hmul⟩ :=
    Asymptotics.exists_tendsto_slowDiagonal_mul_tendsto_zero
      hfixed hr hr_nonneg
  exact ⟨d, hmono, hd, hP, hmul⟩

#print axioms Asymptotics.exists_tendsto_slowDiagonal
#print axioms Asymptotics.exists_tendsto_slowDiagonal_mul_tendsto_zero
#print axioms ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.exists_slowDiagonal_within_stableScale
