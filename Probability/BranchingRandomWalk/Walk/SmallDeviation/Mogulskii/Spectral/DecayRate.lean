import Probability.BranchingRandomWalk.Walk.SmallDeviation.Mogulskii.Spectral.SurvivalBounds
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Long-time decay in a fixed interval

The uniform ground-state bounds identify the exponential decay rate of the
survival probability in every fixed finite interval.
-/

open Filter Topology
open scoped BigOperators Matrix

namespace ProbabilityTheory.BranchingRandomWalk.RandomWalk.Mogulskii

/-- For a fixed interval, the logarithmic row-sum decay is the logarithm of
the principal Dirichlet eigenvalue, independently of the starting site. -/
theorem tendsto_log_intervalKernel_pow_rowSum_div
    {interiorCount : ℕ} (hcount : 1 < interiorCount)
    (start : Fin interiorCount) :
    Tendsto (fun n : ℕ =>
        Real.log (∑ finish,
          (intervalKernel interiorCount ^ n) start finish) / (n : ℝ))
      atTop
      (nhds (Real.log
        (Real.cos (Real.pi / (interiorCount + 1 : ℕ))))) := by
  let lower := Real.sin (Real.pi / (interiorCount + 1 : ℕ))
  let eigenvalue := Real.cos (Real.pi / (interiorCount + 1 : ℕ))
  let mass : ℕ → ℝ := fun n =>
    ∑ finish, (intervalKernel interiorCount ^ n) start finish
  have hlower : 0 < lower := by
    have h := intervalSineWeight_pos (Nat.zero_lt_of_lt hcount)
      (⟨0, Nat.zero_lt_of_lt hcount⟩ : Fin interiorCount)
    simpa [lower, intervalSineWeight, dirichletSine] using h
  have heigenvalue : 0 < eigenvalue := by
    simpa [eigenvalue] using intervalEigenvalue_pos hcount
  have hbounds : ∀ n,
      lower * eigenvalue ^ n ≤ mass n ∧
        mass n ≤ eigenvalue ^ n / lower := by
    intro n
    simpa [lower, eigenvalue, mass] using
      intervalKernel_pow_rowSum_uniform_bounds hcount n start
  have hlowerTendsto :
      Tendsto (fun n : ℕ =>
          Real.log eigenvalue + Real.log lower / (n : ℝ))
        atTop (nhds (Real.log eigenvalue)) := by
    simpa using tendsto_const_nhds.add
      (tendsto_const_div_atTop_nhds_zero_nat (Real.log lower))
  have hupperTendsto :
      Tendsto (fun n : ℕ =>
          Real.log eigenvalue - Real.log lower / (n : ℝ))
        atTop (nhds (Real.log eigenvalue)) := by
    simpa using tendsto_const_nhds.sub
      (tendsto_const_div_atTop_nhds_zero_nat (Real.log lower))
  have hsqueeze : Tendsto (fun n : ℕ => Real.log (mass n) / (n : ℝ))
      atTop (nhds (Real.log eigenvalue)) := by
    apply hlowerTendsto.squeeze' hupperTendsto
    · filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have hpowPos : 0 < eigenvalue ^ n := pow_pos heigenvalue n
      have hlog := Real.log_le_log (mul_pos hlower hpowPos) (hbounds n).1
      rw [Real.log_mul hlower.ne' hpowPos.ne', Real.log_pow] at hlog
      calc
        Real.log eigenvalue + Real.log lower / (n : ℝ) =
            (Real.log lower + (n : ℝ) * Real.log eigenvalue) / (n : ℝ) := by
              field_simp
              ring
        _ ≤ Real.log (mass n) / (n : ℝ) :=
          (div_le_div_iff_of_pos_right hnpos).2 hlog
    · filter_upwards [eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have hpowPos : 0 < eigenvalue ^ n := pow_pos heigenvalue n
      have hmassPos : 0 < mass n :=
        (mul_pos hlower hpowPos).trans_le (hbounds n).1
      have hlog := Real.log_le_log hmassPos (hbounds n).2
      rw [Real.log_div hpowPos.ne' hlower.ne', Real.log_pow] at hlog
      calc
        Real.log (mass n) / (n : ℝ) ≤
            ((n : ℝ) * Real.log eigenvalue - Real.log lower) / (n : ℝ) :=
          (div_le_div_iff_of_pos_right hnpos).2 hlog
        _ = Real.log eigenvalue - Real.log lower / (n : ℝ) := by
          field_simp
  simpa [mass, eigenvalue] using hsqueeze

/-- For a fixed finite interval and an interior lattice starting point, the
Rademacher random walk has the principal Dirichlet eigenvalue as its
logarithmic survival rate. -/
theorem tendsto_log_rademacherProcess_intervalProbability_div
    {interiorCount : ℕ} (hcount : 1 < interiorCount)
    (start : Fin interiorCount) :
    Tendsto (fun n : ℕ =>
        Real.log (ENNReal.toReal
          ((rademacher (intervalSite start)).law
            {walk | ProcessInClosedInterval id 1 interiorCount n walk})) /
          (n : ℝ))
      atTop
      (nhds (Real.log
        (Real.cos (Real.pi / (interiorCount + 1 : ℕ))))) := by
  have hprobability : ∀ n : ℕ,
      ENNReal.toReal
          ((rademacher (intervalSite start)).law
            {walk | ProcessInClosedInterval id 1 interiorCount n walk}) =
        ∑ finish, (intervalKernel interiorCount ^ n) start finish := by
    intro n
    rw [← intervalRademacherKernel_pow_apply_univ_eq_rademacherProcess,
      intervalRademacherKernel_eq_ofRealMatrix,
      intervalKernel_pow_apply_univ, ENNReal.toReal_ofReal]
    exact Finset.sum_nonneg fun _ _ =>
      Matrix.pow_apply_nonneg (intervalKernel_nonneg interiorCount) _ _ _
  convert tendsto_log_intervalKernel_pow_rowSum_div hcount start using 1
  funext n
  rw [hprobability]

end ProbabilityTheory.BranchingRandomWalk.RandomWalk.Mogulskii
