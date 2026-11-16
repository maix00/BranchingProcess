/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Analysis.Asymptotics.Sequence.LogarithmicScale
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Width and time in the critical affine corridor

## Internal proof declarations

* `ProbabilityTheory.BranchingRandomWalk.Spine.CriticalCorridor.cubeRootWidthFacts`:
  for $t_N=N^{1/3}$ and $\Delta_N=ct_N$ with $c>0$, both scales diverge,
  $N/\Delta_N^2=t_N/c^2$ at positive horizons, and
  $\lfloor\Delta_N^{5/2}\rfloor\le N$ eventually. Also
  $\sqrt{\Delta_N}/t_N\to0$ and $\log(N+1)/t_N\to0$.
-/

open Filter
open scoped Topology

namespace ProbabilityTheory.BranchingRandomWalk.Spine.CriticalCorridor

lemma cubeRootWidthFacts {c : ℝ} (hc : 0 < c) :
    let t (N : ℕ) := (N : ℝ) ^ (1 / 3 : ℝ)
    let width (N : ℕ) := c * t N
    Tendsto t atTop atTop ∧ Tendsto width atTop atTop ∧
      (∀ N : ℕ, 1 ≤ N → 0 < t N) ∧
      (∀ N : ℕ, 1 ≤ N → (N : ℝ) / width N ^ 2 = t N / c ^ 2) ∧
      (∀ᶠ N : ℕ in atTop, ⌊width N ^ (2 + 1 / 2 : ℝ)⌋₊ ≤ N) ∧
      Tendsto (fun N => width N ^ (1 / 2 : ℝ) / t N) atTop (𝓝 0) ∧
      Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1) / t N) atTop (𝓝 0) := by
  intro t width
  have ht : Tendsto t atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp tendsto_natCast_atTop_atTop
  have hw : Tendsto width atTop atTop := ht.const_mul_atTop hc
  have hcube (N : ℕ) : t N ^ (3 : ℝ) = (N : ℝ) := by
    dsimp [t]
    rw [← Real.rpow_mul (Nat.cast_nonneg N)]
    norm_num
  have htpos (N : ℕ) (hN : 1 ≤ N) : 0 < t N :=
    Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (by omega : N ≠ 0)) _
  have hratio (N : ℕ) (hN : 1 ≤ N) : (N : ℝ) / width N ^ 2 = t N / c ^ 2 := by
    have h := htpos N hN
    rw [← (Real.rpow_natCast (t N) 3).symm.trans (hcube N)]
    dsimp [width]
    field_simp
  have hhalf : Tendsto (fun N => t N ^ (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp ht
  have hscale : ∀ᶠ N : ℕ in atTop, ⌊width N ^ (2 + 1 / 2 : ℝ)⌋₊ ≤ N := by
    filter_upwards [hhalf.eventually_ge_atTop (c ^ (2 + 1 / 2 : ℝ)),
      eventually_ge_atTop (1 : ℕ)] with N hlarge hN
    have htN := htpos N hN
    apply Nat.floor_le_of_le
    rw [← hcube, show (3 : ℝ) = (2 + 1 / 2) + 1 / 2 by norm_num,
      Real.rpow_add htN, show width N = c * t N from rfl, Real.mul_rpow hc.le htN.le]
    simpa only [mul_comm (c ^ (2 + 1 / 2 : ℝ))] using
      mul_le_mul_of_nonneg_left hlarge (Real.rpow_nonneg htN.le _)
  have hcount : Tendsto (fun N : ℕ => Real.log ((N : ℝ) + 1) / t N) atTop (𝓝 0) :=
    Asymptotics.tendsto_log_add_one_div_scale_of_power_bound ht
      (Eventually.of_forall fun N : ℕ => Nat.cast_nonneg N) (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (0 : ℝ) < 3)
      (Eventually.of_forall fun N : ℕ => by rw [one_mul, hcube])
  have hsqrt : Tendsto (fun N => width N ^ (1 / 2 : ℝ) / t N) atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := c ^ (1 / 2 : ℝ))).div_atTop hhalf
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have htN := htpos N hN
    have htHalf := Real.rpow_pos_of_pos htN (1 / 2 : ℝ)
    rw [show width N = c * t N from rfl, Real.mul_rpow hc.le htN.le]
    have hsq : (t N ^ (1 / 2 : ℝ)) * (t N ^ (1 / 2 : ℝ)) = t N := by
      rw [← Real.rpow_add htN]
      norm_num
    apply (eq_div_iff htN.ne').2
    calc
      _ = c ^ (1 / 2 : ℝ) / t N ^ (1 / 2 : ℝ) *
          (t N ^ (1 / 2 : ℝ) * t N ^ (1 / 2 : ℝ)) := by rw [hsq]
      _ = _ := by field_simp
  exact ⟨ht, hw, htpos, hratio, hscale, hsqrt, hcount⟩

end ProbabilityTheory.BranchingRandomWalk.Spine.CriticalCorridor
