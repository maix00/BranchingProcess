/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Mogulskii.Spectral.Scaling.Power
public import Probability.Process.RandomWalk.Rademacher.FiniteInterval.Spectral.Survival.Bounds
public import Probability.Process.RandomWalk.Rademacher.FiniteInterval.Spectral.Survival.Upper

/-!
# Variable-scale spectral upper bounds

The public declarations in this module are:

For $N\ge2$, let $K_N$ be the transition matrix on
$\{0,\ldots,N-1\}$ with $K_N(x,y)=\frac12$ when $|x-y|=1$ and $0$
otherwise, and define the killed row sum
$R_{N,t}(x)=\sum_{y=0}^{N-1}K_N^t(x,y)$.

- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.scaledLog_remainingMass_le_main_add_geometricCorrection`:
  for $N>1$, $t>0$, and a start $x$, put $W=N+1$ and
  $\lambda_N=\cos(\frac{\pi}{W})$. Then
  $\frac{W^2}{t}\log R_{N,t}(x)\le
  W^2\log\lambda_N+\frac{W^2}{t}
  \log(\frac{4}{1-\lambda_N^t})$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.eventually_scaledLog_remainingMass_lt_neg_pi_sq_div_two_add`:
  if $W_n\to\infty$ and $W_n^2/t_n\to0$, then for every $\varepsilon>0$,
  eventually $\frac{W_n^2}{t_n}\log R_{N_n,t_n}(x_n)<-\pi^2/2+\varepsilon$.
- `ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii.eventually_scaledLog_rademacherIncrement_lt_neg_pi_sq_div_two_add`:
  the same upper rate holds for the IID Rademacher probability of staying in
  the interval through time $t_n$.

These lemmas combine the geometric spectral estimate with the principal
eigenvalue asymptotic to give the sharp upper rate under the diffusive scale.
-/

open Filter Topology


open ProbabilityTheory.RandomWalk.Rademacher.FiniteInterval

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii

/-- Pointwise logarithmic upper bound furnished by the complete sine
spectrum.  Unlike the ground-state comparison, its correction has no
interval-width prefactor. -/
theorem scaledLog_remainingMass_le_main_add_geometricCorrection
    {interiorCount time : ℕ} (hcount : 1 < interiorCount)
    (htime : 0 < time) (start : Fin interiorCount) :
    ((interiorCount + 1 : ℕ) : ℝ) ^ 2 / (time : ℝ) *
        Real.log (Kernel.remainingMass
          (intervalRademacherKernel interiorCount) time start).toReal ≤
      ((interiorCount + 1 : ℕ) : ℝ) ^ 2 *
          Real.log (Real.cos
            (Real.pi / ((interiorCount + 1 : ℕ) : ℝ))) +
        ((interiorCount + 1 : ℕ) : ℝ) ^ 2 / (time : ℝ) *
          Real.log (4 / (1 -
            Real.cos (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) ^ time)) := by
  let q : ℝ := Real.cos (Real.pi / ((interiorCount + 1 : ℕ) : ℝ))
  let mass : ENNReal := Kernel.remainingMass
    (intervalRademacherKernel interiorCount) time start
  have hqPos : 0 < q := by
    simpa [q] using intervalEigenvalue_pos hcount
  have hwidth : (2 : ℝ) ≤ ((interiorCount + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_lt_of_lt hcount)
  have hanglePos : 0 < Real.pi / ((interiorCount + 1 : ℕ) : ℝ) := by
    positivity
  have hangleLeHalf : Real.pi / ((interiorCount + 1 : ℕ) : ℝ) ≤
      Real.pi / 2 :=
    div_le_div_of_nonneg_left Real.pi_pos.le (by norm_num) hwidth
  have hqLtOne : q < 1 := by
    have hanti := Real.strictAntiOn_cos
      (show (0 : ℝ) ∈ Set.Icc 0 Real.pi by
        constructor <;> linarith [Real.pi_pos])
      (show Real.pi / ((interiorCount + 1 : ℕ) : ℝ) ∈
          Set.Icc 0 Real.pi by
        constructor
        · exact hanglePos.le
        · exact hangleLeHalf.trans (by linarith [Real.pi_pos]))
      hanglePos
    simpa [q] using hanti
  have hqPowLtOne : q ^ time < 1 :=
    pow_lt_one₀ hqPos.le hqLtOne htime.ne'
  have hmassEq : mass.toReal =
      ∑ finish, (intervalKernel interiorCount ^ time) start finish := by
    dsimp [mass, Kernel.remainingMass]
    rw [intervalRademacherKernel_eq_ofRealMatrix,
      intervalKernel_pow_apply_univ, ENNReal.toReal_ofReal]
    exact Finset.sum_nonneg fun _ _ =>
      Matrix.pow_apply_nonneg (intervalKernel_nonneg interiorCount) _ _ _
  have hmassUpper : mass.toReal ≤ 4 * (q ^ time / (1 - q ^ time)) := by
    rw [hmassEq]
    simpa [q] using intervalKernel_pow_rowSum_le_four_mul_div_one_sub
      (Nat.zero_lt_of_lt hcount) htime start
  have hmassTop : mass ≠ ⊤ := by
    exact ne_of_lt ((Kernel.remainingMass_le_one
      (intervalRademacherKernel interiorCount) time start).trans_lt
        ENNReal.one_lt_top)
  have hendpointPos : 0 < Real.sin
      (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) := by
    apply Real.sin_pos_of_pos_of_lt_pi
    · exact hanglePos
    · exact hangleLeHalf.trans_lt (by linarith [Real.pi_pos])
  have hlower := (intervalRademacherKernel_remainingMass_uniform_bounds
    hcount time start).1
  have hproductPos : 0 < Real.sin
      (Real.pi / ((interiorCount + 1 : ℕ) : ℝ)) * q ^ time :=
    mul_pos hendpointPos (pow_pos hqPos _)
  have hmassPos : 0 < mass.toReal := by
    have hmassENN : 0 < mass := by
      apply (ENNReal.ofReal_pos.2 hproductPos).trans_le
      simpa [mass, q] using hlower
    exact ENNReal.toReal_pos hmassENN.ne' hmassTop
  have hlog := Real.log_le_log hmassPos hmassUpper
  have hfactorPos : 0 < 4 / (1 - q ^ time) := by
    positivity
  have hupperRewrite : 4 * (q ^ time / (1 - q ^ time)) =
      q ^ time * (4 / (1 - q ^ time)) := by ring
  rw [hupperRewrite, Real.log_mul (pow_pos hqPos _).ne' hfactorPos.ne',
    Real.log_pow] at hlog
  have hratioNonneg : 0 ≤
      ((interiorCount + 1 : ℕ) : ℝ) ^ 2 / (time : ℝ) := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hlog hratioNonneg
  calc
    ((interiorCount + 1 : ℕ) : ℝ) ^ 2 / (time : ℝ) *
        Real.log mass.toReal ≤
      ((interiorCount + 1 : ℕ) : ℝ) ^ 2 / (time : ℝ) *
        ((time : ℝ) * Real.log q +
          Real.log (4 / (1 - q ^ time))) := hscaled
    _ = ((interiorCount + 1 : ℕ) : ℝ) ^ 2 * Real.log q +
        ((interiorCount + 1 : ℕ) : ℝ) ^ 2 / (time : ℝ) *
          Real.log (4 / (1 - q ^ time)) := by
      field_simp [(Nat.cast_ne_zero.mpr htime.ne')]
    _ = _ := by rfl

/-- Sharp spectral upper estimate under the sole diffusive-scale condition
`width² / time → 0`. -/
theorem eventually_scaledLog_remainingMass_lt_neg_pi_sq_div_two_add
    (interiorCount time : ℕ → ℕ)
    (start : ∀ n, Fin (interiorCount n))
    (hcount : ∀ n, 1 < interiorCount n)
    (htime : ∀ n, 0 < time n)
    (hwidth : Tendsto (fun n => ((interiorCount n + 1 : ℕ) : ℝ))
      atTop atTop)
    (hratio : Tendsto (fun n =>
      ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ))
      atTop (nhds 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ) *
          Real.log (Kernel.remainingMass
            (intervalRademacherKernel (interiorCount n))
            (time n) (start n)).toReal <
        -(Real.pi ^ 2) / 2 + ε := by
  let main : ℕ → ℝ := fun n =>
    ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 *
      Real.log (Real.cos
        (Real.pi / ((interiorCount n + 1 : ℕ) : ℝ)))
  let correction : ℕ → ℝ := fun n =>
    ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ) *
      Real.log (4 / (1 -
        Real.cos (Real.pi / ((interiorCount n + 1 : ℕ) : ℝ)) ^ time n))
  have hmain : Tendsto main atTop (nhds (-(Real.pi ^ 2) / 2)) := by
    convert tendsto_sq_mul_log_cos_pi_div.comp hwidth using 1
    funext n
    simp [main, Function.comp_apply, Nat.cast_add, Nat.cast_one]
  have hcorrection : Tendsto correction atTop (nhds 0) := by
    simpa [correction] using tendsto_scaledLog_geometricCorrection
      interiorCount time hcount htime hwidth hratio
  have hupperTendsto : Tendsto (fun n => main n + correction n)
      atTop (nhds (-(Real.pi ^ 2) / 2)) := by
    simpa using hmain.add hcorrection
  have heventuallyUpper : ∀ᶠ n in atTop,
      main n + correction n < -(Real.pi ^ 2) / 2 + ε :=
    (tendsto_order.1 hupperTendsto).2 _ (by linarith)
  filter_upwards [heventuallyUpper] with n hn
  exact (scaledLog_remainingMass_le_main_add_geometricCorrection
    (hcount n) (htime n) (start n)).trans_lt (by
      simpa [main, correction] using hn)

/-- Process-law form of the sharp spectral upper estimate. -/
theorem eventually_scaledLog_rademacherIncrement_lt_neg_pi_sq_div_two_add
    (interiorCount time : ℕ → ℕ)
    (start : ∀ n, Fin (interiorCount n))
    (hcount : ∀ n, 1 < interiorCount n)
    (htime : ∀ n, 0 < time n)
    (hwidth : Tendsto (fun n => ((interiorCount n + 1 : ℕ) : ℝ))
      atTop atTop)
    (hratio : Tendsto (fun n =>
      ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ))
      atTop (nhds 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      ((interiorCount n + 1 : ℕ) : ℝ) ^ 2 / (time n : ℝ) *
          Real.log (ENNReal.toReal
            (iidSequenceLaw rademacherMeasure
        {increment | InClosedInterval 1 (interiorCount n)
                (time n) (intervalSite (start n)) increment})) <
        -(Real.pi ^ 2) / 2 + ε := by
  filter_upwards [eventually_scaledLog_remainingMass_lt_neg_pi_sq_div_two_add
    interiorCount time start hcount htime hwidth hratio hε] with n hn
  rw [← intervalRademacherKernel_pow_apply_univ_eq_randomWalkInterval]
  exact hn

end ProbabilityTheory.RandomWalk.SmallDeviation.Mogulskii
