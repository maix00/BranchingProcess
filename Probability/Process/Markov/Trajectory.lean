/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.Markov.Basic
public import Probability.Kernel.IonescuTulcea.Markov

/-!
# The canonical homogeneous Markov process

## Public declarations

* `ProbabilityTheory.isMarkovChain_traj_historyKernel`: under the native
  Ionescu--Tulcea law started at `x`, the coordinate process is a Markov
  chain with kernel `K` and its natural filtration:
  `E[1_A(Xₙ) | X₀,…,Xₘ] = K^(n-m)(Xₘ,A)` for `m ≤ n`.

The construction and its conditional path law are Mathlib's `traj` and
`condExp_traj`; only the homogeneous endpoint identification is added here.
See O. Kallenberg, *Foundations of Modern Probability*, third edition
(2021), Theorem 8.24, DOI 10.1007/978-3-030-61871-1.
-/

@[expose] public section

open MeasureTheory Finset Preorder
open scoped ProbabilityTheory

namespace ProbabilityTheory

/-- The native homogeneous trajectory realizes the Markov property on any measurable state space. -/
theorem isMarkovChain_traj_historyKernel {S : Type*} [MeasurableSpace S]
    (K : Kernel S S) [IsMarkovKernel K] (x : S) :
    IsMarkovChain (fun n (w : ℕ → S) => w n) Filtration.piLE
      (Kernel.traj (X := fun _ => S) (Kernel.historyKernel K) 0 (fun _ => x)) K := by
  constructor
  · intro n
    rw [Filtration.piLE_eq_comap_frestrictLe]
    exact (show Measurable (fun h : Iic n → S => h ⟨n, by simp⟩) from
      measurable_pi_apply _).comp (comap_measurable (frestrictLe (π := fun _ => S) n))
  · intro m n hmn A hA
    have hB : MeasurableSet ((fun w : ℕ → S => w n) ⁻¹' A) :=
      hA.preimage (measurable_pi_apply n)
    have hi : Integrable (((fun w : ℕ → S => w n) ⁻¹' A).indicator
        (fun _ => (1 : ℝ)))
        (Kernel.traj (X := fun _ => S) (Kernel.historyKernel K) 0 (fun _ => x)) :=
      (integrable_const (1 : ℝ)).indicator hB
    refine (Kernel.condExp_traj (X := fun _ => S) (κ := Kernel.historyKernel K)
      (a := 0) (b := m) (x₀ := fun _ => x) (Nat.zero_le m) hi).trans ?_
    apply Filter.Eventually.of_forall
    intro w
    have hm := Kernel.traj_historyKernel_map_eval K hmn (frestrictLe m w)
    calc
      _ = ∫ z, A.indicator (fun _ => (1 : ℝ)) z
          ∂(Kernel.traj (X := fun _ => S) (Kernel.historyKernel K) m
            (frestrictLe m w)).map (fun y => y n) := by
        rw [integral_map_of_stronglyMeasurable
          (show Measurable (fun y : ℕ → S => y n) from measurable_pi_apply n)
          ((measurable_const.indicator hA).stronglyMeasurable :
            StronglyMeasurable (A.indicator (fun _ => (1 : ℝ))))]
        apply integral_congr_ae
        filter_upwards [] with y
        by_cases hy : y n ∈ A <;> simp [hy]
      _ = ((K ^ (n - m)) (w m) A).toReal := by
        rw [hm, integral_indicator_const (1 : ℝ) hA]
        simp only [smul_eq_mul, mul_one]
        rfl

end ProbabilityTheory

end
