/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.ZeroOne

/-!
# Ergodicity of an i.i.d. sequence shift

For a probability measure $\mu$ on a measurable space $E$, the one-sided shift
on $E^{\mathbb N}$ is ergodic under the product law $\mu^{\otimes\mathbb N}$.
The proof identifies an invariant event with a tail event and applies
Kolmogorov's zero-one law.

## Public declarations

- `ProbabilityTheory.iidSequenceShift_ergodic` states that
  $\theta(\omega)_n=\omega_{n+1}$ is ergodic under
  $\mu^{\otimes\mathbb N}$ for every probability measure $\mu$.
-/

@[expose] public section

open Filter MeasureTheory MeasurableSpace ProbabilityTheory

namespace ProbabilityTheory

variable {E : Type*} [MeasurableSpace E]

private def iidSequenceSuffix (n : ℕ) : (ℕ → E) → (ℕ → E) :=
  fun ω k => ω (k + n)

/-- The one-sided shift on an i.i.d. sequence is ergodic under its product law.
-/
theorem iidSequenceShift_ergodic
    (μ : Measure E) [IsProbabilityMeasure μ] :
    Ergodic (fun ω : ℕ → E => fun n => ω (n + 1))
      (Measure.infinitePi (fun _ : ℕ => μ)) := by
  let ν := Measure.infinitePi (fun _ : ℕ => μ)
  let s : ℕ → MeasurableSpace (ℕ → E) :=
    fun n => (inferInstance : MeasurableSpace E).comap (fun ω => ω n)
  have hIndep : iIndep s ν := by
    apply (iIndepFun_iff_iIndep
      (fun _ : ℕ => (inferInstance : MeasurableSpace E))
      (fun (n : ℕ) (ω : ℕ → E) => ω n) ν).mp
    exact iIndepFun_infinitePi (X := fun _ : ℕ => id)
      (fun _ => measurable_id)
  have hLe : ∀ n, s n ≤ (inferInstance : MeasurableSpace (ℕ → E)) := by
    intro n
    exact (measurable_pi_apply n).comap_le
  let shift : (ℕ → E) → (ℕ → E) := fun ω n => ω (n + 1)
  have hMeasurePreserving : MeasurePreserving shift ν ν := by
    refine ⟨?_, ?_⟩
    · rw [measurable_pi_iff]
      intro n
      exact measurable_pi_apply (n + 1)
    · rw [show shift = (fun ω n => ω (Nat.succ n)) by
          funext ω n
          rfl]
      dsimp [ν]
      exact Measure.map_infinitePi_infinitePi_of_inj
        (P := fun _ : ℕ => μ) Nat.succ_injective
  refine Ergodic.of_preimage_eq hMeasurePreserving ?_
  intro A hA hInvariant
  have hSuffixInvariant : ∀ n, iidSequenceSuffix n ⁻¹' A = A := by
    intro n
    induction n with
    | zero =>
        ext ω
        change (fun k : ℕ => ω (k + 0)) ∈ A ↔ ω ∈ A
        simp
    | succ n ih =>
        have hcomp : iidSequenceSuffix (n + 1) =
            fun ω => iidSequenceSuffix n (shift ω) := by
          funext ω k
          simp [iidSequenceSuffix, shift, Nat.add_assoc]
        calc
          iidSequenceSuffix (n + 1) ⁻¹' A =
              shift ⁻¹' (iidSequenceSuffix n ⁻¹' A) := by rw [hcomp]; rfl
          _ = A := by rw [ih, hInvariant]
  have hSuffixMeasurable : ∀ n,
    MeasurableSet[(inferInstance : MeasurableSpace (ℕ → E)).comap
        (iidSequenceSuffix n)] A := by
    intro n
    rw [MeasurableSpace.measurableSet_comap]
    exact ⟨A, hA, hSuffixInvariant n⟩
  have hSuffixSigma : ∀ n,
      MeasurableSet[⨆ k : ℕ, s (k + n)] A := by
    intro n
    have hcomap :
        (inferInstance : MeasurableSpace (ℕ → E)).comap
            (iidSequenceSuffix n) = ⨆ k : ℕ, s (k + n) := by
      change MeasurableSpace.comap
          (fun ω : ℕ → E => fun k : ℕ => ω (k + n)) inferInstance = _
      simpa only [s] using
        (MeasurableSpace.comap_process_pi
          (fun k : ℕ => fun ω : ℕ → E => ω (k + n)))
    rw [← hcomap]
    exact hSuffixMeasurable n
  have hTail : MeasurableSet[limsup s atTop] A := by
    rw [limsup_eq_iInf_iSup_of_nat']
    rw [MeasurableSpace.measurableSet_iInf]
    intro n
    exact hSuffixSigma n
  have hZeroOne := measure_zero_or_one_of_measurableSet_limsup_atTop hLe hIndep hTail
  rcases hZeroOne with hZero | hOne
  · rw [eventuallyEmptyOrUniv_iff']
    exact Or.inl (ae_eq_empty.mpr hZero)
  · rw [eventuallyEmptyOrUniv_iff']
    exact Or.inr (ae_eq_univ.mpr ((prob_compl_eq_zero_iff hA).2 hOne))

end ProbabilityTheory

end
