/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Environment.Basic
public import Mathlib.Dynamics.Ergodic.Ergodic
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Probability.Independence.ZeroOne

/-!
# Ergodicity of the generation environment

The one-sided shift on the pre-sampled i.i.d. generation environment is
ergodic. The proof identifies every invariant event with a tail event and
applies Kolmogorov's zero-one law.
-/

@[expose] public section

open Filter MeasureTheory MeasurableSpace ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection

abbrev GenerationEnvironment (N : ℕ) := ℕ → GenerationBatch N

private def generationSuffix {N : ℕ} (n : ℕ) :
    GenerationEnvironment N → GenerationEnvironment N :=
  fun ω k => ω (k + n)

@[instance_reducible] def generationCoordinateSigma {N : ℕ}
    (n : ℕ) : MeasurableSpace (GenerationEnvironment N) :=
  (inferInstance : MeasurableSpace (GenerationBatch N)).comap (fun ω => ω n)

/-- The shift of the i.i.d. generation environment is ergodic. -/
theorem generationEnvironmentShift_ergodic
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ] (N : ℕ) :
    Ergodic (generationEnvironmentShift : GenerationEnvironment N →
      GenerationEnvironment N) (generationEnvironmentLaw μ N) := by
  let ν := generationEnvironmentLaw μ N
  haveI : IsProbabilityMeasure ν := generationEnvironmentLaw_isProbability μ N
  let s : ℕ → MeasurableSpace (GenerationEnvironment N) :=
    generationCoordinateSigma
  have hIndep : iIndep s ν := by
    apply (iIndepFun_iff_iIndep
      (fun _ : ℕ => (inferInstance : MeasurableSpace (GenerationBatch N)))
      (fun (n : ℕ) (ω : GenerationEnvironment N) => ω n) ν).mp
    exact generationEnvironmentLaw_generations_independent μ N
  have hLe : ∀ n, s n ≤ (inferInstance : MeasurableSpace (GenerationEnvironment N)) := by
    intro n
    exact (measurable_pi_apply n).comap_le
  have hMeasurePreserving := generationEnvironmentLaw_shift_measurePreserving μ N
  refine Ergodic.of_preimage_eq hMeasurePreserving ?_
  intro A hA hInvariant
  have hSuffixInvariant : ∀ n, generationSuffix n ⁻¹' A = A := by
    intro n
    induction n with
    | zero =>
        ext ω
        change (fun k : ℕ => ω (k + 0)) ∈ A ↔ ω ∈ A
        simp
    | succ n ih =>
        have hcomp : generationSuffix (N := N) (n + 1) =
            fun ω => generationSuffix (N := N) n
              (generationEnvironmentShift (N := N) ω) := by
          funext ω k
          simp [generationSuffix, generationEnvironmentShift, Nat.add_assoc]
        calc
          generationSuffix (N := N) (n + 1) ⁻¹' A =
              generationEnvironmentShift ⁻¹'
                (generationSuffix n ⁻¹' A) := by rw [hcomp]; rfl
          _ = A := by rw [ih, hInvariant]
  have hSuffixMeasurable : ∀ n,
    MeasurableSet[(inferInstance : MeasurableSpace (GenerationEnvironment N)).comap
        (generationSuffix n)] A := by
    intro n
    rw [MeasurableSpace.measurableSet_comap]
    exact ⟨A, hA, hSuffixInvariant n⟩
  have hSuffixSigma : ∀ n,
      MeasurableSet[⨆ k : ℕ, s (k + n)] A := by
    intro n
    have hcomap :
        (inferInstance : MeasurableSpace (GenerationEnvironment N)).comap
            (generationSuffix n) = ⨆ k : ℕ, s (k + n) := by
      change MeasurableSpace.comap
          (fun ω : GenerationEnvironment N => fun k : ℕ => ω (k + n)) inferInstance = _
      simpa only [s, generationCoordinateSigma] using
        (MeasurableSpace.comap_process_pi
          (fun k : ℕ => fun ω : GenerationEnvironment N => ω (k + n)))
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

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

end
