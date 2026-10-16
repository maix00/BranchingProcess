/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Kernel.Survival.Return

/-! # Finite sequences of return blocks

Compose return kernels with possibly different block lengths. This is the
kernel form of concatenating a finite partition whose blocks are not all the
same size.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {S : Type*} [MeasurableSpace S]

/-- The transition kernel obtained by running a finite list of return blocks
in order. The head block is run first. -/
@[expose] noncomputable def returnKernelSequence (K : Kernel S S)
    (returnSet : Set S) (hreturn : MeasurableSet returnSet) :
    List ℕ → Kernel returnSet returnSet
  | [] => Kernel.id
  | length :: lengths =>
      returnKernelSequence K returnSet hreturn lengths ∘ₖ
        returnKernel K returnSet hreturn length

/-- The total number of ambient steps in a finite list of block lengths. -/
@[expose] def returnKernelSequenceLength : List ℕ → ℕ
  | [] => 0
  | length :: lengths => length + returnKernelSequenceLength lengths

/-- The elapsed length of a return-kernel sequence is the sum of its block
lengths. -/
theorem returnKernelSequenceLength_eq_sum (lengths : List ℕ) :
    returnKernelSequenceLength lengths = lengths.sum := by
  induction lengths with
  | nil => rfl
  | cons length lengths ih => simp [returnKernelSequenceLength, ih]

/-- If each return block has mass at least `lowerBound` from every return
state, then a finite sequence of possibly different block lengths has the
product lower bound. -/
theorem pow_le_returnKernelSequence_apply_univ
    (K : Kernel S S) (returnSet : Set S) (hreturn : MeasurableSet returnSet)
    (lengths : List ℕ) (lowerBound : ℝ≥0∞)
    (hblock : ∀ length ∈ lengths, ∀ x : returnSet,
      lowerBound ≤ returnKernel K returnSet hreturn length x Set.univ) :
    ∀ x : returnSet,
      lowerBound ^ lengths.length ≤
        returnKernelSequence K returnSet hreturn lengths x Set.univ := by
  induction lengths with
  | nil =>
      intro x
      simp [returnKernelSequence]
  | cons length lengths ih =>
      intro x
      have htail : ∀ length' ∈ lengths, ∀ y : returnSet,
          lowerBound ≤ returnKernel K returnSet hreturn length' y Set.univ := by
        intro length' hmem y
        exact hblock length' (List.mem_cons_of_mem _ hmem) y
      have hhead := hblock length (List.mem_cons_self ..) x
      calc
        lowerBound ^ (lengths.length + 1) =
            lowerBound ^ lengths.length * lowerBound := by rw [pow_succ]
        _ ≤ lowerBound ^ lengths.length *
            returnKernel K returnSet hreturn length x Set.univ := by
          calc
            lowerBound ^ lengths.length * lowerBound =
                lowerBound * lowerBound ^ lengths.length := by ac_rfl
            _ ≤ returnKernel K returnSet hreturn length x Set.univ *
                lowerBound ^ lengths.length :=
              mul_le_mul_left hhead _
            _ = lowerBound ^ lengths.length *
                returnKernel K returnSet hreturn length x Set.univ := by ac_rfl
        _ = ∫⁻ _ : returnSet, lowerBound ^ lengths.length ∂
            returnKernel K returnSet hreturn length x := by
          rw [MeasureTheory.lintegral_const]
        _ ≤ ∫⁻ y, returnKernelSequence K returnSet hreturn lengths y Set.univ ∂
            returnKernel K returnSet hreturn length x := by
          apply lintegral_mono
          intro y
          exact ih htail y
        _ = (returnKernelSequence K returnSet hreturn (length :: lengths))
            x Set.univ := by
          rw [returnKernelSequence, Kernel.comp_apply' _ _ _ MeasurableSet.univ]

/-- Requiring returns after every block can only decrease the probability of
surviving the ambient kernel for the sum of their lengths. -/
theorem returnKernelSequence_apply_preimage_le
    (K : Kernel S S) [IsSubMarkovKernel K]
    (returnSet : Set S) (hreturn : MeasurableSet returnSet)
    (lengths : List ℕ) :
    ∀ x : returnSet, ∀ target : Set S, MeasurableSet target →
      returnKernelSequence K returnSet hreturn lengths x
          (Subtype.val ⁻¹' target) ≤
        (K ^ returnKernelSequenceLength lengths) (x : S) target := by
  induction lengths with
  | nil =>
      classical
      intro x target htarget
      simp only [returnKernelSequence, returnKernelSequenceLength]
      change Kernel.id x (Subtype.val ⁻¹' target) ≤ Kernel.id (x : S) target
      rw [Kernel.id_apply, Kernel.id_apply,
        Measure.dirac_apply' _ (htarget.preimage measurable_subtype_coe),
        Measure.dirac_apply' _ htarget]
      rfl
  | cons length lengths ih =>
      intro x target htarget
      have hpreimage : MeasurableSet
          ((fun y : returnSet => (y : S)) ⁻¹' target) :=
        htarget.preimage measurable_subtype_coe
      rw [returnKernelSequence, Kernel.comp_apply' _ _ _ hpreimage]
      calc
        (∫⁻ y, returnKernelSequence K returnSet hreturn lengths y
              (Subtype.val ⁻¹' target)
            ∂returnKernel K returnSet hreturn length x) ≤
            ∫⁻ y, (K ^ returnKernelSequenceLength lengths) (y : S) target
              ∂returnKernel K returnSet hreturn length x := by
          apply lintegral_mono
          intro y
          exact ih y target htarget
        _ = ∫⁻ z, (K ^ returnKernelSequenceLength lengths) z target ∂
            Measure.map Subtype.val
              (returnKernel K returnSet hreturn length x) := by
          rw [MeasureTheory.lintegral_map
            (Kernel.measurable_coe (K ^ returnKernelSequenceLength lengths)
              htarget) measurable_subtype_coe]
        _ ≤ ∫⁻ z, (K ^ returnKernelSequenceLength lengths) z target ∂
            (K ^ length) (x : S) := by
          apply lintegral_mono'
          · apply Measure.le_iff.2
            intro measurableTarget hmeasurableTarget
            have hpreimageTarget : MeasurableSet
                ((fun y : returnSet => (y : S)) ⁻¹' measurableTarget) :=
              hmeasurableTarget.preimage measurable_subtype_coe
            rw [Measure.map_apply measurable_subtype_coe hmeasurableTarget,
              returnKernel_apply K returnSet hreturn length x _ hpreimageTarget]
            exact measure_mono (by
              rintro z ⟨y, hy, rfl⟩
              exact hy)
          · exact le_rfl
        _ = (K ^ (length + returnKernelSequenceLength lengths))
            (x : S) target := by
          symm
          exact Kernel.pow_add_apply_eq_lintegral
            K length (returnKernelSequenceLength lengths) (x : S) htarget

/-- Total survival mass after a sequence of variable-length return blocks is
bounded by survival for the same total number of steps. -/
theorem remainingMass_returnKernelSequence_le
    (K : Kernel S S) [IsSubMarkovKernel K]
    (returnSet : Set S) (hreturn : MeasurableSet returnSet)
    (lengths : List ℕ) (x : returnSet) :
    remainingMass (returnKernelSequence K returnSet hreturn lengths)
        1 x ≤
      remainingMass K (returnKernelSequenceLength lengths) (x : S) := by
  unfold remainingMass
  simpa using returnKernelSequence_apply_preimage_le
    K returnSet hreturn lengths x Set.univ MeasurableSet.univ

end ProbabilityTheory.Kernel

end
