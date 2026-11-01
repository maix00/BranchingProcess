/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Kernel.Bridge
public import Probability.Kernel.Survival.Return.VariableBlocks

/-!
# Finite return sequences with a final bridge

## Public declarations

- `returnKernelSequenceExit`
  composes a finite sequence of returns to `core` with a final bridge to
  `target`. If every return block has mass at least `p` on `core`, and the
  exit block has mass at least `q` from every core state, then
  `mul_pow_le_returnKernelSequenceExit_apply_univ` gives the lower bound
  `p ^ lengths.length * q` for the composed kernel.
- For a sub-Markov kernel, `returnKernelSequenceExit_apply_univ_le` bounds the
  mass of this constrained sequence by the unrestricted transition mass
  `(K ^ (returnKernelSequenceLength lengths + exitLength))(x, target)`.

The general bridge kernel is defined in `Probability/Kernel/Bridge.lean`.
This module specializes it to a finite sequence of returns through one
measurable core followed by a transition to a possibly different terminal set.

If every return block has mass at least `p` on `core`, and the last bridge
has mass at least `q` on `target`, then for every `x : core`,

\[
p^{\mathrm{lengths.length}}q
\le \operatorname{returnKernelSequenceExit}(K,core,lengths,target,exitLength)(x,\mathrm{univ})
\le (K^{\mathrm{returnKernelSequenceLength}(lengths)+exitLength})(x,target),
\]

where the upper bound assumes that `K` is sub-Markov. The right-hand side is
the unrestricted transition mass over the total number of steps.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {S : Type*} [MeasurableSpace S]

/-- Compose a finite sequence of returns to a core with one final transition
to a possibly different target core. -/
@[expose] noncomputable def returnKernelSequenceExit
    (K : Kernel S S) (core : Set S) (hcore : MeasurableSet core)
    (lengths : List ℕ) (target : Set S) (htarget : MeasurableSet target)
    (exitLength : ℕ) : Kernel core target :=
  bridgeKernel K core target htarget exitLength ∘ₖ
    returnKernelSequence K core hcore lengths

/-- If every return block has mass at least `p` and the final bridge has mass
at least `q` from every core state, the composed sequence has mass at least
`p ^ numberOfReturns * q`. -/
theorem mul_pow_le_returnKernelSequenceExit_apply_univ
    (K : Kernel S S) (core : Set S) (hcore : MeasurableSet core)
    (lengths : List ℕ) (p q : ℝ≥0∞)
    (hblock : ∀ length ∈ lengths, ∀ x : core,
      p ≤ returnKernel K core hcore length x Set.univ)
    (target : Set S) (htarget : MeasurableSet target) (exitLength : ℕ)
    (hexit : ∀ x : core,
      q ≤ bridgeKernel K core target htarget exitLength x Set.univ) :
    ∀ x : core,
      p ^ lengths.length * q ≤
        returnKernelSequenceExit K core hcore lengths target htarget exitLength
          x Set.univ := by
  have hsequence := pow_le_returnKernelSequence_apply_univ
    K core hcore lengths p hblock
  intro x
  rw [returnKernelSequenceExit,
    Kernel.comp_apply' _ _ _ MeasurableSet.univ]
  calc
    p ^ lengths.length * q = q * p ^ lengths.length := by ac_rfl
    _ ≤ q * returnKernelSequence K core hcore lengths x Set.univ := by
      gcongr
      exact hsequence x
    _ = returnKernelSequence K core hcore lengths x Set.univ * q := by ac_rfl
    _ = ∫⁻ _ : core, q ∂returnKernelSequence K core hcore lengths x := by
      rw [MeasureTheory.lintegral_const]
      exact mul_comm _ _
    _ ≤ ∫⁻ y, bridgeKernel K core target htarget exitLength y Set.univ ∂
        returnKernelSequence K core hcore lengths x := by
      apply lintegral_mono
      intro y
      exact hexit y

/-- Requiring each intermediate block endpoint to return to `core`, and the
last block endpoint to lie in `target`, can only decrease the ambient
transition mass over the sum of all block lengths. -/
theorem returnKernelSequenceExit_apply_univ_le
    (K : Kernel S S) [IsSubMarkovKernel K]
    (core target : Set S) (hcore : MeasurableSet core)
    (htarget : MeasurableSet target) (lengths : List ℕ)
    (exitLength : ℕ) :
    ∀ x : core,
      returnKernelSequenceExit K core hcore lengths target htarget exitLength
          x Set.univ ≤
        (K ^ (returnKernelSequenceLength lengths + exitLength))
          (x : S) target := by
  have hmap (x : core) :
      Measure.map Subtype.val (returnKernelSequence K core hcore lengths x) ≤
        (K ^ returnKernelSequenceLength lengths) (x : S) := by
    apply Measure.le_iff.2
    intro measurableTarget hmeasurableTarget
    rw [Measure.map_apply measurable_subtype_coe hmeasurableTarget]
    exact returnKernelSequence_apply_preimage_le K core hcore lengths x
      measurableTarget hmeasurableTarget
  intro x
  rw [returnKernelSequenceExit,
    Kernel.comp_apply' _ _ _ MeasurableSet.univ]
  calc
    (∫⁻ y, bridgeKernel K core target htarget exitLength y Set.univ ∂
        returnKernelSequence K core hcore lengths x) =
      ∫⁻ z, (K ^ exitLength) z target ∂
        Measure.map Subtype.val
          (returnKernelSequence K core hcore lengths x) := by
        calc
          _ = ∫⁻ y, (K ^ exitLength) (y : S) target ∂
                returnKernelSequence K core hcore lengths x := by
              apply lintegral_congr
              intro y
              exact bridgeKernel_apply_univ K core target htarget exitLength y
          _ = _ := by
              rw [MeasureTheory.lintegral_map
                (Kernel.measurable_coe (K ^ exitLength) htarget)
                measurable_subtype_coe]
    _ ≤ ∫⁻ z, (K ^ exitLength) z target ∂
        (K ^ returnKernelSequenceLength lengths) (x : S) := by
      apply lintegral_mono'
      · exact hmap x
      · exact le_rfl
    _ = (K ^ (returnKernelSequenceLength lengths + exitLength))
        (x : S) target := by
      symm
      exact Kernel.pow_add_apply_eq_lintegral K
        (returnKernelSequenceLength lengths) exitLength (x : S) htarget

end ProbabilityTheory.Kernel

end
