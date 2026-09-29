module

public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Kernel.Basic

/-!
# Markov kernels

Small closure results for mathlib's `Kernel` API.
-/

public section

open MeasureTheory

namespace ProbabilityTheory

variable {State : Type*} [MeasurableSpace State]

/-- Every iterate of a Markov transition kernel remains Markov. -/
instance IsMarkovKernel.pow (K : Kernel State State) [IsMarkovKernel K]
    (n : ℕ) : IsMarkovKernel (K ^ n) := by
  induction n with
  | zero =>
      simp only [pow_zero]
      refine ⟨fun a ↦ ?_⟩
      change IsProbabilityMeasure (Kernel.id a)
      rw [Kernel.id_apply]
      infer_instance
  | succ n ih =>
      rw [pow_succ]
      change IsMarkovKernel ((K ^ n) ∘ₖ K)
      infer_instance

end ProbabilityTheory

end
