import Mathlib.Probability.Martingale.Basic
import Probability.Kernel.Markov

/-!
# Markov processes

This file states the Markov property for a process in the standard
`Time → Ω → State` order.  The transition law is expressed through mathlib's
`Kernel`; conditional probabilities are expressed through conditional
expectations of indicators.  This avoids introducing a second notion of
transition kernel.
-/

open Filter MeasureTheory
open scoped ENNReal ProbabilityTheory

namespace ProbabilityTheory

variable {Time Omega State : Type*} [Preorder Time]
  [MeasurableSpace Omega] [MeasurableSpace State]

/-- A process is Markov with transition kernels `transition s t` when it is
adapted and, conditionally on the information at time `s`, the law at every
later time `t` is `transition s t` started from the current state.

The definition is meaningful for discrete and continuous time.  Compatibility
of the supplied two-time kernels, such as Chapman--Kolmogorov, is kept as a
separate property of the transition family. -/
def IsMarkovProcess (X : Time → Omega → State)
    (F : Filtration Time (inferInstance : MeasurableSpace Omega))
    (P : Measure Omega) (transition : Time → Time → Kernel State State)
    [∀ s t, IsMarkovKernel (transition s t)] : Prop :=
  Adapted F X ∧
    (∀ s t, s ≤ t → ∀ A, MeasurableSet A →
      condExp (F s) P (Set.indicator (X t ⁻¹' A) fun _ ↦ (1 : ℝ)) =ᵐ[P]
        fun omega ↦ (transition s t (X s omega) A).toReal)

namespace IsMarkovProcess

variable {X : Time → Omega → State}
  {F : Filtration Time (inferInstance : MeasurableSpace Omega)}
  {P : Measure Omega} {transition : Time → Time → Kernel State State}
  [∀ s t, IsMarkovKernel (transition s t)]

theorem adapted (h : IsMarkovProcess X F P transition) : Adapted F X :=
  h.1

theorem condExp_preimage_ae_eq (h : IsMarkovProcess X F P transition)
    {s t : Time} (hst : s ≤ t) {A : Set State} (hA : MeasurableSet A) :
    condExp (F s) P (Set.indicator (X t ⁻¹' A) fun _ ↦ (1 : ℝ)) =ᵐ[P]
      fun omega ↦ (transition s t (X s omega) A).toReal :=
  h.2 s t hst A hA

end IsMarkovProcess

/-- A time-homogeneous discrete-time Markov process.  Its transition from
time `m` to time `n` is the `(n - m)`-th power of one kernel. -/
def IsMarkovChain (X : ℕ → Omega → State)
    (F : Filtration ℕ (inferInstance : MeasurableSpace Omega))
    (P : Measure Omega) (K : Kernel State State) [IsMarkovKernel K] : Prop :=
  IsMarkovProcess X F P (fun m n ↦ K ^ (n - m))

namespace IsMarkovChain

variable {X : ℕ → Omega → State}
  {F : Filtration ℕ (inferInstance : MeasurableSpace Omega)}
  {P : Measure Omega} {K : Kernel State State} [IsMarkovKernel K]

theorem isMarkovProcess (h : IsMarkovChain X F P K) :
    IsMarkovProcess X F P (fun m n ↦ K ^ (n - m)) :=
  h

theorem adapted (h : IsMarkovChain X F P K) : Adapted F X :=
  h.1

theorem condExp_preimage_ae_eq (h : IsMarkovChain X F P K)
    {m n : ℕ} (hmn : m ≤ n) {A : Set State} (hA : MeasurableSet A) :
    condExp (F m) P (Set.indicator (X n ⁻¹' A) fun _ ↦ (1 : ℝ)) =ᵐ[P]
      fun omega ↦ ((K ^ (n - m)) (X m omega) A).toReal :=
  h.2 m n hmn A hA

end IsMarkovChain

end ProbabilityTheory
