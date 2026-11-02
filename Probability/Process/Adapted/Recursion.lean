/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Process.Adapted

/-!
# Adapted causal recursions

## Public declarations

- `ProbabilityTheory.causal_recursion_adapted` states that a recursively
  updated state remains adapted. If `state 0` is measurable with respect to
  `F 0`, each `marks n` is measurable with respect to `F (n + 1)`, `step` is
  measurable, and
  `state (n + 1) ω = step (state n ω, marks n ω)`, then
  $\forall n,\quad \texttt{Measurable}[F_n](\texttt{state}_n)$.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- A state recursion driven by marks visible in the next filtration step is
adapted. -/
theorem causal_recursion_adapted {State M : Type*}
    [MeasurableSpace State] [MeasurableSpace M]
    (F : Filtration ℕ m) (state : ℕ → Ω → State)
    (marks : ℕ → Ω → M) (step : State × M → State)
    (hstep : Measurable step)
    (hzero : Measurable[F 0] (state 0))
    (hmarks : ∀ n, Measurable[F (n + 1)] (marks n))
    (hrec : ∀ n ω, state (n + 1) ω = step (state n ω, marks n ω)) :
    ∀ n, Measurable[F n] (state n) := by
  intro n
  induction n with
  | zero => exact hzero
  | succ n ih =>
      have hold : Measurable[F (n + 1)] (state n) :=
        ih.mono (F.mono (Nat.le_succ n)) le_rfl
      have hpair : Measurable[F (n + 1)]
          (fun ω => (state n ω, marks n ω)) :=
        hold.prodMk (hmarks n)
      convert hstep.comp hpair using 1
      funext ω
      exact hrec n ω

end ProbabilityTheory

end
