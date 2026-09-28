import Probability.Kernel.Step

/-!
# Paths of partial random steps

These definitions are independent of finiteness, countability, and any
particular noise law.  They record how an option-valued step consumes a finite
noise history and whether that history survives.
-/

open MeasureTheory Set

namespace ProbabilityTheory.Kernel

variable {α ξ : Type*}

/-- Endpoint obtained by consuming a finite noise history, or `none` when one
of its partial steps is killed. -/
def runPartialSteps (step : α → ξ → Option α) :
    (n : ℕ) → α → (Fin n → ξ) → Option α
  | 0, a, _ => some a
  | n + 1, a, history =>
      (step a (history 0)).bind fun b =>
        runPartialSteps step n b (Fin.tail history)

/-- A finite noise history survives every partial step. -/
def Survives (step : α → ξ → Option α) (n : ℕ)
    (a : α) (history : Fin n → ξ) : Prop :=
  (runPartialSteps step n a history).isSome

@[simp] theorem survives_zero (step : α → ξ → Option α) (a : α)
    (history : Fin 0 → ξ) : Survives step 0 a history := by
  simp [Survives, runPartialSteps]

/-- Restriction of an infinite noise sequence to its first `n` coordinates. -/
def sequencePrefix (n : ℕ) (sequence : ℕ → ξ) : Fin n → ξ :=
  fun k => sequence k

theorem sequencePrefix_measurable [MeasurableSpace ξ] (n : ℕ) :
    Measurable (sequencePrefix (ξ := ξ) n) := by
  rw [measurable_pi_iff]
  exact fun k => measurable_pi_apply (k : ℕ)

/-- An infinite noise sequence survives its first `n` partial steps. -/
def SurvivesPrefix (step : α → ξ → Option α) (n : ℕ)
    (a : α) (sequence : ℕ → ξ) : Prop :=
  Survives step n a (sequencePrefix n sequence)

/-- Executing a finite partial-step history is jointly measurable in the
initial state and the history. -/
theorem runPartialSteps_measurable [MeasurableSpace α] [MeasurableSpace ξ]
    [Nonempty α] (step : α → ξ → Option α)
    (hstep : Measurable (Function.uncurry step)) (n : ℕ) :
    Measurable (fun p : α × (Fin n → ξ) =>
      runPartialSteps step n p.1 p.2) := by
  induction n with
  | zero =>
      change Measurable (some ∘ (Prod.fst : α × (Fin 0 → ξ) → α))
      exact measurable_option_some.comp measurable_fst
  | succ n ih =>
      let default : α := Classical.choice ‹Nonempty α›
      have hfirst : Measurable
          (fun p : α × (Fin (n + 1) → ξ) => step p.1 (p.2 0)) :=
        hstep.comp (measurable_fst.prodMk
          ((measurable_pi_apply (0 : Fin (n + 1))).comp measurable_snd))
      have htail : Measurable
          (fun history : Fin (n + 1) → ξ => Fin.tail history) := by
        rw [measurable_pi_iff]
        exact fun k => measurable_pi_apply k.succ
      have hrest : Measurable
          (fun p : α × (Fin (n + 1) → ξ) =>
            runPartialSteps step n
              ((step p.1 (p.2 0)).getD default) (Fin.tail p.2)) :=
        ih.comp (((measurable_optionGetD default).comp hfirst).prodMk
          (htail.comp measurable_snd))
      rw [show (fun p : α × (Fin (n + 1) → ξ) =>
          runPartialSteps step (n + 1) p.1 p.2) =
          fun p => if (step p.1 (p.2 0)).isSome then
            runPartialSteps step n
              ((step p.1 (p.2 0)).getD default) (Fin.tail p.2)
          else none by
        funext p
        simp only [runPartialSteps]
        cases step p.1 (p.2 0) <;> simp]
      exact hrest.ite
        (measurableSet_option_isSome.preimage hfirst) measurable_const

/-- Survival of a fixed initial state is a measurable finite-history event. -/
theorem measurableSet_survives [MeasurableSpace α] [MeasurableSpace ξ]
    (step : α → ξ → Option α)
    (hstep : Measurable (Function.uncurry step)) (n : ℕ) (a : α) :
    MeasurableSet {history : Fin n → ξ | Survives step n a history} := by
  let _ : Nonempty α := ⟨a⟩
  exact measurableSet_option_isSome.preimage
    ((runPartialSteps_measurable step hstep n).comp
      (measurable_const.prodMk measurable_id))

/-- Prefix survival is measurable on the canonical infinite noise space. -/
theorem measurableSet_survivesPrefix
    [MeasurableSpace α] [MeasurableSpace ξ]
    (step : α → ξ → Option α)
    (hstep : Measurable (Function.uncurry step)) (n : ℕ) (a : α) :
    MeasurableSet {sequence : ℕ → ξ | SurvivesPrefix step n a sequence} :=
  (measurableSet_survives step hstep n a).preimage
    (sequencePrefix_measurable n)

end ProbabilityTheory.Kernel
