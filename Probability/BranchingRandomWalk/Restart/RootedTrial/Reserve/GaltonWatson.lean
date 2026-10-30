/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Restart.Success.GoodSplit
public import Probability.BranchingRandomWalk.Restart.RootedTrial.FiniteSlot.Offspring
public import Probability.BranchingProcess.GaltonWatson.BoundedGrowth

/-!
# Galton--Watson growth for the reserve selection

The reserve selector is obtained by keeping the first two children in slot
order and retaining the second child only below a potential cutoff. Its
selected-child law is encoded by the generic finite-slot construction.

## Public declarations

- `reserveFiniteOffspringLaw L M` is the two-slot unmarked law of this reserve
  selector at cutoff $M$.
- `exists_reserveFiniteOffspring_growth_bound` states that nonempty and
  supercritical original offspring assumptions give a cutoff $M$ for which,
  uniformly for $N\geq1$ and $a\in\mathbb R$, the reserve-law generation size
  reaches $\lfloor N^a\rfloor_+$ by
  $h=\left\lceil\frac{a\log N+\log 2}{\log\rho}\right\rceil_+$ with
  probability at least
  $\left[4\left(1+\frac{\kappa}{\rho(\rho-1)}\right)\right]^{-1}$,
  where $\rho$ and $\kappa$ are the offspring mean and second factorial
  moment of the reserve law.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.Branching ProbabilityTheory.BranchingProcess
  ProbabilityTheory.BranchingProcess.GaltonWatson
open Combinatorics.Branching.Step.FiniteSelection

/-- The nonempty and supercritical offspring assumptions produce a
finite-slot supercritical Galton--Watson law from the bounded reserve rule.
This theorem applies the finite-slot growth estimate to that law at every
target scale. -/
noncomputable def reserveFiniteOffspringLaw
    {ι α X : Type*} [MeasurableSpace X] [Countable ι]
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (L : StepLaw ι α X) [IsProbabilityMeasure L.raw] (M : ℕ) :
    OffspringConfigurationLaw (Fin 2) PUnit.{1} := by
  let R : Step.FiniteSelection α X :=
    Step.FiniteSelection.firstNBySlotOrder (α := α) (X := X) 2
  have hRmeas : Measurable R.select := by
    simpa [R] using firstTwoBySlotOrder_measurable (α := α) (X := X)
  let S : Step.FiniteSelection α X :=
    reserveSelectionBelowPotential R L.potential (M : ℝ)
  have hSmeas : Measurable S.select := by
    simpa [S] using reserveSelectionBelowPotential_measurable
      R hRmeas L.potential (M : ℝ)
  let ν : ProbabilityMeasure (Step α X) := ⟨L.sorted, inferInstance⟩
  exact finiteOffspringLaw ν S hSmeas

theorem exists_reserveFiniteOffspring_growth_bound
    {ι α X : Type*} [MeasurableSpace X] [Countable ι]
    [Countable α] [MeasurableSpace α] [MeasurableSingletonClass α]
    [LinearOrder α] [LocallyFiniteOrder α] [OrderBot α] [NoMaxOrder α]
    (L : StepLaw ι α X) [IsProbabilityMeasure L.raw]
    (hnonempty : OffspringConfigurationLaw.HasAtLeastOneChild
      (⟨L.raw, ‹IsProbabilityMeasure L.raw›⟩ : OffspringConfigurationLaw ι X))
    (hsupercritical : OffspringConfigurationLaw.IsSupercritical
      (⟨L.raw, ‹IsProbabilityMeasure L.raw›⟩ : OffspringConfigurationLaw ι X)) :
    ∃ M : ℕ, ∀ N : ℕ, ∀ a : ℝ, 1 ≤ N →
      ((GaltonWatson.law (reserveFiniteOffspringLaw L M) :
        ProbabilityMeasure (Combinatorics.Branching.Process (Fin 2))).toMeasure.real
        {β | (⌊(N : ℝ) ^ a⌋₊ : ℝ) ≤
          generationSizeReal
            ⌈(a * Real.log N + Real.log 2) /
              Real.log ((offspringMean
                (reserveFiniteOffspringLaw L M)).toReal)⌉₊ β}) ≥
        1 / (4 * (1 +
          (offspringSecondFactorialMoment
            (reserveFiniteOffspringLaw L M)).toReal /
            ((offspringMean (reserveFiniteOffspringLaw L M)).toReal *
              ((offspringMean (reserveFiniteOffspringLaw L M)).toReal - 1)))) := by
  obtain ⟨M, hsplit, _hmeas⟩ :=
    exists_nat_cutoff_positive_reserveSplit L hsupercritical
  let R : Step.FiniteSelection α X :=
    Step.FiniteSelection.firstNBySlotOrder (α := α) (X := X) 2
  let S : Step.FiniteSelection α X :=
    reserveSelectionBelowPotential R L.potential (M : ℝ)
  let ν : ProbabilityMeasure (Step α X) := ⟨L.sorted, inferInstance⟩
  have hRmeas : Measurable R.select := by
    simpa [R] using firstTwoBySlotOrder_measurable (α := α) (X := X)
  have hRcap : R.IsBoundedBy 2 := by
    simpa [R] using
      (Step.FiniteSelection.firstNBySlotOrder_isBoundedBy
        (α := α) (X := X) 2)
  have hSmeas : Measurable S.select := by
    simpa [S] using reserveSelectionBelowPotential_measurable
      R hRmeas L.potential (M : ℝ)
  let μ : OffspringConfigurationLaw (Fin 2) PUnit.{1} :=
    finiteOffspringLaw ν S hSmeas
  have hScap : ∀ ξ, (S ξ).card ≤ 2 := by
    intro ξ
    exact reserveSelectionBelowPotential_isBoundedBy
      R L.potential (M : ℝ) hRcap ξ
  have hSnonempty : ∀ᵐ ξ ∂(ν : Measure (Step α X)), (S ξ).Nonempty := by
    simpa [ν, S] using reserveSelectionBelowPotential_nonempty_ae
      L hnonempty (M : ℝ)
  have hSsplit :
      0 < (ν : Measure (Step α X)) {ξ | 2 ≤ (S ξ).card} := by
    simpa [ν, S, splitBy] using hsplit
  have hμsupercritical : μ.IsSupercritical :=
    finiteOffspringLaw_isSupercritical ν S hSmeas hScap
      hSnonempty hSsplit
  refine ⟨M, ?_⟩
  intro N a hN
  have hμ : μ = reserveFiniteOffspringLaw L M := by
    simp [μ, reserveFiniteOffspringLaw, R, S, ν]
  rw [← hμ]
  exact GaltonWatson.measure_generation_ge_floor_rpow_of_supercritical_finite_slots
    μ hμsupercritical N a hN

end ProbabilityTheory.BranchingRandomWalk

end
