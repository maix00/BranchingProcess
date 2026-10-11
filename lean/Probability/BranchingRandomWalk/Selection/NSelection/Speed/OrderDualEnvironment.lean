/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.Speed.Environment
public import Probability.BranchingRandomWalk.Assumptions.Structural
public import Combinatorics.BranchingWalk.Selection.NSelection.OrderDual
public import Combinatorics.BranchingWalk.Step.ExponentialWeight
public import Combinatorics.BranchingWalk.Step.Map

/-!
# The order-dual view of an offspring environment

The order-dual observation keeps every displacement value unchanged and
reverses only the spatial order. Its additive inverse potential turns the
right exponential weight of the original law into the left exponential
weight in the dual order. All assumptions in this file are stated on the
original offspring measure.
-/

open MeasureTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.Branching

/-- The real-valued potential that is increasing in the order-dual order. -/
def orderDualPotential : Potential (OrderDual ℝ) where
  toFun := fun x => -(OrderDual.ofDual x)
  measurable_toFun := by
    exact measurable_neg.comp measurable_id

/-- Observe a real displacement in the reversed order without changing its
underlying value. -/
def stepOrderDual (ξ : Step ℕ ℝ) : Step ℕ (OrderDual ℝ) :=
  ξ.map OrderDual.toDual

theorem measurable_stepOrderDual : Measurable stepOrderDual := by
  have hf : Measurable (OrderDual.toDual : ℝ → OrderDual ℝ) := measurable_id
  exact Step.map_measurable hf

@[simp] theorem survive_stepOrderDual_iff (ξ : Step ℕ ℝ) (i : ℕ) :
    survive (stepOrderDual ξ) i ↔ survive ξ i := by
  exact survive_map_iff OrderDual.toDual ξ i

theorem orderDualPotentialValue_stepOrderDual (ξ : Step ℕ ℝ) (i : ℕ) :
    (stepOrderDual ξ).potentialValue' orderDualPotential i =
      -(value' ξ i) := by
  cases h : ξ i <;>
    simp [stepOrderDual, orderDualPotential, Step.map,
      Step.potentialValue', Step.potentialAt?, value', h]

@[simp] theorem totalPotentialWeight_orderDual_stepOrderDual
    (ξ : Step ℕ ℝ) :
    totalPotentialWeight orderDualPotential (-1) (stepOrderDual ξ) =
      totalPotentialWeight realPotential 1 ξ := by
  unfold totalPotentialWeight
  apply tsum_congr
  intro i
  have hsurv := survive_stepOrderDual_iff ξ i
  by_cases hs : survive ξ i
  · have hs' : survive (stepOrderDual ξ) i := hsurv.mpr hs
    simp only [realizedPotentialWeight, hs, hs', ite_true]
    rw [orderDualPotentialValue_stepOrderDual]
    have hreal : Step.potentialValue' realPotential ξ i = value' ξ i := by
      simp [Step.potentialValue', Step.potentialAt?, realPotential, value']
    rw [hreal]
    change ENNReal.ofReal (Real.exp ((-1 : ℝ) * -(value' ξ i))) =
      ENNReal.ofReal (Real.exp ((1 : ℝ) * value' ξ i))
    exact congrArg (fun x : ℝ => ENNReal.ofReal (Real.exp x)) (by ring)
  · have hs' : ¬ survive (stepOrderDual ξ) i := fun h => hs (hsurv.mp h)
    simp [realizedPotentialWeight, hs, hs']

/-- The right boundary normalization is stated directly on the original
offspring law. -/
def HasRightBoundaryNormalization (μ : Measure (Step ℕ ℝ)) : Prop :=
  ∫⁻ ξ, totalPotentialWeight realPotential 1 ξ ∂μ = 1

theorem HasRightBoundaryNormalization.orderDual
    (μ : Measure (Step ℕ ℝ))
    (h : HasRightBoundaryNormalization μ) :
    HasBoundaryNormalization orderDualPotential (Measure.map stepOrderDual μ) := by
  change (∫⁻ ξ, totalPotentialWeight orderDualPotential (-1) ξ
    ∂Measure.map stepOrderDual μ) = 1
  rw [lintegral_map (totalPotentialWeight_measurable orderDualPotential (-1))
    measurable_stepOrderDual]
  calc
    (∫⁻ ξ, totalPotentialWeight orderDualPotential (-1)
        (stepOrderDual ξ) ∂μ) =
      ∫⁻ ξ, totalPotentialWeight realPotential 1 ξ ∂μ := by
        apply lintegral_congr
        intro ξ
        exact totalPotentialWeight_orderDual_stepOrderDual ξ
    _ = 1 := h

theorem mem_nonemptySupport_stepOrderDual_iff (ξ : Step ℕ ℝ) :
    stepOrderDual ξ ∈ nonemptySupport ↔ ξ ∈ nonemptySupport := by
  simp [nonemptySupport, stepOrderDual]

/-- Finiteness of the positive exponential weight makes every upper spatial
level contain only finitely many children. This is the dual-order analogue
of `finite_realized_children_potential_below`. -/
theorem finite_realized_children_potential_above
    (ξ : Step ℕ ℝ) (hweight : totalPotentialWeight realPotential 1 ξ ≠ ∞)
    (R : ℝ) :
    {i : ℕ | survive ξ i ∧ R ≤ value' ξ i}.Finite := by
  have hdualWeight :
      totalPotentialWeight orderDualPotential (-1) (stepOrderDual ξ) ≠ ∞ := by
    simpa only [totalPotentialWeight_orderDual_stepOrderDual] using hweight
  have hfinite := finite_realized_children_potential_below orderDualPotential
    (stepOrderDual ξ) hdualWeight (-R)
  rw [show {i : ℕ | survive ξ i ∧ R ≤ value' ξ i} =
      {i : ℕ | survive (stepOrderDual ξ) i ∧
        (stepOrderDual ξ).potentialValue' orderDualPotential i ≤ -R} from ?_]
  exact hfinite
  ext i
  constructor
  · rintro ⟨hsurvive, hbelow⟩
    refine ⟨?_, ?_⟩
    · exact (survive_stepOrderDual_iff ξ i).mpr hsurvive
    · have hvalue := orderDualPotentialValue_stepOrderDual ξ i
      rw [hvalue]
      linarith
  · rintro ⟨hsurvive, habove⟩
    refine ⟨?_, ?_⟩
    · exact (survive_stepOrderDual_iff ξ i).mp hsurvive
    · have hvalue := orderDualPotentialValue_stepOrderDual ξ i
      rw [hvalue] at habove
      linarith

/-- A generation batch observed in the dual order. -/
abbrev OrderDualGenerationBatch (N : ℕ) :=
  Fin N → Step ℕ (OrderDual ℝ)

def generationBatchOrderDual {N : ℕ} (batch : GenerationBatch N) :
    OrderDualGenerationBatch N :=
  fun i => stepOrderDual (batch i)

theorem measurable_generationBatchOrderDual {N : ℕ} :
    Measurable (generationBatchOrderDual (N := N)) := by
  rw [measurable_pi_iff]
  intro i
  exact measurable_stepOrderDual.comp (measurable_pi_apply i)

/-- The i.i.d. generation law after changing only the order observation. -/
noncomputable def orderDualGenerationBatchLaw
    (μ : Measure (Step ℕ ℝ)) (N : ℕ) :
    Measure (OrderDualGenerationBatch N) :=
  Measure.pi (fun _ : Fin N => Measure.map stepOrderDual μ)

theorem generationBatchLaw_orderDual_map
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ] (N : ℕ) :
    (generationBatchLaw μ N).map (generationBatchOrderDual (N := N)) =
      orderDualGenerationBatchLaw μ N := by
  classical
  unfold generationBatchLaw orderDualGenerationBatchLaw
  change (Measure.pi (fun _ : Fin N => μ)).map
      (fun batch i => stepOrderDual (batch i)) =
        Measure.pi (fun _ : Fin N => Measure.map stepOrderDual μ)
  rw [Measure.pi_map_pi
    (hf := fun _ => measurable_stepOrderDual.aemeasurable)]

abbrev OrderDualGenerationEnvironment (N : ℕ) :=
  ℕ → OrderDualGenerationBatch N

def generationEnvironmentOrderDual {N : ℕ}
    (ω : ℕ → GenerationBatch N) : OrderDualGenerationEnvironment N :=
  fun t => generationBatchOrderDual (ω t)

theorem measurable_generationEnvironmentOrderDual {N : ℕ} :
    Measurable (generationEnvironmentOrderDual (N := N)) := by
  rw [measurable_pi_iff]
  intro t
  exact measurable_generationBatchOrderDual.comp (measurable_pi_apply t)

noncomputable def orderDualGenerationEnvironmentLaw
    (μ : Measure (Step ℕ ℝ)) (N : ℕ) :
    Measure (OrderDualGenerationEnvironment N) :=
  Measure.infinitePi (fun _ : ℕ => orderDualGenerationBatchLaw μ N)

theorem generationEnvironmentLaw_orderDual_map
    (μ : Measure (Step ℕ ℝ)) [IsProbabilityMeasure μ] (N : ℕ) :
    (generationEnvironmentLaw μ N).map
        (generationEnvironmentOrderDual (N := N)) =
      orderDualGenerationEnvironmentLaw μ N := by
  unfold generationEnvironmentLaw orderDualGenerationEnvironmentLaw
  change (Measure.infinitePi (fun _ : ℕ => generationBatchLaw μ N)).map
      (fun ω t => generationBatchOrderDual (ω t)) =
        Measure.infinitePi (fun _ : ℕ => orderDualGenerationBatchLaw μ N)
  rw [Measure.infinitePi_map_pi
    (fun _ : ℕ => generationBatchLaw μ N)
    (fun _ => measurable_generationBatchOrderDual)]
  simp_rw [generationBatchLaw_orderDual_map]

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

end
