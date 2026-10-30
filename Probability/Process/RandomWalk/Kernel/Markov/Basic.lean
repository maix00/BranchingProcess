/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.Kernel.Basic
public import Probability.Process.RandomWalk.Path.Adapted.Filtration
public import Probability.Independence.ConditionalIntegral
public import Probability.Process.Markov.Basic

import all Probability.Process.RandomWalk.Kernel.Markov.Lemmas.PrefixDecomposition

/-!
# Markov property of the canonical random walk

## Public declarations

`iidSequenceLaw_isMarkovChain` states that the position process
$X_n=x+\sum_{j<n}\xi_j$, under the IID sequence law, is Markov with respect
to the prefix domain flow $\mathcal F_n=\sigma(\xi_0,\ldots,\xi_{n-1})$ and
transition kernel $Q_\nu(x,\cdot)=\nu\circ(z\mapsto x+z)^{-1}$. For
$m\le n$ and every measurable set $A$, its conditional-expectation identity is
\[
  \mathbb E\!\left[\mathbf 1_{\{X_n\in A\}}\mid\mathcal F_m\right]
    =(Q_\nu^{\,n-m})(X_m,A)\quad\text{almost surely},
\]
where the one-step kernel is given by
\[
  Q_\nu(x,A)=\int \mathbf 1_A(x+z)\,\nu(dz).
\]
-/

@[expose] public section

open Filter MeasureTheory
open scoped BigOperators MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.RandomWalk


variable {E : Type*} [MeasurableSpace E] [AddCommMonoid E]
  [MeasurableAdd₂ E] [StandardBorelSpace E]

/-- The canonical IID additive walk is a homogeneous Markov chain on every
standard Borel additive state space.  No countability assumption on the
state space is used. -/
theorem iidSequenceLaw_isMarkovChain
    (nu : Measure E) [IsProbabilityMeasure nu] (initial : E) :
    IsMarkovChain (positionProcess initial) (sequencePrefixFiltration (E := E))
      (iidSequenceLaw nu) (incrementKernel nu) := by
  classical
  refine ⟨positionProcess_adapted initial, ?_⟩
  intro m n hmn A hA
  let length := n - m
  let past := Combinatorics.Sequence.blockCoordinates 0 (E := E) m
  let future := AdditivePath.blockSum (E := E) m length
  let endpoint : (Fin m → E) × E → E :=
    fun p ↦ positionFromPrefix initial p.1 + p.2
  let event : Set ((Fin m → E) × E) := endpoint ⁻¹' A
  let indicator : ((Fin m → E) × E) → ℝ := event.indicator 1
  have hpast : Measurable past := measurable_blockCoordinates 0 m
  have hfuture : Measurable future := blockSum_measurable m length
  have hendpoint : Measurable endpoint :=
    ((positionFromPrefix_measurable initial m).comp measurable_fst).add measurable_snd
  have hevent : MeasurableSet event := hA.preimage hendpoint
  have hindicator : StronglyMeasurable indicator :=
    stronglyMeasurable_const.indicator hevent
  have hintegrable : Integrable
      (fun increment ↦ indicator (past increment, future increment))
      (iidSequenceLaw nu) := by
    exact (integrable_const (c := (1 : ℝ))).indicator
      (hevent.preimage (hpast.prodMk hfuture))
  have hindep := indepFun_sequencePrefix_blockSum nu m length
  have hcond := hindep.condExp_prod_ae_eq_integral_map
    hpast hfuture hindicator hintegrable
  rw [sequencePrefixFiltration_eq_comap_blockCoordinates]
  have hevent_eq :
      (fun increment ↦ indicator (past increment, future increment)) =
        Set.indicator ((positionProcess initial n) ⁻¹' A) (fun _ ↦ (1 : ℝ)) := by
    funext increment
    unfold indicator event endpoint past future
    have hvalue := positionProcess_eq_prefix_add_blockSum
      initial hmn increment
    change (if positionFromPrefix initial (Combinatorics.Sequence.blockCoordinates 0 m increment) +
        AdditivePath.blockSum m (n - m) increment ∈ A then 1 else 0) =
      if positionProcess initial n increment ∈ A then 1 else 0
    rw [← hvalue]
  rw [hevent_eq] at hcond
  filter_upwards [hcond] with increment hincrement
  rw [hincrement]
  have htranslated : MeasurableSet
      ((fun y ↦ positionProcess initial m increment + y) ⁻¹' A) :=
    hA.preimage (measurable_const_add _)
  rw [show (fun y ↦ indicator (past increment, y)) =
      Set.indicator
        ((fun y ↦ positionProcess initial m increment + y) ⁻¹' A)
        (fun _ ↦ (1 : ℝ)) by
    funext y
    unfold indicator event endpoint past
    have hvalue := positionFromPrefix_blockCoordinates_zero initial m increment
    change (if positionFromPrefix initial (Combinatorics.Sequence.blockCoordinates 0 m increment) + y ∈ A
      then 1 else 0) =
      if positionProcess initial m increment + y ∈ A then 1 else 0
    rw [hvalue]]
  change (∫ y, Set.indicator
      ((fun y ↦ positionProcess initial m increment + y) ⁻¹' A)
        (fun _ ↦ (1 : ℝ)) y ∂(iidSequenceLaw nu).map future) = _
  rw [show (fun _ : E ↦ (1 : ℝ)) = 1 by rfl]
  rw [integral_indicator_one htranslated]
  have hlaw : (iidSequenceLaw nu).map future = nu.convPower length := by
    rw [iidSequenceLaw_map_blockSum, iidSequenceLaw_map_displacement]
  have hkernel :
      (incrementKernel nu ^ length) (positionProcess initial m increment) =
        ((iidSequenceLaw nu).map future).map
          (fun y ↦ positionProcess initial m increment + y) := by
    rw [incrementKernel_pow_apply, hlaw, Measure.dirac_conv]
  change ((iidSequenceLaw nu).map future
      ((fun y ↦ positionProcess initial m increment + y) ⁻¹' A)).toReal =
    (((incrementKernel nu ^ length)
      (positionProcess initial m increment)) A).toReal
  congr 1
  rw [← Measure.map_apply (μ := (iidSequenceLaw nu).map future)
    (measurable_const_add _) hA, hkernel]

end ProbabilityTheory.RandomWalk
