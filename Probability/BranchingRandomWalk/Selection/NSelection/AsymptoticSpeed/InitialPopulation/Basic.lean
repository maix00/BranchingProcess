/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Selection.NSelection.AsymptoticSpeed.Limit.KingmanInterface
public import Combinatorics.BranchingWalk.Step.Measurability
public import Mathlib.Probability.BorelCantelli
public import Mathlib.Order.LiminfLimsup
import Probability.BranchingProcess.Offspring.Count
public import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated

/-!
# Filling an initially smaller selected population

The small-initial-population extension has three dependencies:

1. supercriticality implies a positive chance of at least two children;
2. repeated independent opportunities for this split fill any fixed finite
   capacity in finite time almost surely;
3. the process after the filling time has the law of an exact-`N` process,
   so its asymptotic speed is the one obtained from the Kingman interface.

This file records the independent split events in the exact-`N` generation
environment and transports the rank-zero speed from the origin to any finite
initial vector. The actual smaller root-indexed population and its capacity
hitting argument are developed in the sibling `Trajectory/` modules; their
fresh-field law is then connected to the ranked-batch speed interface.

The public declarations are:

- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed.firstRankSplitEvent`:
  for $h_N:0<N$, the generation-$n$ event
  $\{\omega:2\le\operatorname{childCount}(\omega_n(\langle0,h_N\rangle))\}$.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed.firstRankSplitEvent_measure_eq`:
  $\operatorname{generationEnvironmentLaw}(\mu,N)
  (\operatorname{firstRankSplitEvent}(h_N,n))
   =\mu(\{\xi:2\le\operatorname{childCount}(\xi)\})$ for every $n$.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed.ae_frequently_firstRankSplitEvent`:
  if $\mu$ is supercritical, then the limsup of the rank-zero split events
  has probability one under $\operatorname{generationEnvironmentLaw}(\mu,N)$.
- `ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed.infiniteOffspringRun_rankZero_hasAsymptoticSpeed_of_initial`:
  if the origin-start rank-zero run has asymptotic speed $c$, then so does
  the run from every finite initial position vector.
-/

open MeasureTheory
open scoped ENNReal

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

open Combinatorics.Branching
open Filter ProbabilityTheory
open ProbabilityTheory.BranchingProcess.Offspring
open scoped Topology

/-- A split at the first active rank in generation `n`. The sequence of
these events is independent because it reads disjoint generation coordinates
of the pre-sampled product environment. -/
def firstRankSplitEvent {N : ℕ} (hN : 0 < N) (n : ℕ) :
    Set (GenerationEnvironment N) :=
  {ω | 2 ≤ Step.childCount (ω n (⟨0, hN⟩ : Fin N))}

private def batchFirstRankSplitEvent {N : ℕ} (hN : 0 < N) :
    Set (GenerationBatch N) :=
  {batch | 2 ≤ Step.childCount (batch (⟨0, hN⟩ : Fin N))}

private lemma measurable_batchFirstRankSplitEvent {N : ℕ} (hN : 0 < N) :
    MeasurableSet (batchFirstRankSplitEvent hN) := by
  change MeasurableSet
    {batch : GenerationBatch N |
      2 ≤ Step.childCount (batch (⟨0, hN⟩ : Fin N))}
  simpa [offspringSplitSet] using
    (measurableSet_offspringSplitSet (ι := ℕ) (X := ℝ)).preimage
      (measurable_pi_apply (⟨0, hN⟩ : Fin N))

/-- The first-rank split event has the same positive probability in every
generation. -/
theorem firstRankSplitEvent_measure_eq
    {N : ℕ} (hN : 0 < N) (μ : Measure (Step ℕ ℝ))
    [IsProbabilityMeasure μ] (n : ℕ) :
    generationEnvironmentLaw μ N (firstRankSplitEvent hN n) =
      μ {ξ | 2 ≤ Step.childCount ξ} := by
  let E := batchFirstRankSplitEvent hN
  let evalGen : GenerationEnvironment N → GenerationBatch N := fun ω => ω n
  let evalRank : GenerationBatch N → Step ℕ ℝ :=
    fun batch => batch (⟨0, hN⟩ : Fin N)
  have hE : MeasurableSet E := measurable_batchFirstRankSplitEvent hN
  have hEvalGen : Measurable evalGen := measurable_pi_apply n
  have hEvalRank : Measurable evalRank := measurable_pi_apply (⟨0, hN⟩ : Fin N)
  have hfirst : generationEnvironmentLaw μ N (firstRankSplitEvent hN n) =
      (generationEnvironmentLaw μ N).map evalGen E := by
    rw [Measure.map_apply hEvalGen hE]
    rfl
  have hsecond :
      (generationEnvironmentLaw μ N).map evalGen E =
        generationBatchLaw μ N E := by
    exact congrArg (fun ν : Measure (GenerationBatch N) => ν E)
      (generationEnvironmentLaw_generation_marginal μ N n)
  have hthird :
      generationBatchLaw μ N E =
        μ {ξ | 2 ≤ Step.childCount ξ} := by
    have hrawEvent : MeasurableSet
        {ξ : Step ℕ ℝ | 2 ≤ Step.childCount ξ} := by
      simpa [offspringSplitSet] using
        (measurableSet_offspringSplitSet (ι := ℕ) (X := ℝ))
    have heq : E = evalRank ⁻¹' {ξ : Step ℕ ℝ |
        2 ≤ Step.childCount ξ} := by
      ext batch
      rfl
    rw [heq, ← Measure.map_apply hEvalRank hrawEvent,
      generationBatchLaw_parent_marginal μ (⟨0, hN⟩ : Fin N)]
  exact hfirst.trans (hsecond.trans hthird)

/-- Under supercriticality, the pre-sampled first-rank offspring marks split
infinitely often in an `N`-generation environment. This concerns the marks;
linking them to a still-active parent in a smaller population requires the
separate population-growth argument. -/
theorem ae_frequently_firstRankSplitEvent
    {N : ℕ} (hN : 0 < N) (μ : Measure (Step ℕ ℝ))
    [IsProbabilityMeasure μ]
    (hsupercritical : (1 : ℝ≥0∞) <
      ∫⁻ ξ, (Step.childCount ξ : ℝ≥0∞) ∂μ) :
    ∀ᵐ ω ∂generationEnvironmentLaw μ N,
      ∃ᶠ n in atTop, ω ∈ firstRankSplitEvent hN n := by
  have hsplitRaw :=
    measure_pos_childCount_ge_two_of_expectedChildCount_gt_one μ hsupercritical
  have hsplitRaw' : 0 < μ {ξ | 2 ≤ Step.childCount ξ} := by
    simpa [offspringSplitSet] using hsplitRaw
  let ν := generationEnvironmentLaw μ N
  have hν : IsProbabilityMeasure ν := generationEnvironmentLaw_isProbability μ N
  let events : ℕ → Set (GenerationEnvironment N) :=
    fun n => firstRankSplitEvent hN n
  let coordinate : ℕ → MeasurableSpace (GenerationEnvironment N) :=
    generationCoordinateSigma
  have hcoordinateIndep : iIndep coordinate ν := by
    apply (iIndepFun_iff_iIndep
      (fun _ : ℕ => (inferInstance : MeasurableSpace (GenerationBatch N)))
      (fun (n : ℕ) (ω : GenerationEnvironment N) => ω n) ν).mp
    exact generationEnvironmentLaw_generations_independent μ N
  have heventMeasurable : ∀ n, MeasurableSet[coordinate n] (events n) := by
    intro n
    let evalGen : GenerationEnvironment N → GenerationBatch N := fun ω => ω n
    have hE : MeasurableSet (batchFirstRankSplitEvent hN) :=
      measurable_batchFirstRankSplitEvent hN
    have heq : events n = evalGen ⁻¹' batchFirstRankSplitEvent hN := by
      ext ω
      rfl
    rw [heq]
    change MeasurableSet[
      (inferInstance : MeasurableSpace (GenerationBatch N)).comap evalGen]
      (evalGen ⁻¹' batchFirstRankSplitEvent hN)
    exact ⟨batchFirstRankSplitEvent hN, hE, rfl⟩
  have heventsMeasurable : ∀ n, MeasurableSet (events n) := by
    intro n
    change MeasurableSet
      {ω : GenerationEnvironment N |
        2 ≤ Step.childCount (ω n (⟨0, hN⟩ : Fin N))}
    simpa [offspringSplitSet] using
      (measurableSet_offspringSplitSet (ι := ℕ) (X := ℝ)).preimage
        ((measurable_pi_apply (⟨0, hN⟩ : Fin N)).comp
          (measurable_pi_apply n))
  have heventsIndep : iIndepSet events ν := by
    rw [iIndepSet_iff_iIndep]
    apply iIndep_of_iIndep_of_le hcoordinateIndep
    intro n
    exact MeasurableSpace.generateFrom_le fun s hs => by
      have hs' : s = events n := by simpa using hs
      rw [hs']
      exact heventMeasurable n
  have hprob : ∀ n, ν (events n) = μ {ξ | 2 ≤ Step.childCount ξ} :=
    firstRankSplitEvent_measure_eq hN μ
  have hsum : (∑' n : ℕ, ν (events n)) = ∞ := by
    simpa only [hprob] using
      (ENNReal.tsum_const_eq_top_of_ne_zero hsplitRaw'.ne')
  have hBC := ProbabilityTheory.measure_limsup_eq_one
    heventsMeasurable heventsIndep hsum
  have hlimsupMeasurable : MeasurableSet (Filter.limsup events atTop) := by
    rw [limsup_eq_iInf_iSup_of_nat']
    exact MeasurableSet.iInter (fun n =>
      MeasurableSet.iUnion (fun k => heventsMeasurable (k + n)))
  have hae : ∀ᵐ ω ∂ν, ω ∈ Filter.limsup events atTop :=
    (ae_mem_iff_measure_eq
      hlimsupMeasurable.nullMeasurableSet).2 (by
        simpa using hBC)
  filter_upwards [hae] with ω hω
  simpa [events, Filter.mem_limsup_iff_frequently_mem] using hω

/-- For a fixed good `N`-slot environment, the leftmost rank has the same
asymptotic speed from every finite initial position vector as from the
origin. Coordinatewise monotonicity sandwiches the trajectory between two
constant translates of the origin trajectory. -/
theorem infiniteOffspringRun_rankZero_hasAsymptoticSpeed_of_initial
    {N : ℕ} (hN : 0 < N)
    (offspring : ℕ → Fin N → Step ℕ ℝ)
    (hgood : ∀ t, IsGoodInfiniteOffspringBatch (offspring t))
    (initial : Fin N → ℝ) (c : ℝ)
    (horigin : Combinatorics.Branching.Selection.NSelection.HasAsymptoticSpeed
      (𝕜 := ℝ)
      (fun n => infiniteOffspringRun offspring hgood (fun _ => 0) n
        (⟨0, hN⟩ : Fin N)) c) :
    Combinatorics.Branching.Selection.NSelection.HasAsymptoticSpeed
      (𝕜 := ℝ)
      (fun n => infiniteOffspringRun offspring hgood initial n
        (⟨0, hN⟩ : Fin N)) c := by
  let origin : Fin N := ⟨0, hN⟩
  let K : ℝ := ∑ i : Fin N, |initial i|
  let zeroRun : ℕ → Fin N → ℝ :=
    infiniteOffspringRun offspring hgood (fun _ => 0)
  let initialRun : ℕ → Fin N → ℝ :=
    infiniteOffspringRun offspring hgood initial
  let scaledZero : ℕ → ℝ := fun n =>
    ((n + 1 : ℕ) : ℝ)⁻¹ * zeroRun (n + 1) origin
  let scaledInitial : ℕ → ℝ := fun n =>
    ((n + 1 : ℕ) : ℝ)⁻¹ * initialRun (n + 1) origin
  let scaledLow : ℕ → ℝ := fun n =>
    ((n + 1 : ℕ) : ℝ)⁻¹ * (zeroRun (n + 1) origin - K)
  let scaledHigh : ℕ → ℝ := fun n =>
    ((n + 1 : ℕ) : ℝ)⁻¹ * (zeroRun (n + 1) origin + K)
  have hKnonneg : 0 ≤ K := by
    dsimp [K]
    exact Finset.sum_nonneg fun i _ => abs_nonneg (initial i)
  have hKbound (i : Fin N) : |initial i| ≤ K := by
    dsimp [K]
    exact Finset.single_le_sum (fun j _ => abs_nonneg (initial j))
      (Finset.mem_univ i)
  have hinitialBounds (i : Fin N) : -K ≤ initial i ∧ initial i ≤ K := by
    exact abs_le.mp (hKbound i)
  have hlowMono := infiniteOffspringRun_mono_initial offspring hgood
    (fun _ => -K) initial (fun i => (hinitialBounds i).1)
  have hhighMono := infiniteOffspringRun_mono_initial offspring hgood
    initial (fun _ => K) (fun i => (hinitialBounds i).2)
  have hlowShift : ∀ n,
      infiniteOffspringRun offspring hgood (fun _ => -K) n =
        fun i => zeroRun n i - K := by
    intro n
    simpa [zeroRun, sub_eq_add_neg] using
      infiniteOffspringRun_shift offspring hgood (fun _ => 0) (-K) n
  have hhighShift : ∀ n,
      infiniteOffspringRun offspring hgood (fun _ => K) n =
        fun i => zeroRun n i + K := by
    intro n
    simpa [zeroRun] using
      infiniteOffspringRun_shift offspring hgood (fun _ => 0) K n
  have hzeroSucc : Tendsto scaledZero atTop (𝓝 c) := by
    exact Combinatorics.Branching.Selection.NSelection.hasAsymptoticSpeed_iff_succ
      _ _ |>.1 horigin
  have hreciprocal : Tendsto
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa [one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hscaledK : Tendsto (fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ)⁻¹ * K) atTop (𝓝 0) := by
    simpa using hreciprocal.mul_const K
  have hlowLimit : Tendsto scaledLow atTop (𝓝 c) := by
    have h := hzeroSucc.sub hscaledK
    simpa [scaledLow, scaledZero, mul_sub] using h
  have hhighLimit : Tendsto scaledHigh atTop (𝓝 c) := by
    have h := hzeroSucc.add hscaledK
    simpa [scaledHigh, scaledZero, mul_add] using h
  have hlowBound (n : ℕ) : scaledLow n ≤ scaledInitial n := by
    have hpos : 0 ≤ ((n + 1 : ℕ) : ℝ)⁻¹ := by positivity
    have hrun := hlowMono (n + 1) origin
    have hrun' : zeroRun (n + 1) origin - K ≤ initialRun (n + 1) origin := by
      rw [hlowShift (n + 1)] at hrun
      simpa [zeroRun, initialRun] using hrun
    simpa [scaledLow, scaledInitial, zeroRun, initialRun, mul_sub] using
      (mul_le_mul_of_nonneg_left hrun' hpos)
  have hhighBound (n : ℕ) : scaledInitial n ≤ scaledHigh n := by
    have hpos : 0 ≤ ((n + 1 : ℕ) : ℝ)⁻¹ := by positivity
    have hrun := hhighMono (n + 1) origin
    have hrun' : initialRun (n + 1) origin ≤ zeroRun (n + 1) origin + K := by
      rw [hhighShift (n + 1)] at hrun
      simpa [zeroRun, initialRun] using hrun
    simpa [scaledHigh, scaledInitial, zeroRun, initialRun, mul_add] using
      (mul_le_mul_of_nonneg_left hrun' hpos)
  have hscaledInitial : Tendsto scaledInitial atTop (𝓝 c) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hlowLimit hhighLimit (Eventually.of_forall hlowBound)
      (Eventually.of_forall hhighBound)
  exact Combinatorics.Branching.Selection.NSelection.hasAsymptoticSpeed_iff_succ
    _ _ |>.2 hscaledInitial

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection.Speed

end
