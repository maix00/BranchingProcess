/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Drawdown.FiniteVarianceUpper.Basic
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.Event
public import Probability.Process.RandomWalk.SmallDeviation.DriftedTube.BlockEvent
public import Probability.Process.Filtration.ConditionalBlocks
public import Combinatorics.Sequence.Block
public import Probability.Process.RandomWalk.Path.Block.Partition.Basic
public import Probability.Sequence.Filtration
import Probability.Sequence.IID.Blocks.Conditional
import Probability.Sequence.IID.Blocks.StoppingTime
import Analysis.Asymptotics.Scale.IntermediatePowerBlock

/-!
# Proof lemmas for the finite-variance tilted-tube upper bound

These declarations support the equal-length block proof of Wang Yiyang,
*Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*,
Chapter 3, Lemma 3.4. They encode its complete-block estimate, finite-block
representation, and conditional-expectation step. They are specific to that
proof and are kept under `FiniteVarianceUpper/Lemmas/`.

- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.exists_driftedTubeBlockProbability_le_exp_of_finiteVariance`:
  the complete
  block probability bound obtained from Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, Lemma 3.3.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.measurableSet_driftedTubeBlockEvent`:
  measurability of the block event.
- `ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube.iidSequenceLaw_condExp_driftedTubeBlockEvent_le_of_blockBound`:
  the
  conditional probability bound used in the block iteration.
-/

open Filter MeasureTheory
open scoped Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

/-- The single complete-block estimate in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, proof of
Lemma 3.4. Its inclusion in the no-large-drop event uses Chapter 3, Lemma 3.3
of Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite
Offspring*, with endpoint parameter `η/2`. -/
lemma exists_driftedTubeBlockProbability_le_exp_of_finiteVariance
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {variance drift eta d : ℝ}
    (hν : ProbabilityTheory.IsCenteredSecondMoment ν variance)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < variance) (hdrift : 0 ≤ drift)
    (heta : 0 < eta) (hetaOne : eta < 1)
    (hd : 0 < d) (hcritical : d < Real.pi ^ 2 / 2 * variance) :
    ∃ Delta₀ : ℝ, 1 ≤ Delta₀ ∧
      ∀ Delta ≥ Delta₀, ∀ lower : ℝ,
        -Delta ≤ lower → lower ≤ 0 →
        (iidSequenceLaw ν).real
          (driftedTubeEvent ⌊Delta ^ (2 + eta)⌋₊ Delta drift lower) ≤
          Real.exp (-d * ((⌊Delta ^ (2 + eta)⌋₊ : ℝ) / Delta ^ 2)) := by
  have hetaHalf : 0 < eta / 2 := by linarith
  obtain ⟨DeltaMain, hDeltaMain, hmain⟩ :=
    Drawdown.measureReal_noLargeDropEndpointBelowEvent_le_exp_of_finiteVariance
      ν hν hsquare hvariance hetaHalf hd hcritical
  have hfloor := Asymptotics.eventually_nat_floor_rpow_intermediate_bounds
    (p := 2 + eta / 2) (q := 2 + eta) (by linarith) (by linarith)
  have hgrowth : ∀ᶠ Delta : ℝ in atTop,
      drift ≤ Delta ^ (1 - eta) :=
    (_root_.tendsto_rpow_atTop (by linarith : 0 < 1 - eta)).eventually
      (eventually_ge_atTop drift)
  obtain ⟨DeltaBound, hDeltaBound⟩ :=
    Filter.eventually_atTop.1 (hfloor.and hgrowth)
  let Delta₀ := max DeltaMain (max DeltaBound 1)
  refine ⟨Delta₀, le_max_of_le_right (le_max_right _ _), ?_⟩
  intro Delta hDelta lower hlower hupper
  have hDeltaMain' : DeltaMain ≤ Delta :=
    (le_max_left _ _).trans hDelta
  have hDeltaBound' : DeltaBound ≤ Delta :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hDelta)
  have hDeltaOne : 1 ≤ Delta :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hDelta)
  have hDeltaPos : 0 < Delta := by linarith
  rcases hDeltaBound Delta hDeltaBound' with
    ⟨⟨hfloorPos, _, hfloorLower, hfloorUpper⟩, hgrowthAt⟩
  let length : ℕ := ⌊Delta ^ (2 + eta)⌋₊
  have hlengthLower : Delta ^ (2 + eta / 2) ≤ (length : ℝ) := hfloorLower
  have hlengthUpper : (length : ℝ) ≤ Delta ^ (2 + eta) := hfloorUpper
  have hpower : Delta ^ (2 + eta) = Delta ^ 2 * Delta ^ eta := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_add hDeltaPos 2 eta
  have hpowerOne : Delta ^ eta * Delta ^ (1 - eta) = Delta := by
    rw [← Real.rpow_add hDeltaPos]
    simp
  have hdriftTerm : drift * (length : ℝ) / Delta ^ 2 ≤ Delta := by
    have hle : drift * (length : ℝ) ≤ drift * (Delta ^ 2 * Delta ^ eta) :=
      mul_le_mul_of_nonneg_left (hlengthUpper.trans_eq hpower) hdrift
    have hbound : drift * Delta ^ eta ≤ Delta := by
      calc
        drift * Delta ^ eta ≤ Delta ^ (1 - eta) * Delta ^ eta :=
          mul_le_mul_of_nonneg_right hgrowthAt (by positivity)
        _ = Delta := by simpa [mul_comm] using hpowerOne
    apply (div_le_iff₀ (sq_pos_of_pos hDeltaPos)).2
    nlinarith [hle, hbound, sq_nonneg Delta]
  have hthreshold :
      Delta + drift * (length : ℝ) / Delta ^ 2 ≤ Delta / (eta / 2) := by
    have htwo : 2 * Delta ≤ Delta / (eta / 2) := by
      apply (le_div_iff₀ hetaHalf).2
      nlinarith [hetaOne.le, hDeltaPos.le]
    linarith
  have hsubset :
      driftedTubeEvent length Delta drift lower ⊆
        Drawdown.noLargeDropEndpointBelowEvent length Delta (Delta / (eta / 2)) := by
    intro increment hpath
    have hbasic := driftedTubeEvent_subset_noLargeDropEndpointBelowEvent
      length hDeltaPos hdrift hlower hupper hpath
    exact ⟨hbasic.1, hbasic.2.trans hthreshold⟩
  have hmainAt := hmain Delta hDeltaMain' length hlengthLower
  exact (measureReal_mono hsubset (measure_ne_top (iidSequenceLaw ν) _)).trans hmainAt

private lemma measurable_driftedTubePartialBlockSum {length : ℕ}
    (k : Fin (length + 1)) :
    Measurable (fun block : Fin length → ℝ =>
      Fin.partialSum block k) := by
  induction k using Fin.induction with
  | zero => exact measurable_const
  | succ k ih =>
      have hsum := ih.add (measurable_pi_apply k)
      have heq : (fun block : Fin length → ℝ =>
          Fin.partialSum block k.succ) =
        (fun block => Fin.partialSum block k.castSucc) +
          (fun block : Fin length → ℝ => block k) := by
        funext block
        simp only [Fin.partialSum_succ, Pi.add_apply]
      exact heq ▸ hsum

/-- The pair event for one tilted-tube block is measurable. -/
private lemma measurableSet_driftedTubePairEvent {start length : ℕ}
    (lower width drift : ℝ) :
    MeasurableSet (driftedTubePairEvent (start := start) (length := length)
      lower width drift) := by
  rw [show driftedTubePairEvent (start := start) (length := length)
        lower width drift =
      ⋂ k : Fin (length + 1),
        {pair : (Fin start → ℝ) × (Fin length → ℝ) |
          lower + drift * ((start + (k : ℕ) : ℕ) : ℝ) / width ^ 2 ≤
              (∑ i : Fin start, pair.1 i) +
                Fin.partialSum pair.2 k ∧
            (∑ i : Fin start, pair.1 i) +
                Fin.partialSum pair.2 k ≤
              lower + drift * ((start + (k : ℕ) : ℕ) : ℝ) / width ^ 2 + width} by
    ext pair
    simp [driftedTubePairEvent]]
  apply MeasurableSet.iInter
  intro k
  have hpast : Measurable (fun pair :
      (Fin start → ℝ) × (Fin length → ℝ) =>
        (∑ i : Fin start, pair.1 i)) := by
    exact ((Finset.measurable_sum Finset.univ fun i _ =>
      measurable_pi_apply i).comp measurable_fst)
  have hblock : Measurable (fun pair :
      (Fin start → ℝ) × (Fin length → ℝ) =>
        Fin.partialSum pair.2 k) := by
    exact (measurable_driftedTubePartialBlockSum k).comp measurable_snd
  let pathValue : (Fin start → ℝ) × (Fin length → ℝ) → ℝ := fun pair =>
    (∑ i : Fin start, pair.1 i) +
      Fin.partialSum pair.2 k
  have hvalue : Measurable pathValue := by
    change Measurable (fun pair :
      (Fin start → ℝ) × (Fin length → ℝ) =>
        (∑ i : Fin start, pair.1 i) +
          Fin.partialSum pair.2 k)
    exact hpast.add hblock
  let boundary : ℝ := lower + drift * ((start + (k : ℕ) : ℕ) : ℝ) / width ^ 2
  have hlower : Measurable (fun pair :
      (Fin start → ℝ) × (Fin length → ℝ) =>
        pathValue pair - boundary) := by
    exact hvalue.sub measurable_const
  have hupper : Measurable (fun pair :
      (Fin start → ℝ) × (Fin length → ℝ) =>
        pathValue pair - (boundary + width)) := by
    exact hvalue.sub measurable_const
  have heq :
      {pair : (Fin start → ℝ) × (Fin length → ℝ) |
        boundary ≤ pathValue pair ∧ pathValue pair ≤ boundary + width} =
      {pair | 0 ≤ pathValue pair - boundary ∧
        pathValue pair - (boundary + width) ≤ 0} := by
    ext pair
    simp only [Set.mem_ofPred_eq]
    constructor <;> intro h <;> constructor <;> linarith
  rw [heq]
  exact (measurableSet_Ici.preimage hlower).inter
    (measurableSet_Iic.preimage hupper)

/-- The finite-coordinate tilted-tube event for a block started at zero. -/
private def finiteDriftedTubeEvent (length : ℕ) (lower width drift : ℝ) :
    Set (Fin length → ℝ) :=
  {block | ∀ j : Fin length,
    lower + drift * ((j : ℕ) + 1 : ℝ) / width ^ 2 ≤
        Fin.partialSum block j.succ ∧
      Fin.partialSum block j.succ ≤
        lower + drift * ((j : ℕ) + 1 : ℝ) / width ^ 2 + width}

/-- The finite-coordinate event has the same probability as the
corresponding full-sequence tilted-tube event. -/
private lemma iidSequenceLaw_map_blockCoordinates_driftedTubeEvent_le
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (length : ℕ) (lower width drift bound : ℝ)
    (hbound : (iidSequenceLaw ν).real
      (driftedTubeEvent length width drift lower) ≤ bound) :
    (((iidSequenceLaw ν).map
      (Combinatorics.Sequence.blockCoordinates 0 length)).real
      (finiteDriftedTubeEvent length lower width drift)) ≤
        bound := by
  have hfinite : MeasurableSet
      (finiteDriftedTubeEvent length lower width drift) := by
    rw [show finiteDriftedTubeEvent length lower width drift =
      ⋂ j : Fin length,
        {block : Fin length → ℝ |
          lower + drift * ((j : ℕ) + 1 : ℝ) / width ^ 2 ≤
              Fin.partialSum block j.succ ∧
            Fin.partialSum block j.succ ≤
              lower + drift * ((j : ℕ) + 1 : ℝ) / width ^ 2 + width} by
      ext block
      simp [finiteDriftedTubeEvent]]
    apply MeasurableSet.iInter
    intro j
    have hsum : Measurable (fun block : Fin length → ℝ =>
        Fin.partialSum block j.succ) :=
      measurable_driftedTubePartialBlockSum j.succ
    let boundary : ℝ := lower + drift * ((j : ℕ) + 1 : ℝ) / width ^ 2
    let pathValue : (Fin length → ℝ) → ℝ := fun block =>
      Fin.partialSum block j.succ
    have hlower : Measurable (fun block : Fin length → ℝ =>
        pathValue block - boundary) := by
      exact hsum.sub measurable_const
    have hupper : Measurable (fun block : Fin length → ℝ =>
        pathValue block - (boundary + width)) := by
      exact hsum.sub measurable_const
    have heq :
        {block : Fin length → ℝ | boundary ≤ pathValue block ∧
          pathValue block ≤ boundary + width} =
        {block | 0 ≤ pathValue block - boundary ∧
          pathValue block - (boundary + width) ≤ 0} := by
      ext block
      simp only [Set.mem_ofPred_eq]
      constructor <;> intro h <;> constructor <;> linarith
    rw [heq]
    exact (measurableSet_Ici.preimage hlower).inter
      (measurableSet_Iic.preimage hupper)
  have hevent :
      (Combinatorics.Sequence.blockCoordinates 0 length) ⁻¹'
        finiteDriftedTubeEvent length lower width drift =
    driftedTubeEvent length width drift lower := by
    ext increment
    simp only [Set.mem_preimage, finiteDriftedTubeEvent,
      driftedTubeEvent, Set.mem_ofPred_eq]
    constructor
    · intro h j hj hlength
      have hj' : j - 1 < length := by omega
      let k : Fin length := ⟨j - 1, hj'⟩
      have hk := h k
      have hsum :
          Fin.partialSum
              (Combinatorics.Sequence.blockCoordinates 0 length increment)
              k.succ = AdditivePath.displacement j increment := by
        rw [partialSum_blockCoordinates, AdditivePath.blockSum_zero_start]
        congr 1
        simp [k]
        omega
      have htime : ((k : ℕ) + 1 : ℝ) = (j : ℝ) := by
        simp [k]
        exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ j by omega))
      rw [hsum, htime] at hk
      exact hk
    · intro h j
      have hjpos : 1 ≤ (j : ℕ) + 1 := by omega
      have hjle : (j : ℕ) + 1 ≤ length := by omega
      have hpath := h ((j : ℕ) + 1) hjpos hjle
      have hsum :
          Fin.partialSum
              (Combinatorics.Sequence.blockCoordinates 0 length increment)
              j.succ = AdditivePath.displacement ((j : ℕ) + 1) increment := by
        rw [partialSum_blockCoordinates, AdditivePath.blockSum_zero_start]
        congr 1
      simpa [hsum] using hpath
  change ENNReal.toReal
      (((iidSequenceLaw ν).map
        (Combinatorics.Sequence.blockCoordinates 0 length))
        (finiteDriftedTubeEvent length lower width drift)) ≤ bound
  rw [Measure.map_apply (measurable_blockCoordinates 0 length) hfinite,
    hevent]
  exact hbound

/-- A uniform tilted-tube probability bound for every admissible relative
starting position gives the conditional block bound used in the Markov
iteration in Wang Yiyang, *Asymptotic Speed of the N-Branching Random Walk with Infinite Offspring*, Chapter 3, proof of Lemma 3.4. -/
private lemma iidSequenceLaw_condExp_driftedTubePairEvent_le_of_blockBound
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (start length : ℕ) {lower width drift bound : ℝ}
    (hboundNonneg : 0 ≤ bound)
    (hblockBound : ∀ localLower : ℝ, -width ≤ localLower →
      localLower ≤ 0 →
      (iidSequenceLaw ν).real
        (driftedTubeEvent length width drift localLower) ≤ bound) :
    ∀ᵐ increment ∂iidSequenceLaw ν,
      condExp
        (MeasurableSpace.comap
          (Combinatorics.Sequence.blockCoordinates 0 start) inferInstance)
        (iidSequenceLaw ν)
        (fun increment =>
          (driftedTubePairEvent (start := start) (length := length)
            lower width drift).indicator (fun _ => (1 : ℝ))
            (Combinatorics.Sequence.blockCoordinates 0 start increment,
              Combinatorics.Sequence.blockCoordinates start length increment))
        increment ≤ bound := by
  let startLower : ℝ := lower + drift * (start : ℝ) / width ^ 2
  let event := driftedTubePairEvent (start := start) (length := length)
    lower width drift
  have hmeasurable : MeasurableSet event :=
    measurableSet_driftedTubePairEvent lower width drift
  have hsections : ∀ past : Fin start → ℝ,
      ((iidSequenceLaw ν).map
        (Combinatorics.Sequence.blockCoordinates start length)).real
        {block | (past, block) ∈ event} ≤ bound := by
    intro past
    let initial := (∑ i : Fin start, past i)
    let sectionEvent : Set (Fin length → ℝ) :=
      {block | (past, block) ∈ event}
    by_cases hstart : initial ∈ Set.Icc startLower (startLower + width)
    · let localLower : ℝ := startLower - initial
      have hlocalLower : -width ≤ localLower := by
        dsimp [localLower]
        linarith [hstart.2]
      have hlocalUpper : localLower ≤ 0 := by
        dsimp [localLower]
        linarith [hstart.1]
      have hboundary (j : Fin length) :
          lower + drift * ((start + ((j : ℕ) + 1 : ℕ) : ℕ) : ℝ) /
              width ^ 2 - initial =
            localLower + drift * ((j : ℕ) + 1 : ℝ) / width ^ 2 := by
        dsimp [localLower, startLower]
        push_cast
        ring
      have hsection : sectionEvent =
          finiteDriftedTubeEvent length localLower width drift := by
        ext block
        constructor
        · intro h j
          have hk := h j.succ
          change lower + drift *
              ((start + ((j : ℕ) + 1 : ℕ) : ℕ) : ℝ) / width ^ 2 ≤
                initial + Fin.partialSum block j.succ ∧
            initial + Fin.partialSum block j.succ ≤
              lower + drift *
                ((start + ((j : ℕ) + 1 : ℕ) : ℕ) : ℝ) / width ^ 2 + width
            at hk
          constructor <;> linarith [hk.1, hk.2, hboundary j]
        · intro h k
          refine Fin.cases ?_ (fun j => ?_) k
          · simpa [event, driftedTubePairEvent, initial,
              Fin.partialSum,
              startLower] using hstart
          · have hj := h j
            change localLower + drift * ((j : ℕ) + 1 : ℝ) / width ^ 2 ≤
                Fin.partialSum block j.succ ∧
              Fin.partialSum block j.succ ≤
                localLower + drift * ((j : ℕ) + 1 : ℝ) / width ^ 2 + width
              at hj
            change lower + drift *
                ((start + ((j : ℕ) + 1 : ℕ) : ℕ) : ℝ) / width ^ 2 ≤
                  initial + Fin.partialSum block j.succ ∧
              initial + Fin.partialSum block j.succ ≤
                lower + drift *
                  ((start + ((j : ℕ) + 1 : ℕ) : ℕ) : ℝ) / width ^ 2 + width
            constructor <;> linarith [hj.1, hj.2, hboundary j]
      have hfiniteBound := iidSequenceLaw_map_blockCoordinates_driftedTubeEvent_le
        ν length localLower width drift bound
        (hblockBound localLower hlocalLower hlocalUpper)
      change ((iidSequenceLaw ν).map
        (Combinatorics.Sequence.blockCoordinates start length)).real
        sectionEvent ≤ bound
      rw [iidSequenceLaw_map_blockCoordinates ν start length, hsection]
      exact hfiniteBound
    · have hempty : sectionEvent = ∅ := by
        ext block
        constructor
        · intro h
          have hzero := h ⟨0, Nat.zero_lt_succ _⟩
          apply hstart
          simpa [sectionEvent, event, driftedTubePairEvent, initial,
            Fin.partialSum,
            startLower] using hzero
        · simp
      change ((iidSequenceLaw ν).map
        (Combinatorics.Sequence.blockCoordinates start length)).real
        sectionEvent ≤ bound
      rw [hempty]
      simpa [Measure.real] using hboundNonneg
  exact ProbabilityTheory.iidSequenceLaw_condExp_pairEvent_le_of_sectionProbability
    ν start length event hmeasurable hsections

private def driftedTubePrefixBlockPair (start length : ℕ) :
    (Fin (start + length) → ℝ) →
      (Fin start → ℝ) × (Fin length → ℝ) :=
  fun whole =>
    (fun i : Fin start => whole ⟨(i : ℕ), by omega⟩,
      fun j : Fin length => whole ⟨start + (j : ℕ), by omega⟩)

private lemma measurable_driftedTubePrefixBlockPair (start length : ℕ) :
    Measurable (driftedTubePrefixBlockPair start length) := by
  have hpast : Measurable
      (fun whole : Fin (start + length) → ℝ =>
        fun i : Fin start =>
          whole (⟨(i : ℕ), by omega⟩ : Fin (start + length))) := by
    rw [measurable_pi_iff]
    intro i
    exact measurable_pi_apply (⟨(i : ℕ), by omega⟩ : Fin (start + length))
  have hblock : Measurable
      (fun whole : Fin (start + length) → ℝ =>
        fun j : Fin length =>
          whole (⟨start + (j : ℕ), by omega⟩ : Fin (start + length))) := by
    rw [measurable_pi_iff]
    intro j
    exact measurable_pi_apply
      (⟨start + (j : ℕ), by omega⟩ : Fin (start + length))
  exact hpast.prodMk hblock

private lemma driftedTubePrefixBlockPair_blockCoordinates
    (start length : ℕ) (increment : ℕ → ℝ) :
    driftedTubePrefixBlockPair start length
        (Combinatorics.Sequence.blockCoordinates 0 (start + length) increment) =
      (Combinatorics.Sequence.blockCoordinates 0 start increment,
        Combinatorics.Sequence.blockCoordinates start length increment) := by
  apply Prod.ext
  · funext i
    simp [driftedTubePrefixBlockPair,
      Combinatorics.Sequence.blockCoordinates]
  · funext j
    simp [driftedTubePrefixBlockPair,
      Combinatorics.Sequence.blockCoordinates]

/-- A tilted-tube block event is measurable at its block end. -/
lemma measurableSet_driftedTubeBlockEvent
    (start length : ℕ) (lower width drift : ℝ) :
    MeasurableSet[ProbabilityTheory.sequencePrefixFiltration
      (E := ℝ) (start + length)]
      (driftedTubeBlockEvent start length lower width drift) := by
  have hpair : MeasurableSet
      (driftedTubePairEvent (start := start) (length := length)
        lower width drift) :=
    measurableSet_driftedTubePairEvent lower width drift
  have hpreimage : MeasurableSet
      ((driftedTubePrefixBlockPair start length) ⁻¹'
        driftedTubePairEvent lower width drift) :=
    hpair.preimage (measurable_driftedTubePrefixBlockPair start length)
  have hevent : driftedTubeBlockEvent start length lower width drift =
      (Combinatorics.Sequence.blockCoordinates 0 (start + length)) ⁻¹'
        ((driftedTubePrefixBlockPair start length) ⁻¹'
          driftedTubePairEvent lower width drift) := by
    ext increment
    simp only [driftedTubeBlockEvent, Set.mem_preimage, Set.mem_ofPred_eq]
    rw [← driftedTubePrefixBlockPair_blockCoordinates start length increment]
  rw [ProbabilityTheory.sequencePrefixFiltration_eq_comap_blockCoordinates]
  exact (MeasurableSpace.measurableSet_comap).2
    ⟨_, hpreimage, hevent.symm⟩

/-- The pair-event conditional estimate, expressed for the full increment
sequence at the natural domain filtration of the block start. -/
lemma iidSequenceLaw_condExp_driftedTubeBlockEvent_le_of_blockBound
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (start length : ℕ) {lower width drift bound : ℝ}
    (hboundNonneg : 0 ≤ bound)
    (hblockBound : ∀ localLower : ℝ, -width ≤ localLower →
      localLower ≤ 0 →
      (iidSequenceLaw ν).real
        (driftedTubeEvent length width drift localLower) ≤ bound) :
    ∀ᵐ increment ∂iidSequenceLaw ν,
      condExp
        (ProbabilityTheory.sequencePrefixFiltration (E := ℝ) start)
        (iidSequenceLaw ν)
        ((driftedTubeBlockEvent start length lower width drift).indicator
          (fun _ => (1 : ℝ))) increment ≤ bound := by
  rw [ProbabilityTheory.sequencePrefixFiltration_eq_comap_blockCoordinates]
  have hpair := iidSequenceLaw_condExp_driftedTubePairEvent_le_of_blockBound
    (lower := lower) (width := width) (drift := drift) (bound := bound)
    ν start length hboundNonneg hblockBound
  have hindicator :
      (driftedTubeBlockEvent start length lower width drift).indicator
          (fun _ => (1 : ℝ)) =
        fun increment =>
          (driftedTubePairEvent (start := start) (length := length)
            lower width drift).indicator (fun _ => (1 : ℝ))
            (Combinatorics.Sequence.blockCoordinates 0 start increment,
              Combinatorics.Sequence.blockCoordinates start length increment) := by
    funext increment
    rfl
  filter_upwards [hpair] with increment hconditional
  rw [hindicator]
  exact hconditional

end ProbabilityTheory.RandomWalk.SmallDeviation.DriftedTube

end
