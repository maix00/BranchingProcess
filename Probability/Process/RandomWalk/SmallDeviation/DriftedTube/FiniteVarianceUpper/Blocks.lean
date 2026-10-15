/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Drawdown.FiniteVarianceUpper

/-!
# Conditional blocks for an upper bound in a tilted tube

The public objects and theorems in this file formalize the proof of
Lemma 3.4 in Chapter 3 of Wang Yiyang, *Asymptotic speed of the $N$-branching
random walk with infinite offspring*.

- `driftedTubeEvent` is
  \[
    T_{L,\Delta,c,r_0}:=\left\{Y:
      r_0+\frac{cj}{\Delta^2}\le Y_j\le
      r_0+\frac{cj}{\Delta^2}+\Delta,\ 1\le j\le L\right\}.
  \]
- `driftedTubeEvent_subset_noLargeDropEndpointBelowEvent` proves that, for
  $-\Delta\le r_0\le0$ and $c\ge0$, membership in $T_{L,\Delta,c,r_0}$
  implies $Y_i-Y_j\le\Delta$ for $0\le i\le j\le L$ and
  $Y_L\le\Delta+cL/\Delta^2$.
- `exists_driftedTubeBlockProbability_le_exp_of_finiteVariance` proves that,
  for $0<\eta<1$ and $0<d<\pi^2\sigma^2/2$, the complete block of length
  $\ell=\lfloor\Delta^{2+\eta}\rfloor$ has probability at most
  $\exp(-d\ell/\Delta^2)$, uniformly over $-\Delta\le r_0\le0$ for large
  $\Delta$. Its event inclusion is the application of Chapter 3, Lemma 3.3
  with endpoint parameter $\eta/2$.
- `driftedTubePairEvent` and `driftedTubeBlockEvent` encode the next block
  conditional on the increment prefix. `measurableSet_driftedTubePairEvent`
  and `measurableSet_driftedTubeBlockEvent` give their measurability at the
  block end.
- `finiteDriftedTubeEvent` is the same block event on $\mathrm{Fin}(\ell)$;
  `iidSequenceLaw_map_blockCoordinates_driftedTubeEvent_le` transfers its
  probability bound to finite block coordinates.
- `iidSequenceLaw_condExp_driftedTubePairEvent_le_of_blockBound` and
  `iidSequenceLaw_condExp_driftedTubeBlockEvent_le_of_blockBound` state the
  conditional estimate
  $\mathbb E[\mathbf 1_{E_j}\mid\mathcal F_{j\ell}]\le
  \exp(-d\ell/\Delta^2)$ used in the Markov iteration.
-/

open Filter MeasureTheory
open scoped Topology

@[expose] public section

namespace ProbabilityTheory.RandomWalk.SmallDeviation

open ProbabilityTheory.RandomWalk
open ProbabilityTheory.RandomWalk.SmallDeviation.Drawdown

/-- The path event for a linearly rising tube of width `width`. -/
def driftedTubeEvent (horizon : ℕ) (width drift lower : ℝ) :
    Set (ℕ → ℝ) :=
  {increment | ∀ j : ℕ, 1 ≤ j → j ≤ horizon →
    lower + drift * (j : ℝ) / width ^ 2 ≤
        AdditivePath.displacement j increment ∧
      AdditivePath.displacement j increment ≤
        lower + drift * (j : ℝ) / width ^ 2 + width}

/-- On a tube with nonnegative drift, the upper constraint at time `i`
and lower constraint at time `j ≥ i` bound the drawdown by its width. -/
theorem driftedTubeEvent_subset_noLargeDropEndpointBelowEvent
    (horizon : ℕ) {width drift lower : ℝ}
    (hwidth : 0 < width) (hdrift : 0 ≤ drift)
    (hlower : -width ≤ lower) (hupper : lower ≤ 0) :
    driftedTubeEvent horizon width drift lower ⊆
      noLargeDropEndpointBelowEvent horizon width
        (width + drift * (horizon : ℝ) / width ^ 2) := by
  intro increment hpath
  have hslope : 0 ≤ drift / width ^ 2 := div_nonneg hdrift (sq_nonneg width)
  have htube (j : ℕ) (hj : 1 ≤ j) (horizonBound : j ≤ horizon) :=
    hpath j hj horizonBound
  constructor
  · intro i j hij hj
    by_cases hjzero : j = 0
    · have hizero : i = 0 := by omega
      subst i
      subst j
      simp [AdditivePath.displacement_zero, hwidth.le]
    have hjpos : 1 ≤ j := by omega
    have hjtube := htube j hjpos hj
    by_cases hi : i = 0
    · subst i
      have hterm : 0 ≤ drift * (j : ℝ) / width ^ 2 := by positivity
      simpa [AdditivePath.displacement_zero] using
        (show (0 : ℝ) - AdditivePath.displacement j increment ≤ width by
          linarith [hjtube.1])
    · have hipos : 1 ≤ i := by omega
      have hitube := htube i hipos (by omega)
      have htime : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
      have hnonneg :
          drift * (i : ℝ) / width ^ 2 ≤
            drift * (j : ℝ) / width ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_left htime hslope
        simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hmul
      linarith [hitube.2, hjtube.1]
  · by_cases hzero : horizon = 0
    · subst horizon
      simp [AdditivePath.displacement_zero]
      linarith
    · have hpos : 1 ≤ horizon := by omega
      have hend := htube horizon hpos le_rfl
      linarith [hend.2]

/-- The single complete-block estimate in Wang Yiyang, Chapter 3, proof of
Lemma 3.4. The drifted tube is included in the no-large-drop event of
Chapter 3, Lemma 3.3 with endpoint parameter `η/2`. -/
theorem exists_driftedTubeBlockProbability_le_exp_of_finiteVariance
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
  have hfloor := Drawdown.eventually_drawdownFloorBlockLength_bounds heta
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

/-- The path event for one block of a linearly rising tube, expressed in
terms of the increment prefix before the block and the increments in the
block. At block time `k`, the global interval is
`[lower + drift * (start + k) / width^2, lower + drift * (start + k) / width^2 + width]`.
-/
def driftedTubePairEvent {start length : ℕ}
    (lower width drift : ℝ) :
    Set ((Fin start → ℝ) × (Fin length → ℝ)) :=
  {pair | ∀ k : Fin (length + 1),
    lower + drift * ((start + (k : ℕ) : ℕ) : ℝ) / width ^ 2 ≤
        Drawdown.drawdownPrefixSum pair.1 +
          Drawdown.drawdownPartialBlockSum pair.2 k ∧
      Drawdown.drawdownPrefixSum pair.1 +
          Drawdown.drawdownPartialBlockSum pair.2 k ≤
        lower + drift * ((start + (k : ℕ) : ℕ) : ℝ) / width ^ 2 + width}

/-- The measurable event for one tilted-tube block in the full increment
sequence. -/
def driftedTubeBlockEvent (start length : ℕ)
    (lower width drift : ℝ) : Set (ℕ → ℝ) :=
  {increment |
    (Combinatorics.Sequence.blockCoordinates 0 start increment,
      Combinatorics.Sequence.blockCoordinates start length increment) ∈
      driftedTubePairEvent lower width drift}

private theorem measurable_driftedTubePartialBlockSum {length : ℕ}
    (k : Fin (length + 1)) :
    Measurable (fun block : Fin length → ℝ =>
      Drawdown.drawdownPartialBlockSum block k) := by
  induction k using Fin.induction with
  | zero => exact measurable_const
  | succ k ih =>
      have hsum := ih.add (measurable_pi_apply k)
      have heq : (fun block : Fin length → ℝ =>
          Drawdown.drawdownPartialBlockSum block k.succ) =
        (fun block => Drawdown.drawdownPartialBlockSum block k.castSucc) +
          (fun block : Fin length → ℝ => block k) := by
        funext block
        simp only [Drawdown.drawdownPartialBlockSum, Fin.partialSum_succ,
          Pi.add_apply]
      exact heq ▸ hsum

/-- The pair event for one tilted-tube block is measurable. -/
theorem measurableSet_driftedTubePairEvent {start length : ℕ}
    (lower width drift : ℝ) :
    MeasurableSet (driftedTubePairEvent (start := start) (length := length)
      lower width drift) := by
  rw [show driftedTubePairEvent (start := start) (length := length)
        lower width drift =
      ⋂ k : Fin (length + 1),
        {pair : (Fin start → ℝ) × (Fin length → ℝ) |
          lower + drift * ((start + (k : ℕ) : ℕ) : ℝ) / width ^ 2 ≤
              Drawdown.drawdownPrefixSum pair.1 +
                Drawdown.drawdownPartialBlockSum pair.2 k ∧
            Drawdown.drawdownPrefixSum pair.1 +
                Drawdown.drawdownPartialBlockSum pair.2 k ≤
              lower + drift * ((start + (k : ℕ) : ℕ) : ℝ) / width ^ 2 + width} by
    ext pair
    simp [driftedTubePairEvent]]
  apply MeasurableSet.iInter
  intro k
  have hpast : Measurable (fun pair :
      (Fin start → ℝ) × (Fin length → ℝ) =>
        Drawdown.drawdownPrefixSum pair.1) := by
    exact ((Finset.measurable_sum Finset.univ fun i _ =>
      measurable_pi_apply i).comp measurable_fst)
  have hblock : Measurable (fun pair :
      (Fin start → ℝ) × (Fin length → ℝ) =>
        Drawdown.drawdownPartialBlockSum pair.2 k) := by
    exact (measurable_driftedTubePartialBlockSum k).comp measurable_snd
  let pathValue : (Fin start → ℝ) × (Fin length → ℝ) → ℝ := fun pair =>
    Drawdown.drawdownPrefixSum pair.1 +
      Drawdown.drawdownPartialBlockSum pair.2 k
  have hvalue : Measurable pathValue := by
    change Measurable (fun pair :
      (Fin start → ℝ) × (Fin length → ℝ) =>
        Drawdown.drawdownPrefixSum pair.1 +
          Drawdown.drawdownPartialBlockSum pair.2 k)
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
def finiteDriftedTubeEvent (length : ℕ) (lower width drift : ℝ) :
    Set (Fin length → ℝ) :=
  {block | ∀ j : Fin length,
    lower + drift * ((j : ℕ) + 1 : ℝ) / width ^ 2 ≤
        Drawdown.drawdownPartialBlockSum block j.succ ∧
      Drawdown.drawdownPartialBlockSum block j.succ ≤
        lower + drift * ((j : ℕ) + 1 : ℝ) / width ^ 2 + width}

/-- The finite-coordinate event has the same probability as the
corresponding full-sequence tilted-tube event. -/
theorem iidSequenceLaw_map_blockCoordinates_driftedTubeEvent_le
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
              Drawdown.drawdownPartialBlockSum block j.succ ∧
            Drawdown.drawdownPartialBlockSum block j.succ ≤
              lower + drift * ((j : ℕ) + 1 : ℝ) / width ^ 2 + width} by
      ext block
      simp [finiteDriftedTubeEvent]]
    apply MeasurableSet.iInter
    intro j
    have hsum : Measurable (fun block : Fin length → ℝ =>
        Drawdown.drawdownPartialBlockSum block j.succ) :=
      measurable_driftedTubePartialBlockSum j.succ
    let boundary : ℝ := lower + drift * ((j : ℕ) + 1 : ℝ) / width ^ 2
    let pathValue : (Fin length → ℝ) → ℝ := fun block =>
      Drawdown.drawdownPartialBlockSum block j.succ
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
          Drawdown.drawdownPartialBlockSum
              (Combinatorics.Sequence.blockCoordinates 0 length increment)
              k.succ = AdditivePath.displacement j increment := by
        rw [Drawdown.drawdownPartialBlockSum, partialSum_blockCoordinates,
          AdditivePath.blockSum_zero_start]
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
          Drawdown.drawdownPartialBlockSum
              (Combinatorics.Sequence.blockCoordinates 0 length increment)
              j.succ = AdditivePath.displacement ((j : ℕ) + 1) increment := by
        rw [Drawdown.drawdownPartialBlockSum, partialSum_blockCoordinates,
          AdditivePath.blockSum_zero_start]
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
iteration in Wang Yiyang, Chapter 3, proof of Lemma 3.4. -/
theorem iidSequenceLaw_condExp_driftedTubePairEvent_le_of_blockBound
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
    let initial := Drawdown.drawdownPrefixSum past
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
                initial + Drawdown.drawdownPartialBlockSum block j.succ ∧
            initial + Drawdown.drawdownPartialBlockSum block j.succ ≤
              lower + drift *
                ((start + ((j : ℕ) + 1 : ℕ) : ℕ) : ℝ) / width ^ 2 + width
            at hk
          constructor <;> linarith [hk.1, hk.2, hboundary j]
        · intro h k
          refine Fin.cases ?_ (fun j => ?_) k
          · simpa [event, driftedTubePairEvent, initial,
              Drawdown.drawdownPrefixSum, Drawdown.drawdownPartialBlockSum,
              startLower] using hstart
          · have hj := h j
            change localLower + drift * ((j : ℕ) + 1 : ℝ) / width ^ 2 ≤
                Drawdown.drawdownPartialBlockSum block j.succ ∧
              Drawdown.drawdownPartialBlockSum block j.succ ≤
                localLower + drift * ((j : ℕ) + 1 : ℝ) / width ^ 2 + width
              at hj
            change lower + drift *
                ((start + ((j : ℕ) + 1 : ℕ) : ℕ) : ℝ) / width ^ 2 ≤
                  initial + Drawdown.drawdownPartialBlockSum block j.succ ∧
              initial + Drawdown.drawdownPartialBlockSum block j.succ ≤
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
            Drawdown.drawdownPrefixSum, Drawdown.drawdownPartialBlockSum,
            startLower] using hzero
        · simp
      change ((iidSequenceLaw ν).map
        (Combinatorics.Sequence.blockCoordinates start length)).real
        sectionEvent ≤ bound
      rw [hempty]
      simpa [Measure.real] using hboundNonneg
  exact Drawdown.iidSequenceLaw_condExp_pairEvent_le_of_sectionProbability
    ν start length event hmeasurable hsections

private def driftedTubePrefixBlockPair (start length : ℕ) :
    (Fin (start + length) → ℝ) →
      (Fin start → ℝ) × (Fin length → ℝ) :=
  fun whole =>
    (fun i : Fin start => whole ⟨(i : ℕ), by omega⟩,
      fun j : Fin length => whole ⟨start + (j : ℕ), by omega⟩)

private theorem measurable_driftedTubePrefixBlockPair (start length : ℕ) :
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

private theorem driftedTubePrefixBlockPair_blockCoordinates
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
theorem measurableSet_driftedTubeBlockEvent
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
theorem iidSequenceLaw_condExp_driftedTubeBlockEvent_le_of_blockBound
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

end ProbabilityTheory.RandomWalk.SmallDeviation

end
