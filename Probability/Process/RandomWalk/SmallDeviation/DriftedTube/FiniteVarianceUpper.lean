/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Process.RandomWalk.SmallDeviation.Drawdown.FiniteVarianceUpper

/-!
# Small deviations in a tube with positive linear drift

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
- `exists_driftedTubeProbability_le_exp_of_finiteVariance` proves the full
  conclusion: for $v>0$, $c\ge0$, and $0<d<\pi^2\sigma^2/2$, there is
  $\Delta_0$ such that for $\Delta\ge\Delta_0$, $-\Delta\le r_0\le0$, and
  every $L\ge0$,
  \[
    \mathbb P(T_{L,\Delta,c,r_0})\le
    \exp\!\left(\Delta^v-\frac{dL}{\Delta^2}\right).
  \]
  The proof uses equal-length blocks, conditional-expectation iteration, and
  the estimate $L-q\ell<\ell$ for the final remainder.
-/

open Filter MeasureTheory
open scoped Topology

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

private theorem driftedTubeBlockPosition_eq
    (start length : ℕ) (increment : ℕ → ℝ)
    (k : Fin (length + 1)) :
    Drawdown.drawdownPrefixSum
        (Combinatorics.Sequence.blockCoordinates 0 start increment) +
      Drawdown.drawdownPartialBlockSum
        (Combinatorics.Sequence.blockCoordinates start length increment) k =
      AdditivePath.displacement (start + (k : ℕ)) increment := by
  have hprefix :
      Drawdown.drawdownPrefixSum
          (Combinatorics.Sequence.blockCoordinates 0 start increment) =
        AdditivePath.displacement start increment := by
    simp [Drawdown.drawdownPrefixSum,
      Combinatorics.Sequence.blockCoordinates, AdditivePath.displacement,
      Fin.sum_univ_eq_sum_range]
  calc
    _ = AdditivePath.displacement start increment +
        AdditivePath.blockSum start (k : ℕ) increment := by
      rw [hprefix, Drawdown.drawdownPartialBlockSum,
        partialSum_blockCoordinates]
    _ = AdditivePath.displacement (start + (k : ℕ)) increment :=
      (AdditivePath.displacement_add_eq_add_blockSum start (k : ℕ)
        increment).symm

/-- The full small-drift upper estimate in Wang Yiyang, Chapter 3,
Lemma 3.4. The proof follows its equal-length block decomposition,
conditional-expectation iteration, and final-remainder estimate. -/
theorem exists_driftedTubeProbability_le_exp_of_finiteVariance
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    {variance v drift d : ℝ}
    (hν : ProbabilityTheory.IsCenteredSecondMoment ν variance)
    (hsquare : Integrable (fun x : ℝ => x ^ 2) ν)
    (hvariance : 0 < variance) (hv : 0 < v)
    (hdrift : 0 ≤ drift) (hd : 0 < d)
    (hcritical : d < (Real.pi ^ 2 / 2) * variance) :
    ∃ Delta₀ : ℝ, 1 ≤ Delta₀ ∧
      ∀ Delta ≥ Delta₀, ∀ lower : ℝ, -Delta ≤ lower → lower ≤ 0 →
      ∀ horizon : ℕ,
        (iidSequenceLaw ν).real
          (driftedTubeEvent horizon Delta drift lower) ≤
            Real.exp (Delta ^ v - d * ((horizon : ℝ) / Delta ^ 2)) := by
  let eta : ℝ := min (v / 2) (1 / 2)
  have heta : 0 < eta := by
    dsimp [eta]
    positivity
  have hetaV : eta < v := by
    dsimp [eta]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hetaOne : eta < 1 := by
    dsimp [eta]
    exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hgrowth : ∀ᶠ Delta : ℝ in atTop, d ≤ Delta ^ (v - eta) :=
    (_root_.tendsto_rpow_atTop (by linarith : 0 < v - eta)).eventually
      (eventually_ge_atTop d)
  obtain ⟨DeltaBlock₀, hDeltaBlock₀, hblockProbability⟩ :=
    exists_driftedTubeBlockProbability_le_exp_of_finiteVariance
      ν hν hsquare hvariance hdrift heta hetaOne hd hcritical
  have hgood : ∀ᶠ Delta : ℝ in atTop,
      (1 ≤ (⌊Delta ^ (2 + eta)⌋₊ : ℝ) ∧
        Delta ^ (2 + eta) - Delta ^ (2 + eta / 2) ≤
          (⌊Delta ^ (2 + eta)⌋₊ : ℝ) ∧
        Delta ^ (2 + eta / 2) ≤ (⌊Delta ^ (2 + eta)⌋₊ : ℝ) ∧
        (⌊Delta ^ (2 + eta)⌋₊ : ℝ) ≤ Delta ^ (2 + eta)) ∧
      d ≤ Delta ^ (v - eta) ∧ DeltaBlock₀ ≤ Delta ∧ 1 ≤ Delta := by
    filter_upwards
      [Drawdown.eventually_drawdownFloorBlockLength_bounds heta,
        hgrowth, eventually_ge_atTop DeltaBlock₀,
        eventually_ge_atTop (1 : ℝ)] with Delta hfloor hgrowthAt hblockWidth hDelta
    exact ⟨hfloor, hgrowthAt, hblockWidth, hDelta⟩
  obtain ⟨DeltaBound, hDeltaBound⟩ := Filter.eventually_atTop.1 hgood
  let Delta₀ := max 1 DeltaBound
  refine ⟨Delta₀, le_max_left _ _, ?_⟩
  intro Delta hDelta lower hlower hupper horizon
  have hDeltaLarge : DeltaBound ≤ Delta :=
    (le_max_right _ _).trans hDelta
  obtain ⟨hfloor, hgrowthAt, hblockWidth, hDeltaOne⟩ :=
    hDeltaBound Delta hDeltaLarge
  have hDeltaPos : 0 < Delta := by linarith
  let blockLength : ℕ := ⌊Delta ^ (2 + eta)⌋₊
  let q : ℕ := horizon / blockLength
  let p : ℝ := Real.exp (-d * ((blockLength : ℝ) / Delta ^ 2))
  have hblockLengthPos : 0 < blockLength := by
    have hpos : 1 ≤ (blockLength : ℝ) := by simpa [blockLength] using hfloor.1
    exact_mod_cast hpos
  have hblockLengthLower : Delta ^ (2 + eta / 2) ≤ (blockLength : ℝ) := by
    simpa [blockLength] using hfloor.2.2.1
  have hblockLengthUpper : (blockLength : ℝ) ≤ Delta ^ (2 + eta) := by
    simpa [blockLength] using hfloor.2.2.2
  have hDeltaPower : Delta ^ (2 + eta) = Delta ^ 2 * Delta ^ eta := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_add hDeltaPos 2 eta
  have hscaleGrowth : d * Delta ^ eta ≤ Delta ^ v := by
    calc
      d * Delta ^ eta = Delta ^ eta * d := by ring
      _ ≤ Delta ^ eta * Delta ^ (v - eta) :=
        mul_le_mul_of_nonneg_left hgrowthAt (by positivity)
      _ = Delta ^ v := by
        rw [← Real.rpow_add hDeltaPos]
        congr 1
        ring
  by_cases hshort : horizon < blockLength
  · have hhorizonScale :
        (horizon : ℝ) / Delta ^ 2 ≤ Delta ^ eta := by
      apply (div_le_iff₀ (sq_pos_of_pos hDeltaPos)).2
      calc
        (horizon : ℝ) ≤ (blockLength : ℝ) := by exact_mod_cast hshort.le
        _ ≤ Delta ^ (2 + eta) := hblockLengthUpper
        _ = Delta ^ 2 * Delta ^ eta := hDeltaPower
        _ = Delta ^ eta * Delta ^ 2 := by ring
    have hbudget : d * ((horizon : ℝ) / Delta ^ 2) ≤ Delta ^ v :=
      (mul_le_mul_of_nonneg_left hhorizonScale hd.le).trans hscaleGrowth
    have hexponent : 0 ≤ Delta ^ v - d * ((horizon : ℝ) / Delta ^ 2) := by
      linarith
    have hprobability : (iidSequenceLaw ν).real
        (driftedTubeEvent horizon Delta drift lower) ≤ 1 := by
      calc
        _ ≤ (iidSequenceLaw ν).real Set.univ :=
          measureReal_mono (Set.subset_univ _) (measure_ne_top (iidSequenceLaw ν) _)
        _ = 1 := by simp
    exact hprobability.trans (Real.one_le_exp_iff.mpr hexponent)
  · have hblockRate : ∀ localLower : ℝ, -Delta ≤ localLower →
        localLower ≤ 0 →
        (iidSequenceLaw ν).real
          (driftedTubeEvent blockLength Delta drift localLower) ≤ p := by
      intro localLower hlocalLower hlocalUpper
      have h := hblockProbability Delta hblockWidth localLower
        hlocalLower hlocalUpper
      simpa [p] using h
    let events : ℕ → Set (ℕ → ℝ) := fun j =>
      driftedTubeBlockEvent (j * blockLength) blockLength lower Delta drift
    let filtration : ℕ → MeasurableSpace (ℕ → ℝ) := fun j =>
      ProbabilityTheory.sequencePrefixFiltration (E := ℝ) (j * blockLength)
    have hfiltrationMono : ∀ j, filtration j ≤ filtration (j + 1) := by
      intro j
      dsimp [filtration]
      apply (ProbabilityTheory.sequencePrefixFiltration (E := ℝ)).mono'
      have htime : j * blockLength + blockLength = (j + 1) * blockLength := by
        simp [Nat.succ_mul]
      rw [← htime]
      exact Nat.le_add_right _ _
    have hfiltrationAmbient : ∀ j,
        filtration j ≤ (inferInstance : MeasurableSpace (ℕ → ℝ)) := by
      intro j
      exact (ProbabilityTheory.sequencePrefixFiltration (E := ℝ)).le'
        (j * blockLength)
    have heventMeasurable : ∀ j,
        MeasurableSet[filtration (j + 1)] (events j) := by
      intro j
      have htime : (j + 1) * blockLength =
          j * blockLength + blockLength := by
        rw [Nat.add_mul, one_mul]
      change MeasurableSet[ProbabilityTheory.sequencePrefixFiltration
        (E := ℝ) ((j + 1) * blockLength)]
        (driftedTubeBlockEvent (j * blockLength) blockLength
          lower Delta drift)
      rw [htime]
      exact measurableSet_driftedTubeBlockEvent
        (j * blockLength) blockLength lower Delta drift
    have hconditional : ∀ j, ∀ᵐ increment ∂iidSequenceLaw ν,
        condExp (filtration j) (iidSequenceLaw ν)
          ((events j).indicator (fun _ => (1 : ℝ))) increment ≤ p := by
      intro j
      have h := iidSequenceLaw_condExp_driftedTubeBlockEvent_le_of_blockBound
        (lower := lower) (width := Delta) (drift := drift) (bound := p)
        ν (j * blockLength) blockLength (by positivity) hblockRate
      filter_upwards [h] with increment hbound
      simpa [filtration, events] using hbound
    have hprobabilityBlocks :
        (iidSequenceLaw ν).real
          (Drawdown.drawdownConditionalBlockIntersection events q) ≤ p ^ q :=
      Drawdown.measureReal_drawdownConditionalBlockIntersection_le_pow
        filtration hfiltrationMono hfiltrationAmbient events heventMeasurable
        (Real.exp_nonneg _) hconditional q
    have hblockPath (increment : ℕ → ℝ) (hpath :
        increment ∈ driftedTubeEvent horizon Delta drift lower) :
        ∀ j < q, increment ∈ events j := by
      intro j hj
      have hblockTime : (j + 1) * blockLength ≤ q * blockLength :=
        Nat.mul_le_mul_right blockLength (Nat.succ_le_of_lt hj)
      have hcount : q * blockLength ≤ horizon := by
        dsimp [q]
        exact Nat.div_mul_le_self _ _
      change ∀ k : Fin (blockLength + 1),
        lower + drift *
            ((j * blockLength + (k : ℕ) : ℕ) : ℝ) / Delta ^ 2 ≤
          Drawdown.drawdownPrefixSum
              (Combinatorics.Sequence.blockCoordinates 0 (j * blockLength)
                increment) +
            Drawdown.drawdownPartialBlockSum
              (Combinatorics.Sequence.blockCoordinates (j * blockLength)
                blockLength increment) k ∧
        Drawdown.drawdownPrefixSum
              (Combinatorics.Sequence.blockCoordinates 0 (j * blockLength)
                increment) +
            Drawdown.drawdownPartialBlockSum
              (Combinatorics.Sequence.blockCoordinates (j * blockLength)
                blockLength increment) k ≤
          lower + drift *
            ((j * blockLength + (k : ℕ) : ℕ) : ℝ) / Delta ^ 2 + Delta
      intro k
      have hposition := driftedTubeBlockPosition_eq
        (j * blockLength) blockLength increment k
      have hk : (k : ℕ) ≤ blockLength := Nat.le_of_lt_succ k.isLt
      have htime : j * blockLength + (k : ℕ) ≤ horizon := by
        calc
          j * blockLength + (k : ℕ) ≤ j * blockLength + blockLength :=
            Nat.add_le_add_left hk _
          _ = (j + 1) * blockLength := by simp [Nat.succ_mul]
          _ ≤ q * blockLength := hblockTime
          _ ≤ horizon := hcount
      by_cases htimeZero : j * blockLength + (k : ℕ) = 0
      · have htimeCast :
            ((j * blockLength + (k : ℕ) : ℕ) : ℝ) = 0 := by
          exact_mod_cast htimeZero
        have hpositionZero :
            Drawdown.drawdownPrefixSum
                (Combinatorics.Sequence.blockCoordinates 0 (j * blockLength)
                  increment) +
              Drawdown.drawdownPartialBlockSum
                (Combinatorics.Sequence.blockCoordinates (j * blockLength)
                  blockLength increment) k = 0 := by
          rw [hposition, htimeZero, AdditivePath.displacement_zero]
        constructor
        · rw [hpositionZero, htimeCast]
          simp only [mul_zero, zero_div, add_zero]
          linarith [hlower]
        · rw [hpositionZero, htimeCast]
          simp only [mul_zero, zero_div, add_zero]
          linarith [hupper]
      · have hpathAt := hpath (j * blockLength + (k : ℕ))
          (Nat.one_le_iff_ne_zero.mpr htimeZero) htime
        rw [← hposition] at hpathAt
        exact hpathAt
    have hsubset : driftedTubeEvent horizon Delta drift lower ⊆
        Drawdown.drawdownConditionalBlockIntersection events q := by
      intro increment hpath
      have hmembers : ∀ n ≤ q,
          increment ∈ Drawdown.drawdownConditionalBlockIntersection events n := by
        intro n
        induction n with
        | zero =>
            intro _
            simp [Drawdown.drawdownConditionalBlockIntersection]
        | succ n ih =>
            intro hn
            rw [Drawdown.drawdownConditionalBlockIntersection]
            exact ⟨ih (by omega), hblockPath increment hpath n (by omega)⟩
      exact hmembers q le_rfl
    have hprobability :
        (iidSequenceLaw ν).real (driftedTubeEvent horizon Delta drift lower) ≤
          (iidSequenceLaw ν).real
            (Drawdown.drawdownConditionalBlockIntersection events q) :=
      measureReal_mono hsubset (measure_ne_top (iidSequenceLaw ν) _)
    have hdivision : q * blockLength + horizon % blockLength = horizon := by
      dsimp [q]
      rw [Nat.mul_comm (horizon / blockLength) blockLength, Nat.add_comm]
      exact Nat.mod_add_div horizon blockLength
    have hremainder : horizon % blockLength < blockLength :=
      Nat.mod_lt _ hblockLengthPos
    have hremainderFraction :
        ((horizon % blockLength : ℕ) : ℝ) / Delta ^ 2 ≤ Delta ^ eta := by
      apply (div_le_iff₀ (sq_pos_of_pos hDeltaPos)).2
      calc
        ((horizon % blockLength : ℕ) : ℝ) ≤ (blockLength : ℝ) := by
          exact_mod_cast hremainder.le
        _ ≤ Delta ^ (2 + eta) := hblockLengthUpper
        _ = Delta ^ 2 * Delta ^ eta := hDeltaPower
        _ = Delta ^ eta * Delta ^ 2 := by ring
    have hremainderCost :
        d * (((horizon % blockLength : ℕ) : ℝ) / Delta ^ 2) ≤ Delta ^ v := by
      calc
        _ ≤ d * Delta ^ eta :=
          mul_le_mul_of_nonneg_left hremainderFraction hd.le
        _ = Delta ^ eta * d := by ring
        _ ≤ Delta ^ eta * Delta ^ (v - eta) :=
          mul_le_mul_of_nonneg_left hgrowthAt (by positivity)
        _ = Delta ^ v := by
          rw [← Real.rpow_add hDeltaPos]
          congr 1
          ring
    have hdivisionReal :
        ((q * blockLength : ℕ) : ℝ) +
            ((horizon % blockLength : ℕ) : ℝ) = (horizon : ℝ) := by
      exact_mod_cast hdivision
    have hexponent :
        -d * (((q * blockLength : ℕ) : ℝ) / Delta ^ 2) ≤
          Delta ^ v - d * ((horizon : ℝ) / Delta ^ 2) := by
      rw [show ((q * blockLength : ℕ) : ℝ) =
        (horizon : ℝ) - ((horizon % blockLength : ℕ) : ℝ) by linarith]
      have hidentity :
          -d * (((horizon : ℝ) - ((horizon % blockLength : ℕ) : ℝ)) /
              Delta ^ 2) =
            -d * ((horizon : ℝ) / Delta ^ 2) +
              d * (((horizon % blockLength : ℕ) : ℝ) / Delta ^ 2) := by
        ring
      rw [hidentity]
      linarith [hremainderCost]
    have hpower : p ^ q = Real.exp
        (-d * (((q * blockLength : ℕ) : ℝ) / Delta ^ 2)) := by
      calc
        p ^ q = Real.exp
            ((-d * ((blockLength : ℝ) / Delta ^ 2)) * (q : ℝ)) := by
          dsimp [p]
          rw [← Real.exp_nat_mul]
          congr 1
          ring
        _ = Real.exp (-d * (((q * blockLength : ℕ) : ℝ) / Delta ^ 2)) := by
          congr 1
          push_cast
          ring
    calc
      (iidSequenceLaw ν).real (driftedTubeEvent horizon Delta drift lower) ≤
          (iidSequenceLaw ν).real
            (Drawdown.drawdownConditionalBlockIntersection events q) := hprobability
      _ ≤ p ^ q := hprobabilityBlocks
      _ = Real.exp (-d * (((q * blockLength : ℕ) : ℝ) / Delta ^ 2)) := hpower
      _ ≤ Real.exp (Delta ^ v - d * ((horizon : ℝ) / Delta ^ 2)) :=
        Real.exp_le_exp.mpr hexponent

end ProbabilityTheory.RandomWalk.SmallDeviation
