/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Sequence.Block
public import Probability.Sequence.Filtration
public import Probability.Sequence.IID
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Process.Stopping

/-!
# Fresh IID blocks after stopping times

For a canonical IID sequence, any measurable event of a finite block after a
discrete stopping time has the same conditional probability on every finite
stopping-time cell. Summing the cells gives an exact bounded-stopping-time
factorization. This layer is about IID sequences and does not assume that
coordinates are increments of a random walk.
-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory

variable {E : Type*} [MeasurableSpace E]

/-- A finite block of IID coordinates has the same law after deterministic
translation of its starting index. -/
theorem iidSequenceLaw_map_blockCoordinates
    (ν : Measure E) [IsProbabilityMeasure ν]
    (start length : ℕ) :
    (iidSequenceLaw ν).map (Combinatorics.Sequence.blockCoordinates (E := E) start length) =
      (iidSequenceLaw ν).map (Combinatorics.Sequence.blockCoordinates 0 length) := by
  rw [show Combinatorics.Sequence.blockCoordinates (E := E) start length =
      Combinatorics.Sequence.blockCoordinates 0 length ∘
        (fun sequence : ℕ → E => fun k => sequence (start + k)) by
    funext sequence k
    simp [Combinatorics.Sequence.blockCoordinates]]
  rw [← Measure.map_map (measurable_blockCoordinates 0 length)
    (measurable_sequenceNatAdd start)]
  rw [iidSequenceLaw_map_natAdd]

/-- Two consecutive finite coordinate blocks of an IID sequence are
independent. -/
theorem indepFun_blockCoordinates_blockCoordinates
    (ν : Measure E) [IsProbabilityMeasure ν]
    (start m n : ℕ) :
    IndepFun (Combinatorics.Sequence.blockCoordinates (E := E) start m)
      (Combinatorics.Sequence.blockCoordinates (start + m) n) (iidSequenceLaw ν) := by
  let S := Finset.Ico start (start + m)
  let T := Finset.Ico (start + m) (start + m + n)
  have hdisjoint : Disjoint S T := by
    rw [Finset.disjoint_left]
    intro k hkS hkT
    simp only [S, T, Finset.mem_Ico] at hkS hkT
    omega
  have htuple := (iidSequenceLaw_independent ν).indepFun_finset S T hdisjoint
    (fun k => measurable_pi_apply k)
  let left : (S → E) → (Fin m → E) := fun x k =>
    x ⟨start + k, by simp [S, k.isLt]⟩
  let right : (T → E) → (Fin n → E) := fun x k =>
    x ⟨start + m + k, by simp [T, k.isLt]⟩
  have hleftMeasurable : Measurable left := by
    rw [measurable_pi_iff]
    intro k
    exact measurable_pi_apply _
  have hrightMeasurable : Measurable right := by
    rw [measurable_pi_iff]
    intro k
    exact measurable_pi_apply _
  have h := htuple.comp hleftMeasurable hrightMeasurable
  convert h using 1 <;> funext sequence k <;>
    simp [left, right, Combinatorics.Sequence.blockCoordinates, Nat.add_assoc]

/-- A finite-coordinate event beginning at a stopping time. The value `⊤`
contributes no event. -/
def iidBlockEventAfter {length : ℕ}
    (τ : (ℕ → E) → WithTop ℕ) (event : Set (Fin length → E)) : Set (ℕ → E) :=
  ⋃ n : ℕ, {sequence | τ sequence = n} ∩
    (Combinatorics.Sequence.blockCoordinates n length) ⁻¹' event

/-- The stopping-time cell intersected with a measurable event of the next
finite IID block factors exactly. -/
theorem iidSequenceLaw_measure_stoppingTimeCell_inter_blockEvent_eq_mul
    (ν : Measure E) [IsProbabilityMeasure ν]
    (τ : (ℕ → E) → WithTop ℕ)
    (hτ : IsStoppingTime (sequencePrefixFiltration (E := E)) τ)
    (n length : ℕ) (event : Set (Fin length → E)) (hevent : MeasurableSet event) :
    (iidSequenceLaw ν)
        ({sequence | τ sequence = n} ∩
          (Combinatorics.Sequence.blockCoordinates n length) ⁻¹' event) =
      (iidSequenceLaw ν) {sequence | τ sequence = n} *
        (iidSequenceLaw ν)
          ((Combinatorics.Sequence.blockCoordinates 0 length) ⁻¹' event) := by
  let past := Combinatorics.Sequence.blockCoordinates (E := E) 0 n
  let future := Combinatorics.Sequence.blockCoordinates (E := E) n length
  have hindep := indepFun_blockCoordinates_blockCoordinates ν 0 n length
  have hpastEqPrefix : past = sequencePrefix (E := E) n := by
    funext sequence k
    simp [past, sequencePrefix, Combinatorics.Sequence.blockCoordinates]
  have hpastMeasurable : MeasurableSet[MeasurableSpace.comap past inferInstance]
      {sequence | τ sequence = n} := by
    rw [hpastEqPrefix, ← sequencePrefixFiltration_eq_comap_sequencePrefix]
    exact hτ.measurableSet_eq n
  obtain ⟨pastEvent, hpastEvent, hpastPreimage⟩ :=
    (MeasurableSpace.measurableSet_comap).1 hpastMeasurable
  have hfactor := hindep.measure_inter_preimage_eq_mul
    pastEvent event hpastEvent hevent
  have hfuturePreimage : future ⁻¹' event =
      (Combinatorics.Sequence.blockCoordinates n length) ⁻¹' event := rfl
  have hfutureProbability :
      (iidSequenceLaw ν) ((Combinatorics.Sequence.blockCoordinates n length) ⁻¹' event) =
        (iidSequenceLaw ν)
          ((Combinatorics.Sequence.blockCoordinates 0 length) ⁻¹' event) := by
    calc
      _ = ((iidSequenceLaw ν).map
          (Combinatorics.Sequence.blockCoordinates n length)) event :=
        (Measure.map_apply (μ := iidSequenceLaw ν)
          (measurable_blockCoordinates n length) hevent).symm
      _ = ((iidSequenceLaw ν).map
          (Combinatorics.Sequence.blockCoordinates 0 length)) event := by
        rw [iidSequenceLaw_map_blockCoordinates]
      _ = _ := (Measure.map_apply
        (μ := iidSequenceLaw ν) (measurable_blockCoordinates 0 length) hevent)
  have hcellFactor :
      (iidSequenceLaw ν)
          ({sequence | τ sequence = n} ∩
            (Combinatorics.Sequence.blockCoordinates n length) ⁻¹' event) =
        (iidSequenceLaw ν) {sequence | τ sequence = n} *
          (iidSequenceLaw ν)
            ((Combinatorics.Sequence.blockCoordinates n length) ⁻¹' event) := by
    simpa only [past, future, Nat.zero_add, ← hpastPreimage, hfuturePreimage]
      using hfactor
  calc
    _ = (iidSequenceLaw ν) {sequence | τ sequence = n} *
        (iidSequenceLaw ν)
          ((Combinatorics.Sequence.blockCoordinates n length) ⁻¹' event) := hcellFactor
    _ = (iidSequenceLaw ν) {sequence | τ sequence = n} *
        (iidSequenceLaw ν)
          ((Combinatorics.Sequence.blockCoordinates 0 length) ⁻¹' event) := by
            rw [hfutureProbability]

/-- On the event that a stopping time is bounded by `timeBound`, a measurable
finite-block event after the stopping time has exactly its deterministic IID
block probability, multiplied by the probability that the stopping time is
finite and within the bound. -/
theorem iidSequenceLaw_measure_boundedStoppingTime_iidBlockEventAfter_eq_mul
    (ν : Measure E) [IsProbabilityMeasure ν]
    (τ : (ℕ → E) → WithTop ℕ)
    (hτ : IsStoppingTime (sequencePrefixFiltration (E := E)) τ)
    (timeBound length : ℕ) (event : Set (Fin length → E))
    (hevent : MeasurableSet event) :
    (iidSequenceLaw ν)
        ({sequence | τ sequence ≤ timeBound} ∩ iidBlockEventAfter τ event) =
      (iidSequenceLaw ν) {sequence | τ sequence ≤ timeBound} *
        (iidSequenceLaw ν)
          ((Combinatorics.Sequence.blockCoordinates 0 length) ⁻¹' event) := by
  classical
  let μ := iidSequenceLaw ν
  let cell : Fin (timeBound + 1) → Set (ℕ → E) :=
    fun i => {sequence | τ sequence = i.val}
  let blockEvent : Fin (timeBound + 1) → Set (ℕ → E) :=
    fun i => (Combinatorics.Sequence.blockCoordinates i.val length) ⁻¹' event
  let pairEvent : Fin (timeBound + 1) → Set (ℕ → E) :=
    fun i => cell i ∩ blockEvent i
  have hcellMeasurable (i : Fin (timeBound + 1)) : MeasurableSet (cell i) :=
    (sequencePrefixFiltration (E := E)).le i.val _ (hτ.measurableSet_eq i.val)
  have hblockEventMeasurable (i : Fin (timeBound + 1)) :
      MeasurableSet (blockEvent i) :=
    hevent.preimage (measurable_blockCoordinates i.val length)
  have hpairMeasurable (i : Fin (timeBound + 1)) :
      MeasurableSet (pairEvent i) :=
    (hcellMeasurable i).inter (hblockEventMeasurable i)
  have hcellPairwise : Pairwise (fun i j => Disjoint (cell i) (cell j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro sequence hi hj
    apply hij
    apply Fin.ext
    exact WithTop.coe_injective (hi.symm.trans hj)
  have hpairPairwise : Pairwise (fun i j => Disjoint (pairEvent i) (pairEvent j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro sequence hi hj
    exact (Set.disjoint_left.mp (hcellPairwise hij)) hi.1 hj.1
  have hboundedCells :
      {sequence | τ sequence ≤ timeBound} = ⋃ i : Fin (timeBound + 1), cell i := by
    ext sequence
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, cell]
    constructor
    · intro hτbound
      by_cases htop : τ sequence = ⊤
      · rw [htop] at hτbound
        exfalso
        exact (not_le_of_gt (WithTop.coe_lt_top timeBound)) hτbound
      · obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp htop
        have hnle : n ≤ timeBound := by
          apply WithTop.coe_le_coe.mp
          simpa [hn] using hτbound
        exact ⟨⟨n, by omega⟩, hn.symm⟩
    · rintro ⟨i, hi⟩
      rw [hi]
      exact WithTop.coe_le_coe.mpr (Nat.le_of_lt_succ i.isLt)
  have hpairUnion :
      ({sequence | τ sequence ≤ timeBound} ∩ iidBlockEventAfter τ event) =
        ⋃ i : Fin (timeBound + 1), pairEvent i := by
    ext sequence
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq,
      iidBlockEventAfter, Set.mem_iUnion, pairEvent, cell, blockEvent]
    constructor
    · rintro ⟨hτbound, n, hτn, heventN⟩
      have hnle : n ≤ timeBound := by
        apply WithTop.coe_le_coe.mp
        simpa [hτn] using hτbound
      exact ⟨⟨n, by omega⟩, hτn, heventN⟩
    · rintro ⟨i, hτi, heventI⟩
      refine ⟨?_, i.val, hτi, heventI⟩
      rw [hτi]
      exact WithTop.coe_le_coe.mpr (Nat.le_of_lt_succ i.isLt)
  have hcellMeasure :
      μ {sequence | τ sequence ≤ timeBound} =
        ∑ i : Fin (timeBound + 1), μ (cell i) := by
    rw [hboundedCells, measure_iUnion hcellPairwise hcellMeasurable]
    simp
  have hpairMeasure :
      μ ({sequence | τ sequence ≤ timeBound} ∩ iidBlockEventAfter τ event) =
        ∑ i : Fin (timeBound + 1), μ (pairEvent i) := by
    rw [hpairUnion, measure_iUnion hpairPairwise hpairMeasurable]
    simp
  let futureProbability : ENNReal :=
    μ ((Combinatorics.Sequence.blockCoordinates 0 length) ⁻¹' event)
  have hfactor (i : Fin (timeBound + 1)) :
      μ (pairEvent i) = μ (cell i) * futureProbability := by
    simpa [μ, pairEvent, cell, futureProbability] using
      iidSequenceLaw_measure_stoppingTimeCell_inter_blockEvent_eq_mul
        ν τ hτ i.val length event hevent
  calc
    μ ({sequence | τ sequence ≤ timeBound} ∩ iidBlockEventAfter τ event) =
        ∑ i : Fin (timeBound + 1), μ (pairEvent i) := hpairMeasure
    _ = ∑ i : Fin (timeBound + 1), μ (cell i) * futureProbability := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hfactor i
    _ = (∑ i : Fin (timeBound + 1), μ (cell i)) * futureProbability := by
      rw [Finset.sum_mul]
    _ = μ {sequence | τ sequence ≤ timeBound} * futureProbability := by
      rw [← hcellMeasure]
    _ = _ := by rfl

/-- The event of a measurable finite block excursion after any discrete
stopping time has probability at most its deterministic block probability.
The event at `τ = ⊤` is empty by definition. -/
theorem iidSequenceLaw_measure_iidBlockEventAfter_le
    (ν : Measure E) [IsProbabilityMeasure ν]
    (τ : (ℕ → E) → WithTop ℕ)
    (hτ : IsStoppingTime (sequencePrefixFiltration (E := E)) τ)
    (length : ℕ) (event : Set (Fin length → E)) (hevent : MeasurableSet event) :
    (iidSequenceLaw ν) (iidBlockEventAfter τ event) ≤
      (iidSequenceLaw ν)
        ((Combinatorics.Sequence.blockCoordinates 0 length) ⁻¹' event) := by
  let μ := iidSequenceLaw ν
  let cell : ℕ → Set (ℕ → E) := fun n => {sequence | τ sequence = n}
  let blockEvent : ℕ → Set (ℕ → E) := fun n =>
    (Combinatorics.Sequence.blockCoordinates n length) ⁻¹' event
  have hcellMeasurable (n : ℕ) : MeasurableSet (cell n) :=
    (sequencePrefixFiltration (E := E)).le n _ (hτ.measurableSet_eq n)
  have hblockEventMeasurable (n : ℕ) : MeasurableSet (blockEvent n) :=
    hevent.preimage (measurable_blockCoordinates n length)
  have hcellPairwise : Pairwise (fun i j => Disjoint (cell i) (cell j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro sequence hi hj
    exact hij (WithTop.coe_injective (hi.symm.trans hj))
  have hunionCells : (⋃ n, cell n) = {sequence | τ sequence ≠ ⊤} := by
    ext sequence
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨n, hn⟩
      rw [hn]
      exact WithTop.coe_ne_top
    · intro hfinite
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hfinite
      exact ⟨n, hn.symm⟩
  have hcellTsum : ∑' n, μ (cell n) = μ {sequence | τ sequence ≠ ⊤} := by
    rw [← hunionCells]
    exact (measure_iUnion hcellPairwise hcellMeasurable).symm
  have hcellBound : ∑' n, μ (cell n) ≤ 1 := by
    calc
      ∑' n, μ (cell n) = μ {sequence | τ sequence ≠ ⊤} := hcellTsum
      _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)
      _ = 1 := measure_univ
  let futureProbability : ENNReal :=
    μ ((Combinatorics.Sequence.blockCoordinates 0 length) ⁻¹' event)
  have hfactor (n : ℕ) :
      μ (cell n ∩ blockEvent n) = μ (cell n) * futureProbability := by
    simpa [μ, cell, blockEvent, futureProbability] using
      iidSequenceLaw_measure_stoppingTimeCell_inter_blockEvent_eq_mul
        ν τ hτ n length event hevent
  calc
    μ (iidBlockEventAfter τ event) =
        μ (⋃ n, cell n ∩ blockEvent n) := by rfl
    _ ≤ ∑' n, μ (cell n ∩ blockEvent n) := measure_iUnion_le _
    _ = ∑' n, μ (cell n) * futureProbability := tsum_congr hfactor
    _ = (∑' n, μ (cell n)) * futureProbability := ENNReal.tsum_mul_right
    _ ≤ 1 * futureProbability :=
      mul_le_mul_of_nonneg_right hcellBound (by positivity)
    _ = μ ((Combinatorics.Sequence.blockCoordinates 0 length) ⁻¹' event) := by
      simp [futureProbability]

end ProbabilityTheory

end
