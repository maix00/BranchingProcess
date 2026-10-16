/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Sequence.IID.StoppingTime
public import Probability.Independence.ConditionalIntegral
public import Probability.Process.Filtration.ConditionalBlocks

/-!
# Conditional bounds for independent coordinate blocks

The public theorems in this file are:

- `ProbabilityTheory.iidSequenceLaw_condExp_prefix_nextBlock`:
  for consecutive coordinate blocks $X,Y$ of an IID sequence,
  $\mathbb E[f(X,Y)\mid X]=\int f(X,y)\,d\mathcal L(Y)(y)$.
- `ProbabilityTheory.iidSequenceLaw_condExp_pairEvent_le_of_sectionProbability`:
  a uniform section bound $\mathbb P((x,Y)\in E)\le p$ gives
  $\mathbb E[\mathbf1_E(X,Y)\mid X]\le p$ almost surely.
- `ProbabilityTheory.iidSequenceLaw_condExp_pairEvent_ge_of_sectionProbability`:
  a lower bound $p$ for every section $\mathbb P((x,Y)\in E)$ with
  $x\in G$ gives $\mathbb E[\mathbf1_E(X,Y)\mid X]\ge p$
  almost surely on $X\in G$.

General conditional-probability integration and finite block-intersection
recursions are in
`Probability.Process.Filtration.ConditionalBlocks`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory

/-- Conditioning on a finite IID prefix integrates the next block against
its independent marginal law. -/
theorem iidSequenceLaw_condExp_prefix_nextBlock
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (start length : ℕ)
    {f : (Fin start → ℝ) × (Fin length → ℝ) → ℝ}
    (hf : StronglyMeasurable f)
    (hfi : Integrable
      (fun increment : ℕ → ℝ =>
        f (Combinatorics.Sequence.blockCoordinates 0 start increment,
          Combinatorics.Sequence.blockCoordinates start length increment))
      (iidSequenceLaw ν)) :
    condExp
        (MeasurableSpace.comap
          (Combinatorics.Sequence.blockCoordinates 0 start) inferInstance)
        (iidSequenceLaw ν)
        (fun increment : ℕ → ℝ =>
          f (Combinatorics.Sequence.blockCoordinates 0 start increment,
            Combinatorics.Sequence.blockCoordinates start length increment))
      =ᵐ[iidSequenceLaw ν]
        fun increment =>
          ∫ block, f
            (Combinatorics.Sequence.blockCoordinates 0 start increment, block)
            ∂(iidSequenceLaw ν).map
              (Combinatorics.Sequence.blockCoordinates start length) := by
  have hblock : Measurable
      (Combinatorics.Sequence.blockCoordinates (E := ℝ) (0 + start) length) := by
    simpa only [Nat.zero_add] using
      (measurable_blockCoordinates (E := ℝ) start length)
  have hfi' : Integrable
      (fun sample : ℕ → ℝ =>
        f (Combinatorics.Sequence.blockCoordinates 0 start sample,
          Combinatorics.Sequence.blockCoordinates (0 + start) length sample))
      (iidSequenceLaw ν) := by
    simpa only [Nat.zero_add] using hfi
  have hcond := (indepFun_blockCoordinates_blockCoordinates ν 0 start length)
    |>.condExp_prod_ae_eq_integral_map
      (measurable_blockCoordinates (E := ℝ) 0 start)
      hblock hf hfi'
  simpa only [Nat.zero_add] using hcond

/-- Every section of a measurable prefix/next-block event has probability
at least `bound`, so its indicator has conditional expectation at least
`bound` given the prefix. -/
theorem iidSequenceLaw_condExp_pairEvent_ge_of_sectionProbability
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (start length : ℕ)
    (E : Set ((Fin start → ℝ) × (Fin length → ℝ)))
    (hE : MeasurableSet E) (good : Set (Fin start → ℝ))
    {bound : ℝ}
    (hsections : ∀ past,
      past ∈ good → bound ≤ ((iidSequenceLaw ν).map
        (Combinatorics.Sequence.blockCoordinates start length)).real
        {block | (past, block) ∈ E}) :
    ∀ᵐ increment ∂iidSequenceLaw ν,
      Combinatorics.Sequence.blockCoordinates 0 start increment ∈ good →
        bound ≤
        condExp
          (MeasurableSpace.comap
            (Combinatorics.Sequence.blockCoordinates 0 start) inferInstance)
          (iidSequenceLaw ν)
          (fun increment => E.indicator (fun _ => (1 : ℝ))
            (Combinatorics.Sequence.blockCoordinates 0 start increment,
              Combinatorics.Sequence.blockCoordinates start length increment))
          increment := by
  let pastBlock : (ℕ → ℝ) → Fin start → ℝ :=
    Combinatorics.Sequence.blockCoordinates 0 start
  let nextBlock : (ℕ → ℝ) → Fin length → ℝ :=
    Combinatorics.Sequence.blockCoordinates start length
  let pair : (ℕ → ℝ) → (Fin start → ℝ) × (Fin length → ℝ) :=
    fun increment => (pastBlock increment, nextBlock increment)
  let f : (Fin start → ℝ) × (Fin length → ℝ) → ℝ :=
    E.indicator (fun _ => (1 : ℝ))
  have hpairMeasurable : Measurable pair := by
    exact (measurable_blockCoordinates 0 start).prodMk
      (measurable_blockCoordinates start length)
  have hpreimage : MeasurableSet (pair ⁻¹' E) := hE.preimage hpairMeasurable
  have hf : StronglyMeasurable f := stronglyMeasurable_const.indicator hE
  have hfi : Integrable (fun increment => f (pair increment))
      (iidSequenceLaw ν) :=
    (integrable_const (c := (1 : ℝ))).indicator hpreimage
  have hcond := iidSequenceLaw_condExp_prefix_nextBlock
    ν start length hf hfi
  have hsectionIntegral (x : Fin start → ℝ) :
      (∫ block, f (x, block) ∂
        (iidSequenceLaw ν).map nextBlock) =
        ((iidSequenceLaw ν).map nextBlock).real
          {block | (x, block) ∈ E} := by
    let sectionEvent : Set (Fin length → ℝ) := {block | (x, block) ∈ E}
    have hsectionMeasurable : MeasurableSet sectionEvent :=
      hE.preimage (measurable_const.prodMk measurable_id)
    have hfunction : (fun block => f (x, block)) =
        sectionEvent.indicator (fun _ => (1 : ℝ)) := by
      funext block
      simp [f, sectionEvent, Set.indicator]
    rw [hfunction]
    change (∫ block, sectionEvent.indicator (fun _ => (1 : ℝ)) block
        ∂(iidSequenceLaw ν).map nextBlock) =
      ((iidSequenceLaw ν).map nextBlock).real sectionEvent
    rw [integral_indicator_const (e := (1 : ℝ)) hsectionMeasurable,
      smul_eq_mul, mul_one]
  filter_upwards [hcond] with increment hincrement hgood
  rw [hincrement]
  have hsection := hsectionIntegral
    (Combinatorics.Sequence.blockCoordinates 0 start increment)
  rw [hsection]
  exact hsections
    (Combinatorics.Sequence.blockCoordinates 0 start increment) hgood

/-- A uniform bound on every section of a measurable event in
`prefix × nextBlock` gives the corresponding conditional-probability bound.
The conditional expectation is evaluated by integrating the next block
against its IID law, as in Wang Yiyang, *Asymptotic speed of the
$N$-branching random walk with infinite offspring*, Chapter 3, Lemma 3.3. -/
theorem iidSequenceLaw_condExp_pairEvent_le_of_sectionProbability
    (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (start length : ℕ)
    (E : Set ((Fin start → ℝ) × (Fin length → ℝ)))
    (hE : MeasurableSet E) {bound : ℝ}
    (hsections : ∀ past,
      ((iidSequenceLaw ν).map
        (Combinatorics.Sequence.blockCoordinates start length)).real
        {block | (past, block) ∈ E} ≤ bound) :
    ∀ᵐ increment ∂iidSequenceLaw ν,
      condExp
        (MeasurableSpace.comap
          (Combinatorics.Sequence.blockCoordinates 0 start) inferInstance)
        (iidSequenceLaw ν)
        (fun increment => E.indicator (fun _ => (1 : ℝ))
          (Combinatorics.Sequence.blockCoordinates 0 start increment,
            Combinatorics.Sequence.blockCoordinates start length increment))
        increment ≤ bound := by
  let pastBlock : (ℕ → ℝ) → Fin start → ℝ :=
    Combinatorics.Sequence.blockCoordinates 0 start
  let nextBlock : (ℕ → ℝ) → Fin length → ℝ :=
    Combinatorics.Sequence.blockCoordinates start length
  let pair : (ℕ → ℝ) → (Fin start → ℝ) × (Fin length → ℝ) :=
    fun increment => (pastBlock increment, nextBlock increment)
  let f : (Fin start → ℝ) × (Fin length → ℝ) → ℝ :=
    E.indicator (fun _ => (1 : ℝ))
  have hpairMeasurable : Measurable pair := by
    exact (measurable_blockCoordinates 0 start).prodMk
      (measurable_blockCoordinates start length)
  have hpreimage : MeasurableSet (pair ⁻¹' E) := hE.preimage hpairMeasurable
  have hf : StronglyMeasurable f := stronglyMeasurable_const.indicator hE
  have hfi : Integrable (fun increment => f (pair increment))
      (iidSequenceLaw ν) :=
    (integrable_const (c := (1 : ℝ))).indicator hpreimage
  have hcond := ProbabilityTheory.iidSequenceLaw_condExp_prefix_nextBlock
    ν start length hf hfi
  have hsectionIntegral (x : Fin start → ℝ) :
      (∫ block, f (x, block) ∂
        (iidSequenceLaw ν).map nextBlock) =
        ((iidSequenceLaw ν).map nextBlock).real
          {block | (x, block) ∈ E} := by
    let sectionEvent : Set (Fin length → ℝ) := {block | (x, block) ∈ E}
    have hsectionMeasurable : MeasurableSet sectionEvent :=
      hE.preimage (measurable_const.prodMk measurable_id)
    have hfunction : (fun block => f (x, block)) =
        sectionEvent.indicator (fun _ => (1 : ℝ)) := by
      funext block
      simp [f, sectionEvent, Set.indicator]
    rw [hfunction]
    change (∫ block, sectionEvent.indicator (fun _ => (1 : ℝ)) block
        ∂(iidSequenceLaw ν).map nextBlock) =
      ((iidSequenceLaw ν).map nextBlock).real sectionEvent
    rw [integral_indicator_const (e := (1 : ℝ)) hsectionMeasurable,
      smul_eq_mul, mul_one]
  filter_upwards [hcond] with increment hincrement
  rw [hincrement]
  have hsection := hsectionIntegral
    (Combinatorics.Sequence.blockCoordinates 0 start increment)
  rw [hsection]
  exact hsections (Combinatorics.Sequence.blockCoordinates 0 start increment)

end ProbabilityTheory

end
