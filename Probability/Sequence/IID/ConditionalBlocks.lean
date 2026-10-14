/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.Sequence.IID.StoppingTime
public import Probability.Independence.ConditionalIntegral

/-!
# Conditional lower bounds for independent coordinate blocks

The public theorems in this file are:

- `ProbabilityTheory.iidSequenceLaw_condExp_prefix_nextBlock`:
  for consecutive coordinate blocks $X,Y$ of an IID sequence,
  $\mathbb E[f(X,Y)\mid X]=\int f(X,y)\,d\mathcal L(Y)(y)$.
- `ProbabilityTheory.iidSequenceLaw_condExp_pairEvent_ge_of_sectionProbability`:
  a lower bound $p$ for every section $\mathbb P((x,Y)\in E)$ with
  $x\in G$ gives $\mathbb E[\mathbf1_E(X,Y)\mid X]\ge p$
  almost surely on $X\in G$.
- `ProbabilityTheory.measureReal_inter_ge_of_condExp_indicator_ge`:
  on a past-measurable event $A$, the conditional bound gives
  $\mathbb P(A\cap E)\ge p\mathbb P(A)$.
- `ProbabilityTheory.conditionalBlockIntersection`:
  the event $\bigcap_{j<n}E_j$ formed by successive blocks.
- `ProbabilityTheory.measureReal_conditionalBlockIntersection_ge_prod`:
  prefix-conditional bounds $\mathbb E[\mathbf1_{E_j}\mid\mathcal F_j]\ge p_j$
  on $\bigcap_{i<j}E_i$ give
  $\mathbb P(\bigcap_{j<n}E_j)\ge\prod_{j<n}p_j$.
- `ProbabilityTheory.measureReal_initialInterConditionalBlockIntersection_ge_mul_prod`:
  for an initial event $A$ observable before the first block, the same
  argument gives $\mathbb P(A\cap\bigcap_{j<n}E_j)\ge
  \mathbb P(A)\prod_{j<n}p_j$.

The last two statements are the generic conditional-expectation steps in
Wang Yiyang, *Asymptotic speed of the $N$-branching random walk with infinite
offspring*, Chapter 3, proof of Lemma 3.5, applied to the staircase blocks.
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

/-- Integrating a conditional probability lower bound over a measurable
past event gives the one-step reverse Markov product bound. -/
theorem measureReal_inter_ge_of_condExp_indicator_ge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {A E : Set Ω} (hA : MeasurableSet[m] A)
    (hE : MeasurableSet[mΩ] E)
    {p : ℝ}
    (hcond : ∀ᵐ ω ∂P, ω ∈ A →
      p ≤ condExp m P (E.indicator fun _ => (1 : ℝ)) ω) :
    p * P.real A ≤ P.real (A ∩ E) := by
  let f : Ω → ℝ := E.indicator fun _ => (1 : ℝ)
  have hf : Integrable f P :=
    (integrable_const (c := (1 : ℝ))).indicator hE
  have hAE : MeasurableSet[mΩ] (A ∩ E) := (hm A hA).inter hE
  have hindicator : (A ∩ E).indicator (fun _ => (1 : ℝ)) = A.indicator f := by
    funext ω
    by_cases hωA : ω ∈ A <;> by_cases hωE : ω ∈ E <;>
      simp [f, hωA, hωE]
  calc
    p * P.real A = ∫ ω in A, p ∂P := by
      rw [setIntegral_const, smul_eq_mul, mul_comm]
    _ ≤ ∫ ω in A, condExp m P f ω ∂P := by
      apply setIntegral_mono_on_ae
      · exact (integrable_const p).integrableOn
      · exact integrable_condExp.integrableOn
      · exact hm A hA
      · exact hcond
    _ = ∫ ω in A, f ω ∂P :=
      setIntegral_condExp hm hf hA
    _ = ∫ ω, (A ∩ E).indicator (fun _ => (1 : ℝ)) ω ∂P := by
      rw [hindicator, integral_indicator (hm A hA)]
    _ = P.real (A ∩ E) :=
      integral_indicator_one hAE

/-- The intersection of the first `n` successive block events. -/
def conditionalBlockIntersection
    {Ω : Type*} [MeasurableSpace Ω]
    (events : ℕ → Set Ω) : ℕ → Set Ω
  | 0 => Set.univ
  | n + 1 => conditionalBlockIntersection events n ∩ events n

/-- Iterating the reverse Markov inequality gives the product of the
conditional lower bounds for successive blocks. -/
theorem measureReal_conditionalBlockIntersection_ge_prod
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (filtration : ℕ → MeasurableSpace Ω)
    (hfiltrationMono : ∀ n, filtration n ≤ filtration (n + 1))
    (hfiltrationAmbient : ∀ n, filtration n ≤ mΩ)
    (events : ℕ → Set Ω)
    (heventMeasurable : ∀ n,
      MeasurableSet[filtration (n + 1)] (events n))
    (bounds : ℕ → ℝ) (hboundNonneg : ∀ n, 0 ≤ bounds n)
    (hconditional : ∀ n, ∀ᵐ ω ∂P,
      ω ∈ conditionalBlockIntersection events n →
        bounds n ≤ condExp (filtration n) P
          ((events n).indicator fun _ => (1 : ℝ)) ω)
    (n : ℕ) :
    (∏ j ∈ Finset.range n, bounds j) ≤
      P.real (conditionalBlockIntersection events n) := by
  have hmeas : ∀ k,
      MeasurableSet[filtration k]
        (conditionalBlockIntersection events k) := by
    intro k
    induction k with
    | zero => simp [conditionalBlockIntersection]
    | succ k ih =>
        rw [conditionalBlockIntersection]
        exact (hfiltrationMono k _ ih).inter (heventMeasurable k)
  induction n with
  | zero => simp [conditionalBlockIntersection, Measure.real]
  | succ k ih =>
      rw [conditionalBlockIntersection]
      calc
        (∏ j ∈ Finset.range (k + 1), bounds j) =
            bounds k * (∏ j ∈ Finset.range k, bounds j) := by
          rw [Finset.prod_range_succ]
          ring
        _ ≤ bounds k * P.real (conditionalBlockIntersection events k) :=
          mul_le_mul_of_nonneg_left ih (hboundNonneg k)
        _ ≤ P.real
            (conditionalBlockIntersection events k ∩ events k) :=
          measureReal_inter_ge_of_condExp_indicator_ge
            (filtration k) (hfiltrationAmbient k) (hmeas k)
            (hfiltrationAmbient (k + 1) (events k)
              (heventMeasurable k)) (hconditional k)

/-- The reverse Markov product with an initial event observable before the
first block. -/
theorem measureReal_initialInterConditionalBlockIntersection_ge_mul_prod
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (filtration : ℕ → MeasurableSpace Ω)
    (hfiltrationMono : ∀ n, filtration n ≤ filtration (n + 1))
    (hfiltrationAmbient : ∀ n, filtration n ≤ mΩ)
    (initial : Set Ω) (hinitial : MeasurableSet[filtration 0] initial)
    (events : ℕ → Set Ω)
    (heventMeasurable : ∀ n,
      MeasurableSet[filtration (n + 1)] (events n))
    (bounds : ℕ → ℝ) (hboundNonneg : ∀ n, 0 ≤ bounds n)
    (hconditional : ∀ n, ∀ᵐ ω ∂P,
      ω ∈ initial ∩ conditionalBlockIntersection events n →
        bounds n ≤ condExp (filtration n) P
          ((events n).indicator fun _ => (1 : ℝ)) ω)
    (n : ℕ) :
    P.real initial * (∏ j ∈ Finset.range n, bounds j) ≤
      P.real (initial ∩ conditionalBlockIntersection events n) := by
  have hmeas : ∀ k,
      MeasurableSet[filtration k]
        (initial ∩ conditionalBlockIntersection events k) := by
    intro k
    induction k with
    | zero => simpa [conditionalBlockIntersection] using hinitial
    | succ k ih =>
        rw [conditionalBlockIntersection, ← Set.inter_assoc]
        exact (hfiltrationMono k _ ih).inter (heventMeasurable k)
  induction n with
  | zero => simp [conditionalBlockIntersection]
  | succ k ih =>
      calc
        P.real initial * (∏ j ∈ Finset.range (k + 1), bounds j) =
            bounds k * (P.real initial *
              (∏ j ∈ Finset.range k, bounds j)) := by
          rw [Finset.prod_range_succ]
          ring
        _ ≤ bounds k *
            P.real (initial ∩ conditionalBlockIntersection events k) :=
          mul_le_mul_of_nonneg_left ih (hboundNonneg k)
        _ ≤ P.real
            ((initial ∩ conditionalBlockIntersection events k) ∩ events k) :=
          measureReal_inter_ge_of_condExp_indicator_ge
            (filtration k) (hfiltrationAmbient k) (hmeas k)
            (hfiltrationAmbient (k + 1) (events k)
              (heventMeasurable k)) (hconditional k)
        _ = P.real
            (initial ∩ conditionalBlockIntersection events (k + 1)) := by
          rw [conditionalBlockIntersection, Set.inter_assoc]

end ProbabilityTheory

end
