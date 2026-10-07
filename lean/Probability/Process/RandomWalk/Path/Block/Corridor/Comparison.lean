/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import MeasureTheory.Measure.FiniteCover
public import Probability.Process.RandomWalk.Path.Block.Law
public import Probability.Process.RandomWalk.Path.Block.Corridor.Measure

/-!
# Finite-cover comparison for block events

An event determined by a prefix can be extended by an independent next block.
When finitely many prefix events cover a target event and each corresponding
next-block event has a common positive mass, the endpoint-constrained event
inherits a quantitative lower bound. This is a general IID block result;
applications supply their own path geometry and bridge events.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory.RandomWalk

variable {E : Type*} [AddCommMonoid E] [MeasurableSpace E]
  [MeasurableAdd₂ E]

omit [AddCommMonoid E] [MeasurableAdd₂ E] in
/-- A finite family of prefix events covers `U`. If each prefix event can be
extended by its paired independent next-block event with conditional mass at
least `c`, and each such extension is contained in `T`, then `U` has mass at
most the finite-cover constant times the mass of `T`.

The bridge events are allowed to depend on the prefix cell. This is the
measure-theoretic form used for endpoint-window comparisons. -/
theorem iidSequenceLaw_measure_mul_le_card_mul_of_finite_block_cover
    (ν : Measure E) [IsProbabilityMeasure ν]
    {ι : Type*} (F : Finset ι) (prefixLength bridgeLength : ℕ)
    (U T : Set (ℕ → E))
    (A : ι → Set (Fin prefixLength → E))
    (B : ι → Set (Fin bridgeLength → E)) (c : ENNReal)
    (hA : ∀ i ∈ F, MeasurableSet (A i))
    (hB : ∀ i ∈ F, MeasurableSet (B i))
    (hcover : U ⊆ ⋃ i ∈ F,
      {increment : ℕ → E |
        Combinatorics.Sequence.blockCoordinates 0 prefixLength increment ∈ A i})
    (hbridge : ∀ i ∈ F,
      c ≤ iidSequenceLaw ν {increment : ℕ → E |
        Combinatorics.Sequence.blockCoordinates 0 bridgeLength increment ∈ B i})
    (hglue : ∀ i ∈ F,
      {increment : ℕ → E |
        Combinatorics.Sequence.blockCoordinates 0 prefixLength increment ∈ A i ∧
        Combinatorics.Sequence.blockCoordinates prefixLength bridgeLength increment ∈ B i}
        ⊆ T) :
    c * iidSequenceLaw ν U ≤ (F.card : ENNReal) * iidSequenceLaw ν T := by
  let prefixEvent : ι → Set (ℕ → E) := fun i increment =>
    Combinatorics.Sequence.blockCoordinates 0 prefixLength increment ∈ A i
  let bridgeEvent : ι → Set (ℕ → E) := fun i increment =>
    Combinatorics.Sequence.blockCoordinates prefixLength bridgeLength increment ∈ B i
  have hfactor : ∀ i ∈ F,
      c * iidSequenceLaw ν (prefixEvent i) ≤
        iidSequenceLaw ν (prefixEvent i ∩ bridgeEvent i) := by
    intro i hi
    have hproduct := iidSequenceLaw_measure_inter_prefix_nextBlock ν
      prefixLength bridgeLength (A i) (B i) (hA i hi) (hB i hi)
    have hmass := hbridge i hi
    have hmul := mul_le_mul_left hmass
      (iidSequenceLaw ν (prefixEvent i))
    have hbound : c * iidSequenceLaw ν (prefixEvent i) ≤
        iidSequenceLaw ν (prefixEvent i) *
          iidSequenceLaw ν {increment : ℕ → E |
            Combinatorics.Sequence.blockCoordinates 0 bridgeLength increment ∈ B i} := by
      calc
        c * iidSequenceLaw ν (prefixEvent i) ≤
            iidSequenceLaw ν {increment : ℕ → E |
              Combinatorics.Sequence.blockCoordinates 0 bridgeLength increment ∈ B i} *
                iidSequenceLaw ν (prefixEvent i) := hmul
        _ = iidSequenceLaw ν (prefixEvent i) *
            iidSequenceLaw ν {increment : ℕ → E |
              Combinatorics.Sequence.blockCoordinates 0 bridgeLength increment ∈ B i} :=
          mul_comm _ _
    have hset : prefixEvent i ∩ bridgeEvent i =
        {increment : ℕ → E |
          Combinatorics.Sequence.blockCoordinates 0 prefixLength increment ∈ A i ∧
          Combinatorics.Sequence.blockCoordinates prefixLength bridgeLength increment ∈ B i} := by
      ext increment
      rfl
    rw [hset]
    simpa [prefixEvent] using hbound.trans_eq hproduct.symm
  apply MeasureTheory.measure_mul_le_card_mul_of_finite_cover
    (iidSequenceLaw ν) F U T prefixEvent bridgeEvent c hcover
      hfactor hglue

end ProbabilityTheory.RandomWalk

end
