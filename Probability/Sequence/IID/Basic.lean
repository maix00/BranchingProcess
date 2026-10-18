/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.MeasureTheory.Constructions.Pi
public import Probability.Sequence.Block

/-!
# Canonical laws of i.i.d. sequences

The countable product of a probability measure is the canonical law of an
i.i.d. sequence.  This construction is independent of random walks and
branching.
Write $\mu=\texttt{iidSequenceLaw}\,\nu$ and $X_k(\omega)=\omega(k)$ for
the canonical coordinate process.

The public interfaces include:

- `iidSequenceLaw`: the law $\nu^{\mathbb N}$ on infinite sequences, with its probability-measure instance when $\nu$ is a probability measure.
- `iidSequenceLaw_map_apply` and `iidSequenceLaw_map_finPrefix`: the
  one-coordinate law and the finite product law of the first $n$ coordinates.
- `iidSequenceLaw_map_blockCoordinates` and
  `iidSequenceLaw_measure_blockCoordinates_preimage_eq_pi`: for every start
  $s$ and length $n$, the block $(X_{s+i})_{i<n}$ has law $\nu^n$. For
  measurable $A\subseteq(\texttt{Fin}\,n\to E)$,
  $\mu((\texttt{blockCoordinates}\,s\,n)^{-1}(A))
  =\operatorname{Measure.pi}(i\mapsto\nu)(A)$, where
  $\mu=\texttt{iidSequenceLaw}\,\nu$.
- `iidSequenceLaw_independent`, `iidSequenceLaw_map_coordinatewise`, and
  `iidSequenceLaw_map_natAdd`: coordinate independence, coordinatewise
  pushforward, and invariance under deleting a finite prefix.
- `iidSequenceLaw_measure_forall_lt` and
  `iidSequenceLaw_measure_exists_mem_le`: finite-coordinate product and
  union-bound estimates.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

/-- Canonical sequence law with identical independent coordinates of law
`ν`. -/
noncomputable def iidSequenceLaw {X : Type*} [MeasurableSpace X]
    (ν : Measure X) : Measure (ℕ → X) :=
  Measure.infinitePi fun _ : ℕ => ν

noncomputable instance iidSequenceLaw.instIsProbabilityMeasure
    {X : Type*} [MeasurableSpace X] (ν : Measure X)
    [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (iidSequenceLaw ν) := by
  unfold iidSequenceLaw
  infer_instance

theorem iidSequenceLaw_map_apply {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (n : ℕ) :
    (iidSequenceLaw ν).map (fun sequence => sequence n) = ν := by
  unfold iidSequenceLaw
  exact Measure.infinitePi_map_eval (fun _ : ℕ => ν) n

/-- The first `n` coordinates of the canonical IID sequence have the
finite product law. -/
theorem iidSequenceLaw_map_finPrefix
    {E : Type*} [MeasurableSpace E] (ν : Measure E)
    [IsProbabilityMeasure ν] (n : ℕ) :
    (iidSequenceLaw ν).map (fun x : ℕ → E => fun i : Fin n => x i.val) =
      Measure.pi (fun _ : Fin n => ν) := by
  unfold iidSequenceLaw
  rw [Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ => ν) (f := fun i : Fin n => i.val)
    (fun _ _ h => Fin.val_injective h)]
  rw [Measure.infinitePi_eq_pi]

theorem iidSequenceLaw_independent {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] :
    iIndepFun (fun n (sequence : ℕ → X) => sequence n)
      (iidSequenceLaw ν) := by
  unfold iidSequenceLaw
  simpa using (iIndepFun_infinitePi
    (P := fun _ : ℕ => ν) (X := fun _ : ℕ => id)
    (fun _ => measurable_id))

/-- The probability that the first `n` coordinates of a canonical IID
sequence all belong to one measurable set is the `n`-th power of its
one-coordinate mass. -/
theorem iidSequenceLaw_measure_forall_lt
    {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (s : Set X) (hs : MeasurableSet s) (n : ℕ) :
    iidSequenceLaw ν {sequence | ∀ k < n, sequence k ∈ s} = (ν s) ^ n := by
  let indices := Finset.range n
  let restricted : Set (∀ _i : indices, X) :=
    Set.univ.pi fun _ => s
  have hrestricted : MeasurableSet restricted :=
    MeasurableSet.pi Set.countable_univ fun _ _ => hs
  have hevent : {sequence : ℕ → X | ∀ k < n, sequence k ∈ s} =
      MeasureTheory.cylinder indices restricted := by
    ext sequence
    simp [MeasureTheory.mem_cylinder, restricted, indices]
  rw [hevent]
  change Measure.infinitePi (fun _ : ℕ => ν)
      (MeasureTheory.cylinder indices restricted) = _
  calc
    _ = Measure.pi (fun _i : indices => ν) restricted :=
      Measure.infinitePi_cylinder (fun _ : ℕ => ν) hrestricted
    _ = _ := by simp [restricted, indices, Measure.pi_pi]

/-- Applying the same measurable map to every coordinate of a canonical
i.i.d. sequence gives the canonical i.i.d. law of the pushed-forward
one-coordinate law. -/
theorem iidSequenceLaw_map_coordinatewise
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (f : X → Y) (hf : Measurable f) :
    (iidSequenceLaw ν).map (fun sequence n => f (sequence n)) =
      iidSequenceLaw (ν.map f) := by
  have hindep : iIndepFun
      (fun i (sequence : ℕ → X) => f (sequence i))
      (iidSequenceLaw ν) :=
    (iidSequenceLaw_independent ν).comp (fun _ => f) (fun _ => hf)
  calc
    (iidSequenceLaw ν).map (fun sequence n => f (sequence n)) =
        Measure.infinitePi (fun i =>
          (iidSequenceLaw ν).map (fun sequence => f (sequence i))) := by
      simpa [Function.comp_def] using
        hindep.map_fun_eq_infinitePi_map
          (fun i => hf.comp (measurable_pi_apply i))
    _ = Measure.infinitePi (fun _ : ℕ => ν.map f) := by
      congr 1
      funext i
      calc
        (iidSequenceLaw ν).map (fun sequence => f (sequence i)) =
            ((iidSequenceLaw ν).map fun sequence => sequence i).map f := by
          simpa [Function.comp_def] using
            (Measure.map_map hf (measurable_pi_apply i)).symm
        _ = ν.map f := by rw [iidSequenceLaw_map_apply]
    _ = iidSequenceLaw (ν.map f) := rfl

/-- Dropping any finite prefix from a canonical i.i.d. sequence leaves its
law unchanged. -/
theorem iidSequenceLaw_map_natAdd {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν] (offset : ℕ) :
    (iidSequenceLaw ν).map (fun sequence n => sequence (offset + n)) =
      iidSequenceLaw ν := by
  unfold iidSequenceLaw
  simpa using Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ => ν) (f := fun n => offset + n)
    (fun _ _ hij => Nat.add_left_cancel hij)

/-- A finite block of IID coordinates has the same law after translating
its starting index. -/
theorem iidSequenceLaw_map_blockCoordinates
    {E : Type*} [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (start length : ℕ) :
    (iidSequenceLaw ν).map
        (Combinatorics.Sequence.blockCoordinates (E := E) start length) =
      (iidSequenceLaw ν).map
        (Combinatorics.Sequence.blockCoordinates (E := E) 0 length) := by
  rw [show Combinatorics.Sequence.blockCoordinates (E := E) start length =
      Combinatorics.Sequence.blockCoordinates 0 length ∘
        (fun sequence : ℕ → E => fun k => sequence (start + k)) by
    funext sequence k
    simp [Combinatorics.Sequence.blockCoordinates]]
  have hshift : Measurable
      (fun sequence : ℕ → E => fun k => sequence (start + k)) := by
    rw [measurable_pi_iff]
    exact fun k => measurable_pi_apply (start + k)
  rw [← Measure.map_map (measurable_blockCoordinates 0 length) hshift]
  rw [iidSequenceLaw_map_natAdd]

/-- A measurable event of a finite IID block has the corresponding
finite-product probability, independently of the block's starting index. -/
theorem iidSequenceLaw_measure_blockCoordinates_preimage_eq_pi
    {E : Type*} [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν]
    (start length : ℕ) (A : Set (Fin length → E))
    (hA : MeasurableSet A) :
    iidSequenceLaw ν
        ((Combinatorics.Sequence.blockCoordinates (E := E) start length) ⁻¹' A) =
      Measure.pi (fun _ : Fin length => ν) A := by
  calc
    _ = ((iidSequenceLaw ν).map
        (Combinatorics.Sequence.blockCoordinates start length)) A :=
      (Measure.map_apply (measurable_blockCoordinates start length) hA).symm
    _ = ((iidSequenceLaw ν).map
        (Combinatorics.Sequence.blockCoordinates 0 length)) A := by
      rw [iidSequenceLaw_map_blockCoordinates]
    _ = Measure.pi (fun _ : Fin length => ν) A := by
      have hcoords :
          Combinatorics.Sequence.blockCoordinates (E := E) 0 length =
            (fun sequence : ℕ → E => fun i : Fin length => sequence i.val) := by
        funext sequence i
        simp [Combinatorics.Sequence.blockCoordinates]
      rw [hcoords, iidSequenceLaw_map_finPrefix]

/-- Union bound for the event that one of the first `n` coordinates of a
canonical IID sequence belongs to a measurable set. -/
theorem iidSequenceLaw_measure_exists_mem_le
    {X : Type*} [MeasurableSpace X]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (s : Set X) (hs : MeasurableSet s) (n : ℕ) :
    iidSequenceLaw ν {sequence | ∃ k ∈ Finset.range n, sequence k ∈ s} ≤
      (n : ℕ) * ν s := by
  let event : ℕ → Set (ℕ → X) := fun k => {sequence | sequence k ∈ s}
  have hevent : {sequence : ℕ → X |
      ∃ k ∈ Finset.range n, sequence k ∈ s} =
      ⋃ k ∈ Finset.range n, event k := by
    ext sequence
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, event]
    aesop
  rw [hevent]
  calc
    iidSequenceLaw ν (⋃ k ∈ Finset.range n, event k) ≤
        ∑ k ∈ Finset.range n, iidSequenceLaw ν (event k) :=
      measure_biUnion_finset_le _ _
    _ = ∑ _k ∈ Finset.range n, ν s := by
      apply Finset.sum_congr rfl
      intro k hk
      change iidSequenceLaw ν
          ((fun sequence : ℕ → X => sequence k) ⁻¹' s) = ν s
      calc
        _ = (iidSequenceLaw ν).map (fun sequence => sequence k) s :=
          (Measure.map_apply (measurable_pi_apply k) hs).symm
        _ = ν s := by rw [iidSequenceLaw_map_apply ν k]
    _ = (n : ℕ) * ν s := by simp

end ProbabilityTheory

end
