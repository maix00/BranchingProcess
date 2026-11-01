/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Probability.BranchingRandomWalk.Population.Candidates.MultiRoot
public import Combinatorics.BranchingWalk.Step.Basic
public import Combinatorics.BranchingWalk.Step.Ordering.Monotone
public import Mathlib.Data.Prod.Lex

/-!
# The position/address ordering on candidates

The key is particle position followed by a deterministic encoding of its
labelled address. The latter breaks ties without reading additional marks.
This file defines the key and proves that the key is injective, that ordered
siblings are ordered correctly, and that a comparison between two candidates
is measurable. The leftmost selection built on this order is in
`Candidates/Leftmost.lean`. Only a linear ordered additive commutative monoid
is used, so the position type is a parameter rather than `ℝ`.

## Public declarations

- `ProbabilityTheory.BranchingRandomWalk.labelledPosition` evaluates the
  position of an addressed particle, and `ProbabilityTheory.BranchingRandomWalk.labelledPosition_child` gives the
  additive position formula after appending a child slot.
- `ProbabilityTheory.BranchingRandomWalk.addressTieKey` encodes parent, slot,
  and full address; `ProbabilityTheory.BranchingRandomWalk.childAddress_tieKey_lt` orders siblings by slot.
- `ProbabilityTheory.BranchingRandomWalk.candidateKey` is the lexicographic pair of position and tie key, while
  `ProbabilityTheory.BranchingRandomWalk.candidateEarlier` is its strict order. The theorem
  `ProbabilityTheory.BranchingRandomWalk.candidateEarlier_iff_key_lt` identifies these two relations, and
  `ProbabilityTheory.BranchingRandomWalk.candidateKey_injective` shows distinct addresses have distinct keys.
- `ProbabilityTheory.BranchingRandomWalk.labelledPosition_measurable` and `ProbabilityTheory.BranchingRandomWalk.candidateEarlier_measurableSet` prove
  measurability of positions and pairwise candidate comparisons.
- `ProbabilityTheory.BranchingRandomWalk.candidateEarlier_ordered_siblings` states that under the ordered-step
  condition, every earlier realized sibling precedes a later realized
  sibling, including when their positions tie.

For fixed increments and field, the position/address key orders candidates
first by position and then by an address tie key. Appending a child adds its
mark to the parent position:

\[\begin{aligned}
\operatorname{labelledPosition}(\operatorname{childAddress}(p,j))
&=\operatorname{labelledPosition}(p)+\operatorname{value}'(\omega(p),j),\\
\operatorname{candidateKey}(p)
&=(\operatorname{labelledPosition}(p),\operatorname{addressTieKey}(p)),\\
\operatorname{candidateEarlier}(p,q)&\Longleftrightarrow
  \operatorname{candidateKey}(p)<_{\mathrm{lex}}\operatorname{candidateKey}(q).
\end{aligned}\]

-/

open MeasureTheory

@[expose] public section

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory



variable {X : Type*}

def labelledPosition {m : ℕ} [AddCommMonoid X]
    (x : Fin m → X) (ω : FiniteRootStepField m ℕ X)
    (p : RootAddress m ℕ) : X :=
  RootIndexed.position x id ω p.1 p.2

theorem labelledPosition_measurable {m n : ℕ}
    [MeasurableSpace X] [AddCommMonoid X] [MeasurableAdd₂ X]
    (x : Fin m → X) (p : RootAddress m ℕ) (hp : p.2.length = n) :
    Measurable[multiRootStepFiltration (m := m) (X := X) n]
      (fun ω : FiniteRootStepField m ℕ X => labelledPosition x ω p) := by
  subst n
  exact RootIndexed.position_measurable x id measurable_id p.1 p.2

/-- Tie key: parent identity first, then child-slot number, then the full
address as a final injective fallback. Earlier slots of one parent win ties. -/
def addressTieKey {m : ℕ} (p : RootAddress m ℕ) :
    ℕ ×ₗ (ℕ ×ₗ ℕ) :=
  toLex (Encodable.encode (p.1, p.2.dropLast),
    toLex (p.2.getLast?.getD 0, Encodable.encode p))

theorem childAddress_tieKey_lt {m : ℕ}
    (p : RootAddress m ℕ) {i j : ℕ} (hij : i < j) :
    addressTieKey (RootIndexed.childAddress p i) <
      addressTieKey (RootIndexed.childAddress p j) := by
  simp [addressTieKey, RootIndexed.childAddress, Prod.Lex.lt_iff, hij]

/-- Strict rank order: position first, then the structured tie key. -/
def candidateEarlier {m : ℕ} [AddCommMonoid X] [LinearOrder X]
    (x : Fin m → X) (ω : FiniteRootStepField m ℕ X)
    (p q : RootAddress m ℕ) : Prop :=
  labelledPosition x ω p < labelledPosition x ω q ∨
    (labelledPosition x ω p = labelledPosition x ω q ∧
      addressTieKey p < addressTieKey q)

def candidateKey {m : ℕ} [AddCommMonoid X] [LinearOrder X]
    (x : Fin m → X) (ω : FiniteRootStepField m ℕ X)
    (p : RootAddress m ℕ) : X ×ₗ (ℕ ×ₗ (ℕ ×ₗ ℕ)) :=
  toLex (labelledPosition x ω p, addressTieKey p)

theorem candidateEarlier_iff_key_lt {m : ℕ} [AddCommMonoid X] [LinearOrder X]
    (x : Fin m → X) (ω : FiniteRootStepField m ℕ X) (p q : RootAddress m ℕ) :
    candidateEarlier x ω p q ↔
      candidateKey x ω p < candidateKey x ω q := by
  simp [candidateEarlier, candidateKey, Prod.Lex.lt_iff]

theorem candidateKey_injective {m : ℕ} [AddCommMonoid X] [LinearOrder X]
    (x : Fin m → X) (ω : FiniteRootStepField m ℕ X) :
    Function.Injective (candidateKey x ω) := by
  intro p q hpq
  have htie : addressTieKey p = addressTieKey q :=
    congrArg (fun z : X ×ₗ (ℕ ×ₗ (ℕ ×ₗ ℕ)) => (ofLex z).2) hpq
  have hcode : Encodable.encode p = Encodable.encode q :=
    congrArg (fun z : ℕ ×ₗ (ℕ ×ₗ ℕ) =>
      (ofLex ((ofLex z).2)).2) htie
  exact Encodable.encode_injective hcode

theorem labelledPosition_child {m : ℕ} [AddCommMonoid X]
    (x : Fin m → X) (ω : FiniteRootStepField m ℕ X)
    (p : RootAddress m ℕ) (j : ℕ) :
    labelledPosition x ω (RootIndexed.childAddress p j) =
      labelledPosition x ω p +
        value' (ω p.1 p.2) j := by
  change RootIndexed.position x id ω p.1 (p.2 ++ [j]) =
    RootIndexed.position x id ω p.1 p.2 + value' (ω p.1 p.2) j
  simpa using RootIndexed.position_append_singleton x id ω p.1 p.2 j

/-- Under ordered child marks, earlier siblings precede a realized
later sibling even when their displacements are equal. -/
theorem candidateEarlier_ordered_siblings {m : ℕ}
    (x : Fin m → ℝ) (ω : FiniteRootStepField m ℕ ℝ)
    (p : RootAddress m ℕ) {i j : ℕ}
    (hξ : ω p.1 p.2 ∈ orderedSteps)
    (hij : i < j)
    (hj : survive (ω p.1 p.2) j) :
    candidateEarlier x ω (RootIndexed.childAddress p i)
      (RootIndexed.childAddress p j) := by
  have hi := Step.IsSiblingClosed.survive_of_lt hξ.1 hij hj
  have hdisp := value'_mono_of_survive
    (ω p.1 p.2) hξ.2 (Nat.le_of_lt hij) hi hj
  have hpos : labelledPosition x ω (RootIndexed.childAddress p i) ≤
      labelledPosition x ω (RootIndexed.childAddress p j) := by
    simp only [labelledPosition_child]
    simpa [add_comm] using
      (add_le_add_left hdisp (labelledPosition x ω p))
  rcases lt_or_eq_of_le hpos with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, childAddress_tieKey_lt p hij⟩

theorem candidateEarlier_measurableSet {m n : ℕ}
    [MeasurableSpace X] [AddCommMonoid X] [MeasurableAdd₂ X]
    [LinearOrder X] [TopologicalSpace X] [SecondCountableTopology X]
    [OrderClosedTopology X] [BorelSpace X]
    (x : Fin m → X) (p q : RootAddress m ℕ)
    (hp : p.2.length = n) (hq : q.2.length = n) :
    MeasurableSet[multiRootStepFiltration (m := m) (X := X) n]
      {ω : FiniteRootStepField m ℕ X | candidateEarlier x ω p q} := by
  have hlt := measurableSet_lt
    (labelledPosition_measurable x p hp)
    (labelledPosition_measurable x q hq)
  have heq := measurableSet_eq_fun
    (labelledPosition_measurable x p hp)
    (labelledPosition_measurable x q hq)
  by_cases hcode : addressTieKey p < addressTieKey q
  · have hset : {ω : FiniteRootStepField m ℕ X | candidateEarlier x ω p q} =
        {ω | labelledPosition x ω p < labelledPosition x ω q} ∪
          {ω | labelledPosition x ω p = labelledPosition x ω q} := by
      ext ω
      simp [candidateEarlier, hcode]
    rw [hset]
    exact hlt.union heq
  · have hset : {ω : FiniteRootStepField m ℕ X | candidateEarlier x ω p q} =
        {ω | labelledPosition x ω p < labelledPosition x ω q} := by
      ext ω
      simp [candidateEarlier, hcode]
    rw [hset]
    exact hlt

end ProbabilityTheory.BranchingRandomWalk
