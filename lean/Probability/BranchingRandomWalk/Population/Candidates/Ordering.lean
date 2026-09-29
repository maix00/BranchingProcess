module

public import Probability.BranchingRandomWalk.Population.Candidates.Adapted
public import Combinatorics.BranchingWalk.Step.Basic
public import Combinatorics.BranchingWalk.Step.Monotone
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
    addressTieKey (childAddress p i) <
      addressTieKey (childAddress p j) := by
  simp [addressTieKey, childAddress, Prod.Lex.lt_iff, hij]

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
    labelledPosition x ω (childAddress p j) =
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
    (hξ : Step.IsOrdered (ω p.1 p.2))
    (hij : i < j)
    (hj : survive (ω p.1 p.2) j) :
    candidateEarlier x ω (childAddress p i) (childAddress p j) := by
  have hi := Step.IsSiblingClosed.survive_of_lt hξ.1 hij hj
  have hdisp := value'_mono_of_survive
    (ω p.1 p.2) hξ.2 (Nat.le_of_lt hij) hi hj
  have hpos : labelledPosition x ω (childAddress p i) ≤
      labelledPosition x ω (childAddress p j) := by
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
