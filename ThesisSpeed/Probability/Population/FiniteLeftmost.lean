import ThesisSpeed.Probability.Population.MultiRootCandidateAdapted
import Mathlib.Data.Prod.Lex

/-!
# Leftmost selection from a fixed finite candidate set

The key is particle position followed by a deterministic encoding of its
labelled address. The latter breaks ties without reading additional marks.
The rank of a candidate is the number of candidates with a smaller key.
This file proves the rank and selected set are measurable when the finite
candidate set is fixed. The random-candidate composition and cardinality
theorems are separate steps.
-/

open MeasureTheory

namespace ThesisSpeed

def labelledPosition {m : ℕ} (x : Fin m → ℝ)
    (ω : MultiRootTree m) (p : RootAddress m) : ℝ :=
  multiRootPosition x ω p.1 p.2

theorem labelledPosition_measurable {m n : ℕ}
    (x : Fin m → ℝ) (p : RootAddress m) (hp : p.2.length = n) :
    Measurable[multiRootFiltration m n]
      (fun ω : MultiRootTree m => labelledPosition x ω p) := by
  subst n
  exact multiRootPosition_measurable x p.1 p.2

/-- Tie key: parent identity first, then child-slot number, then the full
address as a final injective fallback. Earlier slots of one parent win ties. -/
def addressTieKey {m : ℕ} (p : RootAddress m) :
    ℕ ×ₗ (ℕ ×ₗ ℕ) :=
  toLex (Encodable.encode (p.1, p.2.dropLast),
    toLex (p.2.getLast?.getD 0, Encodable.encode p))

theorem childAddress_tieKey_lt {m : ℕ}
    (p : RootAddress m) {i j : ℕ} (hij : i < j) :
    addressTieKey (childAddress p i) <
      addressTieKey (childAddress p j) := by
  simp [addressTieKey, childAddress, Prod.Lex.lt_iff, hij]

/-- Strict rank order: position first, then the structured tie key. -/
def candidateEarlier {m : ℕ} (x : Fin m → ℝ)
    (ω : MultiRootTree m) (p q : RootAddress m) : Prop :=
  labelledPosition x ω p < labelledPosition x ω q ∨
    (labelledPosition x ω p = labelledPosition x ω q ∧
      addressTieKey p < addressTieKey q)

def candidateKey {m : ℕ} (x : Fin m → ℝ)
    (ω : MultiRootTree m) (p : RootAddress m) :
    ℝ ×ₗ (ℕ ×ₗ (ℕ ×ₗ ℕ)) :=
  toLex (labelledPosition x ω p, addressTieKey p)

theorem candidateEarlier_iff_key_lt {m : ℕ} (x : Fin m → ℝ)
    (ω : MultiRootTree m) (p q : RootAddress m) :
    candidateEarlier x ω p q ↔
      candidateKey x ω p < candidateKey x ω q := by
  simp [candidateEarlier, candidateKey, Prod.Lex.lt_iff]

theorem candidateKey_injective {m : ℕ} (x : Fin m → ℝ)
    (ω : MultiRootTree m) :
    Function.Injective (candidateKey x ω) := by
  intro p q hpq
  have htie : addressTieKey p = addressTieKey q :=
    congrArg (fun z : ℝ ×ₗ (ℕ ×ₗ (ℕ ×ₗ ℕ)) => (ofLex z).2) hpq
  have hcode : Encodable.encode p = Encodable.encode q :=
    congrArg (fun z : ℕ ×ₗ (ℕ ×ₗ ℕ) =>
      (ofLex ((ofLex z).2)).2) htie
  exact Encodable.encode_injective hcode

theorem labelledPosition_child {m : ℕ}
    (x : Fin m → ℝ) (ω : MultiRootTree m)
    (p : RootAddress m) (j : ℕ) :
    labelledPosition x ω (childAddress p j) =
      labelledPosition x ω p +
        childDisplacement (ω p.1 p.2) j := by
  simp [labelledPosition, childAddress, multiRootPosition_child]

/-- Under ordered offspring marks, earlier siblings precede a realized
later sibling even when their displacements are equal. -/
theorem candidateEarlier_ordered_siblings {m : ℕ}
    (x : Fin m → ℝ) (ω : MultiRootTree m)
    (p : RootAddress m) {i j : ℕ}
    (hξ : ω p.1 p.2 ∈ orderedOffspring)
    (hij : i < j)
    (hj : ω p.1 p.2 ∈ childRealized j) :
    candidateEarlier x ω (childAddress p i) (childAddress p j) := by
  have hdisp := orderedOffspring_childDisplacement_mono
    (ω p.1 p.2) hξ (Nat.le_of_lt hij) hj
  have hpos : labelledPosition x ω (childAddress p i) ≤
      labelledPosition x ω (childAddress p j) := by
    simp only [labelledPosition_child]
    simpa [add_comm] using
      (add_le_add_left hdisp (labelledPosition x ω p))
  rcases lt_or_eq_of_le hpos with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, childAddress_tieKey_lt p hij⟩

theorem candidateEarlier_measurableSet {m n : ℕ}
    (x : Fin m → ℝ) (p q : RootAddress m)
    (hp : p.2.length = n) (hq : q.2.length = n) :
    MeasurableSet[multiRootFiltration m n]
      {ω : MultiRootTree m | candidateEarlier x ω p q} := by
  have hlt := measurableSet_lt
    (labelledPosition_measurable x p hp)
    (labelledPosition_measurable x q hq)
  have heq := measurableSet_eq_fun
    (labelledPosition_measurable x p hp)
    (labelledPosition_measurable x q hq)
  by_cases hcode : addressTieKey p < addressTieKey q
  · have hset : {ω : MultiRootTree m | candidateEarlier x ω p q} =
        {ω | labelledPosition x ω p < labelledPosition x ω q} ∪
          {ω | labelledPosition x ω p = labelledPosition x ω q} := by
      ext ω
      simp [candidateEarlier, hcode]
    rw [hset]
    exact hlt.union heq
  · have hset : {ω : MultiRootTree m | candidateEarlier x ω p q} =
        {ω | labelledPosition x ω p < labelledPosition x ω q} := by
      ext ω
      simp [candidateEarlier, hcode]
    rw [hset]
    exact hlt

/-- Candidates strictly preceding `q` under the position/address key. -/
noncomputable def earlierCandidates {m : ℕ} (x : Fin m → ℝ)
    (ω : MultiRootTree m) (s : Finset (RootAddress m))
    (q : RootAddress m) : Finset (RootAddress m) := by
  classical
  exact s.filter (fun p => candidateEarlier x ω p q)

theorem earlierCandidates_measurable {m n : ℕ}
    (x : Fin m → ℝ) (s : Finset (RootAddress m))
    (hs : ∀ p ∈ s, p.2.length = n)
    (q : RootAddress m) (hq : q.2.length = n) :
    Measurable[multiRootFiltration m n]
      (fun ω : MultiRootTree m => earlierCandidates x ω s q) := by
  classical
  have hfilter (t : Finset (RootAddress m))
      (ht : ∀ p ∈ t, p.2.length = n) :
      Measurable[multiRootFiltration m n]
        (fun ω : MultiRootTree m =>
          t.filter (fun p => candidateEarlier x ω p q)) := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert p t hpt ih =>
        have hp : p.2.length = n := ht p (Finset.mem_insert_self p t)
        have ht' : ∀ r ∈ t, r.2.length = n := by
          intro r hr
          exact ht r (Finset.mem_insert_of_mem hr)
        have htest := candidateEarlier_measurableSet x p q hp hq
        have hinsert : Measurable
            (fun a : Finset (RootAddress m) => insert p a) :=
          measurable_of_countable _
        have h := @Measurable.ite _ _ _ _ _ _
          (fun ω : MultiRootTree m => candidateEarlier x ω p q)
          (Classical.decPred _)
          htest (hinsert.comp (ih ht')) (ih ht')
        simpa only [Finset.filter_insert, Function.comp_def] using h
  exact hfilter s hs

/-- Keep precisely those candidates whose strict rank is below `N`. -/
noncomputable def finiteLeftmost {m : ℕ} (N : ℕ)
    (x : Fin m → ℝ) (ω : MultiRootTree m)
    (s : Finset (RootAddress m)) : Finset (RootAddress m) := by
  classical
  exact s.filter (fun q => (earlierCandidates x ω s q).card < N)

theorem finiteLeftmost_subset {m : ℕ} (N : ℕ)
    (x : Fin m → ℝ) (ω : MultiRootTree m)
    (s : Finset (RootAddress m)) :
    finiteLeftmost N x ω s ⊆ s := by
  classical
  exact Finset.filter_subset _ _

theorem finiteLeftmost_card_le {m : ℕ} (N : ℕ)
    (x : Fin m → ℝ) (ω : MultiRootTree m)
    (s : Finset (RootAddress m)) :
    (finiteLeftmost N x ω s).card ≤ N := by
  classical
  let selected := finiteLeftmost N x ω s
  change selected.card ≤ N
  by_contra hcard
  have hnonempty : selected.Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨q, hq, hmax⟩ :=
    Finset.exists_max_image selected (candidateKey x ω) hnonempty
  have hqrank : (earlierCandidates x ω s q).card < N :=
    (Finset.mem_filter.mp hq).2
  have hsubset : selected.erase q ⊆ earlierCandidates x ω s q := by
    intro p hp
    have hpsel : p ∈ selected := Finset.mem_of_mem_erase hp
    have hpne : p ≠ q := Finset.ne_of_mem_erase hp
    have hle : candidateKey x ω p ≤ candidateKey x ω q :=
      hmax p hpsel
    have hne : candidateKey x ω p ≠ candidateKey x ω q := by
      intro heq
      exact hpne (candidateKey_injective x ω heq)
    have hlt : candidateKey x ω p < candidateKey x ω q :=
      lt_of_le_of_ne hle hne
    apply Finset.mem_filter.mpr
    exact ⟨(finiteLeftmost_subset N x ω s) hpsel,
      (candidateEarlier_iff_key_lt x ω p q).2 hlt⟩
  have hsmall := Finset.card_le_card hsubset
  have herase := Finset.card_erase_add_one hq
  omega

theorem finiteLeftmost_measurable {m n : ℕ} (N : ℕ)
    (x : Fin m → ℝ) (s : Finset (RootAddress m))
    (hs : ∀ p ∈ s, p.2.length = n) :
    Measurable[multiRootFiltration m n]
      (fun ω : MultiRootTree m => finiteLeftmost N x ω s) := by
  classical
  have hrank (q : RootAddress m) (hq : q.2.length = n) :
      Measurable[multiRootFiltration m n]
        (fun ω : MultiRootTree m =>
          (earlierCandidates x ω s q).card) :=
    (measurable_of_countable
      (fun t : Finset (RootAddress m) => t.card)).comp
      (earlierCandidates_measurable x s hs q hq)
  have hfilter (t : Finset (RootAddress m))
      (ht : ∀ p ∈ t, p.2.length = n) :
      Measurable[multiRootFiltration m n]
        (fun ω : MultiRootTree m =>
          t.filter (fun q => (earlierCandidates x ω s q).card < N)) := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert q t hqt ih =>
        have hq : q.2.length = n := ht q (Finset.mem_insert_self q t)
        have ht' : ∀ p ∈ t, p.2.length = n := by
          intro p hp
          exact ht p (Finset.mem_insert_of_mem hp)
        have htest : MeasurableSet[multiRootFiltration m n]
            {ω : MultiRootTree m |
              (earlierCandidates x ω s q).card < N} :=
          measurableSet_lt (hrank q hq)
            (measurable_const : Measurable[multiRootFiltration m n]
              (fun _ : MultiRootTree m => N))
        have hinsert : Measurable
            (fun a : Finset (RootAddress m) => insert q a) :=
          measurable_of_countable _
        have h := @Measurable.ite _ _ _ _ _ _
          (fun ω : MultiRootTree m =>
            (earlierCandidates x ω s q).card < N)
          (Classical.decPred _)
          htest (hinsert.comp (ih ht')) (ih ht')
        convert h using 1
        funext ω
        by_cases hc : (earlierCandidates x ω s q).card < N <;>
          simp [Finset.filter_insert, hc]
  exact hfilter s hs

/-- Ignore malformed addresses from another generation. This is the
identity on the candidate sets produced by `multiRootCandidatesAtGeneration`. -/
noncomputable def finiteLeftmostAtGeneration {m : ℕ} (N n : ℕ)
    (x : Fin m → ℝ) (ω : MultiRootTree m)
    (s : Finset (RootAddress m)) : Finset (RootAddress m) := by
  classical
  exact finiteLeftmost N x ω (s.filter (fun p => p.2.length = n))

theorem finiteLeftmostAtGeneration_fixed_measurable {m : ℕ}
    (N n : ℕ) (x : Fin m → ℝ)
    (s : Finset (RootAddress m)) :
    Measurable[multiRootFiltration m n]
      (fun ω : MultiRootTree m =>
        finiteLeftmostAtGeneration N n x ω s) := by
  classical
  unfold finiteLeftmostAtGeneration
  exact finiteLeftmost_measurable N x _
    (by intro p hp; exact (Finset.mem_filter.mp hp).2)

end ThesisSpeed
