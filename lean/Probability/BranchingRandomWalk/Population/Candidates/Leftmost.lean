import Probability.BranchingRandomWalk.Population.Candidates.Ordering

/-!
# Leftmost selection from a fixed finite candidate set

The rank of a candidate is the number of candidates with a smaller key, and
the selected set consists of those whose rank is below a cutoff. This file
proves the rank and selected set are measurable when the finite candidate set
is fixed, together with the cardinality and nonemptiness bounds. The
random-candidate composition is a separate step. Only the linear order and the
additive structure of the position type are used, so it is a parameter.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

open Combinatorics.UlamHarris Combinatorics.Branching MeasureTheory



variable {X : Type*} [AddCommMonoid X] [LinearOrder X]

/-- Candidates strictly preceding `q` under the position/address key. -/
noncomputable def earlierCandidates {m : ℕ} (x : Fin m → X)
    (ω : FiniteRootStepField m ℕ X) (s : Finset (RootAddress m ℕ))
    (q : RootAddress m ℕ) : Finset (RootAddress m ℕ) := by
  classical
  exact s.filter (fun p => candidateEarlier x ω p q)

theorem earlierCandidates_measurable {m n : ℕ}
    [MeasurableSpace X] [MeasurableAdd₂ X] [TopologicalSpace X]
    [SecondCountableTopology X] [OrderClosedTopology X] [BorelSpace X]
    (x : Fin m → X) (s : Finset (RootAddress m ℕ))
    (hs : ∀ p ∈ s, p.2.length = n)
    (q : RootAddress m ℕ) (hq : q.2.length = n) :
    Measurable[multiRootStepFiltration (m := m) (X := X) n]
      (fun ω : FiniteRootStepField m ℕ X => earlierCandidates x ω s q) := by
  classical
  have hfilter (t : Finset (RootAddress m ℕ))
      (ht : ∀ p ∈ t, p.2.length = n) :
      Measurable[multiRootStepFiltration (m := m) (X := X) n]
        (fun ω : FiniteRootStepField m ℕ X =>
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
            (fun a : Finset (RootAddress m ℕ) => insert p a) :=
          measurable_of_countable _
        have h := @Measurable.ite _ _ _ _ _ _
          (fun ω : FiniteRootStepField m ℕ X => candidateEarlier x ω p q)
          (Classical.decPred _)
          htest (hinsert.comp (ih ht')) (ih ht')
        simpa only [Finset.filter_insert, Function.comp_def] using h
  exact hfilter s hs

/-- Keep precisely those candidates whose strict rank is below `N`. -/
noncomputable def finiteLeftmost {m : ℕ} (N : ℕ)
    (x : Fin m → X) (ω : FiniteRootStepField m ℕ X)
    (s : Finset (RootAddress m ℕ)) : Finset (RootAddress m ℕ) := by
  classical
  exact s.filter (fun q => (earlierCandidates x ω s q).card < N)

theorem finiteLeftmost_subset {m : ℕ} (N : ℕ)
    (x : Fin m → X) (ω : FiniteRootStepField m ℕ X)
    (s : Finset (RootAddress m ℕ)) :
    finiteLeftmost N x ω s ⊆ s := by
  classical
  exact Finset.filter_subset _ _

theorem finiteLeftmost_card_le {m : ℕ} (N : ℕ)
    (x : Fin m → X) (ω : FiniteRootStepField m ℕ X)
    (s : Finset (RootAddress m ℕ)) :
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

theorem finiteLeftmost_nonempty {m : ℕ} (N : ℕ)
    (hN : 0 < N) (x : Fin m → X)
    (ω : FiniteRootStepField m ℕ X) (s : Finset (RootAddress m ℕ))
    (hs : s.Nonempty) :
    (finiteLeftmost N x ω s).Nonempty := by
  classical
  obtain ⟨q, hq, hmin⟩ :=
    Finset.exists_min_image s (candidateKey x ω) hs
  have hempty : earlierCandidates x ω s q = ∅ := by
    ext r
    constructor
    · intro hr
      obtain ⟨hrs, hrearlier⟩ := Finset.mem_filter.mp hr
      have hlt := (candidateEarlier_iff_key_lt x ω r q).1 hrearlier
      exact False.elim ((not_lt_of_ge (hmin r hrs)) hlt)
    · intro hr
      simp at hr
  refine ⟨q, ?_⟩
  apply Finset.mem_filter.mpr
  simpa [hempty] using (show q ∈ s ∧ 0 < N from ⟨hq, hN⟩)

theorem finiteLeftmost_measurable {m n : ℕ} (N : ℕ)
    [MeasurableSpace X] [MeasurableAdd₂ X] [TopologicalSpace X]
    [SecondCountableTopology X] [OrderClosedTopology X] [BorelSpace X]
    (x : Fin m → X) (s : Finset (RootAddress m ℕ))
    (hs : ∀ p ∈ s, p.2.length = n) :
    Measurable[multiRootStepFiltration (m := m) (X := X) n]
      (fun ω : FiniteRootStepField m ℕ X => finiteLeftmost N x ω s) := by
  classical
  have hrank (q : RootAddress m ℕ) (hq : q.2.length = n) :
      Measurable[multiRootStepFiltration (m := m) (X := X) n]
        (fun ω : FiniteRootStepField m ℕ X =>
          (earlierCandidates x ω s q).card) :=
    (measurable_of_countable
      (fun t : Finset (RootAddress m ℕ) => t.card)).comp
      (earlierCandidates_measurable x s hs q hq)
  have hfilter (t : Finset (RootAddress m ℕ))
      (ht : ∀ p ∈ t, p.2.length = n) :
      Measurable[multiRootStepFiltration (m := m) (X := X) n]
        (fun ω : FiniteRootStepField m ℕ X =>
          t.filter (fun q => (earlierCandidates x ω s q).card < N)) := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert q t hqt ih =>
        have hq : q.2.length = n := ht q (Finset.mem_insert_self q t)
        have ht' : ∀ p ∈ t, p.2.length = n := by
          intro p hp
          exact ht p (Finset.mem_insert_of_mem hp)
        have htest : MeasurableSet[multiRootStepFiltration (m := m) (X := X) n]
            {ω : FiniteRootStepField m ℕ X |
              (earlierCandidates x ω s q).card < N} :=
          measurableSet_lt (hrank q hq)
            (measurable_const : Measurable[multiRootStepFiltration (m := m) (X := X) n]
              (fun _ : FiniteRootStepField m ℕ X => N))
        have hinsert : Measurable
            (fun a : Finset (RootAddress m ℕ) => insert q a) :=
          measurable_of_countable _
        have h := @Measurable.ite _ _ _ _ _ _
          (fun ω : FiniteRootStepField m ℕ X =>
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
    (x : Fin m → X) (ω : FiniteRootStepField m ℕ X)
    (s : Finset (RootAddress m ℕ)) : Finset (RootAddress m ℕ) := by
  classical
  exact finiteLeftmost N x ω (s.filter (fun p => p.2.length = n))

theorem finiteLeftmostAtGeneration_fixed_measurable {m : ℕ}
    [MeasurableSpace X] [MeasurableAdd₂ X] [TopologicalSpace X]
    [SecondCountableTopology X] [OrderClosedTopology X] [BorelSpace X]
    (N n : ℕ) (x : Fin m → X)
    (s : Finset (RootAddress m ℕ)) :
    Measurable[multiRootStepFiltration (m := m) (X := X) n]
      (fun ω : FiniteRootStepField m ℕ X =>
        finiteLeftmostAtGeneration N n x ω s) := by
  classical
  unfold finiteLeftmostAtGeneration
  exact finiteLeftmost_measurable N x _
    (by intro p hp; exact (Finset.mem_filter.mp hp).2)

end ProbabilityTheory.BranchingRandomWalk
