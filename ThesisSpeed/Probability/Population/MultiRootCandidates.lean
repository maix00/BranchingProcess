import ThesisSpeed.Probability.Tree.MultiRoot

/-!
# Finite child candidates from several initial ancestors

At a selection step with capacity `N`, only the first `N` child slots of
each retained parent are inspected. Under the ordered-offspring support
condition, later slots cannot enter the global leftmost `N`; that reduction
still needs a proof. The present file establishes the finite candidate set
and its causal measurability.
-/

open MeasureTheory

namespace ThesisSpeed

abbrev RootAddress (m : ℕ) := Fin m × TreeNode

instance (m : ℕ) : MeasurableSpace (Finset (RootAddress m)) := ⊤

def initialRootAddresses (m : ℕ) : Finset (RootAddress m) :=
  Finset.univ.image (fun i : Fin m => (i, []))

def childAddress {m : ℕ} (p : RootAddress m) (j : ℕ) :
    RootAddress m :=
  (p.1, p.2 ++ [j])

/-- The child either exists according to its parent's current mark or
contributes no candidate. -/
noncomputable def oneChildCandidate {m : ℕ}
    (ω : MultiRootTree m) (p : RootAddress m) (j : ℕ) :
    Finset (RootAddress m) := by
  classical
  exact if ω p.1 p.2 ∈ childRealized j then {childAddress p j} else ∅

/-- All candidate children of a finite parent population. Every parent
contributes at most the first `N` slots. -/
noncomputable def multiRootCandidates {m : ℕ} (N : ℕ)
    (s : Finset (RootAddress m)) (ω : MultiRootTree m) :
    Finset (RootAddress m) := by
  classical
  exact s.biUnion (fun p =>
    (Finset.range N).biUnion (oneChildCandidate ω p))

theorem oneChildCandidate_measurable {m n : ℕ}
    (p : RootAddress m) (hp : p.2.length = n) (j : ℕ) :
    Measurable[multiRootFiltration m (n + 1)]
      (fun ω : MultiRootTree m => oneChildCandidate ω p j) := by
  classical
  have htest : MeasurableSet[multiRootFiltration m (n + 1)]
      {ω : MultiRootTree m | ω p.1 p.2 ∈ childRealized j} :=
    (multiRootMark_measurable m (n + 1) p.1 p.2
      (by rw [hp]; exact Nat.lt_succ_self n))
      (childRealized_measurable j)
  unfold oneChildCandidate
  exact measurable_const.ite htest measurable_const

theorem multiRootCandidates_fixed_measurable {m n : ℕ} (N : ℕ)
    (s : Finset (RootAddress m))
    (hs : ∀ p ∈ s, p.2.length = n) :
    Measurable[multiRootFiltration m (n + 1)]
      (fun ω : MultiRootTree m => multiRootCandidates N s ω) := by
  classical
  have hunion : Measurable
      (fun p : Finset (RootAddress m) × Finset (RootAddress m) =>
        p.1 ∪ p.2) := measurable_of_countable _
  have hparent (p : RootAddress m) (hp : p.2.length = n) :
      Measurable[multiRootFiltration m (n + 1)]
        (fun ω : MultiRootTree m =>
          (Finset.range N).biUnion (oneChildCandidate ω p)) := by
    induction Finset.range N using Finset.induction_on with
    | empty => simp
    | @insert j t hj ih =>
        have h := hunion.comp
          ((oneChildCandidate_measurable p hp j).prodMk ih)
        simpa only [Finset.biUnion_insert, Function.comp_def] using h
  induction s using Finset.induction_on with
  | empty => simp [multiRootCandidates]
  | @insert p t hpt ih =>
      have hp : p.2.length = n := hs p (Finset.mem_insert_self p t)
      have ht : ∀ q ∈ t, q.2.length = n := by
        intro q hq
        exact hs q (Finset.mem_insert_of_mem hq)
      have h := hunion.comp ((hparent p hp).prodMk (ih ht))
      simpa only [multiRootCandidates, Finset.biUnion_insert,
        Function.comp_def] using h

/-- Filter out addresses of the wrong generation before exposing marks.
For a genuine selected population this filter is the identity; it makes
the update measurable for every possible finite-set input. -/
noncomputable def multiRootCandidatesAtGeneration {m : ℕ}
    (N n : ℕ) (s : Finset (RootAddress m))
    (ω : MultiRootTree m) : Finset (RootAddress m) := by
  classical
  exact multiRootCandidates N (s.filter (fun p => p.2.length = n)) ω

theorem multiRootCandidatesAtGeneration_fixed_measurable {m : ℕ}
    (N n : ℕ) (s : Finset (RootAddress m)) :
    Measurable[multiRootFiltration m (n + 1)]
      (multiRootCandidatesAtGeneration N n s) := by
  classical
  unfold multiRootCandidatesAtGeneration
  exact multiRootCandidates_fixed_measurable N _
    (by intro p hp; exact (Finset.mem_filter.mp hp).2)

theorem oneChildCandidate_depth {m n : ℕ}
    (ω : MultiRootTree m) (p q : RootAddress m) (j : ℕ)
    (hp : p.2.length = n)
    (hq : q ∈ oneChildCandidate ω p j) : q.2.length = n + 1 := by
  classical
  unfold oneChildCandidate at hq
  split_ifs at hq with h
  · have hq' : q = childAddress p j := by simpa using hq
    subst q
    simp [childAddress, hp]
  · simp at hq

theorem oneChildCandidate_first_mem {m : ℕ}
    (ω : MultiRootTree m) (p : RootAddress m) :
    childAddress p 0 ∈ oneChildCandidate ω p 0 := by
  classical
  simp [oneChildCandidate, childRealized]

theorem multiRootCandidates_first_mem {m N : ℕ}
    (hN : 0 < N) (s : Finset (RootAddress m))
    (ω : MultiRootTree m) (p : RootAddress m) (hp : p ∈ s) :
    childAddress p 0 ∈ multiRootCandidates N s ω := by
  classical
  unfold multiRootCandidates
  apply Finset.mem_biUnion.mpr
  refine ⟨p, hp, ?_⟩
  apply Finset.mem_biUnion.mpr
  exact ⟨0, Finset.mem_range.mpr hN,
    oneChildCandidate_first_mem ω p⟩

theorem multiRootCandidates_depth {m n : ℕ} (N : ℕ)
    (s : Finset (RootAddress m)) (ω : MultiRootTree m)
    (hs : ∀ p ∈ s, p.2.length = n)
    (q : RootAddress m) (hq : q ∈ multiRootCandidates N s ω) :
    q.2.length = n + 1 := by
  classical
  unfold multiRootCandidates at hq
  obtain ⟨p, hp, j, hj, hqj⟩ := by
    simpa only [Finset.mem_biUnion] using hq
  exact oneChildCandidate_depth ω p q j (hs p hp) hqj

theorem multiRootCandidatesAtGeneration_depth {m : ℕ} (N n : ℕ)
    (s : Finset (RootAddress m)) (ω : MultiRootTree m)
    (q : RootAddress m)
    (hq : q ∈ multiRootCandidatesAtGeneration N n s ω) :
    q.2.length = n + 1 := by
  classical
  unfold multiRootCandidatesAtGeneration at hq
  exact multiRootCandidates_depth N _ ω
    (by intro p hp; exact (Finset.mem_filter.mp hp).2) q hq

end ThesisSpeed
