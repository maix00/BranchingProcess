import ThesisSpeed.Probability.Population.Processes.Selected

open MeasureTheory

/-!
# Comparing finite candidates with all countably many offspring

The full one-step offspring set is countable and may be infinite. A child
at slot `j ≥ N` cannot be among the first `N` children globally: its own
parent supplies `N` distinct realized earlier siblings, all strictly ahead
under the position and sibling-consistent tie key. This proves exclusion of
late slots. Equality of the complete selected sets still needs the reverse
rank comparison for first-`N` slots.
-/

namespace ThesisSpeed

/-- All realized children of a finite labelled parent set, without a slot
cutoff. -/
def allMultiRootChildren {m : ℕ}
    (s : Finset (RootAddress m)) (ω : FiniteRootBranchingStepField m ℝ) :
    Set (RootAddress m) :=
  {q | ∃ p ∈ s, ∃ j : ℕ,
    branchingStepPresent (ω p.1 p.2) j ∧ q = childAddress p j}

theorem multiRootCandidates_subset_all {m : ℕ}
    (N : ℕ) (s : Finset (RootAddress m)) (ω : FiniteRootBranchingStepField m ℝ) :
    ↑(multiRootCandidates N s ω) ⊆ allMultiRootChildren s ω := by
  intro q hq
  unfold multiRootCandidates at hq
  obtain ⟨p, hp, hq'⟩ := Finset.mem_biUnion.mp hq
  obtain ⟨j, _, hqj⟩ := Finset.mem_biUnion.mp hq'
  obtain ⟨hj, rfl⟩ :=
    (mem_oneChildCandidate_iff ω p q j).1 hqj
  exact ⟨p, hp, j, hj, rfl⟩

/-- A particle is among the first `N` of a possibly infinite set when there
is no finite set of `N` distinct candidates strictly ahead of it. -/
def fullRankBelow {m : ℕ} (N : ℕ) (x : Fin m → ℝ)
    (ω : FiniteRootBranchingStepField m ℝ) (s : Set (RootAddress m))
    (q : RootAddress m) : Prop :=
  ¬∃ t : Finset (RootAddress m), t.card = N ∧
    ∀ r ∈ t, r ∈ s ∧ candidateEarlier x ω r q

theorem childAddress_injective {m : ℕ} (p : RootAddress m) :
    Function.Injective (childAddress p) := by
  intro i j hij
  have hpath : p.2 ++ [i] = p.2 ++ [j] :=
    (Prod.mk.inj hij).2
  have hsingle : [i] = [j] := List.append_cancel_left hpath
  simpa using hsingle

/-- Every realized slot beyond the finite cutoff has `N` strictly earlier
realized siblings in the full offspring set. -/
theorem lateChild_not_fullRankBelow {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ)
    (s : Finset (RootAddress m)) (ω : FiniteRootBranchingStepField m ℝ)
    (p : RootAddress m) (hp : p ∈ s)
    (horder : OrderedNatRealBranchingStep (ω p.1 p.2))
    (j : ℕ) (hNj : N ≤ j)
    (hj : branchingStepPresent (ω p.1 p.2) j) :
    ¬fullRankBelow N x ω (allMultiRootChildren s ω)
      (childAddress p j) := by
  intro hbelow
  apply hbelow
  let t : Finset (RootAddress m) :=
    (Finset.range N).image (childAddress p)
  refine ⟨t, ?_, ?_⟩
  · dsimp [t]
    rw [Finset.card_image_of_injective _ (childAddress_injective p)]
    simp
  · intro r hr
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
    have hij : i < j := lt_of_lt_of_le (Finset.mem_range.mp hi) hNj
    have hreal : branchingStepPresent (ω p.1 p.2) i :=
      orderedNatRealBranchingStep_support_initial
        (ω p.1 p.2) horder hij hj
    constructor
    · exact ⟨p, hp, i, hreal, rfl⟩
    · exact candidateEarlier_ordered_siblings x ω p horder hij hj

/-- Every full-process child whose strict rank is below `N` belongs to the
finite first-`N`-slots candidate set. -/
theorem fullRankBelow_child_mem_candidates {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ)
    (s : Finset (RootAddress m)) (ω : FiniteRootBranchingStepField m ℝ)
    (horder : ∀ p ∈ s, OrderedNatRealBranchingStep (ω p.1 p.2))
    (q : RootAddress m)
    (hq : q ∈ allMultiRootChildren s ω)
    (hrank : fullRankBelow N x ω (allMultiRootChildren s ω) q) :
    q ∈ multiRootCandidates N s ω := by
  obtain ⟨p, hp, j, hj, rfl⟩ := hq
  by_cases hjN : j < N
  · unfold multiRootCandidates
    apply Finset.mem_biUnion.mpr
    refine ⟨p, hp, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨j, Finset.mem_range.mpr hjN, ?_⟩
    simp [oneChildCandidate, hj]
  · have hNj : N ≤ j := by omega
    exact (lateChild_not_fullRankBelow N x s ω p hp
      (horder p hp) j hNj hj) hrank |>.elim

/-- If a late-slot child is ahead of `q`, its `N` earlier siblings are
already among the finite candidates and all ahead of `q`. -/
theorem lateChild_earlier_forces_finite_rank {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ)
    (s : Finset (RootAddress m)) (ω : FiniteRootBranchingStepField m ℝ)
    (p : RootAddress m) (hp : p ∈ s)
    (horder : OrderedNatRealBranchingStep (ω p.1 p.2))
    (j : ℕ) (hNj : N ≤ j)
    (hj : branchingStepPresent (ω p.1 p.2) j)
    (q : RootAddress m)
    (hjq : candidateEarlier x ω (childAddress p j) q) :
    N ≤ (earlierCandidates x ω (multiRootCandidates N s ω) q).card := by
  classical
  let t : Finset (RootAddress m) :=
    (Finset.range N).image (childAddress p)
  have htcard : t.card = N := by
    dsimp [t]
    rw [Finset.card_image_of_injective _ (childAddress_injective p)]
    simp
  have hsubset : t ⊆
      earlierCandidates x ω (multiRootCandidates N s ω) q := by
    intro r hr
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
    have hij : i < j := lt_of_lt_of_le (Finset.mem_range.mp hi) hNj
    have hreal : branchingStepPresent (ω p.1 p.2) i :=
      orderedNatRealBranchingStep_support_initial
        (ω p.1 p.2) horder hij hj
    have hcandidate : childAddress p i ∈ multiRootCandidates N s ω := by
      unfold multiRootCandidates
      apply Finset.mem_biUnion.mpr
      refine ⟨p, hp, ?_⟩
      apply Finset.mem_biUnion.mpr
      refine ⟨i, hi, ?_⟩
      exact (mem_oneChildCandidate_iff ω p (childAddress p i) i).2
        ⟨hreal, rfl⟩
    have hleft := candidateEarlier_ordered_siblings
      x ω p horder hij hj
    have hright : candidateEarlier x ω (childAddress p i) q :=
      (candidateEarlier_iff_key_lt x ω _ _).2
        (lt_trans
          ((candidateEarlier_iff_key_lt x ω _ _).1 hleft)
          ((candidateEarlier_iff_key_lt x ω _ _).1 hjq))
    exact Finset.mem_filter.mpr ⟨hcandidate, hright⟩
  calc
    N = t.card := htcard.symm
    _ ≤ (earlierCandidates x ω (multiRootCandidates N s ω) q).card :=
      Finset.card_le_card hsubset

/-- Finite-rank selection is not spoiled by omitted late-slot children. -/
theorem finiteLeftmost_mem_fullRankBelow {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ)
    (s : Finset (RootAddress m)) (ω : FiniteRootBranchingStepField m ℝ)
    (horder : ∀ p ∈ s, OrderedNatRealBranchingStep (ω p.1 p.2))
    (q : RootAddress m)
    (hq : q ∈ finiteLeftmost N x ω (multiRootCandidates N s ω)) :
    fullRankBelow N x ω (allMultiRootChildren s ω) q := by
  classical
  let C := multiRootCandidates N s ω
  have hqrank : (earlierCandidates x ω C q).card < N :=
    (Finset.mem_filter.mp hq).2
  intro hex
  obtain ⟨t, htcard, ht⟩ := hex
  by_cases hsubset : t ⊆ C
  · have hsubsetEarlier : t ⊆ earlierCandidates x ω C q := by
      intro r hr
      exact Finset.mem_filter.mpr ⟨hsubset hr, (ht r hr).2⟩
    have hle := Finset.card_le_card hsubsetEarlier
    omega
  · obtain ⟨r, hr, hrnot⟩ := Finset.not_subset.mp hsubset
    have hrq := (ht r hr).2
    obtain ⟨p, hp, j, hj, rfl⟩ := (ht r hr).1
    by_cases hjN : j < N
    · have hmem : childAddress p j ∈ C := by
        unfold C multiRootCandidates
        apply Finset.mem_biUnion.mpr
        refine ⟨p, hp, ?_⟩
        apply Finset.mem_biUnion.mpr
        exact ⟨j, Finset.mem_range.mpr hjN,
          (mem_oneChildCandidate_iff ω p (childAddress p j) j).2
            ⟨hj, rfl⟩⟩
      exact hrnot hmem
    · have hNj : N ≤ j := by omega
      have hlarge := lateChild_earlier_forces_finite_rank
        N x s ω p hp (horder p hp) j hNj hj q hrq
      change N ≤ (earlierCandidates x ω C q).card at hlarge
      omega

/-- A full-process top-`N` child has finite-candidate rank below `N`. -/
theorem fullRankBelow_mem_finiteLeftmost {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ)
    (s : Finset (RootAddress m)) (ω : FiniteRootBranchingStepField m ℝ)
    (horder : ∀ p ∈ s, OrderedNatRealBranchingStep (ω p.1 p.2))
    (q : RootAddress m)
    (hq : q ∈ allMultiRootChildren s ω)
    (hrank : fullRankBelow N x ω (allMultiRootChildren s ω) q) :
    q ∈ finiteLeftmost N x ω (multiRootCandidates N s ω) := by
  classical
  have hcandidate := fullRankBelow_child_mem_candidates
    N x s ω horder q hq hrank
  apply Finset.mem_filter.mpr
  refine ⟨hcandidate, ?_⟩
  by_contra hcount
  have hlarge : N ≤
      (earlierCandidates x ω (multiRootCandidates N s ω) q).card := by
    omega
  obtain ⟨t, htSub, htCard⟩ :=
    Finset.exists_subset_card_eq hlarge
  apply hrank
  refine ⟨t, htCard, ?_⟩
  intro r hr
  obtain ⟨hrCandidate, hrEarlier⟩ :=
    Finset.mem_filter.mp (htSub hr)
  exact ⟨multiRootCandidates_subset_all N s ω hrCandidate,
    hrEarlier⟩

/-- The finite first-`N`-slot rank selection agrees exactly with selection
from every realized child of every parent. -/
theorem finiteLeftmost_eq_fullSelection {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ)
    (s : Finset (RootAddress m)) (ω : FiniteRootBranchingStepField m ℝ)
    (horder : ∀ p ∈ s, OrderedNatRealBranchingStep (ω p.1 p.2)) :
    (↑(finiteLeftmost N x ω (multiRootCandidates N s ω)) :
      Set (RootAddress m)) =
      {q | q ∈ allMultiRootChildren s ω ∧
        fullRankBelow N x ω (allMultiRootChildren s ω) q} := by
  ext q
  constructor
  · intro hq
    have hq' : q ∈ finiteLeftmost N x ω
        (multiRootCandidates N s ω) := hq
    exact ⟨multiRootCandidates_subset_all N s ω
      ((finiteLeftmost_subset N x ω _) hq'),
      finiteLeftmost_mem_fullRankBelow N x s ω horder q hq'⟩
  · rintro ⟨hq, hrank⟩
    exact fullRankBelow_mem_finiteLeftmost N x s ω horder q hq hrank

/-- On a fully ordered multi-root marked tree, every step of the adapted
finite recursion equals the global top-`N` selection from all countably
many children of its current labelled population. -/
theorem selectedPopulation_fullSelection_step {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ)
    (n : ℕ) (ω : FiniteRootBranchingStepField m ℝ)
    (hω : ∀ i : Fin m, ∀ u : TreeNode,
      OrderedNatRealBranchingStep (ω i u)) :
    (↑(selectedPopulation N x (n + 1) ω) : Set (RootAddress m)) =
      {q | q ∈ allMultiRootChildren
          (selectedPopulation N x n ω) ω ∧
        fullRankBelow N x ω
          (allMultiRootChildren (selectedPopulation N x n ω) ω) q} := by
  classical
  let s := selectedPopulation N x n ω
  have hsdepth : ∀ p ∈ s, p.2.length = n := by
    intro p hp
    exact selectedPopulation_depth N x n ω p hp
  have hsfilter : s.filter (fun p => p.2.length = n) = s :=
    Finset.filter_true_of_mem hsdepth
  have hcdepth : ∀ q ∈ multiRootCandidates N s ω,
      q.2.length = n + 1 := by
    intro q hq
    exact multiRootCandidates_depth N s ω hsdepth q hq
  have hcfilter :
      (multiRootCandidates N s ω).filter
        (fun q => q.2.length = n + 1) =
      multiRootCandidates N s ω :=
    Finset.filter_true_of_mem hcdepth
  change (↑(finiteLeftmostAtGeneration N (n + 1) x ω
    (multiRootCandidatesAtGeneration N n s ω)) :
      Set (RootAddress m)) = _
  simp only [multiRootCandidatesAtGeneration,
    finiteLeftmostAtGeneration, hsfilter, hcfilter]
  exact finiteLeftmost_eq_fullSelection N x s ω
    (fun p _ => hω p.1 p.2)

theorem selectedPopulation_fullSelection_step_ae
    (μ : Measure (BranchingStep ℕ ℝ)) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ ξ ∂μ, OrderedNatRealBranchingStep ξ)
    (hordered : MeasurableSet {ξ : BranchingStep ℕ ℝ |
      OrderedNatRealBranchingStep ξ})
    {m : ℕ} (N : ℕ) (x : Fin m → ℝ) :
    ∀ᵐ ω ∂finiteRootBranchingStepFieldLaw μ m, ∀ n : ℕ,
      (↑(selectedPopulation N x (n + 1) ω) : Set (RootAddress m)) =
        {q | q ∈ allMultiRootChildren
            (selectedPopulation N x n ω) ω ∧
          fullRankBelow N x ω
            (allMultiRootChildren
              (selectedPopulation N x n ω) ω) q} := by
  filter_upwards [finiteRootBranchingStepFieldLaw_all_ordered μ hμ hordered m] with ω hω
  exact fun n => selectedPopulation_fullSelection_step N x n ω hω

end ThesisSpeed
