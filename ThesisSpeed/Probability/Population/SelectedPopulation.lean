import ThesisSpeed.Probability.Population.FiniteLeftmost

/-!
# A measurable multi-root finite-candidate selection process

All `m` initial roots enter one common selection pool. At each generation
the process examines the first `N` child slots of every retained parent,
then keeps candidates of finite rank below `N`, with address-code tie
breaking. The process and full labelled population are adapted to the
multi-root domain filtration. The theorem equating this finite rule to
selection from the entire countable offspring point process is still open.
-/

open MeasureTheory

namespace ThesisSpeed

/-- A countably indexed family of measurable functions remains measurable
when its index is selected measurably from the same information. -/
theorem measurable_countable_choice {Ω ι β : Type*}
    [MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSpace β]
    [Countable ι] [MeasurableSingletonClass ι]
    (F : MeasurableSpace Ω)
    (index : Ω → ι) (hindex : Measurable[F] index)
    (f : ι → Ω → β) (hf : ∀ i, Measurable[F] (f i)) :
    Measurable[F] (fun ω => f (index ω) ω) := by
  intro B hB
  have hpre :
      (fun ω => f (index ω) ω) ⁻¹' B =
        ⋃ i : ι, {ω | index ω = i} ∩ {ω | f i ω ∈ B} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_ofPred_eq]
    constructor
    · intro h
      exact ⟨index ω, rfl, h⟩
    · rintro ⟨i, hi, hfi⟩
      simpa [hi] using hfi
  rw [hpre]
  exact MeasurableSet.iUnion (fun i =>
    (hindex (measurableSet_singleton i)).inter ((hf i) hB))

theorem finiteLeftmostAtGeneration_of_adapted {m : ℕ}
    (N n : ℕ) (x : Fin m → ℝ)
    (candidates : MultiRootTree m → Finset (RootAddress m))
    (hcandidates : Measurable[multiRootFiltration m n] candidates) :
    Measurable[multiRootFiltration m n]
      (fun ω => finiteLeftmostAtGeneration N n x ω (candidates ω)) := by
  exact measurable_countable_choice
    (multiRootFiltration m n) candidates hcandidates
    (fun s ω => finiteLeftmostAtGeneration N n x ω s)
    (finiteLeftmostAtGeneration_fixed_measurable N n x)

/-- One common selected population from `m` labelled initial ancestors. -/
noncomputable def selectedPopulation {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ) :
    ℕ → MultiRootTree m → Finset (RootAddress m)
  | 0, _ => initialRootAddresses m
  | n + 1, ω =>
      finiteLeftmostAtGeneration N (n + 1) x ω
        (multiRootCandidatesAtGeneration N n
          (selectedPopulation N x n ω) ω)

theorem selectedPopulation_adapted {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ) :
    ∀ n, Measurable[multiRootFiltration m n]
      (selectedPopulation N x n) := by
  intro n
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      have hcandidates := multiRootCandidatesAtGeneration_of_adapted
        N n (selectedPopulation N x n) ih
      exact finiteLeftmostAtGeneration_of_adapted N (n + 1) x
        (fun ω => multiRootCandidatesAtGeneration N n
          (selectedPopulation N x n ω) ω) hcandidates

theorem selectedPopulation_depth {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ)
    (n : ℕ) (ω : MultiRootTree m)
    (p : RootAddress m) (hp : p ∈ selectedPopulation N x n ω) :
    p.2.length = n := by
  cases n with
  | zero =>
      simp [selectedPopulation, initialRootAddresses] at hp
      obtain ⟨i, _, rfl⟩ := hp
      rfl
  | succ n =>
      unfold selectedPopulation at hp
      unfold finiteLeftmostAtGeneration finiteLeftmost at hp
      have hcandidate : p ∈
          (multiRootCandidatesAtGeneration N n
            (selectedPopulation N x n ω) ω).filter
              (fun q => q.2.length = n + 1) :=
        (Finset.mem_filter.mp hp).1
      exact (Finset.mem_filter.mp hcandidate).2

/-- After the first selection step, the common population contains at most
`N` particles across all initial ancestors. -/
theorem selectedPopulation_card_le {m : ℕ}
    (N : ℕ) (x : Fin m → ℝ)
    (n : ℕ) (ω : MultiRootTree m) :
    (selectedPopulation N x (n + 1) ω).card ≤ N := by
  unfold selectedPopulation finiteLeftmostAtGeneration
  exact finiteLeftmost_card_le N x ω _

/-- The guaranteed first child at every parent prevents extinction when
there is at least one initial ancestor and the capacity is positive. -/
theorem selectedPopulation_nonempty {m : ℕ}
    (hm : 0 < m) (N : ℕ) (hN : 0 < N)
    (x : Fin m → ℝ) (ω : MultiRootTree m) :
    ∀ n, (selectedPopulation N x n ω).Nonempty := by
  intro n
  induction n with
  | zero =>
      let i : Fin m := ⟨0, hm⟩
      refine ⟨(i, []), ?_⟩
      change (i, []) ∈ initialRootAddresses m
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  | succ n ih =>
      obtain ⟨p, hp⟩ := ih
      let C := multiRootCandidatesAtGeneration N n
        (selectedPopulation N x n ω) ω
      have hpC : childAddress p 0 ∈ C := by
        unfold C multiRootCandidatesAtGeneration
        apply multiRootCandidates_first_mem hN _ ω p
        exact Finset.mem_filter.mpr
          ⟨hp, selectedPopulation_depth N x n ω p hp⟩
      have hC : C.Nonempty := ⟨childAddress p 0, hpC⟩
      have hCdepth : ∀ q ∈ C, q.2.length = n + 1 := by
        intro q hq
        exact multiRootCandidatesAtGeneration_depth N n _ ω q hq
      have hfilter : C.filter (fun q => q.2.length = n + 1) = C :=
        Finset.filter_true_of_mem hCdepth
      change (finiteLeftmostAtGeneration N (n + 1) x ω C).Nonempty
      simp only [finiteLeftmostAtGeneration, hfilter]
      exact finiteLeftmost_nonempty N hN x ω C hC

end ThesisSpeed
