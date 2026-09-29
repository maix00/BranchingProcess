module

public import Probability.Process.Markov.Basic
public import Mathlib.Probability.Process.Stopping

/-!
# Strong Markov processes at finite stopping times

The stopping-time σ-algebra is mathlib's
`MeasureTheory.IsStoppingTime.measurableSpace`.  We quantify directly over
ordinary time-valued stopping times, embedded into `WithTop Time`; no second
stopping-time structure is introduced.  Discrete homogeneous chains are a
specialization of the general two-time transition-kernel formulation.
-/

open MeasureTheory
open scoped ENNReal ProbabilityTheory

@[expose] public section

namespace ProbabilityTheory

variable {Time Duration Ω State : Type*} [Preorder Time]
  [MeasurableSpace Ω] [MeasurableSpace State]

/-- A process has the strong Markov property at finite stopping times when,
after a finite-valued stopping time `τ` and a fixed future duration `d`, its
state at `advance (τ ω) d`, conditionally on the stopping-time σ-algebra at
`τ`, has the corresponding transition law started at the stopped state.

`Time` and `Duration` are separate parameters.  The map `advance` supplies
the deterministic time shift; for discrete chains it is natural-number
addition, while continuous-time processes can use addition on `ℝ≥0`.

The definition includes adaptedness, matching `IsMarkovProcess`.  Infinite
stopping times remain expressible through mathlib's `WithTop` API and can be
handled on their finite locus; this core property quantifies over time-valued
stopping times so every displayed stopped state is defined. -/
def IsStrongMarkovProcess (X : Time → Ω → State)
    (F : Filtration Time (inferInstance : MeasurableSpace Ω))
    (P : Measure Ω) (advance : Time → Duration → Time)
    (transition : Time → Time → Kernel State State)
    [∀ s t, IsMarkovKernel (transition s t)] : Prop :=
  Adapted F X ∧
    ∀ (τ : Ω → Time)
      (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop Time)))
      (d : Duration) (A : Set State), MeasurableSet A →
      condExp hτ.measurableSpace P
          (Set.indicator ({ω | X (advance (τ ω) d) ω ∈ A})
            fun _ => (1 : ℝ)) =ᵐ[P]
        fun ω =>
          (transition (τ ω) (advance (τ ω) d) (X (τ ω) ω) A).toReal

namespace IsStrongMarkovProcess

variable {X : Time → Ω → State}
  {F : Filtration Time (inferInstance : MeasurableSpace Ω)}
  {P : Measure Ω} {advance : Time → Duration → Time}
  {transition : Time → Time → Kernel State State}
  [∀ s t, IsMarkovKernel (transition s t)]

theorem adapted (h : IsStrongMarkovProcess X F P advance transition) :
    Adapted F X :=
  h.1

theorem condExp_preimage_ae_eq
    (h : IsStrongMarkovProcess X F P advance transition)
    (τ : Ω → Time)
    (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop Time)))
    (d : Duration) {A : Set State} (hA : MeasurableSet A) :
    condExp hτ.measurableSpace P
        (Set.indicator ({ω | X (advance (τ ω) d) ω ∈ A})
          fun _ => (1 : ℝ)) =ᵐ[P]
      fun ω =>
        (transition (τ ω) (advance (τ ω) d) (X (τ ω) ω) A).toReal :=
  h.2 τ hτ d A hA

/-- If every later deterministic time is obtained by advancing through some
duration, strong Markov at finite stopping times implies ordinary Markov. -/
theorem isMarkovProcess_of_exists_duration
    (h : IsStrongMarkovProcess X F P advance transition)
    (hrepr : ∀ s t, s ≤ t → ∃ d, advance s d = t) :
    IsMarkovProcess X F P transition := by
  refine ⟨h.adapted, ?_⟩
  intro s t hst A hA
  obtain ⟨d, hd⟩ := hrepr s t hst
  let hs : IsStoppingTime F
      (fun _ : Ω => (s : WithTop Time)) := isStoppingTime_const F s
  have hstrong := h.condExp_preimage_ae_eq
    (fun _ : Ω => s) hs d hA
  rw [IsStoppingTime.measurableSpace_const] at hstrong
  simp only [hd] at hstrong
  change condExp (F s) P
      (Set.indicator (X t ⁻¹' A) fun _ => (1 : ℝ)) =ᵐ[P]
    fun ω => (transition s t (X s ω) A).toReal at hstrong
  exact hstrong

end IsStrongMarkovProcess

/-- A time-homogeneous discrete strong Markov process. -/
def IsStrongMarkovChain (X : ℕ → Ω → State)
    (F : Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (P : Measure Ω) (K : Kernel State State) [IsMarkovKernel K] : Prop :=
  IsStrongMarkovProcess X F P (· + ·) (fun m n => K ^ (n - m))

namespace IsStrongMarkovChain

variable {X : ℕ → Ω → State}
  {F : Filtration ℕ (inferInstance : MeasurableSpace Ω)}
  {P : Measure Ω} {K : Kernel State State} [IsMarkovKernel K]

theorem adapted (h : IsStrongMarkovChain X F P K) : Adapted F X :=
  h.1

theorem isStrongMarkovProcess (h : IsStrongMarkovChain X F P K) :
    IsStrongMarkovProcess X F P (· + ·) (fun m n => K ^ (n - m)) :=
  h

theorem condExp_preimage_ae_eq (h : IsStrongMarkovChain X F P K)
    (τ : Ω → ℕ)
    (hτ : IsStoppingTime F (fun ω => (τ ω : WithTop ℕ)))
    (k : ℕ) {A : Set State} (hA : MeasurableSet A) :
    condExp hτ.measurableSpace P
        (Set.indicator ({ω | X (τ ω + k) ω ∈ A}) fun _ => (1 : ℝ)) =ᵐ[P]
      fun ω => ((K ^ k) (X (τ ω) ω) A).toReal := by
  simpa using
  h.isStrongMarkovProcess.condExp_preimage_ae_eq
    τ hτ k hA

/-- Strong Markov at all finite stopping times implies the ordinary Markov
property by applying it to constant stopping times. -/
theorem isMarkovChain (h : IsStrongMarkovChain X F P K) :
    IsMarkovChain X F P K :=
  h.isStrongMarkovProcess.isMarkovProcess_of_exists_duration
    (fun m n hmn => ⟨n - m, Nat.add_sub_of_le hmn⟩)

end IsStrongMarkovChain

namespace IsMarkovChain

variable {X : ℕ → Ω → State}
  {F : Filtration ℕ (inferInstance : MeasurableSpace Ω)}
  {P : Measure Ω} {K : Kernel State State} [IsMarkovKernel K]

/-- A discrete Markov chain has the strong Markov property at every
finite-valued stopping time.  No countability assumption is imposed on the
state space: countability enters only through the natural-number-valued
stopping time, whose level sets partition the sample space. -/
theorem isStrongMarkovChain [IsProbabilityMeasure P]
    (h : IsMarkovChain X F P K) :
    IsStrongMarkovChain X F P K := by
  refine ⟨h.adapted, ?_⟩
  intro τ hτ k A hA
  simp only [Nat.add_sub_cancel_left]
  let f : Ω → ℝ :=
    Set.indicator {ω | X (τ ω + k) ω ∈ A} fun _ => 1
  let g : Ω → ℝ := fun ω => ((K ^ k) (X (τ ω) ω) A).toReal
  change condExp hτ.measurableSpace P f =ᵐ[P] g
  have hevent : MeasurableSet {ω | X (τ ω + k) ω ∈ A} := by
    have heq : {ω | X (τ ω + k) ω ∈ A} =
        ⋃ n : ℕ, {ω | τ ω = n} ∩ X (n + k) ⁻¹' A := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
        Set.mem_preimage]
      constructor
      · intro hω
        exact ⟨τ ω, rfl, hω⟩
      · rintro ⟨n, hn, hω⟩
        simpa [hn] using hω
    rw [heq]
    exact MeasurableSet.iUnion fun n => by
      have hn : MeasurableSet[F n] {ω | τ ω = n} := by
        convert hτ.measurableSet_eq n using 1
        ext ω
        simp
      exact F.le (n + k) _ <|
        (F.mono (Nat.le_add_right n k) _ hn).inter
          (h.adapted (n + k) hA)
  have hf_int : Integrable f P := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
    · exact stronglyMeasurable_const.indicator hevent |>.aestronglyMeasurable
    · exact ae_of_all P fun ω => by
        by_cases hω : X (τ ω + k) ω ∈ A <;> simp [f, hω]
  have hunion : (⋃ n : ℕ, {ω | τ ω = n}) = Set.univ := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    exact ⟨τ ω, rfl⟩
  have hall : condExp hτ.measurableSpace P f =ᵐ[
      P.restrict (⋃ n : ℕ, {ω | τ ω = n})] g := by
    rw [ae_eq_restrict_iUnion_iff]
    intro n
    let s : Set Ω := {ω | τ ω = n}
    have hsFn : MeasurableSet[F n] s := by
      convert hτ.measurableSet_eq n using 1
      ext ω
      simp [s]
    have hs : MeasurableSet s := F.le n _ hsFn
    have hfs : f =ᵐ[P.restrict s]
        Set.indicator (X (n + k) ⁻¹' A) fun _ => 1 := by
      filter_upwards [ae_restrict_mem hs] with ω hω
      simp only [s, Set.mem_ofPred_eq] at hω
      by_cases hx : X (n + k) ω ∈ A <;> simp [f, hω, hx]
    have hfixed_int : Integrable
        (Set.indicator (X (n + k) ⁻¹' A) fun _ => (1 : ℝ)) P :=
      (integrable_const (1 : ℝ)).indicator
        (F.le (n + k) _ (h.adapted (n + k) hA))
    have hlocal : condExp (F n) P f =ᵐ[P.restrict s]
        condExp (F n) P
          (Set.indicator (X (n + k) ⁻¹' A) fun _ => 1) := by
      let q : Ω → ℝ :=
        f - Set.indicator (X (n + k) ⁻¹' A) fun _ => 1
      have hq_zero : q =ᵐ[P.restrict s] 0 :=
        hfs.mono fun _ hω => sub_eq_zero.mpr hω
      have hce_zero : condExp (F n) P q =ᵐ[P.restrict s] 0 :=
        condExp_ae_eq_restrict_zero hsFn hq_zero
      have hsub := condExp_sub hf_int hfixed_int (F n)
      filter_upwards [hce_zero, hsub.restrict] with ω hzero hsubω
      dsimp only [q] at hzero hsubω
      rw [hsubω] at hzero
      exact sub_eq_zero.mp (by simpa using hzero)
    have hmarkov : condExp (F n) P
          (Set.indicator (X (n + k) ⁻¹' A) fun _ => 1) =ᵐ[P]
        fun ω => ((K ^ k) (X n ω) A).toReal := by
      simpa using h.condExp_preimage_ae_eq (Nat.le_add_right n k) hA
    have hstop :=
      condExp_stopping_time_ae_eq_restrict_eq_of_countable
        (μ := P) (ℱ := F) (τ := fun ω => (τ ω : WithTop ℕ))
        (f := f) hτ n
    have hstop' : condExp hτ.measurableSpace P f =ᵐ[P.restrict s]
        condExp (F n) P f := by
      simpa [s] using hstop
    filter_upwards [hstop', hlocal, hmarkov.restrict,
      ae_restrict_mem hs] with ω hstopω hlocalω hmarkovω hω
    change τ ω = n at hω
    rw [hstopω, hlocalω, hmarkovω]
    simpa [g] using (congrArg
      (fun m => ((K ^ k) (X m ω) A).toReal) hω).symm
  simpa [hunion] using hall

end IsMarkovChain

end ProbabilityTheory
