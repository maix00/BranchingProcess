import Probability.BranchingRandomWalk.Population.Processes.Parallel.Finite
import Probability.BranchingRandomWalk.Timing.Stopping

/-!
# A population process started at an observable random generation

The global population is empty before its start time.  On the cell where the
start time is `k`, it reads the age-`n-k` candidate at global generation `n`.
Writing the definition as a finite union of stopping-time cells makes its
adaptation explicit and avoids any retrospective state update.
-/

open MeasureTheory

namespace ProbabilityTheory.BranchingRandomWalk

/-- Embed a family of processes with deterministic start generation into one
process whose start generation may be infinite.  Exactly one term of the
finite union can be nonempty. -/
def populationStartedAt
    {Ω V : Type*} [DecidableEq V]
    (start : Ω → WithTop ℕ)
    (candidate : ℕ → ℕ → Ω → Finset V)
    (n : ℕ) (ω : Ω) : Finset V :=
  (Finset.range (n + 1)).biUnion fun k =>
    if start ω = k then candidate k (n - k) ω else ∅

theorem populationStartedAt_eq_of_start
    {Ω V : Type*} [DecidableEq V]
    (start : Ω → WithTop ℕ)
    (candidate : ℕ → ℕ → Ω → Finset V)
    {n k : ℕ} (ω : Ω) (hk : k ≤ n)
    (hstart : start ω = k) :
    populationStartedAt start candidate n ω = candidate k (n - k) ω := by
  classical
  ext v
  simp only [populationStartedAt, Finset.mem_biUnion,
    Finset.mem_range]
  constructor
  · rintro ⟨j, hj, hv⟩
    by_cases hsj : start ω = (j : WithTop ℕ)
    · simp only [hsj, ↓reduceIte] at hv
      have hjk : j = k := WithTop.coe_injective (hsj.symm.trans hstart)
      simpa [hjk] using hv
    · simp [hsj] at hv
  · intro hv
    refine ⟨k, Nat.lt_succ_iff.mpr hk, ?_⟩
    simp [hstart, hv]

theorem populationStartedAt_eq_empty_of_lt
    {Ω V : Type*} [DecidableEq V]
    (start : Ω → WithTop ℕ)
    (candidate : ℕ → ℕ → Ω → Finset V)
    {n : ℕ} (ω : Ω) (hstart : (n : WithTop ℕ) < start ω) :
    populationStartedAt start candidate n ω = ∅ := by
  classical
  ext v
  simp only [populationStartedAt, Finset.mem_biUnion,
    Finset.mem_range, Finset.notMem_empty, iff_false]
  rintro ⟨k, hk, hv⟩
  by_cases heq : start ω = (k : WithTop ℕ)
  · simp only [heq, ↓reduceIte] at hv
    have hk_le : k ≤ n := Nat.lt_succ_iff.mp hk
    exact (not_lt_of_ge (heq ▸ WithTop.coe_le_coe.mpr hk_le)) hstart
  · simp [heq] at hv

/-- Starting an adapted deterministic-start family at a stopping time
preserves adaptation. -/
theorem populationStartedAt_adapted
    {Ω V : Type*} {m : MeasurableSpace Ω}
    [Countable V] [DecidableEq V]
    (F : Filtration ℕ m)
    (start : Ω → WithTop ℕ) (hstart : IsStoppingTime F start)
    (candidate : ℕ → ℕ → Ω → Finset V)
    (hcandidate : ∀ k age, Measurable[F (k + age)]
      (candidate k age)) :
    ∀ n, Measurable[F n] (populationStartedAt start candidate n) := by
  intro n
  let pieces : Ω → Fin (n + 1) → Finset V := fun ω k =>
    if start ω = k.val then candidate k.val (n - k.val) ω else ∅
  have hpieces : Measurable[F n] pieces := by
    apply (@measurable_pi_iff Ω (Fin (n + 1)) (fun _ => Finset V)
      (F n) (fun _ => inferInstance) pieces).2
    intro k
    have hk : k.val ≤ n := Nat.le_of_lt_succ k.isLt
    have hevent : MeasurableSet[F n] {ω | start ω = k.val} :=
      (F.mono hk) _ (hstart.measurableSet_eq k.val)
    have hcand : Measurable[F n]
        (candidate k.val (n - k.val)) := by
      have h := hcandidate k.val (n - k.val)
      rw [Nat.add_sub_of_le hk] at h
      exact h
    exact hcand.ite hevent measurable_const
  have hcombine : Measurable
      (fun p : Fin (n + 1) → Finset V =>
        Finset.univ.biUnion p) :=
    measurable_of_countable _
  have hresult := hcombine.comp hpieces
  have heq : (fun ω => Finset.univ.biUnion (pieces ω)) =
      populationStartedAt start candidate n := by
    funext ω
    ext v
    simp only [pieces, populationStartedAt, Finset.mem_biUnion,
      Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨k, hv⟩
      have hk : k.val ≤ n := by omega
      exact ⟨k.val, Nat.lt_succ_of_le hk, hv⟩
    · rintro ⟨k, hk, hv⟩
      exact ⟨⟨k, hk⟩, hv⟩
  rw [← heq]
  exact hresult

end ProbabilityTheory.BranchingRandomWalk
