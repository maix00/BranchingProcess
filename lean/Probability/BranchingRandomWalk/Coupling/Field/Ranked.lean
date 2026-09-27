import Probability.BranchingRandomWalk.Coupling.Rank.Measurability
import Probability.BranchingRandomWalk.Step.GenerationUpdate
import Probability.BranchingRandomWalk.Population.Processes.Selected.GenerationUpdate

/-!
# Recursive rank-matched step fields

At stage `n + 1`, the source steps are installed at the equal-rank target
parents of generation `n`, and only coordinates of address depth `n` are
changed.  Earlier coordinates therefore remain stable.  Population and value
functionals stay abstract; the selected branching walk is one application.
-/

namespace ProbabilityTheory.BranchingRandomWalk.Coupling

open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.UlamHarris Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection

variable {Ω Root α X Value : Type*}

/-- Recursively install source steps at equal-rank target particles.  The
population and target-value arguments are evaluated on the field constructed
at the preceding stage. -/
noncomputable def RootIndexed.rankInstalledField
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (sourceValue : ℕ → Ω → RootIndexed.TreeNode Root α → Value)
    (targetValue : ℕ → Ω → RootIndexed.StepField Root α X →
      RootIndexed.TreeNode Root α → Value)
    (source : ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (target : ℕ → Ω → RootIndexed.StepField Root α X →
      Finset (RootIndexed.TreeNode Root α))
    (sourceStep fallback : Ω → RootIndexed.StepField Root α X) :
    ℕ → Ω → RootIndexed.StepField Root α X
  | 0 => fallback
  | n + 1 => fun ω =>
      let prior := RootIndexed.rankInstalledField sourceValue targetValue
        source target sourceStep fallback n
      let installed := RootIndexed.rankInstalledStepField
        (sourceValue n) (fun sample => targetValue n sample (prior sample))
        (source n) (fun sample => target n sample (prior sample))
        sourceStep prior ω
      Combinatorics.Branching.RootIndexed.StepField.updateGeneration
        n installed (prior ω)

@[simp] theorem RootIndexed.rankInstalledField_zero
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (sourceValue : ℕ → Ω → RootIndexed.TreeNode Root α → Value)
    (targetValue : ℕ → Ω → RootIndexed.StepField Root α X →
      RootIndexed.TreeNode Root α → Value)
    (source : ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (target : ℕ → Ω → RootIndexed.StepField Root α X →
      Finset (RootIndexed.TreeNode Root α))
    (sourceStep fallback : Ω → RootIndexed.StepField Root α X)
    (ω : Ω) :
    RootIndexed.rankInstalledField sourceValue targetValue source target
      sourceStep fallback 0 ω = fallback ω :=
  rfl

@[simp] theorem RootIndexed.rankInstalledField_succ
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (sourceValue : ℕ → Ω → RootIndexed.TreeNode Root α → Value)
    (targetValue : ℕ → Ω → RootIndexed.StepField Root α X →
      RootIndexed.TreeNode Root α → Value)
    (source : ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (target : ℕ → Ω → RootIndexed.StepField Root α X →
      Finset (RootIndexed.TreeNode Root α))
    (sourceStep fallback : Ω → RootIndexed.StepField Root α X)
    (n : ℕ) (ω : Ω) :
    RootIndexed.rankInstalledField sourceValue targetValue source target
        sourceStep fallback (n + 1) ω =
      Combinatorics.Branching.RootIndexed.StepField.updateGeneration n
        (RootIndexed.rankInstalledStepField
          (sourceValue n)
          (fun sample => targetValue n sample
            (RootIndexed.rankInstalledField sourceValue targetValue source target
              sourceStep fallback n sample))
          (source n)
          (fun sample => target n sample
            (RootIndexed.rankInstalledField sourceValue targetValue source target
              sourceStep fallback n sample))
          sourceStep
          (RootIndexed.rankInstalledField sourceValue targetValue source target
            sourceStep fallback n) ω)
        (RootIndexed.rankInstalledField sourceValue targetValue source target
          sourceStep fallback n ω) :=
  rfl

/-- A successor stage agrees with the preceding stage at every earlier
address depth. -/
theorem RootIndexed.rankInstalledField_succ_apply_of_lt
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (sourceValue : ℕ → Ω → RootIndexed.TreeNode Root α → Value)
    (targetValue : ℕ → Ω → RootIndexed.StepField Root α X →
      RootIndexed.TreeNode Root α → Value)
    (source : ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (target : ℕ → Ω → RootIndexed.StepField Root α X →
      Finset (RootIndexed.TreeNode Root α))
    (sourceStep fallback : Ω → RootIndexed.StepField Root α X)
    (n : ℕ) (ω : Ω) (r : Root) (u : TreeNode α)
    (hu : u.length < n) :
    RootIndexed.rankInstalledField sourceValue targetValue source target
        sourceStep fallback (n + 1) ω r u =
      RootIndexed.rankInstalledField sourceValue targetValue source target
        sourceStep fallback n ω r u := by
  rw [RootIndexed.rankInstalledField_succ]
  exact Combinatorics.Branching.StepField.updateGeneration_of_lt n _ _ u hu

/-- The successor stage contains the exact source step at the equal-rank
target parent. -/
theorem RootIndexed.rankInstalledField_succ_apply_matchByRankOrSelf
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (sourceValue : ℕ → Ω → RootIndexed.TreeNode Root α → Value)
    (targetValue : ℕ → Ω → RootIndexed.StepField Root α X →
      RootIndexed.TreeNode Root α → Value)
    (source : ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (target : ℕ → Ω → RootIndexed.StepField Root α X →
      Finset (RootIndexed.TreeNode Root α))
    (sourceStep fallback : Ω → RootIndexed.StepField Root α X)
    (n : ℕ) (ω : Ω)
    (hcard : (source n ω).card ≤
      (target n ω (RootIndexed.rankInstalledField sourceValue targetValue source target
        sourceStep fallback n ω)).card)
    (htargetDepth : ∀ q ∈ target n ω
        (RootIndexed.rankInstalledField sourceValue targetValue source target
          sourceStep fallback n ω), q.2.length = n)
    {p : RootIndexed.TreeNode Root α} (hp : p ∈ source n ω) :
    let prior := RootIndexed.rankInstalledField sourceValue targetValue source target
      sourceStep fallback n ω
    let q := matchByRankOrSelf (sourceValue n ω) (targetValue n ω prior)
      (source n ω) (target n ω prior) hcard p
    RootIndexed.rankInstalledField sourceValue targetValue source target
        sourceStep fallback (n + 1) ω q.1 q.2 =
      sourceStep ω p.1 p.2 := by
  dsimp only
  let prior := RootIndexed.rankInstalledField sourceValue targetValue source target
    sourceStep fallback n ω
  let q := matchByRankOrSelf (sourceValue n ω) (targetValue n ω prior)
    (source n ω) (target n ω prior) hcard p
  have hqmem : q ∈ target n ω prior := by
    exact matchByRankOrSelf_mem (sourceValue n ω) (targetValue n ω prior)
      (source n ω) (target n ω prior) hcard hp
  have hqdepth : q.2.length = n := htargetDepth q hqmem
  rw [RootIndexed.rankInstalledField_succ]
  change (if q.2.length = n then
      RootIndexed.rankInstalledStepField
        (sourceValue n)
        (fun sample => targetValue n sample
          (RootIndexed.rankInstalledField sourceValue targetValue source target
            sourceStep fallback n sample))
        (source n)
        (fun sample => target n sample
          (RootIndexed.rankInstalledField sourceValue targetValue source target
            sourceStep fallback n sample))
        sourceStep
        (RootIndexed.rankInstalledField sourceValue targetValue source target
          sourceStep fallback n) ω q.1 q.2
    else prior q.1 q.2) = sourceStep ω p.1 p.2
  rw [ite_eq_left hqdepth]
  exact RootIndexed.rankInstalledStepField_matchByRankOrSelf
    (sourceValue n)
    (fun sample => targetValue n sample
      (RootIndexed.rankInstalledField sourceValue targetValue source target
        sourceStep fallback n sample))
    (source n)
    (fun sample => target n sample
      (RootIndexed.rankInstalledField sourceValue targetValue source target
        sourceStep fallback n sample))
    ω hcard
    sourceStep
    (RootIndexed.rankInstalledField sourceValue targetValue source target
      sourceStep fallback n) hp

/-- All stages after `m` retain the coordinate installed at depth below `m`.
This is the persistence property needed to pass from finite-stage fields to a
single recursively coupled field. -/
theorem RootIndexed.rankInstalledField_apply_stable
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (sourceValue : ℕ → Ω → RootIndexed.TreeNode Root α → Value)
    (targetValue : ℕ → Ω → RootIndexed.StepField Root α X →
      RootIndexed.TreeNode Root α → Value)
    (source : ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (target : ℕ → Ω → RootIndexed.StepField Root α X →
      Finset (RootIndexed.TreeNode Root α))
    (sourceStep fallback : Ω → RootIndexed.StepField Root α X)
    (ω : Ω) (r : Root) (u : TreeNode α) {m n : ℕ}
    (hmn : m ≤ n) (hu : u.length < m) :
    RootIndexed.rankInstalledField sourceValue targetValue source target
        sourceStep fallback n ω r u =
      RootIndexed.rankInstalledField sourceValue targetValue source target
        sourceStep fallback m ω r u := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
      rw [RootIndexed.rankInstalledField_succ_apply_of_lt
        sourceValue targetValue source target sourceStep fallback n ω r u
        (lt_of_lt_of_le hu hmn), ih]

/-- Before stage `n` is installed, every coordinate at depth at least `n`
still comes from the original fallback field. -/
theorem RootIndexed.rankInstalledField_apply_of_le_length
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (sourceValue : ℕ → Ω → RootIndexed.TreeNode Root α → Value)
    (targetValue : ℕ → Ω → RootIndexed.StepField Root α X →
      RootIndexed.TreeNode Root α → Value)
    (source : ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (target : ℕ → Ω → RootIndexed.StepField Root α X →
      Finset (RootIndexed.TreeNode Root α))
    (sourceStep fallback : Ω → RootIndexed.StepField Root α X)
    (n : ℕ) (ω : Ω) (r : Root) (u : TreeNode α)
    (hu : n ≤ u.length) :
    RootIndexed.rankInstalledField sourceValue targetValue source target
        sourceStep fallback n ω r u =
      fallback ω r u := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [RootIndexed.rankInstalledField_succ]
      have hne : u.length ≠ n := by omega
      rw [Combinatorics.Branching.RootIndexed.StepField.updateGeneration_apply,
        ite_eq_right hne]
      exact ih (Nat.le_trans (Nat.le_succ n) hu)

/-- A generation-local rank installation does not change the target selected
population that supplied its parent generation. -/
theorem RootIndexed.selectedPopulation_rankInstalledField_succ
    {Position : Type*}
    [DecidableEq (RootIndexed.TreeNode Root α)]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    [AddCommMonoid Position]
    (N : ℕ) (roots : Finset Root) (initial : Root → Position)
    (d : X → Position) (φ : Position → Value)
    (hadmits : ∀ (k : ℕ) (β : RootIndexed.StepField Root α X)
        (parents : Finset (RootIndexed.TreeNode Root α)),
      AdmitsFirstNBy N
        (RootIndexed.observedPositionAtGeneration initial d φ (k + 1) β)
        (RootIndexed.childrenAtGeneration k parents β))
    (sourceValue : ℕ → Ω → RootIndexed.TreeNode Root α → Value)
    (targetValue : ℕ → Ω → RootIndexed.StepField Root α X →
      RootIndexed.TreeNode Root α → Value)
    (source : ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (target : ℕ → Ω → RootIndexed.StepField Root α X →
      Finset (RootIndexed.TreeNode Root α))
    (sourceStep fallback : Ω → RootIndexed.StepField Root α X)
    (n : ℕ) (ω : Ω) :
    RootIndexed.selectedPopulation N roots initial d φ hadmits n
        (RootIndexed.rankInstalledField sourceValue targetValue source target
          sourceStep fallback (n + 1) ω) =
      RootIndexed.selectedPopulation N roots initial d φ hadmits n
        (RootIndexed.rankInstalledField sourceValue targetValue source target
          sourceStep fallback n ω) := by
  rw [RootIndexed.rankInstalledField_succ]
  exact RootIndexed.selectedPopulation_updateGeneration N roots initial d φ
    hadmits n _ _

/-- Every finite stage of the recursively rank-installed field is measurable.
Countability is localized to the actual ranges of the two random finite
populations used at each stage. -/
theorem RootIndexed.rankInstalledField_measurable
    [MeasurableSpace Ω] [MeasurableSpace X]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (sourceValue : ℕ → Ω → RootIndexed.TreeNode Root α → Value)
    (targetValue : ℕ → Ω → RootIndexed.StepField Root α X →
      RootIndexed.TreeNode Root α → Value)
    (source : ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (target : ℕ → Ω → RootIndexed.StepField Root α X →
      Finset (RootIndexed.TreeNode Root α))
    (sourceStep fallback : Ω → RootIndexed.StepField Root α X)
    (hsourceFiber : ∀ n s, MeasurableSet {ω | source n ω = s})
    (hsourceRange : ∀ n, (Set.range (source n)).Countable)
    (htargetFiber : ∀ n (prior : Ω → RootIndexed.StepField Root α X),
      Measurable prior → ∀ s, MeasurableSet {ω | target n ω (prior ω) = s})
    (htargetRange : ∀ n (prior : Ω → RootIndexed.StepField Root α X),
      Measurable prior → (Set.range fun ω => target n ω (prior ω)).Countable)
    (hsourceKey : ∀ n p q, Measurable fun ω =>
      valueKey (sourceValue n ω) q < valueKey (sourceValue n ω) p)
    (htargetKey : ∀ n (prior : Ω → RootIndexed.StepField Root α X),
      Measurable prior → ∀ p q, Measurable fun ω =>
        valueKey (targetValue n ω (prior ω)) q <
          valueKey (targetValue n ω (prior ω)) p)
    (hsourceStep : Measurable sourceStep)
    (hfallback : Measurable fallback) :
    ∀ n, Measurable fun ω =>
      RootIndexed.rankInstalledField sourceValue targetValue source target
        sourceStep fallback n ω := by
  intro n
  induction n with
  | zero => simpa using hfallback
  | succ n ih =>
      rw [show n + 1 = Nat.succ n by rfl]
      change Measurable fun ω =>
        Combinatorics.Branching.RootIndexed.StepField.updateGeneration n
          (RootIndexed.rankInstalledStepField
            (sourceValue n)
            (fun sample => targetValue n sample
              (RootIndexed.rankInstalledField sourceValue targetValue source target
                sourceStep fallback n sample))
            (source n)
            (fun sample => target n sample
              (RootIndexed.rankInstalledField sourceValue targetValue source target
                sourceStep fallback n sample))
            sourceStep
            (RootIndexed.rankInstalledField sourceValue targetValue source target
              sourceStep fallback n) ω)
          (RootIndexed.rankInstalledField sourceValue targetValue source target
            sourceStep fallback n ω)
      apply RootIndexed.StepField.updateGeneration_measurable
      · apply RootIndexed.rankInstalledStepField_measurable
        · exact hsourceFiber n
        · exact hsourceRange n
        · exact htargetFiber n _ ih
        · exact htargetRange n _ ih
        · exact hsourceKey n
        · exact htargetKey n _ ih
        · intro p
          fun_prop
        · intro q
          fun_prop
      · exact ih

/-- A recursively matched field is measurable when the population and key
data needed at each actual preceding stage are measurable.  Unlike
`rankInstalledField_measurable`, this interface does not quantify over unrelated
candidate preceding fields. -/
theorem RootIndexed.rankInstalledField_measurable_of_stages
    [MeasurableSpace Ω] [MeasurableSpace X]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (sourceValue : ℕ → Ω → RootIndexed.TreeNode Root α → Value)
    (targetValue : ℕ → Ω → RootIndexed.StepField Root α X →
      RootIndexed.TreeNode Root α → Value)
    (source : ℕ → Ω → Finset (RootIndexed.TreeNode Root α))
    (target : ℕ → Ω → RootIndexed.StepField Root α X →
      Finset (RootIndexed.TreeNode Root α))
    (sourceStep fallback : Ω → RootIndexed.StepField Root α X)
    (hsourceFiber : ∀ n s, MeasurableSet {ω | source n ω = s})
    (hsourceRange : ∀ n, (Set.range (source n)).Countable)
    (htargetFiber : ∀ n s, MeasurableSet {ω | target n ω
      (RootIndexed.rankInstalledField sourceValue targetValue source target
        sourceStep fallback n ω) = s})
    (htargetRange : ∀ n, (Set.range fun ω => target n ω
      (RootIndexed.rankInstalledField sourceValue targetValue source target
        sourceStep fallback n ω)).Countable)
    (hsourceKey : ∀ n p q, Measurable fun ω =>
      valueKey (sourceValue n ω) q < valueKey (sourceValue n ω) p)
    (htargetKey : ∀ n p q, Measurable fun ω =>
      valueKey (targetValue n ω
        (RootIndexed.rankInstalledField sourceValue targetValue source target
          sourceStep fallback n ω)) q <
      valueKey (targetValue n ω
        (RootIndexed.rankInstalledField sourceValue targetValue source target
          sourceStep fallback n ω)) p)
    (hsourceStep : Measurable sourceStep)
    (hfallback : Measurable fallback) :
    ∀ n, Measurable fun ω =>
      RootIndexed.rankInstalledField sourceValue targetValue source target
        sourceStep fallback n ω := by
  intro n
  induction n with
  | zero => simpa using hfallback
  | succ n ih =>
      rw [show n + 1 = Nat.succ n by rfl]
      change Measurable fun ω =>
        Combinatorics.Branching.RootIndexed.StepField.updateGeneration n
          (RootIndexed.rankInstalledStepField
            (sourceValue n)
            (fun sample => targetValue n sample
              (RootIndexed.rankInstalledField sourceValue targetValue source target
                sourceStep fallback n sample))
            (source n)
            (fun sample => target n sample
              (RootIndexed.rankInstalledField sourceValue targetValue source target
                sourceStep fallback n sample))
            sourceStep
            (RootIndexed.rankInstalledField sourceValue targetValue source target
              sourceStep fallback n) ω)
          (RootIndexed.rankInstalledField sourceValue targetValue source target
            sourceStep fallback n ω)
      apply RootIndexed.StepField.updateGeneration_measurable
      · apply RootIndexed.rankInstalledStepField_measurable
        · exact hsourceFiber n
        · exact hsourceRange n
        · exact htargetFiber n
        · exact htargetRange n
        · exact hsourceKey n
        · exact htargetKey n
        · intro p
          fun_prop
        · intro q
          fun_prop
      · exact ih

end ProbabilityTheory.BranchingRandomWalk.Coupling
