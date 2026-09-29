import Probability.BranchingRandomWalk.Coupling.Field.Ranked.Basic

/-!
# Past measurability of the recursive matched field

The constructed past is measurable in the generation domain flow, including the
bounded form used by causal induction.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Coupling

open ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.UlamHarris Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection

/-- The restriction of every recursive matching stage to its constructed
past is adapted to the generation domain flow.  This is derived from the same
predictable coordinate-map hypotheses used by the product-law argument. -/
theorem RootIndexed.rankInstalledField_past_measurable
    {Root α X Value : Type*} [MeasurableSpace X]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (sourceValue : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.TreeNode Root α → Value)
    (targetValue : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField Root α X →
        RootIndexed.TreeNode Root α → Value)
    (source : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (target : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField Root α X →
        Finset (RootIndexed.TreeNode Root α))
    (hsourceDepth : ∀ n field p, p ∈ source n field → p.2.length = n)
    (hcount : ∀ n, (Set.range (RootIndexed.rankInstalledBlockChoice
      sourceValue targetValue source target n)).Countable)
    (hfiber : ∀ n roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field | RootIndexed.rankInstalledBlockChoice sourceValue targetValue
        source target n field = roots}) :
    ∀ n, Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      (fun field => (RootIndexed.rankInstalledField sourceValue targetValue source
        target RootIndexed.StepField.left RootIndexed.StepField.right n field
          ).past n) := by
  intro n
  induction n with
  | zero =>
      apply (@measurable_pi_iff
        (RootIndexed.StepField (Root ⊕ Root) α X)
        {q : RootIndexed.TreeNode Root α // q.2.length < 0}
        (fun _ => Step α X)
        (RootIndexed.stepFiltration 0) (fun _ => inferInstance) _).2
      intro q
      exact (Nat.not_lt_zero _ q.2).elim
  | succ n ih =>
      apply (@measurable_pi_iff
        (RootIndexed.StepField (Root ⊕ Root) α X)
        {q : RootIndexed.TreeNode Root α // q.2.length < n + 1}
        (fun _ => Step α X)
        (RootIndexed.stepFiltration (n + 1)) (fun _ => inferInstance) _).2
      intro q
      by_cases hq : q.1.2.length < n
      · have hold : Measurable[RootIndexed.stepFiltration
            (Root := Root ⊕ Root) (α := α) (X := X) n]
            (fun field =>
              (RootIndexed.rankInstalledField sourceValue targetValue source target
                RootIndexed.StepField.left RootIndexed.StepField.right n field
                ).past n ⟨q.1, hq⟩) :=
          by
            have h := (measurable_pi_apply ⟨q.1, hq⟩).comp ih
            convert h using 1
            funext field
            rfl
        have hlift := hold.mono
          (RootIndexed.stepFiltration
            (Root := Root ⊕ Root) (α := α) (X := X) |>.mono
              (Nat.le_succ n)) le_rfl
        change Measurable[RootIndexed.stepFiltration
          (Root := Root ⊕ Root) (α := α) (X := X) (n + 1)]
          (fun field => RootIndexed.rankInstalledField sourceValue targetValue source
            target RootIndexed.StepField.left RootIndexed.StepField.right
              (n + 1) field q.1.1 q.1.2)
        convert hlift using 1
        funext field
        exact RootIndexed.rankInstalledField_succ_apply_of_lt sourceValue targetValue
          source target RootIndexed.StepField.left
          RootIndexed.StepField.right n field q.1.1 q.1.2 hq
      · have heq : q.1.2.length = n := by omega
        let qn : RootIndexed.Generation Root α n := ⟨q.1, heq⟩
        have hselected := RootIndexed.selectedCoordinate_measurable
          (RootIndexed.rankInstalledBlockChoice sourceValue targetValue source target n)
          (hcount n) (hfiber n) (Nat.le_succ n) (qn, []) (by
            intro field
            change (RootIndexed.rankChoice n (sourceValue n)
              (fun sample => targetValue n sample
                (RootIndexed.rankInstalledField sourceValue targetValue source target
                  RootIndexed.StepField.left RootIndexed.StepField.right n
                  sample))
              (source n)
              (fun sample => target n sample
                (RootIndexed.rankInstalledField sourceValue targetValue source target
                  RootIndexed.StepField.left RootIndexed.StepField.right n
                  sample)) field qn).2.length < n + 1
            rw [RootIndexed.rankChoice_depth n (sourceValue n)
              (fun sample => targetValue n sample
                (RootIndexed.rankInstalledField sourceValue targetValue source target
                  RootIndexed.StepField.left RootIndexed.StepField.right n
                  sample))
              (source n)
              (fun sample => target n sample
                (RootIndexed.rankInstalledField sourceValue targetValue source target
                  RootIndexed.StepField.left RootIndexed.StepField.right n
                  sample)) (hsourceDepth n)]
            exact Nat.lt_succ_self n)
        convert hselected using 1
        funext field
        have htake : q.1.2.take n = q.1.2 := by simp [heq]
        have hdrop : q.1.2.drop n = [] := by simp [heq]
        rw [RootIndexed.rankInstalledField_succ_eq_glue sourceValue targetValue
          source target n field]
        simp [RootIndexed.StepField.past, RootIndexed.StepField.glue, heq,
          htake, hdrop, qn, RootIndexed.selectedCoordinateField,
          RootIndexed.StepField.reindexCoordinates_apply,
          RootIndexed.rankInstalledBlockChoice]

/-- A finite recursive stage only needs predictability of the coordinate
maps at strictly earlier stages.  This bounded form supports causal induction
when the next selected population is itself constructed from the preceding
matched field. -/
theorem RootIndexed.rankInstalledField_past_measurable_of_lt
    {Root α X Value : Type*} [MeasurableSpace X]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (sourceValue : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.TreeNode Root α → Value)
    (targetValue : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField Root α X →
        RootIndexed.TreeNode Root α → Value)
    (source : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      Finset (RootIndexed.TreeNode Root α))
    (target : ℕ → RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.StepField Root α X →
        Finset (RootIndexed.TreeNode Root α))
    (hsourceDepth : ∀ n field p, p ∈ source n field → p.2.length = n)
    (n : ℕ)
    (hcount : ∀ k, k < n → (Set.range (RootIndexed.rankInstalledBlockChoice
      sourceValue targetValue source target k)).Countable)
    (hfiber : ∀ k, k < n → ∀ roots,
      MeasurableSet[RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := X) k]
        {field | RootIndexed.rankInstalledBlockChoice sourceValue targetValue
          source target k field = roots}) :
    Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      (fun field => (RootIndexed.rankInstalledField sourceValue targetValue source
        target RootIndexed.StepField.left RootIndexed.StepField.right n field
          ).past n) := by
  induction n with
  | zero =>
      apply (@measurable_pi_iff
        (RootIndexed.StepField (Root ⊕ Root) α X)
        {q : RootIndexed.TreeNode Root α // q.2.length < 0}
        (fun _ => Step α X)
        (RootIndexed.stepFiltration 0) (fun _ => inferInstance) _).2
      intro q
      exact (Nat.not_lt_zero _ q.2).elim
  | succ n ih =>
      have ih' := ih
        (fun k hk => hcount k (lt_trans hk (Nat.lt_succ_self n)))
        (fun k hk => hfiber k (lt_trans hk (Nat.lt_succ_self n)))
      apply (@measurable_pi_iff
        (RootIndexed.StepField (Root ⊕ Root) α X)
        {q : RootIndexed.TreeNode Root α // q.2.length < n + 1}
        (fun _ => Step α X)
        (RootIndexed.stepFiltration (n + 1)) (fun _ => inferInstance) _).2
      intro q
      by_cases hq : q.1.2.length < n
      · have hold : Measurable[RootIndexed.stepFiltration
            (Root := Root ⊕ Root) (α := α) (X := X) n]
            (fun field =>
              (RootIndexed.rankInstalledField sourceValue targetValue source target
                RootIndexed.StepField.left RootIndexed.StepField.right n field
                ).past n ⟨q.1, hq⟩) := by
          have h := (measurable_pi_apply ⟨q.1, hq⟩).comp ih'
          convert h using 1
          funext field
          rfl
        have hlift := hold.mono
          (RootIndexed.stepFiltration
            (Root := Root ⊕ Root) (α := α) (X := X) |>.mono
              (Nat.le_succ n)) le_rfl
        change Measurable[RootIndexed.stepFiltration
          (Root := Root ⊕ Root) (α := α) (X := X) (n + 1)]
          (fun field => RootIndexed.rankInstalledField sourceValue targetValue source
            target RootIndexed.StepField.left RootIndexed.StepField.right
              (n + 1) field q.1.1 q.1.2)
        convert hlift using 1
        funext field
        exact RootIndexed.rankInstalledField_succ_apply_of_lt sourceValue targetValue
          source target RootIndexed.StepField.left
          RootIndexed.StepField.right n field q.1.1 q.1.2 hq
      · have heq : q.1.2.length = n := by omega
        let qn : RootIndexed.Generation Root α n := ⟨q.1, heq⟩
        have hselected := RootIndexed.selectedCoordinate_measurable
          (RootIndexed.rankInstalledBlockChoice sourceValue targetValue source target n)
          (hcount n (Nat.lt_succ_self n))
          (hfiber n (Nat.lt_succ_self n)) (Nat.le_succ n) (qn, []) (by
            intro field
            change (RootIndexed.rankChoice n (sourceValue n)
              (fun sample => targetValue n sample
                (RootIndexed.rankInstalledField sourceValue targetValue source target
                  RootIndexed.StepField.left RootIndexed.StepField.right n
                  sample))
              (source n)
              (fun sample => target n sample
                (RootIndexed.rankInstalledField sourceValue targetValue source target
                  RootIndexed.StepField.left RootIndexed.StepField.right n
                  sample)) field qn).2.length < n + 1
            rw [RootIndexed.rankChoice_depth n (sourceValue n)
              (fun sample => targetValue n sample
                (RootIndexed.rankInstalledField sourceValue targetValue source target
                  RootIndexed.StepField.left RootIndexed.StepField.right n
                  sample))
              (source n)
              (fun sample => target n sample
                (RootIndexed.rankInstalledField sourceValue targetValue source target
                  RootIndexed.StepField.left RootIndexed.StepField.right n
                  sample)) (hsourceDepth n)]
            exact Nat.lt_succ_self n)
        convert hselected using 1
        funext field
        have htake : q.1.2.take n = q.1.2 := by simp [heq]
        have hdrop : q.1.2.drop n = [] := by simp [heq]
        rw [RootIndexed.rankInstalledField_succ_eq_glue sourceValue targetValue
          source target n field]
        simp [RootIndexed.StepField.past, RootIndexed.StepField.glue, heq,
          htake, hdrop, qn, RootIndexed.selectedCoordinateField,
          RootIndexed.StepField.reindexCoordinates_apply,
          RootIndexed.rankInstalledBlockChoice]

end ProbabilityTheory.BranchingRandomWalk.Coupling
