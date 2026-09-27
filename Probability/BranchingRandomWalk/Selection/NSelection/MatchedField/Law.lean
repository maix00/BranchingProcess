import Probability.BranchingRandomWalk.Selection.NSelection.MatchedField
import Probability.BranchingRandomWalk.Selection.NSelection.Matching.Adaptive

/-!
# Product law of the recursive matched field

Source and fallback are the two copies of one root-indexed product field.
At each generation, the equal-rank match is chosen from the exposed past and
only the matched root steps are replaced.  The predictable-coordinate theorem
then proves by induction that every finite stage has the original product law.
-/

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.BranchingRandomWalk.Selection.NSelection

open Combinatorics.UlamHarris Combinatorics.Branching
open Combinatorics.Branching.Selection.NSelection

/-- The source (left) copy of a joint product field. -/
def RootIndexed.StepField.left
    {Root α X : Type*}
    (field : RootIndexed.StepField (Root ⊕ Root) α X) :
    RootIndexed.StepField Root α X :=
  field.reindex Sum.inl

/-- The fallback (right) copy of a joint product field. -/
def RootIndexed.StepField.right
    {Root α X : Type*}
    (field : RootIndexed.StepField (Root ⊕ Root) α X) :
    RootIndexed.StepField Root α X :=
  field.reindex Sum.inr

/-- The complete fresh-coordinate map used at one recursive matching stage. -/
noncomputable def RootIndexed.matchedBlockChoice
    {Root α X Value : Type*}
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
    (n : ℕ) :
    RootIndexed.StepField (Root ⊕ Root) α X →
      RootIndexed.Generation Root α n × TreeNode α →
        (Root ⊕ Root) × TreeNode α :=
  let prior := RootIndexed.matchedField sourceValue targetValue source target
    RootIndexed.StepField.left RootIndexed.StepField.right n
  RootIndexed.rankBlockChoice n
    (sourceValue n) (fun field => targetValue n field (prior field))
    (source n) (fun field => target n field (prior field))

/-- One recursive successor stage is the predictable coordinate gluing used
by the product-law theorem. -/
theorem RootIndexed.matchedField_succ_eq_glue
    {Root α X Value : Type*}
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
    (n : ℕ) (field : RootIndexed.StepField (Root ⊕ Root) α X) :
    RootIndexed.matchedField sourceValue targetValue source target
        RootIndexed.StepField.left RootIndexed.StepField.right (n + 1) field =
      let prior := RootIndexed.matchedField sourceValue targetValue source target
        RootIndexed.StepField.left RootIndexed.StepField.right n field
      RootIndexed.StepField.glue n (prior.past n)
        (RootIndexed.selectedCoordinateField
          (RootIndexed.matchedBlockChoice sourceValue targetValue source target n)
          field) := by
  let prior := RootIndexed.matchedField sourceValue targetValue source target
    RootIndexed.StepField.left RootIndexed.StepField.right n field
  rw [RootIndexed.matchedField_succ]
  symm
  apply RootIndexed.glue_rankBlockChoice_eq_updateGeneration
  intro r u hu
  exact RootIndexed.matchedField_apply_of_le_length sourceValue targetValue
    source target RootIndexed.StepField.left RootIndexed.StepField.right
    n field r u hu

/-- The restriction of every recursive matching stage to its constructed
past is adapted to the generation domain flow.  This is derived from the same
predictable coordinate-map hypotheses used by the product-law argument. -/
theorem RootIndexed.matchedField_past_measurable
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
    (hcount : ∀ n, (Set.range (RootIndexed.matchedBlockChoice
      sourceValue targetValue source target n)).Countable)
    (hfiber : ∀ n roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field | RootIndexed.matchedBlockChoice sourceValue targetValue
        source target n field = roots}) :
    ∀ n, Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      (fun field => (RootIndexed.matchedField sourceValue targetValue source
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
              (RootIndexed.matchedField sourceValue targetValue source target
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
          (fun field => RootIndexed.matchedField sourceValue targetValue source
            target RootIndexed.StepField.left RootIndexed.StepField.right
              (n + 1) field q.1.1 q.1.2)
        convert hlift using 1
        funext field
        exact RootIndexed.matchedField_succ_apply_of_lt sourceValue targetValue
          source target RootIndexed.StepField.left
          RootIndexed.StepField.right n field q.1.1 q.1.2 hq
      · have heq : q.1.2.length = n := by omega
        let qn : RootIndexed.Generation Root α n := ⟨q.1, heq⟩
        have hselected := RootIndexed.selectedCoordinate_measurable
          (RootIndexed.matchedBlockChoice sourceValue targetValue source target n)
          (hcount n) (hfiber n) (Nat.le_succ n) (qn, []) (by
            intro field
            change (RootIndexed.rankChoice n (sourceValue n)
              (fun sample => targetValue n sample
                (RootIndexed.matchedField sourceValue targetValue source target
                  RootIndexed.StepField.left RootIndexed.StepField.right n
                  sample))
              (source n)
              (fun sample => target n sample
                (RootIndexed.matchedField sourceValue targetValue source target
                  RootIndexed.StepField.left RootIndexed.StepField.right n
                  sample)) field qn).2.length < n + 1
            rw [RootIndexed.rankChoice_depth n (sourceValue n)
              (fun sample => targetValue n sample
                (RootIndexed.matchedField sourceValue targetValue source target
                  RootIndexed.StepField.left RootIndexed.StepField.right n
                  sample))
              (source n)
              (fun sample => target n sample
                (RootIndexed.matchedField sourceValue targetValue source target
                  RootIndexed.StepField.left RootIndexed.StepField.right n
                  sample)) (hsourceDepth n)]
            exact Nat.lt_succ_self n)
        convert hselected using 1
        funext field
        have htake : q.1.2.take n = q.1.2 := by simp [heq]
        have hdrop : q.1.2.drop n = [] := by simp [heq]
        rw [RootIndexed.matchedField_succ_eq_glue sourceValue targetValue
          source target n field]
        simp [RootIndexed.StepField.past, RootIndexed.StepField.glue, heq,
          htake, hdrop, qn, RootIndexed.selectedCoordinateField,
          RootIndexed.StepField.reindexCoordinates_apply,
          RootIndexed.matchedBlockChoice]

/-- Every finite stage of predictable equal-rank installation has the same
complete product law as the original fallback field.  The hypotheses mention
only the actual random coordinate-map range and its generation-domain-flow
fibres; roots and offspring slots need not be countable. -/
theorem RootIndexed.matchedField_law
    {Root α X Value : Type*} [MeasurableSpace X]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
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
    (hfield : ∀ n, Measurable
      (RootIndexed.matchedField sourceValue targetValue source target
        RootIndexed.StepField.left RootIndexed.StepField.right n))
    (hpast : ∀ n, Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      (fun field => (RootIndexed.matchedField sourceValue targetValue source
        target RootIndexed.StepField.left RootIndexed.StepField.right n field
          ).past n))
    (hcount : ∀ n, (Set.range (RootIndexed.matchedBlockChoice
      sourceValue targetValue source target n)).Countable)
    (hfiber : ∀ n roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field | RootIndexed.matchedBlockChoice sourceValue targetValue
        source target n field = roots}) :
    ∀ n,
    (RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).map
        (RootIndexed.matchedField sourceValue targetValue source target
          RootIndexed.StepField.left RootIndexed.StepField.right n) =
      RootIndexed.stepFieldLaw (Root := Root) μ := by
  intro n
  induction n with
  | zero =>
      exact RootIndexed.stepFieldLaw_reindex μ Sum.inr Sum.inr_injective
  | succ n ih =>
      let P := RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ
      let prior := RootIndexed.matchedField sourceValue targetValue source target
        RootIndexed.StepField.left RootIndexed.StepField.right n
      let past := fun field => (prior field).past n
      let rightPast := RootIndexed.StepField.rightPast
        (Root := Root) (α := α) (X := X) n
      have hpastGlobal : Measurable past := (hpast n).mono
        (RootIndexed.stepFiltration
          (Root := Root ⊕ Root) (α := α) (X := X) |>.le n) le_rfl
      have hrestrict : Measurable
          (RootIndexed.StepField.past (Root := Root) (α := α) (X := X) n) :=
        (RootIndexed.StepField.past_measurable n).mono
          (RootIndexed.stepFiltration
            (Root := Root) (α := α) (X := X) |>.le n) le_rfl
      have hright : Measurable
          (RootIndexed.StepField.right :
            RootIndexed.StepField (Root ⊕ Root) α X →
              RootIndexed.StepField Root α X) := by
        change Measurable (RootIndexed.StepField.reindex Sum.inr)
        apply measurable_pi_iff.mpr
        intro r
        apply measurable_pi_iff.mpr
        intro u
        exact (measurable_pi_apply u).comp
          (measurable_pi_apply (Sum.inr r))
      have hpastLaw : P.map past = P.map rightPast := by
        calc
          P.map past = (P.map prior).map (RootIndexed.StepField.past n) := by
            rw [Measure.map_map hrestrict (hfield n)]
            rfl
          _ = (RootIndexed.stepFieldLaw (Root := Root) μ).map
              (RootIndexed.StepField.past n) := by rw [ih]
          _ = (P.map RootIndexed.StepField.right).map
              (RootIndexed.StepField.past n) := by
            change (RootIndexed.stepFieldLaw (Root := Root) μ).map
                (RootIndexed.StepField.past n) =
              (P.map (RootIndexed.StepField.reindex Sum.inr)).map
                (RootIndexed.StepField.past n)
            rw [RootIndexed.stepFieldLaw_reindex μ Sum.inr Sum.inr_injective]
          _ = P.map rightPast := by
            rw [Measure.map_map hrestrict hright]
            rfl
      have hglue := RootIndexed.stepFieldLaw_glueCoordinates μ n past
        (hpast n) hpastLaw
        (RootIndexed.matchedBlockChoice sourceValue targetValue source target n)
        (hcount n) (hfiber n)
        (RootIndexed.rankBlockChoice_future n
          (sourceValue n)
          (fun field => targetValue n field (prior field))
          (source n) (fun field => target n field (prior field))
          (hsourceDepth n))
        (RootIndexed.rankBlockChoice_injective n
          (sourceValue n)
          (fun field => targetValue n field (prior field))
          (source n) (fun field => target n field (prior field)))
      rw [show RootIndexed.matchedField sourceValue targetValue source target
          RootIndexed.StepField.left RootIndexed.StepField.right (n + 1) =
          (fun field => RootIndexed.StepField.glue n (past field)
            (RootIndexed.selectedCoordinateField
              (RootIndexed.matchedBlockChoice sourceValue targetValue
                source target n) field)) by
        funext field
        exact RootIndexed.matchedField_succ_eq_glue sourceValue targetValue
          source target n field]
      exact hglue

/-- Product law of the recursive matched field under support-level
measurability assumptions.  The auxiliary countability and fibre conditions
for the complete coordinate map are consequences, rather than inputs. -/
theorem RootIndexed.matchedField_law_of_supports
    {Root α X Value : Type*} [MeasurableSpace X]
    [LinearOrder (RootIndexed.TreeNode Root α)] [LinearOrder Value]
    (μ : Measure (Step α X)) [IsProbabilityMeasure μ]
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
    (hsourceFiber : ∀ n s, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field | source n field = s})
    (hsourceRange : ∀ n, (Set.range (source n)).Countable)
    (htargetFiber : ∀ n s, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field | target n field
        (RootIndexed.matchedField sourceValue targetValue source target
          RootIndexed.StepField.left RootIndexed.StepField.right n field) = s})
    (htargetRange : ∀ n, (Set.range fun field => target n field
      (RootIndexed.matchedField sourceValue targetValue source target
        RootIndexed.StepField.left RootIndexed.StepField.right n field)
        ).Countable)
    (hsourceKey : ∀ n p q, Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      fun field => valueKey (sourceValue n field) q <
        valueKey (sourceValue n field) p)
    (htargetKey : ∀ n p q, Measurable[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      fun field => valueKey (targetValue n field
        (RootIndexed.matchedField sourceValue targetValue source target
          RootIndexed.StepField.left RootIndexed.StepField.right n field)) q <
        valueKey (targetValue n field
          (RootIndexed.matchedField sourceValue targetValue source target
            RootIndexed.StepField.left RootIndexed.StepField.right n field)) p) :
    ∀ n,
    (RootIndexed.stepFieldLaw (Root := Root ⊕ Root) μ).map
        (RootIndexed.matchedField sourceValue targetValue source target
          RootIndexed.StepField.left RootIndexed.StepField.right n) =
      RootIndexed.stepFieldLaw (Root := Root) μ := by
  have hleft : Measurable
      (RootIndexed.StepField.left :
        RootIndexed.StepField (Root ⊕ Root) α X →
          RootIndexed.StepField Root α X) := by
    change Measurable (RootIndexed.StepField.reindex Sum.inl)
    apply measurable_pi_iff.mpr
    intro r
    apply measurable_pi_iff.mpr
    intro u
    exact (measurable_pi_apply u).comp
      (measurable_pi_apply (Sum.inl r))
  have hright : Measurable
      (RootIndexed.StepField.right :
        RootIndexed.StepField (Root ⊕ Root) α X →
          RootIndexed.StepField Root α X) := by
    change Measurable (RootIndexed.StepField.reindex Sum.inr)
    apply measurable_pi_iff.mpr
    intro r
    apply measurable_pi_iff.mpr
    intro u
    exact (measurable_pi_apply u).comp
      (measurable_pi_apply (Sum.inr r))
  have hfield := RootIndexed.matchedField_measurable_of_stages
    sourceValue targetValue source target RootIndexed.StepField.left
      RootIndexed.StepField.right
    (fun n s => (RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) |>.le n) _
        (hsourceFiber n s))
    hsourceRange
    (fun n s => (RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) |>.le n) _
        (htargetFiber n s))
    htargetRange
    (fun n p q => (hsourceKey n p q).mono
      (RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := X) |>.le n) le_rfl)
    (fun n p q => (htargetKey n p q).mono
      (RootIndexed.stepFiltration
        (Root := Root ⊕ Root) (α := α) (X := X) |>.le n) le_rfl)
    hleft hright
  have hcount : ∀ n, (Set.range (RootIndexed.matchedBlockChoice
      sourceValue targetValue source target n)).Countable := by
    intro n
    exact RootIndexed.rankBlockChoice_range_countable_of_supports n
      (sourceValue n)
      (fun field => targetValue n field
        (RootIndexed.matchedField sourceValue targetValue source target
          RootIndexed.StepField.left RootIndexed.StepField.right n field))
      (source n)
      (fun field => target n field
        (RootIndexed.matchedField sourceValue targetValue source target
          RootIndexed.StepField.left RootIndexed.StepField.right n field))
      (hsourceRange n) (htargetRange n)
  have hfiber : ∀ n roots, MeasurableSet[RootIndexed.stepFiltration
      (Root := Root ⊕ Root) (α := α) (X := X) n]
      {field | RootIndexed.matchedBlockChoice sourceValue targetValue
        source target n field = roots} := by
    intro n roots
    exact RootIndexed.measurableSet_rankBlockChoice_eq_of_supports n
      (sourceValue n)
      (fun field => targetValue n field
        (RootIndexed.matchedField sourceValue targetValue source target
          RootIndexed.StepField.left RootIndexed.StepField.right n field))
      (source n)
      (fun field => target n field
        (RootIndexed.matchedField sourceValue targetValue source target
          RootIndexed.StepField.left RootIndexed.StepField.right n field))
      (hsourceFiber n) (hsourceRange n) (htargetFiber n) (htargetRange n)
      (hsourceKey n) (htargetKey n) roots
  have hpast := RootIndexed.matchedField_past_measurable sourceValue
    targetValue source target hsourceDepth hcount hfiber
  exact RootIndexed.matchedField_law μ sourceValue targetValue source target
    hsourceDepth hfield hpast hcount hfiber

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection
