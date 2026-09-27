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

end ProbabilityTheory.BranchingRandomWalk.Selection.NSelection
