import Combinatorics.BranchingWalk.Selection.NSelection.Infinite
import Combinatorics.BranchingWalk.Step.Potential

/-!
# Finite selections from a branching step

A finite step selection chooses finitely many surviving child slots from an
otherwise arbitrary branching step.  It does not prescribe an enumeration,
a distinguished slot, an order, or a capacity.  Those are properties of
particular rules rather than of the branching-step representation.
-/

namespace Combinatorics.Branching

/-- A finite selection of surviving slots from every branching step. -/
structure Step.FiniteSelection (α X : Type*) where
  select : Step α X → Finset α
  subset_support : ∀ ξ i, i ∈ select ξ → survive ξ i

namespace Step.FiniteSelection

variable {α X : Type*}

open Selection.NSelection

attribute [local instance] Classical.propDecidable Classical.decEq

instance : CoeFun (Step.FiniteSelection α X)
    (fun _ => Step α X → Finset α) :=
  ⟨Step.FiniteSelection.select⟩

@[simp] theorem mem_support (R : Step.FiniteSelection α X)
    (ξ : Step α X) {i : α} (hi : i ∈ R ξ) : survive ξ i :=
  R.subset_support ξ i hi

/-- A uniform capacity bound on the number of selected child slots. -/
def IsBoundedBy (R : Step.FiniteSelection α X) (N : ℕ) : Prop :=
  ∀ ξ, (R ξ).card ≤ N

/-- Keep from a finite step selection only slots satisfying a further
step-dependent predicate. -/
noncomputable def filter (R : Step.FiniteSelection α X)
    (keep : Step α X → α → Prop) : Step.FiniteSelection α X where
  select ξ := (R ξ).filter (keep ξ)
  subset_support ξ i hi :=
    R.subset_support ξ i (Finset.mem_filter.mp hi).1

@[simp] theorem mem_filter (R : Step.FiniteSelection α X)
    (keep : Step α X → α → Prop) (ξ : Step α X) (i : α) :
    i ∈ R.filter keep ξ ↔ i ∈ R ξ ∧ keep ξ i := by
  classical
  simp [filter]

theorem filter_isBoundedBy (R : Step.FiniteSelection α X)
    (keep : Step α X → α → Prop) {N : ℕ}
    (hR : R.IsBoundedBy N) : (R.filter keep).IsBoundedBy N := by
  intro ξ
  exact (Finset.card_filter_le _ _).trans (hR ξ)

/-- Kill selected children whose potential exceeds a threshold. -/
noncomputable def belowPotential [MeasurableSpace X]
    (R : Step.FiniteSelection α X) (φ : Potential X) (a : ℝ) :
    Step.FiniteSelection α X :=
  R.filter fun ξ i => ξ.potentialValue' φ i ≤ a

/-- Select the intrinsic first `N` surviving slots by a step-dependent
ordered observation.  Existence is supplied explicitly, so the constructor
does not hide any local-finiteness assumption. -/
noncomputable def firstNBy
    {Value : Type*} [LinearOrder α] [LinearOrder Value]
    (N : ℕ) (value : Step α X → α → Value)
    (hadmits : ∀ ξ, AdmitsFirstNBy N (value ξ) (support ξ)) :
    Step.FiniteSelection α X where
  select ξ := selectFirstNFromSet N (value ξ) (support ξ) (hadmits ξ)
  subset_support ξ _ hi :=
    (selectFirstNFromSet_spec N (value ξ) (support ξ) (hadmits ξ)).subset hi

theorem firstNBy_spec
    {Value : Type*} [LinearOrder α] [LinearOrder Value]
    (N : ℕ) (value : Step α X → α → Value)
    (hadmits : ∀ ξ, AdmitsFirstNBy N (value ξ) (support ξ)) (ξ : Step α X) :
    IsFirstNBy N (value ξ) (support ξ)
      (firstNBy N value hadmits ξ) :=
  selectFirstNFromSet_spec N (value ξ) (support ξ) (hadmits ξ)

theorem firstNBy_isBoundedBy
    {Value : Type*} [LinearOrder α] [LinearOrder Value]
    (N : ℕ) (value : Step α X → α → Value)
    (hadmits : ∀ ξ, AdmitsFirstNBy N (value ξ) (support ξ)) :
    (firstNBy N value hadmits).IsBoundedBy N :=
  fun ξ => (firstNBy_spec N value hadmits ξ).card_le

theorem firstNBy_subset_of_le
    {Value : Type*} [LinearOrder α] [LinearOrder Value]
    {N M : ℕ} (hNM : N ≤ M) (value : Step α X → α → Value)
    (hadmitsN : ∀ ξ, AdmitsFirstNBy N (value ξ) (support ξ))
    (hadmitsM : ∀ ξ, AdmitsFirstNBy M (value ξ) (support ξ))
    (ξ : Step α X) :
    firstNBy N value hadmitsN ξ ⊆ firstNBy M value hadmitsM ξ :=
  (firstNBy_spec N value hadmitsN ξ).subset_of_le
    (firstNBy_spec M value hadmitsM ξ) hNM

/-- First-`N` selection ordered by a real-valued potential of the child
mark.  Raw slots serve only as a deterministic tie breaker. -/
noncomputable def firstNByPotential
    [MeasurableSpace X] [LinearOrder α]
    (N : ℕ) (φ : Potential X)
    (hadmits : ∀ ξ : Step α X, AdmitsFirstNBy N
      (fun i => ξ.potentialValue' φ i) (support ξ)) :
    Step.FiniteSelection α X :=
  firstNBy N (fun ξ i => ξ.potentialValue' φ i) hadmits

/-- Finite lower potential levels guarantee existence of the intrinsic
first-`N` child selection.  This also rules out an unattained left edge such
as displacements `1 / n`. -/
theorem admitsFirstNByPotential_of_level_finite
    [MeasurableSpace X] [LinearOrder α]
    (N : ℕ) (φ : Potential X) (ξ : Step α X)
    (hlevel : ∀ a : ℝ,
      {i | survive ξ i ∧ ξ.potentialValue' φ i ≤ a}.Finite) :
    AdmitsFirstNBy N (fun i => ξ.potentialValue' φ i) (support ξ) := by
  apply admitsFirstNBy_of_lowerFinite N _
  intro p hp
  apply (hlevel (ξ.potentialValue' φ p)).subset
  intro q hq
  refine ⟨hq.1, ?_⟩
  exact (Prod.Lex.le_iff.mp hq.2).elim le_of_lt (fun h => h.1.le)

/-- Preserve the first child whenever it exists, and keep the remaining
members of the first `N` segment only below a potential threshold.  The
branching step itself need not be ordered and may be empty. -/
noncomputable def preserveFirstBelowPotential
    [MeasurableSpace X] [LinearOrder α]
    (N : ℕ) (φ : Potential X) (a : ℝ)
    (hlevel : ∀ ξ : Step α X, ∀ b : ℝ,
      {i | survive ξ i ∧ ξ.potentialValue' φ i ≤ b}.Finite) :
    Step.FiniteSelection α X := by
  let admits : ∀ k ξ, AdmitsFirstNBy k
      (fun i => ξ.potentialValue' φ i) (support ξ) :=
    fun k ξ => admitsFirstNByPotential_of_level_finite k φ ξ (hlevel ξ)
  let first := firstNByPotential 1 φ (admits 1)
  let initial := firstNByPotential N φ (admits N)
  exact {
    select := fun ξ => first ξ ∪ (initial.belowPotential φ a) ξ
    subset_support := fun ξ i hi => by
      rcases Finset.mem_union.mp hi with hi | hi
      · exact first.subset_support ξ i hi
      · exact (initial.belowPotential φ a).subset_support ξ i hi }

theorem mem_preserveFirstBelowPotential_iff
    [MeasurableSpace X] [LinearOrder α]
    (N : ℕ) (φ : Potential X) (a : ℝ)
    (hlevel : ∀ ξ : Step α X, ∀ b : ℝ,
      {i | survive ξ i ∧ ξ.potentialValue' φ i ≤ b}.Finite)
    (ξ : Step α X) (i : α) :
    i ∈ preserveFirstBelowPotential N φ a hlevel ξ ↔
      i ∈ firstNByPotential 1 φ
          (fun ξ => admitsFirstNByPotential_of_level_finite
            1 φ ξ (hlevel ξ)) ξ ∨
        (i ∈ firstNByPotential N φ
            (fun ξ => admitsFirstNByPotential_of_level_finite
              N φ ξ (hlevel ξ)) ξ ∧
          ξ.potentialValue' φ i ≤ a) := by
  simp [preserveFirstBelowPotential, belowPotential, mem_filter]

theorem preserveFirstBelowPotential_isBoundedBy
    [MeasurableSpace X] [LinearOrder α]
    (N : ℕ) (hN : 1 ≤ N) (φ : Potential X) (a : ℝ)
    (hlevel : ∀ ξ : Step α X, ∀ b : ℝ,
      {i | survive ξ i ∧ ξ.potentialValue' φ i ≤ b}.Finite) :
    (preserveFirstBelowPotential N φ a hlevel).IsBoundedBy N := by
  intro ξ
  let admits : ∀ k ξ, AdmitsFirstNBy k
      (fun i => ξ.potentialValue' φ i) (support ξ) :=
    fun k ξ => admitsFirstNByPotential_of_level_finite k φ ξ (hlevel ξ)
  let first := firstNByPotential 1 φ (admits 1)
  let initial := firstNByPotential N φ (admits N)
  have hfirst : first ξ ⊆ initial ξ :=
    firstNBy_subset_of_le hN
      (fun ξ i => ξ.potentialValue' φ i) (admits 1) (admits N) ξ
  have hunion : first ξ ∪ (initial.belowPotential φ a) ξ ⊆ initial ξ := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact hfirst hi
    · have hi' : i ∈ initial.filter
          (fun ξ i => ξ.potentialValue' φ i ≤ a) ξ := by
        simpa only [belowPotential] using hi
      exact (mem_filter initial
        (fun ξ i => ξ.potentialValue' φ i ≤ a) ξ i).mp hi' |>.1
  apply (Finset.card_le_card hunion).trans
  exact (firstNBy_spec N
    (fun ξ i => ξ.potentialValue' φ i) (admits N) ξ).card_le

end Step.FiniteSelection

end Combinatorics.Branching
