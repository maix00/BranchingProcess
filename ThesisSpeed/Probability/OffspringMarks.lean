import ThesisSpeed.Probability.MarkedTree

/-!
# A concrete measurable encoding of countable offspring marks

The first child has a real displacement and is always present. Every later
child slot has a real presence flag and a real displacement; it is present
exactly when the flag is positive. This encodes finite and countably infinite
offspring without imposing a probability law. The law and selected population
are separate later constructions.
-/

open MeasureTheory

namespace ThesisSpeed

abbrev OffspringMark := ℝ × (ℕ → ℝ × ℝ)

def firstDisplacement (ξ : OffspringMark) : ℝ := ξ.1

def childPresent (i : ℕ) : Set OffspringMark :=
  {ξ | 0 < (ξ.2 i).1}

theorem childPresent_measurable (i : ℕ) :
    MeasurableSet (childPresent i) := by
  change MeasurableSet {ξ : OffspringMark | (ξ.2 i).1 ∈ Set.Ioi (0 : ℝ)}
  exact (((measurable_pi_apply i).comp measurable_snd).fst) measurableSet_Ioi

/-- The offspring point process has at least two distinct realized children. -/
def twoChildren : Set OffspringMark :=
  {ξ | ∃ i : ℕ, ξ ∈ childPresent i}

theorem twoChildren_measurable : MeasurableSet twoChildren := by
  have hset : twoChildren = ⋃ i : ℕ, childPresent i := by
    ext ξ
    simp [twoChildren]
  rw [hset]
  exact MeasurableSet.iUnion childPresent_measurable

/-- The causal one-or-two-child rule keeps the first child and accepts the
second only if it exists and its displacement is at most `M`. -/
def keepSecond (M : ℝ) : Set OffspringMark :=
  {ξ | ξ ∈ childPresent 0 ∧ (ξ.2 0).2 ≤ M}

theorem keepSecond_measurable (M : ℝ) : MeasurableSet (keepSecond M) := by
  change MeasurableSet
    (childPresent 0 ∩ {ξ : OffspringMark | (ξ.2 0).2 ∈ Set.Iic M})
  exact (childPresent_measurable 0).inter
    ((((measurable_pi_apply 0).comp measurable_snd).snd) measurableSet_Iic)

noncomputable def retainedChildrenCount (M : ℝ) (ξ : OffspringMark) : ℕ := by
  classical
  exact if ξ ∈ keepSecond M then 2 else 1

theorem retainedChildrenCount_measurable (M : ℝ) :
    Measurable (retainedChildrenCount M) := by
  classical
  unfold retainedChildrenCount
  exact (measurable_const).ite (keepSecond_measurable M) measurable_const

theorem retainedChildrenCount_bounds (M : ℝ) (ξ : OffspringMark) :
    1 ≤ retainedChildrenCount M ξ ∧ retainedChildrenCount M ξ ≤ 2 := by
  classical
  unfold retainedChildrenCount
  split_ifs <;> omega

/-- The visible first bifurcation generation for a causal, full-depth
lineage on the countably marked tree. -/
theorem first_bifurcation_isStoppingTime
    (path : ℕ → MarkedTree OffspringMark → TreeNode)
    (hpath : ∀ n,
      Measurable[generationFiltration (Mark := OffspringMark) n] (path n))
    (hdepth : ∀ n ω, (path n ω).length = n) :
    IsStoppingTime (generationFiltration (Mark := OffspringMark))
      (firstDeclaredSuccess (splitDeclaration path twoChildren)) :=
  first_split_generation_isStoppingTime path hpath hdepth
    twoChildren twoChildren_measurable

end ThesisSpeed
