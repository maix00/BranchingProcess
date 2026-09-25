import ThesisSpeed.Probability.Genealogy.MultiRoot.Filtration

/-!
# Realization and positions of labelled descendants

Realization of a labelled descendant checks only its own ancestral marks, and
its position is the initial ancestor's offset plus the accumulated
displacement. Both are observable at the generation that reveals the address.
-/

open MeasureTheory

namespace ThesisSpeed

/-- Realization of a labelled descendant checks only its own ancestral marks. -/
def multiRootRealized {m : ℕ} (i : Fin m) (u : 𝕍) :
    Set (MultiRootMark m) :=
  {ω | ω i ∈ realizedNode u}

theorem multiRootRealized_measurable {m : ℕ} (i : Fin m)
    (u : 𝕍) :
    MeasurableSet[multiRootFiltration m u.length]
      (multiRootRealized i u) := by
  have hset : multiRootRealized i u =
      ⋂ j ∈ Finset.range u.length,
        {ω : MultiRootMark m |
          ω i (u.take j) ∈ childRealized (u[j]!)} := by
    ext ω
    simp [multiRootRealized, realizedNode]
  rw [hset]
  apply Finset.measurableSet_biInter
  intro j hj
  have hj' : j < u.length := Finset.mem_range.mp hj
  have hprefix : (u.take j).length < u.length := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj'), hj']
  exact (multiRootMark_measurable m u.length i (u.take j) hprefix)
    (childRealized_measurable (u[j]!))

/-- The position of a descendant, including its initial ancestor's offset. -/
def multiRootPosition {m : ℕ} (x : Fin m → ℝ)
    (ω : MultiRootMark m) (i : Fin m) (u : 𝕍) : ℝ :=
  x i + vertexPosition (ω i) u

theorem multiRootPosition_at_root {m : ℕ} (x : Fin m → ℝ)
    (ω : MultiRootMark m) (i : Fin m) :
    multiRootPosition x ω i [] = x i := by
  simp [multiRootPosition, vertexPosition]

theorem multiRootPosition_child {m : ℕ} (x : Fin m → ℝ)
    (ω : MultiRootMark m) (i : Fin m) (u : 𝕍) (j : ℕ) :
    multiRootPosition x ω i (u ++ [j]) =
      multiRootPosition x ω i u + childDisplacement (ω i u) j := by
  simp [multiRootPosition, vertexPosition_append_singleton, add_assoc]

theorem multiRootPosition_measurable {m : ℕ} (x : Fin m → ℝ)
    (i : Fin m) (u : 𝕍) :
    Measurable[multiRootFiltration m u.length]
      (fun ω : MultiRootMark m => multiRootPosition x ω i u) := by
  unfold multiRootPosition vertexPosition
  apply measurable_const.add
  apply Finset.measurable_fun_sum
  intro j hj
  have hj' : j < u.length := Finset.mem_range.mp hj
  have hprefix : (u.take j).length < u.length := by
    simp [List.length_take, Nat.min_eq_left (Nat.le_of_lt hj'), hj']
  exact (childDisplacement_measurable (u[j]!)).comp
    (multiRootMark_measurable m u.length i (u.take j) hprefix)

end ThesisSpeed
