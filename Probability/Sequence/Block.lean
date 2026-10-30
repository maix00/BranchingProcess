/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Combinatorics.Sequence.Block
public import Mathlib.Logic.Function.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Measurability of finite sequence blocks

## Public declarations

- `ProbabilityTheory.measurable_blockCoordinates`: the coordinate map
  $f\mapsto(k\mapsto f(s+k))$ for $k<\ell$ is measurable.
- `ProbabilityTheory.paddedBlockCoordinates_measurable`: its extension by a
  fixed default value for $k\geq\ell$ is measurable.
- `ProbabilityTheory.measurable_function_extend_fin_val`: the map
  $b\mapsto(k\mapsto\begin{cases}b_k,&k< n,\\ d,&n\le k\end{cases})$
  from $(\mathrm{Fin}(n)\to E)$ to $(\mathbb N\to E)$ is measurable.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {E : Type*} [MeasurableSpace E]

/-- The finite block map is measurable on sequence space. -/
theorem measurable_blockCoordinates (start length : ℕ) :
    Measurable (Combinatorics.Sequence.blockCoordinates (E := E) start length) := by
  rw [measurable_pi_iff]
  intro k
  exact measurable_pi_apply (start + k)

/-- The finite block map extended by a fixed value outside its index range is
measurable on sequence space. -/
theorem paddedBlockCoordinates_measurable {E : Type*} [MeasurableSpace E]
    (start length : ℕ) (default : E) :
    Measurable (fun sequence : ℕ → E =>
      Combinatorics.Sequence.paddedBlockCoordinates start length default sequence) := by
  rw [measurable_pi_iff]
  intro k
  by_cases hk : k < length
  · change Measurable (fun sequence : ℕ → E =>
      if k < length then sequence (start + k) else default)
    simp only [ite_eq_left hk]
    exact measurable_pi_apply (start + k)
  · change Measurable (fun sequence : ℕ → E =>
      if k < length then sequence (start + k) else default)
    simp only [ite_eq_right hk]
    exact measurable_const

/-- Extending a finite block along `Fin.val` by a fixed default is measurable.
The map is `Function.extend Fin.val block default` on the sequence index. -/
theorem measurable_function_extend_fin_val {E : Type*} [MeasurableSpace E]
    (length : ℕ) (default : E) :
    Measurable (fun block : Fin length → E =>
      Function.extend Fin.val block (fun _ => default)) := by
  rw [measurable_pi_iff]
  intro k
  by_cases hk : k < length
  · have hfun : (fun block : Fin length → E =>
        Function.extend Fin.val block (fun _ => default) k) =
      fun block => block ⟨k, hk⟩ := by
      funext block
      have hinj : Function.Injective (fun i : Fin length => i.val) :=
        fun i j hij => Fin.ext hij
      simpa using (Function.Injective.extend_apply hinj block
        (fun _ => default) ⟨k, hk⟩)
    rw [hfun]
    exact measurable_pi_apply (⟨k, hk⟩ : Fin length)
  · have hnot : ¬ ∃ i : Fin length, i.val = k := by
      rintro ⟨i, hi⟩
      exact hk (by omega)
    have hfun : (fun block : Fin length → E =>
        Function.extend Fin.val block (fun _ => default) k) = fun _ => default := by
      funext block
      exact Function.extend_apply' block (fun _ => default) k hnot
    rw [hfun]
    exact measurable_const

end ProbabilityTheory

end
