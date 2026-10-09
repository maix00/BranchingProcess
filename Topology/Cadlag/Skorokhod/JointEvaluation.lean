/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

public import Mathlib.MeasureTheory.Function.Floor
public import Topology.Cadlag.Skorokhod.Integral

/-!
# Joint measurability of càdlàg evaluation

Evaluation of a càdlàg path at a variable time is Borel measurable on the
product of Skorokhod path space and time.  The proof approximates time from
the right by a finite grid and uses right continuity.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace Skorokhod

noncomputable section

private def rightGridPoint (n k : ℕ) : unitInterval :=
  ⟨((min k (n + 1) : ℕ) : ℝ) / (n + 1), by
    constructor
    · positivity
    · rw [div_le_one (by positivity)]
      exact_mod_cast Nat.min_le_right k (n + 1)⟩

private def rightGridValue (n : ℕ) (t : unitInterval) : ℝ :=
  if t = ⊤ then 1 else
    ((Nat.floor (((n + 1 : ℕ) : ℝ) * (t : ℝ)) + 1 : ℕ) : ℝ) /
      ((n + 1 : ℕ) : ℝ)

private theorem rightGridValue_mem (n : ℕ) (t : unitInterval) :
    rightGridValue n t ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases ht : t = ⊤
  · simp [rightGridValue, ht]
  · have htlt : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2 (by
      intro h
      apply ht
      exact Subtype.ext h)
    have hNpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
    have hmul : 0 ≤ ((n + 1 : ℕ) : ℝ) * (t : ℝ) :=
      mul_nonneg (by positivity) t.property.1
    have hmulTop : ((n + 1 : ℕ) : ℝ) * (t : ℝ) < (n + 1 : ℕ) := by
      calc
        ((n + 1 : ℕ) : ℝ) * (t : ℝ) < ((n + 1 : ℕ) : ℝ) * 1 :=
          mul_lt_mul_of_pos_left htlt hNpos
        _ = (n + 1 : ℕ) := by ring
    have hfloor : Nat.floor (((n + 1 : ℕ) : ℝ) * (t : ℝ)) < n + 1 :=
      (Nat.floor_lt hmul).2 hmulTop
    constructor
    · simp [rightGridValue, ht]
      positivity
    · rw [rightGridValue, ite_eq_right ht, div_le_one hNpos]
      exact_mod_cast Nat.succ_le_of_lt hfloor

private def rightGridTime (n : ℕ) (t : unitInterval) : unitInterval :=
  ⟨rightGridValue n t, rightGridValue_mem n t⟩

private theorem measurable_rightGridTime (n : ℕ) : Measurable (rightGridTime n) := by
  have hmul : Measurable (fun t : unitInterval =>
      ((n + 1 : ℕ) : ℝ) * (t : ℝ)) := by fun_prop
  have hfloor : Measurable (fun t : unitInterval =>
      Nat.floor (((n + 1 : ℕ) : ℝ) * (t : ℝ))) := Nat.measurable_floor.comp hmul
  have hbase : Measurable (fun t : unitInterval =>
      ((Nat.floor (((n + 1 : ℕ) : ℝ) * (t : ℝ)) + 1 : ℕ) : ℝ) /
        ((n + 1 : ℕ) : ℝ)) := by fun_prop
  have htop : MeasurableSet ({⊤} : Set unitInterval) := measurableSet_singleton ⊤
  have hval : Measurable (rightGridValue n) := by
    exact Measurable.ite htop measurable_const hbase
  exact hval.subtype_mk (h := rightGridValue_mem n)

private theorem rightGridTime_bounds (n : ℕ) (t : unitInterval) (ht : t ≠ ⊤) :
    (t : ℝ) < (rightGridTime n t : ℝ) ∧
      (rightGridTime n t : ℝ) ≤ (t : ℝ) + 1 / ((n + 1 : ℕ) : ℝ) := by
  have htlt : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2 (by
    intro h
    apply ht
    exact Subtype.ext h)
  have hNpos : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hmul : 0 ≤ ((n + 1 : ℕ) : ℝ) * (t : ℝ) :=
    mul_nonneg (by positivity) t.property.1
  have hmulTop : ((n + 1 : ℕ) : ℝ) * (t : ℝ) < (n + 1 : ℕ) := by
    calc
      ((n + 1 : ℕ) : ℝ) * (t : ℝ) < ((n + 1 : ℕ) : ℝ) * 1 :=
        mul_lt_mul_of_pos_left htlt hNpos
      _ = (n + 1 : ℕ) := by ring
  have hfloor : Nat.floor (((n + 1 : ℕ) : ℝ) * (t : ℝ)) < n + 1 :=
    (Nat.floor_lt hmul).2 hmulTop
  have hmin : min (Nat.floor (((n + 1 : ℕ) : ℝ) * (t : ℝ)) + 1) (n + 1) =
      Nat.floor (((n + 1 : ℕ) : ℝ) * (t : ℝ)) + 1 :=
    min_eq_left (Nat.succ_le_of_lt hfloor)
  have hlo : (t : ℝ) * ((n + 1 : ℕ) : ℝ) <
      ((Nat.floor (((n + 1 : ℕ) : ℝ) * (t : ℝ)) + 1 : ℕ) : ℝ) := by
    simpa [mul_comm] using Nat.lt_floor_add_one
      (((n + 1 : ℕ) : ℝ) * (t : ℝ))
  have hhi : ((Nat.floor (((n + 1 : ℕ) : ℝ) * (t : ℝ)) : ℕ) : ℝ) ≤
      (t : ℝ) * ((n + 1 : ℕ) : ℝ) := by
    simpa [mul_comm] using Nat.floor_le hmul
  constructor
  · change (t : ℝ) < rightGridValue n t
    rw [rightGridValue, ite_eq_right ht]
    exact (lt_div_iff₀ hNpos).2 (by simpa [Nat.cast_add] using hlo)
  · change rightGridValue n t ≤ (t : ℝ) + 1 / ((n + 1 : ℕ) : ℝ)
    rw [rightGridValue, ite_eq_right ht]
    have hhi' :
        ((Nat.floor (((n + 1 : ℕ) : ℝ) * (t : ℝ)) + 1 : ℕ) : ℝ) ≤
          (t : ℝ) * ((n + 1 : ℕ) : ℝ) + 1 := by
      calc
        ((Nat.floor (((n + 1 : ℕ) : ℝ) * (t : ℝ)) + 1 : ℕ) : ℝ) =
            ((Nat.floor (((n + 1 : ℕ) : ℝ) * (t : ℝ)) : ℕ) : ℝ) + 1 := by norm_num
        _ ≤ (t : ℝ) * ((n + 1 : ℕ) : ℝ) + 1 := by
          simpa [add_comm] using add_le_add_right hhi 1
    calc
      ((Nat.floor (((n + 1 : ℕ) : ℝ) * (t : ℝ)) + 1 : ℕ) : ℝ) /
          ((n + 1 : ℕ) : ℝ) ≤
        ((t : ℝ) * ((n + 1 : ℕ) : ℝ) + 1) / ((n + 1 : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right hhi' hNpos.le
      _ = (t : ℝ) + 1 / ((n + 1 : ℕ) : ℝ) := by field_simp

private theorem rightGridTime_tendsto (t : unitInterval) :
    Tendsto (fun n => rightGridTime n t) atTop (𝓝 t) := by
  by_cases ht : t = ⊤
  · subst t
    have heq : (fun n => rightGridTime n ⊤) = fun _ => (⊤ : unitInterval) := by
      funext n
      apply Subtype.ext
      simp [rightGridTime, rightGridValue]
    rw [heq]
    exact tendsto_const_nhds
  · have hN : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
      convert tendsto_atTop_add_const_right atTop (1 : ℝ)
        tendsto_natCast_atTop_atTop using 1
      norm_num

    have hinv : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ)⁻¹)) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hN
    have hreal : Tendsto (fun n => (rightGridTime n t : ℝ)) atTop (𝓝 (t : ℝ)) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      have hsmall : ∀ᶠ n : ℕ in atTop, (((n + 1 : ℕ) : ℝ)⁻¹) < ε :=
        hinv.eventually (Iio_mem_nhds hε)
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hsmall
      refine ⟨N, ?_⟩
      intro n hn
      have hn := hN n hn
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (rightGridTime_bounds n t ht).1.le)]
      have hbound := (rightGridTime_bounds n t ht).2
      calc
        (rightGridTime n t : ℝ) - (t : ℝ) ≤ (((n + 1 : ℕ) : ℝ)⁻¹) := by
          have h' : (rightGridTime n t : ℝ) - (t : ℝ) ≤
              1 / ((n + 1 : ℕ) : ℝ) := by linarith [hbound]
          simpa [one_div] using h'
        _ < ε := hn
    exact tendsto_subtype_rng.2 hreal

private theorem rightGridTime_tendstoWithin (t : unitInterval) (ht : t ≠ ⊤) :
    Tendsto (fun n => rightGridTime n t) atTop (𝓝[Set.Ioi t] t) := by
  apply tendsto_nhdsWithin_iff.2
  refine ⟨rightGridTime_tendsto t, Filter.Eventually.of_forall ?_⟩
  intro n
  exact (rightGridTime_bounds n t ht).1

private def gridEvaluation (n : ℕ) (p : CadlagPath unitInterval ℝ × unitInterval) : ℝ :=
  p.1 (rightGridTime n p.2)

private theorem measurable_gridEvaluation (n : ℕ) : Measurable (gridEvaluation n) := by
  let T := {t : unitInterval // t ∈ Set.range (rightGridTime n)}
  have hTcount : Countable T := by
    let f : ℕ → unitInterval := fun k => rightGridPoint n k
    have hrange : Set.range (rightGridTime n) ⊆ insert ⊤ (Set.range f) := by
      rintro t ⟨s, rfl⟩
      by_cases hs : s = ⊤
      · left
        subst s
        apply Subtype.ext
        simp [rightGridTime, rightGridValue]
      · right
        refine ⟨Nat.floor (((n + 1 : ℕ) : ℝ) * (s : ℝ)) + 1, ?_⟩
        have hslt : (s : ℝ) < 1 := lt_of_le_of_ne s.property.2 (by
          intro h
          exact hs (Subtype.ext h))
        have hmul : 0 ≤ ((n + 1 : ℕ) : ℝ) * (s : ℝ) :=
          mul_nonneg (by positivity) s.property.1
        have hmulTop : ((n + 1 : ℕ) : ℝ) * (s : ℝ) < (n + 1 : ℕ) := by
          calc
            ((n + 1 : ℕ) : ℝ) * (s : ℝ) < ((n + 1 : ℕ) : ℝ) * 1 :=
              mul_lt_mul_of_pos_left hslt (by positivity)
            _ = (n + 1 : ℕ) := by ring
        have hfloor : Nat.floor (((n + 1 : ℕ) : ℝ) * (s : ℝ)) < n + 1 :=
          (Nat.floor_lt hmul).2 hmulTop
        have hmin : min (Nat.floor (((n + 1 : ℕ) : ℝ) * (s : ℝ)) + 1) (n + 1) =
            Nat.floor (((n + 1 : ℕ) : ℝ) * (s : ℝ)) + 1 :=
          min_eq_left (Nat.succ_le_of_lt hfloor)
        apply Subtype.ext
        simp only [rightGridTime, rightGridValue, ite_eq_right hs, rightGridPoint, f]
        simpa only [Nat.cast_add, Nat.cast_one] using
          congrArg (fun k : ℕ => (k : ℝ) / ((n + 1 : ℕ) : ℝ)) hmin
    have hcount : (insert ⊤ (Set.range f)).Countable :=
      Set.Countable.insert _ (Set.countable_range f)
    exact hcount.mono hrange |>.to_subtype
  have hEval : Measurable (fun p : CadlagPath unitInterval ℝ × T => p.1 p.2.1) :=
    measurable_from_prod_countable_left fun t => Skorokhod.measurable_apply t.1
  have hmap : Measurable (fun p : CadlagPath unitInterval ℝ × unitInterval =>
      (p.1, (⟨rightGridTime n p.2, ⟨p.2, rfl⟩⟩ : T))) := by
    refine Measurable.prodMk measurable_fst ?_
    exact (measurable_rightGridTime n).comp measurable_snd |>.subtype_mk
  change Measurable (fun p : CadlagPath unitInterval ℝ × unitInterval =>
    p.1 (rightGridTime n p.2))
  exact hEval.comp hmap

/-- Joint evaluation is Borel measurable for càdlàg paths in the Skorokhod
`J₁` topology and a variable time. -/
theorem measurable_joint_apply :
    Measurable (fun p : CadlagPath unitInterval ℝ × unitInterval => p.1 p.2) := by
  have hlim : Tendsto (fun n p => gridEvaluation n p) atTop
      (𝓝 fun p : CadlagPath unitInterval ℝ × unitInterval => p.1 p.2) := by
    rw [tendsto_pi_nhds]
    rintro ⟨path, t⟩
    by_cases ht : t = ⊤
    · subst t
      have heq : (fun n => gridEvaluation n (path, ⊤)) = fun _ => path ⊤ := by
        funext n
        have htop : rightGridTime n ⊤ = ⊤ := by
          apply Subtype.ext
          simp [rightGridTime, rightGridValue]
        simp [gridEvaluation, htop]
      rw [heq]
      exact tendsto_const_nhds
    · exact (path.isCadlag_toFun.isRightContinuous t).tendsto.comp
        (rightGridTime_tendstoWithin t ht)
  exact measurable_of_tendsto_metrizable (fun n => measurable_gridEvaluation n) hlim

end -- noncomputable section

end Skorokhod

end
