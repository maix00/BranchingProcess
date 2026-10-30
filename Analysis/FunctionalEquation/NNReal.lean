/-
Copyright (c) 2026 WANG Yiyang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: WANG Yiyang
-/

module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Topology.Defs.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Continuous additive maps from the nonnegative reals

## Public declarations

* `map_nnreal_smul`: every continuous additive map from $\mathbb R_{\ge 0}$
  to a Hausdorff topological real vector space satisfies
  $f(x)=x\cdot f(1)$.
-/
open scoped NNReal

@[expose] public section

/-- A continuous additive map from the nonnegative reals to a Hausdorff
topological real vector space is determined by its value at one. -/
theorem map_nnreal_smul {E : Type*} {F : Type*}
    [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℝ E] [T2Space E]
    [FunLike F ℝ≥0 E] [AddMonoidHomClass F ℝ≥0 E]
    (f : F) (hf : Continuous f)
    (x : ℝ≥0) : f x = (x : ℝ) • f 1 := by
  have hzero : f 0 = 0 := map_zero f
  let g : ℝ →+ E :=
    { toFun := fun r => f (Real.toNNReal r) - f (Real.toNNReal (-r))
      map_zero' := by simp [hzero]
      map_add' := by
        intro a b
        have hparts : Real.toNNReal (a + b) + Real.toNNReal (-a) +
            Real.toNNReal (-b) =
            Real.toNNReal a + Real.toNNReal b + Real.toNNReal (-(a + b)) := by
          apply NNReal.eq
          simp only [NNReal.coe_add, Real.coe_toNNReal']
          simp only [max_def]
          split_ifs <;> linarith
        have hmap := congrArg f hparts
        simp only [map_add] at hmap
        calc
          f (Real.toNNReal (a + b)) - f (Real.toNNReal (-(a + b))) =
              (f (Real.toNNReal (a + b)) + f (Real.toNNReal (-a)) +
                f (Real.toNNReal (-b))) -
              (f (Real.toNNReal (-(a + b))) + f (Real.toNNReal (-a)) +
                f (Real.toNNReal (-b))) := by abel
          _ = (f (Real.toNNReal a) + f (Real.toNNReal b) +
                f (Real.toNNReal (-(a + b)))) -
              (f (Real.toNNReal (-(a + b))) + f (Real.toNNReal (-a)) +
                f (Real.toNNReal (-b))) := by rw [hmap]
          _ = (f (Real.toNNReal a) - f (Real.toNNReal (-a))) +
              (f (Real.toNNReal b) - f (Real.toNNReal (-b))) := by abel }
  have hg : Continuous g :=
    (hf.comp continuous_real_toNNReal).sub
      (hf.comp (continuous_real_toNNReal.comp continuous_neg))
  have hlin := map_real_smul g hg (x : ℝ) (1 : ℝ)
  have hx : 0 ≤ (x : ℝ) := x.property
  simpa [g, Real.toNNReal_of_nonpos, hzero, hx] using hlin

end
