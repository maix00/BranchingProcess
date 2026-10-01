module

public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Abel
public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Continuous additive maps on the nonnegative real line
-/
open scoped NNReal

@[expose] public section

/-- A continuous additive map from the nonnegative reals to a real normed
vector space is determined by its value at one. -/
theorem continuous_additive_nnreal_eq_smul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ≥0 → E) (hf : Continuous f)
    (hadd : ∀ x y, f (x + y) = f x + f y)
    (x : ℝ≥0) : f x = (x : ℝ) • f 1 := by
  have hzero : f 0 = 0 := by
    have h : f 0 + f 0 = f 0 := by simpa using (hadd 0 0).symm
    exact (add_eq_left).mp h
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
        simp only [hadd] at hmap
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
