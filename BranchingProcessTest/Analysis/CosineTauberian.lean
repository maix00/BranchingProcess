import Analysis.Fourier.CosineTauberian.Mellin
import Analysis.Fourier.CosineTauberian.RegularVariation

open Analysis.Fourier.CosineTauberian

example {α : ℝ} (hα₀ : 0 < α) (hα₂ : α < 2) :
    0 < cosineTauberianMellinMoment α :=
  cosineTauberianMellinMoment_pos hα₀ hα₂

example : 0 < cosineTauberianMellinMoment 1 := by
  exact cosineTauberianMellinMoment_pos (by norm_num) (by norm_num)

example {α : ℝ} (hα₀ : 0 < α) (hα₂ : α < 2) :
    cosineTauberianConstant α =
      1 / (α * (2 - α) * (3 - α) * cosineTauberianCosineMoment α) :=
  cosineTauberianConstant_eq hα₀ hα₂

#print axioms Analysis.Fourier.CosineTauberian.integrableOn_cosineTauberianMellinWeight
#print axioms Analysis.Fourier.CosineTauberian.integrableOn_rpow_mul_abs_cosineTauberianKernel
#print axioms Analysis.Fourier.CosineTauberian.tendsto_integral_ratio_mul_cosineTauberianKernel
#print axioms Analysis.Fourier.CosineTauberian.cosineTauberianMellinMoment_mul_cosineMoment_eq_profileGapMoment
#print axioms Analysis.Fourier.CosineTauberian.integral_cosineTauberianProfileGapWeight
#print axioms Analysis.Fourier.CosineTauberian.cosineTauberianMellinMoment_pos
#print axioms Analysis.Fourier.CosineTauberian.cosineTauberianConstant_eq
#print axioms Analysis.Fourier.CosineTauberian.cosineTauberianConstant_pos
