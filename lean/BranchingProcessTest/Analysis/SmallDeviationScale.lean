import Analysis.Asymptotics.Scale

open Filter
open scoped Topology

example {scale normalization normalization' : ℕ → ℝ}
    (h : Asymptotics.IsSmallDeviationScale scale normalization)
    {c : ℝ} (hc : 0 < c)
    (hpos : ∀ᶠ n in atTop, 0 < normalization n)
    (heq : normalization' =ᶠ[atTop] fun n => c * normalization n) :
    Asymptotics.IsSmallDeviationScale scale normalization' :=
  h.of_eventually_const_mul hc hpos heq

example {scale normalization normalization' : ℕ → ℝ}
    (h : Asymptotics.IsSmallDeviationScale scale normalization)
    {c : ℝ} (hc : 0 < c)
    (hpos : ∀ᶠ n in atTop, 0 < normalization n)
    (hratio : Tendsto (fun n => normalization' n / normalization n)
      atTop (nhds c)) :
    Asymptotics.IsSmallDeviationScale scale normalization' :=
  h.of_tendsto_normalization_ratio hpos hratio hc
