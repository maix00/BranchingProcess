# Mogulskii (1974) small deviations: the original statements, and where each one lives

Source: А. А. Могульский, *Малые уклонения в пространстве траекторий*, Теория вероятностей и её применения
**XIX**(4), 1974. Local copy of the PDF at `~/Downloads/Mogulskii_1974_Small_deviations.pdf` (11 pages,
21363 characters of text layer; extracted to `/tmp/mogul.txt`). Statements below are transcribed from that
text; the OCR is noisy, so formulas are restored to their mathematical reading and the original numbers
(2), (3), (4), (15), (16), (18)–(20), (34) are kept verbatim.

## The original statements

* **(2)** `ξ₁, ξ₂, …` i.i.d. with `P((ξ₁+…+ξₙ)/B(n) < x) → F_a(x)`, where `F_a` is **strictly stable** and
  **`0 < a ≤ 2`**; for `a = 1` an extra centering `βₙ = ∫ sin(t B⁻¹(n)) F(dt)` is used.
* **(3)** `L*(u) = u^{a−2} ∫_{−u}^{u} ξ² F(dξ)` — a **slowly varying** function.
* **(4)** `B*(B(n)) ↝ d·n` with `B*(u) = u^a / L*(u)`; without loss of generality `d = 1`.
* **(15) Теорема 1.** `0 < F_a(0) < 1`. Then for every sequence `{x(n)}` with `x(n) → ∞` and
  `x(n)·B⁻¹(n) → 0`, and every set `G` of paths,
  `ln P(sₙ(·) ∈ G) ~ C · H^a_x(G) · n · x(n)^{-a} · L*(x(n))`,
  where the constant `C` satisfies `−∞ < C < 0` and depends on `F_a` only (see Лемма 1).
* **(16) Теорема 2.** If `P(ξ(1) < x) = F_a(x)` of a strictly stable process satisfies `0 < F_a(0) < 1`, then
  for every `G`, as `a ↓ 0`, `ln P(a⁻¹ ξ(·) ∈ G) ~ C · H^a(G) · a^a` — the *stable-process* (single-block)
  statement.
* **Лемма 1. I (18)** `a^a ln P(ξ(·) ∈ a𝔘) → C` as `a ↓ 0`, `C ∈ (−∞, 0)`. **II (19)(20)** for `1 > b > c > −1`
  the tubes `a𝔙_b^c`, `a𝔙_b^{d(1)}` are asymptotically equivalent to `a𝔘`.
* **Лемма 2** supplies the individual estimates behind Лемма 1; **Лемма 3** is the walk version
  (its item д) is (34)); **Лемма 4. I** states `ln P(sₙ(·) ∈ 𝔘) ~ C · n · x(n)^{-a} · L*(x(n))`, i.e. (15)
  at `G = 𝔘`.
* **§3 «Доказательство теорем 1 и 2»** proves Теорема 1 and Теорема 2 by splitting `[0, 1]` at
  `0 < t₁ < … < 1`, estimating each block and gluing; Теорема 2 is proved "in exactly the same way with
  Лемма 1". **Теорема 3 / 4** are the adjacent statements; the paper notes "В случае а = 2 константу С
  удалось вычислить" — only for `a = 2` is the constant *computed* (Теорема 4). The paper nowhere splits the
  statement into `a < 2` and `a = 2`.

## Normalisation (the single factor every statement is scaled by)

```
λ_n := n · L*(x(n)) · x(n)^{-a}          -- the paper's factor in (15) and Лемма 4
```

so that `−(1/λ_n) ln P(sₙ(·) ∈ G) → −C · H^a(G)`, and for a corridor `G = {f : g ≤ f ≤ h}` the functional
`H^a_x(G)` tends to `∫₀¹ dt / (g − f)^a` — the `corridorEnergy` already in
`Combinatorics/BranchingWalk/Walk/Path/Corridor.lean`.

## Where each piece lives

| original | module | state |
| --- | --- | --- |
| (2), (4): domain of attraction, norming | `Distributions/Stable/{Attraction,Basic}.lean`, `Mogulskii/Stable/Scale.lean` | present as predicates (`IsInAlphaStableDomainOfAttractionAlong`, `IsStableNorming`, `IsStableMogulskiiScale`) |
| (3): `L*` | `Distributions/Stable/SmallDeviation.lean` | `stableSlowVariation`, `truncatedSecondMoment` |
| (15)/(16) normalisation `λ_n` | `Distributions/Stable/SmallDeviation.lean` | **stored as its reciprocal** `stableSmallDeviationRate` (see below) |
| (4) block length in steps | `Mogulskii/Stable/Scale.lean` | `stableBlockArgument` / `stableBlockLength` now divide by `L*`, so the block count is `λ_n` (see below) |
| Лемма 1 I: the constant `C = −C*` | — | **missing**: needs the stable-process escape rate |
| Лемма 2: individual estimates | — | **missing** |
| Теорема 2: single stable block | `Mogulskii/Stable/Corridor.lean` | **missing**: only the corridor *object* (`stableBlockTube`, `stableBlockCorridorProbability`) is there |
| §3: partition and gluing | `Walk/Path/Block/Partition.lean` (scale-free) + `Mogulskii/Stable/Partition.lean` (block bookkeeping) | gluing present and scale-free; block count present, bracket proved (`stableBlockCount_mul_stableBlockLength_le_lt_succ`), asymptotic still open |
| the two `ε`-approximations of the corridor | `Walk/Path/Corridor.lean` | present (`InOpenCorridorOn.of_shrunk`, `.relax`, `corridorEnergy_add_sub`, `corridorEnergy_sub_add`) |
| `a = 2` specialisation | `Mogulskii/Gaussian/DonskerSpecialization.lean` | present (Donsker as the `a = 2` instance) |

## Two semantics problems found while doing this transcription

1. **`stableSmallDeviationRate` is the reciprocal of the paper's factor.** It is defined as
   `scale n ^ α / ((n : ℝ) * stableSlowVariation α μ (scale n))`, whereas (15) and Лемма 4 are scaled by
   `λ_n = n · L* · x^{-α} = 1 / stableSmallDeviationRate`. Every rate statement must therefore take the
   reciprocal; the name suggests the factor itself. Either a companion definition for `λ_n` should be added
   next to it, or the docstring must say which of the two it is.

2. **`stableBlockLength` drops the slowly varying factor.** It is defined as `⌊constant * scale n ^ α⌋₊`,
   whereas by (4) a stretch of `t` steps advances the walk by `B t`, `B* = u^α / L*(u)` is inverse to `B`, so
   the number of steps over which the normalized path advances by `scale n` is
   `constant * scale n ^ α / L*(scale n)` — which is also `constant * n * stableSmallDeviationRate α μ scale n`.
   The two differ by the factor `L*(scale n)`.
   * For `α < 2` in the stable domain of attraction the two tail constants `c₊, c₋` make
     `∫_{−u}^{u} x² F(dx) ~ 2(c₊ + c₋) u^{2−α}/(2 − α)`, so `L*` converges to the positive constant
     `2(c₊ + c₋)/(2 − α)`: the block length stays `Θ(scale n ^ α)` and the missing factor is absorbed into
     the free constant `constant` — at the price that the rate statement then has constant `C · lim L*`
     rather than the `C` of (15), which Лемма 1 I fixes as `a^a ln P(ξ(·) ∈ a𝔘) → C` with no `L*` anywhere.
   * For `α = 2` with finite variance the factor converges to `σ²` — the same situation. For `α = 2` in the
     normal domain of attraction with **infinite** variance (`L*` a slowly varying function tending to `∞`)
     the two normalisations genuinely differ, and no constant absorbs the discrepancy.

   **Done:** the stable route carries `L*`. `stableBlockLength α μ constant scale n` is the floor of
   `stableBlockArgument α μ constant scale n = constant * scale n ^ α / stableSlowVariation α μ (scale n)`,
   and the asymptotic lemmas take the hypothesis that `L*` stays in a positive interval at the scale (which
   the domain of attraction supplies). At `α = 2` the factor is the truncated second moment, and
   `stableBlockLength_two_of_truncatedSecondMoment_eq` recovers `diffusiveBlockLength` with the constant
   rescaled by it. `diffusiveBlockLength` of the `α = 2` branch is left untouched, its `σ²` being absorbed
   into that branch's own spectral constant.

Both items are recorded here rather than silently patched, because (1) is about the name keeping its meaning
and (2) changes a definition shared with the `α = 2` branch.
