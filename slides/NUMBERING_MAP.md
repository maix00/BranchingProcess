# Numbering map (PDF → slides)

The thesis source uses internal LaTeX labels (e.g. `lemma:4.8`).  
In slides we **never cite labels**; we cite the **printed numbering** as it appears in `docs/main.pdf`.

When updating the thesis, check `docs/main.pdf` and update this file to keep slides consistent.

## Lemmas / Theorems / Assumptions used in slides (from `docs/main.aux`)

- `proposition:3.1` → **Theorem 1.1** (trajectory limit in $\mathrm L^2$)
- `theorem:mogulskii` → **Theorem 2.4** (Mogul'skii, small deviations)

- `lemma:4.1` → **Lemma 3.4** (horizontal tube small deviation)
- `lemma:2.3` → **Lemma 3.5** (no large drop small deviation)
- `lemma:4.2` → **Lemma 3.6** (small deviation with small drift / tilted tube)
- `lemma:4.3` → **Lemma 3.7** (lower bound under tilted tube end constraint)
- `lemma:4.5` → **Lemma 3.8** (second-moment bound; where Assumption 6 is used)
- `lemma:4.6` → **Lemma 3.9** (tube existence at scale $L^{1/3}$; Paley--Zygmund)
- `lemma:4.7` → **Lemma 3.10** (log-scale tube probabilities / expectations)
- `lemma:4.8` → **Lemma 3.17** (coupling $N$-BRW and killed BRW)

## Assumptions

- `assumption:log-expt-cross-sum-exp-neg-sum` → **Assumption 6** (finite cross second moment)
- `assumption:moment-exp-1` → **Assumption 9** (exponential moment of the leftmost step, used for the $a=0$ extension)
