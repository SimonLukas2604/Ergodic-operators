# Ergodic operators: Lean 4 formalizations

Lean 4 / Mathlib formalizations around the almost Mathieu operator and one-frequency quasi-periodic
Schrödinger operators. The Lean project is in [`lean/`](lean/). All libraries share one Lake
project, one toolchain (`leanprover/lean4:v4.35.0-rc3`) and one Mathlib.

| Library | Source | Namespace | README |
|---|---|---|---|
| `AnalyticPerturbationsAMO` | S. Becker, *Analytic perturbations of the almost Mathieu operator: Dry Ten Martini and spectral transitions* (Paper I) | `AMO` | [lean/README.md](lean/README.md) |
| `SpectralGapsDimension` | S. Becker, *Self-dual perturbations of the critical almost Mathieu operator: Dry Ten Martini and Hausdorff dimension* (Paper II) | `SGD` | [README](lean/SpectralGapsDimension/README.md) |
| `ContinuumMagnetic` | S. Becker, *Periodic magnetic Schrödinger operators: Dry Ten Martini and spectral transitions* (Paper III) | `CMS` | [README](lean/ContinuumMagnetic/README.md) |
| `CriticalAMOHausdorff` | Becker–Jitomirskaya–Krasovsky, *Critical almost Mathieu operator: hidden singularity, gap continuity, and the Hausdorff dimension of the spectrum* (arXiv:1909.04429v2) | `CAH` | [README](lean/CriticalAMOHausdorff/README.md) |
| `AvilaGlobal` | A. Avila, *Global theory of one-frequency Schrödinger operators I* | | [README](lean/AvilaGlobal/README.md) |
| `Reducibility` | reducibility of analytic one-frequency cocycles (Avila–Fayad–Krikorian), used in Paper I | `Red` | [README](lean/Reducibility/README.md) |
| `DamanikFillman` | Damanik–Fillman, *One-dimensional ergodic Schrödinger operators* (work in progress; not a default target) | | |

## Building

```bash
cd lean
lake exe cache get   # download prebuilt Mathlib
lake build           # builds all default targets
```

Every push runs the same build on GitHub Actions ([workflow](.github/workflows/lean.yml)). The check
fails if the build fails or if any declaration uses `sorry`.

## What is and is not proved

The libraries contain no `sorry` and add no axioms: `#print axioms` on the headline theorems shows only
`propext`, `Classical.choice` and `Quot.sound`.

Some results of the papers rest on deep theory that Mathlib does not (yet) provide: von Neumann
algebra traces, K-theory of rotation algebras, Weyl and semiclassical calculus, Avila's global
theory. Those results are stated faithfully as propositions (`…Claim : Prop`). They are **not
asserted**: they enter the main theorems as explicit hypotheses. A main theorem therefore reads
"if these stated inputs hold, then the theorem holds". Each library's README lists its inputs and
what proving them would require.

Paper sources and PDFs are not included in this repository.
