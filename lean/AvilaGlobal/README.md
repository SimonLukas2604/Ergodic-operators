# Lean 4 formalization of Avila, *Global theory of one-frequency Schrödinger operators I*

Source: `../../avila_global_theory_I.tex`.  Build: `lake build AvilaGlobal` (it is also one of the
default targets).  The library has no `sorry`.  `#print axioms` on every headline theorem shows
only `propext`, `Classical.choice`, `Quot.sound`.

## What is assumed

Every result of the paper itself is proved, and so are all the inputs it cites except one: the
continuity theorem [JKS], which is *stated, not asserted*.  They appear as hypotheses in
the statements that use them:

| Hypothesis | Where | Content |
|---|---|---|
| `Hypotheses.jks` | `Background.lean` | [JKS]/[BJ1]: joint continuity of `L` at irrational frequencies |

A theorem that depends on the first group carries the instance argument `[Hypotheses]`.
(Inside `Stratified`, `Codimension` and `AlmostMathieu` it is a section variable, so some
auxiliary lemmas carry it even though they don't use it.)

## What is proved

| File | Content |
|---|---|
| `Basic.lean` | analytic `SL(2,ℂ)` cocycles on strips, `A_ε`, `L(α, A_ε)`, acceleration, regularity, `𝒰ℋ`, Schrödinger cocycles, `Σ`, stratifications |
| `Background.lean` | **convexity of `ε ↦ L(α, A_ε)`** (`L_convexOn`), via Jensen's formula, a sub-mean-value inequality, a maximum principle and limits of convex functions |
| `Quantization.lean` | **Theorem `quantized`**: the acceleration exists and is an integer for irrational `α`.  Full proof from [JKS]: `tr A_{(p/q)}` is `1/q`-periodic, the Gelfand formula and trace bounds for `ρ`, `L(p/q, A) = (1/q)∫ log ρ`, Fourier decay, a Mahler-measure lower bound (a step the paper skips), the piecewise-linear asymptotics, and limits of piecewise-linear convex functions |
| `UniformHyperbolicity.lean` | Lemma `ang` (quantitative), the identities for `u.l.c.` and the derivative coefficients |
| `Stratified.lean` | real symmetry (`L` is even, `ω ≥ 0`), piecewise affinity, regular ⇔ `ω = 0`, upper semicontinuity of `ω`, the easy direction and full statement of **Theorem `uniformly hyperbolic`**, **Corollary `alter`**, **Proposition `pluri`** (both parts), **Theorems `e`, `v`, `frequen`** (stratified analyticity / smoothness) |
| `Codimension.lean` | `C^ω_δ(ℝ/ℤ, ℝ)` as a normed space, conjugacy invariance of `L`, rotation cocycles have `L = 0`, Schwarz reflection, the algebra of `q₂, q₃`, and **Theorem `cod`** from `cod1` |
| `AlmostMathieu.lean` | **Theorem `am1`** (with the cone-field computation done explicitly), **Corollary `am2`** (Aubry–André), **Example Theorem** |
| `UHOpen.lean` | **openness of `𝒰ℋ`** (`uh_open`), via cone fields and a graph transform |
| `Johnson.lean` | **Johnson's theorem** (`johnson`): `E ∉ Σ ⇔ (α, A^{(E-v)}) ∈ 𝒰ℋ` for irrational `α`, via the Green's function and exponential dichotomy |
| `RegularUH.lean` | **the hard direction of Theorem `uniformly hyperbolic`** (`regular_pos_imp_uh`: regular with `L > 0` ⇒ UH) and **Lemma `per`**, from [JKS] alone: the trace estimate for periodic approximants, spectral projections, a log-derivative bound in place of Lemma `gam`, then Arzelà–Ascoli and Weyl equidistribution in place of the normality argument |
| `UHAnalytic.lean` | **real-analytic dependence of `L` on `𝒰ℋ`** at fixed frequency (`uh_analytic_family`, one half of [HPS]): the family as an analytic map into bounded continuous functions, the invariant graph by the analytic implicit function theorem, and an analytic log-integral |
| `UHSmooth.lean` | **`C^∞` dependence of `L` on `𝒰ℋ` jointly in frequency and parameters** (`uh_smooth_family`, the other half of [HPS]), rationals included: projective approximants with exponential contraction, Cauchy estimates along complex lines, and a summable series of smooth functions |
| `DerivFormula.lean` | **the derivative formula** for `L` on `𝒰ℋ` (§3.2), for every `α`, via graph transforms (no [HPS] needed) |
| `Cod1.lean` | **Theorem `cod1`** and **Theorem `cod`**: joint analyticity of `(v, z) ↦ v(z)` on `C^ω_δ`, diagonalising frames, the extension of `q₃`, `q₂`, `q₁` across `ℝ`, and a holomorphic-logarithm argument in place of the paper's rotation/homotopy step |
| `RationalExample.lean` | Remark `rational`: at `p/q` with `q ∣ q₀` the diagonal example has `L = (2/π)e^{-2πq₀ε}` and acceleration `-2q₀/π ∉ ℤ`; `L = 0` at irrational `α` |

## Corrections to the paper's statements found while formalizing

* §2: the bound `log ρ(B) ≤ max(0, log|tr B|)` is false (`tr B = 2i`).  We use
  `log ρ ≤ log(1 + |tr B|)`, which is enough for the argument.
* §4: with the paper's own definition `q₃ = -ba`, the formula is `q₃ = -us/(u - s)` (the paper
  omits the sign).
* Proposition `pluri`, second part: it needs `j ≠ 0`, since `Ω_{δ,j}` is only defined for `j ≠ 0`.
  The constant cocycle `A ≡ 1` has `ω = 0` and no uniformly hyperbolic shift.
* Example Theorem: the paper says "for `ε` small, for every `α`", but its proof fixes `α` first,
  and that is the form stated here.

* §4: "`q₂, q₃` purely imaginary on `ℝ` ⇒ `u, s` complex conjugate" does not follow on its own
  (`u`, `s` could both be purely imaginary).  `Cod1.lean` avoids this step: it also extends `q₁`
  and uses `q₁² + 4q₂q₃ = 1`.

## Audit of the assumed statements

An independent check of every hypothesis against the formal definitions (looking for
counterexamples) found two errors, both now fixed:

* `Hypotheses.uhOpen` was false as first stated.  It did not require the approximating cocycles
  `As n` to be continuous `1`-periodic SL cocycles, and a non-periodic perturbation of a
  hyperbolic constant cocycle is never UH.  It now assumes `∀ᶠ n, IsSLCocycle (shift (As n) 0)`.
  Until this was fixed, the class `Hypotheses` was unsatisfiable and every theorem carrying
  `[Hypotheses]` held vacuously.
* `DerivFormulaClaim` was false: swapping the columns of `B` flips the sign.  It now requires the
  first column of `B` to be the expanded (unstable) direction.  Nothing used it.

`jks`, `uhAnalytic`, `uhSmooth` (C^∞, not analytic, in the frequency, rationals included, as
[HPS] gives), `johnson`, `regularPosUH`, `PerClaim` and `Cod1Claim` (now with `0 < δ` and
irrational `α` as premises) were found to be correct.
