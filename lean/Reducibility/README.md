# Reducibility of analytic one-frequency cocycles (Paper I, §"Rotations reducibility")

Library `Reducibility`, namespace `Red`. To build it: `lake build Reducibility` (it is also a
default target).

It formalizes Paper I's Lemmas `t-lem:reducibility` and `t-lem:arithmetic-reducibility` in
`PaperLemmas.lean`.

## Convention

Three external cocycle theorems are stated as named propositions in `Claims.lean`. They are never
asserted, and both lemmas take them as the hypothesis `I : ReducibilityInputs`:

| Claim | Source | Content |
|---|---|---|
| `AlmostReducibilityClaim` | Avila, ARC, Thm 1 | subcritical ⇒ almost reducible |
| `RotationsReducibilityClaim` | Avila, ARAC, §1.2, Thm 1.4, Cor 1.5; Avila–Fayad–Krikorian, Thm 1.3 | almost reducible and `ρ` in a full-measure set ⇒ analytically rotations reducible by a degree-zero conjugacy |
| `ArithmeticReducibilityClaim` | Ge–Jitomirskaya, Thm 9.2, Rem 9.1, App. B | subcritical on `\|Im z\| < h` with `2πh > β(α)` and `ρ ∈ Θ_α` ⇒ reducible to a constant rotation |

## What is proved

| File | Content |
|---|---|
| `Basic.lean` | rotation matrices; conjugacies `A(x)Z(x) = Z(x+α)B(x)`; telescoping of iterates; **uniform bounds (t-eq:all-irr-bounded)** for rotations-reducible cocycles; bounded iterates ⇒ `L = 0`; **degree normalization** `Z = B·R_{-dx}` (integer and half-integer `d`) |
| `Diophantine.lean` | `Θ_α` and `Θ_{α,τ}`; **`Θ_α` has full measure** (Borel–Cantelli); the resonant set `4r ∈ 2αℤ + ℤ` is null; **probability integral transform** `N_*(dN) = dt`; hence `dN{E : ρ(E) ∈ S} = 0` for every null `S`, where `ρ = (1-N)/2` |
| `SmallDivisors.lean` | Jordan's inequality `\|e^{2πit} - 1\| ≥ 4‖t‖`; **exponential small divisors** (t-eq:exponential-small-divisor) `\|e^{2πikα} - 1\| ≥ c_δ e^{-(β+δ)\|k\|}`; **cohomological equation** `χ(x+α) - χ(x) = p(x) - p̂(0)`, solved with weighted summability and a real solution |
| `Claims.lean` | analytic `SL(2,ℝ)` cocycles on strips; subcriticality; fibered rotation number (via a lift of the projective action); almost / rotations / constant-rotation reducibility; the three claims |
| `PaperLemmas.lean` | **Lemma `t-lem:reducibility`**: on a Borel set of full `dN` measure, `C_E` is rotations reducible and its iterates are bounded. **Lemma `t-lem:arithmetic-reducibility`**: on a Borel set of full `dN` measure, `C_E` is reducible to a constant rotation, `ρ(E) ∈ Θ_α`, and both nonresonance conditions hold; the hopping coboundary has a real analytic solution |

`SmallDivisors.lean` imports the best-approximation lemma from `CriticalAMOHausdorff`, which is
another session's library.

## Simplifications

- The spectral setting is abstract. The lemmas take as hypotheses: `ν` (the IDS measure, with a continuous distribution function), a Borel set `Σ`, a family of analytic cocycles, and `ρ(E) = (1 - N(E))/2` as their fibered rotation number.
- Degree normalization is proved as an algebraic identity. Winding numbers are not formalized, so `ReducibleToRotation` does not record the degree.

## In progress: Avila–Fayad–Krikorian (`AFK/`)

These files formalize the KAM scheme behind the AFK part of `RotationsReducibilityClaim`: Theorem
`theorem.cd` of arXiv:1001.2878, whose source is in `AFK/afk_source.tex`. So far the foundations are
done; all three files are proved, with no `sorry`.

| File | Content |
|---|---|
| `AFK/Analytic.lean` | strip norms; **Cauchy estimates** on strips (derivative bound, difference bound, translation bound); complex rotation algebra, including `(R_{2θ} - I)⁻¹`; the **𝒬 projection** and identity (Q); projection onto rotations `soProj` with the estimate `‖soProj M - M‖ ≤ (‖M‖+2)‖𝒬M‖` |
| `AFK/Elliptic.lean` | **Lemma `elliptic`**: a matrix near a non-degenerate rotation is conjugate to a rotation, with `‖B - I‖ ≤ C‖R_θ⁻¹A - I‖/‖R_{2θ} - I‖` (stronger than the paper's bound) and `\|θ' - θ\| ≤ C‖R_θ⁻¹A - I‖`; real inputs give a real conjugacy |
| `AFK/Birkhoff.lean` | **§3**: Fourier form of Birkhoff sums; **Lemma `denjoy.el`**; CD bridges and **Lemma `dioph.bridge`** (corrected); **Corollaries `cor3`, `cor4`**; **Proposition `denjoy`** with one constant uniform in α |

Corrections to the paper found while formalizing:

- **Lemma `elliptic`:** its domain condition `‖R_θ⁻¹A - I‖ < ε·max(1, ‖R_{2θ} - I‖²)` admits parabolic matrices. The correct condition uses `min`.
- **Lemma `dioph.bridge`:** with CD(A,A,A³) bridges it is false. An explicit denominator configuration admits no such chain. The proof uses CD(A,A,A⁴) bridges, which changes the exponent `U` to `A⁵`. The bound `Q_{k+1} ≤ Q̄_k^{16M⁴}` of Proposition `denjoy` is unchanged.
- **Corollaries `cor3`, `cor4`:**
  - the paper writes `S_{q_n}φ` and `lφ̂(0)` where it means `S_{q_n}φ - q_nφ̂(0)` and `mφ̂(0)`;
  - `T₀` must also depend on `η`.

Still missing:

- **Proposition `CT`** (the inductive step): Lemma `elliptic` applied along a strip, `N` steps with Cauchy estimates, and the commuting-cocycle argument.
- **Lemma `Aq`** and **Proposition `prop.inductive`**, which need fibered-rotation-number theory.
- **The final iteration** proving Theorem `theorem.cd`.
- **Holomorphic dependence:** the conjugacy in Lemma `elliptic` is not shown to depend holomorphically on the matrix. Prop `CT` needs this to keep `B_i` analytic in `x`.
