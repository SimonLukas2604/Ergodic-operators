# Lean 4 formalization of *Self-dual perturbations of the critical almost Mathieu operator: Dry Ten Martini and Hausdorff dimension* (Paper II)

Build: `lake build SpectralGapsDimension` (same toolchain and Mathlib as Paper I; it reuses Paper I's
operators, spectra, DOS measures, gap labels and analytic norms from `AnalyticPerturbationsAMO`).

Conventions: the critical operator is `AMO.H α 1 R` (= `U + U⁻¹ + V_x + V_x⁻¹ + R_x`),
`Σ_α(R) = AMO.Sigma α 1 R`, `‖R‖_S = AMO.wnorm S S R`, `‖R‖_S < ρ` is `AMO.WSmall S S R ρ`,
admissible perturbations are `SGD.SelfDual R` (`R = R*`, `𝓕R = R`), "every label of `Λ_α` is open" is
`SGD.AllLabelsOpen α R`, and Hausdorff measure / dimension are Mathlib's `μH[d]`, `dimH`.

| File | Content | Status |
|---|---|---|
| `Arithmetic.lean` | μ_irr, β, Brjuno sum; `CFGrowth` of continued-fraction denominators; μ_irr < ∞ ⇒ 𝓑 < ∞ ⇒ β = 0; **Lemma 4.17**: 𝓑 = ∞ ⇒ μ_irr = ∞, Liouville convergents with 2πq²\|α−p/q\| ≤ q^{−M}; Λ_α = (ℤ+αℤ)∩(0,1) = {{nα} : n ≠ 0} | proved |
| `Hausdorff.lean` | covers with vanishing cost ⇒ 𝓗^d = 0; Brjuno covers (≤ 2q_n intervals, total length ≤ C/q_n) ⇒ 𝓗^{1/2} ≤ √(2C) (Cauchy–Schwarz); 𝓗^{1/2} < ∞ ⇒ dim_H ≤ ½ ⇒ zero Lebesgue measure ⇒ empty interior | proved |
| `Liouville.lean` | integrality of p_n, q_n; rational Liouville approximants; `PacketCover` (shape of Prop 4.12); the Hausdorff-cost computation of the proof of **Theorem 1.2** (corner cost 3q(2η)^d, regular cost C^{1+d}q^{A(1+K)(1+d)}h^{Nd−1}) | proved |
| `LabelArithmetic.lean` | §§3, 5 label arithmetic: exact cluster trace q\|δ\|, absolute labels (m₀p ≡ r mod q, \|m₀\| ≤ 2/Δ), r/q + n(α−p/q) = {nα}, convergent supply at β = ∞, the transfer contradiction, r ↦ 1−r symmetry of Λ_α | proved |
| `QuadrantBalance.lean` | §3 comparison family: d+c = 1, dc = b², p_t = dz⁻¹(1+(b/d)tz)², q_t lower bound; **Lemma 3.8 (quadrant balance)** QLu = Ku and the source identity QC_tΩ = tC_t′Ω | proved |
| `SmallDivisors.lean` | §4.1: Bezout trigonometric identity, divisor products ∏\|sin πmα\|⁻¹ ≤ Ψ(b)e^{(b−a)𝔟}, inverse cutoffs, scalar iteration, energy Cauchy sum, divisor-square sum | proved |
| `CornerGeometry.lean` | §§2.4, 5.2: phase contraction, Hessian nondegeneracy, Rieffel projection functions, Dirac square identity, ladder blocks and level spacings, band length, det-distance, integer-shift sign | proved |
| `RationalBloch.lean` | clock–shift matrices and the trace filter, twisted commutation ŨṼ = e^{2πi(p/q+δ)}ṼŨ, **Chambers' cycle formula** det M(z) = A⁰ + (−1)^{q−1}(z∏c + z⁻¹∏c^♯) and its transfer-matrix form, spectral containment \|𝒟\| ≤ 4+ε | proved |
| `MatrixLemmas.lean` | Sylvester inertia for complex Hermitian matrices (trace inertia, matrix version), duality transfer Γ = F(Q)Q⁻¹, transported flow identity, normalization-ODE invariance, projection sandwich, root-Gram identities, Woodbury boundary inclusion | proved |
| `IDSFacts.lean` | the IDS as a distribution function (monotone, continuous if atomless, ν(a,b] = N(b)−N(a)); level-set dichotomy; uniqueness of the DOS measure; perfectness of Σ from an atomless IDS (via full support, Paper I); the paper's open-gap notion `GapOpenWeak` and its upgrade to `AMO.GapOpen` for atomless IDS | proved |
| `ErgodicShared/AtomlessDOS.lean` (shared library, namespace `SGD`) | **Paper I, Lemma 2.8 (atomless half)**: for a norm-continuous, periodic, covariant self-adjoint family with `dim ker(H_x − E) ≤ d`, the DOS measure has no atom at `E` (continuous functional calculus only: shrinking bumps, a Cauchy limit vector in the kernel, Bessel, covariance averaging over N sites) | proved |
| `AtomlessCritical.lean` | the lemma applied to `H_{α,η}(R)` (`dos_H_atomless`); `AtomlessIDSClaim` derived from `EigenspaceBoundClaim` + `DOSExistsClaim` | proved |
| `GapLabelling.lean` | `ComparisonLabelStabilityClaim` **reduced to the classical gap-labelling theorem** (`GapLabellingClaim`: IDS at resolvent points lies in ℤ + αℤ): the label is `g(b) = ∫₀¹⟨δ₀, f(H_{b,x})δ₀⟩dx` for a fixed continuous cutoff, `g` is continuous in `b`, and a continuous function on an interval with countable range is constant | proved |
| `PaperIIIInputs.lean` | inputs discharged with Paper III's results: `DOSExistsClaim` **proved** (`CMS.exists_isDOSMeasure`); `EigenspaceBoundClaim` reduced to `JacobiPrepClaim` (Theorem 2.4: exact Jacobi preparations at spectral energies) via `CMS.JacobiPrep.finrank_ker_le_two`; final bundle `PaperIIInputsFinal`, `thm_joint_final`, `thm_liouville_final` | proved |
| `Reductions.lean` | **Prop 3.9 (transfer) reduced** to the displayed identity (gap:eq:spectral-ids-transfer) and constancy of comparison labels: the level-set argument, the continuity contradiction and the persistence of comparison gaps (‖H_b − H_{b₀}‖ ≤ 4\|b − b₀\| plus spectral stability) are proved (`transfer_of_inertia`, `comparison_resolvent_persists`); refined input bundle `PaperIIInputsRefined` and Theorems 1.1, 1.2, 3.10 under it | proved |
| `LargeWidth.lean` | Theorem 2.4's preparation **proved for widths S ≥ 7/2** from Paper I's `AMO.exists_jacobiPrep`; `JacobiPrepClaim` reduced to the small-width case `JacobiPrepSmallWidthClaim` | proved |
| `ComparisonSign.lean` | sign symmetry `H_{−b,x} = Γ(−H_{b,x+1/2})Γ⁻¹`, `Σ_{−b} = −Σ_b`, DOS transforms by `t ↦ −t`; the comparison DOS is atomless (`dos_Hb_atomless`); `ComparisonClaim` reduced to `ComparisonNonnegClaim` (0 ≤ b < 1/2) | proved |
| `Frontier.lean` | **current smallest input set** `PaperIIRemainingInputs` and **`thm_joint_main` (Thm 1.1), `thm_liouville_main` (Thm 1.2), `thm_finite_exponent_main` (Thm 3.10)** | proved |
| `MainTheorems.lean` | **Theorem 1.1** (`thm_joint`), **Theorem 1.2** (`thm_liouville`), **Theorem 3.10** (`thm_finite_exponent`), proved from the hypothesis `P : PaperIIInputs`; ‖H‖ ≤ 4 + ∑\|R\|, Σ ⊂ [−5,5], compactness, Cantor assertions, weight monotonicity | proved (conditional on the 7 stated inputs) |

The library contains **no `sorry` and no axioms**. The paper inputs whose proofs need theory absent from
Mathlib are stated as propositions (`…Claim : Prop`, not asserted) and taken as explicit hypotheses.
The headline theorems are in `Frontier.lean`: `thm_joint_main`, `thm_liouville_main` and
`thm_finite_exponent_main`, proved from `structure PaperIIRemainingInputs`, the current smallest set of
eight inputs:

| Lean | Paper | needs |
|---|---|---|
| `ComparisonNonnegClaim` | Thm 3.6 for 0 ≤ b < 1/2 | Thouless formula, Jitomirskaya–Marx continuity, rooted resolvents |
| `NormalizationClaim` | Prop 3.5 | annular Riccati analysis, small divisors in the rotation algebra |
| `InertiaTransferClaim` | eq. (gap:eq:spectral-ids-transfer) | trace inertia (being formalized on ℓ²(ℤ²)) |
| `GapLabellingClaim` | gap-labelling theorem (Bellissard; Pimsner–Voiculescu) | classical; rotation-number proof for Jacobi operators in progress |
| `InfiniteExponentClaim` | Prop 5.6 | matrix Weyl calculus, Helffer–Sjöstrand corner quantization, K-theory labels |
| `BrjunoCoverClaim` | Thm 4.1 | singular Jacobi preparation, return-block covers of BJK2026 §§7–8 |
| `PacketCoverClaim` | Prop 4.12 | semiclassical finite compressions |
| `JacobiPrepSmallWidthClaim` | Thm 2.4 for widths 0 < S < 7/2 | analytic Jacobi reduction at small width (Avila global theory, growth-based preparation) |

Earlier stages of the reduction remain valid: `PaperIIRemainingInputs.toFinal` produces
`structure PaperIIInputsFinal` (`thm_joint_final`, `thm_liouville_final`), and
`PaperIIInputsFinal.toRefined` produces the intermediate bundle `structure PaperIIInputsRefined`
(used by `thm_joint_refined`, `thm_liouville_refined`, `thm_finite_exponent_refined`):

| Lean | Paper | needs |
|---|---|---|
| `ComparisonClaim` | Thm 3.6 | Thouless formula, Jitomirskaya–Marx continuity, rooted resolvents |
| `NormalizationClaim` | Prop 3.5 | annular Riccati analysis, small divisors in the rotation algebra |
| `InertiaTransferClaim` | eq. (gap:eq:spectral-ids-transfer) | trace inertia in finite von Neumann algebras (Paper I Lemma 2.9), atomless comparison IDS (Paper I Lemma 2.8) |
| `ComparisonLabelStabilityClaim` | proof of Prop 3.9 | equivalence of nearby spectral projections (K-theory): the comparison label is locally constant in `b` |
| `InfiniteExponentClaim` | Prop 5.6 | matrix Weyl calculus, Helffer–Sjöstrand corner quantization, K-theory labels |
| `BrjunoCoverClaim` | Thm 4.1 | singular Jacobi preparation, return-block covers of BJK2026 §§7–8 |
| `PacketCoverClaim` | Prop 4.12 | semiclassical finite compressions |
| `EigenspaceBoundClaim` | Thm 2.4 (`dim:thm:center`) | analytic Jacobi reduction with nonvanishing hopping ⇒ `dim ker(H_x − E) ≤ 2` |
| `DOSExistsClaim` | §1 (definition of `N_R`) | existence of the DOS measure; **proved** in Paper III's library (`CMS.exists_isDOSMeasure`), kept separate to avoid depending on a module under development |

The coarser bundle `PaperIIInputs` (used by `thm_joint`, `thm_liouville`, `thm_finite_exponent`) has
`TransferClaim` (Prop 3.9) in place of the two transfer inputs and `AtomlessIDSClaim` (Thm 2.4 + Paper I
Lemma 2.8) in place of the last two; `PaperIIInputsRefined.toInputs` proves both from the refined inputs.

**Faithfulness audit.** Each claim was checked against the paper's statement (quantifier order,
constants, conventions, the case `R = 0`). Every claim is the paper's statement or weaker (extra
hypotheses, constants allowed to depend on more data). The one place a claim said *more* than the paper
was fixed: `AMO.GapOpen` asks the IDS to equal the label on the closed gap `[a, b]`, which at the right
endpoint also asserts that the DOS has no atom there. Prop 5.6 does not assert that, so
`InfiniteExponentClaim` now concludes the paper's notion (`AllLabelsOpenWeak`: label on `[a, b)`), and
Theorem 1.1 recovers the full `AllLabelsOpen` inside its radius from `AtomlessIDSClaim` and the uniqueness
of the DOS measure.

`#print axioms` for every result, including `thm_joint` and `thm_liouville`, shows only `propext`,
`Classical.choice`, `Quot.sound`.

**Downstream users — keep these names stable.**
- `ContinuumMagnetic/PaperIIBridge.lean` imports `SpectralGapsDimension.Reductions`. It uses `SGD.PaperIIInputsRefined`, `thm_joint_refined`, `thm_liouville_refined`, `IsDOSMeasure.unique`, `Liouville`, `muIrr` and `muSeq`.
- `SpectralGapsDimension/PaperIIIInputs.lean` imports `ErgodicShared.IDSAveraging` and `ErgodicShared.JacobiKernel`.
- `CriticalAMOHausdorff` imports the helper lemmas in `Arithmetic`, `Hausdorff`, `MatrixLemmas` and `SmallDivisors`.
