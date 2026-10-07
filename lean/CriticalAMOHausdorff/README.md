# Lean 4 formalization of *Critical almost Mathieu operator: hidden singularity, gap continuity, and the Hausdorff dimension of the spectrum*

S. Becker, S. Jitomirskaya, I. Krasovsky (arXiv:1909.04429v2). Library `CriticalAMOHausdorff`, namespace `CAH`.

Build: `lake build CriticalAMOHausdorff` (Lean `v4.35.0-rc3`, Mathlib master).

**Theorem 1.1 is fully formalized.** `CAH.dimH_spectrum_le_half` proves dim_H σ(H_{α,θ}) ≤ 1/2 for every irrational α and real θ, and also 𝓗^{1/2}(σ) < ∞. `CAH.volume_spectrum_eq_zero` proves Theorem 1.2. `CAH.thm_cover` proves Theorem 7.11 (`thm-cover`), and `CAH.measure_convergence'` proves Theorem 1.3. None of these has a hypothesis beyond the paper's. `#print axioms` lists only `propext`, `Classical.choice` and `Quot.sound`. The library contains no `sorry` and no `axiom`.

| File | Content |
|---|---|
| `Basic.lean` | Jacobi matrix (1.3) on ℓ²(ℤ); critical AMO `amo`; chiral operator `chiral` (1.2); σ(M_{v,b,α}) |
| `ContinuedFractions.lean` | §2.3: (2.4)–(2.7), δ_n sign/size, best approximation, **Lemma 7.2** `lemma-rt` (first return times q_n / q_{n−1}), ∑ 1/sin²(πkα) ≤ 4q_n² |
| `ChiralGauge.lean` | §3: operators T, S^x, U_x, R on functions ℤ×ℝ→ℂ; all commutation relations incl. RS = T⁻¹R, RT = SR; **Theorem 3.1** Q(T²+T⁻²+S+S⁻¹) = H̃Q; fibre identities |
| `ChiralSpectrum.lean` | Plancherel for trigonometric polynomials; R and Q isometric; **σ(H_{α,θ}) ⊆ closure ⋃ₓ σ(Ĥ_{α/2,x})** via approximate eigenvectors |
| `ChiralUnitary.lean` | reverse inclusion σ(Ĥ_{α/2,x}) ⊆ σ(M_α); **isospectrality σ(M_α) = σ(M̃_{α/2})** (`sigmaAMO_eq_chiral`) |
| `ChiralUnitaryL2.lean` | L²(𝕋;ℓ²(ℤ)) as a Hilbert space; T, Sˣ, U_x, R, Q as unitaries (R via the fibrewise Fourier transform, given by (3.4) with L²-convergent sum); **Theorem 3.1 as an identity of bounded operators**, Q(T²+T⁻²+S+S⁻¹)Q⁻¹ = M̃_α (`chiralrepresentthm`) |
| `ChiralDOS.lean` | **Lemma 4.1** (`dn`): N_{2α} = Ñ_α, via equality of all moments and Weierstrass |
| `TestFunctions.lean` | **Lemma 5.3** `lemma-commut0`: the test functions f_{m,L}, commutator entries (5.5), bounds (5.6) |
| `AMSCore.lean` | Weyl criterion for self-adjoint operators; the AMS quantitative core (5.10)–(5.13) |
| `GapContinuity.lean` | Denjoy–Koksma special case (proved directly); **Lemma 5.1** `lemma-S`; superlinearity (5.2); **Theorem 5.2** `continuitylemma1`: (5.7), (5.8), (5.9) |
| `MeasureConvergence.lean` | one-sided Hausdorff continuity (replaces [AS1983, El82]); **Theorem 1.3** |
| `RationalBands.lean` | Floquet–Bloch theory: Bloch matrices, discrete Floquet transform with Plancherel, σ(H_θ) = ⋃_k σ(Bloch matrix); σ(M_{p/q}) is a union of ≤ q closed intervals; **Theorem 1.3 unconditional** (`measure_convergence'`) |
| `PaperHypotheses.lean` | the paper's literal hypotheses: C¹ 1-periodic ⇒ bounded and Lipschitz, finitely many zeros per period ⇒ countable zero set, **bounded partial quotients ⇔ Diophantine bounded type**; Lemma 5.1, Theorem 5.2 ((5.7), (5.8) for all n ≥ 1, (5.9) with the explicit r_n) and Theorem 1.3 restated with these hypotheses (`lemma_S_paper`, `continuitylemma1_paper`, `measure_convergence_paper`) |
| `GrapheneLaxPair.lean` | Appendix, Theorem 9.1: graphene Jacobi blocks G_N(x), κ_r, K^g_N; the commutator identity G_N' = [K^g,G_N] + E_N (checked numerically, no typos found); E_N Hermitian, rank ≤ 4, trace-norm bound |
| `GrapheneCover.lean` | Remark after Prop 7.3 (complex b) via gauges; cover of Σ_Φ by ≤ q_n+q_{n−1} intervals of length ≤ C/q_n; **dim_H Σ_Φ ≤ 1/2 unconditionally** (`dimH_SigmaPhi_le_half`) |
| `GrapheneQuantumGraph.lean` | the dimension step through locally Lipschitz branches (proved); **Theorem 9.1** (`dimH_graphene_le_half`) from the [bhj] spectral reduction `BHJReduction` |
| `LastBound.lean` | **Last's bound (1.6)**: \|σ(M_{p/q})\| ≤ 16π/q for all coprime p/q (Chambers-type formula via the chiral gauge, after [JKK]); the paper's **second proof of Theorem 1.2** (`volume_sigmaAMO_eq_zero'`) |
| `BoundaryResolvent.lean` | ABBA identity, Neumann series, the finite-dimensional block step of Lemma 7.1 `lemma-subm` |
| `BlockSeparation.lean` | block-diagonal operators on ℓ²(ℤ); **Lemma 7.1** `lemma-subm` (`lemma_subm_jacobi`); **Proposition 7.3** `prop-blocks` |
| `OrderedEigenvalues.lean` | ordered eigenvalues, min–max monotonicity, trace norm, triangle inequality, **Lidskii inequality** |
| `EigenvalueFlow.lean` | **Lemma 7.5** `lemma-flow` (Σ Var λ_j ≤ ∫‖𝓔‖₁), abstract core of Proposition 7.9 `prop-cover1` |
| `LaxPair.lean` | **Lemma 7.6** `lemma-commut` (d/dx B_N = [K_N,B_N] + 𝓔_even + 𝓔_edge, checked numerically, no typos found), **Lemma 7.7** `lemma-commut2` (rank ≤ 4), Hilbert–Schmidt bounds |
| `BlockCover.lean` | **Propositions 7.8–7.9** (`prop-phase-variation`, `prop-cover1`) with explicit constants |
| `SpectralCover.lean` | cut points from return times, sign gauge for b = 2 sin π·, Theorem 7.11 for Ĥ |
| `HausdorffDim.lean` | §8: Hölder (8.1), 𝓗^t = 0 for 1/2 < t < 1, dim_H ≤ 1/2 from covers |
| `MainTheorems.lean` | **Theorems 7.11 (`thm-cover`), 1.1, 1.2** for H_{α,θ}, M_α and Ĥ |

## Deviations and conventions

- **σ(M_{v,b,α})** is defined as the closure of ⋃_θ σ(H_{v,b,α,θ}). For continuous fibres this is the spectrum of the direct integral.
- **Theorem 1.2** is proved twice. One proof derives it from Theorem 1.1, since dim_H < 1 forces Lebesgue measure zero. The other is the paper's second proof: Theorem 1.3 together with Last's bound (`LastBound.lean`, constant 16π rather than Last's 8e). The Kotani-theory proof of §4 is not formalized.
- **Theorem 3.1** is proved literally: Q is unitary on L²(𝕋;ℓ²(ℤ)) (phases represented in (0,1], which differs from [0,1) only on a null set). The decomposable operator M̃_α is defined by the paper's S/T expression; its fibres are identified almost everywhere (`Mfun_ae`). Lemma 4.1 proves that DOS measures, assumed to exist (the library's `IsDOSMeasure` convention), coincide.
- **Theorem 1.3** is `measure_convergence'`, fully proved, with the rational-frequency band structure derived from Floquet–Bloch theory in `RationalBands.lean`. The core files work with Lipschitz bounds, a Diophantine bounded-type condition and a countable zero set. `PaperHypotheses.lean` derives these from the paper's C¹, bounded-partial-quotient and finite-zeros hypotheses and restates the results in the paper's form.
- **Norms of 2×2 perturbations** V are stated either as ℓ² operator norms or as eigenvalue bounds. `norm_le_iff_abs_eigenvalues_le` converts between the two.
- **Theorem 9.1 (graphene)** is formalized in two parts. The Jacobi-matrix statement dim_H Σ_Φ ≤ 1/2 is proved unconditionally. For the quantum-graph spectrum σ^Φ, the spectral reduction from [bhj, (5.3)–(5.4), Lemma 4.1, §8] enters as the single stated input `BHJReduction`, because the quantum-graph Hamiltonian of [bhj, (3.7)] is not available in Mathlib. The affine constants a, b and the branch domains in `BHJData` were read off the companion manuscript and should be checked against [bhj].
