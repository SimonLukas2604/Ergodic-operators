# Lean 4 formalization of *Periodic magnetic Schrödinger operators: Dry Ten Martini and spectral transitions* (Paper III)

Library `ContinuumMagnetic` (namespace `CMS`). It builds on Paper I's library
`AnalyticPerturbationsAMO` and shares its Lean toolchain and Mathlib.

To build: `lake build ContinuumMagnetic`.

## Convention: claims instead of `sorry`

Two kinds of results are stated as **named propositions** (`…Claim : Prop`) and are never asserted:

- results imported from Papers I–II that are not proved in Lean;
- the semiclassical continuum constructions of the paper, which need theory Mathlib lacks.

Every main theorem *takes these claims as hypotheses*, so the library contains no `sorry` and no axioms beyond Lean's standard ones. There are two bundles of hypotheses:

- `PaperInputs` (`AnalyticInput.lean`): the analytic input.
  - From Paper I: `AMO.DryTenMartiniUniformClaim`, `AMO.SpectralTransitionUniformClaim`, `AMO.CriticalClaim`. Two further Paper I facts not covered by its Lean development: `RegularRepDominationClaim` (Lemma 3.5) — **now proved** (`regularRepDomination`; use `PaperInputs.ofCore`) — and `CriticalIDSAtomlessClaim` (Lemma 2.8) — **now derived from `AMO.CriticalClaim`** (`criticalIDSAtomless_of_critical`). With both, `PaperInputs.ofMain` builds the whole analytic input from Paper I's three main theorems and the Paper II input.
  - From Paper II: `CriticalGeometricInputClaim`.
- `ContinuumInputs` (`MainTheorems.lean`): the exact continuum reductions.
  - `CosineReductionRectClaim`, `CosineReductionSquareClaim`: §3, exact well basis, tunneling and WKB.
  - `SquareBranchExpansionClaim`, `RectBranchSeparationClaim`: local branch energies.
  - `LandauReductionClaim`: §5, exact Landau-band reduction.

These are not formalized because they need:

- the spectral theorem and Borel functional calculus for unbounded self-adjoint operators;
- Agmon estimates and Helffer–Sjöstrand multiple-well theory;
- WKB constructions and Landau-level compression;
- for the Paper I/II inputs: Avila's global theory, reducibility, and Kotani theory.

## Files

| File | Content (paper label) | Status |
|---|---|---|
| `Basic.lean` | field path `𝓑 = 2πhγ/μ`, cosine potential, harmonic levels, `S_cos`, Weyl symbol `c_{r,q} = e^{πiγrq} f_{r,q}`, lattice distances | definitions |
| `Covariance.lean` | magnetic translations: `T₁T₂ = e^{2πiγ}T₂T₁`, composition law of `S_m`, covariance of the magnetic Schrödinger expression; coefficient symmetries (twisted adjoint, rotation); **Cor. `c-cor:critical`** (self-duality `𝓕(c) = c`, `f_{1,0} = f_{0,1} ∈ ℝ`); normalization and Fourier orientation; axial gauge; guiding-center orientation | proved |
| `ExactInteraction.lean` | an operator commuting with the magnetic translations, written in the basis `S_mφ₀`, *is* the Weyl series `op2 (-γ) c` (eq. `full-lattice-generators`); self-adjointness of the symbol; norm bound | proved |
| `PolarBasis.lean` | **Prop. `c-prop:projected-completeness`**: polar orthonormalization `𝒰 = 𝒱K^{-1/2}` is unitary onto `Ran 𝒱`; covariance; **`c-prop:weighted-polar`** in operator norm (`‖K^{-1/2} - 1‖ ≤ ‖K - 1‖`, reference transfer) | proved |
| `CosineActions.lean` | **Lemma `c-lem:cosine-actions`**: Agmon distance (C¹ curves) of the cosine well `D(r,q) = \|r\|S₁ + \|q\|S₂`, attained; `D` is a lattice distance; `S_rem = 2min(S₁,S₂)`; multiplicity `d_{λ_N} = N+1` | proved |
| `SquareShell.lean` | **Prop. `ex-prop:square-splitting`**: the magnetic splitting matrix `K_N` is Hermitian and, for `b ≠ 0`, has `N+1` distinct eigenvalues and eigenvectors with nonzero end coordinates; the `h²` branch separation from an energy expansion | proved |
| `GoodIndices.lean` | **Thm `thm:high-energy-spectrum`, density part**: `{n : \|cos(2√(ns_B) - π/4)\| ≥ Kε}` has natural density `1 - (2/π) arcsin(Kε)`; `𝒢₀` has density one; Laguerre form factor | proved |
| `PhysicalLocalization.lean` | the physical-localization step of **`thm:continuum-types`**: exponentially decaying lattice eigenvectors give physically localized continuum eigenfunctions (`∫ e^{2b\|x₁-x₀\|}\|Ψ\|² < ∞`) | proved |
| `HallLabels.lean` | **Thm `thm:physical-hall`**, arithmetic: uniqueness of gap labels `r + kα`, Hall integers `-k` and `-⌊kα_B⌋`, physical densities and local lines, Středa derivative giving `-k`, `r`, `0`, `1`; block labels | proved (Chern number via Středa) |
| `UnitaryTransfer.lean` | spectral vocabulary on general Hilbert spaces; invariance of spectrum and spectral types (a.c., s.c., eigenbasis) under unitary equivalence | proved |
| `Affine.lean`, `AffineIsland.lean` | the affine energy change `Φ(E) = E₀ + aE` (either sign) on spectral measures and types, Cantor sets, DOS measures and gap labels (`1 - {nα} = {-nα}`); `op2` linearity and self-adjointness | proved |
| `AnalyticInput.lean` | **Thm `thm:analytic-input`** (i)–(iv) from Paper I's claims; uniqueness of the DOS measure; the claims and `PaperInputs` | proved from claims |
| `ScalarCriteria.lean` | **Thms `thm:noncritical-continuum`, `thm:continuum-2d-ac`, `thm:continuum-types`, `thm:continuum-SC`** for any exact scalar-island reduction (`IslandReduction`), in both orientations, with the sufficient conditions `β < log(t₂/t₁) - Cε` and `β > log(t₂/t₁) + Cε` | proved from `PaperInputs` |
| `CriticalCriteria.lean` | **Thm `thm:critical-continuum`**: zero-measure dry Cantor island, purely s.c. 2D island, `L(E,y) = 2π\|y\|`, s.c. fibres for `β > 0`, `𝓗^{1/2} < ∞`, `dim_H ≤ 1/2`, and `dim_H = 0` at ordinary Liouville flux | proved from `PaperInputs` |
| `MainTheorems.lean` | **Thm `cor:cosine`** for `μ ≠ 1` (`cosine_rectangular`) and `μ = 1` (`cosine_square`); branch separation; **Thm `thm:high-energy-spectrum`** (`high_landau`); the continuum claims and `ContinuumInputs` | proved from `PaperInputs` + continuum claims |
| `HighLandauCorollaries.lean` | **Cor. `cor:high-energy-fibres`**: a.e. Bloch fibre has spectrum `𝒞_n`; a.c. for `a_y > a_x`; for `a_x > a_y` a complete eigenbasis on `{𝓛_n > β}`, no a.c. component, s.c. on `{𝓛_n < β}`, the sufficient conditions `β ≶ log(a_x/a_y) ∓ C‖R_n‖`, and localization of the whole cluster when `β(α_B) = 0`; (iv) s.c. fibres at criticality when `β > 0`. **Cor. `cor:high-critical-dimension`**: all gaps open, `𝓗^{1/2}(𝒞_n) < ∞`, and `dim_H 𝒞_n = 0` at Liouville flux. **The `W = 0` statements** on the density-one set `𝒢₀` for Thm `thm:high-energy-spectrum` and Cor. `cor:high-critical-dimension` | proved from `PaperInputs` + `LandauReductionClaim` |
| `PhysicalHall.lean` | **Thm `thm:physical-hall`**: Hall integers `-k` (low energy), `r` and `-⌊kα_B⌋` (high energy), `0` and `1` for the full projections, and every nonzero relative Hall integer realized. **Lemma `lem:magnetic-gap-persistence`** is stated as a spectral-continuity bound (`GapPersistenceBound`); its consequence, that gaps persist under small changes of the field, is proved (`gap_persists`) | proved (the local-line density from `lem:physical-trace` is a hypothesis) |
| `PaperIIBridge.lean` | `criticalGeometricInput_of_paperII`: the Paper II input derived from the Paper II formalization (`SpectralGapsDimension`) | proved from Paper II's inputs |
| `RegularRep.lean`, `RegularRep/*.lean` | **Paper I, Lemma 3.5 proved** (`regularRepDomination : RegularRepDominationClaim`): every spectral measure of `op2 α K` on `ℓ²(ℤ²)` is `≪` the IDS. The proof needs only the continuous functional calculus: existence of spectral measures by Riesz–Markov–Kakutani (`SpectralMeasureExists`), the maximal-spectral-type lemma for an orthonormal basis (`MaximalType`), and the trace identity `spectral measure of δ_p = ν` (`TraceIdentity`, via `op2` multiplicativity and Weierstrass). `PaperInputs.ofCore` builds `PaperInputs` without this claim | proved |
| `IDSAtomless.lean`, `RegularRep/{AtomEigen,JacobiKernel,IDSAveraging}.lean` | **Paper I, Lemma 2.8 (atomless part) from Theorem 1.6** (`criticalIDSAtomless_of_critical : CriticalClaim → CriticalIDSAtomlessClaim`): the IDS exists (spectral measure of `op2` at `δ₀`); atoms of spectral measures are eigenprojections (`μ_v{E} = ‖P_E v‖²`); the exact Jacobi preparation gives `dim ker(H_x − E) ≤ 2`; covariance and averaging over `N` sites give `ν{E} ≤ 2/N`. `PaperInputs.ofMain` | proved from `CriticalClaim` |

## Modelling choices

- **Continuum island operator.** `H_h^island` is a bounded operator on an abstract Hilbert space. Its exact reduction (`IslandReduction`) is a unitary equivalence with the lattice operator `op2 α c`, together with fibre-wise unitary equivalences with `op α c x(k)` for almost every Bloch phase.
- **Link to the physical operator.** `RealizesMagnetic` records that the island operator is a restriction of `(hD₁)² + (hD₂ - 𝓑x₁)² + V`, acting weakly on test functions in `L²(ℝ²)`. That the island is the *full* spectral subspace `Ran 𝟙_{I_h}(H_h)` cannot be stated without the unbounded spectral theorem; it is part of the continuum claims.
- **Simplifications:**
  - Agmon curves are C¹ rather than absolutely continuous.
  - Hall integers are computed by the Středa formula from the physical densities, not from the trace-per-unit-area Chern character.
  - Spectral measures are characterized through the continuous functional calculus, as in Paper I.
- **Coverage:** every numbered result of §1 now has a Lean counterpart. The fibre statements hold for almost every Bloch momentum `k`, because the fibre reductions are assumed only for almost every `k`.
- **`LandauReductionClaim`:** it records the paper's decay rate `δ_n = O(n^{-1/4} log n)` in the weaker form `δ_n n^{1/8} → 0`, which is all the `𝒢₀` statements need.
