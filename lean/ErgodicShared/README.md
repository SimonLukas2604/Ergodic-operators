# ErgodicShared

General spectral tools for covariant Weyl-series operators, shared by the Paper II
(`SpectralGapsDimension`) and Paper III (`ContinuumMagnetic`) formalizations. The library depends
only on `AnalyticPerturbationsAMO`. Declarations live in namespace `CMS`.

To build it: `lake build ErgodicShared` (it is also a default target). It has no `sorry`.

| Module | Content |
|---|---|
| `UnitaryTransfer` | spectral vocabulary on general Hilbert spaces; spectrum and spectral types (a.c., s.c., eigenbasis) are invariant under unitary equivalence |
| `Affine`, `AffineIsland` | the affine energy change `E₀ + aE` on spectral measures, Cantor sets, DOS measures and gap labels; `op`/`op2` affine identities; `op2` linearity and self-adjointness |
| `SpectralMeasureExists` | existence (Riesz–Markov–Kakutani), uniqueness, support and total mass of spectral measures |
| `MaximalType` | if every vector of an orthonormal basis has spectral measure `ρ`, every spectral measure is `≪ ρ` |
| `TraceIdentity` | `op2` is multiplicative; each `δ_p` has the IDS as its spectral measure for `op2` |
| `IDSAveraging` | existence of the DOS measure; covariance of diagonal matrix elements; averaging; the atom bound `ν{E} = 0` under a uniform eigenspace bound |
| `AtomEigen` | atoms of spectral measures are eigenprojections, `μ_v{E} = ‖P_E v‖²`; trace bound by `dim ker` |
| `JacobiKernel` | `dim ker(H_x − E) ≤ 2` from an exact Jacobi preparation |

The old module paths under `ContinuumMagnetic` are re-export shims.
