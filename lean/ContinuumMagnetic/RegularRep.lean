/-
# Paper I, Lemma 3.5: the maximal spectral type of the full lattice realization

**Proof of `RegularRepDominationClaim`**: for a summable self-adjoint Weyl series `K`, every
spectral measure of the full lattice realization `K̃ = op2 α K` on `ℓ²(ℤ²)` is absolutely
continuous with respect to the IDS measure `ν_K` (paper (4.4)–(4.5)).

The classical proof uses the direct-integral decomposition `𝓑 K̃ 𝓑* = ∫^⊕ K_x dx` and the Borel
functional calculus.  We use only the continuous functional calculus:

1. every standard basis vector `δ_p` of `ℓ²(ℤ²)` has spectral measure exactly `ν_K`
   (`CMS.isSpectralMeasure_op2_delta`: diagonal matrix elements of `op2` and the phase-averaged
   matrix elements of the fibres are both the constant Weyl coefficient; polynomials, then
   continuous functions by Weierstrass);
2. if all vectors of an orthonormal basis have the same spectral measure `ρ`, every spectral
   measure is `≪ ρ` (`CMS.IsSpectralMeasure.absolutelyContinuous_of_delta`);
3. spectral measures exist (`CMS.exists_isSpectralMeasureH`, Riesz–Markov–Kakutani).

Irrationality of `α` is not needed.  Consequently `PaperInputs` can be built without this claim:
`PaperInputs.ofCore`.
-/
import ContinuumMagnetic.RegularRep.SpectralMeasureExists
import ContinuumMagnetic.RegularRep.MaximalType
import ContinuumMagnetic.RegularRep.TraceIdentity
import ContinuumMagnetic.AnalyticInput

noncomputable section

open MeasureTheory AMO

namespace CMS

/-- **Paper I, Lemma 3.5 (proved).** -/
theorem regularRepDomination : RegularRepDominationClaim := by
  intro α _ K hK hsa ν hν ψ
  have := hν.1
  obtain ⟨μ, hμ, -⟩ := exists_isSpectralMeasureH (isSelfAdjoint_op2 hK hsa) ψ
  exact ⟨μ, hμ, IsSpectralMeasure.absolutelyContinuous_of_delta
    (fun p => isSpectralMeasure_op2_delta hK hsa hν p) hμ⟩

/-- The analytic input of Paper III without the (now proved) regular-representation lemma. -/
structure PaperInputsCore : Prop where
  dryTenMartini : DryTenMartiniUniformClaim
  spectralTransition : SpectralTransitionUniformClaim
  critical : CriticalClaim
  criticalIDS : CriticalIDSAtomlessClaim
  criticalGeometry : CriticalGeometricInputClaim

/-- `PaperInputs` from the remaining claims: `RegularRepDominationClaim` is a theorem. -/
theorem PaperInputs.ofCore (P : PaperInputsCore) : PaperInputs :=
  ⟨P.dryTenMartini, P.spectralTransition, P.critical, regularRepDomination, P.criticalIDS,
    P.criticalGeometry⟩

end CMS
