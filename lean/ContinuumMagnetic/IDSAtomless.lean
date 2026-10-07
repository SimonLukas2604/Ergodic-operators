/-
# Atomlessness of the critical IDS  (Paper I, Lemma 2.8, atomless part; paper Theorem
`thm:analytic-input` (iv))

**Proof that `CriticalIDSAtomlessClaim` follows from `CriticalClaim`.**  In the critical regime,
Paper I's Theorem 1.6 (`AMO.CriticalClaim`) provides, at every spectral energy `E`, an exact
Jacobi preparation `H_x - E = Q_x^* J_x Q_x`.  Then:

1. the IDS exists: it is the spectral measure of the full lattice operator at `δ₀`
   (`CMS.exists_isDOSMeasure`);
2. `dim ker(H_x - E) ≤ 2` for every phase, since `ker(H_x - E) = Q_x⁻¹ ker J_x` and a solution of
   the second-order recursion is determined by two values (`CMS.JacobiPrep.finrank_ker_le_two`);
3. atoms of spectral measures are eigenprojections, so `∑_{n∈F} μ_{x,δ_n}{E} ≤ dim ker(H_x - E) ≤ 2`
   (`CMS.sum_measureReal_singleton_le_finrank`);
4. covariance and averaging over `N` sites give `ν{E} ≤ 2/N` for every `N`
   (`CMS.dos_measure_singleton_eq_zero_of_two`);
5. off the spectrum the IDS vanishes (`AMO.dos_compl_eq_zero`).

Only the continuous functional calculus is used; irrationality of `α` is not needed.
Consequently Paper III's analytic input reduces to Paper I's three main theorems and the Paper II
input: `PaperInputs.ofMain`.
-/
import ContinuumMagnetic.RegularRep
import ContinuumMagnetic.RegularRep.AtomEigen
import ContinuumMagnetic.RegularRep.JacobiKernel
import ContinuumMagnetic.RegularRep.IDSAveraging

noncomputable section

open MeasureTheory Set AMO

namespace CMS

/-- **Paper I, Lemma 2.8 (atomlessness) in the critical regime, from Theorem 1.6.** -/
theorem criticalIDSAtomless_of_critical (h : CriticalClaim) : CriticalIDSAtomlessClaim := by
  obtain ⟨S, hS, εc, hεc, hcrit⟩ := h
  refine ⟨S, hS, εc, hεc, fun α R hα hsa hF hW => ?_⟩
  have hR : SymbolSummable R := hW.summable hS.le hS.le
  set K : Symbol := amo ((1 : ℝ) : ℂ) + R
  have hK : SymbolSummable K := (amo_summable _).add hR
  have hKsa : SymbolSelfAdjoint K := by
    have h1 := amo_selfAdjoint (1 : ℝ)
    intro p
    show (amo ((1 : ℝ) : ℂ) + R) (-p) = (starRingEnd ℂ) ((amo ((1 : ℝ) : ℂ) + R) p)
    rw [Pi.add_apply, Pi.add_apply, map_add, h1 p, hsa p]
  obtain ⟨ν, hν⟩ := exists_isDOSMeasure α hK hKsa
  obtain ⟨hcantor, -, ⟨ystar, -, hprep⟩, -⟩ := hcrit α R hα hsa hF hW
  refine ⟨ν, hν, fun E => ?_⟩
  by_cases hE : E ∈ Sigma α 1 R
  · obtain ⟨P, -⟩ := hprep E hE
    refine dos_measure_singleton_eq_zero_of_two hK hKsa hν E ?_
    intro x F μ hμ
    have hT : IsSelfAdjoint (op α K x) := isSelfAdjoint_op hK hKsa x
    haveI : FiniteDimensional ℂ (eigenspaceH (op α K x) E) :=
      CMS.JacobiPrep.finiteDimensional_ker P x
    have h0 : Orthonormal ℂ (fun n : ℤ => (delta n : L2 ℤ)) := by
      have := (stdBasis ℤ).orthonormal
      convert this using 1
      funext n
      exact (stdBasis_apply n).symm
    have hon : Orthonormal ℂ (fun n : F => (delta (n : ℤ) : L2 ℤ)) :=
      h0.comp _ Subtype.val_injective
    have hsum := sum_measureReal_singleton_le_finrank hT E hon Finset.univ
      (μ := fun n : F => μ n) (fun n => hμ n n.2)
    have h2 : (Module.finrank ℂ (eigenspaceH (op α K x) E) : ℝ) ≤ 2 := by
      exact_mod_cast CMS.JacobiPrep.finrank_ker_le_two P x
    rw [Finset.sum_coe_sort F (fun n => (μ n).real {E})] at hsum
    linarith
  · have := hν.1
    have hsaH := isSelfAdjoint_H α 1 hR hsa
    have hcl : IsClosed (Sigma α 1 R) := AMO.spectrum_real_isClosed _
    have hνS : ν (Sigma α 1 R)ᶜ = 0 :=
      dos_compl_eq_zero hν hcl hcantor.1 hsaH (fun x => (spectrum_H_eq_Sigma hα hR hsa x).le)
    exact measure_mono_null (by simpa using hE) hνS

/-- The analytic input of Paper III from Paper I's three main theorems and the Paper II input:
both auxiliary Paper I claims (Lemma 3.5 and the atomless part of Lemma 2.8) are theorems. -/
structure PaperInputsMain : Prop where
  dryTenMartini : DryTenMartiniUniformClaim
  spectralTransition : SpectralTransitionUniformClaim
  critical : CriticalClaim
  criticalGeometry : CriticalGeometricInputClaim

/-- `PaperInputs` from Paper I's main theorems and the Paper II input. -/
theorem PaperInputs.ofMain (P : PaperInputsMain) : PaperInputs :=
  PaperInputs.ofCore ⟨P.dryTenMartini, P.spectralTransition, P.critical,
    criticalIDSAtomless_of_critical P.critical, P.criticalGeometry⟩

end CMS
