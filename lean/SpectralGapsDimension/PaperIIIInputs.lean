/-
Copyright (c) 2026. Formalization of
  S. Becker, "Self-dual perturbations of the critical almost Mathieu operator:
  Dry Ten Martini and Hausdorff dimension" (Paper II).

# Discharging inputs with results proved in Paper III's library

Two results of Paper III's development (now in the shared library `ErgodicShared`) prove inputs of `PaperIIInputsRefined`:

* `CMS.exists_isDOSMeasure` (existence of the DOS measure, via the spectral measure of the
  two-dimensional realization) proves `DOSExistsClaim` (`dosExists_holds`);
* `CMS.JacobiPrep.finiteDimensional_ker` and `CMS.JacobiPrep.finrank_ker_le_two` (an exact Jacobi
  preparation `H_x - E = Q_x^* J_x Q_x` with nonvanishing hopping forces `dim ker (H_x - E) ≤ 2`)
  reduce `EigenspaceBoundClaim` to the existence of preparations at spectral energies,
  `JacobiPrepClaim` (`eigenspaceBound_of_jacobiPrep`).  Off the spectrum the kernel is trivial.

`PaperIIInputsFinal` is the resulting input bundle; Theorems 1.1 and 1.2 hold under it
(`thm_joint_final`, `thm_liouville_final`).

The Paper III results live in the shared library `ErgodicShared` (namespace `CMS`), which depends only
on `AnalyticPerturbationsAMO`.
-/
import SpectralGapsDimension.Reductions
import SpectralGapsDimension.GapLabelling
import ErgodicShared.IDSAveraging
import ErgodicShared.JacobiKernel

noncomputable section

open MeasureTheory

namespace SGD

open AMO

/-- **Existence of the DOS measure** for `H_α(R)`, from Paper III's `CMS.exists_isDOSMeasure`. -/
theorem dosExists_holds : DOSExistsClaim := by
  intro α R hRs hsa
  have hsa' : SymbolSelfAdjoint (amo ((1 : ℝ) : ℂ) + R) := by
    intro p
    have h1 := amo_selfAdjoint (1 : ℝ) p
    simp only [Pi.add_apply, map_add, h1, hsa p]
  exact CMS.exists_isDOSMeasure α ((amo_summable _).add hRs) hsa'

/-- **Theorem 2.4 (`dim:thm:center`), preparation form.**  For irrational `α` and `S > 0`, small
admissible perturbations admit, at every spectral energy `E`, an exact analytic, exponentially local
Jacobi preparation `H_{α,x} - E = Q_x^* J_x Q_x` with nonvanishing hopping, in the sense of Paper I
(`AMO.JacobiPrep`; this structure also records the analytic square root `c = (a a^♯)^{1/2}` used in
Paper I). -/
def JacobiPrepClaim : Prop :=
  ∀ {α : ℝ} (hα : Irrational α) {S : ℝ} (hS : 0 < S),
    ∃ ε > 0, ∀ R : Symbol, SelfDual R → WSmall S S R ε →
      ∀ E ∈ Sigma α 1 R, Nonempty (JacobiPrep α (H α 1 R) E)

/-- Off the spectrum, `H - E` is injective. -/
lemma ker_sub_eq_bot_of_notMem {T : Op ℤ} {E : ℝ} (hE : E ∉ spectrum ℝ T) :
    LinearMap.ker ((T - (E : ℂ) • 1 : Op ℤ) : L2 ℤ →ₗ[ℂ] L2 ℤ) = ⊥ := by
  rw [spectrum.notMem_iff] at hE
  have hu : IsUnit (T - (E : ℂ) • 1) := by
    have h2 : algebraMap ℝ (Op ℤ) E - T = -(T - (E : ℂ) • 1) := by
      rw [Algebra.algebraMap_eq_smul_one, neg_sub]
      congr 1
    rw [h2] at hE
    simpa using hE.neg
  obtain ⟨u, hu⟩ := hu
  refine LinearMap.ker_eq_bot.2 fun v w hvw => ?_
  have h := congrArg (fun y => (↑u⁻¹ : Op ℤ) y) hvw
  simp only [ContinuousLinearMap.coe_coe] at h
  rw [← hu] at h
  simpa [← ContinuousLinearMap.mul_apply] using h

/-- **Eigenspace bound from preparations**: `EigenspaceBoundClaim` follows from `JacobiPrepClaim`
(Paper III, `CMS.JacobiPrep.finrank_ker_le_two`; off the spectrum the kernel is trivial). -/
theorem eigenspaceBound_of_jacobiPrep (h : JacobiPrepClaim) : EigenspaceBoundClaim := by
  intro α hα S hS
  obtain ⟨ε, hε, hR⟩ := h hα hS
  refine ⟨ε, hε, fun R hRsd hRS x E => ?_⟩
  have hRs : SymbolSummable R := WSmall.summable hS.le hS.le hRS
  have hform : ((H α 1 R x - (E : ℂ) • 1 : Op ℤ) : L2 ℤ →ₗ[ℂ] L2 ℤ) =
      ((H α 1 R x - algebraMap ℂ (Op ℤ) E : Op ℤ) : L2 ℤ →ₗ[ℂ] L2 ℤ) := by
    rw [Algebra.algebraMap_eq_smul_one]
  by_cases hE : E ∈ Sigma α 1 R
  · obtain ⟨P⟩ := hR R hRsd hRS E hE
    rw [hform]
    exact ⟨CMS.JacobiPrep.finiteDimensional_ker P x, CMS.JacobiPrep.finrank_ker_le_two P x⟩
  · have hE' : E ∉ spectrum ℝ (H α 1 R x) := by
      rwa [spectrum_H_eq_Sigma hα hRs hRsd.1 x]
    have hker := ker_sub_eq_bot_of_notMem hE'
    rw [hker]
    exact ⟨inferInstance, by simp⟩

/-- The input bundle after discharging `DOSExistsClaim`, reducing `EigenspaceBoundClaim` to
`JacobiPrepClaim` (Theorem 2.4) with Paper III's results, and reducing
`ComparisonLabelStabilityClaim` to the classical gap-labelling theorem (`GapLabelling.lean`). -/
structure PaperIIInputsFinal : Prop where
  comparison : ComparisonClaim
  normalization : NormalizationClaim
  inertiaTransfer : InertiaTransferClaim
  gapLabelling : GapLabellingClaim
  infiniteExponent : InfiniteExponentClaim
  brjunoCover : BrjunoCoverClaim
  packetCover : PacketCoverClaim
  jacobiPrep : JacobiPrepClaim

theorem PaperIIInputsFinal.toRefined (P : PaperIIInputsFinal) : PaperIIInputsRefined where
  comparison := P.comparison
  normalization := P.normalization
  inertiaTransfer := P.inertiaTransfer
  comparisonLabelStability := comparisonLabelStability_of_gapLabelling P.gapLabelling
  infiniteExponent := P.infiniteExponent
  brjunoCover := P.brjunoCover
  packetCover := P.packetCover
  eigenspaceBound := eigenspaceBound_of_jacobiPrep P.jacobiPrep
  dosExists := dosExists_holds

/-- **Theorem 1.1** under `PaperIIInputsFinal`. -/
theorem thm_joint_final (P : PaperIIInputsFinal) {α : ℝ} (hα : Irrational α) :
    ∃ Sstar > 0, ∀ S ≥ Sstar, ∃ ρ > 0, ∀ R : Symbol, SelfDual R → WSmall S S R ρ →
      AllLabelsOpen α R ∧ μH[1 / 2] (Sigma α 1 R) < ⊤ ∧ dimH (Sigma α 1 R) ≤ 1 / 2 ∧
        IsCantor (Sigma α 1 R) ∧ volume (Sigma α 1 R) = 0 :=
  thm_joint_refined P.toRefined hα

/-- **Theorem 1.2** under `PaperIIInputsFinal`. -/
theorem thm_liouville_final (P : PaperIIInputsFinal) {α : ℝ} (hα : Irrational α)
    (hL : Liouville α) {S : ℝ} (hS : 0 < S) :
    ∃ ρ > 0, ∀ R : Symbol, SelfDual R → WSmall S S R ρ →
      dimH (Sigma α 1 R) = 0 ∧ IsCantor (Sigma α 1 R) ∧ volume (Sigma α 1 R) = 0 :=
  thm_liouville_refined P.toRefined hα hL hS

end SGD
