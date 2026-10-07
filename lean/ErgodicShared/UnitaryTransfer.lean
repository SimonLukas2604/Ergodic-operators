/-
# Unitary transfer of spectral types  (paper §2, (2.5), (2.8); §4 "regular representation and
continuum reduction")

Paper III obtains every spectral statement about the continuum island operator `P H_h P` on
`Ran P` from an *exact unitary reduction* `𝒰 : ℓ²(ℤ²) → Ran P` (paper (2.8),
eq:intro-reduction) to Paper I's lattice operators (`AMO.op2`, `AMO.op`, `AMO.H`).
This file provides the abstract machinery:

* the spectral vocabulary of Paper I (`AnalyticPerturbationsAMO/Spectral.lean`) generalised to
  an arbitrary complex Hilbert space `H`: `IsSpectralMeasureH`, `PurelyACH`, `PurelySCOnH`,
  `PurelySCH`, `NoACComponentH`, `NoEigenvaluesInH`, and `HasCompleteEigenbasisOn` (the
  Hilbert-space-free part of Anderson localization); on `H = ℓ²(ι)` these agree with Paper I's
  definitions;
* unitary invariance: if `u : H ≃ₗᵢ[ℂ] H'` intertwines `T` and `T'` (`T' ∘ u = u ∘ T`) then
  spectra, self-adjointness, the continuous functional calculus, spectral measures and all
  spectral types transfer;
* corollaries transferring Paper I's conclusions for `AMO.op2`, `AMO.op`, `AMO.H` to any
  operator unitarily equivalent to them, including `spec T' = Σ` for irrational `α`.
-/
import AnalyticPerturbationsAMO

noncomputable section

open scoped ComplexConjugate InnerProductSpace
open MeasureTheory Set BoundedContinuousFunction AMO

namespace CMS

set_option linter.unusedSectionVars false

variable {H H' : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [CompleteSpace H']

/-! ### Spectral vocabulary on a general Hilbert space -/

/-- `μ` is the spectral measure of `T` at `ψ`: `∫ f dμ = ⟪ψ, f(T) ψ⟫` for bounded continuous
real `f` (via the continuous functional calculus, as in Paper I). -/
def IsSpectralMeasureH (T : H →L[ℂ] H) (ψ : H) (μ : Measure ℝ) : Prop :=
  IsFiniteMeasure μ ∧
    ∀ f : ℝ →ᵇ ℝ, ∫ t, f t ∂μ = RCLike.re ⟪ψ, cfc (fun z : ℂ => ((f z.re : ℝ) : ℂ)) T ψ⟫_ℂ

/-- Purely absolutely continuous spectrum. -/
def PurelyACH (T : H →L[ℂ] H) : Prop :=
  ∀ ψ, ∃ μ, IsSpectralMeasureH T ψ μ ∧ μ ≪ volume

/-- The spectral restriction of `T` to `S` is purely singular continuous. -/
def PurelySCOnH (T : H →L[ℂ] H) (S : Set ℝ) : Prop :=
  ∀ ψ, ∃ μ, IsSpectralMeasureH T ψ μ ∧ μ.restrict S ⟂ₘ volume ∧ ∀ E ∈ S, μ {E} = 0

/-- Purely singular continuous spectrum. -/
def PurelySCH (T : H →L[ℂ] H) : Prop := PurelySCOnH T univ

/-- No absolutely continuous component. -/
def NoACComponentH (T : H →L[ℂ] H) : Prop :=
  ∀ ψ, ∃ μ, IsSpectralMeasureH T ψ μ ∧ μ ⟂ₘ volume

/-- No eigenvalues in `S`. -/
def NoEigenvaluesInH (T : H →L[ℂ] H) (S : Set ℝ) : Prop :=
  ∀ E ∈ S, ∀ v : H, T v = algebraMap ℂ (H →L[ℂ] H) E v → v = 0

/-- Complete eigenbasis on `S` (pure point spectrum on `S`): an orthonormal family of
eigenvectors with eigenvalues in `S` whose closed span contains every vector whose spectral
measure is carried by `S`. -/
def HasCompleteEigenbasisOn (T : H →L[ℂ] H) (S : Set ℝ) : Prop :=
  ∃ (J : Type) (v : J → H) (E : J → ℝ),
    Orthonormal ℂ v ∧
    (∀ j, E j ∈ S ∧ T (v j) = algebraMap ℂ (H →L[ℂ] H) (E j) (v j)) ∧
    (∀ ψ, (∃ μ, IsSpectralMeasureH T ψ μ ∧ μ Sᶜ = 0) →
      ψ ∈ (Submodule.span ℂ (range v)).topologicalClosure)

/-! ### Agreement with Paper I on `ℓ²(ι)` -/

section PaperI

variable {ι : Type*}

theorem isSpectralMeasureH_iff (T : Op ι) (ψ : L2 ι) (μ : Measure ℝ) :
    IsSpectralMeasureH T ψ μ ↔ IsSpectralMeasure T ψ μ := Iff.rfl

theorem purelyACH_iff (T : Op ι) : PurelyACH T ↔ PurelyAC T := Iff.rfl

theorem purelySCOnH_iff (T : Op ι) (S : Set ℝ) : PurelySCOnH T S ↔ PurelySCOn T S := Iff.rfl

theorem purelySCH_iff (T : Op ι) : PurelySCH T ↔ PurelySC T := Iff.rfl

theorem noACComponentH_iff (T : Op ι) : NoACComponentH T ↔ NoACComponent T := Iff.rfl

theorem noEigenvaluesInH_iff (T : Op ι) (S : Set ℝ) :
    NoEigenvaluesInH T S ↔ NoEigenvaluesIn T S := Iff.rfl

/-- Anderson localization (Paper I) gives a complete eigenbasis (forgetting decay). -/
theorem AndersonLocalizedOn.hasCompleteEigenbasisOn {T : Op ℤ} {S : Set ℝ}
    (h : AndersonLocalizedOn T S) : HasCompleteEigenbasisOn T S := by
  obtain ⟨J, v, E, hv, hE, -, hspan⟩ := h
  exact ⟨J, v, E, hv, hE, hspan⟩

end PaperI

/-! ### Unitary intertwining -/

lemma algebraMap_op_apply (E : ℂ) (v : H) : algebraMap ℂ (H →L[ℂ] H) E v = E • v := by
  simp [Algebra.algebraMap_eq_smul_one]

/-- `u` intertwines `T` and `T'`: `T' ∘ u = u ∘ T`, i.e. `T' = u T u⁻¹`. -/
def Intertwines (u : H ≃ₗᵢ[ℂ] H') (T : H →L[ℂ] H) (T' : H' →L[ℂ] H') : Prop :=
  ∀ x, T' (u x) = u (T x)

namespace Intertwines

variable {u : H ≃ₗᵢ[ℂ] H'} {T : H →L[ℂ] H} {T' : H' →L[ℂ] H'}

/-- The operator form `T' ∘L u = u ∘L T`. -/
theorem of_comp
    (h : T' ∘L (u.toContinuousLinearEquiv : H →L[ℂ] H') =
      (u.toContinuousLinearEquiv : H →L[ℂ] H') ∘L T) : Intertwines u T T' :=
  fun x => congrArg (fun A : H →L[ℂ] H' => A x) h

theorem comp_eq (h : Intertwines u T T') :
    T' ∘L (u.toContinuousLinearEquiv : H →L[ℂ] H') =
      (u.toContinuousLinearEquiv : H →L[ℂ] H') ∘L T := by
  ext x; exact h x

/-- The conjugate `u T u⁻¹` is intertwined with `T`. -/
theorem of_conj (u : H ≃ₗᵢ[ℂ] H') (T : H →L[ℂ] H) : Intertwines u T (u.conjStarAlgEquiv T) := by
  intro x; simp

theorem eq_conj (h : Intertwines u T T') : T' = u.conjStarAlgEquiv T := by
  ext y
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, ← h, LinearIsometryEquiv.apply_symm_apply]

theorem symm (h : Intertwines u T T') : Intertwines u.symm T' T := by
  intro y
  apply u.injective
  rw [← h]; simp

theorem trans {H'' : Type*} [NormedAddCommGroup H''] [InnerProductSpace ℂ H'']
    [CompleteSpace H''] {w : H' ≃ₗᵢ[ℂ] H''} {T'' : H'' →L[ℂ] H''}
    (h : Intertwines u T T') (h' : Intertwines w T' T'') : Intertwines (u.trans w) T T'' := by
  intro x; simp [h' (u x), h x]

end Intertwines

/-! ### Invariance of spectrum, self-adjointness and functional calculus -/

section Invariance

variable {u : H ≃ₗᵢ[ℂ] H'} {T : H →L[ℂ] H} {T' : H' →L[ℂ] H'}

lemma continuous_conjStarAlgEquiv (u : H ≃ₗᵢ[ℂ] H') : Continuous u.conjStarAlgEquiv :=
  u.toContinuousLinearEquiv.conjContinuousAlgEquiv.continuous

/-- The continuous functional calculus commutes with unitary conjugation (any `f`). -/
theorem conjStarAlgEquiv_cfc (u : H ≃ₗᵢ[ℂ] H') (f : ℂ → ℂ) (T : H →L[ℂ] H) :
    u.conjStarAlgEquiv (cfc f T) = cfc f (u.conjStarAlgEquiv T) := by
  have hspec : spectrum ℂ (u.conjStarAlgEquiv T) = spectrum ℂ T :=
    AlgEquiv.spectrum_eq u.conjStarAlgEquiv T
  by_cases hT : IsStarNormal T
  · have hT' : IsStarNormal (u.conjStarAlgEquiv T) := hT.map u.conjStarAlgEquiv
    by_cases hf : ContinuousOn f (spectrum ℂ T)
    · exact StarAlgHomClass.map_cfc (S := ℂ) u.conjStarAlgEquiv f T hf
        (continuous_conjStarAlgEquiv u) hT hT'
    · rw [cfc_apply_of_not_continuousOn T hf,
        cfc_apply_of_not_continuousOn _ (by rwa [hspec]), map_zero]
  · have hT' : ¬ IsStarNormal (u.conjStarAlgEquiv T) := by
      intro h
      apply hT
      have := h.map u.conjStarAlgEquiv.symm
      rwa [StarAlgEquiv.symm_apply_apply] at this
    rw [cfc_apply_of_not_predicate T hT, cfc_apply_of_not_predicate _ hT', map_zero]

namespace Intertwines

/-- `cfc f T' = u ∘ cfc f T ∘ u⁻¹`. -/
theorem cfc_eq (h : Intertwines u T T') (f : ℂ → ℂ) :
    cfc f T' = u.conjStarAlgEquiv (cfc f T) := by
  rw [h.eq_conj, conjStarAlgEquiv_cfc]

/-- Functional calculus intertwines as well. -/
theorem cfc (h : Intertwines u T T') (f : ℂ → ℂ) : Intertwines u (cfc f T) (cfc f T') := by
  rw [h.cfc_eq f]; exact of_conj u _

theorem spectrum_eq (h : Intertwines u T T') : spectrum ℂ T' = spectrum ℂ T := by
  rw [h.eq_conj]; exact AlgEquiv.spectrum_eq u.conjStarAlgEquiv T

theorem spectrum_real_eq (h : Intertwines u T T') : spectrum ℝ T' = spectrum ℝ T := by
  rw [← spectrum.preimage_algebraMap ℂ (R := ℝ) (a := T'),
    ← spectrum.preimage_algebraMap ℂ (R := ℝ) (a := T), h.spectrum_eq]

theorem isSelfAdjoint_iff (h : Intertwines u T T') : IsSelfAdjoint T' ↔ IsSelfAdjoint T := by
  constructor
  · intro hs
    have := hs.map u.conjStarAlgEquiv.symm
    rwa [h.eq_conj, StarAlgEquiv.symm_apply_apply] at this
  · intro hs
    rw [h.eq_conj]; exact hs.map u.conjStarAlgEquiv

/-- Spectral measures are transported: `μ_ψ^T = μ_{uψ}^{T'}`. -/
theorem isSpectralMeasureH_iff (h : Intertwines u T T') (ψ : H) (μ : Measure ℝ) :
    IsSpectralMeasureH T' (u ψ) μ ↔ IsSpectralMeasureH T ψ μ := by
  have key : ∀ g : ℂ → ℂ, ⟪u ψ, _root_.cfc g T' (u ψ)⟫_ℂ = ⟪ψ, _root_.cfc g T ψ⟫_ℂ := by
    intro g
    rw [h.cfc_eq g, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.inner_map_map]
  unfold IsSpectralMeasureH
  simp_rw [key]

theorem isSpectralMeasureH_iff' (h : Intertwines u T T') (ψ' : H') (μ : Measure ℝ) :
    IsSpectralMeasureH T' ψ' μ ↔ IsSpectralMeasureH T (u.symm ψ') μ := by
  rw [← h.isSpectralMeasureH_iff, LinearIsometryEquiv.apply_symm_apply]

/-! ### Invariance of spectral types -/

theorem purelyACH_iff (h : Intertwines u T T') : PurelyACH T' ↔ PurelyACH T := by
  constructor
  · intro hT ψ
    simpa [h.isSpectralMeasureH_iff] using hT (u ψ)
  · intro hT ψ'
    simpa [h.isSpectralMeasureH_iff'] using hT (u.symm ψ')

theorem purelySCOnH_iff (h : Intertwines u T T') (S : Set ℝ) :
    PurelySCOnH T' S ↔ PurelySCOnH T S := by
  constructor
  · intro hT ψ
    simpa [h.isSpectralMeasureH_iff] using hT (u ψ)
  · intro hT ψ'
    simpa [h.isSpectralMeasureH_iff'] using hT (u.symm ψ')

theorem purelySCH_iff (h : Intertwines u T T') : PurelySCH T' ↔ PurelySCH T :=
  h.purelySCOnH_iff univ

theorem noACComponentH_iff (h : Intertwines u T T') : NoACComponentH T' ↔ NoACComponentH T := by
  constructor
  · intro hT ψ
    simpa [h.isSpectralMeasureH_iff] using hT (u ψ)
  · intro hT ψ'
    simpa [h.isSpectralMeasureH_iff'] using hT (u.symm ψ')

theorem noEigenvaluesInH_of (h : Intertwines u T T') {S : Set ℝ} (hT : NoEigenvaluesInH T S) :
    NoEigenvaluesInH T' S := by
  intro E hE v hv
  have h1 : T (u.symm v) = algebraMap ℂ (H →L[ℂ] H) E (u.symm v) := by
    rw [algebraMap_op_apply] at hv ⊢
    rw [h.symm v, hv, map_smul]
  have := hT E hE _ h1
  simpa using congrArg u this

theorem noEigenvaluesInH_iff (h : Intertwines u T T') (S : Set ℝ) :
    NoEigenvaluesInH T' S ↔ NoEigenvaluesInH T S :=
  ⟨h.symm.noEigenvaluesInH_of, h.noEigenvaluesInH_of⟩

theorem hasCompleteEigenbasisOn_of (h : Intertwines u T T') {S : Set ℝ}
    (hT : HasCompleteEigenbasisOn T S) : HasCompleteEigenbasisOn T' S := by
  obtain ⟨J, v, E, hv, hE, hspan⟩ := hT
  refine ⟨J, fun j => u (v j), E, hv.comp_linearIsometryEquiv u, fun j => ⟨(hE j).1, ?_⟩, ?_⟩
  · rw [algebraMap_op_apply, h, (hE j).2, algebraMap_op_apply, map_smul]
  · intro ψ' hψ'
    have hψ : ψ' = u (u.symm ψ') := (u.apply_symm_apply ψ').symm
    have hmem := hspan (u.symm ψ') (by simpa [h.isSpectralMeasureH_iff'] using hψ')
    rw [hψ]
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at hmem ⊢
    refine map_mem_closure u.continuous hmem ?_
    intro x hx
    have : u x ∈ (Submodule.span ℂ (range v)).map (u.toLinearEquiv.toLinearMap) :=
      Submodule.mem_map_of_mem hx
    rw [Submodule.map_span, ← range_comp] at this
    exact this

theorem hasCompleteEigenbasisOn_iff (h : Intertwines u T T') (S : Set ℝ) :
    HasCompleteEigenbasisOn T' S ↔ HasCompleteEigenbasisOn T S :=
  ⟨h.symm.hasCompleteEigenbasisOn_of, h.hasCompleteEigenbasisOn_of⟩

end Intertwines

end Invariance

/-! ### Transfer of Paper I's conclusions -/

section Transfer

variable {ι : Type*} {A : Op ι} {T' : H' →L[ℂ] H'} {u : L2 ι ≃ₗᵢ[ℂ] H'}

theorem purelyACH_of_purelyAC (hA : PurelyAC A) (h : Intertwines u A T') : PurelyACH T' :=
  h.purelyACH_iff.2 hA

theorem purelySCOnH_of_purelySCOn {S : Set ℝ} (hA : PurelySCOn A S) (h : Intertwines u A T') :
    PurelySCOnH T' S := (h.purelySCOnH_iff S).2 hA

theorem purelySCH_of_purelySC (hA : PurelySC A) (h : Intertwines u A T') : PurelySCH T' :=
  h.purelySCH_iff.2 hA

theorem noACComponentH_of_noACComponent (hA : NoACComponent A) (h : Intertwines u A T') :
    NoACComponentH T' := h.noACComponentH_iff.2 hA

theorem noEigenvaluesInH_of_noEigenvaluesIn {S : Set ℝ} (hA : NoEigenvaluesIn A S)
    (h : Intertwines u A T') : NoEigenvaluesInH T' S := h.noEigenvaluesInH_of hA

/-- Anderson localization of a 1D lattice operator gives a complete eigenbasis of any unitarily
equivalent operator. -/
theorem hasCompleteEigenbasisOn_of_andersonLocalizedOn {A : Op ℤ} {u : L2 ℤ ≃ₗᵢ[ℂ] H'}
    {S : Set ℝ} (hA : AndersonLocalizedOn A S) (h : Intertwines u A T') :
    HasCompleteEigenbasisOn T' S :=
  h.hasCompleteEigenbasisOn_of (AndersonLocalizedOn.hasCompleteEigenbasisOn hA)

/-- Purely a.c. spectrum of the 2D magnetic realization `H̃ = op2 α R` transfers to the
continuum island operator under an exact unitary reduction (paper (2.8)). -/
theorem purelyACH_of_op2 {α : ℝ} {R : Symbol} {u : L2 (ℤ × ℤ) ≃ₗᵢ[ℂ] H'}
    (hA : PurelyAC (op2 α R)) (h : Intertwines u (op2 α R) T') : PurelyACH T' :=
  purelyACH_of_purelyAC hA h

/-- Purely s.c. spectrum on `S` of `H̃ = op2 α R` transfers. -/
theorem purelySCOnH_of_op2 {α : ℝ} {R : Symbol} {u : L2 (ℤ × ℤ) ≃ₗᵢ[ℂ] H'} {S : Set ℝ}
    (hA : PurelySCOn (op2 α R) S) (h : Intertwines u (op2 α R) T') : PurelySCOnH T' S :=
  purelySCOnH_of_purelySCOn hA h

/-- No a.c. component of `H̃ = op2 α R` transfers. -/
theorem noACComponentH_of_op2 {α : ℝ} {R : Symbol} {u : L2 (ℤ × ℤ) ≃ₗᵢ[ℂ] H'}
    (hA : NoACComponent (op2 α R)) (h : Intertwines u (op2 α R) T') : NoACComponentH T' :=
  noACComponentH_of_noACComponent hA h

/-- Anderson localization of the 1D operator `op α R x` transfers as a complete eigenbasis. -/
theorem hasCompleteEigenbasisOn_of_op {α x : ℝ} {R : Symbol} {u : L2 ℤ ≃ₗᵢ[ℂ] H'}
    {S : Set ℝ} (hA : AndersonLocalizedOn (op α R x) S) (h : Intertwines u (op α R x) T') :
    HasCompleteEigenbasisOn T' S :=
  hasCompleteEigenbasisOn_of_andersonLocalizedOn hA h

/-- **Spectrum transfer.**  An operator unitarily equivalent to `H_x = AMO.H α η R x`
(irrational `α`, summable self-adjoint `R`) has spectrum exactly `Σ = AMO.Sigma α η R`. -/
theorem spectrum_eq_Sigma_of_intertwines {α η x : ℝ} {R : Symbol} {u : L2 ℤ ≃ₗᵢ[ℂ] H'}
    (hα : Irrational α) (hR : SymbolSummable R) (hsa : SymbolSelfAdjoint R)
    (h : Intertwines u (AMO.H α η R x) T') : spectrum ℝ T' = Sigma α η R := by
  exact h.spectrum_real_eq.trans (spectrum_H_eq_Sigma hα hR hsa x)

end Transfer

end CMS
