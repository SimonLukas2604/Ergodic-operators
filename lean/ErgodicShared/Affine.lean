/-
# Affine energy changes  (paper §4.1, §4.4: the maps `Φ_h(E) = E_h^0 + t_max E`, `E_h^0 + a_h E`)

The continuum island operator is unitarily equivalent to `E₀ I + a K`, where `K` is the
normalized lattice interaction of Paper I and `a = t_max > 0` (off-critical) or `a = a_h ≠ 0`
(critical, either sign).  This file proves that the affine map `Φ(t) = E₀ + a t` transports:

* the continuous functional calculus and spectral measures (`μ ↦ Φ_* μ`);
* pure absolute continuity, pure singular continuity on a set, absence of a.c. component,
  absence of eigenvalues, Anderson localization;
* real spectra, Cantor sets, density-of-states measures;
* open gaps with their labels: label `{nα}` is kept for `a > 0` and becomes
  `1 - {nα} = {-nα}` for `a < 0` (using atomlessness of the IDS, as in the paper).

It also records the linearity of the two-dimensional realization `op2` and the identities
`op (E₀ δ₀ + a K) = E₀ + a op K`, `op2 (E₀ δ₀ + a K) = E₀ + a op2 K`.
-/
import AnalyticPerturbationsAMO

noncomputable section

open scoped ComplexConjugate ENNReal
open MeasureTheory Set Filter BoundedContinuousFunction AMO

namespace CMS

/-! ### The affine map -/

/-- `Φ(t) = E₀ + a t`. -/
def affine (E₀ a : ℝ) (t : ℝ) : ℝ := E₀ + a * t

lemma affine_inv {E₀ a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    affine (-E₀ / a) a⁻¹ (affine E₀ a t) = t := by
  unfold affine; field_simp; ring

lemma affine_inv' {E₀ a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    affine E₀ a (affine (-E₀ / a) a⁻¹ t) = t := by
  unfold affine; field_simp; ring

lemma continuous_affine (E₀ a : ℝ) : Continuous (affine E₀ a) :=
  continuous_const.add (continuous_const.mul continuous_id)

lemma measurable_affine (E₀ a : ℝ) : Measurable (affine E₀ a) := (continuous_affine E₀ a).measurable

/-- The affine homeomorphism of `ℝ`. -/
def affineHomeomorph (E₀ a : ℝ) (ha : a ≠ 0) : ℝ ≃ₜ ℝ where
  toFun := affine E₀ a
  invFun := affine (-E₀ / a) a⁻¹
  left_inv := affine_inv ha
  right_inv := affine_inv' ha
  continuous_toFun := continuous_affine E₀ a
  continuous_invFun := continuous_affine _ _

lemma affine_injective {E₀ a : ℝ} (ha : a ≠ 0) : Function.Injective (affine E₀ a) :=
  (affineHomeomorph E₀ a ha).injective

lemma volume_map_affine {E₀ a : ℝ} (ha : a ≠ 0) :
    (volume : Measure ℝ).map (affine E₀ a) = ENNReal.ofReal |a⁻¹| • volume := by
  have h : affine E₀ a = (fun t => E₀ + t) ∘ (fun t => a * t) := rfl
  rw [h, ← Measure.map_map (measurable_const_add E₀) (measurable_const_mul a),
    Real.map_volume_mul_left ha, Measure.map_smul, map_add_left_eq_self]
  exact (measurable_const_add E₀).aemeasurable

lemma volume_preimage_affine {E₀ a : ℝ} (ha : a ≠ 0) {N : Set ℝ} (hN : volume N = 0) :
    volume (affine E₀ a ⁻¹' N) = 0 := by
  have h := volume_map_affine (E₀ := E₀) ha
  obtain ⟨M, hNM, hM, hM0⟩ := exists_measurable_superset_of_null hN
  refine measure_mono_null (preimage_mono hNM) ?_
  rw [← Measure.map_apply (measurable_affine E₀ a) hM, h]
  simp [hM0]

lemma volume_image_affine {E₀ a : ℝ} (ha : a ≠ 0) {N : Set ℝ} (hN : volume N = 0) :
    volume (affine E₀ a '' N) = 0 := by
  have : affine E₀ a '' N = affine (-E₀ / a) a⁻¹ ⁻¹' N :=
    (affineHomeomorph E₀ a ha).image_eq_preimage_symm N
  rw [this]
  exact volume_preimage_affine (inv_ne_zero ha) hN

lemma AbsolutelyContinuous.map_affine {μ : Measure ℝ} (h : μ ≪ volume) {E₀ a : ℝ} (ha : a ≠ 0) :
    μ.map (affine E₀ a) ≪ volume := by
  intro N hN
  obtain ⟨M, hNM, hM, hM0⟩ := exists_measurable_superset_of_null hN
  refine measure_mono_null hNM ?_
  rw [Measure.map_apply (measurable_affine E₀ a) hM]
  exact h (volume_preimage_affine ha hM0)

lemma MutuallySingular.map_affine {μ : Measure ℝ} (h : μ ⟂ₘ volume) {E₀ a : ℝ} (ha : a ≠ 0) :
    μ.map (affine E₀ a) ⟂ₘ volume := by
  obtain ⟨s, hs, hμs, hvs⟩ := h
  set Φ := affineHomeomorph E₀ a ha
  refine ⟨affine (-E₀ / a) a⁻¹ ⁻¹' s, measurable_affine _ _ hs, ?_, ?_⟩
  · rw [Measure.map_apply (measurable_affine E₀ a) (measurable_affine _ _ hs), ← preimage_comp]
    have : affine (-E₀ / a) a⁻¹ ∘ affine E₀ a = id := funext (affine_inv ha)
    rw [this, preimage_id]; exact hμs
  · rw [← preimage_compl]
    exact volume_preimage_affine (inv_ne_zero ha) hvs

/-! ### The functional calculus under affine changes -/

section CFC

variable {𝒜 : Type*} [CStarAlgebra 𝒜]

/-- `f(Re Φ(z))` applied to `A` equals `f(Re z)` applied to `Φ(A) = E₀ + a A`. -/
lemma cfc_affine_re (E₀ a : ℝ) (A : 𝒜) [IsStarNormal A] (f : ℝ → ℝ) (hf : Continuous f) :
    cfc (fun z : ℂ => ((f (affine E₀ a z.re) : ℝ) : ℂ)) A =
      cfc (fun z : ℂ => ((f z.re : ℝ) : ℂ)) (algebraMap ℂ 𝒜 E₀ + (a : ℂ) • A) := by
  set F : ℂ → ℂ := fun z => ((f z.re : ℝ) : ℂ)
  have hF : Continuous F := Complex.continuous_ofReal.comp (hf.comp Complex.continuous_re)
  set g : ℂ → ℂ := fun z => (E₀ : ℂ) + (a : ℂ) * z
  have hg : Continuous g := continuous_const.add (continuous_const.mul continuous_id)
  have h1 : cfc g A = algebraMap ℂ 𝒜 E₀ + (a : ℂ) • A := by
    rw [cfc_const_add (E₀ : ℂ) (fun z => (a : ℂ) * z) A, cfc_const_mul_id (a : ℂ) A]
  rw [← h1, ← cfc_comp' F g A hF.continuousOn hg.continuousOn]
  congr 1
  funext z
  simp [F, g, affine, Complex.add_re, Complex.mul_re]

lemma isStarNormal_affine (E₀ a : ℝ) {A : 𝒜} (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (algebraMap ℂ 𝒜 E₀ + (a : ℂ) • A) := by
  refine IsSelfAdjoint.add ?_ ?_
  · rw [IsSelfAdjoint, ← algebraMap_star_comm, Complex.star_def, Complex.conj_ofReal]
  · exact IsSelfAdjoint.smul (by rw [IsSelfAdjoint, Complex.star_def, Complex.conj_ofReal]) hA

/-- Spectral mapping for the affine change: `spec_ℝ(E₀ + aA) = Φ(spec_ℝ A)`. -/
lemma spectrum_real_affine (E₀ a : ℝ) {A : 𝒜} (hA : IsSelfAdjoint A) :
    spectrum ℝ (algebraMap ℂ 𝒜 E₀ + (a : ℂ) • A) = affine E₀ a '' spectrum ℝ A := by
  have hn : IsStarNormal A := hA.isStarNormal
  set g : ℂ → ℂ := fun z => (E₀ : ℂ) + (a : ℂ) * z
  have h1 : cfc g A = algebraMap ℂ 𝒜 E₀ + (a : ℂ) • A := by
    rw [cfc_const_add (E₀ : ℂ) (fun z => (a : ℂ) * z) A, cfc_const_mul_id (a : ℂ) A]
  have hspec : spectrum ℂ (algebraMap ℂ 𝒜 E₀ + (a : ℂ) • A) = g '' spectrum ℂ A := by
    rw [← h1, cfc_map_spectrum g A]
  ext t
  rw [← spectrum.preimage_algebraMap ℂ, ← spectrum.preimage_algebraMap ℂ (a := A)]
  simp only [mem_preimage, Complex.coe_algebraMap, hspec, mem_image]
  constructor
  · rintro ⟨z, hz, hzt⟩
    have hzr : z = ((z.re : ℝ) : ℂ) := by
      have := hA.mem_spectrum_eq_re hz
      exact this
    refine ⟨z.re, by rw [← hzr]; exact hz, ?_⟩
    have := congrArg Complex.re hzt
    simpa [g, affine, Complex.add_re, Complex.mul_re, hzr ▸ (Complex.ofReal_im z.re)] using this
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, by simp [g, affine]⟩

end CFC

/-! ### Spectral measures and spectral types (Paper I vocabulary on `ℓ²(ι)`) -/

section SpectralTypes

variable {ι : Type*}

/-- `Φ(T) = E₀ + a T`. -/
def affineOp (E₀ a : ℝ) (T : Op ι) : Op ι := algebraMap ℂ (Op ι) E₀ + (a : ℂ) • T

lemma _root_.IsSelfAdjoint.affineOp (E₀ a : ℝ) {T : Op ι} (hT : IsSelfAdjoint T) :
    IsSelfAdjoint (affineOp E₀ a T) := isStarNormal_affine E₀ a hT

lemma affineOp_inv {E₀ a : ℝ} (ha : a ≠ 0) (T : Op ι) :
    affineOp (-E₀ / a) a⁻¹ (affineOp E₀ a T) = T := by
  have h1 : ((a⁻¹ : ℝ) : ℂ) * (a : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ ha, Complex.ofReal_one]
  have h2 : ((-E₀ / a : ℝ) : ℂ) + ((a⁻¹ : ℝ) : ℂ) * (E₀ : ℂ) = 0 := by
    push_cast; field_simp; ring
  simp only [affineOp, Algebra.algebraMap_eq_smul_one, smul_add, smul_smul, h1, one_smul]
  rw [← add_assoc, ← add_smul, h2, zero_smul, zero_add]

lemma spectrum_affineOp (E₀ a : ℝ) {T : Op ι} (hT : IsSelfAdjoint T) :
    spectrum ℝ (affineOp E₀ a T) = affine E₀ a '' spectrum ℝ T :=
  spectrum_real_affine E₀ a hT

/-- Spectral measures are pushed forward by `Φ`. -/
theorem _root_.AMO.IsSpectralMeasure.map_affine {T : Op ι} (hT : IsSelfAdjoint T) {ψ : L2 ι}
    {μ : Measure ℝ} (h : IsSpectralMeasure T ψ μ) (E₀ a : ℝ) :
    IsSpectralMeasure (affineOp E₀ a T) ψ (μ.map (affine E₀ a)) := by
  have := h.1
  refine ⟨inferInstance, fun f => ?_⟩
  rw [integral_map (measurable_affine E₀ a).aemeasurable f.continuous.aestronglyMeasurable]
  set g : ℝ →ᵇ ℝ := f.compContinuous ⟨affine E₀ a, continuous_affine E₀ a⟩
  have hg := h.2 g
  rw [show (∫ t, f (affine E₀ a t) ∂μ) = ∫ t, g t ∂μ from rfl, hg]
  have hn : IsStarNormal T := hT.isStarNormal
  rw [show (fun z : ℂ => ((g z.re : ℝ) : ℂ)) = fun z => ((f (affine E₀ a z.re) : ℝ) : ℂ) from rfl,
    cfc_affine_re E₀ a T f f.continuous]
  rfl

theorem _root_.AMO.PurelyAC.affineOp {T : Op ι} (hT : IsSelfAdjoint T) (h : PurelyAC T) (E₀ : ℝ)
    {a : ℝ} (ha : a ≠ 0) : PurelyAC (affineOp E₀ a T) := by
  intro ψ
  obtain ⟨μ, hμ, hac⟩ := h ψ
  exact ⟨_, IsSpectralMeasure.map_affine hT hμ E₀ a, AbsolutelyContinuous.map_affine hac ha⟩

theorem _root_.AMO.NoACComponent.affineOp {T : Op ι} (hT : IsSelfAdjoint T) (h : NoACComponent T)
    (E₀ : ℝ) {a : ℝ} (ha : a ≠ 0) : NoACComponent (affineOp E₀ a T) := by
  intro ψ
  obtain ⟨μ, hμ, hs⟩ := h ψ
  exact ⟨_, IsSpectralMeasure.map_affine hT hμ E₀ a, MutuallySingular.map_affine hs ha⟩

theorem _root_.AMO.PurelySCOn.affineOp {T : Op ι} (hT : IsSelfAdjoint T) {S : Set ℝ} (h : PurelySCOn T S)
    (E₀ : ℝ) {a : ℝ} (ha : a ≠ 0) :
    PurelySCOn (affineOp E₀ a T) (affine E₀ a '' S) := by
  intro ψ
  obtain ⟨μ, hμ, hs, hat⟩ := h ψ
  have hemb : MeasurableEmbedding (affine E₀ a) :=
    (affineHomeomorph E₀ a ha).measurableEmbedding
  refine ⟨_, IsSpectralMeasure.map_affine hT hμ E₀ a, ?_, ?_⟩
  · rw [hemb.restrict_map, show affine E₀ a ⁻¹' (affine E₀ a '' S) = S from
      preimage_image_eq S (affine_injective ha)]
    exact MutuallySingular.map_affine hs ha
  · rintro _ ⟨E, hE, rfl⟩
    rw [hemb.map_apply, show affine E₀ a ⁻¹' {affine E₀ a E} = {E} by
      ext t; simp [(affine_injective ha).eq_iff]]
    exact hat E hE

theorem _root_.AMO.PurelySC.affineOp {T : Op ι} (hT : IsSelfAdjoint T) (h : PurelySC T)
    (E₀ : ℝ) {a : ℝ} (ha : a ≠ 0) : PurelySC (affineOp E₀ a T) := by
  have := PurelySCOn.affineOp hT h E₀ ha
  rwa [image_univ_of_surjective (f := affine E₀ a) (affineHomeomorph E₀ a ha).surjective] at this

lemma affineOp_apply_eigen {E₀ a : ℝ} {T : Op ι} {u : L2 ι} {E : ℝ}
    (h : T u = algebraMap ℂ (Op ι) E u) :
    affineOp E₀ a T u = algebraMap ℂ (Op ι) (affine E₀ a E) u := by
  simp only [affineOp, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, h,
    Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.one_apply, affine]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_smul]
  rw [← add_smul]; push_cast; ring_nf

theorem _root_.AMO.NoEigenvaluesIn.affineOp {T : Op ι} {S : Set ℝ} (h : NoEigenvaluesIn T S) (E₀ : ℝ)
    {a : ℝ} (ha : a ≠ 0) : NoEigenvaluesIn (affineOp E₀ a T) (affine E₀ a '' S) := by
  rintro _ ⟨E, hE, rfl⟩ u hu
  refine h E hE u ?_
  have := affineOp_apply_eigen (E₀ := -E₀ / a) (a := a⁻¹) hu
  rwa [affineOp_inv ha, affine_inv ha] at this

theorem _root_.AMO.AndersonLocalizedOn.affineOp {T : Op ℤ} (hT : IsSelfAdjoint T) {S : Set ℝ}
    (h : AndersonLocalizedOn T S) (E₀ : ℝ) {a : ℝ} (ha : a ≠ 0) :
    AndersonLocalizedOn (affineOp E₀ a T) (affine E₀ a '' S) := by
  obtain ⟨J, u, E, hon, heig, hdec, hcomp⟩ := h
  refine ⟨J, u, fun j => affine E₀ a (E j), hon, fun j => ⟨⟨E j, (heig j).1, rfl⟩,
    affineOp_apply_eigen (heig j).2⟩, hdec, ?_⟩
  rintro ψ ⟨μ', hμ', hcarr⟩
  refine hcomp ψ ⟨μ'.map (affine (-E₀ / a) a⁻¹), ?_, ?_⟩
  · have := IsSpectralMeasure.map_affine (IsSelfAdjoint.affineOp E₀ a hT) hμ' (-E₀ / a) a⁻¹
    rwa [affineOp_inv ha] at this
  · have hemb : MeasurableEmbedding (affine (-E₀ / a) a⁻¹) :=
      (affineHomeomorph E₀ a ha).symm.measurableEmbedding
    rw [hemb.map_apply, preimage_compl]
    have : affine (-E₀ / a) a⁻¹ ⁻¹' S = affine E₀ a '' S :=
      ((affineHomeomorph E₀ a ha).image_eq_preimage_symm S).symm
    rw [this]
    exact hcarr

end SpectralTypes

end CMS
