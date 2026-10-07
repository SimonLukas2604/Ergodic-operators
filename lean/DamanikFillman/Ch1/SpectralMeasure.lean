/-
Formalization of Damanik–Fillman, *One-Dimensional Ergodic Schrödinger Operators I*, Chapter 1.

# Spectral measures of bounded self-adjoint operators  (book §1.4, Theorems 1.4.11–1.4.13,
pp. 21–25)

For a bounded self-adjoint operator `A` on a complex Hilbert space `H` and a vector `φ ∈ H`, we
construct the spectral measure `μ_φ = DF.spectralMeasure A hA φ`, a finite Borel measure on `ℝ`
(Theorem 1.4.12), characterised by
`∫ f dμ_φ = ⟪φ, f(A) φ⟫` for continuous `f`,
where `f(A)` is Mathlib's continuous functional calculus `cfc f A` (this is the book's
Theorem 1.4.11; Mathlib provides it for any C⋆-algebra, in particular `H →L[ℂ] H`).

Construction: `f ↦ Re ⟪φ, cfc f A φ⟫` is a positive linear functional on `C_c(ℝ, ℝ)`; we take
its Riesz–Markov–Kakutani measure (`RealRMK.rieszMeasure`).  The book uses the Riesz–Markov
theorem on `C(σ(A))` instead; the resulting measures coincide.

Main results
* `DF.spectralMeasure` — the measure `μ_φ`;
* `DF.spectralMeasure_compl_spectrum` — `μ_φ(ℝ ∖ σ(A)) = 0`;
* `DF.isFiniteMeasure_spectralMeasure`, `DF.spectralMeasure_univ` — `μ_φ(ℝ) = ‖φ‖²`;
* `DF.integral_spectralMeasure` / `DF.integral_spectralMeasure_complex` — the defining identity
  `∫ f dμ_φ = ⟪φ, f(A) φ⟫` for continuous `f : ℝ → ℝ`, resp. `f : ℝ → ℂ`
  (Theorem 1.4.12 with `ψ = φ`);
* `DF.spectralMeasure_unique` — uniqueness among finite measures;
* `DF.inner_resolvent_eq_integral` — the Stieltjes/Borel transform formula
  `⟪φ, (A - z)⁻¹ φ⟫ = ∫ dμ_φ(x) / (x - z)` for `z ∉ ℝ`;
* `DF.inner_cfc_polarization` — polarization: `⟪φ, f(A) ψ⟫` in terms of the four measures
  `μ_{φ ± ψ}`, `μ_{φ ± iψ}` (this replaces the complex measures `μ_{φ,ψ}` of Theorem 1.4.12);
* `DF.isSpectralMeasure_spectralMeasure` — compatibility with the predicate
  `AMO.IsSpectralMeasure` used elsewhere in the project;
* specialisation to `DF.schr V` on `ℓ²(ℤ)`: `DF.schrSpectralMeasure`.

Deviations
* The complex measures `μ_{φ,ψ}` are not constructed as `ComplexMeasure`s; we provide the
  polarization identity for integrals instead.
* `(A - z)⁻¹` is expressed as `Ring.inverse (A - algebraMap ℂ _ z)`.

No `Statement` props are introduced in this file.
-/
import DamanikFillman.Basic
import AnalyticPerturbationsAMO.Spectral

noncomputable section

open scoped InnerProductSpace ComplexConjugate CompactlySupported
open MeasureTheory Set Filter CompactlySupportedContinuousMap L2

namespace DF

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

section General

variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)

/-- `⟪φ, T φ⟫` is real for self-adjoint `T`. -/
lemma inner_self_apply_im_eq_zero {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) (φ : H) :
    (⟪φ, T φ⟫_ℂ).im = 0 :=
  hT.isSymmetric.im_inner_self_apply φ

lemma inner_self_apply_eq_re {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) (φ : H) :
    ⟪φ, T φ⟫_ℂ = ((RCLike.re ⟪φ, T φ⟫_ℂ : ℝ) : ℂ) := by
  apply Complex.ext <;> simp [inner_self_apply_im_eq_zero hT φ]

/-- The positive linear functional `f ↦ Re ⟪φ, f(A) φ⟫` on `C_c(ℝ, ℝ)`. -/
def spectralFunctional (φ : H) : C_c(ℝ, ℝ) →ₚ[ℝ] ℝ where
  toFun f := RCLike.re ⟪φ, cfc (f : ℝ → ℝ) A φ⟫_ℂ
  map_add' f g := by
    simp only [coe_add, Pi.add_apply]
    rw [cfc_add (a := A) f g (f.continuous.continuousOn) (g.continuous.continuousOn)]
    simp
  map_smul' c f := by
    simp only [coe_smul, Pi.smul_apply, RingHom.id_apply]
    rw [cfc_smul (a := A) c f (f.continuous.continuousOn)]
    simp [_root_.smul_apply]
  monotone' f g hfg := by
    have hle : cfc (f : ℝ → ℝ) A ≤ cfc (g : ℝ → ℝ) A :=
      cfc_mono (fun x _ => hfg x) f.continuous.continuousOn g.continuous.continuousOn
    have hpos := (ContinuousLinearMap.nonneg_iff_isPositive).1 (sub_nonneg.2 hle)
    have := hpos.re_inner_nonneg_right φ
    simp only [_root_.sub_apply, inner_sub_right, map_sub] at this
    simp only
    linarith

lemma spectralFunctional_apply (φ : H) (f : C_c(ℝ, ℝ)) :
    spectralFunctional A φ f = RCLike.re ⟪φ, cfc (f : ℝ → ℝ) A φ⟫_ℂ := rfl

/-- **Spectral measure** `μ_φ` of the self-adjoint operator `A` at `φ` (Theorem 1.4.12). -/
def spectralMeasure (_ : IsSelfAdjoint A) (φ : H) : Measure ℝ :=
  RealRMK.rieszMeasure (spectralFunctional A φ)

include hA

instance (φ : H) : (spectralMeasure A hA φ).Regular := by
  unfold spectralMeasure; infer_instance

/-- Defining identity on compactly supported continuous functions. -/
lemma integral_spectralMeasure_cc (φ : H) (f : C_c(ℝ, ℝ)) :
    ∫ x, f x ∂(spectralMeasure A hA φ) = RCLike.re ⟪φ, cfc (f : ℝ → ℝ) A φ⟫_ℂ :=
  RealRMK.integral_rieszMeasure _ f

omit hA in
lemma isCompact_spectrum_real : IsCompact (spectrum ℝ A) :=
  ContinuousFunctionalCalculus.isCompact_spectrum (p := IsSelfAdjoint) A

/-- `μ_φ` is supported on the spectrum: `μ_φ(ℝ ∖ σ(A)) = 0`. -/
theorem spectralMeasure_compl_spectrum (φ : H) :
    spectralMeasure A hA φ (spectrum ℝ A)ᶜ = 0 := by
  have hopen : IsOpen (spectrum ℝ A)ᶜ := (isCompact_spectrum_real A).isClosed.isOpen_compl
  rw [hopen.measure_eq_iSup_isCompact]
  simp only [ENNReal.iSup_eq_zero]
  intro K hKU hK
  obtain ⟨f, hf1, hfc, hfU, hf01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hopen hKU
  let g : C_c(ℝ, ℝ) := ⟨f, hfc⟩
  have hle := RealRMK.rieszMeasure_le_of_eq_one (spectralFunctional A φ) (f := g)
    (fun x => (hf01 x).1) hK (fun x hx => hf1 hx)
  have h0 : spectralFunctional A φ g = 0 := by
    rw [spectralFunctional_apply]
    have : cfc (g : ℝ → ℝ) A = cfc (0 : ℝ → ℝ) A := by
      refine cfc_congr fun x hx => ?_
      have : x ∉ tsupport f := fun h => hfU h hx
      exact image_eq_zero_of_notMem_tsupport this
    simp [this]
  rw [h0, ENNReal.ofReal_zero] at hle
  exact le_antisymm hle bot_le

lemma ae_mem_spectrum (φ : H) : ∀ᵐ x ∂(spectralMeasure A hA φ), x ∈ spectrum ℝ A :=
  mem_ae_iff.2 (spectralMeasure_compl_spectrum A hA φ)

omit hA in
/-- A cutoff function: compactly supported, equal to `1` on `σ(A)`. -/
lemma exists_cutoff : ∃ g : C_c(ℝ, ℝ), (∀ x ∈ spectrum ℝ A, g x = 1) ∧ ∀ x, 0 ≤ g x := by
  obtain ⟨f, hf1, hfc, -, hf01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
    (isCompact_spectrum_real A) isOpen_univ (subset_univ _)
  exact ⟨⟨f, hfc⟩, fun x hx => hf1 hx, fun x => (hf01 x).1⟩

/-- `μ_φ` is a finite measure. -/
instance isFiniteMeasure_spectralMeasure (φ : H) : IsFiniteMeasure (spectralMeasure A hA φ) := by
  obtain ⟨g, hg1, hg0⟩ := exists_cutoff A
  constructor
  calc spectralMeasure A hA φ univ
      ≤ spectralMeasure A hA φ (spectrum ℝ A) + spectralMeasure A hA φ (spectrum ℝ A)ᶜ := by
        rw [← union_compl_self (spectrum ℝ A)]; exact measure_union_le _ _
    _ = spectralMeasure A hA φ (spectrum ℝ A) := by rw [spectralMeasure_compl_spectrum, add_zero]
    _ ≤ ENNReal.ofReal (spectralFunctional A φ g) :=
        RealRMK.rieszMeasure_le_of_eq_one _ hg0 (isCompact_spectrum_real A) hg1
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- The defining identity `∫ f dμ_φ = Re ⟪φ, f(A) φ⟫` for every continuous `f : ℝ → ℝ`
(Theorem 1.4.12). -/
theorem integral_spectralMeasure_re (φ : H) {f : ℝ → ℝ} (hf : Continuous f) :
    ∫ x, f x ∂(spectralMeasure A hA φ) = RCLike.re ⟪φ, cfc f A φ⟫_ℂ := by
  obtain ⟨g, hg1, -⟩ := exists_cutoff A
  let h : C_c(ℝ, ℝ) := ⟨⟨fun x => f x * g x, hf.mul g.continuous⟩,
    g.hasCompactSupport.mul_left⟩
  have hae : (fun x => f x) =ᵐ[spectralMeasure A hA φ] fun x => h x := by
    filter_upwards [ae_mem_spectrum A hA φ] with x hx
    simp [h, hg1 x hx]
  rw [integral_congr_ae hae, integral_spectralMeasure_cc]
  congr 3
  refine cfc_congr fun x hx => ?_
  simp [h, hg1 x hx]

/-- Continuous functions are `μ_φ`-integrable. -/
lemma integrable_spectralMeasure (φ : H) {f : ℝ → ℝ} (hf : Continuous f) :
    Integrable f (spectralMeasure A hA φ) := by
  obtain ⟨g, hg1, -⟩ := exists_cutoff A
  have hint : Integrable (fun x => f x * g x) (spectralMeasure A hA φ) :=
    (hf.mul g.continuous).integrable_of_hasCompactSupport g.hasCompactSupport.mul_left
  refine hint.congr ?_
  filter_upwards [ae_mem_spectrum A hA φ] with x hx
  simp [hg1 x hx]

lemma integrable_spectralMeasure_complex (φ : H) {f : ℝ → ℂ} (hf : Continuous f) :
    Integrable f (spectralMeasure A hA φ) := by
  obtain ⟨g, hg1, -⟩ := exists_cutoff A
  have hint : Integrable (fun x => f x * (g x : ℂ)) (spectralMeasure A hA φ) :=
    (hf.mul (Complex.continuous_ofReal.comp g.continuous)).integrable_of_hasCompactSupport
      (g.hasCompactSupport.comp_left Complex.ofReal_zero).mul_left
  refine hint.congr ?_
  filter_upwards [ae_mem_spectrum A hA φ] with x hx
  simp [hg1 x hx]

/-- `∫ f dμ_φ = ⟪φ, f(A) φ⟫` for continuous real `f` (the inner product is real). -/
theorem integral_spectralMeasure (φ : H) {f : ℝ → ℝ} (hf : Continuous f) :
    ((∫ x, f x ∂(spectralMeasure A hA φ) : ℝ) : ℂ) = ⟪φ, cfc f A φ⟫_ℂ := by
  rw [integral_spectralMeasure_re A hA φ hf, ← inner_self_apply_eq_re (IsSelfAdjoint.cfc (f := f))]

/-- `μ_φ(ℝ) = ‖φ‖²`. -/
theorem spectralMeasure_univ (φ : H) :
    spectralMeasure A hA φ univ = ENNReal.ofReal (‖φ‖ ^ 2) := by
  have h := integral_spectralMeasure_re A hA φ (f := fun _ => (1 : ℝ)) continuous_const
  rw [cfc_const_one ℝ A] at h
  simp only [integral_const, smul_eq_mul, mul_one, one_apply_eq_self] at h
  rw [inner_self_eq_norm_sq_to_K] at h
  have h' : (spectralMeasure A hA φ).real univ = ‖φ‖ ^ 2 := by
    rw [h]; norm_cast
  rw [← h', measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

lemma spectralMeasure_real_univ (φ : H) : (spectralMeasure A hA φ).real univ = ‖φ‖ ^ 2 := by
  rw [measureReal_def, spectralMeasure_univ A hA, ENNReal.toReal_ofReal (by positivity)]

/-- Complex version of the defining identity: for continuous `f : ℝ → ℂ`,
`∫ f dμ_φ = ⟪φ, f(A) φ⟫`, where `f(A) = cfc (fun z ↦ f (Re z)) A` in the complex functional
calculus (on `σ(A) ⊆ ℝ` this is just `f`). -/
theorem integral_spectralMeasure_complex (φ : H) {f : ℝ → ℂ} (hf : Continuous f) :
    ∫ x, f x ∂(spectralMeasure A hA φ) = ⟪φ, cfc (fun z : ℂ => f z.re) A φ⟫_ℂ := by
  have hre : Continuous fun x => (f x).re := Complex.continuous_re.comp hf
  have him : Continuous fun x => (f x).im := Complex.continuous_im.comp hf
  have hsplit : cfc (fun z : ℂ => f z.re) A =
      cfc (fun x => (f x).re) A + Complex.I • cfc (fun x => (f x).im) A := by
    rw [cfc_real_eq_complex (fun x => (f x).re) hA, cfc_real_eq_complex (fun x => (f x).im) hA,
      ← cfc_smul (a := A) Complex.I _ (by fun_prop),
      ← cfc_add (a := A) _ _ (by fun_prop) (by fun_prop)]
    congr 1
    funext z
    apply Complex.ext <;> simp
  rw [hsplit, _root_.add_apply, _root_.smul_apply, inner_add_right,
    inner_smul_right, ← integral_spectralMeasure A hA φ hre,
    ← integral_spectralMeasure A hA φ him]
  have hint := integrable_spectralMeasure_complex A hA φ hf
  apply Complex.ext
  · have := integral_re hint
    simp only [RCLike.re_to_complex] at this
    simp [← this]
  · have := integral_im hint
    simp only [RCLike.im_to_complex] at this
    simp [← this]

/-- **Uniqueness** of the spectral measure: a finite Borel measure reproducing
`Re ⟪φ, f(A) φ⟫` on `C_c(ℝ, ℝ)` equals `μ_φ`. -/
theorem spectralMeasure_unique (φ : H) (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ∀ f : C_c(ℝ, ℝ), ∫ x, f x ∂ν = RCLike.re ⟪φ, cfc (f : ℝ → ℝ) A φ⟫_ℂ) :
    ν = spectralMeasure A hA φ :=
  Measure.ext_of_integral_eq_on_compactlySupported fun f => by
    rw [hν, integral_spectralMeasure_cc]

/-- Uniqueness, version with arbitrary continuous test functions. -/
theorem spectralMeasure_unique' (φ : H) (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hν : ∀ f : ℝ → ℝ, Continuous f → ∫ x, f x ∂ν = RCLike.re ⟪φ, cfc f A φ⟫_ℂ) :
    ν = spectralMeasure A hA φ :=
  spectralMeasure_unique A hA φ ν fun f => hν f f.continuous

/-- **Resolvent formula** (used in Theorem 1.4.13 and throughout the book):
for `z ∉ ℝ`, `⟪φ, (A - z)⁻¹ φ⟫ = ∫ dμ_φ(x) / (x - z)`. -/
theorem inner_resolvent_eq_integral (φ : H) {z : ℂ} (hz : z.im ≠ 0) :
    ⟪φ, Ring.inverse (A - algebraMap ℂ (H →L[ℂ] H) z) φ⟫_ℂ =
      ∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂(spectralMeasure A hA φ) := by
  have hcont : Continuous fun x : ℝ => ((x : ℂ) - z)⁻¹ := by
    refine Continuous.inv₀ (by fun_prop) fun x h => hz ?_
    have := congrArg Complex.im h
    simpa using this.symm
  rw [integral_spectralMeasure_complex A hA φ hcont]
  have hne : ∀ w ∈ spectrum ℂ A, w - z ≠ 0 := by
    intro w hw h
    have h1 := hA.im_eq_zero_of_mem_spectrum hw
    have : w.im = z.im := by rw [sub_eq_zero.1 h]
    exact hz (this ▸ h1)
  have h1 : cfc (fun w : ℂ => w - z) A = A - algebraMap ℂ (H →L[ℂ] H) z := by
    rw [cfc_sub (a := A) (fun w => w) (fun _ => z), cfc_id' ℂ A, cfc_const z A]
  have h2 : cfc (fun w : ℂ => (w - z)⁻¹) A = Ring.inverse (A - algebraMap ℂ (H →L[ℂ] H) z) := by
    rw [cfc_inv (a := A) (fun w => w - z) hne, h1]
  rw [← h2]
  congr 2
  refine cfc_congr fun w hw => ?_
  show (w - z)⁻¹ = ((w.re : ℂ) - z)⁻¹
  rw [← hA.mem_spectrum_eq_re hw]

/-- **Polarization** (replaces the complex measures `μ_{φ,ψ}` of Theorem 1.4.12):
`⟪φ, f(A) ψ⟫` is a combination of integrals against four spectral measures. -/
theorem inner_cfc_polarization (φ ψ : H) {f : ℝ → ℝ} (hf : Continuous f) :
    ⟪φ, cfc f A ψ⟫_ℂ =
      ((∫ x, f x ∂(spectralMeasure A hA (φ + ψ)) : ℝ) - (∫ x, f x ∂(spectralMeasure A hA (φ - ψ)) : ℝ)
        - Complex.I * (∫ x, f x ∂(spectralMeasure A hA (φ + Complex.I • ψ)) : ℝ)
        + Complex.I * (∫ x, f x ∂(spectralMeasure A hA (φ - Complex.I • ψ)) : ℝ)) / 4 := by
  have hT : IsSelfAdjoint (cfc f A) := IsSelfAdjoint.cfc
  have hsym : ∀ x y, ⟪cfc f A x, y⟫_ℂ = ⟪x, cfc f A y⟫_ℂ := fun x y => hT.isSymmetric x y
  simp only [integral_spectralMeasure A hA _ hf]
  have key : ⟪cfc f A φ, ψ⟫_ℂ =
      (⟪φ + ψ, cfc f A (φ + ψ)⟫_ℂ - ⟪φ - ψ, cfc f A (φ - ψ)⟫_ℂ
        - Complex.I * ⟪φ + Complex.I • ψ, cfc f A (φ + Complex.I • ψ)⟫_ℂ
        + Complex.I * ⟪φ - Complex.I • ψ, cfc f A (φ - Complex.I • ψ)⟫_ℂ) / 4 := by
    rw [← hsym (φ + ψ), ← hsym (φ - ψ), ← hsym (φ + Complex.I • ψ), ← hsym (φ - Complex.I • ψ)]
    exact inner_map_polarization' ((cfc f A : H →L[ℂ] H) : H →ₗ[ℂ] H) φ ψ
  rw [← hsym φ ψ, key]

/-- Scaling: `μ_{cφ} = |c|² μ_φ`. -/
theorem spectralMeasure_smul (c : ℂ) (φ : H) :
    spectralMeasure A hA (c • φ) = ENNReal.ofReal (‖c‖ ^ 2) • spectralMeasure A hA φ := by
  symm
  have : IsFiniteMeasure (ENNReal.ofReal (‖c‖ ^ 2) • spectralMeasure A hA φ) :=
    ⟨by rw [Measure.smul_apply, smul_eq_mul]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)⟩
  refine spectralMeasure_unique A hA (c • φ) _ fun f => ?_
  rw [integral_smul_measure, integral_spectralMeasure_cc, ENNReal.toReal_ofReal (by positivity)]
  simp only [map_smul, inner_smul_left, inner_smul_right, smul_eq_mul]
  rw [inner_self_apply_eq_re (IsSelfAdjoint.cfc (f := (f : ℝ → ℝ)) (a := A)) φ]
  rw [← mul_assoc, Complex.mul_conj']
  norm_cast

end General

/-! ### Compatibility with `AMO.IsSpectralMeasure` -/

section L2

variable {ι : Type*}

/-- `DF.spectralMeasure` satisfies the project-wide predicate `AMO.IsSpectralMeasure`. -/
theorem isSpectralMeasure_spectralMeasure (T : AMO.Op ι) (hT : IsSelfAdjoint T) (ψ : L2 ι) :
    AMO.IsSpectralMeasure T ψ (spectralMeasure T hT ψ) := by
  refine ⟨inferInstance, fun f => ?_⟩
  rw [← cfc_real_eq_complex (fun x => f x) hT]
  exact integral_spectralMeasure_re T hT ψ f.continuous

/-- Any measure satisfying `AMO.IsSpectralMeasure` is `DF.spectralMeasure`. -/
theorem AMO_isSpectralMeasure_iff (T : AMO.Op ι) (hT : IsSelfAdjoint T) (ψ : L2 ι)
    (μ : Measure ℝ) : AMO.IsSpectralMeasure T ψ μ ↔ μ = spectralMeasure T hT ψ := by
  refine ⟨fun h => ?_, fun h => h ▸ isSpectralMeasure_spectralMeasure T hT ψ⟩
  have := h.1
  refine spectralMeasure_unique T hT ψ μ fun f => ?_
  have := h.2 f.toBoundedContinuousFunction
  rw [← cfc_real_eq_complex (fun x => f.toBoundedContinuousFunction x) hT] at this
  exact this

end L2

/-! ### Discrete Schrödinger operators -/

/-- The discrete Schrödinger operator (2.2.1) with bounded real potential is self-adjoint. -/
theorem isSelfAdjoint_schr {V : ℤ → ℝ} (hV : BddPot V) : IsSelfAdjoint (schr V) := by
  rw [IsSelfAdjoint, schr, ContinuousLinearMap.star_eq_adjoint, map_add, map_add,
    L2.adjoint_weightedShift bdd_one, L2.adjoint_weightedShift bdd_one,
    L2.adjoint_weightedShift (bdd_of_bddPot hV)]
  have e1 : weightedShift (fun j => conj ((fun _ : ℤ => (1 : ℂ)) ((Equiv.addRight (1 : ℤ)).symm j)))
      (Equiv.addRight (1 : ℤ)).symm =
      weightedShift (fun _ : ℤ => (1 : ℂ)) (Equiv.addRight (-1)) :=
    weightedShift_congr (fun _ => by simp) (fun i => by simp)
  have e2 : weightedShift (fun j => conj ((fun _ : ℤ => (1 : ℂ)) ((Equiv.addRight (-1 : ℤ)).symm j)))
      (Equiv.addRight (-1 : ℤ)).symm =
      weightedShift (fun _ : ℤ => (1 : ℂ)) (Equiv.addRight 1) :=
    weightedShift_congr (fun _ => by simp) (fun i => by simp)
  have e3 : weightedShift (fun j => conj ((fun n : ℤ => ((V n : ℝ) : ℂ)) ((Equiv.refl ℤ).symm j)))
      (Equiv.refl ℤ).symm = weightedShift (fun n : ℤ => ((V n : ℝ) : ℂ)) (Equiv.refl ℤ) :=
    weightedShift_congr (fun _ => by simp) (fun i => by simp)
  rw [e1, e2, e3]
  abel

/-- Spectral measure of `H_V = schr V` at `φ ∈ ℓ²(ℤ)`.

Technical remark: for operators on `L2 ι` Lean does not find the *real* continuous functional
calculus instance by type-class search (the `ℝ`-algebra structure on `L2 ι →L[ℂ] L2 ι` coming
from `lp` is not reducibly defeq to the one obtained by restricting scalars from `ℂ`), so for
concrete operators on `ℓ²` we state results with the complex calculus
`cfc (fun z : ℂ ↦ f z.re)` (as in `AMO.IsSpectralMeasure`).  The general lemmas above, stated
for an arbitrary Hilbert space `H`, apply to `L2 ι` without problems. -/
def schrSpectralMeasure {V : ℤ → ℝ} (hV : BddPot V) (φ : L2 ℤ) : Measure ℝ :=
  spectralMeasure (schr V) (isSelfAdjoint_schr hV) φ

theorem integral_schrSpectralMeasure {V : ℤ → ℝ} (hV : BddPot V) (φ : L2 ℤ) {f : ℝ → ℝ}
    (hf : Continuous f) :
    ((∫ x, f x ∂(schrSpectralMeasure hV φ) : ℝ) : ℂ) =
      ⟪φ, cfc (fun z : ℂ => ((f z.re : ℝ) : ℂ)) (schr V) φ⟫_ℂ := by
  have := integral_spectralMeasure_complex (schr V) (isSelfAdjoint_schr hV) φ
    (f := fun x => ((f x : ℝ) : ℂ)) (by fun_prop)
  exact integral_complex_ofReal.symm.trans this

theorem schrSpectralMeasure_compl_spectrum {V : ℤ → ℝ} (hV : BddPot V) (φ : L2 ℤ) :
    schrSpectralMeasure hV φ (spectrum ℝ (schr V))ᶜ = 0 :=
  spectralMeasure_compl_spectrum _ _ φ

instance {V : ℤ → ℝ} (hV : BddPot V) (φ : L2 ℤ) : IsFiniteMeasure (schrSpectralMeasure hV φ) :=
  isFiniteMeasure_spectralMeasure _ _ φ

theorem inner_resolvent_schr {V : ℤ → ℝ} (hV : BddPot V) (φ : L2 ℤ) {z : ℂ} (hz : z.im ≠ 0) :
    ⟪φ, Ring.inverse (schr V - algebraMap ℂ Op z) φ⟫_ℂ =
      ∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂(schrSpectralMeasure hV φ) :=
  inner_resolvent_eq_integral _ _ φ hz


end DF
