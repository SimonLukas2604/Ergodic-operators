import ContinuumMagnetic.UnitaryTransfer

/-!
# Existence and uniqueness of spectral measures on a general Hilbert space

For a self-adjoint `T : H →L[ℂ] H` on a complex Hilbert space and a vector `ψ`, we construct
the spectral measure of `(T, ψ)` in the sense of `CMS.IsSpectralMeasureH` (the continuous
functional calculus formulation of Paper I, `AMO.IsSpectralMeasure`).

* `CMS.spectralFunctional T ψ : C_c(ℝ, ℝ) →ₚ[ℝ] ℝ` is `f ↦ Re ⟪ψ, f(T) ψ⟫`; it is positive since
  `cfc` of a nonnegative function is a positive operator.
* `CMS.spectralMeasureH T ψ` is its Riesz–Markov–Kakutani measure.
* `CMS.spectralMeasureH_compl_spectrum`: it does not charge `(spectrum ℝ T)ᶜ`.
* `CMS.isSpectralMeasureH_spectralMeasureH`, `CMS.exists_isSpectralMeasureH`: it is a finite
  spectral measure; the passage from `C_c` to bounded continuous `f` multiplies `f` by a
  compactly supported cutoff `χ = 1` on the (compact) spectrum, using that `cfc` only sees the
  spectrum.
* `CMS.IsSpectralMeasureH.unique`: spectral measures are unique.
* `CMS.IsSpectralMeasureH.measure_univ`: the total mass is `‖ψ‖²`.
-/

noncomputable section

open scoped ComplexConjugate InnerProductSpace CompactlySupported ComplexOrder
open MeasureTheory Set BoundedContinuousFunction

namespace CMS

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The quadratic form `f ↦ Re ⟪ψ, f(T) ψ⟫` of the continuous functional calculus. -/
def spectralForm (T : H →L[ℂ] H) (ψ : H) (f : ℝ → ℝ) : ℝ :=
  RCLike.re ⟪ψ, cfc (fun z : ℂ => ((f z.re : ℝ) : ℂ)) T ψ⟫_ℂ

variable {T : H →L[ℂ] H} {ψ : H}

lemma continuousOn_ofReal_comp_re {f : ℝ → ℝ} (hf : Continuous f) (s : Set ℂ) :
    ContinuousOn (fun z : ℂ => ((f z.re : ℝ) : ℂ)) s :=
  (Complex.continuous_ofReal.comp (hf.comp Complex.continuous_re)).continuousOn

lemma spectralForm_add {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    spectralForm T ψ (f + g) = spectralForm T ψ f + spectralForm T ψ g := by
  unfold spectralForm
  have := cfc_add (a := T) (fun z : ℂ => ((f z.re : ℝ) : ℂ)) (fun z : ℂ => ((g z.re : ℝ) : ℂ))
    (continuousOn_ofReal_comp_re hf _) (continuousOn_ofReal_comp_re hg _)
  simp only [Pi.add_apply, Complex.ofReal_add, this, _root_.add_apply,
    inner_add_right, map_add]

lemma spectralForm_smul (c : ℝ) {f : ℝ → ℝ} (hf : Continuous f) :
    spectralForm T ψ (c • f) = c * spectralForm T ψ f := by
  unfold spectralForm
  have := cfc_const_mul (a := T) (c : ℂ) (fun z : ℂ => ((f z.re : ℝ) : ℂ))
    (continuousOn_ofReal_comp_re hf _)
  simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, this,
    _root_.smul_apply, inner_smul_right]
  simp

lemma spectralForm_nonneg {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) : 0 ≤ spectralForm T ψ f := by
  unfold spectralForm
  have h : 0 ≤ cfc (fun z : ℂ => ((f z.re : ℝ) : ℂ)) T :=
    cfc_nonneg fun z _ => Complex.zero_le_real.mpr (hf z.re)
  exact (ContinuousLinearMap.nonneg_iff_isPositive.mp h).re_inner_nonneg_right ψ

lemma re_mem_spectrum (hT : IsSelfAdjoint T) {z : ℂ} (hz : z ∈ spectrum ℂ T) :
    z.re ∈ spectrum ℝ T := by
  have h : ((z.re : ℝ) : ℂ) ∈ spectrum ℂ T := (hT.mem_spectrum_eq_re hz) ▸ hz
  exact (spectrum.algebraMap_mem_iff ℂ).mp h

/-- The form depends only on the values of `f` on the real spectrum. -/
lemma spectralForm_congr (hT : IsSelfAdjoint T) {f g : ℝ → ℝ}
    (h : ∀ x ∈ spectrum ℝ T, f x = g x) : spectralForm T ψ f = spectralForm T ψ g := by
  unfold spectralForm
  rw [cfc_congr (a := T) (g := fun z : ℂ => ((g z.re : ℝ) : ℂ))
    (fun z hz => by simp only [h _ (re_mem_spectrum hT hz)])]

lemma isCompact_spectrum_real (T : H →L[ℂ] H) : IsCompact (spectrum ℝ T) := by
  rw [← spectrum.preimage_algebraMap ℂ]
  exact Complex.isometry_ofReal.isClosedEmbedding.isCompact_preimage (spectrum.isCompact T)

/-- The positive linear functional `f ↦ Re ⟪ψ, f(T) ψ⟫` on `C_c(ℝ, ℝ)`. -/
def spectralFunctional (T : H →L[ℂ] H) (ψ : H) : C_c(ℝ, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun f => spectralForm T ψ f
      map_add' := fun f g => spectralForm_add f.continuous g.continuous
      map_smul' := fun c f => spectralForm_smul c f.continuous }
    (fun _ hf => spectralForm_nonneg (fun x => hf x))

/-- The spectral measure of `(T, ψ)`, built by Riesz–Markov–Kakutani. -/
def spectralMeasureH (T : H →L[ℂ] H) (ψ : H) : Measure ℝ :=
  RealRMK.rieszMeasure (spectralFunctional T ψ)

/-- `Λ` vanishes on nonnegative functions vanishing on the spectrum, hence the Riesz measure
does not charge the complement of the spectrum. -/
theorem spectralMeasureH_compl_spectrum (hT : IsSelfAdjoint T) (ψ : H) :
    spectralMeasureH T ψ (spectrum ℝ T)ᶜ = 0 := by
  set K := spectrum ℝ T
  have hK : IsCompact K := isCompact_spectrum_real T
  refine measure_null_of_locally_null _ fun x hx => ?_
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hK.isClosed.isOpen_compl x hx
  have hδ : (0 : ℝ) < ε / 2 := half_pos hε
  have hsub : Metric.closedBall x (ε / 2) ⊆ Kᶜ :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hball
  refine ⟨Metric.closedBall x (ε / 2),
    mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds x hδ), ?_⟩
  obtain ⟨φ, hφ1, hφ0, hφc, hφr⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_closedBall x (ε / 2)) hK.isClosed
    (Set.disjoint_left.mpr fun y hy hyK => hsub hy hyK)
  let φc : C_c(ℝ, ℝ) := ⟨φ, hφc⟩
  have hle := RealRMK.rieszMeasure_le_of_eq_one (spectralFunctional T ψ) (f := φc)
    (fun y => (hφr y).1) (isCompact_closedBall x (ε / 2)) (fun y hy => hφ1 hy)
  have h0 : spectralFunctional T ψ φc = 0 := by
    change spectralForm T ψ φ = 0
    rw [spectralForm_congr (g := fun _ => 0) hT (fun y hy => hφ0 hy)]
    simp [spectralForm]
  refine le_antisymm ?_ bot_le
  simpa [spectralMeasureH, h0] using hle

/-- **Existence of spectral measures.** For a self-adjoint `T`, the Riesz measure
`spectralMeasureH T ψ` is a (finite) spectral measure of `(T, ψ)`. -/
theorem isSpectralMeasureH_spectralMeasureH (hT : IsSelfAdjoint T) (ψ : H) :
    IsSpectralMeasureH T ψ (spectralMeasureH T ψ) := by
  set K := spectrum ℝ T
  set μ := spectralMeasureH T ψ
  have hK : IsCompact K := isCompact_spectrum_real T
  have hnull : μ Kᶜ = 0 := spectralMeasureH_compl_spectrum hT ψ
  obtain ⟨χ, hχ1, -, hχc, hχr⟩ := exists_continuous_one_zero_of_isCompact hK isClosed_empty
    (Set.disjoint_empty K)
  let χc : C_c(ℝ, ℝ) := ⟨χ, hχc⟩
  have hfin : IsFiniteMeasure μ := by
    refine ⟨?_⟩
    calc μ univ = μ (K ∪ Kᶜ) := by rw [Set.union_compl_self]
      _ ≤ μ K + μ Kᶜ := measure_union_le _ _
      _ ≤ ENNReal.ofReal (spectralFunctional T ψ χc) + 0 := by
          rw [hnull]
          gcongr
          exact RealRMK.rieszMeasure_le_of_eq_one _ (f := χc) (fun y => (hχr y).1) hK
            (fun y hy => hχ1 hy)
      _ < ⊤ := by simp
  refine ⟨hfin, fun f => ?_⟩
  let fχ : C_c(ℝ, ℝ) := ⟨⟨fun x => f x * χ x, by fun_prop⟩, hχc.mul_left (f := ⇑f)⟩
  have hae : ∀ᵐ x ∂μ, f x = fχ x := by
    filter_upwards [compl_mem_ae_iff.mpr hnull] with x hx
    rw [compl_compl] at hx
    change f x = f x * χ x
    rw [hχ1 hx, Pi.one_apply, mul_one]
  rw [integral_congr_ae hae]
  change ∫ x, fχ x ∂(RealRMK.rieszMeasure (spectralFunctional T ψ)) = _
  rw [RealRMK.integral_rieszMeasure]
  change spectralForm T ψ (fun x => f x * χ x) = _
  rw [spectralForm_congr (g := f) hT (fun x hx => by rw [hχ1 hx, Pi.one_apply, mul_one])]
  rfl

/-- **Existence of spectral measures carried by the spectrum.** -/
theorem exists_isSpectralMeasureH (hT : IsSelfAdjoint T) (ψ : H) :
    ∃ μ, IsSpectralMeasureH T ψ μ ∧ μ (spectrum ℝ T)ᶜ = 0 :=
  ⟨_, isSpectralMeasureH_spectralMeasureH hT ψ, spectralMeasureH_compl_spectrum hT ψ⟩

/-- **Uniqueness of spectral measures.** -/
theorem IsSpectralMeasureH.unique {μ ν : Measure ℝ} (hμ : IsSpectralMeasureH T ψ μ)
    (hν : IsSpectralMeasureH T ψ ν) : μ = ν := by
  have := hμ.1
  have := hν.1
  exact ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => (hμ.2 f).trans (hν.2 f).symm

/-- Every spectral measure of a self-adjoint `T` is the canonical one. -/
theorem IsSpectralMeasureH.eq_spectralMeasureH (hT : IsSelfAdjoint T) {μ : Measure ℝ}
    (hμ : IsSpectralMeasureH T ψ μ) : μ = spectralMeasureH T ψ :=
  hμ.unique (isSpectralMeasureH_spectralMeasureH hT ψ)

/-- Every spectral measure of a self-adjoint `T` is carried by the real spectrum. -/
theorem IsSpectralMeasureH.measure_compl_spectrum (hT : IsSelfAdjoint T) {μ : Measure ℝ}
    (hμ : IsSpectralMeasureH T ψ μ) : μ (spectrum ℝ T)ᶜ = 0 := by
  rw [hμ.eq_spectralMeasureH hT]; exact spectralMeasureH_compl_spectrum hT ψ

/-- **Total mass** (real form): `μ(ℝ) = ‖ψ‖²`. -/
theorem IsSpectralMeasureH.measureReal_univ (hT : IsSelfAdjoint T) {μ : Measure ℝ}
    (hμ : IsSpectralMeasureH T ψ μ) : μ.real univ = ‖ψ‖ ^ 2 := by
  have := hT.isStarNormal
  have h := hμ.2 (BoundedContinuousFunction.const ℝ 1)
  simp only [BoundedContinuousFunction.const_apply, integral_const, smul_eq_mul, mul_one,
    Complex.ofReal_one] at h
  rw [h, cfc_const_one (R := ℂ) (a := T), one_apply_eq_self]
  exact inner_self_eq_norm_sq ψ

/-- **Total mass**: `μ(ℝ) = ‖ψ‖²`. -/
theorem IsSpectralMeasureH.measure_univ (hT : IsSelfAdjoint T) {μ : Measure ℝ}
    (hμ : IsSpectralMeasureH T ψ μ) : μ univ = ENNReal.ofReal (‖ψ‖ ^ 2) := by
  have := hμ.1
  rw [← hμ.measureReal_univ hT, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

end CMS
