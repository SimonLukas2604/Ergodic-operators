/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators, I*,
§1.11 (pp. 103–107): proof of the Poltoratski–Remling theorem (Theorem 1.11.2).

# Main results

* `DF.ae_tendsto_ratio_rnDeriv` — for `m ⟂ Leb` and any finite `ν`,
  `F_ν / F_m → dν/dm` `m`-almost everywhere;
* `DF.exists_arg_rep` — the Krein representation of `arg F_μ` (cf. Exercise 1.11.4):
  `arg F_μ(E + iε) = ∫ ε / ((x - E)² + ε²) G(x) dx` with `G ≥ 0` the boundary values of
  `arg F_μ / π`;
* `DF.singularPart_lambdaS_compl_eq_zero` — Theorem 1.11.2 for measurable `Σ` of finite
  positive measure;
* `DF.poltoratskiRemlingStatement_holds` — Theorem 1.11.2 (`DF.PoltoratskiRemlingStatement`).

# Proof

We follow A. Poltoratski, C. Remling, *Reflectionless Herglotz functions and Jacobi matrices*
(arXiv:0805.4439), §2.  With `Λ = F_{Leb|Σ}`, the functions `F_± = F_μ e^{± Λ/4}` are Herglotz:
by the Krein representation, `arg F_± = arg F_μ ± Im Λ / 4` is the Poisson integral of
`π (G ± χ_Σ / 4)` and `G = 1/2` on `Σ`, so it takes values in `(0, π)` (this is the choice
`θ = χ_Σ / 2` in the paper).  They decay like `1/y` on the imaginary axis, so `F_± = F_{μ_±}`
for finite measures `μ_±`, and `F_+ F_- = F_μ²`.  By Poltoratski's theorem, for `μ_s`-a.e. `E`,
`F_± / F_{μ_s} → f_±(E) ∈ [0, ∞)` and `F_μ / F_{μ_s} → 1`, so `f_+ f_- = 1`, and
`e^{Λ/2} = F_+ / F_- → f_+ / f_- > 0`.  Hence `Im Λ(E + iε) → 0`, i.e. `E ∈ Λ_s` by
`DF.mem_lambdaS_of_tendsto_im_zero`.
-/
import DamanikFillman.Ch1.PoltoratskiProof
import DamanikFillman.Ch1.BoundaryUniqueness

noncomputable section

open MeasureTheory Filter Topology Set Metric Complex
open scoped ENNReal

namespace DF

/-- If `m` is a finite measure singular with respect to Lebesgue measure and `ν` is any finite
measure, then `F_ν(E + iε) / F_m(E + iε) → (dν/dm)(E)` for `m`-a.e. `E`. -/
theorem ae_tendsto_ratio_rnDeriv (m ν : Measure ℝ) [IsFiniteMeasure m] [IsFiniteMeasure ν]
    (hmL : m ⟂ₘ volume) :
    ∀ᵐ (E : ℝ) ∂m, Tendsto (fun ε : ℝ => borelTransform ν (E + ε * I) / borelTransform m (E + ε * I))
      (𝓝[>] 0) (𝓝 ((ν.rnDeriv m E).toReal : ℂ)) := by
  by_cases hm0 : m = 0
  · subst hm0
    rw [ae_zero]
    exact eventually_bot
  have hfm : Measurable fun x => (ν.rnDeriv m x).toReal :=
    (Measure.measurable_rnDeriv ν m).ennreal_toReal
  have hf : Integrable (fun x => (ν.rnDeriv m x).toReal) m := Measure.integrable_toReal_rnDeriv
  have hP := poltoratski_general m hf
  rw [Measure.singularPart_eq_self.2 hmL] at hP
  have hC := poltoratski_corollary_general m (ν.singularPart m)
    (Measure.mutuallySingular_singularPart ν m).symm hmL
  have hwd : m.withDensity (ν.rnDeriv m) =
      m.withDensity (fun x => ENNReal.ofReal (ν.rnDeriv m x).toReal) := by
    refine withDensity_congr_ae ?_
    filter_upwards [Measure.rnDeriv_lt_top ν m] with x hx
    exact (ENNReal.ofReal_toReal hx.ne).symm
  filter_upwards [hP, hC] with E h1 h2
  have h := h1.add h2
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have hz : 0 < ((E : ℂ) + ε * I).im := by simpa using hε
  have key : borelTransformDensity m (fun x => (ν.rnDeriv m x).toReal) (E + ε * I) +
      borelTransform (ν.singularPart m) (E + ε * I) = borelTransform ν (E + ε * I) := by
    calc borelTransformDensity m (fun x => (ν.rnDeriv m x).toReal) (E + ε * I) +
          borelTransform (ν.singularPart m) (E + ε * I)
        = borelTransform (m.withDensity (ν.rnDeriv m)) (E + ε * I) +
            borelTransform (ν.singularPart m) (E + ε * I) := by
          rw [hwd, borelTransformDensity_eq_withDensity m hfm (fun x => ENNReal.toReal_nonneg)]
      _ = borelTransform (ν.singularPart m + m.withDensity (ν.rnDeriv m)) (E + ε * I) := by
          rw [borelTransform_add _ _ hz.ne', add_comm]
      _ = borelTransform ν (E + ε * I) := by
          rw [← Measure.haveLebesgueDecomposition_add ν m]
  have key' : borelTransformDensity m (fun x => (ν.rnDeriv m x).toReal) (E + ε * I) /
      borelTransform m (E + ε * I) + borelTransform (ν.singularPart m) (E + ε * I) /
        borelTransform m (E + ε * I) =
      borelTransform ν (E + ε * I) / borelTransform m (E + ε * I) := by
    rw [← add_div, key]
  exact key'

/-! ### The Krein representation of `arg F_μ` -/

lemma arg_borelTransform_pos (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : μ ≠ 0) {z : ℂ}
    (hz : 0 < z.im) : 0 < arg (borelTransform μ z) := by
  have h := borelTransform_im_pos μ hμ hz
  rcases (Complex.arg_nonneg_iff.2 h.le).lt_or_eq with h1 | h1
  · exact h1
  · exact absurd (Complex.arg_eq_zero_iff.1 h1.symm).2 h.ne'

lemma arg_borelTransform_lt_pi (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : μ ≠ 0) {z : ℂ}
    (hz : 0 < z.im) : arg (borelTransform μ z) < Real.pi :=
  Complex.arg_lt_pi_iff.2 (Or.inr (borelTransform_im_pos μ hμ hz).ne')

/-- `log F_μ` is a Herglotz function. -/
lemma isHerglotz_log_borelTransform (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : μ ≠ 0) :
    IsHerglotz (fun z => Complex.log (borelTransform μ z)) := by
  refine ⟨(differentiableOn_borelTransform μ).clog fun z hz => ?_, fun z hz => ?_⟩
  · exact Complex.mem_slitPlane_iff.2 (Or.inr (borelTransform_im_pos μ hμ hz).ne')
  · rw [Complex.log_im]
    exact arg_borelTransform_pos μ hμ hz

lemma normSq_ofReal_sub_add_mul_I (x E ε : ℝ) :
    Complex.normSq ((x : ℂ) - (E + ε * I)) = (x - E) ^ 2 + ε ^ 2 := by
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, Complex.sub_im, Complex.add_im, Complex.mul_im]
  ring

lemma im_ofReal_add_mul_I (E ε : ℝ) : ((E : ℂ) + ε * I).im = ε := by simp

/-- The Herglotz function `a + ∫ (1 + x z)/(x - z) dρ(x)` in terms of `F_ρ`. -/
lemma im_herglotzRho_zero (a : ℝ) (ρ : Measure ℝ) [IsFiniteMeasure ρ] (E : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    (herglotzRho a 0 ρ (E + ε * I)).im = ρ.real univ * ε +
      (1 + E ^ 2) * (borelTransform ρ (E + ε * I)).im +
        ((((2 * E : ℝ) : ℂ) * I - ε) * (ε * borelTransform ρ (E + ε * I))).im := by
  have hz : 0 < ((E : ℂ) + ε * I).im := by simpa using hε
  unfold herglotzRho
  rw [integral_herglotz_kernel_eq ρ hz]
  simp only [Complex.add_im, Complex.add_re, Complex.mul_im, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im, sq,
    Complex.sub_re, Complex.sub_im]
  ring

/-- **Krein representation of `arg F_μ`** (cf. Exercise 1.11.4): there is a measurable `G ≥ 0`
with `arg F_μ(E + iε) = ∫ ε / ((x - E)² + ε²) G(x) dx`, and `arg F_μ(E + iε) → π G(E)` for
Lebesgue-a.e. `E`. -/
theorem exists_arg_rep (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : μ ≠ 0) :
    ∃ G : ℝ → ℝ, Measurable G ∧ (∀ x, 0 ≤ G x) ∧
      (∀ (E ε : ℝ), 0 < ε → arg (borelTransform μ (E + ε * I)) =
        ∫ x, ε / ((x - E) ^ 2 + ε ^ 2) * G x) ∧
      ∀ᵐ (E : ℝ), Tendsto (fun ε : ℝ => arg (borelTransform μ (E + ε * I))) (𝓝[>] 0)
        (𝓝 (Real.pi * G E)) := by
  obtain ⟨a, b, ρ, hρ, hb, -, hrep⟩ := exists_herglotzRho _ (isHerglotz_log_borelTransform μ hμ)
  have harg : ∀ z : ℂ, 0 < z.im → arg (borelTransform μ z) =
      b * z.im + ∫ x, (1 + x ^ 2) * z.im / Complex.normSq (x - z) ∂ρ := by
    intro z hz
    rw [← Complex.log_im,
      show Complex.log (borelTransform μ z) = herglotzRho a b ρ z from hrep z hz,
      im_herglotzRho a b ρ hz]
  have hKint : ∀ z : ℂ, 0 < z.im →
      Integrable (fun x : ℝ => (1 + x ^ 2) * z.im / Complex.normSq (x - z)) ρ := by
    intro z hz
    have h := (integrable_herglotz_kernel_rho ρ hz).im
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only [RCLike.im_to_complex]
    exact im_herglotz_kernel x z
  have hKnn : ∀ z : ℂ, 0 < z.im → 0 ≤ ∫ x, (1 + x ^ 2) * z.im / Complex.normSq (x - z) ∂ρ :=
    fun z hz => integral_nonneg fun x =>
      div_nonneg (mul_nonneg (by positivity) hz.le) (Complex.normSq_nonneg _)
  -- `b = 0` since `arg F_μ ≤ π`
  have hb0 : b = 0 := by
    by_contra hne
    have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hne)
    set y : ℝ := (Real.pi + 1) / b with hy_def
    have hyim : ((y : ℂ) * I).im = y := by simp
    have hy : 0 < ((y : ℂ) * I).im := by rw [hyim]; exact div_pos (by positivity) hbpos
    have h1 := harg _ hy
    have h2 := hKnn _ hy
    have h3 := Complex.arg_le_pi (borelTransform μ ((y : ℂ) * I))
    have h4 : b * ((y : ℂ) * I).im = Real.pi + 1 := by
      rw [hyim, hy_def]
      field_simp
    linarith
  -- `Im F_ρ ≤ π`, so `ρ` has no singular part
  have hFρle : ∀ (E ε : ℝ), 0 < ε → (borelTransform ρ (E + ε * I)).im ≤ Real.pi := by
    intro E ε hε
    have hz : 0 < ((E : ℂ) + ε * I).im := by simpa using hε
    have h1 := harg _ hz
    rw [hb0, zero_mul, zero_add] at h1
    have h2 := Complex.arg_le_pi (borelTransform μ (E + ε * I))
    rw [h1] at h2
    rw [borelTransform_im ρ E hε.ne']
    refine le_trans ?_ h2
    refine integral_mono_of_nonneg
      (Eventually.of_forall fun x => div_nonneg hε.le (by positivity)) (hKint _ hz)
      (Eventually.of_forall fun x => ?_)
    show ε / ((x - E) ^ 2 + ε ^ 2) ≤
      (1 + x ^ 2) * ((E : ℂ) + ε * I).im / Complex.normSq ((x : ℂ) - (E + ε * I))
    rw [normSq_ofReal_sub_add_mul_I, im_ofReal_add_mul_I]
    gcongr
    nlinarith [mul_nonneg (sq_nonneg x) hε.le]
  have hρs : ρ.singularPart volume = 0 := by
    have h := singularPart_not_tendsto_atTop ρ
    have hall : {E : ℝ | ¬ Tendsto (fun ε : ℝ => (borelTransform ρ (E + ε * I)).im) (𝓝[>] 0)
        atTop} = univ := by
      refine eq_univ_of_forall fun E => ?_
      simp only [mem_setOf_eq]
      intro hT
      obtain ⟨ε, h1, h2⟩ :=
        ((hT.eventually (eventually_gt_atTop Real.pi)).and self_mem_nhdsWithin).exists
      exact absurd (hFρle E ε h2) (not_le.2 h1)
    rw [hall] at h
    exact Measure.measure_univ_eq_zero.1 h
  have hρeq : ρ = volume.withDensity (ρ.rnDeriv volume) := by
    conv_lhs => rw [Measure.haveLebesgueDecomposition_add ρ volume]
    rw [hρs, zero_add]
  have hρac : ρ ≪ volume := by
    rw [hρeq]
    exact withDensity_absolutelyContinuous _ _
  -- the representation
  have hrepG : ∀ (E ε : ℝ), 0 < ε → arg (borelTransform μ (E + ε * I)) =
      ∫ x, ε / ((x - E) ^ 2 + ε ^ 2) * ((1 + x ^ 2) * (ρ.rnDeriv volume x).toReal) := by
    intro E ε hε
    have hz : 0 < ((E : ℂ) + ε * I).im := by simpa using hε
    rw [harg _ hz, hb0, zero_mul, zero_add]
    conv_lhs => rw [hρeq]
    rw [integral_withDensity_eq_integral_toReal_smul (Measure.measurable_rnDeriv _ _)
      (Measure.rnDeriv_lt_top ρ volume)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    show (ρ.rnDeriv volume x).toReal •
        ((1 + x ^ 2) * ((E : ℂ) + ε * I).im / Complex.normSq ((x : ℂ) - (E + ε * I))) =
      ε / ((x - E) ^ 2 + ε ^ 2) * ((1 + x ^ 2) * (ρ.rnDeriv volume x).toReal)
    rw [smul_eq_mul, normSq_ofReal_sub_add_mul_I, im_ofReal_add_mul_I]
    ring
  -- boundary values
  have hlim : ∀ᵐ (E : ℝ), Tendsto (fun ε : ℝ => arg (borelTransform μ (E + ε * I))) (𝓝[>] 0)
      (𝓝 (Real.pi * ((1 + E ^ 2) * (ρ.rnDeriv volume E).toReal))) := by
    filter_upwards [ae_tendsto_im_volume ρ] with E hE
    have hε0 : Tendsto (fun ε : ℝ => (ε : ℂ) * borelTransform ρ (E + ε * I)) (𝓝[>] 0)
        (𝓝 0) := by
      have h := tendsto_eps_mul_borelTransformDensity ρ (f := fun _ => (1 : ℝ))
        (integrable_const 1) E
      simp only [borelTransformDensity_one] at h
      have hsing : ρ.real {E} = 0 := by
        rw [Measure.real, hρac (Real.volume_singleton), ENNReal.toReal_zero]
      rwa [hsing, Complex.ofReal_zero, mul_zero] at h
    have h1 : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have h2 : Tendsto (fun ε : ℝ => (((2 * E : ℝ) : ℂ) * I - (ε : ℂ)) *
        ((ε : ℂ) * borelTransform ρ (E + ε * I))) (𝓝[>] 0)
        (𝓝 ((((2 * E : ℝ) : ℂ) * I - ((0 : ℝ) : ℂ)) * 0)) :=
      (tendsto_const_nhds.sub ((Complex.continuous_ofReal.tendsto 0).comp h1)).mul hε0
    have h3 := (Complex.continuous_im.tendsto _).comp h2
    have h4 := (((tendsto_const_nhds (x := ρ.real univ)).mul h1).add
      ((tendsto_const_nhds (x := 1 + E ^ 2)).mul hE)).add h3
    have h5 : Tendsto (fun ε : ℝ => arg (borelTransform μ (E + ε * I))) (𝓝[>] 0)
        (𝓝 (ρ.real univ * 0 + (1 + E ^ 2) * (Real.pi * (ρ.rnDeriv volume E).toReal) +
          Complex.im ((((2 * E : ℝ) : ℂ) * I - ((0 : ℝ) : ℂ)) * 0))) := by
      refine h4.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      have hz : 0 < ((E : ℂ) + ε * I).im := by simpa using hε
      have key : arg (borelTransform μ (E + ε * I)) = ρ.real univ * ε +
          (1 + E ^ 2) * (borelTransform ρ (E + ε * I)).im +
            ((((2 * E : ℝ) : ℂ) * I - ε) * (ε * borelTransform ρ (E + ε * I))).im := by
        rw [← Complex.log_im,
          show Complex.log (borelTransform μ (E + ε * I)) = herglotzRho a b ρ (E + ε * I) from
            hrep _ hz, hb0, im_herglotzRho_zero a ρ E hε]
      exact key.symm
    convert h5 using 2
    simp only [mul_zero, Complex.zero_im, zero_add, add_zero]
    ring
  refine ⟨fun x => (1 + x ^ 2) * (ρ.rnDeriv volume x).toReal,
    Measurable.mul (by fun_prop) (Measure.measurable_rnDeriv _ _).ennreal_toReal,
    fun x => mul_nonneg (by positivity) ENNReal.toReal_nonneg, hrepG, hlim⟩

/-- For a measure reflectionless on `Σ`, the density `G` of the Krein representation satisfies
`G ≤ 1` a.e. and `G = 1/2` a.e. on `Σ`. -/
lemma arg_rep_bounds (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : μ ≠ 0) {S : Set ℝ}
    (hSm : MeasurableSet S) (hrefl : IsReflectionless μ S) {G : ℝ → ℝ}
    (hlim : ∀ᵐ (E : ℝ), Tendsto (fun ε : ℝ => arg (borelTransform μ (E + ε * I))) (𝓝[>] 0)
      (𝓝 (Real.pi * G E))) :
    (∀ᵐ x, G x ≤ 1) ∧ ∀ᵐ x, x ∈ S → G x = 1 / 2 := by
  constructor
  · filter_upwards [hlim] with E hE
    have h := le_of_tendsto hE (Eventually.of_forall fun ε => Complex.arg_le_pi _)
    have hpi := Real.pi_pos
    nlinarith
  -- `μ_ac > 0` a.e. on `Σ`
  have hQ : volume (S ∩ {x | μ.rnDeriv volume x = 0}) = 0 := by
    by_contra hne
    have h := acPart_pos_of_reflectionless' μ hμ hSm hrefl inter_subset_left
      (pos_iff_ne_zero.2 hne)
    have h0 : volume.withDensity (μ.rnDeriv volume) (S ∩ {x | μ.rnDeriv volume x = 0}) = 0 := by
      rw [withDensity_apply_eq_zero' (Measure.measurable_rnDeriv μ volume).aemeasurable]
      refine measure_mono_null (fun x hx => ?_) measure_empty
      exact hx.1 hx.2.2
    rw [h0] at h
    exact lt_irrefl _ h
  have hpos : ∀ᵐ (E : ℝ), E ∈ S → μ.rnDeriv volume E ≠ 0 := by
    rw [ae_iff]
    refine measure_mono_null (fun E hE => ?_) hQ
    simp only [mem_setOf_eq, not_imp, not_not] at hE
    exact ⟨hE.1, hE.2⟩
  filter_upwards [hlim, (ae_restrict_iff' hSm).1 hrefl, hpos, ae_tendsto_im_volume μ,
    Measure.rnDeriv_lt_top μ volume] with E hE hre hne him hlt hES
  have hc : 0 < Real.pi * (μ.rnDeriv volume E).toReal :=
    mul_pos Real.pi_pos (ENNReal.toReal_pos (hne hES) hlt.ne)
  have hF : Tendsto (fun ε : ℝ => borelTransform μ (E + ε * I)) (𝓝[>] 0)
      (𝓝 (((Real.pi * (μ.rnDeriv volume E).toReal : ℝ) : ℂ) * I)) := by
    have := ((Complex.continuous_ofReal.tendsto _).comp (hre hES)).add
      (((Complex.continuous_ofReal.tendsto _).comp him).mul_const I)
    simp only [Complex.ofReal_zero, zero_add] at this
    refine this.congr fun ε => ?_
    simp only [Function.comp_apply]
    exact Complex.re_add_im _
  have hslit : (((Real.pi * (μ.rnDeriv volume E).toReal : ℝ) : ℂ) * I) ∈ slitPlane :=
    Complex.mem_slitPlane_iff.2 (Or.inr (by simpa using hc.ne'))
  have harg := ((Complex.continuousAt_arg hslit).tendsto).comp hF
  rw [Complex.arg_real_mul I hc, Complex.arg_I] at harg
  have h := tendsto_nhds_unique hE harg
  have h' : Real.pi * (2 * G E - 1) = 0 := by linarith
  rcases mul_eq_zero.1 h' with h0 | h0
  · exact absurd h0 Real.pi_ne_zero
  · linarith

/-! ### The functions `F_± = F_μ e^{± Λ/4}` -/

lemma integrable_cauchyKernel {ε : ℝ} (hε : 0 < ε) (E : ℝ) :
    Integrable (fun x : ℝ => ε / ((x - E) ^ 2 + ε ^ 2)) := by
  refine ((integrable_poissonKernel_volume hε E).const_mul Real.pi).congr
    (Eventually.of_forall fun x => ?_)
  have hd : (x - E) ^ 2 + ε ^ 2 ≠ 0 := (add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hε 2)).ne'
  simp only [poissonKernel]
  field_simp

lemma integral_cauchyKernel {ε : ℝ} (hε : 0 < ε) (E : ℝ) :
    ∫ x : ℝ, ε / ((x - E) ^ 2 + ε ^ 2) = Real.pi := by
  calc ∫ x : ℝ, ε / ((x - E) ^ 2 + ε ^ 2) = ∫ x : ℝ, Real.pi * poissonKernel ε (x - E) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        have hd : (x - E) ^ 2 + ε ^ 2 ≠ 0 :=
          (add_pos_of_nonneg_of_pos (sq_nonneg _) (pow_pos hε 2)).ne'
        show ε / ((x - E) ^ 2 + ε ^ 2) = Real.pi * poissonKernel ε (x - E)
        simp only [poissonKernel]
        field_simp
    _ = Real.pi := by rw [integral_const_mul, integral_poissonKernel hε E, mul_one]

/-- The key inequalities: `Im Λ / 2 ≤ arg F_μ ≤ π - Im Λ / 2`. -/
lemma half_im_lambda_le (μ : Measure ℝ) [IsFiniteMeasure μ] {S : Set ℝ} (hSm : MeasurableSet S)
    (hS : volume S < ∞) {G : ℝ → ℝ} (hGm : Measurable G) (hGnn : ∀ x, 0 ≤ G x)
    (hG1 : ∀ᵐ x, G x ≤ 1) (hGS : ∀ᵐ x, x ∈ S → G x = 1 / 2)
    (hrep : ∀ (E ε : ℝ), 0 < ε → arg (borelTransform μ (E + ε * I)) =
      ∫ x, ε / ((x - E) ^ 2 + ε ^ 2) * G x)
    (E : ℝ) {ε : ℝ} (hε : 0 < ε) :
    (borelTransform (volume.restrict S) (E + ε * I)).im / 2 ≤ arg (borelTransform μ (E + ε * I)) ∧
    (borelTransform (volume.restrict S) (E + ε * I)).im / 2 ≤
      Real.pi - arg (borelTransform μ (E + ε * I)) := by
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hS.ne
  have hk := integrable_cauchyKernel hε E
  have hk0 : ∀ x : ℝ, 0 ≤ ε / ((x - E) ^ 2 + ε ^ 2) := fun x => div_nonneg hε.le (by positivity)
  have hkG : Integrable (fun x => ε / ((x - E) ^ 2 + ε ^ 2) * G x) :=
    hk.mul_bdd hGm.aestronglyMeasurable (by
      filter_upwards [hG1] with x hx
      rw [Real.norm_of_nonneg (hGnn x)]
      exact hx)
  have hkG' : Integrable (fun x => ε / ((x - E) ^ 2 + ε ^ 2) * (1 - G x)) := by
    refine (hk.sub hkG).congr (Eventually.of_forall fun x => ?_)
    simp only [Pi.sub_apply]
    ring
  have hS1 : ∫ x in S, ε / ((x - E) ^ 2 + ε ^ 2) * G x =
      ∫ x in S, ε / ((x - E) ^ 2 + ε ^ 2) * (1 / 2) :=
    setIntegral_congr_ae hSm (by filter_upwards [hGS] with x hx hxS; rw [hx hxS])
  have hS2 : ∫ x in S, ε / ((x - E) ^ 2 + ε ^ 2) * (1 - G x) =
      ∫ x in S, ε / ((x - E) ^ 2 + ε ^ 2) * (1 / 2) :=
    setIntegral_congr_ae hSm (by filter_upwards [hGS] with x hx hxS; rw [hx hxS]; norm_num)
  rw [integral_mul_const] at hS1 hS2
  rw [borelTransform_im _ E hε.ne', hrep E ε hε]
  constructor
  · calc (∫ x in S, ε / ((x - E) ^ 2 + ε ^ 2)) / 2
        = ∫ x in S, ε / ((x - E) ^ 2 + ε ^ 2) * G x := by rw [hS1]; ring
      _ ≤ ∫ x, ε / ((x - E) ^ 2 + ε ^ 2) * G x :=
        setIntegral_le_integral hkG (Eventually.of_forall fun x => mul_nonneg (hk0 x) (hGnn x))
  · have hpi : Real.pi - ∫ x, ε / ((x - E) ^ 2 + ε ^ 2) * G x =
        ∫ x, ε / ((x - E) ^ 2 + ε ^ 2) * (1 - G x) := by
      rw [← integral_cauchyKernel hε E, ← integral_sub hk hkG]
      congr 1
      ext x
      ring
    rw [hpi]
    calc (∫ x in S, ε / ((x - E) ^ 2 + ε ^ 2)) / 2
        = ∫ x in S, ε / ((x - E) ^ 2 + ε ^ 2) * (1 - G x) := by rw [hS2]; ring
      _ ≤ ∫ x, ε / ((x - E) ^ 2 + ε ^ 2) * (1 - G x) :=
        setIntegral_le_integral hkG' (by
          filter_upwards [hG1] with x hx
          exact mul_nonneg (hk0 x) (by linarith))

/-- `F_s = F_μ e^{s Λ}` with `Λ = F_{Leb|Σ}`. -/
def prF (μ : Measure ℝ) (S : Set ℝ) (s : ℝ) (z : ℂ) : ℂ :=
  borelTransform μ z * Complex.exp ((s : ℂ) * borelTransform (volume.restrict S) z)

lemma im_prF_pos (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : μ ≠ 0) {S : Set ℝ}
    (hS : volume S < ∞) (hS0 : 0 < volume S)
    (hI : ∀ (E ε : ℝ), 0 < ε →
      (borelTransform (volume.restrict S) (E + ε * I)).im / 2 ≤
          arg (borelTransform μ (E + ε * I)) ∧
        (borelTransform (volume.restrict S) (E + ε * I)).im / 2 ≤
          Real.pi - arg (borelTransform μ (E + ε * I)))
    {s : ℝ} (hs : |s| ≤ 1 / 4) (E : ℝ) {ε : ℝ} (hε : 0 < ε) :
    0 < (prF μ S s (E + ε * I)).im := by
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hS.ne
  have hS' : volume.restrict S ≠ 0 := fun h => hS0.ne' (Measure.restrict_eq_zero.1 h)
  have hz : 0 < ((E : ℂ) + ε * I).im := by simpa using hε
  have hF0 := borelTransform_ne_zero μ hμ hz
  have hL := borelTransform_im_pos (volume.restrict S) hS' hz
  obtain ⟨h1, h2⟩ := hI E ε hε
  have ha := arg_borelTransform_pos μ hμ hz
  have hb := arg_borelTransform_lt_pi μ hμ hz
  obtain ⟨hs1, hs2⟩ := abs_le.1 hs
  have hm1 : 0 ≤ (s + 1 / 4) * (borelTransform (volume.restrict S) (E + ε * I)).im :=
    mul_nonneg (by linarith) hL.le
  have hm2 : 0 ≤ (1 / 4 - s) * (borelTransform (volume.restrict S) (E + ε * I)).im :=
    mul_nonneg (by linarith) hL.le
  have hlo : 0 < arg (borelTransform μ (E + ε * I)) +
      s * (borelTransform (volume.restrict S) (E + ε * I)).im := by nlinarith
  have hhi : arg (borelTransform μ (E + ε * I)) +
      s * (borelTransform (volume.restrict S) (E + ε * I)).im < Real.pi := by nlinarith
  have him : (Complex.log (borelTransform μ (E + ε * I)) +
      (s : ℂ) * borelTransform (volume.restrict S) (E + ε * I)).im =
      arg (borelTransform μ (E + ε * I)) +
        s * (borelTransform (volume.restrict S) (E + ε * I)).im := by
    rw [Complex.add_im, Complex.log_im, Complex.im_ofReal_mul]
  unfold prF
  rw [← Complex.exp_log hF0, ← Complex.exp_add, Complex.exp_im, him]
  exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi hlo hhi)

lemma isHerglotz_prF (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : μ ≠ 0) {S : Set ℝ}
    (hS : volume S < ∞) (hS0 : 0 < volume S)
    (hI : ∀ (E ε : ℝ), 0 < ε →
      (borelTransform (volume.restrict S) (E + ε * I)).im / 2 ≤
          arg (borelTransform μ (E + ε * I)) ∧
        (borelTransform (volume.restrict S) (E + ε * I)).im / 2 ≤
          Real.pi - arg (borelTransform μ (E + ε * I)))
    {s : ℝ} (hs : |s| ≤ 1 / 4) : IsHerglotz (prF μ S s) := by
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hS.ne
  constructor
  · show DifferentiableOn ℂ (fun z => borelTransform μ z *
      Complex.exp ((s : ℂ) * borelTransform (volume.restrict S) z)) {z | 0 < z.im}
    exact (differentiableOn_borelTransform μ).mul
      ((differentiableOn_const (s : ℂ)).mul
        (differentiableOn_borelTransform (volume.restrict S))).cexp
  · intro z hz
    rw [eq_re_add_im_mul_I z]
    exact im_prF_pos μ hμ hS hS0 hI hs z.re hz

lemma norm_prF_le (μ : Measure ℝ) [IsFiniteMeasure μ] {S : Set ℝ} (hS : volume S < ∞) {s : ℝ}
    (hs : |s| ≤ 1 / 4) {y : ℝ} (hy : 1 ≤ y) :
    ‖prF μ S s (y * I)‖ ≤ (μ.real univ * Real.exp ((volume.restrict S).real univ)) / y := by
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hS.ne
  have hy0 : 0 < y := by linarith
  have hz : 0 < ((y : ℂ) * I).im := by simpa using hy0
  have hyim : ((y : ℂ) * I).im = y := by simp
  have h1 := norm_borelTransform_le μ hz
  have h2 := norm_borelTransform_le (volume.restrict S) hz
  rw [hyim] at h1 h2
  have hre := Complex.abs_re_le_norm (borelTransform (volume.restrict S) (y * I))
  have h3 : s * (borelTransform (volume.restrict S) (y * I)).re ≤
      (volume.restrict S).real univ :=
    calc s * (borelTransform (volume.restrict S) (y * I)).re
        ≤ |s * (borelTransform (volume.restrict S) (y * I)).re| := le_abs_self _
      _ = |s| * |(borelTransform (volume.restrict S) (y * I)).re| := abs_mul _ _
      _ ≤ 1 * ‖borelTransform (volume.restrict S) (y * I)‖ :=
          mul_le_mul (hs.trans (by norm_num)) hre (abs_nonneg _) zero_le_one
      _ ≤ (volume.restrict S).real univ / y := by rw [one_mul]; exact h2
      _ ≤ (volume.restrict S).real univ := div_le_self measureReal_nonneg hy
  unfold prF
  rw [norm_mul, Complex.norm_exp, Complex.re_ofReal_mul]
  calc ‖borelTransform μ (y * I)‖ *
        Real.exp (s * (borelTransform (volume.restrict S) (y * I)).re)
      ≤ (μ.real univ / y) * Real.exp ((volume.restrict S).real univ) :=
        mul_le_mul h1 (Real.exp_le_exp.2 h3) (Real.exp_pos _).le
          (div_nonneg measureReal_nonneg hy0.le)
    _ = (μ.real univ * Real.exp ((volume.restrict S).real univ)) / y := by ring

/-! ### Proof of Theorem 1.11.2 -/

/-- **Theorem 1.11.2** for a measurable `Σ` of finite positive Lebesgue measure. -/
theorem singularPart_lambdaS_compl_eq_zero (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : μ ≠ 0)
    {S : Set ℝ} (hSm : MeasurableSet S) (hS : volume S < ∞) (hS0 : 0 < volume S)
    (hrefl : IsReflectionless μ S) :
    μ.singularPart volume (lambdaS S)ᶜ = 0 := by
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hS.ne
  have hS' : volume.restrict S ≠ 0 := fun h => hS0.ne' (Measure.restrict_eq_zero.1 h)
  obtain ⟨G, hGm, hGnn, hrep, hlim⟩ := exists_arg_rep μ hμ
  obtain ⟨hG1, hGS⟩ := arg_rep_bounds μ hμ hSm hrefl hlim
  have hI : ∀ (E ε : ℝ), 0 < ε →
      (borelTransform (volume.restrict S) (E + ε * I)).im / 2 ≤
          arg (borelTransform μ (E + ε * I)) ∧
        (borelTransform (volume.restrict S) (E + ε * I)).im / 2 ≤
          Real.pi - arg (borelTransform μ (E + ε * I)) :=
    fun E ε hε => half_im_lambda_le μ hSm hS hGm hGnn hG1 hGS hrep E hε
  have hsp : |(1 / 4 : ℝ)| ≤ 1 / 4 := by rw [abs_le]; constructor <;> norm_num
  have hsm : |(-1 / 4 : ℝ)| ≤ 1 / 4 := by rw [abs_le]; constructor <;> norm_num
  obtain ⟨μp, hμp, hFp⟩ := exists_measure_of_isHerglotz (isHerglotz_prF μ hμ hS hS0 hI hsp)
    (fun y hy _ => norm_prF_le μ hS hsp hy)
  obtain ⟨μm, hμm, hFm⟩ := exists_measure_of_isHerglotz (isHerglotz_prF μ hμ hS hS0 hI hsm)
    (fun y hy _ => norm_prF_le μ hS hsm hy)
  by_cases hm0 : μ.singularPart volume = 0
  · rw [hm0]; simp
  have hmL : μ.singularPart volume ⟂ₘ volume := Measure.mutuallySingular_singularPart μ volume
  have hP := ae_tendsto_ratio_rnDeriv (μ.singularPart volume) μp hmL
  have hM := ae_tendsto_ratio_rnDeriv (μ.singularPart volume) μm hmL
  have hac := poltoratski_corollary_general (μ.singularPart volume)
    (volume.withDensity (μ.rnDeriv volume))
    (hmL.mono_ac Measure.AbsolutelyContinuous.rfl (withDensity_absolutelyContinuous _ _)) hmL
  have hmain : ∀ᵐ (E : ℝ) ∂(μ.singularPart volume), E ∈ lambdaS S := by
    filter_upwards [hP, hM, hac] with E hEp hEm hEac
    obtain ⟨a, ha⟩ : ∃ a : ℝ, a = (μp.rnDeriv (μ.singularPart volume) E).toReal := ⟨_, rfl⟩
    obtain ⟨b, hb⟩ : ∃ b : ℝ, b = (μm.rnDeriv (μ.singularPart volume) E).toReal := ⟨_, rfl⟩
    rw [← ha] at hEp
    rw [← hb] at hEm
    have ha0 : 0 ≤ a := by rw [ha]; exact ENNReal.toReal_nonneg
    have hb0 : 0 ≤ b := by rw [hb]; exact ENNReal.toReal_nonneg
    -- `F_μ / F_{μ_s} → 1`
    have hq : Tendsto (fun ε : ℝ => borelTransform μ (E + ε * I) /
        borelTransform (μ.singularPart volume) (E + ε * I)) (𝓝[>] 0) (𝓝 1) := by
      have h := (tendsto_const_nhds (x := (1 : ℂ))).add hEac
      rw [add_zero] at h
      refine h.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      have hz : 0 < ((E : ℂ) + ε * I).im := by simpa using hε
      have hFm0 := borelTransform_ne_zero (μ.singularPart volume) hm0 hz
      have hsplit : borelTransform μ (E + ε * I) =
          borelTransform (μ.singularPart volume) (E + ε * I) +
            borelTransform (volume.withDensity (μ.rnDeriv volume)) (E + ε * I) := by
        rw [← borelTransform_add _ _ hz.ne', ← Measure.haveLebesgueDecomposition_add μ volume]
      have key : 1 + borelTransform (volume.withDensity (μ.rnDeriv volume)) (E + ε * I) /
          borelTransform (μ.singularPart volume) (E + ε * I) =
          borelTransform μ (E + ε * I) / borelTransform (μ.singularPart volume) (E + ε * I) := by
        rw [hsplit, add_div, div_self hFm0]
      exact key
    -- `F_+ F_- = F_μ²`, so `a b = 1`
    have hab : ((a : ℂ) * b) = 1 * 1 := by
      refine tendsto_nhds_unique_of_eventuallyEq (hEp.mul hEm) (hq.mul hq) ?_
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      have hz : 0 < ((E : ℂ) + ε * I).im := by simpa using hε
      have he : Complex.exp (((1 / 4 : ℝ) : ℂ) * borelTransform (volume.restrict S) (E + ε * I)) *
          Complex.exp (((-1 / 4 : ℝ) : ℂ) * borelTransform (volume.restrict S) (E + ε * I)) = 1 := by
        rw [← Complex.exp_add, ← Complex.exp_zero]
        congr 1
        push_cast
        ring
      have key : borelTransform μp (E + ε * I) / borelTransform (μ.singularPart volume) (E + ε * I) *
          (borelTransform μm (E + ε * I) / borelTransform (μ.singularPart volume) (E + ε * I)) =
          borelTransform μ (E + ε * I) / borelTransform (μ.singularPart volume) (E + ε * I) *
            (borelTransform μ (E + ε * I) / borelTransform (μ.singularPart volume) (E + ε * I)) := by
        rw [← hFp _ hz, ← hFm _ hz]
        unfold prF
        calc borelTransform μ (E + ε * I) *
                Complex.exp (((1 / 4 : ℝ) : ℂ) * borelTransform (volume.restrict S) (E + ε * I)) /
                borelTransform (μ.singularPart volume) (E + ε * I) *
              (borelTransform μ (E + ε * I) *
                Complex.exp (((-1 / 4 : ℝ) : ℂ) * borelTransform (volume.restrict S) (E + ε * I)) /
                borelTransform (μ.singularPart volume) (E + ε * I))
            = borelTransform μ (E + ε * I) / borelTransform (μ.singularPart volume) (E + ε * I) *
                (borelTransform μ (E + ε * I) /
                  borelTransform (μ.singularPart volume) (E + ε * I)) *
                (Complex.exp (((1 / 4 : ℝ) : ℂ) *
                    borelTransform (volume.restrict S) (E + ε * I)) *
                  Complex.exp (((-1 / 4 : ℝ) : ℂ) *
                    borelTransform (volume.restrict S) (E + ε * I))) := by ring
          _ = _ := by rw [he, mul_one]
      exact key
    have hab' : a * b = 1 := by
      rw [one_mul] at hab
      exact_mod_cast hab
    have hapos : 0 < a := lt_of_le_of_ne ha0 (by rintro rfl; simp at hab')
    have hbpos : 0 < b := lt_of_le_of_ne hb0 (by rintro rfl; simp at hab')
    have hbne : (b : ℂ) ≠ 0 := by exact_mod_cast hbpos.ne'
    -- `F_+ / F_- = e^{Λ/2}` converges to `a / b > 0`
    have hratio := hEp.div hEm hbne
    have hslit : (a : ℂ) / b ∈ slitPlane := by
      rw [← Complex.ofReal_div]
      exact Complex.mem_slitPlane_iff.2 (Or.inl (by rw [Complex.ofReal_re]; exact div_pos hapos hbpos))
    have harg := ((Complex.continuousAt_arg hslit).tendsto).comp hratio
    have harg0 : arg ((a : ℂ) / b) = 0 := by
      rw [← Complex.ofReal_div]
      exact Complex.arg_ofReal_of_nonneg (div_pos hapos hbpos).le
    rw [harg0] at harg
    have hargeq : ∀ᶠ (ε : ℝ) in 𝓝[>] (0 : ℝ),
        arg (borelTransform μp (E + ε * I) / borelTransform (μ.singularPart volume) (E + ε * I) /
          (borelTransform μm (E + ε * I) / borelTransform (μ.singularPart volume) (E + ε * I))) =
        (borelTransform (volume.restrict S) (E + ε * I)).im / 2 := by
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      have hz : 0 < ((E : ℂ) + ε * I).im := by simpa using hε
      have hFm0 := borelTransform_ne_zero (μ.singularPart volume) hm0 hz
      have hF0 := borelTransform_ne_zero μ hμ hz
      have hL := borelTransform_im_pos (volume.restrict S) hS' hz
      have hI1 := (hI E ε hε).1
      have hpi := Complex.arg_le_pi (borelTransform μ (E + ε * I))
      have hq' : prF μ S (1 / 4) (E + ε * I) / prF μ S (-1 / 4) (E + ε * I) =
          Complex.exp (((1 / 2 : ℝ) : ℂ) * borelTransform (volume.restrict S) (E + ε * I)) := by
        unfold prF
        rw [mul_div_mul_left _ _ hF0, ← Complex.exp_sub]
        congr 1
        push_cast
        ring
      rw [← hFp _ hz, ← hFm _ hz, div_div_div_cancel_right₀ hFm0, hq', ← Complex.log_im,
        Complex.log_exp, Complex.im_ofReal_mul]
      · ring
      · rw [Complex.im_ofReal_mul]; linarith [Real.pi_pos]
      · rw [Complex.im_ofReal_mul]; linarith
    have h3 := (harg.congr' hargeq).mul_const 2
    rw [zero_mul] at h3
    exact mem_lambdaS_of_tendsto_im_zero hS (h3.congr fun ε => by ring)
  exact ae_iff.1 hmain

/-- If `Σ ∩ (E - δ, E + δ) ⊆ T` for small `δ` and `E ∈ Λ_s(T)`, then `E ∈ Λ_s(Σ)`. -/
lemma mem_lambdaS_of_eventually_subset {S T : Set ℝ} {E : ℝ}
    (h : ∀ᶠ δ in 𝓝[>] (0 : ℝ), S ∩ ball E δ ⊆ T) (hT : E ∈ lambdaS T) : E ∈ lambdaS S := by
  simp only [lambdaS, mem_setOf_eq] at hT ⊢
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hT
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [h] with δ hδ
  exact ENNReal.div_le_div_right
    (measure_mono (fun x hx => ⟨hδ hx, hx.2⟩ : S ∩ ball E δ ⊆ T ∩ ball E δ)) _

/-- **Theorem 1.11.2** (Poltoratski–Remling). -/
theorem poltoratskiRemlingStatement_holds : PoltoratskiRemlingStatement := by
  intro μ _ hRc S hrefl
  obtain ⟨R, hR⟩ := hRc
  by_cases hμ : μ = 0
  · subst hμ
    simp
  set R' : ℝ := |R| + 1 with hR'
  set S' := toMeasurable volume (S ∩ Icc (-R') R') with hS'def
  have hfin : volume (S ∩ Icc (-R') R') ≠ ∞ :=
    ((measure_mono inter_subset_right).trans_lt measure_Icc_lt_top).ne
  have hS'm : MeasurableSet S' := measurableSet_toMeasurable _ _
  have hS'fin : volume S' < ∞ := by
    rw [hS'def, measure_toMeasurable]
    exact lt_top_iff_ne_top.2 hfin
  have hrefl' : IsReflectionless μ S' := by
    unfold IsReflectionless
    rw [hS'def, Measure.restrict_toMeasurable hfin]
    exact ae_restrict_of_ae_restrict_of_subset inter_subset_left hrefl
  have hmain : μ.singularPart volume (lambdaS S')ᶜ = 0 := by
    by_cases h0 : volume S' = 0
    · have huniv : lambdaS S' = univ := eq_univ_of_forall fun E => by
        have hz : ∀ δ : ℝ, volume (S' ∩ ball E δ) = 0 := fun δ =>
          measure_mono_null inter_subset_left h0
        show Tendsto (fun δ : ℝ => volume (S' ∩ ball E δ) / ENNReal.ofReal (2 * δ)) (𝓝[>] 0)
          (𝓝 0)
        simp only [hz, ENNReal.zero_div]
        exact tendsto_const_nhds
      rw [huniv, compl_univ, measure_empty]
    · exact singularPart_lambdaS_compl_eq_zero μ hμ hS'm hS'fin (pos_iff_ne_zero.2 h0) hrefl'
  have hac : μ.singularPart volume ≪ μ :=
    Measure.absolutelyContinuous_of_le (Measure.singularPart_le μ volume)
  have hIcc : μ.singularPart volume (Icc (-|R|) |R|)ᶜ = 0 :=
    hac (measure_mono_null (compl_subset_compl.2
      (Icc_subset_Icc (neg_le_neg (le_abs_self R)) (le_abs_self R))) hR)
  refine measure_mono_null (fun E hE => ?_) (measure_union_null hmain hIcc)
  by_contra hcon
  simp only [mem_union, mem_compl_iff, not_or, not_not] at hcon
  obtain ⟨hEl, hEI⟩ := hcon
  refine hE (mem_lambdaS_of_eventually_subset ?_ hEl)
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with δ hδ
  intro x hx
  refine subset_toMeasurable _ _ ⟨hx.1, ?_⟩
  have hx2 := hx.2
  rw [mem_ball, Real.dist_eq, abs_lt] at hx2
  obtain ⟨hx3, hx4⟩ := hx2
  rw [mem_Icc] at hEI ⊢
  obtain ⟨hE1, hE2⟩ := hEI
  have hδ1 := hδ.2
  constructor <;> linarith

end DF
