/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators, I*,
§1.10: proof of Poltoratski's theorem (Theorem 1.10.1).

# Main results

* `DF.poltoratski_bounded` — Theorem 1.10.1 for densities `0 ≤ f ≤ 1`, in the form: for
  `μ`-a.e. `E` with `Im F_μ(E + iε) → ∞`, `F_{fμ}(E + iε) / F_μ(E + iε) → f(E)`.
* `DF.poltoratskiStatement_holds` — Theorem 1.10.1 (`DF.PoltoratskiStatement`).

# Proof

We follow V. Jakšić, Y. Last, *A new proof of Poltoratskii's theorem*, J. Funct. Anal. 215
(2004), which is the proof given in the book.  Their argument uses the rank one perturbation
`A₁ = A + ⟨1, ·⟩ 1` of multiplication by the variable on `L²(μ)`, its spectral measure `μ₁`
(with `F_{μ₁} = F_μ / (1 + F_μ)`), and the image `U f ∈ L²(μ₁)` of `f` under the unitary
`U : L²(μ) → L²(μ₁)` diagonalizing `A₁`, which satisfies
`F_{(Uf) μ₁} = F_{fμ} / (1 + F_μ)` (2.9).  We avoid the spectral theorem: for real `t` the
functions
`Φ_t = F_{(f+t)² μ} - F_{(f+t) μ}² / (1 + F_μ)`
(`= ⟨f + t, (A₁ - z)⁻¹ (f + t)⟩`) have nonnegative imaginary part by an explicit computation,
`Φ_t = Φ_0 + 2 t G + t² Ψ` with `G = F_{fμ} / (1 + F_μ)` and `Ψ = F_μ / (1 + F_μ)`, and
`Φ_t + Ψ` is the Borel transform of a finite measure `τ_t`.  Comparing the measures `τ_t` (via
uniqueness of Borel transforms) gives, after removing a `μ₁`-null set carrying the singular part
of `μ`, the Cauchy–Schwarz inequality `(Im G)² ≤ Im F_σ · Im Ψ` with a finite measure `σ`
singular to `μ_s`, which is all that is used in Jakšić–Last's argument.
-/
import DamanikFillman.Ch1.BorelExt

noncomputable section

open MeasureTheory Filter Topology Set Metric Complex
open scoped ENNReal

namespace DF

/-! ### Algebra -/

/-- The imaginary part of `Φ_t`, in terms of `c = F_{(f+t)μ} / (1 + F_μ)`. -/
lemma im_phi_aux (B1 B2 F c : ℂ) (t : ℝ) (hc : B1 + t * F = c * (1 + F)) :
    (B2 + 2 * t * B1 + t ^ 2 * F - c ^ 2 * (1 + F)).im =
      B2.im + 2 * (t - c.re) * B1.im + (t - c.re) ^ 2 * F.im + c.im ^ 2 * F.im := by
  have h1 := congrArg Complex.im hc
  simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.add_re,
    Complex.sub_re, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
    Complex.re_ofNat, Complex.im_ofNat, pow_two] at h1 ⊢
  linear_combination (2 * c.re) * h1

lemma borelTransform_smul (ν : Measure ℝ) (c : ℝ≥0∞) (z : ℂ) :
    borelTransform (c • ν) z = (c.toReal : ℂ) * borelTransform ν z := by
  unfold borelTransform
  rw [integral_smul_measure, Complex.real_smul]

/-! ### Densities as measures -/

lemma borelTransformDensity_eq_withDensity (μ : Measure ℝ) {f : ℝ → ℝ} (hfm : Measurable f)
    (hf0 : ∀ x, 0 ≤ f x) (z : ℂ) :
    borelTransformDensity μ f z =
      borelTransform (μ.withDensity fun x => ENNReal.ofReal (f x)) z := by
  unfold borelTransformDensity borelTransform
  rw [integral_withDensity_eq_integral_toReal_smul hfm.ennreal_ofReal
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Complex.real_smul]
  rw [ENNReal.toReal_ofReal (hf0 x)]

lemma withDensity_real_univ_le (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hf1 : ∀ x, f x ≤ 1) :
    (μ.withDensity fun x => ENNReal.ofReal (f x)) univ ≤ μ univ := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ ∫⁻ _x, 1 ∂μ :=
        lintegral_mono fun x => by
          rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (hf1 x)
    _ = μ univ := by rw [lintegral_const, one_mul]

lemma isFiniteMeasure_withDensity_le_one (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hf1 : ∀ x, f x ≤ 1) : IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (f x)) :=
  ⟨lt_of_le_of_lt (withDensity_real_univ_le μ hf1) (measure_lt_top μ univ)⟩

lemma one_add_borelTransform_ne_zero (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : μ ≠ 0) {z : ℂ}
    (hz : 0 < z.im) : 1 + borelTransform μ z ≠ 0 := by
  intro h
  have h1 := congrArg Complex.im h
  have h2 := borelTransform_im_pos μ hμ hz
  simp only [Complex.add_im, Complex.one_im, zero_add, Complex.zero_im] at h1
  linarith

/-! ### The functions `Φ_t`, `G`, `Ψ` -/

/-- `G = F_{fμ} / (1 + F_μ)`. -/
def jlG (μ : Measure ℝ) (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  borelTransformDensity μ f z / (1 + borelTransform μ z)

/-- `Ψ = F_μ / (1 + F_μ)`. -/
def jlPsi (μ : Measure ℝ) (z : ℂ) : ℂ := borelTransform μ z / (1 + borelTransform μ z)

/-- `Φ_t = F_{(f+t)² μ} - F_{(f+t) μ}² / (1 + F_μ)`. -/
def jlPhi (μ : Measure ℝ) (f : ℝ → ℝ) (t : ℝ) (z : ℂ) : ℂ :=
  (borelTransformDensity μ (fun x => f x ^ 2) z + 2 * t * borelTransformDensity μ f z +
      t ^ 2 * borelTransform μ z) -
    (borelTransformDensity μ f z + t * borelTransform μ z) ^ 2 / (1 + borelTransform μ z)

lemma jlPhi_eq (μ : Measure ℝ) (f : ℝ → ℝ) (t : ℝ) {z : ℂ}
    (hz : 1 + borelTransform μ z ≠ 0) :
    jlPhi μ f t z = jlPhi μ f 0 z + 2 * t * jlG μ f z + t ^ 2 * jlPsi μ z := by
  unfold jlPhi jlG jlPsi
  field_simp
  ring

lemma im_jlPsi (μ : Measure ℝ) (z : ℂ) :
    (jlPsi μ z).im = (borelTransform μ z).im / Complex.normSq (1 + borelTransform μ z) := by
  have := im_div_one_add_mul (borelTransform μ z) 1
  simp only [Complex.ofReal_one, one_mul] at this
  exact this

lemma im_jlPsi_pos (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : μ ≠ 0) {z : ℂ} (hz : 0 < z.im) :
    0 < (jlPsi μ z).im := by
  rw [im_jlPsi]
  exact div_pos (borelTransform_im_pos μ hμ hz)
    (Complex.normSq_pos.2 (one_add_borelTransform_ne_zero μ hμ hz))

/-- `∫ (f + s)² P ≥ 0`, written with Borel transforms. -/
lemma quad_im_nonneg (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℝ} (hf : Integrable f μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) (s E : ℝ) {ε : ℝ} (hε : 0 < ε) :
    0 ≤ (borelTransformDensity μ (fun x => f x ^ 2) (E + ε * I)).im +
      2 * s * (borelTransformDensity μ f (E + ε * I)).im +
        s ^ 2 * (borelTransform μ (E + ε * I)).im := by
  rw [borelTransformDensity_im μ hf2 E hε, borelTransformDensity_im μ hf E hε,
    borelTransform_im_eq_poisson μ E hε.ne']
  have hP := integrable_poissonKernel μ hε E
  have hPm : AEStronglyMeasurable (fun x => poissonKernel ε (x - E)) μ :=
    ((continuous_poissonKernel hε).comp (continuous_sub_right E)).aestronglyMeasurable
  have hPb : ∀ᵐ x ∂μ, ‖poissonKernel ε (x - E)‖ ≤ 1 / (Real.pi * ε) :=
    Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (poissonKernel_nonneg hε.le _)]; exact poissonKernel_le hε _
  have h1 : Integrable (fun x => f x * poissonKernel ε (x - E)) μ := hf.mul_bdd hPm hPb
  have h2 : Integrable (fun x => f x ^ 2 * poissonKernel ε (x - E)) μ := hf2.mul_bdd hPm hPb
  have heq : ∫ x, (f x + s) ^ 2 * poissonKernel ε (x - E) ∂μ =
      ∫ x, f x ^ 2 * poissonKernel ε (x - E) ∂μ + 2 * s * ∫ x, f x * poissonKernel ε (x - E) ∂μ +
        s ^ 2 * ∫ x, poissonKernel ε (x - E) ∂μ := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add h2 (h1.const_mul _),
      ← integral_add (h2.add (h1.const_mul _)) (hP.const_mul _)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]
    ring
  have hnn : 0 ≤ ∫ x, (f x + s) ^ 2 * poissonKernel ε (x - E) ∂μ :=
    integral_nonneg fun x => mul_nonneg (sq_nonneg _) (poissonKernel_nonneg hε.le _)
  have := mul_nonneg Real.pi_pos.le hnn
  rw [heq] at this
  linarith

/-- `Im Φ_t ≥ 0`. -/
lemma im_jlPhi_nonneg (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : μ ≠ 0) {f : ℝ → ℝ}
    (hf : Integrable f μ) (hf2 : Integrable (fun x => f x ^ 2) μ) (t : ℝ) {z : ℂ}
    (hz : 0 < z.im) : 0 ≤ (jlPhi μ f t z).im := by
  have hw := one_add_borelTransform_ne_zero μ hμ hz
  set c := (borelTransformDensity μ f z + t * borelTransform μ z) / (1 + borelTransform μ z)
    with hcdef
  have hc : borelTransformDensity μ f z + t * borelTransform μ z =
      c * (1 + borelTransform μ z) := by rw [hcdef]; field_simp
  have hphi : jlPhi μ f t z = borelTransformDensity μ (fun x => f x ^ 2) z +
      2 * t * borelTransformDensity μ f z + t ^ 2 * borelTransform μ z -
        c ^ 2 * (1 + borelTransform μ z) := by
    unfold jlPhi
    rw [hc]
    field_simp
  rw [hphi, im_phi_aux _ _ _ c t hc]
  have hzeq : z = (z.re : ℂ) + z.im * I := (Complex.re_add_im z).symm
  have hq := quad_im_nonneg μ hf hf2 (t - c.re) z.re hz
  rw [← hzeq] at hq
  have hF := borelTransform_im_pos μ hμ hz
  have : 0 ≤ c.im ^ 2 * (borelTransform μ z).im := mul_nonneg (sq_nonneg _) hF.le
  linarith

/-! ### `Φ_t + Ψ` is a Borel transform -/

lemma integrable_of_bounded01 (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) : Integrable f μ :=
  Integrable.of_bound (C := 1) hfm.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_of_nonneg (hf0 x)]; exact hf1 x)

lemma differentiableOn_borelTransformDensity (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    DifferentiableOn ℂ (borelTransformDensity μ f) {z | 0 < z.im} := by
  haveI := isFiniteMeasure_withDensity_le_one μ hf1
  have h : borelTransformDensity μ f =
      borelTransform (μ.withDensity fun x => ENNReal.ofReal (f x)) :=
    funext fun z => borelTransformDensity_eq_withDensity μ hfm hf0 z
  rw [h]
  exact differentiableOn_borelTransform _

lemma norm_borelTransformDensity_le (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) {z : ℂ} (hz : 0 < z.im) :
    ‖borelTransformDensity μ f z‖ ≤ μ.real univ / z.im := by
  haveI := isFiniteMeasure_withDensity_le_one μ hf1
  rw [borelTransformDensity_eq_withDensity μ hfm hf0 z]
  refine (norm_borelTransform_le _ hz).trans ?_
  refine div_le_div_of_nonneg_right ?_ hz.le
  rw [measureReal_def, measureReal_def]
  exact ENNReal.toReal_mono (measure_ne_top μ univ) (withDensity_real_univ_le μ hf1)

lemma norm_add_mul_le {a b : ℂ} {u : ℝ} (ha : ‖a‖ ≤ u) (hb : ‖b‖ ≤ u) (t : ℝ) :
    ‖a + t * b‖ ≤ (1 + |t|) * u := by
  calc ‖a + t * b‖ ≤ ‖a‖ + ‖(t : ℂ) * b‖ := norm_add_le _ _
    _ = ‖a‖ + |t| * ‖b‖ := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ u + |t| * u := add_le_add ha (mul_le_mul_of_nonneg_left hb (abs_nonneg t))
    _ = (1 + |t|) * u := by ring

theorem isHerglotz_jlPhi_add (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : μ ≠ 0) {f : ℝ → ℝ}
    (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (t : ℝ) :
    IsHerglotz (fun z => jlPhi μ f t z + jlPsi μ z) := by
  have hf2m : Measurable (fun x => f x ^ 2) := hfm.pow_const 2
  have hf20 : ∀ x, 0 ≤ f x ^ 2 := fun x => sq_nonneg _
  have hf21 : ∀ x, f x ^ 2 ≤ 1 := fun x => by nlinarith [hf0 x, hf1 x]
  have hF := differentiableOn_borelTransform μ
  have hB1 := differentiableOn_borelTransformDensity μ hfm hf0 hf1
  have hB2 := differentiableOn_borelTransformDensity μ hf2m hf20 hf21
  have hW : DifferentiableOn ℂ (fun z => 1 + borelTransform μ z) {z | 0 < z.im} :=
    (differentiableOn_const 1).add hF
  have hne : ∀ z ∈ {z : ℂ | 0 < z.im}, 1 + borelTransform μ z ≠ 0 :=
    fun z hz => one_add_borelTransform_ne_zero μ hμ hz
  refine ⟨?_, fun z hz => ?_⟩
  · have h1 : DifferentiableOn ℂ (fun z => jlPhi μ f t z) {z | 0 < z.im} := by
      unfold jlPhi
      refine DifferentiableOn.sub ?_ ?_
      · exact (hB2.add ((differentiableOn_const _).mul hB1)).add ((differentiableOn_const _).mul hF)
      · exact ((hB1.add ((differentiableOn_const _).mul hF)).pow 2).div hW hne
    have h2 : DifferentiableOn ℂ (fun z => jlPsi μ z) {z | 0 < z.im} := by
      unfold jlPsi
      exact hF.div hW hne
    exact h1.add h2
  · have hf := integrable_of_bounded01 μ hfm hf0 hf1
    have hf2 := integrable_of_bounded01 μ hf2m hf20 hf21
    rw [Complex.add_im]
    exact add_pos_of_nonneg_of_pos (im_jlPhi_nonneg μ hμ hf hf2 t hz) (im_jlPsi_pos μ hμ hz)

theorem norm_jlPhi_add_le (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : μ ≠ 0) {f : ℝ → ℝ}
    (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (t : ℝ) (y : ℝ)
    (hy : 2 * μ.real univ + 1 ≤ y) (hy0 : 0 < y) :
    ‖jlPhi μ f t (y * I) + jlPsi μ (y * I)‖ ≤
      ((2 * (1 + |t|) ^ 2 + 2) * μ.real univ) / y := by
  have hf2m : Measurable (fun x => f x ^ 2) := hfm.pow_const 2
  have hf20 : ∀ x, 0 ≤ f x ^ 2 := fun x => sq_nonneg _
  have hf21 : ∀ x, f x ^ 2 ≤ 1 := fun x => by nlinarith [hf0 x, hf1 x]
  have hz : 0 < ((y : ℂ) * I).im := by simpa using hy0
  have him : ((y : ℂ) * I).im = y := by simp
  set m := μ.real univ with hm
  have hm0 : 0 ≤ m := measureReal_nonneg
  set u := m / y with hu
  have hu0 : 0 ≤ u := div_nonneg hm0 hy0.le
  have hu2 : 2 * u ≤ 1 := by
    rw [hu, ← mul_div_assoc, div_le_one hy0]; linarith
  have hF : ‖borelTransform μ (y * I)‖ ≤ u := by
    have := norm_borelTransform_le μ hz; rwa [him] at this
  have hB1 : ‖borelTransformDensity μ f (y * I)‖ ≤ u := by
    have := norm_borelTransformDensity_le μ hfm hf0 hf1 hz; rwa [him] at this
  have hB2 : ‖borelTransformDensity μ (fun x => f x ^ 2) (y * I)‖ ≤ u := by
    have := norm_borelTransformDensity_le μ hf2m hf20 hf21 hz; rwa [him] at this
  set F := borelTransform μ (y * I)
  set B1 := borelTransformDensity μ f (y * I)
  set B2 := borelTransformDensity μ (fun x => f x ^ 2) (y * I)
  have hw : 1 / 2 ≤ ‖1 + F‖ := by
    have := norm_sub_norm_le (1 : ℂ) (-F)
    rw [sub_neg_eq_add, norm_one, norm_neg] at this
    linarith
  have hwpos : 0 < ‖1 + F‖ := lt_of_lt_of_le (by norm_num) hw
  have hN1 : ‖B2 + 2 * t * B1 + t ^ 2 * F‖ ≤ (1 + |t|) ^ 2 * u := by
    calc ‖B2 + 2 * t * B1 + t ^ 2 * F‖ ≤ ‖B2‖ + ‖(2 * t : ℂ) * B1‖ + ‖((t ^ 2 : ℝ) : ℂ) * F‖ := by
          refine (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) ?_)
          push_cast; exact le_rfl
      _ = ‖B2‖ + 2 * |t| * ‖B1‖ + t ^ 2 * ‖F‖ := by
          rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (sq_nonneg t)]
          norm_num
      _ ≤ u + 2 * |t| * u + t ^ 2 * u := by
          gcongr
      _ = (1 + |t|) ^ 2 * u := by rw [← sq_abs t]; ring
  have hN2 : ‖(B1 + t * F) ^ 2 / (1 + F)‖ ≤ (1 + |t|) ^ 2 * u := by
    have h1 := norm_add_mul_le hB1 hF t
    rw [norm_div, norm_pow, div_le_iff₀ hwpos]
    calc ‖B1 + t * F‖ ^ 2 ≤ ((1 + |t|) * u) ^ 2 := by gcongr
      _ = (1 + |t|) ^ 2 * u * (2 * u) / 2 := by ring
      _ ≤ (1 + |t|) ^ 2 * u * 1 / 2 := by gcongr
      _ ≤ (1 + |t|) ^ 2 * u * ‖1 + F‖ := by
          rw [mul_one, mul_div_assoc]
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hN3 : ‖F / (1 + F)‖ ≤ 2 * u := by
    rw [norm_div, div_le_iff₀ hwpos]
    nlinarith
  have htot : ‖jlPhi μ f t (y * I) + jlPsi μ (y * I)‖ ≤ (2 * (1 + |t|) ^ 2 + 2) * u := by
    unfold jlPhi jlPsi
    calc ‖B2 + 2 * t * B1 + t ^ 2 * F - (B1 + t * F) ^ 2 / (1 + F) + F / (1 + F)‖
        ≤ ‖B2 + 2 * t * B1 + t ^ 2 * F‖ + ‖(B1 + t * F) ^ 2 / (1 + F)‖ + ‖F / (1 + F)‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ (1 + |t|) ^ 2 * u + (1 + |t|) ^ 2 * u + 2 * u := add_le_add (add_le_add hN1 hN2) hN3
      _ = (2 * (1 + |t|) ^ 2 + 2) * u := by ring
  rw [hu, ← mul_div_assoc] at htot
  exact htot

theorem exists_jlTau (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : μ ≠ 0) {f : ℝ → ℝ}
    (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) (t : ℝ) :
    ∃ τ : Measure ℝ, IsFiniteMeasure τ ∧
      ∀ z : ℂ, 0 < z.im → borelTransform τ z = jlPhi μ f t z + jlPsi μ z := by
  obtain ⟨ν, hν, hrep⟩ := exists_measure_of_isHerglotz (isHerglotz_jlPhi_add μ hμ hfm hf0 hf1 t)
    (C := (2 * (1 + |t|) ^ 2 + 2) * μ.real univ) (y₀ := 2 * μ.real univ + 1)
    fun y hy hy0 => norm_jlPhi_add_le μ hμ hfm hf0 hf1 t y hy hy0
  exact ⟨ν, hν, fun z hz => (hrep z hz).symm⟩

lemma jlPhi_zero_zero (μ : Measure ℝ) (z : ℂ) : jlPhi μ (fun _ => 0) 0 z = 0 := by
  simp [jlPhi, borelTransformDensity]

end DF
