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

/-! ### Comparison of the measures `τ_t` -/

lemma quad_disc {A D C : ℝ} (h : ∀ t : ℝ, 0 ≤ A + 2 * t * D + t ^ 2 * C) (hC : 0 < C) :
    D ^ 2 ≤ A * C := by
  have h1 := h (-D / C)
  have h2 : A + 2 * (-D / C) * D + (-D / C) ^ 2 * C = A - D ^ 2 / C := by
    field_simp; ring
  rw [h2] at h1
  have h3 : D ^ 2 / C ≤ A := by linarith
  rwa [div_le_iff₀ hC] at h3

lemma lin_zero {A D : ℝ} (h : ∀ t : ℝ, 0 ≤ A + 2 * t * D) : D = 0 := by
  by_contra hD
  have h1 := h (-(|A| + 1) / (2 * D))
  have h2 : A + 2 * (-(|A| + 1) / (2 * D)) * D = A - (|A| + 1) := by
    field_simp; ring
  rw [h2] at h1
  linarith [le_abs_self A]

lemma borelTransform_restrict_add (ν : Measure ℝ) [IsFiniteMeasure ν] {S : Set ℝ}
    (hS : MeasurableSet S) {z : ℂ} (hz : z.im ≠ 0) :
    borelTransform ν z = borelTransform (ν.restrict S) z + borelTransform (ν.restrict Sᶜ) z := by
  rw [← borelTransform_add _ _ hz, Measure.restrict_add_restrict_compl hS]

section Comparison

variable {μ : Measure ℝ} [IsFiniteMeasure μ] {f : ℝ → ℝ} {τ : ℝ → Measure ℝ}
  [hτf : ∀ t, IsFiniteMeasure (τ t)] {μ₁ : Measure ℝ} [IsFiniteMeasure μ₁]

/-- The basic identity between the measures `τ_t`, `t ≥ 0`. -/
lemma jl_identity_nonneg (hμ : μ ≠ 0)
    (hτ : ∀ t z, 0 < z.im → borelTransform (τ t) z = jlPhi μ f t z + jlPsi μ z)
    (hμ₁ : ∀ z, 0 < z.im → borelTransform μ₁ z = jlPsi μ z) {t : ℝ} (ht : 0 ≤ t) :
    τ t + ENNReal.ofReal (t / 2) • τ (-1) =
      τ 0 + ENNReal.ofReal (t / 2) • τ 1 + ENNReal.ofReal (t ^ 2) • μ₁ := by
  haveI := (τ (-1)).smul_finite (ENNReal.ofReal_ne_top (r := t / 2))
  haveI := (τ 1).smul_finite (ENNReal.ofReal_ne_top (r := t / 2))
  haveI := μ₁.smul_finite (ENNReal.ofReal_ne_top (r := t ^ 2))
  refine borelTransform_ext fun z hz => ?_
  have hz' : z.im ≠ 0 := hz.ne'
  have hw := one_add_borelTransform_ne_zero μ hμ hz
  rw [borelTransform_add _ _ hz', borelTransform_add _ _ hz', borelTransform_add _ _ hz',
    borelTransform_smul, borelTransform_smul, borelTransform_smul, hτ _ _ hz, hτ _ _ hz,
    hτ _ _ hz, hτ _ _ hz, hμ₁ _ hz, ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ t / 2),
    ENNReal.toReal_ofReal (sq_nonneg t), jlPhi_eq μ f t hw, jlPhi_eq μ f (-1) hw,
    jlPhi_eq μ f 1 hw]
  push_cast
  ring

/-- The basic identity between the measures `τ_t`, `t ≤ 0`. -/
lemma jl_identity_nonpos (hμ : μ ≠ 0)
    (hτ : ∀ t z, 0 < z.im → borelTransform (τ t) z = jlPhi μ f t z + jlPsi μ z)
    (hμ₁ : ∀ z, 0 < z.im → borelTransform μ₁ z = jlPsi μ z) {t : ℝ} (ht : t ≤ 0) :
    τ t + ENNReal.ofReal (-t / 2) • τ 1 =
      τ 0 + ENNReal.ofReal (-t / 2) • τ (-1) + ENNReal.ofReal (t ^ 2) • μ₁ := by
  haveI := (τ (-1)).smul_finite (ENNReal.ofReal_ne_top (r := -t / 2))
  haveI := (τ 1).smul_finite (ENNReal.ofReal_ne_top (r := -t / 2))
  haveI := μ₁.smul_finite (ENNReal.ofReal_ne_top (r := t ^ 2))
  refine borelTransform_ext fun z hz => ?_
  have hz' : z.im ≠ 0 := hz.ne'
  have hw := one_add_borelTransform_ne_zero μ hμ hz
  have ht' : 0 ≤ -t / 2 := by linarith
  rw [borelTransform_add _ _ hz', borelTransform_add _ _ hz', borelTransform_add _ _ hz',
    borelTransform_smul, borelTransform_smul, borelTransform_smul, hτ _ _ hz, hτ _ _ hz,
    hτ _ _ hz, hτ _ _ hz, hμ₁ _ hz, ENNReal.toReal_ofReal ht',
    ENNReal.toReal_ofReal (sq_nonneg t), jlPhi_eq μ f t hw, jlPhi_eq μ f (-1) hw,
    jlPhi_eq μ f 1 hw]
  push_cast
  ring

/-- Restricting the identities to a measurable set `S` and taking imaginary parts of Borel
transforms: `0 ≤ Q(τ_0) + 2 t D + t² Q(μ₁)` with `D = (Q(τ_1) - Q(τ_{-1})) / 4`. -/
lemma jl_quad (hμ : μ ≠ 0)
    (hτ : ∀ t z, 0 < z.im → borelTransform (τ t) z = jlPhi μ f t z + jlPsi μ z)
    (hμ₁ : ∀ z, 0 < z.im → borelTransform μ₁ z = jlPsi μ z) (S : Set ℝ) {z : ℂ}
    (hz : 0 < z.im) (t : ℝ) :
    0 ≤ (borelTransform ((τ 0).restrict S) z).im +
      2 * t * (((borelTransform ((τ 1).restrict S) z).im -
        (borelTransform ((τ (-1)).restrict S) z).im) / 4) +
      t ^ 2 * (borelTransform (μ₁.restrict S) z).im := by
  have hz' : z.im ≠ 0 := hz.ne'
  have hzeq : z = (z.re : ℂ) + z.im * I := (Complex.re_add_im z).symm
  have hnn : ∀ (ν : Measure ℝ) [IsFiniteMeasure ν], 0 ≤ (borelTransform ν z).im := by
    intro ν _
    have := borelTransform_im_nonneg ν z.re hz
    rwa [← hzeq] at this
  have him : ∀ (ν₁ ν₂ : Measure ℝ) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] (c : ℝ≥0∞),
      c ≠ ⊤ → (borelTransform ((ν₁ + c • ν₂).restrict S) z).im =
        (borelTransform (ν₁.restrict S) z).im + c.toReal * (borelTransform (ν₂.restrict S) z).im := by
    intro ν₁ ν₂ _ _ c hc
    haveI := (ν₂.restrict S).smul_finite hc
    rw [Measure.restrict_add, Measure.restrict_smul, borelTransform_add _ _ hz',
      borelTransform_smul, Complex.add_im, Complex.im_ofReal_mul]
  rcases le_total 0 t with ht | ht
  · have h := congrArg (fun ν => (borelTransform (ν.restrict S) z).im)
      (jl_identity_nonneg hμ hτ hμ₁ ht)
    simp only at h
    haveI := (τ (-1)).smul_finite (ENNReal.ofReal_ne_top (r := t / 2))
    haveI := (τ 1).smul_finite (ENNReal.ofReal_ne_top (r := t / 2))
    rw [him _ _ _ ENNReal.ofReal_ne_top, him _ _ _ ENNReal.ofReal_ne_top,
      him _ _ _ ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ t / 2),
      ENNReal.toReal_ofReal (sq_nonneg t)] at h
    have h0 := hnn ((τ t).restrict S)
    have h1 := hnn ((τ (-1)).restrict S)
    linarith
  · have h := congrArg (fun ν => (borelTransform (ν.restrict S) z).im)
      (jl_identity_nonpos hμ hτ hμ₁ ht)
    simp only at h
    haveI := (τ (-1)).smul_finite (ENNReal.ofReal_ne_top (r := -t / 2))
    haveI := (τ 1).smul_finite (ENNReal.ofReal_ne_top (r := -t / 2))
    have ht' : 0 ≤ -t / 2 := by linarith
    rw [him _ _ _ ENNReal.ofReal_ne_top, him _ _ _ ENNReal.ofReal_ne_top,
      him _ _ _ ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal ht',
      ENNReal.toReal_ofReal (sq_nonneg t)] at h
    have h0 := hnn ((τ t).restrict S)
    have h1 := hnn ((τ 1).restrict S)
    linarith

/-- The Cauchy–Schwarz inequality `(Im G)² ≤ Im F_σ · Im Ψ`, where `σ = τ_0` restricted to the
complement of a `μ₁`-null measurable set `T`. -/
lemma jl_cauchySchwarz (hμ : μ ≠ 0)
    (hτ : ∀ t z, 0 < z.im → borelTransform (τ t) z = jlPhi μ f t z + jlPsi μ z)
    (hμ₁ : ∀ z, 0 < z.im → borelTransform μ₁ z = jlPsi μ z) {T : Set ℝ}
    (hT : MeasurableSet T) (hμ₁T : μ₁ T = 0) {z : ℂ} (hz : 0 < z.im) :
    (jlG μ f z).im ^ 2 ≤ (borelTransform ((τ 0).restrict Tᶜ) z).im * (jlPsi μ z).im := by
  have hz' : z.im ≠ 0 := hz.ne'
  have hw := one_add_borelTransform_ne_zero μ hμ hz
  -- on `T` the coefficient vanishes
  have hT0 : μ₁.restrict T = 0 := Measure.restrict_eq_zero.2 hμ₁T
  have hTc : μ₁.restrict Tᶜ = μ₁ :=
    Measure.restrict_eq_self_of_ae_mem (measure_eq_zero_iff_ae_notMem.1 hμ₁T |>.mono
      fun x hx => hx)
  have hD0 := lin_zero (A := (borelTransform ((τ 0).restrict T) z).im)
    (D := ((borelTransform ((τ 1).restrict T) z).im -
      (borelTransform ((τ (-1)).restrict T) z).im) / 4) fun t => by
    have := jl_quad hμ hτ hμ₁ T hz t
    rw [hT0] at this
    simpa [borelTransform] using this
  -- `4 G = F_{τ_1} - F_{τ_{-1}}`
  have hG : (jlG μ f z).im = ((borelTransform ((τ 1).restrict T) z).im -
        (borelTransform ((τ (-1)).restrict T) z).im) / 4 +
      ((borelTransform ((τ 1).restrict Tᶜ) z).im -
        (borelTransform ((τ (-1)).restrict Tᶜ) z).im) / 4 := by
    have h1 : borelTransform (τ 1) z - borelTransform (τ (-1)) z = 4 * jlG μ f z := by
      rw [hτ _ _ hz, hτ _ _ hz, jlPhi_eq μ f 1 hw, jlPhi_eq μ f (-1) hw]
      push_cast; ring
    rw [borelTransform_restrict_add (τ 1) hT hz', borelTransform_restrict_add (τ (-1)) hT hz']
      at h1
    have h2 := congrArg Complex.im h1
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.re_ofNat,
      Complex.im_ofNat, zero_mul, add_zero] at h2
    linarith
  rw [hG, hD0, zero_add]
  refine quad_disc (fun t => ?_) ?_
  · have := jl_quad hμ hτ hμ₁ Tᶜ hz t
    rw [hTc, hμ₁ z hz] at this
    exact this
  · exact im_jlPsi_pos μ hμ hz

end Comparison

/-! ### The limit argument of Jakšić–Last -/

/-- The pointwise argument of Jakšić–Last: with `B₁ = G (1 + F)`, `Im F → ∞`,
`Im B₁ / Im F → c`, `A / Im F → 0` and `(Im G)² ≤ A Im (F / (1 + F))`, we get `B₁ / F → c`. -/
theorem jl_limit {Fz B1z Gz : ℝ → ℂ} {A : ℝ → ℝ} {c : ℝ}
    (hF : Tendsto (fun ε => (Fz ε).im) (𝓝[>] 0) atTop)
    (hB : Tendsto (fun ε => (B1z ε).im / (Fz ε).im) (𝓝[>] 0) (𝓝 c))
    (hA : Tendsto (fun ε => A ε / (Fz ε).im) (𝓝[>] 0) (𝓝 0))
    (hG : ∀ᶠ ε in 𝓝[>] 0, B1z ε = Gz ε * (1 + Fz ε))
    (hCS : ∀ᶠ ε in 𝓝[>] 0,
      (Gz ε).im ^ 2 ≤ A ε * ((Fz ε).im / Complex.normSq (1 + Fz ε))) :
    Tendsto (fun ε => B1z ε / Fz ε) (𝓝[>] 0) (𝓝 (c : ℂ)) := by
  have hpos : ∀ᶠ ε in 𝓝[>] 0, 0 < (Fz ε).im := hF.eventually_gt_atTop 0
  have hsq : Tendsto (fun ε => Real.sqrt (A ε / (Fz ε).im)) (𝓝[>] 0) (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hA
    rwa [Real.sqrt_zero] at this
  -- the key estimates
  have hest : ∀ᶠ ε in 𝓝[>] 0, |(Gz ε).im| ≤ Real.sqrt (A ε / (Fz ε).im) ∧
      |(1 + Fz ε).re * (Gz ε).im / (Fz ε).im| ≤ Real.sqrt (A ε / (Fz ε).im) ∧
      (Gz ε).re = (B1z ε).im / (Fz ε).im - (1 + Fz ε).re * (Gz ε).im / (Fz ε).im := by
    filter_upwards [hpos, hCS, hG] with ε hp hcs hg
    set w := 1 + Fz ε with hw
    have hwim : w.im = (Fz ε).im := by rw [hw]; simp
    have hns : (Fz ε).im ^ 2 ≤ Complex.normSq w := by
      rw [← hwim]; exact normSq_ge_im_sq w
    have hnspos : 0 < Complex.normSq w := lt_of_lt_of_le (by positivity) hns
    have hre : w.re ^ 2 ≤ Complex.normSq w := by
      rw [Complex.normSq_apply]; nlinarith [mul_self_nonneg w.im]
    have hA0 : 0 ≤ A ε := by
      by_contra hneg
      push_neg at hneg
      have : A ε * ((Fz ε).im / Complex.normSq w) < 0 :=
        mul_neg_of_neg_of_pos hneg (div_pos hp hnspos)
      nlinarith [sq_nonneg (Gz ε).im]
    have h1 : A ε * ((Fz ε).im / Complex.normSq w) ≤ A ε / (Fz ε).im := by
      rw [mul_div_assoc', div_le_div_iff₀ hnspos hp]
      have := mul_le_mul_of_nonneg_left hns hA0
      nlinarith [this]
    have hc' : (Gz ε).im ^ 2 ≤ A ε * (Fz ε).im / Complex.normSq w := by
      rw [mul_div_assoc]; exact hcs
    have hq : 0 ≤ A ε * (Fz ε).im / Complex.normSq w :=
      div_nonneg (mul_nonneg hA0 hp.le) hnspos.le
    refine ⟨Real.abs_le_sqrt (hcs.trans h1), Real.abs_le_sqrt ?_, ?_⟩
    · rw [div_pow, mul_pow, div_le_div_iff₀ (by positivity) hp]
      calc w.re ^ 2 * (Gz ε).im ^ 2 * (Fz ε).im
          ≤ w.re ^ 2 * (A ε * (Fz ε).im / Complex.normSq w) * (Fz ε).im :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc' (sq_nonneg _)) hp.le
        _ ≤ Complex.normSq w * (A ε * (Fz ε).im / Complex.normSq w) * (Fz ε).im :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hre hq) hp.le
        _ = A ε * (Fz ε).im ^ 2 := by
            rw [mul_div_assoc', mul_div_cancel_left₀ _ hnspos.ne']; ring
    · have h2 := congrArg Complex.im hg
      rw [Complex.mul_im, hwim] at h2
      have hpne := hp.ne'
      field_simp
      linarith
  have hIm : Tendsto (fun ε => (Gz ε).im) (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hsq
    filter_upwards [hest] with ε h
    rw [Real.norm_eq_abs]; exact h.1
  have hL : Tendsto (fun ε => (1 + Fz ε).re * (Gz ε).im / (Fz ε).im) (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hsq
    filter_upwards [hest] with ε h
    rw [Real.norm_eq_abs]; exact h.2.1
  have hRe : Tendsto (fun ε => (Gz ε).re) (𝓝[>] 0) (𝓝 c) := by
    have := hB.sub hL
    rw [sub_zero] at this
    refine this.congr' ?_
    filter_upwards [hest] with ε h
    exact h.2.2.symm
  have hGc : Tendsto Gz (𝓝[>] 0) (𝓝 (c : ℂ)) := by
    have h := ((Complex.continuous_ofReal.tendsto c).comp hRe).add
      (((Complex.continuous_ofReal.tendsto 0).comp hIm).mul_const I)
    simp only [Function.comp_def, Complex.ofReal_zero, zero_mul, add_zero] at h
    exact h.congr fun ε => Complex.re_add_im _
  have hinv : Tendsto (fun ε => (Fz ε)⁻¹) (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
      hF.inv_tendsto_atTop
    filter_upwards [hpos] with ε hp
    rw [norm_inv]
    exact inv_anti₀ hp ((le_abs_self _).trans (Complex.abs_im_le_norm _))
  have h := hGc.mul (hinv.const_add 1)
  rw [add_zero, mul_one] at h
  refine h.congr' ?_
  filter_upwards [hpos, hG] with ε hp hg
  have hF0 : Fz ε ≠ 0 := fun h0 => by rw [h0, Complex.zero_im] at hp; exact lt_irrefl _ hp
  rw [hg]
  field_simp
  ring

/-! ### Theorem 1.10.1 for densities `0 ≤ f ≤ 1` -/

/-- **Poltoratski's theorem for densities `0 ≤ f ≤ 1`** (Jakšić–Last): for `μ`-a.e. `E` at which
`Im F_μ(E + iε) → ∞`, `F_{fμ}(E + iε) / F_μ(E + iε) → f(E)`. -/
theorem poltoratski_bounded (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    ∀ᵐ E ∂μ, Tendsto (fun ε : ℝ => (borelTransform μ (E + ε * I)).im) (𝓝[>] 0) atTop →
      Tendsto (fun ε : ℝ => borelTransformDensity μ f (E + ε * I) / borelTransform μ (E + ε * I))
        (𝓝[>] 0) (𝓝 (f E : ℂ)) := by
  rcases eq_or_ne μ 0 with rfl | hμ
  · simp
  have hf := integrable_of_bounded01 μ hfm hf0 hf1
  choose τ hτfin hτ using exists_jlTau μ hμ hfm hf0 hf1
  haveI := hτfin
  obtain ⟨μ₁, hμ₁fin, hμ₁⟩ := exists_jlTau μ hμ (f := fun _ => 0) measurable_const
    (fun _ => le_rfl) (fun _ => zero_le_one) 0
  haveI := hμ₁fin
  have hμ₁' : ∀ z : ℂ, 0 < z.im → borelTransform μ₁ z = jlPsi μ z := fun z hz => by
    rw [hμ₁ z hz, jlPhi_zero_zero, zero_add]
  -- the set where `Im F_μ → ∞` is `μ₁`-null
  set T := {E : ℝ | Tendsto (fun ε : ℝ => (borelTransform μ (E + ε * I)).im) (𝓝[>] 0) atTop}
    with hTdef
  have hTsing : T ⊆ {E : ℝ | ¬ Tendsto (fun ε : ℝ => (borelTransform μ₁ (E + ε * I)).im)
      (𝓝[>] 0) atTop} := by
    intro E hE h1
    have hev1 := h1.eventually_gt_atTop 1
    have hev2 := (show Tendsto (fun ε : ℝ => (borelTransform μ (E + ε * I)).im) (𝓝[>] 0) atTop
      from hE).eventually_ge_atTop 1
    obtain ⟨ε, hε1, hε2, hε3⟩ := (hev1.and (hev2.and self_mem_nhdsWithin)).exists
    have hz : 0 < ((E : ℂ) + ε * I).im := by simpa using (hε3 : (0 : ℝ) < ε)
    rw [hμ₁' _ hz, im_jlPsi] at hε1
    have hns := normSq_ge_im_sq (1 + borelTransform μ (E + ε * I))
    simp only [Complex.add_im, Complex.one_im, zero_add] at hns
    have hpos : 0 < (borelTransform μ (E + ε * I)).im := by linarith
    rw [lt_div_iff₀ (lt_of_lt_of_le (by positivity) hns)] at hε1
    nlinarith
  have hTvol : volume T = 0 := by
    have h := ae_tendsto_im_volume μ
    rw [ae_iff] at h
    refine measure_mono_null (fun E hE hlim => ?_) h
    exact not_tendsto_atTop_of_tendsto_nhds hlim hE
  have hμ₁T : μ₁ T = 0 := by
    rw [Measure.haveLebesgueDecomposition_add μ₁ volume, Measure.add_apply]
    have h1 : μ₁.singularPart volume T = 0 :=
      measure_mono_null hTsing (singularPart_not_tendsto_atTop μ₁)
    have h2 : (volume.withDensity (μ₁.rnDeriv volume)) T = 0 :=
      withDensity_absolutelyContinuous _ _ hTvol
    rw [h1, h2, add_zero]
  set T' := toMeasurable μ₁ T with hT'def
  have hT'm : MeasurableSet T' := measurableSet_toMeasurable μ₁ T
  have hμ₁T' : μ₁ T' = 0 := by rw [hT'def, measure_toMeasurable, hμ₁T]
  have hTT' : T ⊆ T' := subset_toMeasurable μ₁ T
  set σ := (τ 0).restrict T'ᶜ with hσdef
  have hσT : σ T = 0 := by
    rw [hσdef]
    refine measure_mono_null hTT' ?_
    rw [Measure.restrict_apply hT'm, inter_compl_self, measure_empty]
  -- the singular comparison with `σ`
  have hN : ∀ᵐ E ∂μ, E ∈ T → Tendsto (fun ε : ℝ => (borelTransform σ (E + ε * I)).im /
      (borelTransform μ (E + ε * I)).im) (𝓝[>] 0) (𝓝 0) := by
    have h := ae_singularPart_tendsto_im_ratio_zero μ σ
    rw [ae_iff] at h ⊢
    refine measure_mono_null (t := T ∩ {E | ¬ Tendsto (fun ε : ℝ =>
      (borelTransform σ (E + ε * I)).im / (borelTransform μ (E + ε * I)).im) (𝓝[>] 0) (𝓝 0)})
      (fun E hE => ⟨(not_imp.1 hE).1, (not_imp.1 hE).2⟩) ?_
    rw [Measure.haveLebesgueDecomposition_add μ σ, Measure.add_apply]
    have h1 := measure_mono_null inter_subset_right h
    have h2 : (σ.withDensity (μ.rnDeriv σ)) (T ∩ {E | ¬ Tendsto (fun ε : ℝ =>
        (borelTransform σ (E + ε * I)).im / (borelTransform μ (E + ε * I)).im) (𝓝[>] 0)
          (𝓝 0)}) = 0 :=
      withDensity_absolutelyContinuous _ _ (measure_mono_null inter_subset_left hσT)
    rw [h1, h2, add_zero]
  filter_upwards [ae_tendsto_im_ratio μ hf, hN] with E hb hc hE
  refine jl_limit (Gz := fun ε => jlG μ f (E + ε * I))
    (A := fun ε => (borelTransform σ (E + ε * I)).im) hE hb (hc hE) ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have hz : 0 < ((E : ℂ) + ε * I).im := by simpa using hε
    unfold jlG
    rw [div_mul_cancel₀ _ (one_add_borelTransform_ne_zero μ hμ hz)]
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have hz : 0 < ((E : ℂ) + ε * I).im := by simpa using hε
    have := jl_cauchySchwarz (τ := τ) hμ hτ hμ₁' hT'm hμ₁T' hz
    rw [im_jlPsi] at this
    exact this

/-! ### Theorem 1.10.1 -/

/-- `F_{(f + g) μ} = F_{fμ} + F_{gμ}`. -/
lemma borelTransformDensity_sub (μ : Measure ℝ) [IsFiniteMeasure μ] {f g : ℝ → ℝ}
    (hf : Integrable f μ) (hg : Integrable g μ) {z : ℂ} (hz : z.im ≠ 0) :
    borelTransformDensity μ (fun x => f x - g x) z =
      borelTransformDensity μ f z - borelTransformDensity μ g z := by
  unfold borelTransformDensity
  rw [← integral_sub (integrable_density_inv_sub μ hf hz) (integrable_density_inv_sub μ hg hz)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  push_cast; ring

/-- Theorem 1.10.1 for nonnegative measurable `f ∈ L¹(μ)` (Jakšić–Last, via `1 / (1 + f)`). -/
theorem poltoratski_nonneg (μ : Measure ℝ) [IsFiniteMeasure μ] {f : ℝ → ℝ}
    (hfm : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f μ) :
    ∀ᵐ E ∂(μ.singularPart volume),
      Tendsto (fun ε : ℝ => borelTransformDensity μ f (E + ε * I) / borelTransform μ (E + ε * I))
        (𝓝[>] 0) (𝓝 (f E : ℂ)) := by
  set ν := μ.withDensity fun x => ENNReal.ofReal (1 + f x) with hνdef
  have hfi1 : Integrable (fun x => 1 + f x) μ := (integrable_const 1).add hf
  haveI : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hfi1.2
  set g : ℝ → ℝ := fun x => 1 / (1 + f x) with hgdef
  have hgm : Measurable g := measurable_const.div (measurable_const.add hfm)
  have hg0 : ∀ x, 0 ≤ g x := fun x => by have := hf0 x; positivity
  have hg1 : ∀ x, g x ≤ 1 := fun x => by
    have := hf0 x; rw [hgdef]; simp only; rw [div_le_one (by linarith)]; linarith
  have hB := poltoratski_bounded ν hgm hg0 hg1
  -- `μ ≪ ν`
  have hμν : μ ≪ ν := by
    intro S hS
    rw [hνdef] at hS
    have h1 := withDensity_apply_le (μ := μ) (fun x => ENNReal.ofReal (1 + f x)) S
    have h2 : ∫⁻ x in S, ENNReal.ofReal (1 + f x) ∂μ = 0 := le_antisymm (h1.trans hS.le) zero_le
    have h3 : ∫⁻ x in S, 1 ∂μ ≤ ∫⁻ x in S, ENNReal.ofReal (1 + f x) ∂μ :=
      lintegral_mono fun x => by
        rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by linarith [hf0 x])
    rw [h2, lintegral_const, one_mul, Measure.restrict_apply_univ, nonpos_iff_eq_zero] at h3
    exact h3
  have hBμ : ∀ᵐ E ∂μ, Tendsto (fun ε : ℝ => (borelTransform ν (E + ε * I)).im) (𝓝[>] 0)
      atTop → Tendsto (fun ε : ℝ => borelTransformDensity ν g (E + ε * I) /
        borelTransform ν (E + ε * I)) (𝓝[>] 0) (𝓝 (g E : ℂ)) := hμν.ae_le hB
  have hsing : μ.singularPart volume ≪ μ :=
    Measure.absolutelyContinuous_of_le (Measure.singularPart_le μ volume)
  have hImμ : ∀ᵐ E ∂(μ.singularPart volume),
      Tendsto (fun ε : ℝ => (borelTransform μ (E + ε * I)).im) (𝓝[>] 0) atTop := by
    rw [ae_iff]; exact singularPart_not_tendsto_atTop μ
  -- identities for the Borel transforms
  have hFν : ∀ z : ℂ, z.im ≠ 0 → borelTransform ν z =
      borelTransform μ z + borelTransformDensity μ f z := by
    intro z hz
    unfold borelTransform borelTransformDensity
    rw [hνdef, integral_withDensity_eq_integral_toReal_smul
      (measurable_const.add hfm).ennreal_ofReal (Eventually.of_forall fun x => ENNReal.ofReal_lt_top),
      ← integral_add (integrable_inv_sub μ hz) (integrable_density_inv_sub μ hf hz)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Complex.real_smul]
    rw [ENNReal.toReal_ofReal (by linarith [hf0 x])]
    push_cast; ring
  have hgν : ∀ z : ℂ, z.im ≠ 0 → borelTransformDensity ν g z = borelTransform μ z := by
    intro z hz
    unfold borelTransform borelTransformDensity
    rw [hνdef, integral_withDensity_eq_integral_toReal_smul
      (measurable_const.add hfm).ennreal_ofReal (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Complex.real_smul]
    have hx : 0 < 1 + f x := by linarith [hf0 x]
    rw [ENNReal.toReal_ofReal hx.le, hgdef]
    simp only
    push_cast
    field_simp
  filter_upwards [hsing.ae_le hBμ, hImμ] with E hE hIm
  -- `Im F_ν ≥ Im F_μ → ∞`
  have hImν : Tendsto (fun ε : ℝ => (borelTransform ν (E + ε * I)).im) (𝓝[>] 0) atTop := by
    refine tendsto_atTop_mono' _ ?_ hIm
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    have hz : ((E : ℂ) + ε * I).im ≠ 0 := by simpa using hε.ne'
    rw [hFν _ hz, Complex.add_im, borelTransformDensity_im μ hf E hε]
    have : 0 ≤ ∫ x, f x * poissonKernel ε (x - E) ∂μ :=
      integral_nonneg fun x => mul_nonneg (hf0 x) (poissonKernel_nonneg hε.le _)
    have := Real.pi_pos
    nlinarith
  have h1 := hE hImν
  -- `F_μ / F_ν → 1 / (1 + f E)`, hence `F_{fμ} / F_μ = F_ν / F_μ - 1 → f E`
  have hgE : (g E : ℂ) ≠ 0 := by
    have := hf0 E
    rw [hgdef]; simp only; push_cast
    exact div_ne_zero one_ne_zero (by
      intro h; have := congrArg Complex.re h; simp at this; linarith)
  have h2 := h1.inv₀ hgE
  have h3 := h2.sub_const 1
  have hval : ((g E : ℂ))⁻¹ - 1 = (f E : ℂ) := by
    rw [hgdef]; simp only; push_cast
    have : (1 : ℂ) + f E ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith [hf0 E]
    field_simp
    ring
  rw [hval] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have hz : ((E : ℂ) + ε * I).im ≠ 0 := by simpa using hε.ne'
  have hz' : 0 < ((E : ℂ) + ε * I).im := by simpa using hε
  rw [hgν _ hz, hFν _ hz]
  have hF0 : borelTransform μ (E + ε * I) ≠ 0 := by
    intro h0
    have := borelTransform_im_pos μ (fun h => by
      rw [h] at hIm
      exact absurd hIm (by simp [borelTransform])) hz'
    rw [h0, Complex.zero_im] at this
    exact lt_irrefl _ this
  field_simp
  ring

/-- **Theorem 1.10.1** (Poltoratski's theorem). -/
theorem poltoratskiStatement_holds : PoltoratskiStatement := by
  intro μ hμfin _ f hf
  haveI := hμfin
  -- a measurable representative
  set f' := hf.1.mk f with hf'def
  have hf'm : Measurable f' := hf.1.stronglyMeasurable_mk.measurable
  have hff' : f =ᵐ[μ] f' := hf.1.ae_eq_mk
  have hf' : Integrable f' μ := hf.congr hff'
  set fp : ℝ → ℝ := fun x => max (f' x) 0
  set fn : ℝ → ℝ := fun x => max (-f' x) 0
  have hfpm : Measurable fp := hf'm.max measurable_const
  have hfnm : Measurable fn := hf'm.neg.max measurable_const
  have hfp : Integrable fp μ := hf'.pos_part
  have hfn : Integrable fn μ := hf'.neg_part
  have hP := poltoratski_nonneg μ hfpm (fun x => le_max_right _ _) hfp
  have hN := poltoratski_nonneg μ hfnm (fun x => le_max_right _ _) hfn
  have hsing : μ.singularPart volume ≪ μ :=
    Measure.absolutelyContinuous_of_le (Measure.singularPart_le μ volume)
  filter_upwards [hP, hN, hsing.ae_le hff'] with E hEp hEn hEf
  have h := hEp.sub hEn
  have hval : ((fp E : ℝ) : ℂ) - (fn E : ℂ) = (f E : ℂ) := by
    rw [hEf]
    simp only [fp, fn]
    push_cast
    rcases le_total 0 (f' E) with h0 | h0
    · rw [max_eq_left h0, max_eq_right (by linarith)]; push_cast; ring
    · rw [max_eq_right h0, max_eq_left (by linarith)]; push_cast; ring
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have hz : ((E : ℂ) + ε * I).im ≠ 0 := by simpa using hε.ne'
  have hsplit : borelTransformDensity μ f (E + ε * I) =
      borelTransformDensity μ fp (E + ε * I) - borelTransformDensity μ fn (E + ε * I) := by
    rw [borelTransformDensity_congr_ae μ hff', ← borelTransformDensity_sub μ hfp hfn hz]
    congr 1
    funext x
    simp only [fp, fn]
    rcases le_total 0 (f' x) with h0 | h0
    · rw [max_eq_left h0, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h0, max_eq_left (by linarith)]; ring
  rw [hsplit, sub_div]

end DF
