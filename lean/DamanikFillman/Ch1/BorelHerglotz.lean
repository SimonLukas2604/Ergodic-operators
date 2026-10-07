/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators, I*,
§1.9.1 (pp. 81–85): the Herglotz representation theorem and boundary values of `Re F_μ`.

# Main definitions

* `DF.herglotzRho a b ρ z = a + b z + ∫ (1 + x z)/(x - z) dρ(x)` — the Herglotz representation
  written with the *finite* measure `ρ = (1 + x²)⁻¹ μ` (this is the form produced directly by the
  Carathéodory representation, cf. the computation on p. 83);
* `DF.cayley z = i (1 - z)/(1 + z)` — the conformal map `𝔻 → ℂ₊` of (1.9.15), and its inverse
  `DF.cayleyInv`.

# Main results

* `DF.isHerglotz_herglotzRho`, `DF.exists_herglotzRho` — Theorem 1.9.2 in the `ρ`-form;
* `DF.herglotzRepresentationStatement_holds` — Theorem 1.9.2 (Herglotz representation) as
  stated in the book (with the correction "`b > 0` or `μ ≠ 0`", see
  `DF.HerglotzRepresentationStatement`);
* `DF.ae_exists_tendsto_im_herglotz` — the imaginary part of any Herglotz function has finite
  boundary values Lebesgue-a.e. (Theorem 1.9.4(a) for measures satisfying (1.9.11));
* `DF.isHerglotz_sqrt`, `DF.isHerglotz_I_mul_sqrt` — `√F` and `i √F` are Herglotz (p. 85);
* `DF.reBoundaryValueStatement_holds` — Theorem 1.9.4(d), Lebesgue part: `Re F_μ(E + i0)`
  exists and is finite for Lebesgue-a.e. `E`;
* `DF.rankOne_acParts_equiv'` — Proposition 1.9.9, first bullet, now unconditional.
-/
import DamanikFillman.Ch1.BorelCaratheodory
import DamanikFillman.Ch1.BorelBoundary

noncomputable section

open MeasureTheory Filter Topology Set Metric Complex
open scoped ENNReal NNReal

namespace DF

/-! ## The kernel `(1 + x z)/(x - z)` -/

lemma ofReal_sub_ne_zero (x : ℝ) {z : ℂ} (hz : 0 < z.im) : (x : ℂ) - z ≠ 0 := by
  intro h; have := congrArg Complex.im h; simp at this; linarith

lemma herglotz_kernel_eq (x : ℝ) {z : ℂ} (hz : 0 < z.im) :
    (1 + x * z) / (x - z) = z + (1 + z ^ 2) * ((x : ℂ) - z)⁻¹ := by
  have := ofReal_sub_ne_zero x hz
  field_simp; ring

lemma im_herglotz_kernel (x : ℝ) (z : ℂ) :
    ((1 + x * z) / (x - z)).im = (1 + x ^ 2) * z.im / Complex.normSq (x - z) := by
  rw [Complex.div_im, ← sub_div]
  congr 1
  simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_re, Complex.one_re, Complex.mul_re, Complex.sub_re,
    Complex.sub_im]
  ring

lemma norm_herglotz_kernel_le (x : ℝ) {z : ℂ} (hz : 0 < z.im) :
    ‖(1 + x * z) / (x - z)‖ ≤ ‖z‖ + ‖1 + z ^ 2‖ / z.im := by
  rw [herglotz_kernel_eq x hz]
  refine (norm_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [norm_mul, norm_inv, ← div_eq_mul_inv]
  apply div_le_div_of_nonneg_left (norm_nonneg _) hz
  calc z.im = |((x : ℂ) - z).im| := by simp [abs_of_pos hz]
    _ ≤ ‖(x : ℂ) - z‖ := Complex.abs_im_le_norm _

lemma integrable_herglotz_kernel_rho (ρ : Measure ℝ) [IsFiniteMeasure ρ] {z : ℂ}
    (hz : 0 < z.im) : Integrable (fun x : ℝ => (1 + x * z) / (x - z)) ρ := by
  refine Integrable.of_bound (C := ‖z‖ + ‖1 + z ^ 2‖ / z.im) ?_
    (Eventually.of_forall fun x => norm_herglotz_kernel_le x hz)
  exact (Continuous.div (by fun_prop) (by fun_prop)
    fun x => ofReal_sub_ne_zero x hz).aestronglyMeasurable

/-- The Herglotz representation in terms of a finite measure `ρ`:
`a + b z + ∫ (1 + x z)/(x - z) dρ(x)`. -/
def herglotzRho (a b : ℝ) (ρ : Measure ℝ) (z : ℂ) : ℂ :=
  a + b * z + ∫ x, (1 + x * z) / (x - z) ∂ρ

lemma integral_herglotz_kernel_eq (ρ : Measure ℝ) [IsFiniteMeasure ρ] {z : ℂ} (hz : 0 < z.im) :
    ∫ x, (1 + x * z) / (x - z) ∂ρ = ρ.real univ * z + (1 + z ^ 2) * borelTransform ρ z := by
  have hz' : z.im ≠ 0 := hz.ne'
  rw [integral_congr_ae (Eventually.of_forall fun x => herglotz_kernel_eq x hz),
    integral_add (integrable_const _) ((integrable_inv_sub ρ hz').const_mul _),
    integral_const, integral_const_mul]
  simp [borelTransform, Complex.real_smul]

lemma im_herglotzRho (a b : ℝ) (ρ : Measure ℝ) [IsFiniteMeasure ρ] {z : ℂ} (hz : 0 < z.im) :
    (herglotzRho a b ρ z).im =
      b * z.im + ∫ x, (1 + x ^ 2) * z.im / Complex.normSq (x - z) ∂ρ := by
  unfold herglotzRho
  have h := integral_im (integrable_herglotz_kernel_rho ρ hz)
  simp only [RCLike.im_to_complex] at h
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, zero_mul,
    add_zero, zero_add]
  rw [← h]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  exact im_herglotz_kernel x z

/-- Theorem 1.9.2, "if" direction, in the `ρ`-form. -/
theorem isHerglotz_herglotzRho (a b : ℝ) (ρ : Measure ℝ) [IsFiniteMeasure ρ] (hb : 0 ≤ b)
    (hne : b ≠ 0 ∨ ρ ≠ 0) : IsHerglotz (herglotzRho a b ρ) := by
  constructor
  · have h : DifferentiableOn ℂ (fun z => (a : ℂ) + b * z + (ρ.real univ * z +
        (1 + z ^ 2) * borelTransform ρ z)) {z | 0 < z.im} := by
      apply DifferentiableOn.add (by fun_prop)
      apply DifferentiableOn.add (by fun_prop)
      exact DifferentiableOn.mul (by fun_prop) (differentiableOn_borelTransform ρ)
    refine h.congr fun z hz => ?_
    simp only [herglotzRho]
    rw [integral_herglotz_kernel_eq ρ hz]
  · intro z hz
    rw [im_herglotzRho a b ρ hz]
    have hint : Integrable (fun x : ℝ => (1 + x ^ 2) * z.im / Complex.normSq (x - z)) ρ := by
      have h := (integrable_herglotz_kernel_rho ρ hz).im
      refine h.congr (Eventually.of_forall fun x => ?_)
      simp only [RCLike.im_to_complex]
      exact im_herglotz_kernel x z
    have hpos : ∀ x : ℝ, 0 < (1 + x ^ 2) * z.im / Complex.normSq (x - z) := fun x =>
      div_pos (by positivity) (Complex.normSq_pos.2 (ofReal_sub_ne_zero x hz))
    rcases hne with hb0 | hρ
    · have h1 : 0 < b * z.im := mul_pos (lt_of_le_of_ne hb hb0.symm) hz
      have h2 : 0 ≤ ∫ x, (1 + x ^ 2) * z.im / Complex.normSq (x - z) ∂ρ :=
        integral_nonneg fun x => (hpos x).le
      linarith
    · have h2 : 0 < ∫ x, (1 + x ^ 2) * z.im / Complex.normSq (x - z) ∂ρ := by
        rw [integral_pos_iff_support_of_nonneg (fun x => (hpos x).le) hint]
        have : Function.support (fun x : ℝ => (1 + x ^ 2) * z.im / Complex.normSq (x - z)) =
            univ := by
          ext x; simp only [Function.mem_support, mem_univ, iff_true]; exact (hpos x).ne'
        rw [this, Measure.measure_univ_pos]; exact hρ
      have h1 : 0 ≤ b * z.im := mul_nonneg hb hz.le
      linarith

/-! ## The Cayley transform -/

/-- The conformal map `A z = i (1 - z)/(1 + z)` from the unit disk to `ℂ₊` (1.9.15). -/
def cayley (z : ℂ) : ℂ := I * (1 - z) / (1 + z)

/-- The inverse Cayley map `ζ ↦ (i - ζ)/(i + ζ)`. -/
def cayleyInv (ζ : ℂ) : ℂ := (I - ζ) / (I + ζ)

lemma I_add_ne_zero {ζ : ℂ} (hζ : 0 < ζ.im) : I + ζ ≠ 0 := by
  intro h; have := congrArg Complex.im h; simp at this; linarith

lemma one_add_ne_zero_of_mem_ball {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : 1 + z ≠ 0 := by
  intro h
  have : z = -1 := by linear_combination h
  rw [this] at hz; simp at hz

lemma cayleyInv_mem_ball {ζ : ℂ} (hζ : 0 < ζ.im) : cayleyInv ζ ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_iff_norm, sub_zero, cayleyInv, norm_div,
    div_lt_one (norm_pos_iff.2 (I_add_ne_zero hζ))]
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.I_re, Complex.sub_im, Complex.I_im, Complex.add_re,
    Complex.add_im]
  nlinarith

lemma cayley_cayleyInv {ζ : ℂ} (hζ : 0 < ζ.im) : cayley (cayleyInv ζ) = ζ := by
  have h1 := I_add_ne_zero hζ
  have h2 : 1 + cayleyInv ζ ≠ 0 := one_add_ne_zero_of_mem_ball (cayleyInv_mem_ball hζ)
  unfold cayley
  rw [div_eq_iff h2]
  unfold cayleyInv
  field_simp
  ring_nf

lemma im_cayley_pos {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) : 0 < (cayley z).im := by
  have h1 := one_add_ne_zero_of_mem_ball hz
  have hz1 : ‖z‖ < 1 := by simpa using hz
  have : (cayley z).im = ((1 + -z) / (1 - -z)).re := by
    unfold cayley
    rw [mul_div_assoc, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
    congr 2; ring
  rw [this, DF.re_herglotz_kernel, Complex.normSq_one, Complex.normSq_neg]
  apply div_pos
  · rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  · apply Complex.normSq_pos.2; rwa [sub_neg_eq_add]

lemma differentiableOn_cayley : DifferentiableOn ℂ cayley (ball 0 1) := by
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  unfold cayley
  exact DifferentiableAt.div (by fun_prop) (by fun_prop) (one_add_ne_zero_of_mem_ball hz)

/-- On the unit circle (minus `-1`), `w = cayleyInv x` for the real number
`x = Im w / (1 + Re w)`. -/
lemma eq_cayleyInv_of_mem_sphere {w : ℂ} (hw : ‖w‖ = 1) (hw1 : w ≠ -1) :
    w = cayleyInv (w.im / (1 + w.re) : ℝ) := by
  have hsq : w.re ^ 2 + w.im ^ 2 = 1 := by
    have := Complex.normSq_eq_norm_sq w
    rw [hw, Complex.normSq_apply] at this; nlinarith
  have hre : 0 < 1 + w.re := by
    rcases lt_or_eq_of_le (show -1 ≤ w.re by nlinarith [sq_nonneg w.im]) with h | h
    · linarith
    · exfalso; apply hw1
      have him : w.im = 0 := by nlinarith
      apply Complex.ext <;> simp [← h, him]
  set x : ℝ := w.im / (1 + w.re)
  have hI : I + (x : ℂ) ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this
  unfold cayleyInv
  rw [eq_div_iff hI]
  have hx : x * (1 + w.re) = w.im := by simp only [x]; field_simp
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.add_re, Complex.I_re, Complex.ofReal_re, Complex.add_im,
      Complex.I_im, Complex.ofReal_im, Complex.sub_re]
    nlinarith
  · simp only [Complex.mul_im, Complex.add_re, Complex.I_re, Complex.ofReal_re, Complex.add_im,
      Complex.I_im, Complex.ofReal_im, Complex.sub_im]
    have : w.re + w.im * x = 1 := by
      have h2 : w.im * x * (1 + w.re) = w.im ^ 2 := by rw [mul_assoc, hx]; ring
      have h3 : (w.re + w.im * x) * (1 + w.re) = 1 * (1 + w.re) := by nlinarith
      exact mul_right_cancel₀ hre.ne' h3
    linarith

/-- The kernel identity behind the change of variables on p. 83:
`i (A⁻¹x + A⁻¹ζ)/(A⁻¹x - A⁻¹ζ) = (1 + x ζ)/(x - ζ)`. -/
lemma kernel_cayleyInv (x : ℝ) {ζ : ℂ} (hζ : 0 < ζ.im) :
    I * ((cayleyInv x + cayleyInv ζ) / (cayleyInv x - cayleyInv ζ)) = (1 + x * ζ) / (x - ζ) := by
  have h1 := I_add_ne_zero hζ
  have h2 : I + (x : ℂ) ≠ 0 := by intro h; have := congrArg Complex.im h; simp at this
  have h3 := ofReal_sub_ne_zero x hζ
  have h4 : cayleyInv x - cayleyInv ζ ≠ 0 := by
    unfold cayleyInv
    rw [div_sub_div _ _ h2 h1]
    refine div_ne_zero ?_ (mul_ne_zero h2 h1)
    intro h0
    have : (2 * I) * ((x : ℂ) - ζ) = 0 := by linear_combination -h0
    rcases mul_eq_zero.1 this with h | h
    · simp at h
    · exact h3 h
  rw [mul_div_assoc', div_eq_div_iff h4 h3]
  unfold cayleyInv
  field_simp
  ring_nf
  rw [show I ^ 3 = -I by rw [pow_succ, I_sq]; ring]
  ring

lemma kernel_at_neg_one {ζ : ℂ} (hζ : 0 < ζ.im) :
    I * ((-1 + cayleyInv ζ) / (-1 - cayleyInv ζ)) = ζ := by
  have h1 := I_add_ne_zero hζ
  have h2 : -1 - cayleyInv ζ ≠ 0 := by
    intro h
    have : cayleyInv ζ = -1 := by linear_combination -h
    have h' := cayleyInv_mem_ball hζ
    rw [this] at h'; simp at h'
  rw [mul_div_assoc', div_eq_iff h2]
  unfold cayleyInv
  field_simp
  ring_nf

/-! ## Theorem 1.9.2 -/

/-- Theorem 1.9.2, "only if" direction, in the `ρ`-form: every Herglotz function is of the form
`a + b z + ∫ (1 + x z)/(x - z) dρ(x)` with `ρ` a finite measure. -/
theorem exists_herglotzRho (F : ℂ → ℂ) (hF : IsHerglotz F) :
    ∃ (a b : ℝ) (ρ : Measure ℝ), IsFiniteMeasure ρ ∧ 0 ≤ b ∧ (b ≠ 0 ∨ ρ ≠ 0) ∧
      ∀ z : ℂ, 0 < z.im → F z = herglotzRho a b ρ z := by
  set G : ℂ → ℂ := fun z => -I * F (cayley z)
  have hmaps : MapsTo cayley (ball 0 1) {z | 0 < z.im} := fun z hz => im_cayley_pos hz
  have hG : DifferentiableOn ℂ G (ball 0 1) :=
    (differentiableOn_const _).mul (hF.1.comp differentiableOn_cayley hmaps)
  have hGpos : ∀ z ∈ ball (0 : ℂ) 1, 0 < (G z).re := by
    intro z hz
    have h := hF.2 _ (im_cayley_pos hz)
    simpa [G] using h
  obtain ⟨c, ν, hfin, hν0, hsupp, hrep⟩ := caratheodory_repr G hG hGpos
  set ρ : Measure ℝ := (ν.restrict {(-1 : ℂ)}ᶜ).map fun w => w.im / (1 + w.re)
  have hmeasAr : Measurable fun w : ℂ => w.im / (1 + w.re) := by fun_prop
  have hρfin : IsFiniteMeasure ρ := inferInstance
  refine ⟨-c, ν.real {(-1 : ℂ)}, ρ, hρfin, measureReal_nonneg, ?_, fun ζ hζ => ?_⟩
  · by_contra h
    rw [not_or, not_not, not_not] at h
    obtain ⟨hb, hρ⟩ := h
    apply hν0
    have h1 : ν {(-1 : ℂ)} = 0 := by
      rw [Measure.real, ENNReal.toReal_eq_zero_iff] at hb
      exact hb.resolve_right (measure_ne_top _ _)
    have h2 : ν {(-1 : ℂ)}ᶜ = 0 := by
      have := congrArg (fun m : Measure ℝ => m univ) hρ
      simp only [ρ, Measure.map_apply hmeasAr MeasurableSet.univ, preimage_univ,
        Measure.restrict_apply MeasurableSet.univ, univ_inter, Measure.coe_zero,
        Pi.zero_apply] at this
      exact this
    rw [← Measure.measure_univ_eq_zero, ← union_compl_self {(-1 : ℂ)}]
    exact measure_union_null h1 h2
  · -- `F ζ = i G(A⁻¹ ζ)`
    set u := cayleyInv ζ
    have hu : u ∈ ball (0 : ℂ) 1 := cayleyInv_mem_ball hζ
    have hFζ : F ζ = I * G u := by
      simp only [G, u, cayley_cayleyInv hζ]
      ring_nf; simp [I_sq]
    rw [hFζ, hrep u hu, mul_add, ← integral_const_mul]
    have hint : Integrable (fun w => I * ((w + u) / (w - u))) ν :=
      (integrable_herglotz_kernel ν hsupp hu).const_mul I
    rw [← integral_add_compl (measurableSet_singleton (-1 : ℂ)) hint, integral_singleton,
      kernel_at_neg_one hζ]
    have hcompl : ∫ w in {(-1 : ℂ)}ᶜ, I * ((w + u) / (w - u)) ∂ν =
        ∫ x, (1 + x * ζ) / (x - ζ) ∂ρ := by
      simp only [ρ]
      rw [integral_map hmeasAr.aemeasurable (Continuous.aestronglyMeasurable
        (f := fun x : ℝ => (1 + (x : ℂ) * ζ) / ((x : ℂ) - ζ))
        (Continuous.div (by fun_prop) (by fun_prop) fun x => ofReal_sub_ne_zero x hζ))]
      apply integral_congr_ae
      have hs : ∀ᵐ w ∂(ν.restrict {(-1 : ℂ)}ᶜ), w ∈ sphere (0 : ℂ) 1 ∧ w ≠ -1 := by
        rw [ae_restrict_iff' (measurableSet_singleton _).compl]
        filter_upwards [ae_mem_sphere hsupp] with w hw hw1
        exact ⟨hw, hw1⟩
      filter_upwards [hs] with w ⟨hw, hw1⟩
      have hw' : ‖w‖ = 1 := by simpa using hw
      have := eq_cayleyInv_of_mem_sphere hw' hw1
      conv_lhs => rw [this]
      exact kernel_cayleyInv _ hζ
    rw [hcompl]
    simp only [herglotzRho, Complex.real_smul]
    ring_nf
    simp [I_sq]
    ring

/-- The density change between the `μ`-form and the `ρ`-form of the representation. -/
lemma integral_kernel_withDensity (ρ : Measure ℝ) [IsFiniteMeasure ρ] {z : ℂ} (hz : 0 < z.im) :
    ∫ x, (((x : ℂ) - z)⁻¹ - (x : ℂ) / (1 + (x : ℂ) ^ 2))
        ∂(ρ.withDensity fun x => ENNReal.ofReal (1 + x ^ 2)) =
      ∫ x, (1 + x * z) / (x - z) ∂ρ := by
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (by positivity), Complex.real_smul]
  have h1 := ofReal_sub_ne_zero x hz
  have h2 : (1 + (x : ℂ) ^ 2) ≠ 0 := by
    have : (0 : ℝ) < 1 + x ^ 2 := by positivity
    exact_mod_cast this.ne'
  push_cast
  field_simp
  ring

lemma integrable_inv_one_add_sq_withDensity (ρ : Measure ℝ) [IsFiniteMeasure ρ] :
    Integrable (fun x : ℝ => 1 / (1 + x ^ 2))
      (ρ.withDensity fun x => ENNReal.ofReal (1 + x ^ 2)) := by
  refine ⟨(by fun_prop : Measurable fun x : ℝ => 1 / (1 + x ^ 2)).aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral, lintegral_withDensity_eq_lintegral_mul _ (by fun_prop) (by fun_prop)]
  have : ∀ x : ℝ, (((fun x : ℝ => ENNReal.ofReal (1 + x ^ 2)) *
      fun x : ℝ => ‖1 / (1 + x ^ 2)‖ₑ) : ℝ → ℝ≥0∞) x = 1 :=
    fun x => by
      simp only [Pi.mul_apply]
      rw [← ofReal_norm, Real.norm_of_nonneg (by positivity), ← ENNReal.ofReal_mul (by positivity)]
      have : (1 + x ^ 2) * (1 / (1 + x ^ 2)) = 1 := by field_simp
      rw [this, ENNReal.ofReal_one]
  rw [lintegral_congr this, lintegral_const, one_mul]
  exact measure_lt_top _ _

/-- Theorem 1.9.2 (Herglotz representation), in the book's form (with the correction that one
needs `b > 0` or `μ ≠ 0`). -/
theorem herglotzRepresentationStatement_holds : HerglotzRepresentationStatement := by
  intro F
  constructor
  · intro hF
    obtain ⟨a, b, ρ, hρ, hb, hne, hrep⟩ := exists_herglotzRho F hF
    refine ⟨a, b, ρ.withDensity fun x => ENNReal.ofReal (1 + x ^ 2), hb, ?_,
      integrable_inv_one_add_sq_withDensity ρ, fun z hz => ?_⟩
    · rcases hne with h | h
      · exact Or.inl h
      · right
        intro h0
        apply h
        rw [← Measure.measure_univ_eq_zero]
        have := congrArg (fun m : Measure ℝ => m univ) h0
        simp only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
          Measure.coe_zero, Pi.zero_apply] at this
        refine le_antisymm ?_ bot_le
        calc ρ univ = ∫⁻ _, 1 ∂ρ := by simp
          _ ≤ ∫⁻ x, ENNReal.ofReal (1 + x ^ 2) ∂ρ := by
              apply lintegral_mono; intro x
              rw [← ENNReal.ofReal_one]; apply ENNReal.ofReal_le_ofReal; nlinarith [sq_nonneg x]
          _ = 0 := this
    · rw [hrep z hz, herglotzRho, integral_kernel_withDensity ρ hz]
  · rintro ⟨a, b, μ, hb, hne, hint, hrep⟩
    -- pass to the finite measure `ρ = (1 + x²)⁻¹ μ`
    set ρ := μ.withDensity fun x => ENNReal.ofReal (1 / (1 + x ^ 2))
    have hρ : IsFiniteMeasure ρ := isFiniteMeasure_withDensity_ofReal hint.2
    have hμρ : ρ.withDensity (fun x => ENNReal.ofReal (1 + x ^ 2)) = μ := by
      simp only [ρ]
      rw [← withDensity_mul _ (by fun_prop) (by fun_prop)]
      conv_rhs => rw [← withDensity_one (μ := μ)]
      congr 1
      ext x
      simp only [Pi.mul_apply, Pi.one_apply]
      rw [← ENNReal.ofReal_mul (by positivity)]
      have : 1 / (1 + x ^ 2) * (1 + x ^ 2) = 1 := by field_simp
      rw [this, ENNReal.ofReal_one]
    have hne' : b ≠ 0 ∨ ρ ≠ 0 := by
      rcases hne with h | h
      · exact Or.inl h
      · right; intro h0; apply h; rw [← hμρ, h0]; simp
    have hH := isHerglotz_herglotzRho a b ρ hb hne'
    refine ⟨hH.1.congr fun z hz => ?_, fun z hz => ?_⟩
    · rw [hrep z hz, herglotzRho, ← integral_kernel_withDensity ρ hz, hμρ]
    · rw [hrep z hz, ← hμρ, integral_kernel_withDensity ρ hz]
      exact hH.2 z hz

/-! ## Boundary values of the imaginary part of a Herglotz function -/

lemma im_herglotzRho_eq (a b : ℝ) (ρ : Measure ℝ) [IsFiniteMeasure ρ] (E : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    (herglotzRho a b ρ (E + ε * I)).im =
      b * ε + ∫ x, (1 + x ^ 2) * (ε / ((x - E) ^ 2 + ε ^ 2)) ∂ρ := by
  rw [im_herglotzRho a b ρ (by simpa using hε)]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  rw [Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.add_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, Complex.sub_im, Complex.add_im, Complex.mul_im]
  ring_nf

/-- Theorem 1.9.4(a) for an arbitrary Herglotz function (equivalently, for measures `μ`
satisfying (1.9.11)): `Im F(E + iε)` has a finite limit as `ε ↓ 0` for Lebesgue-a.e. `E`. -/
theorem ae_exists_tendsto_im_herglotzRho (a b : ℝ) (ρ : Measure ℝ) [IsFiniteMeasure ρ] :
    ∀ᵐ (E : ℝ) ∂volume, ∃ y : ℝ,
      Tendsto (fun ε : ℝ => (herglotzRho a b ρ (E + ε * I)).im) (𝓝[>] 0) (𝓝 y) := by
  -- localized finite measures `ν_n = (1 + x²) ρ|_{(-(n+1), n+1)}`
  let J : ℕ → Set ℝ := fun n => Ioo (-((n : ℝ) + 1)) ((n : ℝ) + 1)
  let ν : ℕ → Measure ℝ := fun n =>
    (ρ.restrict (J n)).withDensity fun x => ENNReal.ofReal (1 + x ^ 2)
  have hνfin : ∀ n, IsFiniteMeasure (ν n) := fun n => by
    apply isFiniteMeasure_withDensity_ofReal
    refine (Integrable.of_bound (C := 1 + ((n : ℝ) + 1) ^ 2) (by fun_prop) ?_).2
    rw [ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with x hx
    rw [Real.norm_of_nonneg (by positivity)]
    have : x ^ 2 ≤ ((n : ℝ) + 1) ^ 2 := by
      rw [← sq_abs x]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_lt.2 hx).le 2
    linarith
  have hgood : ∀ᵐ (E : ℝ) ∂volume, ∀ n, ∃ y : ℝ,
      Tendsto (fun ε : ℝ => (borelTransform (ν n) (E + ε * I)).im) (𝓝[>] 0) (𝓝 y) := by
    rw [ae_all_iff]
    intro n
    filter_upwards [ae_tendsto_im_volume (ν n)] with E hE using ⟨_, hE⟩
  filter_upwards [hgood] with E hE
  obtain ⟨n, hn⟩ := exists_nat_gt |E|
  obtain ⟨y, hy⟩ := hE n
  refine ⟨y, ?_⟩
  -- decomposition `Im F = b ε + Im F_{ν_n} + tail`
  have hdec : ∀ ε : ℝ, 0 < ε → (herglotzRho a b ρ (E + ε * I)).im =
      b * ε + (borelTransform (ν n) (E + ε * I)).im +
        ∫ x in (J n)ᶜ, (1 + x ^ 2) * (ε / ((x - E) ^ 2 + ε ^ 2)) ∂ρ := by
    intro ε hε
    have hint : Integrable (fun x : ℝ => (1 + x ^ 2) * (ε / ((x - E) ^ 2 + ε ^ 2))) ρ := by
      refine Integrable.of_bound (C := ε * (2 + (2 * E ^ 2 + 1) / ε ^ 2)) (by fun_prop)
        (Eventually.of_forall fun x => ?_)
      rw [Real.norm_of_nonneg (by positivity)]
      have hq : 0 < (x - E) ^ 2 + ε ^ 2 := by positivity
      rw [mul_div_assoc', div_le_iff₀ hq]
      have : 1 + x ^ 2 ≤ (2 + (2 * E ^ 2 + 1) / ε ^ 2) * ((x - E) ^ 2 + ε ^ 2) := by
        have h1 : (2 * E ^ 2 + 1) / ε ^ 2 * ε ^ 2 = 2 * E ^ 2 + 1 := by field_simp
        nlinarith [sq_nonneg (x - 2 * E), sq_nonneg (x - E), sq_nonneg E,
          div_nonneg (by positivity : (0 : ℝ) ≤ 2 * E ^ 2 + 1) (sq_nonneg ε),
          mul_nonneg (div_nonneg (by positivity : (0 : ℝ) ≤ 2 * E ^ 2 + 1) (sq_nonneg ε))
            (sq_nonneg (x - E))]
      nlinarith
    rw [im_herglotzRho_eq a b ρ E hε, borelTransform_im (ν n) E hε.ne', add_assoc]
    congr 1
    rw [← integral_add_compl measurableSet_Ioo hint]
    congr 1
    simp only [ν]
    rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards with x
    rw [ENNReal.toReal_ofReal (by positivity), smul_eq_mul]
  -- the tail vanishes
  have htail : Tendsto (fun ε => ∫ x in (J n)ᶜ, (1 + x ^ 2) * (ε / ((x - E) ^ 2 + ε ^ 2)) ∂ρ)
      (𝓝[>] 0) (𝓝 0) := by
    have hK : ∀ ε : ℝ, 0 < ε → ∀ x ∈ (J n)ᶜ,
        (1 + x ^ 2) * (ε / ((x - E) ^ 2 + ε ^ 2)) ≤ ε * (2 * ((n : ℝ) + 1) ^ 2) := by
      intro ε hε x hx
      simp only [J, mem_compl_iff, mem_Ioo, not_and_or, not_lt] at hx
      have hx' : (n : ℝ) + 1 ≤ |x| := by
        rcases hx with h | h
        · rw [abs_of_neg (by linarith)]; linarith
        · rw [abs_of_pos (by linarith)]; exact h
      have hEn : |E| < n := hn
      have hd : |x| - n ≤ |x - E| := by
        have := abs_sub_abs_le_abs_sub x E; linarith
      have hd0 : 1 ≤ |x| - n := by linarith
      have h1 : |x| ≤ ((n : ℝ) + 1) * (|x| - n) := by nlinarith
      have h2 : 1 + x ^ 2 ≤ 2 * ((n : ℝ) + 1) ^ 2 * (x - E) ^ 2 := by
        have hx2 : x ^ 2 = |x| ^ 2 := (sq_abs x).symm
        have hxE : (x - E) ^ 2 = |x - E| ^ 2 := (sq_abs _).symm
        rw [hx2, hxE]
        have h3 : |x| ^ 2 ≤ ((n : ℝ) + 1) ^ 2 * (|x| - n) ^ 2 := by
          have := mul_self_le_mul_self (abs_nonneg x) h1; nlinarith
        have h4 : (|x| - n) ^ 2 ≤ |x - E| ^ 2 :=
          pow_le_pow_left₀ (by linarith) hd 2
        have h5 : 1 ≤ |x| ^ 2 := by nlinarith
        nlinarith
      have hq : 0 < (x - E) ^ 2 + ε ^ 2 := by positivity
      rw [mul_div_assoc', div_le_iff₀ hq]
      nlinarith [sq_nonneg ε, mul_pos hε (by positivity : (0 : ℝ) < 2 * ((n : ℝ) + 1) ^ 2)]
    have hup : ∀ ε : ℝ, 0 < ε →
        ∫ x in (J n)ᶜ, (1 + x ^ 2) * (ε / ((x - E) ^ 2 + ε ^ 2)) ∂ρ ≤
          ε * (2 * ((n : ℝ) + 1) ^ 2) * ρ.real univ := by
      intro ε hε
      calc ∫ x in (J n)ᶜ, (1 + x ^ 2) * (ε / ((x - E) ^ 2 + ε ^ 2)) ∂ρ
          ≤ ∫ _ in (J n)ᶜ, ε * (2 * ((n : ℝ) + 1) ^ 2) ∂ρ := by
            apply setIntegral_mono_on _ (integrable_const _) measurableSet_Ioo.compl (hK ε hε)
            refine Integrable.of_bound (C := ε * (2 * ((n : ℝ) + 1) ^ 2)) (by fun_prop) ?_
            rw [ae_restrict_iff' measurableSet_Ioo.compl]
            filter_upwards with x hx
            rw [Real.norm_of_nonneg (by positivity)]
            exact hK ε hε x hx
        _ = ε * (2 * ((n : ℝ) + 1) ^ 2) * ρ.real (J n)ᶜ := by
            rw [setIntegral_const, smul_eq_mul, mul_comm]
        _ ≤ ε * (2 * ((n : ℝ) + 1) ^ 2) * ρ.real univ := by
            exact mul_le_mul_of_nonneg_left (measureReal_mono (subset_univ _)
              (measure_ne_top ρ univ)) (by positivity)
    have hlim : Tendsto (fun ε : ℝ => ε * (2 * ((n : ℝ) + 1) ^ 2) * ρ.real univ) (𝓝[>] 0)
        (𝓝 0) := by
      have h : Continuous fun ε : ℝ => ε * (2 * ((n : ℝ) + 1) ^ 2) * ρ.real univ := by fun_prop
      simpa using (h.tendsto 0).mono_left nhdsWithin_le_nhds
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      exact setIntegral_nonneg measurableSet_Ioo.compl fun x _ => by positivity
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε) using hup ε hε
  have hb : Tendsto (fun ε : ℝ => b * ε) (𝓝[>] 0) (𝓝 0) := by
    have h : Continuous fun ε : ℝ => b * ε := by fun_prop
    simpa using (h.tendsto 0).mono_left nhdsWithin_le_nhds
  have := (hb.add hy).add htail
  simp only [zero_add, add_zero] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [hdec ε hε]

/-- Theorem 1.9.4(a) for Herglotz functions: `Im F(E + i0)` exists and is finite Lebesgue-a.e. -/
theorem ae_exists_tendsto_im_herglotz (F : ℂ → ℂ) (hF : IsHerglotz F) :
    ∀ᵐ (E : ℝ) ∂volume, ∃ y : ℝ,
      Tendsto (fun ε : ℝ => (F (E + ε * I)).im) (𝓝[>] 0) (𝓝 y) := by
  obtain ⟨a, b, ρ, hρ, -, -, hrep⟩ := exists_herglotzRho F hF
  filter_upwards [ae_exists_tendsto_im_herglotzRho a b ρ] with E ⟨y, hy⟩
  refine ⟨y, hy.congr' ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [hrep _ (by simpa using hε)]

/-! ## Square roots and Theorem 1.9.4(d) -/

lemma arg_mem_Ioo {w : ℂ} (hw : 0 < w.im) : 0 < Complex.arg w ∧ Complex.arg w < Real.pi := by
  refine ⟨lt_of_le_of_ne (Complex.arg_nonneg_iff.2 hw.le) ?_,
    Complex.arg_lt_pi_iff.2 (Or.inr hw.ne')⟩
  intro h
  have := Complex.arg_eq_zero_iff.1 h.symm
  linarith [this.2]

lemma sqrt_re_im_pos {w : ℂ} (hw : 0 < w.im) :
    0 < (w ^ (2⁻¹ : ℂ)).re ∧ 0 < (w ^ (2⁻¹ : ℂ)).im := by
  have hw0 : w ≠ 0 := by intro h; rw [h] at hw; simp at hw
  obtain ⟨h1, h2⟩ := arg_mem_Ioo hw
  have him : (Complex.log w * 2⁻¹).im = Complex.arg w / 2 := by
    rw [show (2⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) by push_cast; ring, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add, Complex.log_im]
    ring
  rw [Complex.cpow_def_of_ne_zero hw0, Complex.exp_re, Complex.exp_im, him]
  refine ⟨mul_pos (Real.exp_pos _) (Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩),
    mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))⟩

/-- `√F` is Herglotz for a Herglotz function `F` (principal branch; p. 85). -/
theorem isHerglotz_sqrt {F : ℂ → ℂ} (hF : IsHerglotz F) :
    IsHerglotz fun z => F z ^ (2⁻¹ : ℂ) := by
  refine ⟨fun z hz => ?_, fun z hz => (sqrt_re_im_pos (hF.2 z hz)).2⟩
  have hd : DifferentiableAt ℂ F z :=
    (hF.1 z hz).differentiableAt ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hz)
  exact (hd.cpow_const (Complex.mem_slitPlane_iff.2 (Or.inr (hF.2 z hz).ne'))).differentiableWithinAt

/-- `i √F` is Herglotz for a Herglotz function `F` (p. 85). -/
theorem isHerglotz_I_mul_sqrt {F : ℂ → ℂ} (hF : IsHerglotz F) :
    IsHerglotz fun z => I * F z ^ (2⁻¹ : ℂ) := by
  refine ⟨(differentiableOn_const _).mul (isHerglotz_sqrt hF).1, fun z hz => ?_⟩
  simp only [Complex.mul_im, Complex.I_re, zero_mul, Complex.I_im, one_mul, zero_add]
  exact (sqrt_re_im_pos (hF.2 z hz)).1

/-- Theorem 1.9.4(d), Lebesgue part: for a finite measure `μ`, `Re F_μ(E + i0)` exists and is
finite for Lebesgue-a.e. `E`. -/
theorem reBoundaryValueStatement_holds : ReBoundaryValueStatement := by
  intro μ hμ
  by_cases h0 : μ = 0
  · subst h0
    exact Eventually.of_forall fun E => ⟨0, by simp [borelTransform]⟩
  have hF := borelTransform_isHerglotz μ h0
  filter_upwards [ae_exists_tendsto_im_herglotz _ (isHerglotz_sqrt hF),
    ae_exists_tendsto_im_herglotz _ (isHerglotz_I_mul_sqrt hF)] with E ⟨y₁, h₁⟩ ⟨y₂, h₂⟩
  -- `√F(E + iε) → y₂ + i y₁`
  have hre : Tendsto (fun ε : ℝ => (borelTransform μ (E + ε * I) ^ (2⁻¹ : ℂ)).re) (𝓝[>] 0)
      (𝓝 y₂) := by
    refine h₂.congr fun ε => ?_
    simp only [Complex.mul_im, Complex.I_re, zero_mul, Complex.I_im, one_mul, zero_add]
  have hS : Tendsto (fun ε : ℝ => borelTransform μ (E + ε * I) ^ (2⁻¹ : ℂ)) (𝓝[>] 0)
      (𝓝 ((y₂ : ℂ) + y₁ * I)) := by
    have := ((Complex.continuous_ofReal.tendsto _).comp hre).add
      (((Complex.continuous_ofReal.tendsto _).comp h₁).mul_const I)
    refine this.congr fun ε => ?_
    simp only [Function.comp_apply]
    exact Complex.re_add_im _
  have hF2 := (hS.pow 2)
  simp only [Complex.cpow_ofNat_inv_pow] at hF2
  exact ⟨_, (Complex.continuous_re.tendsto _).comp hF2⟩

/-- Proposition 1.9.9, first bullet, unconditionally: if `F_ν = F_μ / (1 + λ F_μ)` on `ℂ₊` with
`λ ≠ 0`, then the absolutely continuous parts of `μ` and `ν` are equivalent. -/
theorem rankOne_acParts_equiv' (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {lam : ℝ} (hlam : lam ≠ 0)
    (hF : ∀ z : ℂ, 0 < z.im →
      borelTransform ν z = borelTransform μ z / (1 + lam * borelTransform μ z)) :
    volume.withDensity (μ.rnDeriv volume) ≪ volume.withDensity (ν.rnDeriv volume) ∧
      volume.withDensity (ν.rnDeriv volume) ≪ volume.withDensity (μ.rnDeriv volume) :=
  rankOne_acParts_equiv reBoundaryValueStatement_holds μ ν hlam hF

end DF
