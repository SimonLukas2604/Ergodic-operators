/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators, I*,
§1.9 (pp. 79–92): Stieltjes (Borel) transforms of finite measures — basic theory.

# Main definitions

* `DF.borelTransform μ z` — the Stieltjes / Borel transform `F_μ(z) = ∫ dμ(x) / (x - z)` (1.9.7);
* `DF.poissonKernel ε x` — the Poisson kernel `P_ε(x) = ε / (π (x² + ε²))` of the upper
  half-plane (1.9.19);
* `DF.IsHerglotz F` — holomorphic self-map of the upper half-plane `ℂ₊`.

# Main results

* `DF.borelTransform_re`, `DF.borelTransform_im` — formulas (1.9.8), (1.9.9);
* `DF.borelTransform_isHerglotz` — `F_μ` is a Herglotz function for `μ ≠ 0` (remark after
  (1.9.9));
* `DF.tendsto_eps_mul_borelTransform` — Exercise 1.10.4(a): `ε F_μ(E + iε) → i μ({E})`;
* `DF.tendsto_eps_mul_im_borelTransform` — Theorem 1.9.6: `ε Im F_μ(E + iε) → μ({E})`;
* `DF.rankOne_borel` — Lemma 1.9.8, (1.9.33) (Aronszajn–Krein formula), stated for an arbitrary
  bounded operator on a complex inner product space with given resolvents;
* `DF.im_div_one_add_mul` — the algebraic identity behind (1.9.34);
* `DF.im_rankOne_borel` — (1.9.34).

# Statements (`Prop`s), proved in later files

* `DF.HerglotzRepresentationStatement` — Theorem 1.9.2 (Herglotz representation), proved in
  `DamanikFillman.Ch1.BorelHerglotz`;
* `DF.CaratheodoryRepresentationStatement` — Theorem 1.9.3 (Carathéodory representation), proved
  in `DamanikFillman.Ch1.BorelCaratheodory`.

# Deviations

* Throughout we work with *finite* Borel measures on `ℝ` (the book's (1.9.7) asks for finite
  compactly supported measures; compact support is never needed for the results here).
-/
import Mathlib

noncomputable section

open MeasureTheory Filter Topology Set Complex

namespace DF

/-! ## The Stieltjes / Borel transform -/

/-- The Stieltjes (Borel) transform of a measure on `ℝ`, `F_μ(z) = ∫ dμ(x) / (x - z)`
(book (1.9.7)). -/
def borelTransform (μ : Measure ℝ) (z : ℂ) : ℂ := ∫ x, ((x : ℂ) - z)⁻¹ ∂μ

/-- The Poisson kernel of the upper half-plane, `P_ε(x) = (1/π) ε / (x² + ε²)` (book (1.9.19)). -/
def poissonKernel (ε x : ℝ) : ℝ := ε / (Real.pi * (x ^ 2 + ε ^ 2))

/-- A Herglotz function: holomorphic on the upper half-plane `ℂ₊` and mapping it into itself
(book p. 81). -/
def IsHerglotz (F : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ F {z | 0 < z.im} ∧ ∀ z : ℂ, 0 < z.im → 0 < (F z).im

lemma poissonKernel_nonneg {ε : ℝ} (hε : 0 ≤ ε) (x : ℝ) : 0 ≤ poissonKernel ε x := by
  unfold poissonKernel; positivity

lemma poissonKernel_pos {ε : ℝ} (hε : 0 < ε) (x : ℝ) : 0 < poissonKernel ε x := by
  unfold poissonKernel; positivity

lemma poissonKernel_le {ε : ℝ} (hε : 0 < ε) (x : ℝ) : poissonKernel ε x ≤ 1 / (Real.pi * ε) := by
  unfold poissonKernel
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [Real.pi_pos, sq_nonneg x, mul_pos Real.pi_pos hε, sq_nonneg ε,
    mul_nonneg (mul_nonneg Real.pi_pos.le hε.le) (sq_nonneg x)]

lemma poissonKernel_le_of_le {ε r x : ℝ} (hε : 0 < ε) (hr : 0 < r) (hx : r ≤ |x|) :
    poissonKernel ε x ≤ ε / (Real.pi * r ^ 2) := by
  unfold poissonKernel
  apply div_le_div_of_nonneg_left hε.le (by positivity)
  have : r ^ 2 ≤ x ^ 2 := by
    rw [← sq_abs x]; exact pow_le_pow_left₀ hr.le hx 2
  nlinarith [Real.pi_pos, sq_nonneg ε]

lemma measurable_poissonKernel (ε : ℝ) : Measurable (poissonKernel ε) := by
  unfold poissonKernel; fun_prop

lemma continuous_poissonKernel {ε : ℝ} (hε : 0 < ε) : Continuous (poissonKernel ε) := by
  unfold poissonKernel
  refine Continuous.div continuous_const (by fun_prop) (fun x => ?_)
  positivity

/-- The norm of `(x - z)⁻¹` is at most `1 / |Im z|`. -/
lemma norm_inv_sub_le (x : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    ‖((x : ℂ) - z)⁻¹‖ ≤ 1 / |z.im| := by
  rw [norm_inv, one_div]
  have hpos : 0 < |z.im| := abs_pos.mpr hz
  apply inv_anti₀ hpos
  calc |z.im| = |((x : ℂ) - z).im| := by simp
    _ ≤ ‖(x : ℂ) - z‖ := Complex.abs_im_le_norm _

lemma continuous_inv_sub {z : ℂ} (hz : z.im ≠ 0) :
    Continuous fun x : ℝ => ((x : ℂ) - z)⁻¹ := by
  refine Continuous.inv₀ (by fun_prop) (fun x h => hz ?_)
  have := congrArg Complex.im h
  simpa using this.symm

lemma integrable_inv_sub (μ : Measure ℝ) [IsFiniteMeasure μ] {z : ℂ} (hz : z.im ≠ 0) :
    Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) μ := by
  refine Integrable.of_bound (C := 1 / |z.im|) (continuous_inv_sub hz).aestronglyMeasurable ?_
  exact Eventually.of_forall fun x => norm_inv_sub_le x hz

/-- Real part of `(x - (E + iε))⁻¹`. -/
lemma inv_sub_re (x E ε : ℝ) :
    (((x : ℂ) - (E + ε * I))⁻¹).re = (x - E) / ((x - E) ^ 2 + ε ^ 2) := by
  rw [Complex.inv_re, Complex.normSq_apply]
  simp; ring

/-- Imaginary part of `(x - (E + iε))⁻¹`. -/
lemma inv_sub_im (x E ε : ℝ) :
    (((x : ℂ) - (E + ε * I))⁻¹).im = ε / ((x - E) ^ 2 + ε ^ 2) := by
  rw [Complex.inv_im, Complex.normSq_apply]
  simp; ring

/-- Formula (1.9.8): `Re F_μ(E + iε) = ∫ (x - E) / ((x - E)² + ε²) dμ(x)`. -/
theorem borelTransform_re (μ : Measure ℝ) [IsFiniteMeasure μ] (E : ℝ) {ε : ℝ} (hε : ε ≠ 0) :
    (borelTransform μ (E + ε * I)).re = ∫ x, (x - E) / ((x - E) ^ 2 + ε ^ 2) ∂μ := by
  have hz : (E + ε * I : ℂ).im ≠ 0 := by simpa using hε
  unfold borelTransform
  have h := integral_re (integrable_inv_sub μ hz)
  simp only [RCLike.re_to_complex] at h
  rw [← h]
  congr 1; ext x; exact inv_sub_re x E ε

/-- Formula (1.9.9): `Im F_μ(E + iε) = ∫ ε / ((x - E)² + ε²) dμ(x)`. -/
theorem borelTransform_im (μ : Measure ℝ) [IsFiniteMeasure μ] (E : ℝ) {ε : ℝ} (hε : ε ≠ 0) :
    (borelTransform μ (E + ε * I)).im = ∫ x, ε / ((x - E) ^ 2 + ε ^ 2) ∂μ := by
  have hz : (E + ε * I : ℂ).im ≠ 0 := by simpa using hε
  unfold borelTransform
  have h := integral_im (integrable_inv_sub μ hz)
  simp only [RCLike.im_to_complex] at h
  rw [← h]
  congr 1; ext x; exact inv_sub_im x E ε

/-- `Im F_μ(E + iε) = π ∫ P_ε(x - E) dμ(x)`: the imaginary part of the Borel transform is
(up to the factor `π`) the Poisson integral of `μ`. -/
theorem borelTransform_im_eq_poisson (μ : Measure ℝ) [IsFiniteMeasure μ] (E : ℝ) {ε : ℝ}
    (hε : ε ≠ 0) :
    (borelTransform μ (E + ε * I)).im = Real.pi * ∫ x, poissonKernel ε (x - E) ∂μ := by
  rw [borelTransform_im μ E hε, ← integral_const_mul]
  congr 1; ext x
  unfold poissonKernel
  field_simp

lemma integrable_poissonKernel (μ : Measure ℝ) [IsFiniteMeasure μ] {ε : ℝ} (hε : 0 < ε)
    (E : ℝ) : Integrable (fun x => poissonKernel ε (x - E)) μ := by
  refine Integrable.of_bound (C := 1 / (Real.pi * ε)) ?_ ?_
  · exact ((continuous_poissonKernel hε).comp (continuous_sub_right E)).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    rw [Real.norm_of_nonneg (poissonKernel_nonneg hε.le _)]
    exact poissonKernel_le hε _

/-- The imaginary part of the Borel transform divided by `π`, as an `ℝ≥0∞`-valued Poisson
integral. -/
theorem ofReal_im_div_pi (μ : Measure ℝ) [IsFiniteMeasure μ] (E : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ENNReal.ofReal ((borelTransform μ (E + ε * I)).im / Real.pi) =
      ∫⁻ x, ENNReal.ofReal (poissonKernel ε (x - E)) ∂μ := by
  rw [borelTransform_im_eq_poisson μ E hε.ne', mul_div_cancel_left₀ _ Real.pi_ne_zero,
    ofReal_integral_eq_lintegral_ofReal (integrable_poissonKernel μ hε E)
      (Eventually.of_forall fun x => poissonKernel_nonneg hε.le _)]

lemma borelTransform_im_nonneg (μ : Measure ℝ) [IsFiniteMeasure μ] (E : ℝ) {ε : ℝ}
    (hε : 0 < ε) : 0 ≤ (borelTransform μ (E + ε * I)).im := by
  rw [borelTransform_im μ E hε.ne']
  exact integral_nonneg fun x => by positivity

/-- Writing a point of the upper half plane as `E + iε`. -/
lemma eq_re_add_im_mul_I (z : ℂ) : z = (z.re : ℂ) + (z.im : ℂ) * I := (Complex.re_add_im z).symm

lemma borelTransform_im_pos (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : μ ≠ 0) {z : ℂ}
    (hz : 0 < z.im) : 0 < (borelTransform μ z).im := by
  rw [eq_re_add_im_mul_I z, borelTransform_im μ _ hz.ne']
  have hint : Integrable (fun x => z.im / ((x - z.re) ^ 2 + z.im ^ 2)) μ := by
    have h := (integrable_inv_sub μ (z := (z.re : ℂ) + (z.im : ℂ) * I) (by simpa using hz.ne')).im
    refine h.congr (Eventually.of_forall fun x => ?_)
    simp only [RCLike.im_to_complex]
    exact inv_sub_im x z.re z.im
  rw [integral_pos_iff_support_of_nonneg (fun x => by positivity) hint]
  have : Function.support (fun x : ℝ => z.im / ((x - z.re) ^ 2 + z.im ^ 2)) = univ := by
    ext x; simp only [Function.mem_support, mem_univ, iff_true]; positivity
  rw [this]
  simpa [Measure.measure_univ_pos] using hμ

/-- The Borel transform agrees with Mathlib's `resolventTransform`. -/
lemma borelTransform_eq_resolventTransform (μ : Measure ℝ) :
    borelTransform μ = resolventTransform μ := by
  ext z
  simp [borelTransform, resolventTransform, resolvent, Ring.inverse_eq_inv']

lemma differentiableOn_borelTransform (μ : Measure ℝ) [IsFiniteMeasure μ] :
    DifferentiableOn ℂ (borelTransform μ) {z | 0 < z.im} := by
  rw [borelTransform_eq_resolventTransform]
  refine (analyticOn_resolventTransform (μ := μ)).differentiableOn.mono ?_
  intro z hz ⟨x, _, hx⟩
  simp only [mem_ofPred_eq] at hz
  rw [← hx] at hz
  simp at hz

/-- The Borel transform of a nonzero finite measure is a Herglotz function (book p. 81,
after (1.9.9)). -/
theorem borelTransform_isHerglotz (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : μ ≠ 0) :
    IsHerglotz (borelTransform μ) :=
  ⟨differentiableOn_borelTransform μ, fun _ hz => borelTransform_im_pos μ hμ hz⟩

lemma borelTransform_add (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] {z : ℂ}
    (hz : z.im ≠ 0) :
    borelTransform (μ + ν) z = borelTransform μ z + borelTransform ν z := by
  unfold borelTransform
  rw [integral_add_measure (integrable_inv_sub μ hz) (integrable_inv_sub ν hz)]

/-! ## Point masses: Theorem 1.9.6 and Exercise 1.10.4(a) -/

/-- Exercise 1.10.4(a): `ε F_μ(E + iε) → i μ({E})` as `ε ↓ 0`. -/
theorem tendsto_eps_mul_borelTransform (μ : Measure ℝ) [IsFiniteMeasure μ] (E : ℝ) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * borelTransform μ (E + ε * I)) (𝓝[>] 0)
      (𝓝 (I * (μ.real {E} : ℂ))) := by
  have hrw : ∀ ε : ℝ, (ε : ℂ) * borelTransform μ (E + ε * I) =
      ∫ x, (ε : ℂ) * ((x : ℂ) - (E + ε * I))⁻¹ ∂μ := fun ε => by
    unfold borelTransform; rw [integral_const_mul]
  simp_rw [hrw]
  have hlim : ∫ x, ({E} : Set ℝ).indicator (fun _ => I) x ∂μ = I * (μ.real {E} : ℂ) := by
    rw [integral_indicator (measurableSet_singleton E)]
    simp [mul_comm, Measure.real]
  rw [← hlim]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ ?_
    (integrable_const _) ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    have hz : (E + ε * I : ℂ).im ≠ 0 := by simpa using (ne_of_gt hε)
    exact ((continuous_inv_sub hz).const_smul (ε : ℂ)).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    refine Eventually.of_forall fun x => ?_
    have hε' : (0 : ℝ) < ε := hε
    have hz : (E + ε * I : ℂ).im ≠ 0 := by simpa using hε'.ne'
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hε'.le]
    calc ε * ‖((x : ℂ) - (E + ε * I))⁻¹‖ ≤ ε * (1 / |(E + ε * I : ℂ).im|) :=
          mul_le_mul_of_nonneg_left (norm_inv_sub_le x hz) hε'.le
      _ = 1 := by simp [abs_of_pos hε', hε'.ne']
  · refine Eventually.of_forall fun x => ?_
    by_cases hx : x = E
    · subst hx
      simp only [indicator_of_mem (mem_singleton x)]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hε)
      field_simp
      ring_nf
      simp [I_sq]
    · rw [indicator_of_notMem (by simpa using hx)]
      have hc : ContinuousAt (fun ε : ℝ => (ε : ℂ) * ((x : ℂ) - (E + ε * I))⁻¹) 0 := by
        have h0 : ((x : ℂ) - (E + ((0 : ℝ) : ℂ) * I)) ≠ 0 := by
          simpa [sub_eq_zero] using (Complex.ofReal_injective.ne hx)
        refine ContinuousAt.mul (by fun_prop) (ContinuousAt.inv₀ (by fun_prop) h0)
      have := hc.tendsto
      simp only [Complex.ofReal_zero, zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds

/-- Theorem 1.9.6: `μ({E}) = lim_{ε ↓ 0} ε Im F_μ(E + iε)` for every `E ∈ ℝ`. -/
theorem tendsto_eps_mul_im_borelTransform (μ : Measure ℝ) [IsFiniteMeasure μ] (E : ℝ) :
    Tendsto (fun ε : ℝ => ε * (borelTransform μ (E + ε * I)).im) (𝓝[>] 0)
      (𝓝 (μ.real {E})) := by
  have h := (Complex.continuous_im.tendsto _).comp (tendsto_eps_mul_borelTransform μ E)
  simpa [Function.comp_def] using h

/-! ## Rank-one perturbations: Lemma 1.9.8 -/

section RankOne

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The rank-one operator `⟨φ, ·⟩ φ`. -/
def rankOneOp (φ : H) : H →L[ℂ] H := (innerSL ℂ φ).smulRight φ

@[simp] lemma rankOneOp_apply (φ ψ : H) : rankOneOp φ ψ = (inner ℂ φ ψ) • φ := by
  simp [rankOneOp]

/-- Lemma 1.9.8, formula (1.9.33) (Aronszajn–Krein): if `R = (A - z)⁻¹` and
`R_λ = (A_λ - z)⁻¹` with `A_λ = A + λ ⟨φ, ·⟩ φ`, then
`⟨φ, R_λ φ⟩ = ⟨φ, R φ⟩ / (1 + λ ⟨φ, R φ⟩)`.  Only a left inverse of `A - z` and a right inverse
of `A_λ - z` are needed. -/
theorem rankOne_borel (A : H →L[ℂ] H) (φ : H) (lam : ℝ) (z : ℂ) (R Rl : H →L[ℂ] H)
    (hR : R ∘L (A - z • (1 : H →L[ℂ] H)) = 1)
    (hRl : (A + (lam : ℂ) • rankOneOp φ - z • (1 : H →L[ℂ] H)) ∘L Rl = 1) :
    inner ℂ φ (Rl φ) = inner ℂ φ (R φ) / (1 + lam * inner ℂ φ (R φ)) := by
  set F := inner ℂ φ (R φ)
  set Fl := inner ℂ φ (Rl φ)
  have h1 : R ((A - z • (1 : H →L[ℂ] H)) (Rl φ)) = Rl φ := by
    simpa using congrArg (fun T : H →L[ℂ] H => T (Rl φ)) hR
  have h2 : (A + (lam : ℂ) • rankOneOp φ - z • (1 : H →L[ℂ] H)) (Rl φ) = φ := by
    simpa using congrArg (fun T : H →L[ℂ] H => T φ) hRl
  have key : Rl φ - R φ = (-((lam : ℂ) * Fl)) • R φ := by
    calc Rl φ - R φ = R ((A - z • (1 : H →L[ℂ] H)) (Rl φ)) -
          R ((A + (lam : ℂ) • rankOneOp φ - z • (1 : H →L[ℂ] H)) (Rl φ)) := by rw [h1, h2]
      _ = R ((-((lam : ℂ) * Fl)) • φ) := by
          rw [← map_sub]; congr 1
          simp only [sub_apply, add_apply,
            smul_apply, rankOneOp_apply, Fl]
          rw [smul_smul]; abel_nf; simp [neg_smul]
      _ = (-((lam : ℂ) * Fl)) • R φ := by rw [map_smul]
  have key2 : Fl - F = -((lam : ℂ) * Fl) * F := by
    have := congrArg (inner ℂ φ) key
    simpa [inner_sub_right, inner_smul_right, Fl, F] using this
  have hmul : Fl * (1 + lam * F) = F := by linear_combination key2
  have hne : (1 + lam * F) ≠ 0 := by
    intro h0
    have hF : F = 0 := by rw [← hmul, h0, mul_zero]
    rw [hF, mul_zero, add_zero] at h0
    exact one_ne_zero h0
  rw [eq_div_iff hne, hmul]

/-- The algebraic identity behind (1.9.34): for real `λ`,
`Im (F / (1 + λ F)) = Im F / |1 + λ F|²`. -/
theorem im_div_one_add_mul (F : ℂ) (lam : ℝ) :
    (F / (1 + lam * F)).im = F.im / Complex.normSq (1 + lam * F) := by
  rw [Complex.div_im]
  simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, add_zero, zero_add, Complex.add_re, Complex.one_re,
    Complex.mul_re, sub_zero]
  rw [← sub_div]
  congr 1
  ring

/-- Formula (1.9.34): `Im F_λ(z) = Im F(z) / |1 + λ F(z)|²`, in the operator setting of
`rankOne_borel`. -/
theorem im_rankOne_borel (A : H →L[ℂ] H) (φ : H) (lam : ℝ) (z : ℂ) (R Rl : H →L[ℂ] H)
    (hR : R ∘L (A - z • (1 : H →L[ℂ] H)) = 1)
    (hRl : (A + (lam : ℂ) • rankOneOp φ - z • (1 : H →L[ℂ] H)) ∘L Rl = 1) :
    (inner ℂ φ (Rl φ)).im =
      (inner ℂ φ (R φ)).im / Complex.normSq (1 + lam * inner ℂ φ (R φ)) := by
  rw [rankOne_borel A φ lam z R Rl hR hRl, im_div_one_add_mul]

end RankOne

/-! ## Herglotz and Carathéodory representations (recorded as statements) -/

/-- Theorem 1.9.2 (Herglotz representation), as a statement: a function `F` is Herglotz
iff `F(z) = a + b z + ∫ (1/(x - z) - x/(1 + x²)) dμ(x)` with `a ∈ ℝ`, `b ≥ 0`, and a measure `μ`
with `∫ dμ/(1 + x²) < ∞`, where `b > 0` or `μ ≠ 0`.  (The book asks for `μ ≠ 0`; this is not
quite right, e.g. `F(z) = z` is Herglotz with `μ = 0`, `b = 1`.)  Proved in
`DamanikFillman.Ch1.BorelHerglotz` as `DF.herglotzRepresentationStatement_holds`. -/
def HerglotzRepresentationStatement : Prop :=
  ∀ F : ℂ → ℂ, IsHerglotz F ↔
    ∃ (a b : ℝ) (μ : Measure ℝ), 0 ≤ b ∧ (b ≠ 0 ∨ μ ≠ 0) ∧
      Integrable (fun x : ℝ => 1 / (1 + x ^ 2)) μ ∧
      ∀ z : ℂ, 0 < z.im →
        F z = a + b * z + ∫ x, (((x : ℂ) - z)⁻¹ - (x : ℂ) / (1 + (x : ℂ) ^ 2)) ∂μ

/-- Theorem 1.9.3 (Carathéodory representation), as a statement (proved in
`DamanikFillman.Ch1.BorelCaratheodory` as `DF.caratheodoryRepresentationStatement_holds`): `G` is
analytic on the
unit disk with positive real part iff `G(z) = i c + ∫_{∂𝔻} (w + z)/(w - z) dν(w)` for some
`c ∈ ℝ` and a finite (nonzero) measure `ν` on the unit circle.  (We encode `ν` as a finite
measure on `ℂ` concentrated on the unit circle.) -/
def CaratheodoryRepresentationStatement : Prop :=
  ∀ G : ℂ → ℂ,
    (DifferentiableOn ℂ G (Metric.ball 0 1) ∧ ∀ z ∈ Metric.ball (0 : ℂ) 1, 0 < (G z).re) ↔
    ∃ (c : ℝ) (ν : Measure ℂ), IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν (Metric.sphere 0 1)ᶜ = 0 ∧
      ∀ z ∈ Metric.ball (0 : ℂ) 1, G z = c * I + ∫ w, (w + z) / (w - z) ∂ν

end DF
