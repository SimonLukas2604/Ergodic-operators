/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators, I*,
§1.9: uniqueness of Borel transforms, and Herglotz functions which are Borel transforms.

# Main results

* `DF.tendsto_poisson_conv` — the Poisson kernel is an approximate identity:
  `∫ P_ε(E - x) f(E) dE → f(x)` for bounded continuous `f`.
* `DF.tendsto_integral_im_borelTransform` — Stieltjes inversion in weak form:
  `∫ f(E) π⁻¹ Im F_ν(E + iε) dE → ∫ f dν` for `f ∈ C_c(ℝ)`.
* `DF.borelTransform_ext` — a finite measure is determined by its Borel transform on `ℂ₊`.
* `DF.exists_measure_of_isHerglotz` — a Herglotz function with `|Φ(iy)| ≤ C / y` for large `y`
  is the Borel transform of a finite measure.
-/
import DamanikFillman.Ch1.BorelHerglotz
import DamanikFillman.Ch1.BorelDerivative

noncomputable section

open MeasureTheory Filter Topology Set Metric Complex
open scoped ENNReal CompactlySupported

namespace DF

/-! ### The Poisson kernel as an approximate identity -/

lemma poissonKernel_comm (ε a b : ℝ) : poissonKernel ε (a - b) = poissonKernel ε (b - a) := by
  unfold poissonKernel
  rw [show (b - a) ^ 2 = (a - b) ^ 2 by ring]

/-- The Poisson kernel is an approximate identity. -/
theorem tendsto_poisson_conv {f : ℝ → ℝ} (hf : Continuous f) {M : ℝ} (hM : ∀ x, |f x| ≤ M)
    (x : ℝ) :
    Tendsto (fun ε => ∫ E, poissonKernel ε (E - x) * f E) (𝓝[>] 0) (𝓝 (f x)) := by
  rw [Metric.tendsto_nhds]
  intro η hη
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuous_iff.1 hf x (η / 2) (by positivity)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM x)
  -- the mass of the Poisson kernel outside `ball x δ` tends to `0`
  have hlim : Tendsto (fun ε : ℝ => 2 * M * (1 - 2 / Real.pi * Real.arctan (δ / ε)))
      (𝓝[>] 0) (𝓝 (2 * M * (1 - 2 / Real.pi * (Real.pi / 2)))) := by
    have h1 : Tendsto (fun ε : ℝ => δ / ε) (𝓝[>] 0) atTop :=
      Tendsto.const_mul_atTop hδ tendsto_inv_nhdsGT_zero |>.congr fun ε => by ring
    have h2 := (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h1
    exact ((h2.const_mul (2 / Real.pi)).const_sub 1).const_mul (2 * M)
  have h0 : 2 * M * (1 - 2 / Real.pi * (Real.pi / 2)) = 0 := by
    field_simp; ring
  rw [h0] at hlim
  have hev := (Metric.tendsto_nhds.1 hlim) (η / 2) (by positivity)
  filter_upwards [hev, self_mem_nhdsWithin] with ε hε1 (hε : 0 < ε)
  rw [Real.dist_eq, sub_zero] at hε1
  have hP := integrable_poissonKernel_volume hε x
  have hPf : Integrable (fun E => poissonKernel ε (E - x) * f E) :=
    hP.mul_of_top_left (memLp_top_of_bound hf.aestronglyMeasurable M
      (Eventually.of_forall fun E => by rw [Real.norm_eq_abs]; exact hM E))
  have hsplit : (∫ E, poissonKernel ε (E - x) * f E) - f x =
      ∫ E, poissonKernel ε (E - x) * (f E - f x) := by
    have h1 : ∫ E, poissonKernel ε (E - x) * (f E - f x) =
        (∫ E, poissonKernel ε (E - x) * f E) - ∫ E, poissonKernel ε (E - x) * f x := by
      rw [← integral_sub hPf (hP.mul_const _)]
      congr 1; ext E; ring
    rw [h1, integral_mul_const, integral_poissonKernel hε x, one_mul]
  -- pointwise bound
  set B := ball x δ with hBdef
  have hbound : ∀ E, ‖poissonKernel ε (E - x) * (f E - f x)‖ ≤
      η / 2 * poissonKernel ε (E - x) + 2 * M * Bᶜ.indicator (fun E => poissonKernel ε (E - x)) E := by
    intro E
    have hPE := poissonKernel_nonneg hε.le (E - x)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hPE]
    by_cases hE : E ∈ B
    · rw [indicator_of_notMem (show E ∉ Bᶜ from fun h => h hE), mul_zero, add_zero,
        mul_comm (η / 2)]
      refine mul_le_mul_of_nonneg_left ?_ hPE
      have := hδf E hE
      rw [Real.dist_eq] at this
      exact this.le
    · rw [indicator_of_mem hE]
      have h1 : |f E - f x| ≤ 2 * M := by
        have := abs_sub (f E) (f x)
        linarith [hM E, hM x]
      have h2 : 0 ≤ η / 2 * poissonKernel ε (E - x) := by positivity
      nlinarith
  have hPi : Integrable (fun E => poissonKernel ε (E - x) * (f E - f x)) :=
    hP.mul_of_top_left (memLp_top_of_bound (hf.sub continuous_const).aestronglyMeasurable (2 * M)
      (Eventually.of_forall fun E => by
        rw [Real.norm_eq_abs]
        have := abs_sub (f E) (f x)
        linarith [hM E, hM x]))
  have hind : Integrable (Bᶜ.indicator fun E => poissonKernel ε (E - x)) :=
    hP.indicator isOpen_ball.measurableSet.compl
  have hsum : Integrable (fun E => η / 2 * poissonKernel ε (E - x) +
      2 * M * Bᶜ.indicator (fun E => poissonKernel ε (E - x)) E) :=
    (hP.const_mul (η / 2)).add (hind.const_mul (2 * M))
  have hint := norm_integral_le_of_norm_le hsum (Eventually.of_forall hbound)
  rw [integral_add (hP.const_mul _) (hind.const_mul _), integral_const_mul, integral_const_mul,
    integral_poissonKernel hε x, integral_indicator isOpen_ball.measurableSet.compl] at hint
  have hcompl : ∫ E in Bᶜ, poissonKernel ε (E - x) = 1 - 2 / Real.pi * Real.arctan (δ / ε) := by
    have := integral_add_compl isOpen_ball.measurableSet hP
    rw [integral_poissonKernel hε x, hBdef, integral_poissonKernel_ball hε hδ x] at this
    rw [hBdef]; linarith
  rw [hcompl] at hint
  rw [Real.dist_eq, hsplit, ← Real.norm_eq_abs]
  have := (le_abs_self _).trans_lt hε1
  linarith

/-! ### Uniqueness of Borel transforms -/

/-- Stieltjes inversion, weak form: `∫ f(E) π⁻¹ Im F_ν(E + iε) dE → ∫ f dν`. -/
theorem tendsto_integral_im_borelTransform (ν : Measure ℝ) [IsFiniteMeasure ν]
    (f : C_c(ℝ, ℝ)) :
    Tendsto (fun ε : ℝ => ∫ E, f E * ((borelTransform ν (E + ε * I)).im / Real.pi))
      (𝓝[>] 0) (𝓝 (∫ x, f x ∂ν)) := by
  obtain ⟨M, hM⟩ := f.hasCompactSupport.exists_bound_of_continuous f.continuous
  have hM' : ∀ x, |f x| ≤ M := fun x => by rw [← Real.norm_eq_abs]; exact hM x
  have hfi : Integrable (fun E => f E) := f.integrable
  -- rewrite with Fubini
  have heq : ∀ ε : ℝ, 0 < ε → ∫ E, f E * ((borelTransform ν (E + ε * I)).im / Real.pi) =
      ∫ y, (∫ E, poissonKernel ε (E - y) * f E) ∂ν := by
    intro ε hε
    have h1 : ∀ E, f E * ((borelTransform ν (E + ε * I)).im / Real.pi) =
        ∫ y, f E * poissonKernel ε (y - E) ∂ν := by
      intro E
      rw [borelTransform_im_eq_poisson ν E hε.ne', mul_div_cancel_left₀ _ Real.pi_ne_zero,
        integral_const_mul]
    simp_rw [h1]
    have hint : Integrable (Function.uncurry fun (E : ℝ) (y : ℝ) =>
        f E * poissonKernel ε (y - E)) (volume.prod ν) := by
      have hb : Integrable (fun p : ℝ × ℝ => |f p.1| * (1 / (Real.pi * ε))) (volume.prod ν) :=
        hfi.abs.mul_prod (integrable_const _)
      refine hb.mono' ?_ (Eventually.of_forall fun p => ?_)
      · exact (Continuous.mul (f.continuous.comp continuous_fst)
          ((continuous_poissonKernel hε).comp (continuous_snd.sub continuous_fst))).aestronglyMeasurable
      · show ‖f p.1 * poissonKernel ε (p.2 - p.1)‖ ≤ |f p.1| * (1 / (Real.pi * ε))
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (poissonKernel_nonneg hε.le _)]
        exact mul_le_mul_of_nonneg_left (poissonKernel_le hε _) (abs_nonneg _)
    rw [integral_integral_swap hint]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    refine integral_congr_ae (Eventually.of_forall fun E => ?_)
    simp only
    rw [poissonKernel_comm, mul_comm]
  have hconv : Tendsto (fun ε : ℝ => ∫ y, (∫ E, poissonKernel ε (E - y) * f E) ∂ν)
      (𝓝[>] 0) (𝓝 (∫ y, f y ∂ν)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => M) ?_ ?_
      (integrable_const M) (Eventually.of_forall fun y => tendsto_poisson_conv f.continuous hM' y)
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      have : Continuous fun y => ∫ E, poissonKernel ε (E - y) * f E := by
        have h : (fun y => ∫ E, poissonKernel ε (E - y) * f E) =
            fun y => ∫ E, poissonKernel ε E * f (E + y) := by
          funext y
          rw [← integral_add_right_eq_self (μ := volume)
            (fun E => poissonKernel ε (E - y) * f E) y]
          simp only [add_sub_cancel_right]
        rw [h]
        refine continuous_of_dominated (bound := fun E => M * poissonKernel ε E) ?_ ?_ ?_ ?_
        · exact fun y => ((continuous_poissonKernel hε).mul
            (f.continuous.comp (continuous_id.add continuous_const))).aestronglyMeasurable
        · intro y
          refine Eventually.of_forall fun E => ?_
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (poissonKernel_nonneg hε.le _), mul_comm]
          exact mul_le_mul_of_nonneg_right (hM' _) (poissonKernel_nonneg hε.le _)
        · have := (integrable_poissonKernel_volume hε 0).const_mul M
          simpa using this
        · exact Eventually.of_forall fun E =>
            continuous_const.mul (f.continuous.comp (continuous_const.add continuous_id))
      exact this.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      refine Eventually.of_forall fun y => ?_
      rw [Real.norm_eq_abs]
      have hP := integrable_poissonKernel_volume hε y
      calc |∫ E, poissonKernel ε (E - y) * f E|
          ≤ ∫ E, |poissonKernel ε (E - y) * f E| := abs_integral_le_integral_abs
        _ ≤ ∫ E, M * poissonKernel ε (E - y) := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun E => abs_nonneg _)
              (hP.const_mul M) (Eventually.of_forall fun E => ?_)
            simp only
            rw [abs_mul, abs_of_nonneg (poissonKernel_nonneg hε.le _), mul_comm]
            exact mul_le_mul_of_nonneg_right (hM' _) (poissonKernel_nonneg hε.le _)
        _ = M := by rw [integral_const_mul, integral_poissonKernel hε y, mul_one]
  exact hconv.congr' (by
    filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact (heq ε hε).symm)

/-- **Uniqueness**: a finite measure on `ℝ` is determined by its Borel transform on `ℂ₊`. -/
theorem borelTransform_ext {ν ν' : Measure ℝ} [IsFiniteMeasure ν] [IsFiniteMeasure ν']
    (h : ∀ z : ℂ, 0 < z.im → borelTransform ν z = borelTransform ν' z) : ν = ν' := by
  refine Measure.ext_of_integral_eq_on_compactlySupported fun f => ?_
  refine tendsto_nhds_unique (tendsto_integral_im_borelTransform ν f)
    ((tendsto_integral_im_borelTransform ν' f).congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  refine integral_congr_ae (Eventually.of_forall fun E => ?_)
  simp only
  rw [h _ (by simpa using hε)]

/-! ### Herglotz functions which are Borel transforms -/

lemma norm_borelTransform_le (ν : Measure ℝ) [IsFiniteMeasure ν] {z : ℂ} (hz : 0 < z.im) :
    ‖borelTransform ν z‖ ≤ ν.real univ / z.im := by
  unfold borelTransform
  have := norm_integral_le_of_norm_le_const (μ := ν) (C := 1 / z.im)
    (Eventually.of_forall fun x => (norm_inv_sub_le x hz.ne').trans_eq (by
      rw [abs_of_pos hz]))
  rw [measureReal_def] at this ⊢
  calc _ ≤ 1 / z.im * (ν univ).toReal := by simpa [mul_comm] using this
    _ = (ν univ).toReal / z.im := by ring

/-- A Herglotz function `Φ` with `|Φ(iy)| ≤ C / y` for all `y ≥ y₀` is the Borel transform of a
finite measure. -/
theorem exists_measure_of_isHerglotz {Φ : ℂ → ℂ} (hΦ : IsHerglotz Φ) {C y₀ : ℝ}
    (hdec : ∀ y : ℝ, y₀ ≤ y → 0 < y → ‖Φ (y * I)‖ ≤ C / y) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧ ∀ z : ℂ, 0 < z.im → Φ z = borelTransform ν z := by
  obtain ⟨a, b, ρ, hρ, hb, -, hrep⟩ := exists_herglotzRho Φ hΦ
  -- the bound on `Im Φ(iy)`
  have hIm : ∀ y : ℝ, y₀ ≤ y → 0 < y →
      b * y + ∫ x, (1 + x ^ 2) * y / (x ^ 2 + y ^ 2) ∂ρ ≤ C / y := by
    intro y hy hy0
    have hz : 0 < ((y : ℂ) * I).im := by simpa using hy0
    have h1 := im_herglotzRho a b ρ hz
    rw [← hrep _ hz] at h1
    have h2 : (Φ (y * I)).im ≤ C / y := (Complex.im_le_norm _).trans (hdec y hy hy0)
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re,
      mul_one, mul_zero, add_zero] at h1
    have h3 : ∫ x, (1 + x ^ 2) * y / Complex.normSq ((x : ℂ) - y * I) ∂ρ =
        ∫ x, (1 + x ^ 2) * y / (x ^ 2 + y ^ 2) ∂ρ := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      have : Complex.normSq ((x : ℂ) - y * I) = x ^ 2 + y ^ 2 := by
        simp [Complex.normSq_apply]; ring
      simp only
      rw [this]
    rw [h3] at h1
    linarith
  have hnn : ∀ y : ℝ, 0 < y → 0 ≤ ∫ x, (1 + x ^ 2) * y / (x ^ 2 + y ^ 2) ∂ρ := fun y hy =>
    integral_nonneg fun x => by positivity
  -- `b = 0`
  have hb0 : b = 0 := by
    by_contra hne
    have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hne)
    obtain ⟨y, hy1, hy2⟩ : ∃ y : ℝ, max y₀ 1 ≤ y ∧ (|C| + 1) / b ≤ y :=
      ⟨max (max y₀ 1) ((|C| + 1) / b), le_max_left _ _, le_max_right _ _⟩
    have hy0 : 0 < y := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hy1)
    have h := hIm y ((le_max_left _ _).trans hy1) hy0
    have h' := hnn y hy0
    have h4 : b * y ≤ C / y := by linarith
    have h5 : b * y * y ≤ C := by
      have := mul_le_mul_of_nonneg_right h4 hy0.le
      rwa [div_mul_cancel₀ _ hy0.ne'] at this
    have h6 : |C| + 1 ≤ b * y := by
      rw [div_le_iff₀ hbpos] at hy2; linarith
    have h7 : 1 ≤ y := (le_max_right _ _).trans hy1
    have h8 : (|C| + 1) * 1 ≤ b * y * y :=
      mul_le_mul h6 h7 zero_le_one (by positivity)
    linarith [le_abs_self C]
  -- finiteness of `(1 + x²) ρ`
  have hfin : ∫⁻ x, ENNReal.ofReal (1 + x ^ 2) ∂ρ ≤ ENNReal.ofReal |C| := by
    set g : ℕ → ℝ → ℝ≥0∞ := fun n x =>
      ENNReal.ofReal ((1 + x ^ 2) * ((n : ℝ) + max y₀ 1) ^ 2 / (x ^ 2 + ((n : ℝ) + max y₀ 1) ^ 2))
      with hg
    have hlim : ∀ x : ℝ, Tendsto (fun n => g n x) atTop (𝓝 (ENNReal.ofReal (1 + x ^ 2))) := by
      intro x
      refine ENNReal.tendsto_ofReal ?_
      have hy : Tendsto (fun n : ℕ => (n : ℝ) + max y₀ 1) atTop atTop :=
        tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      have h1 : Tendsto (fun n : ℕ => x ^ 2 / ((n : ℝ) + max y₀ 1) ^ 2) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp hy)
      have h2 : Tendsto (fun n : ℕ => (1 + x ^ 2) / (1 + x ^ 2 / ((n : ℝ) + max y₀ 1) ^ 2))
          atTop (𝓝 ((1 + x ^ 2) / (1 + 0))) :=
        tendsto_const_nhds.div (tendsto_const_nhds.add h1) (by norm_num)
      rw [add_zero, div_one] at h2
      refine h2.congr fun n => ?_
      have hpos : 0 < (n : ℝ) + max y₀ 1 := by positivity
      field_simp
      ring
    have hmeas : ∀ n, Measurable (g n) := fun n => by
      refine ENNReal.measurable_ofReal.comp ?_
      fun_prop
    have hbound : ∀ n, ∫⁻ x, g n x ∂ρ ≤ ENNReal.ofReal |C| := by
      intro n
      set y : ℝ := (n : ℝ) + max y₀ 1 with hydef
      have hy0 : 0 < y := by positivity
      have hy1 : 1 ≤ y := by
        have := le_max_right y₀ 1; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
      have hyy : y₀ ≤ y := by
        have := le_max_left y₀ 1; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
      have h := hIm y hyy hy0
      rw [hb0, zero_mul, zero_add] at h
      have hint : Integrable (fun x : ℝ => (1 + x ^ 2) * y / (x ^ 2 + y ^ 2)) ρ := by
        refine Integrable.of_bound (C := y) ?_ (Eventually.of_forall fun x => ?_)
        · exact ((by fun_prop : Continuous fun x : ℝ => (1 + x ^ 2) * y).div
            (by fun_prop : Continuous fun x : ℝ => x ^ 2 + y ^ 2)
            (fun x => by positivity)).aestronglyMeasurable
        · rw [Real.norm_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
          have h1 : 1 ≤ y ^ 2 := by nlinarith
          nlinarith [mul_le_mul_of_nonneg_left h1 hy0.le]
      have h2 : ∫⁻ x, g n x ∂ρ = ENNReal.ofReal (y * ∫ x, (1 + x ^ 2) * y / (x ^ 2 + y ^ 2) ∂ρ) := by
        rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal (hint.const_mul y)
          (Eventually.of_forall fun x => by positivity)]
        refine lintegral_congr fun x => ?_
        simp only [hg]
        congr 1
        ring
      rw [h2]
      refine ENNReal.ofReal_le_ofReal ?_
      have := mul_le_mul_of_nonneg_left h hy0.le
      rw [mul_div_cancel₀ _ hy0.ne'] at this
      exact this.trans (le_abs_self C)
    calc ∫⁻ x, ENNReal.ofReal (1 + x ^ 2) ∂ρ = ∫⁻ x, liminf (fun n => g n x) atTop ∂ρ :=
          lintegral_congr fun x => ((hlim x).liminf_eq).symm
      _ ≤ liminf (fun n => ∫⁻ x, g n x ∂ρ) atTop := lintegral_liminf_le hmeas
      _ ≤ ENNReal.ofReal |C| := by
          refine liminf_le_of_frequently_le' (Frequently.of_forall hbound)
  have hint2 : Integrable (fun x : ℝ => 1 + x ^ 2) ρ := by
    refine ⟨(by fun_prop : Continuous fun x : ℝ => 1 + x ^ 2).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => by positivity)]
    exact lt_of_le_of_lt hfin ENNReal.ofReal_lt_top
  have hintx : Integrable (fun x : ℝ => x) ρ := by
    refine hint2.mono' continuous_id.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    nlinarith [abs_nonneg x, sq_abs x, sq_nonneg (|x| - 1)]
  set ν := ρ.withDensity fun x => ENNReal.ofReal (1 + x ^ 2) with hνdef
  have hνfin : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    rw [hνdef, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact lt_of_le_of_lt hfin ENNReal.ofReal_lt_top
  -- the representation
  set a' : ℝ := a - ∫ x, x ∂ρ with ha'
  have hrep2 : ∀ z : ℂ, 0 < z.im → Φ z = a' + borelTransform ν z := by
    intro z hz
    rw [hrep z hz, herglotzRho, hb0]
    have hk : ∀ x : ℝ, (1 + x * z) / (x - z) = (1 + x ^ 2 : ℝ) * ((x : ℂ) - z)⁻¹ - x := by
      intro x
      have := ofReal_sub_ne_zero x hz
      push_cast
      field_simp
      ring
    have hI0 : Integrable (fun x : ℝ => ((1 + x ^ 2 : ℝ) : ℂ)) ρ := hint2.ofReal
    have hI1 : Integrable (fun x : ℝ => ((1 + x ^ 2 : ℝ) : ℂ) * ((x : ℂ) - z)⁻¹) ρ := by
      refine hI0.mul_of_top_left ?_
      exact memLp_top_of_bound (continuous_inv_sub hz.ne').aestronglyMeasurable (1 / |z.im|)
        (Eventually.of_forall fun x => norm_inv_sub_le x hz.ne')
    have hIx : Integrable (fun x : ℝ => ((x : ℝ) : ℂ)) ρ := hintx.ofReal
    rw [integral_congr_ae (Eventually.of_forall hk), integral_sub hI1 hIx]
    have hB : ∫ x, ((1 + x ^ 2 : ℝ) : ℂ) * ((x : ℂ) - z)⁻¹ ∂ρ = borelTransform ν z := by
      rw [borelTransform, hνdef, integral_withDensity_eq_integral_toReal_smul
        (by fun_prop) (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [Complex.real_smul]
      rw [ENNReal.toReal_ofReal (by positivity)]
    rw [hB, integral_complex_ofReal, ha']
    push_cast
    ring
  -- `a' = 0`
  have ha0 : a' = 0 := by
    have h1 : Tendsto (fun y : ℝ => Φ (y * I) - borelTransform ν (y * I)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hb : Tendsto (fun y : ℝ => (|C| + ν.real univ) / y) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hb
      filter_upwards [eventually_ge_atTop (max y₀ 1)] with y hy
      have hy0 : 0 < y := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hy)
      have hz : 0 < ((y : ℂ) * I).im := by simpa using hy0
      have h1 := hdec y ((le_max_left _ _).trans hy) hy0
      have h2 := norm_borelTransform_le ν hz
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
        Complex.I_re, mul_one, mul_zero, add_zero] at h2
      calc ‖Φ (y * I) - borelTransform ν (y * I)‖
          ≤ ‖Φ (y * I)‖ + ‖borelTransform ν (y * I)‖ := norm_sub_le _ _
        _ ≤ C / y + ν.real univ / y := add_le_add h1 h2
        _ ≤ (|C| + ν.real univ) / y := by
            rw [add_div]
            exact add_le_add (div_le_div_of_nonneg_right (le_abs_self C) hy0.le) le_rfl
    have h2 : Tendsto (fun y : ℝ => Φ (y * I) - borelTransform ν (y * I)) atTop
        (𝓝 (a' : ℂ)) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with y hy
      have hz : 0 < ((y : ℂ) * I).im := by simpa using hy
      rw [hrep2 _ hz]; ring
    exact_mod_cast tendsto_nhds_unique h2 h1
  refine ⟨ν, hνfin, fun z hz => ?_⟩
  rw [hrep2 z hz, ha0]
  simp

end DF
