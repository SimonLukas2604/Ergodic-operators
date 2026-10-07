/-
Formalization of Damanik–Fillman, *One-Dimensional Ergodic Schrödinger Operators I*, Chapter 1.

# Fourier transforms of uniformly Hölder measures  (book §1.8.2, Lemma 1.8.11 and
Theorem 1.8.10, pp. 68–70)

* `DF.cesaro g T = (1/T) ∫_0^T g` — the Cesàro average (1.8.24);
* `DF.integral_gaussian_le` — **Lemma 1.8.11**: for a finite `UαH` measure,
  `∫ e^{-T²(x-y)²} dμ(y) ≤ C T^{-α}` uniformly in `x`;
* `DF.integral_gaussian_fourier` — the Gaussian integral
  `∫ e^{-t²/T²} e^{-ist} dt = √π T e^{-T²s²/4}`;
* `DF.cesaro_fourier_le` — **Theorem 1.8.10**: `⟨|(fμ)^|²⟩_T ≤ C ‖f‖²_{L²(μ)} T^{-α}`, for
  bounded Borel `f`.

Deviation: Theorem 1.8.10 is proved for bounded Borel `f` (which is all that is needed later;
the book allows `f ∈ L²(μ)`), and compact support of `μ` is not needed.

No `Statement` props are introduced in this file.
-/
import DamanikFillman.Ch1.HausdorffDecomposition
import DamanikFillman.Ch1.Localization

noncomputable section

open scoped ENNReal NNReal Topology ComplexConjugate
open MeasureTheory Set Filter Real

namespace DF

/-- The Cesàro average `⟨g⟩_T = (1/T) ∫_0^T g(t) dt` (1.8.24). -/
def cesaro (g : ℝ → ℝ) (T : ℝ) : ℝ := (1 / T) * ∫ t in (0 : ℝ)..T, g t

variable {μ : Measure ℝ} {α : ℝ}

lemma abs_floor_bound {T : ℝ} (hT : 0 < T) (x y : ℝ) :
    |((⌊T * (y - x)⌋ : ℤ) : ℝ)| - 1 ≤ |T * (y - x)| := by
  set j := ⌊T * (y - x)⌋
  have h1 : (j : ℝ) ≤ T * (y - x) := Int.floor_le _
  have h2 : T * (y - x) < j + 1 := Int.lt_floor_add_one _
  rcases le_or_gt 0 (j : ℝ) with hj | hj
  · rw [abs_of_nonneg hj]
    have : 0 ≤ T * (y - x) := le_trans hj h1
    rw [abs_of_nonneg this]; linarith
  · rw [abs_of_neg hj]
    have : T * (y - x) < 0 ∨ 0 ≤ T * (y - x) := lt_or_ge _ 0
    rcases this with h | h
    · rw [abs_of_neg h]; linarith
    · rw [abs_of_nonneg h]; linarith

/-- **Lemma 1.8.11**: for a finite `UαH` measure there is `C` with
`∫ e^{-T²(x-y)²} dμ(y) ≤ C T^{-α}` for all `x` and `T > 0`. -/
theorem integral_gaussian_le [IsFiniteMeasure μ] (hα : 0 ≤ α) (hU : UalphaH μ α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x T : ℝ, 0 < T →
      ∫ y, Real.exp (-(T ^ 2 * (x - y) ^ 2)) ∂μ ≤ C * T ^ (-α) := by
  obtain ⟨C₀, hC₀⟩ := hU
  set C' := max C₀ 0
  set K := Real.exp 1 * geomZ 1
  set M := μ.real univ
  have hK : 0 ≤ K := mul_nonneg (Real.exp_pos 1).le (geomZ_nonneg 1)
  have hsumm : Summable fun j : ℤ => Real.exp (1 - |(j : ℝ)|) := by
    have := (summable_exp_neg_abs (a := 1) one_pos).mul_left (Real.exp 1)
    refine this.congr fun j => ?_
    rw [← Real.exp_add]; ring_nf
  refine ⟨max (C' * K) M, le_max_of_le_right measureReal_nonneg, fun x T hT => ?_⟩
  have hint : Integrable (fun y => Real.exp (-(T ^ 2 * (x - y) ^ 2))) μ :=
    Integrable.of_bound (by fun_prop) 1 (Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg (x - y), sq_nonneg T]))
  rcases lt_or_ge T 1 with hT1 | hT1
  · -- small `T`: trivial bound
    have h1 : ∫ y, Real.exp (-(T ^ 2 * (x - y) ^ 2)) ∂μ ≤ M := by
      have := norm_integral_le_of_norm_le_const (μ := μ) (C := 1)
        (f := fun y => Real.exp (-(T ^ 2 * (x - y) ^ 2))) (Eventually.of_forall fun y => by
          rw [Real.norm_of_nonneg (Real.exp_pos _).le]
          exact Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg (x - y), sq_nonneg T]))
      rw [one_mul] at this
      exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)
    have h2 : 1 ≤ T ^ (-α) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hT hT1.le (by linarith)
    calc ∫ y, Real.exp (-(T ^ 2 * (x - y) ^ 2)) ∂μ ≤ M := h1
      _ ≤ M * T ^ (-α) := le_mul_of_one_le_right measureReal_nonneg h2
      _ ≤ max (C' * K) M * T ^ (-α) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hT.le _)
  · -- large `T`: partition into intervals of length `1/T`
    set J : ℤ → Set ℝ := fun j => Icc (x + j / T) (x + (j + 1) / T)
    have hJ : ∀ j, μ (J j) ≤ ENNReal.ofReal (C' * T ^ (-α)) := by
      intro j
      have hlen : x + (j + 1) / T - (x + j / T) = 1 / T := by field_simp; ring
      have hle : x + (j : ℝ) / T ≤ x + (j + 1) / T := by
        have := one_div_pos.2 hT; linarith
      refine (hC₀ _ _ hle (by rw [hlen]; exact (div_le_one hT).2 hT1)).trans ?_
      rw [hlen, one_div, Real.inv_rpow hT.le, ← Real.rpow_neg hT.le]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg hT.le _))
    have hpt : ∀ y, ENNReal.ofReal (Real.exp (-(T ^ 2 * (x - y) ^ 2))) ≤
        ∑' j : ℤ, (J j).indicator (fun _ => ENNReal.ofReal (Real.exp (1 - |(j : ℝ)|))) y := by
      intro y
      set j := ⌊T * (y - x)⌋
      have hmem : y ∈ J j := by
        have h1 : (j : ℝ) ≤ T * (y - x) := Int.floor_le _
        have h2 : T * (y - x) < j + 1 := Int.lt_floor_add_one _
        constructor
        · rw [← le_sub_iff_add_le', div_le_iff₀ hT]; linarith
        · rw [← sub_le_iff_le_add', le_div_iff₀ hT]; linarith
      refine le_trans ?_ (ENNReal.le_tsum j)
      rw [indicator_of_mem hmem]
      refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
      have hb := abs_floor_bound hT x y
      have hsq : T ^ 2 * (x - y) ^ 2 = |T * (y - x)| ^ 2 := by rw [sq_abs]; ring
      rw [hsq]
      rcases le_or_gt (|(j : ℝ)| - 1) 0 with h | h
      · nlinarith [sq_nonneg |T * (y - x)|]
      · have hj2 : (2 : ℝ) ≤ |(j : ℝ)| := by
          have h' : (1 : ℝ) < ((|j| : ℤ) : ℝ) := by rw [Int.cast_abs]; linarith
          have : (1 : ℤ) < |j| := by exact_mod_cast h'
          have : (2 : ℤ) ≤ |j| := by omega
          rw [← Int.cast_abs]; exact_mod_cast this
        nlinarith
    have hlint : ∫⁻ y, ENNReal.ofReal (Real.exp (-(T ^ 2 * (x - y) ^ 2))) ∂μ ≤
        ENNReal.ofReal (C' * T ^ (-α) * K) := by
      calc ∫⁻ y, ENNReal.ofReal (Real.exp (-(T ^ 2 * (x - y) ^ 2))) ∂μ
          ≤ ∫⁻ y, ∑' j : ℤ, (J j).indicator
              (fun _ => ENNReal.ofReal (Real.exp (1 - |(j : ℝ)|))) y ∂μ := lintegral_mono hpt
        _ = ∑' j : ℤ, ENNReal.ofReal (Real.exp (1 - |(j : ℝ)|)) * μ (J j) := by
            rw [lintegral_tsum fun j => (measurable_const.indicator measurableSet_Icc).aemeasurable]
            congr 1; funext j
            rw [lintegral_indicator_const measurableSet_Icc]
        _ ≤ ∑' j : ℤ, ENNReal.ofReal (Real.exp (1 - |(j : ℝ)|)) *
              ENNReal.ofReal (C' * T ^ (-α)) := ENNReal.tsum_le_tsum fun j =>
            mul_le_mul_right (hJ j) _
        _ = ENNReal.ofReal (C' * T ^ (-α)) * ENNReal.ofReal (∑' j : ℤ, Real.exp (1 - |(j : ℝ)|)) := by
            rw [ENNReal.tsum_mul_right, ENNReal.ofReal_tsum_of_nonneg (fun j => (Real.exp_pos _).le)
              hsumm, mul_comm]
        _ = ENNReal.ofReal (C' * T ^ (-α) * K) := by
            rw [← ENNReal.ofReal_mul (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hT.le _))]
            congr 2
            simp only [K, geomZ]
            rw [← tsum_mul_left]
            congr 1; funext j
            rw [← Real.exp_add]; ring_nf
    have hreal : ∫ y, Real.exp (-(T ^ 2 * (x - y) ^ 2)) ∂μ ≤ C' * T ^ (-α) * K := by
      rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun y => (Real.exp_pos _).le)
        hint.aestronglyMeasurable]
      refine (ENNReal.toReal_mono ENNReal.ofReal_ne_top hlint).trans ?_
      rw [ENNReal.toReal_ofReal (mul_nonneg (mul_nonneg (le_max_right _ _)
        (Real.rpow_nonneg hT.le _)) hK)]
    calc ∫ y, Real.exp (-(T ^ 2 * (x - y) ^ 2)) ∂μ ≤ C' * T ^ (-α) * K := hreal
      _ = C' * K * T ^ (-α) := by ring
      _ ≤ max (C' * K) M * T ^ (-α) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hT.le _)

/-- The Gaussian Fourier integral `∫ e^{-t²/T²} e^{-ist} dt = √π T e^{-(T/2)² s²}`. -/
lemma integral_gaussian_fourier {T : ℝ} (hT : 0 < T) (s : ℝ) :
    ∫ t : ℝ, ((Real.exp (-(t ^ 2 / T ^ 2)) : ℝ) : ℂ) * Complex.exp (-((s * t : ℝ) : ℂ) * Complex.I) =
      ((Real.sqrt π * T * Real.exp (-((T / 2) ^ 2 * s ^ 2)) : ℝ) : ℂ) := by
  have hT' : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  set b : ℂ := -(1 / (T : ℂ) ^ 2)
  have hbre : b.re < 0 := by
    have : b = ((-(1 / T ^ 2) : ℝ) : ℂ) := by simp [b]
    rw [this, Complex.ofReal_re]
    have : 0 < 1 / T ^ 2 := by positivity
    linarith
  have h := integral_cexp_quadratic hbre (-(s : ℂ) * Complex.I) 0
  have hlhs : (fun t : ℝ => ((Real.exp (-(t ^ 2 / T ^ 2)) : ℝ) : ℂ) *
      Complex.exp (-((s * t : ℝ) : ℂ) * Complex.I)) =
      fun t : ℝ => Complex.exp (b * (t : ℂ) ^ 2 + (-(s : ℂ) * Complex.I) * t + 0) := by
    funext t
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    simp only [b]
    push_cast
    field_simp
    ring
  rw [hlhs, h]
  have h1 : (π : ℂ) / -b = ((π * T ^ 2 : ℝ) : ℂ) := by
    simp only [b, neg_neg]; push_cast; field_simp
  have h2 : ((π * T ^ 2 : ℝ) : ℂ) ^ (1 / 2 : ℂ) = ((Real.sqrt π * T : ℝ) : ℂ) := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by positivity)]
    congr 1
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by positivity), Real.sqrt_sq hT.le]
  have h3 : (0 : ℂ) - (-(s : ℂ) * Complex.I) ^ 2 / (4 * b) =
      ((-((T / 2) ^ 2 * s ^ 2) : ℝ) : ℂ) := by
    simp only [b]
    push_cast
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [h1, h2, h3, ← Complex.ofReal_exp, ← Complex.ofReal_mul]

/-- The Fourier transform of `f μ`, `t ↦ ∫ e^{-ixt} f(x) dμ(x)` (cf. (1.8.31)). -/
def fourierDens (μ : Measure ℝ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ x, f x * Complex.exp (-((x * t : ℝ) : ℂ) * Complex.I) ∂μ

lemma norm_expI (r : ℝ) : ‖Complex.exp (-((r : ℝ) : ℂ) * Complex.I)‖ = 1 := norm_exp_neg_mul_I r

lemma continuous_fourierDens [IsFiniteMeasure μ] {f : ℝ → ℂ} (hf : IsBddBorel f) :
    Continuous (fourierDens μ f) := by
  obtain ⟨M, hM⟩ := hf.bdd
  have hfm := hf.meas
  refine continuous_of_dominated (bound := fun _ => M) (fun t => ?_) (fun t => ?_)
    (integrable_const _) (Eventually.of_forall fun x => by fun_prop)
  · exact (hfm.mul (by fun_prop)).aestronglyMeasurable
  · exact Eventually.of_forall fun x => by rw [norm_mul, norm_expI, mul_one]; exact hM x

lemma norm_fourierDens_le [IsFiniteMeasure μ] {f : ℝ → ℂ} {M : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) (t : ℝ) :
    ‖fourierDens μ f t‖ ≤ M * μ.real univ :=
  norm_integral_le_of_norm_le_const (Eventually.of_forall fun x => by
    rw [norm_mul, norm_expI, mul_one]; exact hM x)

/-- `|f̂μ(t)|² = ∫∫ f(x) conj f(y) e^{-i(x-y)t} dμ(x) dμ(y)`. -/
lemma normSq_fourierDens [IsFiniteMeasure μ] (f : ℝ → ℂ) (t : ℝ) :
    ((‖fourierDens μ f t‖ ^ 2 : ℝ) : ℂ) = ∫ p, f p.1 * conj (f p.2) *
      Complex.exp (-(((p.1 - p.2) * t : ℝ) : ℂ) * Complex.I) ∂(μ.prod μ) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj', fourierDens, ← integral_conj, ← integral_prod_mul]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only [map_mul]
  rw [← Complex.exp_conj]
  have : Complex.exp (-(((p.1 - p.2) * t : ℝ) : ℂ) * Complex.I) =
      Complex.exp (-((p.1 * t : ℝ) : ℂ) * Complex.I) *
        Complex.exp ((starRingEnd ℂ) (-((p.2 * t : ℝ) : ℂ) * Complex.I)) := by
    rw [← Complex.exp_add]; congr 1
    simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring
  rw [this]; ring

set_option maxHeartbeats 1000000 in
/-- **Theorem 1.8.10**: for a finite `UαH` measure `μ` there is `C` such that
`⟨|(fμ)^|²⟩_T ≤ C ‖f‖²_{L²(μ)} T^{-α}` for all bounded Borel `f` and `T > 0`. -/
theorem cesaro_fourierDens_le [IsFiniteMeasure μ] (hα : 0 ≤ α) (hU : UalphaH μ α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : ℝ → ℂ, IsBddBorel f → ∀ T : ℝ, 0 < T →
      cesaro (fun t => ‖fourierDens μ f t‖ ^ 2) T ≤ C * (∫ x, ‖f x‖ ^ 2 ∂μ) * T ^ (-α) := by
  obtain ⟨C₀, hC₀, hG⟩ := integral_gaussian_le hα hU
  refine ⟨Real.exp 1 * Real.sqrt π * C₀ * 2 ^ α, by positivity, fun f hf T hT => ?_⟩
  obtain ⟨M, hM⟩ := hf.bdd
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hfm := hf.meas
  set F := fourierDens μ f
  set G : ℝ → ℝ := fun t => Real.exp (-(t ^ 2 / T ^ 2))
  set Kc : ℝ × ℝ → ℝ := fun p => Real.sqrt π * T * Real.exp (-((T / 2) ^ 2 * (p.1 - p.2) ^ 2))
  have hFc : Continuous F := continuous_fourierDens hf
  have hFb : ∀ t, ‖F t‖ ≤ M * μ.real univ := norm_fourierDens_le hM
  have hGint : Integrable G := by
    have := integrable_exp_neg_mul_sq (b := 1 / T ^ 2) (by positivity)
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp only [G]; congr 1; ring
  have hGF : Integrable fun t => G t * ‖F t‖ ^ 2 := by
    refine (hGint.mul_const ((M * μ.real univ) ^ 2)).mono' ?_ (Eventually.of_forall fun t => ?_)
    · exact ((by fun_prop : Continuous G).mul (hFc.norm.pow 2)).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hFb t) 2)
        (Real.exp_pos _).le
  -- Step 1: Cesàro average bounded by the Gaussian average
  have hstep1 : cesaro (fun t => ‖F t‖ ^ 2) T ≤ (Real.exp 1 / T) * ∫ t, G t * ‖F t‖ ^ 2 := by
    unfold cesaro
    rw [intervalIntegral.integral_of_le hT.le, div_eq_mul_one_div (Real.exp 1), mul_comm (Real.exp 1),
      mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc ∫ t in Ioc 0 T, ‖F t‖ ^ 2 ≤ ∫ t in Ioc 0 T, Real.exp 1 * (G t * ‖F t‖ ^ 2) := by
          refine setIntegral_mono_on ((hFc.norm.pow 2).integrableOn_Icc.mono_set
            Ioc_subset_Icc_self) (hGF.const_mul _).integrableOn measurableSet_Ioc fun t ht => ?_
          have hG1 : Real.exp (-1) ≤ G t := Real.exp_le_exp.2 (by
            rw [neg_le_neg_iff, div_le_one (by positivity)]
            exact pow_le_pow_left₀ ht.1.le ht.2 2)
          have : 1 ≤ Real.exp 1 * G t := by
            calc (1 : ℝ) = Real.exp 1 * Real.exp (-1) := by rw [← Real.exp_add]; simp
              _ ≤ Real.exp 1 * G t := mul_le_mul_of_nonneg_left hG1 (Real.exp_pos _).le
          nlinarith [sq_nonneg ‖F t‖]
      _ ≤ ∫ t, Real.exp 1 * (G t * ‖F t‖ ^ 2) := setIntegral_le_integral (hGF.const_mul _)
          (Eventually.of_forall fun t => by positivity)
      _ = Real.exp 1 * ∫ t, G t * ‖F t‖ ^ 2 := integral_const_mul _ _
  -- Step 2: Fubini and the Gaussian integral
  have hstep2 : ((∫ t, G t * ‖F t‖ ^ 2 : ℝ) : ℂ) =
      ∫ p, f p.1 * conj (f p.2) * (Kc p : ℂ) ∂(μ.prod μ) := by
    rw [← integral_complex_ofReal]
    have hpush : ∀ t, ((G t * ‖F t‖ ^ 2 : ℝ) : ℂ) = ∫ p, (G t : ℂ) * (f p.1 * conj (f p.2) *
        Complex.exp (-(((p.1 - p.2) * t : ℝ) : ℂ) * Complex.I)) ∂(μ.prod μ) := by
      intro t
      rw [Complex.ofReal_mul, normSq_fourierDens, integral_const_mul]
    simp_rw [hpush]
    have hint : Integrable (Function.uncurry fun (t : ℝ) (p : ℝ × ℝ) => (G t : ℂ) *
        (f p.1 * conj (f p.2) * Complex.exp (-(((p.1 - p.2) * t : ℝ) : ℂ) * Complex.I)))
        (volume.prod (μ.prod μ)) := by
      have hb : Integrable (fun z : ℝ × (ℝ × ℝ) => G z.1 * (fun _ : ℝ × ℝ => M ^ 2) z.2)
          (volume.prod (μ.prod μ)) := hGint.mul_prod (integrable_const _)
      refine hb.mono' ?_ (Eventually.of_forall fun z => ?_)
      · have : Measurable fun z : ℝ × (ℝ × ℝ) => (G z.1 : ℂ) * (f z.2.1 * conj (f z.2.2) *
            Complex.exp (-(((z.2.1 - z.2.2) * z.1 : ℝ) : ℂ) * Complex.I)) := by
          have h1 : Measurable fun z : ℝ × (ℝ × ℝ) => f z.2.1 := hfm.comp (by fun_prop)
          have h2 : Measurable fun z : ℝ × (ℝ × ℝ) => conj (f z.2.2) :=
            Complex.continuous_conj.measurable.comp (hfm.comp (by fun_prop))
          have h3 : Measurable fun z : ℝ × (ℝ × ℝ) => (G z.1 : ℂ) := by
            simp only [G]; fun_prop
          have h4 : Measurable fun z : ℝ × (ℝ × ℝ) =>
              Complex.exp (-(((z.2.1 - z.2.2) * z.1 : ℝ) : ℂ) * Complex.I) := by fun_prop
          exact h3.mul ((h1.mul h2).mul h4)
        exact this.aestronglyMeasurable
      · show ‖(G z.1 : ℂ) * (f z.2.1 * conj (f z.2.2) *
          Complex.exp (-(((z.2.1 - z.2.2) * z.1 : ℝ) : ℂ) * Complex.I))‖ ≤ G z.1 * M ^ 2
        have hfz : ‖f z.2.1‖ * ‖f z.2.2‖ ≤ M ^ 2 := by
          nlinarith [hM z.2.1, hM z.2.2, norm_nonneg (f z.2.1), norm_nonneg (f z.2.2)]
        rw [norm_mul, norm_mul, norm_mul, norm_expI, mul_one, Complex.norm_real,
          Real.norm_of_nonneg (Real.exp_pos _).le, RCLike.norm_conj]
        exact mul_le_mul_of_nonneg_left hfz (Real.exp_pos _).le
    rw [integral_integral_swap hint]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only
    have : ∀ t : ℝ, (G t : ℂ) * (f p.1 * conj (f p.2) *
        Complex.exp (-(((p.1 - p.2) * t : ℝ) : ℂ) * Complex.I)) = f p.1 * conj (f p.2) *
        (((Real.exp (-(t ^ 2 / T ^ 2)) : ℝ) : ℂ) *
          Complex.exp (-(((p.1 - p.2) * t : ℝ) : ℂ) * Complex.I)) := fun t => by
      simp only [G]; ring
    simp_rw [this]
    rw [integral_const_mul, integral_gaussian_fourier hT (p.1 - p.2)]
  -- Step 3: the Schur-type bound
  have hKc : ∀ p, 0 ≤ Kc p := fun p => by positivity
  have hKint : ∀ g : ℝ × ℝ → ℝ, Measurable g → (∀ p, ‖g p‖ ≤ M ^ 2) →
      Integrable (fun p => g p * Kc p) (μ.prod μ) := by
    intro g hgm hgb
    refine Integrable.of_bound (C := M ^ 2 * (Real.sqrt π * T)) ?_ (Eventually.of_forall fun p => ?_)
    · exact (hgm.mul (by simp only [Kc]; fun_prop)).aestronglyMeasurable
    · rw [norm_mul, Real.norm_of_nonneg (hKc p)]
      refine mul_le_mul (hgb p) ?_ (hKc p) (by positivity)
      simp only [Kc]
      exact mul_le_of_le_one_right (by positivity)
        (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg (p.1 - p.2), sq_nonneg (T / 2)]))
  have hfx : Measurable fun p : ℝ × ℝ => ‖f p.1‖ ^ 2 := (hfm.comp measurable_fst).norm.pow_const 2
  have hfy : Measurable fun p : ℝ × ℝ => ‖f p.2‖ ^ 2 := (hfm.comp measurable_snd).norm.pow_const 2
  have hb1 : ∀ p : ℝ × ℝ, ‖‖f p.1‖ ^ 2‖ ≤ M ^ 2 := fun p => by
    rw [norm_pow, norm_norm]; exact pow_le_pow_left₀ (norm_nonneg _) (hM _) 2
  have hb2 : ∀ p : ℝ × ℝ, ‖‖f p.2‖ ^ 2‖ ≤ M ^ 2 := fun p => by
    rw [norm_pow, norm_norm]; exact pow_le_pow_left₀ (norm_nonneg _) (hM _) 2
  have hsym : ∫ p, ‖f p.2‖ ^ 2 * Kc p ∂(μ.prod μ) = ∫ p, ‖f p.1‖ ^ 2 * Kc p ∂(μ.prod μ) := by
    rw [← integral_prod_swap]
    congr 1; funext p
    simp only [Prod.fst_swap, Prod.snd_swap, Kc]
    congr 3; ring
  have hinner : ∀ x, ∫ y, Kc (x, y) ∂μ ≤ Real.sqrt π * T * (C₀ * (T / 2) ^ (-α)) := by
    intro x
    simp only [Kc]
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact hG x (T / 2) (by positivity)
  have hstep3 : ∫ t, G t * ‖F t‖ ^ 2 ≤
      Real.sqrt π * T * (C₀ * (T / 2) ^ (-α)) * ∫ x, ‖f x‖ ^ 2 ∂μ := by
    have h0 : ∫ t, G t * ‖F t‖ ^ 2 = ‖((∫ t, G t * ‖F t‖ ^ 2 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun t => by positivity)]
    rw [h0, hstep2]
    calc ‖∫ p, f p.1 * conj (f p.2) * (Kc p : ℂ) ∂(μ.prod μ)‖
        ≤ ∫ p, ‖f p.1 * conj (f p.2) * (Kc p : ℂ)‖ ∂(μ.prod μ) := norm_integral_le_integral_norm _
      _ ≤ ∫ p, ((‖f p.1‖ ^ 2 * Kc p) + (‖f p.2‖ ^ 2 * Kc p)) / 2 ∂(μ.prod μ) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun p => norm_nonneg _)
            (((hKint _ hfx hb1).add (hKint _ hfy hb2)).div_const 2)
            (Eventually.of_forall fun p => ?_)
          simp only
          rw [norm_mul, norm_mul, RCLike.norm_conj, Complex.norm_real, Real.norm_of_nonneg (hKc p)]
          nlinarith [sq_nonneg (‖f p.1‖ - ‖f p.2‖), hKc p]
      _ = ∫ p, ‖f p.1‖ ^ 2 * Kc p ∂(μ.prod μ) := by
          rw [integral_div, integral_add (hKint _ hfx hb1) (hKint _ hfy hb2), hsym]; ring
      _ = ∫ x, ∫ y, ‖f x‖ ^ 2 * Kc (x, y) ∂μ ∂μ := integral_prod _ (hKint _ hfx hb1)
      _ = ∫ x, ‖f x‖ ^ 2 * ∫ y, Kc (x, y) ∂μ ∂μ := by
          congr 1; funext x; rw [integral_const_mul]
      _ ≤ ∫ x, ‖f x‖ ^ 2 * (Real.sqrt π * T * (C₀ * (T / 2) ^ (-α))) ∂μ := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun x => mul_nonneg (sq_nonneg _)
            (integral_nonneg fun y => hKc _)) ((Integrable.of_bound (C := M ^ 2)
              (hfm.norm.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun x => by
                rw [norm_pow, norm_norm]
                exact pow_le_pow_left₀ (norm_nonneg _) (hM _) 2)).mul_const _)
            (Eventually.of_forall fun x => mul_le_mul_of_nonneg_left (hinner x) (sq_nonneg _))
      _ = Real.sqrt π * T * (C₀ * (T / 2) ^ (-α)) * ∫ x, ‖f x‖ ^ 2 ∂μ := by
          rw [integral_mul_const]; ring
  -- Step 4: combine
  have hpow : (T / 2) ^ (-α) = 2 ^ α * T ^ (-α) := by
    rw [Real.div_rpow hT.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      div_eq_mul_inv, inv_inv, mul_comm]
  calc cesaro (fun t => ‖F t‖ ^ 2) T ≤ (Real.exp 1 / T) * ∫ t, G t * ‖F t‖ ^ 2 := hstep1
    _ ≤ (Real.exp 1 / T) * (Real.sqrt π * T * (C₀ * (T / 2) ^ (-α)) * ∫ x, ‖f x‖ ^ 2 ∂μ) :=
        mul_le_mul_of_nonneg_left hstep3 (by positivity)
    _ = Real.exp 1 * Real.sqrt π * C₀ * 2 ^ α * (∫ x, ‖f x‖ ^ 2 ∂μ) * T ^ (-α) := by
        rw [hpow]; field_simp

end DF
