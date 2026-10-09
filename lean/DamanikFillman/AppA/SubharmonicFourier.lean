/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Appendix A.3: Fourier coefficients of bounded subharmonic functions (Theorem A.3.1)

`DF.subharmonicFourierDecayStatement_holds`: bounded subharmonic functions `|u| ≤ M` on the
annulus `A_ρ` satisfy `|û(k)| ≤ C M / |k|` on the unit circle, with `C` depending only on `ρ`.

Proof (as in the book): write `u = -Φ_μ + h` on `A_{ρ/2}` (Theorem A.3.2), with
`μ(ℂ) ≤ C M` and `|h| ≤ C M` on `A_{ρ/3}` (Theorem A.3.4).
* `|Φ̂_μ(k)| ≤ μ(ℂ) / (2|k|)` by Fubini and Lemma A.3.5 (`norm_circleCoeff_log_le`), see
  `norm_circleCoeff_logPotential_le`;
* `|ĥ(k)| ≤ ‖∂_t h(e(t))‖_∞ / (2π|k|)` by integration by parts
  (`norm_circleCoeff_le_of_deriv`), and the gradient of `h` on the unit circle is bounded by
  `C' M` (`abs_Dv_harmonic_le`, a Cauchy estimate obtained from the mean value property with
  the mollifier).
-/
import DamanikFillman.AppA.RieszBound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLog

noncomputable section

open Real Complex Metric Set Filter Topology MeasureTheory Laplacian InnerProductSpace
open scoped Convolution

namespace DF

namespace Distr

/-! ### Integrals of `log |e(t) - w|` -/

lemma ex_eq_circleMap (t : ℝ) : ex t = circleMap 0 1 (2 * π * t) := by
  unfold circleMap ex
  simp only [zero_add, Complex.ofReal_one, one_mul]
  congr 1; push_cast; ring

lemma integral_log_norm_ex_sub (w : ℂ) :
    ∫ t in (0 : ℝ)..1, Real.log ‖ex t - w‖ = Real.posLog ‖w‖ := by
  have h := circleAverage_log_norm_sub_const_eq_posLog (a := w)
  rw [circleAverage_def, smul_eq_mul] at h
  have hpi : (2 * π) ≠ 0 := by positivity
  have h2 := intervalIntegral.integral_comp_mul_left
    (fun θ => Real.log ‖circleMap 0 1 θ - w‖) (a := 0) (b := 1) hpi
  simp only [mul_zero, mul_one, smul_eq_mul] at h2
  simp_rw [ex_eq_circleMap]
  rw [h2, ← h]

lemma abs_log_le (a c : ℝ) (hc : 0 ≤ c) (ha : a ≤ c) : |a| ≤ 2 * c - a := by
  rcases le_total 0 a with h | h
  · rw [abs_of_nonneg h]; linarith
  · rw [abs_of_nonpos h]; linarith

lemma integral_abs_log_norm_ex_sub_le {w : ℂ} (hw : ‖w‖ ≤ 2) :
    ∫ t in (0 : ℝ)..1, |Real.log ‖ex t - w‖| ≤ 2 * Real.log 3 := by
  have hint := intervalIntegrable_log_norm_ex_sub w
  have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hpt : ∀ t, |Real.log ‖ex t - w‖| ≤ 2 * Real.log 3 - Real.log ‖ex t - w‖ := by
    intro t
    refine abs_log_le _ _ hlog3 ?_
    by_cases h0 : ‖ex t - w‖ = 0
    · rw [h0, Real.log_zero]; exact hlog3
    · refine Real.log_le_log (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)) ?_
      calc ‖ex t - w‖ ≤ ‖ex t‖ + ‖w‖ := norm_sub_le _ _
        _ ≤ 3 := by rw [norm_ex]; linarith
  calc ∫ t in (0 : ℝ)..1, |Real.log ‖ex t - w‖|
      ≤ ∫ t in (0 : ℝ)..1, (2 * Real.log 3 - Real.log ‖ex t - w‖) :=
        intervalIntegral.integral_mono_on zero_le_one hint.abs (intervalIntegrable_const.sub hint)
          fun t _ => hpt t
    _ = 2 * Real.log 3 - Real.posLog ‖w‖ := by
        rw [intervalIntegral.integral_sub intervalIntegrable_const hint,
          integral_log_norm_ex_sub, intervalIntegral.integral_const, smul_eq_mul]
        ring
    _ ≤ 2 * Real.log 3 := by linarith [Real.posLog_nonneg (x := ‖w‖)]

/-! ### Fourier coefficients of logarithmic potentials -/

/-- **`|Φ̂_μ(k)| ≤ μ(ℂ)/(2|k|)`**, by Fubini and Lemma A.3.5. -/
theorem norm_circleCoeff_logPotential_le {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμS : μ (closedBall 0 2)ᶜ = 0) {k : ℤ} (hk : k ≠ 0) :
    IntervalIntegrable (fun t => ex (-(k * t)) * ((logPotential μ (ex t)).toReal : ℂ))
        volume 0 1 ∧
      ‖∫ t in (0 : ℝ)..1, ex (-(k * t)) * ((logPotential μ (ex t)).toReal : ℂ)‖ ≤
        μ.real univ / (2 * |(k : ℝ)|) := by
  set ν : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1) with hν
  have hμ := integrable_norm_of_bounded hμS
  set F : ℂ × ℝ → ℂ := fun p => ex (-(k * p.2)) * (Real.log ‖ex p.2 - p.1‖ : ℂ) with hF
  have hexc : Continuous (fun t : ℝ => ex (-(k * t))) :=
    continuous_ex.comp (continuous_const.mul continuous_id).neg
  have hmeas : AEStronglyMeasurable F (μ.prod ν) := by
    rw [hF]
    exact ((hexc.measurable.comp measurable_snd).mul (Complex.measurable_ofReal.comp
      (Real.measurable_log.comp (measurable_norm.comp
        ((continuous_ex.measurable.comp measurable_snd).sub measurable_fst))))).aestronglyMeasurable
  have hnormF : ∀ w t, ‖F (w, t)‖ = |Real.log ‖ex t - w‖| := fun w t => by
    simp only [hF, norm_mul, norm_ex, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have hae : ∀ᵐ w ∂μ, w ∈ closedBall (0 : ℂ) 2 :=
    measure_eq_zero_iff_ae_notMem.1 hμS |>.mono fun w hw => by simpa using hw
  have hlogν : ∀ w : ℂ, Integrable (fun t => Real.log ‖ex t - w‖) ν := fun w =>
    (intervalIntegrable_log_norm_ex_sub w).1
  have hFt : ∀ w : ℂ, Integrable (fun t => F (w, t)) ν := by
    intro w
    refine ((hlogν w).norm).mono' ?_ (Eventually.of_forall fun t =>
      le_of_eq (by rw [hnormF, Real.norm_eq_abs]))
    exact (hexc.measurable.mul (Complex.measurable_ofReal.comp (Real.measurable_log.comp
      (measurable_norm.comp (continuous_ex.measurable.sub_const w))))).aestronglyMeasurable
  have hFint : Integrable F (μ.prod ν) := by
    rw [integrable_prod_iff hmeas]
    refine ⟨Eventually.of_forall hFt, ?_⟩
    refine (integrable_const (2 * Real.log 3)).mono' hmeas.norm.integral_prod_right' ?_
    filter_upwards [hae] with w hw
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    simp_rw [hnormF]
    rw [hν, ← intervalIntegral.integral_of_le zero_le_one]
    exact integral_abs_log_norm_ex_sub_le (by simpa using hw)
  -- identification of the integrand for a.e. `t`
  have hatoms : ∀ᵐ t ∂ν, μ {ex t} = 0 := by
    have hc : Set.Countable {z : ℂ | 0 < μ {z}} :=
      Measure.countable_meas_pos_of_disjoint_iUnion (As := fun z : ℂ => ({z} : Set ℂ))
        (fun z => measurableSet_singleton z) (fun a b h => by simpa [Function.onFun] using h)
    have hT : Set.Countable (Ioc (0 : ℝ) 1 ∩ ex ⁻¹' {z : ℂ | 0 < μ {z}}) :=
      MapsTo.countable_of_injOn (f := ex) (fun t ht => ht.2)
        (fun x hx y hy hxy => ex_injOn hx.1 hy.1 hxy) hc
    rw [hν, ae_restrict_iff' measurableSet_Ioc]
    have h0 : volume (Ioc (0 : ℝ) 1 ∩ ex ⁻¹' {z : ℂ | 0 < μ {z}}) = 0 := hT.measure_zero _
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with t ht ht01
    by_contra hpos
    exact ht ⟨ht01, pos_iff_ne_zero.2 hpos⟩
  have hpt : ∀ᵐ t ∂ν, ex (-(k * t)) * ((logPotential μ (ex t)).toReal : ℂ) =
      -∫ w, F (w, t) ∂μ := by
    filter_upwards [hatoms, hFint.prod_left_ae] with t hz hzi
    have hint : Integrable (fun w => Real.log ‖ex t - w‖) μ := by
      refine hzi.norm.mono' ?_ (Eventually.of_forall fun w => ?_)
      · exact (Real.measurable_log.comp (measurable_norm.comp
          (measurable_const.sub measurable_id))).aestronglyMeasurable
      · show ‖Real.log ‖ex t - w‖‖ ≤ ‖F (w, t)‖
        rw [hnormF, Real.norm_eq_abs]
    rw [toReal_logPotential_eq hμ hz hint]
    simp only [hF]
    rw [integral_const_mul, integral_complex_ofReal]
    push_cast
    ring
  have hJ : Integrable (fun t => ∫ w, F (w, t) ∂μ) ν := hFint.integral_prod_right
  have hII : Integrable (fun t => ex (-(k * t)) * ((logPotential μ (ex t)).toReal : ℂ)) ν :=
    hJ.neg.congr (hpt.mono fun t ht => ht.symm)
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2 hII, ?_⟩
  rw [intervalIntegral.integral_of_le zero_le_one, ← hν, integral_congr_ae hpt, integral_neg,
    norm_neg, ← integral_integral_swap (f := fun w t => F (w, t)) hFint]
  calc ‖∫ w, ∫ t, F (w, t) ∂ν ∂μ‖ ≤ ∫ _w, 1 / (2 * |(k : ℝ)|) ∂μ := by
        refine norm_integral_le_of_norm_le (integrable_const _) (Eventually.of_forall fun w => ?_)
        have h := norm_circleCoeff_log_le w hk
        unfold circleCoeff at h
        rw [intervalIntegral.integral_of_le zero_le_one] at h
        exact h
    _ = μ.real univ / (2 * |(k : ℝ)|) := by
        rw [integral_const, smul_eq_mul]; ring

/-! ### Integration by parts -/

lemma ex_neg_int_mul (k : ℤ) (t : ℝ) :
    ex (-(k * t)) = Complex.exp ((-(2 * π * I * k)) * t) := by
  unfold ex; congr 1; push_cast; ring

/-- Fourier coefficients of `C¹` periodic functions decay like `‖G'‖_∞ / (2π|k|)`. -/
theorem norm_circleCoeff_le_of_deriv {G G' : ℝ → ℝ} (hG : ∀ t, HasDerivAt G (G' t) t)
    (hG'c : Continuous G') (hper : G 0 = G 1) {B : ℝ} (hB : ∀ t, |G' t| ≤ B) {k : ℤ}
    (hk : k ≠ 0) :
    ‖∫ t in (0 : ℝ)..1, ex (-(k * t)) * (G t : ℂ)‖ ≤ B / (2 * π * |(k : ℝ)|) := by
  set c : ℂ := -(2 * π * I * k) with hc
  have hc0 : c ≠ 0 := by
    rw [hc, neg_ne_zero]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (ofReal_ne_zero.2 pi_ne_zero)) I_ne_zero)
      (Int.cast_ne_zero.2 hk)
  have hcn : ‖c‖ = 2 * π * |(k : ℝ)| := by
    have : ‖c‖ = ‖(2 : ℂ)‖ * ‖(π : ℂ)‖ * ‖I‖ * ‖(k : ℂ)‖ := by
      rw [hc, norm_neg, norm_mul, norm_mul, norm_mul]
    rw [this, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I, Complex.norm_intCast,
      Real.norm_eq_abs, abs_of_pos pi_pos]
    ring
  set E : ℝ → ℂ := fun t => Complex.exp (c * t) / c with hE
  have hE' : ∀ t : ℝ, HasDerivAt E (Complex.exp (c * t)) t := by
    intro t
    have h1 : HasDerivAt (fun z : ℂ => Complex.exp (c * z)) (Complex.exp (c * t) * c) (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).const_mul c).cexp
    have h2 := (h1.comp_ofReal).div_const c
    rw [mul_div_cancel_right₀ _ hc0] at h2
    exact h2
  have hGc : ∀ t : ℝ, HasDerivAt (fun t => (G t : ℂ)) (G' t : ℂ) t := fun t => (hG t).ofReal_comp
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub (a := 0) (b := 1)
    (fun t _ => hE' t) (fun t _ => hGc t)
    ((Complex.continuous_exp.comp (continuous_const.mul continuous_ofReal)).intervalIntegrable _ _)
    ((continuous_ofReal.comp hG'c).intervalIntegrable _ _)
  have hE01 : E 1 * (G 1 : ℂ) - E 0 * (G 0 : ℂ) = 0 := by
    have h1 : Complex.exp (c * (1 : ℝ)) = 1 := by
      rw [hc, ofReal_one, mul_one, show -(2 * π * I * (k : ℂ)) = ((-k : ℤ) : ℂ) * (2 * π * I) by
        push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I _
    simp only [hE, h1, ofReal_zero, mul_zero, Complex.exp_zero, hper]
    ring
  rw [hE01] at hparts
  have hsplit : ∫ t in (0 : ℝ)..1, ex (-(k * t)) * (G t : ℂ) =
      -∫ t in (0 : ℝ)..1, E t * (G' t : ℂ) := by
    have hi1 : IntervalIntegrable (fun t => Complex.exp (c * t) * (G t : ℂ)) volume 0 1 :=
      ((Complex.continuous_exp.comp (continuous_const.mul continuous_ofReal)).mul
        (continuous_ofReal.comp (continuous_iff_continuousAt.2 fun t =>
          (hG t).continuousAt))).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun t => E t * (G' t : ℂ)) volume 0 1 :=
      (((Complex.continuous_exp.comp (continuous_const.mul continuous_ofReal)).div_const c).mul
        (continuous_ofReal.comp hG'c)).intervalIntegrable _ _
    rw [intervalIntegral.integral_add hi1 hi2] at hparts
    simp_rw [ex_neg_int_mul]
    rw [← hc]
    linear_combination hparts
  rw [hsplit, norm_neg]
  calc ‖∫ t in (0 : ℝ)..1, E t * (G' t : ℂ)‖ ≤ B / ‖c‖ * |1 - 0| := by
        refine intervalIntegral.norm_integral_le_of_norm_le_const fun t _ => ?_
        rw [hE, norm_mul, norm_div, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
        have hre : (c * t).re = 0 := by
          simp [hc, Complex.mul_re]
        rw [hre, Real.exp_zero, div_mul_eq_mul_div, one_mul, div_le_div_iff_of_pos_right
          (norm_pos_iff.2 hc0)]
        exact hB t
    _ = B / (2 * π * |(k : ℝ)|) := by rw [hcn]; simp

/-! ### Gradient estimates for harmonic functions -/

/-- A Cauchy estimate: `|∂_v h(z₀)| ≤ B ∫ |∂_v moll_r|` if `|h| ≤ B` on `closedBall z₀ (2r)`. -/
theorem abs_Dv_harmonic_le {h : ℂ → ℝ} {V : Set ℂ} (hh : HarmonicOnNhd h V) {z₀ : ℂ} {r B : ℝ}
    (hr : 0 < r) (hV : closedBall z₀ (2 * r) ⊆ V) (hB : ∀ z ∈ closedBall z₀ (2 * r), |h z| ≤ B)
    (v : ℂ) : |Dv h v z₀| ≤ B * ∫ x, |Dv (moll r) v x| := by
  set K := closedBall z₀ (2 * r) with hK
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB z₀ (mem_closedBall_self (by positivity)))
  have hhc : ContinuousOn h K := fun z hz => (hh z (hV hz)).1.continuousAt.continuousWithinAt
  set F := K.indicator h with hF
  have hFint : Integrable F :=
    (hhc.integrableOn_compact (isCompact_closedBall _ _)).integrable_indicator
      isClosed_closedBall.measurableSet
  have hFb : ∀ x, |F x| ≤ B := fun x => by
    by_cases hx : x ∈ K
    · rw [hF, indicator_of_mem hx]; exact hB x hx
    · rw [hF, indicator_of_notMem hx, abs_zero]; exact hB0
  -- `h = F ⋆ moll_r` near `z₀`
  have hev : h =ᶠ[𝓝 z₀] mollify F r := by
    filter_upwards [ball_mem_nhds z₀ hr] with z hz
    rw [mem_ball] at hz
    have hzK : closedBall z r ⊆ K := fun w hw => by
      rw [mem_closedBall] at hw ⊢
      linarith [dist_triangle w z z₀]
    have hmean := integral_harmonic_mul_radial hr.le (hh.mono (hzK.trans hV)) (continuous_moll r)
      (moll_eq_mollRad hr) (fun y hy => moll_eq_zero hr hy.le)
    rw [integral_moll hr, mul_one] at hmean
    rw [← hmean, mollify_apply, ← integral_add_left_eq_self (μ := volume)
      (fun t => F t * moll r (z - t)) z]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [sub_add_cancel_left, moll_neg hr]
    by_cases hy : ‖y‖ ≤ r
    · rw [hF, indicator_of_mem (hzK (add_mem_closedBall_of_norm_le hy))]
    · simp [moll_eq_zero hr (not_le.1 hy).le]
  have hD : Dv h v z₀ = (F ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Dv (moll r) v) z₀ := by
    have h1 : Dv h v z₀ = Dv (mollify F r) v z₀ := by
      show fderiv ℝ h z₀ v = fderiv ℝ (mollify F r) z₀ v
      rw [hev.fderiv_eq]
    rw [h1, mollify, Dv_conv hFint.locallyIntegrable ((contDiff_moll r).of_le (by norm_num))
      (hasCompactSupport_moll hr)]
  have hDc : Continuous (Dv (moll r) v) := continuous_Dv ((contDiff_moll r).of_le (by norm_num)) v
  have hDs : HasCompactSupport (Dv (moll r) v) := hasCompactSupport_Dv (hasCompactSupport_moll hr) v
  have hDi : Integrable (fun x => |Dv (moll r) v x|) :=
    hDc.abs.integrable_of_hasCompactSupport (hDs.comp_left (g := fun x : ℝ => |x|) abs_zero)
  rw [hD, convolution_lsmul, ← Real.norm_eq_abs]
  calc ‖∫ t, F t • Dv (moll r) v (z₀ - t)‖ ≤ ∫ t, B * |Dv (moll r) v (z₀ - t)| := by
        refine norm_integral_le_of_norm_le
          ((hDi.comp_sub_left z₀).const_mul B) (Eventually.of_forall fun t => ?_)
        rw [smul_eq_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hFb t) (abs_nonneg _)
    _ = B * ∫ x, |Dv (moll r) v x| := by
        rw [integral_const_mul, integral_sub_left_eq_self (fun x => |Dv (moll r) v x|)
          (volume : Measure ℂ) z₀]

end Distr

/-! ### Theorem A.3.1 -/

open Distr in
/-- **Theorem A.3.1.** -/
theorem subharmonicFourierDecayStatement_holds : SubharmonicFourierDecayStatement := by
  intro ρ hρ hρ1
  obtain ⟨C', hC'⟩ := rieszMeasureBoundStatement_holds ρ hρ hρ1
  set r : ℝ := ρ / 12 with hr_def
  have hr : 0 < r := by positivity
  set K : ℝ := (∫ x, |Dv (moll r) 1 x|) + ∫ x, |Dv (moll r) I x| with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact add_nonneg (integral_nonneg fun _ => abs_nonneg _)
    (integral_nonneg fun _ => abs_nonneg _)
  refine ⟨|C'| * K + |C'| / 2, fun u M hu hM k hk => ?_⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 1 (by
    show 1 - ρ < ‖(1 : ℂ)‖ ∧ ‖(1 : ℂ)‖ < 1 + ρ
    rw [norm_one]; constructor <;> linarith))
  -- the Riesz decomposition on `A_{ρ/2}`
  have hcl : closure (annulus (ρ / 2)) ⊆ (fun z : ℂ => ‖z‖) ⁻¹' Icc (1 - ρ / 2) (1 + ρ / 2) :=
    closure_minimal (fun z hz => ⟨hz.1.le, hz.2.le⟩) (isClosed_Icc.preimage continuous_norm)
  have hclc : IsCompact (closure (annulus (ρ / 2))) := by
    refine Metric.isCompact_of_isClosed_isBounded isClosed_closure
      (isBounded_closedBall (x := (0 : ℂ)) (r := 2) |>.subset fun z hz => ?_)
    have := (hcl hz).2
    rw [mem_closedBall, dist_zero_right]
    linarith
  have hclA : closure (annulus (ρ / 2)) ⊆ annulus ρ := fun z hz =>
    ⟨by have := (hcl hz).1; linarith, by have := (hcl hz).2; linarith⟩
  obtain ⟨μ, ⟨hμfin, hμA2, h, hh, hrep⟩, -⟩ := rieszRepresentationStatement_holds (annulus ρ) u
    (isOpen_annulus ρ) hu (annulus (ρ / 2)) (isOpen_annulus _) hclc hclA
  obtain ⟨hmass, hhb⟩ := hC' u M hu hM μ h hμfin hμA2 hh hrep
  have hA2B : annulus (ρ / 2) ⊆ closedBall 0 2 := fun z hz => by
    rw [mem_closedBall, dist_zero_right]; have := hz.2; linarith
  have hμS : μ (closedBall 0 2)ᶜ = 0 := measure_mono_null (compl_subset_compl.2 hA2B) hμA2
  -- on the unit circle `u = h - Φ`
  have hcirc : ∀ t : ℝ, ex t ∈ annulus (ρ / 2) := fun t => by
    show 1 - ρ / 2 < ‖ex t‖ ∧ ‖ex t‖ < 1 + ρ / 2
    rw [norm_ex]; constructor <;> linarith
  have hu_eq : ∀ t : ℝ, u (ex t) = h (ex t) - (logPotential μ (ex t)).toReal := fun t => by
    have := add_toReal_logPotential_of_rep (hrep _ (hcirc t)); linarith
  obtain ⟨hΦi, hΦb⟩ := norm_circleCoeff_logPotential_le hμS hk
  -- the harmonic part
  set G : ℝ → ℝ := fun t => h (ex t) with hG
  have hex' : ∀ t : ℝ, HasDerivAt ex (2 * π * I * ex t) t := by
    intro t
    have h1 : HasDerivAt (fun z : ℂ => Complex.exp (2 * π * I * z))
        (Complex.exp (2 * π * I * t) * (2 * π * I)) (t : ℂ) := by
      simpa using ((hasDerivAt_id (t : ℂ)).const_mul (2 * π * I)).cexp
    have h2 := h1.comp_ofReal
    unfold ex
    convert h2 using 1
    ring
  have hhd : ∀ t, DifferentiableAt ℝ h (ex t) := fun t =>
    ((hh _ (hcirc t)).1.differentiableAt (by norm_num))
  set G' : ℝ → ℝ := fun t => fderiv ℝ h (ex t) (2 * π * I * ex t) with hG'
  have hGd : ∀ t, HasDerivAt G (G' t) t := fun t => by
    have := (hhd t).hasFDerivAt.comp_hasDerivAt t (hex' t)
    exact this
  have hG'c : Continuous G' := by
    have hfc : ContinuousOn (fderiv ℝ h) (annulus (ρ / 2)) := fun z hz =>
      ((hh z hz).1.fderiv_right (m := 1) (by norm_num)).continuousAt.continuousWithinAt
    have h1 : Continuous (fun t => fderiv ℝ h (ex t)) :=
      hfc.comp_continuous continuous_ex hcirc
    exact h1.clm_apply (continuous_const.mul continuous_ex)
  have hGc : Continuous G := continuous_iff_continuousAt.2 fun t => (hGd t).continuousAt
  have hper : G 0 = G 1 := by
    have : ex 1 = ex 0 := by
      unfold ex
      rw [ofReal_one, ofReal_zero, mul_one, mul_zero, Complex.exp_zero, Complex.exp_two_pi_mul_I]
    simp only [hG, this]
  -- the gradient bound on the unit circle
  have hball : ∀ t : ℝ, closedBall (ex t) (2 * r) ⊆ annulus (ρ / 3) := fun t w hw => by
    rw [mem_closedBall, dist_eq_norm] at hw
    have h1 := norm_sub_norm_le w (ex t)
    have h2 := norm_sub_norm_le (ex t) w
    rw [norm_sub_rev] at h2
    rw [norm_ex] at h1 h2
    exact ⟨by linarith, by linarith⟩
  have hA3A2 : annulus (ρ / 3) ⊆ annulus (ρ / 2) := fun z hz =>
    ⟨by have := hz.1; linarith, by have := hz.2; linarith⟩
  have hDb : ∀ t : ℝ, ∀ v : ℂ, |Dv h v (ex t)| ≤ C' * M * ∫ x, |Dv (moll r) v x| :=
    fun t v => abs_Dv_harmonic_le hh hr ((hball t).trans hA3A2)
      (fun z hz => hhb z (hball t hz)) v
  have hCM : 0 ≤ C' * M := (abs_nonneg _).trans (hhb _ (hball 0 (mem_closedBall_self
    (by positivity))))
  have hG'b : ∀ t, |G' t| ≤ 2 * π * (C' * M * K) := by
    intro t
    set w : ℂ := 2 * π * I * ex t with hw
    have hwn : ‖w‖ = 2 * π := by
      rw [hw, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Complex.norm_I, norm_ex, Real.norm_eq_abs, abs_of_pos pi_pos]
      ring
    show |fderiv ℝ h (ex t) w| ≤ _
    rw [clm_apply_eq (fderiv ℝ h (ex t)) w]
    have hre : |w.re| ≤ 2 * π := hwn ▸ Complex.abs_re_le_norm w
    have him : |w.im| ≤ 2 * π := hwn ▸ Complex.abs_im_le_norm w
    have h1 := hDb t 1
    have h2 := hDb t I
    calc |w.re * fderiv ℝ h (ex t) 1 + w.im * fderiv ℝ h (ex t) I|
        ≤ |w.re| * |Dv h 1 (ex t)| + |w.im| * |Dv h I (ex t)| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul]
          rfl
      _ ≤ 2 * π * (C' * M * ∫ x, |Dv (moll r) 1 x|) + 2 * π * (C' * M * ∫ x, |Dv (moll r) I x|) :=
          add_le_add (mul_le_mul hre h1 (abs_nonneg _) (by positivity))
            (mul_le_mul him h2 (abs_nonneg _) (by positivity))
      _ = 2 * π * (C' * M * K) := by rw [hK]; ring
  have hhat := norm_circleCoeff_le_of_deriv hGd hG'c hper hG'b hk
  -- assemble
  have hGi : IntervalIntegrable (fun t => ex (-(k * t)) * (G t : ℂ)) volume 0 1 :=
    ((continuous_ex.comp (continuous_const.mul continuous_id).neg).mul
      (continuous_ofReal.comp hGc)).intervalIntegrable _ _
  have hsplit : circleCoeff u k = (∫ t in (0 : ℝ)..1, ex (-(k * t)) * (G t : ℂ)) -
      ∫ t in (0 : ℝ)..1, ex (-(k * t)) * ((logPotential μ (ex t)).toReal : ℂ) := by
    unfold circleCoeff
    rw [← intervalIntegral.integral_sub hGi hΦi]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hG, hu_eq t]
    push_cast
    ring
  have hk0 : 0 < |(k : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hk)
  rw [hsplit]
  calc ‖(∫ t in (0 : ℝ)..1, ex (-(k * t)) * (G t : ℂ)) -
        ∫ t in (0 : ℝ)..1, ex (-(k * t)) * ((logPotential μ (ex t)).toReal : ℂ)‖
      ≤ 2 * π * (C' * M * K) / (2 * π * |(k : ℝ)|) + μ.real univ / (2 * |(k : ℝ)|) :=
        (norm_sub_le _ _).trans (add_le_add hhat hΦb)
    _ ≤ (|C'| * K + |C'| / 2) * M / |(k : ℝ)| := by
        have hpi := pi_pos
        have e1 : 2 * π * (C' * M * K) / (2 * π * |(k : ℝ)|) = C' * M * K / |(k : ℝ)| := by
          field_simp
        rw [e1]
        have hC'M : C' * M * K ≤ |C'| * M * K :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hM0) hK0
        have hm : μ.real univ ≤ |C'| * M :=
          hmass.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hM0)
        calc C' * M * K / |(k : ℝ)| + μ.real univ / (2 * |(k : ℝ)|)
            ≤ |C'| * M * K / |(k : ℝ)| + |C'| * M / (2 * |(k : ℝ)|) :=
              add_le_add (div_le_div_of_nonneg_right hC'M hk0.le)
                (div_le_div_of_nonneg_right hm (by positivity))
          _ = (|C'| * K + |C'| / 2) * M / |(k : ℝ)| := by
              field_simp
              ring

end DF
