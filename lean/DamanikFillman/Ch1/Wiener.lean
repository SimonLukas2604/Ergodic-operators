/-
Formalization of Damanik–Fillman, *One-Dimensional Ergodic Schrödinger Operators I*, Chapter 1.

# Wiener's theorem  (book §1.6.2, Theorem 1.6.8, p. 51)

For a finite Borel measure `μ` on `ℝ` with Fourier transform `μ̂(t) = ∫ e^{-ixt} dμ(x)`
(1.6.21) we prove
`(1/2T) ∫_{-T}^{T} |μ̂(t)|² dt → ∑_λ μ({λ})²` as `T → ∞` (1.6.22),
and the consequence that `μ` has no atoms iff these averages tend to `0` (1.6.23).

The limit is first identified with `(μ ⊗ μ)(diagonal)` (`DF.wiener_diagonal`), which is then
shown to be `∑' λ, μ({λ})²` (`DF.prod_diagonal_eq_tsum`).

No `Statement` props are introduced in this file.
-/
import Mathlib

noncomputable section

open scoped ENNReal NNReal Topology
open MeasureTheory Set Filter Complex

namespace DF

/-- Fourier transform of a finite measure on `ℝ`, `μ̂(t) = ∫ e^{-ixt} dμ(x)` (1.6.21). -/
def measFourier (μ : Measure ℝ) (t : ℝ) : ℂ := ∫ x, exp (-((x * t : ℝ) : ℂ) * I) ∂μ

/-- The time average `(1/2T) ∫_{-T}^{T} f(t) dt`. -/
def timeAvg (f : ℝ → ℝ) (T : ℝ) : ℝ := (1 / (2 * T)) * ∫ t in -T..T, f t

/-- The averaged kernel `(1/2T) ∫_{-T}^T e^{-ist} dt`. -/
def avgKernel (T s : ℝ) : ℂ := (1 / (2 * T) : ℂ) * ∫ t in -T..T, exp (-((s * t : ℝ) : ℂ) * I)

lemma norm_exp_neg_mul_I (r : ℝ) : ‖exp (-((r : ℝ) : ℂ) * I)‖ = 1 := by
  rw [show -((r : ℝ) : ℂ) * I = ((-r : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

lemma norm_avgKernel_le {T : ℝ} (hT : 0 < T) (s : ℝ) : ‖avgKernel T s‖ ≤ 1 := by
  unfold avgKernel
  rw [norm_mul]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := -T) (b := T) (C := 1)
    (f := fun t => exp (-((s * t : ℝ) : ℂ) * I)) (fun t _ => (norm_exp_neg_mul_I _).le)
  rw [show |T - -T| = 2 * T by rw [sub_neg_eq_add, ← two_mul, abs_of_pos (by positivity)]] at h
  have h2 : ‖(1 / (2 * T) : ℂ)‖ = 1 / (2 * T) := by
    rw [norm_div, norm_one, show (2 * T : ℂ) = ((2 * T : ℝ) : ℂ) by push_cast; ring,
      norm_real, Real.norm_of_nonneg (by positivity)]
  rw [h2]
  calc 1 / (2 * T) * ‖∫ t in -T..T, exp (-((s * t : ℝ) : ℂ) * I)‖ ≤ 1 / (2 * T) * (1 * (2 * T)) :=
        by gcongr
    _ = 1 := by field_simp

lemma avgKernel_zero {T : ℝ} (hT : 0 < T) : avgKernel T 0 = 1 := by
  unfold avgKernel
  simp only [zero_mul, ofReal_zero, neg_zero, exp_zero, intervalIntegral.integral_const,
    sub_neg_eq_add]
  rw [real_smul, mul_one]
  have : (T : ℂ) ≠ 0 := by exact_mod_cast hT.ne'
  push_cast
  field_simp
  ring

lemma tendsto_avgKernel {s : ℝ} (hs : s ≠ 0) : Tendsto (fun T => avgKernel T s) atTop (𝓝 0) := by
  have hc : (-(s : ℂ) * I) ≠ 0 := by simp [hs, I_ne_zero]
  have hint : ∀ T, ∫ t in -T..T, exp (-((s * t : ℝ) : ℂ) * I) =
      (exp (-(s : ℂ) * I * T) - exp (-(s : ℂ) * I * (-T : ℝ))) / (-(s : ℂ) * I) := by
    intro T
    rw [← integral_exp_mul_complex hc]
    congr 1; funext t; congr 1; push_cast; ring
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero' (g := fun T => 1 / |s| * T⁻¹)
    (Eventually.of_forall fun T => norm_nonneg _) ?_
    (by simpa using (tendsto_inv_atTop_zero.const_mul (1 / |s|)))
  · filter_upwards [eventually_gt_atTop 0] with T hT
    unfold avgKernel
    have h1 : ‖exp (-(s : ℂ) * I * T) - exp (-(s : ℂ) * I * (-T : ℝ))‖ ≤ 2 := by
      refine (norm_sub_le _ _).trans ?_
      rw [show -(s : ℂ) * I * T = -((s * T : ℝ) : ℂ) * I by push_cast; ring,
        show -(s : ℂ) * I * (-T : ℝ) = -((s * -T : ℝ) : ℂ) * I by push_cast; ring,
        norm_exp_neg_mul_I, norm_exp_neg_mul_I]
      norm_num
    have h2 : ‖-(s : ℂ) * I‖ = |s| := by simp
    have h3 : ‖(1 / (2 * T) : ℂ)‖ = 1 / (2 * T) := by
      rw [norm_div, norm_one, show (2 * T : ℂ) = ((2 * T : ℝ) : ℂ) by push_cast; ring,
        norm_real, Real.norm_of_nonneg (by positivity)]
    rw [hint, norm_mul, h3, norm_div, h2]
    have hs' : 0 < |s| := abs_pos.2 hs
    calc 1 / (2 * T) * (‖exp (-(s : ℂ) * I * T) - exp (-(s : ℂ) * I * (-T : ℝ))‖ / |s|)
        ≤ 1 / (2 * T) * (2 / |s|) := by gcongr
      _ = 1 / |s| * T⁻¹ := by field_simp

variable (μ : Measure ℝ) [IsFiniteMeasure μ]

lemma continuous_expKernel : Continuous fun q : ℝ × (ℝ × ℝ) =>
    exp (-(((q.2.1 - q.2.2) * q.1 : ℝ) : ℂ) * I) := by fun_prop

/-- `|μ̂(t)|² = ∫∫ e^{-i(x-y)t} dμ(x) dμ(y)`. -/
lemma normSq_measFourier (t : ℝ) :
    ((‖measFourier μ t‖ ^ 2 : ℝ) : ℂ) =
      ∫ p, exp (-(((p.1 - p.2) * t : ℝ) : ℂ) * I) ∂(μ.prod μ) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj', measFourier, ← integral_conj, ← integral_prod_mul]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only
  rw [← exp_conj, ← exp_add]
  congr 1
  simp only [map_mul, map_neg, conj_ofReal, conj_I]
  push_cast; ring

/-- Wiener's theorem, first form: the time averages of `|μ̂|²` converge to `(μ⊗μ)(Δ)`. -/
theorem wiener_diagonal :
    Tendsto (fun T => timeAvg (fun t => ‖measFourier μ t‖ ^ 2) T) atTop
      (𝓝 ((μ.prod μ).real (diagonal ℝ))) := by
  -- rewrite the average as an integral of the averaged kernel
  have key : ∀ T, 0 < T → ((timeAvg (fun t => ‖measFourier μ t‖ ^ 2) T : ℝ) : ℂ) =
      ∫ p, avgKernel T (p.1 - p.2) ∂(μ.prod μ) := by
    intro T hT
    unfold timeAvg avgKernel
    push_cast
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [normSq_measFourier]
    rw [integral_const_mul]
    congr 1
    rw [intervalIntegral.integral_of_le (by linarith)]
    have hint : Integrable (Function.uncurry fun (t : ℝ) (p : ℝ × ℝ) =>
        exp (-(((p.1 - p.2) * t : ℝ) : ℂ) * I)) ((volume.restrict (Ioc (-T) T)).prod (μ.prod μ)) := by
      refine Integrable.of_bound (continuous_expKernel.aestronglyMeasurable) 1
        (Eventually.of_forall fun q => (norm_exp_neg_mul_I _).le)
    rw [integral_integral_swap hint]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only
    rw [intervalIntegral.integral_of_le (by linarith)]
    congr 1; funext t; congr 3; push_cast; ring
  have hlim : Tendsto (fun T => ∫ p, avgKernel T (p.1 - p.2) ∂(μ.prod μ)) atTop
      (𝓝 (∫ p, (diagonal ℝ).indicator (fun _ => (1 : ℂ)) p ∂(μ.prod μ))) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => 1) ?_ ?_
      (integrable_const _) ?_
    · filter_upwards with T
      unfold avgKernel
      refine (Continuous.aestronglyMeasurable ?_)
      refine continuous_const.mul ?_
      have : Continuous fun q : ℝ × ℝ => ∫ t in -T..T, exp (-((q.1 * t : ℝ) : ℂ) * I) :=
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
          (by fun_prop) _ _
      exact (this.comp (show Continuous fun p : ℝ × ℝ => (p.1 - p.2, (0 : ℝ)) by fun_prop))
    · filter_upwards [eventually_gt_atTop 0] with T hT
      exact Eventually.of_forall fun p => norm_avgKernel_le hT _
    · refine Eventually.of_forall fun p => ?_
      by_cases hp : p.1 = p.2
      · rw [indicator_of_mem (by exact hp), hp, sub_self]
        exact tendsto_const_nhds.congr' (by
          filter_upwards [eventually_gt_atTop 0] with T hT
          exact (avgKernel_zero hT).symm)
      · rw [indicator_of_notMem (by exact hp)]
        exact tendsto_avgKernel (sub_ne_zero.2 hp)
  rw [integral_indicator measurableSet_diagonal, setIntegral_const, real_smul, mul_one] at hlim
  have h2 := (Complex.continuous_re.tendsto _).comp hlim
  simp only [ofReal_re] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with T hT
  simp only [Function.comp_apply]
  rw [← key T hT, ofReal_re]

/-- `(μ ⊗ μ)(Δ) = ∫ μ({y}) dμ(y)`. -/
lemma prod_diagonal_eq_lintegral : (μ.prod μ) (diagonal ℝ) = ∫⁻ y, μ {y} ∂μ := by
  rw [Measure.prod_apply measurableSet_diagonal]
  congr 1; funext x
  congr 1; ext y; simp [eq_comm]

/-- `(μ ⊗ μ)(Δ) = ∑_λ μ({λ})²`. -/
theorem prod_diagonal_eq_tsum : (μ.prod μ) (diagonal ℝ) = ∑' x : ℝ, μ {x} ^ 2 := by
  set C : Set ℝ := {E | 0 < μ {E}}
  have hC : C.Countable := Measure.countable_meas_pos_of_disjoint_iUnion
    (As := fun E : ℝ => ({E} : Set ℝ)) (fun E => measurableSet_singleton E)
    (fun E F hEF => disjoint_singleton.2 hEF)
  rw [prod_diagonal_eq_lintegral]
  have h1 : ∫⁻ y, μ {y} ∂μ = ∫⁻ y in C, μ {y} ∂μ := by
    rw [← lintegral_indicator hC.measurableSet]
    congr 1; funext y
    by_cases hy : y ∈ C
    · rw [indicator_of_mem hy]
    · rw [indicator_of_notMem hy]; simpa [C] using hy
  rw [h1, lintegral_countable _ hC]
  rw [← tsum_subtype_eq_of_support_subset (s := C)]
  · simp [pow_two]
  · intro x hx
    simp only [Function.mem_support, ne_eq, pow_eq_zero_iff two_ne_zero] at hx
    exact pos_iff_ne_zero.2 hx

/-- **Wiener's theorem** (Theorem 1.6.8, (1.6.22)). -/
theorem wiener :
    Tendsto (fun T => timeAvg (fun t => ‖measFourier μ t‖ ^ 2) T) atTop
      (𝓝 (∑' x : ℝ, μ {x} ^ 2).toReal) := by
  have := wiener_diagonal μ
  rwa [measureReal_def, prod_diagonal_eq_tsum] at this

/-- (1.6.23): `μ` is continuous iff the time averages of `|μ̂|²` tend to zero. -/
theorem wiener_continuous_iff :
    (∀ x, μ {x} = 0) ↔ Tendsto (fun T => timeAvg (fun t => ‖measFourier μ t‖ ^ 2) T) atTop (𝓝 0) := by
  have hfin : (μ.prod μ) (diagonal ℝ) ≠ ⊤ := measure_ne_top _ _
  constructor
  · intro h
    have := wiener_diagonal μ
    rwa [measureReal_def, prod_diagonal_eq_tsum, show (fun x => μ {x} ^ 2) = fun _ => 0 by
      funext x; rw [h x]; simp, tsum_zero, ENNReal.toReal_zero] at this
  · intro h x
    have h1 := tendsto_nhds_unique (wiener_diagonal μ) h
    rw [measureReal_def, ENNReal.toReal_eq_zero_iff, prod_diagonal_eq_tsum] at h1
    rcases h1 with h1 | h1
    · have := ENNReal.le_tsum (f := fun x : ℝ => μ {x} ^ 2) x
      rw [h1, nonpos_iff_eq_zero, pow_eq_zero_iff two_ne_zero] at this
      exact this
    · rw [← prod_diagonal_eq_tsum] at h1; exact absurd h1 hfin

end DF
