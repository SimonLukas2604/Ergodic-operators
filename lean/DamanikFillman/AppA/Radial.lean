/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Appendix A.3, preliminaries: integration in polar coordinates and radial kernels

* `DF.Distr.integral_eq_polar` — `∫ f = ∫_{ρ > 0} ∫_{-π}^{π} ρ f(ρ e^{iθ}) dθ dρ` for continuous `f`
  with bounded support;
* `DF.Distr.integral_Ioo_circleMap` — integrals over `(-π, π)` along circles are `2π` times the
  circle average;
* `DF.Distr.integral_harmonic_mul_radial` — **the mean value property for radial kernels**: if
  `H` is harmonic near `closedBall x r` and `K` is a continuous radial kernel supported in
  `closedBall 0 r`, then `∫ H(x + y) K(y) dy = H(x) ∫ K`.
-/
import DamanikFillman.AppA.Distributional
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

noncomputable section

open Real Complex Metric Set Filter Topology MeasureTheory InnerProductSpace

namespace DF

namespace Distr

/-- The unit vector `e^{iθ}` written as in `Complex.polarCoord_symm_apply`. -/
lemma ofReal_mul_e_eq_circleMap (ρ θ : ℝ) :
    (ρ : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I) = circleMap 0 ρ θ := by
  rw [circleMap_zero, Complex.exp_mul_I, ← ofReal_cos, ← ofReal_sin]

lemma norm_ofReal_mul_e (ρ θ : ℝ) :
    ‖(ρ : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I)‖ = |ρ| := by
  rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- **Integration in polar coordinates** for continuous functions with bounded support. -/
theorem integral_eq_polar {f : ℂ → ℝ} (hf : Continuous f) {R : ℝ}
    (hfs : ∀ z, R < ‖z‖ → f z = 0) :
    ∫ z, f z = ∫ ρ in Ioi (0 : ℝ), ∫ θ in Ioo (-π) π,
      ρ * f (ρ * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I)) := by
  set R' := max R 0 with hR'
  have hR0 : 0 ≤ R' := le_max_right _ _
  have hfs' : ∀ z, R' < ‖z‖ → f z = 0 := fun z hz => hfs z (lt_of_le_of_lt (le_max_left _ _) hz)
  have hfc : HasCompactSupport f :=
    HasCompactSupport.intro (isCompact_closedBall 0 R') fun z hz => hfs' z (by
      rw [mem_closedBall, dist_zero_right, not_le] at hz
      exact hz)
  obtain ⟨C, hC⟩ := hfc.exists_bound_of_continuous hf
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  set G : ℝ × ℝ → ℝ := fun p => p.1 * f (p.1 * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * I))
    with hG
  have hGc : Continuous G := by
    rw [hG]
    refine continuous_fst.mul (hf.comp ?_)
    fun_prop
  have hGb : ∀ p, ‖G p‖ ≤ R' * C := by
    intro p
    simp only [hG, norm_mul]
    by_cases hp : ‖p.1‖ ≤ R'
    · exact mul_le_mul hp (hC _) (norm_nonneg _) hR0
    · rw [hfs' _ (by rw [norm_ofReal_mul_e, ← Real.norm_eq_abs]; exact lt_of_not_ge hp),
        norm_zero, mul_zero]
      exact mul_nonneg hR0 hC0
  have hG0 : ∀ p : ℝ × ℝ, R' < p.1 → G p = 0 := by
    intro p hp
    simp only [hG]
    rw [hfs' _ (by rw [norm_ofReal_mul_e, abs_of_pos (hR0.trans_lt hp)]; exact hp), mul_zero]
  have hGint : IntegrableOn G (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) := by
    have h1 : IntegrableOn G (Ioc (0 : ℝ) R' ×ˢ Ioo (-π) π) := by
      refine IntegrableOn.of_bound ?_ hGc.aestronglyMeasurable (R' * C)
        (Eventually.of_forall hGb)
      rw [Measure.volume_eq_prod, Measure.prod_prod]
      simp [ENNReal.mul_lt_top]
    refine h1.of_forall_sdiff_eq_zero (measurableSet_Ioi.prod measurableSet_Ioo) ?_
    rintro ⟨r, θ⟩ ⟨⟨hr, hθ⟩, hn⟩
    apply hG0
    have hr' : (0 : ℝ) < r := hr
    by_contra hle
    push Not at hle
    exact hn ⟨⟨hr', hle⟩, hθ⟩
  have hpol : ∫ z, f z = ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, G p := by
    rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
    refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p _ => ?_
    simp only [Complex.polarCoord_symm_apply, smul_eq_mul, hG]
  rw [hpol]
  exact setIntegral_prod (μ := volume) (ν := volume) G hGint

/-- Integrals over `(-π, π)` along circles are `2π` times the circle average. -/
theorem integral_Ioo_circleMap (g : ℂ → ℝ) (c : ℂ) (R : ℝ) :
    ∫ θ in Ioo (-π) π, g (circleMap c R θ) = 2 * π * circleAverage g c R := by
  have hper : Function.Periodic (fun θ => g (circleMap c R θ)) (2 * π) :=
    fun θ => by simp only [periodic_circleMap c R θ]
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (show -π ≤ π by linarith [pi_pos]), circleAverage_def]
  have h := hper.intervalIntegral_add_eq (-π) 0
  rw [show -π + 2 * π = π by ring, zero_add] at h
  rw [h, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (show (2 * π) ≠ 0 by positivity), one_mul]

/-- Continuity of `y ↦ H(x + y) K(y)` when `H` is continuous near the support of `K`. -/
lemma continuous_mul_kernel {H K : ℂ → ℝ} {x : ℂ} {r r' : ℝ} (hK : Continuous K)
    (hKs : ∀ y, r < ‖y‖ → K y = 0) (hrr : r < r') (hH : ContinuousOn H (ball x r')) :
    Continuous (fun y => H (x + y) * K y) := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  by_cases hy : ‖y‖ < r'
  · have hxy : x + y ∈ ball x r' := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left]; exact hy
    have h1 : ContinuousAt (fun y => H (x + y)) y :=
      (hH.continuousAt (isOpen_ball.mem_nhds hxy)).comp (continuous_const.add continuous_id).continuousAt
    exact h1.mul hK.continuousAt
  · have hev : ∀ᶠ z in 𝓝 y, r < ‖z‖ :=
      (continuous_norm.isOpen_preimage _ isOpen_Ioi).mem_nhds
        (show y ∈ (fun z : ℂ => ‖z‖) ⁻¹' Ioi r from lt_of_lt_of_le hrr (not_lt.1 hy))
    refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [hev] with z hz
    rw [hKs z hz, mul_zero]

/-- **Mean value property for radial kernels.** -/
theorem integral_harmonic_mul_radial {H : ℂ → ℝ} {x : ℂ} {r : ℝ} (hr : 0 ≤ r)
    (hH : HarmonicOnNhd H (closedBall x r)) {K : ℂ → ℝ} (hK : Continuous K) {k : ℝ → ℝ}
    (hrad : ∀ y, K y = k ‖y‖) (hKs : ∀ y, r < ‖y‖ → K y = 0) :
    ∫ y, H (x + y) * K y = H x * ∫ y, K y := by
  -- `H` is continuous on a slightly larger ball
  obtain ⟨δ, hδ, hδs⟩ := (isCompact_closedBall x r).exists_thickening_subset_open
    (isOpen_setOfPred_harmonicAt H) hH
  have hball : ball x (r + δ) ⊆ {z | HarmonicAt H z} := by
    intro z hz
    apply hδs
    rw [thickening_closedBall hδ hr, mem_ball]
    rw [mem_ball] at hz
    linarith
  have hHc : ContinuousOn H (ball x (r + δ)) := fun z hz =>
    (hball hz).1.continuousAt.continuousWithinAt
  have hcont := continuous_mul_kernel hK hKs (by linarith) hHc
  have hks : ∀ ρ, r < ρ → k ρ = 0 := fun ρ hρ => by
    have := hKs (ρ : ℂ) (by rw [Complex.norm_real, Real.norm_eq_abs]; exact lt_of_lt_of_le hρ (le_abs_self ρ))
    rwa [hrad, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lt_of_le_of_lt hr hρ)] at this
  rw [integral_eq_polar hcont (fun y hy => by
      show H (x + y) * K y = 0
      rw [hKs y hy, mul_zero]),
    integral_eq_polar hK hKs, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun ρ hρ => ?_
  have hρ0 : (0 : ℝ) < ρ := hρ
  have hkρ : ∀ θ : ℝ, K (ρ * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I)) = k ρ := fun θ => by
    rw [hrad, norm_ofReal_mul_e, abs_of_pos hρ0]
  simp only [hkρ]
  simp only [ofReal_mul_e_eq_circleMap]
  by_cases hρr : ρ ≤ r
  · have hmean : ∫ θ in Ioo (-π) π, H (circleMap x ρ θ) = 2 * π * H x := by
      rw [integral_Ioo_circleMap,
        (hH.mono (closedBall_subset_closedBall (by rw [abs_of_pos hρ0]; exact hρr))).circleAverage_eq]
    have e1 : (fun θ => ρ * (H (x + circleMap 0 ρ θ) * k ρ)) =
        fun θ => (ρ * k ρ) * H (circleMap x ρ θ) := by
      funext θ
      simp only [circleMap, zero_add]
      ring
    rw [e1, integral_const_mul, hmean, setIntegral_const,
      Real.volume_real_Ioo_of_le (show -π ≤ π by linarith [pi_pos]), smul_eq_mul]
    ring
  · rw [hks ρ (lt_of_not_ge hρr)]
    simp
