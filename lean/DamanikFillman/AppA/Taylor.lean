/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Appendix A.3, preliminaries: second order Taylor expansion of mollifications

For a compactly supported `C²` function `φ` and the radial mollifier `moll r`,

  `∫ φ(z + y) moll_r(y) dy = φ(z) + (Q(r)/4) Δφ(z) + o(Q(r))`

uniformly in `z`, where `Q(r) = ∫ |y|² moll_r(y) dy > 0` (`DF.Distr.taylor_moll`).  This is the
key estimate showing that subharmonic functions have nonnegative distributional Laplacian.
-/
import DamanikFillman.AppA.SubharmonicLocal
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

open Real Complex Metric Set Filter Topology MeasureTheory Laplacian InnerProductSpace

namespace DF

namespace Distr

/-- The unit vector `e^{iθ}`. -/
def eθ (θ : ℝ) : ℂ := (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I

lemma eθ_re (θ : ℝ) : (eθ θ).re = Real.cos θ := by
  simp only [eθ, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

lemma eθ_im (θ : ℝ) : (eθ θ).im = Real.sin θ := by
  simp only [eθ, Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

lemma norm_eθ (θ : ℝ) : ‖eθ θ‖ = 1 := norm_e θ

lemma continuous_eθ : Continuous eθ := by unfold eθ; fun_prop

/-! ### Directional derivatives along lines -/

lemma hasDerivAt_comp_line {F : ℂ → ℝ} (hF : Differentiable ℝ F) (z e : ℂ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => F (z + t * e)) (Dv F e (z + t * e)) t := by
  have h1 : HasDerivAt (fun t : ℝ => z + (t : ℂ) * e) e t := by
    simpa using ((hasDerivAt_id t).ofReal_comp.mul_const e).const_add z
  have h2 := (hF (z + t * e)).hasFDerivAt.comp_hasDerivAt t h1
  exact h2

lemma Dv_Dv_eq {f : ℂ → ℝ} (hd : Differentiable ℝ (fderiv ℝ f)) (v w z : ℂ) :
    Dv (Dv f v) w z = fderiv ℝ (fderiv ℝ f) z w v := by
  show fderiv ℝ (fun y => fderiv ℝ f y v) z w = _
  rw [fderiv_clm_apply (hd z) (differentiableAt_const v)]
  simp

/-- A general form of `clm_apply_eq`. -/
lemma clm_apply_eq' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (ℓ : ℂ →L[ℝ] F)
    (z : ℂ) : ℓ z = z.re • ℓ 1 + z.im • ℓ I := by
  have hz : z = z.re • (1 : ℂ) + z.im • I := by
    apply Complex.ext <;> simp
  calc ℓ z = ℓ (z.re • (1 : ℂ) + z.im • I) := by rw [← hz]
    _ = z.re • ℓ 1 + z.im • ℓ I := by rw [map_add, map_smul, map_smul]

lemma bilin_eθ (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (θ : ℝ) :
    B (eθ θ) (eθ θ) = Real.cos θ ^ 2 * B 1 1 + Real.sin θ * Real.cos θ * (B 1 I + B I 1) +
      Real.sin θ ^ 2 * B I I := by
  rw [clm_apply_eq' B (eθ θ)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [clm_apply_eq (B 1) (eθ θ), clm_apply_eq (B I) (eθ θ), eθ_re, eθ_im]
  ring

/-! ### Taylor's theorem along lines, uniformly -/

/-- **Uniform second order Taylor expansion** along rays. -/
theorem taylor_line {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ ρ : ℝ, 0 ≤ ρ → ρ < δ → ∀ z : ℂ, ∀ θ : ℝ,
      |φ (z + ρ * eθ θ) - φ z - ρ * Dv φ (eθ θ) z - ρ ^ 2 / 2 * Dv (Dv φ (eθ θ)) (eθ θ) z|
        ≤ ε * ρ ^ 2 := by
  have hd : Differentiable ℝ (fderiv ℝ φ) := differentiable_fderiv_of_contDiff_two hφ
  have hD2c : Continuous (fderiv ℝ (fderiv ℝ φ)) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
  have hD2s : HasCompactSupport (fderiv ℝ (fderiv ℝ φ)) :=
    (hφc.fderiv (𝕜 := ℝ)).fderiv (𝕜 := ℝ)
  have hu : UniformContinuous (fderiv ℝ (fderiv ℝ φ)) :=
    hD2s.uniformContinuous_of_continuous hD2c
  obtain ⟨δ, hδ, hδu⟩ :=
    (Metric.uniformContinuous_iff (α := ℂ) (β := ℂ →L[ℝ] ℂ →L[ℝ] ℝ)).1 hu ε hε
  refine ⟨δ, hδ, fun ρ hρ0 hρδ z θ => ?_⟩
  set e := eθ θ with he
  have hne : ‖e‖ = 1 := norm_eθ θ
  set Q := Dv (Dv φ e) e z with hQ
  have hφd : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hDd : Differentiable ℝ (Dv φ e) := differentiable_Dv hφ e
  -- first derivative
  set k : ℝ → ℝ := fun t => Dv φ e (z + (t : ℂ) * e) - Dv φ e z - t * Q with hk
  have hk' : ∀ t : ℝ, HasDerivAt k (Dv (Dv φ e) e (z + (t : ℂ) * e) - Q) t := by
    intro t
    have h1 := hasDerivAt_comp_line hDd z e t
    have h2 : HasDerivAt (fun t : ℝ => t * Q) Q t := by
      simpa using (hasDerivAt_id t).mul_const Q
    exact (h1.sub_const _).sub h2
  have hkb : ∀ t ∈ Icc (0 : ℝ) ρ, ‖k t‖ ≤ ε * t := by
    have := norm_image_sub_le_of_norm_deriv_le_segment' (f := k) (C := ε)
      (f' := fun t : ℝ => Dv (Dv φ e) e (z + (t : ℂ) * e) - Q)
      (fun t _ => (hk' t).hasDerivWithinAt) (fun t ht => by
        rw [hQ, Dv_Dv_eq hd, Dv_Dv_eq hd, ← ContinuousLinearMap.sub_apply,
          ← ContinuousLinearMap.sub_apply]
        refine (ContinuousLinearMap.le_opNorm₂ _ _ _).trans ?_
        rw [hne, mul_one, mul_one]
        have hlt : dist (fderiv ℝ (fderiv ℝ φ) (z + (t : ℂ) * e)) (fderiv ℝ (fderiv ℝ φ) z) < ε := by
          refine hδu ?_
          rw [dist_eq_norm, add_sub_cancel_left, norm_mul, hne, mul_one, Complex.norm_real,
            Real.norm_eq_abs, abs_of_nonneg ht.1]
          exact lt_of_lt_of_le ht.2 hρδ.le
        rw [dist_eq_norm] at hlt
        exact hlt.le)
    intro t ht
    have h := this t ht
    have hk0 : k 0 = 0 := by simp [hk]
    rw [hk0, sub_zero, sub_zero] at h
    exact h
  -- the remainder
  set m : ℝ → ℝ := fun t => φ (z + (t : ℂ) * e) - φ z - t * Dv φ e z - t ^ 2 / 2 * Q with hm
  have hm' : ∀ t : ℝ, HasDerivAt m (k t) t := by
    intro t
    have h1 := hasDerivAt_comp_line hφd z e t
    have h2 : HasDerivAt (fun t : ℝ => t * Dv φ e z) (Dv φ e z) t := by
      simpa using (hasDerivAt_id t).mul_const (Dv φ e z)
    have h3 : HasDerivAt (fun t : ℝ => t ^ 2 / 2 * Q) (t * Q) t := by
      have := (((hasDerivAt_id t).mul (hasDerivAt_id t)).div_const 2).mul_const Q
      convert this using 1
      · funext x; (try simp only [id]); ring
      · (try simp only [id]); ring
    exact ((h1.sub_const _).sub h2).sub h3
  have hmb := norm_image_sub_le_of_norm_deriv_le_segment' (f := m) (C := ε * ρ)
    (fun t _ => (hm' t).hasDerivWithinAt) (fun t ht => (hkb t (Ico_subset_Icc_self ht)).trans
      (mul_le_mul_of_nonneg_left ht.2.le hε.le)) ρ ⟨hρ0, le_rfl⟩
  have hm0 : m 0 = 0 := by simp [hm]
  rw [hm0, sub_zero, sub_zero, Real.norm_eq_abs] at hmb
  calc _ = |m ρ| := rfl
    _ ≤ ε * ρ * ρ := hmb
    _ = ε * ρ ^ 2 := by ring

/-! ### Integrals over circles -/

lemma setIntegral_Ioo_pi (f : ℝ → ℝ) :
    ∫ θ in Ioo (-π) π, f θ = ∫ θ in (-π)..π, f θ := by
  rw [← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (show -π ≤ π by linarith [pi_pos])]

lemma integral_cos_mul_add_sin_mul (a b : ℝ) :
    ∫ θ in (-π)..π, (Real.cos θ * a + Real.sin θ * b) = 0 := by
  rw [intervalIntegral.integral_add, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_mul_const, integral_cos, integral_sin]
  · simp
  · exact (Real.continuous_cos.mul continuous_const).intervalIntegrable _ _
  · exact (Real.continuous_sin.mul continuous_const).intervalIntegrable _ _

lemma integral_quadratic (a b c : ℝ) :
    ∫ θ in (-π)..π, (Real.cos θ ^ 2 * a + Real.sin θ * Real.cos θ * b + Real.sin θ ^ 2 * c) =
      π * (a + c) := by
  have h1 : IntervalIntegrable (fun θ => Real.cos θ ^ 2 * a) volume (-π) π :=
    ((Real.continuous_cos.pow 2).mul continuous_const).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun θ => Real.sin θ * Real.cos θ * b) volume (-π) π :=
    ((Real.continuous_sin.mul Real.continuous_cos).mul continuous_const).intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun θ => Real.sin θ ^ 2 * c) volume (-π) π :=
    ((Real.continuous_sin.pow 2).mul continuous_const).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (h1.add h2) h3, intervalIntegral.integral_add h1 h2,
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_mul_const, integral_cos_sq, integral_sin_sq]
  have hsc : ∫ θ in (-π)..π, Real.sin θ * Real.cos θ = 0 := by
    have := integral_sin_pow_mul_cos_pow_odd (a := -π) (b := π) 1 0
    simp only [pow_one, mul_zero, zero_add, pow_zero, mul_one] at this
    rw [this]
    simp
  rw [hsc]
  simp only [Real.sin_neg, Real.cos_neg, Real.sin_pi, Real.cos_pi]
  ring

/-- The circle integral of the second order Taylor polynomial. -/
lemma integral_taylor_poly {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) (z : ℂ) (ρ : ℝ) :
    ∫ θ in Ioo (-π) π, (ρ * Dv φ (eθ θ) z + ρ ^ 2 / 2 * Dv (Dv φ (eθ θ)) (eθ θ) z) =
      π * ρ ^ 2 / 2 * Δ φ z := by
  have hd := differentiable_fderiv_of_contDiff_two hφ
  have e1 : ∀ θ : ℝ, ρ * Dv φ (eθ θ) z + ρ ^ 2 / 2 * Dv (Dv φ (eθ θ)) (eθ θ) z =
      (Real.cos θ * (ρ * fderiv ℝ φ z 1) + Real.sin θ * (ρ * fderiv ℝ φ z I)) +
      (Real.cos θ ^ 2 * (ρ ^ 2 / 2 * fderiv ℝ (fderiv ℝ φ) z 1 1) + Real.sin θ * Real.cos θ *
        (ρ ^ 2 / 2 * (fderiv ℝ (fderiv ℝ φ) z 1 I + fderiv ℝ (fderiv ℝ φ) z I 1)) +
        Real.sin θ ^ 2 * (ρ ^ 2 / 2 * fderiv ℝ (fderiv ℝ φ) z I I)) := by
    intro θ
    rw [Dv_Dv_eq hd, bilin_eθ]
    show ρ * fderiv ℝ φ z (eθ θ) + _ = _
    rw [clm_apply_eq (fderiv ℝ φ z) (eθ θ), eθ_re, eθ_im]
    ring
  simp_rw [e1]
  rw [setIntegral_Ioo_pi, intervalIntegral.integral_add, integral_cos_mul_add_sin_mul,
    integral_quadratic, laplacian_eq_Dv hφ, Dv_Dv_eq hd, Dv_Dv_eq hd]
  · ring
  · exact ((Real.continuous_cos.mul continuous_const).add
      (Real.continuous_sin.mul continuous_const)).intervalIntegrable _ _
  · exact ((((Real.continuous_cos.pow 2).mul continuous_const).add
      ((Real.continuous_sin.mul Real.continuous_cos).mul continuous_const)).add
      ((Real.continuous_sin.pow 2).mul continuous_const)).intervalIntegrable _ _

/-- **Taylor expansion of circle integrals**: `∫_{-π}^{π} (φ(z + ρe^{iθ}) - φ(z)) dθ
= (πρ²/2) Δφ(z) + O(ερ²)` uniformly in `z`. -/
theorem taylor_circle {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ ρ : ℝ, 0 ≤ ρ → ρ < δ → ∀ z : ℂ,
      |∫ θ in Ioo (-π) π, (φ (z + ρ * eθ θ) - φ z - ρ ^ 2 / 4 * Δ φ z)| ≤
        2 * π * ε * ρ ^ 2 := by
  obtain ⟨δ, hδ, hT⟩ := taylor_line hφ hφc hε
  refine ⟨δ, hδ, fun ρ hρ0 hρδ z => ?_⟩
  have hc : Continuous φ := hφ.continuous
  have hd := differentiable_fderiv_of_contDiff_two hφ
  have hcD : Continuous (fun θ : ℝ => Dv φ (eθ θ) z) :=
    (continuous_const (y := fderiv ℝ φ z)).clm_apply continuous_eθ
  have hcB : Continuous (fun θ : ℝ => Dv (Dv φ (eθ θ)) (eθ θ) z) := by
    simp_rw [Dv_Dv_eq hd]
    exact ((continuous_const (y := fderiv ℝ (fderiv ℝ φ) z)).clm_apply continuous_eθ).clm_apply
      continuous_eθ
  have hcphi : Continuous (fun θ : ℝ => φ (z + ρ * eθ θ)) :=
    hc.comp (continuous_const.add (continuous_const.mul continuous_eθ))
  set P : ℝ → ℝ := fun θ => ρ * Dv φ (eθ θ) z + ρ ^ 2 / 2 * Dv (Dv φ (eθ θ)) (eθ θ) z with hP
  set E : ℝ → ℝ := fun θ => φ (z + ρ * eθ θ) - φ z - ρ * Dv φ (eθ θ) z -
    ρ ^ 2 / 2 * Dv (Dv φ (eθ θ)) (eθ θ) z with hE
  have hsplit : ∀ θ, φ (z + ρ * eθ θ) - φ z - ρ ^ 2 / 4 * Δ φ z =
      (P θ - ρ ^ 2 / 4 * Δ φ z) + E θ := by
    intro θ; simp only [hP, hE]; ring
  have hPc : Continuous P := (continuous_const.mul hcD).add (continuous_const.mul hcB)
  have hEc : Continuous E :=
    ((hcphi.sub continuous_const).sub (continuous_const.mul hcD)).sub (continuous_const.mul hcB)
  simp_rw [hsplit]
  rw [setIntegral_Ioo_pi, intervalIntegral.integral_add, intervalIntegral.integral_sub,
    ← setIntegral_Ioo_pi P]
  simp only [hP]
  rw [integral_taylor_poly hφ z ρ, intervalIntegral.integral_const, smul_eq_mul]
  · have hEb : |∫ θ in (-π)..π, E θ| ≤ ε * ρ ^ 2 * |π - -π| := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := -π) (b := π) (f := E)
        (C := ε * ρ ^ 2) (fun θ _ => by
          rw [Real.norm_eq_abs]; exact hT ρ hρ0 hρδ z θ)
      rwa [Real.norm_eq_abs] at this
    rw [abs_of_pos (by linarith [pi_pos] : (0 : ℝ) < π - -π)] at hEb
    have : π * ρ ^ 2 / 2 * Δ φ z - (π - -π) * (ρ ^ 2 / 4 * Δ φ z) = 0 := by ring
    rw [this, zero_add]
    calc |∫ θ in (-π)..π, E θ| ≤ ε * ρ ^ 2 * (π - -π) := hEb
      _ = 2 * π * ε * ρ ^ 2 := by ring
  all_goals first
    | exact hPc.intervalIntegrable _ _
    | exact intervalIntegrable_const
    | exact (hPc.sub continuous_const).intervalIntegrable _ _
    | exact hEc.intervalIntegrable _ _

end Distr

end DF
