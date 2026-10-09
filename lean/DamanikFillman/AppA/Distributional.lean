/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Appendix A.3, preliminaries: the fundamental solution of the Laplacian in the plane

Toward the Riesz representation of subharmonic functions (Theorem A.3.2) we develop a little
distributional calculus on `ℂ ≅ ℝ²`.

## Main results

* `DF.Distr.laplacian_eq_Dv` — `Δφ = ∂₁∂₁φ + ∂_I∂_Iφ` for `C²` functions, with directional
  derivatives `Dv φ v = fderiv ℝ φ · v`;
* `DF.Distr.integral_mul_laplacian` — first Green identity
  `∫ L Δφ = -∫ (∂₁L ∂₁φ + ∂_I L ∂_I φ)` for `C¹` functions `L` and compactly supported `C²`
  functions `φ` (integration by parts);
* `DF.Distr.integral_log_mul_laplacian` — **the fundamental solution**:
  `∫ log |z| Δφ(z) dz = 2π φ(0)` for compactly supported `C²` functions `φ`.

## Proof of the fundamental solution

Regularize `log |z|` by `L_ε(z) = ½ log(|z|² + ε²)`, whose gradient is `z / (|z|² + ε²)`.  The
first Green identity gives `∫ L_ε Δφ = -∫ Dφ(z)[z] / (|z|² + ε²)`.  Letting `ε → 0` (dominated
convergence, using local integrability of `log |z|` and `1/|z|` in the plane) yields
`∫ log |z| Δφ = -∫ Dφ(z)[z] / |z|²`, and in polar coordinates the integrand becomes
`∂_r φ(r e^{iθ})`, whose radial integral is `-φ(0)`.
-/
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.DominatedConvergence

noncomputable section

open Real Complex Metric Set Filter Topology MeasureTheory Laplacian InnerProductSpace

namespace DF

namespace Distr

/-- The directional derivative `∂_v f`. -/
def Dv (f : ℂ → ℝ) (v : ℂ) : ℂ → ℝ := fun z => fderiv ℝ f z v

lemma differentiable_fderiv_of_contDiff_two {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) :
    Differentiable ℝ (fderiv ℝ f) :=
  (hf.fderiv_right (m := 1) (by norm_num)).differentiable le_rfl

lemma differentiable_Dv {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) (v : ℂ) : Differentiable ℝ (Dv f v) :=
  fun z => ((differentiable_fderiv_of_contDiff_two hf) z).clm_apply (differentiableAt_const v)

lemma continuous_Dv {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (v : ℂ) : Continuous (Dv f v) :=
  (hf.continuous_fderiv le_rfl).clm_apply continuous_const

lemma contDiff_one_Dv {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) (v : ℂ) : ContDiff ℝ 1 (Dv f v) :=
  (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

lemma hasCompactSupport_Dv {f : ℂ → ℝ} (hf : HasCompactSupport f) (v : ℂ) :
    HasCompactSupport (Dv f v) :=
  hf.fderiv_apply (𝕜 := ℝ) v

/-- `Δφ = ∂₁∂₁φ + ∂_I∂_Iφ`. -/
lemma laplacian_eq_Dv {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) (z : ℂ) :
    Δ f z = Dv (Dv f 1) 1 z + Dv (Dv f I) I z := by
  have hd := differentiable_fderiv_of_contDiff_two hf
  have key : ∀ v, Dv (Dv f v) v z = fderiv ℝ (fderiv ℝ f) z v v := by
    intro v
    simp only [Dv]
    rw [fderiv_clm_apply (hd z) (differentiableAt_const v)]
    simp
  rw [key 1, key I]
  simp only [laplacian_eq_iteratedFDeriv_complexPlane, iteratedFDeriv_two_apply, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]

/-- An `ℝ`-linear functional on `ℂ` in coordinates. -/
lemma clm_apply_eq (ℓ : ℂ →L[ℝ] ℝ) (z : ℂ) : ℓ z = z.re * ℓ 1 + z.im * ℓ I := by
  have hz : z = z.re • (1 : ℂ) + z.im • I := by
    apply Complex.ext <;> simp
  calc ℓ z = ℓ (z.re • (1 : ℂ) + z.im • I) := by rw [← hz]
    _ = z.re * ℓ 1 + z.im * ℓ I := by rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]

/-- Integrability of continuous functions against compactly supported continuous functions. -/
lemma integrable_mul_of_hasCompactSupport {f g : ℂ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hgc : HasCompactSupport g) : Integrable (fun z => f z * g z) :=
  (hf.mul hg).integrable_of_hasCompactSupport hgc.mul_left

/-- **First Green identity**: `∫ L Δφ = -∫ ∇L · ∇φ`. -/
theorem integral_mul_laplacian {L φ : ℂ → ℝ} (hL : ContDiff ℝ 1 L) (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) :
    ∫ z, L z * Δ φ z = -∫ z, (Dv L 1 z * Dv φ 1 z + Dv L I z * Dv φ I z) := by
  have hLc : Continuous L := hL.continuous
  have hLd : Differentiable ℝ L := hL.differentiable le_rfl
  -- integration by parts in one direction
  have ibp : ∀ v : ℂ, ∫ z, L z * Dv (Dv φ v) v z = -∫ z, Dv L v z * Dv φ v z := by
    intro v
    have hg := hasCompactSupport_Dv hφc v
    have hgg := hasCompactSupport_Dv hg v
    have hgd := differentiable_Dv hφ v
    exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (f := L) (g := Dv φ v) (v := v)
      (integrable_mul_of_hasCompactSupport (continuous_Dv hL v)
        (continuous_Dv (hφ.of_le (by norm_num)) v) hg)
      (integrable_mul_of_hasCompactSupport hLc (continuous_Dv (contDiff_one_Dv hφ v) v) hgg)
      (integrable_mul_of_hasCompactSupport hLc (continuous_Dv (hφ.of_le (by norm_num)) v) hg)
      (fun x _ => hLd x) (fun x _ => hgd x)
  have e : (fun z => L z * Δ φ z) =
      fun z => L z * Dv (Dv φ 1) 1 z + L z * Dv (Dv φ I) I z := by
    funext z; rw [laplacian_eq_Dv hφ z]; ring
  have i1 : Integrable (fun z => L z * Dv (Dv φ 1) 1 z) :=
    integrable_mul_of_hasCompactSupport hLc (continuous_Dv (contDiff_one_Dv hφ 1) 1)
      (hasCompactSupport_Dv (hasCompactSupport_Dv hφc 1) 1)
  have i2 : Integrable (fun z => L z * Dv (Dv φ I) I z) :=
    integrable_mul_of_hasCompactSupport hLc (continuous_Dv (contDiff_one_Dv hφ I) I)
      (hasCompactSupport_Dv (hasCompactSupport_Dv hφc I) I)
  have j1 : Integrable (fun z => Dv L 1 z * Dv φ 1 z) :=
    integrable_mul_of_hasCompactSupport (continuous_Dv hL 1)
      (continuous_Dv (hφ.of_le (by norm_num)) 1) (hasCompactSupport_Dv hφc 1)
  have j2 : Integrable (fun z => Dv L I z * Dv φ I z) :=
    integrable_mul_of_hasCompactSupport (continuous_Dv hL I)
      (continuous_Dv (hφ.of_le (by norm_num)) I) (hasCompactSupport_Dv hφc I)
  rw [e, integral_add i1 i2, ibp 1, ibp I, integral_add j1 j2]
  ring

/-! ### The regularized kernel -/

/-- `L_ε(z) = ½ log(|z|² + ε²)`. -/
def Lε (ε : ℝ) (z : ℂ) : ℝ := (1 / 2) * Real.log (‖z‖ ^ 2 + ε ^ 2)

lemma hasFDerivAt_Lε {ε : ℝ} (hε : ε ≠ 0) (z : ℂ) :
    HasFDerivAt (Lε ε) ((1 / 2 : ℝ) • ((‖z‖ ^ 2 + ε ^ 2)⁻¹ • (2 • innerSL ℝ z))) z := by
  have hpos : ‖z‖ ^ 2 + ε ^ 2 ≠ 0 := by positivity
  have h1 : HasFDerivAt (fun x : ℂ => ‖x‖ ^ 2 + ε ^ 2) (2 • innerSL ℝ z) z :=
    (hasStrictFDerivAt_norm_sq z).hasFDerivAt.add_const _
  exact (h1.log hpos).const_mul (1 / 2)

lemma contDiff_Lε {ε : ℝ} (hε : ε ≠ 0) : ContDiff ℝ 1 (Lε ε) := by
  unfold Lε
  refine contDiff_const.mul (ContDiff.log ?_ fun z => by positivity)
  exact (contDiff_norm_sq ℝ).add contDiff_const

lemma Dv_Lε {ε : ℝ} (hε : ε ≠ 0) (z v : ℂ) :
    Dv (Lε ε) v z = (v * conj z).re / (‖z‖ ^ 2 + ε ^ 2) := by
  simp only [Dv, (hasFDerivAt_Lε hε z).fderiv]
  simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, Complex.inner]
  field_simp

lemma grad_Lε_dot {ε : ℝ} (hε : ε ≠ 0) (φ : ℂ → ℝ) (z : ℂ) :
    Dv (Lε ε) 1 z * Dv φ 1 z + Dv (Lε ε) I z * Dv φ I z =
      fderiv ℝ φ z z / (‖z‖ ^ 2 + ε ^ 2) := by
  rw [Dv_Lε hε, Dv_Lε hε, clm_apply_eq (fderiv ℝ φ z) z]
  simp only [Dv]
  have h1 : ((1 : ℂ) * conj z).re = z.re := by simp
  have h2 : (I * conj z).re = z.im := by simp
  rw [h1, h2]
  ring

/-! ### Local integrability in the plane -/

lemma norm_log_le (R : ℝ) {z : ℂ} (hz : z ∈ ball (0 : ℂ) R) (hz0 : z ≠ 0) :
    ‖Real.log ‖z‖‖ ≤ max 1 (R ^ 2) * ‖z‖ ^ (-(1 : ℝ)) := by
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hzR : ‖z‖ < R := by simpa using hz
  rw [Real.rpow_neg_one, Real.norm_eq_abs]
  rcases le_or_gt ‖z‖ 1 with h | h
  · rw [abs_of_nonpos (Real.log_nonpos hn.le h)]
    have : -Real.log ‖z‖ ≤ ‖z‖⁻¹ := by
      have := Real.log_le_sub_one_of_pos (inv_pos.2 hn)
      rw [Real.log_inv] at this
      linarith
    calc -Real.log ‖z‖ ≤ ‖z‖⁻¹ := this
      _ ≤ max 1 (R ^ 2) * ‖z‖⁻¹ := le_mul_of_one_le_left (inv_pos.2 hn).le (le_max_left _ _)
  · rw [abs_of_pos (Real.log_pos h)]
    have h1 : Real.log ‖z‖ ≤ ‖z‖ := (Real.log_le_sub_one_of_pos hn).trans (by linarith)
    have h2 : ‖z‖ ≤ R ^ 2 * ‖z‖⁻¹ := by
      rw [le_mul_inv_iff₀ hn]
      nlinarith
    calc Real.log ‖z‖ ≤ ‖z‖ := h1
      _ ≤ R ^ 2 * ‖z‖⁻¹ := h2
      _ ≤ max 1 (R ^ 2) * ‖z‖⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (inv_pos.2 hn).le

lemma finrank_complex : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex

lemma integrableOn_log_norm (R : ℝ) :
    IntegrableOn (fun z : ℂ => Real.log ‖z‖) (ball 0 R) := by
  refine integrableOn_ball_of_norm_le_rpow (by rw [finrank_complex]; norm_num)
    (C := max 1 (R ^ 2)) (α := 1) (by rw [finrank_complex]; norm_num) ?_
    (by fun_prop)
  have h0 : ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) R)), z ≠ 0 := by
    refine ae_restrict_of_ae ?_
    rw [ae_iff]
    simp
  filter_upwards [h0, ae_restrict_mem measurableSet_ball] with z hz0 hz
  exact norm_log_le R hz hz0

lemma integrableOn_inv_norm (R : ℝ) :
    IntegrableOn (fun z : ℂ => ‖z‖⁻¹) (ball 0 R) := by
  refine integrableOn_ball_of_norm_le_rpow (by rw [finrank_complex]; norm_num)
    (C := 1) (α := 1) (by rw [finrank_complex]; norm_num) ?_ (by fun_prop)
  refine Eventually.of_forall fun z => ?_
  rw [Real.rpow_neg_one, one_mul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.2 (norm_nonneg _))]

/-- Products of locally integrable-on-balls functions with compactly supported continuous
functions are integrable. -/
lemma integrable_mul_of_integrableOn_ball {f g : ℂ → ℝ} {R : ℝ}
    (hf : IntegrableOn f (closedBall 0 R)) (hg : Continuous g) (hgs : support g ⊆ closedBall 0 R) :
    Integrable (fun z => f z * g z) := by
  have h := hf.mul_continuousOn hg.continuousOn (isCompact_closedBall 0 R)
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 h
  intro z hz
  exact hgs (right_ne_zero_of_mul hz)

lemma integrableOn_closedBall_of_ball {f : ℂ → ℝ} {R : ℝ} (h : IntegrableOn f (ball 0 (R + 1))) :
    IntegrableOn f (closedBall 0 R) :=
  h.mono_set (closedBall_subset_ball (by linarith))

/-! ### The fundamental solution -/

lemma exists_support_subset_closedBall {φ : ℂ → ℝ} (hφc : HasCompactSupport φ) :
    ∃ R, 0 < R ∧ tsupport φ ⊆ closedBall 0 R := by
  obtain ⟨R, hR⟩ := hφc.isBounded.subset_closedBall 0
  exact ⟨max R 1, by positivity, hR.trans (closedBall_subset_closedBall (le_max_left _ _))⟩

lemma laplacian_eq_zero_of_notMem {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) {z : ℂ}
    (hz : z ∉ tsupport φ) : Δ φ z = 0 := by
  rw [laplacian_eq_Dv hφ z]
  have h : ∀ v : ℂ, Dv (Dv φ v) v z = 0 := by
    intro v
    have hz' : z ∉ tsupport (Dv φ v) := fun h => hz (tsupport_fderiv_apply_subset ℝ v h)
    simp only [Dv] at hz' ⊢
    rw [fderiv_of_notMem_tsupport ℝ hz']
    rfl
  rw [h 1, h I, add_zero]

lemma continuous_laplacian {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) : Continuous (Δ φ) := by
  have e : Δ φ = fun z => Dv (Dv φ 1) 1 z + Dv (Dv φ I) I z := funext (laplacian_eq_Dv hφ)
  rw [e]
  exact (continuous_Dv (contDiff_one_Dv hφ 1) 1).add (continuous_Dv (contDiff_one_Dv hφ I) I)

lemma norm_e (θ : ℝ) : ‖(Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I‖ = 1 := by
  have : (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I = Complex.exp (θ * I) := by
    rw [Complex.exp_mul_I]; push_cast; ring
  rw [this]
  exact Complex.norm_exp_ofReal_mul_I θ

/-- The polar-coordinate computation: `∫ Dφ(z)[z] / |z|² = -2π φ(0)`. -/
lemma integral_fderiv_div_normSq {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) :
    ∫ z, fderiv ℝ φ z z / ‖z‖ ^ 2 = -(2 * π * φ 0) := by
  obtain ⟨R, hR, hRs⟩ := exists_support_subset_closedBall hφc
  have hd : Differentiable ℝ φ := hφ.differentiable le_rfl
  have hcf : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv le_rfl
  obtain ⟨C, hC⟩ := (hφc.fderiv (𝕜 := ℝ)).exists_bound_of_continuous hcf
  set e : ℝ → ℂ := fun θ => (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I with he
  have hne : ∀ θ, ‖e θ‖ = 1 := norm_e
  have hce : Continuous e := by rw [he]; fun_prop
  -- the integrand in polar coordinates
  set G : ℝ × ℝ → ℝ := fun p => fderiv ℝ φ ((p.1 : ℂ) * e p.2) (e p.2) with hG
  have hGc : Continuous G := by
    rw [hG]
    exact (hcf.comp ((continuous_ofReal.comp continuous_fst).mul (hce.comp continuous_snd))).clm_apply
      (hce.comp continuous_snd)
  have hGb : ∀ p, ‖G p‖ ≤ C := by
    intro p
    calc ‖G p‖ ≤ ‖fderiv ℝ φ ((p.1 : ℂ) * e p.2)‖ * ‖e p.2‖ := (fderiv ℝ φ _).le_opNorm _
      _ ≤ C * 1 := by rw [hne]; exact mul_le_mul_of_nonneg_right (hC _) zero_le_one
      _ = C := mul_one C
  have hG0 : ∀ p : ℝ × ℝ, R < |p.1| → G p = 0 := by
    intro p hp
    have hnot : (p.1 : ℂ) * e p.2 ∉ tsupport φ := by
      intro h
      have := hRs h
      rw [mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        hne, mul_one] at this
      linarith
    simp only [hG, fderiv_of_notMem_tsupport ℝ hnot, ContinuousLinearMap.zero_apply]
  have hpolar : ∀ p ∈ polarCoord.target,
      p.1 • (fun z => fderiv ℝ φ z z / ‖z‖ ^ 2) (Complex.polarCoord.symm p) = G p := by
    rintro ⟨r, θ⟩ hp
    have hr : 0 < r := hp.1
    have hr0 := hr.ne'
    simp only [Complex.polarCoord_symm_apply, smul_eq_mul, hG]
    have hz : ((r : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I)) = r • e θ := by
      rw [Complex.real_smul]
    have hn : ‖r • e θ‖ = r := by rw [norm_smul, hne, Real.norm_eq_abs, abs_of_pos hr, mul_one]
    rw [hz, hn, map_smul, smul_eq_mul, ← Complex.real_smul]
    field_simp
  have hint : ∫ z, fderiv ℝ φ z z / ‖z‖ ^ 2 = ∫ p in polarCoord.target, G p := by
    rw [← Complex.integral_comp_polarCoord_symm]
    exact setIntegral_congr_fun polarCoord.open_target.measurableSet hpolar
  rw [hint, polarCoord_target]
  -- integrability on the target
  have hGint : IntegrableOn G (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) := by
    have h1 : IntegrableOn G (Ioc (0 : ℝ) R ×ˢ Ioo (-π) π) := by
      refine IntegrableOn.of_bound ?_ hGc.aestronglyMeasurable C
        (Eventually.of_forall hGb)
      rw [Measure.volume_eq_prod, Measure.prod_prod]
      simp [ENNReal.mul_lt_top]
    refine h1.of_forall_sdiff_eq_zero (measurableSet_Ioi.prod measurableSet_Ioo) ?_
    rintro ⟨r, θ⟩ ⟨⟨hr, hθ⟩, hn⟩
    apply hG0
    have hr' : (0 : ℝ) < r := hr
    have hRr : R < r := by
      by_contra hle
      push Not at hle
      exact hn ⟨⟨hr', hle⟩, hθ⟩
    rwa [abs_of_pos hr']
  refine (setIntegral_prod (μ := volume) (ν := volume) G hGint).trans ?_
  have hsw : Integrable (Function.uncurry fun (r : ℝ) (θ : ℝ) => G (r, θ))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-π) π))) := by
    rw [Measure.prod_restrict]
    exact hGint
  rw [integral_integral_swap hsw]
  have hinner : ∀ θ : ℝ, ∫ r in Ioi (0 : ℝ), G (r, θ) = -φ 0 := by
    intro θ
    have hf : ∀ r ∈ Ioi (0 : ℝ),
        HasDerivAt (fun r : ℝ => φ ((r : ℂ) * e θ)) (G (r, θ)) r := by
      intro r _
      have h1 : HasDerivAt (fun r : ℝ => (r : ℂ) * e θ) ((1 : ℝ) * e θ) r :=
        (hasDerivAt_id r).ofReal_comp.mul_const (e θ)
      have h2 := (hd ((r : ℂ) * e θ)).hasFDerivAt.comp_hasDerivAt r h1
      simpa [hG] using h2
    have hcont : ContinuousWithinAt (fun r : ℝ => φ ((r : ℂ) * e θ)) (Ici 0) 0 :=
      (hφ.continuous.comp (continuous_ofReal.mul continuous_const)).continuousWithinAt
    have hint' : IntegrableOn (fun r => G (r, θ)) (Ioi 0) := by
      have h1 : IntegrableOn (fun r => G (r, θ)) (Ioc 0 R) :=
        IntegrableOn.of_bound (by simp)
          (hGc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable C
          (Eventually.of_forall fun r => hGb _)
      refine h1.of_forall_sdiff_eq_zero measurableSet_Ioi fun r hr => hG0 _ ?_
      obtain ⟨hr0, hrR⟩ := hr
      have h0 : (0 : ℝ) < r := hr0
      simp only [mem_Ioc, not_and, not_le] at hrR
      rw [abs_of_pos h0]
      exact hrR h0
    have hlim : Tendsto (fun r : ℝ => φ ((r : ℂ) * e θ)) atTop (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop R] with r hr
      have hnot : (r : ℂ) * e θ ∉ tsupport φ := by
        intro h
        have := hRs h
        rw [mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          hne, mul_one, abs_of_pos (hR.trans hr)] at this
        linarith
      exact (image_eq_zero_of_notMem_tsupport hnot).symm
    rw [integral_Ioi_of_hasDerivAt_of_tendsto hcont hf hint' hlim]
    simp
  simp_rw [hinner]
  rw [setIntegral_const, Real.volume_real_Ioo_of_le (by linarith [Real.pi_pos]), smul_eq_mul]
  ring

/-- **The fundamental solution of the Laplacian**: `∫ log |z| Δφ(z) dz = 2π φ(0)`. -/
theorem integral_log_mul_laplacian {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) :
    ∫ z, Real.log ‖z‖ * Δ φ z = 2 * π * φ 0 := by
  obtain ⟨R, hR, hRs⟩ := exists_support_subset_closedBall hφc
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hεdef
  have hεpos : ∀ n, 0 < ε n := fun n => by positivity
  have hεle : ∀ n, ε n ≤ 1 := fun n => by
    rw [hεdef]
    exact div_le_one_of_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (by positivity)
  have hε0 : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hφ1 : ContDiff ℝ 1 φ := hφ.of_le (by norm_num)
  have hΔc := continuous_laplacian hφ
  have hΔs : support (Δ φ) ⊆ closedBall 0 R := fun z hz =>
    hRs (by by_contra h; exact hz (laplacian_eq_zero_of_notMem hφ h))
  have hae0 : ∀ᵐ z : ℂ ∂volume, z ≠ 0 := by
    have : ({0}ᶜ : Set ℂ) ∈ ae volume := compl_mem_ae_iff.2 (measure_singleton 0)
    filter_upwards [this] with z hz
    exact hz
  -- the regularized identity
  have hid : ∀ n, ∫ z, Lε (ε n) z * Δ φ z = -∫ z, fderiv ℝ φ z z / (‖z‖ ^ 2 + ε n ^ 2) := by
    intro n
    rw [integral_mul_laplacian (contDiff_Lε (hεpos n).ne') hφ hφc]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun z => grad_Lε_dot (hεpos n).ne' φ z)
  -- the left-hand side converges
  have hL : Tendsto (fun n => ∫ z, Lε (ε n) z * Δ φ z) atTop
      (𝓝 (∫ z, Real.log ‖z‖ * Δ φ z)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun z => (|Real.log ‖z‖| + |(1 / 2) * Real.log (‖z‖ ^ 2 + 1)|) * |Δ φ z|)
      (fun n => ((contDiff_Lε (hεpos n).ne').continuous.mul hΔc).aestronglyMeasurable)
      ?_ (fun n => ?_) ?_
    · have h1 : Integrable (fun z => |Real.log ‖z‖| * |Δ φ z|) := by
        refine integrable_mul_of_integrableOn_ball
          (integrableOn_closedBall_of_ball (integrableOn_log_norm (R + 1))).abs hΔc.abs ?_
        intro z hz
        exact hΔs (by simpa using hz)
      have h2 : Integrable (fun z => |(1 / 2) * Real.log (‖z‖ ^ 2 + 1)| * |Δ φ z|) := by
        refine integrable_mul_of_hasCompactSupport (by fun_prop) hΔc.abs ?_
        exact (HasCompactSupport.intro (isCompact_closedBall 0 R) fun z hz => by
          have : z ∉ support (Δ φ) := fun h => hz (hΔs h)
          simpa using this)
      refine (h1.add h2).congr (Eventually.of_forall fun z => ?_)
      simp only [Pi.add_apply]
      ring
    · filter_upwards [hae0] with z hz
      have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
      have hlow : Real.log ‖z‖ ≤ Lε (ε n) z := by
        unfold Lε
        have e1 : Real.log ‖z‖ = (1 / 2) * Real.log (‖z‖ ^ 2) := by
          rw [Real.log_pow]; push_cast; ring
        rw [e1]
        exact mul_le_mul_of_nonneg_left
          (Real.log_le_log (by positivity) (by nlinarith [sq_nonneg (ε n)])) (by norm_num)
      have hup : Lε (ε n) z ≤ (1 / 2) * Real.log (‖z‖ ^ 2 + 1) := by
        unfold Lε
        have : ε n ^ 2 ≤ 1 := by
          have := hεle n; have := hεpos n; nlinarith
        exact mul_le_mul_of_nonneg_left
          (Real.log_le_log (by positivity) (by linarith)) (by norm_num)
      rw [Real.norm_eq_abs, abs_mul]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      refine abs_le.2 ⟨?_, ?_⟩
      · linarith [neg_abs_le (Real.log ‖z‖), abs_nonneg ((1 / 2) * Real.log (‖z‖ ^ 2 + 1))]
      · linarith [le_abs_self ((1 / 2) * Real.log (‖z‖ ^ 2 + 1)), abs_nonneg (Real.log ‖z‖)]
    · filter_upwards [hae0] with z hz
      have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
      have h1 : Tendsto (fun n => ‖z‖ ^ 2 + ε n ^ 2) atTop (𝓝 (‖z‖ ^ 2 + 0 ^ 2)) :=
        tendsto_const_nhds.add (hε0.pow 2)
      have h2 := ((Real.continuousAt_log (by positivity)).tendsto.comp h1).const_mul (1 / 2)
      have h3 : (1 / 2) * Real.log (‖z‖ ^ 2 + 0 ^ 2) = Real.log ‖z‖ := by
        rw [zero_pow two_ne_zero, add_zero, Real.log_pow]; push_cast; ring
      rw [h3] at h2
      exact h2.mul_const _
  -- the right-hand side converges
  have hRt : Tendsto (fun n => ∫ z, fderiv ℝ φ z z / (‖z‖ ^ 2 + ε n ^ 2)) atTop
      (𝓝 (∫ z, fderiv ℝ φ z z / ‖z‖ ^ 2)) := by
    have hcf : Continuous (fderiv ℝ φ) := hφ1.continuous_fderiv le_rfl
    refine tendsto_integral_of_dominated_convergence (fun z => ‖z‖⁻¹ * ‖fderiv ℝ φ z‖)
      (fun n => ?_) ?_ (fun n => ?_) ?_
    · exact ((hcf.clm_apply continuous_id).div (by fun_prop)
        (fun z => by have := hεpos n; positivity)).aestronglyMeasurable
    · refine integrable_mul_of_integrableOn_ball
        (integrableOn_closedBall_of_ball (integrableOn_inv_norm (R + 1))) hcf.norm ?_
      intro z hz
      have : z ∈ support (fderiv ℝ φ) := by simpa using hz
      exact hRs (support_fderiv_subset ℝ this)
    · filter_upwards [hae0] with z hz
      have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (by have := hεpos n; positivity)]
      calc |fderiv ℝ φ z z| / (‖z‖ ^ 2 + ε n ^ 2) ≤ ‖fderiv ℝ φ z‖ * ‖z‖ / ‖z‖ ^ 2 := by
            refine div_le_div₀ (by positivity) ?_ (by positivity) (by nlinarith [sq_nonneg (ε n)])
            rw [← Real.norm_eq_abs]
            exact (fderiv ℝ φ z).le_opNorm z
        _ = ‖z‖⁻¹ * ‖fderiv ℝ φ z‖ := by field_simp
    · filter_upwards [hae0] with z hz
      have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
      have h1 : Tendsto (fun n => ‖z‖ ^ 2 + ε n ^ 2) atTop (𝓝 (‖z‖ ^ 2 + 0 ^ 2)) :=
        tendsto_const_nhds.add (hε0.pow 2)
      rw [zero_pow two_ne_zero, add_zero] at h1
      exact tendsto_const_nhds.div h1 (by positivity)
  have hlim := hRt.neg
  rw [integral_fderiv_div_normSq hφ1 hφc, neg_neg] at hlim
  refine tendsto_nhds_unique hL ?_
  exact hlim.congr fun n => (hid n).symm

end Distr

end DF
