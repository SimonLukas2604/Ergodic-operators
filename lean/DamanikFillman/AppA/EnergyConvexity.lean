/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Appendix A.2: strict convexity of the logarithmic energy (Proposition A.2.5)

## Main results

* `DF.Convexity.gaussCombo_eq` — for finite measures `μ, ν` on `ℂ` and `t > 0`,
  `∑± ∫∫ e^{-t|z-w|²} = (4πt)⁻¹ ∫ e^{-|ξ|²/(4t)} |μ̂(ξ) - ν̂(ξ)|² dξ` (Gaussian kernels are
  positive definite); `DF.Convexity.gaussCombo_pos` — this is `> 0` if `μ ≠ ν`.
* `DF.Convexity.neg_log_eq_integral` — Frullani: `-log r = ∫₀^∞ (e^{-rt} - e^{-t})/t dt`.
* `DF.Convexity.smoothCombo_eq` — the smoothed kernels `k_a(x) = -½ log(|x|² + a²)` are
  mixtures of Gaussians, so their quadratic forms on `μ - ν` are
  `½ ∫₀^∞ e^{-a²t} t⁻¹ (Gaussian form)(t) dt`, nonnegative and monotone in `a`.
* `DF.energyStrictConvexityStatement_holds` — **Proposition A.2.5**:
  `E(μ/2 + ν/2) < (E(μ) + E(ν))/2` for distinct `μ, ν ∈ M₁(K)` of finite energy.

The book sketches the proof via Fourier transforms; we follow this route, comparing the truncated
kernels `logKer N` with the smooth kernels `k_a` (both differ by `o(1)` as `a → 0`).
-/
import DamanikFillman.AppA.Frostman
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion
import Mathlib.MeasureTheory.Integral.ExpDecay

noncomputable section

open Real Complex Set Filter Topology MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace DF

namespace Convexity

/-! ### Gaussian kernels are positive definite -/

/-- The Fourier representation of the Gaussian kernel on `ℂ = ℝ²`. -/
lemma gauss_repr {t : ℝ} (ht : 0 < t) (x : ℂ) :
    ((Real.exp (-t * ‖x‖ ^ 2) : ℝ) : ℂ) = ((4 * π * t : ℝ) : ℂ)⁻¹ *
      ∫ ξ : ℂ, cexp (-(((4 * t)⁻¹ : ℝ) : ℂ) * ‖ξ‖ ^ 2 + I * ((⟪x, ξ⟫_ℝ : ℝ) : ℂ)) := by
  have hb : 0 < ((((4 * t)⁻¹ : ℝ) : ℂ)).re := by
    rw [Complex.ofReal_re]; positivity
  rw [integral_cexp_neg_mul_sq_norm_add hb I x]
  have e1 : ((Module.finrank ℝ ℂ : ℕ) / 2 : ℂ) = 1 := by
    rw [Complex.finrank_real_complex]; norm_num
  rw [e1, cpow_one]
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have e2 : (π : ℂ) / (((4 * t)⁻¹ : ℝ) : ℂ) = ((4 * π * t : ℝ) : ℂ) := by
    push_cast; field_simp
  have e3 : I ^ 2 * ((‖x‖ : ℝ) : ℂ) ^ 2 / (4 * (((4 * t)⁻¹ : ℝ) : ℂ)) =
      ((-t * ‖x‖ ^ 2 : ℝ) : ℂ) := by
    rw [I_sq]; push_cast; field_simp
  rw [e2, e3, ← Complex.ofReal_exp, ← mul_assoc, inv_mul_cancel₀ (by
    exact_mod_cast (by positivity : (0 : ℝ) < 4 * π * t).ne'), one_mul]

/-- The Gaussian quadratic form `∫∫ e^{-t|z-w|²} dα(w) dβ(z)` (real valued). -/
def gform (t : ℝ) (α β : Measure ℂ) : ℝ :=
  ∫ z, ∫ w, Real.exp (-t * ‖z - w‖ ^ 2) ∂α ∂β

lemma integrable_gauss {t : ℝ} (ht : 0 < t) :
    Integrable (fun ξ : ℂ => Real.exp (-(4 * t)⁻¹ * ‖ξ‖ ^ 2)) := by
  have hb : 0 < ((((4 * t)⁻¹ : ℝ) : ℂ)).re := by rw [Complex.ofReal_re]; positivity
  have := (integrable_cexp_neg_mul_sq_norm_add hb 0 (0 : ℂ)).norm
  refine this.congr (Eventually.of_forall fun ξ => ?_)
  simp only [zero_mul, add_zero, Complex.norm_exp]
  congr 1
  simp [← Complex.ofReal_pow]

/-- The Fourier side of the Gaussian form. -/
lemma gform_eq {t : ℝ} (ht : 0 < t) (α β : Measure ℂ) [IsFiniteMeasure α] [IsFiniteMeasure β] :
    ((gform t α β : ℝ) : ℂ) = ((4 * π * t : ℝ) : ℂ)⁻¹ *
      ∫ ξ : ℂ, ((Real.exp (-(4 * t)⁻¹ * ‖ξ‖ ^ 2) : ℝ) : ℂ) * charFun β ξ *
        conj (charFun α ξ) := by
  -- the integrand on `(β × α) × ℂ`
  obtain ⟨F, hF⟩ : ∃ F : (ℂ × ℂ) × ℂ → ℂ, ∀ p, F p =
      cexp (-(((4 * t)⁻¹ : ℝ) : ℂ) * ‖p.2‖ ^ 2 + I * ((⟪p.1.1 - p.1.2, p.2⟫_ℝ : ℝ) : ℂ)) :=
    ⟨_, fun _ => rfl⟩
  have hFeq : F = fun p : (ℂ × ℂ) × ℂ =>
      cexp (-(((4 * t)⁻¹ : ℝ) : ℂ) * ‖p.2‖ ^ 2 + I * ((⟪p.1.1 - p.1.2, p.2⟫_ℝ : ℝ) : ℂ)) :=
    funext hF
  have hFnorm : ∀ p, ‖F p‖ = Real.exp (-(4 * t)⁻¹ * ‖p.2‖ ^ 2) := by
    intro p
    rw [hF, Complex.norm_exp]
    congr 1
    simp [← Complex.ofReal_pow]
  have hFm : Continuous F := by
    rw [hFeq]
    fun_prop
  have hFi : Integrable F ((β.prod α).prod volume) := by
    refine Integrable.mono' ((integrable_const (1 : ℝ)).mul_prod (integrable_gauss ht))
      hFm.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
    rw [hFnorm]; simp
  -- rewrite the Gaussian by its Fourier representation
  have h1 : ((gform t α β : ℝ) : ℂ) = ∫ p : ℂ × ℂ, ((4 * π * t : ℝ) : ℂ)⁻¹ *
      ∫ ξ : ℂ, F (p, ξ) ∂volume ∂(β.prod α) := by
    have hcont : Continuous fun p : ℂ × ℂ => Real.exp (-t * ‖p.1 - p.2‖ ^ 2) := by fun_prop
    have hint : Integrable (fun p : ℂ × ℂ => Real.exp (-t * ‖p.1 - p.2‖ ^ 2)) (β.prod α) := by
      refine Integrable.of_bound hcont.aestronglyMeasurable 1 (Eventually.of_forall fun p => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      have := sq_nonneg ‖p.1 - p.2‖
      nlinarith
    have e : gform t α β = ∫ z, ∫ w, (fun p : ℂ × ℂ => Real.exp (-t * ‖p.1 - p.2‖ ^ 2)) (z, w)
        ∂α ∂β := rfl
    rw [e, ← integral_prod _ hint, ← integral_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [hF]
    exact gauss_repr ht _
  rw [h1, integral_const_mul]
  congr 1
  rw [integral_integral_swap (f := fun p ξ => F (p, ξ)) hFi]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  -- split the inner product
  have hsplit : ∀ p : ℂ × ℂ, F (p, ξ) = ((Real.exp (-(4 * t)⁻¹ * ‖ξ‖ ^ 2) : ℝ) : ℂ) *
      (cexp (((⟪p.1, ξ⟫_ℝ : ℝ) : ℂ) * I) * cexp (-(((⟪p.2, ξ⟫_ℝ : ℝ) : ℂ) * I))) := by
    intro p
    rw [hF, Complex.ofReal_exp, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [inner_sub_left]
    push_cast
    ring
  simp_rw [hsplit]
  rw [integral_const_mul, integral_prod_mul (fun z => cexp (((⟪z, ξ⟫_ℝ : ℝ) : ℂ) * I))
    (fun w => cexp (-(((⟪w, ξ⟫_ℝ : ℝ) : ℂ) * I)))]
  have hconj : ∫ w, cexp (-(((⟪w, ξ⟫_ℝ : ℝ) : ℂ) * I)) ∂α = conj (charFun α ξ) := by
    rw [charFun_apply, ← integral_conj]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_ofReal]
  rw [hconj, ← charFun_apply]
  ring

/-- The Gaussian form on `μ - ν`. -/
def gaussCombo (t : ℝ) (μ ν : Measure ℂ) : ℝ :=
  gform t μ μ - gform t μ ν - gform t ν μ + gform t ν ν

lemma gaussCombo_eq {t : ℝ} (ht : 0 < t) (μ ν : Measure ℂ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    gaussCombo t μ ν = (4 * π * t)⁻¹ *
      ∫ ξ : ℂ, Real.exp (-(4 * t)⁻¹ * ‖ξ‖ ^ 2) * ‖charFun μ ξ - charFun ν ξ‖ ^ 2 := by
  have hi : ∀ (α β : Measure ℂ) [IsFiniteMeasure α] [IsFiniteMeasure β],
      Integrable (fun ξ : ℂ => ((Real.exp (-(4 * t)⁻¹ * ‖ξ‖ ^ 2) : ℝ) : ℂ) * charFun β ξ *
        conj (charFun α ξ)) := by
    intro α β _ _
    refine Integrable.mono' ((integrable_gauss ht).mul_const (β.real univ * α.real univ))
      ?_ (Eventually.of_forall fun ξ => ?_)
    · exact ((Complex.continuous_ofReal.comp (by fun_prop)).mul continuous_charFun).mul
        (Complex.continuous_conj.comp continuous_charFun) |>.aestronglyMeasurable
    · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _), Complex.norm_conj, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (norm_charFun_le ξ) (norm_charFun_le ξ)
        (norm_nonneg _) measureReal_nonneg) (Real.exp_pos _).le
  have key : ((gaussCombo t μ ν : ℝ) : ℂ) = ((4 * π * t : ℝ) : ℂ)⁻¹ *
      ∫ ξ : ℂ, ((Real.exp (-(4 * t)⁻¹ * ‖ξ‖ ^ 2) * ‖charFun μ ξ - charFun ν ξ‖ ^ 2 : ℝ) : ℂ) := by
    rw [gaussCombo, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_sub, gform_eq ht,
      gform_eq ht, gform_eq ht, gform_eq ht, ← mul_sub, ← mul_sub, ← mul_add,
      ← integral_sub (hi μ μ) (hi μ ν), ← integral_sub ((hi μ μ).sub (hi μ ν)) (hi ν μ),
      ← integral_add (((hi μ μ).sub (hi μ ν)).sub (hi ν μ)) (hi ν ν)]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    rw [Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj', map_sub]
    ring
  apply Complex.ofReal_injective
  rw [key, Complex.ofReal_mul, Complex.ofReal_inv, ← integral_ofReal]

lemma gaussCombo_pos {t : ℝ} (ht : 0 < t) {μ ν : Measure ℂ} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hne : μ ≠ ν) : 0 < gaussCombo t μ ν := by
  rw [gaussCombo_eq ht]
  refine mul_pos (by positivity) ?_
  set f : ℂ → ℝ := fun ξ => Real.exp (-(4 * t)⁻¹ * ‖ξ‖ ^ 2) * ‖charFun μ ξ - charFun ν ξ‖ ^ 2
    with hf
  have hfc : Continuous f := by
    rw [hf]; exact (by fun_prop : Continuous fun ξ : ℂ => Real.exp (-(4 * t)⁻¹ * ‖ξ‖ ^ 2)).mul
      ((continuous_charFun.sub continuous_charFun).norm.pow 2)
  have hf0 : ∀ ξ, 0 ≤ f ξ := fun ξ => by rw [hf]; positivity
  have hfi : Integrable f := by
    refine Integrable.mono' ((integrable_gauss ht).mul_const ((μ.real univ + ν.real univ) ^ 2))
      hfc.aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 ξ), hf]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    have := (norm_sub_le (charFun μ ξ) (charFun ν ξ)).trans
      (add_le_add (norm_charFun_le ξ) (norm_charFun_le ξ))
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  rcases (integral_nonneg hf0).lt_or_eq with h | h
  · exact h
  exfalso
  have hae : f =ᵐ[volume] 0 := (integral_eq_zero_iff_of_nonneg hf0 hfi).1 h.symm
  have hzero : f = 0 := (hfc.ae_eq_iff_eq volume continuous_const).1 hae
  apply hne
  refine Measure.ext_of_charFun (funext fun ξ => ?_)
  have := congrFun hzero ξ
  simp only [hf, Pi.zero_apply, mul_eq_zero, Real.exp_ne_zero, false_or, pow_eq_zero_iff,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, norm_eq_zero, sub_eq_zero] at this
  exact this

end Convexity

end DF
