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
open GaussianFourier

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
    rw [e, ← integral_prod _ hint, ← integral_complex_ofReal]
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
    dsimp only
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
    have hpt : (fun ξ : ℂ => ((Real.exp (-(4 * t)⁻¹ * ‖ξ‖ ^ 2) *
        ‖charFun μ ξ - charFun ν ξ‖ ^ 2 : ℝ) : ℂ)) = fun ξ =>
        ((Real.exp (-(4 * t)⁻¹ * ‖ξ‖ ^ 2) : ℝ) : ℂ) * charFun μ ξ * conj (charFun μ ξ) -
        ((Real.exp (-(4 * t)⁻¹ * ‖ξ‖ ^ 2) : ℝ) : ℂ) * charFun ν ξ * conj (charFun μ ξ) -
        ((Real.exp (-(4 * t)⁻¹ * ‖ξ‖ ^ 2) : ℝ) : ℂ) * charFun μ ξ * conj (charFun ν ξ) +
        ((Real.exp (-(4 * t)⁻¹ * ‖ξ‖ ^ 2) : ℝ) : ℂ) * charFun ν ξ * conj (charFun ν ξ) := by
      funext ξ
      rw [Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj', map_sub]
      ring
    rw [hpt, integral_add, integral_sub, integral_sub]
    · rw [gaussCombo, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_sub, gform_eq ht,
        gform_eq ht, gform_eq ht, gform_eq ht]
      ring
    all_goals first
      | exact hi _ _
      | exact (hi μ μ).sub (hi μ ν)
      | exact ((hi μ μ).sub (hi μ ν)).sub (hi ν μ)
  apply Complex.ofReal_injective
  rw [key, Complex.ofReal_mul ((4 * π * t)⁻¹), Complex.ofReal_inv, integral_complex_ofReal]

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
  have hI : 0 ≤ ∫ ξ, f ξ := integral_nonneg hf0
  rcases hI.lt_or_eq with h | h
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

/-! ### Frullani's integral for `-log r` -/

lemma abs_exp_neg_sub_le (u v : ℝ) :
    |rexp (-u) - rexp (-v)| ≤ rexp (-min u v) * |u - v| := by
  rcases le_total u v with h | h
  · rw [min_eq_left h, abs_of_nonneg (sub_nonneg.2 (Real.exp_le_exp.2 (neg_le_neg h))),
      abs_of_nonpos (sub_nonpos.2 h)]
    have h1 := Real.add_one_le_exp (-(v - u))
    have h2 : rexp (-v) = rexp (-u) * rexp (-(v - u)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h2]
    have h3 := Real.exp_pos (-u)
    nlinarith
  · rw [min_eq_right h, abs_of_nonpos (sub_nonpos.2 (Real.exp_le_exp.2 (neg_le_neg h))),
      abs_of_nonneg (sub_nonneg.2 h)]
    have h1 := Real.add_one_le_exp (-(u - v))
    have h2 : rexp (-u) = rexp (-v) * rexp (-(u - v)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h2]
    have h3 := Real.exp_pos (-v)
    nlinarith

lemma frullani_bound {r t : ℝ} (ht : 0 < t) :
    |t⁻¹ * (rexp (-(r * t)) - rexp (-t))| ≤ |r - 1| * rexp (-(min r 1 * t)) := by
  have h := abs_exp_neg_sub_le (r * t) t
  have e1 : min (r * t) t = min r 1 * t := by rw [min_mul_of_nonneg _ _ ht.le, one_mul]
  have e2 : r * t - t = (r - 1) * t := by ring
  rw [e1, e2, abs_mul, abs_of_pos ht] at h
  rw [abs_mul, abs_inv, abs_of_pos ht]
  calc t⁻¹ * |rexp (-(r * t)) - rexp (-t)|
      ≤ t⁻¹ * (rexp (-(min r 1 * t)) * (|r - 1| * t)) :=
        mul_le_mul_of_nonneg_left h (inv_nonneg.2 ht.le)
    _ = |r - 1| * rexp (-(min r 1 * t)) * (t⁻¹ * t) := by ring
    _ = _ := by rw [inv_mul_cancel₀ ht.ne', mul_one]

lemma integrableOn_frullani {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t⁻¹ * (rexp (-(r * t)) - rexp (-t))) (Ioi 0) := by
  have hm : 0 < min r 1 := lt_min hr one_pos
  have hb : IntegrableOn (fun t : ℝ => |r - 1| * rexp (-(min r 1 * t))) (Ioi 0) := by
    have := (exp_neg_integrableOn_Ioi 0 hm).const_mul |r - 1|
    simpa only [neg_mul] using this
  refine Integrable.mono' hb (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun t ht => ?_)
  rw [Real.norm_eq_abs]
  exact frullani_bound ht

/-- **Frullani's integral**: `-log r = ∫₀^∞ (e^{-rt} - e^{-t}) / t dt`. -/
lemma neg_log_eq_integral {r : ℝ} (hr : 0 < r) :
    ∫ t in Ioi (0 : ℝ), t⁻¹ * (rexp (-(r * t)) - rexp (-t)) = -Real.log r := by
  have hc : Continuous fun x : ℝ => rexp (-x) := by fun_prop
  have hf : LocallyIntegrableOn (fun x : ℝ => rexp (-x)) (Ioi 0) :=
    hc.locallyIntegrable.locallyIntegrableOn _
  have hL : Tendsto (fun x : ℝ => rexp (-x)) (𝓝[>] 0) (𝓝 1) := by
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this
  have hR : Tendsto (fun x : ℝ => rexp (-x)) atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero
  have h := Frullani.integral_Ioi_eq hf hr one_pos hL hR (by simpa using integrableOn_frullani hr)
  simp only [smul_eq_mul, one_mul, sub_zero, mul_one, one_div, Real.log_inv] at h
  exact h

/-! ### The smoothed kernels `k_b(x) = -½ log (|x|² + b)` -/

/-- The smoothed logarithmic kernel `k_b(x) = -½ log (|x|² + b)`. -/
def kb (b : ℝ) (x : ℂ) : ℝ := -(1 / 2) * Real.log (‖x‖ ^ 2 + b)

lemma continuous_kb {b : ℝ} (hb : 0 < b) : Continuous (kb b) := by
  unfold kb
  exact continuous_const.mul ((by fun_prop : Continuous fun x : ℂ => ‖x‖ ^ 2 + b).log
    fun x => (add_pos_of_nonneg_of_pos (sq_nonneg _) hb).ne')

lemma kb_eq_integral {b : ℝ} (hb : 0 < b) (x : ℂ) :
    kb b x = (1 / 2) * ∫ t in Ioi (0 : ℝ),
      t⁻¹ * (rexp (-((‖x‖ ^ 2 + b) * t)) - rexp (-t)) := by
  rw [kb, neg_log_eq_integral (add_pos_of_nonneg_of_pos (sq_nonneg _) hb)]
  ring

lemma kb_le_logKer {b : ℝ} {M : ℕ} (hM : rexp (-(M : ℝ)) ≤ b) (x : ℂ) :
    kb b x ≤ logKer M x := by
  have hm := max_norm_exp_pos M x
  have he1 : rexp (-(M : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (neg_nonpos.2 (Nat.cast_nonneg _))
  have he0 := Real.exp_pos (-(M : ℝ))
  have hsq : max ‖x‖ (rexp (-(M : ℝ))) ^ 2 ≤ ‖x‖ ^ 2 + b := by
    rcases le_total ‖x‖ (rexp (-(M : ℝ))) with h | h
    · rw [max_eq_right h]; nlinarith [sq_nonneg ‖x‖]
    · rw [max_eq_left h]; linarith
  have hlog := Real.log_le_log (pow_pos hm 2) hsq
  rw [Real.log_pow] at hlog
  unfold kb logKer
  push_cast at hlog
  linarith

lemma logKer_le_kb {b : ℝ} (hb : 0 < b) (N : ℕ) (x : ℂ) :
    logKer N x ≤ kb b x + (1 / 2) * Real.log (1 + b * rexp (N : ℝ) ^ 2) := by
  obtain ⟨m, hmd⟩ : ∃ m, m = max ‖x‖ (rexp (-(N : ℝ))) := ⟨_, rfl⟩
  have hm : 0 < m := by rw [hmd]; exact max_norm_exp_pos N x
  have h1 : ‖x‖ ≤ m := by rw [hmd]; exact le_max_left _ _
  have h2 : rexp (-(N : ℝ)) ≤ m := by rw [hmd]; exact le_max_right _ _
  have hE : 0 < rexp (N : ℝ) := Real.exp_pos _
  have h3 : 1 ≤ m * rexp (N : ℝ) := by
    have := mul_le_mul_of_nonneg_right h2 hE.le
    rwa [← Real.exp_add, neg_add_cancel, Real.exp_zero] at this
  have hc : 0 ≤ b * rexp (N : ℝ) ^ 2 := mul_nonneg hb.le (sq_nonneg _)
  have hsq : ‖x‖ ^ 2 + b ≤ m ^ 2 * (1 + b * rexp (N : ℝ) ^ 2) := by
    have h4 : 1 ≤ (m * rexp (N : ℝ)) ^ 2 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left h4 hb.le,
      mul_self_le_mul_self (norm_nonneg x) h1]
  have hpos : 0 < ‖x‖ ^ 2 + b := add_pos_of_nonneg_of_pos (sq_nonneg _) hb
  have hlog := Real.log_le_log hpos hsq
  rw [Real.log_mul (pow_pos hm 2).ne' (by linarith : (0 : ℝ) < 1 + b * rexp (N : ℝ) ^ 2).ne',
    Real.log_pow] at hlog
  unfold kb logKer
  rw [← hmd]
  push_cast at hlog
  linarith

/-! ### Double integrals against measures on a compact set -/

lemma ae_prod_mem {K : Set ℂ} {α β : Measure ℂ} [SFinite α] [SFinite β] (hα : α Kᶜ = 0)
    (hβ : β Kᶜ = 0) : ∀ᵐ p ∂(β.prod α), p.1 ∈ K ∧ p.2 ∈ K := by
  rw [ae_iff]
  refine measure_mono_null (t := Kᶜ ×ˢ univ ∪ univ ×ˢ Kᶜ) ?_ (measure_union_null ?_ ?_)
  · intro p hp
    simp only [mem_setOf_eq, not_and_or] at hp
    rcases hp with h | h
    · exact Or.inl ⟨h, trivial⟩
    · exact Or.inr ⟨trivial, h⟩
  · rw [Measure.prod_prod, hβ, zero_mul]
  · rw [Measure.prod_prod, hα, mul_zero]

lemma integrable_prod_of_continuous {K : Set ℂ} (hK : IsCompact K) {α β : Measure ℂ}
    (hα : α ∈ M1 K) (hβ : β ∈ M1 K) {f : ℂ × ℂ → ℝ} (hf : Continuous f) :
    Integrable f (β.prod α) := by
  haveI := hα.1; haveI := hβ.1
  obtain ⟨C, hC⟩ := (hK.prod hK).exists_bound_of_continuousOn hf.continuousOn
  refine Integrable.of_bound hf.aestronglyMeasurable C ?_
  filter_upwards [ae_prod_mem hα.2 hβ.2] with p hp
  exact hC p ⟨hp.1, hp.2⟩

lemma iint_eq_prod {K : Set ℂ} (hK : IsCompact K) {α β : Measure ℂ} (hα : α ∈ M1 K)
    (hβ : β ∈ M1 K) {f : ℂ → ℝ} (hf : Continuous f) :
    ∫ z, ∫ w, f (z - w) ∂α ∂β = ∫ p, f (p.1 - p.2) ∂(β.prod α) := by
  haveI := hα.1; haveI := hβ.1
  have hc : Continuous fun p : ℂ × ℂ => f (p.1 - p.2) := hf.comp (continuous_fst.sub continuous_snd)
  exact (integral_prod _ (integrable_prod_of_continuous hK hα hβ hc)).symm

/-- The smoothed mutual energy `∫∫ k_b(z - w) dα(w) dβ(z)`. -/
def kform (b : ℝ) (α β : Measure ℂ) : ℝ := ∫ z, ∫ w, kb b (z - w) ∂α ∂β

lemma kform_le_Itr {K : Set ℂ} (hK : IsCompact K) {α β : Measure ℂ} (hα : α ∈ M1 K)
    (hβ : β ∈ M1 K) {b : ℝ} {M : ℕ} (hM : rexp (-(M : ℝ)) ≤ b) :
    kform b α β ≤ Itr M α β := by
  have hb : 0 < b := (Real.exp_pos _).trans_le hM
  unfold kform Itr
  rw [iint_eq_prod hK hα hβ (continuous_kb hb), iint_eq_prod hK hα hβ (continuous_logKer M)]
  exact integral_mono
    (integrable_prod_of_continuous hK hα hβ
      ((continuous_kb hb).comp (continuous_fst.sub continuous_snd)))
    (integrable_prod_of_continuous hK hα hβ
      ((continuous_logKer M).comp (continuous_fst.sub continuous_snd)))
    fun p => kb_le_logKer hM _

lemma Itr_le_kform {K : Set ℂ} (hK : IsCompact K) {α β : Measure ℂ} (hα : α ∈ M1 K)
    (hβ : β ∈ M1 K) {b : ℝ} (hb : 0 < b) (N : ℕ) :
    Itr N α β ≤ kform b α β + (1 / 2) * Real.log (1 + b * rexp (N : ℝ) ^ 2) := by
  haveI := hα.1; haveI := hβ.1
  unfold kform Itr
  rw [iint_eq_prod hK hα hβ (continuous_kb hb), iint_eq_prod hK hα hβ (continuous_logKer N)]
  have hint := integrable_prod_of_continuous hK hα hβ
    ((continuous_kb hb).comp (continuous_fst.sub continuous_snd))
  calc ∫ p, logKer N (p.1 - p.2) ∂(β.prod α)
      ≤ ∫ p, (kb b (p.1 - p.2) + (1 / 2) * Real.log (1 + b * rexp (N : ℝ) ^ 2)) ∂(β.prod α) :=
        integral_mono (integrable_prod_of_continuous hK hα hβ
          ((continuous_logKer N).comp (continuous_fst.sub continuous_snd)))
          (hint.add (integrable_const _)) fun p => logKer_le_kb hb N _
    _ = _ := by
        rw [integral_add hint (integrable_const _), integral_const]
        simp

/-- Fubini: the smoothed mutual energy as a mixture of Gaussian forms. -/
lemma kform_eq {K : Set ℂ} (hK : IsCompact K) {α β : Measure ℂ} (hα : α ∈ M1 K)
    (hβ : β ∈ M1 K) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t⁻¹ * (rexp (-(b * t)) * gform t α β - rexp (-t))) (Ioi 0) ∧
    kform b α β = (1 / 2) *
      ∫ t in Ioi (0 : ℝ), t⁻¹ * (rexp (-(b * t)) * gform t α β - rexp (-t)) := by
  haveI := hα.1; haveI := hβ.1
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  obtain ⟨F, hF⟩ : ∃ F : (ℂ × ℂ) × ℝ → ℝ, ∀ q, F q =
      q.2⁻¹ * (rexp (-((‖q.1.1 - q.1.2‖ ^ 2 + b) * q.2)) - rexp (-q.2)) := ⟨_, fun _ => rfl⟩
  have hFeq : F = fun q : (ℂ × ℂ) × ℝ =>
      q.2⁻¹ * (rexp (-((‖q.1.1 - q.1.2‖ ^ 2 + b) * q.2)) - rexp (-q.2)) := funext hF
  have hm : 0 < min b 1 := lt_min hb one_pos
  -- integrability on the triple product
  have hFi : Integrable F ((β.prod α).prod (volume.restrict (Ioi 0))) := by
    have hg : Integrable (fun t : ℝ => rexp (-(min b 1 * t))) (volume.restrict (Ioi 0)) := by
      have := exp_neg_integrableOn_Ioi 0 hm
      simpa only [neg_mul] using this
    refine Integrable.mono' ((integrable_const (4 * R ^ 2 + b + 1 : ℝ)).mul_prod hg)
      (Measurable.aestronglyMeasurable (by rw [hFeq]; fun_prop)) ?_
    have h1 : ∀ᵐ q ∂((β.prod α).prod (volume.restrict (Ioi 0))), q.1.1 ∈ K ∧ q.1.2 ∈ K :=
      Measure.quasiMeasurePreserving_fst.ae (ae_prod_mem hα.2 hβ.2)
    have h2 : ∀ᵐ q ∂((β.prod α).prod (volume.restrict (Ioi 0))), q.2 ∈ Ioi (0 : ℝ) :=
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioi)
    filter_upwards [h1, h2] with q hq hq2
    have ht : 0 < q.2 := hq2
    rw [hF, Real.norm_eq_abs]
    refine (frullani_bound ht).trans ?_
    have hz := hR _ hq.1
    have hw := hR _ hq.2
    have hzw : ‖q.1.1 - q.1.2‖ ≤ 2 * R := by linarith [norm_sub_le q.1.1 q.1.2]
    have hzw2 : ‖q.1.1 - q.1.2‖ ^ 2 ≤ 4 * R ^ 2 := by
      nlinarith [norm_nonneg (q.1.1 - q.1.2)]
    have hr1 : |‖q.1.1 - q.1.2‖ ^ 2 + b - 1| ≤ 4 * R ^ 2 + b + 1 := by
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg ‖q.1.1 - q.1.2‖]
    have hexp : rexp (-(min (‖q.1.1 - q.1.2‖ ^ 2 + b) 1 * q.2)) ≤ rexp (-(min b 1 * q.2)) := by
      refine Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right ?_ ht.le))
      exact min_le_min_right _ (by linarith [sq_nonneg ‖q.1.1 - q.1.2‖])
    exact mul_le_mul hr1 hexp (Real.exp_pos _).le (by linarith [abs_nonneg (b - 1),
      abs_nonneg (‖q.1.1 - q.1.2‖ ^ 2 + b - 1)])
  -- the inner integrals
  have hinner : ∀ t : ℝ, 0 < t → ∫ p, F (p, t) ∂(β.prod α) =
      t⁻¹ * (rexp (-(b * t)) * gform t α β - rexp (-t)) := by
    intro t ht
    have hg : Integrable (fun p : ℂ × ℂ => Real.exp (-t * ‖p.1 - p.2‖ ^ 2)) (β.prod α) := by
      refine Integrable.of_bound (by fun_prop : Continuous fun p : ℂ × ℂ =>
        Real.exp (-t * ‖p.1 - p.2‖ ^ 2)).aestronglyMeasurable 1
        (Eventually.of_forall fun p => ?_)
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      have := sq_nonneg ‖p.1 - p.2‖
      nlinarith
    have hgf : gform t α β = ∫ p, Real.exp (-t * ‖p.1 - p.2‖ ^ 2) ∂(β.prod α) :=
      (integral_prod _ hg).symm
    have e : ∀ p : ℂ × ℂ, F (p, t) = t⁻¹ * rexp (-(b * t)) * Real.exp (-t * ‖p.1 - p.2‖ ^ 2) -
        t⁻¹ * rexp (-t) := by
      intro p
      rw [hF]
      dsimp only
      have : rexp (-((‖p.1 - p.2‖ ^ 2 + b) * t)) =
          rexp (-(b * t)) * Real.exp (-t * ‖p.1 - p.2‖ ^ 2) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [this]; ring
    simp_rw [e]
    rw [integral_sub (hg.const_mul _) (integrable_const _), integral_const_mul, integral_const,
      hgf]
    simp only [probReal_univ, one_smul]
    ring
  have hkb : (fun p : ℂ × ℂ => kb b (p.1 - p.2)) =
      fun p => (1 / 2) * ∫ t, F (p, t) ∂(volume.restrict (Ioi 0)) := by
    funext p
    rw [kb_eq_integral hb]
    simp only [hF]
  refine ⟨hFi.integral_prod_right.congr
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hinner)), ?_⟩
  have hkint : Integrable (fun p : ℂ × ℂ => kb b (p.1 - p.2)) (β.prod α) :=
    integrable_prod_of_continuous hK hα hβ
      ((continuous_kb hb).comp (continuous_fst.sub continuous_snd))
  have e1 : kform b α β = ∫ p, kb b (p.1 - p.2) ∂(β.prod α) := (integral_prod _ hkint).symm
  rw [e1, hkb, integral_const_mul, integral_integral_swap (f := fun p t => F (p, t)) hFi,
    setIntegral_congr_fun measurableSet_Ioi hinner]

/-- The quadratic form of `k_b` on `μ - ν` as a mixture of Gaussian forms. -/
lemma kcombo_eq {K : Set ℂ} (hK : IsCompact K) {μ ν : Measure ℂ} (hμ : μ ∈ M1 K)
    (hν : ν ∈ M1 K) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun t : ℝ => t⁻¹ * rexp (-(b * t)) * gaussCombo t μ ν) (Ioi 0) ∧
    kform b μ μ - kform b μ ν - kform b ν μ + kform b ν ν =
      (1 / 2) * ∫ t in Ioi (0 : ℝ), t⁻¹ * rexp (-(b * t)) * gaussCombo t μ ν := by
  obtain ⟨i1, e1⟩ := kform_eq hK hμ hμ hb
  obtain ⟨i2, e2⟩ := kform_eq hK hμ hν hb
  obtain ⟨i3, e3⟩ := kform_eq hK hν hμ hb
  obtain ⟨i4, e4⟩ := kform_eq hK hν hν hb
  have hpt : (fun t : ℝ => t⁻¹ * rexp (-(b * t)) * gaussCombo t μ ν) = fun t =>
      t⁻¹ * (rexp (-(b * t)) * gform t μ μ - rexp (-t)) -
        t⁻¹ * (rexp (-(b * t)) * gform t μ ν - rexp (-t)) -
        t⁻¹ * (rexp (-(b * t)) * gform t ν μ - rexp (-t)) +
        t⁻¹ * (rexp (-(b * t)) * gform t ν ν - rexp (-t)) := by
    funext t; rw [gaussCombo]; ring
  refine ⟨?_, ?_⟩
  · rw [hpt]; exact ((i1.sub i2).sub i3).add i4
  · rw [hpt, integral_add, integral_sub, integral_sub, e1, e2, e3, e4]
    · ring
    all_goals first
      | exact i1 | exact i2 | exact i3 | exact i4
      | exact i1.sub i2
      | exact (i1.sub i2).sub i3

end Convexity

open Convexity in
/-- **Proposition A.2.5** (strict convexity of the logarithmic energy). -/
theorem energyStrictConvexityStatement_holds : EnergyStrictConvexityStatement := by
  intro K hK μ hμ ν hν hEμ hEν hne
  haveI := hμ.1; haveI := hν.1
  have hμa := adm_of_M1 hK hμ
  have hνa := adm_of_M1 hK hν
  obtain ⟨Eμ, hEμd⟩ : ∃ E, E = (energy μ).toReal := ⟨_, rfl⟩
  obtain ⟨Eν, hEνd⟩ : ∃ E, E = (energy ν).toReal := ⟨_, rfl⟩
  have hIμ : ∀ N, Itr N μ μ ≤ Eμ := fun N => by
    have := Itr_le_energy μ N
    rw [energy_toReal_eq hEμ, ← hEμd] at this
    exact_mod_cast this
  have hIν : ∀ N, Itr N ν ν ≤ Eν := fun N => by
    have := Itr_le_energy ν N
    rw [energy_toReal_eq hEν, ← hEνd] at this
    exact_mod_cast this
  -- the uniform gain `δ > 0`
  obtain ⟨hδi, -⟩ := kcombo_eq hK hμ hν one_pos
  obtain ⟨δ, hδd⟩ : ∃ δ, δ = ∫ t in Ioi (0 : ℝ), t⁻¹ * rexp (-(1 * t)) * gaussCombo t μ ν :=
    ⟨_, rfl⟩
  have hpos : ∀ t : ℝ, 0 < t → 0 < t⁻¹ * rexp (-(1 * t)) * gaussCombo t μ ν := fun t ht =>
    mul_pos (mul_pos (inv_pos.2 ht) (Real.exp_pos _)) (gaussCombo_pos ht hne)
  have hδ : 0 < δ := by
    rw [hδd, setIntegral_pos_iff_support_of_nonneg_ae _ hδi]
    · have : Function.support (fun t : ℝ => t⁻¹ * rexp (-(1 * t)) * gaussCombo t μ ν) ∩
          Ioi 0 = Ioi 0 := by
        ext t
        simp only [mem_inter_iff, Function.mem_support, mem_Ioi, and_iff_right_iff_imp]
        exact fun ht => (hpos t ht).ne'
      rw [this, Real.volume_Ioi]
      exact ENNReal.zero_lt_top
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact (hpos t ht).le
  have hD : ∀ b : ℝ, 0 < b → b ≤ 1 →
      δ ≤ ∫ t in Ioi (0 : ℝ), t⁻¹ * rexp (-(b * t)) * gaussCombo t μ ν := by
    intro b hb hb1
    rw [hδd]
    refine setIntegral_mono_on hδi (kcombo_eq hK hμ hν hb).1 measurableSet_Ioi fun t ht => ?_
    have ht' : 0 < t := ht
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 ht'.le))
      (gaussCombo_pos ht' hne).le
    exact Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_right hb1 ht'.le))
  -- the mutual terms
  have hcross : ∀ N : ℕ, Itr N μ ν + Itr N ν μ ≤ Eμ + Eν - δ / 4 := by
    intro N
    have hE := Real.exp_pos (N : ℝ)
    obtain ⟨b, hbd⟩ : ∃ b, b = min 1 (δ / (4 * rexp (N : ℝ) ^ 2)) := ⟨_, rfl⟩
    have hb : 0 < b := by rw [hbd]; exact lt_min one_pos (div_pos hδ (by positivity))
    have hb1 : b ≤ 1 := by rw [hbd]; exact min_le_left _ _
    have hc : b * rexp (N : ℝ) ^ 2 ≤ δ / 4 := by
      have h1 : b ≤ δ / (4 * rexp (N : ℝ) ^ 2) := by rw [hbd]; exact min_le_right _ _
      have h2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg (rexp (N : ℝ)))
      rwa [div_mul_eq_mul_div, mul_div_mul_right _ _ (pow_ne_zero 2 hE.ne')] at h2
    obtain ⟨M, hM⟩ : ∃ M : ℕ, rexp (-(M : ℝ)) ≤ b := by
      obtain ⟨M, hM⟩ := exists_nat_gt (-Real.log b)
      exact ⟨M, by rw [← Real.exp_log hb]; exact Real.exp_le_exp.2 (by linarith)⟩
    obtain ⟨-, hcomb⟩ := kcombo_eq hK hμ hν hb
    have hDb := hD b hb hb1
    have k1 := kform_le_Itr hK hμ hμ hM
    have k2 := kform_le_Itr hK hν hν hM
    have j1 := Itr_le_kform hK hμ hν hb N
    have j2 := Itr_le_kform hK hν hμ hb N
    have hlog : Real.log (1 + b * rexp (N : ℝ) ^ 2) ≤ b * rexp (N : ℝ) ^ 2 := by
      have h0 : 0 < b * rexp (N : ℝ) ^ 2 := mul_pos hb (pow_pos hE 2)
      have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + b * rexp (N : ℝ) ^ 2)
      linarith
    linarith [hIμ M, hIν M]
  -- the energy of the midpoint
  have hs : (1 / 2 : ℝ≥0∞) ≠ ⊤ := ENNReal.div_ne_top ENNReal.one_ne_top two_ne_zero
  have a1 := hμa.smul hs
  have a2 := hνa.smul hs
  have h2 : (1 / 2 : ℝ≥0∞).toReal = 1 / 2 := by
    rw [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofNat, one_div]
  have hmix : ∀ N, Itr N ((1 / 2 : ℝ≥0∞) • μ + (1 / 2 : ℝ≥0∞) • ν)
      ((1 / 2 : ℝ≥0∞) • μ + (1 / 2 : ℝ≥0∞) • ν) ≤ (Eμ + Eν) / 2 - δ / 16 := by
    intro N
    rw [Itr_add_left a1 a2 (a1.add a2), Itr_add_right a1 a1 a2, Itr_add_right a2 a1 a2]
    simp only [Itr_smul_left, Itr_smul_right, h2]
    linarith [hIμ N, hIν N, hcross N]
  rw [← hEμd, ← hEνd]
  calc energy ((1 / 2 : ℝ≥0∞) • μ + (1 / 2 : ℝ≥0∞) • ν)
      ≤ (((Eμ + Eν) / 2 - δ / 16 : ℝ) : EReal) := by
        rw [energy_eq_iSup_Itr]
        exact iSup_le fun N => EReal.coe_le_coe_iff.2 (hmix N)
    _ < (((Eμ + Eν) / 2 : ℝ) : EReal) := EReal.coe_lt_coe_iff.2 (by linarith)

/-- **Theorem A.2.6, uniqueness** (unconditional). -/
theorem IsEquilibriumMeasure.unique' {K : Set ℂ} (hK : IsCompact K) (hcap : capCompact K ≠ 0)
    {ρ ρ' : Measure ℂ} (h : IsEquilibriumMeasure K ρ) (h' : IsEquilibriumMeasure K ρ') :
    ρ = ρ' :=
  h.unique energyStrictConvexityStatement_holds hK hcap h'


end DF
