/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Appendix A.1: the Hilbert transform on `L²(ℝ)` (Proposition A.1.5)

## Main results

* `DF.HilbertL2.hilbertL2` — the unitary `U = 𝓕⁻¹ ∘ (-i sgn ξ) ∘ 𝓕` on `L²(ℝ)`.
* `DF.hilbertL2Statement_holds` — **Proposition A.1.5**: `U² = -1`, `U` acts on the Fourier side
  as multiplication by `-i sgn ξ`, and `U g = Hg` (the principal value) a.e. for Schwartz `g`.

## Proof of `U g = Hg`

* The conjugate Poisson kernel `Q_y(x) = x / (π (x² + y²))` is the inverse Fourier transform of
  `-i sgn(ξ) e^{-2π y |ξ|}` (`kernel_eq`, an elementary computation with exponentials), so
  `∫ e^{-2π y |ξ|} (-i sgn ξ) ĝ(ξ) e^{2π i ξ t} dξ = (Q_y * g)(t)` (Fubini).
* As `y → 0`, the left side tends to `F(t) = ∫ (-i sgn ξ) ĝ(ξ) e^{2π i ξ t} dξ` (dominated
  convergence), while `|Q_y * g(t) - H_y g(t)| ≤ L y` for `L`-Lipschitz `g` (the difference kernel
  is odd and `|x| |Q_y(x) - 1_{|x|>y}/(πx)| ≤ y² / (π (x² + y²))`), and `H_y g(t) → Hg(t)`.
  Hence `F = Hg` everywhere.
* `U g = F` a.e.: both have the same pairing with every Schwartz function (Plancherel on one
  side, Fubini on the other), and locally integrable functions are determined by their pairings
  with smooth compactly supported functions.
-/
import DamanikFillman.AppA.HolderHilbert

noncomputable section

open Real Complex Set Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate InnerProductSpace
open FourierTransform SchwartzMap

namespace DF

namespace HilbertL2

/-! ### The Fourier multiplier `-i sgn ξ` on `L²` -/

/-- The symbol `-i sgn ξ` of the Hilbert transform. -/
def symb (ξ : ℝ) : ℂ := -I * (Real.sign ξ : ℂ)

lemma measurable_sign : Measurable Real.sign := by
  have : Real.sign = fun r : ℝ => if r < 0 then (-1 : ℝ) else if 0 < r then 1 else 0 := rfl
  rw [this]
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
      measurable_const)

lemma measurable_symb : Measurable symb :=
  measurable_const.mul (Complex.measurable_ofReal.comp measurable_sign)

lemma symb_of_pos {ξ : ℝ} (h : 0 < ξ) : symb ξ = -I := by simp [symb, Real.sign_of_pos h]

lemma symb_of_neg {ξ : ℝ} (h : ξ < 0) : symb ξ = I := by simp [symb, Real.sign_of_neg h]

lemma norm_symb_le (ξ : ℝ) : ‖symb ξ‖ ≤ 1 := by
  rcases lt_trichotomy ξ 0 with h | h | h
  · rw [symb_of_neg h, Complex.norm_I]
  · simp [symb, h]
  · rw [symb_of_pos h, norm_neg, Complex.norm_I]

lemma symb_ae : ∀ᵐ ξ ∂(volume : Measure ℝ), ‖symb ξ‖ = 1 ∧ symb ξ * symb ξ = -1 := by
  have h0 : ∀ᵐ ξ ∂(volume : Measure ℝ), ξ ∉ ({0} : Set ℝ) :=
    measure_eq_zero_iff_ae_notMem.1 Real.volume_singleton
  filter_upwards [h0] with ξ hξ
  rcases lt_trichotomy ξ 0 with h | h | h
  · rw [symb_of_neg h]; exact ⟨Complex.norm_I, I_mul_I⟩
  · exact absurd h (by simpa using hξ)
  · rw [symb_of_pos h]; exact ⟨by rw [norm_neg, Complex.norm_I], by rw [neg_mul_neg, I_mul_I]⟩

lemma memLp_mulSymb (f : Lp ℂ 2 (volume : Measure ℝ)) : MemLp (fun ξ => symb ξ * f ξ) 2 :=
  (Lp.memLp f).of_le (measurable_symb.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
    (Eventually.of_forall fun ξ => by
      rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (norm_symb_le ξ))

/-- Multiplication by `-i sgn ξ` on `L²(ℝ)`. -/
def mulSymb (f : Lp ℂ 2 (volume : Measure ℝ)) : Lp ℂ 2 (volume : Measure ℝ) := (memLp_mulSymb f).toLp _

lemma coeFn_mulSymb (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (mulSymb f : ℝ → ℂ) =ᵐ[volume] fun ξ => symb ξ * f ξ :=
  MemLp.coeFn_toLp _

lemma mulSymb_add (f g : Lp ℂ 2 (volume : Measure ℝ)) : mulSymb (f + g) = mulSymb f + mulSymb g := by
  apply Lp.ext
  filter_upwards [coeFn_mulSymb (f + g), coeFn_mulSymb f, coeFn_mulSymb g, Lp.coeFn_add f g,
    Lp.coeFn_add (mulSymb f) (mulSymb g)] with ξ h1 h2 h3 h4 h5
  rw [h5, Pi.add_apply, h1, h2, h3, h4, Pi.add_apply]
  ring

lemma mulSymb_smul (c : ℂ) (f : Lp ℂ 2 (volume : Measure ℝ)) : mulSymb (c • f) = c • mulSymb f := by
  apply Lp.ext
  filter_upwards [coeFn_mulSymb (c • f), coeFn_mulSymb f, Lp.coeFn_smul c f,
    Lp.coeFn_smul c (mulSymb f)] with ξ h1 h2 h3 h4
  rw [h4, Pi.smul_apply, h1, h2, h3, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

lemma mulSymb_neg (f : Lp ℂ 2 (volume : Measure ℝ)) : mulSymb (-f) = -mulSymb f := by
  apply Lp.ext
  filter_upwards [coeFn_mulSymb (-f), coeFn_mulSymb f, Lp.coeFn_neg f,
    Lp.coeFn_neg (mulSymb f)] with ξ h1 h2 h3 h4
  rw [h4, Pi.neg_apply, h1, h2, h3, Pi.neg_apply]
  ring

lemma mulSymb_mulSymb (f : Lp ℂ 2 (volume : Measure ℝ)) : mulSymb (mulSymb f) = -f := by
  apply Lp.ext
  filter_upwards [coeFn_mulSymb (mulSymb f), coeFn_mulSymb f, Lp.coeFn_neg f, symb_ae]
    with ξ h1 h2 h3 h4
  rw [h1, h2, h3, Pi.neg_apply, ← mul_assoc, h4.2]
  ring

lemma norm_mulSymb (f : Lp ℂ 2 (volume : Measure ℝ)) : ‖mulSymb f‖ = ‖f‖ := by
  have h : ∀ᵐ ξ ∂(volume : Measure ℝ), ‖(mulSymb f : ℝ → ℂ) ξ‖ = ‖(f : ℝ → ℂ) ξ‖ := by
    filter_upwards [coeFn_mulSymb f, symb_ae] with ξ h1 h2
    rw [h1, norm_mul, h2.1, one_mul]
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_norm_ae h]

/-- Multiplication by `-i sgn ξ` as a unitary operator. -/
def mulSymbₗᵢ : Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun := mulSymb
  invFun f := -mulSymb f
  map_add' := mulSymb_add
  map_smul' := mulSymb_smul
  left_inv f := by
    show -mulSymb (mulSymb f) = f
    rw [mulSymb_mulSymb, neg_neg]
  right_inv f := by
    show mulSymb (-mulSymb f) = f
    rw [mulSymb_neg, mulSymb_mulSymb, neg_neg]
  norm_map' := norm_mulSymb

/-- The Hilbert transform on `L²(ℝ)`: `U = 𝓕⁻¹ ∘ (-i sgn ξ) ∘ 𝓕`. -/
def hilbertL2 : Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  (Lp.fourierTransformₗᵢ ℝ ℂ).trans (mulSymbₗᵢ.trans (Lp.fourierTransformₗᵢ ℝ ℂ).symm)

lemma hilbertL2_apply (f : Lp ℂ 2 (volume : Measure ℝ)) :
    hilbertL2 f = (Lp.fourierTransformₗᵢ ℝ ℂ).symm (mulSymb (Lp.fourierTransformₗᵢ ℝ ℂ f)) :=
  rfl

lemma fourier_hilbertL2 (f : Lp ℂ 2 (volume : Measure ℝ)) :
    Lp.fourierTransformₗᵢ ℝ ℂ (hilbertL2 f) = mulSymb (Lp.fourierTransformₗᵢ ℝ ℂ f) := by
  rw [hilbertL2_apply, LinearIsometryEquiv.apply_symm_apply]

lemma hilbertL2_hilbertL2 (f : Lp ℂ 2 (volume : Measure ℝ)) : hilbertL2 (hilbertL2 f) = -f := by
  rw [hilbertL2_apply, fourier_hilbertL2, mulSymb_mulSymb, map_neg,
    LinearIsometryEquiv.symm_apply_apply]

/-! ### The conjugate Poisson kernel -/

/-- The conjugate Poisson kernel `Q_y(x) = x / (π (x² + y²))`. -/
def poissonQ (y x : ℝ) : ℝ := x / (π * (x ^ 2 + y ^ 2))

lemma sq_add_sq_pos {y : ℝ} (hy : 0 < y) (x : ℝ) : 0 < x ^ 2 + y ^ 2 :=
  add_pos_of_nonneg_of_pos (sq_nonneg x) (pow_pos hy 2)

/-- `Q_y` is the inverse Fourier transform of `-i sgn(ξ) e^{-2π y |ξ|}`. -/
lemma kernel_eq {y : ℝ} (hy : 0 < y) (x : ℝ) :
    ∫ ξ : ℝ, symb ξ * ((rexp (-(2 * π * y) * |ξ|) : ℝ) : ℂ) * cexp (((2 * π * ξ * x : ℝ) : ℂ) * I)
      = ((poissonQ y x : ℝ) : ℂ) := by
  set k : ℝ → ℂ := fun ξ =>
    symb ξ * ((rexp (-(2 * π * y) * |ξ|) : ℝ) : ℂ) * cexp (((2 * π * ξ * x : ℝ) : ℂ) * I) with hk
  have hb : 0 < 2 * π * y := by positivity
  have hkm : Measurable k := by
    rw [hk]
    exact (measurable_symb.mul (by fun_prop)).mul (by fun_prop)
  have hki : Integrable k := by
    refine Integrable.mono' (PlemeljPrivalov.integrable_comp_abs'
      (f := fun r => rexp (-(2 * π * y) * r)) (exp_neg_integrableOn_Ioi 0 hb))
      hkm.aestronglyMeasurable (Eventually.of_forall fun ξ => ?_)
    rw [hk]
    simp only
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
      Complex.norm_exp_ofReal_mul_I, mul_one]
    exact mul_le_of_le_one_left (Real.exp_pos _).le (norm_symb_le ξ)
  set a₁ : ℂ := ((-(2 * π * y) : ℝ) : ℂ) + ((2 * π * x : ℝ) : ℂ) * I with ha₁
  set a₂ : ℂ := ((-(2 * π * y) : ℝ) : ℂ) - ((2 * π * x : ℝ) : ℂ) * I with ha₂
  have ha₁re : a₁.re < 0 := by
    rw [ha₁]; simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero]; linarith
  have ha₂re : a₂.re < 0 := by
    rw [ha₂]; simp only [sub_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, sub_zero]; linarith
  have ha₁0 : a₁ ≠ 0 := fun h => by rw [h, zero_re] at ha₁re; exact lt_irrefl _ ha₁re
  have ha₂0 : a₂ ≠ 0 := fun h => by rw [h, zero_re] at ha₂re; exact lt_irrefl _ ha₂re
  -- the two half-lines
  have hpos : ∫ ξ in Ioi (0 : ℝ), k ξ = -I * (-cexp (a₁ * ((0 : ℝ) : ℂ)) / a₁) := by
    rw [← integral_exp_mul_complex_Ioi ha₁re 0, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun ξ hξ => ?_
    have hξ' : 0 < ξ := hξ
    rw [hk]
    simp only
    rw [symb_of_pos hξ', abs_of_pos hξ', Complex.ofReal_exp, mul_assoc, ← Complex.exp_add]
    congr 2
    rw [ha₁]; push_cast; ring
  have hneg : ∫ ξ in Iic (0 : ℝ), k ξ = I * (-cexp (a₂ * ((0 : ℝ) : ℂ)) / a₂) := by
    have hc := integral_comp_neg_Ioi 0 k
    rw [neg_zero] at hc
    rw [← hc, ← integral_exp_mul_complex_Ioi ha₂re 0, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun ξ hξ => ?_
    have hξ' : 0 < ξ := hξ
    rw [hk]
    simp only
    rw [symb_of_neg (neg_lt_zero.2 hξ'), abs_neg, abs_of_pos hξ', Complex.ofReal_exp, mul_assoc,
      ← Complex.exp_add]
    congr 2
    rw [ha₂]; push_cast; ring
  have hsplit : ∫ ξ, k ξ = (∫ ξ in Iic (0 : ℝ), k ξ) + ∫ ξ in Ioi (0 : ℝ), k ξ := by
    rw [← setIntegral_union (Iic_disjoint_Ioi le_rfl) measurableSet_Ioi hki.integrableOn
      hki.integrableOn, Iic_union_Ioi, Measure.restrict_univ]
  rw [hsplit, hpos, hneg]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  have hprod : a₁ * a₂ = ((4 * π ^ 2 * (x ^ 2 + y ^ 2) : ℝ) : ℂ) := by
    rw [ha₁, ha₂]; push_cast; linear_combination (-((2 * (π : ℂ) * x) ^ 2)) * I_sq
  have hnum : I * a₂ - a₁ * I = ((4 * π * x : ℝ) : ℂ) := by
    rw [ha₁, ha₂]; push_cast; linear_combination (-(4 * (π : ℂ) * x)) * I_sq
  have e : I * (-1 / a₂) + -I * (-1 / a₁) = (I * a₂ - a₁ * I) / (a₁ * a₂) := by
    field_simp; ring
  rw [e, hnum, hprod, ← Complex.ofReal_div]
  congr 1
  unfold poissonQ
  have := sq_add_sq_pos hy x
  have hπ := Real.pi_pos
  rw [div_eq_div_iff (mul_pos (by positivity) this).ne' (mul_pos hπ this).ne']
  ring

/-! ### The difference kernel `Q_y - 1_{|x| > y} / (π x)` -/

/-- The difference between the conjugate Poisson kernel and the truncated Hilbert kernel. -/
def diffKer (y x : ℝ) : ℝ :=
  poissonQ y x - (1 / π) * Set.indicator {x : ℝ | y < |x|} (fun x => x⁻¹) x

lemma measurable_diffKer (y : ℝ) : Measurable (diffKer y) := by
  unfold diffKer poissonQ
  exact (by fun_prop : Measurable fun x : ℝ => x / (π * (x ^ 2 + y ^ 2))).sub
    (measurable_const.mul (measurable_inv.indicator
      (measurableSet_lt measurable_const continuous_abs.measurable)))

lemma diffKer_neg (y x : ℝ) : diffKer y (-x) = -diffKer y x := by
  unfold diffKer poissonQ
  by_cases h : y < |x|
  · simp only [Set.indicator_of_mem (show -x ∈ {x : ℝ | y < |x|} by simpa using h),
      Set.indicator_of_mem (show x ∈ {x : ℝ | y < |x|} from h), neg_sq, inv_neg]
    ring
  · simp only [Set.indicator_of_notMem (show -x ∉ {x : ℝ | y < |x|} by simpa using h),
      Set.indicator_of_notMem (show x ∉ {x : ℝ | y < |x|} from h), neg_sq]
    ring

lemma abs_diffKer_le {y : ℝ} (hy : 0 < y) (x : ℝ) :
    |diffKer y x| ≤ y / (π * (x ^ 2 + y ^ 2)) ∧
      |x| * |diffKer y x| ≤ y ^ 2 / (π * (x ^ 2 + y ^ 2)) := by
  have hs := sq_add_sq_pos hy x
  have hπ := Real.pi_pos
  have hden : 0 < π * (x ^ 2 + y ^ 2) := mul_pos hπ hs
  unfold diffKer poissonQ
  by_cases h : y < |x|
  · simp only [Set.indicator_of_mem (show x ∈ {x : ℝ | y < |x|} from h)]
    have hx0 : x ≠ 0 := by rintro rfl; simp at h; linarith
    have hxa : 0 < |x| := abs_pos.2 hx0
    have e : x / (π * (x ^ 2 + y ^ 2)) - 1 / π * x⁻¹ = -(y ^ 2) / (π * x * (x ^ 2 + y ^ 2)) := by
      field_simp; ring
    rw [e, abs_div, abs_neg, abs_of_nonneg (sq_nonneg y), abs_mul, abs_mul, abs_of_pos hπ,
      abs_of_pos hs]
    have hden' : 0 < π * |x| * (x ^ 2 + y ^ 2) := mul_pos (mul_pos hπ hxa) hs
    constructor
    · rw [div_le_div_iff₀ hden' hden]
      have : y * |x| ≥ y * y := mul_le_mul_of_nonneg_left h.le hy.le
      nlinarith [mul_pos hπ hs]
    · have e2 : |x| / (π * |x| * (x ^ 2 + y ^ 2)) = 1 / (π * (x ^ 2 + y ^ 2)) := by
        rw [div_eq_div_iff hden'.ne' hden.ne']; ring
      calc |x| * (y ^ 2 / (π * |x| * (x ^ 2 + y ^ 2)))
          = y ^ 2 * (|x| / (π * |x| * (x ^ 2 + y ^ 2))) := by ring
        _ = y ^ 2 / (π * (x ^ 2 + y ^ 2)) := by rw [e2]; ring
        _ ≤ _ := le_rfl
  · simp only [Set.indicator_of_notMem (show x ∉ {x : ℝ | y < |x|} from h), mul_zero, sub_zero]
    rw [abs_div, abs_of_pos hden]
    push Not at h
    constructor
    · exact div_le_div_of_nonneg_right h hden.le
    · rw [← mul_div_assoc]
      refine div_le_div_of_nonneg_right ?_ hden.le
      nlinarith [abs_nonneg x]

lemma integrable_inv_sq_add_sq {y : ℝ} (hy : 0 < y) :
    Integrable (fun x : ℝ => (1 + (x / y) ^ 2)⁻¹) :=
  integrable_inv_one_add_sq.comp_div hy.ne'

lemma eq_inv_one_add_sq {y : ℝ} (hy : 0 < y) (c x : ℝ) :
    c / (π * (x ^ 2 + y ^ 2)) = c / (π * y ^ 2) * (1 + (x / y) ^ 2)⁻¹ := by
  have := sq_add_sq_pos hy x
  have hπ := Real.pi_pos
  field_simp
  ring

lemma integrable_poisson {y : ℝ} (hy : 0 < y) (c : ℝ) :
    Integrable (fun x : ℝ => c / (π * (x ^ 2 + y ^ 2))) := by
  simp_rw [eq_inv_one_add_sq hy c]
  exact (integrable_inv_sq_add_sq hy).const_mul _

lemma integral_poisson_sq {y : ℝ} (hy : 0 < y) :
    ∫ x : ℝ, y ^ 2 / (π * (x ^ 2 + y ^ 2)) = y := by
  simp_rw [eq_inv_one_add_sq hy (y ^ 2)]
  rw [integral_const_mul, Measure.integral_comp_div (fun x => (1 + x ^ 2)⁻¹) y,
    integral_univ_inv_one_add_sq, abs_of_pos hy, smul_eq_mul, div_mul_eq_mul_div,
    div_eq_iff (mul_pos Real.pi_pos (pow_pos hy 2)).ne']
  ring

lemma integrable_diffKer {y : ℝ} (hy : 0 < y) : Integrable (diffKer y) :=
  (integrable_poisson hy y).mono' (measurable_diffKer y).aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact (abs_diffKer_le hy x).1)

/-! ### `Q_y * g → Hg` for Schwartz `g` -/

lemma schwartz_lipschitz (g : 𝓢(ℝ, ℂ)) : ∃ L : ℝ, 0 ≤ L ∧ ∀ a b : ℝ, ‖g a - g b‖ ≤ L * |a - b| := by
  set d := (SchwartzMap.derivCLM ℝ ℂ g).toBoundedContinuousFunction with hd
  refine ⟨‖d‖, norm_nonneg _, fun a b => ?_⟩
  have hL : LipschitzWith ‖d‖₊ g := lipschitzWith_of_nnnorm_deriv_le g.differentiable
    (fun x => by
      have := d.norm_coe_le_norm x
      rw [hd, SchwartzMap.toBoundedContinuousFunction_apply, SchwartzMap.derivCLM_apply] at this
      rw [← hd] at this
      rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]
      exact this)
  have := hL.dist_le_mul a b
  rwa [dist_eq_norm, Real.dist_eq, coe_nnnorm] at this

lemma truncHilbert_eq_integral (g : ℝ → ℂ) (y t : ℝ) :
    truncHilbert y g t = ((1 / π : ℝ) : ℂ) * ∫ x, g (t - x) * PlemeljPrivalov.pvKer y x := by
  rw [PlemeljPrivalov.truncHilbert_eq_integral_shift t t y, Complex.real_smul]
  simp only [sub_self, add_zero]

lemma poissonQ_sub_pvKer (y x : ℝ) :
    ((poissonQ y x : ℝ) : ℂ) - ((1 / π : ℝ) : ℂ) * PlemeljPrivalov.pvKer y x =
      ((diffKer y x : ℝ) : ℂ) := by
  unfold diffKer PlemeljPrivalov.pvKer
  by_cases h : y < |x|
  · rw [Set.indicator_of_mem (show x ∈ {x : ℝ | y < |x|} from h),
      Set.indicator_of_mem (show x ∈ {x : ℝ | y < |x|} from h)]
    push_cast; ring
  · rw [Set.indicator_of_notMem (show x ∉ {x : ℝ | y < |x|} from h),
      Set.indicator_of_notMem (show x ∉ {x : ℝ | y < |x|} from h)]
    push_cast; ring

/-- The conjugate Poisson integral `(Q_y * g)(t)`. -/
def qInt (g : ℝ → ℂ) (y t : ℝ) : ℂ := ∫ u, g u * ((poissonQ y (t - u) : ℝ) : ℂ)

lemma abs_poissonQ_le {y : ℝ} (hy : 0 < y) (x : ℝ) : |poissonQ y x| ≤ 1 / (2 * π * y) := by
  unfold poissonQ
  have hs := sq_add_sq_pos hy x
  have hπ := Real.pi_pos
  rw [abs_div, abs_of_pos (mul_pos hπ hs), div_le_div_iff₀ (mul_pos hπ hs) (by positivity)]
  nlinarith [sq_nonneg (|x| - y), sq_abs x, abs_nonneg x]

lemma norm_qInt_sub_truncHilbert_le (g : 𝓢(ℝ, ℂ)) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ a b : ℝ, ‖g a - g b‖ ≤ L * |a - b|) {y : ℝ} (hy : 0 < y) (t : ℝ) :
    ‖qInt g y t - truncHilbert y g t‖ ≤ L * y := by
  have hgi : Integrable (fun x => g (t - x)) := (g.integrable).comp_sub_left t
  have hQ : Integrable (fun x => g (t - x) * ((poissonQ y x : ℝ) : ℂ)) :=
    hgi.mul_bdd (Complex.continuous_ofReal.measurable.comp
      (by unfold poissonQ; fun_prop : Measurable fun x => poissonQ y x)).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_poissonQ_le hy x)
  have hK := PlemeljPrivalov.integrable_mul_pvKer (g.memLp 2) hy t
  have hD : Integrable fun x => ((diffKer y x : ℝ) : ℂ) := (integrable_diffKer hy).ofReal
  have e1 : qInt g y t = ∫ x, g (t - x) * ((poissonQ y x : ℝ) : ℂ) := by
    unfold qInt
    rw [← integral_sub_left_eq_self _ (μ := volume) t]
    simp only [sub_sub_cancel]
  have e2 : qInt g y t - truncHilbert y g t =
      ∫ x, (g (t - x) - g t) * ((diffKer y x : ℝ) : ℂ) := by
    rw [e1, truncHilbert_eq_integral, ← integral_const_mul, ← integral_sub hQ (hK.const_mul _)]
    have h0 : ∫ x, g t * ((diffKer y x : ℝ) : ℂ) = 0 := by
      rw [integral_const_mul]
      have : ∫ x, ((diffKer y x : ℝ) : ℂ) = 0 :=
        PlemeljPrivalov.integral_eq_zero_of_odd fun x => by rw [diffKer_neg]; push_cast; ring
      rw [this, mul_zero]
    have hfun : (fun x => (g (t - x) - g t) * ((diffKer y x : ℝ) : ℂ)) =
        fun x => g (t - x) * ((diffKer y x : ℝ) : ℂ) - g t * ((diffKer y x : ℝ) : ℂ) := by
      funext x; ring
    have hi1 : Integrable fun x => g (t - x) * ((diffKer y x : ℝ) : ℂ) := by
      have := hQ.sub (hK.const_mul ((1 / π : ℝ) : ℂ))
      refine this.congr (Eventually.of_forall fun x => ?_)
      simp only [Pi.sub_apply]
      rw [← poissonQ_sub_pvKer]; ring
    rw [hfun, integral_sub hi1 (hD.const_mul _), h0, sub_zero]
    congr 1; funext x
    rw [← poissonQ_sub_pvKer]; ring
  rw [e2]
  have hbound : ∀ x, ‖(g (t - x) - g t) * ((diffKer y x : ℝ) : ℂ)‖ ≤
      L * (y ^ 2 / (π * (x ^ 2 + y ^ 2))) := by
    intro x
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 := hL (t - x) t
    rw [show t - x - t = -x by ring, abs_neg] at h1
    have h2 := (abs_diffKer_le hy x).2
    calc ‖g (t - x) - g t‖ * |diffKer y x| ≤ L * |x| * |diffKer y x| :=
          mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ = L * (|x| * |diffKer y x|) := by ring
      _ ≤ L * (y ^ 2 / (π * (x ^ 2 + y ^ 2))) := mul_le_mul_of_nonneg_left h2 hL0
  refine (norm_integral_le_of_norm_le ((integrable_poisson hy (y ^ 2)).const_mul L)
    (Eventually.of_forall hbound)).trans_eq ?_
  rw [integral_const_mul, integral_poisson_sq hy]

lemma tendsto_qInt (g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    Tendsto (fun y => qInt g y t) (𝓝[>] 0) (𝓝 (hilbertR g t)) := by
  obtain ⟨L, hL0, hL⟩ := schwartz_lipschitz g
  have hC : ∀ a, |a - t| ≤ 1 → ‖g a - g t‖ ≤ L * |a - t| ^ (1 / 2 : ℝ) := fun a ha =>
    (hL a t).trans (mul_le_mul_of_nonneg_left
      (Real.self_le_rpow_of_le_one (abs_nonneg _) ha (by norm_num)) hL0)
  have htr := tendsto_truncHilbert (g.memLp 2) (by norm_num : (0 : ℝ) < 1 / 2) hC
  refine htr.congr_dist ?_
  have hlim : Tendsto (fun y : ℝ => L * y) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun y : ℝ => L * y) (𝓝 0) (𝓝 (L * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine squeeze_zero' (Eventually.of_forall fun y => dist_nonneg) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with y hy
  rw [dist_comm, dist_eq_norm]
  exact norm_qInt_sub_truncHilbert_le g hL0 hL hy t

/-! ### The Fourier side -/

/-- `h = -i sgn(ξ) ĝ(ξ)`. -/
def hFun (g : 𝓢(ℝ, ℂ)) (ξ : ℝ) : ℂ := symb ξ * 𝓕 (g : ℝ → ℂ) ξ

/-- `F(t) = ∫ h(ξ) e^{2π i ξ t} dξ`. -/
def fFun (g : 𝓢(ℝ, ℂ)) (t : ℝ) : ℂ := ∫ ξ, cexp (((2 * π * ξ * t : ℝ) : ℂ) * I) * hFun g ξ

lemma integrable_hFun (g : 𝓢(ℝ, ℂ)) : Integrable (hFun g) := by
  have hi : Integrable (𝓕 (g : ℝ → ℂ)) := (𝓕 g).integrable
  refine hi.norm.mono' ?_ (Eventually.of_forall fun ξ => ?_)
  · exact measurable_symb.aestronglyMeasurable.mul hi.aestronglyMeasurable
  · rw [hFun, norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (norm_symb_le ξ)

lemma measurable_hFun (g : 𝓢(ℝ, ℂ)) : Measurable (hFun g) :=
  measurable_symb.mul (𝓕 g).continuous.measurable

lemma norm_cexp_mul_I (r : ℝ) : ‖cexp ((r : ℂ) * I)‖ = 1 := Complex.norm_exp_ofReal_mul_I r

lemma continuous_fFun (g : 𝓢(ℝ, ℂ)) : Continuous (fFun g) := by
  refine continuous_of_dominated (bound := fun ξ => ‖hFun g ξ‖) (fun t => ?_)
    (fun t => Eventually.of_forall fun ξ => ?_) (integrable_hFun g).norm
    (Eventually.of_forall fun ξ => by fun_prop)
  · exact ((by fun_prop : Continuous fun ξ : ℝ => cexp (((2 * π * ξ * t : ℝ) : ℂ) * I)).aestronglyMeasurable).mul
      (integrable_hFun g).aestronglyMeasurable
  · rw [norm_mul, norm_cexp_mul_I, one_mul]

lemma tendsto_damped (g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    Tendsto (fun y : ℝ => ∫ ξ, ((rexp (-(2 * π * y) * |ξ|) : ℝ) : ℂ) *
      (cexp (((2 * π * ξ * t : ℝ) : ℂ) * I) * hFun g ξ)) (𝓝[>] 0) (𝓝 (fFun g t)) := by
  unfold fFun
  refine tendsto_integral_filter_of_dominated_convergence (fun ξ => ‖hFun g ξ‖) ?_ ?_
    (integrable_hFun g).norm ?_
  · exact Eventually.of_forall fun y =>
      ((by fun_prop : Continuous fun ξ : ℝ => ((rexp (-(2 * π * y) * |ξ|) : ℝ) : ℂ)).aestronglyMeasurable).mul
        (((by fun_prop : Continuous fun ξ : ℝ => cexp (((2 * π * ξ * t : ℝ) : ℂ) * I)).aestronglyMeasurable).mul
          (integrable_hFun g).aestronglyMeasurable)
  · filter_upwards [self_mem_nhdsWithin] with y hy
    refine Eventually.of_forall fun ξ => ?_
    have hy' : 0 < y := hy
    rw [norm_mul, norm_mul, norm_cexp_mul_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    refine mul_le_of_le_one_left (norm_nonneg _) (Real.exp_le_one_iff.2 ?_)
    have : 0 ≤ 2 * π * y * |ξ| := by positivity
    linarith
  · refine Eventually.of_forall fun ξ => ?_
    have hc : Continuous fun y : ℝ => ((rexp (-(2 * π * y) * |ξ|) : ℝ) : ℂ) *
        (cexp (((2 * π * ξ * t : ℝ) : ℂ) * I) * hFun g ξ) := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
    simpa using this

/-- Fubini: the damped Fourier integral is the conjugate Poisson integral. -/
lemma damped_eq_qInt (g : 𝓢(ℝ, ℂ)) {y : ℝ} (hy : 0 < y) (t : ℝ) :
    ∫ ξ, ((rexp (-(2 * π * y) * |ξ|) : ℝ) : ℂ) *
      (cexp (((2 * π * ξ * t : ℝ) : ℂ) * I) * hFun g ξ) = qInt g y t := by
  have hb : 0 < 2 * π * y := by positivity
  set A : ℝ → ℂ := fun ξ => symb ξ * ((rexp (-(2 * π * y) * |ξ|) : ℝ) : ℂ) with hA
  set G : ℝ × ℝ → ℂ := fun p => A p.1 * cexp (((2 * π * p.1 * (t - p.2) : ℝ) : ℂ) * I) * g p.2
    with hG
  have hAm : Measurable A := measurable_symb.mul (by fun_prop)
  have hexp : Integrable (fun ξ : ℝ => rexp (-(2 * π * y) * |ξ|)) :=
    PlemeljPrivalov.integrable_comp_abs' (f := fun r => rexp (-(2 * π * y) * r))
      (exp_neg_integrableOn_Ioi 0 hb)
  have hGi : Integrable G (volume.prod volume) := by
    refine Integrable.mono' (hexp.mul_prod g.integrable.norm) ?_ (Eventually.of_forall fun p => ?_)
    · exact ((hAm.comp measurable_fst).mul (by fun_prop)).mul
        (g.continuous.measurable.comp measurable_snd) |>.aestronglyMeasurable
    · rw [hG, hA]
      simp only
      rw [norm_mul, norm_mul, norm_mul, norm_cexp_mul_I, mul_one, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_of_le_one_left (Real.exp_pos _).le (norm_symb_le _)) (norm_nonneg _)
  -- rewrite the left side as an iterated integral of `G`
  have hL : ∀ ξ, ((rexp (-(2 * π * y) * |ξ|) : ℝ) : ℂ) *
      (cexp (((2 * π * ξ * t : ℝ) : ℂ) * I) * hFun g ξ) = ∫ u, G (ξ, u) := by
    intro ξ
    rw [hFun, fourier_real_eq_integral_exp_smul, ← integral_const_mul, ← integral_const_mul,
      ← integral_const_mul]
    congr 1; funext u
    rw [hG, hA]
    simp only [smul_eq_mul]
    have : cexp (((2 * π * ξ * (t - u) : ℝ) : ℂ) * I) =
        cexp (((2 * π * ξ * t : ℝ) : ℂ) * I) * cexp (((-2 * π * u * ξ : ℝ) : ℂ) * I) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    rw [this]; ring
  simp_rw [hL]
  rw [integral_integral_swap (f := fun ξ u => G (ξ, u)) hGi]
  unfold qInt
  congr 1; funext u
  rw [hG, hA]
  simp only
  rw [integral_mul_const, ← kernel_eq hy (t - u)]
  ring

lemma fFun_eq_hilbertR (g : 𝓢(ℝ, ℂ)) (t : ℝ) : fFun g t = hilbertR g t := by
  have h1 := tendsto_damped g t
  have h2 : Tendsto (fun y : ℝ => ∫ ξ, ((rexp (-(2 * π * y) * |ξ|) : ℝ) : ℂ) *
      (cexp (((2 * π * ξ * t : ℝ) : ℂ) * I) * hFun g ξ)) (𝓝[>] 0) (𝓝 (hilbertR g t)) := by
    refine (tendsto_qInt g t).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (damped_eq_qInt g hy t).symm
  exact tendsto_nhds_unique h1 h2

/-! ### `U g = F` almost everywhere -/

lemma pairing_fFun (g φ : 𝓢(ℝ, ℂ)) :
    ∫ t, conj (fFun g t) * φ t = ∫ ξ, conj (hFun g ξ) * 𝓕 (φ : ℝ → ℂ) ξ := by
  set G : ℝ × ℝ → ℂ := fun p =>
    conj (cexp (((2 * π * p.2 * p.1 : ℝ) : ℂ) * I)) * conj (hFun g p.2) * φ p.1 with hG
  have hGi : Integrable G (volume.prod volume) := by
    refine Integrable.mono' (φ.integrable.norm.mul_prod (integrable_hFun g).norm) ?_
      (Eventually.of_forall fun p => ?_)
    · exact (((by fun_prop : Continuous fun p : ℝ × ℝ =>
        conj (cexp (((2 * π * p.2 * p.1 : ℝ) : ℂ) * I))).measurable.mul
        (Complex.continuous_conj.measurable.comp ((measurable_hFun g).comp measurable_snd))).mul
        (φ.continuous.measurable.comp measurable_fst)).aestronglyMeasurable
    · rw [hG]
      simp only
      rw [norm_mul, norm_mul, Complex.norm_conj, norm_cexp_mul_I, one_mul, Complex.norm_conj,
        mul_comm]
  have hL : ∀ t, conj (fFun g t) * φ t = ∫ ξ, G (t, ξ) := by
    intro t
    rw [fFun, ← integral_conj, ← integral_mul_const]
    congr 1; funext ξ
    rw [hG]; simp only [map_mul]
  have hR : ∀ ξ, conj (hFun g ξ) * 𝓕 (φ : ℝ → ℂ) ξ = ∫ t, G (t, ξ) := by
    intro ξ
    rw [fourier_real_eq_integral_exp_smul, ← integral_const_mul]
    congr 1; funext t
    rw [hG]
    simp only [smul_eq_mul]
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    have : ((2 * π * ξ * t : ℝ) : ℂ) * -I = ((-2 * π * t * ξ : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [this]; ring
  simp_rw [hL, hR]
  exact integral_integral_swap hGi

lemma pairing_hilbertL2 (g φ : 𝓢(ℝ, ℂ)) :
    ∫ t, conj (hilbertL2 (g.toLp 2) t) * φ t = ∫ ξ, conj (hFun g ξ) * 𝓕 (φ : ℝ → ℂ) ξ := by
  have h1 : ⟪hilbertL2 (g.toLp 2), φ.toLp 2⟫_ℂ = ∫ t, conj (hilbertL2 (g.toLp 2) t) * φ t := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [φ.coeFn_toLp 2] with t ht
    rw [RCLike.inner_apply', ht]
  have h2 : ⟪hilbertL2 (g.toLp 2), φ.toLp 2⟫_ℂ =
      ⟪mulSymb ((𝓕 g).toLp 2), (𝓕 φ).toLp 2⟫_ℂ := by
    rw [← Lp.inner_fourier_eq]
    have e1 : 𝓕 (hilbertL2 (g.toLp 2)) = mulSymb ((𝓕 g).toLp 2) := by
      rw [← fourierL2_schwartz]; exact fourier_hilbertL2 _
    rw [e1, fourierL2_schwartz]
  have h3 : ⟪mulSymb ((𝓕 g).toLp 2), (𝓕 φ).toLp 2⟫_ℂ =
      ∫ ξ, conj (hFun g ξ) * 𝓕 (φ : ℝ → ℂ) ξ := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [coeFn_mulSymb ((𝓕 g).toLp 2), (𝓕 g).coeFn_toLp 2, (𝓕 φ).coeFn_toLp 2]
      with ξ h1 h2 h3
    rw [RCLike.inner_apply', h1, h2, h3, hFun]
    rfl
  rw [← h1, h2, h3]

lemma hilbertL2_ae_eq_fFun (g : 𝓢(ℝ, ℂ)) :
    (hilbertL2 (g.toLp 2) : ℝ → ℂ) =ᵐ[volume] fFun g := by
  have hloc : LocallyIntegrable (fun t => hilbertL2 (g.toLp 2) t - fFun g t) :=
    ((Lp.memLp (hilbertL2 (g.toLp 2))).locallyIntegrable (by norm_num)).sub
      (continuous_fFun g).locallyIntegrable
  suffices H : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ∫ x, ψ x • (hilbertL2 (g.toLp 2) x - fFun g x) = 0 by
    filter_upwards [ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc H] with t ht
    exact sub_eq_zero.1 ht
  intro ψ hψ hψc
  -- the test function as a Schwartz function
  have hcs : HasCompactSupport (fun x => ((ψ x : ℝ) : ℂ)) :=
    hψc.comp_left Complex.ofReal_zero
  have hsm : ContDiff ℝ ∞ (fun x => ((ψ x : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hψ
  set φ : 𝓢(ℝ, ℂ) := hcs.toSchwartzMap hsm with hφ
  have hφx : ∀ x, φ x = ((ψ x : ℝ) : ℂ) := fun x => rfl
  have hp := (pairing_hilbertL2 g φ).trans (pairing_fFun g φ).symm
  simp_rw [hφx] at hp
  have e : ∀ (z : ℂ) (t : ℝ), ((ψ t : ℝ) : ℂ) * z = conj (conj z * ((ψ t : ℝ) : ℂ)) :=
    fun z t => by rw [map_mul, Complex.conj_conj, Complex.conj_ofReal, mul_comm]
  have hp' : ∫ t, ((ψ t : ℝ) : ℂ) * hilbertL2 (g.toLp 2) t =
      ∫ t, ((ψ t : ℝ) : ℂ) * fFun g t := by
    calc ∫ t, ((ψ t : ℝ) : ℂ) * hilbertL2 (g.toLp 2) t
        = ∫ t, conj (conj (hilbertL2 (g.toLp 2) t) * ((ψ t : ℝ) : ℂ)) :=
          integral_congr_ae (Eventually.of_forall fun t => e _ t)
      _ = conj (∫ t, conj (hilbertL2 (g.toLp 2) t) * ((ψ t : ℝ) : ℂ)) := integral_conj
      _ = conj (∫ t, conj (fFun g t) * ((ψ t : ℝ) : ℂ)) := by rw [hp]
      _ = ∫ t, conj (conj (fFun g t) * ((ψ t : ℝ) : ℂ)) := integral_conj.symm
      _ = ∫ t, ((ψ t : ℝ) : ℂ) * fFun g t :=
          integral_congr_ae (Eventually.of_forall fun t => (e _ t).symm)
  have hi1 : Integrable fun t => ((ψ t : ℝ) : ℂ) * hilbertL2 (g.toLp 2) t := by
    refine (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) (φ.toLp 2)
      (hilbertL2 (g.toLp 2))).congr ?_
    filter_upwards [φ.coeFn_toLp 2] with t ht
    rw [RCLike.inner_apply', ht, hφx, Complex.conj_ofReal]
  have hi2 : Integrable fun t => ((ψ t : ℝ) : ℂ) * fFun g t :=
    ((Complex.continuous_ofReal.comp hψ.continuous).mul
      (continuous_fFun g)).integrable_of_hasCompactSupport hcs.mul_right
  simp_rw [Complex.real_smul, mul_sub]
  rw [integral_sub hi1 hi2, hp', sub_self]

end HilbertL2

open HilbertL2 in
/-- **Proposition A.1.5**. -/
theorem hilbertL2Statement_holds : HilbertL2Statement := by
  refine ⟨hilbertL2, fun g => ?_, hilbertL2_hilbertL2, fun f => ?_⟩
  · filter_upwards [hilbertL2_ae_eq_fFun g] with t ht
    rw [ht, fFun_eq_hilbertR]
  · have e : 𝓕 (hilbertL2 f) = mulSymb (𝓕 f) := fourier_hilbertL2 f
    filter_upwards [coeFn_mulSymb (𝓕 f)] with ξ h
    rw [e, h, symb]

end DF
