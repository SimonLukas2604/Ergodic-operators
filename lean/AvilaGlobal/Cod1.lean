import AvilaGlobal.Codimension
import AvilaGlobal.DerivFormula

/-!
# Theorem `cod1` (Avila, *Global theory I*, §4)

For irrational `α`, `δ > 0`, `j > 0` and `v_* ∈ C^ω_δ(ℝ/ℤ, ℝ)` with `ω(α, A^{(v_*)}) = j`, the map
`v ↦ L_{δ,j}(α, A^{(v)})` is real-analytic near `v_*` with nonvanishing derivative at `v_*`.
-/

noncomputable section

open scoped Matrix.Norms.Operator ComplexConjugate NNReal
open Matrix Filter Topology Complex Set

namespace AvilaGlobal

open AMO

/-! ### Diagonal cocycles -/

lemma norm_diagonal_inv {P : ℂ} (_hP : P ≠ 0) :
    ‖(diagonal ![P, P⁻¹] : M2)‖ = max ‖P‖ ‖P‖⁻¹ := by
  rw [linfty_opNorm_diagonal]
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (le_max_of_le_left (norm_nonneg _))).2 fun i => ?_
    fin_cases i
    · simp
    · simp
  · apply max_le
    · have := norm_le_pi_norm (![P, P⁻¹]) 0
      simpa using this
    · have := norm_le_pi_norm (![P, P⁻¹]) 1
      simpa using this

lemma log_max_inv {a : ℝ} (ha : 0 < a) : Real.log (max a a⁻¹) = |Real.log a| := by
  rcases le_total a a⁻¹ with h | h
  · rw [max_eq_right h, Real.log_inv]
    have : Real.log a ≤ 0 := by
      by_contra hc
      push Not at hc
      have h1 : 1 < a := by
        by_contra h2; push Not at h2
        have := Real.log_nonpos ha.le h2; linarith
      have : a⁻¹ < 1 := inv_lt_one_of_one_lt₀ h1
      linarith
    rw [abs_of_nonpos this]
  · rw [max_eq_left h]
    have : 0 ≤ Real.log a := by
      by_contra hc
      push Not at hc
      have h1 : a < 1 := by
        by_contra h2; push Not at h2
        have := Real.log_nonneg h2; linarith
      have : 1 < a⁻¹ := (one_lt_inv₀ ha).2 h1
      linarith
    rw [abs_of_nonneg this]

lemma iter_diagonal_inv (α : ℝ) (μ : ℝ → ℂ) (n : ℕ) (x : ℝ) :
    iter α (fun y => (diagonal ![μ y, (μ y)⁻¹] : M2)) n x =
      diagonal ![∏ k ∈ Finset.range n, μ (x + k * α),
        (∏ k ∈ Finset.range n, μ (x + k * α))⁻¹] := by
  induction n with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp [iter]
  | succ n ih =>
    simp only [iter, ih, diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i
    · simp [Finset.prod_range_succ, mul_comm]
    · simp [Finset.prod_range_succ, mul_comm]

/-- Lyapunov exponent of a diagonal cocycle `diag(μ, μ⁻¹)`. -/
theorem lyapunov_diagonal {α : ℝ} (hα : Irrational α) {μ : ℝ → ℂ} (hc : Continuous μ)
    (hp : Function.Periodic μ 1) (h0 : ∀ x, μ x ≠ 0) :
    lyapunov α (fun x => (diagonal ![μ x, (μ x)⁻¹] : M2)) =
      |∫ x in (0 : ℝ)..1, Real.log ‖μ x‖| := by
  set A : ℝ → M2 := fun x => diagonal ![μ x, (μ x)⁻¹] with hA
  have hS : IsSLCocycle A := by
    refine ⟨?_, ?_, ?_⟩
    · refine continuous_matrix fun i j => ?_
      fin_cases i <;> fin_cases j <;> simp [hA, Matrix.diagonal] <;>
        first | exact continuous_const | exact hc | exact hc.inv₀ h0
    · intro x; simp only [hA, hp x]
    · intro x; simp [hA, det_diagonal, Fin.prod_univ_two, h0 x]
  set g : ℝ → ℝ := fun x => Real.log ‖μ x‖ with hg
  have hgc : Continuous g := (hc.norm).log (fun x => norm_ne_zero_iff.2 (h0 x))
  have hgp : Function.Periodic g 1 := fun x => by simp only [hg, hp x]
  have hlog : ∀ n x, Real.log ‖iter α A n x‖ = |∑ k ∈ Finset.range n, g (x + k * α)| := by
    intro n x
    have hP : ∏ k ∈ Finset.range n, μ (x + k * α) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun k _ => h0 _
    rw [hA, iter_diagonal_inv, norm_diagonal_inv hP, log_max_inv (norm_pos_iff.2 hP),
      norm_prod, Real.log_prod (fun k _ => norm_ne_zero_iff.2 (h0 _))]
  have hseq : ∀ n : ℕ, 0 < n → lyapSeq α A n / n =
      ∫ x in (0 : ℝ)..1, |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, g (x + k * α)| := by
    intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [lyapSeq, hlog]
    rw [div_eq_inv_mul, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [abs_mul, abs_of_pos (inv_pos.2 hn')]
  have hlim : Tendsto (fun n : ℕ => lyapSeq α A n / n) atTop
      (𝓝 |∫ x in (0 : ℝ)..1, g x|) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨n₀, hn₀⟩ := weyl_uniform_real hα hgc hgp (half_pos hε)
    refine ⟨max n₀ 1, fun n hn => ?_⟩
    have hn1 : 0 < n := lt_of_lt_of_le one_pos (le_of_max_le_right hn)
    rw [hseq n hn1, Real.dist_eq]
    have hcont : Continuous fun x : ℝ =>
        |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, g (x + k * α)| := by
      refine (continuous_const.mul (continuous_finsetSum _ fun k _ => ?_)).abs
      exact hgc.comp (continuous_id.add continuous_const)
    have e : (∫ x in (0 : ℝ)..1, |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, g (x + k * α)|) -
        |∫ x in (0 : ℝ)..1, g x| = ∫ x in (0 : ℝ)..1,
          (|(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, g (x + k * α)| - |∫ y in (0 : ℝ)..1, g y|) := by
      rw [intervalIntegral.integral_sub (hcont.intervalIntegrable _ _)
        intervalIntegrable_const]
      simp
    rw [e]
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (C := ε / 2)
      (f := fun x => |(n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, g (x + k * α)| -
        |∫ y in (0 : ℝ)..1, g y|) (fun x _ => by
          rw [Real.norm_eq_abs]
          exact (abs_abs_sub_abs_le_abs_sub _ _).trans (hn₀ n (le_of_max_le_left hn) x))
    rw [Real.norm_eq_abs] at hb
    simp only [sub_zero, abs_one, mul_one] at hb
    linarith
  exact tendsto_nhds_unique hS.tendsto_lyapunov hlim

/-! ### Exponential of a nilpotent matrix -/

lemma exp_of_sq_eq_zero {w : M2} (hw : w * w = 0) : NormedSpace.exp w = 1 + w := by
  rw [NormedSpace.exp_eq_tsum ℂ]
  beta_reduce
  have hpow : ∀ n, 2 ≤ n → w ^ n = 0 := by
    intro n hn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [pow_add, sq, hw, zero_mul]
  rw [tsum_eq_sum (s := Finset.range 2)]
  · simp [Finset.sum_range_succ]
  · intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    rw [hpow n hn, smul_zero]

lemma exp_lower (t : ℝ) (c : ℂ) :
    NormedSpace.exp ((t : ℂ) • (!![0, 0; c, 0] : M2)) = !![1, 0; t * c, 1] := by
  rw [exp_of_sq_eq_zero]
  · ext i j; fin_cases i <;> fin_cases j <;> simp
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-! ### A diagonalizing frame for a uniformly hyperbolic cocycle -/

theorem exists_frame_of_isUH {α : ℝ} {A : ℝ → M2} (h : IsUH α A) :
    ∃ B : ℝ → M2, Continuous B ∧ Function.Periodic B 1 ∧ (∀ x, (B x).det = 1) ∧
      (∀ x, ((B (x + α))⁻¹ * A x * B x) 0 1 = 0 ∧ ((B (x + α))⁻¹ * A x * B x) 1 0 = 0) ∧
      (∃ n : ℕ, 1 ≤ n ∧ ∀ x, ‖B x *ᵥ ![1, 0]‖ < ‖iter α A n x *ᵥ (B x *ᵥ ![1, 0])‖) := by
  obtain ⟨u, s, huc, hsc, hup, hsp, hu0, hs0, hui, hsi, n, hn, hexp⟩ := h
  set d : ℝ → ℂ := fun x => u x 0 * s x 1 - u x 1 * s x 0 with hd
  have hd0 : ∀ x, d x ≠ 0 := by
    intro x hdx
    have hpar : ∃ c : ℂ, s x = c • u x := by
      by_cases h0 : u x 0 = 0
      · have h1 : u x 1 ≠ 0 := by
          intro h1; apply hu0 x; ext i; fin_cases i <;> simp [h0, h1]
        have hs0' : s x 0 = 0 := by
          have : u x 1 * s x 0 = 0 := by simp only [hd, h0, zero_mul, zero_sub] at hdx; simpa using hdx
          exact (mul_eq_zero.1 this).resolve_left h1
        refine ⟨s x 1 / u x 1, ?_⟩
        ext i; fin_cases i
        · simp [h0, hs0']
        · simp [div_mul_cancel₀ _ h1]
      · refine ⟨s x 0 / u x 0, ?_⟩
        ext i; fin_cases i
        · simp [div_mul_cancel₀ _ h0]
        · show s x 1 = s x 0 / u x 0 * u x 1
          have : u x 0 * s x 1 - u x 1 * s x 0 = 0 := hdx
          field_simp
          linear_combination this
    obtain ⟨c, hc⟩ := hpar
    have hc0 : c ≠ 0 := by rintro rfl; apply hs0 x; rw [hc, zero_smul]
    obtain ⟨h1, h2⟩ := hexp x
    rw [hc, Matrix.mulVec_smul, norm_smul, norm_smul] at h1
    have := (mul_lt_mul_iff_right₀ (norm_pos_iff.2 hc0)).1 h1
    linarith
  set B : ℝ → M2 := fun x => !![u x 0, s x 0 / d x; u x 1, s x 1 / d x] with hB
  have hcol : ∀ x, B x *ᵥ ![1, 0] = u x := by
    intro x; ext i; fin_cases i <;> simp [hB, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hdc : Continuous d := by
    simp only [hd]
    have h0 : Continuous fun x => u x 0 := (continuous_apply 0).comp huc
    have h1 : Continuous fun x => u x 1 := (continuous_apply 1).comp huc
    have h2 : Continuous fun x => s x 0 := (continuous_apply 0).comp hsc
    have h3 : Continuous fun x => s x 1 := (continuous_apply 1).comp hsc
    fun_prop
  have hdet : ∀ x, (B x).det = 1 := by
    intro x
    simp only [hB, det_fin_two_of]
    field_simp [hd0 x]
    simp only [hd]; ring
  refine ⟨B, ?_, ?_, hdet, ?_, ⟨n, hn, fun x => ?_⟩⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [hB]
    · exact (continuous_apply 0).comp huc
    · exact ((continuous_apply 0).comp hsc).div hdc hd0
    · exact (continuous_apply 1).comp huc
    · exact ((continuous_apply 1).comp hsc).div hdc hd0
  · intro x
    have hdp : d (x + 1) = d x := by simp only [hd, hup x, hsp x]
    simp only [hB, hup x, hsp x, hdp]
  · intro x
    obtain ⟨c, hc⟩ := hui x
    obtain ⟨c', hc'⟩ := hsi x
    set D : M2 := !![c, 0; 0, c' * d (x + α) / d x] with hD
    have hAB : A x * B x = B (x + α) * D := by
      have e0 := congrFun hc 0
      have e1 := congrFun hc 1
      have f0 := congrFun hc' 0
      have f1 := congrFun hc' 1
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
        at e0 e1 f0 f1
      ext i j; fin_cases i <;> fin_cases j <;>
        simp [hB, hD, Matrix.mul_apply, Fin.sum_univ_two]
      · linear_combination e0
      · field_simp [hd0 x, hd0 (x + α)]; linear_combination f0
      · linear_combination e1
      · field_simp [hd0 x, hd0 (x + α)]; linear_combination f1
    have hu : IsUnit (B (x + α)).det := by rw [hdet]; exact isUnit_one
    have : (B (x + α))⁻¹ * A x * B x = D := by
      rw [Matrix.mul_assoc, hAB, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    rw [this]; simp [hD]
  · rw [hcol]; exact (hexp x).2

/-! ### Fourier series of holomorphic periodic functions -/

lemma iInt_re {f : ℝ → ℂ} (hf : IntervalIntegrable f MeasureTheory.volume 0 1) :
    ∫ x in (0 : ℝ)..1, (f x).re = (∫ x in (0 : ℝ)..1, f x).re :=
  Complex.reCLM.intervalIntegral_comp_comm hf

lemma iInt_conj (f : ℝ → ℂ) :
    ∫ x in (0 : ℝ)..1, conj (f x) = conj (∫ x in (0 : ℝ)..1, f x) :=
  Complex.conjLIE.toLinearIsometry.intervalIntegral_comp_comm f

lemma conj_eC_real (r : ℝ) : conj (eC r) = eC (-r) := by
  unfold eC
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal, map_ofNat]

lemma conj_eC_mul (m : ℤ) (x : ℝ) : conj (eC (m * x)) = eC (((-m : ℤ) : ℂ) * x) := by
  rw [show ((m : ℂ) * x) = ((m * x : ℝ) : ℂ) by push_cast; ring, conj_eC_real]
  push_cast; ring_nf

lemma norm_eC_mul (m : ℤ) (z : ℂ) :
    ‖eC (m * z)‖ = Real.exp (-2 * Real.pi * m * z.im) := by
  rw [norm_eC]; congr 1; simp; ring

/-- The Fourier series `∑ C_m e(mz)`. -/
def fser (C : ℤ → ℂ) (z : ℂ) : ℂ := ∑' m : ℤ, C m * eC (m * z)

lemma fser_term_le {C : ℤ → ℂ} {M y₁ : ℝ}
    (hC : ∀ m : ℤ, ‖C m‖ ≤ M * Real.exp (-2 * Real.pi * |(m : ℝ)| * y₁)) (m : ℤ) (z : ℂ) :
    ‖C m * eC (m * z)‖ ≤ M * Real.exp (-(2 * Real.pi * (y₁ - |z.im|)) * |(m : ℝ)|) := by
  have hM : 0 ≤ M := by
    have := hC 0; simp at this; linarith [norm_nonneg (C 0)]
  rw [norm_mul, norm_eC_mul]
  calc ‖C m‖ * Real.exp (-2 * Real.pi * m * z.im)
      ≤ M * Real.exp (-2 * Real.pi * |(m : ℝ)| * y₁) * Real.exp (-2 * Real.pi * m * z.im) :=
        mul_le_mul_of_nonneg_right (hC m) (Real.exp_pos _).le
    _ = M * Real.exp (-2 * Real.pi * |(m : ℝ)| * y₁ + -2 * Real.pi * m * z.im) := by
        rw [Real.exp_add]; ring
    _ ≤ M * Real.exp (-(2 * Real.pi * (y₁ - |z.im|)) * |(m : ℝ)|) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hM
        have h1 : -((m : ℝ) * z.im) ≤ |(m : ℝ)| * |z.im| := by
          rw [← abs_mul]; exact neg_le_abs _
        nlinarith [Real.pi_pos]

lemma fser_hasSum {C : ℤ → ℂ} {M y₁ : ℝ}
    (hC : ∀ m : ℤ, ‖C m‖ ≤ M * Real.exp (-2 * Real.pi * |(m : ℝ)| * y₁)) {z : ℂ}
    (hz : |z.im| < y₁) : HasSum (fun m : ℤ => C m * eC (m * z)) (fser C z) := by
  have hM : 0 ≤ M := by
    have := hC 0; simp at this; linarith [norm_nonneg (C 0)]
  have ha : 0 < 2 * Real.pi * (y₁ - |z.im|) := by have := Real.pi_pos; nlinarith
  exact (Summable.of_norm_bounded ((summable_exp_neg_abs ha).mul_left M)
    (fun m => fser_term_le hC m z)).hasSum

lemma fser_periodic (C : ℤ → ℂ) (z : ℂ) : fser C (z + 1) = fser C z := by
  unfold fser
  congr 1; funext m
  rw [mul_add, mul_one, eC_add, eC_intCast, mul_one]

lemma fser_differentiableOn {C : ℤ → ℂ} {M y₁ : ℝ}
    (hC : ∀ m : ℤ, ‖C m‖ ≤ M * Real.exp (-2 * Real.pi * |(m : ℝ)| * y₁)) :
    DifferentiableOn ℂ (fser C) (strip y₁) := by
  intro z₀ hz₀
  have hz₀' : |z₀.im| < y₁ := hz₀
  obtain ⟨y₂, h1, h2⟩ := exists_between hz₀'
  have hM : 0 ≤ M := by
    have := hC 0; simp at this; linarith [norm_nonneg (C 0)]
  have ha : 0 < 2 * Real.pi * (y₁ - y₂) := by have := Real.pi_pos; nlinarith
  have hD : DifferentiableOn ℂ (fun w : ℂ => ∑' m : ℤ, C m * eC (m * w)) (strip y₂) := by
    refine differentiableOn_tsum_of_summable_norm ((summable_exp_neg_abs ha).mul_left M)
      (fun m => ?_) (isOpen_strip y₂) (fun m w hw => ?_)
    · exact ((differentiable_eC.comp (differentiable_id.const_mul _)).const_mul _).differentiableOn
    · refine (fser_term_le hC m w).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hM)
      have hw' : |w.im| < y₂ := hw
      have : 0 ≤ Real.pi * (y₂ - |w.im|) * |(m : ℝ)| :=
        mul_nonneg (mul_nonneg Real.pi_pos.le (by linarith)) (abs_nonneg _)
      nlinarith [this]
  exact ((hD z₀ h1).differentiableAt ((isOpen_strip y₂).mem_nhds h1)).differentiableWithinAt

/-- Coefficient symmetry `C_m = -conj C_{-m}` makes the series purely imaginary on `ℝ`. -/
lemma fser_re_zero {C : ℤ → ℂ} {M y₁ : ℝ} (hy₁ : 0 < y₁)
    (hC : ∀ m : ℤ, ‖C m‖ ≤ M * Real.exp (-2 * Real.pi * |(m : ℝ)| * y₁))
    (hsym : ∀ m : ℤ, C m = -conj (C (-m))) (x : ℝ) : (fser C x).re = 0 := by
  have hx : |((x : ℂ)).im| < y₁ := by simpa using hy₁
  have h1 := fser_hasSum hC hx
  have h2 : HasSum (fun m : ℤ => conj (C m * eC (m * x))) (conj (fser C x)) := by
    have := h1.mapL Complex.conjCLE.toContinuousLinearMap
    exact this
  have hterm : ∀ m : ℤ, conj (C m * eC (m * x)) = -(C (-m) * eC (((-m : ℤ) : ℂ) * x)) := by
    intro m
    have hs : C (-m) = -conj (C m) := by rw [hsym (-m), neg_neg]
    rw [map_mul, conj_eC_mul, hs]; ring
  rw [show (fun m : ℤ => conj (C m * eC (m * x))) =
      fun m : ℤ => -(C (-m) * eC (((-m : ℤ) : ℂ) * x)) from funext hterm] at h2
  have h4 : HasSum (fun m : ℤ => -(C m * eC (m * x))) (conj (fser C x)) :=
    (Equiv.neg ℤ).hasSum_iff.mp h2
  have h5 := h1.neg.unique h4
  have h6 := congrArg Complex.re h5
  rw [Complex.neg_re, Complex.conj_re] at h6
  linarith

/-- A continuous `1`-periodic function whose Fourier coefficients along `Im z = y` are `C_m` is the
restriction of the series `∑ C_m e(mz)`. -/
lemma eq_fser {C : ℤ → ℂ} {M y₁ : ℝ}
    (hC : ∀ m : ℤ, ‖C m‖ ≤ M * Real.exp (-2 * Real.pi * |(m : ℝ)| * y₁))
    {f : ℝ → ℂ} (hfc : Continuous f) (hfp : Function.Periodic f 1) {y : ℝ} (hy : |y| < y₁)
    (hcoef : ∀ m : ℤ, ∫ x in (0 : ℝ)..1, f x * eC (-(m * (x + y * I))) = C m) (x : ℝ) :
    f x = fser C (x + y * I) := by
  have hM : 0 ≤ M := by
    have := hC 0; simp at this; linarith [norm_nonneg (C 0)]
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  let F : C(AddCircle (1 : ℝ), ℂ) := ⟨hfp.lift, continuous_coinduced_dom.2 hfc⟩
  have hFt : ∀ t : ℝ, F (t : AddCircle (1 : ℝ)) = f t := fun t => rfl
  have hFc : ∀ n : ℤ, fourierCoeff F n = Real.exp (-2 * Real.pi * n * y) * C n := by
    intro n
    rw [← hcoef n, fourierCoeff_eq_intervalIntegral F n 0, ← intervalIntegral.integral_const_mul]
    simp only [zero_add, div_one, one_smul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [smul_eq_mul, fourier_coe_apply]
    rw [hFt, Complex.ofReal_exp, eC, mul_comm]
    refine exp_mul_helper _ _ _ _ ?_
    push_cast
    linear_combination (2 * (Real.pi : ℂ) * n * y) * I_sq
  have hsum : Summable (fourierCoeff F) := by
    have ha : 0 < 2 * Real.pi * (y₁ - |y|) := by have := Real.pi_pos; nlinarith
    refine Summable.of_norm_bounded ((summable_exp_neg_abs ha).mul_left M) fun n => ?_
    rw [hFc, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (-2 * Real.pi * n * y) * ‖C n‖
        ≤ Real.exp (-2 * Real.pi * n * y) * (M * Real.exp (-2 * Real.pi * |(n : ℝ)| * y₁)) :=
          mul_le_mul_of_nonneg_left (hC n) (Real.exp_pos _).le
      _ = M * Real.exp (-2 * Real.pi * n * y + -2 * Real.pi * |(n : ℝ)| * y₁) := by
          rw [Real.exp_add]; ring
      _ ≤ M * Real.exp (-(2 * Real.pi * (y₁ - |y|)) * |(n : ℝ)|) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hM
          nlinarith [neg_le_abs ((n : ℝ) * y), abs_mul (n : ℝ) y, Real.pi_pos,
            abs_nonneg (n : ℝ)]
  have hS := has_pointwise_sum_fourier_series_of_summable hsum (x : AddCircle (1 : ℝ))
  rw [hFt] at hS
  have hz : |((x : ℂ) + y * I).im| < y₁ := by simpa using hy
  refine hS.unique ?_
  convert fser_hasSum hC hz using 1
  funext n
  symm
  rw [hFc, fourier_coe_apply, smul_eq_mul, Complex.ofReal_exp, eC]
  refine exp_mul_helper' _ _ _ _ ?_
  push_cast
  linear_combination (2 * (Real.pi : ℂ) * n * y) * I_sq

/-- Exponential decay from a one-sided bound plus coefficient symmetry. -/
lemma decay_of_sym {C : ℤ → ℂ} {M y : ℝ}
    (hb : ∀ m : ℤ, ‖C m‖ ≤ M * Real.exp (2 * Real.pi * m * y))
    (hsym : ∀ m : ℤ, C m = -conj (C (-m))) (m : ℤ) :
    ‖C m‖ ≤ M * Real.exp (-2 * Real.pi * |(m : ℝ)| * y) := by
  rcases le_or_gt (m : ℝ) 0 with h | h
  · refine (hb m).trans (le_of_eq ?_)
    rw [abs_of_nonpos h]; congr 2; ring
  · rw [hsym m, norm_neg, Complex.norm_conj]
    refine (hb (-m)).trans (le_of_eq ?_)
    rw [abs_of_pos h]; push_cast; congr 2; ring

/-! ### Joint analyticity from a uniform Taylor expansion -/

lemma analyticAt_of_taylor {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℂ → ℂ} {z₀ : ℂ} {R : ℝ} (hR : 0 < R) (T : ℕ → E →L[ℝ] ℂ)
    (hT : ∀ n v, ‖T n v‖ ≤ R⁻¹ ^ n * ‖v‖)
    (hf : ∀ v (w : ℂ), ‖w‖ < R → HasSum (fun n => w ^ n * T n v) (f v (z₀ + w))) (v₀ : E) :
    AnalyticAt ℝ (fun q : E × ℂ => f q.1 q.2) (v₀, z₀) := by
  have hTn : ∀ n, ‖T n‖ ≤ R⁻¹ ^ n := fun n =>
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) (hT n)
  set p : FormalMultilinearSeries ℂ ℂ (E →L[ℝ] ℂ) := fun n =>
    ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (T n) with hp
  set R' : NNReal := ⟨R, hR.le⟩
  have hrad : (R' : ENNReal) ≤ p.radius := by
    refine p.le_radius_of_bound 1 fun n => ?_
    rw [hp, ContinuousMultilinearMap.norm_mkPiRing]
    calc ‖T n‖ * (R' : ℝ) ^ n ≤ R⁻¹ ^ n * R ^ n :=
          mul_le_mul_of_nonneg_right (hTn n) (by positivity)
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hR.ne', one_pow]
  have hRpos : (0 : ENNReal) < R' := by
    have : (0 : NNReal) < R' := hR
    exact_mod_cast this
  have hG : HasFPowerSeriesOnBall p.sum p 0 p.radius :=
    p.hasFPowerSeriesOnBall (lt_of_lt_of_le hRpos hrad)
  have hGa : AnalyticAt ℝ p.sum 0 := hG.analyticAt.restrictScalars
  have hGval : ∀ w : ℂ, ‖w‖ < R → ∀ v, p.sum w v = f v (z₀ + w) := by
    intro w hw v
    have hw' : w ∈ Metric.eball (0 : ℂ) p.radius := by
      refine Metric.eball_subset_eball hrad ?_
      rw [Metric.mem_eball, edist_zero_right]
      have : ‖w‖₊ < R' := by rw [← NNReal.coe_lt_coe]; exact hw
      exact_mod_cast this
    have h1 := hG.hasSum hw'
    simp only [zero_add] at h1
    have h2 := h1.mapL (ContinuousLinearMap.apply ℝ ℂ v)
    have e : ∀ n, (ContinuousLinearMap.apply ℝ ℂ v) (p n fun _ => w) = w ^ n * T n v := by
      intro n
      simp [hp, ContinuousMultilinearMap.mkPiRing_apply]
    simp only [e] at h2
    simp only [ContinuousLinearMap.apply_apply] at h2
    exact h2.unique (hf v w hw)
  have hb := (ContinuousLinearMap.apply ℝ ℂ :
    E →L[ℝ] (E →L[ℝ] ℂ) →L[ℝ] ℂ).analyticAt_bilinear (v₀, p.sum (z₀ - z₀))
  have hin : AnalyticAt ℝ (fun q : E × ℂ => (q.1, p.sum (q.2 - z₀))) (v₀, z₀) := by
    refine analyticAt_fst.prod ?_
    have h1 : AnalyticAt ℝ (fun q : E × ℂ => q.2 - z₀) (v₀, z₀) :=
      analyticAt_snd.sub analyticAt_const
    have h2 : AnalyticAt ℝ p.sum ((fun q : E × ℂ => q.2 - z₀) (v₀, z₀)) := by
      simpa using hGa
    exact AnalyticAt.comp (g := p.sum) (f := fun q : E × ℂ => q.2 - z₀) h2 h1
  have hcomp := AnalyticAt.comp (g := fun q : E × (E →L[ℝ] ℂ) => q.2 q.1)
    (f := fun q : E × ℂ => (q.1, p.sum (q.2 - z₀))) (by simpa using hb) hin
  refine hcomp.congr ?_
  have hnb : {q : E × ℂ | ‖q.2 - z₀‖ < R} ∈ 𝓝 (v₀, z₀) := by
    have hc : Continuous fun q : E × ℂ => ‖q.2 - z₀‖ := by fun_prop
    exact hc.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by simpa using hR))
  filter_upwards [hnb] with q hq
  simp only [Function.comp_apply, ContinuousLinearMap.apply_apply]
  rw [hGval _ hq q.1, add_sub_cancel]


variable [hH : Hypotheses]
include hH

omit hH in
lemma IsRealAnalyticPotential.schrCocycle {δ : ℝ} {v : ℂ → ℂ}
    (hv : IsRealAnalyticPotential δ v) : IsAnalyticCocycle δ (AvilaGlobal.schr v) := by
  have hw : IsRealAnalyticPotential δ (fun z => -v z) :=
    ⟨hv.pos, hv.holo.neg, fun z => by simp [hv.periodic], fun x => by simp [hv.real x]⟩
  have e : AvilaGlobal.schr (eShift 0 (fun z => -v z)) = AvilaGlobal.schr v := by
    funext z; simp [AvilaGlobal.schr, eShift]
  rw [← e]; exact hw.schr 0

lemma lyapunov_conj' {α : ℝ} {A B : ℝ → M2} (hA : IsSLCocycle A) (hBc : Continuous B)
    (hBp : Function.Periodic B 1) (hBdet : ∀ x, (B x).det = 1) :
    lyapunov α (fun x => (B (x + α))⁻¹ * A x * B x) = lyapunov α A := by
  have hu : ∀ x, IsUnit (B x).det := fun x => by rw [hBdet]; exact isUnit_one
  have hBi : Continuous fun x => (B x)⁻¹ := by
    have : (fun x => (B x)⁻¹) = fun x => (B x).adjugate := funext fun x => by
      rw [Matrix.inv_def, hBdet]; simp
    rw [this]; exact hBc.matrix_adjugate
  have h := lyapunov_conj (α := α) hA hBi (fun x => by simp only [hBp x]) (fun x => by
    rw [Matrix.det_nonsing_inv, hBdet]; simp)
  simpa only [Matrix.nonsing_inv_nonsing_inv _ (hu _)] using h

omit hH in
lemma periodic_int_C {β : Type*} {f : ℂ → β} (hf : ∀ z, f (z + 1) = f z) (n : ℤ) (z : ℂ) :
    f (z - n) = f z := by
  have hp : Function.Periodic f (1 : ℂ) := hf
  simpa using hp.sub_int_mul_eq n

omit hH in
/-- The frame algebra: `A B = B(·+α) diag(μ, μ⁻¹)`. -/
lemma frame_mul {V a b c a' b' : ℂ} (hc : c ≠ 0) (ha1 : 1 + a ≠ 0) (hb : b ≠ 0)
    (hb' : b' = -c) (ha' : a' = -a - 2 * V * c) (h3 : a ^ 2 + 4 * b * c = 1) :
    (!![V, -1; 1, 0] : M2) * !![1 + a, (a - 1) / (4 * b); 2 * b, 1 / 2] =
      !![1 + a', (a' - 1) / (4 * b'); 2 * b', 1 / 2] *
        diagonal ![(1 + a) / (-2 * c), ((1 + a) / (-2 * c))⁻¹] := by
  have hbv : b = (1 - a ^ 2) / (4 * c) := by
    field_simp; linear_combination h3
  have h1a : 1 - a ^ 2 ≠ 0 := by
    intro h; apply hb; rw [hbv, h, zero_div]
  have h1a' : 1 - a ≠ 0 := by
    intro h; apply h1a; linear_combination (1 + a) * h
  subst hb' ha'
  rw [hbv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

/-- **Endgame.**  If the coefficients of the derivative extend across `ℝ` (purely imaginary
there), then `y ↦ L(α, A^{(v)}_y)` is constant for small `y > 0`. -/
theorem L_const_of_ext {δ α : ℝ} (hα : Irrational α) {v : ℂ → ℂ}
    (hv : IsRealAnalyticPotential δ v) {y₁ : ℝ} (hy₁ : 0 < y₁) (hy₁δ : y₁ ≤ δ)
    {Φ₁ Φ₂ Φ₃ : ℂ → ℂ}
    (hd₁ : DifferentiableOn ℂ Φ₁ (strip y₁)) (hd₂ : DifferentiableOn ℂ Φ₂ (strip y₁))
    (hd₃ : DifferentiableOn ℂ Φ₃ (strip y₁))
    (hp₁ : ∀ z, Φ₁ (z + 1) = Φ₁ z) (hp₂ : ∀ z, Φ₂ (z + 1) = Φ₂ z)
    (hp₃ : ∀ z, Φ₃ (z + 1) = Φ₃ z)
    (hr₁ : ∀ x : ℝ, (Φ₁ x).re = 0) (hr₂ : ∀ x : ℝ, (Φ₂ x).re = 0)
    (hr₃ : ∀ x : ℝ, (Φ₃ x).re = 0)
    (hI1 : ∀ z : ℂ, 0 < z.im → z.im < y₁ → Φ₂ (z + (α : ℂ)) = -Φ₃ z)
    (hI2 : ∀ z : ℂ, 0 < z.im → z.im < y₁ → Φ₁ (z + (α : ℂ)) = -Φ₁ z - 2 * v z * Φ₃ z)
    (hI3 : ∀ z : ℂ, 0 < z.im → z.im < y₁ → Φ₁ z ^ 2 + 4 * Φ₂ z * Φ₃ z = 1) :
    ∃ y₃ > 0, ∃ c : ℝ, ∀ y ∈ Ioo 0 y₃, L α (schr v) y = c := by
  have hopen := isOpen_strip y₁
  have hc₁ := hd₁.continuousOn
  have hc₂ := hd₂.continuousOn
  have hc₃ := hd₃.continuousOn
  have hR : ∀ x : ℝ, (x : ℂ) ∈ strip y₁ := fun x => by
    show |((x : ℂ)).im| < y₁; simpa using hy₁
  -- S1: the determinant identity on `ℝ`
  have hI3R : ∀ x : ℝ, Φ₁ x ^ 2 + 4 * Φ₂ x * Φ₃ x = 1 := by
    intro x
    set F : ℂ → ℂ := fun z => Φ₁ z ^ 2 + 4 * Φ₂ z * Φ₃ z with hF
    have hFc : ContinuousAt F x := by
      have h1 := hc₁.continuousAt (hopen.mem_nhds (hR x))
      have h2 := hc₂.continuousAt (hopen.mem_nhds (hR x))
      have h3 := hc₃.continuousAt (hopen.mem_nhds (hR x))
      exact (h1.pow 2).add ((continuousAt_const.mul h2).mul h3)
    have hpath : Tendsto (fun t : ℝ => (x : ℂ) + t * I) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
      have : Continuous fun t : ℝ => (x : ℂ) + t * I := by fun_prop
      have h := this.tendsto 0
      simp only [ofReal_zero, zero_mul, add_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    have hev : (fun t : ℝ => F ((x : ℂ) + t * I)) =ᶠ[𝓝[>] 0] fun _ => 1 := by
      filter_upwards [Ioo_mem_nhdsGT hy₁] with t ht
      exact hI3 _ (by simpa using ht.1) (by simpa using ht.2)
    exact tendsto_nhds_unique ((hFc.tendsto.comp hpath).congr' hev) tendsto_const_nhds
  -- S2: `Im Φ₃ ≠ 0` on `ℝ`
  have hf₃ : ∀ x : ℝ, (Φ₃ x).im ≠ 0 := by
    intro x h0
    have := congrArg Complex.re (hI3R x)
    simp [sq, Complex.mul_re, hr₁ x, hr₂ x, hr₃ x, h0] at this
    nlinarith [sq_nonneg (Φ₁ x).im]
  have hf₃c : Continuous fun x : ℝ => (Φ₃ x).im :=
    Complex.continuous_im.comp (hc₃.comp_continuous Complex.continuous_ofReal hR)
  -- S3: a sign
  obtain ⟨σ, hσ1, hσ⟩ : ∃ σ : ℝ, |σ| = 1 ∧ ∀ x : ℝ, 0 < σ * (Φ₃ x).im := by
    by_cases h0 : 0 < (Φ₃ (0 : ℝ)).im
    · refine ⟨1, by simp, fun x => ?_⟩
      rw [one_mul]
      by_contra hx
      push Not at hx
      have hsub := intermediate_value_uIcc (a := (0 : ℝ)) (b := x) hf₃c.continuousOn
      obtain ⟨t, -, ht⟩ := hsub (Set.mem_uIcc.2 (Or.inr ⟨hx, h0.le⟩))
      exact hf₃ t ht
    · push Not at h0
      have h0' : (Φ₃ (0 : ℝ)).im < 0 := lt_of_le_of_ne h0 (hf₃ 0)
      refine ⟨-1, by simp, fun x => ?_⟩
      rw [neg_one_mul, neg_pos]
      by_contra hx
      push Not at hx
      have hsub := intermediate_value_uIcc (a := (0 : ℝ)) (b := x) hf₃c.continuousOn
      obtain ⟨t, -, ht⟩ := hsub (Set.mem_uIcc.2 (Or.inl ⟨h0'.le, hx⟩))
      exact hf₃ t ht
  -- S4: the function `ρ`
  set N : ℂ → ℂ := fun z => -I * σ * (1 + Φ₁ z) with hN
  set Dn : ℂ → ℂ := fun z => -2 * Φ₃ z with hDn
  set ρ : ℂ → ℝ := fun z => (N z * conj (Dn z)).re with hρ
  have hρc : ContinuousOn ρ (strip y₁) := by
    have h1 : ContinuousOn N (strip y₁) := continuousOn_const.mul (continuousOn_const.add hc₁)
    have h2 : ContinuousOn Dn (strip y₁) := continuousOn_const.mul hc₃
    exact Complex.continuous_re.comp_continuousOn
      (h1.mul (Complex.continuous_conj.comp_continuousOn h2))
  have hρR : ∀ x : ℝ, ρ x = 2 * (σ * (Φ₃ x).im) := by
    intro x
    simp [hρ, hN, hDn, Complex.mul_re, Complex.mul_im, hr₁ x, hr₃ x]
    ring
  have hρper : ∀ z, ρ (z + 1) = ρ z := fun z => by simp only [hρ, hN, hDn, hp₁, hp₃]
  -- S5: positivity of `ρ` on a thin strip
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 (zero_le_one' ℝ))
    (show ContinuousOn (fun t : ℝ => ρ t) (Icc 0 1) from
      (hρc.comp_continuous Complex.continuous_ofReal hR).continuousOn)
  set κ := ρ t₀ with hκ
  have hκpos : 0 < κ := by rw [hκ, hρR]; linarith [hσ t₀]
  set K : Set ℂ := Icc (0 : ℝ) 1 ×ℂ Icc (-(y₁ / 2)) (y₁ / 2) with hK
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hKs : K ⊆ strip y₁ := by
    intro z hz
    have h2 : z.im ∈ Icc (-(y₁ / 2)) (y₁ / 2) := hz.2
    show |z.im| < y₁
    rw [abs_lt]; constructor <;> linarith [h2.1, h2.2]
  obtain ⟨η, hη, hηu⟩ := Metric.uniformContinuousOn_iff.1
    (hKc.uniformContinuousOn_of_continuous (hρc.mono hKs)) κ hκpos
  set y₃ := min η (y₁ / 2) with hy₃
  have hy₃pos : 0 < y₃ := lt_min hη (by linarith)
  have hy₃y₁ : y₃ < y₁ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hρpos : ∀ z : ℂ, |z.im| < y₃ → 0 < ρ z := by
    intro z hz
    set w := z - (⌊z.re⌋ : ℂ) with hw
    have hρw : ρ w = ρ z := by rw [hw]; exact periodic_int_C hρper _ z
    have hwre : w.re ∈ Icc (0 : ℝ) 1 := by
      simp only [hw, sub_re, intCast_re]
      constructor
      · linarith [Int.floor_le z.re]
      · linarith [Int.lt_floor_add_one z.re]
    have hwim : w.im = z.im := by simp [hw]
    have hz' : |z.im| < y₁ / 2 := lt_of_lt_of_le hz (min_le_right _ _)
    have hwK : w ∈ K := ⟨hwre, by
      show w.im ∈ Icc (-(y₁ / 2)) (y₁ / 2)
      rw [hwim]; exact ⟨by linarith [neg_abs_le z.im], by linarith [le_abs_self z.im]⟩⟩
    have hw'K : ((w.re : ℝ) : ℂ) ∈ K := ⟨by simpa using hwre, by
      show (((w.re : ℝ) : ℂ)).im ∈ Icc (-(y₁ / 2)) (y₁ / 2)
      simp; linarith⟩
    have hd : dist w ((w.re : ℝ) : ℂ) < η := by
      rw [dist_eq_norm]
      have : w - ((w.re : ℝ) : ℂ) = (w.im : ℂ) * I := by
        apply Complex.ext <;> simp
      rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, hwim]
      exact lt_of_lt_of_le hz (min_le_left _ _)
    have h1 := hηu w hwK _ hw'K hd
    have h2 : κ ≤ ρ ((w.re : ℝ) : ℂ) := hmin hwre
    rw [Real.dist_eq] at h1
    rw [← hρw]
    have := abs_lt.1 h1
    linarith [this.1]
  have hstrip3 : ∀ z : ℂ, |z.im| < y₃ → z ∈ strip y₁ := fun z hz => by
    show |z.im| < y₁; linarith
  have hDn0 : ∀ z : ℂ, |z.im| < y₃ → Dn z ≠ 0 := by
    intro z hz h; have := hρpos z hz; simp [hρ, h] at this
  have hN0 : ∀ z : ℂ, |z.im| < y₃ → N z ≠ 0 := by
    intro z hz h; have := hρpos z hz; simp [hρ, h] at this
  have hΦ₃0 : ∀ z : ℂ, |z.im| < y₃ → Φ₃ z ≠ 0 := by
    intro z hz h; apply hDn0 z hz; simp [hDn, h]
  have h1a0 : ∀ z : ℂ, |z.im| < y₃ → 1 + Φ₁ z ≠ 0 := by
    intro z hz h; apply hN0 z hz; simp [hN, h]
  -- S6: the logarithm
  set θ : ℂ → ℂ := fun z => N z / Dn z with hθ
  have hθre : ∀ z : ℂ, |z.im| < y₃ → 0 < (θ z).re := by
    intro z hz
    have hn : 0 < Complex.normSq (Dn z) := Complex.normSq_pos.2 (hDn0 z hz)
    have e : (θ z).re = ρ z / Complex.normSq (Dn z) := by
      simp only [hθ, hρ, Complex.div_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    rw [e]; exact div_pos (hρpos z hz) hn
  set h : ℂ → ℂ := fun z => Complex.log (θ z) with hh
  have hhd : DifferentiableOn ℂ h (strip y₃) := by
    intro z hz
    have hz' : |z.im| < y₃ := hz
    have hz1 : z ∈ strip y₁ := hstrip3 z hz'
    have hdz : ∀ {f : ℂ → ℂ}, DifferentiableOn ℂ f (strip y₁) → DifferentiableAt ℂ f z :=
      fun hf => (hf z hz1).differentiableAt (hopen.mem_nhds hz1)
    have hNd : DifferentiableAt ℂ N z :=
      (differentiableAt_const _).mul ((differentiableAt_const _).add (hdz hd₁))
    have hDd : DifferentiableAt ℂ Dn z := (differentiableAt_const _).mul (hdz hd₃)
    have hθd : DifferentiableAt ℂ θ z := hNd.div hDd (hDn0 z hz')
    exact (hθd.clog (Or.inl (hθre z hz'))).differentiableWithinAt
  have hhper : ∀ z, h (z + 1) = h z := fun z => by simp only [hh, hθ, hN, hDn, hp₁, hp₃]
  have hy3' : |y₃ / 2| < y₃ := by rw [abs_of_pos (by linarith)]; linarith
  refine ⟨y₃, hy₃pos, |(fcoef h 0 (y₃ / 2)).re|, fun y hy => ?_⟩
  have hy' : |y| < y₃ := by rw [abs_of_pos hy.1]; exact hy.2
  have hyy₁ : y < y₁ := lt_trans hy.2 hy₃y₁
  have hline : ∀ x : ℝ, |((x : ℂ) + y * I).im| < y₃ := fun x => by simpa using hy'
  -- S7: computation of `L`
  set μ : ℂ → ℂ := fun z => (1 + Φ₁ z) / (-2 * Φ₃ z) with hμ
  have hcl : ∀ {f : ℂ → ℂ}, ContinuousOn f (strip y₁) →
      Continuous fun x : ℝ => f ((x : ℂ) + y * I) := fun hf =>
    hf.comp_continuous (by fun_prop) (fun x => hstrip3 _ (hline x))
  have hμc : Continuous fun x : ℝ => μ ((x : ℂ) + y * I) := by
    simp only [hμ]
    exact ((continuous_const.add (hcl hc₁))).div (continuous_const.mul (hcl hc₃))
      (fun x => mul_ne_zero (by norm_num) (hΦ₃0 _ (hline x)))
  have hμp : Function.Periodic (fun x : ℝ => μ ((x : ℂ) + y * I)) 1 := fun x => by
    simp only [hμ]; push_cast; rw [add_right_comm, hp₁, hp₃]
  have hμ0 : ∀ x : ℝ, μ ((x : ℂ) + y * I) ≠ 0 := fun x =>
    div_ne_zero (h1a0 _ (hline x)) (mul_ne_zero (by norm_num) (hΦ₃0 _ (hline x)))
  -- the frame
  have hΦ₂0 : ∀ x : ℝ, Φ₂ ((x : ℂ) + y * I) ≠ 0 := by
    intro x
    have e := hI1 ((((x - α : ℝ) : ℂ)) + y * I) (by simpa using hy.1) (by simpa using hyy₁)
    have e2 : (((x - α : ℝ) : ℂ)) + y * I + (α : ℂ) = (x : ℂ) + y * I := by push_cast; ring
    rw [e2] at e
    rw [e, neg_ne_zero]
    exact hΦ₃0 _ (hline _)
  set Bf : ℝ → M2 := fun x => !![1 + Φ₁ ((x : ℂ) + y * I),
    (Φ₁ ((x : ℂ) + y * I) - 1) / (4 * Φ₂ ((x : ℂ) + y * I)); 2 * Φ₂ ((x : ℂ) + y * I), 1 / 2]
    with hBf
  have hBc : Continuous Bf := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp only [hBf, of_apply, cons_val', cons_val_zero,
      cons_val_one, empty_val', cons_val_fin_one, head_cons]
    · exact continuous_const.add (hcl hc₁)
    · exact ((hcl hc₁).sub continuous_const).div (continuous_const.mul (hcl hc₂))
        (fun x => mul_ne_zero (by norm_num) (hΦ₂0 x))
    · exact continuous_const.mul (hcl hc₂)
    · exact continuous_const
  have hBp : Function.Periodic Bf 1 := fun x => by
    simp only [hBf]; push_cast; rw [add_right_comm, hp₁, hp₂]
  have hBdet : ∀ x, (Bf x).det = 1 := by
    intro x
    simp only [hBf, det_fin_two_of]
    field_simp [hΦ₂0 x]
    ring
  have hA := (hv.schrCocycle).isSLCocycle_shift (ε := y) (by
    rw [abs_of_pos hy.1]; linarith)
  have hconj := lyapunov_conj' (α := α) hA hBc hBp hBdet
  have hdiag : (fun x => (Bf (x + α))⁻¹ * shift (schr v) y x * Bf x) =
      fun x : ℝ => (diagonal ![μ ((x : ℂ) + y * I), (μ ((x : ℂ) + y * I))⁻¹] : M2) := by
    funext x
    set z : ℂ := (x : ℂ) + y * I with hz
    have hz1 : 0 < z.im := by simpa [hz] using hy.1
    have hz2 : z.im < y₁ := by simpa [hz] using hyy₁
    have hzα : ((x + α : ℝ) : ℂ) + y * I = z + (α : ℂ) := by rw [hz]; push_cast; ring
    have hmul := frame_mul (V := v z) (a' := Φ₁ (z + (α : ℂ))) (b' := Φ₂ (z + (α : ℂ)))
      (hΦ₃0 z (hline x)) (h1a0 z (hline x)) (hΦ₂0 x) (hI1 z hz1 hz2) (hI2 z hz1 hz2)
      (hI3 z hz1 hz2)
    have hB' : Bf (x + α) = !![1 + Φ₁ (z + (α : ℂ)), (Φ₁ (z + (α : ℂ)) - 1) /
        (4 * Φ₂ (z + (α : ℂ))); 2 * Φ₂ (z + (α : ℂ)), 1 / 2] := by
      simp only [hBf, hzα]
    have hu : IsUnit (Bf (x + α)).det := by rw [hBdet]; exact isUnit_one
    have hsh : shift (schr v) y x = !![v z, -1; 1, 0] := rfl
    rw [hsh, Matrix.mul_assoc]
    change (Bf (x + α))⁻¹ * (!![v z, -1; 1, 0] * !![1 + Φ₁ z, (Φ₁ z - 1) / (4 * Φ₂ z);
      2 * Φ₂ z, 1 / 2]) = _
    rw [hmul, ← hB', ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  have hL : L α (schr v) y = |∫ x in (0 : ℝ)..1, Real.log ‖μ ((x : ℂ) + y * I)‖| := by
    rw [L, ← hconj, hdiag]
    exact lyapunov_diagonal hα hμc hμp hμ0
  rw [hL, ← fcoef_indep hhd hhper 0 hy' hy3']
  congr 1
  have hhc : Continuous fun x : ℝ => h ((x : ℂ) + y * I) :=
    hhd.continuousOn.comp_continuous (by fun_prop) (fun x => hline x)
  have e1 : fcoef h 0 y = ∫ x in (0 : ℝ)..1, h ((x : ℂ) + y * I) := by
    simp [fcoef, eC]
  rw [e1, ← iInt_re (hhc.intervalIntegrable 0 1)]
  refine intervalIntegral.integral_congr fun x _ => ?_
  simp only [hh, Complex.log_re]
  congr 1
  have : θ ((x : ℂ) + y * I) = (-I * σ) * μ ((x : ℂ) + y * I) := by
    simp only [hθ, hN, hDn, hμ]; ring
  rw [this, norm_mul, norm_mul, norm_neg, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    hσ1, one_mul, one_mul]

/-! ### `C^ω_δ(ℝ/ℤ, ℝ)` is a real-analytic family -/

lemma Pot.toFun_add {δ : ℝ} (v w : Pot δ) : (v + w).toFun = v.toFun + w.toFun :=
  extend_add v.1 w.1

lemma Pot.toFun_smul {δ : ℝ} (c : ℝ) (v : Pot δ) :
    (c • v).toFun = fun z => (c : ℂ) * v.toFun z :=
  extend_smul c v.1

lemma Pot.norm_toFun_le {δ : ℝ} (v : Pot δ) (z : ℂ) : ‖v.toFun z‖ ≤ ‖v‖ := by
  unfold Pot.toFun extend
  split_ifs with h
  · exact BoundedContinuousFunction.norm_coe_le_norm v.1 ⟨z, h⟩
  · rw [norm_zero]; exact norm_nonneg _

lemma sphere_sub_cstrip {δ R : ℝ} {z₀ : ℂ} (h : Metric.closedBall z₀ R ⊆ strip δ) :
    Metric.sphere z₀ R ⊆ cstrip δ := fun z hz =>
  strip_sub_cstrip (h (Metric.sphere_subset_closedBall hz))

lemma circleIntegrable_taylor {δ R : ℝ} {z₀ : ℂ} (hR : 0 < R)
    (hs : Metric.sphere z₀ R ⊆ cstrip δ) (v : Pot δ) (n : ℕ) :
    CircleIntegrable (fun z => (z - z₀)⁻¹ ^ n • (z - z₀)⁻¹ • v.toFun z) z₀ R := by
  apply ContinuousOn.circleIntegrable hR.le
  have hne : ∀ z ∈ Metric.sphere z₀ R, z - z₀ ≠ 0 := by
    intro z hz h
    rw [Metric.mem_sphere, dist_eq_norm, h, norm_zero] at hz
    linarith
  have h1 : ContinuousOn (fun z : ℂ => (z - z₀)⁻¹) (Metric.sphere z₀ R) :=
    (continuousOn_id.sub continuousOn_const).inv₀ hne
  exact (h1.pow n).smul (h1.smul ((continuousOn_extend v.1).mono hs))

/-- The `n`-th Taylor coefficient at `z₀`. -/
def tco (δ : ℝ) (z₀ : ℂ) (R : ℝ) (n : ℕ) (v : Pot δ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ • ∮ z in C(z₀, R), (z - z₀)⁻¹ ^ n • (z - z₀)⁻¹ • v.toFun z

lemma tco_eq {δ : ℝ} (z₀ : ℂ) (R : ℝ) (n : ℕ) (v : Pot δ) :
    tco δ z₀ R n v = cauchyPowerSeries v.toFun z₀ R n (fun _ => 1) := by
  rw [cauchyPowerSeries_apply, tco]
  simp only [one_div]

lemma tco_add {δ R : ℝ} {z₀ : ℂ} (hR : 0 < R) (hs : Metric.sphere z₀ R ⊆ cstrip δ) (n : ℕ)
    (v w : Pot δ) : tco δ z₀ R n (v + w) = tco δ z₀ R n v + tco δ z₀ R n w := by
  have e : (fun z : ℂ => (z - z₀)⁻¹ ^ n • (z - z₀)⁻¹ • (v + w).toFun z) =
      fun z : ℂ => (z - z₀)⁻¹ ^ n • (z - z₀)⁻¹ • v.toFun z +
        (z - z₀)⁻¹ ^ n • (z - z₀)⁻¹ • w.toFun z := by
    funext z; rw [Pot.toFun_add, Pi.add_apply, smul_add, smul_add]
  unfold tco
  rw [e, circleIntegral.integral_add (circleIntegrable_taylor hR hs v n)
    (circleIntegrable_taylor hR hs w n), smul_add]

lemma tco_smul {δ R : ℝ} {z₀ : ℂ} (n : ℕ) (c : ℝ) (v : Pot δ) :
    tco δ z₀ R n (c • v) = c • tco δ z₀ R n v := by
  have e : (fun z : ℂ => (z - z₀)⁻¹ ^ n • (z - z₀)⁻¹ • (c • v).toFun z) =
      fun z : ℂ => (c : ℂ) • ((z - z₀)⁻¹ ^ n • (z - z₀)⁻¹ • v.toFun z) := by
    funext z; rw [Pot.toFun_smul]; simp only [smul_eq_mul]; ring
  unfold tco
  rw [e, circleIntegral.integral_smul, Complex.real_smul, smul_eq_mul, smul_eq_mul,
    smul_eq_mul]
  ring

lemma tco_bound {δ R : ℝ} {z₀ : ℂ} (hR : 0 < R) (hs : Metric.sphere z₀ R ⊆ cstrip δ) (n : ℕ)
    (v : Pot δ) : ‖tco δ z₀ R n v‖ ≤ R⁻¹ ^ n * ‖v‖ := by
  rw [tco_eq]
  refine ((cauchyPowerSeries v.toFun z₀ R n).le_opNorm _).trans ?_
  simp only [norm_one, Finset.prod_const_one, mul_one]
  refine (norm_cauchyPowerSeries_le _ _ _ _).trans ?_
  rw [abs_of_pos hR, mul_comm (R⁻¹ ^ n)]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have hint : (∫ θ : ℝ in (0 : ℝ)..2 * Real.pi, ‖v.toFun (circleMap z₀ R θ)‖) ≤
      ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi, ‖v‖ := by
    refine intervalIntegral.integral_mono_on Real.two_pi_pos.le ?_
      intervalIntegrable_const (fun θ _ => Pot.norm_toFun_le v _)
    refine ContinuousOn.intervalIntegrable ?_
    refine (((continuousOn_extend v.1).mono hs).comp_continuous
      (continuous_circleMap z₀ R) (fun θ => ?_)).norm.continuousOn
    exact circleMap_mem_sphere z₀ hR.le θ
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hint
  calc (2 * Real.pi)⁻¹ * ∫ θ : ℝ in (0 : ℝ)..2 * Real.pi, ‖v.toFun (circleMap z₀ R θ)‖
      ≤ (2 * Real.pi)⁻¹ * (2 * Real.pi * ‖v‖) :=
        mul_le_mul_of_nonneg_left hint (by positivity)
    _ = ‖v‖ := by
      rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]

/-- The Taylor coefficient as a continuous linear functional. -/
def taylorCLM (δ : ℝ) (z₀ : ℂ) (R : ℝ) (hR : 0 < R) (hs : Metric.sphere z₀ R ⊆ cstrip δ)
    (n : ℕ) : Pot δ →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := tco δ z₀ R n
      map_add' := tco_add hR hs n
      map_smul' := fun c v => tco_smul n c v }
    (R⁻¹ ^ n) (tco_bound hR hs n)

/-- `(v, z) ↦ v(z)` is real-analytic on `C^ω_δ(ℝ/ℤ, ℝ) × {|Im z| < δ}`. -/
theorem pot_analyticFamily {δ : ℝ} (hδ : 0 < δ) :
    IsAnalyticFamily δ (univ : Set (Pot δ)) (fun v => v.toFun) := by
  refine ⟨isOpen_univ, fun v _ => v.isRealAnalyticPotential hδ, ?_⟩
  rintro ⟨v₀, z₀⟩ ⟨-, hz₀⟩
  have hz₀' : |z₀.im| < δ := hz₀
  set R := (δ - |z₀.im|) / 2 with hRdef
  have hR : 0 < R := by rw [hRdef]; linarith
  have hball : Metric.closedBall z₀ R ⊆ strip δ := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    have h1 : |z.im - z₀.im| ≤ ‖z - z₀‖ := by
      simpa using Complex.abs_im_le_norm (z - z₀)
    have h2 : |z.im| ≤ |z₀.im| + |z.im - z₀.im| := by
      have := abs_add_le z₀.im (z.im - z₀.im); simpa using this
    show |z.im| < δ
    linarith
  have hs := sphere_sub_cstrip hball
  refine analyticAt_of_taylor (f := fun v : Pot δ => v.toFun) hR (taylorCLM δ z₀ R hR hs)
    (fun n v => tco_bound hR hs n v) (fun v w hw => ?_) v₀
  set R' : NNReal := ⟨R, hR.le⟩
  have hd : DifferentiableOn ℂ v.toFun (Metric.closedBall z₀ R') :=
    (v.isRealAnalyticPotential hδ).holo.mono hball
  have hp := hd.hasFPowerSeriesOnBall (show (0 : NNReal) < R' from hR)
  rw [show ((R' : NNReal) : ℝ) = R from rfl] at hp
  have hy : w ∈ Metric.eball (0 : ℂ) R' := by
    rw [Metric.mem_eball, edist_zero_right]
    have : ‖w‖₊ < R' := by rw [← NNReal.coe_lt_coe]; exact hw
    exact_mod_cast this
  have h := hp.hasSum hy
  convert h using 1
  funext n
  show w ^ n * tco δ z₀ R n v = _
  rw [tco_eq]
  have : (fun _ : Fin n => w) = fun i => w • (fun _ : Fin n => (1 : ℂ)) i := by
    funext i; simp
  rw [this, ContinuousMultilinearMap.map_smul_univ]
  simp

theorem pot_schrFamily {δ : ℝ} (hδ : 0 < δ) :
    IsAnalyticCocycleFamily δ (univ : Set (Pot δ)) (fun v => schr v.toFun) := by
  have hF := pot_analyticFamily hδ
  refine ⟨isOpen_univ, fun v _ => (v.isRealAnalyticPotential hδ).schrCocycle, ?_⟩
  intro q hq
  exact analyticAt_schr_aux (c := fun q : Pot δ × ℂ => q.1.toFun q.2) (hF.analytic q hq)

/-! ### Algebra of the derivative coefficients for Schrödinger cocycles -/

omit hH in
lemma schr_differentiableOn {s : Set ℂ} {w : ℂ → ℂ} (hw : DifferentiableOn ℂ w s) :
    DifferentiableOn ℂ (schr w) s := by
  have hform : schr w = fun z => w z • (!![1, 0; 0, 0] : M2) + !![0, -1; 1, 0] := by
    funext z; ext i j; fin_cases i <;> fin_cases j <;> simp [schr]
  rw [hform]; exact (hw.smul_const _).add_const _

omit hH in
lemma coeff_I2 {v : ℂ} {B B' : M2} (hB : B.det = 1) (hB' : B'.det = 1)
    (hdiag : (B'⁻¹ * !![v, -1; 1, 0] * B) 0 1 = 0 ∧ (B'⁻¹ * !![v, -1; 1, 0] * B) 1 0 = 0) :
    derivCoeffs B' 0 = -derivCoeffs B 0 - 2 * v * derivCoeffs B 2 := by
  set D := B'⁻¹ * !![v, -1; 1, 0] * B with hDdef
  have hu : IsUnit B'.det := by rw [hB']; exact isUnit_one
  have hD : B' * D = !![v, -1; 1, 0] * B := by
    rw [hDdef, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu,
      Matrix.one_mul]
  have hdetD : D.det = 1 := by
    rw [hDdef, Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, hB', hB]
    simp [Matrix.det_fin_two]
  rw [Matrix.det_fin_two, hdiag.1, hdiag.2] at hdetD
  have h00 := congrFun (congrFun hD 0) 0
  have h01 := congrFun (congrFun hD 0) 1
  have h10 := congrFun (congrFun hD 1) 0
  have h11 := congrFun (congrFun hD 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two, hdiag.1, hdiag.2] at h00 h01 h10 h11
  simp only [derivCoeffs, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  linear_combination (-(B' 0 0 * B' 1 1 + B' 0 1 * B' 1 0)) * hdetD +
    (D 1 1 * B' 1 1) * h00 + (v * B 0 0 - B 1 0) * h11 + (D 0 0 * B' 1 0) * h01 +
    (v * B 0 1 - B 1 1) * h10

omit hH in
lemma coeff_I3 {B : M2} (hB : B.det = 1) :
    derivCoeffs B 0 ^ 2 + 4 * derivCoeffs B 1 * derivCoeffs B 2 = 1 := by
  rw [Matrix.det_fin_two] at hB
  simp only [derivCoeffs, Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Matrix.cons_val_one]
  linear_combination (B 0 0 * B 1 1 - B 0 1 * B 1 0 + 1) * hB

/-! ### Real-analytic potentials from entire periodic functions -/

lemma exists_pot_of_entire {δ : ℝ} (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (hper : ∀ z, f (z + 1) = f z) (hreal : ∀ x : ℝ, (f x).im = 0) :
    ∃ p : Pot δ, ∀ z ∈ cstrip δ, p.toFun z = f z := by
  classical
  set K : Set ℂ := Icc (0 : ℝ) 1 ×ℂ Icc (-δ) δ
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨Mb, hMb⟩ := hK.exists_bound_of_continuousOn hf.continuous.continuousOn
  have hb : ∀ z ∈ cstrip δ, ‖f z‖ ≤ Mb := by
    intro z hz
    have hz' : |z.im| ≤ δ := hz
    have e : f z = f (z - (⌊z.re⌋ : ℂ)) := (periodic_int_C hper _ z).symm
    rw [e]
    refine hMb _ ⟨?_, ?_⟩
    · show (z - (⌊z.re⌋ : ℂ)).re ∈ Icc (0 : ℝ) 1
      simp only [sub_re, intCast_re]
      constructor
      · linarith [Int.floor_le z.re]
      · linarith [Int.lt_floor_add_one z.re]
    · show (z - (⌊z.re⌋ : ℂ)).im ∈ Icc (-δ) δ
      simp only [sub_im, intCast_im, sub_zero]
      exact abs_le.1 hz'
  set g : BoundedContinuousFunction (cstrip δ) ℂ :=
    BoundedContinuousFunction.mkOfBound ⟨fun z => f z, hf.continuous.comp continuous_subtype_val⟩
      (2 * Mb) (fun x y => by
        refine (dist_le_norm_add_norm _ _).trans ?_
        have := hb x x.2; have := hb y y.2
        simp only [ContinuousMap.coe_mk]; linarith)
  have hext : ∀ z ∈ cstrip δ, extend g z = f z := fun z hz => by
    simp [extend, hz, g]
  have hmem : g ∈ PotSpace δ := by
    refine ⟨?_, ?_, ?_⟩
    · exact hf.differentiableOn.congr fun z hz => hext z (strip_sub_cstrip hz)
    · intro z
      by_cases hz : z ∈ cstrip δ
      · have hz1 : z + 1 ∈ cstrip δ := by simpa [cstrip] using hz
        rw [hext _ hz1, hext _ hz, hper]
      · have hz1 : z + 1 ∉ cstrip δ := by simpa [cstrip] using hz
        simp [extend, hz, hz1]
    · intro x
      by_cases hx : (x : ℂ) ∈ cstrip δ
      · rw [hext _ hx, hreal]
      · simp [extend, hx]
  exact ⟨⟨g, hmem⟩, fun z hz => hext z hz⟩

/-! ### The derivative of `L_{δ,j}` along potential perturbations, at a fixed height -/

omit hH in
lemma eC_neg_periodic (m : ℤ) (z : ℂ) : eC (-(m * (z + 1))) = eC (-(m * z)) := by
  rw [show -((m : ℂ) * (z + 1)) = -(m * z) + ((-m : ℤ) : ℂ) by push_cast; ring, eC_add,
    eC_intCast, mul_one]

set_option maxHeartbeats 1000000 in
lemma deriv_at_height (hD : DerivFormulaClaim) {δ α : ℝ} {j : ℤ} {v : ℂ → ℂ}
    (hv : IsRealAnalyticPotential δ v) {y : ℝ} (hy : y ∈ Ioo 0 δ)
    (hUH : UH α (cshift (schr v) y)) (hacc : accel α (cshift (schr v) y) = j)
    {B : ℝ → M2} (hBc : Continuous B) (hBp : Function.Periodic B 1) (hBd : ∀ x, (B x).det = 1)
    (hdiag : ∀ x, ((B (x + α))⁻¹ * shift (schr v) y x * B x) 0 1 = 0 ∧
      ((B (x + α))⁻¹ * shift (schr v) y x * B x) 1 0 = 0)
    (hexp : ∃ n : ℕ, 1 ≤ n ∧ ∀ x, ‖B x *ᵥ ![1, 0]‖ <
      ‖iter α (shift (schr v) y) n x *ᵥ (B x *ᵥ ![1, 0])‖)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (strip δ)) (hgp : ∀ z, g (z + 1) = g z) :
    HasDerivAt (fun t : ℝ => Ldj δ j α (schr (fun z => v z + t * g z)))
      (∫ x in (0 : ℝ)..1, (derivCoeffs (B x) 2 * (-g (x + y * I))).re) 0 := by
  have hδ := hv.pos
  have hyδ : |y| < δ := by rw [abs_of_pos hy.1]; exact hy.2
  set Af : ℝ → ℂ → M2 := fun t => schr (fun z => v z + t * g z) with hAf
  have hcoc : ∀ t, IsAnalyticCocycle δ (Af t) := fun t =>
    ⟨hδ, schr_differentiableOn (hv.holo.add (hg.const_mul _)),
      fun z => by simp only [hAf, schr, hv.periodic, hgp], fun z _ => det_schr _ z⟩
  have hfam : IsAnalyticCocycleFamily δ (univ : Set ℝ) Af := by
    refine ⟨isOpen_univ, fun t _ => hcoc t, ?_⟩
    rintro ⟨t, z⟩ ⟨-, hz⟩
    show AnalyticAt ℝ (fun q : ℝ × ℂ => schr (fun z => v z + q.1 * g z) q.2) (t, z)
    have hvz : AnalyticAt ℝ (fun q : ℝ × ℂ => v q.2) (t, z) :=
      AnalyticAt.comp (g := v) (f := Prod.snd)
        (hv.holo.analyticAt ((isOpen_strip δ).mem_nhds hz)).restrictScalars analyticAt_snd
    have hgz : AnalyticAt ℝ (fun q : ℝ × ℂ => g q.2) (t, z) :=
      AnalyticAt.comp (g := g) (f := Prod.snd)
        (hg.analyticAt ((isOpen_strip δ).mem_nhds hz)).restrictScalars analyticAt_snd
    have ht : AnalyticAt ℝ (fun q : ℝ × ℂ => ((q.1 : ℝ) : ℂ)) (t, z) :=
      AnalyticAt.comp (g := ⇑Complex.ofRealCLM) (f := Prod.fst)
        (Complex.ofRealCLM.analyticAt _) analyticAt_fst
    exact analyticAt_schr_aux (c := fun q : ℝ × ℂ => v q.2 + (q.1 : ℂ) * g q.2)
      (hvz.add (ht.mul hgz))
  have hAf0 : Af 0 = schr v := by funext z; simp [hAf]
  have hcore := (omega_core hfam (j := j) (α₀ := α) (mem_univ (0 : ℝ)) hy
    (by rw [hAf0]; exact hUH) (by rw [hAf0]; exact hacc)).1
  have hev : ∀ᶠ t in 𝓝 (0 : ℝ), UH α (cshift (Af t) y) ∧ accel α (cshift (Af t) y) = j := by
    have ht : Tendsto (fun t : ℝ => (α, t)) (𝓝 0) (𝓝 (α, 0)) :=
      (continuous_const.prodMk continuous_id).tendsto' 0 (α, 0) rfl
    exact (ht.eventually hcore).mono fun t h => ⟨h.2.1, h.2.2⟩
  have hLdj : (fun t : ℝ => L α (Af t) y - 2 * Real.pi * j * y) =ᶠ[𝓝 0]
      fun t : ℝ => Ldj δ j α (Af t) := by
    filter_upwards [hev] with t ht
    exact (Ldj_eq (hcoc t) hy ht.1 ht.2).symm
  set W : ℝ → M2 := fun x => !![0, 0; -g (x + y * I), 0] with hW
  have hline : Continuous fun x : ℝ => g (x + y * I) :=
    hg.continuousOn.comp_continuous (by fun_prop) (mem_strip_shift hyδ)
  have hWc : Continuous W := by
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [hW] <;> first | exact continuous_const | exact hline.neg
  have hWp : Function.Periodic W 1 := fun x => by
    simp only [hW]; push_cast; rw [add_right_comm, hgp]
  have hWt : ∀ x, (W x).trace = 0 := fun x => by simp [hW, Matrix.trace_fin_two]
  have hA := hv.schrCocycle
  have hUH' : IsUH α (shift (schr v) y) := by
    have : shift (cshift (schr v) y) 0 = shift (schr v) y := by rw [shift_cshift, zero_add]
    have h := hUH; unfold UH at h; rwa [this] at h
  have hder := hD (hA.isSLCocycle_shift hyδ) hUH' hBc hBp hBd hdiag hexp hWc hWp hWt
  have hfun : (fun t : ℝ => lyapunov α fun x => shift (schr v) y x *
      NormedSpace.exp ((t : ℂ) • W x)) = fun t : ℝ => L α (Af t) y := by
    funext t
    unfold L
    congr 1
    funext x
    simp only [hW]
    rw [exp_lower]
    ext i k
    fin_cases i <;> fin_cases k <;> simp [shift, schr, hAf, Matrix.mul_apply, Fin.sum_univ_two]
  have hval : (∫ x in (0 : ℝ)..1, (derivCoeffs (B x) 0 * W x 0 0 + derivCoeffs (B x) 1 * W x 0 1 +
      derivCoeffs (B x) 2 * W x 1 0).re) =
      ∫ x in (0 : ℝ)..1, (derivCoeffs (B x) 2 * (-g (x + y * I))).re := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp [hW]
  rw [hfun, hval] at hder
  exact (hder.sub_const _).congr_of_eventuallyEq hLdj.symm

/-! ### Proof of Theorem `cod1` -/

omit hH in
lemma one_add_eC_ne_zero {α : ℝ} (hα : Irrational α) (m : ℤ) : 1 + eC (m * α) ≠ 0 := by
  intro h
  have h1 : eC (m * α) = -1 := by linear_combination h
  have h2 : eC (((2 * m : ℤ) : ℂ) * α) = 1 := by
    rw [show (((2 * m : ℤ) : ℂ) * α) = m * α + m * α by push_cast; ring, eC_add, h1]
    norm_num
  obtain ⟨k, hk⟩ := eC_eq_one_iff.1 h2
  by_cases hm : m = 0
  · subst hm; simp [eC] at h1; norm_num at h1
  · apply hα
    refine ⟨(k : ℚ) / (2 * m), ?_⟩
    have hk' : ((2 * m : ℤ) : ℝ) * α = k := by exact_mod_cast hk
    have h2m : ((2 * m : ℤ) : ℝ) ≠ 0 := by
      have : (2 * m : ℤ) ≠ 0 := by omega
      exact_mod_cast this
    push_cast at hk' h2m ⊢
    field_simp
    linarith

omit hH in
lemma dc0 (B : M2) : derivCoeffs B 0 = B 0 0 * B 1 1 + B 0 1 * B 1 0 := rfl
omit hH in
lemma dc1 (B : M2) : derivCoeffs B 1 = B 1 0 * B 1 1 := rfl
omit hH in
lemma dc2 (B : M2) : derivCoeffs B 2 = -(B 0 1 * B 0 0) := rfl

omit hH in
lemma continuous_derivCoeffs {B : ℝ → M2} (hB : Continuous B) (i : Fin 3) :
    Continuous fun x => derivCoeffs (B x) i := by
  have e : ∀ a b : Fin 2, Continuous fun x => B x a b := fun a b => hB.matrix_elem a b
  fin_cases i
  · simp only [Fin.zero_eta, dc0]; exact ((e 0 0).mul (e 1 1)).add ((e 0 1).mul (e 1 0))
  · simp only [Fin.mk_one, dc1]; exact (e 1 0).mul (e 1 1)
  · show Continuous fun x => derivCoeffs (B x) 2
    simp only [dc2]; exact ((e 0 1).mul (e 0 0)).neg

omit hH in
lemma fcoef_re_eq (f : ℝ → ℂ) (m : ℤ) (y : ℝ) :
    fcoef (fun z => f z.re) m y = ∫ x in (0 : ℝ)..1, f x * eC (-(m * (x + y * I))) := by
  simp [fcoef]

omit hH in
lemma continuous_line_eC (m : ℤ) (y : ℝ) :
    Continuous fun x : ℝ => eC (-(m * ((x : ℂ) + y * I))) :=
  differentiable_eC.continuous.comp (by fun_prop)

set_option maxHeartbeats 1000000 in
/-- **Theorem `cod1`**, assuming the derivative formula for `L` at uniformly hyperbolic
cocycles. -/
theorem cod1_proof (hD : DerivFormulaClaim) {δ α : ℝ} : Cod1Claim δ α := by
  intro hδ hα j hj vstar hacc
  set v : ℂ → ℂ := vstar.toFun with hvdef
  have hv : IsRealAnalyticPotential δ v := vstar.isRealAnalyticPotential hδ
  have hA : IsAnalyticCocycle δ (schr v) := hv.schrCocycle
  have hj0 : j ≠ 0 := hj.ne'
  -- analyticity (Proposition `pluri`)
  have hfam := pot_schrFamily hδ
  obtain ⟨hOpen, hAn⟩ := pluri_open_analytic hfam α j
  obtain ⟨⟨δ₀, hδ₀, hU⟩, hΩ, -⟩ := pluri_mem hA hα hacc hj0
  have hmem : vstar ∈ {p : Pot δ | p ∈ univ ∧ OmegaSet δ j α (schr p.toFun)} :=
    ⟨mem_univ _, hΩ⟩
  refine ⟨_, hOpen.mem_nhds hmem, hAn, fun hfd => ?_⟩
  set F : Pot δ → ℝ := fun w => Ldj δ j α (schr w.toFun) with hF
  have hFd : HasFDerivAt F (0 : Pot δ →L[ℝ] ℝ) vstar := by
    have := (hAn vstar hmem).differentiableAt.hasFDerivAt
    rw [hfd] at this; exact this
  -- frames at small heights
  set δ₁ := min δ₀ δ with hδ₁
  have hδ₁pos : 0 < δ₁ := lt_min hδ₀ hδ
  have hyr : ∀ y ∈ Ioo 0 δ₁, y ∈ Ioo 0 δ₀ ∧ y ∈ Ioo 0 δ := fun y hy =>
    ⟨⟨hy.1, lt_of_lt_of_le hy.2 (min_le_left _ _)⟩,
      ⟨hy.1, lt_of_lt_of_le hy.2 (min_le_right _ _)⟩⟩
  have hfr : ∀ y : ℝ, ∃ B : ℝ → M2, y ∈ Ioo 0 δ₁ →
      (Continuous B ∧ Function.Periodic B 1 ∧ (∀ x, (B x).det = 1) ∧
        (∀ x, ((B (x + α))⁻¹ * shift (schr v) y x * B x) 0 1 = 0 ∧
          ((B (x + α))⁻¹ * shift (schr v) y x * B x) 1 0 = 0) ∧
        (∃ n : ℕ, 1 ≤ n ∧ ∀ x, ‖B x *ᵥ ![1, 0]‖ <
          ‖iter α (shift (schr v) y) n x *ᵥ (B x *ᵥ ![1, 0])‖)) := by
    intro y
    by_cases hy : y ∈ Ioo 0 δ₁
    · have h := (hU y (hyr y hy).1).1
      have e : shift (cshift (schr v) y) 0 = shift (schr v) y := by
        rw [shift_cshift, zero_add]
      unfold UH at h; rw [e] at h
      obtain ⟨B, hB⟩ := exists_frame_of_isUH h
      exact ⟨B, fun _ => hB⟩
    · exact ⟨fun _ => 1, fun h => absurd h hy⟩
  choose Bf hBf using hfr
  have hQc : ∀ y ∈ Ioo 0 δ₁, ∀ i : Fin 3, Continuous fun x => derivCoeffs (Bf y x) i :=
    fun y hy i => continuous_derivCoeffs (hBf y hy).1 i
  have hQp : ∀ y ∈ Ioo 0 δ₁, ∀ i : Fin 3,
      Function.Periodic (fun x => derivCoeffs (Bf y x) i) 1 :=
    fun y hy i x => by simp only [(hBf y hy).2.1 x]
  -- the derivative along `g` at height `y`
  have hder : ∀ y ∈ Ioo 0 δ₁, ∀ g : ℂ → ℂ, DifferentiableOn ℂ g (strip δ) →
      (∀ z, g (z + 1) = g z) →
      HasDerivAt (fun t : ℝ => Ldj δ j α (schr (fun z => v z + t * g z)))
        (∫ x in (0 : ℝ)..1, (derivCoeffs (Bf y x) 2 * (-g (x + y * I))).re) 0 := by
    intro y hy g hg hgp
    obtain ⟨h1, h2, h3, h4, h5⟩ := hBf y hy
    exact deriv_at_height hD hv (hyr y hy).2 (hU y (hyr y hy).1).1 (hU y (hyr y hy).1).2
      h1 h2 h3 h4 h5 hg hgp
  -- Fourier coefficients of `q₃` along `Im z = y`
  set K : ℝ → ℤ → ℂ := fun y m => fcoef (fun z => derivCoeffs (Bf y z.re) 2) m y with hK
  have hKeq : ∀ y m, K y m =
      ∫ x in (0 : ℝ)..1, derivCoeffs (Bf y x) 2 * eC (-(m * (x + y * I))) := fun y m =>
    fcoef_re_eq (fun x => derivCoeffs (Bf y x) 2) m y
  have hint : ∀ y ∈ Ioo 0 δ₁, ∀ m : ℤ, IntervalIntegrable
      (fun x : ℝ => derivCoeffs (Bf y x) 2 * eC (-(m * (x + y * I)))) MeasureTheory.volume 0 1 :=
    fun y hy m => ((hQc y hy 2).mul (continuous_line_eC m y)).intervalIntegrable 0 1
  -- linear combinations of two modes
  have hlin : ∀ y ∈ Ioo 0 δ₁, ∀ (a b : ℂ) (m : ℤ),
      (∫ x in (0 : ℝ)..1, (derivCoeffs (Bf y x) 2 * (-(a * eC (-(m * (x + y * I))) +
        b * eC (-(((-m : ℤ) : ℂ) * (x + y * I)))))).re) = -(a * K y m + b * K y (-m)).re := by
    intro y hy a b m
    have hpt : ∀ x : ℝ, (derivCoeffs (Bf y x) 2 * (-(a * eC (-(m * (x + y * I))) +
        b * eC (-(((-m : ℤ) : ℂ) * (x + y * I)))))).re =
        (-(a * (derivCoeffs (Bf y x) 2 * eC (-(m * (x + y * I)))) +
          b * (derivCoeffs (Bf y x) 2 * eC (-(((-m : ℤ) : ℂ) * (x + y * I)))))).re := by
      intro x; congr 1; ring
    simp_rw [hpt]
    rw [iInt_re (by
      exact (((hint y hy m).const_mul a).add ((hint y hy (-m)).const_mul b)).neg)]
    rw [intervalIntegral.integral_neg, intervalIntegral.integral_add
      ((hint y hy m).const_mul a) ((hint y hy (-m)).const_mul b),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hKeq, hKeq]
    exact Complex.neg_re _
  -- constancy in `y`
  have hKconst : ∀ y ∈ Ioo 0 δ₁, ∀ y' ∈ Ioo 0 δ₁, ∀ m : ℤ, K y m = K y' m := by
    intro y hy y' hy' m
    have hval : ∀ (c : ℂ), (∫ x in (0 : ℝ)..1, (derivCoeffs (Bf y x) 2 *
        (-(c * eC (-(m * ((x : ℂ) + y * I)))))).re) =
        ∫ x in (0 : ℝ)..1, (derivCoeffs (Bf y' x) 2 *
          (-(c * eC (-(m * ((x : ℂ) + y' * I)))))).re := by
      intro c
      have hgd : DifferentiableOn ℂ (fun z => c * eC (-(m * z))) (strip δ) :=
        ((differentiable_eC.comp (differentiable_id.const_mul _).neg).const_mul
          _).differentiableOn
      have hgp : ∀ z, c * eC (-(m * (z + 1))) = c * eC (-(m * z)) := fun z => by
        rw [eC_neg_periodic]
      exact (hder y hy _ hgd hgp).unique (hder y' hy' _ hgd hgp)
    have e : ∀ (y : ℝ), y ∈ Ioo 0 δ₁ → ∀ c : ℂ, (∫ x in (0 : ℝ)..1,
        (derivCoeffs (Bf y x) 2 * (-(c * eC (-(m * ((x : ℂ) + y * I)))))).re) =
        -(c * K y m).re := by
      intro y hy c
      have := hlin y hy c 0 m
      simpa using this
    have h1 := hval 1
    have h2 := hval I
    rw [e y hy, e y' hy'] at h1 h2
    simp only [one_mul, neg_inj] at h1
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub,
      neg_neg] at h2
    exact Complex.ext h1 h2
  -- the vanishing derivative along real potentials
  have hzero : ∀ y ∈ Ioo 0 δ₁, ∀ p : Pot δ,
      (∫ x in (0 : ℝ)..1, (derivCoeffs (Bf y x) 2 * (-p.toFun (x + y * I))).re) = 0 := by
    intro y hy p
    have hp := p.isRealAnalyticPotential hδ
    have h1 := hder y hy p.toFun hp.holo hp.periodic
    have hline : HasDerivAt (fun t : ℝ => vstar + t • p) p 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const p).const_add vstar
    have h2 := HasFDerivAt.comp_hasDerivAt (0 : ℝ)
      (by rw [zero_smul, add_zero]; exact hFd : HasFDerivAt F 0 (vstar + (0 : ℝ) • p)) hline
    have hfun : (fun t : ℝ => Ldj δ j α (schr (fun z => v z + t * p.toFun z))) =
        F ∘ fun t : ℝ => vstar + t • p := by
      funext t
      simp only [hF, Function.comp_apply]
      congr 2
      rw [Pot.toFun_add, Pot.toFun_smul]
      rfl
    rw [hfun] at h1
    have := h1.unique h2
    simpa using this
  -- the symmetry of the coefficients
  set y₀ := δ₁ / 2 with hy₀
  have hy₀mem : y₀ ∈ Ioo 0 δ₁ := ⟨by linarith, by linarith⟩
  set C : ℤ → ℂ := fun m => K y₀ m with hC
  have hsym : ∀ m : ℤ, C m = -conj (C (-m)) := by
    intro m
    have hreal : ∀ x : ℝ, conj (eC (-(m * x))) = eC (-(((-m : ℤ) : ℂ) * x)) := by
      intro x
      rw [show (-((m : ℂ) * x)) = ((-(m * x) : ℝ) : ℂ) by push_cast; ring, conj_eC_real]
      push_cast; ring_nf
    have hx : ∀ x : ℝ, ((x : ℂ) + y₀ * I) ∈ cstrip δ := fun x =>
      strip_sub_cstrip (mem_strip_shift (by
        rw [abs_of_pos hy₀mem.1]; exact (hyr y₀ hy₀mem).2.2) x)
    have hde : ∀ (c : ℂ) (k : ℤ), Differentiable ℂ (fun z : ℂ => c * eC (-(k * z))) :=
      fun c k => (differentiable_eC.comp ((differentiable_id.const_mul (k : ℂ)).neg)).const_mul c
    obtain ⟨pc, hpc⟩ := exists_pot_of_entire (δ := δ)
      (fun z => 1 * eC (-(m * z)) + 1 * eC (-(((-m : ℤ) : ℂ) * z)))
      ((hde 1 m).add (hde 1 (-m)))
      (fun z => by rw [eC_neg_periodic, eC_neg_periodic])
      (fun x => by rw [← hreal x]; simp)
    obtain ⟨ps, hps⟩ := exists_pot_of_entire (δ := δ)
      (fun z => I * eC (-(m * z)) + (-I) * eC (-(((-m : ℤ) : ℂ) * z)))
      ((hde I m).add (hde (-I) (-m)))
      (fun z => by rw [eC_neg_periodic, eC_neg_periodic])
      (fun x => by rw [← hreal x]; simp [Complex.mul_im])
    have e1 := hzero y₀ hy₀mem pc
    have e2 := hzero y₀ hy₀mem ps
    rw [intervalIntegral.integral_congr (g := fun x : ℝ => (derivCoeffs (Bf y₀ x) 2 *
      (-(1 * eC (-(m * ((x : ℂ) + y₀ * I))) +
        1 * eC (-(((-m : ℤ) : ℂ) * ((x : ℂ) + y₀ * I)))))).re)
      (fun x _ => by simp only [hpc _ (hx x)]), hlin y₀ hy₀mem] at e1
    rw [intervalIntegral.integral_congr (g := fun x : ℝ => (derivCoeffs (Bf y₀ x) 2 *
      (-(I * eC (-(m * ((x : ℂ) + y₀ * I))) +
        (-I) * eC (-(((-m : ℤ) : ℂ) * ((x : ℂ) + y₀ * I)))))).re)
      (fun x _ => by simp only [hps _ (hx x)]), hlin y₀ hy₀mem] at e2
    simp only [one_mul, Complex.neg_re, Complex.add_re, neg_eq_zero] at e1
    simp only [Complex.neg_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.neg_im, zero_mul, one_mul, neg_mul, zero_sub, neg_neg, neg_zero, sub_neg_eq_add,
      neg_eq_zero] at e2
    apply Complex.ext
    · simp only [hC, Complex.neg_re, Complex.conj_re]; linarith
    · simp only [hC, Complex.neg_im, Complex.conj_im, neg_neg]; linarith
  -- bounds
  have hbound : ∀ y ∈ Ioo 0 δ₁, ∀ i : Fin 3, ∃ M, ∀ x, ‖derivCoeffs (Bf y x) i‖ ≤ M :=
    fun y hy i => bound_of_periodic (hQc y hy i) (hQp y hy i)
  obtain ⟨M₃, hM₃⟩ := hbound y₀ hy₀mem 2
  have hC3 : ∀ m : ℤ, ‖C m‖ ≤ M₃ * Real.exp (-2 * Real.pi * |(m : ℝ)| * y₀) := by
    refine decay_of_sym (fun m => ?_) hsym
    exact norm_fcoef_le m y₀ M₃ (fun x => by simpa using hM₃ x)
  set Φ₃ : ℂ → ℂ := fser C with hΦ₃
  have hy₀pos : 0 < y₀ := hy₀mem.1
  have hy₀δ : y₀ ≤ δ := by
    have := min_le_right δ₀ δ; rw [hy₀]; linarith
  have hsub : ∀ y ∈ Ioo 0 y₀, y ∈ Ioo 0 δ₁ := fun y hy => ⟨hy.1, by linarith [hy.2]⟩
  have hQ3 : ∀ y ∈ Ioo 0 y₀, ∀ x : ℝ, derivCoeffs (Bf y x) 2 = Φ₃ (x + y * I) := by
    intro y hy x
    refine eq_fser hC3 (hQc y (hsub y hy) 2) (hQp y (hsub y hy) 2)
      (by rw [abs_of_pos hy.1]; exact hy.2) (fun m => ?_) x
    rw [← hKeq, hKconst y (hsub y hy) y₀ hy₀mem m]
  set Φ₂ : ℂ → ℂ := fun z => -Φ₃ (z - α) with hΦ₂
  have hQ2 : ∀ y ∈ Ioo 0 y₀, ∀ x : ℝ, derivCoeffs (Bf y x) 1 = Φ₂ (x + y * I) := by
    intro y hy x
    obtain ⟨-, -, hdet, hdiag, -⟩ := hBf y (hsub y hy)
    have h := hdiag (x - α)
    rw [sub_add_cancel] at h
    rw [schr_coeff_symm (v := v (((x - α : ℝ) : ℂ) + y * I)) (hdet (x - α)) (hdet x) h,
      hQ3 y hy (x - α)]
    simp only [hΦ₂]
    congr 2
    push_cast; ring
  have hI2h : ∀ y ∈ Ioo 0 δ₁, ∀ x : ℝ, derivCoeffs (Bf y (x + α)) 0 =
      -derivCoeffs (Bf y x) 0 - 2 * v (x + y * I) * derivCoeffs (Bf y x) 2 := by
    intro y hy x
    obtain ⟨-, -, hdet, hdiag, -⟩ := hBf y hy
    exact coeff_I2 (v := v (x + y * I)) (hdet x) (hdet (x + α)) (hdiag x)
  have hI3h : ∀ y ∈ Ioo 0 δ₁, ∀ x : ℝ, derivCoeffs (Bf y x) 0 ^ 2 +
      4 * derivCoeffs (Bf y x) 1 * derivCoeffs (Bf y x) 2 = 1 :=
    fun y hy x => coeff_I3 ((hBf y hy).2.2.1 x)
  -- the coefficient `q₁`
  have hΦ₃d : DifferentiableOn ℂ Φ₃ (strip y₀) := fser_differentiableOn hC3
  set E : ℤ → ℂ := fun m => fcoef (fun z => v z * Φ₃ z) m 0 with hE
  have hvΦd : DifferentiableOn ℂ (fun z => v z * Φ₃ z) (strip y₀) :=
    (hv.holo.mono (strip_mono hy₀δ)).mul hΦ₃d
  have hvΦp : ∀ z, v (z + 1) * Φ₃ (z + 1) = v z * Φ₃ z := fun z => by
    rw [hv.periodic, hΦ₃, fser_periodic]
  set K1 : ℝ → ℤ → ℂ := fun y m => fcoef (fun z => derivCoeffs (Bf y z.re) 0) m y with hK1
  set C1 : ℤ → ℂ := fun m => -2 * E m / (1 + eC (m * α)) with hC1
  have hK1C : ∀ y ∈ Ioo 0 y₀, ∀ m : ℤ, K1 y m = C1 m := by
    intro y hy m
    have hy1 := hsub y hy
    have hyabs : |y| < y₀ := by rw [abs_of_pos hy.1]; exact hy.2
    set h : ℝ → ℂ := fun x => derivCoeffs (Bf y x) 0 * eC (-(m * ((x : ℂ) - α + y * I)))
      with hh
    have hhp : Function.Periodic h 1 := fun x => by
      simp only [hh]
      rw [show Bf y (x + 1) = Bf y x from (hBf y hy1).2.1 x]
      congr 1
      push_cast
      rw [show (x : ℂ) + 1 - α + y * I = ((x : ℂ) - α + y * I) + 1 by ring, eC_neg_periodic]
    have hshift : ∫ x in (0 : ℝ)..1, h (x + α) = ∫ x in (0 : ℝ)..1, h x := by
      rw [intervalIntegral.integral_comp_add_right h α, zero_add, add_comm (1 : ℝ) α]
      have := hhp.intervalIntegral_add_eq α 0
      rwa [zero_add] at this
    have hL : ∫ x in (0 : ℝ)..1, h (x + α) = ∫ x in (0 : ℝ)..1,
        (-(derivCoeffs (Bf y x) 0 * eC (-(m * ((x : ℂ) + y * I)))) -
          2 * (v ((x : ℂ) + y * I) * Φ₃ ((x : ℂ) + y * I) * eC (-(m * ((x : ℂ) + y * I))))) := by
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [hh]
      rw [hI2h y hy1 x, hQ3 y hy x]
      push_cast
      rw [show ((x : ℂ) + α - α + y * I) = (x : ℂ) + y * I by ring]
      ring
    have hK1e : K1 y m = ∫ x in (0 : ℝ)..1, derivCoeffs (Bf y x) 0 * eC (-(m * (x + y * I))) :=
      fcoef_re_eq (fun x => derivCoeffs (Bf y x) 0) m y
    have hR : ∫ x in (0 : ℝ)..1, h x = eC (m * α) * K1 y m := by
      rw [hK1e, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [hh]
      rw [show -((m : ℂ) * ((x : ℂ) - α + y * I)) = -(m * ((x : ℂ) + y * I)) + m * α by ring,
        eC_add]
      ring
    have hEy : fcoef (fun z => v z * Φ₃ z) m y = E m :=
      fcoef_indep hvΦd hvΦp m hyabs (by rw [abs_zero]; exact hy₀pos)
    have i1 : IntervalIntegrable (fun x : ℝ => derivCoeffs (Bf y x) 0 *
        eC (-(m * ((x : ℂ) + y * I)))) MeasureTheory.volume 0 1 :=
      ((hQc y hy1 0).mul (continuous_line_eC m y)).intervalIntegrable 0 1
    have i2 : IntervalIntegrable (fun x : ℝ => v ((x : ℂ) + y * I) * Φ₃ ((x : ℂ) + y * I) *
        eC (-(m * ((x : ℂ) + y * I)))) MeasureTheory.volume 0 1 :=
      ((hvΦd.continuousOn.comp_continuous (by fun_prop)
        (fun x => mem_strip_shift hyabs x)).mul (continuous_line_eC m y)).intervalIntegrable 0 1
    have hsplit := intervalIntegral.integral_sub (μ := MeasureTheory.volume) (a := 0) (b := 1)
      (f := fun x : ℝ => -(derivCoeffs (Bf y x) 0 * eC (-(m * ((x : ℂ) + y * I)))))
      (g := fun x : ℝ => 2 * (v ((x : ℂ) + y * I) * Φ₃ ((x : ℂ) + y * I) *
        eC (-(m * ((x : ℂ) + y * I))))) i1.neg (i2.const_mul 2)
    have key : eC (m * α) * K1 y m = -K1 y m - 2 * E m := by
      rw [← hR, ← hshift, hL, hsplit, intervalIntegral.integral_neg,
        intervalIntegral.integral_const_mul, ← hEy, hK1e]
      rfl
    have hne := one_add_eC_ne_zero hα m
    simp only [hC1]
    rw [eq_div_iff hne]
    linear_combination key
  have hEsym : ∀ m : ℤ, conj (E m) = -E (-m) := by
    intro m
    simp only [hE, fcoef]
    rw [← iInt_conj, ← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [ofReal_zero, zero_mul, add_zero]
    have hvx : conj (v x) = v x := Complex.conj_eq_iff_im.2 (hv.real x)
    have hΦx : conj (Φ₃ x) = -Φ₃ x := by
      have := fser_re_zero hy₀pos hC3 hsym x
      apply Complex.ext <;> simp [hΦ₃, this]
    rw [map_mul, map_mul, hvx, hΦx,
      show (-((m : ℂ) * x)) = ((-(m * x) : ℝ) : ℂ) by push_cast; ring, conj_eC_real]
    push_cast
    ring_nf
  have hC1sym : ∀ m : ℤ, C1 m = -conj (C1 (-m)) := by
    intro m
    have h1 : conj (E (-m)) = -E m := by rw [hEsym (-m), neg_neg]
    have h2 : conj (eC (((-m : ℤ) : ℂ) * α)) = eC (m * α) := by
      rw [show (((-m : ℤ) : ℂ) * α) = (((-m : ℤ) * α : ℝ) : ℂ) by push_cast; ring,
        conj_eC_real]
      congr 1; push_cast; ring
    have h3 : conj (2 : ℂ) = 2 := map_ofNat _ 2
    simp only [hC1, map_div₀, map_mul, map_add, map_one, map_neg, h1, h2, h3]
    ring
  set y₂ := y₀ / 2 with hy₂
  have hy₂pos : 0 < y₂ := by rw [hy₂]; linarith
  have hy₂mem : y₂ ∈ Ioo 0 y₀ := ⟨hy₂pos, by rw [hy₂]; linarith⟩
  obtain ⟨M₁, hM₁⟩ := hbound y₂ (hsub y₂ hy₂mem) 0
  have hC1b : ∀ m : ℤ, ‖C1 m‖ ≤ M₁ * Real.exp (-2 * Real.pi * |(m : ℝ)| * y₂) := by
    refine decay_of_sym (fun m => ?_) hC1sym
    rw [← hK1C y₂ hy₂mem m]
    exact norm_fcoef_le m y₂ M₁ (fun x => by simpa using hM₁ x)
  set Φ₁ : ℂ → ℂ := fser C1 with hΦ₁
  have hQ1 : ∀ y ∈ Ioo 0 y₂, ∀ x : ℝ, derivCoeffs (Bf y x) 0 = Φ₁ (x + y * I) := by
    intro y hy x
    have hy0 : y ∈ Ioo 0 y₀ := ⟨hy.1, by linarith [hy.2]⟩
    refine eq_fser hC1b (hQc y (hsub y hy0) 0) (hQp y (hsub y hy0) 0)
      (by rw [abs_of_pos hy.1]; exact hy.2) (fun m => ?_) x
    rw [← fcoef_re_eq]
    exact hK1C y hy0 m
  -- the endgame
  have hy₂y₀ : y₂ ≤ y₀ := by rw [hy₂]; linarith
  have hd₃ : DifferentiableOn ℂ Φ₃ (strip y₂) := hΦ₃d.mono (strip_mono hy₂y₀)
  have hd₂ : DifferentiableOn ℂ Φ₂ (strip y₂) := by
    have : DifferentiableOn ℂ (fun z => Φ₃ (z - α)) (strip y₂) :=
      hd₃.comp (differentiableOn_id.sub_const _) (fun z hz => by simpa [strip] using hz)
    exact this.neg
  have hd₁ : DifferentiableOn ℂ Φ₁ (strip y₂) := fser_differentiableOn hC1b
  have hr₃ : ∀ x : ℝ, (Φ₃ x).re = 0 := fser_re_zero hy₀pos hC3 hsym
  obtain ⟨y₃, hy₃, c, hc⟩ := L_const_of_ext hα hv hy₂pos (hy₂y₀.trans hy₀δ) hd₁ hd₂ hd₃
    (fser_periodic C1)
    (fun z => by
      simp only [hΦ₂]; rw [show z + 1 - (α : ℂ) = (z - α) + 1 by ring, hΦ₃, fser_periodic])
    (fser_periodic C) (fser_re_zero hy₂pos hC1b hC1sym)
    (fun x => by
      simp only [hΦ₂]
      rw [show (x : ℂ) - α = ((x - α : ℝ) : ℂ) by push_cast; ring, Complex.neg_re, hr₃,
        neg_zero])
    hr₃
    (fun z _ _ => by simp only [hΦ₂, add_sub_cancel_right])
    (fun z h1 h2 => by
      have hy : z.im ∈ Ioo 0 y₂ := ⟨h1, h2⟩
      have hy0 : z.im ∈ Ioo 0 y₀ := ⟨h1, by linarith⟩
      have hz : z = (z.re : ℂ) + z.im * I := (re_add_im z).symm
      have hzα : z + (α : ℂ) = ((z.re + α : ℝ) : ℂ) + z.im * I := by
        conv_lhs => rw [hz]
        push_cast; ring
      rw [hzα, ← hQ1 _ hy, hI2h _ (hsub _ hy0), hQ1 _ hy, hQ3 _ hy0, ← hz])
    (fun z h1 h2 => by
      have hy : z.im ∈ Ioo 0 y₂ := ⟨h1, h2⟩
      have hy0 : z.im ∈ Ioo 0 y₀ := ⟨h1, by linarith⟩
      have hz : z = (z.re : ℂ) + z.im * I := (re_add_im z).symm
      rw [hz, ← hQ1 _ hy, ← hQ2 _ hy0, ← hQ3 _ hy0]
      exact hI3h _ (hsub _ hy0) _)
  -- contradiction with `ω = j > 0`
  obtain ⟨η, hη, haff⟩ := L_piecewise_affine hA hα (ε := 0) (by simpa using hδ)
  rw [cshift_zero, hacc] at haff
  set t := min η y₃ with ht
  have htpos : 0 < t := lt_min hη hy₃
  have ht1 := haff (t / 2) ⟨by linarith, by linarith [min_le_left η y₃]⟩
  have ht2 := haff (t / 4) ⟨by linarith, by linarith [min_le_left η y₃]⟩
  have hc1 := hc (t / 2) ⟨by linarith, by linarith [min_le_right η y₃]⟩
  have hc2 := hc (t / 4) ⟨by linarith, by linarith [min_le_right η y₃]⟩
  have hjr : (j : ℝ) ≠ 0 := by exact_mod_cast hj0
  have : 2 * Real.pi * (j : ℝ) * (t / 4) = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · rcases mul_eq_zero.1 h with h' | h'
    · linarith [Real.pi_pos]
    · exact hjr h'
  · linarith

/-- **Theorem `cod1`.** -/
theorem cod1 {δ α : ℝ} : Cod1Claim δ α := cod1_proof derivFormula_proof

/-- **Theorem `cod`.**  For irrational `α`, the set of `(v, E) ∈ C^ω_δ(ℝ/ℤ, ℝ) × ℝ` such that `E`
is a critical energy of `H_{α,v}` is contained in a countable union of codimension-one analytic
submanifolds. -/
theorem cod {δ : ℝ} (hδ : 0 < δ) {α : ℝ} (hα : Irrational α) :
    ∃ S : ℕ → Set (Pot δ × ℝ), (∀ i, IsAnalyticHypersurface (S i)) ∧
      {p : Pot δ × ℝ | IsCriticalEnergy α p.1.toFun p.2} ⊆ ⋃ i, S i :=
  cod_of_cod1 hδ hα cod1

end AvilaGlobal
