/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Appendix A.3: Fourier decay of subharmonic functions   (book pp. 418–422)

## Main definitions and results

* `DF.ex x = e^{2πix}` and `DF.circleCoeff u k = ∫₀¹ e^{-2πikt} u(e^{2πit}) dt`, the Fourier
  coefficients of (the restriction to `∂𝔻` of) a function `u : ℂ → ℝ`.
* `DF.integral_ex_int` — orthogonality of the exponentials on `[0, 1]`.
* `DF.circleCoeff_log_one_sub` — the Fourier coefficients of `log |1 - w e^{2πix}|` for
  `|w| < 1` (computed from the Taylor series of `log (1 - z)`).
* `DF.conjugatePoissonStatement_holds` — Fourier coefficients of the Poisson and conjugate
  Poisson kernels (the claim `H P_r = Q_r` of Theorem A.1.2; see `Fourier.lean`).
* `DF.norm_circleCoeff_log_le` — **Lemma A.3.5**: for every `ξ ∈ ℂ` and `k ≠ 0`,
  the Fourier coefficients of `u_ξ(x) = log |e^{2πix} - ξ|` satisfy `|û_ξ(k)| ≤ 1/(2|k|)`.
  (The book's proof goes through the Hilbert transform; we compute the coefficients
  explicitly for `|ξ| ≠ 1` and pass to the limit `rξ → ξ` for `|ξ| = 1`.)

## Statements (proved in later files)

* `RieszRepresentationStatement` — Theorem A.3.2 (cited by the book); proved as
  `DF.rieszRepresentationStatement_holds` in `DamanikFillman/AppA/RieszRepresentation.lean`;
* `RieszMeasureBoundStatement` — Theorem A.3.4 (cited by the book); proved as
  `DF.rieszMeasureBoundStatement_holds` in `DamanikFillman/AppA/RieszBound.lean`;
* `SubharmonicFourierDecayStatement` — Theorem A.3.1; proved as
  `DF.subharmonicFourierDecayStatement_holds` in `DamanikFillman/AppA/SubharmonicFourier.lean`
  (from A.3.2, A.3.4, Lemma A.3.5 and Cauchy estimates for harmonic functions).
-/
import DamanikFillman.AppA.Potential
import DamanikFillman.AppA.Fourier
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

open Real Complex Metric Set Filter Topology MeasureTheory
open scoped ComplexConjugate Interval

namespace DF

/-! ### Exponentials on `[0,1]` -/

/-- `e(x) = e^{2πix}`. -/
def ex (x : ℝ) : ℂ := Complex.exp (2 * π * I * x)

lemma norm_ex (x : ℝ) : ‖ex x‖ = 1 := by
  unfold ex
  rw [Complex.norm_exp]
  simp

lemma ex_ne_zero (x : ℝ) : ex x ≠ 0 := Complex.exp_ne_zero _

lemma ex_add (x y : ℝ) : ex (x + y) = ex x * ex y := by
  unfold ex; rw [← Complex.exp_add]; push_cast; ring_nf

lemma ex_neg (x : ℝ) : ex (-x) = conj (ex x) := by
  unfold ex
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

lemma ex_pow (x : ℝ) (n : ℕ) : ex x ^ n = ex (n * x) := by
  unfold ex
  rw [← Complex.exp_nat_mul]
  push_cast; ring_nf

lemma continuous_ex : Continuous ex := by
  unfold ex; fun_prop

/-- Orthogonality: `∫₀¹ e^{2πimx} dx = δ_{m,0}`. -/
lemma integral_ex_int (m : ℤ) : ∫ x in (0 : ℝ)..1, ex (m * x) = if m = 0 then 1 else 0 := by
  by_cases hm : m = 0
  · subst hm; simp [ex]
  · rw [ite_eq_right_iff.2 (fun h => absurd h hm)]
    have hc : (2 * π * I * m : ℂ) ≠ 0 := by
      have : (m : ℂ) ≠ 0 := Int.cast_ne_zero.2 hm
      simp [Real.pi_ne_zero, I_ne_zero, this]
    have e : ∀ x : ℝ, ex (m * x) = Complex.exp ((2 * π * I * m : ℂ) * x) := by
      intro x; unfold ex; push_cast; ring_nf
    simp_rw [e]
    rw [integral_exp_mul_complex hc]
    have : Complex.exp ((2 * π * I * m : ℂ) * ((1 : ℝ) : ℂ)) = 1 := by
      rw [← exp_int_mul_two_pi_mul_I m]; push_cast; ring_nf
    rw [this]
    simp

/-! ### Fourier coefficients on the unit circle -/

/-- Fourier coefficients of (the restriction to the unit circle of) `u : ℂ → ℝ`:
`û(k) = ∫₀¹ e^{-2πikt} u(e^{2πit}) dt`. -/
def circleCoeff (u : ℂ → ℝ) (k : ℤ) : ℂ :=
  ∫ t in (0 : ℝ)..1, ex (-(k * t)) * (u (ex t) : ℂ)

/-- The Fourier coefficients of `log |1 - w e(x)|`, `|w| < 1`, from the Taylor series of
`log (1 - z)`. -/
theorem integral_log_one_sub {w : ℂ} (hw : ‖w‖ < 1) {k : ℤ} (hk : k ≠ 0) :
    ∫ x in (0 : ℝ)..1, ex (-(k * x)) * ((Real.log ‖1 - w * ex x‖ : ℝ) : ℂ) =
      -(1 / 2) * ((if 0 < k then w ^ k.natAbs else conj w ^ k.natAbs) / k.natAbs) := by
  set F : ℕ → ℝ → ℂ := fun n x =>
    ex (-(k * x)) * (-(1 / 2) * ((w * ex x) ^ n / n + conj ((w * ex x) ^ n / n))) with hF
  have hsum : ∀ x : ℝ, HasSum (fun n => F n x)
      (ex (-(k * x)) * ((Real.log ‖1 - w * ex x‖ : ℝ) : ℂ)) := by
    intro x
    have hz : ‖w * ex x‖ < 1 := by rw [norm_mul, norm_ex, mul_one]; exact hw
    have h1 := hasSum_taylorSeries_neg_log hz
    have h2 := h1.add (Complex.hasSum_conj'.2 h1)
    have h3 := (h2.mul_left (-(1 / 2))).mul_left (ex (-(k * x)))
    convert h3 using 1
    rw [Complex.add_conj, Complex.neg_re, Complex.log_re]
    push_cast
    ring
  have hint : HasSum (fun n => ∫ x in (0 : ℝ)..1, F n x)
      (∫ x in (0 : ℝ)..1, ex (-(k * x)) * ((Real.log ‖1 - w * ex x‖ : ℝ) : ℂ)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun n _ => ‖w‖ ^ n)
      (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      simp only [hF]
      have := continuous_ex
      fun_prop
    · refine Eventually.of_forall fun x _ => ?_
      simp only [hF, norm_mul]
      rw [norm_ex, one_mul]
      have ha : ‖(w * ex x) ^ n / (n : ℂ)‖ ≤ ‖w‖ ^ n := by
        rw [norm_div, norm_pow, norm_mul, norm_ex, mul_one]
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp
        · rw [Complex.norm_natCast]
          exact div_le_self (by positivity) (by exact_mod_cast hn)
      calc ‖(-(1 / 2) : ℂ)‖ * ‖(w * ex x) ^ n / n + conj ((w * ex x) ^ n / n)‖
          ≤ (1 / 2) * (‖(w * ex x) ^ n / (n : ℂ)‖ + ‖(w * ex x) ^ n / (n : ℂ)‖) := by
            gcongr
            · simp
            · exact (norm_add_le _ _).trans (by rw [Complex.norm_conj])
        _ ≤ ‖w‖ ^ n := by linarith
    · exact Eventually.of_forall fun x _ => summable_geometric_of_lt_one (norm_nonneg w) hw
    · exact intervalIntegrable_const
    · exact Eventually.of_forall fun x _ => hsum x
  refine hint.unique ?_
  -- compute the integrals of the individual terms
  have hterm : ∀ n : ℕ, ∫ x in (0 : ℝ)..1, F n x =
      -(1 / 2) * (w ^ n / n * (if (n : ℤ) - k = 0 then 1 else 0) +
        conj w ^ n / n * (if -(n : ℤ) - k = 0 then 1 else 0)) := by
    intro n
    have e : ∀ x : ℝ, F n x = -(1 / 2) * (w ^ n / n * ex (((n : ℤ) - k : ℤ) * x) +
        conj w ^ n / n * ex ((-(n : ℤ) - k : ℤ) * x)) := by
      intro x
      have h1 : (w * ex x) ^ n = w ^ n * ex (n * x) := by rw [mul_pow, ex_pow]
      have h2 : conj ((w * ex x) ^ n / (n : ℂ)) = conj w ^ n * ex (-(n * x)) / n := by
        rw [map_div₀, map_natCast, h1, map_mul, map_pow, ← ex_neg]
      have e1 : ex (-(k * x)) * ex (n * x) = ex (((n : ℤ) - k : ℤ) * x) := by
        rw [← ex_add]; congr 1; push_cast; ring
      have e2 : ex (-(k * x)) * ex (-(n * x)) = ex ((-(n : ℤ) - k : ℤ) * x) := by
        rw [← ex_add]; congr 1; push_cast; ring
      simp only [hF]
      rw [h2, h1, ← e1, ← e2]; ring
    simp_rw [e]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_ex_int, integral_ex_int]
    · exact (continuous_const.mul (continuous_ex.comp (continuous_const.mul
        continuous_id))).intervalIntegrable _ _
    · exact (continuous_const.mul (continuous_ex.comp (continuous_const.mul
        continuous_id))).intervalIntegrable _ _
  simp_rw [hterm]
  set n₀ := k.natAbs with hn₀
  have hn₀pos : n₀ ≠ 0 := Int.natAbs_ne_zero.2 hk
  convert hasSum_single n₀ (fun n hn => ?_) using 1
  · rcases lt_or_gt_of_ne hk with h | h
    · have h1 : (n₀ : ℤ) - k ≠ 0 := by omega
      have h2 : -(n₀ : ℤ) - k = 0 := by omega
      simp [h1, h2, not_lt.2 h.le]
    · have h1 : (n₀ : ℤ) - k = 0 := by omega
      have h2 : -(n₀ : ℤ) - k ≠ 0 := by omega
      simp [h1, h2, h]
  · have h1 : (n : ℤ) - k ≠ 0 ∨ n = 0 := by omega
    have h2 : -(n : ℤ) - k ≠ 0 ∨ n = 0 := by omega
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have h1' : (n : ℤ) - k ≠ 0 := by omega
      have h2' : -(n : ℤ) - k ≠ 0 := by omega
      simp [h1', h2']

lemma norm_integral_log_one_sub_le {w : ℂ} (hw : ‖w‖ < 1) {k : ℤ} (hk : k ≠ 0) :
    ‖∫ x in (0 : ℝ)..1, ex (-(k * x)) * ((Real.log ‖1 - w * ex x‖ : ℝ) : ℂ)‖ ≤
      ‖w‖ ^ k.natAbs / (2 * |(k : ℝ)|) := by
  rw [integral_log_one_sub hw hk]
  have hk' : (0 : ℝ) < |(k : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hk)
  have habs : ((k.natAbs : ℕ) : ℝ) = |(k : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  split_ifs <;>
  · rw [norm_mul, norm_div, Complex.norm_natCast, habs, norm_pow]
    try rw [Complex.norm_conj]
    rw [show ‖(-(1 / 2) : ℂ)‖ = 1 / 2 by simp]
    field_simp
    rfl

/-! ### Lemma A.3.5 -/

@[simp] lemma ex_zero : ex 0 = 1 := by simp [ex]

lemma ex_mul_ex_neg (x : ℝ) : ex x * ex (-x) = 1 := by
  rw [← ex_add, add_neg_cancel]; simp [ex]

/-- `|e(x) - ξ| = |1 - ξ̄ e(x)|`. -/
lemma norm_ex_sub_eq (x : ℝ) (ξ : ℂ) : ‖ex x - ξ‖ = ‖1 - conj ξ * ex x‖ := by
  rw [← Complex.norm_conj, map_sub, ← ex_neg]
  have : ex (-x) - conj ξ = ex (-x) * (1 - conj ξ * ex x) := by
    rw [mul_sub, mul_one, mul_left_comm, mul_comm (ex (-x)) (ex x), ex_mul_ex_neg, mul_one]
  rw [this, norm_mul, norm_ex, one_mul]

lemma integral_ex_neg_int {k : ℤ} (hk : k ≠ 0) : ∫ x in (0 : ℝ)..1, ex (-(k * x)) = 0 := by
  have := integral_ex_int (-k)
  rw [ite_eq_right_iff.2 (fun h => absurd h (neg_ne_zero.2 hk))] at this
  rw [← this]
  congr 1; funext x; congr 1; push_cast; ring

/-- Lemma A.3.5 for `|ξ| < 1`. -/
lemma norm_circleCoeff_log_le_of_lt {ξ : ℂ} (hξ : ‖ξ‖ < 1) {k : ℤ} (hk : k ≠ 0) :
    ‖circleCoeff (fun z => Real.log ‖z - ξ‖) k‖ ≤ 1 / (2 * |(k : ℝ)|) := by
  unfold circleCoeff
  simp_rw [norm_ex_sub_eq]
  have hw : ‖conj ξ‖ < 1 := by rwa [Complex.norm_conj]
  refine (norm_integral_log_one_sub_le hw hk).trans ?_
  have hk' : (0 : ℝ) < 2 * |(k : ℝ)| := by
    have := abs_pos.2 (Int.cast_ne_zero (α := ℝ) |>.2 hk); linarith
  gcongr
  exact pow_le_one₀ (norm_nonneg _) hw.le

/-- Lemma A.3.5 for `|ξ| > 1`. -/
lemma norm_circleCoeff_log_le_of_gt {ξ : ℂ} (hξ : 1 < ‖ξ‖) {k : ℤ} (hk : k ≠ 0) :
    ‖circleCoeff (fun z => Real.log ‖z - ξ‖) k‖ ≤ 1 / (2 * |(k : ℝ)|) := by
  have hξ0 : ξ ≠ 0 := by rintro rfl; rw [norm_zero] at hξ; linarith
  have hw : ‖ξ⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hξ
  have hsplit : ∀ x : ℝ, Real.log ‖ex x - ξ‖ = Real.log ‖ξ‖ + Real.log ‖1 - ξ⁻¹ * ex x‖ := by
    intro x
    have hne : 1 - ξ⁻¹ * ex x ≠ 0 := by
      intro h
      have : ‖ξ⁻¹ * ex x‖ = 1 := by rw [← sub_eq_zero.1 h, norm_one]
      rw [norm_mul, norm_ex, mul_one] at this; linarith
    have : ex x - ξ = -ξ * (1 - ξ⁻¹ * ex x) := by
      field_simp; ring
    rw [this, norm_mul, norm_neg, Real.log_mul (norm_ne_zero_iff.2 hξ0) (norm_ne_zero_iff.2 hne)]
  unfold circleCoeff
  simp_rw [hsplit]
  have hcont : Continuous (fun x : ℝ => ex (-(k * x))) :=
    continuous_ex.comp (continuous_const.mul continuous_id).neg
  have hcont2 : Continuous (fun x : ℝ => ex (-(k * x)) * ((Real.log ‖1 - ξ⁻¹ * ex x‖ : ℝ) : ℂ)) := by
    refine hcont.mul (continuous_ofReal.comp ?_)
    refine Continuous.log (continuous_const.sub (continuous_const.mul continuous_ex)).norm
      (fun x => ?_)
    rw [norm_ne_zero_iff, sub_ne_zero]
    intro h
    have : ‖ξ⁻¹ * ex x‖ = 1 := by rw [← h]; simp
    rw [norm_mul, norm_ex, mul_one] at this; linarith
  simp_rw [ofReal_add, mul_add]
  have hc1 : IntervalIntegrable (fun x : ℝ => ex (-(k * x)) * ((Real.log ‖ξ‖ : ℝ) : ℂ))
      volume 0 1 := (hcont.mul continuous_const).intervalIntegrable _ _
  rw [intervalIntegral.integral_add hc1 (hcont2.intervalIntegrable _ _),
    intervalIntegral.integral_mul_const,
    integral_ex_neg_int hk, zero_mul, zero_add]
  refine (norm_integral_log_one_sub_le hw hk).trans ?_
  have hk' : (0 : ℝ) < 2 * |(k : ℝ)| := by
    have := abs_pos.2 (Int.cast_ne_zero (α := ℝ) |>.2 hk); linarith
  gcongr
  exact pow_le_one₀ (norm_nonneg _) hw.le

/-- `|e - rξ| ≥ |e - ξ|/2` for `|e| = |ξ| = 1` and `0 ≤ r`. -/
lemma norm_sub_smul_ge {e ξ : ℂ} (he : ‖e‖ = 1) (hξ : ‖ξ‖ = 1) {r : ℝ} (hr0 : 0 ≤ r) :
    ‖e - ξ‖ / 2 ≤ ‖e - r * ξ‖ := by
  have h1 : e.re ^ 2 + e.im ^ 2 = 1 := by
    have := Complex.sq_norm e; rw [he, Complex.normSq_apply] at this; nlinarith
  have h2 : ξ.re ^ 2 + ξ.im ^ 2 = 1 := by
    have := Complex.sq_norm ξ; rw [hξ, Complex.normSq_apply] at this; nlinarith
  have key : ‖e - ξ‖ ^ 2 ≤ (2 * ‖e - r * ξ‖) ^ 2 := by
    rw [mul_pow, Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, add_zero]
    set p := e.re * ξ.re + e.im * ξ.im with hp
    have hp1 : p ≤ 1 := by nlinarith [sq_nonneg (e.re - ξ.re), sq_nonneg (e.im - ξ.im)]
    have hp2 : -1 ≤ p := by nlinarith [sq_nonneg (e.re + ξ.re), sq_nonneg (e.im + ξ.im)]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + p) (sq_nonneg (r - 1)),
      mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - p) (by positivity : (0 : ℝ) ≤ r ^ 2 + 2 * r)]
  have := (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 key
  linarith

/-- `x ↦ log |e(x) - ξ|` is integrable on `[0, 1]` (cf. Exercise A.3.1). -/
lemma intervalIntegrable_log_norm_ex_sub (ξ : ℂ) :
    IntervalIntegrable (fun x => Real.log ‖ex x - ξ‖) volume 0 1 := by
  have h : CircleIntegrable (fun z => Real.log ‖z - ξ‖) 0 1 :=
    MeromorphicOn.circleIntegrable_log_norm (fun _ _ => by fun_prop)
  have h2 := IntervalIntegrable.comp_mul_left h (c := 2 * π)
  have hpi : (2 * π) ≠ 0 := by positivity
  rw [zero_div, div_self hpi] at h2
  refine h2.congr (fun x _ => ?_)
  have e : circleMap 0 1 (2 * π * x) = ex x := by
    unfold circleMap ex
    simp only [zero_add, Complex.ofReal_one, one_mul]
    congr 1; push_cast; ring
  simp only [e]

lemma ex_injOn {x y : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) (hy : y ∈ Ioc (0 : ℝ) 1) (h : ex x = ex y) :
    x = y := by
  have h1 : ex (x - y) = 1 := by
    rw [sub_eq_add_neg, ex_add, h, ex_mul_ex_neg]
  unfold ex at h1
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h1
  have h2 : ((x - y : ℝ) : ℂ) = n := by
    have h3 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
    apply mul_left_cancel₀ h3
    rw [hn]; ring
  have h4 : x - y = n := by exact_mod_cast h2
  have h5 : (n : ℝ) < 1 := by rw [← h4]; linarith [hx.2, hy.1]
  have h6 : (-1 : ℝ) < n := by rw [← h4]; linarith [hx.1, hy.2]
  have : n = 0 := by
    have : n < 1 := by exact_mod_cast h5
    have : -1 < n := by exact_mod_cast h6
    omega
  rw [this] at h4; simpa [sub_eq_zero] using h4

/-- Lemma A.3.5 for `|ξ| = 1`, by approximation `rξ → ξ`, `r ↑ 1`. -/
lemma norm_circleCoeff_log_le_of_eq {ξ : ℂ} (hξ : ‖ξ‖ = 1) {k : ℤ} (hk : k ≠ 0) :
    ‖circleCoeff (fun z => Real.log ‖z - ξ‖) k‖ ≤ 1 / (2 * |(k : ℝ)|) := by
  set r : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2) with hr
  have hr0 : ∀ n, 0 ≤ r n := fun n => by
    simp only [hr]; rw [sub_nonneg, div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  have hr1 : ∀ n, r n < 1 := fun n => by
    simp only [hr]; linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 2) by positivity]
  have hrlim : Tendsto r atTop (𝓝 1) := by
    have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have h2 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
        refine squeeze_zero (fun n => by positivity) (fun n => ?_) this
        gcongr; linarith
      exact h2
    show Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 2)) atTop (𝓝 1)
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub this
  have hlt : ∀ n, ‖(r n : ℂ) * ξ‖ < 1 := fun n => by
    rw [norm_mul, hξ, mul_one, Complex.norm_real, Real.norm_of_nonneg (hr0 n)]; exact hr1 n
  -- almost every `x ∈ (0,1]` has `e(x) ≠ ξ`
  have hae : ∀ᵐ x ∂(volume : Measure ℝ), x ∈ Ι (0 : ℝ) 1 → ex x ≠ ξ := by
    rw [ae_iff]
    refine Set.Subsingleton.measure_zero ?_ _
    intro x hx y hy
    simp only [uIoc_of_le zero_le_one, not_imp, not_not, mem_ofPred_eq] at hx hy
    exact ex_injOn hx.1 hy.1 (hx.2.trans hy.2.symm)
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have htend : Tendsto (fun n => circleCoeff (fun z => Real.log ‖z - r n * ξ‖) k) atTop
      (𝓝 (circleCoeff (fun z => Real.log ‖z - ξ‖) k)) := by
    unfold circleCoeff
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun x => |Real.log ‖ex x - ξ‖| + Real.log 2) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun n => Measurable.aestronglyMeasurable ?_
      exact (continuous_ex.comp (continuous_const.mul continuous_id).neg).measurable.mul
        (Complex.measurable_ofReal.comp (Real.measurable_log.comp
          (continuous_ex.sub continuous_const).norm.measurable))
    · refine Eventually.of_forall fun n => ?_
      filter_upwards [hae] with x hx hxI
      have hne := hx hxI
      rw [norm_mul, norm_ex, one_mul, Complex.norm_real, Real.norm_eq_abs]
      have hpos : 0 < ‖ex x - ξ‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
      have hlow := norm_sub_smul_ge (norm_ex x) hξ (hr0 n)
      have hup : ‖ex x - r n * ξ‖ ≤ 2 := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_ex, norm_mul, hξ, mul_one, Complex.norm_real, Real.norm_of_nonneg (hr0 n)]
        linarith [hr1 n]
      have hpos' : 0 < ‖ex x - r n * ξ‖ := lt_of_lt_of_le (by positivity) hlow
      have h1 : Real.log ‖ex x - r n * ξ‖ ≤ Real.log 2 := Real.log_le_log hpos' hup
      have h2 : Real.log ‖ex x - ξ‖ - Real.log 2 ≤ Real.log ‖ex x - r n * ξ‖ := by
        rw [← Real.log_div hpos.ne' two_ne_zero]
        exact Real.log_le_log (by positivity) hlow
      rw [abs_le]
      constructor
      · have := neg_abs_le (Real.log ‖ex x - ξ‖); linarith
      · have := abs_nonneg (Real.log ‖ex x - ξ‖); linarith
    · exact (intervalIntegrable_log_norm_ex_sub ξ).abs.add intervalIntegrable_const
    · filter_upwards [hae] with x hx hxI
      have hne := hx hxI
      have h1 : Tendsto (fun n => ex x - (r n : ℂ) * ξ) atTop (𝓝 (ex x - ξ)) := by
        have : Tendsto (fun n => ((r n : ℝ) : ℂ)) atTop (𝓝 ((1 : ℝ) : ℂ)) :=
          (continuous_ofReal.tendsto _).comp hrlim
        simpa using tendsto_const_nhds.sub (this.mul_const ξ)
      have h2 := (h1.norm).log (norm_ne_zero_iff.2 (sub_ne_zero.2 hne))
      exact tendsto_const_nhds.mul ((continuous_ofReal.tendsto _).comp h2)
  refine le_of_tendsto' htend.norm (fun n => ?_)
  exact norm_circleCoeff_log_le_of_lt (hlt n) hk

/-- **Lemma A.3.5**: for every `ξ ∈ ℂ`, the function `u_ξ(x) = log |e^{2πix} - ξ|` has Fourier
coefficients `|û_ξ(k)| ≤ 1/(2|k|)` for all `k ≠ 0`. -/
theorem norm_circleCoeff_log_le (ξ : ℂ) {k : ℤ} (hk : k ≠ 0) :
    ‖circleCoeff (fun z => Real.log ‖z - ξ‖) k‖ ≤ 1 / (2 * |(k : ℝ)|) := by
  rcases lt_trichotomy ‖ξ‖ 1 with h | h | h
  · exact norm_circleCoeff_log_le_of_lt h hk
  · exact norm_circleCoeff_log_le_of_eq h hk
  · exact norm_circleCoeff_log_le_of_gt h hk

/-! ### Riesz representation and Theorem A.3.1 (recorded as statements) -/

/-- The annulus `A_ρ = {1 - ρ < |z| < 1 + ρ}`. -/
def annulus (ρ : ℝ) : Set ℂ := {z | 1 - ρ < ‖z‖ ∧ ‖z‖ < 1 + ρ}

/-- **Theorem A.3.2 (Riesz representation)**, cited by the book: a subharmonic `u : U → ℝ`
admits, on every relatively compact open `U' ⋐ U`, a unique decomposition
`u(z) = ∫_{U'} log |z - ζ| dμ(ζ) + h(z)` with a finite Borel measure `μ` carried by `U'` and
`h` harmonic on `U'`.  (`∫ log |z - ζ| dμ(ζ) = -Φ_μ(z)`.) -/
def RieszRepresentationStatement : Prop :=
  ∀ (U : Set ℂ) (u : ℂ → ℝ), IsOpen U → SubharmonicOn (fun z => (u z : EReal)) U →
    ∀ U' : Set ℂ, IsOpen U' → IsCompact (closure U') → closure U' ⊆ U →
      ∃! μ : Measure ℂ, IsFiniteMeasure μ ∧ μ U'ᶜ = 0 ∧
        ∃ h : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd h U' ∧
          ∀ z ∈ U', (u z : EReal) = -logPotential μ z + (h z : EReal)

/-- **Theorem A.3.4**, cited by the book: for a bounded subharmonic `u` on `A = A_ρ` with Riesz
representation on `A' = A_{ρ/2}`, the Riesz mass and the harmonic part on `A'' = A_{ρ/3}` are
controlled by `‖u‖_{L^∞(A)}`, with a constant depending only on `ρ`. -/
def RieszMeasureBoundStatement : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ C : ℝ, ∀ (u : ℂ → ℝ) (M : ℝ),
    SubharmonicOn (fun z => (u z : EReal)) (annulus ρ) → (∀ z ∈ annulus ρ, |u z| ≤ M) →
    ∀ (μ : Measure ℂ) (h : ℂ → ℝ), IsFiniteMeasure μ → μ (annulus (ρ / 2))ᶜ = 0 →
      InnerProductSpace.HarmonicOnNhd h (annulus (ρ / 2)) →
      (∀ z ∈ annulus (ρ / 2), (u z : EReal) = -logPotential μ z + (h z : EReal)) →
      μ.real univ ≤ C * M ∧ ∀ z ∈ annulus (ρ / 3), |h z| ≤ C * M

/-- **Theorem A.3.1**: bounded subharmonic functions on an annulus `A_ρ` have Fourier
coefficients on the unit circle decaying like `‖u‖_∞ / |k|`, with a constant depending only on
`ρ`.  The book derives it from Theorems A.3.2, A.3.4, Lemma A.3.5 (`norm_circleCoeff_log_le`)
and Cauchy estimates for harmonic functions. -/
def SubharmonicFourierDecayStatement : Prop :=
  ∀ ρ : ℝ, 0 < ρ → ρ < 1 → ∃ C : ℝ, ∀ (u : ℂ → ℝ) (M : ℝ),
    SubharmonicOn (fun z => (u z : EReal)) (annulus ρ) → (∀ z ∈ annulus ρ, |u z| ≤ M) →
    ∀ k : ℤ, k ≠ 0 → ‖circleCoeff u k‖ ≤ C * M / |(k : ℝ)|

/-! ### Fourier coefficients of the Poisson kernels (`ConjugatePoissonStatement`) -/

/-- Termwise integration of a two-sided absolutely convergent trigonometric series. -/
lemma integral_ex_mul_two_sided {a c : ℕ → ℂ} (ha : Summable (fun n => ‖a n‖))
    (hc : Summable (fun n => ‖c n‖)) {G : ℝ → ℂ}
    (hG : ∀ x, HasSum (fun n => a n * ex (n * x) + c n * ex (-(n * x))) (G x)) (k : ℤ) :
    ∫ x in (0 : ℝ)..1, ex (-(k * x)) * G x =
      (if 0 ≤ k then a k.toNat else 0) + (if k ≤ 0 then c (-k).toNat else 0) := by
  set F : ℕ → ℝ → ℂ := fun n x => ex (-(k * x)) * (a n * ex (n * x) + c n * ex (-(n * x)))
    with hF
  have hint : HasSum (fun n => ∫ x in (0 : ℝ)..1, F n x) (∫ x in (0 : ℝ)..1, ex (-(k * x)) * G x) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun n _ => ‖a n‖ + ‖c n‖)
      (fun n => ?_) (fun n => ?_) ?_ ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      simp only [hF]
      have := continuous_ex
      fun_prop
    · refine Eventually.of_forall fun x _ => ?_
      simp only [hF, norm_mul, norm_ex, one_mul]
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, norm_mul, norm_ex, norm_ex, mul_one, mul_one]
    · exact Eventually.of_forall fun x _ => ha.add hc
    · exact intervalIntegrable_const
    · exact Eventually.of_forall fun x _ => (hG x).mul_left _
  refine hint.unique ?_
  have hterm : ∀ n : ℕ, ∫ x in (0 : ℝ)..1, F n x =
      a n * (if (n : ℤ) - k = 0 then 1 else 0) + c n * (if -(n : ℤ) - k = 0 then 1 else 0) := by
    intro n
    have e : ∀ x : ℝ, F n x = a n * ex (((n : ℤ) - k : ℤ) * x) +
        c n * ex ((-(n : ℤ) - k : ℤ) * x) := by
      intro x
      have e1 : ex (-(k * x)) * ex (n * x) = ex (((n : ℤ) - k : ℤ) * x) := by
        rw [← ex_add]; congr 1; push_cast; ring
      have e2 : ex (-(k * x)) * ex (-(n * x)) = ex ((-(n : ℤ) - k : ℤ) * x) := by
        rw [← ex_add]; congr 1; push_cast; ring
      simp only [hF]
      rw [← e1, ← e2]; ring
    simp_rw [e]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, integral_ex_int, integral_ex_int]
    · exact (continuous_const.mul (continuous_ex.comp (continuous_const.mul
        continuous_id))).intervalIntegrable _ _
    · exact (continuous_const.mul (continuous_ex.comp (continuous_const.mul
        continuous_id))).intervalIntegrable _ _
  simp_rw [hterm]
  refine HasSum.add ?_ ?_
  · by_cases hk : 0 ≤ k
    · rw [ite_eq_left hk]
      convert hasSum_single k.toNat (fun n hn => ?_) using 1
      · have : ((k.toNat : ℕ) : ℤ) - k = 0 := by omega
        rw [ite_eq_left this, mul_one]
      · have : (n : ℤ) - k ≠ 0 := by omega
        simp [this]
    · rw [ite_eq_right hk]
      convert hasSum_zero with n
      have : (n : ℤ) - k ≠ 0 := by omega
      simp [this]
  · by_cases hk : k ≤ 0
    · rw [ite_eq_left hk]
      convert hasSum_single (-k).toNat (fun n hn => ?_) using 1
      · have : -(((-k).toNat : ℕ) : ℤ) - k = 0 := by omega
        rw [ite_eq_left this, mul_one]
      · have : -(n : ℤ) - k ≠ 0 := by omega
        simp [this]
    · rw [ite_eq_right hk]
      convert hasSum_zero with n
      have : -(n : ℤ) - k ≠ 0 := by omega
      simp [this]

/-- The coefficients `β_n = (2 - δ_{n0}) rⁿ` of `(1 + z)/(1 - z) = Σ β_n e(nx)`, `z = r e(x)`. -/
def poissonCoeff (r : ℝ) (n : ℕ) : ℝ := (2 - if n = 0 then 1 else 0) * r ^ n

lemma summable_poissonCoeff {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n => ‖((poissonCoeff r n : ℝ) : ℂ)‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    ((summable_geometric_of_lt_one hr0 hr1).mul_left 2)
  rw [Complex.norm_real, Real.norm_eq_abs, poissonCoeff, abs_mul, abs_of_nonneg (pow_nonneg hr0 n)]
  gcongr
  split_ifs <;> norm_num

lemma hasSum_poisson {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (x : ℝ) :
    HasSum (fun n => ((poissonCoeff r n : ℝ) : ℂ) * ex (n * x))
      ((1 + r * ex x) / (1 - r * ex x)) := by
  set z := (r : ℂ) * ex x with hz
  have hzn : ‖z‖ < 1 := by
    rw [hz, norm_mul, norm_ex, mul_one, Complex.norm_real, Real.norm_of_nonneg hr0]; exact hr1
  have hne : 1 - z ≠ 0 := by
    intro h; rw [sub_eq_zero] at h; rw [← h, norm_one] at hzn; exact lt_irrefl _ hzn
  have h1 := (hasSum_geometric_of_norm_lt_one hzn).mul_left 2
  have h2 := h1.sub (hasSum_ite_eq 0 (1 : ℂ))
  convert h2 using 1
  · funext n
    simp only [poissonCoeff, hz, mul_pow, ex_pow]
    split_ifs with h <;> simp [h, ex_zero]
    ring
  · field_simp; ring

lemma poisson_re {r : ℝ} (x : ℝ) :
    ((1 + r * ex x) / (1 - r * ex x)).re =
      (1 - r ^ 2) / (1 - 2 * r * (ex x).re + r ^ 2) := by
  have hc : (ex x).re ^ 2 + (ex x).im ^ 2 = 1 := by
    have := Complex.sq_norm (ex x); rw [norm_ex, Complex.normSq_apply] at this; nlinarith
  rw [Complex.div_re, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.add_im, Complex.sub_im, Complex.one_im,
    Complex.mul_im, add_zero, zero_add, zero_sub]
  have hden : (1 - r * (ex x).re) * (1 - r * (ex x).re) + -(r * (ex x).im) * -(r * (ex x).im) =
      1 - 2 * r * (ex x).re + r ^ 2 := by nlinarith
  rw [hden, ← add_div]
  congr 1
  nlinarith

lemma poisson_im {r : ℝ} (x : ℝ) :
    ((1 + r * ex x) / (1 - r * ex x)).im =
      (2 * r * (ex x).im) / (1 - 2 * r * (ex x).re + r ^ 2) := by
  have hc : (ex x).re ^ 2 + (ex x).im ^ 2 = 1 := by
    have := Complex.sq_norm (ex x); rw [norm_ex, Complex.normSq_apply] at this; nlinarith
  rw [Complex.div_im, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.add_im, Complex.sub_im, Complex.one_im,
    Complex.mul_im, add_zero, zero_add, zero_sub]
  have hden : (1 - r * (ex x).re) * (1 - r * (ex x).re) + -(r * (ex x).im) * -(r * (ex x).im) =
      1 - 2 * r * (ex x).re + r ^ 2 := by nlinarith
  rw [hden, ← sub_div]
  congr 1
  ring

lemma fourier_one_coe (x : ℝ) : fourier 1 (x : UnitAddCircle) = ex x := by
  rw [fourier_coe_apply]; unfold ex; congr 1; push_cast; ring

lemma fourier_neg_coe (k : ℤ) (x : ℝ) : fourier (-k) (x : UnitAddCircle) = ex (-(k * x)) := by
  rw [fourier_coe_apply]; unfold ex; congr 1; push_cast; ring

/-- `ConjugatePoissonStatement` holds: `P̂_r(k) = r^{|k|}` and `Q̂_r(k) = -i sgn(k) r^{|k|}`
(Theorem A.1.2, `H P_r = Q_r`). -/
theorem conjugatePoissonStatement_holds : ConjugatePoissonStatement := by
  intro r hr0 hr1 k
  have hsum := summable_poissonCoeff hr0 hr1
  have hhalf : Summable (fun n => ‖((poissonCoeff r n : ℝ) : ℂ) / 2‖) := by
    simpa [norm_div] using hsum.div_const 2
  have hhalfI : Summable (fun n => ‖((poissonCoeff r n : ℝ) : ℂ) / (2 * I)‖) := by
    simpa [norm_div] using hsum.div_const 2
  have hhalfI' : Summable (fun n => ‖-(((poissonCoeff r n : ℝ) : ℂ) / (2 * I))‖) := by
    simpa [norm_neg] using hhalfI
  -- the real and imaginary parts as two-sided series
  have hconj : ∀ n : ℕ, ∀ x : ℝ, conj (((poissonCoeff r n : ℝ) : ℂ) * ex (n * x)) =
      ((poissonCoeff r n : ℝ) : ℂ) * ex (-(n * x)) := by
    intro n x; rw [map_mul, Complex.conj_ofReal, ← ex_neg]
  have hRe : ∀ x : ℝ, HasSum (fun n => ((poissonCoeff r n : ℝ) : ℂ) / 2 * ex (n * x) +
      ((poissonCoeff r n : ℝ) : ℂ) / 2 * ex (-(n * x)))
      (((1 - r ^ 2) / (1 - 2 * r * (ex x).re + r ^ 2) : ℝ) : ℂ) := by
    intro x
    have h := hasSum_poisson hr0 hr1 x
    have h2 := (h.add (Complex.hasSum_conj'.2 h)).div_const 2
    convert h2 using 1
    · funext n; rw [hconj]; ring
    · rw [Complex.add_conj, poisson_re]; push_cast; ring
  have hIm : ∀ x : ℝ, HasSum (fun n => ((poissonCoeff r n : ℝ) : ℂ) / (2 * I) * ex (n * x) +
      -(((poissonCoeff r n : ℝ) : ℂ) / (2 * I)) * ex (-(n * x)))
      (((2 * r * (ex x).im) / (1 - 2 * r * (ex x).re + r ^ 2) : ℝ) : ℂ) := by
    intro x
    have h := hasSum_poisson hr0 hr1 x
    have h2 := (h.sub (Complex.hasSum_conj'.2 h)).div_const (2 * I)
    convert h2 using 1
    · funext n; rw [hconj]; ring
    · rw [Complex.sub_conj, poisson_im]; push_cast; field_simp
  have hcoef : ∀ m : ℕ, ((poissonCoeff r m : ℝ) : ℂ) = (if m = 0 then 1 else 2) * (r : ℂ) ^ m := by
    intro m; simp only [poissonCoeff]; split_ifs <;> push_cast <;> ring
  constructor
  · rw [fourierCoeff_eq_intervalIntegral _ _ 0]
    simp only [zero_add, div_one, one_smul, smul_eq_mul, circlePoissonKernel, fourier_one_coe,
      fourier_neg_coe]
    rw [integral_ex_mul_two_sided hhalf hhalf hRe]
    rcases lt_trichotomy k 0 with h | rfl | h
    · rw [ite_eq_right (by omega), ite_eq_left h.le, zero_add, hcoef, ite_eq_right (by omega)]
      have : (((-k).toNat : ℕ) : ℕ) = k.natAbs := by omega
      rw [this]; ring
    · simp [hcoef]; norm_num
    · rw [ite_eq_left h.le, ite_eq_right (by omega), add_zero, hcoef, ite_eq_right (by omega)]
      have : k.toNat = k.natAbs := by omega
      rw [this]; ring
  · rw [fourierCoeff_eq_intervalIntegral _ _ 0]
    simp only [zero_add, div_one, one_smul, smul_eq_mul, conjPoissonKernel, fourier_one_coe,
      fourier_neg_coe]
    rw [integral_ex_mul_two_sided hhalfI hhalfI' hIm]
    unfold hilbertSymbol
    rcases lt_trichotomy k 0 with h | rfl | h
    · rw [ite_eq_right (by omega), ite_eq_left h.le, zero_add, hcoef, ite_eq_right (by omega),
        Int.sign_eq_neg_one_of_neg h]
      have : (((-k).toNat : ℕ) : ℕ) = k.natAbs := by omega
      rw [this]; field_simp; push_cast; ring_nf; rw [Complex.I_sq]; ring
    · simp [hcoef]
    · rw [ite_eq_left h.le, ite_eq_right (by omega), add_zero, hcoef, ite_eq_right (by omega),
        Int.sign_eq_one_of_pos h]
      have : k.toNat = k.natAbs := by omega
      rw [this]; field_simp; push_cast; ring_nf; rw [Complex.I_sq]; ring

end DF
