/-
# Discontinuity at rationals and failure of quantization  (paper, Remark `rational`)

For `q₀ > 0` let `λ(z) = e^{2πi q₀ z}` and `A(z) = diag(e^{λ(z)}, e^{-λ(z)})`.  Then
`L(α, A_ε) = (2/π) e^{-2π q₀ ε}` if `α = p/q` with `q ∣ q₀`, and `L(α, A_ε) = 0` for irrational
`α`.  So `α ↦ L(α, A)` is discontinuous at such rationals, and there the acceleration is
`-2q₀/π`, which is not an integer: quantization fails at rational frequencies.
-/
import AvilaGlobal.Quantization

noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology Complex Set

namespace AvilaGlobal

open AMO

/-- The diagonal cocycle `diag(e^{λ(z)}, e^{-λ(z)})`, `λ(z) = e^{2πi q₀ z}`. -/
def diagExample (q₀ : ℕ) : ℂ → M2 := fun z =>
  let l := Complex.exp (2 * Real.pi * I * q₀ * z)
  !![Complex.exp l, 0; 0, Complex.exp (-l)]

lemma norm_diag_exp (S : ℂ) :
    ‖(diagonal ![Complex.exp S, Complex.exp (-S)] : M2)‖ = Real.exp |S.re| := by
  rw [linfty_opNorm_diagonal]
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (Real.exp_pos _).le).2 fun i => ?_
    fin_cases i <;> simp [Complex.norm_exp, le_abs_self, neg_le_abs]
  · rcases le_total 0 S.re with h | h
    · rw [abs_of_nonneg h]
      have := norm_le_pi_norm (![Complex.exp S, Complex.exp (-S)]) 0
      simpa [Complex.norm_exp] using this
    · rw [abs_of_nonpos h]
      have := norm_le_pi_norm (![Complex.exp S, Complex.exp (-S)]) 1
      simpa [Complex.norm_exp] using this

lemma iter_diag (α : ℝ) (f : ℝ → ℂ) (n : ℕ) (x : ℝ) :
    iter α (fun y => (diagonal ![Complex.exp (f y), Complex.exp (-f y)] : M2)) n x =
      diagonal ![Complex.exp (∑ k ∈ Finset.range n, f (x + k * α)),
        Complex.exp (-∑ k ∈ Finset.range n, f (x + k * α))] := by
  induction n with
  | zero =>
    ext i j
    fin_cases i <;> fin_cases j <;> simp [iter]
  | succ n ih =>
    simp only [iter, ih, diagonal_mul_diagonal]
    congr 1
    ext i
    fin_cases i
    · simp [Finset.sum_range_succ, ← Complex.exp_add, add_comm]
    · simp only [Finset.sum_range_succ, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [← Complex.exp_add]
      congr 1
      ring

/-- The phase function `λ(x + iε) = e^{-2πq₀ε} e(q₀ x)`. -/
def lamF (q₀ : ℕ) (ε : ℝ) (x : ℝ) : ℂ := (Real.exp (-2 * Real.pi * q₀ * ε) : ℂ) * e (q₀ * x)

lemma shift_diagExample (q₀ : ℕ) (ε : ℝ) :
    shift (diagExample q₀) ε =
      fun y => (diagonal ![Complex.exp (lamF q₀ ε y), Complex.exp (-lamF q₀ ε y)] : M2) := by
  funext x
  have hl : Complex.exp (2 * Real.pi * I * q₀ * ((x : ℂ) + ε * I)) = lamF q₀ ε x := by
    rw [lamF, Complex.ofReal_exp, e, ← Complex.exp_add]
    congr 1
    push_cast
    linear_combination (2 * Real.pi * q₀ * ε : ℂ) * Complex.I_sq
  simp only [shift, diagExample, hl]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

lemma lyapSeq_diagExample (q₀ : ℕ) (α ε : ℝ) (n : ℕ) :
    lyapSeq α (shift (diagExample q₀) ε) n =
      ∫ x in (0 : ℝ)..1, |(∑ k ∈ Finset.range n, lamF q₀ ε (x + k * α)).re| := by
  rw [lyapSeq, shift_diagExample]
  congr 1
  funext x
  rw [iter_diag, norm_diag_exp, Real.log_exp]

lemma integral_abs_cos {q₀ : ℕ} (hq₀ : 0 < q₀) :
    ∫ x in (0 : ℝ)..1, |Real.cos (2 * Real.pi * q₀ * x)| = 2 / Real.pi := by
  have hq : (0 : ℝ) < q₀ := by exact_mod_cast hq₀
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 2 * Real.pi * q₀ := ⟨_, rfl⟩
  rw [← hc]
  have hcpos : 0 < c := by rw [hc]; positivity
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = Real.pi / c := ⟨_, rfl⟩
  have hTpos : 0 < T := by rw [hT]; positivity
  have hcT : c * T = Real.pi := by rw [hT]; field_simp
  have hper : Function.Periodic (fun x => |Real.cos (c * x)|) T := by
    intro x
    simp only
    rw [mul_add, hcT, Real.cos_add_pi, abs_neg]
  have hcont : Continuous (fun x => |Real.cos (c * x)|) := by fun_prop
  have h1per : Function.Periodic (fun x => |Real.cos (c * x)|) 1 := by
    intro x
    simp only
    rw [mul_add, mul_one, hc, show 2 * Real.pi * (q₀ : ℝ) = (q₀ : ℕ) * (2 * Real.pi) by ring,
      Real.cos_add_nat_mul_two_pi]
  have e1 : ∫ x in (0 : ℝ)..1, |Real.cos (c * x)| =
      ∫ x in (-T / 2)..(-T / 2) + 1, |Real.cos (c * x)| := by
    have := h1per.intervalIntegral_add_eq 0 (-T / 2)
    simpa using this
  have e2 : ((2 * q₀ : ℕ) : ℤ) • T = 1 := by
    rw [zsmul_eq_mul, hT, hc]
    push_cast
    field_simp
  rw [e1, ← e2, hper.intervalIntegral_add_zsmul_eq _ _ (fun _ _ => hcont.intervalIntegrable _ _)]
  have e3 : ∫ x in (-T / 2)..(-T / 2 + T), |Real.cos (c * x)| =
      ∫ x in (-T / 2)..(T / 2), Real.cos (c * x) := by
    rw [show -T / 2 + T = T / 2 by ring]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    simp only
    apply abs_of_nonneg
    apply Real.cos_nonneg_of_mem_Icc
    constructor <;> nlinarith [hx.1, hx.2]
  rw [e3, intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hcpos.ne', integral_cos,
    show c * (T / 2) = Real.pi / 2 by linarith, show c * (-T / 2) = -(Real.pi / 2) by linarith,
    Real.sin_neg, Real.sin_pi_div_two, hc]
  rw [zsmul_eq_mul, smul_eq_mul]
  push_cast
  field_simp
  ring

/-- At rationals `p/q` with `q ∣ q₀`: `L(p/q, A_ε) = (2/π) e^{-2π q₀ ε}`. -/
theorem diagExample_L_rational {q₀ : ℕ} (hq₀ : 0 < q₀) {p : ℤ} {q : ℕ} (hq : 0 < q)
    (hdvd : q ∣ q₀) (ε : ℝ) :
    L ((p : ℝ) / q) (diagExample q₀) ε = 2 / Real.pi * Real.exp (-2 * Real.pi * q₀ * ε) := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hF : ∀ k : ℕ, ∀ x : ℝ, lamF q₀ ε (x + k * ((p : ℝ) / q)) = lamF q₀ ε x := by
    intro k x
    obtain ⟨m, hm⟩ := hdvd
    simp only [lamF]
    congr 1
    have : (q₀ : ℝ) * (x + k * (p / q)) = q₀ * x + ((m * k * p : ℤ) : ℝ) := by
      rw [hm]
      push_cast
      field_simp
    rw [this, e_add_int]
  have hre : ∀ x : ℝ, (lamF q₀ ε x).re =
      Real.exp (-2 * Real.pi * q₀ * ε) * Real.cos (2 * Real.pi * q₀ * x) := by
    intro x
    rw [lamF, Complex.re_ofReal_mul, e, Complex.exp_ofReal_mul_I_re]
    ring_nf
  have hseq : ∀ n : ℕ, 1 ≤ n → lyapSeq ((p : ℝ) / q) (shift (diagExample q₀) ε) n / n =
      2 / Real.pi * Real.exp (-2 * Real.pi * q₀ * ε) := by
    intro n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
    rw [lyapSeq_diagExample]
    simp only [hF, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    have : ∀ x : ℝ, |((n : ℂ) * lamF q₀ ε x).re| =
        (n * Real.exp (-2 * Real.pi * q₀ * ε)) * |Real.cos (2 * Real.pi * q₀ * x)| := by
      intro x
      rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul, hre, abs_mul,
        abs_mul, abs_of_nonneg (Nat.cast_nonneg n), abs_of_pos (Real.exp_pos _)]
      ring
    simp only [this]
    rw [intervalIntegral.integral_const_mul, integral_abs_cos hq₀]
    field_simp
  have ht : Tendsto (fun n : ℕ => lyapSeq ((p : ℝ) / q) (shift (diagExample q₀) ε) n / n) atTop
      (𝓝 (2 / Real.pi * Real.exp (-2 * Real.pi * q₀ * ε))) :=
    tendsto_const_nhds.congr' (eventually_atTop.2 ⟨1, fun n hn => (hseq n hn).symm⟩)
  exact ht.limUnder_eq

/-- At irrational frequencies: `L(α, A_ε) = 0`. -/
theorem diagExample_L_irrational {q₀ : ℕ} (hq₀ : 0 < q₀) {α : ℝ} (hα : Irrational α) (ε : ℝ) :
    L α (diagExample q₀) ε = 0 := by
  have hcont : Continuous (lamF q₀ ε) := by
    unfold lamF e
    fun_prop
  have hper : Function.Periodic (lamF q₀ ε) 1 := by
    intro x
    simp only [lamF]
    rw [mul_add, mul_one, show ((q₀ : ℝ)) = ((q₀ : ℤ) : ℝ) by simp, e_add_int]
  have hint : ∫ x in (0 : ℝ)..1, lamF q₀ ε x = 0 := by
    simp only [lamF]
    rw [intervalIntegral.integral_const_mul]
    have := integral_e (q₀ : ℤ)
    simp only [Int.cast_natCast, Nat.cast_eq_zero, hq₀.ne', ite_false] at this
    rw [this, mul_zero]
  have ht : Tendsto (fun n : ℕ => lyapSeq α (shift (diagExample q₀) ε) n / n) atTop (𝓝 0) := by
    rw [Metric.tendsto_atTop]
    intro η hη
    obtain ⟨n₀, hn₀⟩ := weyl_uniform hα hcont hper (half_pos hη)
    refine ⟨max n₀ 1, fun n hn => ?_⟩
    have hn1 : 1 ≤ n := le_of_max_le_right hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hbound : ∀ x, |(∑ k ∈ Finset.range n, lamF q₀ ε (x + k * α)).re| ≤ n * (η / 2) := by
      intro x
      have h := hn₀ n (le_of_max_le_left hn) x
      rw [hint, sub_zero, birk, norm_mul, norm_inv, Complex.norm_natCast,
        inv_mul_le_iff₀ hnpos] at h
      exact (Complex.abs_re_le_norm _).trans h
    have hnn : 0 ≤ lyapSeq α (shift (diagExample q₀) ε) n := by
      rw [lyapSeq_diagExample]
      exact intervalIntegral.integral_nonneg zero_le_one (fun x _ => abs_nonneg _)
    have hle : lyapSeq α (shift (diagExample q₀) ε) n ≤ n * (η / 2) := by
      rw [lyapSeq_diagExample]
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
        (f := fun x => |(∑ k ∈ Finset.range n, lamF q₀ ε (x + k * α)).re|) (C := n * (η / 2))
        (fun x _ => by rw [Real.norm_eq_abs, abs_abs]; exact hbound x)
      simp only [sub_zero, abs_one, mul_one] at this
      exact (le_abs_self _).trans (by rwa [← Real.norm_eq_abs])
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hnn hnpos.le), div_lt_iff₀ hnpos]
    nlinarith
  exact ht.limUnder_eq

/-- Consequently the acceleration at `p/q` (`q ∣ q₀`) is `-2q₀/π`, not an integer. -/
theorem diagExample_accel_not_int {q₀ : ℕ} (hq₀ : 0 < q₀) {p : ℤ} {q : ℕ} (hq : 0 < q)
    (hdvd : q ∣ q₀) : accel ((p : ℝ) / q) (diagExample q₀) = -(2 * q₀ / Real.pi) ∧
      ∀ k : ℤ, accel ((p : ℝ) / q) (diagExample q₀) ≠ k := by
  have hL := fun ε => diagExample_L_rational hq₀ (p := p) hq hdvd ε
  have hval : accel ((p : ℝ) / q) (diagExample q₀) = -(2 * q₀ / Real.pi) := by
    have h1 : HasDerivAt (fun ε : ℝ => -2 * Real.pi * q₀ * ε) (-2 * Real.pi * q₀) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (-2 * Real.pi * q₀)
    have hd := h1.exp.const_mul (2 / Real.pi)
    have h2 := hd.tendsto_slope_zero_right.const_mul (1 / (2 * Real.pi))
    have h3 : Tendsto (fun ε => (L ((p : ℝ) / q) (diagExample q₀) ε -
        L ((p : ℝ) / q) (diagExample q₀) 0) / (2 * Real.pi * ε)) (𝓝[>] 0)
        (𝓝 (-(2 * q₀ / Real.pi))) := by
      convert h2 using 1
      · funext ε
        rw [hL, hL]
        simp only [zero_add, smul_eq_mul]
        ring
      · congr 1
        simp only [mul_zero, Real.exp_zero, one_mul]
        field_simp
    exact h3.limUnder_eq
  refine ⟨hval, fun k hk => ?_⟩
  rw [hval] at hk
  have hpos : (0 : ℝ) < 2 * q₀ / Real.pi := by
    have : (0 : ℝ) < q₀ := by exact_mod_cast hq₀
    positivity
  have hkz : k ≠ 0 := by
    rintro rfl
    simp at hk
    linarith
  have : Real.pi * k = ((-(2 * q₀ : ℤ) : ℤ) : ℝ) := by
    rw [← hk]
    push_cast
    field_simp
  exact (irrational_pi.mul_intCast hkz).ne_int _ this

end AvilaGlobal
