/-
# The diagonal Poisson bound (`t-lem:poisson`): quantitative core

The paper's finite-scale proof of
  `sup_n sup_{0<s<1} ⟨Im (J - i s)^{-1} δ_n, δ_n⟩ < ∞`
for a Jacobi operator with bounded transfer matrices at energy `0` has three quantitative steps,
proved here:

1. **Perturbed transfer matrices** (`perturbed_inverse_bound`): if `X_{n+1} = (1 + x_n) X_n`,
   `X_0 = 1`, with `‖x_n‖ ≤ t ≤ 1/2`, then `X_n` has a left inverse of norm `≤ e^{2tn}`.
   With `x_n = i s D_n`, `‖D_n‖ ≤ K²/a₋`, this is `‖T_{is}(n,1)^{-1}‖ ≤ K e^{2K²/a₋}` for
   `n ≤ s^{-1}`.
2. **Weyl-function bounds** (`weyl_bounds`): `c(|m|² + 1) ≤ Im m` forces `|m| ≤ c^{-1}` and
   `Im m ≥ c`.
3. **Gluing** (`glue_bound`): the diagonal Green function
   `(b - i s - a₋₁² m₋ - a₀² m₊)^{-1}` has modulus `≤ (2 a₋² c)^{-1}` when `Im m_± ≥ c`.

Everything here is proved.
-/
import Mathlib

noncomputable section

open scoped Matrix.Norms.Operator

namespace AMO

namespace Poisson

section Ring

variable {B : Type*} [NormedRing B] [CompleteSpace B] [NormOneClass B]

/-- `(1 + x)^{-1}` exists with norm `≤ 1 + 2t` when `‖x‖ ≤ t ≤ 1/2`. -/
lemma left_inv_one_add {x : B} {t : ℝ} (hx : ‖x‖ ≤ t) (ht : t ≤ 1 / 2) :
    ∃ z : B, z * (1 + x) = 1 ∧ ‖z‖ ≤ 1 + 2 * t := by
  have hlt : ‖-x‖ < 1 := by rw [norm_neg]; linarith
  set u := Units.oneSub (-x) hlt
  refine ⟨↑u⁻¹, ?_, ?_⟩
  · have h := u.inv_mul
    rwa [show (u : B) = 1 + x by simp [u, Units.oneSub, sub_eq_add_neg]] at h
  · have hval : (↑u⁻¹ : B) = ∑' n : ℕ, (-x) ^ n := rfl
    rw [hval]
    have hb := tsum_geometric_le_of_norm_lt_one (-x) hlt
    rw [norm_one, sub_self, zero_add, norm_neg] at hb
    have ht0 : 0 ≤ t := (norm_nonneg x).trans hx
    have h1 : 0 < 1 - ‖x‖ := by linarith
    refine hb.trans ?_
    rw [inv_le_iff_one_le_mul₀ h1]
    nlinarith [norm_nonneg x]

/-- **Step 1.**  Products of near-identity factors have controlled left inverses. -/
theorem perturbed_inverse_bound {x : ℕ → B} {t : ℝ} (hx : ∀ n, ‖x n‖ ≤ t) (ht : t ≤ 1 / 2)
    {X : ℕ → B} (h0 : X 0 = 1) (hrec : ∀ n, X (n + 1) = (1 + x n) * X n) (n : ℕ) :
    ∃ Y : B, Y * X n = 1 ∧ ‖Y‖ ≤ Real.exp (2 * t * n) := by
  have ht0 : 0 ≤ t := (norm_nonneg _).trans (hx 0)
  have key : ∃ Y : B, Y * X n = 1 ∧ ‖Y‖ ≤ (1 + 2 * t) ^ n := by
    induction n with
    | zero => exact ⟨1, by rw [h0, one_mul], by simp⟩
    | succ n ih =>
      obtain ⟨Y, hY, hYn⟩ := ih
      obtain ⟨z, hz, hzn⟩ := left_inv_one_add (hx n) ht
      refine ⟨Y * z, ?_, ?_⟩
      · rw [hrec, ← mul_assoc, mul_assoc Y, hz, mul_one, hY]
      · calc ‖Y * z‖ ≤ ‖Y‖ * ‖z‖ := norm_mul_le _ _
          _ ≤ (1 + 2 * t) ^ n * (1 + 2 * t) :=
            mul_le_mul hYn hzn (norm_nonneg _) (by positivity)
          _ = _ := (pow_succ _ _).symm
  obtain ⟨Y, hY, hYn⟩ := key
  refine ⟨Y, hY, hYn.trans ?_⟩
  calc (1 + 2 * t) ^ n ≤ (Real.exp (2 * t)) ^ n :=
        pow_le_pow_left₀ (by positivity) (by linarith [Real.add_one_le_exp (2 * t)]) n
    _ = Real.exp (2 * t * n) := by rw [← Real.exp_nat_mul]; ring_nf

end Ring

/-- **Step 2.**  `c(|m|² + 1) ≤ Im m` with `c > 0` gives `|m| ≤ c^{-1}` and `Im m ≥ c`. -/
theorem weyl_bounds {m : ℂ} {c : ℝ} (hc : 0 < c) (h : c * (‖m‖ ^ 2 + 1) ≤ m.im) :
    ‖m‖ ≤ c⁻¹ ∧ c ≤ m.im := by
  have him : m.im ≤ ‖m‖ := (le_abs_self _).trans (Complex.abs_im_le_norm m)
  have hcm : c * ‖m‖ ≤ 1 := by
    rcases (norm_nonneg m).eq_or_lt with h0 | hpos
    · rw [← h0, mul_zero]; exact zero_le_one
    · have h1 : c * ‖m‖ * ‖m‖ ≤ 1 * ‖m‖ := by nlinarith
      exact le_of_mul_le_mul_right h1 hpos
  refine ⟨?_, by nlinarith [sq_nonneg ‖m‖]⟩
  calc ‖m‖ = c⁻¹ * (c * ‖m‖) := by field_simp
    _ ≤ c⁻¹ * 1 := mul_le_mul_of_nonneg_left hcm (inv_nonneg.2 hc.le)
    _ = c⁻¹ := mul_one _

/-- **Step 3.**  The gluing denominator: if `Im m₋, Im m₊ ≥ c > 0`, `a₋₁, a₀ ≥ a > 0`, `s > 0`,
`b` real, then `|(b - i s - a₋₁² m₋ - a₀² m₊)^{-1}| ≤ (2 a² c)^{-1}` and the imaginary part of the
diagonal resolvent is bounded by the same constant. -/
theorem glue_bound {b s a am a0 c : ℝ} {mm mp : ℂ} (hs : 0 < s) (ha : 0 < a)
    (ham : a ≤ am) (ha0 : a ≤ a0) (hc : 0 < c) (hmm : c ≤ mm.im) (hmp : c ≤ mp.im) :
    ‖((b : ℂ) - Complex.I * s - (am : ℂ) ^ 2 * mm - (a0 : ℂ) ^ 2 * mp)⁻¹‖ ≤ (2 * a ^ 2 * c)⁻¹ := by
  set Dn : ℂ := (b : ℂ) - Complex.I * s - (am : ℂ) ^ 2 * mm - (a0 : ℂ) ^ 2 * mp with hDn
  have him : -Dn.im = s + am ^ 2 * mm.im + a0 ^ 2 * mp.im := by
    simp only [hDn, Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, ← Complex.ofReal_pow]
    ring
  have hlow : 2 * a ^ 2 * c ≤ -Dn.im := by
    rw [him]
    have h1 : a ^ 2 ≤ am ^ 2 := pow_le_pow_left₀ ha.le ham 2
    have h2 : a ^ 2 ≤ a0 ^ 2 := pow_le_pow_left₀ ha.le ha0 2
    nlinarith [mul_le_mul h1 hmm hc.le (sq_nonneg am), mul_le_mul h2 hmp hc.le (sq_nonneg a0)]
  have hpos : 0 < 2 * a ^ 2 * c := by positivity
  have hnorm : 2 * a ^ 2 * c ≤ ‖Dn‖ :=
    hlow.trans ((neg_le_abs _).trans (Complex.abs_im_le_norm Dn))
  rw [norm_inv]
  exact inv_anti₀ hpos hnorm

/-- A left inverse of norm `≤ K` gives `‖v‖ ≤ K ‖T v‖`. -/
lemma norm_le_of_left_inv {T Y : Matrix (Fin 2) (Fin 2) ℂ} {K : ℝ} (hY : Y * T = 1)
    (hK : ‖Y‖ ≤ K) (v : Fin 2 → ℂ) : ‖v‖ ≤ K * ‖T.mulVec v‖ := by
  calc ‖v‖ = ‖Y.mulVec (T.mulVec v)‖ := by rw [Matrix.mulVec_mulVec, hY, Matrix.one_mulVec]
    _ ≤ ‖Y‖ * ‖T.mulVec v‖ := Matrix.linfty_opNorm_mulVec _ _
    _ ≤ K * ‖T.mulVec v‖ := mul_le_mul_of_nonneg_right hK (norm_nonneg _)

/-- `‖(m, -1)‖_∞² ≥ (|m|² + 1)/2`. -/
lemma norm_init_sq (m : ℂ) : (‖m‖ ^ 2 + 1) / 2 ≤ ‖(![m, -1] : Fin 2 → ℂ)‖ ^ 2 := by
  have h1 : ‖m‖ ≤ ‖(![m, -1] : Fin 2 → ℂ)‖ := by
    simpa using norm_le_pi_norm (![m, -1] : Fin 2 → ℂ) 0
  have h2 : (1 : ℝ) ≤ ‖(![m, -1] : Fin 2 → ℂ)‖ := by
    simpa using norm_le_pi_norm (![m, -1] : Fin 2 → ℂ) 1
  nlinarith [norm_nonneg m]

/-- **Step 4 (half-line Weyl function).**  Let `u_1, u_2, …` be the half-line solution with
`Im m = s ∑_{n ≥ 1} |u_n|²` (spectral theorem), and `y_n = (u_n, a_{n-1} u_{n-1})` its transfer
vectors, `y_1 = (m, -1)`, `y_n = T_n y_1` with left inverses `‖T_n^{-1}‖ ≤ K₁` for `2 ≤ n ≤ L`,
`‖y_n‖² ≤ |u_n|² + A |u_{n-1}|²`, and `2 s (L - 1) ≥ 1`.  Then
`c (|m|² + 1) ≤ Im m` with `c = (4 (1 + A) K₁²)^{-1}`, hence `|m| ≤ c^{-1}` and `Im m ≥ c`. -/
theorem halfline_weyl {s A K₁ : ℝ} {L : ℕ} (hs : 0 < s) (hA : 0 ≤ A) (hK : 0 < K₁)
    (hL : 1 ≤ 2 * s * ((L : ℝ) - 1)) {m : ℂ} {u : ℕ → ℂ}
    (hu : Summable fun n : ℕ => ‖u (n + 1)‖ ^ 2)
    (him : m.im = s * ∑' n : ℕ, ‖u (n + 1)‖ ^ 2)
    {y : ℕ → Fin 2 → ℂ} {T Y : ℕ → Matrix (Fin 2) (Fin 2) ℂ} (hy1 : y 1 = ![m, -1])
    (hyT : ∀ n, 2 ≤ n → n ≤ L → y n = (T n).mulVec (y 1))
    (hYT : ∀ n, 2 ≤ n → n ≤ L → Y n * T n = 1)
    (hYK : ∀ n, 2 ≤ n → n ≤ L → ‖Y n‖ ≤ K₁)
    (hyu : ∀ n, 2 ≤ n → ‖y n‖ ^ 2 ≤ ‖u n‖ ^ 2 + A * ‖u (n - 1)‖ ^ 2) :
    (4 * (1 + A) * K₁ ^ 2)⁻¹ * (‖m‖ ^ 2 + 1) ≤ m.im ∧
      ‖m‖ ≤ 4 * (1 + A) * K₁ ^ 2 ∧ (4 * (1 + A) * K₁ ^ 2)⁻¹ ≤ m.im := by
  set S := ∑' n : ℕ, ‖u (n + 1)‖ ^ 2 with hS
  have hL1 : 1 ≤ L := by
    by_contra h
    push Not at h
    interval_cases L
    simp at hL
    nlinarith
  -- each `n ∈ [2, L]` contributes at least `‖y₁‖²/K₁²`
  have hpt : ∀ k : ℕ, k < L - 1 →
      ‖y 1‖ ^ 2 ≤ K₁ ^ 2 * (‖u (k + 2)‖ ^ 2 + A * ‖u (k + 1)‖ ^ 2) := fun k hk => by
    have h2 : 2 ≤ k + 2 := by omega
    have hLk : k + 2 ≤ L := by omega
    have hb := norm_le_of_left_inv (hYT _ h2 hLk) (hYK _ h2 hLk) (y 1)
    rw [← hyT _ h2 hLk] at hb
    have hyb := hyu (k + 2) h2
    simp only [show k + 2 - 1 = k + 1 by omega] at hyb
    calc ‖y 1‖ ^ 2 ≤ (K₁ * ‖y (k + 2)‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
      _ = K₁ ^ 2 * ‖y (k + 2)‖ ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hyb (by positivity)
  have hA2 : ∀ N : ℕ, ∑ k ∈ Finset.range N, ‖u (k + 1)‖ ^ 2 ≤ S := fun N =>
    hu.sum_le_tsum _ (fun _ _ => by positivity)
  have hA1 : ∀ N : ℕ, ∑ k ∈ Finset.range N, ‖u (k + 2)‖ ^ 2 ≤ S := fun N => by
    have hsh : Summable fun k : ℕ => ‖u (k + 1 + 1)‖ ^ 2 :=
      hu.comp_injective (add_left_injective 1)
    calc ∑ k ∈ Finset.range N, ‖u (k + 2)‖ ^ 2 = ∑ k ∈ Finset.range N, ‖u (k + 1 + 1)‖ ^ 2 := rfl
      _ ≤ ∑' k : ℕ, ‖u (k + 1 + 1)‖ ^ 2 := hsh.sum_le_tsum _ (fun _ _ => by positivity)
      _ ≤ S := tsum_comp_le_tsum_of_inj hu (fun _ => by positivity) (add_left_injective 1)
  have hsum : ((L : ℝ) - 1) * ‖y 1‖ ^ 2 ≤ K₁ ^ 2 * ((1 + A) * S) := by
    have hcard : ((L : ℝ) - 1) = ((L - 1 : ℕ) : ℝ) := by push_cast [Nat.cast_sub hL1]; ring
    rw [hcard]
    have hsplit : ∑ k ∈ Finset.range (L - 1), K₁ ^ 2 * (‖u (k + 2)‖ ^ 2 + A * ‖u (k + 1)‖ ^ 2) =
        K₁ ^ 2 * (∑ k ∈ Finset.range (L - 1), ‖u (k + 2)‖ ^ 2 +
          A * ∑ k ∈ Finset.range (L - 1), ‖u (k + 1)‖ ^ 2) := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
    calc ((L - 1 : ℕ) : ℝ) * ‖y 1‖ ^ 2 = ∑ k ∈ Finset.range (L - 1), ‖y 1‖ ^ 2 := by simp
      _ ≤ ∑ k ∈ Finset.range (L - 1), K₁ ^ 2 * (‖u (k + 2)‖ ^ 2 + A * ‖u (k + 1)‖ ^ 2) :=
          Finset.sum_le_sum fun k hk => hpt k (Finset.mem_range.1 hk)
      _ = _ := hsplit
      _ ≤ K₁ ^ 2 * (S + A * S) :=
          mul_le_mul_of_nonneg_left (add_le_add (hA1 _) (mul_le_mul_of_nonneg_left (hA2 _) hA))
            (by positivity)
      _ = K₁ ^ 2 * ((1 + A) * S) := by ring
  have hS0 : 0 ≤ S := tsum_nonneg fun _ => by positivity
  have hc : 0 < 4 * (1 + A) * K₁ ^ 2 := by positivity
  have hkey : (4 * (1 + A) * K₁ ^ 2)⁻¹ * (‖m‖ ^ 2 + 1) ≤ m.im := by
    rw [him, inv_mul_le_iff₀ hc]
    have hy := norm_init_sq m
    rw [← hy1] at hy
    -- `(‖m‖² + 1) ≤ 2‖y₁‖² ≤ 4 s (L-1) ‖y₁‖² ≤ 4 s K₁² (1+A) S`
    have h1 : ‖m‖ ^ 2 + 1 ≤ 2 * s * ((L : ℝ) - 1) * (2 * ‖y 1‖ ^ 2) := by
      nlinarith [sq_nonneg ‖y 1‖]
    have h2 : 2 * s * ((L : ℝ) - 1) * (2 * ‖y 1‖ ^ 2) ≤ 4 * s * (K₁ ^ 2 * ((1 + A) * S)) := by
      nlinarith
    nlinarith
  have hb := weyl_bounds (inv_pos.2 hc) hkey
  rw [inv_inv] at hb
  exact ⟨hkey, hb⟩

end Poisson

end AMO
