/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §1.14  The Avalanche Principle  (book pp. 122–131)

We work with real `2 × 2` matrices of determinant one and the Euclidean operator norm.  Lines
in `ℝ²` (points of `ℝℙ¹`) are represented by unit vectors; for a matrix `A` with singular
value data `D : SVData A` (see `Ch1/SL2.lean`), `D.u` spans `U(A)`, `perp D.u` spans `S(A)`
and `D.uOut = ‖A‖⁻¹ A D.u` spans `U(A*) = A · U(A)`.  The sine of the angle between the lines
spanned by unit vectors `x, y` is `|cross x y|` (`DF.sin_pangle`).

## Main results
* (1.14.8): `DF.rho` — the multiplicative defect `ϱ(A, B) = ‖BA‖ / (‖A‖ ‖B‖)`.
* **Lemma 1.14.1** (sine form): `DF.SVData.contraction_ball` (cf. (1.14.4)) and
  `DF.SVData.contraction_lipschitz` (cf. (1.14.5)).
* **Lemma 1.14.2**: `DF.abs_cross_le_rho`, `DF.rho_le` (the two middle inequalities of
  (1.14.10)) and the full chain (1.14.10) with `Θ(A, B) = ∠(U(A*), S(B))`: `DF.lemma_1_14_2`.
* **Theorem 1.14.3 (Avalanche Principle)**: `DF.avalanche_principle` (existence of the
  constants), with explicit constants `C = 8`, `c = 6` in `DF.avalanche_principle_explicit`.
* **Theorem 1.14.4** (Banach fixed point theorem): `DF.banach_fixed_point` (from Mathlib).

## Deviations
* Lemma 1.14.1 is stated in terms of sines of angles (the metric `|cross|`): if `x` makes an
  angle with `S(A)` whose sine is at least `ε`, then the sine of the angle between `A x` and
  `U(A*)` is at most `1/(ε ‖A‖²)`, and `A` contracts sines of angles by `1/(ε²‖A‖²)`.  This is
  equivalent to the book's statement up to the comparison `2x/π ≤ sin x ≤ x`, which changes
  the numerical constants.
* The proof of Theorem 1.14.3 is a streamlined version of the book's argument: instead of the
  Banach fixed point theorem applied to `|Aₙ|²` we show directly, by induction on `j`, that
  the most expanded output direction `U(Aⱼ*)` stays within sine-distance `4/(εμ²)` of
  `U(Tⱼ*)` (this is (1.14.23) in the book), using only Lemma 1.14.2 and the elementary
  observation `DF.abs_cross_act_uOut_le`.  The remainder (comparison of `ϱ(Aⱼ, Tⱼ₊₁)` with
  `ϱ(Tⱼ, Tⱼ₊₁)` and the telescoping product) follows the book.  We obtain `C = 8`, `c = 6`
  (the book: `C = 8`, `c = 10`).
* We require `n ≥ 2`: for `n = 1` the middle term of (1.14.14) equals `‖T₁‖`, so (1.14.14)
  fails with the usual convention for empty products.
-/
import DamanikFillman.Ch1.SL2

noncomputable section

open scoped Matrix.Norms.L2Operator RealInnerProductSpace
open Matrix

namespace DF

/-- (1.14.8): the multiplicative defect `ϱ(A, B) = ‖BA‖ / (‖A‖ ‖B‖)`. -/
def rho (A B : M2R) : ℝ := ‖B * A‖ / (‖A‖ * ‖B‖)

lemma abs_cross_comm (x y : E2) : |cross x y| = |cross y x| := by
  rw [cross_comm, abs_neg]

namespace SVData

variable {A : M2R} (D : SVData A)

/-- A unit vector spanning `U(A*) = A · U(A)`. -/
def uOut : E2 := ‖A‖⁻¹ • act A D.u

lemma norm_uOut : ‖D.uOut‖ = 1 := by
  rw [uOut, norm_smul, D.norm_Au, norm_inv, norm_norm, inv_mul_cancel₀ D.norm_pos.ne']

lemma act_u_eq : act A D.u = ‖A‖ • D.uOut := by
  rw [uOut, smul_smul, mul_inv_cancel₀ D.norm_pos.ne', one_smul]

end SVData

/-- The image of any vector `x` under `B` lies close to `U(B*)`:
`|det[B x, u_{B*}]| ≤ ‖x‖ / ‖B‖`. -/
lemma abs_cross_act_uOut_le {B : M2R} (DB : SVData B) (x : E2) :
    |cross (act B x) DB.uOut| ≤ ‖x‖ / ‖B‖ := by
  rw [SVData.uOut, cross_smul_right, DB.cross_act_u, abs_mul, abs_inv, abs_of_pos DB.norm_pos]
  have := abs_cross_le x DB.u
  rw [DB.norm_u, mul_one] at this
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left this (inv_nonneg.mpr DB.norm_pos.le)

/-! ### Lemma 1.14.1 -/

namespace SVData

variable {A : M2R} (D : SVData A)

/-- **Lemma 1.14.1**, (1.14.4) in sine form: if the sine of the angle between the unit
vector `x` and `S(A)` is at least `ε`, then the sine of the angle between `A x` and `U(A*)` is
at most `1 / (ε ‖A‖²)`. -/
theorem contraction_ball {x : E2} (hx : ‖x‖ = 1) {ε : ℝ} (hε : 0 < ε)
    (hxS : ε ≤ |cross x (perp D.u)|) :
    |cross (‖act A x‖⁻¹ • act A x) D.uOut| ≤ 1 / (ε * ‖A‖ ^ 2) := by
  have hA := D.norm_pos
  have hlow : ε * ‖A‖ ≤ ‖act A x‖ := by
    have := D.le_norm_act x
    rw [← cross_perp_right] at this
    nlinarith
  have hpos : 0 < ‖act A x‖ := lt_of_lt_of_le (by positivity) hlow
  rw [cross_smul_left, abs_mul, abs_inv, abs_norm]
  have h1 := abs_cross_act_uOut_le D x
  rw [hx] at h1
  calc ‖act A x‖⁻¹ * |cross (act A x) D.uOut| ≤ ‖act A x‖⁻¹ * (1 / ‖A‖) := by gcongr
    _ ≤ (ε * ‖A‖)⁻¹ * (1 / ‖A‖) := by gcongr
    _ = 1 / (ε * ‖A‖ ^ 2) := by field_simp

/-- **Lemma 1.14.1**, (1.14.5) in sine form: on unit vectors whose angle with `S(A)` has sine
at least `ε`, the projective action of `A` contracts sines of angles by `1 / (ε² ‖A‖²)`. -/
theorem contraction_lipschitz {x y : E2} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) {ε : ℝ} (hε : 0 < ε)
    (hxS : ε ≤ |cross x (perp D.u)|) (hyS : ε ≤ |cross y (perp D.u)|) :
    |cross (‖act A x‖⁻¹ • act A x) (‖act A y‖⁻¹ • act A y)| ≤
      |cross x y| / (ε ^ 2 * ‖A‖ ^ 2) := by
  have hA := D.norm_pos
  have hlow : ∀ z : E2, ε ≤ |cross z (perp D.u)| → ε * ‖A‖ ≤ ‖act A z‖ := by
    intro z hz
    have := D.le_norm_act z
    rw [← cross_perp_right] at this
    nlinarith
  have hx' := hlow x hxS
  have hy' := hlow y hyS
  have hxp : 0 < ‖act A x‖ := lt_of_lt_of_le (by positivity) hx'
  have hyp : 0 < ‖act A y‖ := lt_of_lt_of_le (by positivity) hy'
  rw [cross_smul_left, cross_smul_right, cross_act, D.det_eq, one_mul, abs_mul, abs_mul,
    abs_inv, abs_inv, abs_norm, abs_norm]
  calc ‖act A x‖⁻¹ * (‖act A y‖⁻¹ * |cross x y|)
      ≤ (ε * ‖A‖)⁻¹ * ((ε * ‖A‖)⁻¹ * |cross x y|) := by gcongr
    _ = |cross x y| / (ε ^ 2 * ‖A‖ ^ 2) := by field_simp

end SVData

/-! ### Lemma 1.14.2 -/

/-- **Lemma 1.14.2**, second inequality of (1.14.10): `sin Θ(A, B) ≤ ϱ(A, B)`, where
`sin Θ(A, B) = |det[u_{A*}, s_B]|`. -/
theorem abs_cross_le_rho {A B : M2R} (DA : SVData A) (DB : SVData B) :
    |cross DA.uOut (perp DB.u)| ≤ rho A B := by
  have hA := DA.norm_pos
  have hB := DB.norm_pos
  rw [rho, le_div_iff₀ (mul_pos hA hB), cross_perp_right]
  have h1 : ‖act (B * A) DA.u‖ ≤ ‖B * A‖ := by
    simpa [DA.norm_u] using norm_act_le (B * A) DA.u
  rw [act_mul, DA.act_u_eq, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hA] at h1
  have h2 := DB.le_norm_act DA.uOut
  nlinarith [mul_le_mul_of_nonneg_left h2 hA.le]

/-- **Lemma 1.14.2**, third inequality of (1.14.10):
`ϱ(A, B) ≤ sin Θ(A, B) + ‖A‖⁻² + ‖B‖⁻²`. -/
theorem rho_le {A B : M2R} (DA : SVData A) (DB : SVData B) :
    rho A B ≤ |cross DA.uOut (perp DB.u)| + ‖A‖⁻¹ ^ 2 + ‖B‖⁻¹ ^ 2 := by
  have hsn : |cross DA.uOut (perp DB.u)| = |⟪DA.uOut, DB.u⟫| := by rw [cross_perp_right]
  set sn := |cross DA.uOut (perp DB.u)|
  have hA := DA.norm_pos
  have hB := DB.norm_pos
  rw [rho, div_le_iff₀ (mul_pos hA hB), ← norm_act_eq]
  refine (act (B * A)).opNorm_le_bound (by positivity) fun w => ?_
  rw [act_mul, DA.act_decomp w, map_add, map_smul, map_smul, DA.act_u_eq, map_smul]
  have e1 : ‖act B DA.uOut‖ ≤ sn * ‖B‖ + ‖B‖⁻¹ := by
    refine (DB.norm_act_le' DA.uOut).trans ?_
    have : |⟪DA.uOut, perp DB.u⟫| ≤ 1 :=
      (abs_real_inner_le_norm _ _).trans (by rw [DA.norm_uOut, DB.norm_s]; norm_num)
    rw [← hsn]
    have := inv_pos.mpr hB
    nlinarith
  have e2 : ‖act B (act A (perp DA.u))‖ ≤ ‖B‖ * ‖A‖⁻¹ := by
    refine (norm_act_le _ _).trans ?_
    rw [DA.norm_As]
  have e3 : |⟪w, DA.u⟫| ≤ ‖w‖ :=
    (abs_real_inner_le_norm _ _).trans (by rw [DA.norm_u, mul_one])
  have e4 : |⟪w, perp DA.u⟫| ≤ ‖w‖ :=
    (abs_real_inner_le_norm _ _).trans (by rw [DA.norm_s, mul_one])
  have hsn0 : 0 ≤ sn := abs_nonneg _
  calc ‖⟪w, DA.u⟫ • ‖A‖ • act B DA.uOut + ⟪w, perp DA.u⟫ • act B (act A (perp DA.u))‖
      ≤ |⟪w, DA.u⟫| * (‖A‖ * ‖act B DA.uOut‖) +
          |⟪w, perp DA.u⟫| * ‖act B (act A (perp DA.u))‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_pos hA]
    _ ≤ ‖w‖ * (‖A‖ * (sn * ‖B‖ + ‖B‖⁻¹)) + ‖w‖ * (‖B‖ * ‖A‖⁻¹) := by gcongr
    _ = (sn + ‖A‖⁻¹ ^ 2 + ‖B‖⁻¹ ^ 2) * (‖A‖ * ‖B‖) * ‖w‖ := by field_simp; ring

/-- **Lemma 1.14.2**, the full chain (1.14.10):
`2Θ/π ≤ sin Θ ≤ ϱ(A, B) ≤ sin Θ + ‖A‖⁻² + ‖B‖⁻² ≤ Θ + ‖A‖⁻² + ‖B‖⁻²`, where
`Θ = Θ(A, B) = ∠(U(A*), S(B))` (1.14.9). -/
theorem lemma_1_14_2 {A B : M2R} (DA : SVData A) (DB : SVData B) :
    2 / Real.pi * pangle DA.uOut (perp DB.u) ≤ Real.sin (pangle DA.uOut (perp DB.u)) ∧
      Real.sin (pangle DA.uOut (perp DB.u)) ≤ rho A B ∧
      rho A B ≤ Real.sin (pangle DA.uOut (perp DB.u)) + ‖A‖⁻¹ ^ 2 + ‖B‖⁻¹ ^ 2 ∧
      Real.sin (pangle DA.uOut (perp DB.u)) + ‖A‖⁻¹ ^ 2 + ‖B‖⁻¹ ^ 2 ≤
        pangle DA.uOut (perp DB.u) + ‖A‖⁻¹ ^ 2 + ‖B‖⁻¹ ^ 2 := by
  have h1 : DA.uOut ≠ 0 := by
    intro h; have := DA.norm_uOut; rw [h, norm_zero] at this; norm_num at this
  have h2 : perp DB.u ≠ 0 := by
    intro h; have := DB.norm_s; rw [h, norm_zero] at this; norm_num at this
  have hsin : Real.sin (pangle DA.uOut (perp DB.u)) = |cross DA.uOut (perp DB.u)| := by
    rw [sin_pangle h1 h2, DA.norm_uOut, DB.norm_s, mul_one, div_one]
  have h0 := pangle_nonneg DA.uOut (perp DB.u)
  have hpi := pangle_le_pi_div_two DA.uOut (perp DB.u)
  refine ⟨Real.mul_le_sin h0 hpi, ?_, ?_, ?_⟩
  · rw [hsin]; exact abs_cross_le_rho DA DB
  · rw [hsin]; exact rho_le DA DB
  · have := Real.sin_le h0; linarith

/-! ### Theorem 1.14.4: the Banach fixed point theorem -/

/-- **Theorem 1.14.4** (Banach): a contraction `g` of a nonempty complete metric space with
constant `λ < 1` has a unique fixed point `x*`, and `d(x, x*) ≤ d(x, g x) / (1 - λ)` (1.14.15).
(The book's hypothesis contains a typo; the intended one is `d(gx, gy) ≤ λ d(x, y)`.) -/
theorem banach_fixed_point {X : Type*} [MetricSpace X] [CompleteSpace X] [Nonempty X]
    {g : X → X} {l : ℝ} (hl0 : 0 ≤ l) (hl : l < 1)
    (hg : ∀ x y, dist (g x) (g y) ≤ l * dist x y) :
    ∃ xs : X, g xs = xs ∧ (∀ y, g y = y → y = xs) ∧ ∀ x, dist x xs ≤ dist x (g x) / (1 - l) := by
  set K : NNReal := ⟨l, hl0⟩
  have hK : ContractingWith K g :=
    ⟨by rw [← NNReal.coe_lt_coe]; exact hl, LipschitzWith.of_dist_le_mul fun x y => hg x y⟩
  refine ⟨ContractingWith.fixedPoint g hK, ContractingWith.fixedPoint_isFixedPt hK,
    fun y hy => ContractingWith.fixedPoint_unique hK hy, fun x => ?_⟩
  exact ContractingWith.dist_fixedPoint_le hK x

/-! ### Theorem 1.14.3: the Avalanche Principle -/

/-- The products `A_n = T_n T_{n-1} ⋯ T_1` (`A_0 = I`). -/
def prodT (T : ℕ → M2R) : ℕ → M2R
  | 0 => 1
  | n + 1 => T (n + 1) * prodT T n

@[simp] lemma prodT_zero (T : ℕ → M2R) : prodT T 0 = 1 := rfl

lemma prodT_succ (T : ℕ → M2R) (n : ℕ) : prodT T (n + 1) = T (n + 1) * prodT T n := rfl

@[simp] lemma prodT_one (T : ℕ → M2R) : prodT T 1 = T 1 := by simp [prodT]

section AP

variable {ε μ : ℝ}

lemma ap_consts (hε : 0 < ε) (hε1 : ε ≤ 1) (hμ : 8 / ε ≤ μ) :
    0 < μ ∧ 8 ≤ ε * μ ∧ 2 / μ ^ 2 ≤ ε / 32 ∧ 4 / (ε * μ ^ 2) ≤ ε / 16 ∧
      1 / μ ^ 2 ≤ 4 / (ε * μ ^ 2) ∧ 6 / (ε ^ 2 * μ ^ 2) ≤ 1 / 8 ∧
      4 / (ε * μ ^ 2) + 2 / μ ^ 2 ≤ 6 / (ε ^ 2 * μ ^ 2) * ε := by
  have h8 : 8 ≤ ε * μ := by rwa [div_le_iff₀ hε, mul_comm] at hμ
  have hμ0 : 0 < μ := by
    by_contra h; push Not at h; nlinarith
  have h64 : 64 ≤ ε ^ 2 * μ ^ 2 := by nlinarith
  have h64' : 64 ≤ ε * μ ^ 2 := by nlinarith
  refine ⟨hμ0, h8, ?_, ?_, ?_, ?_, ?_⟩
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  · rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  · rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  · have e : 6 / (ε ^ 2 * μ ^ 2) * ε = 4 / (ε * μ ^ 2) + 2 / (ε * μ ^ 2) := by
      field_simp; ring
    rw [e]
    gcongr
    calc ε * μ ^ 2 ≤ 1 * μ ^ 2 := by gcongr
      _ = μ ^ 2 := one_mul _

/-- The inductive invariant in the proof of the Avalanche Principle: `Aⱼ ∈ SL(2,ℝ)`,
`‖Aⱼ‖ ≥ μ`, and every most expanded output direction of `Aⱼ` is within sine-distance `κ`
of `U(Tⱼ*)` (cf. (1.14.23)). -/
def APInv (T : ℕ → M2R) (μ κ : ℝ) (j : ℕ) : Prop :=
  (prodT T j).det = 1 ∧ μ ≤ ‖prodT T j‖ ∧ ∀ D : SVData (T j), ∀ v : E2, ‖v‖ = 1 →
    ‖act (prodT T j) v‖ = ‖prodT T j‖ →
    |cross (‖prodT T j‖⁻¹ • act (prodT T j) v) D.uOut| ≤ κ

lemma ap_base {T : ℕ → M2R} (hε : 0 < ε) (hε1 : ε ≤ 1) (hμ : 8 / ε ≤ μ)
    (hdet : (T 1).det = 1) (hn : μ ≤ ‖T 1‖) : APInv T μ (4 / (ε * μ ^ 2)) 1 := by
  obtain ⟨hμ0, -, -, -, hc3, -, -⟩ := ap_consts hε hε1 hμ
  unfold APInv
  rw [prodT_one]
  refine ⟨hdet, hn, fun D v hv _ => ?_⟩
  have hT := D.norm_pos
  rw [cross_smul_left, abs_mul, abs_inv, abs_norm]
  have h1 := abs_cross_act_uOut_le D v
  rw [hv] at h1
  calc ‖T 1‖⁻¹ * |cross (act (T 1) v) D.uOut| ≤ ‖T 1‖⁻¹ * (1 / ‖T 1‖) := by gcongr
    _ = 1 / ‖T 1‖ ^ 2 := by field_simp
    _ ≤ 1 / μ ^ 2 := by gcongr
    _ ≤ 4 / (ε * μ ^ 2) := hc3

lemma inv_sq_le {x μ : ℝ} (hμ : 0 < μ) (h : μ ≤ x) : x⁻¹ ^ 2 ≤ 1 / μ ^ 2 := by
  rw [inv_pow, ← one_div]; gcongr

/-- One step of the induction in the proof of the Avalanche Principle: comparison of
`ϱ(Aⱼ, Tⱼ₊₁)` with `ϱ(Tⱼ, Tⱼ₊₁)` and propagation of the invariant. -/
lemma ap_step {T : ℕ → M2R} {j : ℕ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hμ : 8 / ε ≤ μ)
    (hinv : APInv T μ (4 / (ε * μ ^ 2)) j)
    (hTj : (T j).det = 1) (hTj1 : (T (j + 1)).det = 1) (hnj : μ ≤ ‖T j‖)
    (hnj1 : μ ≤ ‖T (j + 1)‖) (hr : ε ≤ rho (T j) (T (j + 1))) :
    |rho (prodT T j) (T (j + 1)) - rho (T j) (T (j + 1))| ≤ 4 / (ε * μ ^ 2) + 2 / μ ^ 2 ∧
      APInv T μ (4 / (ε * μ ^ 2)) (j + 1) := by
  obtain ⟨hμ0, hεμ, hc1, hc2, -, -, -⟩ := ap_consts hε hε1 hμ
  set κ := 4 / (ε * μ ^ 2) with hκ
  obtain ⟨hdetA, hnA, hP⟩ := hinv
  set A := prodT T j with hA_def
  set B := T (j + 1) with hB_def
  obtain ⟨DA⟩ := exists_svd hdetA
  obtain ⟨DT⟩ := exists_svd hTj
  obtain ⟨DB⟩ := exists_svd hTj1
  have hAp : 0 < ‖A‖ := DA.norm_pos
  have hBp : 0 < ‖B‖ := DB.norm_pos
  have hclose : |cross DA.uOut DT.uOut| ≤ κ := hP DT DA.u DA.norm_u DA.norm_Au
  have hiA := inv_sq_le hμ0 hnA
  have hiB := inv_sq_le hμ0 hnj1
  have hiT := inv_sq_le hμ0 hnj
  have h2 : 2 / μ ^ 2 = 1 / μ ^ 2 + 1 / μ ^ 2 := by ring
  set sA := |cross DA.uOut (perp DB.u)|
  set sT := |cross DT.uOut (perp DB.u)|
  have hsT_lo : rho (T j) B - 2 / μ ^ 2 ≤ sT := by have := rho_le DT DB; linarith
  have hsT_hi : sT ≤ rho (T j) B := abs_cross_le_rho DT DB
  have htri1 : sT ≤ |cross DT.uOut DA.uOut| + sA :=
    abs_cross_triangle _ _ _ DA.norm_uOut DT.norm_uOut.le DB.norm_s.le
  have htri2 : sA ≤ |cross DA.uOut DT.uOut| + sT :=
    abs_cross_triangle _ _ _ DT.norm_uOut DA.norm_uOut.le DB.norm_s.le
  rw [abs_cross_comm] at htri1
  have hrA_lo : sA ≤ rho A B := abs_cross_le_rho DA DB
  have hrA_hi : rho A B ≤ sA + ‖A‖⁻¹ ^ 2 + ‖B‖⁻¹ ^ 2 := rho_le DA DB
  have hdiff : |rho A B - rho (T j) B| ≤ κ + 2 / μ ^ 2 := by
    rw [abs_le]; constructor <;> linarith
  have hrA : ε / 2 ≤ rho A B := by linarith
  have hBA : ‖B * A‖ = rho A B * (‖A‖ * ‖B‖) := by
    rw [rho]; field_simp
  refine ⟨hdiff, ?_, ?_, ?_⟩
  · show (T (j + 1) * prodT T j).det = 1
    rw [det_mul, hTj1, hdetA, one_mul]
  · show μ ≤ ‖B * A‖
    rw [hBA]
    have : ε / 2 * μ ≥ 4 := by linarith
    nlinarith [mul_le_mul hrA hnj1 hμ0.le (by linarith : (0:ℝ) ≤ rho A B)]
  · intro D' v hv hmax
    change ‖act (B * A) v‖ = ‖B * A‖ at hmax
    change |cross (‖B * A‖⁻¹ • act (B * A) v) D'.uOut| ≤ κ
    rw [act_mul, cross_smul_left, abs_mul, abs_inv, abs_norm]
    have h1 := abs_cross_act_uOut_le D' (act A v)
    have h2 : ‖act A v‖ ≤ ‖A‖ := by simpa [hv] using norm_act_le A v
    have hBAp : 0 < ‖B * A‖ := by rw [hBA]; have : 0 < rho A B := by linarith
                                  positivity
    have hrpos : 0 < rho A B := by linarith
    calc ‖B * A‖⁻¹ * |cross (act B (act A v)) D'.uOut| ≤ ‖B * A‖⁻¹ * (‖A‖ / ‖B‖) := by
          gcongr; exact h1.trans (by gcongr)
      _ = 1 / (rho A B * ‖B‖ ^ 2) := by rw [hBA]; field_simp
      _ ≤ 1 / (ε / 2 * μ ^ 2) := by gcongr
      _ = 2 / (ε * μ ^ 2) := by field_simp
      _ ≤ κ := by rw [hκ]; gcongr; norm_num

/-- The quantity in the middle of (1.14.14). -/
def apRatio (T : ℕ → M2R) (m : ℕ) : ℝ :=
  ‖prodT T m‖ * (∏ j ∈ Finset.Ico 2 m, ‖T j‖) / ∏ j ∈ Finset.Ico 1 m, ‖T (j + 1) * T j‖

/-- **Theorem 1.14.3 (Avalanche Principle for `SL(2,ℝ)`)**, with the explicit constants
`C = 8` and `c = 6`: if `0 < ε ≤ 1`, `μ ≥ 8/ε`, `T₁, …, Tₙ ∈ SL(2,ℝ)` (`n ≥ 2`) satisfy
`‖Tⱼ‖ ≥ μ` (1.14.12) and `‖Tⱼ₊₁Tⱼ‖ ≥ ε ‖Tⱼ₊₁‖ ‖Tⱼ‖` (1.14.13), then
`(1 - c/(ε²μ²))^{n-1} ≤ ‖Aₙ‖ ∏_{j=2}^{n-1} ‖Tⱼ‖ / ∏_{j=1}^{n-1} ‖Tⱼ₊₁Tⱼ‖ ≤ (1 + c/(ε²μ²))^{n-1}`
(1.14.14). -/
theorem avalanche_principle_explicit (hε : 0 < ε) (hε1 : ε ≤ 1) (hμ : 8 / ε ≤ μ)
    {n : ℕ} (hn : 2 ≤ n) {T : ℕ → M2R} (hdet : ∀ j, 1 ≤ j → j ≤ n → (T j).det = 1)
    (hnorm : ∀ j, 1 ≤ j → j ≤ n → μ ≤ ‖T j‖)
    (hrho : ∀ j, 1 ≤ j → j < n → ε ≤ ‖T (j + 1) * T j‖ / (‖T (j + 1)‖ * ‖T j‖)) :
    (1 - 6 / (ε ^ 2 * μ ^ 2)) ^ (n - 1) ≤ apRatio T n ∧
      apRatio T n ≤ (1 + 6 / (ε ^ 2 * μ ^ 2)) ^ (n - 1) := by
  obtain ⟨hμ0, hεμ, hc1, hc2, hc3, hc4, hc5⟩ := ap_consts hε hε1 hμ
  set κ := 4 / (ε * μ ^ 2)
  set c' := 6 / (ε ^ 2 * μ ^ 2) with hc'
  have hrho' : ∀ j, 1 ≤ j → j < n → ε ≤ rho (T j) (T (j + 1)) := by
    intro j h1 h2; rw [rho, mul_comm ‖T j‖]; exact hrho j h1 h2
  -- the invariant
  have hInv : ∀ m, 1 ≤ m → m ≤ n → APInv T μ κ m := by
    intro m
    induction m with
    | zero => intro h; omega
    | succ k ih =>
      intro h1 h2
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · exact ap_base hε hε1 hμ (hdet 1 le_rfl (by omega)) (hnorm 1 le_rfl (by omega))
      · exact (ap_step hε hε1 hμ (ih hk (by omega)) (hdet k hk (by omega)) (hdet (k + 1) h1 h2)
          (hnorm k hk (by omega)) (hnorm (k + 1) h1 h2) (hrho' k hk (by omega))).2
  -- comparison of the defects
  have hcmp : ∀ j, 1 ≤ j → j < n →
      |rho (prodT T j) (T (j + 1)) - rho (T j) (T (j + 1))| ≤ κ + 2 / μ ^ 2 := fun j h1 h2 =>
    (ap_step hε hε1 hμ (hInv j h1 h2.le) (hdet j h1 h2.le) (hdet (j + 1) (by omega) h2)
      (hnorm j h1 h2.le) (hnorm (j + 1) (by omega) h2) (hrho' j h1 h2)).1
  have hq : ∀ j, 1 ≤ j → j < n →
      1 - c' ≤ rho (prodT T j) (T (j + 1)) / rho (T j) (T (j + 1)) ∧
        rho (prodT T j) (T (j + 1)) / rho (T j) (T (j + 1)) ≤ 1 + c' := by
    intro j h1 h2
    have hb := hrho' j h1 h2
    have hbpos : 0 < rho (T j) (T (j + 1)) := lt_of_lt_of_le hε hb
    have hd := abs_le.mp (hcmp j h1 h2)
    have hcb : κ + 2 / μ ^ 2 ≤ c' * rho (T j) (T (j + 1)) :=
      hc5.trans (mul_le_mul_of_nonneg_left hb (by positivity))
    constructor
    · rw [le_div_iff₀ hbpos]; nlinarith
    · rw [div_le_iff₀ hbpos]; nlinarith
  -- positivity facts
  have hTpos : ∀ j, 1 ≤ j → j ≤ n → 0 < ‖T j‖ := fun j h1 h2 =>
    lt_of_lt_of_le hμ0 (hnorm j h1 h2)
  have hPpos : ∀ j, 1 ≤ j → j < n → 0 < ‖T (j + 1) * T j‖ := by
    intro j h1 h2
    have := hrho j h1 h2
    have hden : 0 < ‖T (j + 1)‖ * ‖T j‖ :=
      mul_pos (hTpos (j + 1) (by omega) h2) (hTpos j h1 h2.le)
    have : 0 < ‖T (j + 1) * T j‖ / (‖T (j + 1)‖ * ‖T j‖) := lt_of_lt_of_le hε this
    exact (div_pos_iff_of_pos_right hden).mp this
  have hApos : ∀ j, 1 ≤ j → j ≤ n → 0 < ‖prodT T j‖ := fun j h1 h2 =>
    lt_of_lt_of_le hμ0 (hInv j h1 h2).2.1
  -- recursion for the ratio
  have hR2 : apRatio T 2 = 1 := by
    have h := hPpos 1 le_rfl (by omega)
    simp only [apRatio, prodT_succ, prodT_zero, Finset.Ico_self, Finset.prod_empty,
      mul_one]
    rw [show Finset.Ico 1 2 = {1} from rfl, Finset.prod_singleton]
    exact div_self h.ne'
  have hRs : ∀ m, 2 ≤ m → m < n → apRatio T (m + 1) =
      apRatio T m * (rho (prodT T m) (T (m + 1)) / rho (T m) (T (m + 1))) := by
    intro m h1 h2
    have hP : 0 < ∏ j ∈ Finset.Ico 1 m, ‖T (j + 1) * T j‖ :=
      Finset.prod_pos fun j hj => by
        obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
        exact hPpos j hj1 (by omega)
    have hTm := hTpos m (by omega) h2.le
    have hTm1 := hTpos (m + 1) (by omega) h2
    have hAm := hApos m (by omega) h2.le
    have hPm := hPpos m (by omega) h2
    simp only [apRatio, rho]
    rw [Finset.prod_Ico_succ_top (by omega : 2 ≤ m), Finset.prod_Ico_succ_top (by omega : 1 ≤ m),
      prodT_succ]
    field_simp
  have hmain : ∀ m, 2 ≤ m → m ≤ n →
      (1 - c') ^ (m - 1) ≤ apRatio T m ∧ apRatio T m ≤ (1 + c') ^ (m - 1) := by
    intro m h1
    induction m, h1 using Nat.le_induction with
    | base =>
      intro _
      have : (0:ℝ) ≤ c' := by positivity
      rw [hR2, show 2 - 1 = 1 from rfl, pow_one, pow_one]
      constructor <;> linarith
    | succ k hk ih =>
      intro h2
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      obtain ⟨q1, q2⟩ := hq k (by omega) (by omega)
      rw [hRs k hk (by omega), show k + 1 - 1 = (k - 1) + 1 by omega, pow_succ, pow_succ]
      have hc'1 : 0 ≤ 1 - c' := by linarith
      have hR0 : 0 ≤ apRatio T k := le_trans (pow_nonneg hc'1 _) ih1
      constructor
      · exact mul_le_mul ih1 q1 hc'1 hR0
      · exact mul_le_mul ih2 q2 (by linarith) (by positivity)
  exact hmain n hn le_rfl

/-- **Theorem 1.14.3 (Avalanche Principle for `SL(2,ℝ)`)**: there are constants `C, c > 0`
such that for `0 < ε ≤ 1`, `μ ≥ C/ε`, and `T₁, …, Tₙ ∈ SL(2,ℝ)` (`n ≥ 2`) with `‖Tⱼ‖ ≥ μ`
(1.14.12) and `‖Tⱼ₊₁Tⱼ‖ ≥ ε ‖Tⱼ₊₁‖ ‖Tⱼ‖` (1.14.13), the product `Aₙ = Tₙ ⋯ T₁` satisfies
(1.14.14). -/
theorem avalanche_principle : ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ ε μ : ℝ, 0 < ε → ε ≤ 1 →
    C / ε ≤ μ → ∀ (n : ℕ) (T : ℕ → M2R), 2 ≤ n →
    (∀ j, 1 ≤ j → j ≤ n → (T j).det = 1) → (∀ j, 1 ≤ j → j ≤ n → μ ≤ ‖T j‖) →
    (∀ j, 1 ≤ j → j < n → ε ≤ ‖T (j + 1) * T j‖ / (‖T (j + 1)‖ * ‖T j‖)) →
    (1 - c / (ε ^ 2 * μ ^ 2)) ^ (n - 1) ≤
        ‖prodT T n‖ * (∏ j ∈ Finset.Ico 2 n, ‖T j‖) / ∏ j ∈ Finset.Ico 1 n, ‖T (j + 1) * T j‖ ∧
      ‖prodT T n‖ * (∏ j ∈ Finset.Ico 2 n, ‖T j‖) / ∏ j ∈ Finset.Ico 1 n, ‖T (j + 1) * T j‖ ≤
        (1 + c / (ε ^ 2 * μ ^ 2)) ^ (n - 1) :=
  ⟨8, 6, by norm_num, by norm_num, fun _ _ hε hε1 hμ _ _ hn hdet hnorm hrho =>
    avalanche_principle_explicit hε hε1 hμ hn hdet hnorm hrho⟩

end AP

end DF
