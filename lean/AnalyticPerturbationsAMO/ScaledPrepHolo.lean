/-
# Lemma 2.1 without adjoints: the holomorphic (complex-energy) preparation

For complex energies `E` the phase coefficient `w = v - E` is no longer self-adjoint and the
adjoint `Q^*` of the preparation is not holomorphic in `E`.  Following the paper ("first carry
out the preparation on the complex neighbourhood"), we solve instead
  `(I + L)(J₀ + j)(I + K) = J₀ + R`
with **independent** unknowns `K` (hopping `≥ 1`), `L` (hopping `≤ -1`) and a Jacobi correction
`j` (hopping in `{-1, 0, 1}`).  The fixed-point map has no adjoints; the `L`-equation is the
`K`-equation conjugated by the transpose `τ` (which fixes `J₀`).  The contraction constants
are those of `ScaledPreparation.lean`.

* `HData`: the data of Lemma 2.1 without self-adjointness;
* `HData.contract`, `HData.norm_Φ0`: the contraction estimates;
* `HData.fixed_point_props`: the factorization and the hopping structure of a fixed point;
* `HData.fixed_real`: for self-adjoint data the fixed point has `L = K^*`, `j = j^*`;
* `holo_preparation`: the solution is holomorphic in `E` (via `holo_fixed_point`) and reduces
  to the self-adjoint Lemma 2.1 factorization at real energies.

Everything here is proved.
-/
import AnalyticPerturbationsAMO.ScaledPreparation
import AnalyticPerturbationsAMO.Transpose
import AnalyticPerturbationsAMO.HoloFixedPoint

noncomputable section

open scoped ComplexConjugate

namespace AMO

namespace ScaledPrep

open Weights

variable {ω : Weights} (α : ℝ)

/-- The data of Lemma 2.1 without self-adjointness of `w`. -/
structure HData (ω : Weights) where
  a0 : ℝ
  ha0 : 0 < a0
  c0 : ℝ
  hc0 : 0 ≤ c0
  hc1 : c0 < 1
  w : WA
  w_ge : HopGE (ω.toS w) 0
  w_le : HopLE (ω.toS w) 0
  hsmall : Real.exp (-ω.s) / a0 * ‖w‖ + Real.exp (-ω.s) * Real.exp (-ω.s) ≤ c0

/-! ### The nonlinear remainder with independent left factor -/

/-- `N(L, K, Y) = L Y + Y K + L J K + L Y K`. -/
def Nh2 (Jh L K Y : WA) : WA :=
  ω.mul α L Y + ω.mul α Y K + ω.mul α (ω.mul α L Jh) K + ω.mul α (ω.mul α L Y) K

lemma Nh2_zero (Jh : WA) : Nh2 (ω := ω) α Jh 0 0 0 = 0 := by
  simp [Nh2, ω.mul_zero', ω.zero_mul']

lemma smul_Nh2 (κ : ℂ) (hκ : κ ≠ 0) (J L K Y : WA) :
    κ • Nh2 (ω := ω) α J L K (κ⁻¹ • Y) = Nh2 (ω := ω) α (κ • J) L K Y := by
  unfold Nh2
  simp only [smul_add, ω.mul_smul, ω.smul_mul, smul_smul, mul_inv_cancel₀ hκ, one_smul]

/-- **Lipschitz bound for the remainder** on a ball of radius `ρ ≤ 1`. -/
lemma norm_Nh2_sub_le (Jh L K Y L' K' Y' : WA) {ρ d : ℝ} (hρ : ρ ≤ 1) (hJ : ‖Jh‖ ≤ 1)
    (hL : ‖L‖ ≤ ρ) (hL' : ‖L'‖ ≤ ρ) (hK : ‖K‖ ≤ ρ) (hK' : ‖K'‖ ≤ ρ) (hY : ‖Y‖ ≤ ρ)
    (hY' : ‖Y'‖ ≤ ρ) (hdL : ‖L - L'‖ ≤ d) (hdK : ‖K - K'‖ ≤ d) (hdY : ‖Y - Y'‖ ≤ d) :
    ‖Nh2 (ω := ω) α Jh L K Y - Nh2 (ω := ω) α Jh L' K' Y'‖ ≤ 9 * ρ * d := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hL
  have hd0 : 0 ≤ d := (norm_nonneg _).trans hdL
  have t1 : ‖ω.mul α L Y - ω.mul α L' Y'‖ ≤ 2 * ρ * d := by
    refine (ω.norm_mul_sub_mul_le α _ _ _ _).trans ?_
    have a := mul_le_mul hdL hY (norm_nonneg _) hd0
    have b := mul_le_mul hL' hdY (norm_nonneg _) hρ0
    linarith
  have t2 : ‖ω.mul α Y K - ω.mul α Y' K'‖ ≤ 2 * ρ * d := by
    refine (ω.norm_mul_sub_mul_le α _ _ _ _).trans ?_
    have a := mul_le_mul hdY hK (norm_nonneg _) hd0
    have b := mul_le_mul hY' hdK (norm_nonneg _) hρ0
    linarith
  have hJX : ‖ω.mul α L Jh - ω.mul α L' Jh‖ ≤ d := by
    rw [← ω.sub_mul]
    refine (ω.norm_mul_le α _ _).trans ?_
    have := mul_le_mul hdL hJ (norm_nonneg _) hd0
    linarith
  have hJX' : ‖ω.mul α L' Jh‖ ≤ ρ := by
    refine (ω.norm_mul_le α _ _).trans ?_
    have := mul_le_mul hL' hJ (norm_nonneg _) hρ0
    linarith
  have t3 : ‖ω.mul α (ω.mul α L Jh) K - ω.mul α (ω.mul α L' Jh) K'‖ ≤ 2 * ρ * d := by
    refine (ω.norm_mul_sub_mul_le α _ _ _ _).trans ?_
    have a := mul_le_mul hJX hK (norm_nonneg _) hd0
    have b := mul_le_mul hJX' hdK (norm_nonneg _) hρ0
    linarith
  have hYX' : ‖ω.mul α L' Y'‖ ≤ ρ := by
    refine (ω.norm_mul_le α _ _).trans ?_
    have h1 := mul_le_mul hL' hY' (norm_nonneg _) hρ0
    have h2 : ρ * ρ ≤ ρ := mul_le_of_le_one_left hρ0 hρ
    linarith
  have t4 : ‖ω.mul α (ω.mul α L Y) K - ω.mul α (ω.mul α L' Y') K'‖ ≤ 3 * ρ * d := by
    refine (ω.norm_mul_sub_mul_le α _ _ _ _).trans ?_
    have a := mul_le_mul t1 hK (norm_nonneg _) (by positivity)
    have b := mul_le_mul hYX' hdK (norm_nonneg _) hρ0
    have c : 2 * ρ * d * ρ ≤ 2 * ρ * d := mul_le_of_le_one_right (by positivity) hρ
    linarith
  have hsplit : Nh2 (ω := ω) α Jh L K Y - Nh2 (ω := ω) α Jh L' K' Y' =
      (ω.mul α L Y - ω.mul α L' Y') + (ω.mul α Y K - ω.mul α Y' K') +
      (ω.mul α (ω.mul α L Jh) K - ω.mul α (ω.mul α L' Jh) K') +
      (ω.mul α (ω.mul α L Y) K - ω.mul α (ω.mul α L' Y') K') := by
    unfold Nh2; abel
  rw [hsplit]
  refine norm_add₄_le.trans ?_
  linarith

namespace HData

variable (D : HData ω)

/-! ### Numerical data (as in `ScaledPreparation.lean`) -/

def J0 : WA := ((D.a0 : ℂ)) • (U1 (ω := ω)) + ((D.a0 : ℂ)) • (Um1 (ω := ω)) + D.w
def lam : ℝ := Real.exp (-ω.s) / D.a0
def μ : ℝ := (1 - D.c0) / 24
def κ : ℝ := D.μ * D.lam
def kc : ℝ := (1 + 3 * D.c0) / 4

lemma lam_pos : 0 < D.lam := div_pos (Real.exp_pos _) D.ha0
lemma μ_pos : 0 < D.μ := by unfold μ; linarith [D.hc1]
lemma κ_pos : 0 < D.κ := mul_pos D.μ_pos D.lam_pos
lemma kc_nonneg : 0 ≤ D.kc := by unfold kc; linarith [D.hc0]
lemma kc_lt_one : D.kc < 1 := by unfold kc; linarith [D.hc1]

lemma lam_mul : D.lam * (D.a0 * Real.exp ω.s) = 1 := by
  unfold lam
  rw [div_mul_eq_mul_div, mul_comm D.a0, ← mul_assoc, ← Real.exp_add, neg_add_cancel,
    Real.exp_zero, one_mul, div_self D.ha0.ne']

lemma lam_a0 : D.lam * D.a0 = Real.exp (-ω.s) := by
  unfold lam; field_simp [D.ha0.ne']

lemma norm_w_le : ‖D.w‖ ≤ D.c0 * (D.a0 * Real.exp ω.s) := by
  have h := D.hsmall
  have hpos : 0 ≤ Real.exp (-ω.s) * Real.exp (-ω.s) := by positivity
  have h1 : D.lam * ‖D.w‖ ≤ D.c0 := by unfold lam; linarith
  have hA : 0 < D.a0 * Real.exp ω.s := mul_pos D.ha0 (Real.exp_pos _)
  calc ‖D.w‖ = (D.lam * (D.a0 * Real.exp ω.s)) * ‖D.w‖ := by rw [lam_mul, one_mul]
    _ = (D.lam * ‖D.w‖) * (D.a0 * Real.exp ω.s) := by ring
    _ ≤ D.c0 * (D.a0 * Real.exp ω.s) := mul_le_mul_of_nonneg_right h1 hA.le

lemma norm_J0_le : ‖D.J0‖ ≤ 3 * (D.a0 * Real.exp ω.s) := by
  unfold J0
  have h1 : ‖((D.a0 : ℂ)) • (U1 (ω := ω))‖ = D.a0 * Real.exp ω.s := by
    rw [norm_smul, norm_U1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos D.ha0]
  have h2 : ‖((D.a0 : ℂ)) • (Um1 (ω := ω))‖ = D.a0 * Real.exp ω.s := by
    rw [norm_smul, norm_Um1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos D.ha0]
  have hw := D.norm_w_le
  have hc := D.hc1
  calc ‖((D.a0 : ℂ)) • (U1 (ω := ω)) + ((D.a0 : ℂ)) • (Um1 (ω := ω)) + D.w‖
      ≤ ‖((D.a0 : ℂ)) • (U1 (ω := ω))‖ + ‖((D.a0 : ℂ)) • (Um1 (ω := ω))‖ + ‖D.w‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 3 * (D.a0 * Real.exp ω.s) := by
        rw [h1, h2]; nlinarith [mul_pos D.ha0 (Real.exp_pos ω.s)]

lemma norm_smulSinv_le' (Y : WA) :
    ‖((D.a0⁻¹ : ℝ) : ℂ) • ω.Sinv' α Y‖ ≤ D.lam * ‖Y‖ := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 D.ha0)]
  calc D.a0⁻¹ * ‖ω.Sinv' α Y‖ ≤ D.a0⁻¹ * (Real.exp (-ω.s) * ‖Y‖) :=
        mul_le_mul_of_nonneg_left (ω.norm_Sinv'_le α _) (inv_pos.2 D.ha0).le
    _ = D.lam * ‖Y‖ := by unfold lam; ring

/-- The tail operator `T K = a₀^{-1} S^{-1} Π_{≥2}(w K + a₀ U^{-1} K)`. -/
def T (K : WA) : WA :=
  ((D.a0⁻¹ : ℝ) : ℂ) • ω.Sinv' α (ω.P2' (ω.mul α D.w K + (D.a0 : ℂ) • ω.mul α (Um1 (ω := ω)) K))

lemma norm_T_le (K : WA) : ‖D.T α K‖ ≤ D.c0 * ‖K‖ := by
  unfold T
  refine (D.norm_smulSinv_le' α _).trans ?_
  rw [ω.P2'_add, ω.P2'_smul]
  have hb : ‖ω.P2' (ω.mul α D.w K) + (D.a0 : ℂ) • ω.P2' (ω.mul α (Um1 (ω := ω)) K)‖ ≤
      ‖D.w‖ * ‖K‖ + D.a0 * (Real.exp (-ω.s) * ‖K‖) := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (ω.norm_P2'_le _).trans (ω.norm_mul_le α _ _)
    · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos D.ha0]
      exact mul_le_mul_of_nonneg_left (Data.norm_P2_Um1_le α K) D.ha0.le
  have hsm := D.hsmall
  have hl := D.lam_a0
  calc D.lam * ‖_‖ ≤ D.lam * (‖D.w‖ * ‖K‖ + D.a0 * (Real.exp (-ω.s) * ‖K‖)) :=
        mul_le_mul_of_nonneg_left hb D.lam_pos.le
    _ = (D.lam * ‖D.w‖ + (D.lam * D.a0) * Real.exp (-ω.s)) * ‖K‖ := by ring
    _ = (Real.exp (-ω.s) / D.a0 * ‖D.w‖ + Real.exp (-ω.s) * Real.exp (-ω.s)) * ‖K‖ := by
        rw [hl]; rfl
    _ ≤ D.c0 * ‖K‖ := mul_le_mul_of_nonneg_right hsm (norm_nonneg _)

lemma T_sub (K K' : WA) : D.T α K - D.T α K' = D.T α (K - K') := by
  unfold T
  rw [← smul_sub, ← ω.Sinv'_sub, ← ω.P2'_sub]
  congr 3
  rw [ω.mul_sub, ω.mul_sub, smul_sub]
  abel

lemma T_zero : D.T α 0 = 0 := by
  have := D.T_sub α 0 0
  simpa using this.symm

lemma κ_J0 : D.κ * ‖D.J0‖ ≤ 3 * D.μ := by
  have h := D.norm_J0_le
  calc D.κ * ‖D.J0‖ ≤ D.κ * (3 * (D.a0 * Real.exp ω.s)) :=
        mul_le_mul_of_nonneg_left h D.κ_pos.le
    _ = 3 * D.μ * (D.lam * (D.a0 * Real.exp ω.s)) := by unfold κ; ring
    _ = 3 * D.μ := by rw [lam_mul, mul_one]

lemma norm_κJ0_le_one : ‖((D.κ : ℝ) : ℂ) • D.J0‖ ≤ 1 := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos D.κ_pos]
  have := D.κ_J0
  have : D.μ ≤ 1 / 24 := by unfold μ; linarith [D.hc0]
  linarith

/-! ### The fixed-point map -/

/-- The remainder with `J = J₀`. -/
def N (K L j : WA) : WA := Nh2 (ω := ω) α D.J0 L K j

/-- The tail solve `𝒮(A, Y) = a₀^{-1} S^{-1} Π_{≥2} A - T Y`. -/
def solve (A Y : WA) : WA := ((D.a0⁻¹ : ℝ) : ℂ) • ω.Sinv' α (ω.P2' A) - D.T α Y

/-- `K' = 𝒮(R - N, K)`. -/
def Kn (R K L j : WA) : WA := D.solve α (R - D.N α K L j) K

/-- `L' = τ 𝒮(τ(R - N), τ L)`. -/
def Ln (R K L j : WA) : WA := ω.tr' (D.solve α (ω.tr' (R - D.N α K L j)) (ω.tr' L))

/-- `j' = (R - N) - J₀ K' - L' J₀`. -/
def jn (R K L j : WA) : WA :=
  (R - D.N α K L j) - ω.mul α D.J0 (D.Kn α R K L j) - ω.mul α (D.Ln α R K L j) D.J0

def jOf (g : WA) : WA := (((D.κ⁻¹ : ℝ)) : ℂ) • g

/-- The fixed-point map on `(K, L, g)`, `j = κ^{-1} g`. -/
def Φ (R : WA) (z : WA × WA × WA) : WA × WA × WA :=
  (D.Kn α R z.1 z.2.1 (D.jOf z.2.2), D.Ln α R z.1 z.2.1 (D.jOf z.2.2),
    ((D.κ : ℝ) : ℂ) • D.jn α R z.1 z.2.1 (D.jOf z.2.2))

lemma solve_sub (A Y A' Y' : WA) :
    D.solve α A Y - D.solve α A' Y' =
      ((D.a0⁻¹ : ℝ) : ℂ) • ω.Sinv' α (ω.P2' (A - A')) - D.T α (Y - Y') := by
  unfold solve
  rw [← D.T_sub α, ω.P2'_sub, ω.Sinv'_sub, smul_sub]
  abel

lemma norm_solve_sub_le (A Y A' Y' : WA) :
    ‖D.solve α A Y - D.solve α A' Y'‖ ≤ D.lam * ‖A - A'‖ + D.c0 * ‖Y - Y'‖ := by
  rw [D.solve_sub]
  refine (norm_sub_le _ _).trans (add_le_add ?_ (D.norm_T_le α _))
  exact (D.norm_smulSinv_le' α _).trans
    (mul_le_mul_of_nonneg_left (ω.norm_P2'_le _) D.lam_pos.le)

lemma κN_eq (K L g : WA) :
    ((D.κ : ℝ) : ℂ) • D.N α K L (D.jOf g) = Nh2 (ω := ω) α (((D.κ : ℝ) : ℂ) • D.J0) L K g := by
  unfold N jOf
  rw [Complex.ofReal_inv]
  exact smul_Nh2 α _ (Complex.ofReal_ne_zero.2 D.κ_pos.ne') _ _ _ _

/-- **The contraction estimate** (componentwise). -/
lemma contract (R : WA) {ρ : ℝ} (hρ1 : ρ ≤ 1) (hρ2 : 9 * ρ ≤ D.μ * ((1 - D.c0) / 4))
    (z z' : WA × WA × WA) (hz : ‖z‖ ≤ ρ) (hz' : ‖z'‖ ≤ ρ) :
    ‖(D.Φ α R z).1 - (D.Φ α R z').1‖ ≤ D.kc * dist z z' ∧
      ‖(D.Φ α R z).2.1 - (D.Φ α R z').2.1‖ ≤ D.kc * dist z z' ∧
      ‖(D.Φ α R z).2.2 - (D.Φ α R z').2.2‖ ≤ D.kc * dist z z' := by
  set d := dist z z' with hd
  have hnorm : ∀ x : WA × WA × WA, ‖x.1‖ ≤ ‖x‖ ∧ ‖x.2.1‖ ≤ ‖x‖ ∧ ‖x.2.2‖ ≤ ‖x‖ := fun x =>
    ⟨norm_fst_le x, (norm_fst_le x.2).trans (norm_snd_le x),
      (norm_snd_le x.2).trans (norm_snd_le x)⟩
  have hdz := hnorm (z - z')
  rw [← dist_eq_norm] at hdz
  have hd1 : ‖z.1 - z'.1‖ ≤ d := hdz.1
  have hd2 : ‖z.2.1 - z'.2.1‖ ≤ d := hdz.2.1
  have hd3 : ‖z.2.2 - z'.2.2‖ ≤ d := hdz.2.2
  have hz1 := (hnorm z).1.trans hz
  have hz2 := (hnorm z).2.1.trans hz
  have hz3 := (hnorm z).2.2.trans hz
  have hz1' := (hnorm z').1.trans hz'
  have hz2' := (hnorm z').2.1.trans hz'
  have hz3' := (hnorm z').2.2.trans hz'
  have hd0 : 0 ≤ d := dist_nonneg
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hz
  have hμ := D.μ_pos
  have hκ := D.κ_pos
  have hc0 := D.hc0
  have hc1 := D.hc1
  have hN : D.κ * ‖D.N α z.1 z.2.1 (D.jOf z.2.2) - D.N α z'.1 z'.2.1 (D.jOf z'.2.2)‖ ≤
      9 * ρ * d := by
    have h := norm_Nh2_sub_le (ω := ω) α (((D.κ : ℝ) : ℂ) • D.J0) z.2.1 z.1 z.2.2
      z'.2.1 z'.1 z'.2.2 hρ1 D.norm_κJ0_le_one hz2 hz2' hz1 hz1' hz3 hz3' hd2 hd1 hd3
    rw [← D.κN_eq, ← D.κN_eq, ← smul_sub, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hκ] at h
    exact h
  have hlam : D.lam = D.κ / D.μ := by unfold κ; field_simp
  have hNl : D.lam * ‖D.N α z.1 z.2.1 (D.jOf z.2.2) - D.N α z'.1 z'.2.1 (D.jOf z'.2.2)‖ ≤
      ((1 - D.c0) / 4) * d := by
    rw [hlam, div_mul_eq_mul_div, div_le_iff₀ hμ]
    nlinarith
  set ΔN := D.N α z.1 z.2.1 (D.jOf z.2.2) - D.N α z'.1 z'.2.1 (D.jOf z'.2.2) with hΔN
  have hK : ‖(D.Φ α R z).1 - (D.Φ α R z').1‖ ≤ D.kc * d := by
    simp only [Φ, Kn]
    refine (D.norm_solve_sub_le α _ _ _ _).trans ?_
    have e : R - D.N α z.1 z.2.1 (D.jOf z.2.2) - (R - D.N α z'.1 z'.2.1 (D.jOf z'.2.2)) = -ΔN := by
      rw [hΔN]; abel
    rw [e, norm_neg]
    have h6 : D.c0 * ‖z.1 - z'.1‖ ≤ D.c0 * d := mul_le_mul_of_nonneg_left hd1 hc0
    unfold kc
    linarith
  have hL : ‖(D.Φ α R z).2.1 - (D.Φ α R z').2.1‖ ≤ D.kc * d := by
    simp only [Φ, Ln]
    rw [← ω.tr'_sub, ω.norm_tr']
    refine (D.norm_solve_sub_le α _ _ _ _).trans ?_
    rw [← ω.tr'_sub, ← ω.tr'_sub, ω.norm_tr', ω.norm_tr']
    have e : R - D.N α z.1 z.2.1 (D.jOf z.2.2) - (R - D.N α z'.1 z'.2.1 (D.jOf z'.2.2)) = -ΔN := by
      rw [hΔN]; abel
    rw [e, norm_neg]
    have h6 : D.c0 * ‖z.2.1 - z'.2.1‖ ≤ D.c0 * d := mul_le_mul_of_nonneg_left hd2 hc0
    unfold kc
    linarith
  refine ⟨hK, hL, ?_⟩
  simp only [Φ]
  rw [← smul_sub, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ]
  have hsplit : D.jn α R z.1 z.2.1 (D.jOf z.2.2) - D.jn α R z'.1 z'.2.1 (D.jOf z'.2.2) =
      -ΔN - ω.mul α D.J0 (D.Kn α R z.1 z.2.1 (D.jOf z.2.2) - D.Kn α R z'.1 z'.2.1 (D.jOf z'.2.2)) -
        ω.mul α (D.Ln α R z.1 z.2.1 (D.jOf z.2.2) - D.Ln α R z'.1 z'.2.1 (D.jOf z'.2.2)) D.J0 := by
    rw [hΔN, ω.mul_sub, ω.sub_mul]
    unfold jn
    abel
  set ΔK := D.Kn α R z.1 z.2.1 (D.jOf z.2.2) - D.Kn α R z'.1 z'.2.1 (D.jOf z'.2.2)
  set ΔL := D.Ln α R z.1 z.2.1 (D.jOf z.2.2) - D.Ln α R z'.1 z'.2.1 (D.jOf z'.2.2)
  have hΔK : ‖ΔK‖ ≤ D.kc * d := hK
  have hΔL : ‖ΔL‖ ≤ D.kc * d := hL
  have hb : ‖D.jn α R z.1 z.2.1 (D.jOf z.2.2) - D.jn α R z'.1 z'.2.1 (D.jOf z'.2.2)‖ ≤
      ‖ΔN‖ + ‖D.J0‖ * ‖ΔK‖ + ‖D.J0‖ * ‖ΔL‖ := by
    rw [hsplit]
    refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
      (add_le_add (norm_neg _).le (ω.norm_mul_le α _ _))) ?_)
    have := ω.norm_mul_le α ΔL D.J0
    linarith [mul_comm ‖ΔL‖ ‖D.J0‖]
  have hJ := D.κ_J0
  have hμ24 : D.μ ≤ 1 / 24 := by unfold μ; linarith
  have hkc := D.kc_nonneg
  calc D.κ * ‖_‖ ≤ D.κ * (‖ΔN‖ + ‖D.J0‖ * ‖ΔK‖ + ‖D.J0‖ * ‖ΔL‖) :=
        mul_le_mul_of_nonneg_left hb hκ.le
    _ = D.κ * ‖ΔN‖ + (D.κ * ‖D.J0‖) * ‖ΔK‖ + (D.κ * ‖D.J0‖) * ‖ΔL‖ := by ring
    _ ≤ 9 * ρ * d + (3 * D.μ) * (D.kc * d) + (3 * D.μ) * (D.kc * d) := by
        gcongr
    _ ≤ D.kc * d := by
        have : 9 * ρ ≤ (1 / 24) * ((1 - D.c0) / 4) := by nlinarith
        unfold kc at *
        nlinarith

lemma norm_Φ0 (R : WA) : ‖D.Φ α R 0‖ ≤ D.lam * ‖R‖ := by
  have hσ0 : 0 ≤ D.lam * ‖R‖ := mul_nonneg D.lam_pos.le (norm_nonneg _)
  have hN0 : D.N α 0 0 (D.jOf 0) = 0 := by
    simp only [jOf, smul_zero]; exact Nh2_zero α D.J0
  have hK0 : ‖D.Kn α R 0 0 (D.jOf 0)‖ ≤ D.lam * ‖R‖ := by
    have := D.norm_solve_sub_le α (R - D.N α 0 0 (D.jOf 0)) 0 0 0
    simp only [hN0, sub_zero, sub_self, norm_zero, mul_zero, add_zero] at this
    have e : D.solve α 0 0 = 0 := by
      have h0 : ω.P2' 0 = 0 := by simpa using ω.P2'_sub 0 0
      have h1 : ω.Sinv' α 0 = 0 := by simpa using ω.Sinv'_sub α 0 0
      unfold solve; rw [D.T_zero, h0, h1, smul_zero, sub_zero]
    rw [e, sub_zero] at this
    simpa [Kn, hN0] using this
  have hL0 : ‖D.Ln α R 0 0 (D.jOf 0)‖ ≤ D.lam * ‖R‖ := by
    unfold Ln
    rw [ω.norm_tr', hN0, sub_zero, ω.tr'_zero]
    have := D.norm_solve_sub_le α (ω.tr' R) 0 0 0
    have e : D.solve α 0 0 = 0 := by
      unfold solve; rw [D.T_zero]
      have h0 : ω.P2' 0 = 0 := by simpa using ω.P2'_sub 0 0
      have h1 : ω.Sinv' α 0 = 0 := by simpa using ω.Sinv'_sub α 0 0
      rw [h0, h1, smul_zero, sub_zero]
    rw [e, sub_zero, sub_zero, sub_zero, ω.norm_tr', norm_zero, mul_zero, add_zero] at this
    exact this
  have hj0 : ‖((D.κ : ℝ) : ℂ) • D.jn α R 0 0 (D.jOf 0)‖ ≤ D.lam * ‖R‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos D.κ_pos]
    unfold jn
    rw [hN0, sub_zero]
    set K0 := D.Kn α R 0 0 (D.jOf 0)
    set L0 := D.Ln α R 0 0 (D.jOf 0)
    have hb : ‖R - ω.mul α D.J0 K0 - ω.mul α L0 D.J0‖ ≤ ‖R‖ + ‖D.J0‖ * ‖K0‖ + ‖D.J0‖ * ‖L0‖ := by
      refine (norm_sub_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
        (add_le_add le_rfl (ω.norm_mul_le α _ _))) ?_)
      have := ω.norm_mul_le α L0 D.J0
      linarith [mul_comm ‖L0‖ ‖D.J0‖]
    have hJ := D.κ_J0
    have hμ24 : D.μ ≤ 1 / 24 := by unfold μ; linarith [D.hc0]
    have hκR : D.κ * ‖R‖ = D.μ * (D.lam * ‖R‖) := by unfold κ; ring
    calc D.κ * ‖_‖ ≤ D.κ * (‖R‖ + ‖D.J0‖ * ‖K0‖ + ‖D.J0‖ * ‖L0‖) :=
          mul_le_mul_of_nonneg_left hb D.κ_pos.le
      _ = D.κ * ‖R‖ + (D.κ * ‖D.J0‖) * ‖K0‖ + (D.κ * ‖D.J0‖) * ‖L0‖ := by ring
      _ ≤ D.μ * (D.lam * ‖R‖) + (3 * D.μ) * (D.lam * ‖R‖) + (3 * D.μ) * (D.lam * ‖R‖) := by
          rw [hκR]
          have : 0 ≤ 3 * D.μ := by linarith [D.μ_pos]
          gcongr
      _ ≤ D.lam * ‖R‖ := by nlinarith [D.μ_pos]
  simp only [Φ, Prod.fst_zero, Prod.snd_zero]
  refine (Prod.norm_def _).le.trans (max_le hK0 ((Prod.norm_def _).le.trans (max_le hL0 hj0)))

/-! ### Existence and uniqueness of the fixed point -/

lemma norm_triple_le {x : WA × WA × WA} {r : ℝ} (h1 : ‖x.1‖ ≤ r) (h2 : ‖x.2.1‖ ≤ r)
    (h3 : ‖x.2.2‖ ≤ r) : ‖x‖ ≤ r :=
  (Prod.norm_def _).le.trans (max_le h1 ((Prod.norm_def _).le.trans (max_le h2 h3)))

lemma Φ_lip (R : WA) {ρ : ℝ} (hρ1 : ρ ≤ 1) (hρ2 : 9 * ρ ≤ D.μ * ((1 - D.c0) / 4))
    {z z' : WA × WA × WA} (hz : ‖z‖ ≤ ρ) (hz' : ‖z'‖ ≤ ρ) :
    dist (D.Φ α R z) (D.Φ α R z') ≤ D.kc * dist z z' := by
  have hc := D.contract α R hρ1 hρ2 z z' hz hz'
  rw [dist_eq_norm]
  exact norm_triple_le hc.1 hc.2.1 hc.2.2

lemma Φ_maps (R : WA) {ρ : ℝ} (hρ1 : ρ ≤ 1) (hρ2 : 9 * ρ ≤ D.μ * ((1 - D.c0) / 4))
    (hσ : D.lam * ‖R‖ ≤ (1 - D.kc) * ρ) {z : WA × WA × WA} (hz : ‖z‖ ≤ ρ) :
    ‖D.Φ α R z‖ ≤ ρ := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hz
  have h0 : ‖(0 : WA × WA × WA)‖ ≤ ρ := by simpa using hρ0
  have hl := D.Φ_lip α R hρ1 hρ2 hz h0
  rw [dist_zero_right] at hl
  have hd : dist (D.Φ α R z) (D.Φ α R 0) = ‖D.Φ α R z - D.Φ α R 0‖ := dist_eq_norm _ _
  have := norm_le_insert' (D.Φ α R z) (D.Φ α R 0)
  have hΦ0 := D.norm_Φ0 α R
  have hkc := D.kc_nonneg
  have : D.kc * ‖z‖ ≤ D.kc * ρ := mul_le_mul_of_nonneg_left hz hkc
  have h3 : ‖D.Φ α R z‖ ≤ ‖D.Φ α R z - D.Φ α R 0‖ + ‖D.Φ α R 0‖ := norm_le_norm_sub_add _ _
  rw [← hd] at h3
  linarith

/-- **Existence and uniqueness of the fixed point** in the ball of radius `ρ`. -/
theorem exists_unique_fixed (R : WA) {ρ : ℝ} (hρ1 : ρ ≤ 1)
    (hρ2 : 9 * ρ ≤ D.μ * ((1 - D.c0) / 4)) (hσ : D.lam * ‖R‖ ≤ (1 - D.kc) * ρ) :
    ∃ z, ‖z‖ ≤ ρ ∧ D.Φ α R z = z ∧ ∀ z', ‖z'‖ ≤ ρ → D.Φ α R z' = z' → z' = z := by
  have hσ0 : 0 ≤ D.lam * ‖R‖ := mul_nonneg D.lam_pos.le (norm_nonneg _)
  have hkc1 := D.kc_lt_one
  have hρ0 : 0 ≤ ρ := by
    by_contra h; push Not at h; nlinarith
  have hS : IsClosed (Metric.closedBall (0 : WA × WA × WA) ρ) := Metric.isClosed_closedBall
  have hmem : ∀ {x : WA × WA × WA}, x ∈ Metric.closedBall 0 ρ ↔ ‖x‖ ≤ ρ := by
    intro x; rw [mem_closedBall_zero_iff]
  obtain ⟨z, hz, hfix⟩ := exists_fixed_of_contract hS ((hmem (x := 0)).2 (by simpa using hρ0))
    (fun x hx => hmem.2 (D.Φ_maps α R hρ1 hρ2 hσ (hmem.1 hx))) D.kc_nonneg hkc1
    (fun x hx y hy => D.Φ_lip α R hρ1 hρ2 (hmem.1 hx) (hmem.1 hy))
  refine ⟨z, hmem.1 hz, hfix, fun z' hz' hfix' => ?_⟩
  have h := D.Φ_lip α R hρ1 hρ2 hz' (hmem.1 hz)
  rw [hfix, hfix'] at h
  have h0 : dist z' z ≤ 0 := by nlinarith [dist_nonneg (x := z') (y := z)]
  exact dist_le_zero.1 h0

/-! ### Structure of the fixed point -/

lemma toS_J0 : ω.toS D.J0 = (D.a0 : ℂ) • u1 + (D.a0 : ℂ) • um1 + ω.toS D.w := by
  unfold J0
  rw [ω.toS_add, ω.toS_add, ω.toS_smul, ω.toS_smul, toS_U1, toS_Um1]

lemma HopLE_J0 : HopLE (ω.toS D.J0) 1 := by
  rw [D.toS_J0]
  exact ((HopLE_u1.smul _).add ((HopLE_um1.smul _).mono (by norm_num))).add
    (D.w_le.mono (by norm_num))

lemma tr'_J0 : ω.tr' D.J0 = D.J0 := by
  apply ω.toS_injective
  rw [toS_tr', D.toS_J0, tsym_add, tsym_add, tsym_smul, tsym_smul, tsym_u1, tsym_um1,
    tsym_hop0 D.w_ge D.w_le]
  abel

lemma HopGE_solve (A Y : WA) : HopGE (ω.toS (D.solve α A Y)) 1 := by
  unfold solve T
  rw [ω.toS_sub, ω.toS_smul, ω.toS_smul, toS_Sinv', toS_Sinv']
  exact ((HopGE_Sinv _).smul _).sub ((HopGE_Sinv _).smul _)

/-- If `Y = 𝒮(A, Y)` then `Π_{≥2}(J₀ Y) = Π_{≥2} A`. -/
lemma P2'_J0_mul_of_solve {A Y : WA} (hY : D.solve α A Y = Y) :
    ω.P2' (ω.mul α D.J0 Y) = ω.P2' A := by
  have hYge : HopGE (ω.toS Y) 1 := by rw [← hY]; exact D.HopGE_solve α A Y
  set X := ω.mul α D.w Y + (D.a0 : ℂ) • ω.mul α (Um1 (ω := ω)) Y
  have hU : (D.a0 : ℂ) • ω.mul α (U1 (ω := ω)) Y = ω.P2' A - ω.P2' X := by
    conv_lhs => rw [← hY]
    unfold solve T
    rw [ω.mul_sub, ω.mul_smul, ω.mul_smul, Data.mul_U1_Sinv', Data.mul_U1_Sinv',
      Data.P2'_P2', Data.P2'_P2', ← smul_sub, smul_smul, ← Complex.ofReal_mul,
      mul_inv_cancel₀ D.ha0.ne', Complex.ofReal_one, one_smul]
  have hP2 : ω.P2' (ω.mul α D.J0 Y) = (D.a0 : ℂ) • ω.mul α (U1 (ω := ω)) Y + ω.P2' X := by
    unfold J0
    rw [ω.add_mul, ω.add_mul, ω.smul_mul, ω.smul_mul, ω.P2'_add, ω.P2'_add, ω.P2'_smul,
      ω.P2'_smul, Data.P2'_mul_U1 α hYge]
    simp only [X, ω.P2'_add, ω.P2'_smul]
    abel
  rw [hP2, hU]
  abel

lemma P2'_mul_of_HopLE {A B : WA} {m n : ℤ} (hA : HopLE (ω.toS A) m)
    (hB : HopLE (ω.toS B) n) (hmn : m + n ≤ 1) : ω.P2' (ω.mul α A B) = 0 := by
  apply ω.toS_injective
  rw [toS_P2', ω.toS_mul, ω.toS_zero]
  exact P2_of_HopLE ((hA.tmul (α := α) hB).mono hmn)

/-- **Properties of a fixed point**: `K` has hopping `≥ 1`, `L` hopping `≤ -1`, `j` is a
Jacobi correction, and `(I + L)(J₀ + j)(I + K) = J₀ + R`. -/
theorem fixed_point_props (R : WA) (z : WA × WA × WA) (hfix : D.Φ α R z = z) :
    HopGE (ω.toS z.1) 1 ∧ HopLE (ω.toS z.2.1) (-1) ∧
      HopLE (ω.toS (D.jOf z.2.2)) 1 ∧ HopGE (ω.toS (D.jOf z.2.2)) (-1) ∧
      ω.mul α (ω.mul α (ω.one' + z.2.1) (D.J0 + D.jOf z.2.2)) (ω.one' + z.1) = D.J0 + R := by
  set K := z.1
  set L := z.2.1
  set j := D.jOf z.2.2
  have hK : D.Kn α R K L j = K := congrArg Prod.fst hfix
  have hL : D.Ln α R K L j = L := congrArg (fun x => x.2.1) hfix
  have hj : D.jn α R K L j = j := by
    have h2 : ((D.κ : ℝ) : ℂ) • D.jn α R K L j = z.2.2 := congrArg (fun x => x.2.2) hfix
    show _ = D.jOf z.2.2
    rw [← h2, jOf, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ D.κ_pos.ne',
      Complex.ofReal_one, one_smul]
  have hKge : HopGE (ω.toS K) 1 := by rw [← hK]; exact D.HopGE_solve α _ _
  have htrL : D.solve α (ω.tr' (R - D.N α K L j)) (ω.tr' L) = ω.tr' L := by
    conv_rhs => rw [← hL]
    unfold Ln
    rw [ω.tr'_tr']
  have hLle : HopLE (ω.toS L) (-1) := by
    have h := D.HopGE_solve α (ω.tr' (R - D.N α K L j)) (ω.tr' L)
    rw [htrL, toS_tr'] at h
    have := h.tsym
    rwa [tsym_tsym] at this
  have hjeq : j = (R - D.N α K L j) - ω.mul α D.J0 K - ω.mul α L D.J0 := by
    have h := hj
    unfold jn at h
    rw [hK, hL] at h
    exact h.symm
  have hKsolve : D.solve α (R - D.N α K L j) K = K := hK
  -- `Π_{≥2} j = 0`
  have hP2j : ω.P2' j = 0 := by
    rw [hjeq, ω.P2'_sub, ω.P2'_sub, D.P2'_J0_mul_of_solve α hKsolve,
      P2'_mul_of_HopLE α hLle D.HopLE_J0 (by norm_num)]
    abel
  -- `Π_{≥2} τ j = 0`
  have hP2tj : ω.P2' (ω.tr' j) = 0 := by
    have hKle : HopLE (ω.toS (ω.tr' K)) (-1) := by rw [toS_tr']; exact hKge.tsym
    rw [hjeq, ω.tr'_sub, ω.tr'_sub, ω.tr'_mul, ω.tr'_mul, D.tr'_J0, ω.P2'_sub, ω.P2'_sub,
      D.P2'_J0_mul_of_solve α htrL, P2'_mul_of_HopLE α hKle D.HopLE_J0 (by norm_num)]
    abel
  have hjle : HopLE (ω.toS j) 1 := by
    apply HopLE_of_P2
    rw [← toS_P2', hP2j, ω.toS_zero]
  have hjge : HopGE (ω.toS j) (-1) := by
    have h : HopLE (ω.toS (ω.tr' j)) 1 := by
      apply HopLE_of_P2
      rw [← toS_P2', hP2tj, ω.toS_zero]
    rw [toS_tr'] at h
    have := h.tsym
    rwa [tsym_tsym] at this
  refine ⟨hKge, hLle, hjle, hjge, ?_⟩
  have hR : R = j + D.N α K L j + ω.mul α D.J0 K + ω.mul α L D.J0 := by
    calc R = ((R - D.N α K L j) - ω.mul α D.J0 K - ω.mul α L D.J0) + D.N α K L j +
          ω.mul α D.J0 K + ω.mul α L D.J0 := by abel
      _ = j + D.N α K L j + ω.mul α D.J0 K + ω.mul α L D.J0 := by rw [← hjeq]
  simp only [ω.add_mul, ω.mul_add, ω.one'_mul, ω.mul_one']
  conv_rhs => rw [hR]
  unfold N Nh2
  abel


/-! ### Holomorphic dependence on the energy -/

namespace Holo

variable (ω)

/-- The twisted product as a continuous bilinear map. -/
def mulCLM : WA →L[ℂ] WA →L[ℂ] WA :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℂ (fun f g => ω.mul α f g) (fun f f' g => ω.add_mul α f f' g)
      (fun c f g => ω.smul_mul α c f g) (fun f g g' => ω.mul_add α f g g')
      (fun c f g => ω.mul_smul α c f g))
    1 fun f g => by simpa using ω.norm_mul_le α f g

lemma Sinv'_add (f g : WA) : ω.Sinv' α (f + g) = ω.Sinv' α f + ω.Sinv' α g := by
  apply ω.toS_injective; simp [ω.toS_add, Sinv_add]

def P2CLM : WA →L[ℂ] WA :=
  LinearMap.mkContinuous ⟨⟨ω.P2', ω.P2'_add⟩, ω.P2'_smul⟩ 1 fun f => by
    simpa using ω.norm_P2'_le f

def SinvCLM : WA →L[ℂ] WA :=
  LinearMap.mkContinuous ⟨⟨ω.Sinv' α, Sinv'_add ω α⟩, ω.Sinv'_smul α⟩ (Real.exp (-ω.s))
    fun f => ω.norm_Sinv'_le α f

def trCLM : WA →L[ℂ] WA :=
  LinearMap.mkContinuous ⟨⟨ω.tr', ω.tr'_add⟩, ω.tr'_smul⟩ 1 fun f => by
    simp [ω.norm_tr']

variable {ω} {U : Set ℂ}

@[fun_prop] lemma diff_mul {f g : ℂ → WA} (hf : DifferentiableOn ℂ f U)
    (hg : DifferentiableOn ℂ g U) : DifferentiableOn ℂ (fun E => ω.mul α (f E) (g E)) U :=
  ((mulCLM ω α).differentiable.comp_differentiableOn hf).clm_apply hg

@[fun_prop] lemma diff_P2' {f : ℂ → WA} (hf : DifferentiableOn ℂ f U) :
    DifferentiableOn ℂ (fun E => ω.P2' (f E)) U :=
  (P2CLM ω).differentiable.comp_differentiableOn hf

@[fun_prop] lemma diff_Sinv' {f : ℂ → WA} (hf : DifferentiableOn ℂ f U) :
    DifferentiableOn ℂ (fun E => ω.Sinv' α (f E)) U :=
  (SinvCLM ω α).differentiable.comp_differentiableOn hf

@[fun_prop] lemma diff_tr' {f : ℂ → WA} (hf : DifferentiableOn ℂ f U) :
    DifferentiableOn ℂ (fun E => ω.tr' (f E)) U :=
  (trCLM ω).differentiable.comp_differentiableOn hf

end Holo

/-- **The fixed-point map is holomorphic in the energy.**  For a family of data `D E` with fixed
`a₀, c₀` and holomorphic phase coefficient `w(E)`, `E ↦ Φ_E(g(E))` is holomorphic whenever `g`
is. -/
lemma Φ_holo (D : ℂ → HData ω) {a0 c0 : ℝ} (ha : ∀ E, (D E).a0 = a0)
    (hc : ∀ E, (D E).c0 = c0) {U : Set ℂ} (hw : DifferentiableOn ℂ (fun E => (D E).w) U)
    (R : WA) {g : ℂ → WA × WA × WA} (hg : DifferentiableOn ℂ g U) :
    DifferentiableOn ℂ (fun E => (D E).Φ α R (g E)) U := by
  have hK : DifferentiableOn ℂ (fun E => (g E).1) U := hg.fst
  have hL : DifferentiableOn ℂ (fun E => (g E).2.1) U := hg.snd.fst
  have hG : DifferentiableOn ℂ (fun E => (g E).2.2) U := hg.snd.snd
  simp only [HData.Φ, HData.Kn, HData.Ln, HData.jn, HData.solve, HData.N, Nh2, HData.T,
    HData.jOf, HData.J0, HData.κ, HData.μ, HData.lam, ha, hc]
  refine DifferentiableOn.prodMk ?_ (DifferentiableOn.prodMk ?_ ?_) <;> fun_prop

end HData

/-! ### Real energies: recovering the self-adjoint factorization -/

namespace HData

variable (D : HData ω)

/-- The swap `σ(K, L, g) = (L^*, K^*, g^*)`. -/
def swap (z : WA × WA × WA) : WA × WA × WA := (ω.star z.2.1, ω.star z.1, ω.star z.2.2)

lemma norm_swap_le {z : WA × WA × WA} {ρ : ℝ} (hz : ‖z‖ ≤ ρ) : ‖swap (ω := ω) z‖ ≤ ρ := by
  have h1 : ‖z.1‖ ≤ ρ := (norm_fst_le z).trans hz
  have h2 : ‖z.2.1‖ ≤ ρ := ((norm_fst_le z.2).trans (norm_snd_le z)).trans hz
  have h3 : ‖z.2.2‖ ≤ ρ := ((norm_snd_le z.2).trans (norm_snd_le z)).trans hz
  exact norm_triple_le (by simpa [swap, ω.norm_star] using h2) (by simpa [swap, ω.norm_star] using h1)
    (by simpa [swap, ω.norm_star] using h3)

variable (hw : ω.star D.w = D.w)
include hw

lemma star_J0' : ω.star D.J0 = D.J0 := by
  unfold J0
  rw [ω.star_add, ω.star_add, ω.star_real_smul, ω.star_real_smul, Data.star_U1, Data.star_Um1, hw]
  abel

lemma tc'_w : ω.tc' D.w = D.w := by
  have htr : ω.tr' D.w = D.w := by
    apply ω.toS_injective; rw [toS_tr', tsym_hop0 D.w_ge D.w_le]
  rw [tc'_eq, htr, hw]

lemma tc'_Um1 : ω.tc' (Um1 (ω := ω)) = Um1 (ω := ω) := by
  apply ω.toS_injective; rw [toS_tc', toS_Um1, tconj_um1]

lemma tc'_T (X : WA) : ω.tc' (D.T α X) = D.T α (ω.tc' X) := by
  unfold T
  rw [ω.tc'_real_smul, ω.tc'_Sinv', ω.tc'_P2', ω.tc'_add, ω.tc'_mul, ω.tc'_real_smul,
    ω.tc'_mul, D.tc'_w hw, D.tc'_Um1 hw]

lemma tc'_solve (A Y : WA) : ω.tc' (D.solve α A Y) = D.solve α (ω.tc' A) (ω.tc' Y) := by
  unfold solve
  rw [ω.tc'_sub, ω.tc'_real_smul, ω.tc'_Sinv', ω.tc'_P2', D.tc'_T α hw]

lemma star_N (K L j : WA) :
    ω.star (D.N α K L j) = D.N α (ω.star L) (ω.star K) (ω.star j) := by
  unfold N Nh2
  simp only [ω.star_add, ω.star_mul, D.star_J0' hw]
  rw [ω.mul_assoc', ω.mul_assoc']
  abel

lemma star_jOf (g : WA) : ω.star (D.jOf g) = D.jOf (ω.star g) := by
  unfold jOf; rw [ω.star_real_smul]

variable {R : WA} (hR : ω.star R = R)
include hR

/-- **`σ` commutes with `Φ`** for self-adjoint data. -/
lemma Φ_swap (z : WA × WA × WA) : D.Φ α R (swap (ω := ω) z) = swap (ω := ω) (D.Φ α R z) := by
  obtain ⟨K, L, g⟩ := z
  simp only [swap, Φ]
  have hN : D.N α (ω.star L) (ω.star K) (D.jOf (ω.star g)) =
      ω.star (D.N α K L (D.jOf g)) := by
    rw [D.star_N α hw, D.star_jOf hw]
  have hRN : R - D.N α (ω.star L) (ω.star K) (D.jOf (ω.star g)) =
      ω.star (R - D.N α K L (D.jOf g)) := by
    rw [hN, ω.star_sub, hR]
  have h1 : D.Kn α R (ω.star L) (ω.star K) (D.jOf (ω.star g)) =
      ω.star (D.Ln α R K L (D.jOf g)) := by
    unfold Kn Ln
    rw [← ω.tc'_eq, D.tc'_solve α hw, ω.tc'_tr', ω.tc'_tr', hRN]
  have h2 : D.Ln α R (ω.star L) (ω.star K) (D.jOf (ω.star g)) =
      ω.star (D.Kn α R K L (D.jOf g)) := by
    unfold Kn Ln
    rw [hRN, ω.tr'_star, ω.tr'_star, ← ω.tc'_eq, ← ω.tc'_eq, ← D.tc'_solve α hw,
      ω.tr'_tc']
  refine Prod.ext h1 (Prod.ext h2 ?_)
  simp only
  rw [ω.star_real_smul]
  congr 1
  unfold jn
  rw [hRN, h1, h2]
  simp only [ω.star_sub, ω.star_mul, D.star_J0' hw]
  abel

/-- **Real case.**  For self-adjoint data the unique fixed point satisfies `L = K^*` and
`j = j^*`, so `(I + K)^*(J₀ + j)(I + K) = J₀ + R` — the original Lemma 2.1. -/
theorem fixed_real {ρ : ℝ} (hρ1 : ρ ≤ 1) (hρ2 : 9 * ρ ≤ D.μ * ((1 - D.c0) / 4))
    (hσ : D.lam * ‖R‖ ≤ (1 - D.kc) * ρ) {z : WA × WA × WA} (hz : ‖z‖ ≤ ρ)
    (hfix : D.Φ α R z = z) :
    z.2.1 = ω.star z.1 ∧ ω.star (D.jOf z.2.2) = D.jOf z.2.2 := by
  obtain ⟨z₀, -, -, huniq⟩ := D.exists_unique_fixed α R hρ1 hρ2 hσ
  have hsw : swap (ω := ω) z = z := by
    have h1 := huniq (swap (ω := ω) z) (norm_swap_le hz) (by rw [D.Φ_swap α hw hR, hfix])
    have h2 := huniq z hz hfix
    rw [h1, h2]
  have h1 : ω.star z.2.1 = z.1 := congrArg Prod.fst hsw
  have h3 : ω.star z.2.2 = z.2.2 := congrArg (fun x => x.2.2) hsw
  refine ⟨?_, ?_⟩
  · rw [← h1, ω.star_star]
  · rw [D.star_jOf hw, h3]

end HData

/-- **Lemma 2.1 for complex energies, holomorphic version.**  Let `D E` be data with fixed
`a₀, c₀` whose phase coefficient `w(E)` is holomorphic on an open set `U`, and let
`λ ‖R‖ ≤ σ₀(c₀)`.  Then there is a holomorphic `E ↦ (K(E), L(E), g(E))` on `U` such that for
every `E ∈ U`, with `j = κ^{-1} g`,
`(I + L)(J₀(E) + j)(I + K) = J₀(E) + R`, `K` has hopping `≥ 1`, `L` hopping `≤ -1`, `j` is a
Jacobi correction, and `‖(K, L, g)‖ ≤ λ ‖R‖ / (1 - k)`.  At energies where the data are
self-adjoint (real `E`), `L = K^*` and `j = j^*`, i.e. the solution is the original Lemma 2.1
factorization `(I + K)^*(J₀ + j)(I + K) = J₀ + R`, which therefore depends holomorphically on
`E`. -/
theorem holo_preparation (D : ℂ → HData ω) {a0 c0 : ℝ} (ha : ∀ E, (D E).a0 = a0)
    (hc : ∀ E, (D E).c0 = c0) {U : Set ℂ} (hU : IsOpen U)
    (hw : DifferentiableOn ℂ (fun E => (D E).w) U) (R : WA) (E₀ : ℂ)
    (hsmall : (D E₀).lam * ‖R‖ ≤ sig0 c0) :
    ∃ z : ℂ → WA × WA × WA, DifferentiableOn ℂ z U ∧ ∀ E ∈ U,
      ‖z E‖ ≤ (D E₀).lam * ‖R‖ / (1 - (D E₀).kc) ∧ (D E).Φ α R (z E) = z E ∧
      HopGE (ω.toS (z E).1) 1 ∧ HopLE (ω.toS (z E).2.1) (-1) ∧
      HopLE (ω.toS ((D E).jOf (z E).2.2)) 1 ∧ HopGE (ω.toS ((D E).jOf (z E).2.2)) (-1) ∧
      ω.mul α (ω.mul α (ω.one' + (z E).2.1) ((D E).J0 + (D E).jOf (z E).2.2))
        (ω.one' + (z E).1) = (D E).J0 + R ∧
      (ω.star (D E).w = (D E).w → ω.star R = R →
        (z E).2.1 = ω.star (z E).1 ∧ ω.star ((D E).jOf (z E).2.2) = (D E).jOf (z E).2.2) := by
  -- the constants do not depend on `E`
  have hlam : ∀ E, (D E).lam = (D E₀).lam := fun E => by simp only [HData.lam, ha]
  have hkc : ∀ E, (D E).kc = (D E₀).kc := fun E => by simp only [HData.kc, hc]
  have hμ : ∀ E, (D E).μ = (D E₀).μ := fun E => by simp only [HData.μ, hc]
  have hc0 : (D E₀).c0 = c0 := hc E₀
  set k := (D E₀).kc
  set σ := (D E₀).lam * ‖R‖
  have hk0 : 0 ≤ k := (D E₀).kc_nonneg
  have hk1 : k < 1 := (D E₀).kc_lt_one
  have h1c : 0 < 1 - c0 := by have := (D E₀).hc1; linarith
  have hkc' : 1 - k = 3 * (1 - c0) / 4 := by
    simp only [k, HData.kc, hc0]; ring
  have hkpos : 0 < 1 - k := by linarith
  set ρ := σ / (1 - k) with hρdef
  have hσ0 : 0 ≤ σ := mul_nonneg (D E₀).lam_pos.le (norm_nonneg _)
  have hρ0 : 0 ≤ ρ := div_nonneg hσ0 hkpos.le
  have hρle : ρ ≤ min 1 ((1 - c0) / 24 * ((1 - c0) / 4) / 9) := by
    rw [hρdef, div_le_iff₀ hkpos, mul_comm, hkc']
    have := hsmall
    unfold sig0 at this
    linarith
  have hρ1 : ρ ≤ 1 := hρle.trans (min_le_left _ _)
  have hρ2 : ∀ E, 9 * ρ ≤ (D E).μ * ((1 - (D E).c0) / 4) := fun E => by
    have := hρle.trans (min_le_right _ _)
    rw [hc E]
    simp only [HData.μ, hc E]
    linarith
  have hσρ : ∀ E, (D E).lam * ‖R‖ ≤ (1 - (D E).kc) * ρ := fun E => by
    rw [hlam, hkc, hρdef]; field_simp; exact le_rfl
  obtain ⟨z, hzd, hz⟩ := holo_fixed_point (Φ := fun E => (D E).Φ α R) hU hρ0 hk0 hk1
    (fun E _ x hx => (D E).Φ_maps α R hρ1 (hρ2 E) (hσρ E) hx)
    (fun E _ x y hx hy => by
      have h := (D E).Φ_lip α R hρ1 (hρ2 E) hx hy
      rw [dist_eq_norm, dist_eq_norm, hkc] at h
      exact h)
    (fun g hg _ => HData.Φ_holo α D ha hc hw R hg)
  refine ⟨z, hzd, fun E hE => ?_⟩
  obtain ⟨hzb, hfix, -⟩ := hz E hE
  obtain ⟨p1, p2, p3, p4, p5⟩ := (D E).fixed_point_props α R (z E) hfix
  exact ⟨hzb, hfix, p1, p2, p3, p4, p5, fun hw' hR' =>
    (D E).fixed_real α hw' hR' hρ1 (hρ2 E) (hσρ E) hzb hfix⟩

end ScaledPrep

end AMO
