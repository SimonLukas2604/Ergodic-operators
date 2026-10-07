/-
# Lemma 2.1: preparation in the scaled Banach algebra  (paper `d-lem:scaled`)

Let `J₀ = a₀(U + U^{-1}) + w` with `a₀ > 0`, `w = v - E` a self-adjoint phase coefficient
(hopping index `0`), and
  `e^{-s} a₀^{-1} ‖w‖_{s,ℓ} + e^{-2s} ≤ c₀ < 1`.
For a self-adjoint `R` with `σ = e^{-s} a₀^{-1} ‖R‖_{s,ℓ}` small (in terms of `c₀` only) there
are `K` (hopping indices `≥ 1`) and a self-adjoint Jacobi correction `j` (hopping indices in
`{-1, 0, 1}`) with
  `(I + K)^* (J₀ + j) (I + K) = J₀ + R`,   `‖K‖ + e^{-s} a₀^{-1} ‖j‖ ≤ C(c₀) σ`.
The proof is the paper's: a contraction mapping for the pair `(K, j)`, where the linearized
equation is solved through the tail inverse `S^{-1}` of `K ↦ a₀ U K`.
Everything here is proved.
-/
import AnalyticPerturbationsAMO.WeightedSpace

noncomputable section

open scoped ComplexConjugate

namespace AMO

namespace ScaledPrep

open Weights

variable (ω : Weights) (α : ℝ)

/-- The data of Lemma 2.1. -/
structure Data where
  a0 : ℝ
  ha0 : 0 < a0
  c0 : ℝ
  hc0 : 0 ≤ c0
  hc1 : c0 < 1
  /-- the phase coefficient `v - E`, as an element of `𝒲_{s,ℓ}` -/
  w : WA
  w_ge : HopGE (ω.toS w) 0
  w_le : HopLE (ω.toS w) 0
  w_sa : ω.star w = w
  hsmall : Real.exp (-ω.s) / a0 * ‖w‖ + Real.exp (-ω.s) * Real.exp (-ω.s) ≤ c0

variable {ω}

lemma u1_wsum : WSum ω.s ω.ℓ u1 := by unfold u1; exact single_wsum _ _
lemma um1_wsum : WSum ω.s ω.ℓ um1 := by unfold um1; exact single_wsum _ _

/-- `U` in `𝒲_{s,ℓ}`. -/
def U1 : WA := ω.ofS u1 u1_wsum
/-- `U^{-1}` in `𝒲_{s,ℓ}`. -/
def Um1 : WA := ω.ofS um1 um1_wsum

lemma toS_U1 : ω.toS (U1 (ω := ω)) = u1 := ω.toS_ofS _ _
lemma toS_Um1 : ω.toS (Um1 (ω := ω)) = um1 := ω.toS_ofS _ _

lemma norm_U1 : ‖U1 (ω := ω)‖ = Real.exp ω.s := by rw [U1, ω.norm_ofS, wnorm_u1]
lemma norm_Um1 : ‖Um1 (ω := ω)‖ = Real.exp ω.s := by rw [Um1, ω.norm_ofS, wnorm_um1]

namespace Data

variable (D : Data ω)

/-- `J₀ = a₀ U + a₀ U^{-1} + w`. -/
def J0 : WA := ((D.a0 : ℂ)) • (U1 (ω := ω)) + ((D.a0 : ℂ)) • (Um1 (ω := ω)) + D.w

/-- `λ = e^{-s} / a₀`. -/
def lam : ℝ := Real.exp (-ω.s) / D.a0

/-- The tail operator `T K = a₀^{-1} S^{-1} Π_{≥2}(w K + a₀ U^{-1} K)`. -/
def T (K : WA) : WA :=
  ((D.a0⁻¹ : ℝ) : ℂ) • ω.Sinv' α (ω.P2' (ω.mul α D.w K + (D.a0 : ℂ) • ω.mul α (Um1 (ω := ω)) K))


lemma lam_pos : 0 < D.lam := div_pos (Real.exp_pos _) D.ha0

lemma lam_mul : D.lam * (D.a0 * Real.exp ω.s) = 1 := by
  unfold lam
  rw [div_mul_eq_mul_div, mul_comm D.a0, ← mul_assoc, ← Real.exp_add, neg_add_cancel,
    Real.exp_zero, one_mul, div_self D.ha0.ne']

lemma norm_w_le : ‖D.w‖ ≤ D.c0 * (D.a0 * Real.exp ω.s) := by
  have h := D.hsmall
  have hpos : 0 ≤ Real.exp (-ω.s) * Real.exp (-ω.s) := by positivity
  have h1 : D.lam * ‖D.w‖ ≤ D.c0 := by unfold lam; linarith
  have hA : 0 < D.a0 * Real.exp ω.s := mul_pos D.ha0 (Real.exp_pos _)
  calc ‖D.w‖ = (D.lam * (D.a0 * Real.exp ω.s)) * ‖D.w‖ := by rw [lam_mul, one_mul]
    _ = (D.lam * ‖D.w‖) * (D.a0 * Real.exp ω.s) := by ring
    _ ≤ D.c0 * (D.a0 * Real.exp ω.s) := mul_le_mul_of_nonneg_right h1 hA.le

lemma norm_J0_le : ‖J0 D‖ ≤ 3 * (D.a0 * Real.exp ω.s) := by
  unfold J0
  have h1 : ‖((D.a0 : ℂ)) • (U1 (ω := ω))‖ = D.a0 * Real.exp ω.s := by
    rw [norm_smul, norm_U1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos D.ha0]
  have h2 : ‖((D.a0 : ℂ)) • (Um1 (ω := ω))‖ = D.a0 * Real.exp ω.s := by
    rw [norm_smul, norm_Um1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos D.ha0]
  have hw := D.norm_w_le
  have hc := D.hc1
  have hA : 0 < D.a0 * Real.exp ω.s := mul_pos D.ha0 (Real.exp_pos _)
  calc ‖((D.a0 : ℂ)) • (U1 (ω := ω)) + ((D.a0 : ℂ)) • (Um1 (ω := ω)) + D.w‖
      ≤ ‖((D.a0 : ℂ)) • (U1 (ω := ω))‖ + ‖((D.a0 : ℂ)) • (Um1 (ω := ω))‖ + ‖D.w‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 3 * (D.a0 * Real.exp ω.s) := by
        rw [h1, h2]; nlinarith

lemma norm_P2_Um1_le (K : WA) : ‖ω.P2' (ω.mul α (Um1 (ω := ω)) K)‖ ≤ Real.exp (-ω.s) * ‖K‖ := by
  rw [← ω.wnorm_toS, toS_P2', toS_mul, toS_Um1, ← ω.wnorm_toS K]
  exact (P2_um1_wsum ω.hs (ω.toS_wsum K)).2

lemma norm_smulSinv_le' (Y : WA) :
    ‖((D.a0⁻¹ : ℝ) : ℂ) • ω.Sinv' α Y‖ ≤ D.lam * ‖Y‖ := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 D.ha0)]
  calc D.a0⁻¹ * ‖ω.Sinv' α Y‖ ≤ D.a0⁻¹ * (Real.exp (-ω.s) * ‖Y‖) :=
        mul_le_mul_of_nonneg_left (ω.norm_Sinv'_le α _) (inv_pos.2 D.ha0).le
    _ = D.lam * ‖Y‖ := by unfold lam; ring

lemma lam_a0 : D.lam * D.a0 = Real.exp (-ω.s) := by
  unfold lam; field_simp [D.ha0.ne']

/-- `‖T K‖ ≤ c₀ ‖K‖`. -/
lemma norm_T_le (K : WA) : ‖T α D K‖ ≤ D.c0 * ‖K‖ := by
  unfold T
  refine (D.norm_smulSinv_le' α _).trans ?_
  rw [ω.P2'_add, ω.P2'_smul]
  have hb : ‖ω.P2' (ω.mul α D.w K) + (D.a0 : ℂ) • ω.P2' (ω.mul α (Um1 (ω := ω)) K)‖ ≤
      ‖D.w‖ * ‖K‖ + D.a0 * (Real.exp (-ω.s) * ‖K‖) := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact (ω.norm_P2'_le _).trans (ω.norm_mul_le α _ _)
    · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos D.ha0]
      exact mul_le_mul_of_nonneg_left (norm_P2_Um1_le α K) D.ha0.le
  have hsm := D.hsmall
  have hl := D.lam_a0
  have hlpos := D.lam_pos
  calc D.lam * ‖_‖ ≤ D.lam * (‖D.w‖ * ‖K‖ + D.a0 * (Real.exp (-ω.s) * ‖K‖)) :=
        mul_le_mul_of_nonneg_left hb hlpos.le
    _ = (D.lam * ‖D.w‖ + (D.lam * D.a0) * Real.exp (-ω.s)) * ‖K‖ := by ring
    _ = (Real.exp (-ω.s) / D.a0 * ‖D.w‖ + Real.exp (-ω.s) * Real.exp (-ω.s)) * ‖K‖ := by
        rw [hl]; rfl
    _ ≤ D.c0 * ‖K‖ := mul_le_mul_of_nonneg_right hsm (norm_nonneg _)

/-- `T` is linear. -/
lemma T_sub (K K' : WA) : T α D K - T α D K' = T α D (K - K') := by
  unfold T
  rw [← smul_sub, ← ω.Sinv'_sub, ← ω.P2'_sub]
  congr 3
  rw [ω.mul_sub, ω.mul_sub, smul_sub]
  abel

lemma T_zero : T α D 0 = 0 := by
  have := D.T_sub α 0 0
  simpa using this.symm

end Data

/-! ### The nonlinear remainder -/

/-- `N(X, Y) = X^* Y + Y X + (X^* J) X + (X^* Y) X`. -/
def Nh (Jh X Y : WA) : WA :=
  ω.mul α (ω.star X) Y + ω.mul α Y X + ω.mul α (ω.mul α (ω.star X) Jh) X +
    ω.mul α (ω.mul α (ω.star X) Y) X

lemma Nh_zero (Jh : WA) : Nh (ω := ω) α Jh 0 0 = 0 := by
  simp [Nh, ω.mul_zero', ω.zero_mul', ω.star_zero']

/-- Scaling: `κ N_J(X, κ^{-1} Y) = N_{κJ}(X, Y)`. -/
lemma smul_Nh (κ : ℂ) (hκ : κ ≠ 0) (J X Y : WA) :
    κ • Nh (ω := ω) α J X (κ⁻¹ • Y) = Nh (ω := ω) α (κ • J) X Y := by
  unfold Nh
  simp only [smul_add, ω.mul_smul, ω.smul_mul, smul_smul, mul_inv_cancel₀ hκ, one_smul]

/-- **Lipschitz bound for the remainder** on a ball of radius `ρ ≤ 1`. -/
lemma norm_Nh_sub_le (Jh X Y X' Y' : WA) {ρ d : ℝ} (hρ : ρ ≤ 1) (hJ : ‖Jh‖ ≤ 1)
    (hX : ‖X‖ ≤ ρ) (hX' : ‖X'‖ ≤ ρ) (hY : ‖Y‖ ≤ ρ) (hY' : ‖Y'‖ ≤ ρ)
    (hdX : ‖X - X'‖ ≤ d) (hdY : ‖Y - Y'‖ ≤ d) :
    ‖Nh (ω := ω) α Jh X Y - Nh (ω := ω) α Jh X' Y'‖ ≤ 9 * ρ * d := by
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hX
  have hd0 : 0 ≤ d := (norm_nonneg _).trans hdX
  have hsX : ‖ω.star X‖ ≤ ρ := by rwa [ω.norm_star]
  have hsX' : ‖ω.star X'‖ ≤ ρ := by rwa [ω.norm_star]
  have hsd : ‖ω.star X - ω.star X'‖ ≤ d := by rwa [← ω.star_sub, ω.norm_star]
  -- term 1
  have t1 : ‖ω.mul α (ω.star X) Y - ω.mul α (ω.star X') Y'‖ ≤ 2 * ρ * d := by
    refine (ω.norm_mul_sub_mul_le α _ _ _ _).trans ?_
    have a := mul_le_mul hsd hY (norm_nonneg _) hd0
    have b := mul_le_mul hsX' hdY (norm_nonneg _) hρ0
    linarith
  -- term 2
  have t2 : ‖ω.mul α Y X - ω.mul α Y' X'‖ ≤ 2 * ρ * d := by
    refine (ω.norm_mul_sub_mul_le α _ _ _ _).trans ?_
    have a := mul_le_mul hdY hX (norm_nonneg _) hd0
    have b := mul_le_mul hY' hdX (norm_nonneg _) hρ0
    linarith
  -- term 3
  have hJX : ‖ω.mul α (ω.star X) Jh - ω.mul α (ω.star X') Jh‖ ≤ d := by
    rw [← ω.sub_mul]
    refine (ω.norm_mul_le α _ _).trans ?_
    have := mul_le_mul hsd hJ (norm_nonneg _) hd0
    linarith
  have hJX' : ‖ω.mul α (ω.star X') Jh‖ ≤ ρ := by
    refine (ω.norm_mul_le α _ _).trans ?_
    have := mul_le_mul hsX' hJ (norm_nonneg _) hρ0
    linarith
  have t3 : ‖ω.mul α (ω.mul α (ω.star X) Jh) X - ω.mul α (ω.mul α (ω.star X') Jh) X'‖ ≤
      2 * ρ * d := by
    refine (ω.norm_mul_sub_mul_le α _ _ _ _).trans ?_
    have a := mul_le_mul hJX hX (norm_nonneg _) hd0
    have b := mul_le_mul hJX' hdX (norm_nonneg _) hρ0
    linarith
  -- term 4
  have hYX' : ‖ω.mul α (ω.star X') Y'‖ ≤ ρ := by
    refine (ω.norm_mul_le α _ _).trans ?_
    have h1 := mul_le_mul hsX' hY' (norm_nonneg _) hρ0
    have h2 : ρ * ρ ≤ ρ := mul_le_of_le_one_left hρ0 hρ
    linarith
  have t4 : ‖ω.mul α (ω.mul α (ω.star X) Y) X - ω.mul α (ω.mul α (ω.star X') Y') X'‖ ≤
      3 * ρ * d := by
    refine (ω.norm_mul_sub_mul_le α _ _ _ _).trans ?_
    have a := mul_le_mul t1 hX (norm_nonneg _) (by positivity)
    have b := mul_le_mul hYX' hdX (norm_nonneg _) hρ0
    have c : 2 * ρ * d * ρ ≤ 2 * ρ * d := mul_le_of_le_one_right (by positivity) hρ
    linarith
  have hsplit : Nh (ω := ω) α Jh X Y - Nh (ω := ω) α Jh X' Y' =
      (ω.mul α (ω.star X) Y - ω.mul α (ω.star X') Y') + (ω.mul α Y X - ω.mul α Y' X') +
      (ω.mul α (ω.mul α (ω.star X) Jh) X - ω.mul α (ω.mul α (ω.star X') Jh) X') +
      (ω.mul α (ω.mul α (ω.star X) Y) X - ω.mul α (ω.mul α (ω.star X') Y') X') := by
    unfold Nh; abel
  rw [hsplit]
  refine norm_add₄_le.trans ?_
  linarith

namespace Data

variable (D : Data ω)

/-! ### The fixed-point map -/

/-- The remainder with `J = J₀`. -/
def N (K j : WA) : WA := Nh (ω := ω) α D.J0 K j

/-- The `K`-update: `K' = a₀^{-1} S^{-1} Π_{≥2}(R - N) - T K`. -/
def Kn (R K j : WA) : WA :=
  ((D.a0⁻¹ : ℝ) : ℂ) • ω.Sinv' α (ω.P2' (R - D.N α K j)) - D.T α K

/-- The `j`-update: `j' = (R - N) - J₀ K' - K'^* J₀`. -/
def jn (R K j : WA) : WA :=
  (R - D.N α K j) - ω.mul α D.J0 (D.Kn α R K j) - ω.mul α (ω.star (D.Kn α R K j)) D.J0

/-- `μ = (1 - c₀)/24`. -/
def μ : ℝ := (1 - D.c0) / 24
/-- `κ = μ λ`, the scaling of the `j`-coordinate. -/
def κ : ℝ := D.μ * D.lam
/-- The contraction constant `(1 + 3c₀)/4`. -/
def kc : ℝ := (1 + 3 * D.c0) / 4

lemma μ_pos : 0 < D.μ := by unfold μ; linarith [D.hc1]
lemma κ_pos : 0 < D.κ := mul_pos D.μ_pos D.lam_pos
lemma kc_nonneg : 0 ≤ D.kc := by unfold kc; linarith [D.hc0]
lemma kc_lt_one : D.kc < 1 := by unfold kc; linarith [D.hc1]

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

lemma Kn_sub (R K j K' j' : WA) :
    D.Kn α R K j - D.Kn α R K' j' =
      ((D.a0⁻¹ : ℝ) : ℂ) • ω.Sinv' α (ω.P2' (D.N α K' j' - D.N α K j)) - D.T α (K - K') := by
  unfold Kn
  rw [← D.T_sub α]
  have e : ((D.a0⁻¹ : ℝ) : ℂ) • ω.Sinv' α (ω.P2' (D.N α K' j' - D.N α K j)) =
      ((D.a0⁻¹ : ℝ) : ℂ) • ω.Sinv' α (ω.P2' (R - D.N α K j)) -
        ((D.a0⁻¹ : ℝ) : ℂ) • ω.Sinv' α (ω.P2' (R - D.N α K' j')) := by
    rw [← smul_sub, ← ω.Sinv'_sub, ← ω.P2'_sub]
    congr 3
    abel
  rw [e]
  abel

lemma jn_sub (R K j K' j' : WA) :
    D.jn α R K j - D.jn α R K' j' =
      (D.N α K' j' - D.N α K j) - ω.mul α D.J0 (D.Kn α R K j - D.Kn α R K' j') -
        ω.mul α (ω.star (D.Kn α R K j - D.Kn α R K' j')) D.J0 := by
  unfold jn
  rw [ω.mul_sub, ω.star_sub, ω.sub_mul]
  abel

/-- The coordinates: `z = (K, g)` with `j = κ^{-1} g`. -/
def jOf (g : WA) : WA := (((D.κ⁻¹ : ℝ)) : ℂ) • g

/-- The fixed-point map `Φ(K, g) = (K', κ j')`. -/
def Φ (R : WA) (z : WA × WA) : WA × WA :=
  (D.Kn α R z.1 (D.jOf z.2), ((D.κ : ℝ) : ℂ) • D.jn α R z.1 (D.jOf z.2))

lemma κN_eq (K g : WA) :
    ((D.κ : ℝ) : ℂ) • D.N α K (D.jOf g) = Nh (ω := ω) α (((D.κ : ℝ) : ℂ) • D.J0) K g := by
  unfold N jOf
  rw [Complex.ofReal_inv]
  exact smul_Nh α _ (Complex.ofReal_ne_zero.2 D.κ_pos.ne') _ _ _

/-- **The contraction estimate.** -/
lemma contract (R : WA) {ρ : ℝ} (hρ1 : ρ ≤ 1) (hρ2 : 9 * ρ ≤ D.μ * ((1 - D.c0) / 4))
    (z z' : WA × WA) (hz1 : ‖z.1‖ ≤ ρ) (hz2 : ‖z.2‖ ≤ ρ) (hz1' : ‖z'.1‖ ≤ ρ)
    (hz2' : ‖z'.2‖ ≤ ρ) :
    ‖(D.Φ α R z).1 - (D.Φ α R z').1‖ ≤ D.kc * dist z z' ∧
      ‖(D.Φ α R z).2 - (D.Φ α R z').2‖ ≤ D.kc * dist z z' := by
  set d := dist z z' with hd
  have hd1 : ‖z.1 - z'.1‖ ≤ d := by
    rw [hd, Prod.dist_eq, ← dist_eq_norm]; exact le_max_left _ _
  have hd2 : ‖z.2 - z'.2‖ ≤ d := by
    rw [hd, Prod.dist_eq, ← dist_eq_norm]; exact le_max_right _ _
  have hd0 : 0 ≤ d := dist_nonneg
  have hρ0 : 0 ≤ ρ := (norm_nonneg _).trans hz1
  have hμ := D.μ_pos
  have hκ := D.κ_pos
  have hc0 := D.hc0
  have hc1 := D.hc1
  -- the remainder
  have hN : D.κ * ‖D.N α z.1 (D.jOf z.2) - D.N α z'.1 (D.jOf z'.2)‖ ≤ 9 * ρ * d := by
    have h := norm_Nh_sub_le (ω := ω) α (((D.κ : ℝ) : ℂ) • D.J0) z.1 z.2 z'.1 z'.2 hρ1
      D.norm_κJ0_le_one hz1 hz1' hz2 hz2' hd1 hd2
    rw [← D.κN_eq, ← D.κN_eq, ← smul_sub, norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hκ] at h
    exact h
  -- the `K`-component
  have hK : ‖(D.Φ α R z).1 - (D.Φ α R z').1‖ ≤ D.kc * d := by
    simp only [Φ]
    rw [D.Kn_sub]
    refine (norm_sub_le _ _).trans ?_
    have h1 := D.norm_smulSinv_le' α (ω.P2' (D.N α z'.1 (D.jOf z'.2) - D.N α z.1 (D.jOf z.2)))
    have h2 := ω.norm_P2'_le (D.N α z'.1 (D.jOf z'.2) - D.N α z.1 (D.jOf z.2))
    have h3 := D.norm_T_le α (z.1 - z'.1)
    rw [norm_sub_rev] at h2
    have hlam : D.lam = D.κ / D.μ := by unfold κ; field_simp
    have h4 : D.lam * ‖D.N α z.1 (D.jOf z.2) - D.N α z'.1 (D.jOf z'.2)‖ ≤
        (9 * ρ * d) / D.μ := by
      rw [hlam, div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right hN hμ.le
    have h5 : (9 * ρ * d) / D.μ ≤ ((1 - D.c0) / 4) * d := by
      rw [div_le_iff₀ hμ]
      nlinarith
    have h6 : D.c0 * ‖z.1 - z'.1‖ ≤ D.c0 * d := mul_le_mul_of_nonneg_left hd1 hc0
    have h7 : D.lam * ‖ω.P2' _‖ ≤ D.lam * ‖_‖ := mul_le_mul_of_nonneg_left h2 D.lam_pos.le
    unfold kc
    linarith
  refine ⟨hK, ?_⟩
  -- the `j`-component
  simp only [Φ]
  rw [← smul_sub, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hκ, D.jn_sub]
  set ΔK := D.Kn α R z.1 (D.jOf z.2) - D.Kn α R z'.1 (D.jOf z'.2)
  have hΔK : ‖ΔK‖ ≤ D.kc * d := hK
  have hb : ‖(D.N α z'.1 (D.jOf z'.2) - D.N α z.1 (D.jOf z.2)) - ω.mul α D.J0 ΔK -
      ω.mul α (ω.star ΔK) D.J0‖ ≤
      ‖D.N α z.1 (D.jOf z.2) - D.N α z'.1 (D.jOf z'.2)‖ + 2 * (‖D.J0‖ * ‖ΔK‖) := by
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add (norm_sub_le _ _) le_rfl).trans ?_
    have m1 := ω.norm_mul_le α D.J0 ΔK
    have m2 := ω.norm_mul_le α (ω.star ΔK) D.J0
    rw [ω.norm_star] at m2
    rw [norm_sub_rev]
    nlinarith
  have hJ := D.κ_J0
  have hμ24 : D.μ ≤ 1 / 24 := by unfold μ; linarith
  have hkc := D.kc_nonneg
  calc D.κ * ‖_‖ ≤ D.κ * (‖D.N α z.1 (D.jOf z.2) - D.N α z'.1 (D.jOf z'.2)‖ +
        2 * (‖D.J0‖ * ‖ΔK‖)) := mul_le_mul_of_nonneg_left hb hκ.le
    _ = D.κ * ‖D.N α z.1 (D.jOf z.2) - D.N α z'.1 (D.jOf z'.2)‖ +
        2 * ((D.κ * ‖D.J0‖) * ‖ΔK‖) := by ring
    _ ≤ 9 * ρ * d + 2 * ((3 * D.μ) * (D.kc * d)) := by
        gcongr
    _ ≤ D.kc * d := by
        have : 9 * ρ ≤ (1 / 24) * ((1 - D.c0) / 4) := by nlinarith
        unfold kc at *
        nlinarith

/-! ### Self-adjointness is preserved -/

lemma star_U1 : ω.star (U1 (ω := ω)) = Um1 (ω := ω) := by
  apply ω.toS_injective
  rw [toS_star, toS_U1, toS_Um1, sstar_u1]

lemma star_Um1 : ω.star (Um1 (ω := ω)) = U1 (ω := ω) := by
  rw [← star_U1, ω.star_star]

lemma star_J0 : ω.star D.J0 = D.J0 := by
  unfold J0
  rw [ω.star_add, ω.star_add, ω.star_real_smul, ω.star_real_smul, star_U1, star_Um1, D.w_sa]
  abel

lemma star_N (K j : WA) (hj : ω.star j = j) : ω.star (D.N α K j) = D.N α K j := by
  unfold N Nh
  simp only [ω.star_add, ω.star_mul, ω.star_star, hj, D.star_J0]
  rw [ω.mul_assoc', ω.mul_assoc']
  abel

lemma star_jn (R K j : WA) (hR : ω.star R = R) (hj : ω.star j = j) :
    ω.star (D.jn α R K j) = D.jn α R K j := by
  unfold jn
  simp only [ω.star_sub, ω.star_mul, ω.star_star, hR, D.star_N α K j hj, D.star_J0]
  abel

lemma star_jOf (g : WA) (hg : ω.star g = g) : ω.star (D.jOf g) = D.jOf g := by
  unfold jOf; rw [ω.star_real_smul, hg]

/-! ### The invariant ball -/

/-- The ball `{‖K‖ ≤ ρ, ‖g‖ ≤ ρ, g = g^*}`. -/
def ball (ρ : ℝ) : Set (WA × WA) := {z | ‖z.1‖ ≤ ρ ∧ ‖z.2‖ ≤ ρ ∧ ω.star z.2 = z.2}

lemma isClosed_ball (ρ : ℝ) : IsClosed (ball (ω := ω) ρ) := by
  have e : ball (ω := ω) ρ =
      {z : WA × WA | ‖z.1‖ ≤ ρ} ∩ {z | ‖z.2‖ ≤ ρ} ∩ Prod.snd ⁻¹' {f | ω.star f = f} := by
    ext z
    simp only [ball, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, and_assoc]
  rw [e]
  exact ((isClosed_le (continuous_norm.comp continuous_fst) continuous_const).inter
    (isClosed_le (continuous_norm.comp continuous_snd) continuous_const)).inter
    (ω.isClosed_selfAdjoint.preimage continuous_snd)

lemma zero_mem_ball {ρ : ℝ} (hρ : 0 ≤ ρ) : (0 : WA × WA) ∈ ball (ω := ω) ρ :=
  ⟨by simpa using hρ, by simpa using hρ, by simpa using ω.star_zero'⟩

lemma N_zero : D.N α 0 0 = 0 := Nh_zero α D.J0

lemma jOf_zero : D.jOf 0 = 0 := by simp [jOf]

lemma Kn_zero (R : WA) : D.Kn α R 0 (D.jOf 0) = ((D.a0⁻¹ : ℝ) : ℂ) • ω.Sinv' α (ω.P2' R) := by
  rw [jOf_zero]; unfold Kn; rw [N_zero, T_zero, sub_zero, sub_zero]

lemma norm_Φ0 (R : WA) :
    ‖(D.Φ α R 0).1‖ ≤ D.lam * ‖R‖ ∧ ‖(D.Φ α R 0).2‖ ≤ D.lam * ‖R‖ := by
  have hK0 : ‖(D.Φ α R 0).1‖ ≤ D.lam * ‖R‖ := by
    simp only [Φ, Prod.fst_zero, Prod.snd_zero]
    rw [Kn_zero]
    exact (D.norm_smulSinv_le' α _).trans
      (mul_le_mul_of_nonneg_left (ω.norm_P2'_le R) D.lam_pos.le)
  refine ⟨hK0, ?_⟩
  simp only [Φ, Prod.fst_zero, Prod.snd_zero] at hK0 ⊢
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos D.κ_pos]
  unfold jn
  rw [jOf_zero, N_zero, sub_zero] at *
  set K0 := D.Kn α R 0 0
  have hb : ‖R - ω.mul α D.J0 K0 - ω.mul α (ω.star K0) D.J0‖ ≤ ‖R‖ + 2 * (‖D.J0‖ * ‖K0‖) := by
    refine (norm_sub_le _ _).trans ?_
    refine (add_le_add (norm_sub_le _ _) le_rfl).trans ?_
    have m1 := ω.norm_mul_le α D.J0 K0
    have m2 := ω.norm_mul_le α (ω.star K0) D.J0
    rw [ω.norm_star] at m2
    nlinarith
  have hJ := D.κ_J0
  have hμ24 : D.μ ≤ 1 / 24 := by unfold μ; linarith [D.hc0]
  have hκR : D.κ * ‖R‖ = D.μ * (D.lam * ‖R‖) := by unfold κ; ring
  have hσ0 : 0 ≤ D.lam * ‖R‖ := mul_nonneg D.lam_pos.le (norm_nonneg _)
  have hK0' : ‖K0‖ ≤ D.lam * ‖R‖ := hK0
  calc D.κ * ‖_‖ ≤ D.κ * (‖R‖ + 2 * (‖D.J0‖ * ‖K0‖)) := mul_le_mul_of_nonneg_left hb D.κ_pos.le
    _ = D.κ * ‖R‖ + 2 * ((D.κ * ‖D.J0‖) * ‖K0‖) := by ring
    _ ≤ D.μ * (D.lam * ‖R‖) + 2 * ((3 * D.μ) * (D.lam * ‖R‖)) := by
        rw [hκR]
        have : 0 ≤ 3 * D.μ := by linarith [D.μ_pos]
        gcongr
    _ ≤ D.lam * ‖R‖ := by nlinarith

/-- **Existence of the fixed point.** -/
theorem exists_fixed (R : WA) (hR : ω.star R = R) {ρ : ℝ} (hρ1 : ρ ≤ 1)
    (hρ2 : 9 * ρ ≤ D.μ * ((1 - D.c0) / 4)) (hσ : D.lam * ‖R‖ = (1 - D.kc) * ρ) :
    ∃ z ∈ ball (ω := ω) ρ, D.Φ α R z = z := by
  have hkc0 := D.kc_nonneg
  have hkc1 := D.kc_lt_one
  have hσ0 : 0 ≤ D.lam * ‖R‖ := mul_nonneg D.lam_pos.le (norm_nonneg _)
  have hρ0 : 0 ≤ ρ := by nlinarith
  have hlip : ∀ x ∈ ball (ω := ω) ρ, ∀ y ∈ ball (ω := ω) ρ,
      dist (D.Φ α R x) (D.Φ α R y) ≤ D.kc * dist x y := by
    intro x hx y hy
    have hc := D.contract α R hρ1 hρ2 x y hx.1 hx.2.1 hy.1 hy.2.1
    rw [Prod.dist_eq, dist_eq_norm, dist_eq_norm]
    exact max_le hc.1 hc.2
  have hmaps : Set.MapsTo (D.Φ α R) (ball (ω := ω) ρ) (ball (ω := ω) ρ) := by
    intro x hx
    have h0mem := zero_mem_ball (ω := ω) hρ0
    have hc := D.contract α R hρ1 hρ2 x 0 hx.1 hx.2.1 h0mem.1 h0mem.2.1
    have hdist : dist x 0 ≤ ρ := by
      rw [Prod.dist_eq]
      simp only [Prod.fst_zero, Prod.snd_zero, dist_zero_right]
      exact max_le hx.1 hx.2.1
    have h0 := D.norm_Φ0 α R
    have hkd : D.kc * dist x 0 ≤ D.kc * ρ := mul_le_mul_of_nonneg_left hdist hkc0
    refine ⟨?_, ?_, ?_⟩
    · have := norm_sub_norm_le (D.Φ α R x).1 (D.Φ α R 0).1
      linarith [hc.1]
    · have := norm_sub_norm_le (D.Φ α R x).2 (D.Φ α R 0).2
      linarith [hc.2]
    · simp only [Φ]
      rw [ω.star_real_smul, D.star_jn α R _ _ hR (D.star_jOf _ hx.2.2)]
  exact exists_fixed_of_contract (isClosed_ball ρ) (zero_mem_ball hρ0) hmaps hkc0 hkc1 hlip

/-! ### Structure of the fixed point -/

lemma mul_U1_Sinv' (Y : WA) : ω.mul α (U1 (ω := ω)) (ω.Sinv' α Y) = ω.P2' Y := by
  apply ω.toS_injective
  rw [toS_mul, toS_U1, toS_Sinv', toS_P2', u1_tmul_Sinv]

lemma P2'_P2' (Y : WA) : ω.P2' (ω.P2' Y) = ω.P2' Y := by
  apply ω.toS_injective
  rw [toS_P2', toS_P2', P2_P2]

lemma P2'_mul_U1 {K : WA} (hK : HopGE (ω.toS K) 1) :
    ω.P2' (ω.mul α (U1 (ω := ω)) K) = ω.mul α (U1 (ω := ω)) K := by
  apply ω.toS_injective
  rw [toS_P2', toS_mul, toS_U1]
  exact P2_of_HopGE (hK.u1_tmul (α := α))

lemma toS_J0 : ω.toS D.J0 = (D.a0 : ℂ) • u1 + (D.a0 : ℂ) • um1 + ω.toS D.w := by
  unfold J0
  rw [ω.toS_add, ω.toS_add, ω.toS_smul, ω.toS_smul, toS_U1, toS_Um1]

lemma HopLE_J0 : HopLE (ω.toS D.J0) 1 := by
  rw [toS_J0]
  exact ((HopLE_u1.smul _).add ((HopLE_um1.smul _).mono (by norm_num))).add
    (D.w_le.mono (by norm_num))

lemma P2'_star_mul_J0 {K : WA} (hK : HopGE (ω.toS K) 1) :
    ω.P2' (ω.mul α (ω.star K) D.J0) = 0 := by
  apply ω.toS_injective
  rw [toS_P2', toS_mul, toS_star, ω.toS_zero]
  exact P2_of_HopLE ((hK.sstar.tmul (α := α) D.HopLE_J0).mono (by norm_num))

/-- Properties of a fixed point `z = Φ(z)` in the ball. -/
theorem fixed_point_props (R : WA) {ρ : ℝ} (z : WA × WA) (hz : z ∈ ball (ω := ω) ρ)
    (hfix : D.Φ α R z = z) :
    HopGE (ω.toS z.1) 1 ∧ HopLE (ω.toS (D.jOf z.2)) 1 ∧ HopGE (ω.toS (D.jOf z.2)) (-1) ∧
      ω.star (D.jOf z.2) = D.jOf z.2 ∧
      ω.mul α (ω.mul α (ω.star (ω.one' + z.1)) (D.J0 + D.jOf z.2)) (ω.one' + z.1) =
        D.J0 + R := by
  set K := z.1
  set j := D.jOf z.2
  have hK : D.Kn α R K j = K := congrArg Prod.fst hfix
  have hj : D.jn α R K j = j := by
    have h2 : ((D.κ : ℝ) : ℂ) • D.jn α R K j = z.2 := congrArg Prod.snd hfix
    show _ = D.jOf z.2
    rw [← h2, jOf, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ D.κ_pos.ne',
      Complex.ofReal_one, one_smul]
  have hjsa : ω.star j = j := D.star_jOf _ hz.2.2
  -- `K` lives on hopping indices `≥ 1`
  have hKge : HopGE (ω.toS K) 1 := by
    rw [← hK]
    unfold Kn T
    rw [ω.toS_sub, ω.toS_smul, ω.toS_smul, toS_Sinv', toS_Sinv']
    exact ((HopGE_Sinv _).smul _).sub ((HopGE_Sinv _).smul _)
  -- `Π_{≥2} j = 0`
  set X := ω.mul α D.w K + (D.a0 : ℂ) • ω.mul α (Um1 (ω := ω)) K
  set A := ω.P2' (R - D.N α K j)
  have hU : (D.a0 : ℂ) • ω.mul α (U1 (ω := ω)) K = A - ω.P2' X := by
    conv_lhs => rw [← hK]
    unfold Kn T
    rw [ω.mul_sub, ω.mul_smul, ω.mul_smul, mul_U1_Sinv', mul_U1_Sinv', P2'_P2', P2'_P2',
      ← smul_sub, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ D.ha0.ne',
      Complex.ofReal_one, one_smul]
  have hP2J0K : ω.P2' (ω.mul α D.J0 K) = (D.a0 : ℂ) • ω.mul α (U1 (ω := ω)) K + ω.P2' X := by
    unfold J0
    rw [ω.add_mul, ω.add_mul, ω.smul_mul, ω.smul_mul, ω.P2'_add, ω.P2'_add, ω.P2'_smul,
      ω.P2'_smul, P2'_mul_U1 α hKge]
    simp only [X, ω.P2'_add, ω.P2'_smul]
    abel
  have hP2j : ω.P2' j = 0 := by
    rw [← hj]
    unfold jn
    rw [hK, ω.P2'_sub, ω.P2'_sub, D.P2'_star_mul_J0 α hKge, hP2J0K, hU]
    abel
  have hjle : HopLE (ω.toS j) 1 := by
    apply HopLE_of_P2
    rw [← toS_P2', hP2j, ω.toS_zero]
  have hjge : HopGE (ω.toS j) (-1) := by
    have h := hjle.sstar
    rwa [← toS_star, hjsa] at h
  refine ⟨hKge, hjle, hjge, hjsa, ?_⟩
  -- the factorization
  have hR : R = j + D.N α K j + ω.mul α D.J0 K + ω.mul α (ω.star K) D.J0 := by
    have h1 : R = (R - D.N α K j - ω.mul α D.J0 K - ω.mul α (ω.star K) D.J0) + D.N α K j +
        ω.mul α D.J0 K + ω.mul α (ω.star K) D.J0 := by abel
    have h2 : R - D.N α K j - ω.mul α D.J0 K - ω.mul α (ω.star K) D.J0 = j := by
      have h := hj
      unfold jn at h
      rw [hK] at h
      exact h
    rw [h2] at h1
    exact h1
  rw [ω.star_add, ω.star_one', ω.add_mul, ω.one'_mul, ω.mul_add, ω.mul_add, ω.mul_one',
    ω.add_mul, ω.add_mul, ω.add_mul]
  conv_rhs => rw [hR]
  unfold N Nh
  abel

end Data

/-! ### The theorem -/

/-- The smallness threshold `σ₀(c₀)` of Lemma 2.1. -/
def sig0 (c0 : ℝ) : ℝ := (3 * (1 - c0) / 4) * min 1 ((1 - c0) / 24 * ((1 - c0) / 4) / 9)

/-- The constant `C(c₀)` of Lemma 2.1. -/
def Cst (c0 : ℝ) : ℝ := (1 + 24 / (1 - c0)) / (3 * (1 - c0) / 4)

lemma sig0_pos {c0 : ℝ} (hc1 : c0 < 1) : 0 < sig0 c0 := by
  unfold sig0
  have h : 0 < 1 - c0 := by linarith
  apply mul_pos (by positivity)
  exact lt_min one_pos (by positivity)

/-- **Lemma 2.1 (preparation in the scaled Banach algebra).**  If
`e^{-s} a₀^{-1} ‖w‖ + e^{-2s} ≤ c₀ < 1` and `R = R^*` with
`σ = e^{-s} a₀^{-1} ‖R‖_{s,ℓ} ≤ σ₀(c₀)`, then there are `K` (hopping `≥ 1`) and a self-adjoint
Jacobi correction `j` (hopping in `{-1,0,1}`) with
`(I + K)^* (J₀ + j)(I + K) = J₀ + R` and `‖K‖ + e^{-s} a₀^{-1} ‖j‖ ≤ C(c₀) σ`. -/
theorem scaled_preparation (D : Data ω) (R : WA) (hR : ω.star R = R)
    (hsmall : D.lam * ‖R‖ ≤ sig0 D.c0) :
    ∃ K j : WA, HopGE (ω.toS K) 1 ∧ HopLE (ω.toS j) 1 ∧ HopGE (ω.toS j) (-1) ∧
      ω.star j = j ∧
      ω.mul α (ω.mul α (ω.star (ω.one' + K)) (D.J0 + j)) (ω.one' + K) = D.J0 + R ∧
      ‖K‖ + D.lam * ‖j‖ ≤ Cst D.c0 * (D.lam * ‖R‖) := by
  have hc1 := D.hc1
  have h1c : 0 < 1 - D.c0 := by linarith
  have hkc : 1 - D.kc = 3 * (1 - D.c0) / 4 := by unfold Data.kc; ring
  have hkpos : 0 < 1 - D.kc := by rw [hkc]; positivity
  set σ := D.lam * ‖R‖ with hσdef
  set ρ := σ / (1 - D.kc) with hρdef
  have hσ0 : 0 ≤ σ := mul_nonneg D.lam_pos.le (norm_nonneg _)
  have hρ0 : 0 ≤ ρ := div_nonneg hσ0 hkpos.le
  have hρle : ρ ≤ min 1 ((1 - D.c0) / 24 * ((1 - D.c0) / 4) / 9) := by
    rw [hρdef, div_le_iff₀ hkpos, mul_comm, hkc]
    exact hsmall
  have hρ1 : ρ ≤ 1 := hρle.trans (min_le_left _ _)
  have hρ2 : 9 * ρ ≤ D.μ * ((1 - D.c0) / 4) := by
    have := hρle.trans (min_le_right _ _)
    unfold Data.μ
    linarith
  have hσρ : σ = (1 - D.kc) * ρ := by rw [hρdef]; field_simp
  obtain ⟨z, hz, hfix⟩ := D.exists_fixed α R hR hρ1 hρ2 hσρ
  obtain ⟨hK, hjle, hjge, hjsa, hid⟩ := D.fixed_point_props α R z hz hfix
  refine ⟨z.1, D.jOf z.2, hK, hjle, hjge, hjsa, hid, ?_⟩
  -- the bound
  have hz1 : ‖z.1‖ ≤ ρ := hz.1
  have hj : ‖D.jOf z.2‖ ≤ ρ / D.κ := by
    unfold Data.jOf
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 D.κ_pos),
      inv_mul_eq_div]
    exact div_le_div_of_nonneg_right hz.2.1 D.κ_pos.le
  have hlj : D.lam * ‖D.jOf z.2‖ ≤ ρ / D.μ := by
    calc D.lam * ‖D.jOf z.2‖ ≤ D.lam * (ρ / D.κ) := mul_le_mul_of_nonneg_left hj D.lam_pos.le
      _ = ρ / D.μ := by
        unfold Data.κ
        field_simp [D.lam_pos.ne', D.μ_pos.ne']
  have hC : ρ + ρ / D.μ = Cst D.c0 * σ := by
    unfold Cst Data.μ
    rw [hρdef, ← hkc]
    field_simp
  linarith

/-! ### Operator form -/

open scoped InnerProductSpace

lemma op_neg' (α : ℝ) (R : Symbol) (x : ℝ) : op α (-R) x = -op α R x := by
  unfold op
  rw [← tsum_neg]
  congr 1
  funext p
  exact neg_smul (R p) (W α x p.1 p.2)

/-- **Operator form of Lemma 2.1.**  On every fibre,
`(J₀ + R)_x = Q_x^* (J₀ + j)_x Q_x` with `Q = I + K`. -/
theorem operator_factorization (D : Data ω) (R K j : WA)
    (hid : ω.mul α (ω.mul α (ω.star (ω.one' + K)) (D.J0 + j)) (ω.one' + K) = D.J0 + R)
    (x : ℝ) :
    op α (ω.toS (D.J0 + R)) x =
      star (op α (ω.toS (ω.one' + K)) x) * op α (ω.toS (D.J0 + j)) x *
        op α (ω.toS (ω.one' + K)) x := by
  rw [← hid, ω.toS_mul, op_tmul (ω.toS_summable _) (ω.toS_summable _), ω.toS_mul,
    op_tmul (ω.toS_summable _) (ω.toS_summable _), ω.toS_star, op_sstar (ω.toS_summable _)]

/-- **`Q = I + K` and `Q^{-1}` are exponentially local** when `‖K‖_{s,ℓ} < 1`. -/
theorem Q_exp_local (K : WA) (hK : ‖K‖ < 1) (x : ℝ) :
    ∃ Qi : L2 ℤ →L[ℂ] L2 ℤ,
      op α (ω.toS (ω.one' + K)) x * Qi = 1 ∧ Qi * op α (ω.toS (ω.one' + K)) x = 1 ∧
      (∀ n m : ℤ, ‖⟪delta n, Qi (delta m)⟫_ℂ‖ ≤
        (1 - ‖K‖)⁻¹ * Real.exp (-ω.s * |((n - m : ℤ) : ℝ)|)) ∧
      (∀ n m : ℤ, ‖⟪delta n, op α (ω.toS (ω.one' + K)) x (delta m)⟫_ℂ‖ ≤
        ‖ω.one' + K‖ * Real.exp (-ω.s * |((n - m : ℤ) : ℝ)|)) := by
  set L : Symbol := -ω.toS K
  have hL : WSum ω.s ω.ℓ L := by
    have := ω.toS_wsum K
    unfold WSum at *
    simpa [L] using this
  have hLn : wnorm ω.s ω.ℓ L = ‖K‖ := by
    rw [← ω.wnorm_toS K, wnorm_eq, wnorm_eq]
    simp [L]
  have hq : wnorm ω.s ω.ℓ L < 1 := hLn ▸ hK
  have hQ : op α (ω.toS (ω.one' + K)) x = 1 - op α L x := by
    rw [ω.toS_add, toS_one', op_add (one_wsum.symbolSummable ω.hs ω.hℓ) (ω.toS_summable K),
      op_one, op_neg', sub_neg_eq_add]
  obtain ⟨h1, h2⟩ := neumann_inverse ω.hs ω.hℓ hL hq (α := α) x
  refine ⟨op α (neumann α L) x, by rw [hQ]; exact h1, by rw [hQ]; exact h2, ?_, ?_⟩
  · intro n m
    have := norm_entry_inverse_le ω.hs ω.hℓ hL hq (α := α) x n m
    rwa [hLn] at this
  · intro n m
    have := norm_entry_le ω.hs ω.hℓ (ω.toS_wsum (ω.one' + K)) (α := α) x n m
    rwa [ω.wnorm_toS] at this

end ScaledPrep

end AMO
