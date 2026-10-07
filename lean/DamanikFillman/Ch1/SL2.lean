/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §1.13  `SL(2,ℝ)` and `SL(2,ℂ)`  (book pp. 113–121)

Matrices are plain `2 × 2` matrices with a determinant hypothesis `det = 1`; norms are the
Euclidean operator norms (`Matrix.Norms.L2Operator`), as in (1.13.2).  Real matrices act on
`E2 = EuclideanSpace ℝ (Fin 2)` through `DF.act`.

## Main results
* (1.13.5)/(1.13.6): `DF.inv_eq_Jsym`, `DF.Jflip_conj` — symplectic identities.
* **Proposition 1.13.1**: `DF.norm_inv_eq_norm` (`‖M⁻¹‖ = ‖M‖` in `SL(2,ℂ)`) and
  `DF.norm_prod_eq_norm_reverse_prod` (`‖M₁⋯Mₙ‖ = ‖Mₙ⋯M₁‖` when `Tr(J'Mₖ) = 0`).
* (1.13.3): `DF.transpose_mul_self_eq_one_iff_rot`, `DF.isometry_iff_transpose_mul_self`,
  `DF.norm_eq_one_iff_transpose_mul_self` — descriptions of `SO(2,ℝ)`.
* **Definition 1.13.2**: `DF.IsEllipticTr`, `DF.IsHyperbolicTr`, `DF.IsParabolicTr`.
* **Theorem 1.13.3** (book: exercise): `DF.elliptic_eigen`, `DF.hyperbolic_eigen`,
  `DF.parabolic_similar`.
* (1.13.11): the angle between lines `DF.pangle`, with `DF.sin_pangle`.
* **Proposition 1.13.5** (singular value decomposition, real case): the structure
  `DF.SVData` and `DF.exists_svd`; (a) `SVData.norm_Au`, `SVData.norm_As`;
  uniqueness `SVData.inner_s_eq_zero_of_max`, `SVData.inner_u_eq_zero_of_min`; (b) by
  construction (`inner_perp`); (d) `SVData.transpose_top`, `SVData.transpose_bottom`;
  (e) `SVData.sin_sq_pangle`, `SVData.pangle_bounds`, `SVData.pangle_le`.
* **Proposition 1.13.6**: `DF.smul_I_eq_I_iff`.
* **Proposition 1.13.7**: `DF.elliptic_iff_existsUnique_fixed`,
  `DF.exists_conj_rot`, `DF.conj_rot_unique`.

## Deviations
* Proposition 1.13.5 is proved for `SL(2,ℝ)` (which is what §1.14 uses); part (c) is then
  automatic, and the continuity statement (f) is not formalized.  The subspaces `S(A)`,
  `U(A)` are represented by unit vectors `u`, `s = perp u`.
* Theorem 1.13.8 / Lemma 1.13.9 (non-commuting matrices generate unbounded subgroups) are in
  `DamanikFillman/Ch1/SL2Nonabelian.lean`.
-/
import Mathlib

noncomputable section

open scoped Matrix.Norms.L2Operator RealInnerProductSpace ComplexConjugate MatrixGroups
open Matrix

namespace DF

/-- Real `2 × 2` matrices. -/
abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ
/-- Complex `2 × 2` matrices. -/
abbrev M2C := Matrix (Fin 2) (Fin 2) ℂ
/-- Euclidean `ℝ²`. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

/-! ### Symplectic identities (1.13.4)–(1.13.7) -/

section Symplectic

variable {R : Type*} [CommRing R]

/-- The symplectic matrix `J` of (1.13.4). -/
def Jsym : Matrix (Fin 2) (Fin 2) R := !![0, 1; -1, 0]

/-- The flip matrix `J'` of (1.13.7). -/
def Jflip : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 0]

/-- (1.13.5): for `det M = 1`, `M⁻¹ = J Mᵀ Jᵀ`. -/
theorem inv_eq_Jsym (M : Matrix (Fin 2) (Fin 2) R) (h : M.det = 1) :
    M⁻¹ = Jsym * Mᵀ * Jsymᵀ := by
  rw [Matrix.inv_def, h, Ring.inverse_one, one_smul, adjugate_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Jsym, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]

lemma Jflip_mul_self : (Jflip : Matrix (Fin 2) (Fin 2) R) * Jflip = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Jflip, Matrix.mul_apply, Fin.sum_univ_two]

/-- `Tr(J' M) = b + c`. -/
lemma trace_Jflip_mul (M : Matrix (Fin 2) (Fin 2) R) : (Jflip * M).trace = M 0 1 + M 1 0 := by
  simp [Jflip, Matrix.trace_fin_two, Matrix.vecMul, dotProduct, Fin.sum_univ_two]; ring

/-- (1.13.6): if `det M = 1` and `b + c = 0`, then `J' M J'⁻¹ = M⁻¹` (note `J'⁻¹ = J'`). -/
theorem Jflip_conj (M : Matrix (Fin 2) (Fin 2) R) (h : M.det = 1) (hbc : M 0 1 + M 1 0 = 0) :
    Jflip * M * Jflip = M⁻¹ := by
  rw [Matrix.inv_def, h, Ring.inverse_one, one_smul, adjugate_fin_two]
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Jflip, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct] <;>
    linear_combination hbc

lemma det_list_prod {l : List (Matrix (Fin 2) (Fin 2) R)} (h : ∀ M ∈ l, M.det = 1) :
    l.prod.det = 1 := by
  induction l with
  | nil => simp
  | cons M l ih =>
    rw [List.prod_cons, det_mul, h M (by simp), ih fun N hN => h N (by simp [hN]), one_mul]

end Symplectic

/-! ### Norms in `SL(2,ℂ)`: Proposition 1.13.1 -/

section NormC

lemma norm_map_star_le (M : M2C) : ‖M.map star‖ ≤ ‖M‖ := by
  rw [cstar_norm_def (A := M.map star)]
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun x => ?_
  set y : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 (fun i => star (x i))
  have h1 : ‖toEuclideanCLM (𝕜 := ℂ) (M.map star) x‖ = ‖toEuclideanCLM (𝕜 := ℂ) M y‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    have : (toEuclideanCLM (𝕜 := ℂ) (M.map star) x) i =
        star ((toEuclideanCLM (𝕜 := ℂ) M y) i) := by
      fin_cases i <;> simp [y, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    rw [this, norm_star]
  have h2 : ‖y‖ = ‖x‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [y]
  rw [h1, ← h2]
  exact (toEuclideanCLM (𝕜 := ℂ) M).le_opNorm y

lemma norm_map_star (M : M2C) : ‖M.map star‖ = ‖M‖ := by
  refine le_antisymm (norm_map_star_le M) ?_
  have := norm_map_star_le (M.map star)
  have hM : (M.map star).map star = M := by ext i j; simp
  rwa [hM] at this

/-- The Euclidean operator norm is invariant under transposition. -/
lemma norm_transpose_C (M : M2C) : ‖Mᵀ‖ = ‖M‖ := by
  have : Mᵀ = (M.map star)ᴴ := by ext i j; simp [conjTranspose_apply]
  rw [this, l2_opNorm_conjTranspose, norm_map_star]

lemma Jsym_mem_unitary : (Jsym : M2C) ∈ unitary M2C := by
  rw [Unitary.mem_iff, star_eq_conjTranspose]
  constructor <;>
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Jsym, Matrix.mul_apply, Fin.sum_univ_two, conjTranspose_apply]

lemma Jsym_transpose_mem_unitary : (Jsymᵀ : M2C) ∈ unitary M2C := by
  rw [Unitary.mem_iff, star_eq_conjTranspose]
  constructor <;>
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Jsym, Matrix.mul_apply, Fin.sum_univ_two, conjTranspose_apply]

lemma Jflip_mem_unitary : (Jflip : M2C) ∈ unitary M2C := by
  rw [Unitary.mem_iff, star_eq_conjTranspose]
  constructor <;>
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [Jflip, Matrix.mul_apply, Fin.sum_univ_two, conjTranspose_apply]

lemma norm_unitary_conj {U V : M2C} (hU : U ∈ unitary M2C) (hV : V ∈ unitary M2C) (X : M2C) :
    ‖U * X * V‖ = ‖X‖ := by
  have h1 := CStarRing.norm_mul_coe_unitary (U * X) ⟨V, hV⟩
  have h2 := CStarRing.norm_coe_unitary_mul ⟨U, hU⟩ X
  simp only at h1 h2
  rw [h1, h2]

/-- **Proposition 1.13.1**, first claim: `‖M⁻¹‖ = ‖M‖` for `M ∈ SL(2,ℂ)`. -/
theorem norm_inv_eq_norm (M : M2C) (h : M.det = 1) : ‖M⁻¹‖ = ‖M‖ := by
  rw [inv_eq_Jsym M h, norm_unitary_conj Jsym_mem_unitary Jsym_transpose_mem_unitary,
    norm_transpose_C]

lemma map_Jflip_conj_prod (l : List M2C) :
    Jflip * l.prod * Jflip = (l.map fun M => Jflip * M * Jflip).prod := by
  induction l with
  | nil => simp [Jflip_mul_self]
  | cons M l ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons, ← ih]
    calc Jflip * (M * l.prod) * Jflip = Jflip * M * (Jflip * Jflip) * l.prod * Jflip := by
          rw [Jflip_mul_self]; noncomm_ring
      _ = Jflip * M * Jflip * (Jflip * l.prod * Jflip) := by noncomm_ring

lemma prod_map_inv (l : List M2C) : (l.map fun M => M⁻¹).prod = l.reverse.prod⁻¹ := by
  induction l with
  | nil => simp
  | cons M l ih =>
    rw [List.map_cons, List.prod_cons, ih, List.reverse_cons, List.prod_append,
      List.prod_singleton, Matrix.mul_inv_rev]

/-- **Proposition 1.13.1**, second claim (1.13.8): if `det Mₖ = 1` and `Tr(J' Mₖ) = 0` for all
`k`, then `‖M₁ ⋯ Mₙ‖ = ‖Mₙ ⋯ M₁‖`. -/
theorem norm_prod_eq_norm_reverse_prod (l : List M2C) (hdet : ∀ M ∈ l, M.det = 1)
    (htr : ∀ M ∈ l, (Jflip * M).trace = 0) : ‖l.prod‖ = ‖l.reverse.prod‖ := by
  have h1 : Jflip * l.prod * Jflip = l.reverse.prod⁻¹ := by
    rw [map_Jflip_conj_prod, ← prod_map_inv]
    congr 1
    refine List.map_congr_left fun M hM => ?_
    exact Jflip_conj M (hdet M hM) (by rw [← trace_Jflip_mul]; exact htr M hM)
  have h2 : l.reverse.prod.det = 1 := det_list_prod fun M hM => hdet M (List.mem_reverse.mp hM)
  rw [← norm_inv_eq_norm _ h2, ← h1, norm_unitary_conj Jflip_mem_unitary Jflip_mem_unitary]

end NormC

/-! ### Euclidean `ℝ²` and the action of real matrices -/

section Plane

/-- The action of a real `2 × 2` matrix on `ℝ²`. -/
def act (A : M2R) : E2 →L[ℝ] E2 := toEuclideanCLM (𝕜 := ℝ) A

@[simp] lemma act_apply (A : M2R) (v : E2) (i : Fin 2) :
    act A v i = A i 0 * v 0 + A i 1 * v 1 := by
  simp [act, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma act_mul (A B : M2R) (v : E2) : act (A * B) v = act A (act B v) := by
  simp [act, map_mul]

@[simp] lemma act_one (v : E2) : act 1 v = v := by simp [act]

lemma norm_act_eq (A : M2R) : ‖act A‖ = ‖A‖ := rfl

lemma norm_act_le (A : M2R) (v : E2) : ‖act A v‖ ≤ ‖A‖ * ‖v‖ := (act A).le_opNorm v

lemma norm_sq_E2 (v : E2) : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_two]

lemma inner_E2 (u v : E2) : ⟪u, v⟫ = u 0 * v 0 + u 1 * v 1 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

/-- `cross u v = det [u v]`. -/
def cross (u v : E2) : ℝ := u 0 * v 1 - u 1 * v 0

lemma cross_act (A : M2R) (u v : E2) : cross (act A u) (act A v) = A.det * cross u v := by
  simp only [cross, act_apply, det_fin_two]; ring

lemma cross_comm (u v : E2) : cross u v = - cross v u := by simp only [cross]; ring

lemma cross_smul_left (c : ℝ) (u v : E2) : cross (c • u) v = c * cross u v := by
  simp only [cross, PiLp.smul_apply, smul_eq_mul]; ring

lemma cross_smul_right (c : ℝ) (u v : E2) : cross u (c • v) = c * cross u v := by
  simp only [cross, PiLp.smul_apply, smul_eq_mul]; ring

/-- Lagrange's identity in the plane. -/
lemma lagrange (u v : E2) : ‖u‖ ^ 2 * ‖v‖ ^ 2 = ⟪u, v⟫ ^ 2 + cross u v ^ 2 := by
  rw [norm_sq_E2, norm_sq_E2, inner_E2, cross]; ring

lemma abs_cross_le (u v : E2) : |cross u v| ≤ ‖u‖ * ‖v‖ := by
  have h := lagrange u v
  rw [← sq_le_sq₀ (abs_nonneg _) (by positivity), sq_abs, mul_pow, h]
  nlinarith [sq_nonneg ⟪u, v⟫]

/-- Rotation by `π/2`. -/
def perp (u : E2) : E2 := WithLp.toLp 2 ![-u 1, u 0]

@[simp] lemma perp_apply_zero (u : E2) : perp u 0 = -u 1 := by simp [perp]
@[simp] lemma perp_apply_one (u : E2) : perp u 1 = u 0 := by simp [perp]

lemma norm_perp (u : E2) : ‖perp u‖ = ‖u‖ := by
  have h : ‖perp u‖ ^ 2 = ‖u‖ ^ 2 := by rw [norm_sq_E2, norm_sq_E2]; simp; ring
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

lemma inner_perp (u : E2) : ⟪u, perp u⟫ = 0 := by
  rw [inner_E2]; simp only [perp_apply_zero, perp_apply_one]; ring

lemma cross_perp (u : E2) : cross u (perp u) = ‖u‖ ^ 2 := by
  rw [norm_sq_E2, cross]; simp only [perp_apply_zero, perp_apply_one]; ring

lemma cross_perp_right (x u : E2) : cross x (perp u) = ⟪x, u⟫ := by
  rw [inner_E2, cross]; simp only [perp_apply_zero, perp_apply_one]; ring

lemma inner_perp_right (x u : E2) : ⟪x, perp u⟫ = cross u x := by
  rw [inner_E2, cross]; simp only [perp_apply_zero, perp_apply_one]; ring

/-- Orthonormal decomposition along `u`, `perp u` for a unit vector `u`. -/
lemma decomp (u : E2) (hu : ‖u‖ = 1) (w : E2) :
    w = ⟪w, u⟫ • u + ⟪w, perp u⟫ • perp u := by
  have h1 : u 0 ^ 2 + u 1 ^ 2 = 1 := by rw [← norm_sq_E2, hu]; norm_num
  ext i; fin_cases i
  · simp [inner_E2]; linear_combination (-(w 0)) * h1
  · simp [inner_E2]; linear_combination (-(w 1)) * h1

lemma norm_sq_decomp (u : E2) (hu : ‖u‖ = 1) (w : E2) :
    ‖w‖ ^ 2 = ⟪w, u⟫ ^ 2 + ⟪w, perp u⟫ ^ 2 := by
  have h1 : u 0 ^ 2 + u 1 ^ 2 = 1 := by rw [← norm_sq_E2, hu]; norm_num
  rw [norm_sq_E2, inner_E2, inner_E2]; simp
  linear_combination -(w 0 ^ 2 + w 1 ^ 2) * h1

/-- Triangle inequality for the "sine distance" `|cross|`. -/
lemma abs_cross_triangle (x y z : E2) (hy : ‖y‖ = 1) (hx : ‖x‖ ≤ 1) (hz : ‖z‖ ≤ 1) :
    |cross x z| ≤ |cross x y| + |cross y z| := by
  have hy2 : y 0 ^ 2 + y 1 ^ 2 = 1 := by rw [← norm_sq_E2, hy]; norm_num
  have hid : cross x z = ⟪x, y⟫ * cross y z + cross x y * ⟪y, z⟫ := by
    rw [inner_E2, inner_E2]; simp only [cross]; linear_combination
      (-(x 0 * z 1) + x 1 * z 0) * hy2
  have h1 : |⟪x, y⟫| ≤ 1 := (abs_real_inner_le_norm x y).trans (by rw [hy]; nlinarith [norm_nonneg x])
  have h2 : |⟪y, z⟫| ≤ 1 := (abs_real_inner_le_norm y z).trans (by rw [hy]; nlinarith [norm_nonneg z])
  rw [hid]
  calc |⟪x, y⟫ * cross y z + cross x y * ⟪y, z⟫|
      ≤ |⟪x, y⟫| * |cross y z| + |cross x y| * |⟪y, z⟫| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ 1 * |cross y z| + |cross x y| * 1 := by gcongr
    _ = _ := by ring

/-- Adjoint relation for the transpose. -/
lemma inner_act_transpose (A : M2R) (x y : E2) : ⟪act Aᵀ x, y⟫ = ⟪x, act A y⟫ := by
  rw [inner_E2, inner_E2]; simp; ring

lemma norm_transpose_R (A : M2R) : ‖Aᵀ‖ = ‖A‖ := by
  rw [← conjTranspose_eq_transpose_of_trivial, l2_opNorm_conjTranspose]

end Plane

/-! ### `SO(2,ℝ)`: (1.13.3) -/

section SO2

open Real

/-- The rotation matrix `R_θ`. -/
def rot (θ : ℝ) : M2R := !![cos θ, -sin θ; sin θ, cos θ]

lemma det_rot (θ : ℝ) : (rot θ).det = 1 := by
  simp [rot, det_fin_two]; nlinarith [sin_sq_add_cos_sq θ]

lemma trace_rot (θ : ℝ) : (rot θ).trace = 2 * cos θ := by
  simp [rot, trace_fin_two]; ring

lemma entries_of_transpose_mul_self {A : M2R} (h : A.det = 1) (hA : Aᵀ * A = 1) :
    A 1 1 = A 0 0 ∧ A 0 1 = - A 1 0 ∧ A 0 0 ^ 2 + A 1 0 ^ 2 = 1 := by
  have e00 := congrFun (congrFun hA 0) 0
  have e01 := congrFun (congrFun hA 0) 1
  have e11 := congrFun (congrFun hA 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e11
  rw [det_fin_two] at h
  have hsq : (A 1 1 - A 0 0) ^ 2 + (A 0 1 + A 1 0) ^ 2 = 0 := by nlinarith
  have h1 : A 1 1 - A 0 0 = 0 := by nlinarith [sq_nonneg (A 1 1 - A 0 0), sq_nonneg (A 0 1 + A 1 0)]
  have h2 : A 0 1 + A 1 0 = 0 := by nlinarith [sq_nonneg (A 1 1 - A 0 0), sq_nonneg (A 0 1 + A 1 0)]
  refine ⟨by linarith, by linarith, by nlinarith⟩

/-- (1.13.3): for `A ∈ SL(2,ℝ)`, `AᵀA = I` iff `A` is a rotation `R_θ`. -/
theorem transpose_mul_self_eq_one_iff_rot {A : M2R} (h : A.det = 1) :
    Aᵀ * A = 1 ↔ ∃ θ, A = rot θ := by
  constructor
  · intro hA
    obtain ⟨h1, h2, h3⟩ := entries_of_transpose_mul_self h hA
    set z : ℂ := ⟨A 0 0, A 1 0⟩
    have hz : ‖z‖ = 1 := by
      rw [Complex.norm_eq_sqrt_sq_add_sq]; simp [z, h3]
    have hz0 : z ≠ 0 := by intro h0; rw [h0, norm_zero] at hz; norm_num at hz
    refine ⟨Complex.arg z, ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [rot, Complex.cos_arg hz0, Complex.sin_arg, hz, z, h1, h2]
  · rintro ⟨θ, rfl⟩
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [rot, Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith [sin_sq_add_cos_sq θ]

/-- (1.13.3): `AᵀA = I` iff `A` is an isometry of `ℝ²`. -/
theorem isometry_iff_transpose_mul_self (A : M2R) :
    (∀ v : E2, ‖act A v‖ = ‖v‖) ↔ Aᵀ * A = 1 := by
  constructor
  · intro hv
    have key : ∀ v : E2, ⟪act A v, act A v⟫ = ⟪v, v⟫ := fun v => by
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hv]
    have k0 := key (WithLp.toLp 2 ![1, 0])
    have k1 := key (WithLp.toLp 2 ![0, 1])
    have k2 := key (WithLp.toLp 2 ![1, 1])
    rw [inner_E2, inner_E2] at k0 k1 k2
    simp only [act_apply, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] at k0 k1 k2
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> nlinarith
  · intro hA v
    have h : ‖act A v‖ ^ 2 = ‖v‖ ^ 2 := by
      have e00 := congrFun (congrFun hA 0) 0
      have e01 := congrFun (congrFun hA 0) 1
      have e11 := congrFun (congrFun hA 1) 1
      simp [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e11
      rw [norm_sq_E2, norm_sq_E2]; simp
      linear_combination (v 0 ^ 2) * e00 + (2 * v 0 * v 1) * e01 + (v 1 ^ 2) * e11
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

end SO2

/-! ### Elliptic, hyperbolic, parabolic: Definition 1.13.2 and Theorem 1.13.3 -/

section Classification

/-- **Definition 1.13.2**: `A ∈ SL(2,ℝ)` is elliptic if `Tr A ∈ (-2, 2)`. -/
def IsEllipticTr (A : M2R) : Prop := |A.trace| < 2

/-- **Definition 1.13.2**: hyperbolic if `Tr A ∈ ℝ \ [-2, 2]`. -/
def IsHyperbolicTr (A : M2R) : Prop := 2 < |A.trace|

/-- **Definition 1.13.2**: parabolic if `Tr A = ±2` but `A ≠ ±I`. -/
def IsParabolicTr (A : M2R) : Prop := |A.trace| = 2 ∧ A ≠ 1 ∧ A ≠ -1

lemma ne_zero_of_elliptic {A : M2R} (h : A.det = 1) (hA : IsEllipticTr A) : A 1 0 ≠ 0 := by
  intro hc
  rw [det_fin_two, hc] at h
  have ht : |A 0 0 + A 1 1| < 2 := by simpa [IsEllipticTr, trace_fin_two] using hA
  have := abs_lt.mp ht
  nlinarith [sq_nonneg (A 0 0 - A 1 1)]

lemma eigvec_of_root {A : M2R} (h : A.det = 1) (hc : A 1 0 ≠ 0) {l : ℂ}
    (hl : l ^ 2 - (A.trace : ℂ) * l + 1 = 0) :
    (A.map (↑) : M2C) *ᵥ ![(l - A 1 1) / A 1 0, 1] = l • ![(l - A 1 1) / A 1 0, 1] := by
  have hc' : (A 1 0 : ℂ) ≠ 0 := by exact_mod_cast hc
  rw [det_fin_two] at h
  have h' : (A 0 0 : ℂ) * A 1 1 - A 0 1 * A 1 0 = 1 := by exact_mod_cast h
  rw [trace_fin_two] at hl
  push_cast at hl
  ext i; fin_cases i
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Pi.smul_apply, smul_eq_mul,
      Fin.zero_eta, Fin.isValue, mul_one]
    have key : (A 1 0 : ℂ) * ((A 0 0 : ℂ) * ((l - A 1 1) / A 1 0) + A 0 1 -
        l * ((l - A 1 1) / A 1 0)) = -(l ^ 2 - (A 0 0 + A 1 1) * l + 1) + (1 - ((A 0 0 : ℂ) *
          A 1 1 - A 0 1 * A 1 0)) := by
      field_simp; ring
    rw [hl, h'] at key
    have : (A 0 0 : ℂ) * ((l - A 1 1) / A 1 0) + A 0 1 - l * ((l - A 1 1) / A 1 0) = 0 := by
      have := mul_eq_zero.mp (key.trans (by ring))
      exact this.resolve_left hc'
    linear_combination this
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Pi.smul_apply, smul_eq_mul,
      Fin.mk_one, Fin.isValue, mul_one]
    field_simp; ring

/-- **Theorem 1.13.3 (a)**: an elliptic `A` has eigenvalues `e^{±iθ}`, `θ ∈ (0, π)`,
`2 cos θ = Tr A`, with eigenvectors `(z, 1)ᵀ` and `(z̄, 1)ᵀ`, where `z ∉ ℝ`. -/
theorem elliptic_eigen {A : M2R} (h : A.det = 1) (hA : IsEllipticTr A) :
    ∃ θ : ℝ, 0 < θ ∧ θ < Real.pi ∧ 2 * Real.cos θ = A.trace ∧ ∃ z : ℂ, z.im ≠ 0 ∧
      (A.map (↑) : M2C) *ᵥ ![z, 1] = Complex.exp (θ * Complex.I) • ![z, 1] ∧
      (A.map (↑) : M2C) *ᵥ ![conj z, 1] = Complex.exp (-(θ * Complex.I)) • ![conj z, 1] := by
  have hc := ne_zero_of_elliptic h hA
  have ht := abs_lt.mp (show |A.trace| < 2 from hA)
  set θ := Real.arccos (A.trace / 2)
  have hcos : Real.cos θ = A.trace / 2 := Real.cos_arccos (by linarith) (by linarith)
  have hθ0 : 0 < θ := Real.arccos_pos.mpr (by linarith)
  have hθπ : θ < Real.pi := Real.arccos_lt_pi.mpr (by linarith)
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ
  have htr : (A.trace : ℂ) = 2 * Complex.cos θ := by
    rw [← Complex.ofReal_cos, hcos]; push_cast; ring
  have hroot : ∀ l : ℂ, l = Complex.cos θ + Complex.sin θ * Complex.I ∨
      l = Complex.cos θ - Complex.sin θ * Complex.I → l ^ 2 - (A.trace : ℂ) * l + 1 = 0 := by
    intro l hl
    have hcs := Complex.cos_sq_add_sin_sq (θ : ℂ)
    rw [htr]
    rcases hl with rfl | rfl
    · linear_combination (Complex.sin θ) ^ 2 * Complex.I_sq - hcs
    · linear_combination (Complex.sin θ) ^ 2 * Complex.I_sq - hcs
  have hl1 : Complex.exp (θ * Complex.I) = Complex.cos θ + Complex.sin θ * Complex.I :=
    Complex.exp_mul_I _
  have hl2 : Complex.exp (-(θ * Complex.I)) = Complex.cos θ - Complex.sin θ * Complex.I := by
    rw [← neg_mul, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]; ring
  refine ⟨θ, hθ0, hθπ, by rw [hcos]; ring, (Complex.exp (θ * Complex.I) - A 1 1) / A 1 0,
    ?_, eigvec_of_root h hc (hroot _ (Or.inl hl1)), ?_⟩
  · rw [hl1, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    rw [Complex.div_ofReal_im]
    simp
    exact ⟨hsin.ne', hc⟩
  · have hz : conj ((Complex.exp (θ * Complex.I) - A 1 1) / A 1 0) =
        (Complex.exp (-(θ * Complex.I)) - A 1 1) / A 1 0 := by
      rw [hl1, hl2, map_div₀, map_sub, map_add, map_mul, Complex.conj_I, Complex.conj_ofReal,
        Complex.conj_ofReal, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Complex.conj_ofReal,
        Complex.conj_ofReal]
      ring
    rw [hz]
    exact eigvec_of_root h hc (hroot _ (Or.inr hl2))

lemma exists_eigvec {A : M2R} (h : A.det = 1) {l : ℝ} (hl : l ^ 2 - A.trace * l + 1 = 0) :
    ∃ v : Fin 2 → ℝ, v ≠ 0 ∧ A *ᵥ v = l • v := by
  have hdet : (A - l • (1 : M2R)).det = 0 := by
    rw [det_fin_two] at h ⊢
    rw [trace_fin_two] at hl
    simp
    linear_combination hl + h
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨v, hv, ?_⟩
  rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] at hv0
  exact hv0

/-- **Theorem 1.13.3 (b)**: a hyperbolic `A` has distinct real eigenvalues `λ` and `1/λ`. -/
theorem hyperbolic_eigen {A : M2R} (h : A.det = 1) (hA : IsHyperbolicTr A) :
    ∃ l : ℝ, l ≠ l⁻¹ ∧ l + l⁻¹ = A.trace ∧ (∃ v : Fin 2 → ℝ, v ≠ 0 ∧ A *ᵥ v = l • v) ∧
      (∃ w : Fin 2 → ℝ, w ≠ 0 ∧ A *ᵥ w = l⁻¹ • w) := by
  set t := A.trace
  have ht : 4 < t ^ 2 := by
    have := sq_lt_sq.mpr (show |(2:ℝ)| < |t| by rwa [abs_two])
    linarith
  set r := Real.sqrt (t ^ 2 - 4)
  have hr : 0 < r := Real.sqrt_pos.mpr (by linarith)
  have hr2 : r ^ 2 = t ^ 2 - 4 := Real.sq_sqrt (by linarith)
  have hprod : ((t + r) / 2) * ((t - r) / 2) = 1 := by linear_combination (-1/4) * hr2
  have hinv : ((t + r) / 2)⁻¹ = (t - r) / 2 := (eq_inv_of_mul_eq_one_right hprod).symm
  refine ⟨(t + r) / 2, ?_, ?_, exists_eigvec h ?_, ?_⟩
  · rw [hinv]; intro h'; linarith
  · rw [hinv]; ring
  · linear_combination (1/4) * hr2
  · rw [hinv]; exact exists_eigvec h (by linear_combination (1/4) * hr2)

/-- **Theorem 1.13.3 (c)**: a parabolic `A` is similar to `[[±1, 1], [0, ±1]]`. -/
theorem parabolic_similar {A : M2R} (h : A.det = 1) (hA : IsParabolicTr A) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∃ P : M2R, P.det ≠ 0 ∧ A * P = P * !![s, 1; 0, s] := by
  obtain ⟨htr, hne1, hne2⟩ := hA
  set s := A.trace / 2 with hs_def
  have hs : s = 1 ∨ s = -1 := by
    rcases abs_eq (show (0:ℝ) ≤ 2 by norm_num) |>.mp htr with h2 | h2 <;>
      [left; right] <;> rw [hs_def, h2] <;> norm_num
  have hs2 : s ^ 2 = 1 := by rcases hs with h' | h' <;> rw [h'] <;> norm_num
  have hd : A 0 0 + A 1 1 = 2 * s := by rw [hs_def, trace_fin_two]; ring
  rw [det_fin_two] at h
  refine ⟨s, hs, ?_⟩
  by_cases hc : A 1 0 = 0
  · have had : A 0 0 = s ∧ A 1 1 = s := by
      rw [hc] at h
      have : (A 0 0 - A 1 1) ^ 2 = 0 := by
        linear_combination (A 0 0 + A 1 1 + 2 * s) * hd + 4 * hs2 - 4 * h
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      constructor <;> linarith
    have hb : A 0 1 ≠ 0 := by
      intro hb
      have hA : A = s • (1 : M2R) := by
        ext i j; fin_cases i <;> fin_cases j <;> simp [had.1, had.2, hb, hc]
      rcases hs with h' | h'
      · exact hne1 (by rw [hA, h', one_smul])
      · exact hne2 (by rw [hA, h', neg_one_smul])
    refine ⟨!![A 0 1, 0; 0, 1], by simpa [det_fin_two] using hb, ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, had.1, had.2, hc] <;> ring
  · refine ⟨!![A 0 0 - s, 1; A 1 0, 0], by simpa [det_fin_two] using hc, ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · linear_combination (-1) * h + (A 0 0) * hd + hs2
    · linear_combination (A 1 0) * hd

end Classification

/-! ### The angle between lines (1.13.11) -/

section Angle

/-- (1.13.11): the angle `∠(v, w) ∈ [0, π/2]` between the lines spanned by `v` and `w`,
`cos ∠(v, w) = |⟨v, w⟩| / (‖v‖ ‖w‖)`. -/
def pangle (v w : E2) : ℝ := Real.arccos (|⟪v, w⟫| / (‖v‖ * ‖w‖))

lemma pangle_nonneg (v w : E2) : 0 ≤ pangle v w := Real.arccos_nonneg _

lemma pangle_le_pi_div_two (v w : E2) : pangle v w ≤ Real.pi / 2 :=
  Real.arccos_le_pi_div_two.mpr (by positivity)

/-- `sin ∠(v, w) = |det[v w]| / (‖v‖ ‖w‖)`. -/
lemma sin_pangle {v w : E2} (hv : v ≠ 0) (hw : w ≠ 0) :
    Real.sin (pangle v w) = |cross v w| / (‖v‖ * ‖w‖) := by
  have hv' : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hw' : 0 < ‖w‖ := norm_pos_iff.mpr hw
  rw [pangle, Real.sin_arccos]
  have h : 1 - (|⟪v, w⟫| / (‖v‖ * ‖w‖)) ^ 2 = (|cross v w| / (‖v‖ * ‖w‖)) ^ 2 := by
    rw [div_pow, div_pow, sq_abs, sq_abs]
    field_simp
    linear_combination lagrange v w
  rw [h, Real.sqrt_sq (by positivity)]

end Angle

/-! ### Singular value decomposition in `SL(2,ℝ)`: Proposition 1.13.5 -/

section SVD

/-- Singular value data of `A ∈ SL(2,ℝ)`: a unit vector `u` (spanning `U(A)`) such that
`‖A u‖ = ‖A‖`, `A u ⊥ A s` and `‖A s‖ = ‖A‖⁻¹`, where `s = perp u` spans `S(A)`. -/
structure SVData (A : M2R) where
  /-- unit vector in the most expanded direction `U(A)` -/
  u : E2
  det_eq : A.det = 1
  norm_u : ‖u‖ = 1
  norm_Au : ‖act A u‖ = ‖A‖
  inner_AuAs : ⟪act A u, act A (perp u)⟫ = 0
  norm_As : ‖act A (perp u)‖ = ‖A‖⁻¹

/-- The operator norm of a real `2 × 2` matrix is attained on the unit circle. -/
lemma exists_max (A : M2R) : ∃ u : E2, ‖u‖ = 1 ∧ ‖act A u‖ = ‖A‖ := by
  have hK : IsCompact (Metric.sphere (0 : E2) 1) := isCompact_sphere 0 1
  have hne : (Metric.sphere (0 : E2) 1).Nonempty := ⟨EuclideanSpace.single 0 1, by simp⟩
  obtain ⟨u, hu, hmax⟩ := hK.exists_isMaxOn hne (f := fun v => ‖act A v‖)
    (act A).continuous.norm.continuousOn
  have hu1 : ‖u‖ = 1 := by simpa using hu
  refine ⟨u, hu1, le_antisymm (by simpa [hu1] using norm_act_le A u) ?_⟩
  rw [← norm_act_eq]
  refine (act A).opNorm_le_bound (norm_nonneg _) fun v => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hw : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : E2) 1 := by
      simp [norm_smul, hvn.ne']
    have h1 : ‖act A (‖v‖⁻¹ • v)‖ ≤ ‖act A u‖ := hmax hw
    rw [map_smul, norm_smul, norm_inv, norm_norm, inv_mul_le_iff₀ hvn] at h1
    linarith

lemma eq_zero_of_forall_le {p K : ℝ} (h : ∀ t : ℝ, 2 * t * p ≤ t ^ 2 * K) : p = 0 := by
  set c := |K| + 1 with hc_def
  have hc : 0 < c := by positivity
  have h1 := h (p / c)
  have h2 : (p / c) ^ 2 * K ≤ (p / c) ^ 2 * |K| :=
    mul_le_mul_of_nonneg_left (le_abs_self K) (sq_nonneg _)
  have h3 : 2 * (p / c) * p = (2 * c) * (p / c) ^ 2 := by field_simp
  have h4 : |K| = c - 1 := by rw [hc_def]; ring
  have h5 : 2 * c * (p / c) ^ 2 ≤ (p / c) ^ 2 * (c - 1) := by rw [← h3, ← h4]; linarith
  have h6 : (p / c) ^ 2 = 0 := by
    by_contra hne
    have hX : 0 < (p / c) ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
    have : 0 < (p / c) ^ 2 * (c + 1) := mul_pos hX (by linarith)
    linarith
  have : p / c = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h6
  rcases div_eq_zero_iff.mp this with h7 | h7
  · exact h7
  · exact absurd h7 hc.ne'

/-- **Proposition 1.13.5** (existence of the singular value decomposition) for `A ∈ SL(2,ℝ)`. -/
theorem exists_svd {A : M2R} (hA : A.det = 1) : Nonempty (SVData A) := by
  obtain ⟨u, hu, hAu⟩ := exists_max A
  set s := perp u
  have hs : ‖s‖ = 1 := by rw [norm_perp, hu]
  have horth : ⟪act A u, act A s⟫ = 0 := by
    apply eq_zero_of_forall_le (K := ‖A‖ ^ 2 - ‖act A s‖ ^ 2)
    intro t
    have h1 : ‖act A (u + t • s)‖ ≤ ‖A‖ * ‖u + t • s‖ := norm_act_le _ _
    have h2 : ‖u + t • s‖ ^ 2 = 1 + t ^ 2 := by
      rw [norm_add_sq_real, norm_smul, inner_smul_right, inner_perp, hu, hs]
      simp [Real.norm_eq_abs, sq_abs]
    have h3 : ‖act A (u + t • s)‖ ^ 2 =
        ‖A‖ ^ 2 + 2 * t * ⟪act A u, act A s⟫ + t ^ 2 * ‖act A s‖ ^ 2 := by
      rw [map_add, map_smul, norm_add_sq_real, norm_smul, inner_smul_right, hAu]
      simp [mul_pow, Real.norm_eq_abs, sq_abs]; ring
    have h4 : ‖act A (u + t • s)‖ ^ 2 ≤ ‖A‖ ^ 2 * (1 + t ^ 2) := by
      rw [← h2, ← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith
  have hcross : cross (act A u) (act A s) = 1 := by
    rw [cross_act, hA, cross_perp, hu]; norm_num
  have hlag := lagrange (act A u) (act A s)
  rw [horth, hcross, hAu] at hlag
  have hnn : 0 ≤ ‖A‖ * ‖act A s‖ := by positivity
  have h' : ‖A‖ * ‖act A s‖ = 1 :=
    (sq_eq_sq₀ hnn zero_le_one).mp (by rw [mul_pow, hlag]; norm_num)
  exact ⟨⟨u, hA, hu, hAu, horth, eq_inv_of_mul_eq_one_right h'⟩⟩

/-- Matrices in `SL(2,ℝ)` have norm at least one. -/
lemma one_le_norm_of_det {A : M2R} (hA : A.det = 1) : 1 ≤ ‖A‖ := by
  obtain ⟨D⟩ := exists_svd hA
  have h1 : ‖A‖⁻¹ ≤ ‖A‖ := by
    rw [← D.norm_As]; simpa [norm_perp, D.norm_u] using norm_act_le A (perp D.u)
  have hpos : 0 < ‖A‖ := by
    rcases (norm_nonneg A).lt_or_eq with h | h
    · exact h
    · have := D.norm_Au; rw [← h] at this
      have h0 : act A D.u = 0 := norm_eq_zero.mp this
      have := cross_act A D.u (perp D.u)
      rw [h0, hA, cross_perp, D.norm_u] at this
      simp [cross] at this
  by_contra hlt
  replace hlt := lt_of_not_ge hlt
  have : ‖A‖⁻¹ > 1 := one_lt_inv_iff₀.mpr ⟨hpos, hlt⟩
  linarith

namespace SVData

variable {A : M2R} (D : SVData A)

omit D in
lemma norm_pos (D : SVData A) : 0 < ‖A‖ := zero_lt_one.trans_le (one_le_norm_of_det D.det_eq)

lemma norm_s : ‖perp D.u‖ = 1 := by rw [norm_perp, D.norm_u]

lemma act_decomp (w : E2) :
    act A w = ⟪w, D.u⟫ • act A D.u + ⟪w, perp D.u⟫ • act A (perp D.u) := by
  conv_lhs => rw [decomp D.u D.norm_u w]
  simp [map_add, map_smul]

lemma norm_sq_act (w : E2) :
    ‖act A w‖ ^ 2 = ⟪w, D.u⟫ ^ 2 * ‖A‖ ^ 2 + ⟪w, perp D.u⟫ ^ 2 * ‖A‖⁻¹ ^ 2 := by
  rw [D.act_decomp w, norm_add_sq_real, norm_smul, norm_smul, inner_smul_left,
    inner_smul_right, D.inner_AuAs, D.norm_Au, D.norm_As]
  simp [mul_pow, Real.norm_eq_abs, sq_abs]

/-- `‖A w‖ ≥ |⟨w, u⟩| ‖A‖`. -/
lemma le_norm_act (w : E2) : |⟪w, D.u⟫| * ‖A‖ ≤ ‖act A w‖ := by
  refine (sq_le_sq₀ (by positivity) (norm_nonneg _)).mp ?_
  rw [D.norm_sq_act, mul_pow, sq_abs]
  nlinarith [sq_nonneg (⟪w, perp D.u⟫ * ‖A‖⁻¹)]

/-- `‖A w‖ ≤ |⟨w, u⟩| ‖A‖ + |⟨w, s⟩| ‖A‖⁻¹`. -/
lemma norm_act_le' (w : E2) :
    ‖act A w‖ ≤ |⟪w, D.u⟫| * ‖A‖ + |⟪w, perp D.u⟫| * ‖A‖⁻¹ := by
  rw [D.act_decomp w]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, D.norm_Au, D.norm_As, Real.norm_eq_abs, Real.norm_eq_abs]

/-- `|det[A x, A u]| = |det[x, u]|`. -/
lemma cross_act_u (x : E2) : cross (act A x) (act A D.u) = cross x D.u := by
  rw [cross_act, D.det_eq, one_mul]

/-- Uniqueness of `U(A)` in Proposition 1.13.5: if `‖A‖ > 1` and `‖A w‖ = ‖A‖ ‖w‖`, then
`w ⊥ s`, i.e. `w ∈ U(A)`. -/
theorem inner_s_eq_zero_of_max (h1 : 1 < ‖A‖) {w : E2} (hw : ‖act A w‖ = ‖A‖ * ‖w‖) :
    ⟪w, perp D.u⟫ = 0 := by
  have hsq := D.norm_sq_act w
  have hn := norm_sq_decomp D.u D.norm_u w
  rw [hw, mul_pow, hn] at hsq
  have hm : ‖A‖⁻¹ ^ 2 < ‖A‖ ^ 2 := by
    have : ‖A‖⁻¹ < ‖A‖ := (inv_lt_one_of_one_lt₀ h1).trans h1
    exact pow_lt_pow_left₀ this (by positivity) (by norm_num)
  have : ⟪w, perp D.u⟫ ^ 2 * (‖A‖ ^ 2 - ‖A‖⁻¹ ^ 2) = 0 := by linear_combination hsq
  rcases mul_eq_zero.mp this with h | h
  · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
  · linarith

/-- Uniqueness of `S(A)` in Proposition 1.13.5: if `‖A‖ > 1` and `‖A w‖ = ‖A‖⁻¹ ‖w‖`, then
`w ⊥ u`, i.e. `w ∈ S(A)`. -/
theorem inner_u_eq_zero_of_min (h1 : 1 < ‖A‖) {w : E2} (hw : ‖act A w‖ = ‖A‖⁻¹ * ‖w‖) :
    ⟪w, D.u⟫ = 0 := by
  have hsq := D.norm_sq_act w
  have hn := norm_sq_decomp D.u D.norm_u w
  rw [hw, mul_pow, hn] at hsq
  have hm : ‖A‖⁻¹ ^ 2 < ‖A‖ ^ 2 := by
    have : ‖A‖⁻¹ < ‖A‖ := (inv_lt_one_of_one_lt₀ h1).trans h1
    exact pow_lt_pow_left₀ this (by positivity) (by norm_num)
  have : ⟪w, D.u⟫ ^ 2 * (‖A‖ ^ 2 - ‖A‖⁻¹ ^ 2) = 0 := by linear_combination -hsq
  rcases mul_eq_zero.mp this with h | h
  · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
  · linarith

lemma transpose_act_u : act Aᵀ (act A D.u) = ‖A‖ ^ 2 • D.u := by
  set x := act Aᵀ (act A D.u)
  have h1 : ⟪x, D.u⟫ = ‖A‖ ^ 2 := by
    rw [inner_act_transpose, real_inner_self_eq_norm_sq, D.norm_Au]
  have h2 : ⟪x, perp D.u⟫ = 0 := by rw [inner_act_transpose, D.inner_AuAs]
  rw [decomp D.u D.norm_u x, h1, h2, zero_smul, add_zero]

lemma transpose_act_s : act Aᵀ (act A (perp D.u)) = ‖A‖⁻¹ ^ 2 • perp D.u := by
  set x := act Aᵀ (act A (perp D.u))
  have h1 : ⟪x, D.u⟫ = 0 := by rw [inner_act_transpose, real_inner_comm, D.inner_AuAs]
  have h2 : ⟪x, perp D.u⟫ = ‖A‖⁻¹ ^ 2 := by
    rw [inner_act_transpose, real_inner_self_eq_norm_sq, D.norm_As]
  rw [decomp D.u D.norm_u x, h1, h2, zero_smul, zero_add]

/-- **Proposition 1.13.5 (d)**: `A` maps `U(A)` onto the most expanded direction `U(A*)` of
`A* = Aᵀ`. -/
theorem transpose_top : ‖act Aᵀ (act A D.u)‖ = ‖Aᵀ‖ * ‖act A D.u‖ := by
  rw [D.transpose_act_u, norm_smul, D.norm_u, norm_transpose_R, D.norm_Au]
  simp [Real.norm_eq_abs, sq]

/-- **Proposition 1.13.5 (d)**: `A` maps `S(A)` onto the most contracted direction `S(A*)`. -/
theorem transpose_bottom :
    ‖act Aᵀ (act A (perp D.u))‖ = ‖Aᵀ‖⁻¹ * ‖act A (perp D.u)‖ := by
  rw [D.transpose_act_s, norm_smul, D.norm_s, norm_transpose_R, D.norm_As]
  simp [Real.norm_eq_abs, sq]

/-- **Proposition 1.13.5 (e)**, the identity (1.13.16): if `‖A w‖ = R ‖w‖` and
`θ = ∠(w, S(A))`, then `sin² θ = (R² - ‖A‖⁻²) / (‖A‖² - ‖A‖⁻²)`. -/
theorem sin_sq_pangle (h1 : 1 < ‖A‖) {w : E2} (hw0 : w ≠ 0) {R : ℝ}
    (hR : ‖act A w‖ = R * ‖w‖) :
    Real.sin (pangle w (perp D.u)) ^ 2 =
      (R ^ 2 - ‖A‖⁻¹ ^ 2) / (‖A‖ ^ 2 - ‖A‖⁻¹ ^ 2) := by
  have hs0 : perp D.u ≠ 0 := by
    intro h; have := D.norm_s; rw [h, norm_zero] at this; norm_num at this
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  rw [sin_pangle hw0 hs0, D.norm_s, mul_one, cross_perp_right, div_pow, sq_abs]
  have hm : ‖A‖⁻¹ ^ 2 < ‖A‖ ^ 2 := by
    have : ‖A‖⁻¹ < ‖A‖ := (inv_lt_one_of_one_lt₀ h1).trans h1
    exact pow_lt_pow_left₀ this (by positivity) (by norm_num)
  rw [div_eq_div_iff (by positivity) (by linarith)]
  have hsq := D.norm_sq_act w
  have hn := norm_sq_decomp D.u D.norm_u w
  rw [hR, mul_pow] at hsq
  rw [hn] at hsq ⊢
  linear_combination -hsq

lemma sin_pangle_eq (h1 : 1 < ‖A‖) {w : E2} (hw0 : w ≠ 0) {R : ℝ}
    (hR : ‖act A w‖ = R * ‖w‖) :
    Real.sin (pangle w (perp D.u)) =
      Real.sqrt ((R ^ 2 - ‖A‖⁻¹ ^ 2) / (‖A‖ ^ 2 - ‖A‖⁻¹ ^ 2)) := by
  rw [← D.sin_sq_pangle h1 hw0 hR, Real.sqrt_sq]
  exact Real.sin_nonneg_of_nonneg_of_le_pi (pangle_nonneg _ _)
    ((pangle_le_pi_div_two _ _).trans (by linarith [Real.pi_pos]))

/-- **Proposition 1.13.5 (e)**, the bounds (1.13.14). -/
theorem pangle_bounds (h1 : 1 < ‖A‖) {w : E2} (hw0 : w ≠ 0) {R : ℝ}
    (hR : ‖act A w‖ = R * ‖w‖) :
    Real.sqrt ((R ^ 2 - ‖A‖⁻¹ ^ 2) / (‖A‖ ^ 2 - ‖A‖⁻¹ ^ 2)) ≤ pangle w (perp D.u) ∧
      pangle w (perp D.u) ≤
        Real.pi / 2 * Real.sqrt ((R ^ 2 - ‖A‖⁻¹ ^ 2) / (‖A‖ ^ 2 - ‖A‖⁻¹ ^ 2)) := by
  rw [← D.sin_pangle_eq h1 hw0 hR]
  have h0 := pangle_nonneg w (perp D.u)
  have hpi := pangle_le_pi_div_two w (perp D.u)
  refine ⟨Real.sin_le h0, ?_⟩
  have := Real.mul_le_sin h0 hpi
  have hp := Real.pi_pos
  rw [div_mul_eq_mul_div, div_le_iff₀ hp] at this
  nlinarith

/-- **Proposition 1.13.5 (e)**, the bound (1.13.15): `θ ≤ π R / (2 ‖A‖)`. -/
theorem pangle_le (h1 : 1 < ‖A‖) {w : E2} (hw0 : w ≠ 0) {R : ℝ}
    (hR : ‖act A w‖ = R * ‖w‖) :
    pangle w (perp D.u) ≤ Real.pi / 2 * (R / ‖A‖) := by
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hApos : 0 < ‖A‖ := zero_lt_one.trans h1
  have hR0 : 0 ≤ R := by
    have := norm_nonneg (act A w); rw [hR] at this
    exact nonneg_of_mul_nonneg_left this hwpos
  have hRA : R ≤ ‖A‖ := by
    have := norm_act_le A w; rw [hR] at this
    exact le_of_mul_le_mul_right this hwpos
  refine (D.pangle_bounds h1 hw0 hR).2.trans ?_
  gcongr
  have hm : ‖A‖⁻¹ ^ 2 < ‖A‖ ^ 2 := by
    have : ‖A‖⁻¹ < ‖A‖ := (inv_lt_one_of_one_lt₀ h1).trans h1
    exact pow_lt_pow_left₀ this (by positivity) (by norm_num)
  rw [show R / ‖A‖ = Real.sqrt ((R / ‖A‖) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
  apply Real.sqrt_le_sqrt
  rw [div_pow, div_le_div_iff₀ (by linarith) (by positivity)]
  have : R ^ 2 ≤ ‖A‖ ^ 2 := pow_le_pow_left₀ hR0 hRA 2
  have hinv : ‖A‖⁻¹ ^ 2 * ‖A‖ ^ 2 = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hApos.ne', one_pow]
  nlinarith

end SVData

/-- (1.13.3): for `A ∈ SL(2,ℝ)`, `‖A‖ = 1` iff `AᵀA = I`. -/
theorem norm_eq_one_iff_transpose_mul_self {A : M2R} (hA : A.det = 1) :
    ‖A‖ = 1 ↔ Aᵀ * A = 1 := by
  rw [← isometry_iff_transpose_mul_self]
  obtain ⟨D⟩ := exists_svd hA
  constructor
  · intro h1 v
    have hsq := D.norm_sq_act v
    rw [h1, inv_one, one_pow, mul_one, mul_one, ← norm_sq_decomp D.u D.norm_u v] at hsq
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  · intro h
    have := D.norm_Au
    rw [h, D.norm_u] at this
    exact this.symm

end SVD

/-! ### Möbius transformations: Propositions 1.13.6 and 1.13.7 -/

section Mobius

open UpperHalfPlane

lemma coe_mapGL (g : SL(2, ℝ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : M2R) = (g : M2R) := by
  ext i j; simp

lemma smul_eq_mapGL (g : SL(2, ℝ)) (z : ℍ) :
    g • z = (Matrix.SpecialLinearGroup.mapGL ℝ g) • z := rfl

/-- **Proposition 1.13.6**: `SO(2,ℝ)` is the stabilizer of `i`: `A · i = i` iff `AᵀA = I`. -/
theorem smul_I_eq_I_iff (g : SL(2, ℝ)) : g • I = I ↔ (g : M2R)ᵀ * (g : M2R) = 1 := by
  rw [smul_eq_mapGL, gl_smul_I_eq_I_iff_of_pos (by simp), coe_mapGL]
  have hd := g.det_coe
  constructor
  · rintro ⟨h1, h2⟩
    rw [det_fin_two, ← h1, h2] at hd
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, ← h1, h2] <;>
      first | linear_combination hd | ring
  · intro h
    obtain ⟨h1, h2, -⟩ := entries_of_transpose_mul_self hd h
    exact ⟨h1.symm, h2⟩

lemma isElliptic_mapGL_iff (g : SL(2, ℝ)) :
    Matrix.IsElliptic ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : M2R) ↔
      IsEllipticTr (g : M2R) := by
  rw [Matrix.IsElliptic, coe_mapGL, discr_fin_two, g.det_coe, IsEllipticTr]
  constructor
  · intro h; exact abs_lt.mpr ⟨by nlinarith, by nlinarith⟩
  · intro h; have := abs_lt.mp h; nlinarith

/-- **Proposition 1.13.7**, first claim: `|Tr A| < 2` iff the action of `A` on `ℂ₊` has a
unique fixed point. -/
theorem elliptic_iff_existsUnique_fixed (g : SL(2, ℝ)) :
    IsEllipticTr (g : M2R) ↔ ∃! z : ℍ, g • z = z := by
  have hpos : 0 < ((Matrix.SpecialLinearGroup.mapGL ℝ g).det : ℝ) := by simp
  constructor
  · intro h
    have hell := (isElliptic_mapGL_iff g).mpr h
    refine ⟨fixedPt _ hell, (gl_smul_eq_self_iff_eq_fixedPt hpos hell).mpr rfl, ?_⟩
    intro z hz
    exact (gl_smul_eq_self_iff_eq_fixedPt hpos hell).mp hz
  · rintro ⟨z, hz, huniq⟩
    rw [← isElliptic_mapGL_iff]
    refine isElliptic_of_exists_smul_eq_self hpos ?_ ⟨z, hz⟩
    intro hc
    have hall := forall_smul_eq_self_iff_mem_center.mpr hc
    set w : ℍ := ⟨2 * Complex.I, by simp⟩
    have h1 : I = z := huniq I (hall I)
    have h2 : w = z := huniq w (hall w)
    have : (I : ℂ) = (w : ℂ) := by rw [h1, h2]
    simp [w, Complex.ext_iff] at this

lemma trace_conj (M g : SL(2, ℝ)) :
    ((M * g * M⁻¹ : SL(2, ℝ)) : M2R).trace = (g : M2R).trace := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, trace_mul_comm,
    ← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]

/-- **Proposition 1.13.7**, second claim (1.13.18)–(1.13.19): an elliptic `A ∈ SL(2,ℝ)` is
conjugate in `SL(2,ℝ)` to a rotation `R_θ` with `2 cos θ = Tr A`. -/
theorem exists_conj_rot (g : SL(2, ℝ)) (hg : IsEllipticTr (g : M2R)) :
    ∃ (M : SL(2, ℝ)) (θ : ℝ), ((M * g * M⁻¹ : SL(2, ℝ)) : M2R) = rot θ ∧
      2 * Real.cos θ = (g : M2R).trace := by
  obtain ⟨z, hz, -⟩ := (elliptic_iff_existsUnique_fixed g).mp hg
  set M : SL(2, ℝ) := z.toSL2R⁻¹
  have hMz : M • z = I := by
    rw [show M = z.toSL2R⁻¹ from rfl, inv_smul_eq_iff, toSL2R_smul_I]
  have hfix : (M * g * M⁻¹) • I = I := by
    rw [mul_smul, mul_smul, show M⁻¹ = z.toSL2R by simp [M], toSL2R_smul_I, hz, hMz]
  obtain ⟨θ, hθ⟩ := (transpose_mul_self_eq_one_iff_rot (M * g * M⁻¹).det_coe).mp
    ((smul_I_eq_I_iff _).mp hfix)
  refine ⟨M, θ, hθ, ?_⟩
  rw [← trace_rot, ← hθ, trace_conj]

/-- **Proposition 1.13.7**, uniqueness: a conjugacy of an elliptic `A` to a rotation is unique
modulo left multiplication by an element of `SO(2,ℝ)`. -/
theorem conj_rot_unique (g : SL(2, ℝ)) (hg : IsEllipticTr (g : M2R)) {M M₀ : SL(2, ℝ)}
    {θ θ₀ : ℝ} (hM : ((M * g * M⁻¹ : SL(2, ℝ)) : M2R) = rot θ)
    (hM₀ : ((M₀ * g * M₀⁻¹ : SL(2, ℝ)) : M2R) = rot θ₀) :
    ∃ φ, ((M₀ * M⁻¹ : SL(2, ℝ)) : M2R) = rot φ := by
  obtain ⟨z, -, huniq⟩ := (elliptic_iff_existsUnique_fixed g).mp hg
  have key : ∀ N : SL(2, ℝ), ∀ φ, ((N * g * N⁻¹ : SL(2, ℝ)) : M2R) = rot φ → N⁻¹ • I = z := by
    intro N φ hN
    have hfix : (N * g * N⁻¹) • I = I := by
      rw [smul_I_eq_I_iff, transpose_mul_self_eq_one_iff_rot (N * g * N⁻¹).det_coe]
      exact ⟨φ, hN⟩
    apply huniq
    rw [mul_smul, mul_smul] at hfix
    have := congrArg (fun w => N⁻¹ • w) hfix
    simpa using this
  have h1 := key M θ hM
  have h2 := key M₀ θ₀ hM₀
  have hfix : (M₀ * M⁻¹) • I = I := by
    rw [mul_smul, h1, ← h2, smul_inv_smul]
  exact (transpose_mul_self_eq_one_iff_rot (M₀ * M⁻¹).det_coe).mp ((smul_I_eq_I_iff _).mp hfix)

end Mobius

end DF
