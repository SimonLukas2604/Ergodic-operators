/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §2.2.1  Transfer matrices and the Wronskian  (book pp. 139–143)

## Main definitions and results
* `DF.transferInv` — the inverse one-step matrix `T_z(m)⁻¹`; `DF.transferInv_eq_inv`.
* `DF.transferZ V z n` — the transfer matrices `A_z(n)` for all `n ∈ ℤ` (2.2.10), extending
  `DF.transferProd`; `DF.transferZ_succ`, `DF.det_transferZ`.
* (2.2.9): `DF.isSolution_iff_transferZ` — `u` solves (2.2.2) iff
  `(u(n+1), u(n))ᵀ = A_z(n) (u(1), u(0))ᵀ` for all `n`.
* (2.2.12)/(2.2.13): `DF.transferZ₂`, `DF.transferZ₂_mulVec`.
* `DF.solFrom` — the solution with prescribed initial data, `DF.u₁`, `DF.u₂` (2.2.16);
  `DF.eq_zero_of_isSolution` (uniqueness of solutions).
* **Proposition 2.2.2**: `DF.wronskian`, `DF.wronskian_succ` (constancy),
  `DF.wronskian_eq_zero_iff` (vanishing iff linear dependence).
* **Proposition 2.2.4**: `DF.transferZ_eq_u₁_u₂`.
* **Proposition 2.2.6**: `DF.norm_transferProd_sub_le` (perturbative estimate), for the
  Euclidean operator norm on `2 × 2` matrices.

## Deviations
* In Proposition 2.2.6 the quantities `Γ` (2.2.22) and `max_{1≤j≤n} |V(j) - W(j)|` are replaced
  by arbitrary upper bounds `Γ`, `δ` (this is equivalent).
-/
import DamanikFillman.Basic

noncomputable section

open scoped Matrix.Norms.L2Operator
open Matrix

namespace DF

/-- Complex `2 × 2` matrices. -/
abbrev Mat2 := Matrix (Fin 2) (Fin 2) ℂ

/-- The inverse of the one-step transfer matrix: `T_z(m)⁻¹ = [[0, 1], [-1, z - V(m)]]`. -/
def transferInv (z : ℂ) (v : ℝ) : Mat2 := !![0, 1; -1, z - v]

lemma transfer_mul_transferInv (z : ℂ) (v : ℝ) : transfer z v * transferInv z v = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [transfer, transferInv, Matrix.mul_apply]

lemma transferInv_mul_transfer (z : ℂ) (v : ℝ) : transferInv z v * transfer z v = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [transfer, transferInv, Matrix.mul_apply]

lemma transferInv_eq_inv (z : ℂ) (v : ℝ) : transferInv z v = (transfer z v)⁻¹ :=
  (Matrix.inv_eq_right_inv (transfer_mul_transferInv z v)).symm

/-- `A_z(-k) = T_z(-k+1)⁻¹ ⋯ T_z(0)⁻¹`. -/
def transferNeg (V : ℤ → ℝ) (z : ℂ) : ℕ → Mat2
  | 0 => 1
  | k + 1 => transferInv z (V (-(k : ℤ))) * transferNeg V z k

/-- The transfer matrices `A_z(n)`, `n ∈ ℤ`, of (2.2.10). -/
def transferZ (V : ℤ → ℝ) (z : ℂ) : ℤ → Mat2
  | (n : ℕ) => transferProd V z n
  | Int.negSucc k => transferNeg V z (k + 1)

@[simp] lemma transferZ_zero (V : ℤ → ℝ) (z : ℂ) : transferZ V z 0 = 1 := rfl

lemma transferZ_natCast (V : ℤ → ℝ) (z : ℂ) (n : ℕ) :
    transferZ V z n = transferProd V z n := rfl

lemma transferZ_neg_natCast (V : ℤ → ℝ) (z : ℂ) (k : ℕ) :
    transferZ V z (-(k : ℤ)) = transferNeg V z k := by
  rcases k with _ | k
  · rfl
  · rfl

/-- `A_z(n+1) = T_z(n+1) A_z(n)` for all `n ∈ ℤ`. -/
theorem transferZ_succ (V : ℤ → ℝ) (z : ℂ) (n : ℤ) :
    transferZ V z (n + 1) = transfer z (V (n + 1)) * transferZ V z n := by
  rcases n with n | k
  · show transferProd V z (n + 1) = _
    simp [transferProd, transferZ]
  · rcases k with _ | k
    · show transferZ V z 0 = transfer z (V (-1 + 1)) * transferNeg V z 1
      simp [transferNeg, ← Matrix.mul_assoc, transfer_mul_transferInv]
    · have h1 : Int.negSucc (k + 1) + 1 = -((k + 1 : ℕ) : ℤ) := by push_cast; omega
      rw [h1, transferZ_neg_natCast]
      show transferNeg V z (k + 1) = transfer z (V (-((k + 1 : ℕ) : ℤ))) *
        (transferInv z (V (-((k + 1 : ℕ) : ℤ))) * transferNeg V z (k + 1))
      rw [← Matrix.mul_assoc, transfer_mul_transferInv, Matrix.one_mul]

lemma transferZ_pred (V : ℤ → ℝ) (z : ℂ) (n : ℤ) :
    transferZ V z n = transfer z (V n) * transferZ V z (n - 1) := by
  have := transferZ_succ V z (n - 1)
  simpa using this

/-- `det A_z(n) = 1` for all `n ∈ ℤ`. -/
theorem det_transferZ (V : ℤ → ℝ) (z : ℂ) (n : ℤ) : (transferZ V z n).det = 1 := by
  induction n using Int.induction_on with
  | zero => simp
  | succ i ih => rw [transferZ_succ, det_mul, det_transfer, ih, one_mul]
  | pred i ih =>
    have := transferZ_succ V z (-(i : ℤ) - 1)
    rw [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring] at this
    rw [this, det_mul, det_transfer, one_mul] at ih
    exact ih

/-- (2.2.9): `u` solves (2.2.2) iff `(u(n+1), u(n))ᵀ = A_z(n) (u(1), u(0))ᵀ` for every `n`. -/
theorem isSolution_iff_transferZ (V : ℤ → ℝ) (z : ℂ) (u : ℤ → ℂ) :
    IsSolution V z u ↔ ∀ n : ℤ, ![u (n + 1), u n] = transferZ V z n *ᵥ ![u 1, u 0] := by
  constructor
  · intro hu n
    induction n using Int.induction_on with
    | zero => simp
    | succ i ih =>
      rw [transferZ_succ, ← mulVec_mulVec, ← ih]
      have := transfer_step hu ((i : ℤ) + 1)
      simp only [add_sub_cancel_right] at this
      rw [this]
    | pred i ih =>
      have h := transfer_step hu (-(i : ℤ))
      rw [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring]
      rw [transferZ_pred V z (-(i : ℤ)), ← mulVec_mulVec, ← h] at ih
      have := congrArg (fun w => transferInv z (V (-(i : ℤ))) *ᵥ w) ih
      simpa only [mulVec_mulVec, ← Matrix.mul_assoc, transferInv_mul_transfer, Matrix.one_mul,
        one_mulVec] using this
  · intro h n
    have h1 := h n
    have h0 := h (n - 1)
    rw [transferZ_pred V z n, ← mulVec_mulVec, ← h0, sub_add_cancel] at h1
    have := congrFun h1 0
    simp [transfer, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
    linear_combination this

/-- (2.2.12): `A_z(n, k) = A_z(n) A_z(k)⁻¹`. -/
def transferZ₂ (V : ℤ → ℝ) (z : ℂ) (n k : ℤ) : Mat2 := transferZ V z n * (transferZ V z k)⁻¹

/-- (2.2.13): `(u(n+1), u(n))ᵀ = A_z(n, k) (u(k+1), u(k))ᵀ` for solutions `u`. -/
theorem transferZ₂_mulVec {V : ℤ → ℝ} {z : ℂ} {u : ℤ → ℂ} (hu : IsSolution V z u) (n k : ℤ) :
    ![u (n + 1), u n] = transferZ₂ V z n k *ᵥ ![u (k + 1), u k] := by
  have h := (isSolution_iff_transferZ V z u).mp hu
  have hk : (transferZ V z k)⁻¹ * transferZ V z k = 1 :=
    Matrix.nonsing_inv_mul _ (by rw [det_transferZ]; exact isUnit_one)
  calc ![u (n + 1), u n] = transferZ V z n *ᵥ ![u 1, u 0] := h n
    _ = (transferZ V z n * ((transferZ V z k)⁻¹ * transferZ V z k)) *ᵥ ![u 1, u 0] := by
        rw [hk, Matrix.mul_one]
    _ = (transferZ V z n * (transferZ V z k)⁻¹) *ᵥ (transferZ V z k *ᵥ ![u 1, u 0]) := by
        rw [mulVec_mulVec, Matrix.mul_assoc]
    _ = _ := by rw [← h k]; rfl

/-- The solution of (2.2.2) with initial data `u(1) = a`, `u(0) = b`. -/
def solFrom (V : ℤ → ℝ) (z : ℂ) (a b : ℂ) (n : ℤ) : ℂ := (transferZ V z n *ᵥ ![a, b]) 1

lemma solFrom_succ (V : ℤ → ℝ) (z : ℂ) (a b : ℂ) (n : ℤ) :
    solFrom V z a b (n + 1) = (transferZ V z n *ᵥ ![a, b]) 0 := by
  rw [solFrom, transferZ_succ, ← mulVec_mulVec]
  simp [transfer, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma solFrom_vec (V : ℤ → ℝ) (z : ℂ) (a b : ℂ) (n : ℤ) :
    ![solFrom V z a b (n + 1), solFrom V z a b n] = transferZ V z n *ᵥ ![a, b] := by
  ext i; fin_cases i
  · simp [solFrom_succ]
  · simp [solFrom]

@[simp] lemma solFrom_zero (V : ℤ → ℝ) (z : ℂ) (a b : ℂ) : solFrom V z a b 0 = b := by
  simp [solFrom]

@[simp] lemma solFrom_one (V : ℤ → ℝ) (z : ℂ) (a b : ℂ) : solFrom V z a b 1 = a := by
  have := solFrom_succ V z a b 0
  simpa using this

theorem isSolution_solFrom (V : ℤ → ℝ) (z : ℂ) (a b : ℂ) : IsSolution V z (solFrom V z a b) := by
  rw [isSolution_iff_transferZ]
  intro n
  rw [solFrom_vec, solFrom_one, solFrom_zero]

/-- Solutions are determined by their values at `0` and `1`. -/
theorem eq_solFrom {V : ℤ → ℝ} {z : ℂ} {u : ℤ → ℂ} (hu : IsSolution V z u) :
    u = solFrom V z (u 1) (u 0) := by
  funext n
  have h := congrFun ((isSolution_iff_transferZ V z u).mp hu n) 1
  simpa [solFrom] using h

theorem eq_zero_of_isSolution {V : ℤ → ℝ} {z : ℂ} {u : ℤ → ℂ} (hu : IsSolution V z u)
    (h0 : u 0 = 0) (h1 : u 1 = 0) : u = 0 := by
  rw [eq_solFrom hu, h0, h1]
  funext n; simp [solFrom]

lemma transferZ_succ_one (V : ℤ → ℝ) (z : ℂ) (n : ℤ) (j : Fin 2) :
    transferZ V z (n + 1) 1 j = transferZ V z n 0 j := by
  rw [transferZ_succ]; simp [transfer, Matrix.mul_apply, Fin.sum_univ_two]

/-- The solutions `u₁`, `u₂` with initial conditions (2.2.16). -/
def u₁ (V : ℤ → ℝ) (z : ℂ) : ℤ → ℂ := solFrom V z 1 0

/-- The solutions `u₁`, `u₂` with initial conditions (2.2.16). -/
def u₂ (V : ℤ → ℝ) (z : ℂ) : ℤ → ℂ := solFrom V z 0 1

/-- **Proposition 2.2.4**: the columns of `A_z(n)` are given by `u₁`, `u₂`, (2.2.15). -/
theorem transferZ_eq_u₁_u₂ (V : ℤ → ℝ) (z : ℂ) (n : ℤ) :
    transferZ V z n = !![u₁ V z (n + 1), u₂ V z (n + 1); u₁ V z n, u₂ V z n] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [u₁, u₂, solFrom, Matrix.mulVec, dotProduct, Fin.sum_univ_two, transferZ_succ_one]

/-! ### The Wronskian -/

/-- The Wronskian (2.2.14): `W(u, ũ)(n) = u(n) ũ(n+1) - ũ(n) u(n+1)`. -/
def wronskian (u v : ℤ → ℂ) (n : ℤ) : ℂ := u n * v (n + 1) - v n * u (n + 1)

/-- **Proposition 2.2.2** (conservation of the Wronskian). -/
theorem wronskian_succ {V : ℤ → ℝ} {z : ℂ} {u v : ℤ → ℂ} (hu : IsSolution V z u)
    (hv : IsSolution V z v) (n : ℤ) : wronskian u v (n + 1) = wronskian u v n := by
  have h1 := hu (n + 1)
  have h2 := hv (n + 1)
  simp only [add_sub_cancel_right] at h1 h2
  rw [wronskian, wronskian]
  linear_combination u (n + 1) * h2 - v (n + 1) * h1

/-- **Proposition 2.2.2**: the Wronskian of two solutions is independent of `n`. -/
theorem wronskian_const {V : ℤ → ℝ} {z : ℂ} {u v : ℤ → ℂ} (hu : IsSolution V z u)
    (hv : IsSolution V z v) (n : ℤ) : wronskian u v n = wronskian u v 0 := by
  induction n using Int.induction_on with
  | zero => rfl
  | succ i ih => rw [wronskian_succ hu hv, ih]
  | pred i ih =>
    rw [← ih, ← wronskian_succ hu hv (-(i : ℤ) - 1), show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring]

/-- **Proposition 2.2.2**: the Wronskian of two solutions vanishes iff they are linearly
dependent. -/
theorem wronskian_eq_zero_iff {V : ℤ → ℝ} {z : ℂ} {u v : ℤ → ℂ} (hu : IsSolution V z u)
    (hv : IsSolution V z v) :
    wronskian u v 0 = 0 ↔ ∃ a b : ℂ, (a ≠ 0 ∨ b ≠ 0) ∧ ∀ n, a * u n + b * v n = 0 := by
  constructor
  · intro hW
    rw [wronskian, zero_add] at hW
    have hsol : ∀ a b : ℂ, IsSolution V z (fun n => a * u n + b * v n) := by
      intro a b n
      have h1 := hu n; have h2 := hv n
      simp only
      linear_combination a * h1 + b * h2
    by_cases h0 : u 0 = 0 ∧ v 0 = 0
    · by_cases h1 : u 1 = 0 ∧ v 1 = 0
      · refine ⟨1, 0, Or.inl one_ne_zero, fun n => ?_⟩
        have := eq_zero_of_isSolution hu h0.1 h1.1
        simp [this]
      · refine ⟨v 1, -u 1, ?_, fun n => ?_⟩
        · by_contra hc; push Not at hc; exact h1 ⟨neg_eq_zero.mp hc.2, hc.1⟩
        · have := eq_zero_of_isSolution (hsol (v 1) (-u 1)) (by simp [h0.1, h0.2])
            (by simp; ring)
          simpa using congrFun this n
    · refine ⟨v 0, -u 0, ?_, fun n => ?_⟩
      · by_contra hc; push Not at hc; exact h0 ⟨neg_eq_zero.mp hc.2, hc.1⟩
      · have := eq_zero_of_isSolution (hsol (v 0) (-u 0)) (by simp; ring)
          (by simp; linear_combination -hW)
        simpa using congrFun this n
  · rintro ⟨a, b, hab, h⟩
    have h0 := h 0
    have h1 := h 1
    rw [wronskian, zero_add]
    rcases hab with ha | hb
    · have : a * (u 0 * v 1 - v 0 * u 1) = 0 := by
        linear_combination v 1 * h0 - v 0 * h1
      exact (mul_eq_zero.mp this).resolve_left ha
    · have : b * (u 0 * v 1 - v 0 * u 1) = 0 := by
        linear_combination (-(u 1)) * h0 + u 0 * h1
      exact (mul_eq_zero.mp this).resolve_left hb

/-! ### Proposition 2.2.6 -/

lemma norm_diag_le (c : ℂ) : ‖(!![c, 0; 0, 0] : Mat2)‖ ≤ ‖c‖ := by
  have : (!![c, 0; 0, 0] : Mat2) = diagonal ![c, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [this, l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg c)).mpr fun i => ?_
  fin_cases i <;> simp

lemma transfer_sub_transfer (z z' : ℂ) (v w : ℝ) :
    transfer z v - transfer z' w = !![(z - z') - ((v : ℂ) - w), 0; 0, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [transfer]; ring

/-- **Proposition 2.2.6** (perturbative estimate): if all one-step matrices
`T_z(n; V)`, `T_z(n; W)`, `z ∈ K`, have norm at most `Γ`, and `|V(j) - W(j)| ≤ δ` for
`1 ≤ j ≤ n`, then `‖A_z(n; V) - A_{z'}(n; W)‖ ≤ n Γⁿ⁻¹ (|z - z'| + δ)` for `z, z' ∈ K`. -/
theorem norm_transferProd_sub_le {V W : ℤ → ℝ} {K : Set ℂ} {Γ δ : ℝ}
    (hΓ : ∀ z ∈ K, ∀ n : ℤ, ‖transfer z (V n)‖ ≤ Γ ∧ ‖transfer z (W n)‖ ≤ Γ)
    {z z' : ℂ} (hz : z ∈ K) (hz' : z' ∈ K) (n : ℕ)
    (hδ : ∀ j : ℕ, 1 ≤ j → j ≤ n → |V j - W j| ≤ δ) :
    ‖transferProd V z n - transferProd W z' n‖ ≤ n * Γ ^ (n - 1) * (‖z - z'‖ + δ) := by
  have hΓ0 : 0 ≤ Γ := (norm_nonneg _).trans (hΓ z hz 0).1
  have hW : ∀ m : ℕ, ‖transferProd W z' m‖ ≤ Γ ^ m := by
    intro m
    induction m with
    | zero => simp [transferProd]
    | succ k ih =>
      rw [transferProd, pow_succ']
      exact (norm_mul_le _ _).trans (mul_le_mul (hΓ z' hz' _).2 ih (norm_nonneg _) hΓ0)
  induction n with
  | zero => simp [transferProd]
  | succ k ih =>
    have ih' := ih (fun j h1 h2 => hδ j h1 (by omega))
    have hdiff : ‖transfer z (V (k + 1 : ℕ)) - transfer z' (W (k + 1 : ℕ))‖ ≤ ‖z - z'‖ + δ := by
      rw [transfer_sub_transfer]
      refine (norm_diag_le _).trans ((norm_sub_le _ _).trans ?_)
      gcongr
      have := hδ (k + 1) (by omega) le_rfl
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      exact this
    have hsplit : transferProd V z (k + 1) - transferProd W z' (k + 1) =
        transfer z (V (k + 1 : ℕ)) * (transferProd V z k - transferProd W z' k) +
          (transfer z (V (k + 1 : ℕ)) - transfer z' (W (k + 1 : ℕ))) * transferProd W z' k := by
      simp only [transferProd]; push_cast; noncomm_ring
    rw [hsplit]
    have hδ0 : 0 ≤ ‖z - z'‖ + δ := le_trans (norm_nonneg _) hdiff
    calc ‖transfer z (V (k + 1 : ℕ)) * (transferProd V z k - transferProd W z' k) +
          (transfer z (V (k + 1 : ℕ)) - transfer z' (W (k + 1 : ℕ))) * transferProd W z' k‖
        ≤ Γ * (k * Γ ^ (k - 1) * (‖z - z'‖ + δ)) + (‖z - z'‖ + δ) * Γ ^ k := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · exact (norm_mul_le _ _).trans (mul_le_mul (hΓ z hz _).1 ih' (norm_nonneg _) hΓ0)
          · exact (norm_mul_le _ _).trans (mul_le_mul hdiff (hW k) (norm_nonneg _) hδ0)
      _ = ((k + 1 : ℕ) : ℝ) * Γ ^ (k + 1 - 1) * (‖z - z'‖ + δ) := by
          rcases k with _ | k
          · simp
          · simp only [Nat.add_sub_cancel, pow_succ]; push_cast; ring

end DF
