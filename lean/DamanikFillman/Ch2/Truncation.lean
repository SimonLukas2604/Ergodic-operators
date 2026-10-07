/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §2.2  Dirichlet truncations  (book pp. 140–147)

`DF.truncMat V a N` is the `N × N` matrix of `H_Λ` for `Λ = [a+1, a+N]` (2.2.17); in
particular `H_n = truncMat V 0 n` and `H_{[k+1,N]} = truncMat V k (N - k)`.

## Main results
* `DF.truncMat_mulVec` — the action of `H_Λ` (Dirichlet boundary conditions).
* **Proposition 2.2.5**: `DF.truncMat_eigen_simple` (simplicity of the eigenvalues of
  `H_Λ`), `DF.det_truncMat` (2.2.18) `u₁(n+1, z) = det(z - H_n)`, `DF.u₂_eq_det` (2.2.19),
  `DF.transferZ_eq_det` (2.2.20).
* **Proposition 2.2.9**: `DF.sol_eq_green_boundary` — `u(n) = -G_Λ(n,a) u(a-1) - G_Λ(n,b) u(b+1)`.
* **Proposition 2.2.10**, (2.2.33): `DF.green_truncMat` —
  `G_N(j,k) = -det(z - H_{[1,j-1]}) det(z - H_{[k+1,N]}) / det(z - H_N)` for `j ≤ k`; via the
  reflection identity `DF.det_truncMat_rev` and the Green-function row computation
  `DF.greenFun_row`.

## Not formalized
The norm bound (2.2.34).
-/
import DamanikFillman.Ch2.Green

noncomputable section

open Matrix

namespace DF

variable {V : ℤ → ℝ} {z : ℂ}

/-- The matrix of the Dirichlet truncation `H_Λ`, `Λ = [a+1, a+N]` (2.2.17). -/
def truncMat (V : ℤ → ℝ) (a : ℤ) (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => if i = j then (V (a + 1 + i) : ℂ) else
    if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then 1 else 0

/-- Extension by zero of a vector on `Fin N` to `ℤ` (index `k` ↔ site `a + 1 + k`). -/
def vext {N : ℕ} (v : Fin N → ℂ) (k : ℤ) : ℂ :=
  if h : 0 ≤ k ∧ k < N then v ⟨k.toNat, by omega⟩ else 0

lemma vext_coe {N : ℕ} (v : Fin N → ℂ) (i : Fin N) : vext v i = v i := by
  simp only [vext]
  rw [dif_pos (by constructor <;> omega)]
  congr 1

lemma vext_of_neg {N : ℕ} (v : Fin N → ℂ) {k : ℤ} (hk : k < 0) : vext v k = 0 := by
  simp only [vext]; rw [dif_neg (by omega)]

lemma vext_of_ge {N : ℕ} (v : Fin N → ℂ) {k : ℤ} (hk : (N : ℤ) ≤ k) : vext v k = 0 := by
  simp only [vext]; rw [dif_neg (by omega)]

lemma sum_fin_ite_eq {N : ℕ} (v : Fin N → ℂ) (k : ℤ) :
    ∑ j : Fin N, (if (j : ℤ) = k then v j else 0) = vext v k := by
  by_cases h : 0 ≤ k ∧ k < N
  · rw [Fintype.sum_eq_single ⟨k.toNat, by omega⟩]
    · simp only [vext]; rw [dif_pos h, if_pos (by simp; omega)]
    · intro j hj
      rw [if_neg]
      intro h'; apply hj; ext; simp; omega
  · rw [Finset.sum_eq_zero, vext, dif_neg h]
    intro j _
    rw [if_neg]; intro h'; apply h; constructor <;> omega

/-- The action of `H_Λ`: `(H_Λ v)_i = V(a+1+i) vᵢ + v_{i+1} + v_{i-1}` with `v` extended by
zero (Dirichlet boundary conditions). -/
theorem truncMat_mulVec (V : ℤ → ℝ) (a : ℤ) {N : ℕ} (v : Fin N → ℂ) (i : Fin N) :
    (truncMat V a N *ᵥ v) i = (V (a + 1 + i) : ℂ) * v i + vext v ((i : ℤ) + 1) +
      vext v ((i : ℤ) - 1) := by
  simp only [mulVec, dotProduct, truncMat]
  have hpt : ∀ j : Fin N, (if i = j then (V (a + 1 + i) : ℂ) else
      if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then 1 else 0) * v j =
      (if i = j then (V (a + 1 + i) : ℂ) * v i else 0) +
        (if (j : ℤ) = (i : ℤ) + 1 then v j else 0) + (if (j : ℤ) = (i : ℤ) - 1 then v j else 0) := by
    intro j
    by_cases h1 : i = j
    · subst h1
      have e1 : ¬ ((i : ℤ) = (i : ℤ) + 1) := by omega
      have e2 : ¬ ((i : ℤ) = (i : ℤ) - 1) := by omega
      simp [e1, e2]
    · rw [if_neg h1, if_neg h1]
      have h1' : (i : ℕ) ≠ j := fun h => h1 (Fin.ext h)
      by_cases h2 : (j : ℤ) = (i : ℤ) + 1
      · rw [if_pos (Or.inl (by omega)), if_pos h2, if_neg (by omega)]; ring
      · by_cases h3 : (j : ℤ) = (i : ℤ) - 1
        · rw [if_pos (Or.inr (by omega)), if_neg h2, if_pos h3]; ring
        · rw [if_neg (by omega), if_neg h2, if_neg h3]; ring
  rw [Finset.sum_congr rfl (fun j _ => hpt j), Finset.sum_add_distrib, Finset.sum_add_distrib,
    sum_fin_ite_eq, sum_fin_ite_eq]
  simp

/-! ### Simplicity of the eigenvalues of `H_Λ` -/

/-- The solution of (2.2.2) for the shifted potential `n ↦ V(a + n)` with `u(0) = 0`,
`u(1) = 1`. -/
def u₁At (V : ℤ → ℝ) (a : ℤ) (z : ℂ) : ℤ → ℂ := u₁ (fun n => V (a + n)) z

@[simp] lemma u₁At_zero (V : ℤ → ℝ) (a : ℤ) (z : ℂ) : u₁At V a z 0 = 0 := by simp [u₁At, u₁]
@[simp] lemma u₁At_one (V : ℤ → ℝ) (a : ℤ) (z : ℂ) : u₁At V a z 1 = 1 := by simp [u₁At, u₁]

lemma u₁At_sol (V : ℤ → ℝ) (a : ℤ) (z : ℂ) (n : ℤ) :
    u₁At V a z (n - 1) + u₁At V a z (n + 1) + (V (a + n) : ℂ) * u₁At V a z n =
      z * u₁At V a z n :=
  isSolution_solFrom (fun n => V (a + n)) z 1 0 n

/-- An eigenvector of `H_Λ` is determined by its first entry: `vᵢ = v₀ u₁(i+1)` for the
shifted potential. -/
theorem truncMat_eigen_eq {a : ℤ} {N : ℕ} {v : Fin N → ℂ} (hv : truncMat V a N *ᵥ v = z • v)
    (h0 : 0 < N) : ∀ k : ℤ, 0 ≤ k → k < N → vext v k = v ⟨0, h0⟩ * u₁At V a z (k + 1) := by
  have hrow : ∀ i : Fin N, vext v ((i : ℤ) - 1) + vext v ((i : ℤ) + 1) +
      (V (a + 1 + i) : ℂ) * vext v i = z * vext v i := by
    intro i
    have := congrFun hv i
    rw [truncMat_mulVec] at this
    simp only [Pi.smul_apply, smul_eq_mul] at this
    rw [vext_coe]; linear_combination this
  have key : ∀ k : ℕ, (k : ℤ) < N → vext v k = v ⟨0, h0⟩ * u₁At V a z (k + 1) ∧
      ((k : ℤ) + 1 < N → vext v (k + 1) = v ⟨0, h0⟩ * u₁At V a z (k + 2)) := by
    intro k
    induction k with
    | zero =>
      intro _
      have e0 : vext v 0 = v ⟨0, h0⟩ := by
        have := vext_coe v ⟨0, h0⟩; simpa using this
      refine ⟨by simp [e0], fun h1 => ?_⟩
      have := hrow ⟨0, h0⟩
      have e : ((⟨0, h0⟩ : Fin N) : ℤ) = 0 := rfl
      rw [e] at this
      norm_num at this
      rw [vext_of_neg v (by norm_num), e0] at this
      have hu := u₁At_sol V a z 1
      norm_num at hu
      norm_num
      linear_combination this - v ⟨0, h0⟩ * hu
    | succ k ih =>
      intro hk
      have ih' := ih (by omega)
      refine ⟨by push_cast; rw [ih'.2 (by omega)]; ring_nf, fun h2 => ?_⟩
      have := hrow ⟨k + 1, by omega⟩
      simp only [Fin.val_mk] at this
      push_cast at this
      rw [show (k : ℤ) + 1 - 1 = k by ring, ih'.1, ih'.2 (by omega)] at this
      have hu := u₁At_sol V a z ((k : ℤ) + 2)
      push_cast
      ring_nf at this hu ⊢
      linear_combination this - v ⟨0, h0⟩ * hu
  intro k hk0 hkN
  have := (key k.toNat (by omega)).1
  rwa [show ((k.toNat : ℕ) : ℤ) = k by omega] at this

/-- **Proposition 2.2.5**, first claim: every eigenvalue of `H_Λ` is simple. -/
theorem truncMat_eigen_simple {a : ℤ} {N : ℕ} {v w : Fin N → ℂ}
    (hv : truncMat V a N *ᵥ v = z • v) (hw : truncMat V a N *ᵥ w = z • w) :
    ∃ c d : ℂ, (c ≠ 0 ∨ d ≠ 0) ∧ c • v + d • w = 0 := by
  rcases Nat.eq_zero_or_pos N with rfl | h0
  · exact ⟨1, 0, Or.inl one_ne_zero, by ext i; exact i.elim0⟩
  by_cases hz : v ⟨0, h0⟩ = 0 ∧ w ⟨0, h0⟩ = 0
  · refine ⟨1, 0, Or.inl one_ne_zero, ?_⟩
    ext i
    have := truncMat_eigen_eq hv h0 i (by omega) (by omega)
    rw [vext_coe, hz.1, zero_mul] at this
    simp [this]
  · refine ⟨w ⟨0, h0⟩, -v ⟨0, h0⟩, ?_, ?_⟩
    · by_contra hc; push Not at hc; exact hz ⟨neg_eq_zero.mp hc.2, hc.1⟩
    · ext i
      have h1 := truncMat_eigen_eq hv h0 i (by omega) (by omega)
      have h2 := truncMat_eigen_eq hw h0 i (by omega) (by omega)
      rw [vext_coe] at h1 h2
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, h1, h2]
      ring

/-! ### Determinants: (2.2.18)–(2.2.20) -/

lemma truncMat_apply (V : ℤ → ℝ) (a : ℤ) (N : ℕ) (i j : Fin N) :
    truncMat V a N i j = if i = j then (V (a + 1 + i) : ℂ) else
      if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then 1 else 0 := rfl

/-- **Proposition 2.2.5**, (2.2.18) for a general interval `Λ = [a+1, a+N]`:
`det(z - H_Λ) = u₁(N+1)` for the shifted potential `n ↦ V(a+n)`. -/
theorem det_truncMat_shift (V : ℤ → ℝ) (a : ℤ) (z : ℂ) (N : ℕ) :
    (z • (1 : Matrix (Fin N) (Fin N) ℂ) - truncMat V a N).det = u₁At V a z (N + 1) := by
  rcases N with _ | n
  · simp
  set M := z • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) - truncMat V a (n + 1) with hM
  set U : Fin (n + 1) → ℂ := fun i => u₁At V a z ((i : ℤ) + 1)
  set c := u₁At V a z ((n : ℤ) + 2)
  set P := (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ).updateCol 0 U
  have hU : ∀ k : ℤ, -1 ≤ k → k ≤ n → vext U k = u₁At V a z (k + 1) := by
    intro k h1 h2
    rcases eq_or_lt_of_le h1 with h | h
    · subst h; rw [vext_of_neg U (by norm_num)]; simp
    · have := vext_coe U ⟨k.toNat, by omega⟩
      simp only [Fin.val_mk] at this
      rw [show ((k.toNat : ℕ) : ℤ) = k by omega] at this
      rw [this]; simp only [U]; congr 2; simp; omega
  have hP : P.det = 1 := by
    rw [det_of_isLowerTriangular P]
    · refine Finset.prod_eq_one fun i _ => ?_
      by_cases hi : i = 0
      · subst hi; simp [P, U]
      · simp [P, updateCol_apply, hi]
    · intro i j hij
      have hij' : i < j := hij
      have hj : j ≠ 0 := by intro h; subst h; exact absurd hij' (by simp)
      simp [P, updateCol_apply, hj, ne_of_lt hij']
  have hMU : M *ᵥ U = Pi.single (Fin.last n) c := by
    ext i
    rw [hM, sub_mulVec, smul_mulVec, one_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      truncMat_mulVec]
    have hsol := u₁At_sol V a z ((i : ℤ) + 1)
    rw [show (i : ℤ) + 1 - 1 = i by ring, show a + ((i : ℤ) + 1) = a + 1 + i by ring] at hsol
    have him : vext U ((i : ℤ) - 1) = u₁At V a z i := by
      rw [hU _ (by omega) (by omega)]; ring_nf
    rw [him]
    by_cases hi : i = Fin.last n
    · subst hi
      rw [vext_of_ge U (by simp), Pi.single_eq_same]
      simp only [Fin.val_last, U, c] at hsol ⊢
      rw [show (n : ℤ) + 1 + 1 = n + 2 by ring] at hsol
      linear_combination -hsol
    · have hin : (i : ℕ) < n := by
        have := Fin.val_lt_last hi; simpa using this
      rw [hU _ (by omega) (by omega), Pi.single_eq_of_ne hi]
      simp only [U]
      rw [show (i : ℤ) + 1 + 1 = i + 2 by ring] at hsol ⊢
      linear_combination -hsol
  have hQ : M * P = M.updateCol 0 (Pi.single (Fin.last n) c) := by
    rw [mul_updateCol, Matrix.mul_one, hMU]
  have hdet : (M * P).det = M.det := by rw [det_mul, hP, mul_one]
  rw [← hdet, hQ, det_succ_column_zero, Fintype.sum_eq_single (Fin.last n)]
  · have hS : ((M.updateCol 0 (Pi.single (Fin.last n) c)).submatrix (Fin.last n).succAbove
        Fin.succ).det = (-1) ^ n := by
      have hdiag : ∀ r : Fin n, ((M.updateCol 0 (Pi.single (Fin.last n) c)).submatrix
          (Fin.last n).succAbove Fin.succ) r r = -1 := by
        intro r
        simp only [submatrix_apply, Fin.succAbove_last, updateCol_apply, Fin.succ_ne_zero,
          if_false, hM, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, truncMat_apply]
        have h1 : (Fin.castSucc r) ≠ Fin.succ r := by
          intro h; have := congrArg Fin.val h; simp at this
        rw [one_apply_ne h1, if_neg h1, if_pos (Or.inl (by simp))]; ring
      rw [det_of_isLowerTriangular]
      · rw [Finset.prod_congr rfl (fun r _ => hdiag r)]; simp
      · intro r k hrk
        have hrk' : r < k := hrk
        simp only [submatrix_apply, Fin.succAbove_last, updateCol_apply, Fin.succ_ne_zero,
          if_false, hM, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, truncMat_apply]
        have h1 : (Fin.castSucc r) ≠ Fin.succ k := by
          intro h; have := congrArg Fin.val h; simp at this; omega
        rw [one_apply_ne h1, if_neg h1, if_neg]
        · ring
        · simp only [Fin.coe_castSucc, Fin.val_succ]
          have : (r : ℕ) < k := hrk'
          omega
    rw [hS]
    simp only [updateCol_apply, if_true, Pi.single_eq_same, Fin.val_last]
    rw [show c = u₁At V a z ((n + 1 : ℕ) + 1 : ℤ) by simp only [c]; push_cast; ring_nf]
    rw [mul_comm ((-1 : ℂ) ^ n), mul_assoc, ← mul_pow]
    simp
  · intro i hi
    simp [updateCol_apply, Pi.single_eq_of_ne hi]

/-- **Proposition 2.2.5**, (2.2.18): `u₁(n+1, z) = det(z - H_n)`. -/
theorem det_truncMat (V : ℤ → ℝ) (z : ℂ) (n : ℕ) :
    (z • (1 : Matrix (Fin n) (Fin n) ℂ) - truncMat V 0 n).det = u₁ V z (n + 1) := by
  rw [det_truncMat_shift]
  simp only [u₁At, zero_add]

/-- **Proposition 2.2.5**, (2.2.19): `u₂(n+2, z) = -det(z - H_{[2, n+1]})`
(`H_{[2,n+1]} = truncMat V 1 n`). -/
theorem u₂_eq_det (V : ℤ → ℝ) (z : ℂ) (n : ℕ) :
    u₂ V z (n + 2) = -(z • (1 : Matrix (Fin n) (Fin n) ℂ) - truncMat V 1 n).det := by
  rw [det_truncMat_shift]
  have hs2 : IsSolution V z (u₂ V z) := isSolution_solFrom _ _ _ _
  have hw : (fun k : ℤ => -u₂ V z (k + 1)) = u₁At V 1 z := by
    apply eq_of_isSolution (V := fun n => V (1 + n)) (z := z)
    · intro k
      have := hs2 (k + 1)
      simp only
      rw [show k + 1 - 1 = k - 1 + 1 by ring, show k + 1 + 1 = k + 1 + 1 by ring,
        show 1 + k = k + 1 by ring] at *
      linear_combination -this
    · exact isSolution_solFrom _ _ _ _
    · simp [u₁At, u₂]
    · have := hs2 1
      simp [u₂] at this ⊢
      linear_combination -this
  have := congrFun hw ((n : ℤ) + 1)
  rw [show (n : ℤ) + 1 + 1 = n + 2 by ring] at this
  push_cast
  rw [show (n : ℤ) + 1 = (n : ℤ) + 1 by rfl, ← this]
  ring

/-- **Proposition 2.2.5**, (2.2.20): the transfer matrix in terms of Dirichlet determinants,
`A_z(n) = [[det(z - H_n), -det(z - H̃_n)], [det(z - H_{n-1}), -det(z - H̃_{n-1})]]`
(`n = m + 2`, `H̃_n = H_{[2,n]}`). -/
theorem transferZ_eq_det (V : ℤ → ℝ) (z : ℂ) (m : ℕ) :
    transferZ V z ((m : ℤ) + 2) =
      !![(z • (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℂ) - truncMat V 0 (m + 2)).det,
        -(z • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) - truncMat V 1 (m + 1)).det;
        (z • (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) - truncMat V 0 (m + 1)).det,
        -(z • (1 : Matrix (Fin m) (Fin m) ℂ) - truncMat V 1 m).det] := by
  rw [transferZ_eq_u₁_u₂, det_truncMat, det_truncMat, ← u₂_eq_det, ← u₂_eq_det]
  push_cast
  ring_nf

/-! ### Proposition 2.2.9 -/

/-- **Proposition 2.2.9**: for `Λ = [a, a+n]`, `z ∉ σ(H_Λ)` and a solution `u` of (2.2.2),
`u(m) = -G_Λ(m, a) u(a-1) - G_Λ(m, b) u(b+1)` for `m ∈ Λ`, where
`G_Λ = (H_Λ - z)⁻¹` (2.2.29). -/
theorem sol_eq_green_boundary {u : ℤ → ℂ} (hu : IsSolution V z u) (a : ℤ) (n : ℕ)
    (hz : (truncMat V (a - 1) (n + 1) - z • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).det ≠ 0)
    (i : Fin (n + 1)) :
    u (a + i) = -((truncMat V (a - 1) (n + 1) - z • 1)⁻¹ i 0) * u (a - 1) -
      ((truncMat V (a - 1) (n + 1) - z • 1)⁻¹ i (Fin.last n)) * u (a + n + 1) := by
  set T := truncMat V (a - 1) (n + 1) - z • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
  set φ : Fin (n + 1) → ℂ := fun j => u (a + j)
  have hφ : T *ᵥ φ = fun j => -(if j = 0 then u (a - 1) else 0) -
      (if j = Fin.last n then u (a + n + 1) else 0) := by
    ext j
    simp only [T, sub_mulVec, smul_mulVec, one_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      truncMat_mulVec]
    have hj := hu (a + j)
    have e1 : vext φ ((j : ℤ) + 1) = if j = Fin.last n then 0 else u (a + j + 1) := by
      split_ifs with h
      · subst h; exact vext_of_ge φ (by simp)
      · have hj' : (j : ℕ) < n := by have := Fin.val_lt_last h; simpa using this
        have := vext_coe φ ⟨j + 1, by omega⟩
        simp only [Fin.val_mk, φ] at this
        push_cast at this
        rw [this]; ring_nf
    have e2 : vext φ ((j : ℤ) - 1) = if j = 0 then 0 else u (a + j - 1) := by
      split_ifs with h
      · subst h; exact vext_of_neg φ (by simp)
      · have hj' : 1 ≤ (j : ℕ) := by
          rcases Nat.eq_zero_or_pos j with h' | h'
          · exact absurd (Fin.ext h') h
          · exact h'
        have := vext_coe φ ⟨j - 1, by omega⟩
        simp only [Fin.val_mk, φ] at this
        rw [show ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 by omega] at this
        rw [this]; ring_nf
    rw [e1, e2]
    simp only [φ]
    rw [show a - 1 + 1 + (j : ℤ) = a + j by ring]
    by_cases h0 : j = 0 <;> by_cases hl : j = Fin.last n
    · rw [if_pos hl, if_pos h0, if_pos h0, if_pos hl]
      have : (j : ℤ) = 0 := by rw [h0]; rfl
      have hn : (n : ℤ) = 0 := by have := congrArg Fin.val (h0.symm.trans hl); simp at this; omega
      rw [this] at hj ⊢; rw [hn]; simp at hj ⊢; linear_combination hj
    · rw [if_neg hl, if_pos h0, if_pos h0, if_neg hl]
      have : (j : ℤ) = 0 := by rw [h0]; rfl
      rw [this] at hj ⊢; simp at hj ⊢; linear_combination hj
    · rw [if_pos hl, if_neg h0, if_neg h0, if_pos hl]
      have : (j : ℤ) = n := by rw [hl]; simp
      rw [this] at hj ⊢
      rw [show a + (n : ℤ) - 1 = a + n - 1 by ring] at *
      linear_combination hj
    · rw [if_neg hl, if_neg h0, if_neg h0, if_neg hl]
      linear_combination hj
  have hinv : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul T (isUnit_iff_ne_zero.mpr hz)
  have hφ' : φ = T⁻¹ *ᵥ (T *ᵥ φ) := by rw [mulVec_mulVec, hinv, one_mulVec]
  have := congrFun hφ' i
  rw [hφ] at this
  simp only [φ] at this
  rw [this]
  simp only [mulVec, dotProduct, mul_sub, mul_neg, mul_ite, mul_zero, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/-! ### Proposition 2.2.10 -/

/-- Reversal of the interval: `H_{[j+1, j+m]}` for `V` is unitarily equivalent (by reversing
the order of the sites) to the corresponding truncation of the reflected potential
`t ↦ V(N + 1 - t)`. -/
lemma truncMat_rev (V : ℤ → ℝ) (z : ℂ) (N j m : ℕ) (h : j + m = N) :
    (z • (1 : Matrix (Fin m) (Fin m) ℂ) - truncMat V j m).submatrix Fin.rev Fin.rev =
      z • 1 - truncMat (fun t => V (N + 1 - t)) 0 m := by
  ext i i'
  simp only [submatrix_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, truncMat_apply,
    Fin.rev_inj]
  by_cases hii : i = i'
  · subst hii
    simp only [one_apply_eq, if_true]
    have hi := i.2
    congr 3
    simp only [Fin.val_rev]
    push_cast [Nat.cast_sub (show (i : ℕ) + 1 ≤ m by omega)]
    have : (j : ℤ) + m = N := by exact_mod_cast h
    linarith
  · have hr : Fin.rev i ≠ Fin.rev i' := fun h => hii (Fin.rev_injective h)
    rw [one_apply_ne hr, one_apply_ne hii, if_neg hii, if_neg hii]
    simp only [Fin.val_rev]
    have hi := i.2; have hi' := i'.2
    by_cases hadj : (i : ℕ) + 1 = i' ∨ (i' : ℕ) + 1 = i
    · rw [if_pos (by omega), if_pos hadj]
    · rw [if_neg (by omega), if_neg hadj]

lemma det_truncMat_rev (V : ℤ → ℝ) (z : ℂ) (N j m : ℕ) (h : j + m = N) :
    (z • (1 : Matrix (Fin m) (Fin m) ℂ) - truncMat V j m).det =
      u₁ (fun t => V (N + 1 - t)) z (m + 1) := by
  rw [← det_submatrix_equiv_self Fin.revPerm, show ⇑(Fin.revPerm (n := m)) = Fin.rev from rfl,
    truncMat_rev V z N j m h, det_truncMat]

/-- One row of the equation `(H - z) G(·, c) = δ_c` for the Green function built from two
solutions (computation behind Propositions 2.2.7 and 2.2.10). -/
lemma greenFun_row {um up : ℤ → ℂ} (hum : IsSolution V z um) (hup : IsSolution V z up)
    (hW : wronskian um up 0 ≠ 0) (c s : ℤ) :
    greenFun um up c (s - 1) + greenFun um up c (s + 1) + (V s : ℂ) * greenFun um up c s =
      z * greenFun um up c s + if s = c then 1 else 0 := by
  rcases lt_trichotomy s c with hk | rfl | hk
  · simp only [greenFun, min_eq_left (by omega : s + 1 ≤ c), max_eq_right (by omega : s + 1 ≤ c),
      min_eq_left (by omega : s - 1 ≤ c), max_eq_right (by omega : s - 1 ≤ c),
      min_eq_left hk.le, max_eq_right hk.le, if_neg hk.ne]
    have := hum s
    field_simp
    linear_combination (up c) * this
  · simp only [greenFun, min_self, max_self, if_pos rfl, ite_true,
      min_eq_right (by omega : s ≤ s + 1), max_eq_left (by omega : s ≤ s + 1),
      min_eq_left (by omega : s - 1 ≤ s), max_eq_right (by omega : s - 1 ≤ s)]
    have h1 := hum s
    have hWk := wronskian_const hum hup s
    rw [wronskian] at hWk
    field_simp
    linear_combination (up s) * h1 + hWk
  · simp only [greenFun, min_eq_right (by omega : c ≤ s + 1), max_eq_left (by omega : c ≤ s + 1),
      min_eq_right (by omega : c ≤ s - 1), max_eq_left (by omega : c ≤ s - 1),
      min_eq_right hk.le, max_eq_left hk.le, if_neg hk.ne']
    have := hup s
    field_simp
    linear_combination (um c) * this

/-- **Proposition 2.2.10**, (2.2.33): for `0 ≤ j ≤ k < N` (sites `j+1 ≤ k+1` of `[1, N]`) and
`z ∉ σ(H_N)`,
`G_N(j+1, k+1; z) = -det(z - H_{[1,j]}) det(z - H_{[k+2,N]}) / det(z - H_N)`. -/
theorem green_truncMat (V : ℤ → ℝ) (z : ℂ) (N : ℕ) (j k : Fin N) (hjk : j ≤ k)
    (hz : (z • (1 : Matrix (Fin N) (Fin N) ℂ) - truncMat V 0 N).det ≠ 0) :
    (truncMat V 0 N - z • (1 : Matrix (Fin N) (Fin N) ℂ))⁻¹ j k =
      -(z • (1 : Matrix (Fin j) (Fin j) ℂ) - truncMat V 0 j).det *
        (z • (1 : Matrix (Fin (N - (k + 1))) (Fin (N - (k + 1))) ℂ) -
          truncMat V (k + 1) (N - (k + 1))).det /
        (z • (1 : Matrix (Fin N) (Fin N) ℂ) - truncMat V 0 N).det := by
  set W : ℤ → ℝ := fun t => V (N + 1 - t)
  set um : ℤ → ℂ := u₁ V z
  set up : ℤ → ℂ := fun s => u₁ W z ((N : ℤ) + 1 - s)
  have hum : IsSolution V z um := isSolution_solFrom _ _ _ _
  have hup : IsSolution V z up := by
    intro s
    have := isSolution_solFrom W z 1 0 ((N : ℤ) + 1 - s)
    simp only [up, u₁, W] at this ⊢
    rw [show (N : ℤ) + 1 - (s - 1) = (N : ℤ) + 1 - s + 1 by ring,
      show (N : ℤ) + 1 - (s + 1) = (N : ℤ) + 1 - s - 1 by ring,
      show (N : ℤ) + 1 - ((N : ℤ) + 1 - s) = s by ring] at *
    linear_combination this
  have hupN : up ((N : ℤ) + 1) = 0 := by simp [up, u₁]
  have hum0 : um 0 = 0 := by simp [um, u₁]
  have hdetN : (z • (1 : Matrix (Fin N) (Fin N) ℂ) - truncMat V 0 N).det = up 0 := by
    have := det_truncMat_rev V z N 0 N (by omega)
    simp only [Nat.cast_zero] at this
    rw [this]; simp [up, W]
  have hdetk : (z • (1 : Matrix (Fin (N - (k + 1))) (Fin (N - (k + 1))) ℂ) -
      truncMat V (k + 1) (N - (k + 1))).det = up ((k : ℤ) + 1) := by
    have := det_truncMat_rev V z N (k + 1) (N - (k + 1)) (by omega)
    push_cast at this
    rw [this]
    simp only [up, W]
    congr 1
    have := k.2
    push_cast [Nat.cast_sub (show (k : ℕ) + 1 ≤ N by omega)]
    ring
  have hWr : wronskian um up 0 = -up 0 := by
    simp [wronskian, hum0, um, u₁]
  have hW : wronskian um up 0 ≠ 0 := by rw [hWr, ← hdetN]; exact neg_ne_zero.mpr hz
  set Φ := greenFun um up ((k : ℤ) + 1)
  set φ : Fin N → ℂ := fun i => Φ ((i : ℤ) + 1)
  have hΦ0 : Φ 0 = 0 := by
    simp only [Φ, greenFun, min_eq_left (by omega : (0 : ℤ) ≤ (k : ℤ) + 1), hum0, zero_mul,
      zero_div]
  have hΦN : Φ ((N : ℤ) + 1) = 0 := by
    have := k.2
    simp only [Φ, greenFun, max_eq_left (by omega : (k : ℤ) + 1 ≤ (N : ℤ) + 1), hupN, mul_zero,
      zero_div]
  have hvext : ∀ t : ℤ, -1 ≤ t → t ≤ N → vext φ t = Φ (t + 1) := by
    intro t h1 h2
    rcases eq_or_lt_of_le h1 with h | h
    · subst h; rw [vext_of_neg φ (by norm_num)]; simp [hΦ0]
    rcases eq_or_lt_of_le h2 with h' | h'
    · subst h'; rw [vext_of_ge φ le_rfl, hΦN]
    · have key : vext φ t = φ ⟨t.toNat, by omega⟩ := by
        simp only [vext]; rw [dif_pos (by omega)]
      rw [key]
      show Φ (((t.toNat : ℕ) : ℤ) + 1) = Φ (t + 1)
      rw [show ((t.toNat : ℕ) : ℤ) = t by omega]
  set T := truncMat V 0 N - z • (1 : Matrix (Fin N) (Fin N) ℂ)
  have hTφ : T *ᵥ φ = Pi.single k 1 := by
    ext i
    simp only [T, sub_mulVec, smul_mulVec, one_mulVec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      truncMat_mulVec]
    have hi := i.2
    rw [hvext _ (by omega) (by omega), hvext _ (by omega) (by omega)]
    have := greenFun_row hum hup hW ((k : ℤ) + 1) ((i : ℤ) + 1)
    simp only [φ]
    rw [show (i : ℤ) + 1 + 1 = (i : ℤ) + 1 + 1 by rfl, show (i : ℤ) - 1 + 1 = (i : ℤ) + 1 - 1 by ring,
      show (0 : ℤ) + 1 + (i : ℤ) = (i : ℤ) + 1 by ring]
    rw [Pi.single_apply]
    have hik : ((i : ℤ) + 1 = (k : ℤ) + 1) ↔ i = k := by
      constructor
      · intro h; ext; omega
      · intro h; rw [h]
    simp only [hik] at this
    linear_combination this
  have hdetT : T.det ≠ 0 := by
    have : T = -(z • (1 : Matrix (Fin N) (Fin N) ℂ) - truncMat V 0 N) := by simp [T]
    rw [this, det_neg]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hz
  have hinv : T⁻¹ * T = 1 := Matrix.nonsing_inv_mul T (isUnit_iff_ne_zero.mpr hdetT)
  have hφ : φ = T⁻¹ *ᵥ Pi.single k 1 := by rw [← hTφ, mulVec_mulVec, hinv, one_mulVec]
  have hj : φ j = T⁻¹ j k := by
    rw [hφ]; simp [mulVec, dotProduct, Pi.single_apply]
  rw [← hj]
  simp only [φ, Φ, greenFun]
  have hjk' : (j : ℤ) + 1 ≤ (k : ℤ) + 1 := by have : (j : ℕ) ≤ k := hjk; omega
  rw [min_eq_left hjk', max_eq_right hjk', hWr, hdetk, hdetN, det_truncMat]
  simp only [um]
  push_cast
  field_simp

end DF
