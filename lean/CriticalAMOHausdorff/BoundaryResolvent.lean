/-
Copyright (c) 2026. Formalization of
  S. Becker, S. Jitomirskaya, I. Krasovsky, "Critical almost Mathieu operator: hidden
  singularity, gap continuity, and the Hausdorff dimension of the spectrum"
  (arXiv:1909.04429v2).

# Boundary resolvent: the algebraic and finite-dimensional cores of Lemma `lemma-subm`

Paper §"Finite covers for the spectrum", subsection "Separation of blocks"
(`section-separation`, tex l. 1067–1205).

1. **The (ABBA) identity** (eq. `ABBA`, l. 1166–1170), for bounded operators between two
   different spaces: if `1 + 𝒴𝒳` is invertible then so is `1 + 𝒳𝒴`, with inverse
   `1 - 𝒳 (1 + 𝒴𝒳)⁻¹ 𝒴` (`abba_mul_eq_one`, `abba_mul_eq_one'`, `isUnit_one_add_comp`).
2. **Abstract Neumann/Woodbury step** (proof of `lemma-subm`, l. 1153–1180, eq. `A-E-factor`):
   if `D - E` is invertible and `‖Γ_out (D-E)⁻¹ Γ_in‖ ‖Φ‖ < 1`, then `D + Γ_in Φ Γ_out - E` is
   invertible (`isUnit_add_boundary_of_norm_lt`).  In the paper `Γ_in = Γ^*`, `Γ_out = Γ`,
   `Φ = F`, and `Γ (D-E)⁻¹ Γ^* = G(E)` is the boundary resolvent.
3. **The blocks** `B̂_N(x)` of (`BhN`, l. 1279–1286) (`blockMatrix`), the boundary map `Γ̂_N` and
   the projection `P_N = Γ̂_N^* Γ̂_N` of (`bp`, l. 1271–1276) (`bdry`, `bdryProj`).
4. **Hermitian matrix facts** used in the proof: `‖A‖ ≤ max |eigenvalue|`
   (`IsHermitian.norm_le_of_abs_eigenvalues_le`), and the resolvent bound
   `‖(A - E)⁻¹‖ ≤ dist(E, σ(A))⁻¹` (`IsHermitian.resolvent_spec`).
5. **The finite block step** (proof of `lemma-subm`, l. 1185–1204, eqs. `Gk-def`, `mu-v`):
   if the `2 × 2` boundary resolvent `G_k(E) = Γ̂ (B - E)⁻¹ Γ̂^*` has an eigenvalue `μ ≠ 0`, then
   `V = -μ⁻¹ v v^*` is Hermitian with `‖V‖ ≤ |μ|⁻¹` and `E ∈ σ(B + Γ̂^* V Γ̂)`
   (`block_step`); in particular `‖G_k(E)‖ > (2τ)⁻¹` produces such a `V` with `‖V‖ < 2τ`
   (`block_step_of_norm_gt`), and conversely if no such `V` exists, `‖G_k(E)‖ ≤ (2τ)⁻¹`
   (`norm_bdryResolvent_le`).

## Conventions

* Matrices act on `ℂ^N` with the Euclidean norm; **norms of matrices are `ℓ²` operator norms**
  (Mathlib's scoped instances `Matrix.Norms.L2Operator`, opened in this file).  This is the norm
  `‖V‖` of the paper, and for Hermitian matrices it is the maximal modulus of an eigenvalue.
* The spectrum of a matrix `M` is `spectrum ℝ M` (`M` viewed as an element of the real algebra
  `Matrix (Fin N) (Fin N) ℂ`); for Hermitian `M` it is the set of eigenvalues.
* `blockMatrix v b α N x` is `B̂_N(x)`: `(B̂_N)_{j,j} = v(x + (j+1)α)`,
  `(B̂_N)_{j,j+1} = (B̂_N)_{j+1,j} = b(x + (j+1)α)`.  With `v = 0` and `b = 2 sin(π·)` this is the
  block `B_N(x)` of the chiral representation.
-/
import CriticalAMOHausdorff.Basic
import SpectralGapsDimension.MatrixLemmas

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator

namespace CAH

/-! ## 1. The (ABBA) identity for operators between two spaces -/

section ABBA

variable {H F : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [NormedAddCommGroup F]
  [NormedSpace ℂ F]

/-- **(ABBA)**, right inverse (eq. `ABBA`, l. 1166–1170): if `W` is a right inverse of
`1 + 𝒴𝒳`, then `1 - 𝒳 W 𝒴` is a right inverse of `1 + 𝒳𝒴`. -/
theorem abba_mul_eq_one (X : F →L[ℂ] H) (Y : H →L[ℂ] F) (W : F →L[ℂ] F)
    (hW : (1 + Y.comp X) * W = 1) :
    (1 + X.comp Y) * (1 - X.comp (W.comp Y)) = 1 := by
  ext h
  have h1 := congrArg (fun T : F →L[ℂ] F => X (T (Y h))) hW
  simp only [mul_apply_eq_comp, _root_.add_apply,
    one_apply_eq_self, ContinuousLinearMap.coe_comp, Function.comp_apply,
    map_add] at h1
  simp only [mul_apply_eq_comp, _root_.add_apply,
    _root_.sub_apply, one_apply_eq_self, ContinuousLinearMap.coe_comp,
    Function.comp_apply, map_sub]
  rw [← h1]
  abel

/-- **(ABBA)**, left inverse: if `W` is a left inverse of `1 + 𝒴𝒳`, then `1 - 𝒳 W 𝒴` is a left
inverse of `1 + 𝒳𝒴`. -/
theorem abba_mul_eq_one' (X : F →L[ℂ] H) (Y : H →L[ℂ] F) (W : F →L[ℂ] F)
    (hW : W * (1 + Y.comp X) = 1) :
    (1 - X.comp (W.comp Y)) * (1 + X.comp Y) = 1 := by
  ext h
  have h1 : X (W (Y (h + X (Y h)))) = X (Y h) := by
    have := congrArg (fun T : F →L[ℂ] F => X (T (Y h))) hW
    simpa [map_add] using this
  have e : ((1 - X.comp (W.comp Y)) * (1 + X.comp Y)) h =
      (h + X (Y h)) - X (W (Y (h + X (Y h)))) := rfl
  rw [e, h1, add_sub_cancel_right]
  rfl

/-- **(ABBA)**, invertibility form: if `1 + 𝒴𝒳` is invertible (on `F`), then `1 + 𝒳𝒴` is
invertible (on `H`). -/
theorem isUnit_one_add_comp (X : F →L[ℂ] H) (Y : H →L[ℂ] F) (h : IsUnit (1 + Y.comp X)) :
    IsUnit (1 + X.comp Y) := by
  obtain ⟨u, hu⟩ := h
  refine ⟨⟨1 + X.comp Y, 1 - X.comp ((u⁻¹ : (F →L[ℂ] F)ˣ).val.comp Y), ?_, ?_⟩, rfl⟩
  · exact abba_mul_eq_one X Y _ (by rw [← hu]; exact u.mul_inv)
  · exact abba_mul_eq_one' X Y _ (by rw [← hu]; exact u.inv_mul)

/-- **Neumann + Woodbury step of Lemma `lemma-subm`** (l. 1153–1180, eq. `A-E-factor`).
Let `D' = D - E` be invertible with inverse `Dinv`, and let `Γ_in : F → H`, `Φ : F → F`,
`Γ_out : H → F` be bounded, `F` complete.  If `‖Γ_out Dinv Γ_in‖ · ‖Φ‖ < 1` then
`D' + Γ_in Φ Γ_out` is invertible.

(In the paper, `Γ_in = Γ^*`, `Γ_out = Γ`, `Φ = F`, and `G(E) = Γ (D-E)⁻¹ Γ^*`; the factorisation
is `A - E = [1 + 𝒳𝒴](D - E)` with `𝒳 = Γ^* F`, `𝒴 = Γ(D-E)⁻¹`, `𝒴𝒳 = G(E) F`.) -/
theorem isUnit_add_boundary_of_norm_lt [CompleteSpace F] (D' Dinv : H →L[ℂ] H)
    (h2 : Dinv * D' = 1) (h1 : D' * Dinv = 1)
    (Γin : F →L[ℂ] H) (Φ : F →L[ℂ] F) (Γout : H →L[ℂ] F)
    (hnorm : ‖Γout.comp (Dinv.comp Γin)‖ * ‖Φ‖ < 1) :
    IsUnit (D' + Γin.comp (Φ.comp Γout)) := by
  set X : F →L[ℂ] H := Γin.comp Φ
  set Y : H →L[ℂ] F := Γout.comp Dinv
  have hYX : ‖-(Y.comp X)‖ < 1 := by
    rw [norm_neg]
    calc ‖Y.comp X‖ = ‖(Γout.comp (Dinv.comp Γin)).comp Φ‖ := rfl
      _ ≤ ‖Γout.comp (Dinv.comp Γin)‖ * ‖Φ‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ < 1 := hnorm
  have hU : IsUnit (1 + Y.comp X) := by
    have := (Units.oneSub _ hYX).isUnit
    rwa [Units.val_oneSub, sub_neg_eq_add] at this
  have hXY := isUnit_one_add_comp X Y hU
  have hD : IsUnit D' := ⟨⟨D', Dinv, h1, h2⟩, rfl⟩
  have hfac : D' + Γin.comp (Φ.comp Γout) = (1 + X.comp Y) * D' := by
    ext h
    have := congrArg (fun T : H →L[ℂ] H => T h) h2
    simp only [mul_apply_eq_comp, one_apply_eq_self] at this
    simp [X, Y, this]
  rw [hfac]
  exact hXY.mul hD

end ABBA

/-! ## 2. Blocks, boundary map and boundary projection -/

/-- The tridiagonal block `B̂_N(x)` of (`BhN`, l. 1279–1286):
`B̂_N(x)_{j,j} = v(x+(j+1)α)` and `B̂_N(x)_{j+1,j} = B̂_N(x)_{j,j+1} = b(x+(j+1)α)`. -/
def blockMatrix (v b : ℝ → ℝ) (α : ℝ) (N : ℕ) (x : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j =>
    if i = j then ((v (x + ((i : ℕ) + 1) * α) : ℝ) : ℂ)
    else if (j : ℕ) = i + 1 then ((b (x + ((i : ℕ) + 1) * α) : ℝ) : ℂ)
    else if (i : ℕ) = j + 1 then ((b (x + ((j : ℕ) + 1) * α) : ℝ) : ℂ)
    else 0

/-- The boundary map `Γ̂_N : ℂ^N → ℂ^2`, `Γ̂_N u = (u_0, u_{N-1})` of (`bp`, l. 1271–1276). -/
def bdry (N : ℕ) : Matrix (Fin 2) (Fin N) ℂ :=
  Matrix.of fun i j =>
    if ((i : ℕ) = 0 ∧ (j : ℕ) = 0) ∨ ((i : ℕ) = 1 ∧ (j : ℕ) + 1 = N) then 1 else 0

/-- The boundary projection `P_N = Γ̂_N^* Γ̂_N` onto `span{e_0, e_{N-1}}` of (`bp`). -/
def bdryProj (N : ℕ) : Matrix (Fin N) (Fin N) ℂ := (bdry N)ᴴ * bdry N

/-- The `2 × 2` boundary resolvent `G(E) = Γ̂_N (B - E)⁻¹ Γ̂_N^*` of a block (eq. `Gk-def`). -/
def bdryResolvent {N : ℕ} (B : Matrix (Fin N) (Fin N) ℂ) (E : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  bdry N * (B - (E : ℂ) • 1)⁻¹ * (bdry N)ᴴ

lemma blockMatrix_isHermitian (v b : ℝ → ℝ) (α : ℝ) (N : ℕ) (x : ℝ) :
    (blockMatrix v b α N x).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, blockMatrix, of_apply]
  by_cases hij : i = j
  · subst hij; simp
  · have hji : j ≠ i := fun h => hij h.symm
    simp only [if_neg hij, if_neg hji]
    by_cases h1 : (j : ℕ) = i + 1
    · have h2 : ¬ (i : ℕ) = j + 1 := by omega
      simp only [if_neg h2, if_pos h1, Complex.star_def, Complex.conj_ofReal]
    · by_cases h3 : (i : ℕ) = j + 1
      · simp only [if_pos h3, if_neg h1, Complex.star_def, Complex.conj_ofReal]
      · simp only [if_neg h3, if_neg h1, star_zero]

/-- Matrix–vector product with the tridiagonal block (`BhN`). -/
lemma blockMatrix_mulVec (v b : ℝ → ℝ) (α : ℝ) (N : ℕ) (x : ℝ) (y : Fin N → ℂ) (i : Fin N) :
    (blockMatrix v b α N x *ᵥ y) i =
      ((v (x + ((i : ℕ) + 1) * α) : ℝ) : ℂ) * y i
      + (if h : (i : ℕ) + 1 < N then ((b (x + ((i : ℕ) + 1) * α) : ℝ) : ℂ) * y ⟨i + 1, h⟩
          else 0)
      + (if h : 0 < (i : ℕ) then
          ((b (x + (((i : ℕ) - 1 : ℕ) + 1) * α) : ℝ) : ℂ) * y ⟨i - 1, by omega⟩ else 0) := by
  have hsplit : ∀ j : Fin N, blockMatrix v b α N x i j * y j =
      (if i = j then ((v (x + ((i : ℕ) + 1) * α) : ℝ) : ℂ) * y j else 0)
      + (if (j : ℕ) = i + 1 then ((b (x + ((i : ℕ) + 1) * α) : ℝ) : ℂ) * y j else 0)
      + (if (i : ℕ) = j + 1 then ((b (x + ((j : ℕ) + 1) * α) : ℝ) : ℂ) * y j else 0) := by
    intro j
    simp only [blockMatrix, of_apply]
    by_cases hij : i = j
    · subst hij; simp
    · have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
      by_cases h1 : (j : ℕ) = i + 1
      · have h2 : ¬ (i : ℕ) = j + 1 := by omega
        simp only [if_neg hij, if_pos h1, if_neg h2, zero_add, add_zero]
      · by_cases h3 : (i : ℕ) = j + 1
        · simp only [if_neg hij, if_neg h1, if_pos h3, zero_add]
        · simp only [if_neg hij, if_neg h1, if_neg h3, zero_mul, add_zero]
  rw [mulVec, dotProduct]
  simp only [hsplit, Finset.sum_add_distrib]
  congr 1
  congr 1
  · rw [Finset.sum_ite_eq]; simp
  · split_ifs with h
    · rw [Finset.sum_eq_single (⟨(i : ℕ) + 1, h⟩ : Fin N)]
      · simp
      · intro j _ hj
        have : (j : ℕ) ≠ i + 1 := fun h' => hj (Fin.ext h')
        simp [this]
      · simp
    · refine Finset.sum_eq_zero fun j _ => ?_
      have : (j : ℕ) ≠ i + 1 := by omega
      simp [this]
  · split_ifs with h
    · rw [Finset.sum_eq_single (⟨(i : ℕ) - 1, by omega⟩ : Fin N)]
      · have : (i : ℕ) = (i : ℕ) - 1 + 1 := by omega
        simp only [Fin.val_mk]
        rw [if_pos this]
      · intro j _ hj
        have : (i : ℕ) ≠ j + 1 := fun h' => hj (Fin.ext (by simp; omega))
        simp [this]
      · simp
    · refine Finset.sum_eq_zero fun j _ => ?_
      have : (i : ℕ) ≠ j + 1 := by omega
      simp [this]

lemma bdry_mulVec_zero {N : ℕ} (hN : 0 < N) (y : Fin N → ℂ) :
    (bdry N *ᵥ y) 0 = y ⟨0, hN⟩ := by
  rw [mulVec, dotProduct, Finset.sum_eq_single (⟨0, hN⟩ : Fin N)]
  · simp [bdry]
  · intro j _ hj
    have : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
    simp [bdry, this]
  · simp

lemma bdry_mulVec_one {N : ℕ} (hN : 0 < N) (y : Fin N → ℂ) :
    (bdry N *ᵥ y) 1 = y ⟨N - 1, by omega⟩ := by
  rw [mulVec, dotProduct, Finset.sum_eq_single (⟨N - 1, by omega⟩ : Fin N)]
  · simp only [bdry, of_apply]
    rw [if_pos (Or.inr ⟨rfl, show N - 1 + 1 = N by omega⟩), one_mul]
  · intro j _ hj
    have : (j : ℕ) + 1 ≠ N := fun h => hj (Fin.ext (by simp; omega))
    simp [bdry, this]
  · simp

lemma conjTranspose_bdry_mulVec {N : ℕ} (z : Fin 2 → ℂ) (j : Fin N) :
    ((bdry N)ᴴ *ᵥ z) j =
      (if (j : ℕ) = 0 then z 0 else 0) + (if (j : ℕ) + 1 = N then z 1 else 0) := by
  rw [mulVec, dotProduct, Fin.sum_univ_two]
  simp [bdry, conjTranspose_apply]

/-- `Γ̂_N Γ̂_N^* = 1` on `ℂ^2` for `N ≥ 2`: `Γ̂_N` is a co-isometry, `Γ̂_N^*` an isometry. -/
lemma bdry_mul_conjTranspose {N : ℕ} (hN : 2 ≤ N) : bdry N * (bdry N)ᴴ = 1 := by
  refine Matrix.toLin'.injective (LinearMap.ext fun z => ?_)
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← mulVec_mulVec, one_mulVec]
  ext i
  fin_cases i
  · rw [show ((⟨0, by norm_num⟩ : Fin 2)) = 0 from rfl, bdry_mulVec_zero (by omega),
      conjTranspose_bdry_mulVec]
    simp only [if_true]
    rw [if_neg (by simp; omega), add_zero]
  · rw [show ((⟨1, by norm_num⟩ : Fin 2)) = 1 from rfl, bdry_mulVec_one (by omega),
      conjTranspose_bdry_mulVec]
    simp only
    rw [if_neg (by omega), if_pos (by omega), zero_add]

lemma conjTranspose_bdry_injective {N : ℕ} (hN : 2 ≤ N) :
    Function.Injective (bdry N)ᴴ.mulVec := by
  intro z z' h
  have := congrArg (fun y => bdry N *ᵥ y) h
  simpa only [mulVec_mulVec, bdry_mul_conjTranspose hN, one_mulVec] using this

lemma norm_bdry {N : ℕ} (hN : 2 ≤ N) : ‖bdry N‖ = 1 := by
  have h := l2_opNorm_conjTranspose_mul_self (bdry N)ᴴ
  rw [conjTranspose_conjTranspose, bdry_mul_conjTranspose hN, CStarRing.norm_one,
    l2_opNorm_conjTranspose] at h
  nlinarith [norm_nonneg (bdry N)]

lemma norm_conjTranspose_bdry {N : ℕ} (hN : 2 ≤ N) : ‖(bdry N)ᴴ‖ = 1 := by
  rw [l2_opNorm_conjTranspose, norm_bdry hN]

lemma bdryProj_mulVec {N : ℕ} (hN : 2 ≤ N) (y : Fin N → ℂ) (j : Fin N) :
    (bdryProj N *ᵥ y) j =
      (if (j : ℕ) = 0 then y ⟨0, by omega⟩ else 0) +
        (if (j : ℕ) + 1 = N then y ⟨N - 1, by omega⟩ else 0) := by
  rw [bdryProj, ← mulVec_mulVec, conjTranspose_bdry_mulVec, bdry_mulVec_zero (by omega),
    bdry_mulVec_one (by omega)]

lemma norm_bdryProj {N : ℕ} (hN : 2 ≤ N) : ‖bdryProj N‖ = 1 := by
  rw [bdryProj, l2_opNorm_conjTranspose_mul_self, norm_bdry hN, mul_one]

/-! ## 3. Hermitian matrices: norm and resolvent bounds from the eigenvalues -/

section Hermitian

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A Hermitian matrix whose eigenvalues all have modulus `≤ r` has `ℓ²` operator norm `≤ r`. -/
theorem _root_.Matrix.IsHermitian.norm_le_of_abs_eigenvalues_le {A : Matrix n n ℂ}
    (hA : A.IsHermitian) {r : ℝ} (hr : 0 ≤ r) (h : ∀ i, |hA.eigenvalues i| ≤ r) : ‖A‖ ≤ r := by
  rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply, ← Unitary.coe_star,
    CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul, l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg hr).2 fun i => ?_
  simpa [Complex.norm_real] using h i

/-- **Resolvent of a Hermitian matrix.**  If `A` is Hermitian and every eigenvalue is at distance
`≥ ε > 0` from `E`, then `A - E` is invertible and `‖(A - E)⁻¹‖ ≤ ε⁻¹`. -/
theorem _root_.Matrix.IsHermitian.resolvent_spec {A : Matrix n n ℂ} (hA : A.IsHermitian)
    {E ε : ℝ} (hε : 0 < ε) (h : ∀ i, ε ≤ |hA.eigenvalues i - E|) :
    IsUnit (A - (E : ℂ) • 1).det ∧ ‖(A - (E : ℂ) • 1)⁻¹‖ ≤ ε⁻¹ := by
  obtain ⟨V, hVdef⟩ : ∃ V, V = hA.eigenvectorUnitary := ⟨_, rfl⟩
  have hspec : A = (V : Matrix n n ℂ) * diagonal (RCLike.ofReal ∘ hA.eigenvalues) *
      star (V : Matrix n n ℂ) := by
    rw [hVdef]; exact hA.spectral_theorem
  set U : Matrix n n ℂ := (V : Matrix n n ℂ) with hU
  have hUU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hUU' : U * star U = 1 := Unitary.coe_mul_star_self _
  have hne : ∀ i, (hA.eigenvalues i : ℂ) - E ≠ 0 := by
    intro i h0
    have : hA.eigenvalues i - E = 0 := by exact_mod_cast h0
    have := h i
    rw [‹hA.eigenvalues i - E = 0›, abs_zero] at this
    linarith
  set d : n → ℂ := fun i => (hA.eigenvalues i : ℂ) - E
  set R : Matrix n n ℂ := U * diagonal (fun i => (d i)⁻¹) * star U
  have hAE : A - (E : ℂ) • 1 = U * diagonal d * star U := by
    conv_lhs => rw [hspec]
    have : diagonal d = diagonal (RCLike.ofReal ∘ hA.eigenvalues) - (E : ℂ) • 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij; simp [d]
      · simp [diagonal, hij]
    rw [this, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul,
      hUU']
  have hmul : (A - (E : ℂ) • 1) * R = 1 := by
    rw [hAE]
    simp only [R, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star U) U, hUU, Matrix.one_mul, ← Matrix.mul_assoc (diagonal d),
      diagonal_mul_diagonal]
    have : (fun i => d i * (d i)⁻¹) = fun _ => (1 : ℂ) := funext fun i => mul_inv_cancel₀ (hne i)
    rw [this, diagonal_one, Matrix.one_mul, hUU']
  refine ⟨isUnit_det_of_right_inverse hmul, ?_⟩
  rw [inv_eq_right_inv hmul]
  simp only [R, hU]
  rw [← Unitary.coe_star, CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul,
    l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (inv_nonneg.2 hε.le)).2 fun i => ?_
  rw [norm_inv]
  refine inv_anti₀ hε ?_
  have : d i = ((hA.eigenvalues i - E : ℝ) : ℂ) := by simp [d]
  rw [this, Complex.norm_real, Real.norm_eq_abs]
  exact h i

end Hermitian

/-! ## 4. The finite block step -/

/-- `E ∈ σ(M)` as soon as `E` is an eigenvalue of `M`. -/
lemma mem_spectrum_of_mulVec_eq_zero {n : Type*} [Fintype n] [DecidableEq n]
    {M : Matrix n n ℂ} {E : ℝ} {w : n → ℂ} (hw : w ≠ 0) (h : (M - (E : ℂ) • 1) *ᵥ w = 0) :
    E ∈ spectrum ℝ M := by
  rw [spectrum.mem_iff]
  intro hu
  have hu' : IsUnit (M - (E : ℂ) • 1) := by
    have : -(algebraMap ℝ (Matrix n n ℂ) E - M) = M - (E : ℂ) • 1 := by
      rw [Algebra.algebraMap_eq_smul_one, neg_sub]
      congr 1
    rw [← this]; exact hu.neg
  have hinj := mulVec_injective_iff_isUnit.2 hu'
  exact hw (hinj (h.trans (mulVec_zero _).symm))

/-- **The block step** (proof of `lemma-subm`, l. 1192–1204).  Let `B` be an `N × N` matrix,
`N ≥ 2`, with `E ∉ σ(B)`, and let `v` be a unit eigenvector of the boundary resolvent
`G(E) = Γ̂ (B-E)⁻¹ Γ̂^*` with real eigenvalue `μ ≠ 0` (eq. `mu-v`).  Then `V = -μ⁻¹ v v^*` is
Hermitian, `‖V‖ ≤ |μ|⁻¹`, and `E ∈ σ(B + Γ̂^* V Γ̂)`. -/
theorem block_step {N : ℕ} (hN : 2 ≤ N) (B : Matrix (Fin N) (Fin N) ℂ) {E : ℝ}
    (hE : IsUnit (B - (E : ℂ) • 1).det) {μ : ℝ} (hμ : μ ≠ 0) {v : Fin 2 → ℂ}
    (hv : star v ⬝ᵥ v = 1) (hGv : bdryResolvent B E *ᵥ v = (μ : ℂ) • v) :
    ∃ V : Matrix (Fin 2) (Fin 2) ℂ, V.IsHermitian ∧ ‖V‖ ≤ |μ|⁻¹ ∧
      E ∈ spectrum ℝ (B + (bdry N)ᴴ * V * bdry N) := by
  obtain ⟨hker, hherm, hinj⟩ :=
    SGD.MatrixLemmas.rank_one_kernel B (bdry N) (E : ℂ) hE v μ hμ hGv hv
  refine ⟨_, hherm, ?_, mem_spectrum_of_mulVec_eq_zero
    (hinj (conjTranspose_bdry_injective hN)) hker⟩
  -- `‖-μ⁻¹ v v^*‖ ≤ |μ|⁻¹`
  rw [norm_smul, norm_neg, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  have hvv : ‖vecMulVec v (star v)‖ ≤ 1 := by
    rw [vecMulVec_eq Unit, ← conjTranspose_replicateCol]
    set C := replicateCol Unit v
    have hC : Cᴴ * C = 1 := by
      ext i j
      simp only [C, mul_apply, conjTranspose_apply, replicateCol_apply, Matrix.one_apply]
      simp only [if_true]
      rw [← hv]
      simp [dotProduct, mul_comm]
    have h1 := l2_opNorm_conjTranspose_mul_self C
    rw [hC, CStarRing.norm_one] at h1
    have hCn : ‖C‖ = 1 := by nlinarith [norm_nonneg C]
    calc ‖C * Cᴴ‖ ≤ ‖C‖ * ‖Cᴴ‖ := l2_opNorm_mul _ _
      _ = 1 := by rw [l2_opNorm_conjTranspose, hCn, one_mul]
  calc |μ|⁻¹ * ‖vecMulVec v (star v)‖ ≤ |μ|⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left hvv (inv_nonneg.2 (abs_nonneg _))
    _ = |μ|⁻¹ := mul_one _

/-- The boundary resolvent of a Hermitian block is Hermitian. -/
lemma bdryResolvent_isHermitian {N : ℕ} {B : Matrix (Fin N) (Fin N) ℂ} (hB : B.IsHermitian)
    (E : ℝ) : (bdryResolvent B E).IsHermitian := by
  have hBE : (B - (E : ℂ) • 1).IsHermitian := by
    refine hB.sub ?_
    simp [IsHermitian, conjTranspose_smul, Complex.star_def]
  unfold bdryResolvent
  rw [IsHermitian, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    hBE.inv.eq, Matrix.mul_assoc]

/-- Unit eigenvectors of a Hermitian matrix (columns of the eigenvector unitary). -/
lemma hermitian_eigenpair {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ}
    (hA : A.IsHermitian) (i : n) :
    star (⇑(hA.eigenvectorBasis i)) ⬝ᵥ ⇑(hA.eigenvectorBasis i) = 1 ∧
      A *ᵥ ⇑(hA.eigenvectorBasis i) = ((hA.eigenvalues i : ℝ) : ℂ) • ⇑(hA.eigenvectorBasis i) := by
  refine ⟨?_, ?_⟩
  · have h := congrArg (fun M : Matrix n n ℂ => M i i)
      (Unitary.coe_star_mul_self hA.eigenvectorUnitary)
    simp only [mul_apply, star_apply, Matrix.one_apply_eq] at h
    rw [← h, dotProduct]
    simp [Matrix.IsHermitian.eigenvectorUnitary_apply]
  · rw [hA.mulVec_eigenvectorBasis, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    rfl

/-- **Bound on the boundary resolvent of a block** (contrapositive of l. 1188–1204).  Let `B` be
Hermitian, `N ≥ 2`, `E ∉ σ(B)` and `τ > 0`.  If `E ∉ σ(B + Γ̂^* V Γ̂)` for every Hermitian `V`
with `‖V‖ ≤ 2τ`, then `‖G(E)‖ ≤ (2τ)⁻¹`. -/
theorem norm_bdryResolvent_le {N : ℕ} (hN : 2 ≤ N) {B : Matrix (Fin N) (Fin N) ℂ}
    (hB : B.IsHermitian) {E τ : ℝ} (hτ : 0 < τ) (hE : IsUnit (B - (E : ℂ) • 1).det)
    (hV : ∀ V : Matrix (Fin 2) (Fin 2) ℂ, V.IsHermitian → ‖V‖ ≤ 2 * τ →
      E ∉ spectrum ℝ (B + (bdry N)ᴴ * V * bdry N)) :
    ‖bdryResolvent B E‖ ≤ (2 * τ)⁻¹ := by
  have hG := bdryResolvent_isHermitian hB E
  refine hG.norm_le_of_abs_eigenvalues_le (inv_nonneg.2 (by positivity)) fun i => ?_
  obtain ⟨hv, hGv⟩ := hermitian_eigenpair hG i
  set μ := hG.eigenvalues i
  by_cases hμ : μ = 0
  · rw [hμ, abs_zero]; positivity
  by_contra hlt
  push Not at hlt
  obtain ⟨V, hVh, hVn, hspec⟩ := block_step hN B hE hμ hv hGv
  have hμpos : 0 < |μ| := abs_pos.2 hμ
  refine hV V hVh (hVn.trans ?_) hspec
  rw [inv_le_comm₀ hμpos (by positivity)]
  exact hlt.le

/-- **The block step, paper form** (l. 1188–1204): if `‖G_k(E)‖ > (2τ)⁻¹` then there is a
Hermitian `V` with `‖V‖ < 2τ` and `E ∈ σ(B_k + Γ_k^* V Γ_k)`. -/
theorem block_step_of_norm_gt {N : ℕ} (hN : 2 ≤ N) {B : Matrix (Fin N) (Fin N) ℂ}
    (hB : B.IsHermitian) {E τ : ℝ} (hτ : 0 < τ) (hE : IsUnit (B - (E : ℂ) • 1).det)
    (hG : (2 * τ)⁻¹ < ‖bdryResolvent B E‖) :
    ∃ V : Matrix (Fin 2) (Fin 2) ℂ, V.IsHermitian ∧ ‖V‖ < 2 * τ ∧
      E ∈ spectrum ℝ (B + (bdry N)ᴴ * V * bdry N) := by
  have hGh := bdryResolvent_isHermitian hB E
  have : ∃ i, (2 * τ)⁻¹ < |hGh.eigenvalues i| := by
    by_contra hcon
    push Not at hcon
    exact absurd (hGh.norm_le_of_abs_eigenvalues_le (inv_nonneg.2 (by positivity)) hcon)
      (not_le.2 hG)
  obtain ⟨i, hi⟩ := this
  obtain ⟨hv, hGv⟩ := hermitian_eigenpair hGh i
  have hμ : hGh.eigenvalues i ≠ 0 := by
    intro h0; rw [h0, abs_zero] at hi; exact absurd hi (not_lt.2 (by positivity))
  obtain ⟨V, hVh, hVn, hspec⟩ := block_step hN B hE hμ hv hGv
  refine ⟨V, hVh, hVn.trans_lt ?_, hspec⟩
  rw [inv_lt_comm₀ (abs_pos.2 hμ) (by positivity)]
  exact hi

end CAH
