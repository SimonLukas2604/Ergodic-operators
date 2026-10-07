/-
Copyright (c) 2026. Formalization of
  S. Becker, S. Jitomirskaya, I. Krasovsky, "Critical almost Mathieu operator: hidden
  singularity, gap continuity, and the Hausdorff dimension of the spectrum"
  (arXiv:1909.04429v2).

# Variation of the block eigenvalues and the spectral cover of the blocks
  (paper §5, `.tex` l. 1583–1772)

* **Proposition `prop-phase-variation`** (l. 1583–1669, eq. `phase-variation-main`):
  for `N ∈ {q_n, q_{n-1}}`, `N ≥ 3`, `J_n = [-|δ_{n-1}|, |δ_{n-1}|]` and a real parameter `c`
  with `|c| ≤ C₀ |J_n|`, the ordered eigenvalues of `H_N(x) = B_N(x) + c P_N` satisfy
  `∑_j Var_{J_n} λ_j ≤ C(C₀) |J_n|` with the explicit constant
  `C(C₀) = phaseConst C₀ = 6π + 14π² + 8πC₀` (`phase_variation`), and hence
  `≤ 2 C(C₀) / q_n` (`phase_variation_le`).  The paper's paths `H_N^±` are the cases
  `c = ±C₀|J_n|`.
* **Proposition `prop-cover1`** (l. 1672–1772, eqs. `subBN`, `lengthBN`): there are `N`
  intervals `[lo_j, hi_j]`, independent of `x ∈ J_n` and of the Hermitian `2 × 2` matrix `V`
  with `‖V‖ ≤ C₀ |J_n|` (expressed as: all eigenvalues of `V` lie in `[-C₀|J_n|, C₀|J_n|]`),
  covering `σ(B_N(x) + Γ̂_N^* V Γ̂_N)`, of total length `≤ coverConst C₀ / q_n`,
  `coverConst C₀ = 2(4C₀ + 2·phaseConst C₀)` (`block_cover`, for `n ≥ 4` as in the paper;
  `block_cover_of_three_le` for any `n ≥ 1` provided `N ≥ 3`); in the shape
  `CAH.BlockCoverProp α n (4π) C'` of `SpectralCover.lean`: `blockCoverProp_holds`.

## Proof of `prop-phase-variation` (as in the paper)

Lemma `lemma-flow` (`CAH.Flow.flow_bound`) is applied with `H = H_N`, `K = K_N`,
`𝓔 = 𝓔_N = 𝓔_even + 𝓔_edge - c [K_N, P_N]` (Lemma `lemma-commut2`,
`CAH.LaxPair.lemma_commut2`), all mapped entrywise from `ℝ` to `ℂ` (`toC`).  Each of the three
pieces is real symmetric and vanishes off the rows/columns `0, N-1`, hence has rank `≤ 4`
(`CAH.LaxPair.rank_le_of_interior_eq_zero`) and `‖·‖_{S_1} ≤ 2 ‖·‖_{S_2}`.  The
Hilbert–Schmidt bounds (Enorms) are `CAH.LaxPair.Eeven_hs`, `Eedge_hs`, `commKP_hs`; the
arithmetic input `∑_{r=1}^L c_r² ≤ π² q_n²` (`sum_cr_sq_le_q`) comes from
`CAH.sum_inv_sin_sq_le` (`∑ 1/sin²(πkα) ≤ 4 q_n²` for `L < q_n`).  On `J_n`:
`|2 sin πx| ≤ 2π|δ_{n-1}|` and, writing `Nα = p_m + δ_m` (`N = q_m`, `m ∈ {n, n-1}`,
`|δ_m| ≤ |δ_{n-1}|`), `|2 sin π(x+Nα)| = |2 sin π(x+δ_m)| ≤ 4π|δ_{n-1}|`; finally
`|δ_{n-1}| < 1/q_n` (`CAH.abs_delta_bounds`).  This gives, pointwise on `J_n`,
`‖𝓔_N(x)‖_{S_1} ≤ 2(3π + 7π² + 4πC₀) = phaseConst C₀` (`traceNorm_Epm_le_const`).

## Conventions and deviations

* We use the trace-norm triangle inequality for the three pieces (instead of the paper's
  `‖𝓔‖_{S_1} ≤ √4 ‖𝓔‖_{S_2}` followed by the `S_2` triangle inequality); same estimate.
* The boundary projection `P_N` of `LaxPair` (real diagonal) and `Flow.bdryProj N = Γ̂^*Γ̂`
  agree for `N ≥ 2` (`PN_eq_bdryProj`); the boundary map is `CAH.Flow.bdry`.
* `n ≥ 4` (as in the paper) guarantees `q_{n-1} ≥ 3` (`three_le_qN`: `q_3 ≥ q_1 + q_2 ≥ 3`),
  which is what Lemma `lemma-commut` needs; the general statements only assume `n ≥ 1`,
  `N ≥ 3`.
* Variation is Mathlib's `eVariationOn` on `Set.Icc (-|δ_{n-1}|) |δ_{n-1}|` (an `ℝ≥0∞`).

No `sorry`s, no axioms.
-/
import CriticalAMOHausdorff.LaxPair
import CriticalAMOHausdorff.EigenvalueFlow
import CriticalAMOHausdorff.ContinuedFractions
import CriticalAMOHausdorff.SpectralCover

noncomputable section

open Matrix Real

namespace CAH
namespace BlockCover

variable {N : ℕ}

/-! ## Real matrices as complex matrices -/

/-- Entrywise embedding `M_N(ℝ) → M_N(ℂ)` (a ring homomorphism). -/
def toC : Matrix (Fin N) (Fin N) ℝ →+* Matrix (Fin N) (Fin N) ℂ := Complex.ofRealHom.mapMatrix

@[simp] lemma toC_apply (M : Matrix (Fin N) (Fin N) ℝ) (i k : Fin N) :
    toC M i k = (M i k : ℂ) := rfl

lemma toC_smul (c : ℝ) (M : Matrix (Fin N) (Fin N) ℝ) : toC (c • M) = (c : ℂ) • toC M := by
  ext i k; simp

lemma BNc_eq (α x : ℝ) : LaxPair.BNc α N x = toC (LaxPair.BN α N x) := rfl

lemma KNc_eq (α : ℝ) : LaxPair.KNc α N = toC (LaxPair.KN α N) := rfl

lemma isHermitian_toC (M : Matrix (Fin N) (Fin N) ℝ) (h : ∀ i k, M i k = M k i) :
    (toC M).IsHermitian :=
  IsHermitian.ext fun i k => by
    rw [toC_apply, toC_apply, h k i, Complex.star_def, Complex.conj_ofReal]

lemma hsNorm_toC (M : Matrix (Fin N) (Fin N) ℝ) :
    Flow.hsNorm (toC M) = Real.sqrt (LaxPair.hs2 M) := by
  unfold Flow.hsNorm LaxPair.hs2
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  rw [toC_apply, Complex.norm_real, Real.norm_eq_abs, sq_abs]

lemma hs2_smul (c : ℝ) (M : Matrix (Fin N) (Fin N) ℝ) :
    LaxPair.hs2 (c • M) = c ^ 2 * LaxPair.hs2 M := by
  simp only [LaxPair.hs2, Matrix.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

/-- The boundary projections agree: `P_N` (real diagonal, `LaxPair`) equals
`Γ̂_N^* Γ̂_N` (`Flow.bdryProj`) for `N ≥ 2`. -/
lemma PN_eq_bdryProj (hN : 2 ≤ N) : toC (LaxPair.PN N) = Flow.bdryProj N := by
  ext i k
  have hi := i.isLt
  have hk := k.isLt
  simp only [toC_apply, LaxPair.PN, diagonal_apply, Flow.bdryProj, Flow.bdry, mul_apply,
    conjTranspose_apply, of_apply, Fin.sum_univ_two, Fin.val_zero, Fin.val_one, Fin.ext_iff,
    true_and, zero_ne_one, one_ne_zero, false_and, or_false, false_or]
  split_ifs <;> first | (exfalso; omega) | simp

/-! ## Symmetry and support of the pieces -/

lemma BN_symm (α x : ℝ) (j k : Fin N) : LaxPair.BN α N x j k = LaxPair.BN α N x k j := by
  unfold LaxPair.BN
  split_ifs <;> first | rfl | omega

lemma KN_antisymm (α : ℝ) (j k : Fin N) : LaxPair.KN α N j k = -LaxPair.KN α N k j := by
  unfold LaxPair.KN
  simp only [Nat.even_iff]
  split_ifs <;> first | ring1 | omega

lemma PN_symm (i k : Fin N) : LaxPair.PN N i k = LaxPair.PN N k i := by
  by_cases h : i = k
  · subst h; rfl
  · simp [LaxPair.PN, h, Ne.symm h]

lemma HN_symm (α c x : ℝ) (i k : Fin N) :
    LaxPair.HN α N c x i k = LaxPair.HN α N c x k i := by
  simp only [LaxPair.HN, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [BN_symm α x i k, PN_symm i k]

/-- The commutator `[K_N, P_N]`. -/
def commKP (α : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  LaxPair.KN α N * LaxPair.PN N - LaxPair.PN N * LaxPair.KN α N

lemma commKP_symm (α : ℝ) (i k : Fin N) : commKP α N i k = commKP α N k i := by
  rw [commKP, LaxPair.commKP_apply, LaxPair.commKP_apply, KN_antisymm α i k]
  ring

lemma Epm_eq (α c x : ℝ) : LaxPair.Epm α N c x =
    LaxPair.Eeven α N x + LaxPair.Eedge α N x + (-c) • commKP α N := by
  simp only [LaxPair.Epm, commKP, sub_eq_add_neg, neg_smul]

lemma Eeven_int (α x : ℝ) (i k : Fin N) (hi0 : (i : ℕ) ≠ 0) (hi1 : (i : ℕ) ≠ N - 1) :
    LaxPair.Eeven α N x i k = 0 := by
  simp [LaxPair.Eeven, hi0, hi1]

lemma Eedge_int (α x : ℝ) (i k : Fin N) (hi0 : (i : ℕ) ≠ 0) (hi1 : (i : ℕ) ≠ N - 1)
    (hk0 : (k : ℕ) ≠ 0) (hk1 : (k : ℕ) ≠ N - 1) : LaxPair.Eedge α N x i k = 0 := by
  simp [LaxPair.Eedge, LaxPair.EedgeR0, LaxPair.EedgeC0, LaxPair.EedgeCN, LaxPair.EedgeRN,
    hi0, hi1, hk0, hk1]

lemma commKP_int (α : ℝ) (i k : Fin N) (hi0 : (i : ℕ) ≠ 0) (hi1 : (i : ℕ) ≠ N - 1)
    (hk0 : (k : ℕ) ≠ 0) (hk1 : (k : ℕ) ≠ N - 1) : commKP α N i k = 0 := by
  rw [commKP, LaxPair.commKP_apply]
  simp [hi0, hi1, hk0, hk1]

/-- A real symmetric matrix vanishing off the rows and columns `0, N-1` has rank `≤ 4`, hence
`‖M‖_{S_1} ≤ 2 ‖M‖_{S_2}`. -/
lemma traceNorm_piece_le (hN : 1 ≤ N) (M : Matrix (Fin N) (Fin N) ℝ)
    (hsym : ∀ i k, M i k = M k i)
    (hint : ∀ i k : Fin N, (i : ℕ) ≠ 0 → (i : ℕ) ≠ N - 1 → (k : ℕ) ≠ 0 → (k : ℕ) ≠ N - 1 →
      M i k = 0) :
    Flow.traceNorm (toC M) ≤ 2 * Real.sqrt (LaxPair.hs2 M) := by
  have hH := isHermitian_toC M hsym
  let S : Finset (Fin N) := {⟨0, by omega⟩, ⟨N - 1, by omega⟩}
  have hS : S.card ≤ 2 := Finset.card_le_two
  have hr : (toC M).rank ≤ 4 := by
    refine (LaxPair.rank_le_of_interior_eq_zero _ S ?_).trans (by omega)
    intro i k hi hk
    have hi0 : (i : ℕ) ≠ 0 := fun h => hi (by simp [S, Fin.ext_iff, h])
    have hi1 : (i : ℕ) ≠ N - 1 := fun h => hi (by simp [S, Fin.ext_iff, h])
    have hk0 : (k : ℕ) ≠ 0 := fun h => hk (by simp [S, Fin.ext_iff, h])
    have hk1 : (k : ℕ) ≠ N - 1 := fun h => hk (by simp [S, Fin.ext_iff, h])
    simp [hint i k hi0 hi1 hk0 hk1]
  have h := Flow.traceNorm_le_sqrt_mul_hsNorm hH hr
  rw [hsNorm_toC, show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h
  exact h

/-- `‖𝓔_N(x)‖_{S_1} ≤ 2‖𝓔_even‖_{S_2} + 2‖𝓔_edge‖_{S_2} + 2‖c[K_N,P_N]‖_{S_2}`. -/
lemma traceNorm_Epm_le (α : ℝ) (hN : 3 ≤ N) (c x : ℝ) :
    Flow.traceNorm (toC (LaxPair.Epm α N c x)) ≤
      2 * Real.sqrt (LaxPair.hs2 (LaxPair.Eeven α N x)) +
      2 * Real.sqrt (LaxPair.hs2 (LaxPair.Eedge α N x)) +
      2 * Real.sqrt (LaxPair.hs2 ((-c) • commKP α N)) := by
  have s1 := LaxPair.Eeven_symm α N x
  have s2 := LaxPair.Eedge_symm α N x
  have s3 : ∀ i k, ((-c) • commKP α N) i k = ((-c) • commKP α N) k i := fun i k => by
    rw [Matrix.smul_apply, Matrix.smul_apply, commKP_symm α i k]
  have h1 := isHermitian_toC _ s1
  have h2 := isHermitian_toC _ s2
  have h3 := isHermitian_toC _ s3
  have p1 := traceNorm_piece_le (by omega) _ s1 fun i k hi0 hi1 _ _ => Eeven_int α x i k hi0 hi1
  have p2 := traceNorm_piece_le (by omega) _ s2 fun i k hi0 hi1 hk0 hk1 =>
    Eedge_int α x i k hi0 hi1 hk0 hk1
  have p3 := traceNorm_piece_le (by omega) _ s3 fun i k hi0 hi1 hk0 hk1 => by
    simp [commKP_int α i k hi0 hi1 hk0 hk1]
  rw [Epm_eq, map_add, map_add]
  have t1 := Flow.traceNorm_add_le (h1.add h2) h3
  have t2 := Flow.traceNorm_add_le h1 h2
  linarith

/-! ## The arithmetic estimates on `J_n` -/

/-- `∑_{r=1}^L c_r² ≤ π² q_n²` for `L = ⌊(N-1)/2⌋`, `N ≤ q_n` (l. 1612–1636). -/
lemma sum_cr_sq_le_q {α : ℝ} (hα : Irrational α) {n : ℕ} (hn : 1 ≤ n) (hNq : N ≤ qN α n) :
    ∑ r ∈ Finset.Icc 1 (LaxPair.LN N), LaxPair.cr α r ^ 2 ≤ π ^ 2 * q α n ^ 2 := by
  have hL : LaxPair.LN N < qN α n := by
    unfold LaxPair.LN; have := one_le_qN hα n; omega
  have h := CAH.sum_inv_sin_sq_le hα hn hL
  simp only [LaxPair.cr_sq, ← Finset.mul_sum]
  have e : ∑ r ∈ Finset.Icc 1 (LaxPair.LN N), 1 / sin (π * α * r) ^ 2 =
      ∑ k ∈ Finset.Icc 1 (LaxPair.LN N), 1 / Real.sin (π * k * α) ^ 2 :=
    Finset.sum_congr rfl fun r _ => by rw [mul_right_comm]
  rw [e]
  calc π ^ 2 / 4 * ∑ k ∈ Finset.Icc 1 (LaxPair.LN N), 1 / Real.sin (π * k * α) ^ 2
      ≤ π ^ 2 / 4 * (4 * q α n ^ 2) := by gcongr
    _ = π ^ 2 * q α n ^ 2 := by ring

lemma sq_two_sin_le {x d : ℝ} (hx : |x| ≤ d) : (2 * sin (π * x)) ^ 2 ≤ 4 * π ^ 2 * d ^ 2 := by
  have h1 : |sin (π * x)| ≤ π * d :=
    (Real.abs_sin_le_abs (x := π * x)).trans (by
      rw [abs_mul, abs_of_pos pi_pos]; exact mul_le_mul_of_nonneg_left hx pi_pos.le)
  calc (2 * sin (π * x)) ^ 2 = 4 * |sin (π * x)| ^ 2 := by rw [mul_pow, sq_abs]; norm_num
    _ ≤ 4 * (π * d) ^ 2 := by gcongr
    _ = 4 * π ^ 2 * d ^ 2 := by ring

lemma abs_sin_shift {α : ℝ} (hα : Irrational α) (m : ℕ) (x : ℝ) :
    |sin (π * (x + (qN α m : ℝ) * α))| = |sin (π * (x + delta α m))| := by
  have : π * (x + (qN α m : ℝ) * α) = π * (x + delta α m) + ((pZ α m : ℤ) : ℝ) * π := by
    rw [delta_eq_cast hα]; ring
  rw [this, Real.sin_add_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul]

/-- `|δ_{n-1}| < 1/q_n`, i.e. `|δ_{n-1}| q_n < 1`. -/
lemma abs_delta_mul_q_lt {α : ℝ} (hα : Irrational α) {n : ℕ} (hn : 1 ≤ n) :
    |delta α (n - 1)| * q α n < 1 := by
  have h := (abs_delta_bounds hα (n - 1)).2
  rw [Nat.sub_add_cancel hn, lt_div_iff₀ (q_pos hα n)] at h
  exact h

lemma abs_delta_le {α : ℝ} (hα : Irrational α) {n m : ℕ} (hn : 1 ≤ n) (hm : m = n ∨ m = n - 1) :
    |delta α m| ≤ |delta α (n - 1)| := by
  rcases hm with rfl | rfl
  · have := abs_delta_succ_lt hα (m - 1)
    rw [Nat.sub_add_cancel hn] at this
    exact this.le
  · exact le_rfl

/-- `|2 sin π(x+Nα)| ≤ 4π|δ_{n-1}|` on `J_n`, for `N ∈ {q_n, q_{n-1}}`. -/
lemma sq_two_sin_shift_le {α : ℝ} (hα : Irrational α) {n : ℕ} (hn : 1 ≤ n)
    (hN : N = qN α n ∨ N = qN α (n - 1)) {x : ℝ} (hx : |x| ≤ |delta α (n - 1)|) :
    (2 * sin (π * (x + N * α))) ^ 2 ≤ 16 * π ^ 2 * |delta α (n - 1)| ^ 2 := by
  obtain ⟨m, hm, rfl⟩ : ∃ m, (m = n ∨ m = n - 1) ∧ N = qN α m := by
    rcases hN with h | h
    · exact ⟨n, Or.inl rfl, h⟩
    · exact ⟨n - 1, Or.inr rfl, h⟩
  have hdm := abs_delta_le hα hn hm
  have h1 : |sin (π * (x + (qN α m : ℝ) * α))| ≤ π * (2 * |delta α (n - 1)|) := by
    rw [abs_sin_shift hα m x]
    refine (Real.abs_sin_le_abs (x := π * (x + delta α m))).trans ?_
    calc |π * (x + delta α m)| = π * |x + delta α m| := by rw [abs_mul, abs_of_pos pi_pos]
      _ ≤ π * (|x| + |delta α m|) := by gcongr; exact abs_add_le _ _
      _ ≤ π * (2 * |delta α (n - 1)|) := by gcongr; linarith
  calc (2 * sin (π * (x + (qN α m : ℝ) * α))) ^ 2
      = 4 * |sin (π * (x + (qN α m : ℝ) * α))| ^ 2 := by rw [mul_pow, sq_abs]; norm_num
    _ ≤ 4 * (π * (2 * |delta α (n - 1)|)) ^ 2 := by gcongr
    _ = 16 * π ^ 2 * |delta α (n - 1)| ^ 2 := by ring

lemma qN_le_of_mem {α : ℝ} (hα : Irrational α) {n : ℕ} (hn : 1 ≤ n)
    (hN : N = qN α n ∨ N = qN α (n - 1)) : N ≤ qN α n := by
  rcases hN with rfl | rfl
  · exact le_rfl
  · have := qN_le_succ hα (n - 1); rwa [Nat.sub_add_cancel hn] at this

/-- The constant of Proposition `prop-phase-variation`: `C(C₀) = 6π + 14π² + 8πC₀`. -/
def phaseConst (C₀ : ℝ) : ℝ := 6 * π + 14 * π ^ 2 + 8 * π * C₀

lemma phaseConst_nonneg {C₀ : ℝ} (hC₀ : 0 ≤ C₀) : 0 ≤ phaseConst C₀ := by
  unfold phaseConst; positivity

/-- Pointwise bound (Enorms2) and the `S_1`-estimate: for `x ∈ J_n` and `|c| ≤ C₀|J_n|`,
`‖𝓔_N(x)‖_{S_1} ≤ phaseConst C₀`. -/
theorem traceNorm_Epm_le_const {α : ℝ} (hα : Irrational α) {n : ℕ} (hn : 1 ≤ n) (hN3 : 3 ≤ N)
    (hN : N = qN α n ∨ N = qN α (n - 1)) {C₀ c : ℝ} (hC₀ : 0 ≤ C₀)
    (hc : |c| ≤ C₀ * (2 * |delta α (n - 1)|)) {x : ℝ} (hx : |x| ≤ |delta α (n - 1)|) :
    Flow.traceNorm (toC (LaxPair.Epm α N c x)) ≤ phaseConst C₀ := by
  have hd0 : 0 ≤ |delta α (n - 1)| := abs_nonneg _
  have hQ0 : 0 < q α n := q_pos hα n
  have hdQ : |delta α (n - 1)| * q α n < 1 := abs_delta_mul_q_lt hα hn
  have hdQ0 : 0 ≤ |delta α (n - 1)| * q α n := by positivity
  set d := |delta α (n - 1)| with hd
  set Q := q α n with hQ
  have hS := sum_cr_sq_le_q hα hn (qN_le_of_mem hα hn hN)
  set S := ∑ r ∈ Finset.Icc 1 (LaxPair.LN N), LaxPair.cr α r ^ 2 with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hpi := pi_pos
  -- piece 1: `‖𝓔_even‖_{S_2} ≤ 3π`
  have b1 : Real.sqrt (LaxPair.hs2 (LaxPair.Eeven α N x)) ≤ 3 * π := by
    refine (Real.sqrt_le_sqrt ((LaxPair.Eeven_hs α hN3 x).trans ?_)).trans_eq
      (Real.sqrt_sq (by positivity))
    nlinarith [sq_nonneg π]
  -- piece 2: `‖𝓔_edge‖_{S_2} ≤ 7π²`
  have hsx := sq_two_sin_le hx
  have hsN := sq_two_sin_shift_le hα hn hN hx
  have b2 : Real.sqrt (LaxPair.hs2 (LaxPair.Eedge α N x)) ≤ 7 * π ^ 2 := by
    refine (Real.sqrt_le_sqrt ((LaxPair.Eedge_hs α x).trans ?_)).trans_eq
      (Real.sqrt_sq (by positivity))
    have hA0 : 0 ≤ (2 * sin (π * x)) ^ 2 + (2 * sin (π * (x + N * α))) ^ 2 := by positivity
    have hA : (2 * sin (π * x)) ^ 2 + (2 * sin (π * (x + N * α))) ^ 2 ≤ 20 * π ^ 2 * d ^ 2 := by
      linarith
    calc 2 * ((2 * sin (π * x)) ^ 2 + (2 * sin (π * (x + N * α))) ^ 2) * S
        ≤ 2 * (20 * π ^ 2 * d ^ 2) * (π ^ 2 * Q ^ 2) := by gcongr
      _ = 40 * π ^ 4 * (d * Q) ^ 2 := by ring
      _ ≤ 40 * π ^ 4 * 1 := by
          gcongr
          nlinarith
      _ ≤ (7 * π ^ 2) ^ 2 := by nlinarith [pow_pos hpi 4]
  -- piece 3: `‖c [K_N, P_N]‖_{S_2} ≤ 4πC₀`
  have b3 : Real.sqrt (LaxPair.hs2 ((-c) • commKP α N)) ≤ 4 * π * C₀ := by
    rw [hs2_smul]
    have hK := LaxPair.commKP_hs α hN3
    have hc0 : 0 ≤ |c| := abs_nonneg c
    refine (Real.sqrt_le_sqrt (?_ : (-c) ^ 2 * LaxPair.hs2 (commKP α N) ≤ (4 * π * C₀) ^ 2))
      |>.trans_eq (Real.sqrt_sq (by positivity))
    have e1 : (-c) ^ 2 = |c| ^ 2 := by rw [neg_sq, sq_abs]
    rw [e1]
    have hKS : LaxPair.hs2 (commKP α N) ≤ 4 * (π ^ 2 * Q ^ 2) := by
      have : LaxPair.hs2 (commKP α N) ≤ 4 * S := hK
      linarith
    have hK0 : 0 ≤ LaxPair.hs2 (commKP α N) :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc |c| ^ 2 * LaxPair.hs2 (commKP α N) ≤ (C₀ * (2 * d)) ^ 2 * (4 * (π ^ 2 * Q ^ 2)) := by
          gcongr
      _ = (4 * π * C₀) ^ 2 * (d * Q) ^ 2 := by ring
      _ ≤ (4 * π * C₀) ^ 2 * 1 := by gcongr; nlinarith
      _ = (4 * π * C₀) ^ 2 := mul_one _
  have := traceNorm_Epm_le α hN3 c x
  unfold phaseConst
  linarith

/-! ## Continuity and the flow equation -/

lemma continuous_Epm (α : ℝ) (N : ℕ) (c : ℝ) : Continuous fun x => LaxPair.Epm α N c x := by
  refine continuous_pi fun i => continuous_pi fun k => ?_
  simp only [LaxPair.Epm, LaxPair.Eeven, LaxPair.Eedge, LaxPair.EedgeR0, LaxPair.EedgeC0,
    LaxPair.EedgeCN, LaxPair.EedgeRN, Matrix.add_apply, Matrix.sub_apply]
  repeat (first | fun_prop | apply Continuous.if_const | apply Continuous.add |
    apply Continuous.sub)

lemma continuous_toC_Epm (α : ℝ) (N : ℕ) (c : ℝ) :
    Continuous fun x => toC (LaxPair.Epm α N c x) := by
  refine continuous_pi fun i => continuous_pi fun k => ?_
  exact Complex.continuous_ofReal.comp
    ((continuous_apply k).comp ((continuous_apply i).comp (continuous_Epm α N c)))

lemma KNc_skew (α : ℝ) : (LaxPair.KNc α N)ᴴ = -LaxPair.KNc α N := by
  ext i k
  rw [conjTranspose_apply, neg_apply, KNc_eq, toC_apply, toC_apply, Complex.star_def,
    Complex.conj_ofReal, KN_antisymm α k i, Complex.ofReal_neg]

lemma HN_eq (hN : 2 ≤ N) (α c y : ℝ) :
    LaxPair.BNc α N y + (c : ℂ) • Flow.bdryProj N = toC (LaxPair.HN α N c y) := by
  rw [LaxPair.HN, map_add, toC_smul, PN_eq_bdryProj hN]; rfl

/-- The flow equation `H_N' = [K_N, H_N] + 𝓔_N` (Lemma `lemma-commut2`) for the complex
matrices. -/
lemma hasDerivWithinAt_toC_HN {α : ℝ} (hα : Irrational α) (hN3 : 3 ≤ N) (c x : ℝ)
    (s : Set ℝ) :
    HasDerivWithinAt (fun y => toC (LaxPair.HN α N c y))
      (LaxPair.KNc α N * toC (LaxPair.HN α N c x) - toC (LaxPair.HN α N c x) * LaxPair.KNc α N +
        toC (LaxPair.Epm α N c x)) s x := by
  have hD : HasDerivAt (F := Fin N → Fin N → ℂ) (fun y => toC (LaxPair.HN α N c y))
      (toC (LaxPair.KN α N * LaxPair.HN α N c x - LaxPair.HN α N c x * LaxPair.KN α N +
        LaxPair.Epm α N c x)) x := by
    refine (hasDerivAt_pi (φ := fun y => toC (LaxPair.HN α N c y))).2 fun i => ?_
    refine (hasDerivAt_pi (φ := fun y => toC (LaxPair.HN α N c y) i)).2 fun k => ?_
    exact (LaxPair.lemma_commut2 hN3 (LaxPair.sin_hyp_of_irrational hα N) c x i k).ofReal_comp
  have h2 := hD.hasDerivWithinAt (s := s)
  rw [map_add, map_sub, map_mul, map_mul] at h2
  exact h2

/-! ## Proposition `prop-phase-variation` -/

/-- **Proposition `prop-phase-variation`** (eq. `phase-variation-main`, l. 1583–1669): for
irrational `α`, `n ≥ 1`, `N ∈ {q_n, q_{n-1}}` with `N ≥ 3`, `J_n = [-|δ_{n-1}|, |δ_{n-1}|]`
and real `c` with `|c| ≤ C₀|J_n|` (the paper's `H_N^±` are `c = ±C₀|J_n|`), the ordered
eigenvalues `λ_j` of `H_N(x) = B_N(x) + c P_N` satisfy
`∑_j Var_{J_n} λ_j ≤ C(C₀) |J_n|`, `C(C₀) = 6π + 14π² + 8πC₀`. -/
theorem phase_variation {α : ℝ} (hα : Irrational α) {n : ℕ} (hn : 1 ≤ n) (hN3 : 3 ≤ N)
    (hN : N = qN α n ∨ N = qN α (n - 1)) {C₀ c : ℝ} (hC₀ : 0 ≤ C₀)
    (hc : |c| ≤ C₀ * (2 * |delta α (n - 1)|)) :
    ∑ j, eVariationOn (fun x => Flow.eig (LaxPair.BNc α N x + (c : ℂ) • Flow.bdryProj N) j)
        (Set.Icc (-|delta α (n - 1)|) (|delta α (n - 1)|)) ≤
      ENNReal.ofReal (phaseConst C₀ * (2 * |delta α (n - 1)|)) := by
  set d := |delta α (n - 1)| with hd
  have hd0 : 0 ≤ d := abs_nonneg _
  have hab : -d ≤ d := by linarith
  simp only [HN_eq (by omega : 2 ≤ N)]
  have key := Flow.flow_bound hab (H := fun y => toC (LaxPair.HN α N c y))
    (E := fun y => toC (LaxPair.Epm α N c y)) (KNc_skew α)
    (fun x _ => isHermitian_toC _ (HN_symm α c x))
    (fun x _ => hasDerivWithinAt_toC_HN hα hN3 c x _)
    (continuous_toC_Epm α N c).continuousOn
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const (a := -d) (b := d)
    (C := phaseConst C₀) (f := fun y => Flow.traceNorm (toC (LaxPair.Epm α N c y)))
    (fun y hy => by
      rw [Set.uIoc_of_le hab] at hy
      rw [Real.norm_eq_abs, abs_of_nonneg (Flow.traceNorm_nonneg _)]
      exact traceNorm_Epm_le_const hα hn hN3 hN hC₀ hc (abs_le.2 ⟨hy.1.le, hy.2⟩))
  rw [show d - -d = 2 * d by ring, abs_of_nonneg (by linarith)] at hint
  exact (le_abs_self _).trans ((Real.norm_eq_abs _).symm.le.trans hint)

/-- Prop. `prop-phase-variation`, second inequality: `∑_j Var_{J_n} λ_j ≤ 2C(C₀)/q_n`. -/
theorem phase_variation_le {α : ℝ} (hα : Irrational α) {n : ℕ} (hn : 1 ≤ n) (hN3 : 3 ≤ N)
    (hN : N = qN α n ∨ N = qN α (n - 1)) {C₀ c : ℝ} (hC₀ : 0 ≤ C₀)
    (hc : |c| ≤ C₀ * (2 * |delta α (n - 1)|)) :
    ∑ j, eVariationOn (fun x => Flow.eig (LaxPair.BNc α N x + (c : ℂ) • Flow.bdryProj N) j)
        (Set.Icc (-|delta α (n - 1)|) (|delta α (n - 1)|)) ≤
      ENNReal.ofReal (2 * phaseConst C₀ / q α n) := by
  refine (phase_variation hα hn hN3 hN hC₀ hc).trans (ENNReal.ofReal_le_ofReal ?_)
  have hQ := q_pos hα n
  have hdQ := abs_delta_mul_q_lt hα hn
  have hP := phaseConst_nonneg hC₀
  rw [le_div_iff₀ hQ]
  nlinarith

/-! ## Proposition `prop-cover1` -/

/-- The constant of Proposition `prop-cover1`: `C'(C₀) = 2(4C₀ + 2 C(C₀))`. -/
def coverConst (C₀ : ℝ) : ℝ := 2 * (4 * C₀ + 2 * phaseConst C₀)

/-- **Proposition `prop-cover1`** (eqs. `subBN`, `lengthBN`, l. 1672–1772), for `n ≥ 1` and
`N ∈ {q_n, q_{n-1}}`, `N ≥ 3`: there are `N` intervals `[lo_j, hi_j]`, independent of
`x ∈ J_n` and of the Hermitian `V ∈ M_2(ℂ)` with `‖V‖ ≤ C₀|J_n|` (all eigenvalues in
`[-C₀|J_n|, C₀|J_n|]`), covering `σ(B_N(x) + Γ̂_N^* V Γ̂_N)`, with total length
`≤ (4C₀ + 2C(C₀))|J_n| ≤ C'(C₀)/q_n`. -/
theorem block_cover_of_three_le {α : ℝ} (hα : Irrational α) {n : ℕ} (hn : 1 ≤ n)
    (hN3 : 3 ≤ N) (hN : N = qN α n ∨ N = qN α (n - 1)) {C₀ : ℝ} (hC₀ : 0 ≤ C₀) :
    ∃ lo hi : Fin N → ℝ, (∀ j, lo j ≤ hi j) ∧
      ∑ j, (hi j - lo j) ≤ (4 * C₀ + 2 * phaseConst C₀) * (2 * |delta α (n - 1)|) ∧
      ∑ j, (hi j - lo j) ≤ coverConst C₀ / q α n ∧
      ∀ x ∈ Set.Icc (-|delta α (n - 1)|) (|delta α (n - 1)|),
      ∀ V : Matrix (Fin 2) (Fin 2) ℂ, ∀ hV : V.IsHermitian,
        (∀ i, |hV.eigenvalues i| ≤ C₀ * (2 * |delta α (n - 1)|)) →
        spectrum ℝ (LaxPair.BNc α N x + (Flow.bdry N)ᴴ * V * Flow.bdry N) ⊆
          ⋃ j, Set.Icc (lo j) (hi j) := by
  set d := |delta α (n - 1)| with hd
  have hd0 : 0 ≤ d := abs_nonneg _
  have hab : -d ≤ d := by linarith
  set c := C₀ * (2 * d) with hcdef
  have hc0 : 0 ≤ c := by positivity
  have hP := phaseConst_nonneg hC₀
  have hplus := phase_variation hα hn hN3 hN hC₀ (c := c) (by rw [abs_of_nonneg hc0])
  have hminus := phase_variation hα hn hN3 hN hC₀ (c := -c) (by rw [abs_neg, abs_of_nonneg hc0])
  have e : ∀ x, LaxPair.BNc α N x - (c : ℂ) • Flow.bdryProj N =
      LaxPair.BNc α N x + ((-c : ℝ) : ℂ) • Flow.bdryProj N := fun x => by
    rw [Complex.ofReal_neg, neg_smul, sub_eq_add_neg]
  have hV : ∑ j, eVariationOn (fun x => Flow.eig (LaxPair.BNc α N x + (c : ℂ) •
        Flow.bdryProj N) j) (Set.Icc (-d) d) +
      ∑ j, eVariationOn (fun x => Flow.eig (LaxPair.BNc α N x - (c : ℂ) •
        Flow.bdryProj N) j) (Set.Icc (-d) d) ≤
      ENNReal.ofReal (2 * (phaseConst C₀ * (2 * d))) := by
    simp only [e]
    rw [two_mul, ENNReal.ofReal_add (by positivity) (by positivity)]
    exact add_le_add hplus hminus
  have hB : ∀ x ∈ Set.Icc (-d) d, (LaxPair.BNc α N x).IsHermitian := fun x _ =>
    isHermitian_toC _ (BN_symm α x)
  obtain ⟨lo, hi, hle, hlen, hcov⟩ :=
    Flow.cover_bdry hab (by omega : 1 ≤ N) (fun x => LaxPair.BNc α N x) hc0 (by positivity) hB hV
  have hlen' : ∑ j, (hi j - lo j) ≤ (4 * C₀ + 2 * phaseConst C₀) * (2 * d) := by
    have : 4 * c + 2 * (phaseConst C₀ * (2 * d)) = (4 * C₀ + 2 * phaseConst C₀) * (2 * d) := by
      rw [hcdef]; ring
    linarith
  refine ⟨lo, hi, hle, hlen', ?_, fun x hx V hV₁ hV₂ => hcov x hx V hV₁ hV₂⟩
  have hQ := q_pos hα n
  have hdQ := abs_delta_mul_q_lt hα hn
  have hK : 0 ≤ 4 * C₀ + 2 * phaseConst C₀ := by positivity
  rw [le_div_iff₀ hQ]
  calc (∑ j, (hi j - lo j)) * q α n ≤ (4 * C₀ + 2 * phaseConst C₀) * (2 * d) * q α n :=
        mul_le_mul_of_nonneg_right hlen' hQ.le
    _ = 2 * (4 * C₀ + 2 * phaseConst C₀) * (d * q α n) := by ring
    _ ≤ 2 * (4 * C₀ + 2 * phaseConst C₀) * 1 := by gcongr
    _ = coverConst C₀ := by rw [coverConst, mul_one]

/-- `q_m ≥ 3` for `m ≥ 3` (`q_3 ≥ q_1 + q_2 ≥ q_1 + q_0 + q_1 ≥ 3`). -/
lemma three_le_qN {α : ℝ} (hα : Irrational α) {m : ℕ} (hm : 3 ≤ m) : 3 ≤ qN α m := by
  have a := q_add_le hα 1
  have b := q_add_le hα 0
  have c0 := q_one_le hα 0
  have c1 := q_one_le hα 1
  norm_num at a b
  have h3 : 3 ≤ q α 3 := by linarith
  have hmono : q α 3 ≤ q α m := (monotone_nat_of_le_succ (q_le_succ hα)) hm
  have : (3 : ℝ) ≤ qN α m := by rw [qN_cast hα]; linarith
  exact_mod_cast this

/-- **Proposition `prop-cover1`** (eqs. `subBN`, `lengthBN`, l. 1672–1772), in the paper's
range `n ≥ 4`: for `N ∈ {q_n, q_{n-1}}` there are `N` intervals `[lo_j, hi_j]` independent of
`x ∈ J_n = [-|δ_{n-1}|, |δ_{n-1}|]` and of `V = V^* ∈ M_2(ℂ)` with `‖V‖ ≤ C₀|J_n|`, such that
`σ(B_N(x) + Γ̂_N^* V Γ̂_N) ⊆ ⋃_j [lo_j, hi_j]` and `∑_j (hi_j - lo_j) ≤ C'(C₀)/q_n`, where
`C'(C₀) = coverConst C₀ = 2(4C₀ + 2(6π + 14π² + 8πC₀))`. -/
theorem block_cover {α : ℝ} (hα : Irrational α) {n : ℕ} (hn : 4 ≤ n) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hN : N = qN α n ∨ N = qN α (n - 1)) :
    ∃ lo hi : Fin N → ℝ, (∀ j, lo j ≤ hi j) ∧ ∑ j, (hi j - lo j) ≤ coverConst C₀ / q α n ∧
      ∀ x ∈ Set.Icc (-|delta α (n - 1)|) (|delta α (n - 1)|),
      ∀ V : Matrix (Fin 2) (Fin 2) ℂ, ∀ hV : V.IsHermitian,
        (∀ i, |hV.eigenvalues i| ≤ C₀ * (2 * |delta α (n - 1)|)) →
        spectrum ℝ (LaxPair.BNc α N x + (Flow.bdry N)ᴴ * V * Flow.bdry N) ⊆
          ⋃ j, Set.Icc (lo j) (hi j) := by
  have hN3 : 3 ≤ N := by
    rcases hN with rfl | rfl
    · exact three_le_qN hα (by omega)
    · exact three_le_qN hα (by omega)
  obtain ⟨lo, hi, hle, -, hlen, hcov⟩ :=
    block_cover_of_three_le hα (by omega) hN3 hN hC₀
  exact ⟨lo, hi, hle, hlen, hcov⟩

/-- **Proposition `prop-cover1`** in the form consumed by Theorem `thm-cover`
(`CAH.BlockCoverProp`, `SpectralCover.lean`), with `C₀ = 4π` and the explicit absolute constant
`C' = coverConst (4π) = 2(16π + 2(6π + 14π² + 32π²))`, for all irrational `α` and `n ≥ 4`. -/
theorem blockCoverProp_holds : ∃ C' : ℝ, 0 ≤ C' ∧ ∀ α : ℝ, Irrational α → ∀ n ≥ 4,
    BlockCoverProp α n (4 * π) C' := by
  refine ⟨coverConst (4 * π), ?_, fun α hα n hn N hN => ?_⟩
  · have := phaseConst_nonneg (C₀ := 4 * π) (by positivity)
    unfold coverConst; positivity
  · have e : JnLen α n = 2 * |delta α (n - 1)| := rfl
    simp only [e]
    exact block_cover hα hn (by positivity) hN

end BlockCover
end CAH
