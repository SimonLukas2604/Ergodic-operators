/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §2.7 (first part)  The Jitomirskaya–Last inequality  (book pp. 179–186)

## Main definitions
* `DF.lenWt L n`, `DF.normSqL u L`, `DF.normL u L` — the interpolated local norm
  `‖u‖_L` of (2.7.7), written as a weighted sum with weights `min(1, max(0, L - n + 1))`;
  `DF.normSqL_book` recovers the formula (2.7.7).
* `DF.solAB V E a b` — the solution at energy `E` with `u(1) = a`, `u(0) = b`; the book's
  `u_{1,θ}, u_{2,θ}` of (2.7.26) are `solAB V E (cos θ) (-sin θ)` and `solAB V E (sin θ) (cos θ)`.
* `DF.mAB V a b z = (a m₊(z) - b) / (a + b m₊(z))` — the `m`-function for the boundary
  condition determined by `(a, b)`; `DF.mTheta V θ = mAB V (cos θ) (-sin θ)` is the book's
  `m^θ_+` (formula (2.7.31)).

## Main results
* **Lemma 2.7.4** (variation of parameters, (2.7.13), (2.7.30)): `DF.variation_of_parameters`.
* (2.7.9) / proof of Theorem 2.7.8: `DF.hasSum_im_m` — `Im m = ε ∑_{n ≥ 1} |u⁺(n)|²`.
* **Proposition 2.7.5**: `DF.continuous_normSqL`, `DF.normSqL_mono`, `DF.normL_zero_left`,
  `DF.tendsto_normL_mul_atTop` (the map `P(L) = ‖u₁‖_L ‖u₂‖_L` is continuous, nondecreasing,
  vanishes at `L = 0`, and tends to `∞`).
* **Definition 2.7.6**: `DF.exists_jlLength` — for every `ε > 0` there is `L` with
  `‖u₁‖_L ‖u₂‖_L = 1 / (2ε)`, and such `L` tend to `∞` as `ε ↓ 0`.
* **Theorem 2.7.7 / 2.7.8** (Jitomirskaya–Last inequality): `DF.jitomirskaya_last_abstract`
  (for an arbitrary real fundamental system with Wronskian `-1`), `DF.jitomirskaya_last`
  (Dirichlet case, (2.7.18)) and `DF.jitomirskaya_last_theta` (general boundary condition,
  (2.7.29)).

## Deviations
* `L(ε)` is not made into a function: the inequality holds for *every* `L` solving (2.7.17),
  and we prove existence of such `L` (strict monotonicity of `P`, hence uniqueness of `L(ε)`,
  is not formalized; it is never needed).
* We use the sites `n = 1, 2, …` of `ℤ` for the half-line, as in the book.
-/
import DamanikFillman.Ch2.HalfLine

noncomputable section

open scoped ComplexConjugate
open Filter Topology Complex

namespace DF

/-! ### The interpolated norm `‖u‖_L` (2.7.7) -/

/-- The weight of site `n` in `‖·‖_L`: `1` for `n ≤ L`, `L - ⌊L⌋` for `n = ⌊L⌋ + 1`, and
`0` beyond. -/
def lenWt (L : ℝ) (n : ℕ) : ℝ := max 0 (min 1 (L - n + 1))

lemma lenWt_nonneg (L : ℝ) (n : ℕ) : 0 ≤ lenWt L n := le_max_left _ _

lemma lenWt_le_one (L : ℝ) (n : ℕ) : lenWt L n ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma lenWt_of_le {L : ℝ} {n : ℕ} (h : (n : ℝ) ≤ L) : lenWt L n = 1 := by
  unfold lenWt; rw [min_eq_left (by linarith), max_eq_right zero_le_one]

lemma lenWt_of_ge {L : ℝ} {n : ℕ} (h : L + 1 ≤ n) : lenWt L n = 0 := by
  unfold lenWt
  rw [max_eq_left]
  exact (min_le_right _ _).trans (by linarith)

lemma lenWt_mono {L L' : ℝ} (h : L ≤ L') (n : ℕ) : lenWt L n ≤ lenWt L' n := by
  unfold lenWt
  exact max_le_max le_rfl (min_le_min le_rfl (by linarith))

lemma continuous_lenWt (n : ℕ) : Continuous fun L => lenWt L n := by
  unfold lenWt; fun_prop

/-- `‖u‖_L²` (2.7.7), as a weighted sum over the sites `1, …, ⌊L⌋ + 1`. -/
def normSqL (u : ℤ → ℂ) (L : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊L⌋₊ + 1), lenWt L (n + 1) * ‖u ((n : ℤ) + 1)‖ ^ 2

/-- The interpolated norm `‖u‖_L` of (2.7.7). -/
def normL (u : ℤ → ℂ) (L : ℝ) : ℝ := √(normSqL u L)

lemma normSqL_nonneg (u : ℤ → ℂ) (L : ℝ) : 0 ≤ normSqL u L :=
  Finset.sum_nonneg fun n _ => mul_nonneg (lenWt_nonneg _ _) (by positivity)

lemma normL_nonneg (u : ℤ → ℂ) (L : ℝ) : 0 ≤ normL u L := Real.sqrt_nonneg _

lemma normL_sq (u : ℤ → ℂ) (L : ℝ) : normL u L ^ 2 = normSqL u L :=
  Real.sq_sqrt (normSqL_nonneg u L)

/-- The weighted sum may be taken over any longer range. -/
lemma normSqL_eq_range (u : ℤ → ℂ) (L : ℝ) {M : ℕ} (hM : ⌊L⌋₊ + 1 ≤ M) :
    normSqL u L = ∑ n ∈ Finset.range M, lenWt L (n + 1) * ‖u ((n : ℤ) + 1)‖ ^ 2 := by
  unfold normSqL
  apply Finset.sum_subset (Finset.range_subset_range.2 hM)
  intro n _ hn
  rw [Finset.mem_range, not_lt] at hn
  have h1 : L < ⌊L⌋₊ + 1 := Nat.lt_floor_add_one L
  have h2 : ((⌊L⌋₊ + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
  push_cast at h2
  rw [lenWt_of_ge (by push_cast; linarith), zero_mul]

/-- Formula (2.7.7): `‖u‖_L² = ∑_{n=1}^{⌊L⌋} |u(n)|² + (L - ⌊L⌋) |u(⌊L⌋+1)|²` for `L ≥ 0`. -/
theorem normSqL_book (u : ℤ → ℂ) {L : ℝ} (hL : 0 ≤ L) :
    normSqL u L = ∑ n ∈ Finset.range ⌊L⌋₊, ‖u ((n : ℤ) + 1)‖ ^ 2 +
      (L - ⌊L⌋₊) * ‖u ((⌊L⌋₊ : ℤ) + 1)‖ ^ 2 := by
  unfold normSqL
  rw [Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finset.mem_range] at hn
    have : ((n + 1 : ℕ) : ℝ) ≤ L := by
      have h1 : ((n + 1 : ℕ) : ℝ) ≤ ⌊L⌋₊ := by exact_mod_cast hn
      exact h1.trans (Nat.floor_le hL)
    rw [lenWt_of_le this, one_mul]
  · congr 1
    unfold lenWt
    have h1 : (⌊L⌋₊ : ℝ) ≤ L := Nat.floor_le hL
    have h2 : L < ⌊L⌋₊ + 1 := Nat.lt_floor_add_one L
    push_cast
    rw [min_eq_right (by linarith), max_eq_right (by linarith)]
    ring

lemma normSqL_mono (u : ℤ → ℂ) {L L' : ℝ} (h : L ≤ L') : normSqL u L ≤ normSqL u L' := by
  have hf : ⌊L⌋₊ ≤ ⌊L'⌋₊ := Nat.floor_le_floor h
  rw [normSqL_eq_range u L (M := ⌊L'⌋₊ + 1) (by omega)]
  unfold normSqL
  exact Finset.sum_le_sum fun n _ =>
    mul_le_mul_of_nonneg_right (lenWt_mono h _) (by positivity)

lemma normL_mono (u : ℤ → ℂ) {L L' : ℝ} (h : L ≤ L') : normL u L ≤ normL u L' :=
  Real.sqrt_le_sqrt (normSqL_mono u h)

lemma continuous_normSqL (u : ℤ → ℂ) : Continuous (normSqL u) := by
  rw [continuous_iff_continuousAt]
  intro L₀
  set M := ⌊L₀ + 1⌋₊ + 1
  have hg : Continuous fun L => ∑ n ∈ Finset.range M, lenWt L (n + 1) * ‖u ((n : ℤ) + 1)‖ ^ 2 :=
    continuous_finsetSum _ fun n _ => (continuous_lenWt _).mul continuous_const
  refine hg.continuousAt.congr ?_
  filter_upwards [Iio_mem_nhds (lt_add_one L₀)] with L hL
  exact (normSqL_eq_range u L (by have := Nat.floor_le_floor (le_of_lt (Set.mem_Iio.1 hL)); omega)).symm

lemma continuous_normL (u : ℤ → ℂ) : Continuous (normL u) :=
  (continuous_normSqL u).sqrt

@[simp] lemma normSqL_zero_left (u : ℤ → ℂ) : normSqL u 0 = 0 := by
  simp [normSqL, lenWt]

@[simp] lemma normL_zero_left (u : ℤ → ℂ) : normL u 0 = 0 := by simp [normL]

/-- Sites `1, …, k` with `k ≤ L` carry full weight. -/
lemma sum_le_normSqL (u : ℤ → ℂ) {L : ℝ} {k : ℕ} (hk : (k : ℝ) ≤ L) :
    ∑ n ∈ Finset.range k, ‖u ((n : ℤ) + 1)‖ ^ 2 ≤ normSqL u L := by
  have hL : 0 ≤ L := le_trans (Nat.cast_nonneg _) hk
  have hk' : k ≤ ⌊L⌋₊ := Nat.le_floor hk
  rw [normSqL_book u hL]
  have h1 : (⌊L⌋₊ : ℝ) ≤ L := Nat.floor_le hL
  have h2 : 0 ≤ (L - ⌊L⌋₊) * ‖u ((⌊L⌋₊ : ℤ) + 1)‖ ^ 2 :=
    mul_nonneg (by linarith) (by positivity)
  have h3 := Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hk')
    (f := fun n : ℕ => ‖u ((n : ℤ) + 1)‖ ^ 2) (fun _ _ _ => by positivity)
  linarith

lemma normSqL_le_sum (u : ℤ → ℂ) (L : ℝ) :
    normSqL u L ≤ ∑ n ∈ Finset.range (⌊L⌋₊ + 1), ‖u ((n : ℤ) + 1)‖ ^ 2 :=
  Finset.sum_le_sum fun n _ => by
    have := lenWt_le_one L (n + 1)
    nlinarith [sq_nonneg ‖u ((n : ℤ) + 1)‖, lenWt_nonneg L (n + 1)]

lemma normSqL_smul (u : ℤ → ℂ) (c : ℂ) (L : ℝ) :
    normSqL (fun n => c * u n) L = ‖c‖ ^ 2 * normSqL u L := by
  unfold normSqL
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [norm_mul]; ring

lemma normL_smul (u : ℤ → ℂ) (c : ℂ) (L : ℝ) :
    normL (fun n => c * u n) L = ‖c‖ * normL u L := by
  rw [normL, normSqL_smul, Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
  rfl

lemma normSqL_congr {u v : ℤ → ℂ} (h : ∀ n : ℤ, 1 ≤ n → ‖u n‖ = ‖v n‖) (L : ℝ) :
    normSqL u L = normSqL v L := by
  unfold normSqL
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [h _ (by omega)]

/-! ### Euclidean vectors realizing `‖·‖_L` -/

/-- The vector `(√w_L(n) u(n))_{n = 1}^{M}`, whose Euclidean norm is `‖u‖_L` for
`M ≥ ⌊L⌋ + 1`. -/
def lvec (u : ℤ → ℂ) (L : ℝ) (M : ℕ) : EuclideanSpace ℂ (Fin M) :=
  WithLp.toLp 2 fun i : Fin M => ((√(lenWt L ((i : ℕ) + 1)) : ℝ) : ℂ) * u (((i : ℕ) : ℤ) + 1)

lemma norm_lvec (u : ℤ → ℂ) (L : ℝ) {M : ℕ} (hM : ⌊L⌋₊ + 1 ≤ M) :
    ‖lvec u L M‖ = normL u L := by
  rw [EuclideanSpace.norm_eq, normL, normSqL_eq_range u L hM]
  congr 1
  rw [← Fin.sum_univ_eq_sum_range (fun n => lenWt L (n + 1) * ‖u ((n : ℤ) + 1)‖ ^ 2)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [lvec, PiLp.toLp_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (lenWt_nonneg _ _)]

lemma lvec_sub_smul (u v : ℤ → ℂ) (c : ℂ) (L : ℝ) (M : ℕ) :
    lvec (fun n => u n - c * v n) L M = lvec u L M - c • lvec v L M := by
  ext i
  simp only [lvec, PiLp.toLp_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
  ring

lemma lvec_add_smul (u v : ℤ → ℂ) (c d : ℂ) (L : ℝ) (M : ℕ) :
    lvec (fun n => c * u n + d * v n) L M = c • lvec u L M + d • lvec v L M := by
  ext i
  simp only [lvec, PiLp.toLp_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

/-- Pointwise domination of weighted norms. -/
lemma norm_lvec_le_of_le {u v : ℤ → ℂ} {L : ℝ} {M : ℕ}
    (h : ∀ i : Fin M, ‖u (((i : ℕ) : ℤ) + 1)‖ ≤ ‖v (((i : ℕ) : ℤ) + 1)‖) :
    ‖lvec u L M‖ ≤ ‖lvec v L M‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [lvec, PiLp.toLp_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (lenWt_nonneg _ _)]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (h i) 2) (lenWt_nonneg _ _)

/-! ### Real solutions at real energies -/

variable {V : ℤ → ℝ}

/-- The solution of (2.7.10) at real energy `E` with `u(1) = a`, `u(0) = b`. -/
def solAB (V : ℤ → ℝ) (E a b : ℝ) : ℤ → ℂ := solFrom V (E : ℂ) a b

lemma isSolution_solAB (E a b : ℝ) : IsSolution V E (solAB V E a b) :=
  isSolution_solFrom _ _ _ _

@[simp] lemma solAB_zero (E a b : ℝ) : solAB V E a b 0 = b := by simp [solAB]

@[simp] lemma solAB_one (E a b : ℝ) : solAB V E a b 1 = a := by simp [solAB]

/-- Solutions with real data at a real energy are real. -/
lemma solAB_im (E a b : ℝ) (n : ℤ) : (solAB V E a b n).im = 0 := by
  have hc : IsSolution V E (fun n => conj (solAB V E a b n)) := by
    intro n
    have h := congrArg conj (isSolution_solAB (V := V) E a b n)
    simp only [map_add, map_mul, Complex.conj_ofReal] at h
    exact h
  have h := eq_of_isSolution hc (isSolution_solAB E a b) (by simp [Complex.conj_ofReal])
    (by simp [Complex.conj_ofReal])
  exact Complex.conj_eq_iff_im.1 (congrFun h n)

lemma wronskian_solAB (E a b : ℝ) :
    wronskian (solAB V E a b) (solAB V E (-b) a) 0 = -((a : ℂ) ^ 2 + (b : ℂ) ^ 2) := by
  simp [wronskian]; ring

/-! ### Lemma 2.7.4: variation of parameters -/

/-- The partial sums `∑_{k=1}^{n-1} φ(k) ψ(k)`. -/
def psum (φ ψ : ℤ → ℂ) (n : ℕ) : ℂ := ∑ k ∈ Finset.Ico 1 n, φ k * ψ k

lemma psum_succ (φ ψ : ℤ → ℂ) {n : ℕ} (hn : 1 ≤ n) :
    psum φ ψ (n + 1) = psum φ ψ n + φ n * ψ n := Finset.sum_Ico_succ_top hn _

/-- The correction term `φ₂(n) ∑_{k<n} φ₁ ψ - φ₁(n) ∑_{k<n} φ₂ ψ` of (2.7.13). -/
def vpT (φ₁ φ₂ ψ : ℤ → ℂ) (n : ℕ) : ℂ := φ₂ n * psum φ₁ ψ n - φ₁ n * psum φ₂ ψ n

lemma vpT_alt (φ₁ φ₂ ψ : ℤ → ℂ) (n : ℕ) :
    vpT φ₁ φ₂ ψ n = φ₂ n * psum φ₁ ψ (n + 1) - φ₁ n * psum φ₂ ψ (n + 1) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [vpT, psum]
  · rw [vpT, psum_succ _ _ hn, psum_succ _ _ hn]; ring

/-- **Lemma 2.7.4** (variation of parameters, (2.7.13) and (2.7.30)): if `φ₁, φ₂` solve
(2.7.10) at energy `E` with Wronskian `-1` (i.e. `φ₁(n+1) φ₂(n) - φ₂(n+1) φ₁(n) = 1`), and
`ψ` solves (2.2.2) at `z = E + iε` with `ψ = φ₂ - m φ₁` at `n = 0, 1`, then for all `n ≥ 0`
`ψ(n) = φ₂(n) - m φ₁(n) - iε φ₂(n) ∑_{k=1}^{n} φ₁(k) ψ(k) + iε φ₁(n) ∑_{k=1}^{n} φ₂(k) ψ(k)`
(the `k = n` terms cancel, so we sum up to `n - 1`). -/
theorem variation_of_parameters {E ε : ℝ} {φ₁ φ₂ ψ : ℤ → ℂ} {m : ℂ}
    (h₁ : IsSolution V E φ₁) (h₂ : IsSolution V E φ₂) (hW : wronskian φ₁ φ₂ 0 = -1)
    (hψ : IsSolution V (E + ε * I) ψ) (h0 : ψ 0 = φ₂ 0 - m * φ₁ 0)
    (h1 : ψ 1 = φ₂ 1 - m * φ₁ 1) (n : ℕ) :
    ψ n = φ₂ n - m * φ₁ n - I * ε * vpT φ₁ φ₂ ψ n := by
  have key : ∀ n : ℕ, (ψ n = φ₂ n - m * φ₁ n - I * ε * vpT φ₁ φ₂ ψ n) ∧
      (ψ ((n + 1 : ℕ) : ℤ) = φ₂ ((n + 1 : ℕ) : ℤ) - m * φ₁ ((n + 1 : ℕ) : ℤ) -
        I * ε * vpT φ₁ φ₂ ψ (n + 1)) := by
    intro n
    induction n with
    | zero => exact ⟨by simp [vpT, psum, h0], by simp [vpT, psum, h1]⟩
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      obtain ⟨hP0, hP1⟩ := ih
      have eψ := hψ ((n : ℤ) + 1)
      have e1 := h₁ ((n : ℤ) + 1)
      have e2 := h₂ ((n : ℤ) + 1)
      have hW1 := wronskian_const h₁ h₂ ((n : ℤ) + 1)
      rw [hW] at hW1
      simp only [wronskian] at hW1
      simp only [add_sub_cancel_right] at eψ e1 e2
      rw [vpT_alt] at hP0
      rw [vpT] at hP1 ⊢
      rw [psum_succ _ _ (by omega : 1 ≤ n + 1), psum_succ _ _ (by omega : 1 ≤ n + 1)]
      set A₁ := psum φ₁ ψ (n + 1)
      set A₂ := psum φ₂ ψ (n + 1)
      push_cast at hP0 hP1 ⊢
      linear_combination eψ - hP0 + ((E : ℂ) - V ((n : ℤ) + 1)) * hP1 +
        I * ε * ψ ((n : ℤ) + 1) * hW1 - e2 + m * e1 + I * ε * A₁ * e2 - I * ε * A₂ * e1
  exact (key n).1

/-! ### (2.7.9): `Im m = ε ∑ |u⁺(n)|²` -/

/-- Summing (2.7.8): for a solution `ψ` at `z` that is square-summable at `+∞`,
`∑_{n ≥ 1} |ψ(n)|² = -Im (conj ψ(0) ψ(1)) / Im z`. -/
lemma hasSum_flux {z : ℂ} (hz : z.im ≠ 0) {ψ : ℤ → ℂ} (hψ : IsSolution V z ψ)
    (hψ2 : SqSumTop ψ) :
    HasSum (fun n : ℕ => ‖ψ ((n : ℤ) + 1)‖ ^ 2) (-(flux ψ 0) / z.im) := by
  have hpart : ∀ N : ℕ, z.im * ∑ n ∈ Finset.range N, ‖ψ ((n : ℤ) + 1)‖ ^ 2 =
      flux ψ N - flux ψ 0 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      have := flux_step hψ ((N : ℤ) + 1)
      rw [add_sub_cancel_right] at this
      push_cast
      have hn : ‖ψ ((N : ℤ) + 1)‖ ^ 2 = (ψ ((N : ℤ) + 1)).re ^ 2 + (ψ ((N : ℤ) + 1)).im ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      rw [hn]; linarith
  have hA := tendsto_shift hψ2 0
  have hB : Tendsto (fun N : ℕ => ψ ((N : ℤ) + 1)) atTop (𝓝 0) := by
    have := tendsto_shift hψ2 1
    refine (tendsto_congr fun N => ?_).mp this
    rw [add_comm]
  have hflux : Tendsto (fun N : ℕ => flux ψ N) atTop (𝓝 0) := by
    have hre : Continuous Complex.re := Complex.continuous_re
    have him : Continuous Complex.im := Complex.continuous_im
    have := (((hre.tendsto 0).comp hA).mul ((him.tendsto 0).comp hB)).sub
      (((him.tendsto 0).comp hA).mul ((hre.tendsto 0).comp hB))
    simp only [Complex.zero_re, Complex.zero_im, mul_zero, sub_zero] at this
    refine this.congr fun N => ?_
    simp [flux, Function.comp]
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun _ => by positivity)]
  have : Tendsto (fun N : ℕ => (flux ψ N - flux ψ 0) / z.im) atTop (𝓝 ((0 - flux ψ 0) / z.im)) :=
    (hflux.sub_const _).div_const _
  rw [zero_sub] at this
  refine this.congr fun N => ?_
  rw [← hpart N]; field_simp

/-- For `ψ = φ₂ - m φ₁` at `0, 1` with real `φ₁, φ₂` of Wronskian `-1`,
`-Im (conj ψ(0) ψ(1)) = Im m` (the computation in the proof of Theorem 2.7.8). -/
lemma neg_flux_eq_im {φ₁ φ₂ ψ : ℤ → ℂ} {m : ℂ} (hr₁ : ∀ n, (φ₁ n).im = 0)
    (hr₂ : ∀ n, (φ₂ n).im = 0) (hW : wronskian φ₁ φ₂ 0 = -1)
    (h0 : ψ 0 = φ₂ 0 - m * φ₁ 0) (h1 : ψ 1 = φ₂ 1 - m * φ₁ 1) : -(flux ψ 0) = m.im := by
  have hW' := congrArg Complex.re hW
  simp only [wronskian, zero_add, Complex.sub_re, Complex.mul_re, hr₁, hr₂, mul_zero,
    sub_zero, Complex.neg_re, Complex.one_re] at hW'
  simp only [flux, zero_add, h0, h1, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, hr₁, hr₂, mul_zero, sub_zero, zero_sub]
  linear_combination (-m.im) * hW'

/-- (2.7.9) (and its analogue in the proof of Theorem 2.7.8):
`Im m = ε ∑_{n ≥ 1} |ψ(n)|²`. -/
theorem hasSum_im_m {E ε : ℝ} (hε : ε ≠ 0) {φ₁ φ₂ ψ : ℤ → ℂ} {m : ℂ}
    (hr₁ : ∀ n, (φ₁ n).im = 0) (hr₂ : ∀ n, (φ₂ n).im = 0) (hW : wronskian φ₁ φ₂ 0 = -1)
    (hψ : IsSolution V (E + ε * I) ψ) (hψ2 : SqSumTop ψ)
    (h0 : ψ 0 = φ₂ 0 - m * φ₁ 0) (h1 : ψ 1 = φ₂ 1 - m * φ₁ 1) :
    HasSum (fun n : ℕ => ‖ψ ((n : ℤ) + 1)‖ ^ 2) (m.im / ε) := by
  have hz : (E + ε * I : ℂ).im = ε := by simp
  have := hasSum_flux (by rw [hz]; exact hε) hψ hψ2
  rwa [hz, neg_flux_eq_im hr₁ hr₂ hW h0 h1] at this

/-! ### The Jitomirskaya–Last inequality, abstract form -/

lemma abs_psum_le {φ ψ : ℤ → ℂ} {L : ℝ} (hL : 0 ≤ L) {n : ℕ} (hn : n ≤ ⌊L⌋₊ + 1) :
    ‖psum φ ψ n‖ ≤ normL φ L * normL ψ L := by
  unfold psum
  rw [Finset.sum_Ico_eq_sum_range]
  have hk : ((n - 1 : ℕ) : ℝ) ≤ L := by
    have : n - 1 ≤ ⌊L⌋₊ := by omega
    exact (Nat.cast_le.2 this).trans (Nat.floor_le hL)
  calc ‖∑ k ∈ Finset.range (n - 1), φ ((1 + k : ℕ) : ℤ) * ψ ((1 + k : ℕ) : ℤ)‖
      ≤ ∑ k ∈ Finset.range (n - 1), ‖φ ((k : ℤ) + 1)‖ * ‖ψ ((k : ℤ) + 1)‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [norm_mul]; push_cast; rw [add_comm (1 : ℤ)]
    _ ≤ √(∑ k ∈ Finset.range (n - 1), ‖φ ((k : ℤ) + 1)‖ ^ 2) *
          √(∑ k ∈ Finset.range (n - 1), ‖ψ ((k : ℤ) + 1)‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ normL φ L * normL ψ L :=
        mul_le_mul (Real.sqrt_le_sqrt (sum_le_normSqL φ hk))
          (Real.sqrt_le_sqrt (sum_le_normSqL ψ hk)) (Real.sqrt_nonneg _) (normL_nonneg _ _)

lemma normSqL_nonpos_of_nonpos (u : ℤ → ℂ) {L : ℝ} (hL : L ≤ 0) : normSqL u L = 0 :=
  le_antisymm ((normSqL_mono u hL).trans_eq (normSqL_zero_left u)) (normSqL_nonneg u L)

/-- **Theorems 2.7.7 and 2.7.8** (Jitomirskaya–Last inequality), abstract form: let `φ₁, φ₂`
be real solutions of (2.7.10) at energy `E` with Wronskian `-1`, `ε > 0`, and let `ψ ≠ 0` solve
(2.2.2) at `E + iε`, be square-summable at `+∞`, and satisfy `ψ = φ₂ - m φ₁` at `0, 1`.  If
`2ε ‖φ₁‖_L ‖φ₂‖_L = 1` (the length scale (2.7.17)/(2.7.27)), then
`(5 - √24)/|m| < ‖φ₁‖_L / ‖φ₂‖_L < (5 + √24)/|m|`. -/
theorem jitomirskaya_last_abstract {E ε : ℝ} (hε : 0 < ε) {φ₁ φ₂ ψ : ℤ → ℂ} {m : ℂ}
    (h₁ : IsSolution V E φ₁) (h₂ : IsSolution V E φ₂)
    (hr₁ : ∀ n, (φ₁ n).im = 0) (hr₂ : ∀ n, (φ₂ n).im = 0) (hW : wronskian φ₁ φ₂ 0 = -1)
    (hψ : IsSolution V (E + ε * I) ψ) (hψ2 : SqSumTop ψ) (hψ0 : ψ ≠ 0)
    (h0 : ψ 0 = φ₂ 0 - m * φ₁ 0) (h1 : ψ 1 = φ₂ 1 - m * φ₁ 1)
    {L : ℝ} (hL : 2 * ε * (normL φ₁ L * normL φ₂ L) = 1) :
    (5 - √24) / ‖m‖ < normL φ₁ L / normL φ₂ L ∧
      normL φ₁ L / normL φ₂ L < (5 + √24) / ‖m‖ := by
  set a := normL φ₁ L
  set b := normL φ₂ L
  set p := normL ψ L
  have ha0 := normL_nonneg φ₁ L
  have hb0 := normL_nonneg φ₂ L
  have hp0 := normL_nonneg ψ L
  have hab : 0 < a * b := by
    by_contra h; push Not at h
    have h' := le_antisymm h (mul_nonneg ha0 hb0)
    rw [h', mul_zero] at hL; norm_num at hL
  have ha : 0 < a := by
    by_contra h; push Not at h
    have h' := le_antisymm h ha0
    rw [h', zero_mul] at hab; exact lt_irrefl _ hab
  have hb : 0 < b := by
    by_contra h; push Not at h
    have h' := le_antisymm h hb0
    rw [h', mul_zero] at hab; exact lt_irrefl _ hab
  have hL0 : 0 ≤ L := by
    by_contra hneg
    push Not at hneg
    have : a = 0 := by simp [a, normL, normSqL_nonpos_of_nonpos φ₁ hneg.le]
    linarith
  have hz : (E + ε * I : ℂ).im ≠ 0 := by simp [hε.ne']
  -- (2.7.9) and (2.7.21)
  have hsum := hasSum_im_m hε.ne' hr₁ hr₂ hW hψ hψ2 h0 h1
  set N := ⌊L⌋₊
  have hpsq : p ^ 2 < m.im / ε := by
    rw [normL_sq]
    have hnz : ψ (((N + 1 : ℕ) : ℤ) + 1) ≠ 0 := weyl_top_ne_zero hz hψ hψ2 hψ0 _
    have h1 := normSqL_le_sum ψ L
    have h2 := sum_le_hasSum (Finset.range (N + 2)) (fun _ _ => by positivity) hsum
    rw [Finset.sum_range_succ] at h2
    have h3 : 0 < ‖ψ (((N + 1 : ℕ) : ℤ) + 1)‖ ^ 2 := by positivity
    linarith
  have him_le : m.im ≤ ‖m‖ := Complex.im_le_norm m
  have hmpos : 0 < ‖m‖ := by
    have : 0 ≤ p ^ 2 := by positivity
    have : 0 < m.im / ε := lt_of_le_of_lt this hpsq
    have : 0 < m.im := by
      rcases lt_or_ge 0 m.im with h | h
      · exact h
      · exact absurd this (not_lt.2 (div_nonpos_of_nonpos_of_nonneg h hε.le))
    linarith
  -- variation of parameters in vector form
  set M := N + 1
  set T : ℤ → ℂ := fun n => vpT φ₁ φ₂ ψ n.toNat
  have hvp : lvec (fun n => φ₂ n - m * φ₁ n) L M = lvec ψ L M + ((I * ε : ℂ)) • lvec T L M := by
    ext i
    simp only [lvec, PiLp.toLp_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
    have hv := variation_of_parameters h₁ h₂ hW hψ h0 h1 ((i : ℕ) + 1)
    have ht : T (((i : ℕ) : ℤ) + 1) = vpT φ₁ φ₂ ψ ((i : ℕ) + 1) := by
      simp only [T]; congr 1
    push_cast at hv
    rw [ht, hv]; ring
  -- bound on the correction term
  have hT : ‖lvec T L M‖ ≤ 2 * a * b * p := by
    set g : ℤ → ℂ := fun n => ((a * p : ℝ) : ℂ) * (‖φ₂ n‖ : ℂ) + ((b * p : ℝ) : ℂ) * (‖φ₁ n‖ : ℂ)
      with hg_def
    have hpt : ∀ i : Fin M, ‖T (((i : ℕ) : ℤ) + 1)‖ ≤ ‖g (((i : ℕ) : ℤ) + 1)‖ := by
      intro i
      have hi : (i : ℕ) + 1 ≤ N + 1 := by have := i.2; omega
      have ht : T (((i : ℕ) : ℤ) + 1) = vpT φ₁ φ₂ ψ ((i : ℕ) + 1) := by
        simp only [T]; congr 1
      rw [ht, vpT]
      have e1 := abs_psum_le (φ := φ₁) (ψ := ψ) hL0 hi
      have e2 := abs_psum_le (φ := φ₂) (ψ := ψ) hL0 hi
      simp only [g]
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc _ ≤ ‖φ₂ (((i : ℕ) + 1 : ℕ) : ℤ)‖ * ‖psum φ₁ ψ ((i : ℕ) + 1)‖ +
            ‖φ₁ (((i : ℕ) + 1 : ℕ) : ℤ)‖ * ‖psum φ₂ ψ ((i : ℕ) + 1)‖ := by
            refine (norm_sub_le _ _).trans ?_
            rw [norm_mul, norm_mul]
        _ ≤ ‖φ₂ (((i : ℕ) + 1 : ℕ) : ℤ)‖ * (a * p) + ‖φ₁ (((i : ℕ) + 1 : ℕ) : ℤ)‖ * (b * p) := by
            gcongr
        _ = _ := by push_cast; ring
    refine (norm_lvec_le_of_le (v := g) hpt).trans ?_
    rw [hg_def, lvec_add_smul]
    refine (norm_add_le _ _).trans ?_
    have hg : ∀ u : ℤ → ℂ, normL (fun n => (‖u n‖ : ℂ)) L = normL u L := fun u => by
      unfold normL; rw [normSqL_congr (v := u) (fun n _ => by simp)]
    rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity),
      norm_lvec _ _ le_rfl, norm_lvec _ _ le_rfl, hg, hg]
    apply le_of_eq; ring
  have hnorm : ‖lvec ψ L M‖ = p := norm_lvec _ _ le_rfl
  have hdiff : ‖lvec (fun n => φ₂ n - m * φ₁ n) L M‖ ≤ 2 * p := by
    rw [hvp]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, hnorm]
    have he : ‖(I * ε : ℂ)‖ = ε := by simp [abs_of_pos hε]
    rw [he]
    have : ε * ‖lvec T L M‖ ≤ ε * (2 * a * b * p) := mul_le_mul_of_nonneg_left hT hε.le
    have h2 : ε * (2 * a * b * p) = p := by linear_combination p * hL
    linarith
  have hlow : |b - ‖m‖ * a| ≤ ‖lvec (fun n => φ₂ n - m * φ₁ n) L M‖ := by
    rw [lvec_sub_smul]
    have := abs_norm_sub_norm_le (lvec φ₂ L M) (m • lvec φ₁ L M)
    rwa [norm_smul, norm_lvec _ _ le_rfl, norm_lvec _ _ le_rfl] at this
  -- (2.7.22)–(2.7.23)
  have hq : (b - ‖m‖ * a) ^ 2 < 8 * ‖m‖ * a * b := by
    have h1 : (b - ‖m‖ * a) ^ 2 ≤ 4 * p ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg _) (hlow.trans hdiff) 2
      rw [sq_abs] at h
      nlinarith
    have h3 : m.im / ε ≤ ‖m‖ / ε := div_le_div_of_nonneg_right him_le hε.le
    have h4 : ‖m‖ / ε = 2 * ‖m‖ * a * b := by
      rw [div_eq_iff hε.ne']; linear_combination (-‖m‖) * hL
    linarith
  set x := ‖m‖
  set t := x * (a / b)
  have hab' : a = (a / b) * b := by field_simp
  have key : b ^ 2 * ((1 - t) ^ 2 - 8 * t) < 0 := by
    rw [hab'] at hq; nlinarith [hq]
  have hkey := neg_of_mul_neg_right key (sq_nonneg b)
  have h24 : (t - 5) ^ 2 < √24 ^ 2 := by
    rw [Real.sq_sqrt (by norm_num)]; nlinarith [hkey]
  have habs := abs_lt.1 (abs_lt_of_sq_lt_sq h24 (Real.sqrt_nonneg _))
  constructor
  · rw [div_lt_iff₀ hmpos]; simp only [t] at habs; linarith [habs.1, mul_comm x (a / b)]
  · rw [lt_div_iff₀ hmpos]; simp only [t] at habs; linarith [habs.2, mul_comm x (a / b)]

/-! ### Proposition 2.7.5 and Definition 2.7.6 -/

lemma tendsto_normSqL_atTop {u : ℤ → ℂ} (h : ¬ SqSumTop u) :
    Tendsto (normSqL u) atTop atTop := by
  have h' : ¬ Summable (fun n : ℕ => ‖u ((n : ℤ) + 1)‖ ^ 2) := by
    intro hs; apply h
    unfold SqSumTop
    rw [← summable_nat_add_iff 1]
    refine hs.congr fun n => ?_
    push_cast; rfl
  have hpart := (not_summable_iff_tendsto_nat_atTop_of_nonneg (fun n => by positivity)).1 h'
  refine tendsto_atTop_mono' atTop ?_ (hpart.comp tendsto_nat_floor_atTop)
  filter_upwards [eventually_ge_atTop 0] with L hL
  exact sum_le_normSqL u (Nat.floor_le hL)

lemma tendsto_normL_atTop {u : ℤ → ℂ} (h : ¬ SqSumTop u) : Tendsto (normL u) atTop atTop :=
  Real.tendsto_sqrt_atTop.comp (tendsto_normSqL_atTop h)

/-- A nonzero solution has positive local norm for `L ≥ 2`. -/
lemma normL_pos {z : ℂ} {u : ℤ → ℂ} (hu : IsSolution V z u) (hne : u ≠ 0) {L : ℝ}
    (hL : 2 ≤ L) : 0 < normL u L := by
  apply Real.sqrt_pos.2
  have h := sum_le_normSqL u (k := 2) (by norm_num; linarith)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  by_contra hc
  push Not at hc
  have h1 : u 1 = 0 := by
    have : ‖u ((0 : ℕ) + 1)‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖u ((1 : ℕ) + 1)‖]
    simpa using this
  have h2 : u 2 = 0 := by
    have : ‖u ((1 : ℕ) + 1)‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖u ((0 : ℕ) + 1)‖]
    have : u ((1 : ℕ) + 1) = 0 := by simpa using this
    simpa using this
  have h0 : u 0 = 0 := by
    have := hu 1
    norm_num at this
    rw [h1, h2] at this; simpa using this
  exact hne (eq_zero_of_isSolution hu h0 h1)

/-- **Proposition 2.7.5**: for solutions `φ₁, φ₂` with nonzero Wronskian (e.g. `u₁, u₂`),
`P(L) = ‖φ₁‖_L ‖φ₂‖_L → ∞` (continuity and monotonicity are `DF.continuous_normL` and
`DF.normL_mono`; `P(0) = 0` is `DF.normL_zero_left`). -/
theorem tendsto_normL_mul_atTop {z : ℂ} {φ₁ φ₂ : ℤ → ℂ} (h₁ : IsSolution V z φ₁)
    (h₂ : IsSolution V z φ₂) (hW : wronskian φ₁ φ₂ 0 ≠ 0) :
    Tendsto (fun L => normL φ₁ L * normL φ₂ L) atTop atTop := by
  have hne₁ : φ₁ ≠ 0 := by rintro rfl; simp [wronskian] at hW
  have hne₂ : φ₂ ≠ 0 := by rintro rfl; simp [wronskian] at hW
  have hnot : ¬ (SqSumTop φ₁ ∧ SqSumTop φ₂) := fun h =>
    hW (wronskian_eq_zero_of_sqSumTop h₁ h₂ h.1 h.2)
  by_cases hs : SqSumTop φ₁
  · have hs2 : ¬ SqSumTop φ₂ := fun h => hnot ⟨hs, h⟩
    have hc := normL_pos h₁ hne₁ (le_refl 2)
    refine tendsto_atTop_mono' atTop ?_ ((tendsto_normL_atTop hs2).const_mul_atTop hc)
    filter_upwards [eventually_ge_atTop 2] with L hL
    exact mul_le_mul_of_nonneg_right (normL_mono _ hL) (normL_nonneg _ _)
  · have hc := normL_pos h₂ hne₂ (le_refl 2)
    refine tendsto_atTop_mono' atTop ?_ ((tendsto_normL_atTop hs).atTop_mul_const hc)
    filter_upwards [eventually_ge_atTop 2] with L hL
    exact mul_le_mul_of_nonneg_left (normL_mono _ hL) (normL_nonneg _ _)

/-- **Definition 2.7.6** (existence of the length scale `L(ε)`): if `P` is continuous and
tends to `∞`, then for every `R`, all sufficiently small `ε > 0` admit some `L > R` with
`2 ε P(L) = 1`. -/
theorem exists_jlLength {P : ℝ → ℝ} (hPc : Continuous P) (hP : Tendsto P atTop atTop)
    (R : ℝ) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ L, R < L ∧ 2 * ε * P L = 1 := by
  have hy : Tendsto (fun ε : ℝ => (2 * ε)⁻¹) (𝓝[>] 0) atTop := by
    refine tendsto_inv_nhdsGT_zero.comp ?_
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have : Tendsto (fun ε : ℝ => 2 * ε) (𝓝[>] 0) (𝓝 (2 * 0)) :=
        (tendsto_nhdsWithin_of_tendsto_nhds (continuous_const.mul continuous_id).continuousAt)
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      exact mul_pos two_pos hε
  filter_upwards [hy.eventually (eventually_gt_atTop (P R)), self_mem_nhdsWithin]
    with ε hε (hε0 : 0 < ε)
  obtain ⟨R', hR'⟩ := ((hP.eventually (eventually_ge_atTop (2 * ε)⁻¹)).and
    (eventually_ge_atTop R)).exists
  obtain ⟨L, hL, hPL⟩ := intermediate_value_Icc hR'.2 hPc.continuousOn ⟨hε.le, hR'.1⟩
  refine ⟨L, lt_of_le_of_ne hL.1 ?_, ?_⟩
  · rintro rfl; rw [hPL] at hε; exact lt_irrefl _ hε
  · rw [hPL]; field_simp

/-- Conversely, every large `L` is a length scale `L(ε)` with `ε = 1/(2 P(L)) → 0⁺`. -/
theorem tendsto_jlEps {P : ℝ → ℝ} (hP : Tendsto P atTop atTop) :
    Tendsto (fun L => (2 * P L)⁻¹) atTop (𝓝[>] 0) :=
  tendsto_inv_atTop_nhdsGT_zero.comp (hP.const_mul_atTop two_pos)

/-! ### Theorems 2.7.7 and 2.7.8 -/

lemma u₁_eq_solAB (E : ℝ) : u₁ V (E : ℂ) = solAB V E 1 0 := by simp [u₁, solAB]

lemma u₂_eq_solAB (E : ℝ) : u₂ V (E : ℂ) = solAB V E 0 1 := by simp [u₂, solAB]

/-- The normalized Dirichlet Weyl solution `u⁺_z = u₂ - m₊(z) u₁` (with `u⁺_z(0) = 1`). -/
def weylDir (V : ℤ → ℝ) (z : ℂ) : ℤ → ℂ := fun n => u₂ V z n - mPlus V z * u₁ V z n

lemma isSolution_weylDir (V : ℤ → ℝ) (z : ℂ) : IsSolution V z (weylDir V z) := by
  intro n
  have a := isSolution_solFrom V z 0 1 n
  have b := isSolution_solFrom V z 1 0 n
  simp only [weylDir, u₁, u₂]
  linear_combination a - mPlus V z * b

lemma weylDir_ne_zero (V : ℤ → ℝ) (z : ℂ) : weylDir V z ≠ 0 := by
  intro h; have := congrFun h 0; simp [weylDir] at this

/-- `Im m₊(E + iε) = ε ∑_{n≥1} |u⁺_z(n)|²` (2.7.9). -/
theorem hasSum_im_mPlus (hV : BddPot V) {E ε : ℝ} (hε : 0 < ε) :
    HasSum (fun n : ℕ => ‖weylDir V (E + ε * I) ((n : ℤ) + 1)‖ ^ 2)
      ((mPlus V (E + ε * I)).im / ε) := by
  have hz : (E + ε * I : ℂ).im ≠ 0 := by simp [hε.ne']
  refine hasSum_im_m hε.ne' (φ₁ := u₁ V (E : ℂ)) (φ₂ := u₂ V (E : ℂ))
    (fun n => by rw [u₁_eq_solAB]; exact solAB_im _ _ _ _)
    (fun n => by rw [u₂_eq_solAB]; exact solAB_im _ _ _ _) (by simp [wronskian])
    (isSolution_weylDir V _) (mPlus_spec hV hz).1 (by simp [weylDir]) (by simp [weylDir])

/-- `m₊` maps the upper half-plane into itself. -/
theorem im_mPlus_pos (hV : BddPot V) {E ε : ℝ} (hε : 0 < ε) :
    0 < (mPlus V (E + ε * I)).im := by
  have hz : (E + ε * I : ℂ).im ≠ 0 := by simp [hε.ne']
  have h := hasSum_im_mPlus hV (E := E) hε
  have hle := le_hasSum h 0 (fun _ _ => by positivity)
  have hne : weylDir V (E + ε * I) ((0 : ℕ) + 1) ≠ 0 :=
    weyl_top_ne_zero hz (isSolution_weylDir V _) (mPlus_spec hV hz).1 (weylDir_ne_zero V _) _
  have hpos : 0 < ‖weylDir V (E + ε * I) ((0 : ℕ) + 1)‖ ^ 2 := by positivity
  have := lt_of_lt_of_le hpos hle
  exact (div_pos_iff_of_pos_right hε).1 this

/-- The `m`-function for the boundary condition `ψ(1) b - ψ(0) a = 0`... more precisely, for the
fundamental system `φ₁ = solAB a b`, `φ₂ = solAB (-b) a`: the unique `m` with
`v₂ - m v₁ ∈ ℓ²` at `+∞` (cf. (2.7.28)); explicitly `(a m₊ - b) / (a + b m₊)`. -/
def mAB (V : ℤ → ℝ) (a b : ℝ) (z : ℂ) : ℂ := (a * mPlus V z - b) / (a + b * mPlus V z)

/-- The book's `m^θ_+` (2.7.28), with `u_{1,θ} = solAB (cos θ) (-sin θ)`. -/
def mTheta (V : ℤ → ℝ) (θ : ℝ) (z : ℂ) : ℂ := mAB V (Real.cos θ) (-Real.sin θ) z

/-- Formula (2.7.31). -/
lemma mTheta_eq (V : ℤ → ℝ) (θ : ℝ) (z : ℂ) :
    mTheta V θ z = (Real.sin θ + mPlus V z * Real.cos θ) / (Real.cos θ - mPlus V z * Real.sin θ) := by
  unfold mTheta mAB; push_cast; congr 1 <;> ring

@[simp] lemma mAB_one_zero (V : ℤ → ℝ) (z : ℂ) : mAB V 1 0 z = mPlus V z := by simp [mAB]

lemma add_mul_mPlus_ne_zero (hV : BddPot V) {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) {E ε : ℝ}
    (hε : 0 < ε) : (a : ℂ) + b * mPlus V (E + ε * I) ≠ 0 := by
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, zero_mul,
    add_zero, zero_add, Complex.zero_im] at him
  have hpos := im_mPlus_pos hV (E := E) hε
  have hb : b = 0 := by
    rcases mul_eq_zero.1 him with h' | h'
    · exact h'
    · linarith
  subst hb
  have hre := congrArg Complex.re h
  simp at hre
  subst hre; norm_num at hab

/-- The Weyl solution adapted to `(a, b)`: `v₂ - m v₁` with `v₁ = solFrom a b`,
`v₂ = solFrom (-b) a` at energy `z`. -/
def weylAB (V : ℤ → ℝ) (a b : ℝ) (z : ℂ) : ℤ → ℂ :=
  fun n => solFrom V z (-b) a n - mAB V a b z * solFrom V z a b n

lemma weylAB_eq (hV : BddPot V) {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) {E ε : ℝ} (hε : 0 < ε) :
    weylAB V a b (E + ε * I) =
      fun n => (a - mAB V a b (E + ε * I) * b) * weylDir V (E + ε * I) n := by
  set z : ℂ := E + ε * I
  have hne := add_mul_mPlus_ne_zero hV hab (E := E) hε
  apply eq_of_isSolution (V := V) (z := z)
  · intro n
    have a1 := isSolution_solFrom V z (-b) a n
    have a2 := isSolution_solFrom V z a b n
    simp only [weylAB]
    linear_combination a1 - mAB V a b z * a2
  · intro n
    have := isSolution_weylDir V z n
    simp only
    linear_combination (a - mAB V a b z * b) * this
  · simp [weylAB, weylDir]
  · have hm : mAB V a b z * (a + b * mPlus V z) = a * mPlus V z - b := div_mul_cancel₀ _ hne
    simp only [weylAB, weylDir, solFrom_one, u₂, u₁]
    linear_combination (-1 : ℂ) * hm

/-- **Theorem 2.7.8** (Jitomirskaya–Last inequality, general boundary condition), stated for
the fundamental system `φ₁ = solAB a b`, `φ₂ = solAB (-b) a` with `a² + b² = 1`. -/
theorem jitomirskaya_last_ab (hV : BddPot V) {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) {E ε : ℝ}
    (hε : 0 < ε) {L : ℝ}
    (hL : 2 * ε * (normL (solAB V E a b) L * normL (solAB V E (-b) a) L) = 1) :
    (5 - √24) / ‖mAB V a b (E + ε * I)‖ < normL (solAB V E a b) L / normL (solAB V E (-b) a) L ∧
      normL (solAB V E a b) L / normL (solAB V E (-b) a) L <
        (5 + √24) / ‖mAB V a b (E + ε * I)‖ := by
  set z : ℂ := E + ε * I
  have hz : z.im ≠ 0 := by simp [z, hε.ne']
  have hne := add_mul_mPlus_ne_zero hV hab (E := E) hε
  have hab' : (a : ℂ) ^ 2 + (b : ℂ) ^ 2 = 1 := by exact_mod_cast hab
  have hm : mAB V a b z * (a + b * mPlus V z) = a * mPlus V z - b := div_mul_cancel₀ _ hne
  have hc : (a - mAB V a b z * b) * (a + b * mPlus V z) = 1 := by
    linear_combination (-(b : ℂ)) * hm + hab'
  have hc0 : (a - mAB V a b z * b) ≠ 0 := left_ne_zero_of_mul_eq_one hc
  have hW : wronskian (solAB V E a b) (solAB V E (-b) a) 0 = -1 := by
    rw [wronskian_solAB, hab']
  refine jitomirskaya_last_abstract hε (isSolution_solAB E a b) (isSolution_solAB E (-b) a)
    (solAB_im E a b) (solAB_im E (-b) a) hW (ψ := weylAB V a b z) ?_ ?_ ?_ ?_ ?_ hL
  · intro n
    have a1 := isSolution_solFrom V z (-b) a n
    have a2 := isSolution_solFrom V z a b n
    simp only [weylAB]
    linear_combination a1 - mAB V a b z * a2
  · rw [weylAB_eq hV hab hε]; exact sqSumTop_smul (mPlus_spec hV hz).1 _
  · intro h
    have := congrFun h 0
    rw [weylAB_eq hV hab hε] at this
    simp [weylDir] at this
    exact hc0 this
  · simp [weylAB]
  · simp [weylAB]

/-- **Theorem 2.7.8** (Jitomirskaya–Last inequality (2.7.29)) for `u_{1,θ}, u_{2,θ}` of
(2.7.26) and `m^θ_+`. -/
theorem jitomirskaya_last_theta (hV : BddPot V) (θ : ℝ) {E ε : ℝ} (hε : 0 < ε) {L : ℝ}
    (hL : 2 * ε * (normL (solAB V E (Real.cos θ) (-Real.sin θ)) L *
      normL (solAB V E (Real.sin θ) (Real.cos θ)) L) = 1) :
    (5 - √24) / ‖mTheta V θ (E + ε * I)‖ <
        normL (solAB V E (Real.cos θ) (-Real.sin θ)) L /
          normL (solAB V E (Real.sin θ) (Real.cos θ)) L ∧
      normL (solAB V E (Real.cos θ) (-Real.sin θ)) L /
          normL (solAB V E (Real.sin θ) (Real.cos θ)) L <
        (5 + √24) / ‖mTheta V θ (E + ε * I)‖ := by
  have h := jitomirskaya_last_ab hV (a := Real.cos θ) (b := -Real.sin θ)
    (by rw [neg_sq]; exact Real.cos_sq_add_sin_sq θ) hε (L := L) (by rwa [neg_neg])
  rw [neg_neg] at h
  exact h

/-- **Theorem 2.7.7** (Jitomirskaya–Last inequality (2.7.18)), Dirichlet case: if
`2ε ‖u₁‖_L ‖u₂‖_L = 1` then
`(5 - √24)/|m₊(E + iε)| < ‖u₁‖_L/‖u₂‖_L < (5 + √24)/|m₊(E + iε)|`. -/
theorem jitomirskaya_last (hV : BddPot V) {E ε : ℝ} (hε : 0 < ε) {L : ℝ}
    (hL : 2 * ε * (normL (u₁ V E) L * normL (u₂ V E) L) = 1) :
    (5 - √24) / ‖mPlus V (E + ε * I)‖ < normL (u₁ V E) L / normL (u₂ V E) L ∧
      normL (u₁ V E) L / normL (u₂ V E) L < (5 + √24) / ‖mPlus V (E + ε * I)‖ := by
  rw [u₁_eq_solAB, u₂_eq_solAB] at hL ⊢
  have h := jitomirskaya_last_ab hV (a := 1) (b := 0) (by norm_num) hε (L := L)
    (by simpa using hL)
  simpa using h

end DF
