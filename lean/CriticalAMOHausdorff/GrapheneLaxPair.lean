/-
Copyright (c) 2026. Formalization of
  S. Becker, S. Jitomirskaya, I. Krasovsky, "Critical almost Mathieu operator: hidden
  singularity, gap continuity, and the Hausdorff dimension of the spectrum"
  (arXiv:1909.04429v2).

# The graphene commutator identity  (Appendix §9, proof of Theorem 9.1 `gr`, tex l. 1836–1910)

For `α = Φ/2π` the auxiliary Jacobi operator of [bhj, (5.4)], translated by `1/2`, has the
complex coefficients `c(x) = 1 - e^{-2πix}` (`cB`) and `v(x) = -2cos(2πx)` (`vB`).

* `GN α x N`: the Hermitian block `G_N(x)` (tex l. 1848–1851), `c_m = c(x+mα)` (`cm`);
* `kap α r`: `κ_r`, defined as `2πi(-1)^r/(e^{-2πirα} - 1)`; `kap_eq` proves it equals the
  paper's `π(-1)^{r-1}e^{πirα}/sin(πrα)` (`r ≠ 0`), `kap_neg`: `κ_{-r} = -conj κ_r`,
  `kap_zero`: `κ_0 = 0`, `kap_mul`: `κ_r(e^{-2πirα} - 1) = 2πi(-1)^r`,
  `norm_kap`: `|κ_r| = π/|sin(πrα)|`;
* `KG α N`: `(K_N^g)_{jk} = κ_{k-j}`, skew-Hermitian (`KG_skew`);
* `EG α x N`: the error `E_N(x)` **exactly as printed in the paper** (tex l. 1866–1872);
* `commutator_identity`: **`G_N'(x) = [K_N^g, G_N(x)] + E_N(x)`** for irrational `α`, all `N`;
* `corner_eq`: the combined corner `(E_N)_{0,N-1} = κ_N(conj c_N - conj c_0) =
  2πi(-1)^N e^{2πi(x+Nα)}` (tex l. 1876–1879);
* `EG_isHermitian`, `Epm_isHermitian`, `rank_Epm_le` (`rank E_N^± ≤ 4`),
  `Sk_le` (`∑_{r<N} |κ_r|² ≤ 4π² q_n²` for `N ≤ q_n`, from `CAH.sum_inv_sin_sq_le`),
  `hs_Epm_le` (Hilbert–Schmidt estimate), and `traceNorm_Epm_le_const`:
  `sup_{x∈J_n} ‖E_N^±(x)‖_{S_1} ≤ grPhaseConst C₀` (tex l. 1885–1910), where
  `E_N^± = E_N ∓ τ[K_N^g, P_N]` is `Epm α N (±τ) x`.

## Numerical check

The formula for `E_N` and the corner identity were checked numerically (Python, `N = 1,2,3,7,8`,
generic `α`, `x`): the paper's formulas are correct as stated (no typo found), `E_N` is
Hermitian, and the identity holds for every `N ≥ 1`.

## Remarks

* The trace-norm bound is obtained as in the paper from rank `≤ 4` and a Hilbert–Schmidt bound;
  `E_N` is split as corner + four boundary rows/columns (`EG_split`), the corner being handled
  through `κ_N(conj c_N - conj c_0)`, `|·| = 2π` (`norm_conj_sub_le`).
* The paper's estimate `|c_0| + |c_N| + τ ≤ C/q_n` enters via `|c(y)| = 2|sin πy|` (`norm_cm`)
  and `BlockCover.sq_two_sin_le`, `BlockCover.sq_two_sin_shift_le`.

No `sorry`, no axioms.
-/
import CriticalAMOHausdorff.BlockCover

noncomputable section

open Matrix Real
open scoped ComplexConjugate

namespace CAH
namespace Graphene

/-! ## 1. The coefficients -/

/-- `e(t) = e^{-2πit}`. -/
def ex (t : ℝ) : ℂ := Complex.exp (-(2 * π * Complex.I) * (t : ℂ))

/-- The off-diagonal coefficient `c(x) = 1 - e^{-2πix}` (tex l. 1846). -/
def cB (x : ℝ) : ℂ := 1 - ex x

/-- The potential `v(x) = -2 cos(2πx)` (tex l. 1846). -/
def vB (x : ℝ) : ℝ := -2 * Real.cos (2 * π * x)

lemma ex_add (s t : ℝ) : ex (s + t) = ex s * ex t := by
  unfold ex; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma ex_zero : ex 0 = 1 := by simp [ex]

lemma ex_neg_mul (t : ℝ) : ex (-t) * ex t = 1 := by rw [← ex_add]; simp [ex_zero]

lemma conj_ex (t : ℝ) : conj (ex t) = ex (-t) := by
  unfold ex; rw [← Complex.exp_conj]; congr 1
  simp only [map_mul, map_neg, Complex.conj_I, Complex.conj_ofReal, map_ofNat]; push_cast; ring

lemma norm_ex (t : ℝ) : ‖ex t‖ = 1 := by
  unfold ex; rw [Complex.norm_exp]; simp

lemma ex_shift {a b s : ℝ} (h : b = a + s) : ex b = ex a * ex s := by rw [h, ex_add]

/-- The key identity `e^{-2πit} - 1 = -2i sin(πt) e^{-πit}`. -/
lemma ex_sub_one (t : ℝ) :
    ex t - 1 = -2 * Complex.I * (Real.sin (π * t) : ℂ) * Complex.exp (-((π * t : ℝ) : ℂ) * Complex.I) := by
  set z : ℂ := ((π * t : ℝ) : ℂ)
  have h1 : ex t = Complex.exp (-z * Complex.I) * Complex.exp (-z * Complex.I) := by
    rw [← Complex.exp_add]; unfold ex; congr 1; simp only [z]; push_cast; ring
  have h2 : Complex.exp (z * Complex.I) * Complex.exp (-z * Complex.I) = 1 := by
    rw [← Complex.exp_add]; simp
  rw [h1, Complex.ofReal_sin, Complex.sin]
  linear_combination (Complex.exp (-z * Complex.I) ^ 2 -
    Complex.exp (z * Complex.I) * Complex.exp (-z * Complex.I)) * Complex.I_sq + h2

lemma vB_eq (y : ℝ) : ((vB y : ℝ) : ℂ) = -(ex y + ex (-y)) := by
  have h1 : ex (-y) = Complex.exp ((2 * π * y : ℂ) * Complex.I) := by
    unfold ex; congr 1; push_cast; ring
  have h2 : ex y = Complex.exp (-(2 * π * y : ℂ) * Complex.I) := by
    unfold ex; congr 1; ring
  rw [h1, h2]; unfold vB; push_cast; rw [Complex.cos]; ring

lemma conj_cB (y : ℝ) : conj (cB y) = 1 - ex (-y) := by
  simp [cB, conj_ex]


lemma norm_ex_sub_one (t : ℝ) : ‖ex t - 1‖ = 2 * |Real.sin (π * t)| := by
  rw [ex_sub_one, norm_mul, norm_mul, norm_mul, Complex.norm_exp, Complex.norm_real,
    Real.norm_eq_abs]
  simp

/-! ## 2. The Toeplitz symbol `κ_r` -/

variable {α : ℝ}

/-- `σ(s) = (-1)^s` for `s ≠ 0`, `σ(0) = 0`. -/
def sgn (s : ℤ) : ℂ := if s = 0 then 0 else (-1 : ℂ) ^ s

/-- The symbol `κ_r = 2πi (-1)^r / (e^{-2πirα} - 1)` of `K_N^g` (tex l. 1856).  For `r ≠ 0`
this is the paper's `π(-1)^{r-1} e^{πirα} / sin(πrα)` (`kap_eq`), it satisfies
`κ_{-r} = -conj κ_r` (`kap_neg`), and `κ_0 = 0` (division by zero). -/
def kap (α : ℝ) (r : ℤ) : ℂ := 2 * π * Complex.I * (-1 : ℂ) ^ r / (ex (r * α) - 1)

lemma kap_zero (α : ℝ) : kap α 0 = 0 := by simp [kap, ex_zero]

lemma sin_ne_of_irrational (hα : Irrational α) {r : ℤ} (hr : r ≠ 0) :
    Real.sin (π * (r * α)) ≠ 0 := by
  have := LaxPair.sin_ne_zero_of_irrational hα hr
  rwa [show π * α * r = π * (r * α) by ring] at this

lemma ex_sub_one_ne (hα : Irrational α) {r : ℤ} (hr : r ≠ 0) : ex (r * α) - 1 ≠ 0 := by
  rw [ex_sub_one]
  refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) ?_)
    (Complex.exp_ne_zero _)
  exact_mod_cast sin_ne_of_irrational hα hr

/-- The identity `κ_r (e^{-2πirα} - 1) = 2πi(-1)^r` (`r ≠ 0`) used in the paper (l. 1862). -/
lemma kap_mul (hα : Irrational α) (r : ℤ) :
    kap α r * (ex (r * α) - 1) = 2 * π * Complex.I * sgn r := by
  by_cases hr : r = 0
  · subst hr; simp [sgn, ex_zero]
  · rw [kap, div_mul_cancel₀ _ (ex_sub_one_ne hα hr), sgn, if_neg hr]

lemma neg_one_zpow_neg (r : ℤ) : (-1 : ℂ) ^ (-r) = (-1 : ℂ) ^ r := by
  rcases Int.even_or_odd r with h | h
  · rw [h.neg_one_zpow, h.neg.neg_one_zpow]
  · rw [h.neg_one_zpow, h.neg.neg_one_zpow]

lemma conj_neg_one_zpow (r : ℤ) : conj ((-1 : ℂ) ^ r) = (-1 : ℂ) ^ r := by
  rw [map_zpow₀]; simp

/-- `conj κ_r = -κ_{-r}`, i.e. `κ_{-r} = -conj κ_r` (tex l. 1857). -/
lemma conj_kap (r : ℤ) : conj (kap α r) = -kap α (-r) := by
  unfold kap
  rw [map_div₀, map_mul, map_sub, map_one, conj_ex, conj_neg_one_zpow, neg_one_zpow_neg]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat, Int.cast_neg, neg_mul]
  ring

lemma kap_neg (r : ℤ) : kap α (-r) = -conj (kap α r) := by rw [conj_kap]; ring

/-- `|κ_r| = π / |sin(πrα)|` (also for `r = 0`, both sides vanishing). -/
lemma norm_kap (α : ℝ) (r : ℤ) : ‖kap α r‖ = π / |Real.sin (π * (r * α))| := by
  rw [kap, norm_div, norm_ex_sub_one]
  have h1 : ‖(2 : ℂ) * π * Complex.I * (-1 : ℂ) ^ r‖ = 2 * π := by
    simp [norm_mul, norm_zpow, abs_of_pos Real.pi_pos]
  rw [h1]
  by_cases hs : Real.sin (π * (r * α)) = 0
  · simp [hs]
  · field_simp

lemma norm_kap_neg (r : ℤ) : ‖kap α (-r)‖ = ‖kap α r‖ := by
  rw [kap_neg, norm_neg, Complex.norm_conj]

/-- **The paper's formula** `κ_r = π(-1)^{r-1} e^{πirα} / sin(πrα)` for `r ≠ 0` (tex l. 1853). -/
theorem kap_eq (hα : Irrational α) {r : ℤ} (hr : r ≠ 0) :
    kap α r = π * (-1 : ℂ) ^ (r - 1) * Complex.exp (((π * (r * α) : ℝ) : ℂ) * Complex.I) /
      (Real.sin (π * (r * α)) : ℂ) := by
  have hs : (Real.sin (π * (r * α)) : ℂ) ≠ 0 := by exact_mod_cast sin_ne_of_irrational hα hr
  have hd := ex_sub_one_ne hα hr
  set z : ℂ := ((π * (r * α) : ℝ) : ℂ)
  have hfe : Complex.exp (z * Complex.I) * Complex.exp (-z * Complex.I) = 1 := by
    rw [← Complex.exp_add]; simp
  have hm : (-1 : ℂ) ^ (r - 1) = -(-1 : ℂ) ^ r := by
    rw [zpow_sub_one₀ (by norm_num : (-1 : ℂ) ≠ 0)]; simp
  rw [kap, div_eq_div_iff hd hs, hm, ex_sub_one]
  linear_combination (-(2 * π * Complex.I * (-1 : ℂ) ^ r * (Real.sin (π * (r * α)) : ℂ))) * hfe

/-! ## 3. The block `G_N(x)`, the matrix `K_N^g` and the error `E_N(x)` -/

/-- `c_m = c(x + mα)` (tex l. 1847). -/
def cm (α x : ℝ) (m : ℤ) : ℂ := cB (x + m * α)

/-- `v(x + mα)` as a complex number. -/
def vm (α x : ℝ) (m : ℤ) : ℂ := ((vB (x + m * α) : ℝ) : ℂ)

/-- **The Hermitian block `G_N(x)`** (tex l. 1848–1851): `(G_N)_{jj} = v(x+(j+1)α)`,
`(G_N)_{j,j+1} = c_{j+1}`, `(G_N)_{j+1,j} = conj c_{j+1}`, `0 ≤ j,k ≤ N-1`. -/
def GN (α x : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun j k =>
  if j = k then vm α x ((j : ℕ) + 1)
  else if (k : ℕ) = (j : ℕ) + 1 then cm α x ((j : ℕ) + 1)
  else if (j : ℕ) = (k : ℕ) + 1 then conj (cm α x ((k : ℕ) + 1))
  else 0

/-- **The skew-Hermitian Toeplitz matrix** `(K_N^g)_{jk} = κ_{k-j}` (tex l. 1858). -/
def KG (α : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun j k =>
  kap α (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ))

/-- **The error matrix `E_N(x)`** exactly as in the paper (tex l. 1866–1872):
`(E_N)_{jk} = 1_{k=0} c_0 κ_{-j-1} + 1_{k=N-1} conj(c_N) κ_{N-j} - 1_{j=0} conj(c_0) κ_{k+1}
 - 1_{j=N-1} c_N κ_{k-N}`. -/
def EG (α x : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun j k =>
  (if (k : ℕ) = 0 then cm α x 0 * kap α (-((j : ℕ) : ℤ) - 1) else 0) +
  (if (k : ℕ) = N - 1 then conj (cm α x N) * kap α ((N : ℤ) - ((j : ℕ) : ℤ)) else 0) -
  (if (j : ℕ) = 0 then conj (cm α x 0) * kap α (((k : ℕ) : ℤ) + 1) else 0) -
  (if (j : ℕ) = N - 1 then cm α x N * kap α (((k : ℕ) : ℤ) - N) else 0)

lemma KG_skew (α : ℝ) (N : ℕ) : (KG α N)ᴴ = -KG α N := by
  ext j k
  simp only [conjTranspose_apply, neg_apply, KG, of_apply, RCLike.star_def, conj_kap]
  congr 2; ring

lemma conj_vm (α x : ℝ) (m : ℤ) : conj (vm α x m) = vm α x m := by
  simp [vm, Complex.conj_ofReal]

lemma GN_isHermitian (α x : ℝ) (N : ℕ) : (GN α x N).IsHermitian := by
  refine IsHermitian.ext fun j k => ?_
  by_cases hjk : j = k
  · subst hjk; simp [GN, conj_vm]
  · have hkj : k ≠ j := fun h => hjk h.symm
    by_cases h1 : (k : ℕ) = (j : ℕ) + 1
    · have h2 : ¬ (j : ℕ) = (k : ℕ) + 1 := by omega
      simp only [GN, of_apply, if_neg hkj, if_neg hjk, if_pos h1, if_neg h2, RCLike.star_def,
        Complex.conj_conj]
    · by_cases h2 : (j : ℕ) = (k : ℕ) + 1
      · simp only [GN, of_apply, if_neg hkj, if_neg hjk, if_neg h1, if_pos h2, RCLike.star_def]
      · simp only [GN, of_apply, if_neg hkj, if_neg hjk, if_neg h1, if_neg h2, star_zero]

lemma EG_isHermitian (α x : ℝ) (N : ℕ) : (EG α x N).IsHermitian := by
  refine IsHermitian.ext fun j k => ?_
  simp only [EG, of_apply, RCLike.star_def, map_sub, map_add, apply_ite conj, map_zero,
    map_mul, Complex.conj_conj, conj_kap]
  have e1 : kap α (-(-((k : ℕ) : ℤ) - 1)) = kap α (((k : ℕ) : ℤ) + 1) := by congr 1; ring
  have e2 : kap α (-((N : ℤ) - ((k : ℕ) : ℤ))) = kap α (((k : ℕ) : ℤ) - N) := by congr 1; ring
  have e3 : kap α (-(((j : ℕ) : ℤ) + 1)) = kap α (-((j : ℕ) : ℤ) - 1) := by congr 1; ring
  have e4 : kap α (-(((j : ℕ) : ℤ) - N)) = kap α ((N : ℤ) - ((j : ℕ) : ℤ)) := by congr 1; ring
  rw [e1, e2, e3, e4]
  split_ifs <;> ring

/-! ## 4. The commutator identity `G_N' = [K_N^g, G_N] + E_N` -/

/-- Entries of `G_N` along a column (with `ℤ`-indices). -/
lemma mul_GN_col (φ : ℤ → ℂ) (α x : ℝ) {N : ℕ} (m k : Fin N) :
    φ ((m : ℕ) : ℤ) * GN α x N m k =
      (if ((m : ℕ) : ℤ) = (k : ℕ) then φ (k : ℕ) * vm α x ((k : ℕ) + 1) else 0) +
      (if ((m : ℕ) : ℤ) = ((k : ℕ) : ℤ) - 1 then φ (((k : ℕ) : ℤ) - 1) * cm α x (k : ℕ)
        else 0) +
      (if ((m : ℕ) : ℤ) = ((k : ℕ) : ℤ) + 1 then
        φ (((k : ℕ) : ℤ) + 1) * conj (cm α x (((k : ℕ) : ℤ) + 1)) else 0) := by
  simp only [GN, of_apply]
  by_cases h0 : m = k
  · subst h0
    rw [if_pos rfl, if_pos rfl, if_neg (show ¬ ((m : ℕ) : ℤ) = ((m : ℕ) : ℤ) - 1 by omega),
      if_neg (show ¬ ((m : ℕ) : ℤ) = ((m : ℕ) : ℤ) + 1 by omega)]
    ring
  · have h0' : ¬ ((m : ℕ) : ℤ) = (k : ℕ) := fun h => h0 (Fin.ext (by exact_mod_cast h))
    rw [if_neg h0, if_neg h0']
    by_cases h1 : (k : ℕ) = (m : ℕ) + 1
    · have hm : ((m : ℕ) : ℤ) = ((k : ℕ) : ℤ) - 1 := by omega
      rw [if_pos h1, if_pos hm, if_neg (show ¬ ((m : ℕ) : ℤ) = ((k : ℕ) : ℤ) + 1 by omega), hm,
        sub_add_cancel]
      ring
    · rw [if_neg h1, if_neg (show ¬ ((m : ℕ) : ℤ) = ((k : ℕ) : ℤ) - 1 by omega)]
      by_cases h2 : (m : ℕ) = (k : ℕ) + 1
      · have hm : ((m : ℕ) : ℤ) = ((k : ℕ) : ℤ) + 1 := by omega
        rw [if_pos h2, if_pos hm, hm]; ring
      · rw [if_neg h2, if_neg (show ¬ ((m : ℕ) : ℤ) = ((k : ℕ) : ℤ) + 1 by omega)]; ring

/-- Entries of `G_N` along a row (with `ℤ`-indices). -/
lemma GN_row_mul (φ : ℤ → ℂ) (α x : ℝ) {N : ℕ} (j m : Fin N) :
    GN α x N j m * φ ((m : ℕ) : ℤ) =
      (if ((m : ℕ) : ℤ) = (j : ℕ) then vm α x ((j : ℕ) + 1) * φ (j : ℕ) else 0) +
      (if ((m : ℕ) : ℤ) = ((j : ℕ) : ℤ) + 1 then
        cm α x (((j : ℕ) : ℤ) + 1) * φ (((j : ℕ) : ℤ) + 1) else 0) +
      (if ((m : ℕ) : ℤ) = ((j : ℕ) : ℤ) - 1 then
        conj (cm α x (j : ℕ)) * φ (((j : ℕ) : ℤ) - 1) else 0) := by
  simp only [GN, of_apply]
  by_cases h0 : j = m
  · subst h0
    rw [if_pos rfl, if_pos rfl, if_neg (show ¬ ((j : ℕ) : ℤ) = ((j : ℕ) : ℤ) + 1 by omega),
      if_neg (show ¬ ((j : ℕ) : ℤ) = ((j : ℕ) : ℤ) - 1 by omega)]
    ring
  · have h0' : ¬ ((m : ℕ) : ℤ) = (j : ℕ) := fun h => h0 (Fin.ext (by exact_mod_cast h.symm))
    rw [if_neg h0, if_neg h0']
    by_cases h1 : (m : ℕ) = (j : ℕ) + 1
    · have hm : ((m : ℕ) : ℤ) = ((j : ℕ) : ℤ) + 1 := by omega
      rw [if_pos h1, if_pos hm, if_neg (show ¬ ((m : ℕ) : ℤ) = ((j : ℕ) : ℤ) - 1 by omega), hm]
      ring
    · rw [if_neg h1, if_neg (show ¬ ((m : ℕ) : ℤ) = ((j : ℕ) : ℤ) + 1 by omega)]
      by_cases h2 : (j : ℕ) = (m : ℕ) + 1
      · have hm : ((m : ℕ) : ℤ) = ((j : ℕ) : ℤ) - 1 := by omega
        rw [if_pos h2, if_pos hm, hm, sub_add_cancel]; ring
      · rw [if_neg h2, if_neg (show ¬ ((m : ℕ) : ℤ) = ((j : ℕ) : ℤ) - 1 by omega)]; ring

lemma sum_fin_ite_const {N : ℕ} (t : ℤ) (c : ℂ) :
    ∑ m : Fin N, (if ((m : ℕ) : ℤ) = t then c else 0) = if 0 ≤ t ∧ t < N then c else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨t.toNat, by omega⟩ : Fin N)]
    · rw [if_pos (by simp; omega)]
    · intro b _ hb
      rw [if_neg]
      intro h'; apply hb; ext; simp; omega
    · simp
  · refine Finset.sum_eq_zero fun m _ => ?_
    rw [if_neg]
    have := m.isLt
    omega

/-- **Entries of the commutator** `[K_N^g, G_N(x)]` (four boundary-truncated terms). -/
lemma comm_apply (α x : ℝ) {N : ℕ} (j k : Fin N) :
    (KG α N * GN α x N - GN α x N * KG α N) j k =
      kap α (((k : ℕ) : ℤ) - (j : ℕ)) * vm α x ((k : ℕ) + 1) +
      (if ((k : ℕ) : ℤ) = 0 then 0 else
        kap α (((k : ℕ) : ℤ) - 1 - (j : ℕ)) * cm α x (k : ℕ)) +
      (if ((k : ℕ) : ℤ) = N - 1 then 0 else
        kap α (((k : ℕ) : ℤ) + 1 - (j : ℕ)) * conj (cm α x (((k : ℕ) : ℤ) + 1))) -
      (vm α x ((j : ℕ) + 1) * kap α (((k : ℕ) : ℤ) - (j : ℕ)) +
      (if ((j : ℕ) : ℤ) = N - 1 then 0 else
        cm α x (((j : ℕ) : ℤ) + 1) * kap α (((k : ℕ) : ℤ) - 1 - (j : ℕ))) +
      (if ((j : ℕ) : ℤ) = 0 then 0 else
        conj (cm α x (j : ℕ)) * kap α (((k : ℕ) : ℤ) + 1 - (j : ℕ)))) := by
  have hj := j.isLt
  have hk := k.isLt
  have h1 : (KG α N * GN α x N) j k = ∑ m : Fin N,
      ((if ((m : ℕ) : ℤ) = (k : ℕ) then
          kap α (((k : ℕ) : ℤ) - (j : ℕ)) * vm α x ((k : ℕ) + 1) else 0) +
        (if ((m : ℕ) : ℤ) = ((k : ℕ) : ℤ) - 1 then
          kap α (((k : ℕ) : ℤ) - 1 - (j : ℕ)) * cm α x (k : ℕ) else 0) +
        (if ((m : ℕ) : ℤ) = ((k : ℕ) : ℤ) + 1 then
          kap α (((k : ℕ) : ℤ) + 1 - (j : ℕ)) * conj (cm α x (((k : ℕ) : ℤ) + 1)) else 0)) := by
    rw [mul_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    exact mul_GN_col (fun t => kap α (t - (j : ℕ))) α x m k
  have h2 : (GN α x N * KG α N) j k = ∑ m : Fin N,
      ((if ((m : ℕ) : ℤ) = (j : ℕ) then
          vm α x ((j : ℕ) + 1) * kap α (((k : ℕ) : ℤ) - (j : ℕ)) else 0) +
        (if ((m : ℕ) : ℤ) = ((j : ℕ) : ℤ) + 1 then
          cm α x (((j : ℕ) : ℤ) + 1) * kap α (((k : ℕ) : ℤ) - (((j : ℕ) : ℤ) + 1)) else 0) +
        (if ((m : ℕ) : ℤ) = ((j : ℕ) : ℤ) - 1 then
          conj (cm α x (j : ℕ)) * kap α (((k : ℕ) : ℤ) - (((j : ℕ) : ℤ) - 1)) else 0)) := by
    rw [mul_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    exact GN_row_mul (fun t => kap α (((k : ℕ) : ℤ) - t)) α x j m
  rw [Matrix.sub_apply, h1, h2]
  simp only [Finset.sum_add_distrib, sum_fin_ite_const]
  have e1 : ((k : ℕ) : ℤ) - (((j : ℕ) : ℤ) + 1) = ((k : ℕ) : ℤ) - 1 - (j : ℕ) := by ring
  have e2 : ((k : ℕ) : ℤ) - (((j : ℕ) : ℤ) - 1) = ((k : ℕ) : ℤ) + 1 - (j : ℕ) := by ring
  have c1 : (0 ≤ ((k : ℕ) : ℤ) - 1 ∧ ((k : ℕ) : ℤ) - 1 < N) ↔ ¬ (((k : ℕ) : ℤ) = 0) := by omega
  have c2 : (0 ≤ ((k : ℕ) : ℤ) + 1 ∧ ((k : ℕ) : ℤ) + 1 < N) ↔ ¬ (((k : ℕ) : ℤ) = N - 1) := by
    omega
  have c3 : (0 ≤ ((j : ℕ) : ℤ) + 1 ∧ ((j : ℕ) : ℤ) + 1 < N) ↔ ¬ (((j : ℕ) : ℤ) = N - 1) := by
    omega
  have c4 : (0 ≤ ((j : ℕ) : ℤ) - 1 ∧ ((j : ℕ) : ℤ) - 1 < N) ↔ ¬ (((j : ℕ) : ℤ) = 0) := by omega
  have c5 : 0 ≤ ((k : ℕ) : ℤ) ∧ ((k : ℕ) : ℤ) < N := by omega
  have c6 : 0 ≤ ((j : ℕ) : ℤ) ∧ ((j : ℕ) : ℤ) < N := by omega
  simp only [c1, c2, c3, c4, if_pos c5, if_pos c6, ite_not]
  rw [e1, e2]

/-- The raw boundary error (terms cut off at the indices `-1` and `N`). -/
def EGr (α x : ℝ) (N : ℕ) (J K : ℤ) : ℂ :=
  (if K = 0 then kap α (K - 1 - J) * cm α x K else 0) +
  (if K = N - 1 then kap α (K + 1 - J) * conj (cm α x (K + 1)) else 0) -
  (if J = N - 1 then cm α x (J + 1) * kap α (K - 1 - J) else 0) -
  (if J = 0 then conj (cm α x J) * kap α (K + 1 - J) else 0)

lemma EG_eq_EGr (α x : ℝ) {N : ℕ} (j k : Fin N) :
    EG α x N j k = EGr α x N (j : ℕ) (k : ℕ) := by
  have hj := j.isLt
  have hk := k.isLt
  simp only [EG, EGr, of_apply]
  have a1 : (if (k : ℕ) = 0 then cm α x 0 * kap α (-((j : ℕ) : ℤ) - 1) else 0) =
      (if ((k : ℕ) : ℤ) = 0 then kap α (((k : ℕ) : ℤ) - 1 - (j : ℕ)) * cm α x (k : ℕ)
        else 0) := by
    by_cases h : (k : ℕ) = 0
    · have hK : ((k : ℕ) : ℤ) = 0 := by simp [h]
      rw [if_pos h, if_pos hK, hK, mul_comm]; congr 2; ring
    · rw [if_neg h, if_neg (by omega)]
  have a2 : (if (k : ℕ) = N - 1 then conj (cm α x N) * kap α ((N : ℤ) - ((j : ℕ) : ℤ)) else 0) =
      (if ((k : ℕ) : ℤ) = N - 1 then
        kap α (((k : ℕ) : ℤ) + 1 - (j : ℕ)) * conj (cm α x (((k : ℕ) : ℤ) + 1)) else 0) := by
    by_cases h : (k : ℕ) = N - 1
    · have hK : ((k : ℕ) : ℤ) + 1 = N := by omega
      rw [if_pos h, if_pos (by omega), hK, mul_comm]
    · rw [if_neg h, if_neg (by omega)]
  have a3 : (if (j : ℕ) = 0 then conj (cm α x 0) * kap α (((k : ℕ) : ℤ) + 1) else 0) =
      (if ((j : ℕ) : ℤ) = 0 then conj (cm α x (j : ℕ)) * kap α (((k : ℕ) : ℤ) + 1 - (j : ℕ))
        else 0) := by
    by_cases h : (j : ℕ) = 0
    · have hJ : ((j : ℕ) : ℤ) = 0 := by simp [h]
      rw [if_pos h, if_pos hJ, hJ, sub_zero]
    · rw [if_neg h, if_neg (by omega)]
  have a4 : (if (j : ℕ) = N - 1 then cm α x N * kap α (((k : ℕ) : ℤ) - N) else 0) =
      (if ((j : ℕ) : ℤ) = N - 1 then cm α x (((j : ℕ) : ℤ) + 1) * kap α (((k : ℕ) : ℤ) - 1 - (j : ℕ))
        else 0) := by
    by_cases h : (j : ℕ) = N - 1
    · have hJ : ((j : ℕ) : ℤ) + 1 = N := by omega
      rw [if_pos h, if_pos (by omega), hJ]; congr 2; omega
    · rw [if_neg h, if_neg (by omega)]
  rw [a1, a2, a3, a4]; ring

/-- The derivative of the (doubly infinite) block in `ℤ`-indices. -/
def dG (α x : ℝ) (J K : ℤ) : ℂ :=
  (if K = J then 2 * π * Complex.I * ex (x + ((J + 1 : ℤ) : ℝ) * α) -
    2 * π * Complex.I * ex (-(x + ((J + 1 : ℤ) : ℝ) * α)) else 0) +
  (if K = J + 1 then 2 * π * Complex.I * ex (x + ((J + 1 : ℤ) : ℝ) * α) else 0) +
  (if J = K + 1 then -(2 * π * Complex.I) * ex (-(x + ((K + 1 : ℤ) : ℝ) * α)) else 0)

lemma sgn_of_ne {s : ℤ} (h : s ≠ 0) : sgn s = (-1 : ℂ) ^ s := by simp [sgn, h]

lemma sgn_sub_one {s : ℤ} (h : s ≠ 0) (h' : s - 1 ≠ 0) : sgn (s - 1) = -sgn s := by
  rw [sgn_of_ne h, sgn_of_ne h', zpow_sub_one₀ (by norm_num : (-1 : ℂ) ≠ 0)]; simp

lemma sgn_add_one {s : ℤ} (h : s ≠ 0) (h' : s + 1 ≠ 0) : sgn (s + 1) = -sgn s := by
  rw [sgn_of_ne h, sgn_of_ne h', zpow_add_one₀ (by norm_num : (-1 : ℂ) ≠ 0)]; simp

/-- **The core identity** of the commutator computation (l. 1859–1864): in the bulk,
`G' = κ_r (v_{k+1} - v_{j+1}) + κ_{r-1}(c_k - c_{j+1}) + κ_{r+1}(conj c_{k+1} - conj c_j)`,
`r = k - j`; it rests on `κ_s (e^{-2πisα} - 1) = 2πi(-1)^s`. -/
lemma core (hα : Irrational α) (x : ℝ) (J K : ℤ) :
    dG α x J K = kap α (K - J) * (vm α x (K + 1) - vm α x (J + 1)) +
      kap α (K - 1 - J) * (cm α x K - cm α x (J + 1)) +
      kap α (K + 1 - J) * (conj (cm α x (K + 1)) - conj (cm α x J)) := by
  simp only [vm, cm, vB_eq, cB, map_sub, map_one, conj_ex]
  have r1 : ex (x + ((K + 1 : ℤ) : ℝ) * α) =
      ex (x + ((J + 1 : ℤ) : ℝ) * α) * ex (((K - J : ℤ) : ℝ) * α) :=
    ex_shift (by push_cast; ring)
  have r2 : ex (-(x + ((J + 1 : ℤ) : ℝ) * α)) =
      ex (-(x + ((K + 1 : ℤ) : ℝ) * α)) * ex (((K - J : ℤ) : ℝ) * α) :=
    ex_shift (by push_cast; ring)
  have r3 : ex (x + ((K : ℤ) : ℝ) * α) =
      ex (x + ((J + 1 : ℤ) : ℝ) * α) * ex (((K - 1 - J : ℤ) : ℝ) * α) :=
    ex_shift (by push_cast; ring)
  have r4 : ex (-(x + ((J : ℤ) : ℝ) * α)) =
      ex (-(x + ((K + 1 : ℤ) : ℝ) * α)) * ex (((K + 1 - J : ℤ) : ℝ) * α) :=
    ex_shift (by push_cast; ring)
  have h0 := kap_mul hα (K - J)
  have h1 := kap_mul hα (K - 1 - J)
  have h2 := kap_mul hα (K + 1 - J)
  unfold dG
  rw [r1, r2, r3, r4]
  set A := ex (x + ((J + 1 : ℤ) : ℝ) * α)
  set B := ex (-(x + ((K + 1 : ℤ) : ℝ) * α))
  set T : ℂ := 2 * π * Complex.I
  by_cases e0 : K = J
  · have s0 : sgn (K - J) = 0 := by simp [sgn, e0]
    have s1 : sgn (K - 1 - J) = -1 := by rw [show K - 1 - J = -1 by omega]; simp [sgn]
    have s2 : sgn (K + 1 - J) = -1 := by rw [show K + 1 - J = 1 by omega]; simp [sgn]
    have he : ex (((K - J : ℤ) : ℝ) * α) = 1 := by rw [show K - J = 0 by omega]; simp [ex_zero]
    rw [s0] at h0; rw [s1] at h1; rw [s2] at h2
    rw [if_pos e0, if_neg (by omega), if_neg (by omega)]
    linear_combination (A - B) * h0 + A * h1 - B * h2 - T * B * he
  by_cases e1 : K = J + 1
  · have s0 : sgn (K - J) = -1 := by rw [show K - J = 1 by omega]; simp [sgn]
    have s1 : sgn (K - 1 - J) = 0 := by rw [show K - 1 - J = 0 by omega]; simp [sgn]
    have s2 : sgn (K + 1 - J) = 1 := by rw [show K + 1 - J = 2 by omega]; simp [sgn]
    rw [s0] at h0; rw [s1] at h1; rw [s2] at h2
    rw [if_neg e0, if_pos e1, if_neg (by omega)]
    linear_combination (A - B) * h0 + A * h1 - B * h2
  by_cases e2 : J = K + 1
  · have s0 : sgn (K - J) = -1 := by rw [show K - J = -1 by omega]; simp [sgn]
    have s1 : sgn (K - 1 - J) = 1 := by rw [show K - 1 - J = -2 by omega]; simp [sgn]
    have s2 : sgn (K + 1 - J) = 0 := by rw [show K + 1 - J = 0 by omega]; simp [sgn]
    rw [s0] at h0; rw [s1] at h1; rw [s2] at h2
    rw [if_neg e0, if_neg e1, if_pos e2]
    linear_combination (A - B) * h0 + A * h1 - B * h2
  · have hσ1 : sgn (K - 1 - J) = -sgn (K - J) := by
      rw [show K - 1 - J = (K - J) - 1 by ring]; exact sgn_sub_one (by omega) (by omega)
    have hσ2 : sgn (K + 1 - J) = -sgn (K - J) := by
      rw [show K + 1 - J = (K - J) + 1 by ring]; exact sgn_add_one (by omega) (by omega)
    rw [if_neg e0, if_neg e1, if_neg e2]
    linear_combination (A - B) * h0 + A * h1 - B * h2 + A * T * hσ1 - B * T * hσ2

lemma hasDerivAt_ex_add (a x : ℝ) :
    HasDerivAt (fun y => ex (y + a)) (-(2 * π * Complex.I) * ex (x + a)) x := by
  have h : HasDerivAt (fun y : ℝ => ((y + a : ℝ) : ℂ)) 1 x :=
    ((hasDerivAt_id x).add_const a).ofReal_comp
  have := (h.const_mul (-(2 * π * Complex.I))).cexp
  unfold ex
  convert this using 1; ring

lemma hasDerivAt_ex_neg_add (a x : ℝ) :
    HasDerivAt (fun y => ex (-(y + a))) (2 * π * Complex.I * ex (-(x + a))) x := by
  have h : HasDerivAt (fun y : ℝ => ((-(y + a) : ℝ) : ℂ)) (-1 : ℝ) x :=
    ((hasDerivAt_id x).add_const a).neg.ofReal_comp
  have := (h.const_mul (-(2 * π * Complex.I))).cexp
  unfold ex
  convert this using 1; push_cast; ring

/-- The entries of `G_N(y)` are differentiable in `y` with derivative `dG`. -/
lemma hasDerivAt_GN_entry (α x : ℝ) {N : ℕ} (j k : Fin N) :
    HasDerivAt (fun y => GN α y N j k) (dG α x (j : ℕ) (k : ℕ)) x := by
  by_cases h0 : j = k
  · subst h0
    have e : (fun y => GN α y N j j) = fun y =>
        -(ex (y + ((((j : ℕ) : ℤ) + 1 : ℤ) : ℝ) * α) +
          ex (-(y + ((((j : ℕ) : ℤ) + 1 : ℤ) : ℝ) * α))) := by
      funext y; simp only [GN, of_apply, if_true, vm, vB_eq]
    rw [e]
    refine ((hasDerivAt_ex_add _ x).add (hasDerivAt_ex_neg_add _ x)).neg.congr_deriv ?_
    simp only [dG, if_true, if_neg (show ¬ (((j : ℕ) : ℤ) = ((j : ℕ) : ℤ) + 1) by omega)]
    ring
  · by_cases h1 : (k : ℕ) = (j : ℕ) + 1
    · have e : (fun y => GN α y N j k) = fun y =>
          1 - ex (y + ((((j : ℕ) : ℤ) + 1 : ℤ) : ℝ) * α) := by
        funext y; simp only [GN, of_apply, if_neg h0, if_pos h1, cm, cB]
      rw [e]
      refine ((hasDerivAt_ex_add _ x).const_sub 1).congr_deriv ?_
      simp only [dG, if_neg (show ¬ (((k : ℕ) : ℤ) = ((j : ℕ) : ℤ)) by omega),
        if_pos (show ((k : ℕ) : ℤ) = ((j : ℕ) : ℤ) + 1 by omega),
        if_neg (show ¬ (((j : ℕ) : ℤ) = ((k : ℕ) : ℤ) + 1) by omega)]
      ring
    · by_cases h2 : (j : ℕ) = (k : ℕ) + 1
      · have e : (fun y => GN α y N j k) = fun y =>
            1 - ex (-(y + ((((k : ℕ) : ℤ) + 1 : ℤ) : ℝ) * α)) := by
          funext y; simp only [GN, of_apply, if_neg h0, if_neg h1, if_pos h2, cm, conj_cB]
        rw [e]
        refine ((hasDerivAt_ex_neg_add _ x).const_sub 1).congr_deriv ?_
        simp only [dG, if_neg (show ¬ (((k : ℕ) : ℤ) = ((j : ℕ) : ℤ)) by omega),
          if_neg (show ¬ (((k : ℕ) : ℤ) = ((j : ℕ) : ℤ) + 1) by omega),
          if_pos (show ((j : ℕ) : ℤ) = ((k : ℕ) : ℤ) + 1 by omega)]
        ring
      · have e : (fun y => GN α y N j k) = fun _ => 0 := by
          funext y; simp only [GN, of_apply, if_neg h0, if_neg h1, if_neg h2]
        rw [e]
        refine (hasDerivAt_const x (0 : ℂ)).congr_deriv ?_
        have h0' : ((k : ℕ) : ℤ) ≠ (j : ℕ) := fun h => h0 (Fin.ext (by omega))
        simp only [dG, if_neg h0', if_neg (show ¬ (((k : ℕ) : ℤ) = ((j : ℕ) : ℤ) + 1) by omega),
          if_neg (show ¬ (((j : ℕ) : ℤ) = ((k : ℕ) : ℤ) + 1) by omega)]
        ring

/-- The entrywise commutator identity: `G_N' = [K_N^g, G_N] + E_N`. -/
lemma dG_eq (hα : Irrational α) (x : ℝ) {N : ℕ} (j k : Fin N) :
    dG α x (j : ℕ) (k : ℕ) = (KG α N * GN α x N - GN α x N * KG α N + EG α x N) j k := by
  rw [Matrix.add_apply, comm_apply, EG_eq_EGr, core hα, EGr]
  split_ifs <;> ring

/-- **The graphene commutator identity** (tex l. 1859–1873):
`G_N'(x) = [K_N^g, G_N(x)] + E_N(x)` for irrational `α`, every `N` and `x`. -/
theorem commutator_identity (hα : Irrational α) (N : ℕ) (x : ℝ) :
    HasDerivAt (fun y => GN α y N) (KG α N * GN α x N - GN α x N * KG α N + EG α x N) x := by
  refine (hasDerivAt_pi (φ := fun y => GN α y N)).2 fun j => ?_
  refine (hasDerivAt_pi (φ := fun y => GN α y N j)).2 fun k => ?_
  rw [← dG_eq hα x j k]
  exact hasDerivAt_GN_entry α x j k


/-! ## 5. Rank and trace-norm bounds for `E_N^± = E_N ∓ τ [K_N^g, P_N]` -/

/-- `∑_{r=0}^{N-1} |κ_r|^2` (the `r = 0` term vanishes). -/
def Sk (α : ℝ) (N : ℕ) : ℝ := ∑ r ∈ Finset.range N, ‖kap α (r : ℤ)‖ ^ 2

lemma Sk_nonneg (α : ℝ) (N : ℕ) : 0 ≤ Sk α N := Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **`∑_{r=1}^{N-1} |κ_r|^2 ≤ 4π² q_n²`** for `N ≤ q_n` (tex l. 1893–1904), from
`∑_{k=1}^{L} 1/sin²(πkα) ≤ 4 q_n²` (`CAH.sum_inv_sin_sq_le`, `L < q_n`). -/
lemma Sk_le (hα : Irrational α) {n : ℕ} (hn : 1 ≤ n) {N : ℕ} (hN1 : 1 ≤ N)
    (hNq : N ≤ qN α n) : Sk α N ≤ 4 * π ^ 2 * q α n ^ 2 := by
  have hL : N - 1 < qN α n := by omega
  have h := CAH.sum_inv_sin_sq_le hα hn hL
  have e : ∀ r : ℕ, ‖kap α (r : ℤ)‖ ^ 2 = π ^ 2 * (1 / Real.sin (π * r * α) ^ 2) := by
    intro r
    rw [norm_kap, div_pow, sq_abs, Int.cast_natCast, mul_assoc]; ring
  have hr : Finset.range N = insert 0 (Finset.Icc 1 (N - 1)) := by
    ext r; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
  unfold Sk
  simp only [e]
  rw [← Finset.mul_sum, hr, Finset.sum_insert (by simp)]
  have h0 : 1 / Real.sin (π * ((0 : ℕ) : ℝ) * α) ^ 2 = 0 := by simp
  rw [h0, zero_add]
  calc π ^ 2 * ∑ k ∈ Finset.Icc 1 (N - 1), 1 / Real.sin (π * k * α) ^ 2
      ≤ π ^ 2 * (4 * q α n ^ 2) := by gcongr
    _ = 4 * π ^ 2 * q α n ^ 2 := by ring

/-- Sums over `Fin N` along an injection into `{0, …, N-1}` are bounded by the full sum. -/
lemma sum_le_range_of_inj {N : ℕ} (s : Finset (Fin N)) (φ : Fin N → ℕ)
    (hφ : ∀ j ∈ s, φ j < N) (hinj : ∀ i ∈ s, ∀ j ∈ s, φ i = φ j → i = j) (f : ℕ → ℝ)
    (hf : ∀ r, 0 ≤ f r) : ∑ j ∈ s, f (φ j) ≤ ∑ r ∈ Finset.range N, f r := by
  rw [← Finset.sum_image (by intro i hi j hj h; exact hinj i hi j hj h)]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _ => hf _)
  intro r hr
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hr
  exact Finset.mem_range.2 (hφ j hj)

/-- `∑_j |κ_{k-j}|^2 ≤ 2 ∑_{r<N} |κ_r|^2`. -/
lemma sum_col_kap (α : ℝ) {N : ℕ} (k : Fin N) :
    ∑ j : Fin N, ‖kap α (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ))‖ ^ 2 ≤ 2 * Sk α N := by
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin N => (j : ℕ) < k)]
  have h1 : ∑ j ∈ Finset.univ.filter (fun j : Fin N => (j : ℕ) < k),
      ‖kap α (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ))‖ ^ 2 ≤ Sk α N := by
    have e : ∀ j ∈ Finset.univ.filter (fun j : Fin N => (j : ℕ) < k),
        ‖kap α (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ))‖ ^ 2 =
          (fun r : ℕ => ‖kap α (r : ℤ)‖ ^ 2) ((fun j : Fin N => (k : ℕ) - (j : ℕ)) j) := by
      intro j hj
      simp only [Finset.mem_filter] at hj
      simp only [Nat.cast_sub hj.2.le]
    rw [Finset.sum_congr rfl e]
    have := sum_le_range_of_inj (Finset.univ.filter (fun j : Fin N => (j : ℕ) < k))
      (fun j : Fin N => (k : ℕ) - (j : ℕ)) (fun j _ => by have := k.isLt; omega)
      (by
        intro i hi j hj h
        simp only [Finset.mem_filter] at hi hj
        exact Fin.ext (by omega))
      (fun r : ℕ => ‖kap α (r : ℤ)‖ ^ 2) (fun _ => sq_nonneg _)
    exact this
  have h2 : ∑ j ∈ Finset.univ.filter (fun j : Fin N => ¬ (j : ℕ) < k),
      ‖kap α (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ))‖ ^ 2 ≤ Sk α N := by
    have e : ∀ j ∈ Finset.univ.filter (fun j : Fin N => ¬ (j : ℕ) < k),
        ‖kap α (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ))‖ ^ 2 =
          (fun r : ℕ => ‖kap α (r : ℤ)‖ ^ 2) ((fun j : Fin N => (j : ℕ) - (k : ℕ)) j) := by
      intro j hj
      simp only [Finset.mem_filter, not_lt] at hj
      simp only
      rw [← norm_kap_neg, Nat.cast_sub hj.2]; congr 3; ring
    rw [Finset.sum_congr rfl e]
    have := sum_le_range_of_inj (Finset.univ.filter (fun j : Fin N => ¬ (j : ℕ) < k))
      (fun j : Fin N => (j : ℕ) - (k : ℕ)) (fun j _ => by have := j.isLt; omega)
      (by
        intro i hi j hj h
        simp only [Finset.mem_filter, not_lt] at hi hj
        exact Fin.ext (by omega))
      (fun r : ℕ => ‖kap α (r : ℤ)‖ ^ 2) (fun _ => sq_nonneg _)
    exact this
  linarith

lemma sum_ite_val_le {N : ℕ} (a : ℕ) (f : Fin N → ℝ) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ j : Fin N, (j : ℕ) = a → f j ≤ M) :
    ∑ j : Fin N, (if (j : ℕ) = a then f j else 0) ≤ M := by
  by_cases ha : a < N
  · rw [Finset.sum_eq_single (⟨a, ha⟩ : Fin N)]
    · simp only [if_true]; exact hM _ rfl
    · intro b _ hb
      rw [if_neg]; intro h; exact hb (Fin.ext h)
    · simp
  · rw [Finset.sum_eq_zero]
    · exact hM0
    · intro j _
      rw [if_neg]; have := j.isLt; omega

lemma dsum_col_le {N : ℕ} (a : ℕ) (F : Fin N → ℝ) (hF : ∀ j, 0 ≤ F j) :
    ∑ j : Fin N, ∑ k : Fin N, (if (k : ℕ) = a then F j else 0) ≤ ∑ j, F j :=
  Finset.sum_le_sum fun j _ => sum_ite_val_le a (fun _ => F j) (hF j) (fun _ _ => le_rfl)

lemma dsum_row_le {N : ℕ} (a : ℕ) (F : Fin N → ℝ) (hF : ∀ j, 0 ≤ F j) :
    ∑ j : Fin N, ∑ k : Fin N, (if (j : ℕ) = a then F k else 0) ≤ ∑ k, F k := by
  rw [Finset.sum_comm]; exact dsum_col_le a F hF

lemma sum_F1_le (α : ℝ) (N : ℕ) :
    ∑ j : Fin N, (if (j : ℕ) = N - 1 then 0 else ‖kap α (((j : ℕ) : ℤ) + 1)‖ ^ 2) ≤ Sk α N := by
  have e0 : ∑ j : Fin N, (if (j : ℕ) = N - 1 then 0 else ‖kap α (((j : ℕ) : ℤ) + 1)‖ ^ 2) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin N => ¬ (j : ℕ) = N - 1),
        (fun r : ℕ => ‖kap α (r : ℤ)‖ ^ 2) ((fun j : Fin N => (j : ℕ) + 1) j) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> first | rfl | (push_cast; rfl)
  rw [e0]
  have := sum_le_range_of_inj (Finset.univ.filter (fun j : Fin N => ¬ (j : ℕ) = N - 1))
    (fun j : Fin N => (j : ℕ) + 1)
    (fun j hj => by simp only [Finset.mem_filter] at hj; have := j.isLt; omega)
    (fun i _ j _ h => Fin.ext (by omega))
    (fun r : ℕ => ‖kap α (r : ℤ)‖ ^ 2) (fun _ => sq_nonneg _)
  exact this

lemma sum_F2_le (α : ℝ) (N : ℕ) :
    ∑ j : Fin N, (if (j : ℕ) = 0 then 0 else ‖kap α ((N : ℤ) - ((j : ℕ) : ℤ))‖ ^ 2) ≤
      Sk α N := by
  have e0 : ∑ j : Fin N, (if (j : ℕ) = 0 then 0 else ‖kap α ((N : ℤ) - ((j : ℕ) : ℤ))‖ ^ 2) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin N => ¬ (j : ℕ) = 0),
        (fun r : ℕ => ‖kap α (r : ℤ)‖ ^ 2) ((fun j : Fin N => N - (j : ℕ)) j) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs
    · rfl
    · simp only [Nat.cast_sub j.isLt.le]
  rw [e0]
  have := sum_le_range_of_inj (Finset.univ.filter (fun j : Fin N => ¬ (j : ℕ) = 0))
    (fun j : Fin N => N - (j : ℕ))
    (fun j hj => by simp only [Finset.mem_filter] at hj; have := j.isLt; omega)
    (fun i _ j _ h => by
      have := i.isLt; have := j.isLt; exact Fin.ext (by omega))
    (fun r : ℕ => ‖kap α (r : ℤ)‖ ^ 2) (fun _ => sq_nonneg _)
  exact this

/-- The diagonal boundary projection. -/
def Pd (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  diagonal fun i => if (i : ℕ) = 0 ∨ (i : ℕ) = N - 1 then 1 else 0

lemma Pd_eq_bdryProj {N : ℕ} (hN : 2 ≤ N) : Pd N = Flow.bdryProj N := by
  rw [← BlockCover.PN_eq_bdryProj hN]
  ext i k
  simp only [Pd, BlockCover.toC_apply, LaxPair.PN, diagonal_apply]
  split_ifs <;> simp

/-- The pieces of `E_N`: the opposite corners, which must be combined (tex l. 1874–1879). -/
def cornerA (α x : ℝ) (N : ℕ) (j k : Fin N) : ℂ :=
  (if (j : ℕ) = 0 then (if (k : ℕ) = N - 1 then
    conj (cm α x N) * kap α ((N : ℤ) - ((j : ℕ) : ℤ)) -
      conj (cm α x 0) * kap α (((k : ℕ) : ℤ) + 1) else 0) else 0) +
  (if (j : ℕ) = N - 1 then (if (k : ℕ) = 0 then
    cm α x 0 * kap α (-((j : ℕ) : ℤ) - 1) - cm α x N * kap α (((k : ℕ) : ℤ) - N) else 0) else 0)

/-- The column-`0` piece of `E_N` (without the corner). -/
def a0 (α x : ℝ) (N : ℕ) (j k : Fin N) : ℂ :=
  if (k : ℕ) = 0 then (if (j : ℕ) = N - 1 then 0 else
    cm α x 0 * kap α (-((j : ℕ) : ℤ) - 1)) else 0
/-- The row-`0` piece of `E_N` (without the corner). -/
def b0 (α x : ℝ) (N : ℕ) (j k : Fin N) : ℂ :=
  if (j : ℕ) = 0 then (if (k : ℕ) = N - 1 then 0 else
    conj (cm α x 0) * kap α (((k : ℕ) : ℤ) + 1)) else 0
/-- The column-`(N-1)` piece of `E_N` (without the corner). -/
def aN (α x : ℝ) (N : ℕ) (j k : Fin N) : ℂ :=
  if (k : ℕ) = N - 1 then (if (j : ℕ) = 0 then 0 else
    conj (cm α x N) * kap α ((N : ℤ) - ((j : ℕ) : ℤ))) else 0
/-- The row-`(N-1)` piece of `E_N` (without the corner). -/
def bN (α x : ℝ) (N : ℕ) (j k : Fin N) : ℂ :=
  if (j : ℕ) = N - 1 then (if (k : ℕ) = 0 then 0 else
    cm α x N * kap α (((k : ℕ) : ℤ) - N)) else 0

lemma EG_split {N : ℕ} (hN : 2 ≤ N) (α x : ℝ) (j k : Fin N) :
    EG α x N j k = cornerA α x N j k + a0 α x N j k - b0 α x N j k + aN α x N j k -
      bN α x N j k := by
  simp only [EG, of_apply, cornerA, a0, b0, aN, bN]
  split_ifs <;> first | ring | (exfalso; omega)

lemma norm_cm (α x : ℝ) (m : ℤ) : ‖cm α x m‖ = 2 * |Real.sin (π * (x + m * α))| := by
  rw [cm, cB, ← norm_neg, neg_sub, norm_ex_sub_one]

lemma norm_conj_sub_le (hα : Irrational α) (x : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ‖kap α N * (conj (cm α x N) - conj (cm α x 0))‖ ≤ 2 * π := by
  have hN0 : (N : ℤ) ≠ 0 := by omega
  have hs := sin_ne_of_irrational hα hN0
  have hs' : |Real.sin (π * (((N : ℤ) : ℝ) * α))| ≠ 0 := abs_ne_zero.2 hs
  have e : conj (cm α x N) - conj (cm α x 0) = ex (-x) * -(ex (-((N : ℤ) * α)) - 1) := by
    simp only [cm, conj_cB, Int.cast_zero, zero_mul, add_zero]
    rw [show -(x + ((N : ℤ) : ℝ) * α) = -x + -(((N : ℤ) : ℝ) * α) by ring, ex_add]; ring
  rw [e]
  calc ‖kap α N * (ex (-x) * -(ex (-((N : ℤ) * α)) - 1))‖
      = ‖kap α N‖ * (‖ex (-x)‖ * ‖ex (-((N : ℤ) * α)) - 1‖) := by
        rw [norm_mul, norm_mul, norm_neg]
    _ = π / |Real.sin (π * (((N : ℤ) : ℝ) * α))| *
          (1 * (2 * |Real.sin (π * (((N : ℤ) : ℝ) * α))|)) := by
        rw [norm_ex, norm_ex_sub_one, norm_kap,
          show π * -(((N : ℤ) : ℝ) * α) = -(π * (((N : ℤ) : ℝ) * α)) by ring, Real.sin_neg,
          abs_neg]
    _ = 2 * π := by
        rw [one_mul, div_mul_eq_mul_div, div_eq_iff hs']; ring
    _ ≤ 2 * π := le_rfl

lemma norm_sub_conj_le (hα : Irrational α) (x : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ‖kap α (-(N : ℤ)) * (cm α x 0 - cm α x N)‖ ≤ 2 * π := by
  have hN0 : (N : ℤ) ≠ 0 := by omega
  have hs := sin_ne_of_irrational hα hN0
  have hs' : |Real.sin (π * (((N : ℤ) : ℝ) * α))| ≠ 0 := abs_ne_zero.2 hs
  have e : cm α x 0 - cm α x N = ex x * (ex ((N : ℤ) * α) - 1) := by
    simp only [cm, cB, Int.cast_zero, zero_mul, add_zero]
    rw [ex_add]; ring
  rw [e]
  calc ‖kap α (-(N : ℤ)) * (ex x * (ex ((N : ℤ) * α) - 1))‖
      = ‖kap α (N : ℤ)‖ * (‖ex x‖ * ‖ex ((N : ℤ) * α) - 1‖) := by
        rw [norm_mul, norm_mul, norm_kap_neg]
    _ = π / |Real.sin (π * (((N : ℤ) : ℝ) * α))| *
          (1 * (2 * |Real.sin (π * (((N : ℤ) : ℝ) * α))|)) := by
        rw [norm_ex, norm_ex_sub_one, norm_kap]
    _ = 2 * π := by
        rw [one_mul, div_mul_eq_mul_div, div_eq_iff hs']; ring
    _ ≤ 2 * π := le_rfl

/-- **The corner value** (tex l. 1876–1879):
`(E_N)_{0,N-1} = κ_N (conj c_N - conj c_0) = 2πi(-1)^N e^{2πi(x+Nα)}`. -/
theorem corner_eq (hα : Irrational α) (x : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    kap α N * (conj (cm α x N) - conj (cm α x 0)) =
      2 * π * Complex.I * (-1 : ℂ) ^ (N : ℤ) * ex (-(x + N * α)) := by
  have hN0 : (N : ℤ) ≠ 0 := by omega
  have hk := kap_mul hα (N : ℤ)
  rw [sgn_of_ne hN0] at hk
  have e : conj (cm α x N) - conj (cm α x 0) =
      ex (-(x + N * α)) * (ex ((N : ℤ) * α) - 1) := by
    simp only [cm, conj_cB, Int.cast_zero, zero_mul, add_zero, Int.cast_natCast]
    have h1 : ex (-x) = ex (-(x + N * α)) * ex (N * α) := ex_shift (by ring)
    rw [h1]; ring
  rw [e]
  linear_combination ex (-(x + N * α)) * hk

lemma cornerA_sq_le (hα : Irrational α) (x : ℝ) {N : ℕ} (hN : 2 ≤ N) (j k : Fin N) :
    ‖cornerA α x N j k‖ ^ 2 ≤
      (if (j : ℕ) = 0 then (if (k : ℕ) = N - 1 then 4 * π ^ 2 else 0) else 0) +
      (if (j : ℕ) = N - 1 then (if (k : ℕ) = 0 then 4 * π ^ 2 else 0) else 0) := by
  have hpi := Real.pi_pos
  have hsq : ∀ z : ℂ, ‖z‖ ≤ 2 * π → ‖z‖ ^ 2 ≤ 4 * π ^ 2 := fun z hz => by
    calc ‖z‖ ^ 2 ≤ (2 * π) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
      _ = 4 * π ^ 2 := by ring
  unfold cornerA
  by_cases hj0 : (j : ℕ) = 0
  · have hj1 : ¬ (j : ℕ) = N - 1 := by omega
    rw [if_pos hj0, if_pos hj0, if_neg hj1, if_neg hj1, add_zero, add_zero]
    by_cases hk1 : (k : ℕ) = N - 1
    · rw [if_pos hk1, if_pos hk1]
      have e1 : (N : ℤ) - ((j : ℕ) : ℤ) = N := by simp [hj0]
      have e2 : ((k : ℕ) : ℤ) + 1 = N := by omega
      rw [e1, e2, ← sub_mul, mul_comm (conj (cm α x N) - conj (cm α x 0))]
      exact hsq _ (norm_conj_sub_le hα x (N := N) (by omega))
    · rw [if_neg hk1, if_neg hk1]; simp
  · rw [if_neg hj0, if_neg hj0, zero_add, zero_add]
    by_cases hj1 : (j : ℕ) = N - 1
    · rw [if_pos hj1, if_pos hj1]
      by_cases hk0 : (k : ℕ) = 0
      · rw [if_pos hk0, if_pos hk0]
        have e1 : -((j : ℕ) : ℤ) - 1 = -(N : ℤ) := by omega
        have e2 : ((k : ℕ) : ℤ) - N = -(N : ℤ) := by simp [hk0]
        rw [e1, e2, ← sub_mul, mul_comm (cm α x 0 - cm α x N)]
        exact hsq _ (norm_sub_conj_le hα x (N := N) (by omega))
      · rw [if_neg hk0, if_neg hk0]; simp
    · rw [if_neg hj1, if_neg hj1]; simp

lemma a0_sq_le (α x : ℝ) {N : ℕ} (j k : Fin N) :
    ‖a0 α x N j k‖ ^ 2 ≤ if (k : ℕ) = 0 then
      (if (j : ℕ) = N - 1 then 0 else ‖cm α x 0‖ ^ 2 * ‖kap α (((j : ℕ) : ℤ) + 1)‖ ^ 2)
        else 0 := by
  have e : ‖kap α (-((j : ℕ) : ℤ) - 1)‖ = ‖kap α (((j : ℕ) : ℤ) + 1)‖ := by
    rw [show -((j : ℕ) : ℤ) - 1 = -(((j : ℕ) : ℤ) + 1) by ring, norm_kap_neg]
  unfold a0
  split_ifs
  · simp
  · rw [norm_mul, mul_pow, e]
  · simp

lemma b0_sq_le (α x : ℝ) {N : ℕ} (j k : Fin N) :
    ‖b0 α x N j k‖ ^ 2 ≤ if (j : ℕ) = 0 then
      (if (k : ℕ) = N - 1 then 0 else ‖cm α x 0‖ ^ 2 * ‖kap α (((k : ℕ) : ℤ) + 1)‖ ^ 2)
        else 0 := by
  unfold b0
  split_ifs
  · simp
  · rw [norm_mul, mul_pow, Complex.norm_conj]
  · simp

lemma aN_sq_le (α x : ℝ) {N : ℕ} (j k : Fin N) :
    ‖aN α x N j k‖ ^ 2 ≤ if (k : ℕ) = N - 1 then
      (if (j : ℕ) = 0 then 0 else ‖cm α x N‖ ^ 2 * ‖kap α ((N : ℤ) - ((j : ℕ) : ℤ))‖ ^ 2)
        else 0 := by
  unfold aN
  split_ifs
  · simp
  · rw [norm_mul, mul_pow, Complex.norm_conj]
  · simp

lemma bN_sq_le (α x : ℝ) {N : ℕ} (j k : Fin N) :
    ‖bN α x N j k‖ ^ 2 ≤ if (j : ℕ) = N - 1 then
      (if (k : ℕ) = 0 then 0 else ‖cm α x N‖ ^ 2 * ‖kap α ((N : ℤ) - ((k : ℕ) : ℤ))‖ ^ 2)
        else 0 := by
  have e : ‖kap α (((k : ℕ) : ℤ) - N)‖ = ‖kap α ((N : ℤ) - ((k : ℕ) : ℤ))‖ := by
    rw [show ((k : ℕ) : ℤ) - N = -((N : ℤ) - ((k : ℕ) : ℤ)) by ring, norm_kap_neg]
  unfold bN
  split_ifs
  · simp
  · rw [norm_mul, mul_pow, e]
  · simp

/-- Entries of `[K_N^g, P_N]`. -/
lemma commKP_apply (α : ℝ) {N : ℕ} (j k : Fin N) :
    (KG α N * Pd N - Pd N * KG α N) j k =
      kap α (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ)) *
        ((if (k : ℕ) = 0 ∨ (k : ℕ) = N - 1 then 1 else 0) -
          (if (j : ℕ) = 0 ∨ (j : ℕ) = N - 1 then 1 else 0)) := by
  simp only [Pd, Matrix.sub_apply, mul_diagonal, diagonal_mul, KG, of_apply]; ring

/-- The indicator of the boundary sites. -/
def bd {N : ℕ} (i : Fin N) : ℝ := if (i : ℕ) = 0 ∨ (i : ℕ) = N - 1 then 1 else 0

lemma bd_nonneg {N : ℕ} (i : Fin N) : 0 ≤ bd i := by unfold bd; split_ifs <;> norm_num

lemma sum_bd_le (N : ℕ) : ∑ i : Fin N, bd i ≤ 2 := by
  have : ∀ i : Fin N, bd i ≤ (if (i : ℕ) = 0 then 1 else 0) + (if (i : ℕ) = N - 1 then 1 else 0) := by
    intro i; unfold bd; split_ifs <;> norm_num <;> tauto
  calc ∑ i : Fin N, bd i ≤ ∑ i : Fin N, ((if (i : ℕ) = 0 then (1 : ℝ) else 0) +
        (if (i : ℕ) = N - 1 then 1 else 0)) := Finset.sum_le_sum fun i _ => this i
    _ ≤ 1 + 1 := by
        rw [Finset.sum_add_distrib]
        exact add_le_add (sum_ite_val_le 0 (fun _ => 1) zero_le_one (fun _ _ => le_rfl))
          (sum_ite_val_le (N - 1) (fun _ => 1) zero_le_one (fun _ _ => le_rfl))
    _ = 2 := by norm_num

lemma commKP_sq_le (α : ℝ) {N : ℕ} (j k : Fin N) :
    ‖(KG α N * Pd N - Pd N * KG α N) j k‖ ^ 2 ≤
      ‖kap α (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ))‖ ^ 2 * (bd k + bd j) := by
  rw [commKP_apply, norm_mul, mul_pow]
  refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
  unfold bd
  split_ifs <;> norm_num

/-- `‖[K_N^g, P_N]‖_{S_2}^2 ≤ 8 ∑_{r<N} |κ_r|^2`. -/
lemma hs_commKP_le (α : ℝ) (N : ℕ) :
    ∑ j : Fin N, ∑ k : Fin N, ‖(KG α N * Pd N - Pd N * KG α N) j k‖ ^ 2 ≤ 8 * Sk α N := by
  have hS := Sk_nonneg α N
  calc ∑ j : Fin N, ∑ k : Fin N, ‖(KG α N * Pd N - Pd N * KG α N) j k‖ ^ 2
      ≤ ∑ j : Fin N, ∑ k : Fin N, ‖kap α (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ))‖ ^ 2 * (bd k + bd j) :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => commKP_sq_le α j k
    _ = ∑ k : Fin N, bd k * ∑ j : Fin N, ‖kap α (((k : ℕ) : ℤ) - ((j : ℕ) : ℤ))‖ ^ 2 +
        ∑ j : Fin N, bd j * ∑ k : Fin N, ‖kap α (((j : ℕ) : ℤ) - ((k : ℕ) : ℤ))‖ ^ 2 := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        · rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ =>
            Finset.sum_congr rfl fun _ _ => by ring
        · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
          rw [← norm_kap_neg]; ring_nf
    _ ≤ ∑ k : Fin N, bd k * (2 * Sk α N) + ∑ j : Fin N, bd j * (2 * Sk α N) := by
        gcongr with k _ j _
        · exact bd_nonneg k
        · exact sum_col_kap α k
        · exact bd_nonneg j
        · exact sum_col_kap α j
    _ ≤ 2 * (2 * Sk α N) + 2 * (2 * Sk α N) := by
        have hb := sum_bd_le N
        try simp only [← Finset.sum_mul]
        nlinarith
    _ = 8 * Sk α N := by ring

lemma sq_add6_le (a b c d e f : ℝ) :
    (a + b + c + d + e + f) ^ 2 ≤ 6 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 + f ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d), sq_nonneg (a - e),
    sq_nonneg (a - f), sq_nonneg (b - c), sq_nonneg (b - d), sq_nonneg (b - e), sq_nonneg (b - f),
    sq_nonneg (c - d), sq_nonneg (c - e), sq_nonneg (c - f), sq_nonneg (d - e), sq_nonneg (d - f),
    sq_nonneg (e - f)]

lemma norm_six_sq_le (z1 z2 z3 z4 z5 z6 : ℂ) :
    ‖z1 + z2 - z3 + z4 - z5 - z6‖ ^ 2 ≤
      6 * (‖z1‖ ^ 2 + ‖z2‖ ^ 2 + ‖z3‖ ^ 2 + ‖z4‖ ^ 2 + ‖z5‖ ^ 2 + ‖z6‖ ^ 2) := by
  have h : ‖z1 + z2 - z3 + z4 - z5 - z6‖ ≤ ‖z1‖ + ‖z2‖ + ‖z3‖ + ‖z4‖ + ‖z5‖ + ‖z6‖ := by
    have := norm_sub_le (z1 + z2 - z3 + z4 - z5) z6
    have := norm_sub_le (z1 + z2 - z3 + z4) z5
    have := norm_add_le (z1 + z2 - z3) z4
    have := norm_sub_le (z1 + z2) z3
    have := norm_add_le z1 z2
    linarith
  calc ‖z1 + z2 - z3 + z4 - z5 - z6‖ ^ 2
      ≤ (‖z1‖ + ‖z2‖ + ‖z3‖ + ‖z4‖ + ‖z5‖ + ‖z6‖) ^ 2 := by gcongr
    _ ≤ _ := sq_add6_le _ _ _ _ _ _

/-- The error matrices `E_N^±(x) = E_N(x) ∓ τ[K_N^g, P_N]`, written with the real parameter
`s = ±τ` (tex l. 1880–1884). -/
def Epm (α : ℝ) (N : ℕ) (s x : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  EG α x N - (s : ℂ) • (KG α N * Pd N - Pd N * KG α N)

lemma Pd_isHermitian (N : ℕ) : (Pd N).IsHermitian := by
  rw [Pd, IsHermitian, diagonal_conjTranspose]; congr 1; funext i; simp only [Pi.star_apply]
  split_ifs <;> simp

lemma Epm_isHermitian (α : ℝ) (N : ℕ) (s x : ℝ) : (Epm α N s x).IsHermitian := by
  have hc : (KG α N * Pd N - Pd N * KG α N).IsHermitian := by
    unfold IsHermitian
    rw [conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, KG_skew, (Pd_isHermitian N).eq]
    noncomm_ring
  exact (EG_isHermitian α x N).sub (Flow.isHermitian_real_smul hc s)

/-- `E_N^±` vanishes off the boundary rows and columns, so `rank E_N^± ≤ 4` (tex l. 1885). -/
lemma Epm_interior (α : ℝ) {N : ℕ} (s x : ℝ) (j k : Fin N) (hj0 : (j : ℕ) ≠ 0)
    (hj1 : (j : ℕ) ≠ N - 1) (hk0 : (k : ℕ) ≠ 0) (hk1 : (k : ℕ) ≠ N - 1) : Epm α N s x j k = 0 := by
  rw [Epm, Matrix.sub_apply, Matrix.smul_apply, commKP_apply]
  simp [EG, hj0, hj1, hk0, hk1]

theorem rank_Epm_le (α : ℝ) {N : ℕ} (hN : 1 ≤ N) (s x : ℝ) : (Epm α N s x).rank ≤ 4 := by
  let S : Finset (Fin N) := {⟨0, by omega⟩, ⟨N - 1, by omega⟩}
  have hS : S.card ≤ 2 := Finset.card_le_two
  refine (LaxPair.rank_le_of_interior_eq_zero _ S ?_).trans (by omega)
  intro i k hi hk
  have hi0 : (i : ℕ) ≠ 0 := fun h => hi (by simp [S, Fin.ext_iff, h])
  have hi1 : (i : ℕ) ≠ N - 1 := fun h => hi (by simp [S, Fin.ext_iff, h])
  have hk0 : (k : ℕ) ≠ 0 := fun h => hk (by simp [S, Fin.ext_iff, h])
  have hk1 : (k : ℕ) ≠ N - 1 := fun h => hk (by simp [S, Fin.ext_iff, h])
  exact Epm_interior α s x i k hi0 hi1 hk0 hk1

/-- `‖E_N^±‖_{S_1} ≤ 2 ‖E_N^±‖_{S_2}` (rank `≤ 4`). -/
lemma traceNorm_Epm_le_hs (α : ℝ) {N : ℕ} (hN : 1 ≤ N) (s x : ℝ) :
    Flow.traceNorm (Epm α N s x) ≤ 2 * Flow.hsNorm (Epm α N s x) := by
  have h := Flow.traceNorm_le_sqrt_mul_hsNorm (Epm_isHermitian α N s x) (rank_Epm_le α hN s x)
  rwa [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h

/-- The Hilbert–Schmidt estimate:
`‖E_N^±‖_{S_2}^2 ≤ 6 (8π² + 2(|c_0|² + |c_N|²) S + 8 s² S)`, `S = ∑_{r<N} |κ_r|²`. -/
lemma hs_Epm_le (hα : Irrational α) {N : ℕ} (hN : 2 ≤ N) (s x : ℝ) :
    ∑ j : Fin N, ∑ k : Fin N, ‖Epm α N s x j k‖ ^ 2 ≤
      6 * (8 * π ^ 2 + 2 * (‖cm α x 0‖ ^ 2 + ‖cm α x N‖ ^ 2) * Sk α N + 8 * s ^ 2 * Sk α N) := by
  have hS := Sk_nonneg α N
  have hent : ∀ j k : Fin N, ‖Epm α N s x j k‖ ^ 2 ≤ 6 * (‖cornerA α x N j k‖ ^ 2 +
      ‖a0 α x N j k‖ ^ 2 + ‖b0 α x N j k‖ ^ 2 + ‖aN α x N j k‖ ^ 2 + ‖bN α x N j k‖ ^ 2 +
      s ^ 2 * ‖(KG α N * Pd N - Pd N * KG α N) j k‖ ^ 2) := by
    intro j k
    have e : Epm α N s x j k = cornerA α x N j k + a0 α x N j k - b0 α x N j k +
        aN α x N j k - bN α x N j k - (s : ℂ) * (KG α N * Pd N - Pd N * KG α N) j k := by
      rw [Epm, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, EG_split hN]
    rw [e]
    refine (norm_six_sq_le _ _ _ _ _ _).trans_eq ?_
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  -- the six double sums
  have s1 : ∑ j : Fin N, ∑ k : Fin N, ‖cornerA α x N j k‖ ^ 2 ≤ 8 * π ^ 2 := by
    calc _ ≤ ∑ j : Fin N, ∑ k : Fin N,
          ((if (j : ℕ) = 0 then (if (k : ℕ) = N - 1 then 4 * π ^ 2 else 0) else 0) +
          (if (j : ℕ) = N - 1 then (if (k : ℕ) = 0 then 4 * π ^ 2 else 0) else 0)) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => cornerA_sq_le hα x hN j k
      _ ≤ 4 * π ^ 2 + 4 * π ^ 2 := by
          simp only [Finset.sum_add_distrib]
          have hp : 0 ≤ 4 * π ^ 2 := by positivity
          refine add_le_add ?_ ?_
          · refine (dsum_row_le 0 (fun k => if (k : ℕ) = N - 1 then 4 * π ^ 2 else 0)
              (fun k => by split_ifs <;> simp [hp])).trans ?_
            exact sum_ite_val_le _ (fun _ => 4 * π ^ 2) hp (fun _ _ => le_rfl)
          · refine (dsum_row_le (N - 1) (fun k => if (k : ℕ) = 0 then 4 * π ^ 2 else 0)
              (fun k => by split_ifs <;> simp [hp])).trans ?_
            exact sum_ite_val_le _ (fun _ => 4 * π ^ 2) hp (fun _ _ => le_rfl)
      _ = 8 * π ^ 2 := by ring
  have hF1 : ∀ j : Fin N, 0 ≤ (if (j : ℕ) = N - 1 then 0 else
      ‖cm α x 0‖ ^ 2 * ‖kap α (((j : ℕ) : ℤ) + 1)‖ ^ 2) := fun j => by
    split_ifs <;> positivity
  have hF2 : ∀ j : Fin N, 0 ≤ (if (j : ℕ) = 0 then 0 else
      ‖cm α x N‖ ^ 2 * ‖kap α ((N : ℤ) - ((j : ℕ) : ℤ))‖ ^ 2) := fun j => by
    split_ifs <;> positivity
  have hsum1 : ∑ j : Fin N, (if (j : ℕ) = N - 1 then 0 else
      ‖cm α x 0‖ ^ 2 * ‖kap α (((j : ℕ) : ℤ) + 1)‖ ^ 2) ≤ ‖cm α x 0‖ ^ 2 * Sk α N := by
    have := sum_F1_le α N
    calc _ = ‖cm α x 0‖ ^ 2 * ∑ j : Fin N, (if (j : ℕ) = N - 1 then 0 else
          ‖kap α (((j : ℕ) : ℤ) + 1)‖ ^ 2) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
          split_ifs <;> simp
      _ ≤ _ := by gcongr
  have hsum2 : ∑ j : Fin N, (if (j : ℕ) = 0 then 0 else
      ‖cm α x N‖ ^ 2 * ‖kap α ((N : ℤ) - ((j : ℕ) : ℤ))‖ ^ 2) ≤
        ‖cm α x N‖ ^ 2 * Sk α N := by
    have := sum_F2_le α N
    calc _ = ‖cm α x N‖ ^ 2 * ∑ j : Fin N, (if (j : ℕ) = 0 then 0 else
          ‖kap α ((N : ℤ) - ((j : ℕ) : ℤ))‖ ^ 2) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
          split_ifs <;> simp
      _ ≤ _ := by gcongr
  have s2 : ∑ j : Fin N, ∑ k : Fin N, ‖a0 α x N j k‖ ^ 2 ≤ ‖cm α x 0‖ ^ 2 * Sk α N :=
    ((Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => a0_sq_le α x j k).trans
      (dsum_col_le 0 _ hF1)).trans hsum1
  have s3 : ∑ j : Fin N, ∑ k : Fin N, ‖b0 α x N j k‖ ^ 2 ≤ ‖cm α x 0‖ ^ 2 * Sk α N :=
    ((Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => b0_sq_le α x j k).trans
      (dsum_row_le 0 _ hF1)).trans hsum1
  have s4 : ∑ j : Fin N, ∑ k : Fin N, ‖aN α x N j k‖ ^ 2 ≤ ‖cm α x N‖ ^ 2 * Sk α N :=
    ((Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => aN_sq_le α x j k).trans
      (dsum_col_le (N - 1) _ hF2)).trans hsum2
  have s5 : ∑ j : Fin N, ∑ k : Fin N, ‖bN α x N j k‖ ^ 2 ≤ ‖cm α x N‖ ^ 2 * Sk α N :=
    ((Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => bN_sq_le α x j k).trans
      (dsum_row_le (N - 1) _ hF2)).trans hsum2
  have s6 : ∑ j : Fin N, ∑ k : Fin N, s ^ 2 * ‖(KG α N * Pd N - Pd N * KG α N) j k‖ ^ 2 ≤
      s ^ 2 * (8 * Sk α N) := by
    simp only [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hs_commKP_le α N) (sq_nonneg s)
  calc ∑ j : Fin N, ∑ k : Fin N, ‖Epm α N s x j k‖ ^ 2
      ≤ ∑ j : Fin N, ∑ k : Fin N, 6 * (‖cornerA α x N j k‖ ^ 2 +
        ‖a0 α x N j k‖ ^ 2 + ‖b0 α x N j k‖ ^ 2 + ‖aN α x N j k‖ ^ 2 + ‖bN α x N j k‖ ^ 2 +
        s ^ 2 * ‖(KG α N * Pd N - Pd N * KG α N) j k‖ ^ 2) :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => hent j k
    _ = 6 * ((∑ j : Fin N, ∑ k : Fin N, ‖cornerA α x N j k‖ ^ 2) +
        (∑ j : Fin N, ∑ k : Fin N, ‖a0 α x N j k‖ ^ 2) +
        (∑ j : Fin N, ∑ k : Fin N, ‖b0 α x N j k‖ ^ 2) +
        (∑ j : Fin N, ∑ k : Fin N, ‖aN α x N j k‖ ^ 2) +
        (∑ j : Fin N, ∑ k : Fin N, ‖bN α x N j k‖ ^ 2) +
        (∑ j : Fin N, ∑ k : Fin N, s ^ 2 * ‖(KG α N * Pd N - Pd N * KG α N) j k‖ ^ 2)) := by
        simp only [← Finset.mul_sum, Finset.sum_add_distrib]
    _ ≤ 6 * (8 * π ^ 2 + ‖cm α x 0‖ ^ 2 * Sk α N + ‖cm α x 0‖ ^ 2 * Sk α N +
        ‖cm α x N‖ ^ 2 * Sk α N + ‖cm α x N‖ ^ 2 * Sk α N + s ^ 2 * (8 * Sk α N)) := by
        gcongr
    _ = _ := by ring

/-- The constant of the graphene phase-variation estimate:
`C_g(C₀) = 2 √(6 (8π² + 160π⁴ + 128π² C₀²))`. -/
def grPhaseConst (C₀ : ℝ) : ℝ := 2 * Real.sqrt (6 * (8 * π ^ 2 + 160 * π ^ 4 + 128 * π ^ 2 * C₀ ^ 2))

lemma grPhaseConst_nonneg (C₀ : ℝ) : 0 ≤ grPhaseConst C₀ := by
  unfold grPhaseConst; positivity

/-- **The trace-norm bound** `sup_{x ∈ J_n} ‖E_N^±(x)‖_{S_1} ≤ C` (tex l. 1885–1910): for
`N ∈ {q_n, q_{n-1}}`, `N ≥ 2`, `|x| ≤ |δ_{n-1}|` and `|s| ≤ C₀|J_n|`,
`‖E_N(x) - s[K_N^g, P_N]‖_{S_1} ≤ grPhaseConst C₀`. -/
theorem traceNorm_Epm_le_const (hα : Irrational α) {n : ℕ} (hn : 1 ≤ n) {N : ℕ} (hN2 : 2 ≤ N)
    (hN : N = qN α n ∨ N = qN α (n - 1)) {C₀ s : ℝ}
    (hs : |s| ≤ C₀ * (2 * |delta α (n - 1)|)) {x : ℝ} (hx : |x| ≤ |delta α (n - 1)|) :
    Flow.traceNorm (Epm α N s x) ≤ grPhaseConst C₀ := by
  have hpi := Real.pi_pos
  set d := |delta α (n - 1)| with hd
  set Q := q α n with hQ
  have hd0 : 0 ≤ d := abs_nonneg _
  have hQ0 : 0 < Q := q_pos hα n
  have hdQ : d * Q < 1 := BlockCover.abs_delta_mul_q_lt hα hn
  have hdQ0 : 0 ≤ d * Q := by positivity
  have hdQ1 : (d * Q) ^ 2 ≤ 1 := by nlinarith
  have hS := Sk_le hα hn (by omega) (BlockCover.qN_le_of_mem hα hn hN)
  have hS0 := Sk_nonneg α N
  have hc0 : ‖cm α x 0‖ ^ 2 ≤ 4 * π ^ 2 * d ^ 2 := by
    rw [norm_cm, mul_pow, sq_abs]
    have := BlockCover.sq_two_sin_le (x := x) hx
    simp only [Int.cast_zero, zero_mul, add_zero]
    nlinarith
  have hcN : ‖cm α x N‖ ^ 2 ≤ 16 * π ^ 2 * d ^ 2 := by
    rw [norm_cm, mul_pow, sq_abs]
    have := BlockCover.sq_two_sin_shift_le hα hn hN hx
    simp only [Int.cast_natCast]
    nlinarith
  have hs2 : s ^ 2 ≤ (C₀ * (2 * d)) ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hs 2
  have hhs := hs_Epm_le hα hN2 s x
  -- `‖E‖_{S_2}^2 ≤ 6 (8π² + 160π⁴ + 128π²C₀²)`
  have hbound : ∑ j : Fin N, ∑ k : Fin N, ‖Epm α N s x j k‖ ^ 2 ≤
      6 * (8 * π ^ 2 + 160 * π ^ 4 + 128 * π ^ 2 * C₀ ^ 2) := by
    refine hhs.trans ?_
    have t1 : 2 * (‖cm α x 0‖ ^ 2 + ‖cm α x N‖ ^ 2) * Sk α N ≤ 160 * π ^ 4 := by
      calc 2 * (‖cm α x 0‖ ^ 2 + ‖cm α x N‖ ^ 2) * Sk α N
          ≤ 2 * (4 * π ^ 2 * d ^ 2 + 16 * π ^ 2 * d ^ 2) * (4 * π ^ 2 * Q ^ 2) := by gcongr
        _ = 160 * π ^ 4 * (d * Q) ^ 2 := by ring
        _ ≤ 160 * π ^ 4 * 1 := by gcongr
        _ = 160 * π ^ 4 := by ring
    have t2 : 8 * s ^ 2 * Sk α N ≤ 128 * π ^ 2 * C₀ ^ 2 := by
      calc 8 * s ^ 2 * Sk α N ≤ 8 * (C₀ * (2 * d)) ^ 2 * (4 * π ^ 2 * Q ^ 2) := by gcongr
        _ = 128 * π ^ 2 * C₀ ^ 2 * (d * Q) ^ 2 := by ring
        _ ≤ 128 * π ^ 2 * C₀ ^ 2 * 1 := by gcongr
        _ = 128 * π ^ 2 * C₀ ^ 2 := by ring
    linarith
  refine (traceNorm_Epm_le_hs α (by omega) s x).trans ?_
  unfold grPhaseConst Flow.hsNorm
  gcongr

end Graphene
end CAH
