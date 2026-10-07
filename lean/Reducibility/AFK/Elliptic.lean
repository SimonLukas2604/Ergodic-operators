/-
# AFK, Lemma `elliptic`: conjugating a matrix close to a rotation to a rotation

Formalization of Lemma `elliptic` (stated inside the proof of Proposition `CT`) of
Avila–Fayad–Krikorian, *A KAM scheme for `SL(2,ℝ)` cocycles with Liouvillean frequencies*.

For `φ ∈ ℂ` let `R_φ = [[cos φ, -sin φ], [sin φ, cos φ]]` (`Rc φ`, angle in radians).

**Lemma `elliptic`.** For every `D > 0` there are `C, ε > 0` such that for every
`A ∈ SL(2,ℂ)`, `θ ∈ ℂ` with `‖A‖ < 2D` and
`‖R_θ⁻¹ A - id‖ < ε · min {1, ‖R_{2θ} - id‖²}`, there are `B ∈ SL(2,ℂ)` and `θ' ∈ ℂ` with
`B A B⁻¹ = R_{θ'}`, `‖B - id‖ ≤ C ‖R_θ⁻¹ A - id‖ / ‖R_{2θ} - id‖²` (in fact even with the
first power of `‖R_{2θ} - id‖`), `|θ' - θ| ≤ C ‖R_θ⁻¹ A - id‖`, and with `B`, `θ'` real when
`A`, `θ` are real.

Remarks / deviations from the paper.
* The paper's domain condition reads `ε max {1, ‖R_{2θ} - id‖²}`; with `max` the statement
  is false (take `θ = 0` and `A` a nontrivial parabolic matrix close to `id`), so we use
  `min`, i.e. `‖R_θ⁻¹A - id‖ < ε` and `‖R_θ⁻¹A - id‖ < ε ‖R_{2θ} - id‖²`.  (The condition
  `< ε ‖R_{2θ}-id‖²` alone is also insufficient: for `|Im θ|` large it allows any `A`.)
* The paper produces a *holomorphic* real-symmetric function `F(A, θ)`; we prove the
  pointwise statement (existence of `B`, `θ'` with the estimates, real in the real case),
  without the holomorphic dependence.
* Proof: instead of the paper's Newton iteration we diagonalize directly.  With
  `P = [[1, 1], [-i, i]]` one has `R_φ = P diag(e^{iφ}, e^{-iφ}) P⁻¹`; in these coordinates
  `A` is a small perturbation of `diag(λ, λ⁻¹)`, `λ = e^{iθ}`, whose eigenvalue gap
  `|λ - λ⁻¹| = 2|sin θ|` controls `‖R_{2θ} - id‖`.  We pick explicitly the eigenvalue
  `μ` (quadratic formula, branch chosen near `λ`) and eigenvectors, normalize to
  determinant `1`, and put `θ' = θ - i log(μ/λ)`.

We use the `ℓ^∞` operator norm on `2 × 2` matrices (`Matrix.Norms.Operator`).
-/
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section

open scoped Matrix.Norms.Operator ComplexConjugate
open Matrix Complex

namespace Red.AFK

/-- Complex `2 × 2` matrices. -/
abbrev M2c := Matrix (Fin 2) (Fin 2) ℂ

/-! ### Norm helpers -/

lemma norm_row_le (M : M2c) (i : Fin 2) : ‖M i 0‖ + ‖M i 1‖ ≤ ‖M‖ := by
  have h2 : ∑ k, ‖M i k‖₊ ≤ ‖M‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact Finset.le_sup (f := fun i => ∑ k, ‖M i k‖₊) (Finset.mem_univ i)
  have h3 : ((∑ k, ‖M i k‖₊ : NNReal) : ℝ) ≤ ‖M‖₊ := by exact_mod_cast h2
  simpa [Fin.sum_univ_two] using h3

lemma norm_entry_le (M : M2c) (i j : Fin 2) : ‖M i j‖ ≤ ‖M‖ := by
  have := norm_row_le M i
  fin_cases j <;> simp <;> linarith [norm_nonneg (M i 0), norm_nonneg (M i 1)]

lemma ell_norm_le_of_rows {M : M2c} {c : ℝ} (hc : 0 ≤ c) (h : ∀ i, ‖M i 0‖ + ‖M i 1‖ ≤ c) :
    ‖M‖ ≤ c := by
  have : ‖M‖₊ ≤ ⟨c, hc⟩ := by
    rw [Matrix.linfty_opNNNorm_def]
    refine Finset.sup_le fun i _ => ?_
    rw [Fin.sum_univ_two]
    refine NNReal.coe_le_coe.mp ?_
    simp only [NNReal.coe_add, coe_nnnorm]
    exact h i
  exact NNReal.coe_le_coe.mpr this

/-! ### Square roots near a given value -/

lemma sq_sub_bound {s w Z : ℂ} (h : s ^ 2 = Z) (hsw : ‖w‖ ≤ ‖s + w‖) :
    ‖s - w‖ * ‖w‖ ≤ ‖Z - w ^ 2‖ := by
  have : Z - w ^ 2 = (s - w) * (s + w) := by rw [← h]; ring
  rw [this, norm_mul]
  exact mul_le_mul_of_nonneg_left hsw (norm_nonneg _)

lemma exists_sqrt_near (w Z : ℂ) : ∃ s : ℂ, s ^ 2 = Z ∧ ‖w‖ ≤ ‖s + w‖ := by
  obtain ⟨s0, hs0⟩ : ∃ s0 : ℂ, s0 ^ 2 = Z := ⟨_, Complex.cpow_nat_inv_pow Z two_ne_zero⟩
  by_cases h : ‖w‖ ≤ ‖s0 + w‖
  · exact ⟨s0, hs0, h⟩
  · refine ⟨-s0, by rw [neg_sq, hs0], ?_⟩
    have h2 : ‖(2 : ℂ) * w‖ ≤ ‖s0 + w‖ + ‖-s0 + w‖ := by
      calc ‖(2 : ℂ) * w‖ = ‖(s0 + w) + (-s0 + w)‖ := by congr 1; ring
        _ ≤ _ := norm_add_le _ _
    rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num] at h2
    linarith [not_le.mp h]

lemma exists_sqrt_near_one (Z : ℂ) (P : Prop) (hP : P → conj Z = Z ∧ 0 < Z.re) :
    ∃ ρ : ℂ, ρ ^ 2 = Z ∧ 1 ≤ ‖ρ + 1‖ ∧ (P → conj ρ = ρ) := by
  by_cases h : P
  · obtain ⟨hc, hre⟩ := hP h
    have hZ : (Z.re : ℂ) = Z := Complex.conj_eq_iff_re.mp hc
    refine ⟨(Real.sqrt Z.re : ℂ), ?_, ?_, fun _ => Complex.conj_ofReal _⟩
    · rw [← Complex.ofReal_pow, Real.sq_sqrt hre.le, hZ]
    · rw [← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity)]
      linarith [Real.sqrt_nonneg Z.re]
  · obtain ⟨s, hs, hsw⟩ := exists_sqrt_near 1 Z
    exact ⟨s, hs, by simpa using hsw, fun hp => absurd hp h⟩

lemma norm_eq_one_of_mul_conj {z : ℂ} (h : z * conj z = 1) : ‖z‖ = 1 := by
  rw [Complex.mul_conj'] at h
  have h1 : ‖z‖ ^ 2 = 1 := by exact_mod_cast h
  have h0 := norm_nonneg z
  nlinarith

/-! ### The scalar core: diagonalizing a perturbation of `diag(λ, λ⁻¹)` -/

set_option maxHeartbeats 1000000 in
/-- **Core of Lemma `elliptic`** in diagonal coordinates.  Let `M = [[a, b], [c, d]]` with
`a = λ(1+p)`, `b = λq`, `c = λ'r`, `d = λ'(1+u)`, `λλ' = 1`, `|λ|, |λ'| ≤ K`, `det M = 1`,
`|p|, |q|, |r|, |u| ≤ η` and `64 K⁴ η ≤ |λ - λ'|²`.  Then `B' = ρ [[1, -x], [-y, 1]]`
(with `ρ²(1 - xy) = 1`) satisfies `B' M = diag(μ, ν) B'` (the four scalar relations),
`μν = 1`, `|μ - λ| ≤ 8Kη` and `|ρ - 1|, |ρx|, |ρy| ≤ 4Kη/|λ - λ'|`.  In the real-symmetric
case (`λ' = λ̄`, `u = p̄`, `r = q̄`) one has `μ̄ = ν`, `ρ` real and `y = x̄`. -/
theorem elliptic_core {lam lam' p q r u a b c d : ℂ} {K η : ℝ} {Rl : Prop}
    (hK : 1 ≤ K) (hll : lam * lam' = 1) (hl : ‖lam‖ ≤ K) (hl' : ‖lam'‖ ≤ K)
    (hp : ‖p‖ ≤ η) (hq : ‖q‖ ≤ η) (hr : ‖r‖ ≤ η) (hu : ‖u‖ ≤ η)
    (hdet : (1 + p) * (1 + u) - q * r = 1)
    (ha : a = lam * (1 + p)) (hb : b = lam * q) (hc : c = lam' * r) (hd : d = lam' * (1 + u))
    (hw : 0 < ‖lam - lam'‖) (hη : 64 * K ^ 4 * η ≤ ‖lam - lam'‖ ^ 2)
    (hR : Rl → lam' = conj lam ∧ u = conj p ∧ r = conj q) :
    ∃ μ ν ρ x y : ℂ, μ * ν = 1 ∧ ρ ^ 2 * (1 - x * y) = 1 ∧
      a - x * c = μ ∧ b - x * d = -(μ * x) ∧ c - y * a = -(ν * y) ∧ d - y * b = ν ∧
      ‖μ - lam‖ ≤ 8 * K * η ∧ ‖ρ - 1‖ ≤ 4 * K * η / ‖lam - lam'‖ ∧
      ‖ρ * x‖ ≤ 4 * K * η / ‖lam - lam'‖ ∧ ‖ρ * y‖ ≤ 4 * K * η / ‖lam - lam'‖ ∧
      (Rl → conj μ = ν ∧ conj ρ = ρ ∧ y = conj x) := by
  obtain ⟨W, hWdef⟩ : ∃ W, W = ‖lam - lam'‖ := ⟨_, rfl⟩
  rw [← hWdef] at hw hη ⊢
  have hW0 : W ≠ 0 := hw.ne'
  have hη0 : 0 ≤ η := (norm_nonneg _).trans hp
  have hK0 : 0 < K := by linarith
  have hW2 : W ≤ 2 * K := by rw [hWdef]; exact (norm_sub_le _ _).trans (by linarith)
  have hWW : W * W ≤ W * (2 * K) := mul_le_mul_of_nonneg_left hW2 hw.le
  have hG : 32 * K ^ 3 * η ≤ W := by
    have h1 : 2 * K * (32 * K ^ 3 * η) ≤ 2 * K * W := by nlinarith
    exact le_of_mul_le_mul_left h1 (by positivity)
  have hK3 : K ≤ K ^ 3 := by
    nlinarith [mul_nonneg (mul_nonneg hK0.le (sub_nonneg.2 hK)) (by linarith : (0:ℝ) ≤ K + 1)]
  have hKη : 32 * K * η ≤ W := le_trans (by nlinarith) hG
  have h16 : 16 * K ^ 2 * η ≤ 1 := by
    have h1 : 2 * K * (16 * K ^ 2 * η) ≤ 2 * K * 1 := by nlinarith
    exact le_of_mul_le_mul_left h1 (by positivity)
  have hη1 : η ≤ 1 / 16 := by nlinarith
  have hKη0 : 0 ≤ K * η := by positivity
  -- determinant
  have hAd : a * d - b * c = 1 := by
    rw [ha, hb, hc, hd]; linear_combination (lam * lam') * hdet + hll
  have hpu : ‖p + u‖ ≤ 2 * η ^ 2 := by
    have : p + u = q * r - p * u := by linear_combination hdet
    rw [this]
    calc ‖q * r - p * u‖ ≤ ‖q * r‖ + ‖p * u‖ := norm_sub_le _ _
      _ = ‖q‖ * ‖r‖ + ‖p‖ * ‖u‖ := by rw [norm_mul, norm_mul]
      _ ≤ η * η + η * η := add_le_add (mul_le_mul hq hr (norm_nonneg _) hη0)
          (mul_le_mul hp hu (norm_nonneg _) hη0)
      _ = 2 * η ^ 2 := by ring
  obtain ⟨t, ht⟩ : ∃ t, t = a + d := ⟨_, rfl⟩
  have htτ : ‖t - (lam + lam')‖ ≤ 2 * W * η := by
    have htt : t - (lam + lam') = (lam - lam') * p + lam' * (p + u) := by
      rw [ht, ha, hd]; ring
    have e1 : ‖(lam - lam') * p‖ ≤ W * η := by
      rw [norm_mul, ← hWdef]; exact mul_le_mul_of_nonneg_left hp hw.le
    have e2 : ‖lam' * (p + u)‖ ≤ K * (2 * η ^ 2) := by
      rw [norm_mul]; exact mul_le_mul hl' hpu (norm_nonneg _) hK0.le
    have e3 : K * (2 * η ^ 2) ≤ W * η := by
      nlinarith [mul_le_mul_of_nonneg_left (show 2 * K * η ≤ W by linarith) hη0]
    rw [htt]; linarith [norm_add_le ((lam - lam') * p) (lam' * (p + u))]
  have hτ : ‖lam + lam'‖ ≤ 2 * K := (norm_add_le _ _).trans (by linarith)
  have htpτ : ‖t + (lam + lam')‖ ≤ 5 * K := by
    have : t + (lam + lam') = (t - (lam + lam')) + 2 * (lam + lam') := by ring
    rw [this]
    have e : ‖(2 : ℂ) * (lam + lam')‖ ≤ 4 * K := by
      rw [norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]; linarith
    have e2 : 2 * W * η ≤ K := by
      nlinarith [mul_le_mul_of_nonneg_right hW2 hη0, mul_le_mul_of_nonneg_left hη1 hK0.le]
    linarith [norm_add_le (t - (lam + lam')) (2 * (lam + lam'))]
  obtain ⟨s, hs2, hsw⟩ := exists_sqrt_near (lam - lam') (t ^ 2 - 4)
  have hsb : ‖s - (lam - lam')‖ ≤ 10 * K * η := by
    have h1 := sq_sub_bound hs2 hsw
    rw [← hWdef] at h1
    have h2 : t ^ 2 - 4 - (lam - lam') ^ 2 = (t - (lam + lam')) * (t + (lam + lam')) := by
      linear_combination 4 * hll
    rw [h2, norm_mul] at h1
    have h3 : ‖t - (lam + lam')‖ * ‖t + (lam + lam')‖ ≤ (2 * W * η) * (5 * K) :=
      mul_le_mul htτ htpτ (norm_nonneg _) (by positivity)
    have h4 : ‖s - (lam - lam')‖ * W ≤ (10 * K * η) * W := by nlinarith
    exact le_of_mul_le_mul_right h4 hw
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = (t + s) / 2 := ⟨_, rfl⟩
  obtain ⟨ν, hν⟩ : ∃ ν, ν = (t - s) / 2 := ⟨_, rfl⟩
  have hμν : μ * ν = 1 := by rw [hμ, hν]; linear_combination (-1 / 4 : ℂ) * hs2
  have hsum : μ + ν = a + d := by rw [hμ, hν, ← ht]; ring
  have hμ0 : μ ≠ 0 := left_ne_zero_of_mul_eq_one hμν
  have hμl : ‖μ - lam‖ ≤ 7 * K * η := by
    have : μ - lam = ((t - (lam + lam')) + (s - (lam - lam'))) / 2 := by rw [hμ]; ring
    rw [this, norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num, div_le_iff₀ (by norm_num)]
    have := norm_add_le (t - (lam + lam')) (s - (lam - lam'))
    have : W * η ≤ 2 * K * η := mul_le_mul_of_nonneg_right hW2 hη0
    nlinarith
  obtain ⟨m, hm⟩ : ∃ m, m = μ - d := ⟨_, rfl⟩
  have hmw : ‖m - (lam - lam')‖ ≤ 8 * K * η := by
    have : m - (lam - lam') = (μ - lam) - lam' * u := by rw [hm, hd]; ring
    rw [this]
    have e : ‖lam' * u‖ ≤ K * η := by
      rw [norm_mul]; exact mul_le_mul hl' hu (norm_nonneg _) hK0.le
    linarith [norm_sub_le (μ - lam) (lam' * u)]
  have hmW : W / 2 ≤ ‖m‖ := by
    have h1 : W ≤ ‖m‖ + ‖m - (lam - lam')‖ := by
      calc W = ‖m - (m - (lam - lam'))‖ := by rw [sub_sub_cancel, hWdef]
        _ ≤ _ := norm_sub_le _ _
    linarith
  have hmpos : 0 < ‖m‖ := by linarith
  have hm0 : m ≠ 0 := norm_pos_iff.mp hmpos
  obtain ⟨x, hx⟩ : ∃ x, x = -b / m := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = c / m := ⟨_, rfl⟩
  have hxm : x * m = -b := by rw [hx]; field_simp
  have hym : y * m = c := by rw [hy]; field_simp
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = 2 * K * η / W := ⟨_, rfl⟩
  have hk0 : 0 ≤ k := by rw [hk]; positivity
  have hk16 : k ≤ 1 / 16 := by rw [hk, div_le_iff₀ hw]; linarith
  have hb' : ‖b‖ ≤ K * η := by
    rw [hb, norm_mul]; exact mul_le_mul hl hq (norm_nonneg _) hK0.le
  have hc' : ‖c‖ ≤ K * η := by
    rw [hc, norm_mul]; exact mul_le_mul hl' hr (norm_nonneg _) hK0.le
  have hkm : K * η ≤ k * ‖m‖ := by
    have e : 2 * K * η / W * (W / 2) = K * η := by field_simp
    have h2 : 2 * K * η / W * (W / 2) ≤ 2 * K * η / W * ‖m‖ :=
      mul_le_mul_of_nonneg_left hmW (by positivity)
    rw [hk]; linarith
  have hxk : ‖x‖ ≤ k := by
    rw [hx, norm_div, norm_neg, div_le_iff₀ hmpos]; linarith
  have hyk : ‖y‖ ≤ k := by
    rw [hy, norm_div, div_le_iff₀ hmpos]; linarith
  have hxy : ‖x * y‖ ≤ k * k := by
    rw [norm_mul]; exact mul_le_mul hxk hyk (norm_nonneg _) hk0
  have hxy1 : ‖x * y‖ ≤ 1 / 256 := by nlinarith
  have h1xy : 1 - x * y ≠ 0 := by
    intro h
    have : x * y = 1 := by linear_combination -h
    rw [this, norm_one] at hxy1; norm_num at hxy1
  -- the real-symmetric case
  have hreal : Rl → conj μ = ν ∧ y = conj x := by
    intro hRl
    obtain ⟨h1, h2, h3⟩ := hR hRl
    have hca : conj a = d := by rw [ha, hd, h1, h2]; simp
    have hcb : conj b = c := by rw [hb, hc, h1, h3]; simp
    have hcd : conj d = a := by rw [← hca, Complex.conj_conj]
    have hct : conj t = t := by rw [ht, map_add, hca, hcd, add_comm]
    have hcw : conj (lam - lam') = -(lam - lam') := by rw [h1]; simp
    have hcs : conj s = -s := by
      have e : (conj s - s) * (conj s + s) = 0 := by
        have : conj s ^ 2 = s ^ 2 := by
          rw [← map_pow, hs2, map_sub, map_pow, hct, map_ofNat]
        linear_combination this
      rcases mul_eq_zero.mp e with h | h
      · exfalso
        have hcs' : conj s = s := sub_eq_zero.mp h
        have e1 : ‖s + (lam - lam')‖ = ‖s - (lam - lam')‖ := by
          rw [← Complex.norm_conj (s - (lam - lam')), map_sub, hcs', hcw, sub_neg_eq_add]
        have e2 : 2 * W ≤ ‖s + (lam - lam')‖ + ‖s - (lam - lam')‖ := by
          have h' := norm_sub_le (s + (lam - lam')) (s - (lam - lam'))
          have : (s + (lam - lam')) - (s - (lam - lam')) = (2 : ℂ) * (lam - lam') := by ring
          rw [this, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num, ← hWdef] at h'
          linarith
        linarith
      · linear_combination h
    have hcμ : conj μ = ν := by
      rw [hμ, hν, map_div₀, map_add, hct, hcs, map_ofNat, sub_eq_add_neg]
    refine ⟨hcμ, ?_⟩
    have hcm : conj m = -m := by
      rw [hm, map_sub, hcμ, hcd]; linear_combination hsum
    rw [hy, hx, map_div₀, map_neg, hcb, hcm, neg_div_neg_eq]
  obtain ⟨ρ, hρ2, hρ1, hρc⟩ := exists_sqrt_near_one (1 - x * y)⁻¹ Rl (fun hRl => by
    have hy' := (hreal hRl).2
    have hZ : (1 - x * y)⁻¹ = (((1 - ‖x‖ ^ 2)⁻¹ : ℝ) : ℂ) := by
      rw [hy', Complex.mul_conj']; push_cast; ring
    rw [hZ]
    refine ⟨Complex.conj_ofReal _, ?_⟩
    rw [Complex.ofReal_re]
    apply inv_pos.mpr
    nlinarith [norm_nonneg x])
  have hρ' : ‖ρ - 1‖ ≤ 2 * ‖x * y‖ := by
    have h1 := sq_sub_bound (w := 1) hρ2 (by simpa using hρ1)
    rw [norm_one, mul_one, one_pow] at h1
    have : (1 - x * y)⁻¹ - 1 = x * y / (1 - x * y) := by field_simp; ring
    rw [this, norm_div] at h1
    have h2 : 1 - ‖x * y‖ ≤ ‖1 - x * y‖ := by
      have := norm_sub_norm_le (1 : ℂ) (x * y); rw [norm_one] at this; linarith
    have h3 : ‖x * y‖ / ‖1 - x * y‖ ≤ 2 * ‖x * y‖ := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [mul_nonneg (norm_nonneg (x * y)) (show 0 ≤ ‖1 - x * y‖ - 1 / 2 by linarith)]
    linarith
  have hρk : ‖ρ - 1‖ ≤ k := by nlinarith
  have hρn : ‖ρ‖ ≤ 2 := by
    have := norm_sub_norm_le ρ 1; rw [norm_one] at this; linarith
  have h2k : 2 * k = 4 * K * η / W := by rw [hk]; ring
  -- eigen-relations
  have hrel1 : a - x * c = μ := by
    apply mul_right_cancel₀ hm0
    linear_combination (-c) * hxm + (a - μ) * hm - μ * hsum + hμν - hAd
  have hrel2 : b - x * d = -(μ * x) := by linear_combination hxm - x * hm
  have hrel3 : c - y * a = -(ν * y) := by linear_combination (-1) * hym + y * hsum + y * hm
  have hrel4 : d - y * b = ν := by
    apply mul_right_cancel₀ hm0
    linear_combination (-b) * hym + (d - ν) * hm + d * hsum + hAd - hμν
  refine ⟨μ, ν, ρ, x, y, hμν, ?_, hrel1, hrel2, hrel3, hrel4, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hρ2]; exact inv_mul_cancel₀ h1xy
  · linarith
  · rw [← h2k]; linarith
  · rw [← h2k, norm_mul]
    nlinarith [mul_le_mul hρn hxk (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)]
  · rw [← h2k, norm_mul]
    nlinarith [mul_le_mul hρn hyk (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)]
  · intro hRl; exact ⟨(hreal hRl).1, hρc hRl, (hreal hRl).2⟩

/-! ### Rotation matrices and their diagonalization -/

/-- The complex rotation `R_θ = [[cos θ, -sin θ], [sin θ, cos θ]]` (angle in radians). -/
def Rc (θ : ℂ) : M2c := !![cos θ, -sin θ; sin θ, cos θ]

/-- The constant matrix `P` with columns `(1, -i)`, `(1, i)` diagonalizing all `R_θ`. -/
def Pm : M2c := !![1, 1; -I, I]

/-- The inverse of `Pm`. -/
def Pinv : M2c := !![1 / 2, I / 2; 1 / 2, -I / 2]

lemma Pm_mul_Pinv : Pm * Pinv = 1 := by
  rw [Pm, Pinv, Matrix.mul_fin_two, Matrix.one_fin_two]
  congr 1 <;> simp <;> ring_nf <;> simp [Complex.I_sq] <;> ring

lemma Pinv_mul_Pm : Pinv * Pm = 1 := by
  rw [Pm, Pinv, Matrix.mul_fin_two, Matrix.one_fin_two]
  congr 1 <;> simp <;> ring_nf <;> simp [Complex.I_sq] <;> ring

lemma norm_Pm_le : ‖Pm‖ ≤ 2 :=
  ell_norm_le_of_rows (by norm_num) fun i => by fin_cases i <;> simp [Pm] <;> norm_num

lemma norm_Pinv_le : ‖Pinv‖ ≤ 1 :=
  ell_norm_le_of_rows (by norm_num) fun i => by fin_cases i <;> simp [Pinv] <;> norm_num

lemma conj_Pinv_Pm (M : M2c) : Pinv * (Pm * M * Pinv) * Pm = M := by
  simp only [Matrix.mul_assoc]
  rw [Pinv_mul_Pm, Matrix.mul_one, ← Matrix.mul_assoc, Pinv_mul_Pm, Matrix.one_mul]

/-- `R_φ = P diag(e^{iφ}, e^{-iφ}) P⁻¹`, written with `e^{±iφ} = cos φ ± i sin φ`. -/
theorem Rc_eq (φ : ℂ) :
    Rc φ = Pm * !![cos φ + sin φ * I, 0; 0, cos φ - sin φ * I] * Pinv := by
  rw [Rc, Pm, Pinv, Matrix.mul_fin_two, Matrix.mul_fin_two]
  congr 1 <;> simp <;> ring_nf <;> simp [Complex.I_sq] <;> (try ring_nf) <;>
    first | exact Complex.cos_sq_add_sin_sq (x := φ) | exact Complex.sin_sq_add_cos_sq (x := φ)

theorem Rc_mul_neg (θ : ℂ) : Rc θ * Rc (-θ) = 1 := by
  rw [Rc, Rc, Matrix.mul_fin_two, Matrix.one_fin_two]
  simp only [Complex.cos_neg, Complex.sin_neg, neg_neg]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;>
    first | linear_combination Complex.cos_sq_add_sin_sq (x := θ) | ring

lemma Rc_apply_10 (θ : ℂ) : Rc θ 1 0 = sin θ := by simp [Rc]
lemma Rc_apply_11 (θ : ℂ) : Rc θ 1 1 = cos θ := by simp [Rc]

/-- Entries of `P⁻¹ X P`. -/
lemma Pconj_eq (X : M2c) : Pinv * X * Pm =
    !![(X 0 0 + X 1 1 + I * (X 1 0 - X 0 1)) / 2, (X 0 0 - X 1 1 + I * (X 1 0 + X 0 1)) / 2;
       (X 0 0 - X 1 1 - I * (X 1 0 + X 0 1)) / 2, (X 0 0 + X 1 1 - I * (X 1 0 - X 0 1)) / 2] := by
  conv_lhs => rw [Matrix.eta_fin_two X]
  rw [Pinv, Pm, Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring_nf <;> simp [Complex.I_sq] <;> ring

theorem Rc_inv (θ : ℂ) : (Rc θ)⁻¹ = Rc (-θ) := Matrix.inv_eq_right_inv (Rc_mul_neg θ)

theorem norm_Rc_two_mul_sub_one_le (θ : ℂ) :
    ‖Rc (2 * θ) - 1‖ ≤ 2 * ‖sin θ‖ * (‖cos θ‖ + ‖sin θ‖) := by
  have e1 : cos (2 * θ) - 1 = -2 * sin θ ^ 2 := by
    rw [Complex.cos_two_mul]; linear_combination 2 * Complex.cos_sq_add_sin_sq (x := θ)
  have n1 : ‖cos (2 * θ) - 1‖ = 2 * ‖sin θ‖ ^ 2 := by rw [e1]; simp
  have n2 : ‖sin (2 * θ)‖ = 2 * ‖sin θ‖ * ‖cos θ‖ := by rw [Complex.sin_two_mul]; simp
  refine ell_norm_le_of_rows (by positivity) fun i => ?_
  fin_cases i
  · simp only [Rc]; simp [n1, n2]; ring_nf; rfl
  · simp only [Rc]; simp [n1, n2]; ring_nf; rfl

/-! ### Lemma `elliptic` -/

set_option maxHeartbeats 1000000 in
/-- **Lemma `elliptic`** (AFK, in the proof of Proposition `CT`).  For every `D > 0` there
are `C, ε > 0` such that if `A ∈ SL(2,ℂ)`, `θ ∈ ℂ`, `‖A‖ < 2D` and
`‖R_θ⁻¹ A - id‖ < ε min {1, ‖R_{2θ} - id‖²}`, then there are `B ∈ SL(2,ℂ)` and `θ'` with
`B A B⁻¹ = R_{θ'}`, `‖B - id‖ ≤ C ‖R_θ⁻¹A - id‖ / ‖R_{2θ} - id‖` and
`‖B - id‖ ≤ C ‖R_θ⁻¹A - id‖ / ‖R_{2θ} - id‖²`, `|θ' - θ| ≤ C ‖R_θ⁻¹A - id‖`, and `B`, `θ'`
are real whenever `A` and `θ` are real. -/
theorem elliptic (D : ℝ) (hD : 0 < D) :
    ∃ C ε : ℝ, 0 < C ∧ 0 < ε ∧ ∀ (A : M2c) (θ : ℂ), A.det = 1 → ‖A‖ < 2 * D →
      ‖(Rc θ)⁻¹ * A - 1‖ < ε * min 1 (‖Rc (2 * θ) - 1‖ ^ 2) →
      ∃ (B : M2c) (θ' : ℂ), B.det = 1 ∧ B * A * B⁻¹ = Rc θ' ∧
        ‖B - 1‖ ≤ C * ‖(Rc θ)⁻¹ * A - 1‖ / ‖Rc (2 * θ) - 1‖ ∧
        ‖B - 1‖ ≤ C * ‖(Rc θ)⁻¹ * A - 1‖ / ‖Rc (2 * θ) - 1‖ ^ 2 ∧
        ‖θ' - θ‖ ≤ C * ‖(Rc θ)⁻¹ * A - 1‖ ∧
        ((∀ i j, (A i j).im = 0) → θ.im = 0 → (∀ i j, (B i j).im = 0) ∧ θ'.im = 0) := by
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 4 * D + 1 := ⟨_, rfl⟩
  have hK : 1 ≤ K := by linarith
  have hK0 : 0 < K := by linarith
  refine ⟨64 * K ^ 4, 1 / (128 * K ^ 6), by positivity, by positivity, ?_⟩
  intro A θ hdetA hA hX
  rw [Rc_inv] at hX ⊢
  obtain ⟨X, hXdef⟩ : ∃ X, X = Rc (-θ) * A - 1 := ⟨_, rfl⟩
  rw [← hXdef] at hX ⊢
  obtain ⟨ε0, hε0⟩ : ∃ e, e = ‖X‖ := ⟨_, rfl⟩
  rw [← hε0] at hX ⊢
  obtain ⟨g, hg⟩ : ∃ g, g = ‖Rc (2 * θ) - 1‖ := ⟨_, rfl⟩
  rw [← hg] at hX ⊢
  have hε0nn : 0 ≤ ε0 := hε0 ▸ norm_nonneg _
  have hmin_pos : 0 < min 1 (g ^ 2) := by
    by_contra h
    push Not at h
    have : 1 / (128 * K ^ 6) * min 1 (g ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    linarith
  have hg0 : 0 < g := by
    have h2 : 0 < g ^ 2 := lt_of_lt_of_le hmin_pos (min_le_right _ _)
    by_contra hn
    push Not at hn
    have : g = 0 := le_antisymm hn (hg ▸ norm_nonneg _)
    rw [this] at h2; norm_num at h2
  have hε0g : 128 * K ^ 6 * ε0 < g ^ 2 := by
    have h1 : ε0 < 1 / (128 * K ^ 6) * g ^ 2 :=
      lt_of_lt_of_le hX (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity))
    rw [div_mul_eq_mul_div, one_mul, lt_div_iff₀ (by positivity)] at h1
    linarith
  have hε0half : ε0 ≤ 1 / 2 := by
    have h1 : ε0 < 1 / (128 * K ^ 6) * 1 :=
      lt_of_lt_of_le hX (mul_le_mul_of_nonneg_left (min_le_left _ _) (by positivity))
    have h2 : 1 / (128 * K ^ 6) * 1 ≤ 1 / 2 := by
      rw [mul_one, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [one_le_pow₀ hK (n := 6)]
    linarith
  -- `A = R_θ (1 + X)`
  have hAeq : A = Rc θ * (1 + X) := by
    have : Rc θ * (1 + X) = A := by
      rw [hXdef, Matrix.mul_add, Matrix.mul_sub, ← Matrix.mul_assoc, Rc_mul_neg, Matrix.one_mul,
        Matrix.mul_one]
      abel
    exact this.symm
  have hRn : ‖Rc θ‖ ≤ K := by
    have e : Rc θ = A - Rc θ * X := by
      conv_rhs => rw [hAeq]
      rw [Matrix.mul_add, Matrix.mul_one]; abel
    have h1 : ‖Rc θ‖ ≤ ‖A‖ + ‖Rc θ‖ * ε0 :=
      calc ‖Rc θ‖ = ‖A - Rc θ * X‖ := congrArg norm e
        _ ≤ ‖A‖ + ‖Rc θ * X‖ := norm_sub_le _ _
        _ ≤ ‖A‖ + ‖Rc θ‖ * ε0 := by
            rw [hε0]; exact add_le_add le_rfl (norm_mul_le _ _)
    nlinarith [mul_nonneg (norm_nonneg (Rc θ)) (by linarith : 0 ≤ 1 / 2 - ε0)]
  have hcs : ‖cos θ‖ + ‖sin θ‖ ≤ K := by
    have := norm_row_le (Rc θ) 1
    rw [Rc_apply_10, Rc_apply_11] at this; linarith
  obtain ⟨lam, hlam⟩ : ∃ l, l = cos θ + sin θ * I := ⟨_, rfl⟩
  obtain ⟨lam', hlam'⟩ : ∃ l, l = cos θ - sin θ * I := ⟨_, rfl⟩
  have hll : lam * lam' = 1 := by
    rw [hlam, hlam']
    linear_combination Complex.cos_sq_add_sin_sq (x := θ) + (-(sin θ) ^ 2) * Complex.I_sq
  have hl : ‖lam‖ ≤ K := by
    rw [hlam]
    calc ‖cos θ + sin θ * I‖ ≤ ‖cos θ‖ + ‖sin θ * I‖ := norm_add_le _ _
      _ = ‖cos θ‖ + ‖sin θ‖ := by simp
      _ ≤ K := hcs
  have hl' : ‖lam'‖ ≤ K := by
    rw [hlam']
    calc ‖cos θ - sin θ * I‖ ≤ ‖cos θ‖ + ‖sin θ * I‖ := norm_sub_le _ _
      _ = ‖cos θ‖ + ‖sin θ‖ := by simp
      _ ≤ K := hcs
  have hwnorm : ‖lam - lam'‖ = 2 * ‖sin θ‖ := by
    have : lam - lam' = 2 * sin θ * I := by rw [hlam, hlam']; ring
    rw [this]; simp
  obtain ⟨W, hWdef⟩ : ∃ W, W = ‖lam - lam'‖ := ⟨_, rfl⟩
  rw [← hWdef] at hwnorm
  have hgle : g ≤ K * W := by
    rw [hwnorm, hg]
    have := norm_Rc_two_mul_sub_one_le θ
    nlinarith [norm_nonneg (sin θ)]
  have hW : 0 < W := by
    have : 0 < K * W := lt_of_lt_of_le hg0 hgle
    by_contra h; push Not at h; nlinarith
  have hW2 : W ≤ 2 * K := by rw [hwnorm]; nlinarith [norm_nonneg (cos θ)]
  -- conjugation by `P`
  obtain ⟨X', hX'⟩ : ∃ X', X' = Pinv * X * Pm := ⟨_, rfl⟩
  have hX'n : ‖X'‖ ≤ 2 * ε0 := by
    rw [hX', hε0]
    calc ‖Pinv * X * Pm‖ ≤ ‖Pinv * X‖ * ‖Pm‖ := norm_mul_le _ _
      _ ≤ (‖Pinv‖ * ‖X‖) * ‖Pm‖ := mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (1 * ‖X‖) * 2 := mul_le_mul (mul_le_mul norm_Pinv_le le_rfl (norm_nonneg _) zero_le_one)
          norm_Pm_le (norm_nonneg _) (by positivity)
      _ = 2 * ‖X‖ := by ring
  have hPRP : Pinv * Rc θ * Pm = !![lam, 0; 0, lam'] := by
    rw [Rc_eq, ← hlam, ← hlam', conj_Pinv_Pm]
  have hA'0 : Pinv * A * Pm = !![lam, 0; 0, lam'] * (1 + X') := by
    rw [← hPRP, hX', hAeq]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Pm Pinv (X * Pm), Pm_mul_Pinv, Matrix.one_mul]
  have hA' : Pinv * A * Pm = !![lam * (1 + X' 0 0), lam * X' 0 1; lam' * X' 1 0,
      lam' * (1 + X' 1 1)] := by
    rw [hA'0]
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hdetA' : (Pinv * A * Pm).det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, hdetA, mul_one, ← Matrix.det_mul, Pinv_mul_Pm,
      Matrix.det_one]
  have hdetX : (1 + X' 0 0) * (1 + X' 1 1) - X' 0 1 * X' 1 0 = 1 := by
    have h := hdetA'
    rw [hA', Matrix.det_fin_two_of] at h
    linear_combination h - ((1 + X' 0 0) * (1 + X' 1 1) - X' 0 1 * X' 1 0) * hll
  have hη : 64 * K ^ 4 * (2 * ε0) ≤ W ^ 2 := by
    have h1 : g ^ 2 ≤ K ^ 2 * W ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ hg0.le hgle 2
    have h2 : K ^ 2 * (128 * K ^ 4 * ε0) ≤ K ^ 2 * W ^ 2 := by nlinarith
    have := le_of_mul_le_mul_left h2 (by positivity)
    linarith
  -- the real-symmetric structure
  have hRsym : ((∀ i j, (A i j).im = 0) ∧ θ.im = 0) →
      lam' = conj lam ∧ X' 1 1 = conj (X' 0 0) ∧ X' 1 0 = conj (X' 0 1) := by
    rintro ⟨hAr, hθr⟩
    have hθc : conj θ = θ := Complex.conj_eq_iff_im.mpr hθr
    have hcc : conj (cos θ) = cos θ := by rw [← Complex.cos_conj, hθc]
    have hsc : conj (sin θ) = sin θ := by rw [← Complex.sin_conj, hθc]
    have hAc : ∀ i j, conj (A i j) = A i j := fun i j => Complex.conj_eq_iff_im.mpr (hAr i j)
    have hRA : Rc (-θ) * A = !![cos θ * A 0 0 + sin θ * A 1 0, cos θ * A 0 1 + sin θ * A 1 1;
        -sin θ * A 0 0 + cos θ * A 1 0, -sin θ * A 0 1 + cos θ * A 1 1] := by
      rw [Rc, Complex.cos_neg, Complex.sin_neg, neg_neg]
      conv_lhs => rw [Matrix.eta_fin_two A]
      rw [Matrix.mul_fin_two]
    have hXc : ∀ i j, conj (X i j) = X i j := by
      intro i j
      rw [hXdef, Matrix.sub_apply, hRA]
      fin_cases i <;> fin_cases j <;> simp [hAc, hcc, hsc]
    refine ⟨?_, ?_, ?_⟩
    · rw [hlam, hlam']; simp [hcc, hsc, sub_eq_add_neg]
    · rw [hX', Pconj_eq]; simp [hXc, Complex.conj_ofNat]; ring
    · rw [hX', Pconj_eq]; simp [hXc, Complex.conj_ofNat]; ring
  obtain ⟨μ, ν, ρ, x, y, hμν, hρ, h1, h2, h3, h4, hμl, hρ1, hρx, hρy, hreal⟩ :=
    elliptic_core (Rl := (∀ i j, (A i j).im = 0) ∧ θ.im = 0) hK hll hl hl'
      ((norm_entry_le X' 0 0).trans hX'n) ((norm_entry_le X' 0 1).trans hX'n)
      ((norm_entry_le X' 1 0).trans hX'n) ((norm_entry_le X' 1 1).trans hX'n) hdetX
      rfl rfl rfl rfl (by rw [← hWdef]; exact hW) (by rw [← hWdef]; exact hη) hRsym
  rw [← hWdef] at hρ1 hρx hρy
  -- the conjugacy
  obtain ⟨B', hB'⟩ : ∃ B' : M2c, B' = !![ρ, -(ρ * x); -(ρ * y), ρ] := ⟨_, rfl⟩
  have hB'A' : B' * (Pinv * A * Pm) = !![μ, 0; 0, ν] * B' := by
    rw [hA', hB']
    ext i j; fin_cases i <;> fin_cases j
    · simp [Matrix.mul_apply, Fin.sum_univ_two]; linear_combination ρ * h1
    · simp [Matrix.mul_apply, Fin.sum_univ_two]; linear_combination ρ * h2
    · simp [Matrix.mul_apply, Fin.sum_univ_two]; linear_combination ρ * h3
    · simp [Matrix.mul_apply, Fin.sum_univ_two]; linear_combination ρ * h4
  have hdetB' : B'.det = 1 := by
    rw [hB', Matrix.det_fin_two_of]; linear_combination hρ
  obtain ⟨B, hBdef⟩ : ∃ B : M2c, B = Pm * B' * Pinv := ⟨_, rfl⟩
  have hdetB : B.det = 1 := by
    rw [hBdef, Matrix.det_mul, Matrix.det_mul, hdetB', mul_one, ← Matrix.det_mul, Pm_mul_Pinv,
      Matrix.det_one]
  have hμ0 : μ ≠ 0 := left_ne_zero_of_mul_eq_one hμν
  have hlam'0 : lam' ≠ 0 := right_ne_zero_of_mul_eq_one hll
  obtain ⟨θ', hθ'⟩ : ∃ θ' : ℂ, θ' = θ - I * Complex.log (μ * lam') := ⟨_, rfl⟩
  have hexp : Complex.exp (θ' * I) = μ := by
    have e : θ' * I = θ * I + Complex.log (μ * lam') := by
      rw [hθ']; linear_combination (-Complex.log (μ * lam')) * Complex.I_sq
    rw [e, Complex.exp_add, Complex.exp_mul_I, ← hlam, Complex.exp_log (mul_ne_zero hμ0 hlam'0)]
    linear_combination μ * hll
  have hexp' : Complex.exp (-θ' * I) = ν := by
    rw [neg_mul, Complex.exp_neg, hexp]; exact inv_eq_of_mul_eq_one_right hμν
  have hc1 : cos θ' + sin θ' * I = μ := by rw [← Complex.exp_mul_I]; exact hexp
  have hc2 : cos θ' - sin θ' * I = ν := by
    rw [Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg] at hexp'
    linear_combination hexp'
  have hRc' : Rc θ' = Pm * !![μ, 0; 0, ν] * Pinv := by rw [Rc_eq, hc1, hc2]
  have hAP : A = Pm * (Pinv * A * Pm) * Pinv := by
    simp only [Matrix.mul_assoc]
    rw [Pm_mul_Pinv, Matrix.mul_one, ← Matrix.mul_assoc, Pm_mul_Pinv, Matrix.one_mul]
  have hBA : B * A = Rc θ' * B := by
    calc B * A = Pm * B' * Pinv * (Pm * (Pinv * A * Pm) * Pinv) := by rw [← hAP, hBdef]
      _ = Pm * (B' * (Pinv * A * Pm)) * Pinv := by
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Pinv Pm, Pinv_mul_Pm, Matrix.one_mul]
      _ = Pm * (!![μ, 0; 0, ν] * B') * Pinv := by rw [hB'A']
      _ = Rc θ' * B := by
          rw [hRc', hBdef]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc Pinv Pm, Pinv_mul_Pm, Matrix.one_mul]
  -- norm estimates
  have hB'n : ‖B' - 1‖ ≤ 2 * (4 * K * (2 * ε0) / W) := by
    rw [norm_mul] at hρx hρy
    refine ell_norm_le_of_rows (by positivity) fun i => ?_
    fin_cases i
    · simp [hB', Matrix.one_apply]; linarith
    · simp [hB', Matrix.one_apply]; linarith
  have hBn : ‖B - 1‖ ≤ 32 * K * ε0 / W := by
    have e : B - 1 = Pm * (B' - 1) * Pinv := by
      rw [hBdef, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Pm_mul_Pinv]
    rw [e]
    calc ‖Pm * (B' - 1) * Pinv‖ ≤ ‖Pm * (B' - 1)‖ * ‖Pinv‖ := norm_mul_le _ _
      _ ≤ (‖Pm‖ * ‖B' - 1‖) * ‖Pinv‖ :=
          mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (2 * (2 * (4 * K * (2 * ε0) / W))) * 1 :=
          mul_le_mul (mul_le_mul norm_Pm_le hB'n (norm_nonneg _) (by norm_num)) norm_Pinv_le
            (norm_nonneg _) (by positivity)
      _ = 32 * K * ε0 / W := by ring
  have hK24 : K ^ 2 ≤ K ^ 4 := pow_le_pow_right₀ hK (by norm_num)
  refine ⟨B, θ', hdetB, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hBA, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (by rw [hdetB]; exact isUnit_one),
      Matrix.mul_one]
  · refine hBn.trans ?_
    rw [div_le_div_iff₀ hW hg0]
    have e1 : 32 * K * ε0 * g ≤ 32 * K * ε0 * (K * W) :=
      mul_le_mul_of_nonneg_left hgle (by positivity)
    have e3 : 0 ≤ ε0 * W := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hK24 e3]
  · refine hBn.trans ?_
    rw [div_le_div_iff₀ hW (by positivity)]
    have hg2 : g ^ 2 ≤ 2 * K ^ 3 * W := by
      nlinarith [mul_le_mul hgle hgle hg0.le (by positivity),
        mul_le_mul_of_nonneg_left hW2 (by positivity : (0:ℝ) ≤ K ^ 2 * W)]
    nlinarith [mul_le_mul_of_nonneg_left hg2 (by positivity : (0:ℝ) ≤ 32 * K * ε0)]
  · have hz : μ * lam' = 1 + (μ - lam) * lam' := by linear_combination hll
    have hzn : ‖(μ - lam) * lam'‖ ≤ 16 * K ^ 2 * ε0 := by
      rw [norm_mul]
      have := mul_le_mul hμl hl' (norm_nonneg _) (by positivity)
      nlinarith
    have hsmall : 32 * K ^ 2 * ε0 ≤ 1 := by
      have h1 : 128 * K ^ 4 * ε0 ≤ 4 * K ^ 2 := by nlinarith
      nlinarith
    have hlog := Complex.norm_log_one_add_half_le_self (z := (μ - lam) * lam') (by linarith)
    have e : θ' - θ = -(I * Complex.log (μ * lam')) := by rw [hθ']; ring
    rw [e, norm_neg, norm_mul, Complex.norm_I, one_mul, hz]
    nlinarith
  · intro hAr hθr
    obtain ⟨hcμ, hρc, hy⟩ := hreal ⟨hAr, hθr⟩
    obtain ⟨hl'c, -, -⟩ := hRsym ⟨hAr, hθr⟩
    constructor
    · intro i j
      apply Complex.conj_eq_iff_im.mp
      rw [hBdef, hB', hy, Pm, Pinv, Matrix.mul_fin_two, Matrix.mul_fin_two]
      fin_cases i <;> fin_cases j <;> simp [hρc, Complex.conj_ofNat] <;> ring
    · have hμn : ‖μ‖ = 1 := norm_eq_one_of_mul_conj (by rw [hcμ, hμν])
      have hl'n : ‖lam'‖ = 1 :=
        norm_eq_one_of_mul_conj (by rw [hl'c, Complex.conj_conj, mul_comm, ← hl'c, hll])
      rw [hθ']
      simp [Complex.mul_im, Complex.log_re, hμn, hl'n, hθr]

end Red.AFK
