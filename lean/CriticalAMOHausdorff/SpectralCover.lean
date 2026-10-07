/-
Copyright (c) 2026. Formalization of
  S. Becker, S. Jitomirskaya, I. Krasovsky, "Critical almost Mathieu operator: hidden
  singularity, gap continuity, and the Hausdorff dimension of the spectrum"
  (arXiv:1909.04429v2).

# The finite cover of the spectrum: Theorem `thm-cover`  (tex l. 1236–1341, 1775–1789)

We assemble Theorem 7.11 (`thm-cover`) for the chiral Jacobi operator
`Ĥ = H_{0, 2 sin(π·), α, θ}` (`chiralH α θ`), which is `CAH.chiral (α/2) (θ/2)` (`chiral_half`).

1. **Cut points** (l. 1237–1264).  From the first-return Lemma 6.2 (`first_return`,
   `return_gap` of `ContinuedFractions.lean`) we build cut points `c_k`: forward returns of
   `x₀ + mα` to `J̃_n` for `k ≥ 0`, backward returns to `-J̃_n` for `k ≤ 0`, starting from
   `x₀ ∈ (-|δ_n|, |δ_n|) (mod 1)` (density of `ℤα + ℤ`).  The gaps are in
   `{q_n, q_{n-1}}`, they are `≥ 2` for `n ≥ 4`, and the bond phases lie in `J_n (mod 1)`
   (`exists_cuts`).  Conventions: `J̃_n = Jt α n` (`ContinuedFractions.lean`) and
   `J_n = Jn α n = [-|δ_{n-1}|, |δ_{n-1}|]` (`BlockSeparation.lean`), `δ_m = delta α m`;
   `J̃_n ⊆ J_n` (`Jt_subset_Jn`) and `(-|δ_n|, |δ_n|) ⊆ J̃_n ∩ (-J̃_n)` (`Ioo_subset_Jt`).
2. **Sign gauge.**  For `b = 2 sin(π·)`, `b(x+1) = -b(x)`, so
   `B̂_N(x+1) = D B̂_N(x) D` with `D = diag((-1)^j)` (`blockMatrix_chiral_add_one`), and
   `D Γ̂^* V Γ̂ D = Γ̂^* (S V S) Γ̂` with `S = diag(1, (-1)^{N-1})`, `‖SVS‖ ≤ ‖V‖`.  Hence the
   spectra over `x ∈ J_n + ℤ` reduce to `x ∈ J_n` (`spectrum_shift`, `prop_blocks_chiral`).
3. **Bridges** to the block cover (Props 7.6–7.7, `BlockCover.lean`, written by another agent):
   `blockMatrix_chiral_eq_BNc : B̂_N(x) = LaxPair.BNc α N x`, `bdry_eq_flow_bdry`,
   `norm_le_iff_abs_eigenvalues_le` (for Hermitian `V`, `‖V‖ ≤ r ↔ ∀ i, |λ_i(V)| ≤ r`).
4. **Theorem `thm-cover`** (`thm_cover_chiral`): for irrational `α`, `n ≥ 4`, the spectrum of
   `Ĥ_{α,θ}` is contained, for *every* `θ`, in a union of `m = q_n + q_{n-1}` closed intervals of
   total length `≤ 2C'/q_n`; and `dimH_spectrum_chiral_le_half` (Theorem 1.1 for `Ĥ`).

## The hypothesis waiting on `BlockCover.lean`

The block cover (Props `prop-cover1`, 7.6–7.7) is taken as the hypothesis
`BlockCoverProp α n C₀ C'` (defined below, exactly the shape announced for `block_cover`), with
`C₀ = 4π` (the bound `‖V‖ ≤ 4π |J_n|` of the paper, l. 1338).  Everything else is proved.

The isospectrality of the chiral operator with the almost Mathieu operator (§3) is *not* used
here; the statements are about `Ĥ`.

No `sorry`s.
-/
import CriticalAMOHausdorff.BlockSeparation
import CriticalAMOHausdorff.ContinuedFractions
import CriticalAMOHausdorff.LaxPair
import CriticalAMOHausdorff.EigenvalueFlow
import CriticalAMOHausdorff.HausdorffDim

noncomputable section

open Real Set Matrix MeasureTheory
open scoped Matrix.Norms.L2Operator ENNReal

namespace CAH

/-! ## 0. The chiral operator -/

/-- The bond function `b(x) = 2 sin(π x)` of the chiral representation. -/
def chiralBond (x : ℝ) : ℝ := 2 * Real.sin (π * x)

/-- The chiral Jacobi operator `H_{0, 2 sin(π·), α, θ}`. -/
def chiralH (α θ : ℝ) : Op := jacobi (fun _ => 0) chiralBond α θ

/-- `Ĥ_{α/2, θ/2} = H_{0, 2 sin(π·), α, θ}` (proof of Thm `thm-cover`, l. 1786). -/
theorem chiral_half (α θ : ℝ) : chiral (α / 2) (θ / 2) = chiralH α θ := by
  have h : ∀ y : ℝ, 2 * π * (θ / 2 + y * (α / 2)) = π * (θ + y * α) := fun y => by ring
  simp only [chiral, chiralH, chiralBond, jacobi, h]

lemma chiralBond_add_one (y : ℝ) : chiralBond (y + 1) = -chiralBond y := by
  simp only [chiralBond, mul_add, mul_one, Real.sin_add_pi]; ring

lemma bddFun_chiralBond : BddFun chiralBond := bddFun_two_sin π

lemma hasDerivAt_chiralBond (x : ℝ) :
    HasDerivAt chiralBond (2 * (Real.cos (π * x) * π)) x := by
  unfold chiralBond
  convert ((Real.hasDerivAt_sin (π * x)).comp x
    ((hasDerivAt_id x).const_mul π)).const_mul 2 using 1 <;> simp [Function.comp_def]

lemma abs_deriv_chiralBond_le (x : ℝ) : |deriv chiralBond x| ≤ 2 * π := by
  rw [(hasDerivAt_chiralBond x).deriv, abs_mul, abs_mul, abs_of_pos pi_pos, abs_two]
  have := Real.abs_cos_le_one (π * x)
  nlinarith [pi_pos]

lemma chiralBond_periodic : Function.Periodic chiralBond 2 := by
  intro x
  simp only [chiralBond]
  rw [show π * (x + 2) = π * x + 2 * π by ring, Real.sin_add_two_pi]

/-! ## 1. Cut points from the return times -/

section Cuts

variable {α : ℝ}

lemma Jt_subset_Jn (hα : Irrational α) {n : ℕ} (hn : 1 ≤ n) : Jt α n ⊆ Jn α n := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hlt := abs_delta_succ_lt hα N
  intro y hy
  change y ∈ Icc (-|delta α (N + 1 - 1)|) (|delta α (N + 1 - 1)|)
  simp only [Nat.add_sub_cancel]
  by_cases he : Even (N + 1)
  · have hd := delta_neg_of_odd hα (Nat.even_add_one.1 he |> Nat.not_even_iff_odd.1)
    have he' := delta_pos_of_even hα he
    rw [Jt_eq_even hα hn he, Nat.add_sub_cancel] at hy
    rw [abs_of_neg hd] at hlt ⊢
    rw [abs_of_pos he'] at hlt
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  · have hd := delta_pos_of_even hα (by simpa [Nat.even_add_one] using he)
    have he' := delta_neg_of_odd hα (Nat.not_even_iff_odd.1 he)
    rw [Jt_eq_odd hα hn he, Nat.add_sub_cancel] at hy
    rw [abs_of_pos hd] at hlt ⊢
    rw [abs_of_neg he'] at hlt
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩

lemma Ioo_subset_Jt (hα : Irrational α) {n : ℕ} (hn : 1 ≤ n) :
    Ioo (-|delta α n|) (|delta α n|) ⊆ Jt α n := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hlt := abs_delta_succ_lt hα N
  intro y hy
  by_cases he : Even (N + 1)
  · have hd := delta_neg_of_odd hα (Nat.even_add_one.1 he |> Nat.not_even_iff_odd.1)
    have he' := delta_pos_of_even hα he
    rw [Jt_eq_even hα hn he, Nat.add_sub_cancel]
    rw [abs_of_neg hd, abs_of_pos he'] at hlt
    rw [abs_of_pos he'] at hy
    exact ⟨by linarith [hy.1], hy.2⟩
  · have hd := delta_pos_of_even hα (by simpa [Nat.even_add_one] using he)
    have he' := delta_neg_of_odd hα (Nat.not_even_iff_odd.1 he)
    rw [Jt_eq_odd hα hn he, Nat.add_sub_cancel]
    rw [abs_of_pos hd, abs_of_neg he'] at hlt
    rw [abs_of_neg he'] at hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩

lemma neg_mem_Jn {n : ℕ} {y : ℝ} (hy : y ∈ Jn α n) : -y ∈ Jn α n :=
  ⟨by linarith [hy.2], by linarith [hy.1]⟩

lemma returns_succ (hα : Irrational α) {n : ℕ} (hn : 1 ≤ n) {y : ℝ} {t : ℕ}
    (h : Returns α n y t) : ∃ N : ℕ, 1 ≤ N ∧ Returns α n y (t + N) := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨N, -, hN1, ⟨m', hm'⟩, -⟩ := first_return hα hn hm
  refine ⟨N, hN1, m + m', ?_⟩
  convert hm' using 1
  push_cast; ring

lemma returns_infinite (hα : Irrational α) {n : ℕ} (hn : 1 ≤ n) {y : ℝ}
    (h0 : Returns α n y 0) : {t | Returns α n y t}.Infinite := by
  have key : ∀ a : ℕ, ∃ t, Returns α n y t ∧ a < t := by
    intro a
    induction a with
    | zero =>
      obtain ⟨N, hN, h⟩ := returns_succ hα hn h0
      exact ⟨0 + N, h, by omega⟩
    | succ a ih =>
      obtain ⟨t, ht, hat⟩ := ih
      obtain ⟨N, hN, h⟩ := returns_succ hα hn ht
      exact ⟨t + N, h, by omega⟩
  refine Set.infinite_of_not_bddAbove ?_
  rintro ⟨M, hM⟩
  obtain ⟨t, ht, hMt⟩ := key M
  exact absurd (hM ht) (not_le.2 hMt)

/-- Consecutive return times (enumerated by `Nat.nth`) differ by `q_n` or `q_{n-1}`. -/
lemma nth_returns_gap (hα : Irrational α) {n : ℕ} (hn : 1 ≤ n) {y : ℝ}
    (h0 : Returns α n y 0) (j : ℕ) :
    ((Nat.nth (Returns α n y) (j + 1) : ℤ) - Nat.nth (Returns α n y) j = qN α n) ∨
      ((Nat.nth (Returns α n y) (j + 1) : ℤ) - Nat.nth (Returns α n y) j = qN α (n - 1)) := by
  have hinf := returns_infinite hα hn h0
  have hlt : Nat.nth (Returns α n y) j < Nat.nth (Returns α n y) (j + 1) :=
    Nat.nth_strictMono hinf (Nat.lt_succ_self j)
  have h := return_gap hα hn (Nat.nth_mem_of_infinite hinf j) (Nat.nth_mem_of_infinite hinf (j + 1))
    hlt (fun k h1 h2 hk => by have := Nat.le_nth_of_lt_nth_succ h2 hk; omega)
  rcases h with h | h
  · left; rw [← h]; push_cast [hlt.le]; ring
  · right; rw [← h]; push_cast [hlt.le]; ring

lemma two_le_qN (hα : Irrational α) {n : ℕ} (hn : 4 ≤ n) : 2 ≤ qN α (n - 1) := by
  have h := two_rpow_le_q hα (n - 1)
  have he : (1 : ℝ) ≤ (((n - 1 : ℕ) : ℝ) - 1) / 2 := by
    rw [Nat.cast_sub (by omega)]
    have : (4 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ ((((n - 1 : ℕ) : ℝ) - 1) / 2) := by
    calc (2 : ℝ) = 2 ^ (1 : ℝ) := (Real.rpow_one 2).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) he
  have : (2 : ℝ) ≤ (qN α (n - 1) : ℝ) := by rw [qN_cast hα]; linarith
  exact_mod_cast this

/-- **Cut points** (l. 1237–1264): for irrational `α`, `n ≥ 4` and any `θ` there are cut points
`c_k` with gaps `N_k ∈ {q_n, q_{n-1}}`, `N_k ≥ 2`, and bond phases `x_k = θ + (c_k - 1)α ∈ J_n`
modulo `1` — exactly the hypotheses of `prop_blocks`. -/
theorem exists_cuts (hα : Irrational α) {n : ℕ} (hn : 4 ≤ n) (θ : ℝ) :
    ∃ c : ℤ → ℤ, (∀ k, c k + 2 ≤ c (k + 1)) ∧
      (∀ k, ((c (k + 1) - c k : ℤ) : ℝ) = q α n ∨ ((c (k + 1) - c k : ℤ) : ℝ) = q α (n - 1)) ∧
      (∀ k, ∃ m : ℤ, θ + (c k - 1) * α - m ∈ Jn α n) := by
  have hn1 : 1 ≤ n := by omega
  -- a starting point `x₀ ∈ (-|δ_n|, |δ_n|) (mod 1)` (density of `ℤα + ℤ`)
  have hδ : 0 < |delta α n| := lt_trans (by
    have := q_pos hα (n + 1); have := q_pos hα n; positivity) (abs_delta_bounds hα n).1
  obtain ⟨m₀, j₀, hm₀⟩ : ∃ m₀ j₀ : ℤ, |θ + (m₀ - 1) * α - j₀| < |delta α n| := by
    have hd : Dense (AddSubgroup.closure {α, (1 : ℝ)} : Set ℝ) :=
      dense_addSubgroupClosure_pair_iff.2 (by simpa using hα)
    obtain ⟨z, hz, hzS⟩ := Metric.dense_iff.1 hd (α - θ) _ hδ
    obtain ⟨m, j, rfl⟩ := AddSubgroup.mem_closure_pair.1 hzS
    refine ⟨m, -j, ?_⟩
    rw [Metric.mem_ball, Real.dist_eq] at hz
    simp only [zsmul_eq_mul, mul_one] at hz
    convert hz using 2; push_cast; ring
  set x₀ := θ + (m₀ - 1) * α with hx₀
  have hf0 : Returns α n x₀ 0 :=
    ⟨j₀, by simpa using Ioo_subset_Jt hα hn1 (abs_lt.1 hm₀)⟩
  have hb0 : Returns α n (-x₀) 0 := by
    refine ⟨-j₀, ?_⟩
    have := Ioo_subset_Jt hα hn1 (abs_lt.1 (show |-(x₀ - j₀)| < |delta α n| by
      rw [abs_neg]; exact hm₀))
    convert this using 1; push_cast; ring
  set F := Nat.nth (Returns α n x₀)
  set Bk := Nat.nth (Returns α n (-x₀))
  have hF0 : F 0 = 0 := Nat.nth_zero_of_zero hf0
  have hB0 : Bk 0 = 0 := Nat.nth_zero_of_zero hb0
  let c : ℤ → ℤ := fun k => if 0 ≤ k then m₀ + F k.toNat else m₀ - Bk (-k).toNat
  have hc_nat : ∀ t : ℕ, c t = m₀ + F t := fun t => by simp [c]
  have hc_neg : ∀ t : ℕ, c (-(t : ℤ)) = m₀ - Bk t := by
    intro t
    rcases Nat.eq_zero_or_pos t with rfl | ht
    · simp [c, hF0, hB0]
    · have : ¬ (0 ≤ -(t : ℤ)) := by omega
      simp only [c]
      rw [if_neg this]
      simp
  have hgapZ : ∀ k, c (k + 1) - c k = qN α n ∨ c (k + 1) - c k = qN α (n - 1) := by
    have hpos : ∀ t : ℕ, c ((t : ℤ) + 1) - c t = qN α n ∨ c ((t : ℤ) + 1) - c t = qN α (n - 1) := by
      intro t
      rw [show (t : ℤ) + 1 = ((t + 1 : ℕ) : ℤ) by push_cast; ring, hc_nat, hc_nat]
      have := nth_returns_gap hα hn1 hf0 t
      rcases this with h | h
      · left; linarith
      · right; linarith
    intro k
    obtain ⟨t, rfl | rfl⟩ := Int.eq_nat_or_neg k
    · exact hpos t
    · rcases t with _ | s
      · simpa using hpos 0
      · rw [show -((s + 1 : ℕ) : ℤ) + 1 = -(s : ℤ) by push_cast; ring, hc_neg, hc_neg]
        have := nth_returns_gap hα hn1 hb0 s
        rcases this with h | h
        · left; linarith
        · right; linarith
  have h2 := two_le_qN hα hn
  have h3 : qN α (n - 1) ≤ qN α n := by
    have := qN_le_succ hα (n - 1); rwa [Nat.sub_add_cancel hn1] at this
  refine ⟨c, fun k => ?_, fun k => ?_, fun k => ?_⟩
  · rcases hgapZ k with h | h <;> push_cast at h <;> omega
  · rcases hgapZ k with h | h
    · left; rw [h]; exact_mod_cast qN_cast hα n
    · right; rw [h]; exact_mod_cast qN_cast hα (n - 1)
  · obtain ⟨t, rfl | rfl⟩ := Int.eq_nat_or_neg k
    · obtain ⟨j, hj⟩ := Nat.nth_mem_of_infinite (returns_infinite hα hn1 hf0) t
      refine ⟨j, ?_⟩
      have := Jt_subset_Jn hα hn1 hj
      rw [hc_nat]
      convert this using 1; simp only [F, hx₀]; push_cast; ring
    · obtain ⟨j, hj⟩ := Nat.nth_mem_of_infinite (returns_infinite hα hn1 hb0) t
      refine ⟨-j, ?_⟩
      have := neg_mem_Jn (Jt_subset_Jn hα hn1 hj)
      rw [hc_neg]
      convert this using 1; simp only [Bk, hx₀]; push_cast; ring

end Cuts

/-! ## 2. The sign gauge -/

section Gauge

/-- `D = diag((-1)^j)`. -/
def gaugeD (N : ℕ) : Matrix (Fin N) (Fin N) ℂ := diagonal fun j => (-1 : ℂ) ^ (j : ℕ)

/-- `S = diag(1, (-1)^{N-1})`. -/
def gaugeS (N : ℕ) : Matrix (Fin 2) (Fin 2) ℂ :=
  diagonal fun i => if (i : ℕ) = 0 then 1 else (-1 : ℂ) ^ (N - 1)

lemma neg_one_pow_mul_self (j : ℕ) : (-1 : ℂ) ^ j * (-1 : ℂ) ^ j = 1 := by
  rw [← mul_pow]; norm_num

lemma gaugeD_mul_self (N : ℕ) : gaugeD N * gaugeD N = 1 := by
  rw [gaugeD, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext j; exact neg_one_pow_mul_self _

lemma gaugeS_mul_self (N : ℕ) : gaugeS N * gaugeS N = 1 := by
  rw [gaugeS, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext i
  split_ifs
  · norm_num
  · exact neg_one_pow_mul_self _

lemma gaugeD_conjTranspose (N : ℕ) : (gaugeD N)ᴴ = gaugeD N := by
  rw [gaugeD, diagonal_conjTranspose]
  congr 1; funext j; simp

lemma gaugeS_conjTranspose (N : ℕ) : (gaugeS N)ᴴ = gaugeS N := by
  rw [gaugeS, diagonal_conjTranspose]
  congr 1; funext i; simp only [Pi.star_apply]; split_ifs <;> simp

lemma norm_gaugeS_le (N : ℕ) : ‖gaugeS N‖ ≤ 1 := by
  rw [gaugeS, l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => ?_
  split_ifs <;> simp

lemma bdry_mul_gaugeD (N : ℕ) : bdry N * gaugeD N = gaugeS N * bdry N := by
  ext i j
  rw [gaugeD, gaugeS, mul_diagonal, diagonal_mul]
  simp only [bdry, of_apply]
  fin_cases i
  · by_cases hj : (j : ℕ) = 0
    · simp [hj]
    · simp [hj]
  · by_cases hj : (j : ℕ) + 1 = N
    · have : (j : ℕ) = N - 1 := by omega
      simp [hj, this]
    · simp [hj]

lemma gaugeD_mul_conjTranspose_bdry (N : ℕ) :
    gaugeD N * (bdry N)ᴴ = (bdry N)ᴴ * gaugeS N := by
  have h := congrArg conjTranspose (bdry_mul_gaugeD N)
  simpa only [conjTranspose_mul, gaugeD_conjTranspose, gaugeS_conjTranspose] using h

/-- **Sign gauge of the blocks:** `B̂_N(x+1) = D B̂_N(x) D` for `b = 2 sin(π·)`, `v = 0`. -/
lemma blockMatrix_chiral_add_one (α : ℝ) (N : ℕ) (x : ℝ) :
    blockMatrix (fun _ => 0) chiralBond α N (x + 1) =
      gaugeD N * blockMatrix (fun _ => 0) chiralBond α N x * gaugeD N := by
  have e : ∀ y : ℝ, chiralBond (x + 1 + y) = -chiralBond (x + y) := fun y => by
    rw [show x + 1 + y = (x + y) + 1 by ring, chiralBond_add_one]
  ext i j
  rw [gaugeD, mul_diagonal, diagonal_mul]
  simp only [blockMatrix, of_apply]
  by_cases hij : i = j
  · subst hij; simp
  · simp only [if_neg hij]
    by_cases h1 : (j : ℕ) = i + 1
    · simp only [if_pos h1, e]
      have hs := neg_one_pow_mul_self (i : ℕ)
      rw [h1, pow_succ]
      push_cast
      linear_combination (↑(chiralBond (x + ((i : ℕ) + 1) * α)) : ℂ) * hs
    · simp only [if_neg h1]
      by_cases h3 : (i : ℕ) = j + 1
      · simp only [if_pos h3, e]
        have hs := neg_one_pow_mul_self (j : ℕ)
        rw [h3, pow_succ]
        push_cast
        linear_combination (↑(chiralBond (x + ((j : ℕ) + 1) * α)) : ℂ) * hs
      · simp [if_neg h3]

/-- Conjugation by an involution preserves the spectrum. -/
lemma spectrum_conj_involution {n : Type*} [Fintype n] [DecidableEq n] (D M : Matrix n n ℂ)
    (hD : D * D = 1) : spectrum ℝ (D * M * D) = spectrum ℝ M := by
  let u : (Matrix n n ℂ)ˣ := ⟨D, D, hD, hD⟩
  ext E
  simp only [spectrum.mem_iff]
  have : algebraMap ℝ (Matrix n n ℂ) E - D * M * D = D * (algebraMap ℝ _ E - M) * D := by
    rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.mul_one, Matrix.smul_mul, hD]
  rw [this]
  change ¬IsUnit ((u : Matrix n n ℂ) * _ * (u : Matrix n n ℂ)) ↔ _
  rw [Units.isUnit_mul_units, Units.isUnit_units_mul]

lemma gauge_conj (α : ℝ) (N : ℕ) (x : ℝ) (W : Matrix (Fin 2) (Fin 2) ℂ) :
    gaugeD N * (blockMatrix (fun _ => 0) chiralBond α N x + (bdry N)ᴴ * W * bdry N) * gaugeD N =
      blockMatrix (fun _ => 0) chiralBond α N (x + 1) +
        (bdry N)ᴴ * (gaugeS N * W * gaugeS N) * bdry N := by
  rw [blockMatrix_chiral_add_one, Matrix.mul_add, Matrix.add_mul]
  congr 1
  calc gaugeD N * ((bdry N)ᴴ * W * bdry N) * gaugeD N
      = (gaugeD N * (bdry N)ᴴ) * W * (bdry N * gaugeD N) := by simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [gaugeD_mul_conjTranspose_bdry, bdry_mul_gaugeD]; simp only [Matrix.mul_assoc]

lemma gaugeS_conj_isHermitian {N : ℕ} {V : Matrix (Fin 2) (Fin 2) ℂ} (hV : V.IsHermitian) :
    (gaugeS N * V * gaugeS N).IsHermitian := by
  rw [IsHermitian, conjTranspose_mul, conjTranspose_mul, gaugeS_conjTranspose, hV.eq,
    Matrix.mul_assoc]

lemma norm_gaugeS_conj_le (N : ℕ) (V : Matrix (Fin 2) (Fin 2) ℂ) :
    ‖gaugeS N * V * gaugeS N‖ ≤ ‖V‖ := by
  have h1 := norm_gaugeS_le N
  calc ‖gaugeS N * V * gaugeS N‖ ≤ ‖gaugeS N * V‖ * ‖gaugeS N‖ := l2_opNorm_mul _ _
    _ ≤ (‖gaugeS N‖ * ‖V‖) * ‖gaugeS N‖ := by gcongr; exact l2_opNorm_mul _ _
    _ ≤ (1 * ‖V‖) * 1 := by gcongr
    _ = ‖V‖ := by ring

/-- **Integer shifts of the phase** for the chiral blocks: for every `m ∈ ℤ` and Hermitian `V`
there is a Hermitian `V'` with `‖V'‖ ≤ ‖V‖` and
`σ(B̂_N(y+m) + Γ̂^* V Γ̂) = σ(B̂_N(y) + Γ̂^* V' Γ̂)`. -/
theorem spectrum_shift (α : ℝ) (N : ℕ) (y : ℝ) (m : ℤ) :
    ∀ V : Matrix (Fin 2) (Fin 2) ℂ, V.IsHermitian → ∃ V' : Matrix (Fin 2) (Fin 2) ℂ,
      V'.IsHermitian ∧ ‖V'‖ ≤ ‖V‖ ∧
      spectrum ℝ (blockMatrix (fun _ => 0) chiralBond α N (y + m) + (bdry N)ᴴ * V * bdry N) =
        spectrum ℝ (blockMatrix (fun _ => 0) chiralBond α N y + (bdry N)ᴴ * V' * bdry N) := by
  induction m using Int.induction_on with
  | zero => intro V hV; exact ⟨V, hV, le_rfl, by simp⟩
  | succ m ih =>
    intro V hV
    obtain ⟨V', hV', hn, hs⟩ := ih _ (gaugeS_conj_isHermitian (N := N) hV)
    refine ⟨V', hV', hn.trans (norm_gaugeS_conj_le N V), ?_⟩
    simp only [Int.cast_natCast] at hs
    rw [← hs]
    have := gauge_conj α N (y + m) (gaugeS N * V * gaugeS N)
    rw [show gaugeS N * (gaugeS N * V * gaugeS N) * gaugeS N = V by
      simp only [← Matrix.mul_assoc, gaugeS_mul_self, Matrix.one_mul]
      rw [Matrix.mul_assoc, gaugeS_mul_self, Matrix.mul_one]] at this
    rw [show y + ((m + 1 : ℤ) : ℝ) = y + m + 1 by push_cast; ring, ← this,
      spectrum_conj_involution _ _ (gaugeD_mul_self N)]
  | pred m ih =>
    intro V hV
    obtain ⟨V', hV', hn, hs⟩ := ih _ (gaugeS_conj_isHermitian (N := N) hV)
    refine ⟨V', hV', hn.trans (norm_gaugeS_conj_le N V), ?_⟩
    rw [← hs]
    have := gauge_conj α N (y + ((-(m : ℤ) - 1 : ℤ) : ℝ)) V
    rw [show y + ((-(m : ℤ) - 1 : ℤ) : ℝ) + 1 = y + ((-(m : ℤ) : ℤ) : ℝ) by push_cast; ring]
      at this
    rw [← this, spectrum_conj_involution _ _ (gaugeD_mul_self N)]

end Gauge

/-! ## 3. Proposition `prop-blocks` for the chiral operator -/

/-- **Proposition `prop-blocks` for `Ĥ`** (l. 1318–1341): for irrational `α`, `n ≥ 4`, any `θ`,
`σ(Ĥ) ⊆ closure ⋃_{N ∈ {q_n, q_{n-1}}} ⋃_{x ∈ J_n} ⋃_{V = V^*, ‖V‖ ≤ 4π|J_n|}
σ(B̂_N(x) + Γ̂_N^* V Γ̂_N)`. -/
theorem prop_blocks_chiral {α : ℝ} (hα : Irrational α) {n : ℕ} (hn : 4 ≤ n) (θ : ℝ) :
    spectrum ℝ (chiralH α θ) ⊆
      closure (⋃ N ∈ {N : ℕ | (N : ℝ) = q α n ∨ (N : ℝ) = q α (n - 1)},
        ⋃ x ∈ Jn α n,
        ⋃ V ∈ {V : Matrix (Fin 2) (Fin 2) ℂ | V.IsHermitian ∧ ‖V‖ ≤ 4 * π * JnLen α n},
          spectrum ℝ (blockMatrix (fun _ => 0) chiralBond α N x + (bdry N)ᴴ * V * bdry N)) := by
  obtain ⟨c, hc, hgap, hx⟩ := exists_cuts hα hn θ
  refine (prop_blocks (bddFun_const 0) bddFun_chiralBond
    (fun x => (hasDerivAt_chiralBond x).differentiableAt) abs_deriv_chiralBond_le
    (Or.inr ⟨chiralBond_periodic, by simp [chiralBond], by simp [chiralBond]⟩)
    α θ n c hc hgap hx).trans (closure_mono ?_)
  refine Set.iUnion₂_subset fun N hN => Set.subset_iUnion₂_of_subset N hN ?_
  refine Set.iUnion₂_subset fun x hx' => ?_
  obtain ⟨m, hm⟩ := hx'
  refine Set.iUnion₂_subset fun V hV => ?_
  obtain ⟨V', hV', hVn, hs⟩ := spectrum_shift α N (x - m) m V hV.1
  rw [sub_add_cancel] at hs
  rw [hs]
  refine Set.subset_iUnion₂_of_subset (x - m) hm ?_
  refine Set.subset_iUnion₂_of_subset V' ⟨hV', hVn.trans ?_⟩ subset_rfl
  have := hV.2; linarith

/-! ## 4. Bridges to the block cover -/

/-- `B̂_N(x)` for `v = 0`, `b = 2 sin(π·)` is the block `B_N(x)` of (BN) (`LaxPair.BNc`). -/
theorem blockMatrix_chiral_eq_BNc (α : ℝ) (N : ℕ) (x : ℝ) :
    blockMatrix (fun _ => 0) chiralBond α N x = LaxPair.BNc α N x := by
  ext i j
  simp only [blockMatrix, LaxPair.BNc, LaxPair.BN, Matrix.map_apply, of_apply, chiralBond]
  by_cases hij : i = j
  · subst hij; simp
  · simp only [if_neg hij]
    by_cases h1 : (j : ℕ) = i + 1
    · simp only [if_pos h1]
    · simp only [if_neg h1]
      by_cases h3 : (i : ℕ) = j + 1
      · simp only [if_pos h3]
      · simp only [if_neg h3, Complex.ofReal_zero]

/-- `CAH.bdry = CAH.Flow.bdry`. -/
theorem bdry_eq_flow_bdry (N : ℕ) : bdry N = Flow.bdry N := rfl

/-- For a Hermitian matrix, `‖V‖ ≤ r` iff all eigenvalues have modulus `≤ r`. -/
theorem norm_le_iff_abs_eigenvalues_le {n : Type*} [Fintype n] [DecidableEq n]
    {V : Matrix n n ℂ} (hV : V.IsHermitian) {r : ℝ} (hr : 0 ≤ r) :
    ‖V‖ ≤ r ↔ ∀ i, |hV.eigenvalues i| ≤ r := by
  refine ⟨fun h i => ?_, hV.norm_le_of_abs_eigenvalues_le hr⟩
  refine le_trans ?_ h
  set x := hV.eigenvectorBasis i
  have hx : ‖x‖ = 1 := hV.eigenvectorBasis.orthonormal.1 i
  have h1 := l2_opNorm_mulVec V x
  rw [hV.mulVec_eigenvectorBasis, hx, mul_one, RCLike.real_smul_eq_coe_smul (K := ℂ),
    map_smul, norm_smul, RCLike.norm_ofReal] at h1
  have h2 : (EuclideanSpace.equiv n ℂ).symm (⇑(hV.eigenvectorBasis i)) = x := by
    first | rfl | simp [x]
  rw [h2, hx, mul_one] at h1
  exact h1

/-- **The block cover hypothesis** (Props `prop-cover1`, 7.6–7.7, to be supplied by
`BlockCover.lean`): for `N ∈ {q_n, q_{n-1}}` there are `N` closed intervals `[lo_j, hi_j]` of
total length `≤ C'/q_n` covering `σ(B_N(x) + Γ̂_N^* V Γ̂_N)` for all `x ∈ J_n` and all Hermitian
`V` with eigenvalues bounded by `C₀ |J_n|`. -/
def BlockCoverProp (α : ℝ) (n : ℕ) (C₀ C' : ℝ) : Prop :=
  ∀ N : ℕ, (N = qN α n ∨ N = qN α (n - 1)) → ∃ lo hi : Fin N → ℝ, (∀ j, lo j ≤ hi j) ∧
    ∑ j, (hi j - lo j) ≤ C' / q α n ∧
    ∀ x ∈ Icc (-|delta α (n - 1)|) (|delta α (n - 1)|), ∀ V : Matrix (Fin 2) (Fin 2) ℂ,
      ∀ hV : V.IsHermitian, (∀ i, |hV.eigenvalues i| ≤ C₀ * JnLen α n) →
        spectrum ℝ (LaxPair.BNc α N x + (Flow.bdry N)ᴴ * V * Flow.bdry N) ⊆
          ⋃ j, Icc (lo j) (hi j)

/-! ## 5. Theorem `thm-cover` -/

/-- **Theorem `thm-cover`** (l. 1775–1789) for the chiral operator, conditional on the block
cover (`BlockCoverProp α n (4π) C'`): for irrational `α` and `n ≥ 4` there are
`m = q_n + q_{n-1}` closed intervals `[a_i, b_i]`, independent of `θ`, of total length
`≤ 2C'/q_n`, with `σ(Ĥ_{α,θ}) ⊆ ⋃_i [a_i, b_i]` for every `θ`. -/
theorem thm_cover_chiral {α : ℝ} (hα : Irrational α) {n : ℕ} (hn : 4 ≤ n) {C' : ℝ}
    (hBC : BlockCoverProp α n (4 * π) C') :
    ∃ (m : ℕ) (a b : Fin m → ℝ), (∀ i, a i ≤ b i) ∧ (m : ℝ) ≤ q α n + q α (n - 1) ∧
      ∑ i, (b i - a i) ≤ 2 * C' / q α n ∧
      ∀ θ : ℝ, spectrum ℝ (chiralH α θ) ⊆ ⋃ i, Icc (a i) (b i) := by
  obtain ⟨lo₁, hi₁, hle₁, hlen₁, hcov₁⟩ := hBC (qN α n) (Or.inl rfl)
  obtain ⟨lo₂, hi₂, hle₂, hlen₂, hcov₂⟩ := hBC (qN α (n - 1)) (Or.inr rfl)
  refine ⟨qN α n + qN α (n - 1), Fin.append lo₁ lo₂, Fin.append hi₁ hi₂, ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using hle₁ j
    · simpa using hle₂ j
  · push_cast; rw [qN_cast hα, qN_cast hα]
  · rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [two_mul, add_div]; exact add_le_add hlen₁ hlen₂
  · intro θ
    set T := ⋃ i, Icc (Fin.append lo₁ lo₂ i) (Fin.append hi₁ hi₂ i)
    have hT : IsClosed T := isClosed_iUnion_of_finite fun i => isClosed_Icc
    refine (prop_blocks_chiral hα hn θ).trans (closure_minimal ?_ hT)
    refine Set.iUnion₂_subset fun N hN => Set.iUnion₂_subset fun x hx =>
      Set.iUnion₂_subset fun V hV => ?_
    have hr : 0 ≤ 4 * π * JnLen α n := by
      have := pi_pos; unfold JnLen; positivity
    have heig := (norm_le_iff_abs_eigenvalues_le hV.1 hr).1 hV.2
    rw [blockMatrix_chiral_eq_BNc, bdry_eq_flow_bdry]
    rcases hN with hN | hN
    · have hNe : N = qN α n := by
        have : (N : ℝ) = (qN α n : ℝ) := by rw [hN, qN_cast hα]
        exact_mod_cast this
      subst hNe
      refine (hcov₁ x hx V hV.1 heig).trans (Set.iUnion_subset fun j => ?_)
      exact Set.subset_iUnion_of_subset (Fin.castAdd (qN α (n - 1)) j) (by simp)
    · have hNe : N = qN α (n - 1) := by
        have : (N : ℝ) = (qN α (n - 1) : ℝ) := by rw [hN, qN_cast hα]
        exact_mod_cast this
      subst hNe
      refine (hcov₂ x hx V hV.1 heig).trans (Set.iUnion_subset fun j => ?_)
      exact Set.subset_iUnion_of_subset (Fin.natAdd (qN α n) j) (by simp)

/-- **Theorem 1.1 for `Ĥ`** (§8), conditional on the block cover for all `n ≥ 4`:
`dim_H σ(Ĥ_{α,θ}) ≤ 1/2` and `𝓗^{1/2}(σ(Ĥ_{α,θ})) < ∞`. -/
theorem dimH_spectrum_chiral_le_half {α : ℝ} (hα : Irrational α) {C' : ℝ} (hC' : 0 ≤ C')
    (hBC : ∀ n ≥ 4, BlockCoverProp α n (4 * π) C') (θ : ℝ) :
    dimH (spectrum ℝ (chiralH α θ)) ≤ 1 / 2 ∧ μH[1 / 2] (spectrum ℝ (chiralH α θ)) < ⊤ := by
  have key : ∀ n : ℕ, ∃ (m : ℕ) (a b : Fin m → ℝ), 4 ≤ n → (∀ i, a i ≤ b i) ∧
      (m : ℝ) ≤ q α n + q α (n - 1) ∧ ∑ i, (b i - a i) ≤ 2 * C' / q α n ∧
      spectrum ℝ (chiralH α θ) ⊆ ⋃ i, Icc (a i) (b i) := by
    intro n
    by_cases hn : 4 ≤ n
    · obtain ⟨m, a, b, h1, h2, h3, h4⟩ := thm_cover_chiral hα hn (hBC n hn)
      exact ⟨m, a, b, fun _ => ⟨h1, h2, h3, h4 θ⟩⟩
    · exact ⟨0, Fin.elim0, Fin.elim0, fun h => absurd h hn⟩
  choose m a b h using key
  exact dimH_le_half_of_cfCovers hα (by positivity) m a b (fun n hn => (h n hn).1)
    (fun n hn => (h n hn).2.2.2) (fun n hn => (h n hn).2.1) (fun n hn => (h n hn).2.2.1)

end CAH
