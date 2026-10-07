/-
Copyright (c) 2026. Formalization of
  S. Becker, S. Jitomirskaya, I. Krasovsky, "Critical almost Mathieu operator: hidden
  singularity, gap continuity, and the Hausdorff dimension of the spectrum"
  (arXiv:1909.04429v2).

# Test functions of the AMS argument  (paper §5, Lemma 5.3 `lemma-commut0`)

Paper references (`Arxiv_version-5.tex`):
* the sums `S_{+,m}`, `S_{-,m}` (unnumbered display, tex l. 846–850);
* the test function `f_{m,L}` (tex l. 851–861);
* Lemma 5.3 (`lemma-commut0`, tex l. 863–912): the commutator matrix elements (5.5)
  (`commut0`) and the bound (5.6) (`sumest`)  `(L+1)/2 ≤ ∑_m f_{m,L}(n)² ≤ 2L+1`;
* the averaging step "Hence, there exists some `m` with `f_{m,L}φ_ε ≠ 0` such that …"
  (tex l. 946–951).

We work with an arbitrary sequence of positive weights `w : ℤ → ℝ` (in the paper
`w_k = 1/|b_k|`).  The commutator `[f, H]` of the diagonal operator `f` with a Jacobi
matrix with off-diagonal entries `b_j` has `(j, j+1)` entry `(f(j) - f(j+1)) b_j`; the
scalar identity (5.5) for this quantity is `testFn_sub_succ_mul_right/left/out`.  The
operator-level use is in `GapContinuity.lean`.

All results in this file are proved completely (no `sorry`).
-/
import Mathlib

noncomputable section

open Finset

namespace CAH

/-! ### Definitions -/

section Defs

variable (w : ℤ → ℝ) (L : ℕ)

/-- `S_{+,m} = ∑_{k=m}^{m+L-1} w_k`. -/
def Splus (m : ℤ) : ℝ := ∑ k ∈ Ico m (m + L), w k

/-- `S_{-,m} = ∑_{k=m-L}^{m-1} w_k`. -/
def Sminus (m : ℤ) : ℝ := ∑ k ∈ Ico (m - L) m, w k

/-- The test function `f_{m,L}(n)` of the paper (tex l. 851–861), centred at `m`:
`1` at `n = m`, `1 - S_{+,m}⁻¹ ∑_{k=m}^{n-1} w_k` for `m < n ≤ m+L`,
`1 - S_{-,m}⁻¹ ∑_{k=n}^{m-1} w_k` for `m-L ≤ n < m`, and `0` otherwise. -/
def testFn (m n : ℤ) : ℝ :=
  if n = m then 1
  else if m < n ∧ n ≤ m + L then 1 - (∑ k ∈ Ico m n, w k) / Splus w L m
  else if m - L ≤ n ∧ n < m then 1 - (∑ k ∈ Ico n m, w k) / Sminus w L m
  else 0

end Defs

/-! ### Elementary properties -/

section Props

variable {w : ℤ → ℝ} {L : ℕ}

lemma Sminus_eq_Splus (m : ℤ) : Sminus w L m = Splus w L (m - L) := by
  simp [Sminus, Splus]

lemma sum_Ico_split {a b c : ℤ} (hab : a ≤ b) (hbc : b ≤ c) (f : ℤ → ℝ) :
    ∑ k ∈ Ico a c, f k = ∑ k ∈ Ico a b, f k + ∑ k ∈ Ico b c, f k := by
  rw [← sum_union (Ico_disjoint_Ico_consecutive a b c), Ico_union_Ico_eq_Ico hab hbc]

lemma sum_Ico_succ_right {a b : ℤ} (hab : a ≤ b) (f : ℤ → ℝ) :
    ∑ k ∈ Ico a (b + 1), f k = ∑ k ∈ Ico a b, f k + f b := by
  rw [sum_Ico_split hab (by omega)]
  congr 1
  rw [Ico_add_one_right_eq_Icc, Icc_self, sum_singleton]

lemma sum_Ico_nonneg' (hw : ∀ k, 0 < w k) (a b : ℤ) : 0 ≤ ∑ k ∈ Ico a b, w k :=
  sum_nonneg fun k _ => (hw k).le

lemma Splus_pos (hw : ∀ k, 0 < w k) (hL : 1 ≤ L) (m : ℤ) : 0 < Splus w L m :=
  sum_pos (fun k _ => hw k) ⟨m, by simp; omega⟩

lemma Sminus_pos (hw : ∀ k, 0 < w k) (hL : 1 ≤ L) (m : ℤ) : 0 < Sminus w L m := by
  rw [Sminus_eq_Splus]; exact Splus_pos hw hL _

lemma testFn_right {m n : ℤ} (hm : m ≤ n) (hn : n ≤ m + L) :
    testFn w L m n = 1 - (∑ k ∈ Ico m n, w k) / Splus w L m := by
  unfold testFn
  by_cases h : n = m
  · subst h; simp
  · rw [if_neg h, if_pos ⟨lt_of_le_of_ne hm (Ne.symm h), hn⟩]

lemma testFn_left {m n : ℤ} (hm : m - L ≤ n) (hn : n ≤ m) :
    testFn w L m n = 1 - (∑ k ∈ Ico n m, w k) / Sminus w L m := by
  unfold testFn
  by_cases h : n = m
  · subst h; simp
  · rw [if_neg h, if_neg (by omega), if_pos ⟨hm, lt_of_le_of_ne hn h⟩]

lemma testFn_out {m n : ℤ} (h : n < m - L ∨ m + L < n) : testFn w L m n = 0 := by
  unfold testFn
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

/-- `f_{m,L}(n) = 0` for `|n - m| ≥ L`. -/
lemma testFn_eq_zero (hw : ∀ k, 0 < w k) (hL : 1 ≤ L) {m n : ℤ} (h : n ≤ m - L ∨ m + L ≤ n) :
    testFn w L m n = 0 := by
  rcases h with h | h
  · rcases h.lt_or_eq with h | h
    · exact testFn_out (Or.inl h)
    · rw [testFn_left (by omega) (by omega), h, ← Sminus,
        div_self (Sminus_pos hw hL m).ne', sub_self]
  · rcases h.lt_or_eq with h | h
    · exact testFn_out (Or.inr h)
    · rw [testFn_right (by omega) (by omega), ← h, ← Splus,
        div_self (Splus_pos hw hL m).ne', sub_self]

lemma testFn_eq_zero_of_le_abs (hw : ∀ k, 0 < w k) (hL : 1 ≤ L) {m n : ℤ}
    (h : (L : ℤ) ≤ |n - m|) : testFn w L m n = 0 :=
  testFn_eq_zero hw hL (by
    rcases le_abs'.1 h with h | h
    · left; omega
    · right; omega)

lemma testFn_mem_Icc (hw : ∀ k, 0 < w k) (hL : 1 ≤ L) (m n : ℤ) :
    0 ≤ testFn w L m n ∧ testFn w L m n ≤ 1 := by
  by_cases h1 : m ≤ n ∧ n ≤ m + L
  · rw [testFn_right h1.1 h1.2]
    have hS := Splus_pos hw hL m
    have h0 := sum_Ico_nonneg' hw m n
    have hle : ∑ k ∈ Ico m n, w k ≤ Splus w L m :=
      sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico le_rfl h1.2) (fun k _ _ => (hw k).le)
    constructor
    · rw [sub_nonneg, div_le_one hS]; exact hle
    · have : 0 ≤ (∑ k ∈ Ico m n, w k) / Splus w L m := div_nonneg h0 hS.le
      linarith
  by_cases h2 : m - L ≤ n ∧ n ≤ m
  · rw [testFn_left h2.1 h2.2]
    have hS := Sminus_pos hw hL m
    have h0 := sum_Ico_nonneg' hw n m
    have hle : ∑ k ∈ Ico n m, w k ≤ Sminus w L m :=
      sum_le_sum_of_subset_of_nonneg (Ico_subset_Ico h2.1 le_rfl) (fun k _ _ => (hw k).le)
    constructor
    · rw [sub_nonneg, div_le_one hS]; exact hle
    · have : 0 ≤ (∑ k ∈ Ico n m, w k) / Sminus w L m := div_nonneg h0 hS.le
      linarith
  rw [testFn_out (by omega)]
  norm_num

lemma testFn_nonneg (hw : ∀ k, 0 < w k) (hL : 1 ≤ L) (m n : ℤ) : 0 ≤ testFn w L m n :=
  (testFn_mem_Icc hw hL m n).1

lemma testFn_le_one (hw : ∀ k, 0 < w k) (hL : 1 ≤ L) (m n : ℤ) : testFn w L m n ≤ 1 :=
  (testFn_mem_Icc hw hL m n).2

lemma testFn_self (m : ℤ) : testFn w L m m = 1 := by simp [testFn]

/-- The pairing used in the lower bound of (5.6): `f_{m,L}(n) + f_{m+L,L}(n) = 1` for
`m < n < m + L` (in the notation of the paper, `u_j + (1 - u_j) = 1`). -/
lemma testFn_add_testFn_add (hw : ∀ k, 0 < w k) (hL : 1 ≤ L) {m n : ℤ} (h1 : m < n)
    (h2 : n < m + L) : testFn w L m n + testFn w L (m + L) n = 1 := by
  rw [testFn_right h1.le h2.le, testFn_left (by omega) h2.le, Sminus_eq_Splus,
    add_sub_cancel_right]
  have hS := Splus_pos hw hL m
  have hsplit : Splus w L m = ∑ k ∈ Ico m n, w k + ∑ k ∈ Ico n (m + L), w k :=
    sum_Ico_split h1.le h2.le w
  field_simp
  linarith

/-! ### The commutator matrix elements (5.5) -/

/-- (5.5), right window: `f(j) - f(j+1) = w_j / S_{+,m}` for `j = m, …, m+L-1`. -/
lemma testFn_sub_succ_right {m j : ℤ} (hm : m ≤ j) (hj : j < m + L) :
    testFn w L m j - testFn w L m (j + 1) = w j / Splus w L m := by
  rw [testFn_right hm hj.le, testFn_right (by omega) (by omega), sum_Ico_succ_right hm]
  ring

/-- (5.5), left window: `f(j) - f(j+1) = -w_j / S_{-,m}` for `j = m-L, …, m-1`. -/
lemma testFn_sub_succ_left {m j : ℤ} (hm : m - L ≤ j) (hj : j < m) :
    testFn w L m j - testFn w L m (j + 1) = -(w j / Sminus w L m) := by
  rw [testFn_left hm hj.le, testFn_left (by omega) (by omega)]
  have : ∑ k ∈ Ico j m, w k = w j + ∑ k ∈ Ico (j + 1) m, w k := by
    rw [sum_Ico_split (show j ≤ j + 1 by omega) (show j + 1 ≤ m by omega)]
    rw [Ico_add_one_right_eq_Icc, Icc_self, sum_singleton]
  rw [this]
  ring

/-- (5.5): all other commutator elements vanish. -/
lemma testFn_sub_succ_out (hw : ∀ k, 0 < w k) (hL : 1 ≤ L) {m j : ℤ}
    (h : j < m - L ∨ m + L ≤ j) : testFn w L m j - testFn w L m (j + 1) = 0 := by
  rw [testFn_eq_zero hw hL (by omega), testFn_eq_zero hw hL (by omega), sub_zero]

/-- **(5.5)** with `w_k = 1/|b_k|`: `(f(j) - f(j+1)) b_j = sgn b_j / S_{+,m}` on the right
window (`sgn b = b/|b|`). -/
lemma testFn_sub_succ_mul_right {b : ℤ → ℝ} (hb : ∀ k, b k ≠ 0) {m j : ℤ} (hm : m ≤ j)
    (hj : j < m + L) :
    (testFn (fun k => 1 / |b k|) L m j - testFn (fun k => 1 / |b k|) L m (j + 1)) * b j =
      (b j / |b j|) / Splus (fun k => 1 / |b k|) L m := by
  rw [testFn_sub_succ_right hm hj]
  have := abs_pos.2 (hb j)
  field_simp

/-- **(5.5)** with `w_k = 1/|b_k|`: `(f(j) - f(j+1)) b_j = -sgn b_j / S_{-,m}` on the left
window. -/
lemma testFn_sub_succ_mul_left {b : ℤ → ℝ} (hb : ∀ k, b k ≠ 0) {m j : ℤ} (hm : m - L ≤ j)
    (hj : j < m) :
    (testFn (fun k => 1 / |b k|) L m j - testFn (fun k => 1 / |b k|) L m (j + 1)) * b j =
      -((b j / |b j|) / Sminus (fun k => 1 / |b k|) L m) := by
  rw [testFn_sub_succ_left hm hj]
  have := abs_pos.2 (hb j)
  field_simp

/-- The commutator elements are bounded by `1/S_min` and vanish outside `[m-L, m+L)`. -/
lemma abs_testFn_sub_succ_mul_le {b : ℤ → ℝ} (hb : ∀ k, b k ≠ 0) (hL : 1 ≤ L) {S : ℝ}
    (hS : 0 < S) (hSle : ∀ m, S ≤ Splus (fun k => 1 / |b k|) L m) (m j : ℤ) :
    |(testFn (fun k => 1 / |b k|) L m j - testFn (fun k => 1 / |b k|) L m (j + 1)) * b j|
      ≤ 1 / S := by
  have hw : ∀ k, 0 < 1 / |b k| := fun k => by have := abs_pos.2 (hb k); positivity
  have hsgn : abs (b j / abs (b j)) = 1 := by
    rw [abs_div, abs_abs, div_self (abs_pos.2 (hb j)).ne']
  by_cases h1 : m ≤ j ∧ j < m + L
  · rw [testFn_sub_succ_mul_right hb h1.1 h1.2, abs_div, hsgn,
      abs_of_pos (Splus_pos hw hL m)]
    exact one_div_le_one_div_of_le hS (hSle m)
  by_cases h2 : m - L ≤ j ∧ j < m
  · rw [testFn_sub_succ_mul_left hb h2.1 h2.2, abs_neg, abs_div, hsgn,
      abs_of_pos (Sminus_pos hw hL m), Sminus_eq_Splus]
    exact one_div_le_one_div_of_le hS (hSle _)
  rw [testFn_sub_succ_out hw hL (by omega)]
  simp [hS.le]

lemma testFn_sub_succ_mul_eq_zero {b : ℤ → ℝ} (hb : ∀ k, b k ≠ 0) (hL : 1 ≤ L) {m j : ℤ}
    (h : j < m - L ∨ m + L ≤ j) :
    (testFn (fun k => 1 / |b k|) L m j - testFn (fun k => 1 / |b k|) L m (j + 1)) * b j = 0 := by
  have hw : ∀ k, 0 < 1 / |b k| := fun k => by have := abs_pos.2 (hb k); positivity
  rw [testFn_sub_succ_out hw hL h, zero_mul]

/-! ### Finite-sum bookkeeping -/

/-- If `g ≥ 0` vanishes off `T`, then `∑_{B} g ≤ ∑_{T} g`. -/
lemma sum_le_sum_of_support_subset {g : ℤ → ℝ} (hg : ∀ m, 0 ≤ g m) (B T : Finset ℤ)
    (hT : ∀ m, g m ≠ 0 → m ∈ T) : ∑ m ∈ B, g m ≤ ∑ m ∈ T, g m := by
  rw [← sum_filter_of_ne (p := fun m => m ∈ T) (fun m _ h => hT m h)]
  exact sum_le_sum_of_subset_of_nonneg (fun x hx => (mem_filter.1 hx).2)
    (fun m _ _ => hg m)

/-- Sum of the squared commutator elements over the centres `m`:
`∑_m ((f_m(j) - f_m(j+1)) b_j)² ≤ 2L / S_min²` (used in the second sum of (5.8)–(5.10)). -/
lemma sum_sq_testFn_sub_succ_mul_le {b : ℤ → ℝ} (hb : ∀ k, b k ≠ 0) (hL : 1 ≤ L) {S : ℝ}
    (hS : 0 < S) (hSle : ∀ m, S ≤ Splus (fun k => 1 / |b k|) L m) (B : Finset ℤ) (j : ℤ) :
    ∑ m ∈ B, ((testFn (fun k => 1 / |b k|) L m j -
        testFn (fun k => 1 / |b k|) L m (j + 1)) * b j) ^ 2 ≤ 2 * L / S ^ 2 := by
  set g : ℤ → ℝ := fun m => ((testFn (fun k => 1 / |b k|) L m j -
        testFn (fun k => 1 / |b k|) L m (j + 1)) * b j) ^ 2
  have hT : ∀ m, g m ≠ 0 → m ∈ Ioc (j - L) (j + L) := by
    intro m hm
    by_contra hc
    apply hm
    simp only [g]
    rw [testFn_sub_succ_mul_eq_zero hb hL (by simp at hc; omega)]
    ring
  refine (sum_le_sum_of_support_subset (fun m => sq_nonneg _) B _ hT).trans ?_
  have hle : ∀ m ∈ Ioc (j - L) (j + L), g m ≤ 1 / S ^ 2 := by
    intro m _
    have h := abs_testFn_sub_succ_mul_le hb hL hS hSle m j
    have h0 := abs_nonneg ((testFn (fun k => 1 / |b k|) L m j -
        testFn (fun k => 1 / |b k|) L m (j + 1)) * b j)
    simp only [g]
    rw [← sq_abs, one_div, ← inv_pow, ← one_div]
    exact pow_le_pow_left₀ h0 h 2
  refine (sum_le_sum hle).trans (le_of_eq ?_)
  rw [sum_const, Int.card_Ioc, nsmul_eq_mul]
  have : (j + L - (j - L)).toNat = 2 * L := by omega
  rw [this]
  push_cast
  ring

/-! ### The bound (5.6) -/

/-- **(5.6), upper bound.** `∑_m f_{m,L}(n)² ≤ 2L + 1` (the sum is over any finite set
of centres; only `|m - n| ≤ L` contribute). -/
theorem sum_sq_testFn_le (hw : ∀ k, 0 < w k) (hL : 1 ≤ L) (B : Finset ℤ) (n : ℤ) :
    ∑ m ∈ B, testFn w L m n ^ 2 ≤ 2 * L + 1 := by
  have hT : ∀ m, testFn w L m n ^ 2 ≠ 0 → m ∈ Icc (n - L) (n + L) := by
    intro m hm
    by_contra hc
    apply hm
    rw [testFn_eq_zero hw hL (by simp at hc; omega)]
    ring
  refine (sum_le_sum_of_support_subset (fun m => sq_nonneg _) B _ hT).trans ?_
  have hle : ∀ m ∈ Icc (n - L) (n + L), testFn w L m n ^ 2 ≤ 1 := fun m _ =>
    pow_le_one₀ (testFn_nonneg hw hL m n) (testFn_le_one hw hL m n)
  refine (sum_le_sum hle).trans (le_of_eq ?_)
  rw [sum_const, Int.card_Icc, nsmul_eq_mul, mul_one]
  have : (n + L + 1 - (n - L)).toNat = 2 * L + 1 := by omega
  rw [this]
  push_cast
  ring

/-- **(5.6), lower bound** over the full window `m ∈ [n-L, n+L]`. -/
theorem le_sum_sq_testFn_Icc (hw : ∀ k, 0 < w k) (hL : 1 ≤ L) (n : ℤ) :
    ((L : ℝ) + 1) / 2 ≤ ∑ m ∈ Icc (n - L) (n + L), testFn w L m n ^ 2 := by
  set f : ℤ → ℝ := fun m => testFn w L m n ^ 2 with hf
  have hf0 : ∀ m, 0 ≤ f m := fun m => sq_nonneg _
  have h1 : ∑ m ∈ Ico (n - L) (n + L), f m ≤ ∑ m ∈ Icc (n - L) (n + L), f m :=
    sum_le_sum_of_subset_of_nonneg Ico_subset_Icc_self (fun m _ _ => hf0 m)
  have h2 : ∑ m ∈ Ico (n - L) (n + L), f m =
      ∑ m ∈ Ico (n - L) n, (f m + f (m + L)) := by
    rw [sum_Ico_split (show n - L ≤ n by omega) (show n ≤ n + L by omega), sum_add_distrib]
    congr 1
    rw [sum_Ico_add' f (n - L) n (L : ℤ), sub_add_cancel]
  -- each pair contributes at least `1/2`, and the pair `m = n - L` contributes `1`
  have hpair : ∀ m ∈ Ico (n - L) n, (1 : ℝ) / 2 ≤ f m + f (m + L) := by
    intro m hm
    rw [mem_Ico] at hm
    rcases hm.1.lt_or_eq with hlt | heq
    · have h := testFn_add_testFn_add hw hL (show m < n by omega) (show n < m + L by omega)
      simp only [hf]
      nlinarith [sq_nonneg (testFn w L m n - testFn w L (m + L) n)]
    · have h0 : f m = 0 := by
        simp only [hf]; rw [testFn_eq_zero hw hL (by omega)]; ring
      have h1' : f (m + L) = 1 := by
        simp only [hf]; rw [← heq, sub_add_cancel, testFn_self]; ring
      rw [h0, h1']; norm_num
  have hfirst : (1 : ℝ) ≤ f (n - L) + f (n - L + L) := by
    have h0 : f (n - L) = 0 := by
      simp only [hf]; rw [testFn_eq_zero hw hL (by omega)]; ring
    have h1' : f (n - L + L) = 1 := by
      simp only [hf]; rw [sub_add_cancel, testFn_self]; ring
    rw [h0, h1']; norm_num
  have hmem : n - L ∈ Ico (n - L) n := by simp; omega
  have hsum : ∑ m ∈ Ico (n - L) n, (f m + f (m + L) - 1 / 2) ≥ 1 / 2 := by
    have := single_le_sum (f := fun m => f m + f (m + L) - 1 / 2)
      (fun m hm => by have := hpair m hm; linarith) hmem
    linarith
  have hcard : ∑ m ∈ Ico (n - L) n, (f m + f (m + L)) =
      ∑ m ∈ Ico (n - L) n, (f m + f (m + L) - 1 / 2) + L / 2 := by
    rw [sum_sub_distrib, sum_const, Int.card_Ico, nsmul_eq_mul]
    have : (n - (n - L)).toNat = L := by omega
    rw [this]
    ring
  linarith

/-- **(5.6), lower bound** for any finite set of centres containing `[n-L, n+L]`. -/
theorem le_sum_sq_testFn (hw : ∀ k, 0 < w k) (hL : 1 ≤ L) {B : Finset ℤ} {n : ℤ}
    (hB : Icc (n - L) (n + L) ⊆ B) :
    ((L : ℝ) + 1) / 2 ≤ ∑ m ∈ B, testFn w L m n ^ 2 :=
  (le_sum_sq_testFn_Icc hw hL n).trans
    (sum_le_sum_of_subset_of_nonneg hB (fun m _ _ => sq_nonneg _))

/-- **Lemma 5.3, (5.6).** For every `n`, `(L+1)/2 ≤ ∑_m f_{m,L}(n)² ≤ 2L+1`, where the sum is
over the (only contributing) centres `m ∈ [n-L, n+L]`. -/
theorem sumest (hw : ∀ k, 0 < w k) (hL : 1 ≤ L) (n : ℤ) :
    ((L : ℝ) + 1) / 2 ≤ ∑ m ∈ Icc (n - L) (n + L), testFn w L m n ^ 2 ∧
      ∑ m ∈ Icc (n - L) (n + L), testFn w L m n ^ 2 ≤ 2 * L + 1 :=
  ⟨le_sum_sq_testFn_Icc hw hL n, sum_sq_testFn_le hw hL _ n⟩

end Props

/-! ### The averaging step -/

/-- **Averaging (tex l. 946–951).** If `∑_m X_m ≤ c ∑_m Y_m` with `X, Y ≥ 0` and
`∑_m Y_m > 0`, then some `m` has `Y_m > 0` and `X_m ≤ c Y_m`.  (Applied with
`X_m = ‖(H-E) f_m φ‖²`, `Y_m = ‖f_m φ‖²`.) -/
theorem exists_le_mul_of_sum_le {ι : Type*} (B : Finset ι) (X Y : ι → ℝ) (c : ℝ)
    (hX : ∀ m, 0 ≤ X m) (h : ∑ m ∈ B, X m ≤ c * ∑ m ∈ B, Y m) (hpos : 0 < ∑ m ∈ B, Y m) :
    ∃ m ∈ B, 0 < Y m ∧ X m ≤ c * Y m := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨m₀, hm₀, hY₀⟩ : ∃ m ∈ B, 0 < Y m := by
    by_contra h'
    push_neg at h'
    have := sum_nonpos h'
    linarith
  have hle : ∀ m ∈ B, c * Y m ≤ X m := by
    intro m hm
    by_cases hY : 0 < Y m
    · exact (hcon m hm hY).le
    · -- `Y m ≤ 0`; if `Y m < 0` it is still fine when `c ≥ 0`, so argue directly
      by_cases hc : c * Y m ≤ 0
      · exact hc.trans (hX m)
      · push_neg at hc
        -- here `Y m ≤ 0` and `c * Y m > 0` force `c < 0`; then `c * ∑ Y < 0 ≤ ∑ X`
        exfalso
        have hYm : Y m < 0 := lt_of_le_of_ne (not_lt.1 hY) (by rintro h; simp [h] at hc)
        have hc0 : c < 0 := by nlinarith
        have : c * ∑ m ∈ B, Y m < 0 := mul_neg_of_neg_of_pos hc0 hpos
        have : 0 ≤ ∑ m ∈ B, X m := sum_nonneg fun m _ => hX m
        linarith
  have hlt : ∑ m ∈ B, c * Y m < ∑ m ∈ B, X m :=
    sum_lt_sum hle ⟨m₀, hm₀, hcon m₀ hm₀ hY₀⟩
  rw [← mul_sum] at hlt
  linarith

end CAH
