/-
Copyright (c) 2026. Formalization of
  S. Becker, S. Jitomirskaya, I. Krasovsky, "Critical almost Mathieu operator: hidden
  singularity, gap continuity, and the Hausdorff dimension of the spectrum"
  (arXiv:1909.04429v2).

# Continued fractions  (paper §2.3, eqs. (2.4)–(2.7); §6, Lemma 6.2 `lemma-rt`)

TeX references (`Arxiv_version-5.tex`):
* §2.3 "Continued fraction expansion", lines ~517–546: `(defpnqn)`, `(detid)` = (2.4),
  `(nnm1)` = (2.5), `(pdord)` = (2.6), `(q)` = (2.7);
* §6, lines ~1200–1235: `δ_n = q_n(α - p_n/q_n)`, the intervals `J_{n,1}`, `J_{n,2}`,
  `J̃_n`, and Lemma 6.2 (`lemma-rt`, first return times and `‖kα‖_𝕋 ≥ |δ_{n-1}|`);
* lines ~1612–1636: the bound `∑_{k=1}^{L} 1/sin²(πkα) ≤ C q_n²`.

## Indexing

We use `CAH.q α n = (GenContFract.of α).dens n` and `CAH.p α n = (GenContFract.of α).nums n`.
For `α ∈ (0,1)` Mathlib's head term is `h = ⌊α⌋ = 0`, the `i`-th partial denominator
`(GenContFract.of α).partDens.get? i` is the paper's `a_{i+1}`, and `p_n, q_n` *coincide with
the paper's* `p_n, q_n` for every `n ≥ 0` (`p_0 = 0`, `q_0 = 1`, `q_1 = a_1`, ...).
All results below are stated for an arbitrary irrational `α` (not necessarily in `(0,1)`);
for `α ∉ (0,1)` the numerators are shifted by `q_n ⌊α⌋`, which changes none of the
statements about `δ_n = q_n α - p_n`.

## Main results
* `q_mul_p_sub` — (2.4): `q_n p_{n-1} - p_n q_{n-1} = (-1)^n`;
* `conv_sub_conv` — (2.5);
* `delta_eq` — the exact error formula `δ_n = (-1)^n / D` with `q_{n+1} < D < q_{n+1} + q_n`;
* `abs_sub_lt`, `lt_abs_sub` — (2.7);
* `conv_even_lt`, `lt_conv_odd` — (2.6), plus monotonicity of even/odd convergents;
* `delta_pos_of_even`, `delta_neg_of_odd`, `abs_delta_succ_lt`, `inv_lt_abs_delta`;
* `abs_delta_le_abs_mul_sub` / `best_approx` — the best-approximation property
  `|kα - m| ≥ |δ_{n-1}|` for `0 < k < q_n`, all `m ∈ ℤ` (Lemma 6.2, last assertion);
* `lemma_rt_one`, `lemma_rt_two` — Lemma 6.2 (first return times `q_n` on `J_{n,1}` and
  `q_{n-1}` on `J_{n,2}`);  `first_return`, `return_gap` — the return gaps lie in
  `{q_n, q_{n-1}}`;
* `sum_inv_sin_sq_le` — `∑_{k=1}^{L} 1/sin²(πkα) ≤ 4 q_n²` for `L ≤ q_n - 1`.

There are no `sorry`s in this file.
-/
import SpectralGapsDimension.Arithmetic
import CriticalAMOHausdorff.Basic

noncomputable section

open Real Set Finset

namespace CAH

open GenContFract

/-! ### Integrality of the convergents -/

lemma exists_int_contsAux (v : ℝ) : ∀ n : ℕ, ∃ a b : ℤ, (GenContFract.of v).contsAux n = ⟨a, b⟩
  | 0 => ⟨1, 0, by simp [zeroth_contAux_eq_one_zero]⟩
  | 1 => ⟨⌊v⌋, 1, by simp [first_contAux_eq_h_one, of_h_eq_floor]⟩
  | n + 2 => by
    obtain ⟨a0, b0, h0⟩ := exists_int_contsAux v n
    obtain ⟨a1, b1, h1⟩ := exists_int_contsAux v (n + 1)
    rcases hs : (GenContFract.of v).s.get? n with _ | gp
    · rw [contsAux_stable_step_of_terminated hs]; exact ⟨a1, b1, h1⟩
    · obtain ⟨ha, z, hz⟩ := of_partNum_eq_one_and_exists_int_partDen_eq hs
      refine ⟨z * a1 + a0, z * b1 + b0, ?_⟩
      rw [contsAux_recurrence hs h0 h1, ha, hz]
      push_cast; ring_nf

lemma exists_int_q (α : ℝ) (n : ℕ) : ∃ z : ℤ, q α n = z := by
  obtain ⟨a, b, h⟩ := exists_int_contsAux α (n + 1)
  refine ⟨b, ?_⟩
  simp [q, AMO.cfDen, den_eq_conts_b, nth_cont_eq_succ_nth_contAux, h]

lemma exists_int_p (α : ℝ) (n : ℕ) : ∃ z : ℤ, p α n = z := by
  obtain ⟨a, b, h⟩ := exists_int_contsAux α (n + 1)
  refine ⟨a, ?_⟩
  simp [p, num_eq_conts_a, nth_cont_eq_succ_nth_contAux, h]

lemma q_one_le {α : ℝ} (hα : Irrational α) (n : ℕ) : 1 ≤ q α n :=
  (SGD.cfGrowth hα).one_le n

lemma q_pos {α : ℝ} (hα : Irrational α) (n : ℕ) : 0 < q α n :=
  zero_lt_one.trans_le (q_one_le hα n)

/-- `q_n` as a natural number. -/
def qN (α : ℝ) (n : ℕ) : ℕ := ⌊q α n⌋₊

/-- `p_n` as an integer. -/
def pZ (α : ℝ) (n : ℕ) : ℤ := ⌊p α n⌋

lemma qN_cast {α : ℝ} (hα : Irrational α) (n : ℕ) : (qN α n : ℝ) = q α n := by
  obtain ⟨z, hz⟩ := exists_int_q α n
  have h0 : (0 : ℝ) ≤ z := hz ▸ (q_pos hα n).le
  have : (0 : ℤ) ≤ z := by exact_mod_cast h0
  lift z to ℕ using this
  simp [qN, hz]

lemma pZ_cast (α : ℝ) (n : ℕ) : (pZ α n : ℝ) = p α n := by
  obtain ⟨z, hz⟩ := exists_int_p α n
  simp [pZ, hz]

lemma one_le_qN {α : ℝ} (hα : Irrational α) (n : ℕ) : 1 ≤ qN α n := by
  have := q_one_le hα n
  rw [← qN_cast hα] at this
  exact_mod_cast this

/-! ### Recurrence and the determinant identity -/

/-- The recurrence `q_{n+2} = a_{n+2} q_{n+1} + q_n` with an integer `a_{n+2} ≥ 1`. -/
lemma q_recurrence {α : ℝ} (hα : Irrational α) (n : ℕ) :
    ∃ a : ℤ, 1 ≤ a ∧ q α (n + 2) = a * q α (n + 1) + q α n ∧
      p α (n + 2) = a * p α (n + 1) + p α n := by
  obtain ⟨gp, hgp⟩ : ∃ gp, (GenContFract.of α).s.get? (n + 1) = some gp :=
    Option.ne_none_iff_exists'.1 (SGD.not_terminatedAt hα (n + 1))
  obtain ⟨ha, z, hz⟩ := of_partNum_eq_one_and_exists_int_partDen_eq hgp
  have hb : 1 ≤ gp.b := of_one_le_get?_partDen (partDen_eq_s_b hgp)
  refine ⟨z, by rw [hz] at hb; exact_mod_cast hb, ?_, ?_⟩
  · simp only [q, AMO.cfDen]; rw [dens_recurrence hgp rfl rfl, ha, hz]; ring
  · simp only [p]; rw [nums_recurrence hgp rfl rfl, ha, hz]; ring

lemma q_add_le {α : ℝ} (hα : Irrational α) (n : ℕ) : q α n + q α (n + 1) ≤ q α (n + 2) := by
  obtain ⟨a, ha, hq, -⟩ := q_recurrence hα n
  have : (1 : ℝ) ≤ a := by exact_mod_cast ha
  rw [hq]; nlinarith [q_pos hα (n + 1)]

lemma q_le_succ {α : ℝ} (_hα : Irrational α) (n : ℕ) : q α n ≤ q α (n + 1) := by
  show (GenContFract.of α).dens n ≤ (GenContFract.of α).dens (n + 1)
  exact of_den_mono

lemma q_lt_succ {α : ℝ} (hα : Irrational α) (n : ℕ) (hn : 1 ≤ n) : q α n < q α (n + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have := q_add_le hα m
  linarith [q_pos hα m]

/-- `q_n ≥ 2^{(n-1)/2}` (§2.3). -/
lemma two_rpow_le_q {α : ℝ} (hα : Irrational α) (n : ℕ) :
    (2 : ℝ) ^ (((n : ℝ) - 1) / 2) ≤ q α n :=
  (SGD.cfGrowth hα).rpow_le n

/-- **(2.4)** `q_n p_{n-1} - p_n q_{n-1} = (-1)^n`, `n ≥ 1` (written with `n+1`). -/
theorem q_mul_p_sub {α : ℝ} (hα : Irrational α) (n : ℕ) :
    q α (n + 1) * p α n - p α (n + 1) * q α n = (-1) ^ (n + 1) := by
  have := (SimpContFract.of α).determinant (n := n) (SGD.not_terminatedAt hα n)
  simp only [q, AMO.cfDen, p]
  change (GenContFract.of α).nums n * (GenContFract.of α).dens (n + 1) - (GenContFract.of α).dens n * (GenContFract.of α).nums (n + 1) =
    (-1) ^ (n + 1) at this
  linarith

/-- **(2.5)** `p_{n-1}/q_{n-1} - p_n/q_n = (-1)^n/(q_n q_{n-1})`, `n ≥ 1`. -/
theorem conv_sub_conv {α : ℝ} (hα : Irrational α) (n : ℕ) :
    p α n / q α n - p α (n + 1) / q α (n + 1) = (-1) ^ (n + 1) / (q α (n + 1) * q α n) := by
  have h0 := q_pos hα n
  have h1 := q_pos hα (n + 1)
  rw [← q_mul_p_sub hα n]
  field_simp

/-- The convergents `p_n, q_n` are coprime (consequence of (2.4)). -/
lemma isCoprime_pZ_qN {α : ℝ} (hα : Irrational α) (n : ℕ) :
    IsCoprime (pZ α n) (qN α n : ℤ) := by
  rcases n with _ | n
  · have : qN α 0 = 1 := by
      have := qN_cast hα 0
      simp only [q, AMO.cfDen, zeroth_den_eq_one] at this
      exact_mod_cast this
    rw [this, Nat.cast_one]; exact isCoprime_one_right
  · have h := q_mul_p_sub hα n
    rw [← qN_cast hα, ← qN_cast hα, ← pZ_cast, ← pZ_cast] at h
    have h' : (qN α (n + 1) : ℤ) * pZ α n - pZ α (n + 1) * qN α n = (-1) ^ (n + 1) := by
      exact_mod_cast h
    refine ⟨-((-1) ^ (n + 1) * qN α n), (-1) ^ (n + 1) * pZ α n, ?_⟩
    have hsq : ((-1 : ℤ) ^ (n + 1)) * (-1) ^ (n + 1) = 1 := by
      rw [← mul_pow]; simp
    linear_combination (-1 : ℤ) ^ (n + 1) * h' + hsq

/-! ### The error terms `δ_n` -/

/-- `δ_n = q_n α - p_n = q_n (α - p_n/q_n)` (§6, line ~1203). -/
def delta (α : ℝ) (n : ℕ) : ℝ := q α n * α - p α n

lemma delta_eq_mul {α : ℝ} (hα : Irrational α) (n : ℕ) :
    delta α n = q α n * (α - p α n / q α n) := by
  have := q_pos hα n
  unfold delta; field_simp

/-- **Exact error formula.**  `δ_n = (-1)^n / D_n` with `q_{n+1} < D_n < q_{n+1} + q_n`
(here `D_n = x_{n+1} q_n + q_{n-1}`, `x_{n+1}` the `(n+1)`-st complete quotient). -/
theorem delta_eq {α : ℝ} (hα : Irrational α) (n : ℕ) :
    ∃ D : ℝ, q α (n + 1) < D ∧ D < q α (n + 1) + q α n ∧ delta α n = (-1) ^ n / D := by
  have hne : IntFractPair.stream α (n + 1) ≠ none :=
    (not_congr of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none).1
      (SGD.not_terminatedAt hα n)
  obtain ⟨ifs, hifs⟩ := Option.ne_none_iff_exists'.1 hne
  obtain ⟨ifp, hifp, hfr, hof⟩ := IntFractPair.succ_nth_stream_eq_some_iff.1 hifs
  have hne2 : IntFractPair.stream α (n + 1 + 1) ≠ none :=
    (not_congr of_terminatedAt_n_iff_succ_nth_intFractPair_stream_eq_none).1
      (SGD.not_terminatedAt hα (n + 1))
  obtain ⟨ifs2, hifs2⟩ := Option.ne_none_iff_exists'.1 hne2
  obtain ⟨ifp', hifp', hfr', -⟩ := IntFractPair.succ_nth_stream_eq_some_iff.1 hifs2
  rw [hifs] at hifp'
  cases hifp'
  subst hof
  set x := ifp.fr⁻¹ with hx
  have hfx : Int.fract x ≠ 0 := hfr'
  have hb : ((⌊x⌋ : ℤ) : ℝ) < x := by
    refine lt_of_le_of_ne (Int.floor_le x) (fun h => hfx ?_)
    rw [Int.fract, h, sub_self]
  have hb' : x < ⌊x⌋ + 1 := Int.lt_floor_add_one x
  have hs : (GenContFract.of α).s.get? n = some ⟨1, ((IntFractPair.of x).b : ℝ)⟩ :=
    get?_of_eq_some_of_succ_get?_intFractPair_stream hifs
  have hqn : q α n = ((GenContFract.of α).contsAux (n + 1)).b := by
    simp [q, AMO.cfDen, den_eq_conts_b, nth_cont_eq_succ_nth_contAux]
  have hqn1 : q α (n + 1) = ⌊x⌋ * ((GenContFract.of α).contsAux (n + 1)).b + ((GenContFract.of α).contsAux n).b := by
    simp [q, AMO.cfDen, den_eq_conts_b, nth_cont_eq_succ_nth_contAux,
      contsAux_recurrence hs rfl rfl, IntFractPair.of]
  have hpB : 0 ≤ ((GenContFract.of α).contsAux n).b := zero_le_of_contsAux_b
  have herr := sub_convs_eq hifp
  simp only [hfr, ↓reduceIte] at herr
  rw [conv_eq_num_div_den] at herr
  have hB := q_pos hα n
  rw [hqn] at hB
  refine ⟨x * ((GenContFract.of α).contsAux (n + 1)).b + ((GenContFract.of α).contsAux n).b, ?_, ?_, ?_⟩
  · rw [hqn1]; nlinarith
  · rw [hqn1, hqn]; nlinarith
  · rw [delta_eq_mul hα, hqn]
    change ((GenContFract.of α).contsAux (n + 1)).b *
      (α - (GenContFract.of α).nums n / (GenContFract.of α).dens n) = _
    rw [herr, ← hx]
    have hfr0 : 0 < ifp.fr := lt_of_le_of_ne (IntFractPair.nth_stream_fr_nonneg hifp) (Ne.symm hfr)
    have hx0 : 0 < x := inv_pos.2 hfr0
    have : 0 < x * ((GenContFract.of α).contsAux (n + 1)).b + ((GenContFract.of α).contsAux n).b := by positivity
    field_simp

/-- Sign of `δ_n`: `(-1)^n δ_n > 0`. -/
lemma neg_one_pow_mul_delta_pos {α : ℝ} (hα : Irrational α) (n : ℕ) :
    0 < (-1) ^ n * delta α n := by
  obtain ⟨D, h1, -, h⟩ := delta_eq hα n
  have hD : 0 < D := (q_pos hα _).trans h1
  have h1 : (-1 : ℝ) ^ n * (-1) ^ n = 1 := by rw [← mul_pow]; norm_num
  rw [h, mul_div_assoc', h1]; exact one_div_pos.2 hD

lemma delta_pos_of_even {α : ℝ} (hα : Irrational α) {n : ℕ} (hn : Even n) : 0 < delta α n := by
  simpa [hn.neg_one_pow] using neg_one_pow_mul_delta_pos hα n

lemma delta_neg_of_odd {α : ℝ} (hα : Irrational α) {n : ℕ} (hn : Odd n) : delta α n < 0 := by
  simpa [hn.neg_one_pow] using neg_one_pow_mul_delta_pos hα n

/-- `δ_n δ_{n+1} < 0`. -/
lemma delta_mul_delta_succ_neg {α : ℝ} (hα : Irrational α) (n : ℕ) :
    delta α n * delta α (n + 1) < 0 := by
  rcases Nat.even_or_odd n with h | h
  · exact mul_neg_of_pos_of_neg (delta_pos_of_even hα h) (delta_neg_of_odd hα h.add_one)
  · exact mul_neg_of_neg_of_pos (delta_neg_of_odd hα h) (delta_pos_of_even hα h.add_one)

/-- `1/(q_{n+1} + q_n) < |δ_n| < 1/q_{n+1}`. -/
lemma abs_delta_bounds {α : ℝ} (hα : Irrational α) (n : ℕ) :
    1 / (q α (n + 1) + q α n) < |delta α n| ∧ |delta α n| < 1 / q α (n + 1) := by
  obtain ⟨D, h1, h2, h⟩ := delta_eq hα n
  have hq := q_pos hα (n + 1)
  have hD : 0 < D := hq.trans h1
  rw [h, abs_div, abs_pow, abs_neg, abs_one, one_pow, abs_of_pos hD]
  exact ⟨one_div_lt_one_div_of_lt hD h2, one_div_lt_one_div_of_lt hq h1⟩

/-- `|δ_{n-1}| > 1/(q_n + q_{n-1})` (§6, used in Lemma 6.2 and line ~1625). -/
lemma inv_lt_abs_delta {α : ℝ} (hα : Irrational α) (n : ℕ) :
    1 / (q α (n + 1) + q α n) < |delta α n| := (abs_delta_bounds hα n).1

/-- `|δ_{n+1}| < |δ_n|`. -/
lemma abs_delta_succ_lt {α : ℝ} (hα : Irrational α) (n : ℕ) :
    |delta α (n + 1)| < |delta α n| := by
  have h1 := (abs_delta_bounds hα (n + 1)).2
  have h2 := (abs_delta_bounds hα n).1
  have h3 : q α n + q α (n + 1) ≤ q α (n + 1 + 1) := q_add_le hα n
  have h4 := q_pos hα n
  have : 1 / q α (n + 1 + 1) ≤ 1 / (q α (n + 1) + q α n) :=
    one_div_le_one_div_of_le (by linarith [q_pos hα (n+1)]) (by linarith)
  linarith

/-- **(2.7)**, upper bound: `|α - p_n/q_n| < 1/(q_n q_{n+1})`. -/
theorem abs_sub_lt {α : ℝ} (hα : Irrational α) (n : ℕ) :
    |α - p α n / q α n| < 1 / (q α n * q α (n + 1)) := by
  have h := (abs_delta_bounds hα n).2
  have hq := q_pos hα n
  rw [delta_eq_mul hα, abs_mul, abs_of_pos hq] at h
  rw [show (1 : ℝ) / (q α n * q α (n + 1)) = 1 / q α (n + 1) / q α n by ring,
    lt_div_iff₀ hq]
  linarith [mul_comm (q α n) |α - p α n / q α n|]

/-- **(2.7)**, lower bound: `1/(q_n(q_n + q_{n+1})) < |α - p_n/q_n|`. -/
theorem lt_abs_sub {α : ℝ} (hα : Irrational α) (n : ℕ) :
    1 / (q α n * (q α n + q α (n + 1))) < |α - p α n / q α n| := by
  have h := (abs_delta_bounds hα n).1
  have hq := q_pos hα n
  rw [delta_eq_mul hα, abs_mul, abs_of_pos hq] at h
  rw [show (1 : ℝ) / (q α n * (q α n + q α (n + 1))) = 1 / (q α (n + 1) + q α n) / q α n by
    rw [div_div, add_comm (q α (n + 1)), mul_comm], div_lt_iff₀ hq]
  linarith [mul_comm (q α n) |α - p α n / q α n|]

/-- `|α - p_n/q_n| < 1/q_n²` (last inequality in (2.7)). -/
theorem abs_sub_lt_sq {α : ℝ} (hα : Irrational α) (n : ℕ) (hn : 1 ≤ n) :
    |α - p α n / q α n| < 1 / q α n ^ 2 := by
  refine (abs_sub_lt hα n).trans_le ?_
  have := q_lt_succ hα n hn
  have := q_pos hα n
  rw [sq]; exact one_div_le_one_div_of_le (by positivity) (by nlinarith)

lemma sub_conv_eq {α : ℝ} (hα : Irrational α) (n : ℕ) :
    α - p α n / q α n = delta α n / q α n := by
  rw [delta_eq_mul hα]; field_simp [(q_pos hα n).ne']

/-- **(2.6)** `p_{2k}/q_{2k} < α`. -/
theorem conv_even_lt {α : ℝ} (hα : Irrational α) (k : ℕ) : p α (2 * k) / q α (2 * k) < α := by
  have := delta_pos_of_even hα (even_two_mul k)
  have h := sub_conv_eq hα (2 * k)
  have : 0 < delta α (2 * k) / q α (2 * k) := div_pos this (q_pos hα _)
  linarith

/-- **(2.6)** `α < p_{2k-1}/q_{2k-1}` (written with `2k+1`). -/
theorem lt_conv_odd {α : ℝ} (hα : Irrational α) (k : ℕ) :
    α < p α (2 * k + 1) / q α (2 * k + 1) := by
  have := delta_neg_of_odd hα (odd_two_mul_add_one k)
  have h := sub_conv_eq hα (2 * k + 1)
  have : delta α (2 * k + 1) / q α (2 * k + 1) < 0 := div_neg_of_neg_of_pos this (q_pos hα _)
  linarith

lemma abs_sub_conv_succ_succ_lt {α : ℝ} (hα : Irrational α) (n : ℕ) :
    |α - p α (n + 2) / q α (n + 2)| < |α - p α n / q α n| := by
  rw [sub_conv_eq hα, sub_conv_eq hα, abs_div, abs_div, abs_of_pos (q_pos hα _),
    abs_of_pos (q_pos hα _)]
  have h1 : |delta α (n + 2)| < |delta α (n + 1)| := abs_delta_succ_lt hα (n + 1)
  have h2 := abs_delta_succ_lt hα n
  have h3 : q α n ≤ q α (n + 2) := by linarith [q_add_le hα n, q_pos hα (n+1)]
  have h4 := q_pos hα n
  rw [div_lt_div_iff₀ (q_pos hα _) h4]
  calc |delta α (n + 2)| * q α n < |delta α n| * q α n := by gcongr; linarith
    _ ≤ |delta α n| * q α (n + 2) := by gcongr

/-- The even convergents increase strictly (§2.3). -/
theorem conv_even_strictMono {α : ℝ} (hα : Irrational α) (k : ℕ) :
    p α (2 * k) / q α (2 * k) < p α (2 * (k + 1)) / q α (2 * (k + 1)) := by
  have h := abs_sub_conv_succ_succ_lt hα (2 * k)
  have h1 := conv_even_lt hα k
  have h2 := conv_even_lt hα (k + 1)
  rw [show 2 * (k + 1) = 2 * k + 2 by ring] at h2 ⊢
  rw [abs_of_pos (by linarith), abs_of_pos (by linarith)] at h
  linarith

/-- The odd convergents decrease strictly (§2.3). -/
theorem conv_odd_strictAnti {α : ℝ} (hα : Irrational α) (k : ℕ) :
    p α (2 * (k + 1) + 1) / q α (2 * (k + 1) + 1) < p α (2 * k + 1) / q α (2 * k + 1) := by
  have h := abs_sub_conv_succ_succ_lt hα (2 * k + 1)
  have h1 := lt_conv_odd hα k
  have h2 := lt_conv_odd hα (k + 1)
  rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 2 by ring] at h2 ⊢
  rw [abs_of_neg (by linarith), abs_of_neg (by linarith)] at h
  linarith

/-! ### Best approximation  (Lemma 6.2, last assertion) -/

lemma det_int {α : ℝ} (hα : Irrational α) (n : ℕ) :
    (qN α (n + 1) : ℤ) * pZ α n - pZ α (n + 1) * qN α n = (-1) ^ (n + 1) := by
  have h := q_mul_p_sub hα n
  rw [← qN_cast hα, ← qN_cast hα, ← pZ_cast, ← pZ_cast] at h
  exact_mod_cast h

lemma delta_eq_cast {α : ℝ} (hα : Irrational α) (n : ℕ) :
    delta α n = (qN α n : ℝ) * α - (pZ α n : ℝ) := by
  rw [qN_cast hα, pZ_cast]; rfl

/-- Every `(k, m) ∈ ℤ²` is an integer combination of `(q_n, p_n)` and `(q_{n+1}, p_{n+1})`;
consequently `kα - m = u δ_n + v δ_{n+1}`. -/
lemma decomp {α : ℝ} (hα : Irrational α) (n : ℕ) (k m : ℤ) :
    ∃ u v : ℤ, k = u * qN α n + v * qN α (n + 1) ∧
      (k : ℝ) * α - m = u * delta α n + v * delta α (n + 1) := by
  have key : ∀ Q0 Q1 P0 P1 : ℤ, Q1 * P0 - P1 * Q0 = (-1) ^ (n + 1) →
      ∃ u v : ℤ, k = u * Q0 + v * Q1 ∧ m = u * P0 + v * P1 := by
    intro Q0 Q1 P0 P1 h'
    have hsq : ((-1 : ℤ) ^ (n + 1)) * (-1) ^ (n + 1) = 1 := by rw [← mul_pow]; norm_num
    exact ⟨-((-1) ^ (n + 1) * (k * P1 - Q1 * m)), -((-1) ^ (n + 1) * (Q0 * m - P0 * k)),
      by linear_combination (-((-1) ^ (n + 1) * k)) * h' - k * hsq,
      by linear_combination (-((-1) ^ (n + 1) * m)) * h' - m * hsq⟩
  obtain ⟨u, v, hk, hm⟩ := key _ _ _ _ (det_int hα n)
  refine ⟨u, v, hk, ?_⟩
  have hk' : (k : ℝ) = u * (qN α n : ℝ) + v * (qN α (n + 1) : ℝ) := by
    rw [hk]; push_cast; ring
  have hm' : (m : ℝ) = u * (pZ α n : ℝ) + v * (pZ α (n + 1) : ℝ) := by
    rw [hm]; push_cast; ring
  rw [delta_eq_cast hα, delta_eq_cast hα, hk', hm']
  ring

/-- Sign pattern of the coefficients for `0 < k < q_{n+1}`. -/
lemma uv_cases {Q0 Q1 k u v : ℤ} (hQ0 : 1 ≤ Q0) (hQ : Q0 ≤ Q1) (hk : 0 < k) (hk' : k < Q1)
    (h : k = u * Q0 + v * Q1) : (1 ≤ u ∧ v ≤ 0) ∨ (u ≤ -1 ∧ 1 ≤ v) := by
  rcases le_or_gt 1 u with hu | hu
  · rcases le_or_gt v 0 with hv | hv
    · exact Or.inl ⟨hu, hv⟩
    · exfalso; nlinarith
  · rcases le_or_gt 1 v with hv | hv
    · rcases le_or_gt u (-1) with hu' | hu'
      · exact Or.inr ⟨hu', hv⟩
      · exfalso
        have : u = 0 := by omega
        subst this; nlinarith
    · exfalso; nlinarith

/-- Refined sign pattern for `0 < k < q_n`. -/
lemma uv_cases' {Q0 Q1 k u v : ℤ} (hQ0 : 1 ≤ Q0) (hQ : Q0 ≤ Q1) (hk : 0 < k) (hk' : k < Q0)
    (h : k = u * Q0 + v * Q1) : (1 ≤ u ∧ v ≤ -1) ∨ (u ≤ -1 ∧ 1 ≤ v) := by
  rcases uv_cases hQ0 hQ hk (hk'.trans_le hQ) h with ⟨hu, hv⟩ | h2
  · left; refine ⟨hu, ?_⟩
    by_contra hv'
    have : v = 0 := by omega
    subst this
    nlinarith
  · exact Or.inr h2

lemma qN_le_succ {α : ℝ} (hα : Irrational α) (n : ℕ) : qN α n ≤ qN α (n + 1) := by
  have := q_le_succ hα n
  rw [← qN_cast hα, ← qN_cast hα] at this
  exact_mod_cast this

/-- **Best approximation** (Lemma 6.2, last assertion, in the strong form valid for every
integer `m`): for `0 < k < q_{n+1}`, `|kα - m| ≥ |δ_n|`. -/
theorem abs_delta_le_abs_mul_sub {α : ℝ} (hα : Irrational α) (n : ℕ) (k m : ℤ) (hk : 0 < k)
    (hk' : k < qN α (n + 1)) : |delta α n| ≤ |(k : ℝ) * α - m| := by
  obtain ⟨u, v, hkuv, hrel⟩ := decomp hα n k m
  have hQ0 : (1 : ℤ) ≤ qN α n := by exact_mod_cast one_le_qN hα n
  have hQ : (qN α n : ℤ) ≤ qN α (n + 1) := by exact_mod_cast qN_le_succ hα n
  have hde := delta_mul_delta_succ_neg hα n
  rw [hrel]
  rcases uv_cases hQ0 hQ hk hk' hkuv with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · have hu' : (1 : ℝ) ≤ u := by exact_mod_cast hu
    have hv' : (v : ℝ) ≤ 0 := by exact_mod_cast hv
    rcases lt_or_gt_of_ne (show delta α n ≠ 0 by rintro h; simp [h] at hde) with hd | hd
    · have he : 0 < delta α (n + 1) := by nlinarith
      rw [abs_of_neg hd, abs_of_neg (by nlinarith)]; nlinarith
    · have he : delta α (n + 1) < 0 := by nlinarith
      rw [abs_of_pos hd, abs_of_pos (by nlinarith)]; nlinarith
  · have hu' : (u : ℝ) ≤ -1 := by exact_mod_cast hu
    have hv' : (1 : ℝ) ≤ v := by exact_mod_cast hv
    rcases lt_or_gt_of_ne (show delta α n ≠ 0 by rintro h; simp [h] at hde) with hd | hd
    · have he : 0 < delta α (n + 1) := by nlinarith
      rw [abs_of_neg hd, abs_of_pos (by nlinarith)]; nlinarith
    · have he : delta α (n + 1) < 0 := by nlinarith
      rw [abs_of_pos hd, abs_of_neg (by nlinarith)]; nlinarith

/-- **Lemma 6.2, last assertion** (paper indexing, `n ≥ 1`): `‖kα‖_𝕋 ≥ |δ_{n-1}|` for
`1 ≤ k ≤ q_n - 1`. -/
theorem best_approx {α : ℝ} (hα : Irrational α) {n : ℕ} (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k)
    (hk' : k < qN α n) : |delta α (n - 1)| ≤ ‖((k * α : ℝ) : UnitAddCircle)‖ := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  rw [UnitAddCircle.norm_eq, Nat.add_sub_cancel]
  have := abs_delta_le_abs_mul_sub hα N k (round ((k : ℝ) * α)) (by exact_mod_cast hk)
    (by exact_mod_cast hk')
  simpa using this

/-- `‖q_n α‖_𝕋 = |δ_n|` for `n ≥ 1`. -/
theorem norm_q_mul_eq {α : ℝ} (hα : Irrational α) {n : ℕ} (hn : 1 ≤ n) :
    ‖((qN α n * α : ℝ) : UnitAddCircle)‖ = |delta α n| := by
  rw [UnitAddCircle.norm_eq]
  apply le_antisymm
  · have := round_le ((qN α n : ℝ) * α) (pZ α n)
    rwa [← delta_eq_cast hα] at this
  · have hlt : qN α n < qN α (n + 1) := by
      have := q_lt_succ hα n hn
      rw [← qN_cast hα, ← qN_cast hα] at this
      exact_mod_cast this
    have := abs_delta_le_abs_mul_sub hα n (qN α n) (round ((qN α n : ℝ) * α))
      (by exact_mod_cast one_le_qN hα n) (by exact_mod_cast hlt)
    simpa using this

/-! ### Lemma 6.2: first return times -/

/-- `J_{n,1}` (§6, line ~1205): `(0, δ_{n-1}]` for `n` odd, `[δ_{n-1}, 0)` for `n` even. -/
def J1 (α : ℝ) (n : ℕ) : Set ℝ :=
  if Even n then Ico (delta α (n - 1)) 0 else Ioc 0 (delta α (n - 1))

/-- `J_{n,2}`: `(δ_n, 0]` for `n` odd, `[0, δ_n)` for `n` even. -/
def J2 (α : ℝ) (n : ℕ) : Set ℝ :=
  if Even n then Ico 0 (delta α n) else Ioc (delta α n) 0

/-- `J̃_n = J_{n,1} ∪ J_{n,2}`. -/
def Jt (α : ℝ) (n : ℕ) : Set ℝ := J1 α n ∪ J2 α n

lemma Jt_eq_even {α : ℝ} (hα : Irrational α) {n : ℕ} (hn : 1 ≤ n) (he : Even n) :
    Jt α n = Ico (delta α (n - 1)) (delta α n) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hd := delta_neg_of_odd hα (Nat.even_add_one.1 he |> Nat.not_even_iff_odd.1)
  have he' := delta_pos_of_even hα he
  simp only [Jt, J1, J2, he, ↓reduceIte, Nat.add_sub_cancel]
  exact Ico_union_Ico_eq_Ico hd.le he'.le

lemma Jt_eq_odd {α : ℝ} (hα : Irrational α) {n : ℕ} (hn : 1 ≤ n) (ho : ¬Even n) :
    Jt α n = Ioc (delta α n) (delta α (n - 1)) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hd := delta_pos_of_even hα (by simpa [Nat.even_add_one] using ho)
  have he' := delta_neg_of_odd hα (Nat.not_even_iff_odd.1 ho)
  simp only [Jt, J1, J2, ho, ↓reduceIte, Nat.add_sub_cancel]
  rw [union_comm]
  exact Ioc_union_Ioc_eq_Ioc he'.le hd.le

/-- `|J̃_n| < 2/q_n`: `J̃_n ⊆ (-1/q_n, 1/q_n)`. -/
lemma Jt_subset {α : ℝ} (hα : Irrational α) {n : ℕ} (hn : 1 ≤ n) :
    Jt α n ⊆ Ioo (-(1 / q α n)) (1 / q α n) := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have h1 := (abs_delta_bounds hα N).2
  have h2 := (abs_delta_bounds hα (N + 1)).2
  have h3 : 1 / q α (N + 1 + 1) ≤ 1 / q α (N + 1) :=
    one_div_le_one_div_of_le (q_pos hα _) (q_le_succ hα _)
  rw [abs_lt] at h1 h2
  by_cases he : Even (N + 1)
  · rw [Jt_eq_even hα hn he, Nat.add_sub_cancel]
    intro y hy; constructor <;> linarith [hy.1, hy.2, h1.1, h2.2]
  · rw [Jt_eq_odd hα hn he, Nat.add_sub_cancel]
    intro y hy; constructor <;> linarith [hy.1, hy.2, h1.2, h2.1]

section core

variable {d e x y : ℝ} {u v : ℤ}

private lemma core_odd1 (hd : 0 < d) (he : e < 0) (huv : (1 ≤ u ∧ v ≤ 0) ∨ (u ≤ -1 ∧ 1 ≤ v))
    (hx : x ∈ Ioc 0 d) (hy : y ∈ Ioc e d) (h : y - x = u * d + v * e) : False := by
  obtain ⟨hx1, hx2⟩ := hx; obtain ⟨hy1, hy2⟩ := hy
  rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · have hu' : (1 : ℝ) ≤ u := by exact_mod_cast hu
    have hv' : (v : ℝ) ≤ 0 := by exact_mod_cast hv
    nlinarith
  · have hu' : (u : ℝ) ≤ -1 := by exact_mod_cast hu
    have hv' : (1 : ℝ) ≤ v := by exact_mod_cast hv
    nlinarith

private lemma core_odd2 (hd : 0 < d) (he : e < 0) (huv : (1 ≤ u ∧ v ≤ -1) ∨ (u ≤ -1 ∧ 1 ≤ v))
    (hx : x ∈ Ioc e 0) (hy : y ∈ Ioc e d) (h : y - x = u * d + v * e) : False := by
  obtain ⟨hx1, hx2⟩ := hx; obtain ⟨hy1, hy2⟩ := hy
  rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · have hu' : (1 : ℝ) ≤ u := by exact_mod_cast hu
    have hv' : (v : ℝ) ≤ -1 := by exact_mod_cast hv
    nlinarith
  · have hu' : (u : ℝ) ≤ -1 := by exact_mod_cast hu
    have hv' : (1 : ℝ) ≤ v := by exact_mod_cast hv
    nlinarith

private lemma core_even1 (hd : d < 0) (he : 0 < e) (huv : (1 ≤ u ∧ v ≤ 0) ∨ (u ≤ -1 ∧ 1 ≤ v))
    (hx : x ∈ Ico d 0) (hy : y ∈ Ico d e) (h : y - x = u * d + v * e) : False := by
  obtain ⟨hx1, hx2⟩ := hx; obtain ⟨hy1, hy2⟩ := hy
  rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · have hu' : (1 : ℝ) ≤ u := by exact_mod_cast hu
    have hv' : (v : ℝ) ≤ 0 := by exact_mod_cast hv
    nlinarith
  · have hu' : (u : ℝ) ≤ -1 := by exact_mod_cast hu
    have hv' : (1 : ℝ) ≤ v := by exact_mod_cast hv
    nlinarith

private lemma core_even2 (hd : d < 0) (he : 0 < e) (huv : (1 ≤ u ∧ v ≤ -1) ∨ (u ≤ -1 ∧ 1 ≤ v))
    (hx : x ∈ Ico 0 e) (hy : y ∈ Ico d e) (h : y - x = u * d + v * e) : False := by
  obtain ⟨hx1, hx2⟩ := hx; obtain ⟨hy1, hy2⟩ := hy
  rcases huv with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · have hu' : (1 : ℝ) ≤ u := by exact_mod_cast hu
    have hv' : (v : ℝ) ≤ -1 := by exact_mod_cast hv
    nlinarith
  · have hu' : (u : ℝ) ≤ -1 := by exact_mod_cast hu
    have hv' : (1 : ℝ) ≤ v := by exact_mod_cast hv
    nlinarith

end core

/-- **Lemma 6.2 (`lemma-rt`), first assertion.**  Let `n ≥ 1` (the paper takes `n ≥ 2`).
If `x ∈ J_{n,1}` then `z_{q_n} = x + q_n α ∈ J̃_n (mod 1)` (namely `x + q_nα - p_n ∈ J̃_n`)
and `z_k ∉ J̃_n (mod 1)` for `1 ≤ k ≤ q_n - 1`. -/
theorem lemma_rt_one {α : ℝ} (hα : Irrational α) {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx : x ∈ J1 α n) :
    x + qN α n * α - pZ α n ∈ Jt α n ∧
      ∀ k : ℕ, 1 ≤ k → k < qN α n → ∀ m : ℤ, x + k * α - m ∉ Jt α n := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have hret : x + qN α (N + 1) * α - pZ α (N + 1) = x + delta α (N + 1) := by
    rw [delta_eq_cast hα]; ring
  have hQ0 : (1 : ℤ) ≤ qN α N := by exact_mod_cast one_le_qN hα N
  have hQ : (qN α N : ℤ) ≤ qN α (N + 1) := by exact_mod_cast qN_le_succ hα N
  refine ⟨?_, fun k hk hk' m hmem => ?_⟩
  · rw [hret]
    by_cases he : Even (N + 1)
    · have hd := delta_neg_of_odd hα (Nat.even_add_one.1 he |> Nat.not_even_iff_odd.1)
      have he' := delta_pos_of_even hα he
      simp only [J1, he, ↓reduceIte, Nat.add_sub_cancel] at hx
      rw [Jt_eq_even hα hn he, Nat.add_sub_cancel]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · have hd := delta_pos_of_even hα (by simpa [Nat.even_add_one] using he)
      have he' := delta_neg_of_odd hα (Nat.not_even_iff_odd.1 he)
      simp only [J1, he, ↓reduceIte, Nat.add_sub_cancel] at hx
      rw [Jt_eq_odd hα hn he, Nat.add_sub_cancel]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · obtain ⟨u, v, hkuv, hrel⟩ := decomp hα N k m
    have huv := uv_cases hQ0 hQ (by exact_mod_cast hk) (by exact_mod_cast hk') hkuv
    have hyx : (x + k * α - m) - x = u * delta α N + v * delta α (N + 1) := by
      rw [← hrel]; push_cast; ring
    by_cases he : Even (N + 1)
    · have hd := delta_neg_of_odd hα (Nat.even_add_one.1 he |> Nat.not_even_iff_odd.1)
      have he' := delta_pos_of_even hα he
      simp only [J1, he, ↓reduceIte, Nat.add_sub_cancel] at hx
      rw [Jt_eq_even hα hn he, Nat.add_sub_cancel] at hmem
      exact core_even1 hd he' huv hx hmem hyx
    · have hd := delta_pos_of_even hα (by simpa [Nat.even_add_one] using he)
      have he' := delta_neg_of_odd hα (Nat.not_even_iff_odd.1 he)
      simp only [J1, he, ↓reduceIte, Nat.add_sub_cancel] at hx
      rw [Jt_eq_odd hα hn he, Nat.add_sub_cancel] at hmem
      exact core_odd1 hd he' huv hx hmem hyx

/-- **Lemma 6.2 (`lemma-rt`), second assertion.**  If `x ∈ J_{n,2}` then
`x + q_{n-1}α - p_{n-1} ∈ J̃_n` and `z_k ∉ J̃_n (mod 1)` for `1 ≤ k ≤ q_{n-1} - 1`. -/
theorem lemma_rt_two {α : ℝ} (hα : Irrational α) {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx : x ∈ J2 α n) :
    x + qN α (n - 1) * α - pZ α (n - 1) ∈ Jt α n ∧
      ∀ k : ℕ, 1 ≤ k → k < qN α (n - 1) → ∀ m : ℤ, x + k * α - m ∉ Jt α n := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hret : x + qN α N * α - pZ α N = x + delta α N := by
    rw [delta_eq_cast hα]; ring
  have hQ0 : (1 : ℤ) ≤ qN α N := by exact_mod_cast one_le_qN hα N
  have hQ : (qN α N : ℤ) ≤ qN α (N + 1) := by exact_mod_cast qN_le_succ hα N
  refine ⟨?_, fun k hk hk' m hmem => ?_⟩
  · rw [hret]
    by_cases he : Even (N + 1)
    · have hd := delta_neg_of_odd hα (Nat.even_add_one.1 he |> Nat.not_even_iff_odd.1)
      have he' := delta_pos_of_even hα he
      simp only [J2, he, ↓reduceIte] at hx
      rw [Jt_eq_even hα hn he, Nat.add_sub_cancel]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · have hd := delta_pos_of_even hα (by simpa [Nat.even_add_one] using he)
      have he' := delta_neg_of_odd hα (Nat.not_even_iff_odd.1 he)
      simp only [J2, he, ↓reduceIte] at hx
      rw [Jt_eq_odd hα hn he, Nat.add_sub_cancel]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · obtain ⟨u, v, hkuv, hrel⟩ := decomp hα N k m
    have huv := uv_cases' hQ0 hQ (by exact_mod_cast hk) (by exact_mod_cast hk') hkuv
    have hyx : (x + k * α - m) - x = u * delta α N + v * delta α (N + 1) := by
      rw [← hrel]; push_cast; ring
    by_cases he : Even (N + 1)
    · have hd := delta_neg_of_odd hα (Nat.even_add_one.1 he |> Nat.not_even_iff_odd.1)
      have he' := delta_pos_of_even hα he
      simp only [J2, he, ↓reduceIte] at hx
      rw [Jt_eq_even hα hn he, Nat.add_sub_cancel] at hmem
      exact core_even2 hd he' huv hx hmem hyx
    · have hd := delta_pos_of_even hα (by simpa [Nat.even_add_one] using he)
      have he' := delta_neg_of_odd hα (Nat.not_even_iff_odd.1 he)
      simp only [J2, he, ↓reduceIte] at hx
      rw [Jt_eq_odd hα hn he, Nat.add_sub_cancel] at hmem
      exact core_odd2 hd he' huv hx hmem hyx

/-- `z_k = x + kα` lies in `J̃_n` modulo `1`. -/
def Returns (α : ℝ) (n : ℕ) (x : ℝ) (k : ℕ) : Prop := ∃ m : ℤ, x + k * α - m ∈ Jt α n

/-- **First return to `J̃_n`.**  For `x ∈ J̃_n` the first return time of the orbit
`x + kα (mod 1)` to `J̃_n` is `q_n` or `q_{n-1}`. -/
theorem first_return {α : ℝ} (hα : Irrational α) {n : ℕ} (hn : 1 ≤ n) {x : ℝ}
    (hx : x ∈ Jt α n) :
    ∃ N : ℕ, (N = qN α n ∨ N = qN α (n - 1)) ∧ 1 ≤ N ∧ Returns α n x N ∧
      ∀ k : ℕ, 1 ≤ k → k < N → ¬Returns α n x k := by
  rcases hx with hx | hx
  · obtain ⟨h1, h2⟩ := lemma_rt_one hα hn hx
    exact ⟨qN α n, Or.inl rfl, one_le_qN hα n, ⟨_, h1⟩,
      fun k hk hk' ⟨m, hm⟩ => h2 k hk hk' m hm⟩
  · obtain ⟨h1, h2⟩ := lemma_rt_two hα hn hx
    exact ⟨qN α (n - 1), Or.inr rfl, one_le_qN hα _, ⟨_, h1⟩,
      fun k hk hk' ⟨m, hm⟩ => h2 k hk hk' m hm⟩

/-- **Return gaps.**  If `k₁ < k₂` are consecutive return times of the orbit `x + kα (mod 1)`
to `J̃_n`, then `k₂ - k₁ ∈ {q_n, q_{n-1}}`. -/
theorem return_gap {α : ℝ} (hα : Irrational α) {n : ℕ} (hn : 1 ≤ n) {x : ℝ} {k₁ k₂ : ℕ}
    (h₁ : Returns α n x k₁) (h₂ : Returns α n x k₂) (h12 : k₁ < k₂)
    (hgap : ∀ k, k₁ < k → k < k₂ → ¬Returns α n x k) :
    k₂ - k₁ = qN α n ∨ k₂ - k₁ = qN α (n - 1) := by
  obtain ⟨m₁, hm₁⟩ := h₁
  obtain ⟨N, hN, hN1, ⟨m, hm⟩, hfirst⟩ := first_return hα hn hm₁
  have key : k₂ = k₁ + N := by
    rcases lt_trichotomy k₂ (k₁ + N) with h | h | h
    · exfalso
      obtain ⟨m₂, hm₂⟩ := h₂
      refine hfirst (k₂ - k₁) (by omega) (by omega) ⟨m₂ - m₁, ?_⟩
      convert hm₂ using 1
      rw [Nat.cast_sub h12.le]; push_cast; ring
    · exact h
    · exfalso
      refine hgap (k₁ + N) (by omega) h ⟨m₁ + m, ?_⟩
      convert hm using 1
      push_cast; ring
  rw [key, Nat.add_sub_cancel_left]; exact hN

/-! ### The sum `∑ 1/sin²(πkα)`  (lines ~1612–1636) -/

/-- `|sin(πx)| ≥ 2‖x‖_𝕋`. -/
lemma two_abs_sub_round_le_abs_sin (x : ℝ) : 2 * |x - round x| ≤ |Real.sin (π * x)| := by
  set t := x - round x with ht
  have hx : π * x = π * t + ((round x : ℤ) : ℝ) * π := by rw [ht]; ring
  have h1 : |Real.sin (π * x)| = |Real.sin (π * t)| := by
    rw [hx, Real.sin_add_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  have ht2 : |t| ≤ 1 / 2 := abs_sub_round x
  have hs : 2 * |t| ≤ Real.sin (π * |t|) := by
    have := Real.mul_le_sin (x := π * |t|) (by positivity) (by nlinarith [pi_pos])
    calc 2 * |t| = 2 / π * (π * |t|) := by field_simp
      _ ≤ _ := this
  have h2 : Real.sin (π * |t|) ≤ |Real.sin (π * t)| := by
    rcases abs_cases t with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]; exact le_abs_self _
    · rw [h, mul_neg, Real.sin_neg]; exact neg_le_abs _
  linarith

/-- `∑_{j=1}^{N} 1/j² ≤ 2`. -/
lemma sum_inv_sq_le_two (N : ℕ) : ∑ j ∈ Finset.Icc 1 N, 1 / (j : ℝ) ^ 2 ≤ 2 := by
  have key : ∀ N : ℕ, 1 ≤ N → ∑ j ∈ Finset.Icc 1 N, 1 / (j : ℝ) ^ 2 ≤ 2 - 1 / (N : ℝ) := by
    intro N hN
    induction N, hN using Nat.le_induction with
    | base => norm_num
    | succ N hN ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
      have : 1 / ((N + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / (N : ℝ) - 1 / ((N + 1 : ℕ) : ℝ) := by
        push_cast
        rw [_root_.div_sub_div _ _ (by positivity) (by positivity),
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp [Finset.Icc_eq_empty_of_lt]
  · linarith [key N h, (by positivity : (0 : ℝ) ≤ 1 / (N : ℝ))]

/-- Sum of `1/j² + 1/(Q-j)²` over `1 ≤ j ≤ Q - 1` is at most `4`. -/
lemma sum_inv_sq_reflect_le (Q : ℕ) :
    ∑ j ∈ Finset.Icc 1 (Q - 1), (1 / (j : ℝ) ^ 2 + 1 / ((Q - j : ℕ) : ℝ) ^ 2) ≤ 4 := by
  rw [Finset.sum_add_distrib]
  have h2 : ∑ j ∈ Finset.Icc 1 (Q - 1), 1 / ((Q - j : ℕ) : ℝ) ^ 2 =
      ∑ j ∈ Finset.Icc 1 (Q - 1), 1 / (j : ℝ) ^ 2 := by
    refine Finset.sum_nbij' (fun j => Q - j) (fun j => Q - j) ?_ ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_Icc] at hj ⊢; omega
    · intro j hj
      simp only [Finset.mem_Icc] at hj ⊢; omega
    · intro j hj
      simp only [Finset.mem_Icc] at hj; omega
    · intro j hj
      simp only [Finset.mem_Icc] at hj; omega
    · intro j hj; rfl
  rw [h2]
  linarith [sum_inv_sq_le_two (Q - 1)]

/-- Abstract form of the bound: if `Q ≥ 1` and `P` are coprime, `Q |Qα - P| ≤ 1`, and
`|kα - i| ≥ 1/(2Q)` for `0 < k < Q`, `i ∈ ℤ`, then `∑_{k=1}^{L} 1/sin²(πkα) ≤ 4Q²` for `L < Q`. -/
lemma sum_inv_sin_sq_le_aux (α : ℝ) (Q : ℕ) (P : ℤ) (hQ1 : 1 ≤ Q) (hcop : IsCoprime (Q : ℤ) P)
    (hsmall : (Q : ℝ) * |(Q : ℝ) * α - P| ≤ 1)
    (hbest : ∀ k : ℕ, 1 ≤ k → k < Q → ∀ i : ℤ, 1 / (2 * (Q : ℝ)) ≤ |(k : ℝ) * α - i|)
    (L : ℕ) (hL : L < Q) :
    ∑ k ∈ Finset.Icc 1 L, 1 / Real.sin (π * k * α) ^ 2 ≤ 4 * (Q : ℝ) ^ 2 := by
  have hQpos : (0 : ℤ) < Q := by exact_mod_cast hQ1
  have hQpos' : (0 : ℝ) < Q := by exact_mod_cast hQ1
  set j : ℕ → ℕ := fun k => ((P * k) % (Q : ℤ)).toNat with hjdef
  have hj_cast : ∀ k, ((j k : ℕ) : ℤ) = (P * k) % Q := fun k =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ hQpos.ne')
  have hj_lt : ∀ k, j k < Q := by
    intro k
    have h := Int.emod_lt_of_pos (P * k) hQpos
    rw [← hj_cast] at h; exact_mod_cast h
  have hj_pos : ∀ k, 1 ≤ k → k < Q → 1 ≤ j k := by
    intro k hk hkQ
    by_contra h
    have h0 : j k = 0 := by omega
    have hd : (Q : ℤ) ∣ P * k := Int.dvd_of_emod_eq_zero (by rw [← hj_cast, h0, Nat.cast_zero])
    have hd' : (Q : ℤ) ∣ (k : ℤ) := hcop.dvd_of_dvd_mul_left hd
    have := Int.le_of_dvd (by exact_mod_cast hk) hd'
    have : (k : ℤ) < Q := by exact_mod_cast hkQ
    omega
  have hj_inj : Set.InjOn j (Finset.Icc 1 (Q - 1) : Set ℕ) := by
    intro k₁ hk₁ k₂ hk₂ hjk
    simp only [Finset.coe_Icc, Set.mem_Icc] at hk₁ hk₂
    have h1 : (P * k₁) % (Q : ℤ) = (P * k₂) % Q := by rw [← hj_cast, ← hj_cast, hjk]
    have hd : (Q : ℤ) ∣ P * k₂ - P * k₁ := Int.ModEq.dvd h1
    rw [← mul_sub] at hd
    have hd' : (Q : ℤ) ∣ ((k₂ : ℤ) - k₁) := hcop.dvd_of_dvd_mul_left hd
    have : |(k₂ : ℤ) - k₁| < Q := by rw [abs_lt]; constructor <;> omega
    have := Int.eq_zero_of_abs_lt_dvd hd' this
    omega
  have hbound : ∀ k, 1 ≤ k → k < Q →
      1 / Real.sin (π * k * α) ^ 2 ≤
        (Q : ℝ) ^ 2 * (1 / (j k : ℝ) ^ 2 + 1 / ((Q - j k : ℕ) : ℝ) ^ 2) := by
    intro k hk hkQ
    have hj1 := hj_pos k hk hkQ
    have hjQ := hj_lt k
    set ρ := min (j k) (Q - j k) with hρ
    have hρ1 : 1 ≤ ρ := by omega
    -- `|kα - i| ≥ ρ/(2Q)` for all integers `i`
    have hA : ∀ i : ℤ, (ρ : ℝ) / (2 * Q) ≤ |(k : ℝ) * α - i| := by
      intro i
      have hid : (k : ℝ) * α - i =
          ((P * k - i * Q : ℤ) : ℝ) / Q + k * ((Q : ℝ) * α - P) / Q := by
        push_cast; field_simp; ring
      have hwρ : (ρ : ℤ) ≤ |P * k - i * Q| := by
        have hdiv := Int.mul_ediv_add_emod (P * k) Q
        have hwt : P * k - i * Q = (j k : ℤ) + Q * ((P * k) / (Q : ℤ) - i) := by
          rw [hj_cast]; linear_combination -hdiv
        have hρj : (ρ : ℤ) ≤ j k := by exact_mod_cast min_le_left _ _
        have hρj' : (ρ : ℤ) ≤ Q - j k := by
          have : ρ ≤ Q - j k := min_le_right _ _
          omega
        rw [hwt]
        rcases le_or_gt 0 ((P * k) / (Q : ℤ) - i) with ht | ht
        · rw [abs_of_nonneg (by nlinarith)]; nlinarith
        · rw [abs_of_neg (by nlinarith)]; nlinarith
      have hwρ' : (ρ : ℝ) ≤ |((P * k - i * Q : ℤ) : ℝ)| := by exact_mod_cast hwρ
      have hkδ : |(k : ℝ) * ((Q : ℝ) * α - P)| ≤ 1 := by
        rw [abs_mul, abs_of_nonneg (by positivity)]
        have : (k : ℝ) ≤ Q := by exact_mod_cast hkQ.le
        calc (k : ℝ) * |(Q : ℝ) * α - P| ≤ Q * |(Q : ℝ) * α - P| := by gcongr
          _ ≤ 1 := hsmall
      have hlow : ((ρ : ℝ) - 1) / Q ≤ |(k : ℝ) * α - i| := by
        rw [hid, ← add_div, abs_div, abs_of_pos hQpos']
        gcongr
        have := abs_add_le (((P * k - i * Q : ℤ) : ℝ) + k * ((Q : ℝ) * α - P))
          (-(k * ((Q : ℝ) * α - P)))
        rw [add_neg_cancel_right, abs_neg] at this
        linarith
      rcases eq_or_lt_of_le hρ1 with h1 | h2
      · rw [← h1]
        have := hbest k hk hkQ i
        push_cast
        linarith
      · have h2' : (2 : ℝ) ≤ ρ := by exact_mod_cast h2
        refine le_trans ?_ hlow
        rw [div_le_div_iff₀ (by positivity) hQpos']
        nlinarith
    -- `|sin(πkα)| ≥ ρ/Q`
    have hsin : (ρ : ℝ) / Q ≤ |Real.sin (π * k * α)| := by
      have h1 := two_abs_sub_round_le_abs_sin ((k : ℝ) * α)
      have h2 := hA (round ((k : ℝ) * α))
      rw [mul_assoc]
      calc (ρ : ℝ) / Q = 2 * ((ρ : ℝ) / (2 * Q)) := by field_simp
        _ ≤ _ := by linarith
    have hρpos : (0 : ℝ) < ρ / Q := by
      have : (1 : ℝ) ≤ ρ := by exact_mod_cast hρ1
      positivity
    have hsq : ((ρ : ℝ) / Q) ^ 2 ≤ Real.sin (π * k * α) ^ 2 := by
      rw [← sq_abs (Real.sin _)]
      exact pow_le_pow_left₀ hρpos.le hsin 2
    have h3 : 1 / Real.sin (π * k * α) ^ 2 ≤ (Q : ℝ) ^ 2 * (1 / (ρ : ℝ) ^ 2) := by
      calc 1 / Real.sin (π * k * α) ^ 2 ≤ 1 / ((ρ : ℝ) / Q) ^ 2 :=
            one_div_le_one_div_of_le (by positivity) hsq
        _ = _ := by field_simp
    refine h3.trans ?_
    gcongr
    rcases min_choice (j k) (Q - j k) with h | h
    · rw [hρ, h]
      have : (0 : ℝ) ≤ 1 / ((Q - j k : ℕ) : ℝ) ^ 2 := by positivity
      linarith
    · rw [hρ, h]
      have : (0 : ℝ) ≤ 1 / (j k : ℝ) ^ 2 := by positivity
      linarith
  -- sum up
  have hsub : Finset.Icc 1 L ⊆ Finset.Icc 1 (Q - 1) := Finset.Icc_subset_Icc le_rfl (by omega)
  calc ∑ k ∈ Finset.Icc 1 L, 1 / Real.sin (π * k * α) ^ 2
      ≤ ∑ k ∈ Finset.Icc 1 (Q - 1), 1 / Real.sin (π * k * α) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ ∑ k ∈ Finset.Icc 1 (Q - 1),
          (Q : ℝ) ^ 2 * (1 / (j k : ℝ) ^ 2 + 1 / ((Q - j k : ℕ) : ℝ) ^ 2) := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        simp only [Finset.mem_Icc] at hk
        exact hbound k hk.1 (by omega)
    _ = (Q : ℝ) ^ 2 * ∑ i ∈ (Finset.Icc 1 (Q - 1)).image j,
          (1 / (i : ℝ) ^ 2 + 1 / ((Q - i : ℕ) : ℝ) ^ 2) := by
        rw [Finset.mul_sum, Finset.sum_image hj_inj]
    _ ≤ (Q : ℝ) ^ 2 * ∑ i ∈ Finset.Icc 1 (Q - 1),
          (1 / (i : ℝ) ^ 2 + 1 / ((Q - i : ℕ) : ℝ) ^ 2) := by
        have hsub2 : (Finset.Icc 1 (Q - 1)).image j ⊆ Finset.Icc 1 (Q - 1) := by
          intro i hi
          obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hi
          simp only [Finset.mem_Icc] at hk ⊢
          exact ⟨hj_pos k hk.1 (by omega), by have := hj_lt k; omega⟩
        exact mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun i _ _ => by positivity))
          (by positivity)
    _ ≤ (Q : ℝ) ^ 2 * 4 := by gcongr; exact sum_inv_sq_reflect_le Q
    _ = 4 * (Q : ℝ) ^ 2 := by ring

/-- **The bound (lines ~1612–1636).**  For `n ≥ 1` and `L ≤ q_n - 1`,
`∑_{k=1}^{L} 1/sin²(πkα) ≤ 4 q_n²`.  (The paper uses `L ≤ ⌊q_n/2⌋` and an unspecified
absolute constant `C`.)  Proof as in the paper: the points `kα (mod 1)`, `1 ≤ k < q_n`, lie
within `1/q_{n+1}` of the distinct points `j(k)/q_n`, `j(k) = p_n k mod q_n`, and
`‖kα‖ ≥ |δ_{n-1}| > 1/(2q_n)` by Lemma 6.2. -/
theorem sum_inv_sin_sq_le {α : ℝ} (hα : Irrational α) {n : ℕ} (hn : 1 ≤ n) {L : ℕ}
    (hL : L < qN α n) :
    ∑ k ∈ Finset.Icc 1 L, 1 / Real.sin (π * k * α) ^ 2 ≤ 4 * q α n ^ 2 := by
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  rw [← qN_cast hα]
  refine sum_inv_sin_sq_le_aux α (qN α (N + 1)) (pZ α (N + 1)) (one_le_qN hα _)
    (isCoprime_pZ_qN hα _).symm ?_ ?_ L hL
  · rw [← delta_eq_cast hα, qN_cast hα]
    have h1 := (abs_delta_bounds hα (N + 1)).2
    have h2 : q α (N + 1) ≤ q α (N + 1 + 1) := q_le_succ hα _
    have h3 := q_pos hα (N + 1)
    rw [lt_div_iff₀ (q_pos hα _)] at h1
    nlinarith [abs_nonneg (delta α (N + 1))]
  · intro k hk hkQ i
    have hba := abs_delta_le_abs_mul_sub hα N k i (by exact_mod_cast hk) (by exact_mod_cast hkQ)
    have hprev := (abs_delta_bounds hα N).1
    have hqN : q α N ≤ q α (N + 1) := q_le_succ hα N
    have : 1 / (2 * (qN α (N + 1) : ℝ)) ≤ 1 / (q α (N + 1) + q α N) := by
      rw [qN_cast hα]
      exact one_div_le_one_div_of_le (by linarith [q_pos hα N, q_pos hα (N + 1)]) (by linarith)
    push_cast at hba
    linarith

end CAH
