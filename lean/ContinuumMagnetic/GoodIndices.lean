import Mathlib

/-
# Paper III: density of good Landau indices
(Theorem `thm:high-energy-spectrum`, §5 "Normalization and density of good indices")

For fixed `s = s_B > 0` the good-index condition (hi-eq:good-index) reads
`|cos(2√(ns) - π/4)| ≥ Kε`. We prove

* `hasNatDensity_goodIndexSet`: for every `0 ≤ c ≤ 1` the set `{n : |cos(2√(ns) - π/4)| ≥ c}`
  has natural density `1 - (2/π) arcsin c` (eq. (hi-eq:density));
* `hasNatDensity_G0`: the set `𝒢₀ = {n ≥ 1 : |cos(2√(ns) - π/4)| ≥ n^{-1/8}}` has density one;
* the parameter definitions of (hi-eq:parameters): `α_B`, `s_B = π α_B`, `E_n`, the
  Laguerre polynomial `L_n` (parameter zero) and the form factor `f_n = e^{-s_B/2} L_n(s_B)`.

Instead of Weyl's criterion (as in the paper) we use an elementary counting argument:
`|cos u| ≥ c` iff `fract((u + arccos c)/π) ≤ 2 arccos c / π` (`le_abs_cos_iff`), and for the
slowly increasing phase `t_n = a√n + ψ` the number of `n < N` with `fract t_n ≤ l` is
`lN + O(√N)`: each period `k ≤ t_n < k+1` is an explicit interval of indices
(`count_block`) whose good part has length `l·(period length) + O(1)` (`Zf_defect`), and there are
`O(√N)` periods below `N` (`count_fractSet_bound`).
-/

open Filter Topology Real

noncomputable section

namespace CMS

open Classical in
/-- `S ⊆ ℕ` has natural density `d`: `#(S ∩ [1,N]) / N → d`. -/
def HasNatDensity (S : Set ℕ) (d : ℝ) : Prop :=
  Tendsto (fun N : ℕ => ((((Finset.Icc 1 N).filter (· ∈ S)).card : ℕ) : ℝ) / N) atTop (𝓝 d)

section Counting

open Classical

/-- A counting bound `|#(S ∩ [0,N)) - dN| ≤ C₁√N + C₂` implies natural density `d`. -/
theorem hasNatDensity_of_count_bound (S : Set ℕ) (d C₁ C₂ : ℝ)
    (h : ∀ N : ℕ, |(Nat.count (· ∈ S) N : ℝ) - d * N| ≤ C₁ * √N + C₂) :
    HasNatDensity S d := by
  have hC₁ : 0 ≤ C₁ + C₂ := by
    have := h 1; simp at this; linarith [abs_nonneg ((Nat.count (· ∈ S) 1 : ℝ) - d)]
  -- compare the filtered `Icc 1 N` with `count (N+1)`
  have hcmp : ∀ N : ℕ, ((((Finset.Icc 1 N).filter (· ∈ S)).card : ℕ) : ℝ) ≤ Nat.count (· ∈ S) (N+1) ∧
      (Nat.count (· ∈ S) (N+1) : ℝ) ≤ (((Finset.Icc 1 N).filter (· ∈ S)).card : ℕ) + 1 := by
    intro N
    rw [Nat.count_eq_card_filter_range]
    constructor
    · exact_mod_cast Finset.card_le_card (by
        intro x hx; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hx ⊢
        exact ⟨by omega, hx.2⟩)
    · have : (Finset.range (N+1)).filter (· ∈ S) ⊆ insert 0 ((Finset.Icc 1 N).filter (· ∈ S)) := by
        intro x hx; simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range,
          Finset.mem_insert] at hx ⊢
        rcases Nat.eq_zero_or_pos x with h0 | h0
        · exact Or.inl h0
        · exact Or.inr ⟨⟨h0, by omega⟩, hx.2⟩
      have := (Finset.card_le_card this).trans (Finset.card_insert_le _ _)
      exact_mod_cast this
  set K := 2 * |C₁| + |C₂| + |d| + 1 with hK
  have hbound : ∀ N : ℕ, 1 ≤ N → ‖((((Finset.Icc 1 N).filter (· ∈ S)).card : ℕ) : ℝ) / N - d‖
      ≤ K / √N := by
    intro N hN
    have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hs1 : 1 ≤ √(N : ℝ) := by rw [Real.one_le_sqrt]; exact hN'
    have hsN : √((N:ℝ) + 1) ≤ √N + 1 := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ N by positivity)]
    obtain ⟨h1, h2⟩ := hcmp N
    have hh := h (N+1)
    push_cast at hh
    set c := ((((Finset.Icc 1 N).filter (· ∈ S)).card : ℕ) : ℝ)
    set c' := (Nat.count (· ∈ S) (N+1) : ℝ)
    have hNpos : (0:ℝ) < N := by linarith
    have hdiff : |c - d * N| ≤ K * √N := by
      have e1 : |c' - d * (N+1)| ≤ |C₁| * (√N + 1) + |C₂| := by
        refine hh.trans ?_
        have := mul_le_mul_of_nonneg_left hsN (abs_nonneg C₁)
        have := le_abs_self C₁
        have : C₁ * √((N:ℝ)+1) ≤ |C₁| * √((N:ℝ)+1) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _)
        linarith [le_abs_self C₂]
      have h3 : |c - c' + d| ≤ 1 + |d| := by
        rw [abs_le]; constructor <;> cases abs_cases d <;> linarith
      have : |c - d * N| ≤ |c' - d * (N+1)| + (1 + |d|) := by
        calc |c - d * N| = |(c' - d * (N+1)) + (c - c' + d)| := by ring_nf
          _ ≤ |c' - d * (N+1)| + |c - c' + d| := abs_add_le _ _
          _ ≤ _ := by linarith
      rw [hK]
      nlinarith [abs_nonneg C₁, abs_nonneg C₂, abs_nonneg d, mul_le_mul_of_nonneg_left hs1 (abs_nonneg C₁),
        mul_le_mul_of_nonneg_left hs1 (abs_nonneg C₂), mul_le_mul_of_nonneg_left hs1 (abs_nonneg d)]
    rw [Real.norm_eq_abs, div_sub' (ne_of_gt hNpos), abs_div, abs_of_pos hNpos]
    rw [div_le_div_iff₀ hNpos (by positivity)]
    have hsq : (N:ℝ) = √N * √N := (Real.mul_self_sqrt hNpos.le).symm
    calc |c - N * d| * √N = |c - d * N| * √N := by rw [mul_comm (N:ℝ) d]
      _ ≤ K * √N * √N := mul_le_mul_of_nonneg_right hdiff (Real.sqrt_nonneg _)
      _ = K * N := by rw [mul_assoc, ← hsq]
  rw [HasNatDensity, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    ((eventually_ge_atTop 1).mono hbound) ?_
  exact Tendsto.div_atTop tendsto_const_nhds
    ((Real.tendsto_sqrt_atTop).comp tendsto_natCast_atTop_atTop)

end Counting

section SqrtCounting

open Classical

/-- The slowly increasing phase `t_n = a√n + ψ`. -/
def tseq (a ψ : ℝ) (n : ℕ) : ℝ := a * √(n : ℝ) + ψ

/-- The squared (clipped) inverse phase `Z(y) = max(0, (y-ψ)/a)²`; it measures
`#{n : t_n < y}` up to `O(1)`. -/
def Zf (a ψ y : ℝ) : ℝ := (max 0 ((y - ψ) / a)) ^ 2

/-- `#{n : t_n < y}`. -/
def uCnt (a ψ y : ℝ) : ℕ := ⌈Zf a ψ y⌉₊

/-- `#{n : t_n ≤ y}`. -/
def vCnt (a ψ y : ℝ) : ℕ := if y < ψ then 0 else ⌊((y - ψ) / a) ^ 2⌋₊ + 1

/-- The indices whose phase lies in the window `[0, l]` modulo one. -/
def fractSet (a ψ l : ℝ) : Set ℕ := {n | Int.fract (tseq a ψ n) ≤ l}

variable {a ψ l : ℝ}

lemma tseq_ge (ha : 0 < a) (n : ℕ) : ψ ≤ tseq a ψ n := by
  unfold tseq; have := Real.sqrt_nonneg (n : ℝ); nlinarith

lemma lt_uCnt_iff (ha : 0 < a) (y : ℝ) (n : ℕ) :
    n < uCnt a ψ y ↔ tseq a ψ n < y := by
  unfold uCnt Zf
  rw [Nat.lt_ceil]
  rcases le_or_gt y ψ with h | h
  · have h0 : (y - ψ) / a ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le
    rw [max_eq_left h0]
    have := tseq_ge (ψ := ψ) ha n
    constructor
    · intro hn; have : (0:ℝ) ≤ n := Nat.cast_nonneg n; nlinarith
    · intro hn; linarith
  · have hz : 0 < (y - ψ) / a := div_pos (by linarith) ha
    rw [max_eq_right hz.le, ← Real.sqrt_lt' hz, lt_div_iff₀ ha]
    unfold tseq; constructor <;> intro <;> linarith
  
lemma lt_vCnt_iff (ha : 0 < a) (y : ℝ) (n : ℕ) :
    n < vCnt a ψ y ↔ tseq a ψ n ≤ y := by
  unfold vCnt
  have := tseq_ge (ψ := ψ) ha n
  split_ifs with h
  · simp only [Nat.not_lt_zero, false_iff, not_le]; linarith
  · push Not at h
    have hz : 0 ≤ (y - ψ) / a := div_nonneg (by linarith) ha.le
    rw [Nat.lt_add_one_iff, Nat.le_floor_iff (sq_nonneg _), ← Real.sqrt_le_left hz, le_div_iff₀ ha]
    unfold tseq; constructor <;> intro <;> linarith

lemma Zf_nonneg (a ψ y : ℝ) : 0 ≤ Zf a ψ y := sq_nonneg _

lemma uCnt_bounds (a ψ y : ℝ) :
    Zf a ψ y ≤ uCnt a ψ y ∧ (uCnt a ψ y : ℝ) ≤ Zf a ψ y + 1 :=
  ⟨Nat.le_ceil _, (Nat.ceil_lt_add_one (Zf_nonneg a ψ y)).le⟩

lemma vCnt_bounds (ha : 0 < a) (y : ℝ) :
    Zf a ψ y ≤ vCnt a ψ y ∧ (vCnt a ψ y : ℝ) ≤ Zf a ψ y + 1 := by
  unfold vCnt Zf
  split_ifs with h
  · have h0 : (y - ψ) / a ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le
    rw [max_eq_left h0]; norm_num
  · push Not at h
    have hz : 0 ≤ (y - ψ) / a := div_nonneg (by linarith) ha.le
    rw [max_eq_right hz]; push_cast
    exact ⟨(Nat.lt_floor_add_one _).le, by linarith [Nat.floor_le (sq_nonneg ((y - ψ) / a))]⟩

lemma Zf_of_le (ha : 0 < a) {y : ℝ} (h : ψ ≤ y) : Zf a ψ y = ((y - ψ) / a) ^ 2 := by
  unfold Zf; rw [max_eq_right (div_nonneg (by linarith) ha.le)]

lemma Zf_of_ge (ha : 0 < a) {y : ℝ} (h : y ≤ ψ) : Zf a ψ y = 0 := by
  unfold Zf; rw [max_eq_left (div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le)]; ring

lemma Zf_le_of_le_one (ha : 0 < a) (hψ : 0 ≤ ψ) {y : ℝ} (hy : y ≤ 1) : Zf a ψ y ≤ 1 / a ^ 2 := by
  rcases le_total y ψ with h | h
  · rw [Zf_of_ge ha h]; positivity
  · rw [Zf_of_le ha h, div_pow, div_le_div_iff_of_pos_right (pow_pos ha 2)]
    have : 0 ≤ y - ψ := by linarith
    nlinarith

/-- Convexity defect of `Z` on a period window: `|Z(k+l) - (1-l)Z(k) - lZ(k+1)| ≤ 1/a²`. -/
lemma Zf_defect (ha : 0 < a) (hψ0 : 0 ≤ ψ) (hψ1 : ψ < 1) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (k : ℕ) :
    |Zf a ψ (k + l) - (1 - l) * Zf a ψ k - l * Zf a ψ (k + 1)| ≤ 1 / a ^ 2 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [Nat.cast_zero, zero_add]
    rw [Zf_of_ge ha hψ0]
    have h1 := Zf_le_of_le_one ha hψ0 hl1
    have h2 := Zf_le_of_le_one ha hψ0 le_rfl
    have h3 := Zf_nonneg a ψ l
    have h4 := Zf_nonneg a ψ 1
    have : l * Zf a ψ 1 ≤ 1 / a ^ 2 := by nlinarith
    rw [abs_le]; constructor <;> nlinarith
  · have hk' : (1:ℝ) ≤ k := by exact_mod_cast hk
    rw [Zf_of_le ha (y := (k:ℝ) + l) (by linarith), Zf_of_le ha (y := (k:ℝ)) (by linarith),
      Zf_of_le ha (y := (k:ℝ) + 1) (by linarith)]
    have : (((k:ℝ) + l - ψ) / a) ^ 2 - (1 - l) * ((k - ψ) / a) ^ 2 - l * ((k + 1 - ψ) / a) ^ 2
        = (l ^ 2 - l) / a ^ 2 := by field_simp; ring
    rw [this, abs_div, abs_of_pos (pow_pos ha 2)]
    gcongr
    rw [abs_le]; constructor <;> nlinarith

/-- Growth of `Z` over one period: `Z(k+1) - Z(k) ≤ (2k+2)/a²`. -/
lemma Zf_step (ha : 0 < a) (hψ0 : 0 ≤ ψ) (k : ℕ) :
    Zf a ψ (k + 1) - Zf a ψ k ≤ (2 * k + 2) / a ^ 2 := by
  unfold Zf
  set p := max 0 (((k:ℝ) - ψ) / a)
  set q := max 0 (((k:ℝ) + 1 - ψ) / a)
  have hp : 0 ≤ p := le_max_left _ _
  have hpq : p ≤ q := max_le_max le_rfl (div_le_div_of_nonneg_right (by linarith) ha.le)
  have hq1 : q ≤ p + 1 / a := by
    have : ((k:ℝ) + 1 - ψ) / a = ((k:ℝ) - ψ) / a + 1 / a := by ring
    show max 0 (((k:ℝ) + 1 - ψ) / a) ≤ p + 1 / a
    rw [this]
    apply max_le (add_nonneg hp (by positivity))
    linarith [le_max_right 0 (((k:ℝ) - ψ) / a)]
  have hq2 : q ≤ (k + 1) / a := max_le (div_nonneg (by positivity) ha.le)
    (div_le_div_of_nonneg_right (by linarith) ha.le)
  have : q ^ 2 - p ^ 2 ≤ (1 / a) * (2 * ((k + 1) / a)) := by
    have : q ^ 2 - p ^ 2 = (q - p) * (q + p) := by ring
    rw [this]
    apply mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
  calc q ^ 2 - p ^ 2 ≤ (1 / a) * (2 * ((k + 1) / a)) := this
    _ = (2 * k + 2) / a ^ 2 := by field_simp

end SqrtCounting

section SqrtDensity

open Classical

variable {a ψ l : ℝ}

/-- Inside the `k`-th period `[uCnt k, uCnt (k+1))`, an index is good iff it lies before
`vCnt (k+l)`. -/
lemma mem_fractSet_iff_of_block (ha : 0 < a) (k : ℕ) {n : ℕ}
    (h1 : uCnt a ψ k ≤ n) (h2 : n < uCnt a ψ (k + 1)) :
    n ∈ fractSet a ψ l ↔ n < vCnt a ψ (k + l) := by
  have hk1 : (k:ℝ) ≤ tseq a ψ n := by
    have := (lt_uCnt_iff (ψ := ψ) ha k n).not.1 (by omega); linarith
  have hk2 : tseq a ψ n < k + 1 := (lt_uCnt_iff ha _ n).1 h2
  have hfl : ⌊tseq a ψ n⌋ = (k : ℤ) := Int.floor_eq_iff.2 ⟨by exact_mod_cast hk1, by exact_mod_cast hk2⟩
  rw [lt_vCnt_iff ha, fractSet, Set.mem_ofPred_eq, Int.fract, hfl]
  push_cast
  constructor <;> intro <;> linarith

lemma uCnt_le_vCnt (ha : 0 < a) (hl0 : 0 ≤ l) (k : ℕ) : uCnt a ψ k ≤ vCnt a ψ (k + l) := by
  by_contra hc; push Not at hc
  have h1 := (lt_uCnt_iff (ψ := ψ) ha k _).1 hc
  have h2 := (lt_vCnt_iff (ψ := ψ) ha ((k:ℝ) + l) (vCnt a ψ (k + l))).not.1 (lt_irrefl _)
  linarith

lemma vCnt_le_uCnt (ha : 0 < a) (hl1 : l < 1) (k : ℕ) : vCnt a ψ (k + l) ≤ uCnt a ψ (k + 1) := by
  by_contra hc; push Not at hc
  have h1 := (lt_vCnt_iff (ψ := ψ) ha _ _).1 hc
  have h2 := (lt_uCnt_iff (ψ := ψ) ha ((k:ℝ) + 1) (uCnt a ψ (k + 1))).not.1 (lt_irrefl _)
  linarith

/-- Exact count of good indices over one period. -/
lemma count_block (ha : 0 < a) (hl0 : 0 ≤ l) (hl1 : l < 1) (k : ℕ) :
    Nat.count (· ∈ fractSet a ψ l) (uCnt a ψ (k + 1)) =
      Nat.count (· ∈ fractSet a ψ l) (uCnt a ψ k) + (vCnt a ψ (k + l) - uCnt a ψ k) := by
  have h1 := uCnt_le_vCnt (ψ := ψ) ha hl0 k
  have h2 := vCnt_le_uCnt (ψ := ψ) ha hl1 k
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (h1.trans h2)
  rw [hd, Nat.count_add]
  congr 1
  rw [Nat.count_eq_card_filter_range]
  have : (Finset.range d).filter (fun j => uCnt a ψ k + j ∈ fractSet a ψ l)
      = Finset.range (vCnt a ψ (k + l) - uCnt a ψ k) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hj, hg⟩
      have := (mem_fractSet_iff_of_block ha k (n := uCnt a ψ k + j) (by omega) (by omega)).1 hg
      omega
    · intro hj
      refine ⟨by omega, ?_⟩
      exact (mem_fractSet_iff_of_block ha k (n := uCnt a ψ k + j) (by omega) (by omega)).2
        (by omega)
  rw [this, Finset.card_range]

lemma uCnt_zero (ha : 0 < a) (hψ0 : 0 ≤ ψ) : uCnt a ψ 0 = 0 := by
  unfold uCnt; rw [Zf_of_ge ha hψ0]; simp

/-- Error at period boundaries: `|#good(< uCnt k) - l · uCnt k| ≤ (1 + 1/a²) k`. -/
lemma count_block_error (ha : 0 < a) (hψ0 : 0 ≤ ψ) (hψ1 : ψ < 1) (hl0 : 0 ≤ l) (hl1 : l < 1)
    (k : ℕ) :
    |(Nat.count (· ∈ fractSet a ψ l) (uCnt a ψ k) : ℝ) - l * uCnt a ψ k| ≤ (1 + 1 / a ^ 2) * k := by
  induction k with
  | zero => simp [uCnt_zero ha hψ0]
  | succ k ih =>
    have hc := count_block (ψ := ψ) ha hl0 hl1 k
    have h1 := uCnt_le_vCnt (ψ := ψ) ha hl0 k
    push_cast
    rw [hc]
    push_cast [Nat.cast_sub h1]
    have hD := Zf_defect ha hψ0 hψ1 hl0 hl1.le k
    obtain ⟨u0a, u0b⟩ := uCnt_bounds a ψ k
    obtain ⟨u1a, u1b⟩ := uCnt_bounds a ψ (k + 1)
    obtain ⟨va, vb⟩ := vCnt_bounds (ψ := ψ) ha (k + l)
    have m1 := mul_le_mul_of_nonneg_left u0a (by linarith : (0:ℝ) ≤ 1 - l)
    have m2 := mul_le_mul_of_nonneg_left u0b (by linarith : (0:ℝ) ≤ 1 - l)
    have m3 := mul_le_mul_of_nonneg_left u1a hl0
    have m4 := mul_le_mul_of_nonneg_left u1b hl0
    rw [abs_le] at ih hD ⊢
    constructor <;> linarith

/-- The counting estimate `|#{n < N : fract(a√n+ψ) ≤ l} - lN| ≤ C₁√N + C₂`. -/
lemma count_fractSet_bound (ha : 0 < a) (hψ0 : 0 ≤ ψ) (hψ1 : ψ < 1) (hl0 : 0 ≤ l) (hl1 : l < 1)
    (N : ℕ) :
    |(Nat.count (· ∈ fractSet a ψ l) N : ℝ) - l * N| ≤
      (a * (1 + 3 / a ^ 2)) * √N + (2 * (1 + 3 / a ^ 2) + 1) := by
  set k := ⌊tseq a ψ N⌋₊ with hk
  have ht0 : 0 ≤ tseq a ψ N := le_trans hψ0 (tseq_ge ha N)
  have hN1 : uCnt a ψ k ≤ N := by
    by_contra hc; push Not at hc
    have := (lt_uCnt_iff ha _ _).1 hc
    linarith [Nat.floor_le ht0]
  have hN2 : N < uCnt a ψ ((k : ℝ) + 1) := (lt_uCnt_iff ha _ _).2 (Nat.lt_floor_add_one _)
  have hkt : (k : ℝ) ≤ a * √N + 1 := by
    have h1 : (k:ℝ) ≤ tseq a ψ N := Nat.floor_le ht0
    have h2 : tseq a ψ N ≤ a * √N + 1 := by unfold tseq; linarith
    linarith
  have c1 : (Nat.count (· ∈ fractSet a ψ l) (uCnt a ψ k) : ℝ) ≤ Nat.count (· ∈ fractSet a ψ l) N := by
    exact_mod_cast Nat.count_monotone _ hN1
  have c2 : (Nat.count (· ∈ fractSet a ψ l) N : ℝ) ≤
      Nat.count (· ∈ fractSet a ψ l) (uCnt a ψ ((k : ℝ) + 1)) := by
    exact_mod_cast Nat.count_monotone _ hN2.le
  have e0 := count_block_error ha hψ0 hψ1 hl0 hl1 k
  have e1 := count_block_error ha hψ0 hψ1 hl0 hl1 (k + 1)
  push_cast at e1
  have hU0 : (uCnt a ψ k : ℝ) ≤ N := by exact_mod_cast hN1
  have hU1 : (N : ℝ) ≤ uCnt a ψ ((k : ℝ) + 1) := by exact_mod_cast hN2.le
  have hstep := Zf_step ha hψ0 k
  obtain ⟨u0a, u0b⟩ := uCnt_bounds a ψ k
  obtain ⟨u1a, u1b⟩ := uCnt_bounds a ψ (k + 1)
  have hgap : (uCnt a ψ ((k : ℝ) + 1) : ℝ) - uCnt a ψ k ≤ (2 * k + 2) / a ^ 2 + 1 := by linarith
  have m1 := mul_le_mul_of_nonneg_left hU0 hl0
  have m2 := mul_le_mul_of_nonneg_left hU1 hl0
  have m3 : l * ((uCnt a ψ ((k : ℝ) + 1) : ℝ) - uCnt a ψ k) ≤ (uCnt a ψ ((k : ℝ) + 1) : ℝ) - uCnt a ψ k :=
    mul_le_of_le_one_left (by linarith) hl1.le
  have hB : (1 + 1 / a ^ 2) * (k + 1) + ((2 * k + 2) / a ^ 2 + 1) ≤
      (a * (1 + 3 / a ^ 2)) * √N + (2 * (1 + 3 / a ^ 2) + 1) := by
    have : (1 + 1 / a ^ 2) * (k + 1) + ((2 * k + 2) / a ^ 2 + 1) = (1 + 3 / a ^ 2) * (k + 1) + 1 := by
      ring
    rw [this]
    have hpos : 0 ≤ 1 + 3 / a ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_left hkt hpos
    nlinarith
  have hB0 : 0 ≤ 1 / a ^ 2 := by positivity
  rw [abs_le] at e0 e1 ⊢
  constructor <;> linarith

/-- **Equidistribution of `a√n` modulo one along a window.** For `a > 0`, any phase `ψ` and
`0 ≤ l < 1`, the set `{n : fract(a√n + ψ) ≤ l}` has natural density `l`. -/
theorem hasNatDensity_fract_sqrt (ha : 0 < a) (ψ : ℝ) (hl0 : 0 ≤ l) (hl1 : l < 1) :
    HasNatDensity {n : ℕ | Int.fract (a * √(n : ℝ) + ψ) ≤ l} l := by
  have hset : {n : ℕ | Int.fract (a * √(n : ℝ) + ψ) ≤ l} = fractSet a (Int.fract ψ) l := by
    ext n
    simp only [fractSet, tseq, Set.mem_ofPred_eq]
    have : a * √(n:ℝ) + Int.fract ψ = (a * √(n:ℝ) + ψ) - ⌊ψ⌋ := by rw [Int.fract]; ring
    rw [this, Int.fract_sub_intCast]
  rw [hset]
  exact hasNatDensity_of_count_bound _ l _ _
    (count_fractSet_bound ha (Int.fract_nonneg ψ) (Int.fract_lt_one ψ) hl0 hl1)

end SqrtDensity

section Cosine

open Classical

lemma abs_cos_add_int_mul_pi (x : ℝ) (m : ℤ) : |cos (x + m * π)| = |cos x| := by
  rw [Real.cos_add_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul]

/-- `|cos u| ≥ c` iff `u + arccos c` lies within `2 arccos c` of `πℤ` from above, i.e.
`fract((u + β)/π) ≤ 2β/π` with `β = arccos c`. -/
lemma le_abs_cos_iff {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (u : ℝ) :
    c ≤ |cos u| ↔ Int.fract ((u + arccos c) / π) ≤ 2 * arccos c / π := by
  set β := arccos c with hβdef
  have hβ0 : 0 ≤ β := arccos_nonneg c
  have hβπ : β ≤ π / 2 := arccos_le_pi_div_two.2 hc0
  have hcβ : cos β = c := cos_arccos (by linarith) hc1
  have hpi := pi_pos
  set m := ⌊(u + β) / π⌋
  set f := Int.fract ((u + β) / π) with hfdef
  have hf0 : 0 ≤ f := Int.fract_nonneg _
  have hf1 : f < 1 := Int.fract_lt_one _
  have hf : π * f = u + β - m * π := by
    rw [hfdef, Int.fract]; field_simp; ring
  have hcos : |cos u| = |cos (π * f - β)| := by
    have : cos u = cos ((π * f - β) + m * π) := by congr 1; linarith
    rw [this, abs_cos_add_int_mul_pi]
  rw [hcos, le_div_iff₀ hpi]
  set w := π * f - β with hw
  have hwl : -β ≤ w := by nlinarith
  have hwu : w < π - β := by nlinarith
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    have hβw : β < w := by nlinarith
    have h1 : cos w < cos β := cos_lt_cos_of_nonneg_of_le_pi hβ0 (by linarith) hβw
    have h2 : cos (π - w) < cos β := cos_lt_cos_of_nonneg_of_le_pi hβ0 (by linarith) (by linarith)
    rw [cos_pi_sub] at h2
    have : |cos w| < c := by rw [abs_lt]; constructor <;> linarith
    linarith
  · intro h
    have hw' : |w| ≤ β := abs_le.2 ⟨by linarith, by nlinarith⟩
    have := cos_le_cos_of_nonneg_of_le_pi (abs_nonneg w) (by linarith) hw'
    rw [cos_abs] at this
    linarith [le_abs_self (cos w)]

end Cosine

section GoodIndices

open Classical

/-- The good indices of (hi-eq:good-index) at threshold `c` (paper: `c = Kε`):
`{n : |cos(2√(ns) - π/4)| ≥ c}`. -/
def goodIndexSet (s c : ℝ) : Set ℕ := {n | c ≤ |cos (2 * √((n : ℝ) * s) - π / 4)|}

lemma hasNatDensity_univ : HasNatDensity Set.univ 1 :=
  hasNatDensity_of_count_bound _ 1 0 0 fun N => by
    simp [Nat.count_eq_card_filter_range]

/-- **Density of good indices** (Theorem `thm:high-energy-spectrum`, density statement;
proof in §5 "Normalization and density of good indices", eq. (hi-eq:density)).
For `s > 0` and `0 ≤ c ≤ 1`, the set `{n : |cos(2√(ns) - π/4)| ≥ c}` has natural density
`1 - (2/π) arcsin c`. -/
theorem hasNatDensity_goodIndexSet {s c : ℝ} (hs : 0 < s) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    HasNatDensity (goodIndexSet s c) (1 - 2 / π * arcsin c) := by
  rcases eq_or_lt_of_le hc0 with rfl | hcpos
  · have : goodIndexSet s 0 = Set.univ := Set.eq_univ_of_forall fun n => show (0:ℝ) ≤ _ from abs_nonneg _
    rw [this, arcsin_zero, mul_zero, sub_zero]
    exact hasNatDensity_univ
  have hpi := pi_pos
  set β := arccos c with hβdef
  have hβ0 : 0 ≤ β := arccos_nonneg c
  have hβπ : β < π / 2 := arccos_lt_pi_div_two.2 hcpos
  have hset : goodIndexSet s c =
      {n : ℕ | Int.fract (2 * √s / π * √(n : ℝ) + (β - π / 4) / π) ≤ 2 * β / π} := by
    ext n
    simp only [goodIndexSet, Set.mem_ofPred_eq]
    rw [le_abs_cos_iff hc0 hc1, ← hβdef, Real.sqrt_mul (Nat.cast_nonneg n)]
    have e : (2 * (√(n:ℝ) * √s) - π / 4 + β) / π = 2 * √s / π * √(n:ℝ) + (β - π / 4) / π := by
      ring
    rw [e]
  have hdens : 1 - 2 / π * arcsin c = 2 * β / π := by
    rw [hβdef, arccos_eq_pi_div_two_sub_arcsin]; field_simp
  rw [hset, hdens]
  exact hasNatDensity_fract_sqrt (div_pos (mul_pos two_pos (Real.sqrt_pos.2 hs)) hpi) _
    (div_nonneg (by linarith) hpi.le)
    (by rw [div_lt_one hpi]; linarith)

/-- The density-one set `𝒢₀ = {n ≥ 1 : |cos(2√(ns) - π/4)| ≥ n^{-1/8}}` of
Theorem `thm:high-energy-spectrum` (case `W = 0`). -/
def G0 (s : ℝ) : Set ℕ :=
  {n | 1 ≤ n ∧ (n : ℝ) ^ (-(1 / 8 : ℝ)) ≤ |cos (2 * √((n : ℝ) * s) - π / 4)|}

/-- **`𝒢₀` has density one** (Theorem `thm:high-energy-spectrum`, last paragraph of §5). -/
theorem hasNatDensity_G0 {s : ℝ} (hs : 0 < s) : HasNatDensity (G0 s) 1 := by
  rw [HasNatDensity, tendsto_order]
  constructor
  · intro b hb
    set ε := 1 - b with hε
    have hεpos : 0 < ε := by linarith
    have hpi := pi_gt_three
    set δ := min (π * ε / 8) 1 with hδ
    have hδpos : 0 < δ := lt_min (div_pos (mul_pos pi_pos hεpos) (by norm_num)) one_pos
    have hδ1 : δ ≤ 1 := min_le_right _ _
    have hδε : δ ≤ π * ε / 8 := min_le_left _ _
    set c := sin δ
    have hcpos : 0 < c := sin_pos_of_pos_of_lt_pi hδpos (by linarith)
    have hc1 : c ≤ 1 := sin_le_one δ
    have harc : arcsin c = δ := arcsin_sin (by linarith) (by linarith)
    have hD := hasNatDensity_goodIndexSet hs hcpos.le hc1
    rw [harc] at hD
    have hlim : 1 - ε / 2 < 1 - 2 / π * δ := by
      have : 2 / π * δ ≤ ε / 4 := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
      linarith
    have ev1 := (tendsto_order.1 hD).1 _ hlim
    -- threshold beyond which `n^{-1/8} ≤ c`
    have hrp : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 8 : ℝ))) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop
    obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 ((tendsto_order.1 hrp).2 c hcpos)
    have ev2 := (tendsto_order.1 (tendsto_const_div_atTop_nhds_zero_nat (n₀ : ℝ))).2 (ε / 2)
      (by linarith)
    filter_upwards [ev1, ev2, eventually_ge_atTop 1] with N h1 h2 hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hsub : (Finset.Icc 1 N).filter (· ∈ goodIndexSet s c) ⊆
        (Finset.Icc 1 N).filter (· ∈ G0 s) ∪ Finset.range n₀ := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_range] at hn ⊢
      by_cases h : n < n₀
      · exact Or.inr h
      · push Not at h
        refine Or.inl ⟨hn.1, hn.1.1, ?_⟩
        exact (hn₀ n h).le.trans hn.2
    have hcard := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    rw [Finset.card_range] at hcard
    have hcard' : ((((Finset.Icc 1 N).filter (· ∈ goodIndexSet s c)).card : ℕ) : ℝ) / N ≤
        ((((Finset.Icc 1 N).filter (· ∈ G0 s)).card : ℕ) : ℝ) / N + n₀ / N := by
      rw [← add_div]
      exact div_le_div_of_nonneg_right (by exact_mod_cast hcard) hNpos.le
    linarith
  · intro b hb
    refine Eventually.of_forall fun N => lt_of_le_of_lt ?_ hb
    refine div_le_one_of_le₀ ?_ (Nat.cast_nonneg _)
    have := Finset.card_filter_le (Finset.Icc 1 N) (· ∈ G0 s)
    rw [Nat.card_Icc] at this
    exact_mod_cast this.trans (by omega)

end GoodIndices

section Parameters

/-- The Laguerre polynomial of degree `n` and parameter zero,
`L_n(x) = ∑_{k=0}^n (n choose k) (-x)^k / k!`. -/
def laguerre (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (-x) ^ k / (k.factorial : ℝ)

@[simp] lemma laguerre_zero (x : ℝ) : laguerre 0 x = 1 := by simp [laguerre]

lemma laguerre_one (x : ℝ) : laguerre 1 x = 1 - x := by
  simp [laguerre, Finset.sum_range_succ]; try ring

/-- The Landau form factor `f_n = e^{-s/2} L_n(s)` of (hi-eq:parameters). -/
def landauFormFactor (n : ℕ) (s : ℝ) : ℝ := Real.exp (-s / 2) * laguerre n s

/-- Reciprocal flux `α_B = 2πh/B` (hi-eq:parameters). -/
def alphaB (h B : ℝ) : ℝ := 2 * π * h / B

/-- Laguerre argument `s_B = 2π²h/B` (hi-eq:parameters). -/
def sB (h B : ℝ) : ℝ := 2 * π ^ 2 * h / B

/-- Landau level `E_n = (2n+1)hB + V̄` (hi-eq:parameters). -/
def landauLevel (h B Vbar : ℝ) (n : ℕ) : ℝ := (2 * n + 1) * h * B + Vbar

lemma sB_eq_pi_mul_alphaB (h B : ℝ) : sB h B = π * alphaB h B := by
  unfold sB alphaB; ring

lemma sB_pos {h B : ℝ} (hh : 0 < h) (hB : 0 < B) : 0 < sB h B := by
  unfold sB; exact div_pos (mul_pos (mul_pos two_pos (pow_pos pi_pos 2)) hh) hB

/-- The density statement of Theorem `thm:high-energy-spectrum` in the paper's parameters:
for `h, B > 0` and `0 ≤ Kε ≤ 1`, the good indices (hi-eq:good-index) have natural density
`1 - (2/π) arcsin(Kε)`. -/
theorem goodIndex_density {h B Kε : ℝ} (hh : 0 < h) (hB : 0 < B) (h0 : 0 ≤ Kε) (h1 : Kε ≤ 1) :
    HasNatDensity {n | Kε ≤ |cos (2 * √((n : ℝ) * sB h B) - π / 4)|} (1 - 2 / π * arcsin Kε) :=
  hasNatDensity_goodIndexSet (sB_pos hh hB) h0 h1

/-- For `W = 0`, the set `𝒢₀` (with `s = s_B`) has natural density one. -/
theorem G0_density {h B : ℝ} (hh : 0 < h) (hB : 0 < B) : HasNatDensity (G0 (sB h B)) 1 :=
  hasNatDensity_G0 (sB_pos hh hB)

end Parameters

end CMS
