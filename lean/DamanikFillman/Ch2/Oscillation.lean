/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §2.3  Oscillation theory  (book pp. 156–159)

For real energies `E` we work with the real polynomials `DF.Qpoly V k` (`Q_k(E) = u₁(k, E)`,
the Dirichlet solution; `Q_{n+1}(E) = det(E - H_n)` by (2.2.18)).

## Main results
* `DF.u₁_eq_Qpoly` — `u₁(k, E) = Q_k(E)`.
* `DF.Qpoly_wronskian` — the identity `Q_{k+1}' Q_k - Q_k' Q_{k+1} = ∑_{i ≤ k} Q_i²`
  (a Christoffel–Darboux-type identity; used instead of the function `h` of (2.3.6)).
* `DF.exists_root_between` — between two zeros of `Q_{k+1}` there is a zero of `Q_k`.
* **Lemma 2.3.2 (interlacing)**: `DF.interlacing` — between any two eigenvalues of `H_N` lies an
  eigenvalue of `H_{N-1}` — and its counting form `DF.interlacing_count`:
  `#(σ(H_{N-1}) ∩ (E,∞)) ≤ #(σ(H_N) ∩ (E,∞)) ≤ #(σ(H_{N-1}) ∩ (E,∞)) + 1`.
* **Theorem 2.3.1 (oscillation theorem)**: `DF.oscillation` —
  `#(σ(H_N) ∩ (E, ∞)) = F_N(E)` with `F_N` from (2.3.2)–(2.3.3) (`DF.oscCount`).
-/
import DamanikFillman.Ch2.Truncation

noncomputable section

open Polynomial Filter Topology
open scoped Matrix

namespace DF

variable {V : ℤ → ℝ}

/-- The real polynomials `Q_0 = 0`, `Q_1 = 1`, `Q_{k+2} = (X - V(k+1)) Q_{k+1} - Q_k`. -/
def Qpoly (V : ℤ → ℝ) : ℕ → ℝ[X]
  | 0 => 0
  | 1 => 1
  | k + 2 => (X - C (V (k + 1))) * Qpoly V (k + 1) - Qpoly V k

@[simp] lemma Qpoly_zero : Qpoly V 0 = 0 := rfl
@[simp] lemma Qpoly_one : Qpoly V 1 = 1 := rfl
lemma Qpoly_succ_succ (k : ℕ) :
    Qpoly V (k + 2) = (X - C (V (k + 1))) * Qpoly V (k + 1) - Qpoly V k := rfl

/-- `u₁(k, E) = Q_k(E)` for real `E`. -/
theorem u₁_eq_Qpoly (V : ℤ → ℝ) (E : ℝ) (k : ℕ) : u₁ V (E : ℂ) k = (((Qpoly V k).eval E : ℝ) : ℂ) := by
  have hs : IsSolution V (E : ℂ) (u₁ V E) := isSolution_solFrom _ _ _ _
  have key : ∀ k : ℕ, u₁ V (E : ℂ) k = (((Qpoly V k).eval E : ℝ) : ℂ) ∧
      u₁ V (E : ℂ) (k + 1) = (((Qpoly V (k + 1)).eval E : ℝ) : ℂ) := by
    intro k
    induction k with
    | zero => simp [u₁]
    | succ k ih =>
      refine ⟨by exact_mod_cast ih.2, ?_⟩
      have h := hs ((k : ℤ) + 1)
      simp only [add_sub_cancel_right] at h
      rw [Qpoly_succ_succ]
      simp only [eval_sub, eval_mul, eval_X, eval_C]
      push_cast at h ⊢
      rw [show (k : ℤ) + 1 + 1 = (k : ℤ) + 2 by ring] at h
      rw [ih.1, ih.2] at h
      rw [show (k : ℤ) + 1 + 1 = (k : ℤ) + 2 by ring]
      linear_combination h
  exact (key k).1

/-- The Wronskian identity `Q_{k+1}' Q_k - Q_k' Q_{k+1} = ∑_{i ≤ k} Q_i²`. -/
theorem Qpoly_wronskian (V : ℤ → ℝ) (k : ℕ) :
    derivative (Qpoly V (k + 1)) * Qpoly V k - derivative (Qpoly V k) * Qpoly V (k + 1) =
      ∑ i ∈ Finset.range (k + 1), Qpoly V i ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ← ih, Qpoly_succ_succ]
    simp only [derivative_sub, derivative_mul, derivative_X, derivative_C, sub_zero]
    ring

lemma wronskian_eval_pos (V : ℤ → ℝ) {k : ℕ} (hk : 1 ≤ k) (x : ℝ) :
    0 < (derivative (Qpoly V (k + 1))).eval x * (Qpoly V k).eval x -
      (derivative (Qpoly V k)).eval x * (Qpoly V (k + 1)).eval x := by
  have h := congrArg (eval x) (Qpoly_wronskian V k)
  simp only [eval_sub, eval_mul, eval_finset_sum, eval_pow] at h
  rw [h]
  have h1 : (1 : ℝ) ≤ ∑ i ∈ Finset.range (k + 1), (Qpoly V i).eval x ^ 2 := by
    have := Finset.single_le_sum (f := fun i => (Qpoly V i).eval x ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_range.mpr (show 1 < k + 1 by omega))
    simpa using this
  linarith

lemma Qpoly_ne_zero (V : ℤ → ℝ) (k : ℕ) : Qpoly V (k + 1) ≠ 0 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · intro h
    have := wronskian_eval_pos V hk 0
    rw [h] at this; simp at this

/-- `Q_k` and `Q_{k+1}` have no common zeros. -/
lemma no_common_root (V : ℤ → ℝ) {k : ℕ} (hk : 1 ≤ k) {x : ℝ}
    (h1 : (Qpoly V (k + 1)).eval x = 0) (h2 : (Qpoly V k).eval x = 0) : False := by
  have := wronskian_eval_pos V hk x
  rw [h1, h2] at this; simp at this

/-- A continuous function without zeros on `(a, c)` has constant sign there. -/
lemma const_sign {f : ℝ → ℝ} (hf : Continuous f) {a c m : ℝ} (hm : m ∈ Set.Ioo a c)
    (hne : ∀ t ∈ Set.Ioo a c, f t ≠ 0) (hpos : 0 < f m) : ∀ t ∈ Set.Ioo a c, 0 < f t := by
  intro t ht
  by_contra hle
  push Not at hle
  rcases le_total m t with hmt | hmt
  · obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc' hmt hf.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (f t) (f m) from ⟨hle, hpos.le⟩)
    exact hne s ⟨lt_of_lt_of_le hm.1 hs.1, lt_of_le_of_lt hs.2 ht.2⟩ hs0
  · obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc hmt hf.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (f t) (f m) from ⟨hle, hpos.le⟩)
    exact hne s ⟨lt_of_lt_of_le ht.1 hs.1, lt_of_le_of_lt hs.2 hm.2⟩ hs0

/-- If `p(a) = 0` and `p > 0` on `(a, c)`, then `p'(a) ≥ 0`. -/
lemma deriv_nonneg_left (p : ℝ[X]) {a c : ℝ} (hac : a < c) (h0 : p.eval a = 0)
    (hpos : ∀ t ∈ Set.Ioo a c, 0 < p.eval t) : 0 ≤ (derivative p).eval a := by
  have h := (p.hasDerivAt a).tendsto_slope_zero_right
  refine ge_of_tendsto h ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < c - a by linarith)] with t ht
  rw [h0, sub_zero, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr ht.1.le) (hpos _ ⟨by linarith [ht.1], by linarith [ht.2]⟩).le

/-- If `p(c) = 0` and `p > 0` on `(a, c)`, then `p'(c) ≤ 0`. -/
lemma deriv_nonpos_right (p : ℝ[X]) {a c : ℝ} (hac : a < c) (h0 : p.eval c = 0)
    (hpos : ∀ t ∈ Set.Ioo a c, 0 < p.eval t) : (derivative p).eval c ≤ 0 := by
  have h := (p.hasDerivAt c).tendsto_slope_zero_left
  refine le_of_tendsto h ?_
  filter_upwards [Ioo_mem_nhdsLT (show a - c < (0 : ℝ) by linarith)] with t ht
  rw [h0, sub_zero, smul_eq_mul]
  exact mul_nonpos_of_nonpos_of_nonneg (inv_nonpos.mpr ht.2.le)
    (hpos _ ⟨by linarith [ht.1], by linarith [ht.2]⟩).le

/-- Between two consecutive zeros of `Q_{k+1}` there is a zero of `Q_k`. -/
lemma exists_root_between_consec {k : ℕ} (hk : 1 ≤ k) {a c : ℝ} (hac : a < c)
    (ha : (Qpoly V (k + 1)).eval a = 0) (hc : (Qpoly V (k + 1)).eval c = 0)
    (hno : ∀ t ∈ Set.Ioo a c, (Qpoly V (k + 1)).eval t ≠ 0) :
    ∃ s ∈ Set.Ioo a c, (Qpoly V k).eval s = 0 := by
  set p := Qpoly V (k + 1)
  set q := Qpoly V k
  have hWa := wronskian_eval_pos V hk a
  have hWc := wronskian_eval_pos V hk c
  rw [ha, mul_zero, sub_zero] at hWa
  rw [hc, mul_zero, sub_zero] at hWc
  have hm : (a + c) / 2 ∈ Set.Ioo a c := ⟨by linarith, by linarith⟩
  have hcont : Continuous fun t => q.eval t := q.continuous
  rcases lt_or_gt_of_ne (hno _ hm) with hneg | hpos
  · -- `p < 0` on `(a, c)`
    have hneg' : ∀ t ∈ Set.Ioo a c, 0 < (-p).eval t := by
      have := const_sign (f := fun t => (-p).eval t) (-p).continuous hm
        (fun t ht => by simpa using hno t ht) (by simpa using hneg)
      exact this
    have d1 := deriv_nonneg_left (-p) hac (by simp [ha]) hneg'
    have d2 := deriv_nonpos_right (-p) hac (by simp [hc]) hneg'
    simp only [derivative_neg, eval_neg] at d1 d2
    have hqa : q.eval a < 0 := by
      by_contra h; push Not at h; nlinarith
    have hqc : 0 < q.eval c := by
      by_contra h; push Not at h; nlinarith
    obtain ⟨s, hs, hs0⟩ := intermediate_value_Ioo hac.le hcont.continuousOn
      (show (0 : ℝ) ∈ Set.Ioo (q.eval a) (q.eval c) from ⟨hqa, hqc⟩)
    exact ⟨s, hs, hs0⟩
  · have hpos' := const_sign (f := fun t => p.eval t) p.continuous hm hno hpos
    have d1 := deriv_nonneg_left p hac ha hpos'
    have d2 := deriv_nonpos_right p hac hc hpos'
    have hqa : 0 < q.eval a := by
      by_contra h; push Not at h; nlinarith
    have hqc : q.eval c < 0 := by
      by_contra h; push Not at h; nlinarith
    obtain ⟨s, hs, hs0⟩ := intermediate_value_Ioo' hac.le hcont.continuousOn
      (show (0 : ℝ) ∈ Set.Ioo (q.eval c) (q.eval a) from ⟨hqc, hqa⟩)
    exact ⟨s, hs, hs0⟩

/-- Between any two zeros of `Q_{k+1}` there is a zero of `Q_k`. -/
theorem exists_root_between {k : ℕ} (hk : 1 ≤ k) {a b : ℝ} (hab : a < b)
    (ha : (Qpoly V (k + 1)).eval a = 0) (hb : (Qpoly V (k + 1)).eval b = 0) :
    ∃ s ∈ Set.Ioo a b, (Qpoly V k).eval s = 0 := by
  classical
  have hne := Qpoly_ne_zero V k
  set S := (Qpoly V (k + 1)).roots.toFinset.filter (fun r => a < r ∧ r ≤ b)
  have hbS : b ∈ S := by
    simp only [S, Finset.mem_filter, Multiset.mem_toFinset, mem_roots hne, IsRoot.def]
    exact ⟨hb, hab, le_rfl⟩
  set c := S.min' ⟨b, hbS⟩
  have hcS := S.min'_mem ⟨b, hbS⟩
  simp only [S, Finset.mem_filter, Multiset.mem_toFinset, mem_roots hne, IsRoot.def] at hcS
  obtain ⟨s, hs, hs0⟩ := exists_root_between_consec hk hcS.2.1 ha hcS.1 (by
    intro t ht h0
    have htS : t ∈ S := by
      simp only [S, Finset.mem_filter, Multiset.mem_toFinset, mem_roots hne, IsRoot.def]
      exact ⟨h0, ht.1, le_trans ht.2.le hcS.2.2⟩
    exact absurd (S.min'_le t htS) (not_le.mpr ht.2))
  exact ⟨s, ⟨hs.1, lt_of_lt_of_le hs.2 hcS.2.2⟩, hs0⟩

/-! ### Spectral structure of `H_N` -/

lemma truncMat_isHermitian (V : ℤ → ℝ) (a : ℤ) (N : ℕ) : (truncMat V a N).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, truncMat_apply]
  by_cases h : j = i
  · subst h; simp
  · rw [if_neg h, if_neg (Ne.symm h)]
    by_cases hadj : (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j
    · rw [if_pos hadj, if_pos (hadj.symm)]; simp
    · rw [if_neg hadj, if_neg (fun h' => hadj h'.symm)]; simp

/-- The eigenvalues of `H_N` (Mathlib's spectral theorem). -/
def eigH (V : ℤ → ℝ) (N : ℕ) : Fin N → ℝ := (truncMat_isHermitian V 0 N).eigenvalues

/-- `Q_{N+1}(x) = ∏ (x - Eⱼ)` over the eigenvalues of `H_N`. -/
theorem Qpoly_eq_prod (V : ℤ → ℝ) (N : ℕ) (x : ℝ) :
    (Qpoly V (N + 1)).eval x = ∏ i, (x - eigH V N i) := by
  have hH := truncMat_isHermitian V 0 N
  have h1 := u₁_eq_Qpoly V x (N + 1)
  have h2 := det_truncMat V (x : ℂ) N
  have h3 : ((x : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - truncMat V 0 N).det =
      ∏ i, ((x : ℂ) - (eigH V N i : ℂ)) := by
    have := Matrix.eval_charpoly (truncMat V 0 N) (x : ℂ)
    rw [hH.charpoly_eq] at this
    simp only [eval_prod, eval_sub, eval_X, eval_C] at this
    rw [show (x : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) = Matrix.scalar (Fin N) (x : ℂ) by
      rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal], ← this]
    rfl
  push_cast at h1
  rw [h2, h1] at h3
  exact_mod_cast h3

/-- The eigenvalues of `H_N` are simple (Proposition 2.2.5), i.e. `eigH` is injective. -/
theorem eigH_injective (V : ℤ → ℝ) (N : ℕ) : Function.Injective (eigH V N) := by
  intro i j hij
  by_contra hne
  have hH := truncMat_isHermitian V 0 N
  set B := hH.eigenvectorBasis
  have hi := hH.mulVec_eigenvectorBasis i
  have hj := hH.mulVec_eigenvectorBasis j
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)] at hi hj
  have hij2 : hH.eigenvalues j = hH.eigenvalues i := hij.symm
  rw [hij2] at hj
  obtain ⟨c, d, hcd, h⟩ := truncMat_eigen_simple hi hj
  have hli : LinearIndependent ℂ ![B i, B j] := by
    have h0 := B.orthonormal.linearIndependent.comp ![i, j] (by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all [eq_comm])
    convert h0 using 1
    ext k; fin_cases k <;> rfl
  have heq : c • B i + d • B j = 0 := by
    apply WithLp.ofLp_injective
    simpa using h
  have := LinearIndependent.pair_iff.mp hli c d heq
  rcases hcd with h' | h' <;> simp_all

/-- Real eigenvalues of `H_N` (the book's `σ(H_N)`). -/
def truncSpec (V : ℤ → ℝ) (N : ℕ) : Set ℝ :=
  {x : ℝ | ∃ v : Fin N → ℂ, v ≠ 0 ∧ truncMat V 0 N *ᵥ v = (x : ℂ) • v}

theorem mem_truncSpec_iff (V : ℤ → ℝ) (N : ℕ) (x : ℝ) :
    x ∈ truncSpec V N ↔ (Qpoly V (N + 1)).eval x = 0 := by
  have h1 := u₁_eq_Qpoly V x (N + 1)
  have h2 := det_truncMat V (x : ℂ) N
  push_cast at h1
  rw [h1] at h2
  constructor
  · rintro ⟨v, hv, hmv⟩
    have : ((x : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - truncMat V 0 N) *ᵥ v = 0 := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hmv, sub_self]
    have hd := Matrix.exists_mulVec_eq_zero_iff.mp ⟨v, hv, this⟩
    rw [hd] at h2; exact_mod_cast h2.symm
  · intro h
    have hd : ((x : ℂ) • (1 : Matrix (Fin N) (Fin N) ℂ) - truncMat V 0 N).det = 0 := by
      rw [h2, h, Complex.ofReal_zero]
    obtain ⟨v, hv, hmv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hmv
    exact hmv.symm

/-- The zeros of `Q_k` above `E`, as a finset. -/
def rootsAbove (V : ℤ → ℝ) (k : ℕ) (E : ℝ) : Finset ℝ :=
  (Qpoly V k).roots.toFinset.filter (fun x => E < x)

/-- `Z_k(E)`: the number of zeros of `Q_k` above `E`. -/
def Zc (V : ℤ → ℝ) (k : ℕ) (E : ℝ) : ℕ := (rootsAbove V k E).card

lemma mem_rootsAbove (V : ℤ → ℝ) (k : ℕ) (E x : ℝ) :
    x ∈ rootsAbove V (k + 1) E ↔ E < x ∧ (Qpoly V (k + 1)).eval x = 0 := by
  simp [rootsAbove, mem_roots (Qpoly_ne_zero V k), and_comm]

lemma roots_eq_image (V : ℤ → ℝ) (N : ℕ) :
    (Qpoly V (N + 1)).roots.toFinset = Finset.univ.image (eigH V N) := by
  ext x
  simp only [Multiset.mem_toFinset, mem_roots (Qpoly_ne_zero V N), IsRoot.def, Qpoly_eq_prod,
    Finset.prod_eq_zero_iff, Finset.mem_univ, true_and, sub_eq_zero, Finset.mem_image]
  exact ⟨fun ⟨i, h⟩ => ⟨i, h.symm⟩, fun ⟨i, h⟩ => ⟨i, h.symm⟩⟩

lemma Zc_eq_card (V : ℤ → ℝ) (N : ℕ) (E : ℝ) :
    Zc V (N + 1) E = (Finset.univ.filter (fun i => E < eigH V N i)).card := by
  rw [Zc, rootsAbove, roots_eq_image, Finset.filter_image,
    Finset.card_image_of_injective _ (eigH_injective V N)]

lemma card_roots (V : ℤ → ℝ) (N : ℕ) : (Qpoly V (N + 1)).roots.toFinset.card = N := by
  rw [roots_eq_image, Finset.card_image_of_injective _ (eigH_injective V N)]; simp

/-- Sign of `Q_{N+1}(E) = det(E - H_N)`: `(-1)^{Z_{N+1}(E)} Q_{N+1}(E) > 0` if `E ∉ σ(H_N)`. -/
theorem sign_Qpoly (V : ℤ → ℝ) (N : ℕ) {E : ℝ} (hE : (Qpoly V (N + 1)).eval E ≠ 0) :
    0 < (-1 : ℝ) ^ Zc V (N + 1) E * (Qpoly V (N + 1)).eval E := by
  rw [Zc_eq_card, Qpoly_eq_prod]
  have hpow : (-1 : ℝ) ^ (Finset.univ.filter (fun i => E < eigH V N i)).card =
      ∏ i, (if E < eigH V N i then (-1 : ℝ) else 1) := by
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
  rw [hpow, ← Finset.prod_mul_distrib]
  refine Finset.prod_pos fun i _ => ?_
  have hne : E ≠ eigH V N i := by
    intro h; apply hE; rw [Qpoly_eq_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h, sub_self])
  split_ifs with h
  · linarith
  · have : eigH V N i < E := lt_of_le_of_ne (not_lt.mp h) (Ne.symm hne)
    linarith

/-! ### Interlacing: Lemma 2.3.2 -/

/-- Combinatorial lemma: if between any two points of `R` there is a point of `S`, then `S`
has at least `|R| - 1` points strictly between points of `R`. -/
lemma count_between (S R : Finset ℝ)
    (h : ∀ a ∈ R, ∀ b ∈ R, a < b → ∃ s ∈ S, a < s ∧ s < b) :
    R.card ≤ (S.filter (fun s => ∃ a ∈ R, ∃ b ∈ R, a < s ∧ s < b)).card + 1 := by
  classical
  induction R using Finset.induction_on_max with
  | empty => simp
  | insert a R hlt ih =>
    have ih' := ih (fun x hx y hy hxy =>
      h x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy)
    have haR : a ∉ R := fun ha => lt_irrefl a (hlt a ha)
    rw [Finset.card_insert_of_notMem haR]
    rcases R.eq_empty_or_nonempty with hR | hR
    · simp [hR]
    · have hm := R.max'_mem hR
      obtain ⟨s0, hs0, h1, h2⟩ := h (R.max' hR) (Finset.mem_insert_of_mem hm) a
        (Finset.mem_insert_self a R) (hlt _ hm)
      have hsub : insert s0 (S.filter (fun s => ∃ a ∈ R, ∃ b ∈ R, a < s ∧ s < b)) ⊆
          S.filter (fun s => ∃ a' ∈ insert a R, ∃ b ∈ insert a R, a' < s ∧ s < b) := by
        intro x hx
        rw [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · exact Finset.mem_filter.mpr ⟨hs0, _, Finset.mem_insert_of_mem hm, a,
            Finset.mem_insert_self a R, h1, h2⟩
        · obtain ⟨hxS, a', ha', b', hb', h3, h4⟩ := Finset.mem_filter.mp hx
          exact Finset.mem_filter.mpr ⟨hxS, a', Finset.mem_insert_of_mem ha', b',
            Finset.mem_insert_of_mem hb', h3, h4⟩
      have hnot : s0 ∉ S.filter (fun s => ∃ a ∈ R, ∃ b ∈ R, a < s ∧ s < b) := by
        intro hx
        obtain ⟨_, a', ha', b', hb', h3, h4⟩ := Finset.mem_filter.mp hx
        have := R.le_max' b' hb'
        linarith
      have := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hnot] at this
      omega

/-- **Lemma 2.3.2 (interlacing)**: between any two eigenvalues of `H_{N+1}` there is an
eigenvalue of `H_N`. -/
theorem interlacing (V : ℤ → ℝ) (N : ℕ) {a b : ℝ} (ha : a ∈ truncSpec V (N + 1))
    (hb : b ∈ truncSpec V (N + 1)) (hab : a < b) : ∃ s ∈ Set.Ioo a b, s ∈ truncSpec V N := by
  rw [mem_truncSpec_iff] at ha hb
  obtain ⟨s, hs, h0⟩ := exists_root_between (V := V) (k := N + 1) (by omega) hab ha hb
  exact ⟨s, hs, (mem_truncSpec_iff V N s).mpr h0⟩

/-- **Lemma 2.3.2**, counting form: `Z_N(E) ≤ Z_{N+1}(E) ≤ Z_N(E) + 1`, where `Z_N(E)` is the
number of eigenvalues of `H_N` above `E`. -/
theorem interlacing_count (V : ℤ → ℝ) (N : ℕ) (E : ℝ) :
    Zc V (N + 1) E ≤ Zc V (N + 2) E ∧ Zc V (N + 2) E ≤ Zc V (N + 1) E + 1 := by
  classical
  have hne1 := Qpoly_ne_zero V N
  have hne2 := Qpoly_ne_zero V (N + 1)
  constructor
  · have hc := count_between ((Qpoly V (N + 1)).roots.toFinset.filter (fun x => ¬ E < x))
      ((Qpoly V (N + 2)).roots.toFinset.filter (fun x => ¬ E < x)) (by
      intro x hx y hy hxy
      simp only [Finset.mem_filter, Multiset.mem_toFinset, mem_roots hne2, IsRoot.def] at hx hy
      obtain ⟨s, hs, h0⟩ := exists_root_between (V := V) (k := N + 1) (by omega) hxy hx.1 hy.1
      refine ⟨s, ?_, hs.1, hs.2⟩
      simp only [Finset.mem_filter, Multiset.mem_toFinset, mem_roots hne1, IsRoot.def]
      exact ⟨h0, fun h => hy.2 (lt_trans h hs.2)⟩)
    have hc' := hc.trans (Nat.add_le_add_right (Finset.card_filter_le _ _) 1)
    clear hc
    have t1 := Finset.card_filter_add_card_filter_not
      (s := (Qpoly V (N + 2)).roots.toFinset) (fun x => E < x)
    have t2 := Finset.card_filter_add_card_filter_not
      (s := (Qpoly V (N + 1)).roots.toFinset) (fun x => E < x)
    rw [card_roots V (N + 1)] at t1
    rw [card_roots V N] at t2
    simp only [Zc, rootsAbove]
    omega
  · set R := rootsAbove V (N + 2) E
    set S := rootsAbove V (N + 1) E
    have hc := count_between S R (by
      intro x hx y hy hxy
      rw [mem_rootsAbove] at hx hy
      obtain ⟨s, hs, h0⟩ := exists_root_between (V := V) (k := N + 1) (by omega) hxy hx.2 hy.2
      exact ⟨s, (mem_rootsAbove V N E s).mpr ⟨lt_trans hx.1 hs.1, h0⟩, hs.1, hs.2⟩)
    have hc2 := Finset.card_filter_le S (fun s => ∃ a ∈ R, ∃ b ∈ R, a < s ∧ s < b)
    show R.card ≤ S.card + 1
    omega

/-! ### Theorem 2.3.1 -/

/-- `sgn` with the convention `sgn(0) = 1`. -/
def sgnR (x : ℝ) : ℤ := if 0 ≤ x then 1 else -1

/-- `1` if `u₁(j, E)` and `u₁(j+1, E)` have different signs. -/
def flipQ (V : ℤ → ℝ) (E : ℝ) (j : ℕ) : ℕ :=
  if sgnR ((Qpoly V j).eval E) ≠ sgnR ((Qpoly V (j + 1)).eval E) then 1 else 0

/-- The number `F_N(E)` of sign flips of `u₁(·, E)` on `[1, N+1]`, (2.3.2)–(2.3.3). -/
def oscCount (V : ℤ → ℝ) (N : ℕ) (E : ℝ) : ℕ :=
  if (Qpoly V (N + 1)).eval E = 0 then ∑ j ∈ Finset.Ico 1 N, flipQ V E j
  else ∑ j ∈ Finset.Ico 1 (N + 1), flipQ V E j

lemma sgnR_eq (V : ℤ → ℝ) (N : ℕ) {E : ℝ} (hE : (Qpoly V (N + 1)).eval E ≠ 0) :
    sgnR ((Qpoly V (N + 1)).eval E) = if Even (Zc V (N + 1) E) then 1 else -1 := by
  have h := sign_Qpoly V N hE
  unfold sgnR
  rcases Nat.even_or_odd (Zc V (N + 1) E) with he | ho
  · rw [he.neg_one_pow, one_mul] at h
    rw [if_pos h.le, if_pos he]
  · rw [ho.neg_one_pow] at h
    rw [if_neg (by linarith), if_neg (Nat.not_even_iff_odd.mpr ho)]

lemma exists_gap (p : ℝ[X]) (hp : p ≠ 0) (E : ℝ) :
    ∃ δ > 0, ∀ x, E - δ < x → x < E → p.eval x ≠ 0 := by
  classical
  set F := p.roots.toFinset.filter (fun x => x < E)
  rcases F.eq_empty_or_nonempty with hF | hF
  · refine ⟨1, one_pos, fun x _ hx h0 => ?_⟩
    have : x ∈ F := by simp [F, mem_roots hp, h0, hx]
    rw [hF] at this; simp at this
  · have hm := F.max'_mem hF
    simp only [F, Finset.mem_filter] at hm
    refine ⟨E - F.max' hF, by linarith [hm.2], fun x hx1 hx2 h0 => ?_⟩
    have : x ∈ F := by simp [F, mem_roots hp, h0, hx2]
    have := F.le_max' x this
    linarith

lemma Zc_shift (V : ℤ → ℝ) (k : ℕ) {E δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ x, E - δ < x → x < E → (Qpoly V (k + 1)).eval x ≠ 0) :
    Zc V (k + 1) (E - δ) = Zc V (k + 1) E + if (Qpoly V (k + 1)).eval E = 0 then 1 else 0 := by
  classical
  split_ifs with h0
  · have : rootsAbove V (k + 1) (E - δ) = insert E (rootsAbove V (k + 1) E) := by
      ext x
      rw [Finset.mem_insert, mem_rootsAbove, mem_rootsAbove]
      constructor
      · rintro ⟨h1, h2⟩
        rcases lt_trichotomy x E with hx | rfl | hx
        · exact absurd h2 (hgap x h1 hx)
        · exact Or.inl rfl
        · exact Or.inr ⟨hx, h2⟩
      · rintro (rfl | ⟨h1, h2⟩)
        · exact ⟨by linarith, h0⟩
        · exact ⟨by linarith, h2⟩
    rw [Zc, this, Finset.card_insert_of_notMem (by rw [mem_rootsAbove]; simp)]
    rfl
  · have : rootsAbove V (k + 1) (E - δ) = rootsAbove V (k + 1) E := by
      ext x
      rw [mem_rootsAbove, mem_rootsAbove]
      constructor
      · rintro ⟨h1, h2⟩
        rcases lt_trichotomy x E with hx | rfl | hx
        · exact absurd h2 (hgap x h1 hx)
        · exact absurd h2 h0
        · exact ⟨hx, h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, h2⟩
    rw [Zc, this, add_zero]; rfl

/-- **Theorem 2.3.1 (oscillation theorem)**, in terms of `Z_{N+1}(E)`. -/
theorem Zc_eq_oscCount (V : ℤ → ℝ) (N : ℕ) (E : ℝ) : Zc V (N + 1) E = oscCount V N E := by
  induction N generalizing E with
  | zero =>
    simp [Zc, rootsAbove, oscCount]
  | succ N ih =>
    rw [show N + 1 + 1 = N + 2 by ring]
    have ihE := ih E
    set a := (Qpoly V (N + 1)).eval E
    set b := (Qpoly V (N + 2)).eval E
    have hnc : ¬ (b = 0 ∧ a = 0) := fun h =>
      no_common_root V (k := N + 1) (by omega) h.1 h.2
    -- the gap below `E`
    obtain ⟨δ, hδ, hgap⟩ := exists_gap (Qpoly V (N + 1) * Qpoly V (N + 2))
      (mul_ne_zero (Qpoly_ne_zero V N) (Qpoly_ne_zero V (N + 1))) E
    have g1 : ∀ x, E - δ < x → x < E → (Qpoly V (N + 1)).eval x ≠ 0 := fun x h1 h2 h0 =>
      hgap x h1 h2 (by simp [h0])
    have g2 : ∀ x, E - δ < x → x < E → (Qpoly V (N + 2)).eval x ≠ 0 := fun x h1 h2 h0 =>
      hgap x h1 h2 (by simp [h0])
    have s1 := Zc_shift V N hδ g1
    have s2 := Zc_shift V (N + 1) hδ g2
    rw [show N + 1 + 1 = N + 2 by ring] at s2
    have c0 := interlacing_count V N E
    have c1 := interlacing_count V N (E - δ)
    unfold oscCount
    by_cases hb : b = 0
    · have ha : a ≠ 0 := fun ha => hnc ⟨hb, ha⟩
      rw [if_pos hb]
      rw [if_pos hb] at s2
      rw [if_neg ha] at s1
      have : oscCount V N E = ∑ j ∈ Finset.Ico 1 (N + 1), flipQ V E j := by
        unfold oscCount; rw [if_neg ha]
      omega
    · rw [if_neg hb]
      rw [if_neg hb] at s2
      by_cases ha : a = 0
      · rw [if_pos ha] at s1
        have hN : 1 ≤ N := by
          rcases Nat.eq_zero_or_pos N with h | h
          · subst h; simp [a] at ha
          · exact h
        have hosc : oscCount V N E = ∑ j ∈ Finset.Ico 1 N, flipQ V E j := by
          unfold oscCount; rw [if_pos ha]
        have hQN : (Qpoly V N).eval E ≠ 0 := by
          intro h0
          obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
          exact no_common_root V (k := M + 1) (by omega) ha h0
        have hrec : b = -(Qpoly V N).eval E := by
          simp only [b]
          rw [Qpoly_succ_succ]
          simp only [eval_sub, eval_mul, eval_X, eval_C]
          rw [show (Qpoly V (N + 1)).eval E = a from rfl, ha]; ring
        have hA : (Qpoly V (N + 1)).eval E = 0 := ha
        have hB : (Qpoly V (N + 1 + 1)).eval E = -(Qpoly V N).eval E := hrec
        have hflip : flipQ V E N + flipQ V E (N + 1) = 1 := by
          rcases lt_or_gt_of_ne hQN with h | h
          · have h1 : ¬ (0 ≤ (Qpoly V N).eval E) := not_le.mpr h
            have h2 : 0 ≤ -(Qpoly V N).eval E := by linarith
            simp [flipQ, sgnR, hA, hB, h1, h2]
          · have h1 : 0 ≤ (Qpoly V N).eval E := h.le
            have h2 : ¬ (0 ≤ -(Qpoly V N).eval E) := by linarith
            simp [flipQ, sgnR, hA, hB, h1, h2]
        rw [Finset.sum_Ico_succ_top (by omega), Finset.sum_Ico_succ_top (by omega)]
        omega
      · rw [if_neg ha] at s1
        have hosc : oscCount V N E = ∑ j ∈ Finset.Ico 1 (N + 1), flipQ V E j := by
          unfold oscCount; rw [if_neg ha]
        have e1 := sgnR_eq V N ha
        have e2 := sgnR_eq V (N + 1) hb
        have hf : flipQ V E (N + 1) = if sgnR a ≠ sgnR b then 1 else 0 := rfl
        rw [show N + 1 + 1 = N + 2 by ring] at e2
        have hflip : flipQ V E (N + 1) = Zc V (N + 2) E - Zc V (N + 1) E := by
          rw [hf, e1, show sgnR b = _ from e2]
          rcases c0 with ⟨c0a, c0b⟩
          obtain ⟨d, hd⟩ := Nat.le.dest c0a
          have hd' : d = 0 ∨ d = 1 := by omega
          rcases hd' with rfl | rfl
          · rw [← hd, add_zero]; simp
          · rw [← hd]
            rcases Nat.even_or_odd (Zc V (N + 1) E) with he | ho
            · have hne : ¬ Even (Zc V (N + 1) E + 1) := by
                rw [Nat.even_add_one]; exact not_not.mpr he
              rw [if_pos he, if_neg hne]; simp
            · have hne : ¬ Even (Zc V (N + 1) E) := Nat.not_even_iff_odd.mpr ho
              have hev : Even (Zc V (N + 1) E + 1) := by
                rw [Nat.even_add_one]; exact hne
              rw [if_neg hne, if_pos hev]; simp
        rw [Finset.sum_Ico_succ_top (by omega)]
        omega

/-- **Theorem 2.3.1 (oscillation theorem)**: the number of eigenvalues of `H_N` exceeding `E`
equals the number `F_N(E)` of sign flips of the Dirichlet solution `u₁(·, E)`, (2.3.4). -/
theorem oscillation (V : ℤ → ℝ) (N : ℕ) (E : ℝ) :
    (truncSpec V N ∩ Set.Ioi E).ncard = oscCount V N E := by
  rw [← Zc_eq_oscCount, Zc, ← Set.ncard_coe_finset]
  congr 1
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Ioi, Finset.mem_coe, mem_rootsAbove, mem_truncSpec_iff]
  tauto

end DF
