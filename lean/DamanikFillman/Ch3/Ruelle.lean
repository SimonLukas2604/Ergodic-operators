/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §3.8.2: Ruelle's deterministic theorem (Theorem 3.8.7, book pp. 288–290)

Main result:
* `DF.Cocycle.ruelle` — **Theorem 3.8.7**: if `A_n ∈ SL(2, ℂ)` satisfy `(1/n) log ‖A_n‖ → 0` and
  `(1/n) log ‖A_n ⋯ A_1‖ → L > 0`, there is a one-dimensional subspace `V ⊆ ℂ²` such that
  `(1/n) log ‖A_n ⋯ A_1 v‖ → -L` for `0 ≠ v ∈ V` and `→ L` for `v ∉ V`. This proves
  `DF.Cocycle.RuelleStatement`.

The proof follows the book, with the following simplifications: instead of the exact most
contracted directions (singular value decomposition) we use unit vectors `uₙ` with
`‖Tₙ uₙ‖ ≤ 4/‖Tₙ‖` (obtained from `Tₙ⁻¹ = adj Tₙ`), and the angle between two lines is measured
by `|det[u, u']|`, which together with `uₙ^⊥ = (-ūₙ₁, ūₙ₀)` gives `‖Tₙ uₙ^⊥‖ ≥ 1/‖Tₙ uₙ‖`.
After aligning phases the unit vectors `uₙ` form a Cauchy sequence whose limit spans `V`.
The real case of the theorem (the last sentence of Theorem 3.8.7) is not formalized.
-/
import DamanikFillman.Ch3.Cocycle

noncomputable section

set_option linter.unusedSectionVars false

open Filter Set Function Topology Matrix
open scoped Matrix.Norms.L2Operator ComplexConjugate InnerProductSpace

namespace DF

namespace Cocycle

/-- `ℂ²` with the Euclidean norm. -/
abbrev C2 := EuclideanSpace ℂ (Fin 2)

/-! ### Two-dimensional linear algebra -/

/-- `det[x, y] = x₀ y₁ - x₁ y₀`. -/
def det2 (x y : C2) : ℂ := x 0 * y 1 - x 1 * y 0

/-- `x^⊥ = (-x̄₁, x̄₀)`. -/
def perp (x : C2) : C2 := WithLp.toLp 2 ![-(conj (x 1)), conj (x 0)]

@[simp] lemma perp_zero (x : C2) : perp x 0 = -(conj (x 1)) := rfl
@[simp] lemma perp_one (x : C2) : perp x 1 = conj (x 0) := rfl

lemma inner_perp (x y : C2) : ⟪perp x, y⟫_ℂ = det2 x y := by
  simp [PiLp.inner_apply, Fin.sum_univ_two, det2]; ring

lemma inner_self_perp (x : C2) : ⟪x, perp x⟫_ℂ = 0 := by
  simp [PiLp.inner_apply, Fin.sum_univ_two]; ring

lemma normsq_C2 (x : C2) : ‖x‖ ^ 2 = ‖x 0‖ ^ 2 + ‖x 1‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]

lemma norm_perp (x : C2) : ‖perp x‖ = ‖x‖ := by
  have h1 := normsq_C2 (perp x)
  have h2 := normsq_C2 x
  simp only [perp_zero, perp_one, norm_neg, Complex.norm_conj] at h1
  have : ‖perp x‖ ^ 2 = ‖x‖ ^ 2 := by rw [h1, h2]; ring
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 this

lemma norm_det2_le (x y : C2) : ‖det2 x y‖ ≤ ‖x‖ * ‖y‖ := by
  rw [← inner_perp, ← norm_perp x]; exact norm_inner_le_norm _ _

lemma det2_sub_left (x x' y : C2) : det2 x y - det2 x' y = det2 (x - x') y := by
  simp [det2]; ring

lemma det2_self_perp (x : C2) : det2 x (perp x) = ((‖x‖ ^ 2 : ℝ) : ℂ) := by
  have h0 : x 0 * (starRingEnd ℂ) (x 0) = ((‖x 0‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj']; push_cast; ring
  have h1 : x 1 * (starRingEnd ℂ) (x 1) = ((‖x 1‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj']; push_cast; ring
  rw [normsq_C2]
  simp only [det2, perp_zero, perp_one]
  push_cast at h0 h1 ⊢
  linear_combination h0 + h1

lemma decomp (u v : C2) (hu : ‖u‖ = 1) : v = ⟪u, v⟫_ℂ • u + det2 u v • perp u := by
  have h : ((‖u 0‖ : ℂ)) ^ 2 + ((‖u 1‖ : ℂ)) ^ 2 = 1 := by
    have : ‖u 0‖ ^ 2 + ‖u 1‖ ^ 2 = 1 := by rw [← normsq_C2, hu]; norm_num
    exact_mod_cast this
  have h0 : (starRingEnd ℂ) (u 0) * u 0 = (‖u 0‖ : ℂ) ^ 2 := Complex.conj_mul' _
  have h1 : (starRingEnd ℂ) (u 1) * u 1 = (‖u 1‖ : ℂ) ^ 2 := Complex.conj_mul' _
  ext i
  fin_cases i <;> simp [PiLp.inner_apply, Fin.sum_univ_two, det2] <;>
    linear_combination (-v _) * h - v _ * h0 - v _ * h1

lemma norm_sq_decomp (u v : C2) (hu : ‖u‖ = 1) :
    ‖v‖ ^ 2 = ‖⟪u, v⟫_ℂ‖ ^ 2 + ‖det2 u v‖ ^ 2 := by
  have horth : ⟪⟪u, v⟫_ℂ • u, det2 u v • perp u⟫_ℂ = 0 := by
    rw [inner_smul_left, inner_smul_right, inner_self_perp]; simp
  have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  rw [← decomp u v hu, norm_smul, norm_smul, norm_perp, hu] at this
  nlinarith [this]

lemma actC_apply (B : M2) (v : C2) (i : Fin 2) : actC B v i = B i 0 * v 0 + B i 1 * v 1 := by
  simp [actC, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma det2_actC (B : M2) (x y : C2) : det2 (actC B x) (actC B y) = B.det * det2 x y := by
  simp only [det2, actC_apply, det_fin_two]; ring

lemma actC_mul (B C : M2) (x : C2) : actC (B * C) x = actC B (actC C x) := by
  simp [actC, map_mul]

lemma actC_lin (B : M2) (a b : ℂ) (x y : C2) :
    actC B (a • x + b • y) = a • actC B x + b • actC B y := by
  simp [actC]

lemma actC_smul (B : M2) (a : ℂ) (x : C2) : actC B (a • x) = a • actC B x := by
  simp [actC]

lemma actC_sub (B : M2) (x y : C2) : actC B (x - y) = actC B x - actC B y := by
  simp [actC]

lemma norm_actC_le (B : M2) (x : C2) : ‖actC B x‖ ≤ ‖B‖ * ‖x‖ :=
  (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) B).le_opNorm x

lemma norm_entry_le (M : M2) (i j : Fin 2) : ‖M i j‖ ≤ ‖M‖ := by
  have h := sq_norm_col_le M j
  have hi : ‖M i j‖ ^ 2 ≤ ‖M‖ ^ 2 := by
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one] <;> nlinarith [sq_nonneg ‖M 0 j‖,
      sq_nonneg ‖M 1 j‖]
  nlinarith [norm_nonneg (M i j), norm_nonneg M]

lemma norm_le_of_entries (K : M2) {c : ℝ} (hc : 0 ≤ c) (h : ∀ i j, ‖K i j‖ ≤ c) :
    ‖K‖ ≤ 2 * c := by
  show ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) K‖ ≤ 2 * c
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hv := normsq_C2 v
  have hKv := normsq_C2 (actC K v)
  have e : ∀ i, ‖actC K v i‖ ≤ c * ‖v 0‖ + c * ‖v 1‖ := by
    intro i
    rw [actC_apply]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul] <;>
      exact mul_le_mul_of_nonneg_right (h _ _) (norm_nonneg _)
  have e0 := e 0
  have e1 := e 1
  have hsq : ‖actC K v‖ ^ 2 ≤ (2 * c * ‖v‖) ^ 2 := by
    rw [hKv, mul_pow, hv]
    have h0 : ‖actC K v 0‖ ^ 2 ≤ (c * ‖v 0‖ + c * ‖v 1‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) e0 2
    have h1 : ‖actC K v 1‖ ^ 2 ≤ (c * ‖v 0‖ + c * ‖v 1‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) e1 2
    nlinarith [sq_nonneg (‖v 0‖ - ‖v 1‖), sq_nonneg c]
  have hpos : 0 ≤ 2 * c * ‖v‖ := by positivity
  show ‖actC K v‖ ≤ 2 * c * ‖v‖
  nlinarith [norm_nonneg (actC K v)]

lemma norm_adjugate_le (A : M2) : ‖adjugate A‖ ≤ 2 * ‖A‖ :=
  norm_le_of_entries _ (norm_nonneg _) fun i j => by
    fin_cases i <;> fin_cases j <;> simp [adjugate_fin_two, norm_entry_le]

/-- A matrix of determinant one contracts some unit vector to length `≤ 4 / ‖T‖`. -/
lemma small_vector (T : M2) (hT : T.det = 1) : ∃ u : C2, ‖u‖ = 1 ∧ ‖T‖ * ‖actC T u‖ ≤ 4 := by
  set N := adjugate T
  have hTN : T * N = 1 := by rw [mul_adjugate, hT, one_smul]
  have hNadj : adjugate N = T := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [N, adjugate_fin_two]
  have hle : ‖T‖ ≤ 2 * ‖N‖ := hNadj ▸ norm_adjugate_le N
  have hT1 := one_le_norm_of_det_eq_one hT
  have hN0 : 0 < ‖N‖ := by linarith
  obtain ⟨y, hy1, hy⟩ := (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) N).exists_lt_apply_of_lt_opNorm
    (show ‖N‖ / 2 < ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) N‖ from by
      show ‖N‖ / 2 < ‖N‖; linarith)
  set w := actC N y
  have hw : ‖N‖ / 2 < ‖w‖ := hy
  have hw0 : 0 < ‖w‖ := by linarith
  refine ⟨(‖w‖⁻¹ : ℂ) • w, by rw [norm_smul]; simp [hw0.ne'], ?_⟩
  rw [actC_smul, show actC T w = y by rw [← actC_mul, hTN]; simp [actC], norm_smul]
  simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hw0]
  have : ‖y‖ ≤ 1 := hy1.le
  rw [← mul_assoc, mul_comm ‖T‖, ← div_eq_inv_mul]
  rw [div_mul_eq_mul_div, div_le_iff₀ hw0]
  nlinarith [norm_nonneg y, norm_nonneg T]

/-- `‖T x^⊥‖ · ‖T x‖ ≥ 1` for a unit vector `x` and `det T = 1`. -/
lemma one_le_norm_mul_perp {T : M2} (hT : T.det = 1) {x : C2} (hx : ‖x‖ = 1) :
    1 ≤ ‖actC T x‖ * ‖actC T (perp x)‖ := by
  have := norm_det2_le (actC T x) (actC T (perp x))
  rw [det2_actC, hT, one_mul, det2_self_perp, hx] at this
  simpa using this

/-- The coefficient bound from the decomposition `v = ⟨x, v⟩ x + det[x, v] x^⊥`. -/
lemma norm_det2_mul_le {T : M2} {x v : C2} (hx : ‖x‖ = 1) :
    ‖det2 x v‖ * ‖actC T (perp x)‖ ≤ ‖actC T v‖ + ‖v‖ * ‖actC T x‖ := by
  have hv := congrArg (actC T) (decomp x v hx)
  rw [actC_lin] at hv
  have h1 : det2 x v • actC T (perp x) = actC T v - ⟪x, v⟫_ℂ • actC T x := by
    rw [hv]; abel
  have h2 := congrArg norm h1
  rw [norm_smul] at h2
  rw [h2]
  refine (norm_sub_le _ _).trans (add_le_add le_rfl ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right ((norm_inner_le_norm _ _).trans (by rw [hx, one_mul]))
    (norm_nonneg _)

/-- Phases: for `x, y` there is `|c| = 1` with `⟨x, c y⟩ = |⟨x, y⟩|`. -/
lemma exists_phase (x y : C2) : ∃ c : ℂ, ‖c‖ = 1 ∧ ⟪x, c • y⟫_ℂ = ((‖⟪x, y⟫_ℂ‖ : ℝ) : ℂ) := by
  by_cases h : ⟪x, y⟫_ℂ = 0
  · exact ⟨1, by simp, by simp [h]⟩
  · have hn : 0 < ‖⟪x, y⟫_ℂ‖ := norm_pos_iff.2 h
    refine ⟨conj ⟪x, y⟫_ℂ / (‖⟪x, y⟫_ℂ‖ : ℂ), ?_, ?_⟩
    · rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hn,
        div_self hn.ne']
    · rw [inner_smul_right, div_mul_eq_mul_div, Complex.conj_mul', div_eq_iff (by exact_mod_cast hn.ne')]
      push_cast; ring

/-! ### A geometric tail estimate -/

lemma geom_tail {d : ℕ → ℝ} (hd0 : ∀ n, 0 ≤ d n) {C ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    {N : ℕ} (h : ∀ n, N ≤ n → d n ≤ C * ρ ^ n) :
    Summable d ∧ ∀ n, N ≤ n → ∑' m, d (n + m) ≤ C * ρ ^ n / (1 - ρ) := by
  have hC : ∀ n, N ≤ n → 0 ≤ C * ρ ^ n := fun n hn => (hd0 n).trans (h n hn)
  have hsN : Summable fun m => d (m + N) := by
    refine Summable.of_nonneg_of_le (fun m => hd0 _) (fun m => h (m + N) (by omega)) ?_
    exact ((summable_geometric_of_lt_one hρ0 hρ1).mul_left (C * ρ ^ N)).congr fun m => by
      rw [pow_add]; ring
  refine ⟨(summable_nat_add_iff N).1 hsN, fun n hn => ?_⟩
  have hs : Summable fun m => C * ρ ^ n * ρ ^ m :=
    (summable_geometric_of_lt_one hρ0 hρ1).mul_left _
  calc ∑' m, d (n + m) ≤ ∑' m, C * ρ ^ n * ρ ^ m := by
        refine Summable.tsum_le_tsum (fun m => ?_) ?_ hs
        · rw [mul_assoc, ← pow_add]; exact h _ (by omega)
        · exact Summable.of_nonneg_of_le (fun m => hd0 _)
            (fun m => by rw [mul_assoc, ← pow_add]; exact h _ (by omega)) hs
    _ = C * ρ ^ n / (1 - ρ) := by rw [tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1]; ring

/-! ### Theorem 3.8.7 -/

/-- **Theorem 3.8.7** (Ruelle): `DF.Cocycle.RuelleStatement` holds. -/
theorem ruelle : RuelleStatement := by
  intro A L hdet hA hT hL
  set T := seqProd A with hTdef
  have hTsucc : ∀ n, T (n + 1) = A (n + 1) * T n := fun n => rfl
  have hTdet : ∀ n, (T n).det = 1 := by
    intro n; induction n with
    | zero => simp [T, seqProd]
    | succ n ih => rw [hTsucc, det_mul, hdet, ih, one_mul]
  have ht1 : ∀ n, 1 ≤ ‖T n‖ := fun n => one_le_norm_of_det_eq_one (hTdet n)
  have ha1 : ∀ n, 1 ≤ ‖A n‖ := fun n => one_le_norm_of_det_eq_one (hdet n)
  have hback : ∀ n, adjugate (A (n + 1)) * T (n + 1) = T n := by
    intro n; rw [hTsucc, ← mul_assoc, adjugate_mul, hdet, one_smul, one_mul]
  -- small vectors and aligned phases
  choose u hu1 hu using fun n => small_vector (T n) (hTdet n)
  choose ph hph1 hph using exists_phase
  set w : ℕ → C2 := fun n => Nat.rec (motive := fun _ => C2) (u 0)
    (fun k wk => ph wk (u (k + 1)) • u (k + 1)) n with hwdef
  have hw0 : w 0 = u 0 := rfl
  have hws : ∀ n, w (n + 1) = ph (w n) (u (n + 1)) • u (n + 1) := fun n => rfl
  have hw1 : ∀ n, ‖w n‖ = 1 := by
    intro n; cases n with
    | zero => rw [hw0, hu1]
    | succ n => rw [hws, norm_smul, hph1, hu1, one_mul]
  have hwT : ∀ n, ‖T n‖ * ‖actC (T n) (w n)‖ ≤ 4 := by
    intro n; cases n with
    | zero => rw [hw0]; exact hu 0
    | succ n => rw [hws, actC_smul, norm_smul, hph1, one_mul]; exact hu _
  have hwT' : ∀ n, ‖actC (T n) (w n)‖ ≤ 4 / ‖T n‖ := fun n => by
    rw [le_div_iff₀ (by linarith [ht1 n]), mul_comm]; exact hwT n
  have hperp : ∀ n, ‖T n‖ / 4 ≤ ‖actC (T n) (perp (w n))‖ := by
    intro n
    have h1 := one_le_norm_mul_perp (hTdet n) (hw1 n)
    have h2 := hwT n
    have h3 : 0 ≤ ‖actC (T n) (perp (w n))‖ := norm_nonneg _
    nlinarith [norm_nonneg (actC (T n) (w n)), ht1 n]
  -- the angle bound
  set δ : ℕ → ℝ := fun n => ‖det2 (w n) (w (n + 1))‖
  have hδ : ∀ n, δ n ≤ 80 * ‖A (n + 1)‖ ^ 2 / ‖T n‖ ^ 2 := by
    intro n
    set a := ‖A (n + 1)‖
    set t := ‖T n‖
    have ht0 : 0 < t := by linarith [ht1 n]
    have hy : ‖actC (T n) (w (n + 1))‖ ≤ 16 * a ^ 2 / t := by
      have e1 : actC (T n) (w (n + 1)) = actC (adjugate (A (n + 1))) (actC (T (n + 1)) (w (n + 1))) := by
        rw [← actC_mul, hback]
      have e2 := norm_actC_le (adjugate (A (n + 1))) (actC (T (n + 1)) (w (n + 1)))
      have e3 := norm_adjugate_le (A (n + 1))
      have e4 := hwT' (n + 1)
      have e5 : t ≤ 2 * a * ‖T (n + 1)‖ := by
        have := norm_mul_le (adjugate (A (n + 1))) (T (n + 1))
        rw [hback] at this
        nlinarith [norm_nonneg (T (n + 1))]
      have hT1 : 0 < ‖T (n + 1)‖ := by linarith [ht1 (n + 1)]
      rw [e1]
      calc ‖actC (adjugate (A (n + 1))) (actC (T (n + 1)) (w (n + 1)))‖
          ≤ 2 * a * (4 / ‖T (n + 1)‖) :=
            e2.trans (mul_le_mul e3 e4 (norm_nonneg _) (by positivity))
        _ ≤ 16 * a ^ 2 / t := by
            rw [mul_div_assoc', div_le_div_iff₀ hT1 ht0]
            nlinarith [ha1 (n + 1)]
    have hx := hwT' n
    have key := norm_det2_mul_le (T := T n) (v := w (n + 1)) (hw1 n)
    rw [hw1 (n + 1), one_mul] at key
    have hp := one_le_norm_mul_perp (hTdet n) (hw1 n)
    -- `δ ≤ δ ‖T x^⊥‖ ‖T x‖ ≤ (‖T y‖ + ‖T x‖) ‖T x‖`
    have hδ1 : δ n ≤ (‖actC (T n) (w (n + 1))‖ + ‖actC (T n) (w n)‖) * ‖actC (T n) (w n)‖ := by
      have hd0 : 0 ≤ δ n := norm_nonneg _
      calc δ n ≤ δ n * (‖actC (T n) (w n)‖ * ‖actC (T n) (perp (w n))‖) := by nlinarith
        _ = (δ n * ‖actC (T n) (perp (w n))‖) * ‖actC (T n) (w n)‖ := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right key (norm_nonneg _)
    have ha : 1 ≤ a := ha1 (n + 1)
    calc δ n ≤ (16 * a ^ 2 / t + 4 / t) * (4 / t) := by
          refine hδ1.trans (mul_le_mul (add_le_add hy hx) hx (norm_nonneg _) (by positivity))
      _ ≤ 80 * a ^ 2 / t ^ 2 := by
          have : (16 * a ^ 2 / t + 4 / t) * (4 / t) = (64 * a ^ 2 + 16) / t ^ 2 := by
            field_simp; ring
          rw [this]
          gcongr
          nlinarith
  -- increments of `w`
  have hinc : ∀ n, dist (w n) (w (n + 1)) ≤ 2 * δ n := by
    intro n
    have hr : ⟪w n, w (n + 1)⟫_ℂ = ((‖⟪w n, u (n + 1)⟫_ℂ‖ : ℝ) : ℂ) := by
      rw [hws]; exact hph _ _
    have hr' : ‖⟪w n, w (n + 1)⟫_ℂ‖ = ‖⟪w n, u (n + 1)⟫_ℂ‖ := by rw [hr]; simp
    have hsq := norm_sq_decomp (w n) (w (n + 1)) (hw1 n)
    rw [hw1 (n + 1), hr'] at hsq
    have hr0 : 0 ≤ ‖⟪w n, u (n + 1)⟫_ℂ‖ := norm_nonneg _
    have hr1 : ‖⟪w n, u (n + 1)⟫_ℂ‖ ≤ 1 := by nlinarith [norm_nonneg (det2 (w n) (w (n + 1)))]
    have hd : dist (w n) (w (n + 1)) ^ 2 = 2 - 2 * ‖⟪w n, u (n + 1)⟫_ℂ‖ := by
      rw [dist_eq_norm, @norm_sub_sq ℂ, hw1 n, hw1 (n + 1), hr]
      simp
      try ring
    have hδn : δ n ^ 2 = 1 - ‖⟪w n, u (n + 1)⟫_ℂ‖ ^ 2 := by
      simp only [δ]; linarith
    have : dist (w n) (w (n + 1)) ^ 2 ≤ (2 * δ n) ^ 2 := by nlinarith
    exact (pow_le_pow_iff_left₀ dist_nonneg (by positivity) two_ne_zero).1 this
  -- rates
  have hrateT : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, (L - ε) * n ≤ Real.log ‖T n‖ ∧
      Real.log ‖T n‖ ≤ (L + ε) * n := by
    intro ε hε
    filter_upwards [hT.eventually (Ioo_mem_nhds (show L - ε < L by linarith)
      (show L < L + ε by linarith)), eventually_ge_atTop 1] with n hn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    obtain ⟨h1, h2⟩ := hn
    rw [lt_div_iff₀ hnpos] at h1
    rw [div_lt_iff₀ hnpos] at h2
    exact ⟨h1.le, h2.le⟩
  have hrateA : ∀ ε > 0, ∀ᶠ n : ℕ in atTop, Real.log ‖A (n + 1)‖ ≤ ε * n := by
    intro ε hε
    have := (hA.comp (tendsto_add_atTop_nat 1)).eventually (gt_mem_nhds (half_pos hε))
    filter_upwards [this, eventually_ge_atTop 1] with n hn hn1
    simp only [Function.comp_apply] at hn
    have hnpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    rw [div_lt_iff₀ hnpos] at hn
    push_cast at hn
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    nlinarith
  -- exponential bound on `δ`
  have hδexp : ∀ ε > 0, ∀ᶠ n : ℕ in atTop,
      δ n ≤ 80 * Real.exp (-(2 * L - 4 * ε)) ^ n := by
    intro ε hε
    filter_upwards [hrateT ε hε, hrateA ε hε] with n hn ha
    refine (hδ n).trans ?_
    have ht0 : 0 < ‖T n‖ := by linarith [ht1 n]
    have ha0 : 0 < ‖A (n + 1)‖ := by linarith [ha1 (n + 1)]
    rw [← Real.exp_nat_mul, mul_div_assoc]
    gcongr
    rw [div_le_iff₀ (by positivity), ← Real.exp_log ha0, ← Real.exp_log ht0, ← Real.exp_nat_mul,
      ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.2
    push_cast
    nlinarith [hn.1]
  -- summability and the limit
  have hL4 : 0 < L / 4 := by positivity
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (hδexp (L / 4) hL4)
  have hρ0 : 0 ≤ Real.exp (-(2 * L - 4 * (L / 4))) := (Real.exp_pos _).le
  have hρ1 : Real.exp (-(2 * L - 4 * (L / 4))) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hδsum : Summable δ := (geom_tail (fun n => norm_nonneg _) hρ0 hρ1 hN0).1
  have hcauchy : CauchySeq w :=
    cauchySeq_of_summable_dist (Summable.of_nonneg_of_le (fun n => dist_nonneg) hinc
      (hδsum.mul_left 2))
  obtain ⟨uinf, hlim⟩ := cauchySeq_tendsto_of_complete hcauchy
  have huinf1 : ‖uinf‖ = 1 := by
    have := (continuous_norm.tendsto uinf).comp hlim
    simp only [comp_def, hw1] at this
    exact (tendsto_nhds_unique tendsto_const_nhds this).symm
  have htail : ∀ n, dist (w n) uinf ≤ ∑' m, 2 * δ (n + m) :=
    fun n => dist_le_tsum_of_dist_le_of_tendsto (fun n => 2 * δ n) hinc (hδsum.mul_left 2) hlim n
  -- the subspace
  refine ⟨ℂ ∙ uinf, ?_, ?_, ?_⟩
  · exact finrank_span_singleton (by intro h; rw [h, norm_zero] at huinf1; norm_num at huinf1)
  · -- vectors in `V`
    intro v hv hv0
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
    have hc : c ≠ 0 := by rintro rfl; simp at hv0
    have hcpos : 0 < ‖c‖ := norm_pos_iff.2 hc
    -- lower bound
    have hlow : ∀ n, 1 / ‖T n‖ ≤ ‖actC (T n) uinf‖ := by
      intro n
      have h1 := one_le_norm_mul_perp (hTdet n) huinf1
      have h2 := norm_actC_le (T n) (perp uinf)
      rw [norm_perp, huinf1, mul_one] at h2
      rw [div_le_iff₀ (by linarith [ht1 n])]
      nlinarith [norm_nonneg (actC (T n) uinf)]
    have hpos : ∀ n, 0 < ‖actC (T n) uinf‖ := fun n =>
      lt_of_lt_of_le (by have := ht1 n; positivity) (hlow n)
    suffices hmain : Tendsto (fun n : ℕ => Real.log ‖actC (T n) uinf‖ / n) atTop (𝓝 (-L)) by
      have h2 : Tendsto (fun n : ℕ => Real.log ‖c‖ / n) atTop (𝓝 0) :=
        tendsto_const_div_atTop_nhds_zero_nat _
      have := h2.add hmain
      rw [zero_add] at this
      refine this.congr fun n => ?_
      rw [actC_smul, norm_smul, Real.log_mul hcpos.ne' (hpos n).ne', add_div]
    rw [tendsto_order]
    refine ⟨fun a ha => ?_, fun b hb => ?_⟩
    · -- lower bound: `log ‖T uinf‖ ≥ - log ‖T‖`
      have hneg : Tendsto (fun n : ℕ => -(Real.log ‖T n‖ / n)) atTop (𝓝 (-L)) := hT.neg
      filter_upwards [hneg.eventually (lt_mem_nhds ha), eventually_ge_atTop 1] with n hn hn1
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
      refine hn.trans_le ?_
      rw [neg_div', div_le_div_iff_of_pos_right hnpos, ← Real.log_inv]
      exact Real.log_le_log (by have := ht1 n; positivity) (by rw [inv_eq_one_div]; exact hlow n)
    · -- upper bound
      set ε := min ((b + L) / 10) (L / 8)
      have hε : 0 < ε := lt_min (by linarith) (by positivity)
      have hε1 : ε ≤ (b + L) / 10 := min_le_left _ _
      have hε2 : ε ≤ L / 8 := min_le_right _ _
      set ρ := Real.exp (-(2 * L - 4 * ε))
      have hρ0' : 0 ≤ ρ := (Real.exp_pos _).le
      have hρ1' : ρ < 1 := Real.exp_lt_one_iff.2 (by linarith)
      obtain ⟨N1, hN1⟩ := eventually_atTop.1 (hδexp ε hε)
      have hgt := (geom_tail (C := 80) (fun n => norm_nonneg _) hρ0' hρ1' hN1).2
      set K := 160 / (1 - ρ)
      have hK : 0 < K := div_pos (by norm_num) (by linarith)
      -- `‖T uinf‖ ≤ (4 + K) e^{-(L - 5ε) n}` eventually
      have hbound : ∀ᶠ n : ℕ in atTop,
          ‖actC (T n) uinf‖ ≤ (4 + K) * Real.exp (-(L - 5 * ε) * n) := by
        filter_upwards [hrateT ε hε, eventually_ge_atTop N1] with n hn hnN
        have ht0 : 0 < ‖T n‖ := by linarith [ht1 n]
        have e1 : ‖actC (T n) uinf‖ ≤ ‖actC (T n) (w n)‖ + ‖T n‖ * dist (w n) uinf := by
          have : actC (T n) uinf = actC (T n) (w n) - actC (T n) (w n - uinf) := by
            rw [actC_sub]; abel
          rw [this, dist_eq_norm]
          exact (norm_sub_le _ _).trans (add_le_add le_rfl (norm_actC_le _ _))
        have e2 : dist (w n) uinf ≤ K * ρ ^ n := by
          refine (htail n).trans ?_
          rw [tsum_mul_left]
          have := hgt n hnN
          calc 2 * ∑' m, δ (n + m) ≤ 2 * (80 * ρ ^ n / (1 - ρ)) := by linarith
            _ = K * ρ ^ n := by simp only [K]; ring
        have e3 : ‖T n‖ ≤ Real.exp ((L + ε) * n) := by
          rw [← Real.exp_log ht0]; exact Real.exp_le_exp.2 hn.2
        have e4 : 4 / ‖T n‖ ≤ 4 * Real.exp (-(L - ε) * n) := by
          rw [div_le_iff₀ ht0, mul_assoc, ← Real.exp_log ht0, ← Real.exp_add]
          have : 1 ≤ Real.exp (-(L - ε) * n + Real.log ‖T n‖) :=
            Real.one_le_exp (by nlinarith [hn.1])
          linarith
        have hρn : ρ ^ n = Real.exp (-(2 * L - 4 * ε) * n) := by
          rw [← Real.exp_nat_mul]; ring_nf
        have e5 : Real.exp (-(L - ε) * n) ≤ Real.exp (-(L - 5 * ε) * n) :=
          Real.exp_le_exp.2 (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
        calc ‖actC (T n) uinf‖ ≤ 4 / ‖T n‖ + ‖T n‖ * (K * ρ ^ n) :=
              e1.trans (add_le_add (hwT' n) (mul_le_mul_of_nonneg_left e2 ht0.le))
          _ ≤ 4 * Real.exp (-(L - 5 * ε) * n) +
              Real.exp ((L + ε) * n) * (K * Real.exp (-(2 * L - 4 * ε) * n)) := by
              rw [← hρn]
              refine add_le_add (e4.trans (by linarith)) (mul_le_mul_of_nonneg_right e3 (by positivity))
          _ = (4 + K) * Real.exp (-(L - 5 * ε) * n) := by
              rw [mul_left_comm, ← Real.exp_add]
              ring_nf
      have hc4 : Tendsto (fun n : ℕ => Real.log (4 + K) / n - (L - 5 * ε)) atTop
          (𝓝 (0 - (L - 5 * ε))) :=
        (tendsto_const_div_atTop_nhds_zero_nat _).sub tendsto_const_nhds
      have hlt : 0 - (L - 5 * ε) < b := by linarith
      filter_upwards [hbound, hc4.eventually (gt_mem_nhds hlt), eventually_ge_atTop 1]
        with n hn hn' hn1
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
      refine lt_of_le_of_lt ?_ hn'
      rw [div_le_iff₀ hnpos, sub_mul, div_mul_cancel₀ _ hnpos.ne']
      have := Real.log_le_log (hpos n) hn
      rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at this
      linarith
  · -- vectors outside `V`
    intro v hv
    set κ := ‖det2 uinf v‖
    have hκ : 0 < κ := by
      rcases eq_or_lt_of_le (norm_nonneg (det2 uinf v)) with h | h
      · exfalso
        apply hv
        have h0 : det2 uinf v = 0 := norm_eq_zero.1 h.symm
        rw [decomp uinf v huinf1, h0, zero_smul, add_zero]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self uinf)
      · exact h
    have hv0 : 0 < ‖v‖ := by
      rcases eq_or_lt_of_le (norm_nonneg v) with h | h
      · exfalso
        have : v = 0 := norm_eq_zero.1 h.symm
        exact hv (this ▸ Submodule.zero_mem _)
      · exact h
    -- eventually `‖det2 (w n) v‖ ≥ κ / 2`
    have hdet : ∀ᶠ n : ℕ in atTop, κ / 2 ≤ ‖det2 (w n) v‖ := by
      have hd : Tendsto (fun n => dist (w n) uinf * ‖v‖) atTop (𝓝 (0 * ‖v‖)) :=
        (tendsto_iff_dist_tendsto_zero.1 hlim).mul_const _
      rw [zero_mul] at hd
      filter_upwards [hd.eventually (gt_mem_nhds (half_pos hκ))] with n hn
      have e1 : ‖det2 uinf v - det2 (w n) v‖ ≤ dist (w n) uinf * ‖v‖ := by
        rw [det2_sub_left, dist_comm, dist_eq_norm]; exact norm_det2_le _ _
      have e2 := norm_sub_norm_le (det2 uinf v) (det2 (w n) v)
      linarith
    -- `‖T n‖ → ∞`
    have htinf : Tendsto (fun n => ‖T n‖) atTop atTop := by
      have := hT.eventually (lt_mem_nhds (half_lt_self hL))
      refine tendsto_atTop_mono' atTop ?_ (tendsto_natCast_atTop_atTop.const_mul_atTop
        (half_pos hL))
      filter_upwards [this, eventually_ge_atTop 1] with n hn hn1
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
      rw [lt_div_iff₀ hnpos] at hn
      have := Real.log_le_sub_one_of_pos (show 0 < ‖T n‖ by linarith [ht1 n])
      linarith
    -- eventually `‖T v‖ ≥ κ ‖T‖ / 16`
    have hlowv : ∀ᶠ n : ℕ in atTop, κ * ‖T n‖ / 16 ≤ ‖actC (T n) v‖ := by
      filter_upwards [hdet, htinf.eventually (eventually_ge_atTop (Real.sqrt (64 * ‖v‖ / κ) + 1))]
        with n hn htn
      have ht0 : 0 < ‖T n‖ := by linarith [ht1 n]
      have key := norm_det2_mul_le (T := T n) (v := v) (hw1 n)
      have e1 := hperp n
      have e2 := hwT' n
      have hsq : 64 * ‖v‖ / κ ≤ ‖T n‖ ^ 2 := by
        have h1 : Real.sqrt (64 * ‖v‖ / κ) ≤ ‖T n‖ := by linarith
        have h2 := Real.sq_sqrt (show 0 ≤ 64 * ‖v‖ / κ by positivity)
        nlinarith [Real.sqrt_nonneg (64 * ‖v‖ / κ)]
      have hsq' : 64 * ‖v‖ ≤ κ * ‖T n‖ ^ 2 := by
        rw [div_le_iff₀ hκ] at hsq; linarith
      have e3 : κ / 2 * (‖T n‖ / 4) ≤ ‖det2 (w n) v‖ * ‖actC (T n) (perp (w n))‖ :=
        mul_le_mul hn e1 (by positivity) (norm_nonneg _)
      have e4 : ‖v‖ * ‖actC (T n) (w n)‖ ≤ ‖v‖ * (4 / ‖T n‖) :=
        mul_le_mul_of_nonneg_left e2 hv0.le
      have e5 : ‖v‖ * (4 / ‖T n‖) ≤ κ * ‖T n‖ / 16 := by
        rw [mul_div_assoc', div_le_div_iff₀ ht0 (by norm_num)]
        nlinarith
      linarith
    have hpos : ∀ᶠ n : ℕ in atTop, 0 < ‖actC (T n) v‖ := by
      filter_upwards [hlowv] with n hn
      exact lt_of_lt_of_le (by have := ht1 n; positivity) hn
    have hg : Tendsto (fun n : ℕ => Real.log (κ / 16) / n + Real.log ‖T n‖ / n) atTop
        (𝓝 (0 + L)) := (tendsto_const_div_atTop_nhds_zero_nat _).add hT
    have hh : Tendsto (fun n : ℕ => Real.log ‖T n‖ / n + Real.log ‖v‖ / n) atTop
        (𝓝 (L + 0)) := hT.add (tendsto_const_div_atTop_nhds_zero_nat _)
    rw [zero_add] at hg
    rw [add_zero] at hh
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hg hh ?_ ?_
    · filter_upwards [hlowv, eventually_ge_atTop 1] with n hn hn1
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
      rw [← add_div, div_le_div_iff_of_pos_right hnpos,
        ← Real.log_mul (by positivity) (by linarith [ht1 n])]
      exact Real.log_le_log (by have := ht1 n; positivity) (by linarith)
    · filter_upwards [hpos, eventually_ge_atTop 1] with n hn hn1
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
      rw [← add_div, div_le_div_iff_of_pos_right hnpos,
        ← Real.log_mul (by linarith [ht1 n]) hv0.ne']
      exact Real.log_le_log hn (norm_actC_le _ _)

end Cocycle

end DF
