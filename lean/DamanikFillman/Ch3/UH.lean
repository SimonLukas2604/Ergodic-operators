/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §3.8.1: uniform hyperbolicity — absence of bounded orbits implies uniform growth

Main results:
* `DF.Cocycle.iterZ_succ`, `DF.Cocycle.iterZ_add` — the cocycle identity
  `A_{n+m}(ω) = A_m(Tⁿω) A_n(ω)` for all `n, m ∈ ℤ` (cf. (3.8.2), (3.8.3));
* `DF.Cocycle.one_le_norm_SL2R` — `‖M‖ ≥ 1` for `M ∈ SL(2, ℝ)`;
* `DF.Cocycle.uniformExpGrowth_of_not_boundedOrbit` — **Theorem 3.8.2, (c) ⇒ (a)**: if a
  continuous `SL(2, ℝ)` cocycle over a homeomorphism of a compact metric space has no bounded
  orbit, then it exhibits uniform exponential growth. (Equivalently: a cocycle which is not
  uniformly hyperbolic has a bounded orbit.)

The proof follows the book (compactness, Claim 1 and Claim 2). Claim 2 is made rigorous by
noting that, along the sequences of Claim 1, the indices eventually have constant sign after a
number of steps bounded uniformly in `(ω, v)`; if all unit vectors at `ω` were expanded in
backward time with uniform constants, some `A_{-n}(ω) ∈ SL(2, ℝ)` would expand every vector,
contradicting `‖A_{-n}(ω)⁻¹‖ ≥ 1`.

The converse (a) ⇒ (c) is proved in `DamanikFillman.Ch3.UH2`; the implications involving the
invariant splitting (b) are proved in `DamanikFillman.Ch3.UHSplit` ((b) ⇒ (a)) and
`DamanikFillman.Ch3.UHStable` ((a) ⇒ (b), and the full statement
`DF.Cocycle.uniformHyperbolicityCharacterization`).
-/
import DamanikFillman.Ch3.Cocycle

noncomputable section

set_option linter.unusedSectionVars false

open Filter Set Function Topology Matrix
open scoped Matrix.Norms.L2Operator

namespace DF

namespace Cocycle

/-! ### The cocycle identity over `ℤ` -/

section algebra

variable {Ω : Type*} {R : Type*} [Group R] {T : Ω ≃ Ω} {A : Ω → R}

/-- `Tⁿ` for `n ∈ ℤ`. -/
def tpow (T : Ω ≃ Ω) (n : ℤ) : Ω → Ω := ⇑((T : Equiv.Perm Ω) ^ n)

lemma tpow_natCast (k : ℕ) (x : Ω) : tpow T k x = T^[k] x := by
  simp only [tpow]; rw [zpow_natCast, Equiv.Perm.coe_pow]

lemma tpow_negSucc (k : ℕ) (x : Ω) : tpow T (Int.negSucc k) x = T.symm^[k + 1] x := by
  simp only [tpow]; rw [zpow_negSucc, ← inv_pow, Equiv.Perm.coe_pow]; rfl

lemma tpow_add (n m : ℤ) (x : Ω) : tpow T (n + m) x = tpow T m (tpow T n x) := by
  simp only [tpow]; rw [add_comm, _root_.zpow_add, Equiv.Perm.mul_apply]

lemma tpow_zero (x : Ω) : tpow T 0 x = x := by simp [tpow]

lemma tpow_add_one (n : ℤ) (x : Ω) : tpow T (n + 1) x = T (tpow T n x) := by
  rw [tpow_add]; simp [tpow]

lemma tpow_sub_one (n : ℤ) (x : Ω) : tpow T (n - 1) x = T.symm (tpow T n x) := by
  have := tpow_add_one (T := T) (n - 1) x
  rw [sub_add_cancel] at this
  rw [this, Equiv.symm_apply_apply]

lemma iterZ_zero (ω : Ω) : iterZ T A 0 ω = 1 := rfl

/-- One step of the cocycle over `ℤ`: `A_{n+1}(ω) = A(Tⁿω) A_n(ω)`. -/
theorem iterZ_succ (n : ℤ) (ω : Ω) : iterZ T A (n + 1) ω = A (tpow T n ω) * iterZ T A n ω := by
  rcases n with k | k
  · simp only [Int.ofNat_eq_natCast]
    rw [show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by push_cast; ring, iterZ_natCast, iterZ_natCast,
      iter_succ, tpow_natCast]
  · rcases k with _ | j
    · rw [show Int.negSucc 0 + 1 = ((0 : ℕ) : ℤ) by rfl, iterZ_natCast, tpow_negSucc]
      simp only [iterZ, iter_zero, zero_add, iter_one, mul_inv_cancel]
    · rw [show Int.negSucc (j + 1) + 1 = Int.negSucc j by omega, tpow_negSucc]
      simp only [iterZ]
      set y := T.symm^[j + 1 + 1] ω
      have hy : iter T A (j + 1 + 1) y = iter T A (j + 1) (T y) * A y := by
        rw [show j + 1 + 1 = 1 + (j + 1) by ring, iter_add]; simp
      have hTy : T y = T.symm^[j + 1] ω := by
        simp only [y]; rw [iterate_succ_apply' T.symm (j + 1), Equiv.apply_symm_apply]
      rw [hy, hTy, _root_.mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]

/-- The cocycle identity `A_{n+m}(ω) = A_m(Tⁿω) A_n(ω)` for `n, m ∈ ℤ`. -/
theorem iterZ_add (n m : ℤ) (ω : Ω) :
    iterZ T A (n + m) ω = iterZ T A m (tpow T n ω) * iterZ T A n ω := by
  induction m using Int.induction_on with
  | zero => simp [iterZ_zero]
  | succ i ih => rw [← add_assoc, iterZ_succ, ih, iterZ_succ, tpow_add, mul_assoc]
  | pred i ih =>
    have h1 := iterZ_succ (T := T) (A := A) (n + (-(i : ℤ) - 1)) ω
    have h2 := iterZ_succ (T := T) (A := A) (-(i : ℤ) - 1) (tpow T n ω)
    rw [show n + (-(i : ℤ) - 1) + 1 = n + -(i : ℤ) by ring, ih] at h1
    rw [show -(i : ℤ) - 1 + 1 = -(i : ℤ) by ring] at h2
    have ha : tpow T (n + (-(i : ℤ) - 1)) ω = tpow T (-(i : ℤ) - 1) (tpow T n ω) := tpow_add _ _ _
    rw [h2, ha, mul_assoc] at h1
    exact (mul_left_cancel h1).symm

/-- `A_m(ω)⁻¹ = A_{-m}(Tᵐω)`, generalising (3.8.3). -/
theorem iterZ_inv (m : ℤ) (y : Ω) : (iterZ T A m y)⁻¹ = iterZ T A (-m) (tpow T m y) := by
  have := iterZ_add (T := T) (A := A) m (-m) y
  rw [add_neg_cancel, iterZ_zero] at this
  exact (eq_inv_of_mul_eq_one_left this.symm).symm

lemma iterZ_pred (n : ℤ) (ω : Ω) :
    iterZ T A (n - 1) ω = (A (tpow T (n - 1) ω))⁻¹ * iterZ T A n ω := by
  have := iterZ_succ (T := T) (A := A) (n - 1) ω
  rw [sub_add_cancel] at this
  rw [this, ← mul_assoc, inv_mul_cancel, one_mul]

end algebra

/-! ### Norm estimates in `SL(2, ℝ)` -/

lemma sq_norm_col_le_R (M : M2R) (j : Fin 2) : ‖M 0 j‖ ^ 2 + ‖M 1 j‖ ^ 2 ≤ ‖M‖ ^ 2 := by
  have h := (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) M).le_opNorm
    (WithLp.toLp 2 (Pi.single j 1))
  rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.toEuclideanCLM_toLp] at h
  have h1 : ‖(WithLp.toLp 2 (Pi.single j (1 : ℝ)) : EuclideanSpace ℝ (Fin 2))‖ = 1 := by
    rw [EuclideanSpace.norm_eq]; fin_cases j <;> simp [Fin.sum_univ_two]
  have h2 : ‖(WithLp.toLp 2 (M *ᵥ Pi.single j 1) : EuclideanSpace ℝ (Fin 2))‖ ^ 2 =
      ‖M 0 j‖ ^ 2 + ‖M 1 j‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [h1, mul_one] at h
  have := pow_le_pow_left₀ (norm_nonneg _) h 2
  linarith

/-- For `M ∈ SL(2, ℝ)`, the operator norm satisfies `‖M‖ ≥ 1`. -/
theorem one_le_norm_SL2R (M : SL2R) : 1 ≤ ‖(M : M2R)‖ := by
  have hM : (M : M2R).det = 1 := M.2
  have h0 := sq_norm_col_le_R M 0
  have h1 := sq_norm_col_le_R M 1
  have hdet : ‖(M : M2R).det‖ ≤ ‖(M : M2R) 0 0‖ * ‖(M : M2R) 1 1‖ +
      ‖(M : M2R) 0 1‖ * ‖(M : M2R) 1 0‖ := by
    rw [det_fin_two]; refine (norm_sub_le _ _).trans ?_; rw [norm_mul, norm_mul]
  rw [hM, norm_one] at hdet
  set a := ‖(M : M2R) 0 0‖
  set b := ‖(M : M2R) 0 1‖
  set c := ‖(M : M2R) 1 0‖
  set d := ‖(M : M2R) 1 1‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hc : 0 ≤ c := norm_nonneg _
  have hd : 0 ≤ d := norm_nonneg _
  have hcs : (a * d + b * c) ^ 2 ≤ (a ^ 2 + c ^ 2) * (b ^ 2 + d ^ 2) := by
    nlinarith [sq_nonneg (a * b - c * d)]
  have h4 : 1 ≤ ‖(M : M2R)‖ ^ 4 := by
    calc (1 : ℝ) ≤ (a * d + b * c) ^ 2 := by nlinarith
      _ ≤ (a ^ 2 + c ^ 2) * (b ^ 2 + d ^ 2) := hcs
      _ ≤ ‖(M : M2R)‖ ^ 2 * ‖(M : M2R)‖ ^ 2 := mul_le_mul h0 h1 (by positivity) (by positivity)
      _ = ‖(M : M2R)‖ ^ 4 := by ring
  by_contra hlt
  push Not at hlt
  have : ‖(M : M2R)‖ ^ 4 < 1 := pow_lt_one₀ (norm_nonneg _) hlt (by norm_num)
  linarith

lemma act_mul (B C : M2R) (v : EuclideanSpace ℝ (Fin 2)) : act (B * C) v = act B (act C v) := by
  simp [act, map_mul]

lemma act_one (v : EuclideanSpace ℝ (Fin 2)) : act 1 v = v := by simp [act]

lemma act_smul (B : M2R) (c : ℝ) (v : EuclideanSpace ℝ (Fin 2)) : act B (c • v) = c • act B v := by
  simp [act]

lemma norm_act_le (B : M2R) (v : EuclideanSpace ℝ (Fin 2)) : ‖act B v‖ ≤ ‖B‖ * ‖v‖ :=
  (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) B).le_opNorm v

lemma norm_le_inv_mul_act (M : SL2R) (v : EuclideanSpace ℝ (Fin 2)) :
    ‖v‖ ≤ ‖((M⁻¹ : SL2R) : M2R)‖ * ‖act (M : M2R) v‖ := by
  have : act ((M⁻¹ : SL2R) : M2R) (act M v) = v := by
    rw [← act_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
      act_one]
  calc ‖v‖ = ‖act ((M⁻¹ : SL2R) : M2R) (act M v)‖ := by rw [this]
    _ ≤ _ := norm_act_le _ _

lemma continuous_act {Y : Type*} [TopologicalSpace Y] {f : Y → M2R}
    {g : Y → EuclideanSpace ℝ (Fin 2)} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun y => act (f y) (g y) := by
  have : Continuous fun M : M2R => Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) M :=
    AddMonoidHomClass.continuous_of_bound (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ)) 1
      fun M => by rw [one_mul]; exact le_of_eq rfl
  exact (this.comp hf).clm_apply hg

lemma adjugate_eq_trace (M : M2R) : adjugate M = (Matrix.trace M) • (1 : M2R) - M := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [adjugate_fin_two, trace_fin_two]

/-- An element of `SL(2, ℝ)` cannot expand every vector by a factor `c > 1`. -/
lemma not_expanding (M : SL2R) {c : ℝ} (hc : 1 < c)
    (h : ∀ v : EuclideanSpace ℝ (Fin 2), c * ‖v‖ ≤ ‖act (M : M2R) v‖) : False := by
  have hb : ‖((M⁻¹ : SL2R) : M2R)‖ ≤ c⁻¹ := by
    show ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) ((M⁻¹ : SL2R) : M2R)‖ ≤ c⁻¹
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
    have h1 := h (act ((M⁻¹ : SL2R) : M2R) w)
    rw [← act_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
      act_one] at h1
    have hc0 : 0 < c := by linarith
    rw [show Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) ((M⁻¹ : SL2R) : M2R) w =
      act ((M⁻¹ : SL2R) : M2R) w from rfl]
    rw [inv_mul_eq_div, le_div_iff₀ hc0]
    linarith
  have h1 := one_le_norm_SL2R M⁻¹
  have : c⁻¹ < 1 := inv_lt_one_of_one_lt₀ hc
  linarith

/-! ### An interpolation lemma for sequences with bounded gaps -/

/-- If `a(s_k) ≥ (1+ε)^k a(0)` along a sequence `s` with `s_0 = 0`, gaps `≤ N`, eventually
positive indices, and `a` can decrease by at most `Q^N` over `N` steps, then
`a(m) ≥ λ^m ((1+ε) Q^N)⁻¹ a(0)` for `m ≥ K₀ N`, where `λ^N = 1+ε`. -/
lemma interp (a : ℤ → ℝ) {Q : ℝ} (hQ : 1 ≤ Q) {N : ℕ} {ε l : ℝ} (hε : 0 < ε) (hl : 1 ≤ l)
    (hlN : l ^ N = 1 + ε) (s : ℕ → ℤ) (K0 : ℕ) (h0 : s 0 = 0)
    (hstep : ∀ k, |s (k + 1) - s k| ≤ N) (hgrow : ∀ k, (1 + ε) ^ k * a 0 ≤ a (s k))
    (hP1 : ∀ (p : ℤ) (j : ℕ), j ≤ N → a p * (Q ^ N)⁻¹ ≤ a (p + j))
    (hupper : ∀ n : ℤ, a n ≤ Q ^ n.natAbs * a 0) (hpos : ∀ k, K0 ≤ k → 0 < s k) (ha0 : 0 < a 0) :
    ∀ m : ℕ, K0 * N ≤ m → l ^ m * ((1 + ε) * Q ^ N)⁻¹ * a 0 ≤ a m := by
  intro m hm
  have hsk : ∀ k : ℕ, s k ≤ k * N := by
    intro k
    induction k with
    | zero => simp [h0]
    | succ k ih => have := (abs_le.1 (hstep k)).2; push_cast; linarith
  have hunb : ∀ M : ℤ, ∃ k, K0 ≤ k ∧ M < s k := by
    intro M
    obtain ⟨k0, hk0⟩ := pow_unbounded_of_one_lt (Q ^ M.toNat) (by linarith : 1 < 1 + ε)
    refine ⟨max k0 K0, le_max_right _ _, ?_⟩
    by_contra hc
    push Not at hc
    set k := max k0 K0
    have hsp := hpos k (le_max_right _ _)
    have h1 := hgrow k
    have h2 := hupper (s k)
    have h3 : Q ^ (s k).natAbs ≤ Q ^ M.toNat := pow_le_pow_right₀ hQ (by omega)
    have h4 : (1 + ε) ^ k0 ≤ (1 + ε) ^ k := pow_le_pow_right₀ (by linarith) (le_max_left _ _)
    have h5 : Q ^ M.toNat * a 0 < (1 + ε) ^ k * a 0 := by nlinarith
    nlinarith
  classical
  have hex : ∃ k, K0 ≤ k ∧ (m : ℤ) - N < s k := hunb (m - N)
  set k1 := Nat.find hex
  have hk1 : K0 ≤ k1 ∧ (m : ℤ) - N < s k1 := Nat.find_spec hex
  have hle : s k1 ≤ m := by
    by_cases hk : k1 = K0
    · have := hsk k1
      rw [hk] at this ⊢
      have hm' : ((K0 * N : ℕ) : ℤ) ≤ m := by exact_mod_cast hm
      push_cast at hm'
      linarith
    · have hk1' : K0 < k1 := lt_of_le_of_ne hk1.1 (Ne.symm hk)
      obtain ⟨j, hj⟩ : ∃ j, k1 = j + 1 := ⟨k1 - 1, by omega⟩
      have hnot : ¬ (K0 ≤ j ∧ (m : ℤ) - N < s j) := Nat.find_min hex (by omega)
      have hjK : K0 ≤ j := by omega
      have h1 : s j ≤ (m : ℤ) - N := by
        by_contra hc; exact hnot ⟨hjK, not_le.1 hc⟩
      have h2 := (abs_le.1 (hstep j)).2
      rw [hj]; linarith
  have hmk : m ≤ (k1 + 1) * N := by
    have h1 := hsk k1
    have h2 := hk1.2
    have : (m : ℤ) ≤ ((k1 + 1) * N : ℕ) := by push_cast; linarith
    exact_mod_cast this
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (m : ℤ) = s k1 + j := ⟨(m - s k1).toNat, by omega⟩
  have hjN : j ≤ N := by have := hk1.2; omega
  have hP := hP1 (s k1) j hjN
  rw [← hj] at hP
  have hQN : 0 < Q ^ N := by positivity
  have hlm : l ^ m ≤ (1 + ε) * (1 + ε) ^ k1 := by
    calc l ^ m ≤ l ^ ((k1 + 1) * N) := pow_le_pow_right₀ hl hmk
      _ = (1 + ε) * (1 + ε) ^ k1 := by rw [mul_comm, pow_mul, hlN, pow_succ, mul_comm]
  calc l ^ m * ((1 + ε) * Q ^ N)⁻¹ * a 0
      ≤ (1 + ε) * (1 + ε) ^ k1 * ((1 + ε) * Q ^ N)⁻¹ * a 0 := by gcongr
    _ = (1 + ε) ^ k1 * a 0 * (Q ^ N)⁻¹ := by field_simp
    _ ≤ a (s k1) * (Q ^ N)⁻¹ := by gcongr; exact hgrow k1
    _ ≤ a m := hP

/-! ### Theorem 3.8.2, (c) ⇒ (a) -/

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- **Theorem 3.8.2, (c) ⇒ (a)**: a continuous `SL(2, ℝ)` cocycle over a homeomorphism of a
compact metric space without bounded orbits exhibits uniform exponential growth. -/
theorem uniformExpGrowth_of_not_boundedOrbit (T : X ≃ₜ X) (A : X → SL2R)
    (hA : Continuous fun ω => (A ω : M2R)) (h : ¬ BoundedOrbit T A) : UniformExpGrowth T A := by
  classical
  set B : ℤ → X → SL2R := fun n ω => iterZ T.toEquiv A n ω with hBdef
  set tp := tpow T.toEquiv
  have hBadd : ∀ (n m : ℤ) ω, B (n + m) ω = B m (tp n ω) * B n ω := fun n m ω => iterZ_add n m ω
  have hB0 : ∀ ω, B 0 ω = 1 := fun ω => rfl
  -- continuity
  have htp : ∀ n, Continuous (tp n) := by
    intro n
    induction n using Int.induction_on with
    | zero => exact continuous_id.congr fun x => (tpow_zero x).symm
    | succ i ih => exact (T.continuous.comp ih).congr fun x => (tpow_add_one (i : ℤ) x).symm
    | pred i ih => exact (T.symm.continuous.comp ih).congr fun x => (tpow_sub_one (-(i : ℤ)) x).symm
  have hAinv : Continuous fun ω => (((A ω)⁻¹ : SL2R) : M2R) := by
    simp_rw [Matrix.SpecialLinearGroup.coe_inv, adjugate_eq_trace]
    exact (hA.matrix_trace.smul continuous_const).sub hA
  have hBc : ∀ n, Continuous fun ω => (B n ω : M2R) := by
    intro n
    induction n using Int.induction_on with
    | zero => exact continuous_const.congr fun ω => by rw [hB0, Matrix.SpecialLinearGroup.coe_one]
    | succ i ih =>
      refine ((hA.comp (htp i)).mul ih).congr fun ω => ?_
      show (A (tp i ω) : M2R) * (B i ω : M2R) = (B (i + 1) ω : M2R)
      rw [show B (i + 1) ω = A (tp i ω) * B i ω from iterZ_succ _ _, Matrix.SpecialLinearGroup.coe_mul]
    | pred i ih =>
      refine ((hAinv.comp (htp (-(i : ℤ) - 1))).mul ih).congr fun ω => ?_
      show (((A (tp (-(i : ℤ) - 1) ω))⁻¹ : SL2R) : M2R) * (B (-(i : ℤ)) ω : M2R) =
        (B (-(i : ℤ) - 1) ω : M2R)
      rw [show B (-(i : ℤ) - 1) ω = (A (tp (-(i : ℤ) - 1) ω))⁻¹ * B (-(i : ℤ)) ω from
        iterZ_pred _ _, Matrix.SpecialLinearGroup.coe_mul]
  -- the bound `Q`
  obtain ⟨Q1, hQ1⟩ := (isCompact_range hA).isBounded.exists_norm_le
  obtain ⟨Q2, hQ2⟩ := (isCompact_range hAinv).isBounded.exists_norm_le
  set Q := max (max Q1 Q2) 1
  have hQ : 1 ≤ Q := le_max_right _ _
  have hQA : ∀ ω, ‖(A ω : M2R)‖ ≤ Q := fun ω =>
    (hQ1 _ ⟨ω, rfl⟩).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hQAi : ∀ ω, ‖(((A ω)⁻¹ : SL2R) : M2R)‖ ≤ Q := fun ω =>
    (hQ2 _ ⟨ω, rfl⟩).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hBn : ∀ n ω, ‖(B n ω : M2R)‖ ≤ Q ^ n.natAbs := by
    intro n
    induction n using Int.induction_on with
    | zero => intro ω; rw [hB0, Matrix.SpecialLinearGroup.coe_one, norm_one]; simp
    | succ i ih =>
      intro ω
      rw [show B (i + 1) ω = A (tp i ω) * B i ω from iterZ_succ _ _, Matrix.SpecialLinearGroup.coe_mul,
        show ((i : ℤ) + 1).natAbs = i + 1 by omega, pow_succ']
      refine (norm_mul_le _ _).trans (mul_le_mul (hQA _) ?_ (norm_nonneg _) (by positivity))
      simpa using ih ω
    | pred i ih =>
      intro ω
      rw [show B (-(i : ℤ) - 1) ω = (A (tp (-(i : ℤ) - 1) ω))⁻¹ * B (-(i : ℤ)) ω from
        iterZ_pred _ _, Matrix.SpecialLinearGroup.coe_mul,
        show (-(i : ℤ) - 1).natAbs = i + 1 by omega, pow_succ']
      refine (norm_mul_le _ _).trans (mul_le_mul (hQAi _) ?_ (norm_nonneg _) (by positivity))
      simpa using ih ω
  have hBinv : ∀ m y, ‖(((B m y)⁻¹ : SL2R) : M2R)‖ ≤ Q ^ m.natAbs := by
    intro m y
    rw [show (B m y)⁻¹ = B (-m) (tp m y) from iterZ_inv m y]
    exact (hBn _ _).trans_eq (by rw [Int.natAbs_neg])
  -- Step 1: compactness
  set K : Set (X × EuclideanSpace ℝ (Fin 2)) := univ ×ˢ Metric.sphere 0 1
  have hK : IsCompact K := isCompact_univ.prod (isCompact_sphere 0 1)
  set U : ℤ × ℕ → Set (X × EuclideanSpace ℝ (Fin 2)) :=
    fun q => {p | 1 + 1 / ((q.2 : ℝ) + 1) < ‖act (B q.1 p.1 : M2R) p.2‖}
  have hUo : ∀ q, IsOpen (U q) := fun q =>
    isOpen_lt continuous_const (continuous_act ((hBc q.1).comp continuous_fst) continuous_snd).norm
  have hcov : K ⊆ ⋃ q, U q := by
    rintro ⟨ω, v⟩ ⟨-, hv⟩
    have hv1 : ‖v‖ = 1 := by simpa using hv
    have : ∃ n : ℤ, 1 < ‖act (B n ω : M2R) v‖ := by
      by_contra hc
      push Not at hc
      exact h ⟨ω, v, hv1, hc⟩
    obtain ⟨n, hn⟩ := this
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt (sub_pos.2 hn)
    exact mem_iUnion.2 ⟨(n, j), by simp only [U, mem_setOf_eq]; linarith⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hUo hcov
  set N : ℕ := t.sup (fun q => q.1.natAbs) + 1
  set J : ℕ := t.sup (fun q => q.2)
  set ε : ℝ := 1 / ((J : ℝ) + 1)
  have hε : 0 < ε := by positivity
  have hN1 : 1 ≤ N := by omega
  have hstep1 : ∀ ω (w : EuclideanSpace ℝ (Fin 2)), ∃ m : ℤ, |m| ≤ N ∧
      (w ≠ 0 → (1 + ε) * ‖w‖ ≤ ‖act (B m ω : M2R) w‖) := by
    intro ω w
    by_cases hw : w = 0
    · exact ⟨0, by simp, fun h => absurd hw h⟩
    have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
    set u := ‖w‖⁻¹ • w
    have hu : (ω, u) ∈ K := ⟨mem_univ _, by simp [u, norm_smul, hwpos.ne']⟩
    obtain ⟨q, hq, hpq⟩ := mem_iUnion₂.1 (ht hu)
    refine ⟨q.1, ?_, fun _ => ?_⟩
    · have h1 : q.1.natAbs ≤ t.sup (fun q : ℤ × ℕ => q.1.natAbs) :=
        Finset.le_sup (f := fun q : ℤ × ℕ => q.1.natAbs) hq
      rw [Int.abs_eq_natAbs]
      have : q.1.natAbs ≤ N := by omega
      exact_mod_cast this
    · have hJ : ε ≤ 1 / ((q.2 : ℝ) + 1) := by
        have h1 : q.2 ≤ J := Finset.le_sup (f := fun q : ℤ × ℕ => q.2) hq
        have h2 : (q.2 : ℝ) ≤ J := by exact_mod_cast h1
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      simp only [U, mem_setOf_eq] at hpq
      rw [act_smul, norm_smul, norm_inv, norm_norm] at hpq
      have h3 : ‖w‖ * (1 + 1 / ((q.2 : ℝ) + 1)) < ‖act (B q.1 ω : M2R) w‖ := by
        rw [lt_inv_mul_iff₀ hwpos] at hpq; exact hpq
      nlinarith
  choose mstep hmstep using hstep1
  -- Claim 1: the sequences
  set seq : X → EuclideanSpace ℝ (Fin 2) → ℕ → ℤ := fun ω v k =>
    Nat.rec (motive := fun _ => ℤ) 0 (fun _ sk => sk + mstep (tp sk ω) (act (B sk ω : M2R) v)) k
  have hseq0 : ∀ ω v, seq ω v 0 = 0 := fun _ _ => rfl
  have hseqs : ∀ ω v k, seq ω v (k + 1) =
      seq ω v k + mstep (tp (seq ω v k) ω) (act (B (seq ω v k) ω : M2R) v) := fun _ _ _ => rfl
  have hseq_step : ∀ ω v k, |seq ω v (k + 1) - seq ω v k| ≤ N := by
    intro ω v k
    rw [hseqs, add_sub_cancel_left]
    exact (hmstep _ _).1
  have hseq_grow : ∀ ω v, v ≠ 0 → ∀ k,
      (1 + ε) ^ k * ‖v‖ ≤ ‖act (B (seq ω v k) ω : M2R) v‖ := by
    intro ω v hv k
    induction k with
    | zero => rw [hseq0, hB0, Matrix.SpecialLinearGroup.coe_one, act_one]; simp
    | succ k ih =>
      set sk := seq ω v k
      set w := act (B sk ω : M2R) v
      have hw : w ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at ih
        have : 0 < (1 + ε) ^ k * ‖v‖ := by have := norm_pos_iff.2 hv; positivity
        linarith
      rw [hseqs, hBadd, Matrix.SpecialLinearGroup.coe_mul, act_mul]
      have := (hmstep (tp sk ω) w).2 hw
      calc (1 + ε) ^ (k + 1) * ‖v‖ = (1 + ε) * ((1 + ε) ^ k * ‖v‖) := by ring
        _ ≤ (1 + ε) * ‖w‖ := by gcongr
        _ ≤ _ := this
  have hP : ∀ ω v (p d : ℤ), ‖act (B p ω : M2R) v‖ * (Q ^ d.natAbs)⁻¹ ≤
      ‖act (B (p + d) ω : M2R) v‖ := by
    intro ω v p d
    rw [hBadd, Matrix.SpecialLinearGroup.coe_mul, act_mul]
    have h1 := norm_le_inv_mul_act (B d (tp p ω)) (act (B p ω : M2R) v)
    have h2 := hBinv d (tp p ω)
    have hQpos : 0 < Q ^ d.natAbs := by positivity
    rw [mul_inv_le_iff₀ hQpos]
    calc ‖act (B p ω : M2R) v‖
        ≤ ‖(((B d (tp p ω))⁻¹ : SL2R) : M2R)‖ * ‖act (B d (tp p ω) : M2R) (act (B p ω : M2R) v)‖ :=
          h1
      _ ≤ Q ^ d.natAbs * ‖act (B d (tp p ω) : M2R) (act (B p ω : M2R) v)‖ :=
          mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ = _ := mul_comm _ _
  have hup : ∀ ω v (n : ℤ), ‖act (B n ω : M2R) v‖ ≤ Q ^ n.natAbs * ‖v‖ := fun ω v n =>
    (norm_act_le _ _).trans (mul_le_mul_of_nonneg_right (hBn n ω) (norm_nonneg _))
  -- uniform sign change time
  obtain ⟨K0', hK0'⟩ := pow_unbounded_of_one_lt (Q ^ N) (by linarith : 1 < 1 + ε)
  set K0 := K0' + 1
  have hK0 : Q ^ N < (1 + ε) ^ K0 :=
    hK0'.trans_le (pow_le_pow_right₀ (by linarith) (by omega))
  have hsign : ∀ ω (v : EuclideanSpace ℝ (Fin 2)), ‖v‖ = 1 →
      (∀ k, K0 ≤ k → 0 < seq ω v k) ∨ (∀ k, K0 ≤ k → seq ω v k < 0) := by
    intro ω v hv
    have hv0 : v ≠ 0 := by intro h; rw [h, norm_zero] at hv; norm_num at hv
    have hbig : ∀ k, K0 ≤ k → (N : ℤ) < |seq ω v k| := by
      intro k hk
      by_contra hc
      push Not at hc
      have h1 := hseq_grow ω v hv0 k
      have h2 := hup ω v (seq ω v k)
      rw [hv, mul_one] at h1 h2
      rw [Int.abs_eq_natAbs] at hc
      have h3 : Q ^ (seq ω v k).natAbs ≤ Q ^ N := pow_le_pow_right₀ hQ (by exact_mod_cast hc)
      have h4 : (1 + ε) ^ K0 ≤ (1 + ε) ^ k := pow_le_pow_right₀ (by linarith) hk
      linarith
    by_cases hp : 0 < seq ω v K0
    · left
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => exact hp
      | succ k hk ih =>
        have hk' : (N : ℤ) < seq ω v k := by
          have := hbig k hk; rwa [abs_of_pos ih] at this
        have h2 := (abs_le.1 (hseq_step ω v k)).1
        linarith
    · right
      have hneg : seq ω v K0 < 0 := by
        have := hbig K0 le_rfl
        rcases lt_abs.1 this with h1 | h1
        · exfalso; exact hp (by linarith)
        · linarith
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => exact hneg
      | succ k hk ih =>
        have hk' : seq ω v k < -(N : ℤ) := by
          have := hbig k hk; rw [abs_of_neg ih] at this; linarith
        have h2 := (abs_le.1 (hseq_step ω v k)).2
        linarith
  -- the growth rate `λ`
  set l : ℝ := (1 + ε) ^ ((1 : ℝ) / N)
  have hl1 : 1 ≤ l := Real.one_le_rpow (by linarith) (by positivity)
  have hlN : l ^ N = 1 + ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), one_div_mul_cancel (by positivity),
      Real.rpow_one]
  have hlgt : 1 < l := by
    rcases eq_or_lt_of_le hl1 with h1 | h1
    · rw [← h1, one_pow] at hlN; linarith
    · exact h1
  set C0 := ((1 + ε) * Q ^ N)⁻¹
  have hC0 : 0 < C0 := by positivity
  have hC01 : C0 ≤ 1 := by
    apply inv_le_one_of_one_le₀
    have : 1 ≤ Q ^ N := one_le_pow₀ hQ
    nlinarith
  -- forward and backward estimates for unit vectors
  have hfwd : ∀ ω (v : EuclideanSpace ℝ (Fin 2)), ‖v‖ = 1 → (∀ k, K0 ≤ k → 0 < seq ω v k) →
      ∀ m : ℕ, K0 * N ≤ m → l ^ m * C0 ≤ ‖act (B m ω : M2R) v‖ := by
    intro ω v hv hpos m hm
    have hv0 : v ≠ 0 := by intro h; rw [h, norm_zero] at hv; norm_num at hv
    have ha0 : ‖act (B 0 ω : M2R) v‖ = 1 := by
      rw [hB0, Matrix.SpecialLinearGroup.coe_one, act_one, hv]
    have hg : ∀ k, (1 + ε) ^ k * ‖act (B 0 ω : M2R) v‖ ≤ ‖act (B (seq ω v k) ω : M2R) v‖ := by
      intro k; rw [ha0]; simpa [hv] using hseq_grow ω v hv0 k
    have hp1 : ∀ (p : ℤ) (j : ℕ), j ≤ N →
        ‖act (B p ω : M2R) v‖ * (Q ^ N)⁻¹ ≤ ‖act (B (p + j) ω : M2R) v‖ := by
      intro p j hj
      have h1 := hP ω v p j
      rw [Int.natAbs_natCast] at h1
      refine le_trans ?_ h1
      gcongr
    have hu : ∀ n : ℤ, ‖act (B n ω : M2R) v‖ ≤ Q ^ n.natAbs * ‖act (B 0 ω : M2R) v‖ := by
      intro n; rw [ha0, mul_one]; simpa [hv] using hup ω v n
    have := interp (fun n => ‖act (B n ω : M2R) v‖) hQ hε hl1 hlN (seq ω v) K0 (hseq0 ω v)
      (hseq_step ω v) hg hp1 hu hpos (by rw [ha0]; norm_num) m hm
    beta_reduce at this
    rw [ha0, mul_one] at this
    exact this
  have hbwd : ∀ ω (v : EuclideanSpace ℝ (Fin 2)), ‖v‖ = 1 → (∀ k, K0 ≤ k → seq ω v k < 0) →
      ∀ m : ℕ, K0 * N ≤ m → l ^ m * C0 ≤ ‖act (B (-(m : ℤ)) ω : M2R) v‖ := by
    intro ω v hv hneg m hm
    have hv0 : v ≠ 0 := by intro h; rw [h, norm_zero] at hv; norm_num at hv
    have ha0 : ‖act (B (-0) ω : M2R) v‖ = 1 := by
      rw [neg_zero, hB0, Matrix.SpecialLinearGroup.coe_one, act_one, hv]
    have hst : ∀ k, |(-seq ω v (k + 1)) - (-seq ω v k)| ≤ N := by
      intro k
      rw [show -seq ω v (k + 1) - -seq ω v k = -(seq ω v (k + 1) - seq ω v k) by ring, abs_neg]
      exact hseq_step ω v k
    have hg : ∀ k, (1 + ε) ^ k * ‖act (B (-0) ω : M2R) v‖ ≤
        ‖act (B (-(-seq ω v k)) ω : M2R) v‖ := by
      intro k; rw [ha0, neg_neg]; simpa [hv] using hseq_grow ω v hv0 k
    have hp1 : ∀ (p : ℤ) (j : ℕ), j ≤ N →
        ‖act (B (-p) ω : M2R) v‖ * (Q ^ N)⁻¹ ≤ ‖act (B (-(p + j)) ω : M2R) v‖ := by
      intro p j hj
      have h1 := hP ω v (-p) (-(j : ℤ))
      rw [Int.natAbs_neg, Int.natAbs_natCast] at h1
      rw [show -(p + (j : ℤ)) = -p + -(j : ℤ) by ring]
      refine le_trans ?_ h1
      gcongr
    have hu : ∀ n : ℤ, ‖act (B (-n) ω : M2R) v‖ ≤ Q ^ n.natAbs * ‖act (B (-0) ω : M2R) v‖ := by
      intro n; rw [ha0, mul_one]
      have := hup ω v (-n)
      rw [Int.natAbs_neg, hv, mul_one] at this
      exact this
    have := interp (fun n => ‖act (B (-n) ω : M2R) v‖) hQ hε hl1 hlN (fun k => -seq ω v k) K0
      (by simp [hseq0]) hst hg hp1 hu (fun k hk => by linarith [hneg k hk])
      (by rw [ha0]; norm_num) m hm
    beta_reduce at this
    rw [ha0, mul_one] at this
    exact this
  -- Claim 2: at every point there are forward and backward unit vectors
  have hexp : ∀ (M : SL2R) (m : ℕ), K0 * N ≤ m → 1 < l ^ m * C0 →
      (∀ v : EuclideanSpace ℝ (Fin 2), ‖v‖ = 1 → l ^ m * C0 ≤ ‖act (M : M2R) v‖) → False := by
    intro M m _ hgt hall
    refine not_expanding M hgt fun v => ?_
    by_cases hv : v = 0
    · simp [hv]
    have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
    have h1 := hall (‖v‖⁻¹ • v) (by simp [norm_smul, hvpos.ne'])
    rw [act_smul, norm_smul, norm_inv, norm_norm] at h1
    rw [le_inv_mul_iff₀ hvpos] at h1
    linarith
  obtain ⟨m0, hm0⟩ := pow_unbounded_of_one_lt C0⁻¹ hlgt
  set mbig := max m0 (K0 * N)
  have hmbig : 1 < l ^ mbig * C0 := by
    have : C0⁻¹ < l ^ mbig := hm0.trans_le (pow_le_pow_right₀ hl1 (le_max_left _ _))
    rw [inv_lt_iff_one_lt_mul₀ hC0] at this
    linarith [mul_comm C0 (l ^ mbig)]
  have hfex : ∀ ω, ∃ v : EuclideanSpace ℝ (Fin 2), ‖v‖ = 1 ∧ ∀ k, K0 ≤ k → 0 < seq ω v k := by
    intro ω
    by_contra hc
    push Not at hc
    have hb : ∀ v : EuclideanSpace ℝ (Fin 2), ‖v‖ = 1 → ∀ k, K0 ≤ k → seq ω v k < 0 :=
      fun v hv => (hsign ω v hv).resolve_left fun hf => by
        obtain ⟨k, hk, hk'⟩ := hc v hv
        exact absurd (hf k hk) (not_lt.2 hk')
    exact hexp (B (-(mbig : ℤ)) ω) mbig (le_max_right _ _) hmbig
      fun v hv => hbwd ω v hv (hb v hv) mbig (le_max_right _ _)
  have hbex : ∀ ω, ∃ v : EuclideanSpace ℝ (Fin 2), ‖v‖ = 1 ∧ ∀ k, K0 ≤ k → seq ω v k < 0 := by
    intro ω
    by_contra hc
    push Not at hc
    have hf : ∀ v : EuclideanSpace ℝ (Fin 2), ‖v‖ = 1 → ∀ k, K0 ≤ k → 0 < seq ω v k :=
      fun v hv => (hsign ω v hv).resolve_right fun hb => by
        obtain ⟨k, hk, hk'⟩ := hc v hv
        exact absurd (hb k hk) (not_lt.2 hk')
    exact hexp (B (mbig : ℤ) ω) mbig (le_max_right _ _) hmbig
      fun v hv => hfwd ω v hv (hf v hv) mbig (le_max_right _ _)
  -- conclusion
  have hlK : 1 ≤ l ^ (K0 * N) := one_le_pow₀ hl1
  refine ⟨C0 * (l ^ (K0 * N))⁻¹, by positivity, l, hlgt, fun n ω => ?_⟩
  have hgen : ∀ (m : ℕ) (M : SL2R), (K0 * N ≤ m → ∃ v : EuclideanSpace ℝ (Fin 2), ‖v‖ = 1 ∧
      l ^ m * C0 ≤ ‖act (M : M2R) v‖) → C0 * (l ^ (K0 * N))⁻¹ * l ^ m ≤ ‖(M : M2R)‖ := by
    intro m M hM
    by_cases hm : K0 * N ≤ m
    · obtain ⟨v, hv, hv'⟩ := hM hm
      have h1 := norm_act_le (M : M2R) v
      rw [hv, mul_one] at h1
      have h2 : C0 * (l ^ (K0 * N))⁻¹ * l ^ m ≤ l ^ m * C0 := by
        rw [mul_comm (l ^ m) C0]
        gcongr
        exact mul_le_of_le_one_right hC0.le (inv_le_one_of_one_le₀ hlK)
      linarith
    · have h1 : l ^ m ≤ l ^ (K0 * N) := pow_le_pow_right₀ hl1 (by omega)
      have h2 : C0 * (l ^ (K0 * N))⁻¹ * l ^ m ≤ C0 := by
        rw [mul_assoc]
        apply mul_le_of_le_one_right hC0.le
        rw [inv_mul_le_iff₀ (by positivity), mul_one]
        exact h1
      linarith [one_le_norm_SL2R M]
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [Int.natAbs_natCast]
    refine hgen m _ fun hm => ?_
    obtain ⟨v, hv, hpos⟩ := hfex ω
    exact ⟨v, hv, hfwd ω v hv hpos m hm⟩
  · rw [Int.natAbs_neg, Int.natAbs_natCast]
    refine hgen m _ fun hm => ?_
    obtain ⟨v, hv, hneg⟩ := hbex ω
    exact ⟨v, hv, hbwd ω v hv hneg m hm⟩

end Cocycle

end DF
