/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §3.8.1: uniform growth gives an invariant exponential splitting (Theorem 3.8.2, (a) ⇒ (b))

Main results:
* `DF.Cocycle.fwdBdd` — the subspace of vectors with bounded forward orbit at `ω`;
* `DF.Cocycle.stable_core` — under uniform exponential growth, `fwdBdd ω` is a nonzero proper
  subspace (hence a line), and its vectors decay exponentially with uniform constants;
* `DF.Cocycle.exists_stable_field` — the stable directions form a continuous invariant line
  field (continuity via the closed graph theorem for maps into a compact space);
* `DF.Cocycle.invExpSplitting_of_uniformExpGrowth` — **Theorem 3.8.2, (a) ⇒ (b)**; the unstable
  field is the stable field of the inverse cocycle `(T⁻¹, A(T⁻¹ ·)⁻¹)`;
* `DF.Cocycle.uniformHyperbolicityCharacterization` — **Theorem 3.8.2**, items (a)–(c):
  `DF.Cocycle.UniformHyperbolicityCharacterizationStatement`.

The proof of (a) ⇒ (b) is not the book's: we use the dichotomy
`DF.Cocycle.one_sided_growth_of_uniformExpGrowth` (every vector grows uniformly on one
half-line). A vector with bounded forward orbit cannot grow forward, so it is contracted
uniformly; small vectors for `A_n(ω)` (`n → ∞`) have orbits bounded on `[0, n]`, and a limit
point has a bounded forward orbit. Line fields are encoded by the projections `v vᵀ`.
-/
import DamanikFillman.Ch3.UHOpen
import DamanikFillman.Ch3.UHSplit

noncomputable section

set_option linter.unusedSectionVars false

open Filter Set Function Topology Matrix
open scoped Matrix.Norms.L2Operator

namespace DF

namespace Cocycle

local notation "R2" => EuclideanSpace ℝ (Fin 2)

/-! ### Rank-one projections -/

/-- The matrix `v vᵀ`. -/
def outer (v : R2) : M2R := Matrix.of fun i j => v i * v j

lemma norm_sq_fin2 (v : R2) : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs,
    sq_abs]

lemma act_outer (v w : R2) : act (outer v) w = (v 0 * w 0 + v 1 * w 1) • v := by
  ext i
  rw [act_apply]
  simp only [outer, Matrix.of_apply, PiLp.smul_apply, smul_eq_mul]
  ring

lemma isLineProj_outer {v : R2} (hv : ‖v‖ = 1) : IsLineProj (outer v) := by
  have h := norm_sq_fin2 v
  rw [hv] at h
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_two, outer, Matrix.of_apply]
    linear_combination (v i * v j) * h.symm
  · ext i j
    simp only [Matrix.transpose_apply, outer, Matrix.of_apply]
    ring
  · rw [Matrix.trace_fin_two]
    simp only [outer, Matrix.of_apply]
    linear_combination h.symm

lemma mem_lineOf_outer_iff {v : R2} (hv : ‖v‖ = 1) (w : R2) :
    w ∈ lineOf (outer v) ↔ ∃ c : ℝ, w = c • v := by
  constructor
  · intro hw
    exact ⟨_, (show act (outer v) w = w from hw).symm.trans (act_outer v w)⟩
  · rintro ⟨c, rfl⟩
    show act (outer v) (c • v) = c • v
    have h := norm_sq_fin2 v
    rw [hv] at h
    rw [act_outer]
    congr 1
    simp only [PiLp.smul_apply, smul_eq_mul]
    linear_combination c * h.symm

lemma outer_smul (c : ℝ) (v : R2) : outer (c • v) = (c ^ 2) • outer v := by
  ext i j
  simp only [outer, Matrix.of_apply, PiLp.smul_apply, smul_eq_mul, Matrix.smul_apply]
  ring

/-- A line projection fixing a unit vector `v` is `v vᵀ`. -/
lemma eq_outer_of_mem {P : M2R} (hP : IsLineProj P) {v : R2} (hv : ‖v‖ = 1)
    (hPv : v ∈ lineOf P) : P = outer v := by
  obtain ⟨-, hPT, htr⟩ := hP
  have h := norm_sq_fin2 v
  rw [hv] at h
  have h' : v 0 ^ 2 + v 1 ^ 2 = 1 := by linear_combination -h
  have e0 := congrArg (fun w : R2 => w 0) (show act P v = v from hPv)
  have e1 := congrArg (fun w : R2 => w 1) (show act P v = v from hPv)
  simp only [act_apply] at e0 e1
  have s : P 1 0 = P 0 1 := by
    have := congrFun (congrFun hPT 0) 1
    simpa [Matrix.transpose_apply] using this
  rw [s] at e1
  rw [Matrix.trace_fin_two] at htr
  have h00 : P 0 0 = v 0 * v 0 := by
    linear_combination v 0 * e0 - v 1 * e1 + v 1 ^ 2 * htr - P 0 0 * h'
  have h11 : P 1 1 = v 1 * v 1 := by
    linear_combination v 1 * e1 - v 0 * e0 + v 0 ^ 2 * htr - P 1 1 * h'
  have h01 : P 0 1 = v 0 * v 1 := by
    linear_combination v 1 * e0 + v 0 * e1 - v 0 * v 1 * htr - P 0 1 * h'
  have h10 : P 1 0 = v 1 * v 0 := by rw [s, h01]; ring
  ext i j
  fin_cases i <;> fin_cases j <;> simp [outer, h00, h01, h10, h11]

lemma exists_unit_mem_lineOf {P : M2R} (hP : IsLineProj P) :
    ∃ v : R2, ‖v‖ = 1 ∧ v ∈ lineOf P := by
  obtain ⟨v, hv0, hv⟩ := exists_ne_zero_mem_lineOf hP
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
  refine ⟨‖v‖⁻¹ • v, ?_, ?_⟩
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvpos.ne']
  · show act P (‖v‖⁻¹ • v) = ‖v‖⁻¹ • v
    rw [act_smul, show act P v = v from hv]

lemma IsLineProj.abs_le {P : M2R} (hP : IsLineProj P) (i j : Fin 2) : |P i j| ≤ 1 := by
  obtain ⟨v, hv1, hv⟩ := exists_unit_mem_lineOf hP
  rw [eq_outer_of_mem hP hv1 hv]
  simp only [outer, Matrix.of_apply, abs_mul]
  have hb : ∀ k : Fin 2, |v k| ≤ 1 := fun k => by
    rw [← Real.norm_eq_abs, ← hv1]; exact PiLp.norm_apply_le v k
  exact mul_le_one₀ (hb i) (abs_nonneg _) (hb j)

/-- The space of line projections. -/
def LP : Set M2R := {P | IsLineProj P}

lemma isCompact_LP : IsCompact LP := by
  have hK : IsCompact (Set.pi univ fun _ : Fin 2 => Set.pi univ fun _ : Fin 2 =>
      Icc (-1 : ℝ) 1 : Set M2R) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  have h1 : IsClosed {P : M2R | P * P = P} :=
    isClosed_eq (continuous_id.matrix_mul continuous_id) continuous_id
  have h2 : IsClosed {P : M2R | Pᵀ = P} := isClosed_eq continuous_id.matrix_transpose continuous_id
  have h3 : IsClosed {P : M2R | P.trace = 1} :=
    isClosed_eq continuous_id.matrix_trace continuous_const
  have hLP : IsClosed LP := by
    have : LP = {P : M2R | P * P = P} ∩ ({P : M2R | Pᵀ = P} ∩ {P : M2R | P.trace = 1}) := rfl
    rw [this]
    exact h1.inter (h2.inter h3)
  exact hK.of_isClosed_subset hLP fun P hP => Set.mem_univ_pi.2 fun i =>
    Set.mem_univ_pi.2 fun j => abs_le.1 (IsLineProj.abs_le hP i j)

/-! ### Iterates -/

variable {X : Type*} [MetricSpace X] [CompactSpace X]

lemma act_add' (B : M2R) (v w : R2) : act B (v + w) = act B v + act B w := by simp [act]

lemma act_zero' (B : M2R) : act B 0 = 0 := by simp [act]

lemma tpow_symm {Ω : Type*} (T : Ω ≃ Ω) (n : ℤ) (x : Ω) : tpow T.symm n x = tpow T (-n) x := by
  show ⇑(((T : Equiv.Perm Ω))⁻¹ ^ n) x = ⇑((T : Equiv.Perm Ω) ^ (-n)) x
  rw [inv_zpow']

lemma tpow_one_apply {Ω : Type*} (T : Ω ≃ Ω) (x : Ω) : tpow T 1 x = T x := by
  have := tpow_add_one (T := T) 0 x
  rwa [zero_add, tpow_zero] at this

lemma iterZ_one_apply {Ω R : Type*} [Group R] (T : Ω ≃ Ω) (A : Ω → R) (x : Ω) :
    iterZ T A 1 x = A x := by
  have := iterZ_succ (T := T) (A := A) 0 x
  rwa [zero_add, iterZ_zero, mul_one, tpow_zero] at this

/-- The iterates of the inverse cocycle `(T⁻¹, A(T⁻¹ ·)⁻¹)` are the backward iterates. -/
lemma iterZ_symm {Ω R : Type*} [Group R] (T : Ω ≃ Ω) (A : Ω → R) (n : ℤ) (ω : Ω) :
    iterZ T.symm (fun x => (A (T.symm x))⁻¹) n ω = iterZ T A (-n) ω := by
  induction n using Int.induction_on with
  | zero => simp only [neg_zero, iterZ_zero]
  | succ i ih =>
    rw [iterZ_succ, ih, show -((i : ℤ) + 1) = -(i : ℤ) - 1 by ring, iterZ_pred, tpow_symm,
      tpow_sub_one]
  | pred i ih =>
    rw [iterZ_pred, ih, tpow_symm, show -(-(i : ℤ) - 1) = (i : ℤ) + 1 by ring, neg_neg,
      iterZ_succ, tpow_add_one]
    simp only [Equiv.symm_apply_apply, inv_inv]

lemma act_iterZ_add (T : X ≃ₜ X) (A : X → SL2R) (n m : ℤ) (ω : X) (v : R2) :
    act ((iterZ T.toEquiv A (n + m) ω : SL2R) : M2R) v =
      act ((iterZ T.toEquiv A m (tpow T.toEquiv n ω) : SL2R) : M2R)
        (act ((iterZ T.toEquiv A n ω : SL2R) : M2R) v) := by
  rw [iterZ_add, Matrix.SpecialLinearGroup.coe_mul, act_mul]

lemma act_iterZ_inv (T : X ≃ₜ X) (A : X → SL2R) (n : ℤ) (ω : X) (v : R2) :
    act ((iterZ T.toEquiv A (-n) (tpow T.toEquiv n ω) : SL2R) : M2R)
      (act ((iterZ T.toEquiv A n ω : SL2R) : M2R) v) = v := by
  rw [← act_iterZ_add, add_neg_cancel, iterZ_zero, Matrix.SpecialLinearGroup.coe_one, act_one]

lemma continuous_iterZ (T : X ≃ₜ X) (A : X → SL2R) (hA : Continuous fun ω => (A ω : M2R))
    (n : ℤ) : Continuous fun ω => ((iterZ T.toEquiv A n ω : SL2R) : M2R) := by
  set B : ℤ → X → SL2R := fun n ω => iterZ T.toEquiv A n ω with hBdef
  set tp := tpow T.toEquiv
  have hB0 : ∀ ω, B 0 ω = 1 := fun ω => rfl
  have htp : ∀ n, Continuous (tp n) := by
    intro n
    induction n using Int.induction_on with
    | zero => exact continuous_id.congr fun x => (tpow_zero x).symm
    | succ i ih => exact (T.continuous.comp ih).congr fun x => (tpow_add_one (i : ℤ) x).symm
    | pred i ih =>
      exact (T.symm.continuous.comp ih).congr fun x => (tpow_sub_one (-(i : ℤ)) x).symm
  have hAinv : Continuous fun ω => (((A ω)⁻¹ : SL2R) : M2R) := by
    simp_rw [Matrix.SpecialLinearGroup.coe_inv, adjugate_eq_trace]
    exact (hA.matrix_trace.smul continuous_const).sub hA
  show Continuous fun ω => (B n ω : M2R)
  induction n using Int.induction_on with
  | zero => exact continuous_const.congr fun ω => by rw [hB0, Matrix.SpecialLinearGroup.coe_one]
  | succ i ih =>
    refine ((hA.comp (htp i)).mul ih).congr fun ω => ?_
    show (A (tp i ω) : M2R) * (B i ω : M2R) = (B (i + 1) ω : M2R)
    rw [show B (i + 1) ω = A (tp i ω) * B i ω from iterZ_succ _ _,
      Matrix.SpecialLinearGroup.coe_mul]
  | pred i ih =>
    refine ((hAinv.comp (htp (-(i : ℤ) - 1))).mul ih).congr fun ω => ?_
    show (((A (tp (-(i : ℤ) - 1) ω))⁻¹ : SL2R) : M2R) * (B (-(i : ℤ)) ω : M2R) =
      (B (-(i : ℤ) - 1) ω : M2R)
    rw [show B (-(i : ℤ) - 1) ω = (A (tp (-(i : ℤ) - 1) ω))⁻¹ * B (-(i : ℤ)) ω from
      iterZ_pred _ _, Matrix.SpecialLinearGroup.coe_mul]

lemma exists_norm_iterZ_le (T : X ≃ₜ X) (A : X → SL2R) (hA : Continuous fun ω => (A ω : M2R)) :
    ∃ Q : ℝ, 1 ≤ Q ∧ ∀ (n : ℤ) (ω : X),
      ‖((iterZ T.toEquiv A n ω : SL2R) : M2R)‖ ≤ Q ^ n.natAbs := by
  set B : ℤ → X → SL2R := fun n ω => iterZ T.toEquiv A n ω with hBdef
  set tp := tpow T.toEquiv
  have hB0 : ∀ ω, B 0 ω = 1 := fun ω => rfl
  have hAinv : Continuous fun ω => (((A ω)⁻¹ : SL2R) : M2R) := by
    simp_rw [Matrix.SpecialLinearGroup.coe_inv, adjugate_eq_trace]
    exact (hA.matrix_trace.smul continuous_const).sub hA
  obtain ⟨Q1, hQ1⟩ := (isCompact_range hA).isBounded.exists_norm_le
  obtain ⟨Q2, hQ2⟩ := (isCompact_range hAinv).isBounded.exists_norm_le
  set Q := max (max Q1 Q2) 1
  have hQ : 1 ≤ Q := le_max_right _ _
  have hQA : ∀ ω, ‖(A ω : M2R)‖ ≤ Q := fun ω =>
    (hQ1 _ ⟨ω, rfl⟩).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hQAi : ∀ ω, ‖(((A ω)⁻¹ : SL2R) : M2R)‖ ≤ Q := fun ω =>
    (hQ2 _ ⟨ω, rfl⟩).trans ((le_max_right _ _).trans (le_max_left _ _))
  refine ⟨Q, hQ, fun n => ?_⟩
  show ∀ ω, ‖(B n ω : M2R)‖ ≤ Q ^ n.natAbs
  induction n using Int.induction_on with
  | zero => intro ω; rw [hB0, Matrix.SpecialLinearGroup.coe_one, norm_one]; simp
  | succ i ih =>
    intro ω
    rw [show B (i + 1) ω = A (tp i ω) * B i ω from iterZ_succ _ _,
      Matrix.SpecialLinearGroup.coe_mul, show ((i : ℤ) + 1).natAbs = i + 1 by omega, pow_succ']
    refine (norm_mul_le _ _).trans (mul_le_mul (hQA _) ?_ (norm_nonneg _) (by positivity))
    simpa using ih ω
  | pred i ih =>
    intro ω
    rw [show B (-(i : ℤ) - 1) ω = (A (tp (-(i : ℤ) - 1) ω))⁻¹ * B (-(i : ℤ)) ω from
      iterZ_pred _ _, Matrix.SpecialLinearGroup.coe_mul,
      show (-(i : ℤ) - 1).natAbs = i + 1 by omega, pow_succ']
    refine (norm_mul_le _ _).trans (mul_le_mul (hQAi _) ?_ (norm_nonneg _) (by positivity))
    simpa using ih ω

/-- Every element of `SL(2, ℝ)` has a unit vector which it does not expand. -/
lemma exists_unit_small (M : SL2R) : ∃ u : R2, ‖u‖ = 1 ∧ ‖act (M : M2R) u‖ ≤ 1 := by
  have hc : Continuous fun x : R2 => ‖act (M : M2R) x‖ :=
    (continuous_act (f := fun _ : R2 => (M : M2R)) continuous_const continuous_id).norm
  obtain ⟨u, hu, hmin⟩ := (isCompact_sphere (0 : R2) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.2 zero_le_one) hc.continuousOn
  have hu1 : ‖u‖ = 1 := mem_sphere_zero_iff_norm.1 hu
  refine ⟨u, hu1, ?_⟩
  by_contra hlt
  push_neg at hlt
  refine not_expanding M hlt fun v => ?_
  rcases eq_or_ne v 0 with rfl | hv
  · simp [act]
  · have hvpos := norm_pos_iff.2 hv
    have h1 : ‖‖v‖⁻¹ • v‖ = 1 := by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvpos.ne']
    have : ‖act (M : M2R) u‖ ≤ ‖act (M : M2R) (‖v‖⁻¹ • v)‖ :=
      isMinOn_iff.1 hmin _ (mem_sphere_zero_iff_norm.2 h1)
    rw [act_smul, norm_smul, norm_inv, norm_norm] at this
    calc ‖act (M : M2R) u‖ * ‖v‖ ≤ ‖v‖⁻¹ * ‖act (M : M2R) v‖ * ‖v‖ := by gcongr
      _ = ‖act (M : M2R) v‖ := by field_simp

/-! ### The forward-bounded subspace -/

/-- The vectors at `ω` with bounded forward orbit. -/
def fwdBdd (T : X ≃ₜ X) (A : X → SL2R) (ω : X) : Submodule ℝ R2 where
  carrier := {v | ∃ M, ∀ m : ℕ, ‖act ((iterZ T.toEquiv A m ω : SL2R) : M2R) v‖ ≤ M}
  add_mem' := by
    rintro v w ⟨M, hM⟩ ⟨N, hN⟩
    refine ⟨M + N, fun m => ?_⟩
    rw [act_add']
    exact (norm_add_le _ _).trans (add_le_add (hM m) (hN m))
  zero_mem' := ⟨0, fun m => by rw [act_zero', norm_zero]⟩
  smul_mem' := by
    rintro c v ⟨M, hM⟩
    refine ⟨‖c‖ * M, fun m => ?_⟩
    rw [act_smul, norm_smul]
    exact mul_le_mul_of_nonneg_left (hM m) (norm_nonneg _)

lemma mem_fwdBdd {T : X ≃ₜ X} {A : X → SL2R} {ω : X} {v : R2} :
    v ∈ fwdBdd T A ω ↔ ∃ M, ∀ m : ℕ, ‖act ((iterZ T.toEquiv A m ω : SL2R) : M2R) v‖ ≤ M :=
  Iff.rfl

lemma mem_fwdBdd_shift (T : X ≃ₜ X) (A : X → SL2R) (ω : X) (v : R2) :
    act (A ω : M2R) v ∈ fwdBdd T A (T ω) ↔ v ∈ fwdBdd T A ω := by
  have key : ∀ m : ℕ, act ((iterZ T.toEquiv A ((m + 1 : ℕ) : ℤ) ω : SL2R) : M2R) v =
      act ((iterZ T.toEquiv A m (T ω) : SL2R) : M2R) (act (A ω : M2R) v) := by
    intro m
    rw [show ((m + 1 : ℕ) : ℤ) = 1 + (m : ℤ) by push_cast; ring, act_iterZ_add,
      iterZ_one_apply, tpow_one_apply]
    try rfl
  rw [mem_fwdBdd, mem_fwdBdd]
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨max ‖v‖ M, fun m => ?_⟩
    cases m with
    | zero =>
      rw [Nat.cast_zero, iterZ_zero, Matrix.SpecialLinearGroup.coe_one, act_one]
      exact le_max_left _ _
    | succ m => rw [key]; exact (hM m).trans (le_max_right _ _)
  · rintro ⟨M, hM⟩
    exact ⟨M, fun m => by rw [← key]; exact hM _⟩

/-- Under uniform exponential growth, `fwdBdd ω` is nonzero, proper, and uniformly contracted. -/
theorem stable_core (T : X ≃ₜ X) (A : X → SL2R) (hA : Continuous fun ω => (A ω : M2R))
    (h : UniformExpGrowth T A) :
    ∃ c > (0 : ℝ), ∃ l > (1 : ℝ), ∀ ω : X,
      (∀ v ∈ fwdBdd T A ω, ∀ m : ℕ,
        ‖act ((iterZ T.toEquiv A m ω : SL2R) : M2R) v‖ ≤ c * l⁻¹ ^ m * ‖v‖) ∧
      (∃ s : R2, ‖s‖ = 1 ∧ s ∈ fwdBdd T A ω) ∧ fwdBdd T A ω ≠ ⊤ := by
  obtain ⟨C0, hC0, l, hl, M0, hos⟩ := one_sided_growth_of_uniformExpGrowth T A hA h
  obtain ⟨Q, hQ1, hQ⟩ := exists_norm_iterZ_le T A hA
  set c := max C0⁻¹ ((Q * l) ^ M0) with hcdef
  have hc : 0 < c := lt_max_of_lt_left (inv_pos.2 hC0)
  have hl0 : 0 < l := by linarith
  have hfw : ∀ (m : ℕ) ω v, ‖act ((iterZ T.toEquiv A m ω : SL2R) : M2R) v‖ ≤ Q ^ m * ‖v‖ :=
    fun m ω v => (norm_act_le _ _).trans
      (mul_le_mul_of_nonneg_right ((hQ m ω).trans_eq (by rw [Int.natAbs_natCast]))
        (norm_nonneg _))
  have hbw : ∀ (k : ℕ) ω w,
      ‖w‖ ≤ Q ^ k * ‖act ((iterZ T.toEquiv A k ω : SL2R) : M2R) w‖ := by
    intro k ω w
    calc ‖w‖ = ‖act ((iterZ T.toEquiv A (-(k : ℤ)) (tpow T.toEquiv k ω) : SL2R) : M2R)
          (act ((iterZ T.toEquiv A k ω : SL2R) : M2R) w)‖ := by rw [act_iterZ_inv]
      _ ≤ _ := norm_act_le _ _
      _ ≤ Q ^ k * ‖act ((iterZ T.toEquiv A k ω : SL2R) : M2R) w‖ :=
          mul_le_mul_of_nonneg_right
            ((hQ _ _).trans_eq (by rw [Int.natAbs_neg, Int.natAbs_natCast])) (norm_nonneg _)
  -- from `l ^ m C0 ‖w‖ ≤ 1` (or `≤ ‖v‖`)
  have hsmall : ∀ (m : ℕ) (x y : ℝ), 0 ≤ x → l ^ m * C0 * x ≤ y → x ≤ C0⁻¹ * l⁻¹ ^ m * y := by
    intro m x y _ hxy
    have hpos : 0 < l ^ m * C0 := by positivity
    calc x = (l ^ m * C0)⁻¹ * (l ^ m * C0 * x) := by
          rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
      _ ≤ (l ^ m * C0)⁻¹ * y := by gcongr
      _ = C0⁻¹ * l⁻¹ ^ m * y := by rw [mul_inv, inv_pow]; ring
  -- decay
  have hdecay : ∀ ω, ∀ v ∈ fwdBdd T A ω, ∀ m : ℕ,
      ‖act ((iterZ T.toEquiv A m ω : SL2R) : M2R) v‖ ≤ c * l⁻¹ ^ m * ‖v‖ := by
    intro ω v hv m
    obtain ⟨M, hM⟩ := mem_fwdBdd.1 hv
    have hll : l ^ m * l⁻¹ ^ m = 1 := by rw [← mul_pow, mul_inv_cancel₀ hl0.ne', one_pow]
    rcases lt_or_ge m M0 with hm | hm
    · calc ‖act ((iterZ T.toEquiv A m ω : SL2R) : M2R) v‖ ≤ Q ^ m * ‖v‖ := hfw m ω v
        _ = (Q * l) ^ m * l⁻¹ ^ m * ‖v‖ := by
          rw [mul_pow, mul_assoc (Q ^ m) (l ^ m), hll, mul_one]
        _ ≤ c * l⁻¹ ^ m * ‖v‖ := by
          gcongr
          exact (pow_le_pow_right₀ (by nlinarith) hm.le).trans (le_max_right _ _)
    · set ω' := tpow T.toEquiv m ω with hω'
      set w := act ((iterZ T.toEquiv A m ω : SL2R) : M2R) v with hw
      rcases eq_or_ne w 0 with h0 | h0
      · rw [h0, norm_zero]; positivity
      rcases hos ω' w with hF | hB
      · exfalso
        have hwpos := norm_pos_iff.2 h0
        obtain ⟨j, hjM, hj⟩ := (((tendsto_pow_atTop_atTop_of_one_lt hl).eventually_gt_atTop
          (M / (C0 * ‖w‖))).and (eventually_ge_atTop M0)).exists
        have h1 := hF j hj
        have h2 : act ((iterZ T.toEquiv A j ω' : SL2R) : M2R) w =
            act ((iterZ T.toEquiv A ((m + j : ℕ) : ℤ) ω : SL2R) : M2R) v := by
          rw [hw, Nat.cast_add, act_iterZ_add]
        rw [h2] at h1
        have h3 := hM (m + j)
        rw [div_lt_iff₀ (by positivity)] at hjM
        nlinarith
      · have h1 := hB m hm
        have hinv : act ((iterZ T.toEquiv A (-(m : ℤ)) ω' : SL2R) : M2R) w = v :=
          act_iterZ_inv T A m ω v
        rw [hinv] at h1
        exact (hsmall m _ _ (norm_nonneg _) h1).trans (by gcongr; exact le_max_left _ _)
  -- existence of a bounded forward orbit
  have hex : ∀ ω, ∃ s : R2, ‖s‖ = 1 ∧ s ∈ fwdBdd T A ω := by
    intro ω
    set K := max C0⁻¹ (Q ^ M0)
    choose u hu1 hu using fun n : ℕ => exists_unit_small (iterZ T.toEquiv A n ω)
    have hCK : ∀ x : ℝ, 0 ≤ x → C0 * x ≤ 1 → x ≤ K := by
      intro x hx hCx
      calc x = C0⁻¹ * (C0 * x) := by rw [← mul_assoc, inv_mul_cancel₀ hC0.ne', one_mul]
        _ ≤ C0⁻¹ * 1 := by gcongr
        _ = C0⁻¹ := mul_one _
        _ ≤ K := le_max_left _ _
    have hK : ∀ n m : ℕ, m ≤ n → ‖act ((iterZ T.toEquiv A m ω : SL2R) : M2R) (u n)‖ ≤ K := by
      intro n m hmn
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
      set w := act ((iterZ T.toEquiv A m ω : SL2R) : M2R) (u (m + k)) with hw
      have hwk : act ((iterZ T.toEquiv A k (tpow T.toEquiv m ω) : SL2R) : M2R) w =
          act ((iterZ T.toEquiv A ((m + k : ℕ) : ℤ) ω : SL2R) : M2R) (u (m + k)) := by
        rw [hw, Nat.cast_add, act_iterZ_add]
      have hsm := hu (m + k)
      rcases hos (tpow T.toEquiv m ω) w with hF | hB
      · rcases lt_or_ge k M0 with hk | hk
        · calc ‖w‖ ≤ Q ^ k *
                ‖act ((iterZ T.toEquiv A k (tpow T.toEquiv m ω) : SL2R) : M2R) w‖ := hbw k _ w
            _ ≤ Q ^ k * 1 := by rw [hwk]; exact mul_le_mul_of_nonneg_left hsm (by positivity)
            _ ≤ Q ^ M0 := by rw [mul_one]; exact pow_le_pow_right₀ hQ1 hk.le
            _ ≤ K := le_max_right _ _
        · have h1 := hF k hk
          rw [hwk] at h1
          have hlk : 1 ≤ l ^ k := one_le_pow₀ hl.le
          have := mul_le_mul_of_nonneg_right hlk (by positivity : 0 ≤ C0 * ‖w‖)
          exact hCK _ (norm_nonneg _) (by nlinarith)
      · rcases lt_or_ge m M0 with hm | hm
        · calc ‖w‖ ≤ Q ^ m * ‖u (m + k)‖ := hfw m ω _
            _ = Q ^ m := by rw [hu1, mul_one]
            _ ≤ Q ^ M0 := pow_le_pow_right₀ hQ1 hm.le
            _ ≤ K := le_max_right _ _
        · have h1 := hB m hm
          have hinv : act ((iterZ T.toEquiv A (-(m : ℤ)) (tpow T.toEquiv m ω) : SL2R) : M2R) w =
              u (m + k) := act_iterZ_inv T A m ω _
          rw [hinv, hu1] at h1
          have hlk : 1 ≤ l ^ m := one_le_pow₀ hl.le
          have := mul_le_mul_of_nonneg_right hlk (by positivity : 0 ≤ C0 * ‖w‖)
          exact hCK _ (norm_nonneg _) (by nlinarith)
    obtain ⟨a, ha, φ, hφ, hlim⟩ := (isCompact_sphere (0 : R2) 1).tendsto_subseq
      (fun n => mem_sphere_zero_iff_norm.2 (hu1 n))
    refine ⟨a, mem_sphere_zero_iff_norm.1 ha, mem_fwdBdd.2 ⟨K, fun m => ?_⟩⟩
    have hcont : Continuous fun x : R2 => ‖act ((iterZ T.toEquiv A m ω : SL2R) : M2R) x‖ :=
      (continuous_act (f := fun _ : R2 => ((iterZ T.toEquiv A m ω : SL2R) : M2R))
        continuous_const continuous_id).norm
    refine le_of_tendsto ((hcont.tendsto a).comp hlim) ?_
    filter_upwards [eventually_ge_atTop m] with k hk
    exact hK _ _ (hk.trans (hφ.id_le k))
  -- `fwdBdd ω` is proper
  have hntop : ∀ ω, fwdBdd T A ω ≠ ⊤ := by
    intro ω htop
    obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hc) (inv_lt_one_of_one_lt₀ hl)
    have hb : ‖((iterZ T.toEquiv A m ω : SL2R) : M2R)‖ ≤ c * l⁻¹ ^ m := by
      show ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) ((iterZ T.toEquiv A m ω : SL2R) : M2R)‖
        ≤ c * l⁻¹ ^ m
      refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
      exact hdecay ω w (by rw [htop]; exact Submodule.mem_top) m
    have h1 := one_le_norm_SL2R (iterZ T.toEquiv A m ω)
    have h2 : c * l⁻¹ ^ m < c * c⁻¹ := mul_lt_mul_of_pos_left hm hc
    rw [mul_inv_cancel₀ hc.ne'] at h2
    linarith
  exact ⟨c, hc, l, hl, fun ω => ⟨hdecay ω, hex ω, hntop ω⟩⟩

/-- A nonzero proper subspace of `ℝ²` is a line. -/
lemma exists_smul_of_ne_top {S : Submodule ℝ R2} (hbot : ∃ s : R2, ‖s‖ = 1 ∧ s ∈ S)
    (htop : S ≠ ⊤) : ∀ s ∈ S, s ≠ 0 → ∀ w ∈ S, ∃ c : ℝ, w = c • s := by
  have hle : Module.finrank ℝ S ≤ 2 :=
    (Submodule.finrank_le S).trans_eq finrank_euclideanSpace_fin
  have h0 : Module.finrank ℝ S ≠ 0 := by
    rw [Ne, Submodule.finrank_eq_zero]
    rintro rfl
    obtain ⟨s, hs1, hs⟩ := hbot
    rw [Submodule.mem_bot] at hs
    rw [hs, norm_zero] at hs1
    exact zero_ne_one hs1
  have h2 : Module.finrank ℝ S ≠ 2 := by
    intro h2
    exact htop (Submodule.eq_top_of_finrank_eq (by rw [h2, finrank_euclideanSpace_fin]))
  have h1 : Module.finrank ℝ S = 1 := by omega
  intro s hs hs0 w hw
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (⟨s, hs⟩ : S)
    (by simpa using hs0)).1 h1 ⟨w, hw⟩
  exact ⟨c, by simpa using (congrArg Subtype.val hc).symm⟩

/-- The stable line field of a uniformly hyperbolic cocycle: continuous, invariant, and
uniformly contracted in forward time. -/
theorem exists_stable_field (T : X ≃ₜ X) (A : X → SL2R) (hA : Continuous fun ω => (A ω : M2R))
    (h : UniformExpGrowth T A) :
    ∃ c > (0 : ℝ), ∃ L > (1 : ℝ), ∃ P : X → M2R, Continuous P ∧ (∀ ω, IsLineProj (P ω)) ∧
      (∀ ω v, act (A ω : M2R) v ∈ lineOf (P (T ω)) ↔ v ∈ lineOf (P ω)) ∧
      (∀ (n : ℕ) (ω : X), ∀ v ∈ lineOf (P ω),
        ‖act ((iterZ T.toEquiv A n ω : SL2R) : M2R) v‖ ≤ c * L⁻¹ ^ n * ‖v‖) := by
  obtain ⟨c, hc, l, hl, H⟩ := stable_core T A hA h
  have hline : ∀ ω, ∀ s ∈ fwdBdd T A ω, s ≠ 0 → ∀ w ∈ fwdBdd T A ω, ∃ a : ℝ, w = a • s :=
    fun ω => exists_smul_of_ne_top (H ω).2.1 (H ω).2.2
  have hdec_iff : ∀ ω v, v ∈ fwdBdd T A ω ↔
      ∀ m : ℕ, ‖act ((iterZ T.toEquiv A m ω : SL2R) : M2R) v‖ ≤ c * l⁻¹ ^ m * ‖v‖ := by
    intro ω v
    refine ⟨fun hv => (H ω).1 v hv, fun hd => mem_fwdBdd.2 ⟨c * ‖v‖, fun m => (hd m).trans ?_⟩⟩
    have : l⁻¹ ^ m ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hl.le)
    calc c * l⁻¹ ^ m * ‖v‖ ≤ c * 1 * ‖v‖ := by gcongr
      _ = c * ‖v‖ := by ring
  choose s hs1 hs using fun ω => (H ω).2.1
  have hs0 : ∀ ω, s ω ≠ 0 := fun ω h0 => by
    have := hs1 ω
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have hlineP : ∀ ω v, v ∈ lineOf (outer (s ω)) ↔ v ∈ fwdBdd T A ω := by
    intro ω v
    rw [mem_lineOf_outer_iff (hs1 ω)]
    constructor
    · rintro ⟨a, rfl⟩
      exact Submodule.smul_mem _ a (hs ω)
    · intro hv
      exact hline ω (s ω) (hs ω) (hs0 ω) v hv
  let g : X → LP := fun ω => ⟨outer (s ω), isLineProj_outer (hs1 ω)⟩
  have hgraph : ∀ ω (P : LP), g ω = P ↔ ∀ e : R2, ∀ m : ℕ,
      ‖act ((iterZ T.toEquiv A m ω : SL2R) : M2R) (act (P : M2R) e)‖ ≤
        c * l⁻¹ ^ m * ‖act (P : M2R) e‖ := by
    intro ω P
    constructor
    · rintro rfl e m
      show ‖act ((iterZ T.toEquiv A m ω : SL2R) : M2R) (act (outer (s ω)) e)‖ ≤
        c * l⁻¹ ^ m * ‖act (outer (s ω)) e‖
      refine (hdec_iff ω _).1 ?_ m
      rw [act_outer]
      exact Submodule.smul_mem _ _ (hs ω)
    · intro hP
      apply Subtype.ext
      show outer (s ω) = (P : M2R)
      obtain ⟨v, hv1, hv⟩ := exists_unit_mem_lineOf (show IsLineProj (P : M2R) from P.2)
      have hvS : v ∈ fwdBdd T A ω := (hdec_iff ω v).2 fun m => by
        have := hP v m
        rwa [show act (P : M2R) v = v from hv] at this
      obtain ⟨a, rfl⟩ := hline ω (s ω) (hs ω) (hs0 ω) v hvS
      rw [eq_outer_of_mem (show IsLineProj (P : M2R) from P.2) hv1 hv, outer_smul]
      have ha : a ^ 2 = 1 := by
        rw [norm_smul, hs1, mul_one, Real.norm_eq_abs] at hv1
        rw [← sq_abs, hv1, one_pow]
      rw [ha, one_smul]
  have hG : IsClosed (⋂ (e : R2), ⋂ (m : ℕ), {p : X × LP |
      ‖act ((iterZ T.toEquiv A m p.1 : SL2R) : M2R) (act (p.2 : M2R) e)‖ ≤
        c * l⁻¹ ^ m * ‖act (p.2 : M2R) e‖}) := by
    refine isClosed_iInter fun e => isClosed_iInter fun m => isClosed_le ?_ ?_
    · exact (continuous_act ((continuous_iterZ T A hA m).comp continuous_fst)
        (continuous_act (continuous_subtype_val.comp continuous_snd) continuous_const)).norm
    · exact continuous_const.mul
        (continuous_act (continuous_subtype_val.comp continuous_snd) continuous_const).norm
  have hgr : Function.graph g = ⋂ (e : R2), ⋂ (m : ℕ), {p : X × LP |
      ‖act ((iterZ T.toEquiv A m p.1 : SL2R) : M2R) (act (p.2 : M2R) e)‖ ≤
        c * l⁻¹ ^ m * ‖act (p.2 : M2R) e‖} := by
    ext ⟨ω, P⟩
    simp only [mem_iInter, mem_setOf_eq]
    exact hgraph ω P
  haveI : CompactSpace LP := isCompact_iff_compactSpace.mp isCompact_LP
  have hgc : Continuous g := continuous_of_isClosed_graph (by rw [hgr]; exact hG)
  refine ⟨c, hc, l, hl, fun ω => outer (s ω), continuous_subtype_val.comp hgc,
    fun ω => isLineProj_outer (hs1 ω), fun ω v => ?_, fun n ω v hv => ?_⟩
  · rw [hlineP, hlineP]
    exact mem_fwdBdd_shift T A ω v
  · exact (hdec_iff ω v).1 ((hlineP ω v).1 hv) n

lemma const_mono {c1 c L1 L : ℝ} (hc1 : 0 ≤ c1) (hc : c1 ≤ c) (hL : 0 < L) (hLL : L ≤ L1)
    (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : c1 * L1⁻¹ ^ n * x ≤ c * L⁻¹ ^ n * x := by
  have h1 : L1⁻¹ ≤ L⁻¹ := inv_anti₀ hL hLL
  have h0 : 0 ≤ L1⁻¹ := inv_nonneg.2 (hL.le.trans hLL)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hc (pow_le_pow_left₀ h0 h1 n) (pow_nonneg h0 n) (hc1.trans hc)) hx

/-- **Theorem 3.8.2, (a) ⇒ (b)**: uniform exponential growth gives an invariant exponential
splitting. -/
theorem invExpSplitting_of_uniformExpGrowth (T : X ≃ₜ X) (A : X → SL2R)
    (hA : Continuous fun ω => (A ω : M2R)) (h : UniformExpGrowth T A) : InvExpSplitting T A := by
  obtain ⟨c1, hc1, L1, hL1, Ps, hPsc, hPs, hinvs, hs⟩ := exists_stable_field T A hA h
  obtain ⟨A', hA'def⟩ : ∃ A' : X → SL2R, A' = fun ω => (A (T.symm ω))⁻¹ := ⟨_, rfl⟩
  have hA' : Continuous fun ω => (A' ω : M2R) := by
    have hAinv : Continuous fun ω => (((A ω)⁻¹ : SL2R) : M2R) := by
      simp_rw [Matrix.SpecialLinearGroup.coe_inv, adjugate_eq_trace]
      exact (hA.matrix_trace.smul continuous_const).sub hA
    rw [hA'def]
    exact hAinv.comp T.symm.continuous
  have hiter : ∀ (n : ℤ) ω, iterZ T.symm.toEquiv A' n ω = iterZ T.toEquiv A (-n) ω := by
    intro n ω
    rw [hA'def]
    exact iterZ_symm T.toEquiv A n ω
  have h' : UniformExpGrowth T.symm A' := by
    obtain ⟨C, hC, l, hl, hg⟩ := h
    refine ⟨C, hC, l, hl, fun n ω => ?_⟩
    rw [hiter, ← Int.natAbs_neg n]
    exact hg (-n) ω
  obtain ⟨c2, hc2, L2, hL2, Pu, hPuc, hPu, hinvu, hu⟩ := exists_stable_field T.symm A' hA' h'
  have hL : 0 < min L1 L2 := lt_min (by linarith) (by linarith)
  refine ⟨max c1 c2, lt_max_of_lt_left hc1, min L1 L2, lt_min hL1 hL2, Ps, Pu, hPsc, hPuc, hPs,
    hPu, fun ω v hv => (hinvs ω v).2 hv, fun ω v hv => ?_, fun n ω v hv => ?_,
    fun n ω v hv => ?_⟩
  · refine (hinvu (T ω) (act (A ω : M2R) v)).1 ?_
    have e1 : A' (T ω) = (A ω)⁻¹ := by rw [hA'def]; simp
    rw [e1, Homeomorph.symm_apply_apply, ← act_mul, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, act_one]
    exact hv
  · exact (hs n ω v hv).trans
      (const_mono hc1.le (le_max_left _ _) hL (min_le_left _ _) n (norm_nonneg _))
  · have := hu n ω v hv
    rw [hiter] at this
    exact this.trans
      (const_mono hc2.le (le_max_right _ _) hL (min_le_right _ _) n (norm_nonneg _))

/-- **Theorem 3.8.2** (characterizations of uniform hyperbolicity), items (a)–(c). -/
theorem uniformHyperbolicityCharacterization : UniformHyperbolicityCharacterizationStatement :=
  uniformHyperbolicityCharacterization_of fun _ _ _ T A hA h =>
    invExpSplitting_of_uniformExpGrowth T A hA h

end Cocycle

end DF
