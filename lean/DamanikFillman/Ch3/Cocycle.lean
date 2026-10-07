/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §3.8 Unimodular cocycles (book pp. 278–292)

We work with `2 × 2` matrices equipped with the Euclidean operator norm
(`Matrix.Norms.L2Operator`), as in the book.

Main definitions:
* `DF.Cocycle.iter T A n` — the iterates `A_n(ω) = A(T^{n-1}ω) ⋯ A(ω)` of the cocycle `(T, A)`
  for `n ≥ 0` (3.8.2); `DF.Cocycle.iterZ` — the iterates for `n ∈ ℤ` when `T` is invertible;
* `DF.Cocycle.lyap μ T A` — the Lyapunov exponent `L_μ(A) = inf_{n ≥ 1} (1/n) ∫ log ‖A_n‖ dμ`;
* `DF.Cocycle.UniformExpGrowth`, `DF.Cocycle.BoundedOrbit`, `DF.Cocycle.InvExpSplitting` — the
  notions of Definition 3.8.1 (for `SL(2, ℝ)` cocycles over homeomorphisms).

Main results:
* `DF.Cocycle.iter_add` — the cocycle identity `A_{n+m}(ω) = A_m(Tⁿω) A_n(ω)`;
* `DF.Cocycle.iterZ_neg_apply` — identity (3.8.3): `A_{-n}(Tⁿω) = A_n(ω)⁻¹`;
* `DF.Cocycle.one_le_norm_of_det_eq_one` — `‖A‖ ≥ 1` for `A ∈ SL(2, ℂ)` (operator norm);
* `DF.Cocycle.lyapunov_exponent` — **Proposition 3.8.6**: for ergodic `μ` and bounded
  measurable `A : Ω → SL(2, ℂ)`, `L_μ(A) ≥ 0` and
  `L_μ(A) = inf (1/n) ∫ log‖A_n‖ = lim (1/n) ∫ log‖A_n‖ = lim (1/n) log‖A_n(ω)‖` a.e.
  (Furstenberg–Kesten, via Kingman's theorem `DF.kingman`).

Statements (stated as `Prop`s, not asserted):
* `DF.Cocycle.UniformHyperbolicityCharacterizationStatement` — Theorem 3.8.2 (equivalence of
  (a) uniform exponential growth, (b) invariant exponential splitting, (c) absence of bounded
  orbits; item (d), projective conjugacy to a diagonal cocycle, is omitted);
* `DF.Cocycle.RuelleStatement` — Theorem 3.8.7 (deterministic Oseledets/Ruelle theorem);
* `DF.Cocycle.OseledetsStatement` — Corollary 3.8.8 (multiplicative ergodic theorem).
-/
import DamanikFillman.Ch3.Kingman

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Set Function Topology Matrix
open scoped Matrix.Norms.L2Operator

namespace DF

namespace Cocycle

/-- `2 × 2` complex matrices (with the Euclidean operator norm). -/
abbrev M2 := Matrix (Fin 2) (Fin 2) ℂ

/-- `2 × 2` real matrices (with the Euclidean operator norm). -/
abbrev M2R := Matrix (Fin 2) (Fin 2) ℝ

/-! ### Elementary norm estimates -/

lemma sq_norm_col_le (M : M2) (j : Fin 2) : ‖M 0 j‖ ^ 2 + ‖M 1 j‖ ^ 2 ≤ ‖M‖ ^ 2 := by
  have h := (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) M).le_opNorm
    (WithLp.toLp 2 (Pi.single j 1))
  rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.toEuclideanCLM_toLp] at h
  have h1 : ‖(WithLp.toLp 2 (Pi.single j (1 : ℂ)) : EuclideanSpace ℂ (Fin 2))‖ = 1 := by
    rw [EuclideanSpace.norm_eq]; fin_cases j <;> simp [Fin.sum_univ_two]
  have h2 : ‖(WithLp.toLp 2 (M *ᵥ Pi.single j 1) : EuclideanSpace ℂ (Fin 2))‖ ^ 2 =
      ‖M 0 j‖ ^ 2 + ‖M 1 j‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]
    fin_cases j <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [h1, mul_one] at h
  have := pow_le_pow_left₀ (norm_nonneg _) h 2
  linarith

/-- For `M ∈ SL(2, ℂ)`, the operator norm satisfies `‖M‖ ≥ 1`. -/
theorem one_le_norm_of_det_eq_one {M : M2} (h : M.det = 1) : 1 ≤ ‖M‖ := by
  have h0 := sq_norm_col_le M 0
  have h1 := sq_norm_col_le M 1
  have hdet : ‖M.det‖ ≤ ‖M 0 0‖ * ‖M 1 1‖ + ‖M 0 1‖ * ‖M 1 0‖ := by
    rw [det_fin_two]; refine (norm_sub_le _ _).trans ?_; rw [norm_mul, norm_mul]
  rw [h, norm_one] at hdet
  set a := ‖M 0 0‖
  set b := ‖M 0 1‖
  set c := ‖M 1 0‖
  set d := ‖M 1 1‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hc : 0 ≤ c := norm_nonneg _
  have hd : 0 ≤ d := norm_nonneg _
  have hcs : (a * d + b * c) ^ 2 ≤ (a ^ 2 + c ^ 2) * (b ^ 2 + d ^ 2) := by
    nlinarith [sq_nonneg (a * b - c * d)]
  have h4 : 1 ≤ ‖M‖ ^ 4 := by
    calc (1 : ℝ) ≤ (a * d + b * c) ^ 2 := by nlinarith
      _ ≤ (a ^ 2 + c ^ 2) * (b ^ 2 + d ^ 2) := hcs
      _ ≤ ‖M‖ ^ 2 * ‖M‖ ^ 2 := mul_le_mul h0 h1 (by positivity) (by positivity)
      _ = ‖M‖ ^ 4 := by ring
  by_contra hlt
  push Not at hlt
  have : ‖M‖ ^ 4 < 1 := pow_lt_one₀ (norm_nonneg _) hlt (by norm_num)
  linarith

/-! ### Cocycle iterates -/

variable {Ω : Type*}

/-- The iterates `A_n(ω) = A(T^{n-1}ω) ⋯ A(Tω) A(ω)`, `A_0 = I`, of the cocycle `(T, A)`
(3.8.2), for any monoid-valued `A`. -/
def iter {R : Type*} [Monoid R] (T : Ω → Ω) (A : Ω → R) : ℕ → Ω → R
  | 0 => fun _ => 1
  | n + 1 => fun ω => A (T^[n] ω) * iter T A n ω

section iter

variable {R : Type*} [Monoid R] {T : Ω → Ω} {A : Ω → R}

@[simp] lemma iter_zero (ω : Ω) : iter T A 0 ω = 1 := rfl

lemma iter_succ (n : ℕ) (ω : Ω) : iter T A (n + 1) ω = A (T^[n] ω) * iter T A n ω := rfl

@[simp] lemma iter_one (ω : Ω) : iter T A 1 ω = A ω := by simp [iter_succ]

/-- The cocycle identity `A_{n+m}(ω) = A_m(Tⁿω) A_n(ω)`. -/
theorem iter_add (n m : ℕ) (ω : Ω) : iter T A (n + m) ω = iter T A m (T^[n] ω) * iter T A n ω := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [← add_assoc, iter_succ, ih, iter_succ, mul_assoc, ← iterate_add_apply, add_comm m n]

end iter

/-- Iterates `A_n` for `n ∈ ℤ` of a cocycle over an invertible map `T` (3.8.2):
for `n ≤ -1`, `A_n(ω) = A(Tⁿω)⁻¹ ⋯ A(T⁻¹ω)⁻¹ = (A_{|n|}(Tⁿω))⁻¹`. -/
def iterZ {R : Type*} [Group R] (T : Ω ≃ Ω) (A : Ω → R) : ℤ → Ω → R
  | (n : ℕ) => iter T A n
  | Int.negSucc n => fun ω => (iter T A (n + 1) (T.symm^[n + 1] ω))⁻¹

section iterZ

variable {R : Type*} [Group R] {T : Ω ≃ Ω} {A : Ω → R}

lemma iterZ_natCast (n : ℕ) (ω : Ω) : iterZ T A n ω = iter T A n ω := rfl

lemma symm_iterate_iterate (n : ℕ) (ω : Ω) : T.symm^[n] (T^[n] ω) = ω := by
  induction n generalizing ω with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply, iterate_succ_apply', Equiv.symm_apply_apply, ih]

lemma iterate_symm_iterate (n : ℕ) (ω : Ω) : T^[n] (T.symm^[n] ω) = ω := by
  induction n generalizing ω with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply, iterate_succ_apply', Equiv.apply_symm_apply, ih]

/-- Identity (3.8.3): `A_{-n}(Tⁿω) = A_n(ω)⁻¹`. -/
theorem iterZ_neg_apply (n : ℕ) (ω : Ω) :
    iterZ T A (-(n : ℤ)) (T^[n] ω) = (iter T A n ω)⁻¹ := by
  rcases n with _ | n
  · simp [iterZ]
  · show iterZ T A (Int.negSucc n) _ = _
    simp only [iterZ, symm_iterate_iterate]

end iterZ

/-! ### The measurable setting: Lyapunov exponents -/

variable [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω} {A : Ω → M2}

lemma det_iter (hdet : ∀ ω, (A ω).det = 1) (n : ℕ) (ω : Ω) : (iter T A n ω).det = 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [iter_succ, det_mul, hdet, ih, one_mul]

lemma norm_iter_le {M : ℝ} (hM : ∀ ω, ‖A ω‖ ≤ M) (n : ℕ) (ω : Ω) : ‖iter T A n ω‖ ≤ M ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iter_succ, pow_succ']
    calc ‖A (T^[n] ω) * iter T A n ω‖ ≤ ‖A (T^[n] ω)‖ * ‖iter T A n ω‖ := norm_mul_le _ _
      _ ≤ M * M ^ n := mul_le_mul (hM _) ih (norm_nonneg _)
          ((norm_nonneg _).trans (hM ω))

lemma measurable_iter (hT : Measurable T) (hA : Measurable A) (n : ℕ) :
    Measurable (iter T A n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih => exact (hA.comp (hT.iterate n)).mul ih

/-- The Lyapunov exponent `L_μ(A) = inf_{n ≥ 1} (1/n) ∫ log ‖A_n(ω)‖ dμ(ω)`. -/
def lyap (μ : Measure Ω) (T : Ω → Ω) (A : Ω → M2) : ℝ :=
  ⨅ n : ℕ, (∫ ω, Real.log ‖iter T A (n + 1) ω‖ ∂μ) / (n + 1)

/-- **Proposition 3.8.6** (Furstenberg–Kesten). Let `μ` be `T`-ergodic and `A : Ω → SL(2, ℂ)`
bounded and measurable. Then `L_μ(A) ≥ 0`,
`L_μ(A) = inf_n (1/n) ∫ log‖A_n‖ dμ = lim_n (1/n) ∫ log‖A_n‖ dμ`, and
`(1/n) log ‖A_n(ω)‖ → L_μ(A)` for `μ`-a.e. `ω`. -/
theorem lyapunov_exponent [IsProbabilityMeasure μ] (hT : Ergodic T μ) (hA : Measurable A)
    (hdet : ∀ ω, (A ω).det = 1) {M : ℝ} (hM : ∀ ω, ‖A ω‖ ≤ M) :
    0 ≤ lyap μ T A ∧
      Tendsto (fun n : ℕ => (∫ ω, Real.log ‖iter T A n ω‖ ∂μ) / n) atTop (𝓝 (lyap μ T A)) ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => Real.log ‖iter T A n ω‖ / n) atTop (𝓝 (lyap μ T A)) := by
  have hone : ∀ n ω, 1 ≤ ‖iter T A n ω‖ := fun n ω =>
    one_le_norm_of_det_eq_one (det_iter hdet n ω)
  have hM1 : 1 ≤ M := by
    obtain ⟨ω⟩ : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
    exact (one_le_norm_of_det_eq_one (hdet ω)).trans (hM ω)
  set f : ℕ → Ω → ℝ := fun n ω => Real.log ‖iter T A n ω‖
  have hfm : ∀ n, Measurable (f n) := fun n =>
    (measurable_iter hT.measurable hA n).norm.log
  have hsub : ∀ n m ω, 1 ≤ n → 1 ≤ m → f (n + m) ω ≤ f n ω + f m (T^[n] ω) := by
    intro n m ω _ _
    simp only [f]
    have hpos : 0 < ‖iter T A m (T^[n] ω) * iter T A n ω‖ := by
      have := hone (n + m) ω; rw [iter_add] at this; linarith
    rw [iter_add]
    calc Real.log ‖iter T A m (T^[n] ω) * iter T A n ω‖
        ≤ Real.log (‖iter T A m (T^[n] ω)‖ * ‖iter T A n ω‖) :=
          Real.log_le_log hpos (norm_mul_le _ _)
      _ = Real.log ‖iter T A m (T^[n] ω)‖ + Real.log ‖iter T A n ω‖ :=
          Real.log_mul (by linarith [hone m (T^[n] ω)]) (by linarith [hone n ω])
      _ = _ := add_comm _ _
  have hC : ∀ n ω, 1 ≤ n → |f n ω| ≤ Real.log M * n := by
    intro n ω _
    have h0 : 0 ≤ f n ω := Real.log_nonneg (hone n ω)
    rw [abs_of_nonneg h0]
    calc f n ω ≤ Real.log (M ^ n) :=
          Real.log_le_log (by linarith [hone n ω]) (norm_iter_le hM n ω)
      _ = Real.log M * n := by rw [Real.log_pow]; ring
  obtain ⟨hae, hint⟩ := kingman hT hfm hsub hC
  refine ⟨?_, hint, hae⟩
  apply le_ciInf
  intro n
  apply div_nonneg _ (by positivity)
  exact integral_nonneg fun ω => Real.log_nonneg (hone _ ω)

/-! ### The topological setting: uniform hyperbolicity (Definition 3.8.1) -/

section UH

/-- `SL(2, ℝ)`. -/
abbrev SL2R := Matrix.SpecialLinearGroup (Fin 2) ℝ

/-- The action of a real `2 × 2` matrix on `ℝ²` (Euclidean space). -/
def act (B : M2R) (v : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℝ) B v

/-- A real `2 × 2` matrix `P` is the orthogonal projection onto a line (`P² = P`, `Pᵀ = P`,
`tr P = 1`). Continuous maps into `ℝℙ¹` are encoded as continuous fields of such projections. -/
def IsLineProj (P : M2R) : Prop := P * P = P ∧ Pᵀ = P ∧ P.trace = 1

/-- The line `{v : P v = v}` onto which `P` projects. -/
def lineOf (P : M2R) : Set (EuclideanSpace ℝ (Fin 2)) := {v | act P v = v}

variable {X : Type*} [TopologicalSpace X]

/-- Definition 3.8.1: `(T, A)` exhibits *uniform exponential growth* if
`‖A_n(ω)‖ ≥ C λ^{|n|}` for all `n ∈ ℤ`, `ω ∈ Ω`, with constants `C > 0`, `λ > 1`. -/
def UniformExpGrowth (T : X ≃ₜ X) (A : X → SL2R) : Prop :=
  ∃ C > (0 : ℝ), ∃ l > (1 : ℝ), ∀ (n : ℤ) (ω : X),
    C * l ^ n.natAbs ≤ ‖((iterZ T.toEquiv A n ω : SL2R) : M2R)‖

/-- Definition 3.8.1: `(T, A)` *enjoys a bounded orbit* if there are `ω` and a unit vector `v`
with `‖A_n(ω) v‖ ≤ 1` for all `n ∈ ℤ` (3.8.9). -/
def BoundedOrbit (T : X ≃ₜ X) (A : X → SL2R) : Prop :=
  ∃ ω : X, ∃ v : EuclideanSpace ℝ (Fin 2), ‖v‖ = 1 ∧
    ∀ n : ℤ, ‖act ((iterZ T.toEquiv A n ω : SL2R) : M2R) v‖ ≤ 1

/-- Definition 3.8.1: `(T, A)` admits an *invariant exponential splitting*: there are continuous
line fields `Λˢ, Λᵘ` (encoded by projections), invariant under the cocycle (3.8.7), such that
vectors in `Λˢ` decay exponentially in forward time and vectors in `Λᵘ` decay exponentially in
backward time (3.8.8). -/
def InvExpSplitting (T : X ≃ₜ X) (A : X → SL2R) : Prop :=
  ∃ c > (0 : ℝ), ∃ L > (1 : ℝ), ∃ Ps Pu : X → M2R, Continuous Ps ∧ Continuous Pu ∧
    (∀ ω, IsLineProj (Ps ω)) ∧ (∀ ω, IsLineProj (Pu ω)) ∧
    (∀ ω, ∀ v ∈ lineOf (Ps ω), act (A ω : M2R) v ∈ lineOf (Ps (T ω))) ∧
    (∀ ω, ∀ v ∈ lineOf (Pu ω), act (A ω : M2R) v ∈ lineOf (Pu (T ω))) ∧
    (∀ (n : ℕ) (ω : X), ∀ v ∈ lineOf (Ps ω),
      ‖act ((iterZ T.toEquiv A n ω : SL2R) : M2R) v‖ ≤ c * L⁻¹ ^ n * ‖v‖) ∧
    (∀ (n : ℕ) (ω : X), ∀ v ∈ lineOf (Pu ω),
      ‖act ((iterZ T.toEquiv A (-(n : ℤ)) ω : SL2R) : M2R) v‖ ≤ c * L⁻¹ ^ n * ‖v‖)

/-- **Theorem 3.8.2** (characterizations of uniform hyperbolicity), items (a)–(c): for a
topological dynamical system `(Ω, T)` and continuous `A : Ω → SL(2, ℝ)`, uniform exponential
growth, the existence of an invariant exponential splitting, and the absence of bounded orbits
are equivalent. (Item (d) is not included.) Stated, not proved. -/
def UniformHyperbolicityCharacterizationStatement : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] (T : X ≃ₜ X) (A : X → SL2R),
    Continuous (fun ω => (A ω : M2R)) →
      (UniformExpGrowth T A ↔ InvExpSplitting T A) ∧ (UniformExpGrowth T A ↔ ¬ BoundedOrbit T A)

end UH

/-! ### Theorem 3.8.7 and Corollary 3.8.8 (stated) -/

/-- `SL(2, ℂ)`. -/
abbrev SL2C := Matrix.SpecialLinearGroup (Fin 2) ℂ

/-- The action of a complex `2 × 2` matrix on `ℂ²` (Euclidean space). -/
def actC (B : M2) (v : EuclideanSpace ℂ (Fin 2)) : EuclideanSpace ℂ (Fin 2) :=
  Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) B v

/-- The products `A_n ⋯ A_1` of a sequence of matrices. -/
def seqProd (A : ℕ → M2) : ℕ → M2
  | 0 => 1
  | n + 1 => A (n + 1) * seqProd A n

/-- **Theorem 3.8.7** (Ruelle). If `A_n ∈ SL(2, ℂ)` satisfy `(1/n) log ‖A_n‖ → 0` (3.8.34) and
`(1/n) log ‖A_n ⋯ A_1‖ → L > 0` (3.8.35), there is a one-dimensional subspace `V ⊆ ℂ²` such that
`(1/n) log ‖A_n ⋯ A_1 v‖ → -L` for `v ∈ V \ {0}` and `→ L` for `v ∉ V` (3.8.36).
Stated, not proved. -/
def RuelleStatement : Prop :=
  ∀ (A : ℕ → M2) (L : ℝ), (∀ n, (A n).det = 1) →
    Tendsto (fun n : ℕ => Real.log ‖A n‖ / n) atTop (𝓝 0) →
    Tendsto (fun n : ℕ => Real.log ‖seqProd A n‖ / n) atTop (𝓝 L) → 0 < L →
    ∃ V : Submodule ℂ (EuclideanSpace ℂ (Fin 2)), Module.finrank ℂ V = 1 ∧
      (∀ v ∈ V, v ≠ 0 →
        Tendsto (fun n : ℕ => Real.log ‖actC (seqProd A n) v‖ / n) atTop (𝓝 (-L))) ∧
      (∀ v ∉ V, Tendsto (fun n : ℕ => Real.log ‖actC (seqProd A n) v‖ / n) atTop (𝓝 L))

/-- **Corollary 3.8.8** (Oseledets' multiplicative ergodic theorem). For an invertible ergodic
`T` and bounded measurable `A : Ω → SL(2, ℂ)` with `L_μ(A) > 0`, there are measurable line fields
(represented by nonzero vectors) `vˢ, vᵘ`, invariant under the cocycle, along which
`(1/n) log ‖A_n(ω) v‖ → -L_μ(A)` resp. `(1/n) log ‖A_{-n}(ω) v‖ → -L_μ(A)` a.e. Stated, not
proved. -/
def OseledetsStatement : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (T : Ω ≃ᵐ Ω)
    (A : Ω → SL2C), Ergodic T μ → Measurable (fun ω => (A ω : M2)) →
    (∃ M, ∀ ω, ‖(A ω : M2)‖ ≤ M) → 0 < lyap μ T (fun ω => (A ω : M2)) →
    ∃ vs vu : Ω → EuclideanSpace ℂ (Fin 2), Measurable vs ∧ Measurable vu ∧
      ∀ᵐ ω ∂μ, vs ω ≠ 0 ∧ vu ω ≠ 0 ∧
        (∃ a : ℂ, actC (A ω : M2) (vs ω) = a • vs (T ω)) ∧
        (∃ a : ℂ, actC (A ω : M2) (vu ω) = a • vu (T ω)) ∧
        Tendsto (fun n : ℕ => Real.log ‖actC ((iterZ T.toEquiv A n ω : SL2C) : M2) (vs ω)‖ / n)
          atTop (𝓝 (-lyap μ T (fun ω => (A ω : M2)))) ∧
        Tendsto (fun n : ℕ =>
          Real.log ‖actC ((iterZ T.toEquiv A (-(n : ℤ)) ω : SL2C) : M2) (vu ω)‖ / n)
          atTop (𝓝 (-lyap μ T (fun ω => (A ω : M2))))

end Cocycle

end DF
