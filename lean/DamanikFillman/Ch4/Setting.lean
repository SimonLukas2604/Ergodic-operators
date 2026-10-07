/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §4.1–§4.2: the ergodic setting   (book pp. 307–310)

Throughout Chapter 4 the book fixes an invertible ergodic system `(Ω, B, μ, T)` and a bounded
measurable sampling function `f : Ω → ℝ`, and studies the family of Schrödinger operators
`H_ω` on `ℓ²(ℤ)` with potentials `V_ω(n) = f(Tⁿω)` (4.1.1), (4.1.2).

## Main definitions (namespace `DF.ErgodicFamily`)
* `DF.ErgodicFamily Ω` — the data `(μ, T, f)`: `μ` a probability measure, `T : Ω ≃ᵐ Ω` an
  ergodic measurable automorphism, `f` bounded measurable.
* `E.Tz n` — the `ℤ`-iterates `Tⁿ`; `E.V ω` — the potential (4.1.1); `E.H ω` — the operator
  `H_ω = schr (V_ω)` (4.1.2); `E.fBound` — a bound for `|f|`.
* `DF.shiftL` — the left shift `[Uψ](n) = ψ(n+1)` (p. 309), a unitary with `U* = DF.shiftR`.
* `E.spec ω φ` — the spectral measure of `(H_ω, φ)` (so `η_{ω,n} = E.spec ω (dlt n)`, (4.1.4));
  `E.canonical ω` — the canonical spectral measure `η_ω = η_{ω,0} + η_{ω,1}` (4.1.3);
  `E.fc ω g = g(H_ω)` — bounded Borel functional calculus; `E.proj ω S = χ_S(H_ω)`.

## Main results
* `E.H_T` — **covariance (4.2.1)**: `H_{Tω} = U H_ω U*`; `E.fc_T`: `g(H_{Tω}) = U g(H_ω) U*`
  (Exercise 4.2.1); `E.spec_T`, `E.spec_Tz`: `η_{Tⁿω, m} = η_{ω, m+n}`.
* `E.norm_H_le` — `‖H_ω‖ ≤ 2 + ‖f‖_∞`.
* `E.measurable_spec`, `E.measurable_inner_fc` — **Lemma 4.2.1** (weak measurability): for every
  bounded Borel `g`, `ω ↦ ⟪φ, g(H_ω) ψ⟫` is measurable; equivalently `ω ↦ η^ω_φ` is a measurable
  map into the space of measures.
* `E.measurePreserving_Tz`, `E.measurable_Tz` — basic facts on the iterates.

## Design remarks
The structure bundles the data; later sections (IDS, Lyapunov exponent, Thouless formula,
Kotani theory, gap labelling) take an `E : ErgodicFamily Ω` and use `E.H`, `E.spec`, `E.fc`.
The topological setting (compact metric `Ω`, homeomorphism `T`, continuous `f`) is recorded by
the predicate `E.IsTopological`.

No `Statement` props are introduced in this file.
-/
import DamanikFillman.Ch4.MeasurableFamily
import DamanikFillman.Ch2.Schrodinger

noncomputable section

open scoped InnerProductSpace ComplexConjugate NNReal ENNReal Topology
open MeasureTheory Set Filter L2

namespace DF

/-! ### The shift operator -/

/-- The left shift `[Uψ](n) = ψ(n+1)` on `ℓ²(ℤ)` (p. 309). -/
def shiftL : Op := weightedShift (fun _ : ℤ => (1 : ℂ)) (Equiv.addRight 1)

/-- The right shift `[U*ψ](n) = ψ(n-1)`, the inverse (and adjoint) of `shiftL`. -/
def shiftR : Op := weightedShift (fun _ : ℤ => (1 : ℂ)) (Equiv.addRight (-1))

lemma shiftL_apply (ψ : L2 ℤ) (n : ℤ) : shiftL ψ n = ψ (n + 1) := by
  rw [shiftL, weightedShift_apply bdd_one]; simp

lemma shiftR_apply (ψ : L2 ℤ) (n : ℤ) : shiftR ψ n = ψ (n - 1) := by
  rw [shiftR, weightedShift_apply bdd_one]; simp [sub_eq_add_neg]

lemma shiftL_shiftR (ψ : L2 ℤ) : shiftL (shiftR ψ) = ψ := by
  ext n; rw [shiftL_apply, shiftR_apply]; simp

lemma shiftR_shiftL (ψ : L2 ℤ) : shiftR (shiftL ψ) = ψ := by
  ext n; rw [shiftR_apply, shiftL_apply]; simp

lemma star_shiftL : star shiftL = shiftR := by
  rw [shiftL, star_weightedShift bdd_one, shiftR]
  exact weightedShift_congr (fun _ => by simp) (fun i => by simp)

lemma shiftL_mem_unitary : shiftL ∈ unitary Op := by
  rw [Unitary.mem_iff, star_shiftL]
  constructor <;> ext1 ψ
  · exact shiftR_shiftL ψ
  · exact shiftL_shiftR ψ

lemma shiftR_dlt (n : ℤ) : shiftR (dlt n) = dlt (n + 1) := by
  ext m; rw [shiftR_apply, dlt_apply, dlt_apply]
  congr 1; exact propext (by omega)

lemma shiftL_dlt (n : ℤ) : shiftL (dlt n) = dlt (n - 1) := by
  ext m; rw [shiftL_apply, dlt_apply, dlt_apply]
  congr 1; exact propext (by omega)

/-- `‖schr V‖ ≤ 2 + sup |V|`. -/
lemma norm_schr_le {V : ℤ → ℝ} {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ n, |V n| ≤ C) :
    ‖schr V‖ ≤ 2 + C := by
  have h1 : ‖weightedShift (fun _ : ℤ => (1 : ℂ)) (Equiv.addRight (1 : ℤ))‖ ≤ 1 :=
    norm_weightedShift_le zero_le_one fun _ => by simp
  have h2 : ‖weightedShift (fun _ : ℤ => (1 : ℂ)) (Equiv.addRight (-1 : ℤ))‖ ≤ 1 :=
    norm_weightedShift_le zero_le_one fun _ => by simp
  have h3 : ‖weightedShift (fun n : ℤ => ((V n : ℝ) : ℂ)) (Equiv.refl ℤ)‖ ≤ C :=
    norm_weightedShift_le hC0 fun n => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hC n
  calc ‖schr V‖ ≤ ‖weightedShift (fun _ : ℤ => (1 : ℂ)) (Equiv.addRight (1 : ℤ))‖ +
        ‖weightedShift (fun _ : ℤ => (1 : ℂ)) (Equiv.addRight (-1 : ℤ))‖ +
        ‖weightedShift (fun n : ℤ => ((V n : ℝ) : ℂ)) (Equiv.refl ℤ)‖ := by
        rw [schr]; exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ ≤ 2 + C := by linarith

/-- A spectral measure only depends on the operator (not on the proof of self-adjointness), and
can be transported along equalities of operators. -/
lemma spectralMeasure_congr {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {A B : H →L[ℂ] H} (h : A = B) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (φ : H) : spectralMeasure A hA φ = spectralMeasure B hB φ := by
  subst h; rfl

lemma borelCalc_congr_op {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {A B : H →L[ℂ] H} (h : A = B) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (g : ℝ → ℂ) : borelCalc A hA g = borelCalc B hB g := by
  subst h; rfl

/-! ### The ergodic family -/

/-- **The setting of Chapter 4** (§4.1): an invertible ergodic system `(Ω, μ, T)` and a bounded
measurable sampling function `f : Ω → ℝ`, defining potentials `V_ω(n) = f(Tⁿω)`. -/
structure ErgodicFamily (Ω : Type*) [MeasurableSpace Ω] where
  /-- the ergodic probability measure -/
  μ : Measure Ω
  isProb : IsProbabilityMeasure μ
  /-- the (invertible, bimeasurable) transformation -/
  T : Ω ≃ᵐ Ω
  ergodic : Ergodic T μ
  /-- the sampling function -/
  f : Ω → ℝ
  measurable_f : Measurable f
  bdd_f : ∃ C, ∀ ω, |f ω| ≤ C

namespace ErgodicFamily

variable {Ω : Type*} [MeasurableSpace Ω] (E : ErgodicFamily Ω)

instance : IsProbabilityMeasure E.μ := E.isProb

lemma measurePreserving_T : MeasurePreserving E.T E.μ E.μ := E.ergodic.toMeasurePreserving

lemma measurePreserving_symm : MeasurePreserving E.T.symm E.μ E.μ :=
  MeasurePreserving.symm E.T E.measurePreserving_T

/-- A bound for `|f|`. -/
def fBound : ℝ := max 0 (Classical.choose E.bdd_f)

lemma fBound_nonneg : 0 ≤ E.fBound := le_max_left _ _

lemma abs_f_le (ω : Ω) : |E.f ω| ≤ E.fBound :=
  (Classical.choose_spec E.bdd_f ω).trans (le_max_right _ _)

/-! #### Iterates `Tⁿ`, `n ∈ ℤ` -/

/-- The iterate `Tⁿ`, `n ∈ ℤ`. -/
def Tz (n : ℤ) (ω : Ω) : Ω := (E.T.toEquiv ^ n) ω

@[simp] lemma Tz_zero (ω : Ω) : E.Tz 0 ω = ω := by simp [Tz]

lemma Tz_add (m n : ℤ) (ω : Ω) : E.Tz (m + n) ω = E.Tz m (E.Tz n ω) := by
  simp [Tz, zpow_add, Equiv.Perm.mul_apply]

@[simp] lemma Tz_one (ω : Ω) : E.Tz 1 ω = E.T ω := by simp [Tz]

@[simp] lemma Tz_neg_one (ω : Ω) : E.Tz (-1) ω = E.T.symm ω := by
  simp [Tz, Equiv.Perm.inv_def]

lemma Tz_succ (n : ℤ) (ω : Ω) : E.Tz (n + 1) ω = E.T (E.Tz n ω) := by
  rw [add_comm, Tz_add, Tz_one]

lemma Tz_pred (n : ℤ) (ω : Ω) : E.Tz (n - 1) ω = E.T.symm (E.Tz n ω) := by
  rw [sub_eq_add_neg, add_comm, Tz_add, Tz_neg_one]

lemma Tz_T (n : ℤ) (ω : Ω) : E.Tz n (E.T ω) = E.Tz (n + 1) ω := by
  rw [Tz_add, Tz_one]

lemma Tz_natCast (n : ℕ) (ω : Ω) : E.Tz n ω = (⇑E.T)^[n] ω := by
  induction n generalizing ω with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, Tz_succ, ih, Function.iterate_succ_apply']

lemma measurable_Tz (n : ℤ) : Measurable (E.Tz n) := by
  induction n using Int.induction_on with
  | zero =>
    have : E.Tz 0 = id := funext fun ω => E.Tz_zero ω
    rw [this]; exact measurable_id
  | succ n ih =>
    have : E.Tz (n + 1) = E.T ∘ E.Tz n := funext fun ω => E.Tz_succ n ω
    rw [this]; exact E.T.measurable.comp ih
  | pred n ih =>
    have : E.Tz (-n - 1) = E.T.symm ∘ E.Tz (-n) := funext fun ω => E.Tz_pred (-n) ω
    rw [this]; exact E.T.symm.measurable.comp ih

lemma measurePreserving_Tz (n : ℤ) : MeasurePreserving (E.Tz n) E.μ E.μ := by
  induction n using Int.induction_on with
  | zero =>
    have : E.Tz 0 = id := funext fun ω => E.Tz_zero ω
    rw [this]; exact MeasurePreserving.id _
  | succ n ih =>
    have : E.Tz (n + 1) = E.T ∘ E.Tz n := funext fun ω => E.Tz_succ n ω
    rw [this]; exact E.measurePreserving_T.comp ih
  | pred n ih =>
    have : E.Tz (-n - 1) = E.T.symm ∘ E.Tz (-n) := funext fun ω => E.Tz_pred (-n) ω
    rw [this]; exact E.measurePreserving_symm.comp ih

/-! #### Potentials and operators -/

/-- The potential `V_ω(n) = f(Tⁿω)` (4.1.1). -/
def V (ω : Ω) (n : ℤ) : ℝ := E.f (E.Tz n ω)

lemma V_T (ω : Ω) (n : ℤ) : E.V (E.T ω) n = E.V ω (n + 1) := by
  simp only [V, Tz_T]

lemma V_Tz (ω : Ω) (m n : ℤ) : E.V (E.Tz m ω) n = E.V ω (n + m) := by
  simp only [V, ← Tz_add]

lemma V_zero (ω : Ω) : E.V ω 0 = E.f ω := by simp [V]

lemma V_one (ω : Ω) : E.V ω 1 = E.f (E.T ω) := by simp [V]

lemma bddPot (ω : Ω) : BddPot (E.V ω) := ⟨E.fBound, fun n => E.abs_f_le _⟩

lemma abs_V_le (ω : Ω) (n : ℤ) : |E.V ω n| ≤ E.fBound := E.abs_f_le _

lemma measurable_V (n : ℤ) : Measurable fun ω => E.V ω n :=
  E.measurable_f.comp (E.measurable_Tz n)

/-- The operator `H_ω` (4.1.2). -/
def H (ω : Ω) : Op := schr (E.V ω)

lemma isSelfAdjoint_H (ω : Ω) : IsSelfAdjoint (E.H ω) := isSelfAdjoint_schr (E.bddPot ω)

lemma H_apply (ω : Ω) (ψ : L2 ℤ) (n : ℤ) :
    E.H ω ψ n = ψ (n + 1) + ψ (n - 1) + (E.V ω n : ℂ) * ψ n :=
  schr_apply (E.bddPot ω) ψ n

/-- `‖H_ω‖ ≤ 2 + ‖f‖_∞`. -/
lemma norm_H_le (ω : Ω) : ‖E.H ω‖ ≤ 2 + E.fBound :=
  norm_schr_le E.fBound_nonneg (E.abs_V_le ω)

/-- **Covariance (4.2.1)**: `H_{Tω} = U H_ω U*`. -/
theorem H_T (ω : Ω) : E.H (E.T ω) = shiftL * E.H ω * star shiftL := by
  rw [star_shiftL]
  ext1 ψ
  ext n
  simp only [ContinuousLinearMap.mul_apply]
  rw [H_apply, shiftL_apply, H_apply, shiftR_apply, shiftR_apply, shiftR_apply, V_T]
  simp only [add_sub_cancel_right]

/-! #### Spectral measures and functional calculus -/

/-- The spectral measure of `(H_ω, φ)`; `η_{ω,n} = E.spec ω (dlt n)` (4.1.4). -/
def spec (ω : Ω) (φ : L2 ℤ) : Measure ℝ := spectralMeasure (E.H ω) (E.isSelfAdjoint_H ω) φ

instance (ω : Ω) (φ : L2 ℤ) : IsFiniteMeasure (E.spec ω φ) :=
  isFiniteMeasure_spectralMeasure _ _ φ

lemma spec_univ (ω : Ω) (φ : L2 ℤ) : E.spec ω φ univ = ENNReal.ofReal (‖φ‖ ^ 2) :=
  spectralMeasure_univ _ _ φ

instance (ω : Ω) (n : ℤ) : IsProbabilityMeasure (E.spec ω (dlt n)) :=
  ⟨by rw [spec_univ, norm_dlt]; simp⟩

/-- The canonical spectral measure `η_ω = η_{ω,0} + η_{ω,1}` (4.1.3). -/
def canonical (ω : Ω) : Measure ℝ := E.spec ω (dlt 0) + E.spec ω (dlt 1)

/-- The bounded Borel functional calculus `g ↦ g(H_ω)`. -/
def fc (ω : Ω) (g : ℝ → ℂ) : Op := borelCalc (E.H ω) (E.isSelfAdjoint_H ω) g

/-- The spectral projections `P_ω(S) = χ_S(H_ω)`. -/
def proj (ω : Ω) (S : Set ℝ) : Op := specProj (E.H ω) (E.isSelfAdjoint_H ω) S

lemma inner_fc_self {g : ℝ → ℂ} (hg : IsBddBorel g) (ω : Ω) (φ : L2 ℤ) :
    ⟪φ, E.fc ω g φ⟫_ℂ = ∫ x, g x ∂(E.spec ω φ) :=
  inner_borelCalc_self hg φ

lemma isSelfAdjoint_HT (ω : Ω) : IsSelfAdjoint (shiftL * E.H ω * star shiftL) := by
  rw [← E.H_T]; exact E.isSelfAdjoint_H _

/-- Covariance of spectral measures: `η^{Tω}_φ = η^ω_{U*φ}`. -/
theorem spec_T (ω : Ω) (φ : L2 ℤ) : E.spec (E.T ω) φ = E.spec ω (shiftR φ) := by
  rw [spec, spectralMeasure_congr (E.H_T ω) _ (E.isSelfAdjoint_HT ω),
    spectralMeasure_unitary_conj (E.isSelfAdjoint_H ω) shiftL_mem_unitary, star_shiftL]
  rfl

/-- **Exercise 4.2.1** in the ergodic setting: `g(H_{Tω}) = U g(H_ω) U*`. -/
theorem fc_T {g : ℝ → ℂ} (hg : IsBddBorel g) (ω : Ω) :
    E.fc (E.T ω) g = shiftL * E.fc ω g * star shiftL := by
  rw [fc, borelCalc_congr_op (E.H_T ω) _ (E.isSelfAdjoint_HT ω),
    borelCalc_unitary_conj (E.isSelfAdjoint_H ω) shiftL_mem_unitary _ hg]
  rfl

/-- `η_{Tⁿω, m} = η_{ω, m+n}`. -/
theorem spec_Tz (ω : Ω) (n m : ℤ) : E.spec (E.Tz n ω) (dlt m) = E.spec ω (dlt (m + n)) := by
  induction n using Int.induction_on generalizing m with
  | zero => simp
  | succ n ih =>
    rw [Tz_succ, spec_T, shiftR_dlt, ih]; congr 2; ring
  | pred n ih =>
    have h := ih (m - 1)
    rw [show -(n : ℤ) = (-n - 1) + 1 by ring, Tz_succ, spec_T, shiftR_dlt, sub_add_cancel] at h
    rw [h]; congr 2; ring

/-- In particular `η_{ω, n} = η_{Tⁿω, 0}`. -/
lemma spec_dlt_eq (ω : Ω) (n : ℤ) : E.spec ω (dlt n) = E.spec (E.Tz n ω) (dlt 0) := by
  rw [spec_Tz, zero_add]

/-! #### Measurability: Lemma 4.2.1 -/

/-- The diagonal multiplication part of `H_ω`. -/
lemma H_eq (ω : Ω) : E.H ω = shiftL + shiftR +
    weightedShift (fun n : ℤ => ((E.V ω n : ℝ) : ℂ)) (Equiv.refl ℤ) := rfl

/-- The multiplication operator by a bounded potential is the norm limit of its finite
sections. -/
lemma tendsto_mult_sections {W : ℤ → ℝ} (hW : BddPot W) (x : L2 ℤ) :
    Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) N,
      ((W n : ℂ) * x n) • dlt n) atTop
      (𝓝 (weightedShift (fun n : ℤ => ((W n : ℝ) : ℂ)) (Equiv.refl ℤ) x)) := by
  have h := lp.hasSum_single (E := fun _ : ℤ => ℂ) (p := 2) (by norm_num)
    (weightedShift (fun n : ℤ => ((W n : ℝ) : ℂ)) (Equiv.refl ℤ) x)
  have h2 := h.comp Finset.tendsto_Icc_neg
  refine h2.congr fun N => Finset.sum_congr rfl fun n _ => ?_
  show lp.single 2 n _ = _
  rw [weightedShift_apply (bdd_of_bddPot hW)]
  ext m
  simp only [Equiv.refl_apply, dlt, lp.single_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, Pi.single_apply]
  split_ifs <;> simp_all

/-- `ω ↦ H_ω (g ω)` is strongly measurable if `g` is. -/
theorem stronglyMeasurable_H_apply {g : Ω → L2 ℤ} (hg : StronglyMeasurable g) :
    StronglyMeasurable fun ω => E.H ω (g ω) := by
  simp_rw [H_eq, ContinuousLinearMap.add_apply]
  refine ((shiftL.continuous.comp_stronglyMeasurable hg).add
    (shiftR.continuous.comp_stronglyMeasurable hg)).add ?_
  have ht := tendsto_pi_nhds.2 fun ω => tendsto_mult_sections (E.bddPot ω) (g ω)
  refine stronglyMeasurable_of_tendsto atTop (fun N => ?_) ht
  refine Finset.stronglyMeasurable_fun_sum _ fun n _ => ?_
  refine StronglyMeasurable.smul_const ?_ _
  have h1 : Measurable fun ω => ((E.V ω n : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (E.measurable_V n)
  have h2 : StronglyMeasurable fun ω => (g ω) n := by
    have := (innerSL ℂ (dlt n)).continuous.comp_stronglyMeasurable hg
    simpa [Function.comp_def, innerSL_apply_apply, inner_dlt] using this
  exact h1.stronglyMeasurable.mul h2

theorem stronglyMeasurable_H_pow_apply (k : ℕ) (φ : L2 ℤ) :
    StronglyMeasurable fun ω => (E.H ω ^ k) φ := by
  induction k with
  | zero => simpa using stronglyMeasurable_const
  | succ k ih =>
    simp_rw [pow_succ', ContinuousLinearMap.mul_apply]
    exact E.stronglyMeasurable_H_apply ih

theorem measurable_inner_H_pow (φ ψ : L2 ℤ) (k : ℕ) :
    Measurable fun ω => ⟪φ, (E.H ω ^ k) ψ⟫_ℂ :=
  ((innerSL ℂ φ).continuous.comp_stronglyMeasurable
    (E.stronglyMeasurable_H_pow_apply k ψ)).measurable

/-- `ω ↦ η^ω_φ` is measurable (as a map into the space of measures on `ℝ`). -/
theorem measurable_spec (φ : L2 ℤ) : Measurable fun ω => E.spec ω φ :=
  measurable_spectralMeasure E.H E.isSelfAdjoint_H E.norm_H_le φ
    (E.measurable_inner_H_pow φ φ)

lemma measurable_spec_apply (φ : L2 ℤ) {S : Set ℝ} (hS : MeasurableSet S) :
    Measurable fun ω => E.spec ω φ S :=
  (Measure.measurable_coe hS).comp (E.measurable_spec φ)

/-- **Lemma 4.2.1** (weak measurability): `ω ↦ ⟪φ, g(H_ω) ψ⟫` is measurable for every bounded
Borel `g`; in particular the spectral projections `P_ω(I)` form a weakly measurable family. -/
theorem measurable_inner_fc {g : ℝ → ℂ} (hg : IsBddBorel g) (φ ψ : L2 ℤ) :
    Measurable fun ω => ⟪φ, E.fc ω g ψ⟫_ℂ :=
  measurable_inner_borelCalc E.H E.isSelfAdjoint_H E.norm_H_le
    (fun v k => E.measurable_inner_H_pow v v k) hg φ ψ

lemma measurable_integral_spec {g : ℝ → ℂ} (hg : IsBddBorel g) (φ : L2 ℤ) :
    Measurable fun ω => ∫ x, g x ∂(E.spec ω φ) :=
  measurable_integral_complex_of_bdd (E.measurable_spec φ) hg

/-! #### The topological setting -/

/-- The topological setting of Chapter 4: `Ω` is a compact metric space with its Borel
σ-algebra, `T` is a homeomorphism and the sampling function `f` is continuous. -/
structure IsTopological [TopologicalSpace Ω] : Prop where
  borel : BorelSpace Ω
  compact : CompactSpace Ω
  metrizable : TopologicalSpace.MetrizableSpace Ω
  continuous_T : Continuous E.T
  continuous_symm : Continuous E.T.symm
  continuous_f : Continuous E.f

end ErgodicFamily

end DF
