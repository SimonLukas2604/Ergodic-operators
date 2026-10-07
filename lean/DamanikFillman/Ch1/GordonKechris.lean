/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators, I*,
§1.12 (pp. 107–113): measurability of eigenfunctions à la Gordon–Kechris.

Throughout, `H` is a separable complex Hilbert space and `(Ω, 𝓑)` a measurable space.
Measurability notions follow Definition 1.4.17 of the book: an operator family `A : Ω → B(H)` is
*weakly measurable* if all matrix elements `ω ↦ ⟨φ, A_ω ψ⟩` are measurable, and a vector family
`ϕ : Ω → H` is measurable if all `ω ↦ ⟨ψ, ϕ(ω)⟩` are measurable (`DF.VecMeasurable`).

# Main definitions

* `DF.WeaklyMeasurable`, `DF.VecMeasurable` — Definition 1.4.17;
* `DF.eigenCount T` — the number `N` of eigenvalues of `T` counted with multiplicity
  (the supremum of the sizes of orthonormal families of eigenvectors);
* `DF.MeasurableEigenEnumeration A` — Definition 1.12.1;
* `DF.IsAgreeable K` — Definition 1.12.4.

# Main results

* `DF.measurable_norm_of_vecMeasurable` — Lemma 1.12.3(b);
* `DF.measurable_norm_apply` — Lemma 1.12.3(a);
* `DF.measurable_inner_apply` — Lemma 1.12.3(c);
* `DF.measurable_inner_of_vecMeasurable` — measurability of `ω ↦ ⟨ϕ(ω), ψ(ω)⟩`;
* `DF.isAgreeable_closedBall` — closed balls of radius `1/2` around unit vectors are agreeable
  (p. 109);
* `DF.inner_eq_zero_of_eigen` — eigenvectors of a self-adjoint operator for distinct eigenvalues
  are orthogonal (used in Lemma 1.12.6(b)).

# Statements (`Prop`s)

* `DF.GordonKechrisStatement` — Theorem 1.12.2 (Gordon–Kechris); proved in
  `DamanikFillman.Ch1.GordonKechrisProof` as `DF.gordonKechrisStatement_holds`.

# Deviations

* In `DF.MeasurableEigenEnumeration` the maps `E_m`, `ϕ_m` are total functions on `Ω`, measurable
  on all of `Ω`, with the eigen-properties required only on `Ω_m = {N ≥ m}`; since `Ω_m` is
  measurable this is equivalent to the book's formulation with functions defined on `Ω_m`.
  Measurability of `N` is encoded as measurability of every `Ω_m` (equivalent, as `N` takes values
  in the countable set `ℤ₊ ∪ {∞}`).
-/
import Mathlib

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace DF

variable {Ω : Type*} [MeasurableSpace Ω]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Definition 1.4.17: weak measurability of an operator family. -/
def WeaklyMeasurable (A : Ω → H →L[ℂ] H) : Prop :=
  ∀ φ ψ : H, Measurable fun ω => inner ℂ φ (A ω ψ)

/-- Definition 1.4.17: (weak) measurability of a vector family. -/
def VecMeasurable (ϕ : Ω → H) : Prop :=
  ∀ ψ : H, Measurable fun ω => inner ℂ ψ (ϕ ω)

lemma VecMeasurable.add {ϕ ψ : Ω → H} (h₁ : VecMeasurable ϕ) (h₂ : VecMeasurable ψ) :
    VecMeasurable fun ω => ϕ ω + ψ ω := fun χ => by
  simp only [inner_add_right]; exact (h₁ χ).add (h₂ χ)

lemma VecMeasurable.sub {ϕ ψ : Ω → H} (h₁ : VecMeasurable ϕ) (h₂ : VecMeasurable ψ) :
    VecMeasurable fun ω => ϕ ω - ψ ω := fun χ => by
  simp only [inner_sub_right]; exact (h₁ χ).sub (h₂ χ)

lemma VecMeasurable.const_smul {ϕ : Ω → H} (h : VecMeasurable ϕ) (c : ℂ) :
    VecMeasurable fun ω => c • ϕ ω := fun χ => by
  simp only [inner_smul_right]; exact (h χ).const_mul c

lemma WeaklyMeasurable.vecMeasurable_apply {A : Ω → H →L[ℂ] H} (hA : WeaklyMeasurable A)
    (χ : H) : VecMeasurable fun ω => A ω χ := fun ψ => hA ψ χ

/-! ## Lemma 1.12.3 -/

section Separable

variable [TopologicalSpace.SeparableSpace H]

omit [TopologicalSpace.SeparableSpace H] in
/-- The norm is the supremum of `|⟨d, v⟩|` over a dense sequence `d` of the closed unit ball. -/
lemma enorm_eq_iSup_inner {d : ℕ → H} (hd1 : ∀ n, ‖d n‖ ≤ 1)
    (hd : ∀ u : H, ‖u‖ ≤ 1 → ∀ δ > 0, ∃ n, ‖d n - u‖ < δ) (v : H) :
    ‖v‖ₑ = ⨆ n, ‖inner ℂ (d n) v‖ₑ := by
  apply le_antisymm
  · rcases eq_or_ne v 0 with rfl | hv
    · simp
    have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
    refine ENNReal.le_of_forall_pos_le_add fun δ hδ _ => ?_
    set u : H := ((‖v‖ : ℂ)⁻¹) • v
    have hu : ‖u‖ ≤ 1 := by
      simp only [u, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hvpos.le]
      rw [inv_mul_cancel₀ hvpos.ne']
    obtain ⟨n, hn⟩ := hd u hu (δ / (‖v‖ + 1)) (by positivity)
    have hinner : inner ℂ u v = ‖v‖ := by
      have hv' : (‖v‖ : ℂ) ≠ 0 := by exact_mod_cast hvpos.ne'
      simp only [u, inner_smul_left, inner_self_eq_norm_sq_to_K, map_inv₀, Complex.conj_ofReal]
      field_simp
      rfl
    have h1 : ‖v‖ ≤ ‖inner ℂ (d n) v‖ + δ := by
      have h2 : ‖inner ℂ u v‖ ≤ ‖inner ℂ (d n) v‖ + ‖inner ℂ (u - d n) v‖ := by
        rw [inner_sub_left]
        calc ‖inner ℂ u v‖ = ‖inner ℂ (d n) v + (inner ℂ u v - inner ℂ (d n) v)‖ := by ring_nf
          _ ≤ _ := norm_add_le _ _
      have h3 : ‖inner ℂ (u - d n) v‖ ≤ δ := by
        calc ‖inner ℂ (u - d n) v‖ ≤ ‖u - d n‖ * ‖v‖ := norm_inner_le_norm _ _
          _ ≤ δ / (‖v‖ + 1) * ‖v‖ := by
              gcongr; rw [norm_sub_rev]; exact hn.le
          _ ≤ δ := by
              rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
      rw [hinner, Complex.norm_real, Real.norm_of_nonneg hvpos.le] at h2
      linarith
    calc ‖v‖ₑ = ENNReal.ofReal ‖v‖ := (ofReal_norm v).symm
      _ ≤ ENNReal.ofReal (‖inner ℂ (d n) v‖ + δ) := ENNReal.ofReal_le_ofReal h1
      _ = ‖inner ℂ (d n) v‖ₑ + δ := by
          rw [ENNReal.ofReal_add (norm_nonneg _) δ.coe_nonneg, ofReal_norm, ENNReal.ofReal_coe_nnreal]
      _ ≤ (⨆ n, ‖inner ℂ (d n) v‖ₑ) + δ := by gcongr; exact le_iSup (fun n => ‖inner ℂ (d n) v‖ₑ) n
  · refine iSup_le fun n => ?_
    calc ‖inner ℂ (d n) v‖ₑ ≤ ‖d n‖ₑ * ‖v‖ₑ := by
          rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
          exact ENNReal.ofReal_le_ofReal (norm_inner_le_norm _ _)
      _ ≤ 1 * ‖v‖ₑ := by
          gcongr; rw [← ofReal_norm, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (hd1 n)
      _ = ‖v‖ₑ := one_mul _

omit [InnerProductSpace ℂ H] in
/-- A dense sequence in the closed unit ball. -/
lemma exists_dense_seq_closedBall :
    ∃ d : ℕ → H, (∀ n, ‖d n‖ ≤ 1) ∧ ∀ u : H, ‖u‖ ≤ 1 → ∀ δ > 0, ∃ n, ‖d n - u‖ < δ := by
  have : Nonempty (closedBall (0 : H) 1) := ⟨⟨0, by simp⟩⟩
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq (closedBall (0 : H) 1)
  refine ⟨fun n => d n, fun n => by
    have := (d n).2; rw [mem_closedBall, dist_zero_right] at this; exact this, fun u hu δ hδ => ?_⟩
  obtain ⟨n, hn⟩ := hd.exists_dist_lt (⟨u, by simpa using hu⟩ : closedBall (0 : H) 1) hδ
  exact ⟨n, by rw [← dist_eq_norm, dist_comm]; exact hn⟩

/-- Lemma 1.12.3(b): `ω ↦ ‖ϕ(ω)‖` is measurable for a measurable vector family `ϕ`. -/
theorem measurable_norm_of_vecMeasurable {ϕ : Ω → H} (hϕ : VecMeasurable ϕ) :
    Measurable fun ω => ‖ϕ ω‖ := by
  obtain ⟨d, hd1, hd⟩ := exists_dense_seq_closedBall (H := H)
  have h : Measurable fun ω => ‖ϕ ω‖ₑ := by
    simp_rw [enorm_eq_iSup_inner hd1 hd]
    exact Measurable.iSup fun n => (hϕ (d n)).enorm
  have := h.ennreal_toReal
  simpa [← ofReal_norm] using this

/-- Lemma 1.12.3(a): for a weakly measurable `A` and fixed `χ`, `ω ↦ ‖A_ω χ‖` is measurable. -/
theorem measurable_norm_apply {A : Ω → H →L[ℂ] H} (hA : WeaklyMeasurable A) (χ : H) :
    Measurable fun ω => ‖A ω χ‖ :=
  measurable_norm_of_vecMeasurable (hA.vecMeasurable_apply χ)

/-- The inner product of two measurable vector families is measurable (by polarization). -/
theorem measurable_inner_of_vecMeasurable {ϕ ψ : Ω → H} (hϕ : VecMeasurable ϕ)
    (hψ : VecMeasurable ψ) : Measurable fun ω => inner ℂ (ϕ ω) (ψ ω) := by
  have hn : ∀ {χ : Ω → H}, VecMeasurable χ → Measurable fun ω => ((‖χ ω‖ : ℂ)) ^ 2 :=
    fun hχ => ((Complex.measurable_ofReal.comp (measurable_norm_of_vecMeasurable hχ)).pow_const 2)
  simp_rw [inner_eq_sum_norm_sq_div_four (𝕜 := ℂ)]
  refine Measurable.div_const ?_ 4
  refine ((hn (hϕ.add hψ)).sub (hn (hϕ.sub hψ))).add ?_
  refine Measurable.mul_const ?_ _
  exact (hn (hϕ.sub (hψ.const_smul _))).sub (hn (hϕ.add (hψ.const_smul _)))

variable [CompleteSpace H]

/-- Lemma 1.12.3(c): for a weakly measurable `A` and measurable `ϕ, ψ`,
`ω ↦ ⟨ϕ(ω), A_ω ψ(ω)⟩` is measurable. -/
theorem measurable_inner_apply {A : Ω → H →L[ℂ] H} (hA : WeaklyMeasurable A) {ϕ ψ : Ω → H}
    (hϕ : VecMeasurable ϕ) (hψ : VecMeasurable ψ) :
    Measurable fun ω => inner ℂ (ϕ ω) (A ω (ψ ω)) := by
  -- the vector family `ω ↦ A_ω ψ(ω)` is measurable, via adjoints
  have hAψ : VecMeasurable fun ω => A ω (ψ ω) := by
    intro χ
    have hadj : VecMeasurable fun ω => ContinuousLinearMap.adjoint (A ω) χ := by
      intro η
      have : (fun ω => inner ℂ η (ContinuousLinearMap.adjoint (A ω) χ)) =
          fun ω => (starRingEnd ℂ) (inner ℂ χ (A ω η)) := by
        ext ω
        rw [ContinuousLinearMap.adjoint_inner_right, inner_conj_symm]
      rw [this]
      exact Complex.continuous_conj.measurable.comp (hA χ η)
    have : (fun ω => inner ℂ χ (A ω (ψ ω))) =
        fun ω => inner ℂ (ContinuousLinearMap.adjoint (A ω) χ) (ψ ω) := by
      ext ω; rw [ContinuousLinearMap.adjoint_inner_left]
    rw [this]
    exact measurable_inner_of_vecMeasurable hadj hψ
  exact measurable_inner_of_vecMeasurable hϕ hAψ

end Separable

/-! ## Definition 1.12.1: measurable enumerations of eigenelements -/

/-- `v` is an eigenvector of `T` with (real) eigenvalue `E`. -/
def IsEigenvec (T : H →L[ℂ] H) (E : ℝ) (v : H) : Prop := v ≠ 0 ∧ T v = (E : ℂ) • v

/-- The number of eigenvalues of `T` counted with multiplicity: the supremum of the sizes of
orthonormal families consisting of eigenvectors (for self-adjoint `T` the eigenspaces are
mutually orthogonal, so this is the sum of the eigenspace dimensions). -/
def eigenCount (T : H →L[ℂ] H) : ℕ∞ :=
  ⨆ (n : ℕ) (_ : ∃ v : Fin n → H, Orthonormal ℂ v ∧ ∀ i, ∃ E : ℝ, T (v i) = (E : ℂ) • v i),
    (n : ℕ∞)

/-- Definition 1.12.1: a measurable enumeration of eigenelements of the family `A`.
Here `Ω_m = {ω : m ≤ N(ω)}` with `N = eigenCount ∘ A`. -/
structure MeasurableEigenEnumeration (A : Ω → H →L[ℂ] H) where
  /-- the eigenvalues `E_m` -/
  E : ℕ → Ω → ℝ
  /-- the eigenvectors `ϕ_m` -/
  ϕ : ℕ → Ω → H
  measurableSet_count : ∀ m : ℕ, MeasurableSet {ω | (m : ℕ∞) ≤ eigenCount (A ω)}
  measurable_E : ∀ m, Measurable (E m)
  measurable_ϕ : ∀ m, VecMeasurable (ϕ m)
  /-- (a): `A_ω ϕ_m(ω) = E_m(ω) ϕ_m(ω)` on `Ω_m` -/
  eigen : ∀ m : ℕ, 1 ≤ m → ∀ ω, (m : ℕ∞) ≤ eigenCount (A ω) → A ω (ϕ m ω) = (E m ω : ℂ) • ϕ m ω
  /-- (b): for each eigenvalue `E` of `A_ω`, `{ϕ_m(ω) : E_m(ω) = E}` is an orthonormal basis of
  the eigenspace. -/
  basis : ∀ ω (lam : ℝ), (∃ v, IsEigenvec (A ω) lam v) →
    Orthonormal ℂ (fun m : {m : ℕ // 1 ≤ m ∧ (m : ℕ∞) ≤ eigenCount (A ω) ∧ lam = E m ω} =>
      ϕ m.1 ω) ∧
    (Submodule.span ℂ (range fun m : {m : ℕ // 1 ≤ m ∧ (m : ℕ∞) ≤ eigenCount (A ω) ∧
      lam = E m ω} => ϕ m.1 ω)).topologicalClosure =
      LinearMap.ker ((A ω - (lam : ℂ) • (1 : H →L[ℂ] H) : H →L[ℂ] H) : H →ₗ[ℂ] H)

/-- Theorem 1.12.2 (Gordon–Kechris), as a statement for given `Ω` and `H` (proved in
`DamanikFillman.Ch1.GordonKechrisProof`): every weakly
measurable family of bounded self-adjoint operators on a separable Hilbert space admits a
measurable enumeration of eigenelements. -/
def GordonKechrisStatement (Ω : Type*) [MeasurableSpace Ω] (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] [TopologicalSpace.SeparableSpace H] : Prop :=
  ∀ A : Ω → H →L[ℂ] H, WeaklyMeasurable A → (∀ ω, IsSelfAdjoint (A ω)) →
    Nonempty (MeasurableEigenEnumeration A)

/-! ## Agreeable convex sets (Definition 1.12.4) -/

/-- Definition 1.12.4: a convex set is agreeable if it is closed, bounded, nonempty, and contains
no pair of orthogonal vectors. -/
def IsAgreeable (K : Set H) : Prop :=
  Convex ℝ K ∧ IsClosed K ∧ Bornology.IsBounded K ∧ K.Nonempty ∧
    ∀ φ ∈ K, ∀ ψ ∈ K, inner ℂ φ ψ ≠ 0

/-- Decomposition of a vector `ψ` near a unit vector `φ`: with `a = Re ⟨φ, ψ⟩` and
`w = ψ - a φ`, one has `Re ⟨φ, w⟩ = 0` and `‖ψ - φ‖² = (a - 1)² + ‖w‖²`. -/
lemma decomp_near_unit {φ : H} (hφ : ‖φ‖ = 1) (ψ : H) :
    (inner ℂ φ (ψ - ((inner ℂ φ ψ).re : ℂ) • φ)).re = 0 ∧
      ‖ψ - φ‖ ^ 2 = ((inner ℂ φ ψ).re - 1) ^ 2 + ‖ψ - ((inner ℂ φ ψ).re : ℂ) • φ‖ ^ 2 := by
  set a := (inner ℂ φ ψ).re
  set w := ψ - (a : ℂ) • φ
  have hφφ : inner ℂ φ φ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hφ]; simp
  have h1 : (inner ℂ φ w).re = 0 := by
    simp only [w, inner_sub_right, inner_smul_right, hφφ, mul_one, Complex.sub_re,
      Complex.ofReal_re, a, sub_self]
  refine ⟨h1, ?_⟩
  have hdec : ψ - φ = ((a : ℂ) - 1) • φ + w := by
    simp only [w, sub_smul, one_smul]; abel
  rw [hdec, norm_add_sq (𝕜 := ℂ), norm_smul, hφ, mul_one, inner_smul_left]
  have : ‖(a : ℂ) - 1‖ = |a - 1| := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [this, sq_abs]
  simp only [map_sub, Complex.conj_ofReal, map_one, RCLike.re_to_complex, Complex.mul_re,
    Complex.sub_re, Complex.ofReal_re, Complex.one_re, Complex.sub_im, Complex.ofReal_im,
    Complex.one_im, sub_zero, h1, mul_zero, zero_mul]
  ring

/-- For a unit vector `φ`, the closed ball `B(φ, 1/2)` is agreeable (book p. 109): any two of its
elements make an angle of at most `60°` (as real vectors), so they are never orthogonal. -/
theorem isAgreeable_closedBall {φ : H} (hφ : ‖φ‖ = 1) : IsAgreeable (closedBall φ (1 / 2)) := by
  refine ⟨convex_closedBall _ _, isClosed_closedBall, isBounded_closedBall,
    ⟨φ, mem_closedBall_self (by norm_num)⟩, fun ψ₁ h₁ ψ₂ h₂ h0 => ?_⟩
  rw [mem_closedBall, dist_eq_norm] at h₁ h₂
  obtain ⟨o₁, n₁⟩ := decomp_near_unit hφ ψ₁
  obtain ⟨o₂, n₂⟩ := decomp_near_unit hφ ψ₂
  set a₁ := (inner ℂ φ ψ₁).re
  set a₂ := (inner ℂ φ ψ₂).re
  set w₁ := ψ₁ - (a₁ : ℂ) • φ
  set w₂ := ψ₂ - (a₂ : ℂ) • φ
  have hφφ : inner ℂ φ φ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hφ]; simp
  have hq₁ : ‖ψ₁ - φ‖ ^ 2 ≤ 1 / 4 := by nlinarith [norm_nonneg (ψ₁ - φ)]
  have hq₂ : ‖ψ₂ - φ‖ ^ 2 ≤ 1 / 4 := by nlinarith [norm_nonneg (ψ₂ - φ)]
  -- `a_i ≥ 1/2` and `‖w_i‖² ≤ a_i² / 3`
  have ha₁ : 1 / 2 ≤ a₁ := by nlinarith [sq_nonneg ‖w₁‖]
  have ha₂ : 1 / 2 ≤ a₂ := by nlinarith [sq_nonneg ‖w₂‖]
  have hw₁ : ‖w₁‖ ^ 2 ≤ a₁ ^ 2 / 3 := by nlinarith [sq_nonneg (a₁ - 3 / 4)]
  have hw₂ : ‖w₂‖ ^ 2 ≤ a₂ ^ 2 / 3 := by nlinarith [sq_nonneg (a₂ - 3 / 4)]
  have hprod : ‖w₁‖ * ‖w₂‖ ≤ a₁ * a₂ / 3 := by
    have h := mul_le_mul hw₁ hw₂ (sq_nonneg _) (by positivity)
    have h' : (‖w₁‖ * ‖w₂‖) ^ 2 ≤ (a₁ * a₂ / 3) ^ 2 := by
      rw [mul_pow, show (a₁ * a₂ / 3) ^ 2 = a₁ ^ 2 / 3 * (a₂ ^ 2 / 3) by ring]; exact h
    exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) h'
  -- expand `Re ⟨ψ₁, ψ₂⟩`
  have e₁ : ψ₁ = (a₁ : ℂ) • φ + w₁ := by simp [w₁]
  have e₂ : ψ₂ = (a₂ : ℂ) • φ + w₂ := by simp [w₂]
  have hexp : (inner ℂ ψ₁ ψ₂).re = a₁ * a₂ + (inner ℂ w₁ w₂).re := by
    rw [e₁, e₂]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal, hφφ, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, mul_one]
    have : (inner ℂ w₁ φ).re = 0 := by rw [← inner_conj_symm, Complex.conj_re]; exact o₁
    rw [o₂, this]; ring
  have hcs : |(inner ℂ w₁ w₂).re| ≤ ‖w₁‖ * ‖w₂‖ :=
    (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
  have h0re : (inner ℂ ψ₁ ψ₂).re = 0 := by rw [h0]; simp
  have := abs_le.1 hcs
  nlinarith [mul_pos (by linarith : (0 : ℝ) < a₁) (by linarith : (0 : ℝ) < a₂)]

/-- Eigenvectors of a self-adjoint operator for distinct eigenvalues are orthogonal. -/
theorem inner_eq_zero_of_eigen [CompleteSpace H] {T : H →L[ℂ] H} (hT : IsSelfAdjoint T) {E₁ E₂ : ℝ} {v₁ v₂ : H}
    (h₁ : T v₁ = (E₁ : ℂ) • v₁) (h₂ : T v₂ = (E₂ : ℂ) • v₂) (hne : E₁ ≠ E₂) :
    inner ℂ v₁ v₂ = 0 := by
  have hsym : inner ℂ (T v₁) v₂ = inner ℂ v₁ (T v₂) := hT.isSymmetric v₁ v₂
  rw [h₁, h₂, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at hsym
  have : ((E₁ : ℂ) - E₂) * inner ℂ v₁ v₂ = 0 := by linear_combination hsym
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (by exact_mod_cast sub_eq_zero.1 h) hne
  · exact h

end DF
