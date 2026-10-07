/-
Copyright (c) 2026. Formalization of
  S. Becker, "Self-dual perturbations of the critical almost Mathieu operator:
  Dry Ten Martini and Hausdorff dimension" (Paper II).

# Finite-dimensional linear-algebra cores

This file collects the finite-dimensional / purely algebraic cores of several arguments of the
paper.

1. **Trace inertia** (Lemma `gap:lem:inertia`, l. 3245; Paper I, Lemma 2.9), matrix version:
   Sylvester's law of inertia for Hermitian matrices under congruence `P ↦ Gᴴ P G`, for both the
   number of negative and the number of zero eigenvalues.
2. **Kernel transfer and duality algebra** (proof of `dim:thm:center`, l. 897, 1002–1013).
3. **Transported flow** (eq. `dim:br:transported-flow`, l. 4342), the kernel cancellation used
   with it, and the **normalization ODE invariance** (proof of `gap:eq:normalization`,
   l. 2700–2745).
4. **Projection sandwich** (l. 6555–6570).
5. **Root–Gram identity** (Lemma `dim:br:root-gram`, l. 4489–4600), algebraic part.
6. **Boundary inclusion**, finite core (eq. `dim:br:boundary-inclusion`, l. 4801–4835).
-/
import Mathlib

noncomputable section

open Matrix

namespace SGD
namespace MatrixLemmas

/-! ## 1. Trace inertia (Sylvester's law of inertia) -/

section Inertia

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The (real part of the) Hermitian form `x ↦ ⟪x, P x⟫ = x^* P x` of a square matrix.
Auxiliary for **Lemma `gap:lem:inertia`** (l. 3245). -/
def hform (P : Matrix n n ℂ) (x : n → ℂ) : ℝ := (star x ⬝ᵥ (P *ᵥ x)).re

/-- The set of dimensions of subspaces on which the Hermitian form of `P` is negative definite.
Its maximum is the negative index of `P`.  Auxiliary for **Lemma `gap:lem:inertia`**
(l. 3245). -/
def negDefDims (P : Matrix n n ℂ) : Set ℕ :=
  {k | ∃ W : Submodule ℂ (n → ℂ), Module.finrank ℂ W = k ∧
      ∀ x ∈ W, x ≠ 0 → hform P x < 0}

omit [DecidableEq n] in
/-- Congruence identity `x^* (G^* P G) x = (G x)^* P (G x)`.  Auxiliary for
**Lemma `gap:lem:inertia`** (l. 3245). -/
lemma hform_conj (P G : Matrix n n ℂ) (x : n → ℂ) :
    hform (Gᴴ * P * G) x = hform P (G *ᵥ x) := by
  unfold hform
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]

/-- Negative-definite subspaces are transported by an invertible congruence.  Auxiliary for
**Lemma `gap:lem:inertia`** (l. 3245). -/
lemma negDefDims_conj_subset (P G : Matrix n n ℂ) (hG : IsUnit G.det) :
    negDefDims (Gᴴ * P * G) ⊆ negDefDims P := by
  rintro k ⟨W, rfl, hW⟩
  have hinj : Function.Injective (Matrix.toLin' G) := by
    have : Function.Injective G.mulVec :=
      mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det G).2 hG)
    intro x y hxy
    apply this
    simpa only [Matrix.toLin'_apply] using hxy
  refine ⟨W.map (Matrix.toLin' G), ?_, ?_⟩
  · exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj W)).symm
  · rintro x hx hx0
    obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.1 hx
    have hy0 : y ≠ 0 := by
      rintro rfl
      exact hx0 (map_zero _)
    have := hW y hy hy0
    rwa [hform_conj, ← Matrix.toLin'_apply] at this

/-- The negative-definite dimensions are invariant under congruence by an invertible matrix.
Auxiliary for **Lemma `gap:lem:inertia`** (l. 3245). -/
lemma negDefDims_conj (P G : Matrix n n ℂ) (hG : IsUnit G.det) :
    negDefDims (Gᴴ * P * G) = negDefDims P := by
  refine (negDefDims_conj_subset P G hG).antisymm ?_
  have hP : (G⁻¹)ᴴ * (Gᴴ * P * G) * G⁻¹ = P := by
    have : (G⁻¹)ᴴ * (Gᴴ * P * G) * G⁻¹ = (G * G⁻¹)ᴴ * P * (G * G⁻¹) := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [this, mul_nonsing_inv _ hG]
    simp
  conv_lhs => rw [← hP]
  exact negDefDims_conj_subset _ _ (isUnit_nonsing_inv_det G hG)

/-- The Hermitian form of a real diagonal matrix.  Auxiliary for **Lemma `gap:lem:inertia`**
(l. 3245). -/
lemma hform_diagonal (d : n → ℝ) (x : n → ℂ) :
    hform (diagonal (fun i => (d i : ℂ))) x = ∑ i, d i * Complex.normSq (x i) := by
  unfold hform
  simp only [dotProduct, mulVec_diagonal, Complex.re_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, mul_left_comm, Complex.re_ofReal_mul, Complex.conj_mul']
  norm_cast
  simp [Complex.normSq_eq_norm_sq]

/-- For a real diagonal matrix the maximal dimension of a negative-definite subspace is the number
of negative diagonal entries.  Auxiliary for **Lemma `gap:lem:inertia`** (l. 3245). -/
lemma isGreatest_negDefDims_diagonal (d : n → ℝ) :
    IsGreatest (negDefDims (diagonal (fun i => (d i : ℂ)))) (Fintype.card {i // d i < 0}) := by
  classical
  constructor
  · -- the coordinate subspace spanned by the negative directions
    let ι : ({i // d i < 0} → ℂ) →ₗ[ℂ] (n → ℂ) :=
      LinearMap.pi (fun i => if h : d i < 0 then LinearMap.proj ⟨i, h⟩ else 0)
    have hι : ∀ c i, ι c i = if h : d i < 0 then c ⟨i, h⟩ else 0 := by
      intro c i
      simp only [ι, LinearMap.pi_apply]
      split_ifs <;> simp
    have hinj : Function.Injective ι := by
      intro c c' h
      funext j
      have := congrFun h j.1
      simpa only [hι, j.2, dite_true] using this
    refine ⟨LinearMap.range ι, ?_, ?_⟩
    · rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_fintype_fun_eq_card]
    · rintro x ⟨c, rfl⟩ hx0
      rw [hform_diagonal]
      have hle : ∀ i ∈ Finset.univ, d i * Complex.normSq (ι c i) ≤ 0 := by
        intro i _
        rw [hι]
        split_ifs with h
        · exact mul_nonpos_of_nonpos_of_nonneg h.le (Complex.normSq_nonneg _)
        · simp
      obtain ⟨i, hi⟩ : ∃ i, ι c i ≠ 0 := by
        by_contra h
        push Not at h
        exact hx0 (funext h)
      have hlt : d i * Complex.normSq (ι c i) < 0 := by
        have hdi : d i < 0 := by
          by_contra h
          simp [hι, h] at hi
        exact mul_neg_of_neg_of_pos hdi (Complex.normSq_pos.2 hi)
      calc ∑ i, d i * Complex.normSq (ι c i) < ∑ _i : n, (0 : ℝ) :=
            Finset.sum_lt_sum hle ⟨i, Finset.mem_univ _, hlt⟩
        _ = 0 := by simp
  · rintro k ⟨W, rfl, hW⟩
    let π : (n → ℂ) →ₗ[ℂ] ({i // d i < 0} → ℂ) := LinearMap.funLeft ℂ ℂ Subtype.val
    have hinj : Function.Injective (π ∘ₗ W.subtype) := by
      rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨x, hxW⟩ hx
      by_contra hx0
      have hx0' : x ≠ 0 := fun h => hx0 (Subtype.ext h)
      have hneg := hW x hxW hx0'
      rw [hform_diagonal] at hneg
      have hnn : 0 ≤ ∑ i, d i * Complex.normSq (x i) := by
        refine Finset.sum_nonneg fun i _ => ?_
        by_cases h : d i < 0
        · have : x i = 0 := congrFun hx ⟨i, h⟩
          simp [this]
        · exact mul_nonneg (not_lt.1 h) (Complex.normSq_nonneg _)
      linarith
    have := LinearMap.finrank_le_finrank_of_injective hinj
    rwa [Module.finrank_fintype_fun_eq_card] at this

/-- For a Hermitian matrix, the number of negative eigenvalues is the maximal dimension of a
subspace on which the Hermitian form is negative definite (min-max-free characterization).
Auxiliary for **Lemma `gap:lem:inertia`** (l. 3245). -/
theorem isGreatest_negDefDims {P : Matrix n n ℂ} (hP : P.IsHermitian) :
    IsGreatest (negDefDims P) (Fintype.card {i // hP.eigenvalues i < 0}) := by
  set U : Matrix n n ℂ := (hP.eigenvectorUnitary : Matrix n n ℂ) with hU
  have hspec : P = (Uᴴ)ᴴ * (diagonal (fun i => (hP.eigenvalues i : ℂ))) * Uᴴ := by
    have h := hP.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at h
    rw [conjTranspose_conjTranspose, ← star_eq_conjTranspose]
    exact h
  have hdet : IsUnit (Uᴴ).det := by
    have h1 : Uᴴ * U = 1 := by
      rw [hU, ← star_eq_conjTranspose]
      exact Unitary.coe_star_mul_self _
    exact isUnit_det_of_right_inverse h1
  have key := isGreatest_negDefDims_diagonal (n := n) (fun i => hP.eigenvalues i)
  rw [← negDefDims_conj _ _ hdet, ← hspec] at key
  exact key

/-- **Lemma `gap:lem:inertia`** (l. 3245; Paper I, Lemma 2.9), negative part, matrix version.
For a Hermitian matrix `P` and an invertible matrix `G`, the congruent matrix `G^* P G` has the
same number of negative eigenvalues as `P` (Sylvester's law of inertia).  For the normalized
trace `τ = n⁻¹ tr` of `Mₙ(ℂ)` (a finite von Neumann algebra with faithful normal trace) this is
`τ 1_{(-∞,0)}(G^* P G) = τ 1_{(-∞,0)}(P)`. -/
theorem card_neg_eigenvalues_conj {P : Matrix n n ℂ} (hP : P.IsHermitian) (G : Matrix n n ℂ)
    (hG : IsUnit G.det) :
    Fintype.card {i // (isHermitian_conjTranspose_mul_mul G hP).eigenvalues i < 0} =
      Fintype.card {i // hP.eigenvalues i < 0} :=
  (isGreatest_negDefDims (isHermitian_conjTranspose_mul_mul G hP)).unique
    (by rw [negDefDims_conj P G hG]; exact isGreatest_negDefDims hP)

/-- The number of zero eigenvalues of a Hermitian matrix is `n - rank`.  Auxiliary for
**Lemma `gap:lem:inertia`** (l. 3245). -/
lemma card_zero_eigenvalues {P : Matrix n n ℂ} (hP : P.IsHermitian) :
    Fintype.card {i // hP.eigenvalues i = 0} = Fintype.card n - P.rank := by
  rw [hP.rank_eq_card_non_zero_eigs, Fintype.card_subtype_compl]
  have := Fintype.card_subtype_le (fun i => hP.eigenvalues i = 0)
  omega

/-- **Lemma `gap:lem:inertia`** (l. 3245; Paper I, Lemma 2.9), kernel part, matrix version.
For a Hermitian matrix `P` and an invertible matrix `G`, `G^* P G` and `P` have the same number of
zero eigenvalues, i.e. `τ 1_{\{0\}}(G^* P G) = τ 1_{\{0\}}(P)` for the normalized trace. -/
theorem card_zero_eigenvalues_conj {P : Matrix n n ℂ} (hP : P.IsHermitian) (G : Matrix n n ℂ)
    (hG : IsUnit G.det) :
    Fintype.card {i // (isHermitian_conjTranspose_mul_mul G hP).eigenvalues i = 0} =
      Fintype.card {i // hP.eigenvalues i = 0} := by
  rw [card_zero_eigenvalues, card_zero_eigenvalues, rank_mul_eq_left_of_isUnit_det _ _ hG,
    rank_mul_eq_right_of_isUnit_det]
  rw [det_conjTranspose]
  exact hG.star

/-- The kernel of a congruent matrix: `ker (G^* P G) = G⁻¹ ker P` for invertible `G`.
Auxiliary for **Lemma `gap:lem:inertia`** (l. 3245). -/
lemma mulVec_conj_eq_zero_iff (P G : Matrix n n ℂ) (hG : IsUnit G.det) (x : n → ℂ) :
    (Gᴴ * P * G) *ᵥ x = 0 ↔ P *ᵥ (G *ᵥ x) = 0 := by
  rw [← mulVec_mulVec, ← mulVec_mulVec]
  have hinj : Function.Injective Gᴴ.mulVec := by
    refine mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det _).2 ?_)
    rw [det_conjTranspose]
    exact hG.star
  constructor
  · intro h
    exact hinj (h.trans (mulVec_zero _).symm)
  · intro h
    rw [h, mulVec_zero]

end Inertia

/-! ## 2. Kernel transfer and duality algebra -/

section Duality

variable {A : Type*} [Monoid A] [StarMul A]

/-- **Duality transfer** (proof of Theorem `dim:thm:center`, l. 1002–1007).  Let `♯ = star` be an
involutive anti-automorphism and `𝓕` a multiplicative map commuting with `♯`.  If
`Q^♯ J Q = 𝓕(Q)^♯ 𝓕(J) 𝓕(Q)` with `Q` invertible, then `J = Γ^♯ 𝓕(J) Γ` with
`Γ = 𝓕(Q) Q⁻¹`. -/
theorem duality_transfer (F : A →* A) (Q : Aˣ) (J : A)
    (h : star (Q : A) * J * Q = star (F Q) * F J * F Q) :
    J = star (F Q * (↑Q⁻¹ : A)) * F J * (F Q * (↑Q⁻¹ : A)) := by
  have h1 : star (↑Q⁻¹ : A) * star (Q : A) = 1 := by
    rw [← star_mul, Units.mul_inv, star_one]
  calc J = star (↑Q⁻¹ : A) * (star (Q : A) * J * Q) * ↑Q⁻¹ := by
          simp only [← mul_assoc, h1, one_mul, Units.mul_inv_cancel_right]
    _ = star (↑Q⁻¹ : A) * (star (F Q) * F J * F Q) * ↑Q⁻¹ := by rw [h]
    _ = star (F Q * (↑Q⁻¹ : A)) * F J * (F Q * (↑Q⁻¹ : A)) := by
          rw [star_mul]; simp only [mul_assoc]

omit [StarMul A] in
/-- **Duality of the transfer factor** (proof of Theorem `dim:thm:center`, l. 1006–1007).  If
moreover `𝓕(𝓕(Q)) = Q`, then `𝓕(Γ) = Γ⁻¹` for `Γ = 𝓕(Q) Q⁻¹`, i.e. `𝓕(Γ) Γ = 1 = Γ 𝓕(Γ)`. -/
theorem map_transfer_factor (F : A →* A) (Q : Aˣ) (hFF : F (F Q) = Q) :
    F (F Q * (↑Q⁻¹ : A)) * (F Q * (↑Q⁻¹ : A)) = 1 ∧
      (F Q * (↑Q⁻¹ : A)) * F (F Q * (↑Q⁻¹ : A)) = 1 := by
  have hu : F (↑Q⁻¹ : A) * F Q = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have hu' : F Q * F (↑Q⁻¹ : A) = 1 := by rw [← map_mul, Units.mul_inv, map_one]
  rw [map_mul, hFF]
  constructor
  · calc (Q : A) * F (↑Q⁻¹ : A) * (F Q * ↑Q⁻¹) = Q * (F (↑Q⁻¹ : A) * F Q) * ↑Q⁻¹ := by
          simp only [mul_assoc]
      _ = 1 := by rw [hu, mul_one, Units.mul_inv]
  · calc F Q * (↑Q⁻¹ : A) * (Q * F (↑Q⁻¹ : A)) = F Q * ((↑Q⁻¹ : A) * Q) * F (↑Q⁻¹ : A) := by
          simp only [mul_assoc]
      _ = 1 := by rw [Units.inv_mul, mul_one, hu']

/-- **Invertibility transfer** (proof of Theorem `dim:thm:center`, l. 1008–1011):
for invertible `Q`, `Q^♯ J Q` is invertible iff `J` is. -/
theorem isUnit_star_mul_mul_iff (Q : Aˣ) (J : A) :
    IsUnit (star (Q : A) * J * Q) ↔ IsUnit J := by
  obtain ⟨v, hv⟩ := (Q.isUnit).star
  rw [← hv, Units.isUnit_mul_units, Units.isUnit_units_mul]

/-- **Kernel transfer** (proof of Theorem `dim:thm:center`, l. 1011–1012):
`ker (Q^♯ J Q) = Q⁻¹ ker J` when `Q` is invertible and `Q^♯` is injective.  Here `Q^♯` is any
injective linear map (e.g. the adjoint of `Q`). -/
theorem ker_conj_eq {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (Qs J : M →ₗ[R] M) (Q : M ≃ₗ[R] M) (hQs : Function.Injective Qs) :
    LinearMap.ker (Qs ∘ₗ J ∘ₗ (Q : M →ₗ[R] M)) = (LinearMap.ker J).map (Q.symm : M →ₗ[R] M) := by
  ext x
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm, LinearMap.mem_ker, LinearMap.mem_ker]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  exact ⟨fun h => hQs (h.trans (map_zero Qs).symm), fun h => by rw [h, map_zero]⟩

end Duality

/-! ## 3. Transported flow and normalization ODE -/

section Flow

/-- **Transported flow identity** (eq. `dim:br:transported-flow`, l. 4334–4351), abstract form.
Let `∂` be an additive derivation of a star ring commuting with `star`, `T^* = -T`, `Γ` a unit.
If `J = Γ^♯ K Γ` (with `K = 𝓕(J)`) and `∂K = [T, K] + 𝒟` (eq. `dim:br:dual-flow`), then
`∂J = X^♯ J + J X + Γ^♯ 𝒟 Γ` with `X = Γ⁻¹ ∂Γ - Γ⁻¹ T Γ`. -/
theorem transported_flow {A : Type*} [Ring A] [StarRing A] (d : A →+ A)
    (hd : ∀ x y, d (x * y) = d x * y + x * d y) (hds : ∀ x, d (star x) = star (d x))
    (T K Dm J : A) (Γ : Aˣ) (hT : star T = -T) (hJ : J = star (Γ : A) * K * Γ)
    (hK : d K = T * K - K * T + Dm) :
    d J = star ((↑Γ⁻¹ : A) * d Γ - ↑Γ⁻¹ * T * Γ) * J + J * ((↑Γ⁻¹ : A) * d Γ - ↑Γ⁻¹ * T * Γ)
      + star (Γ : A) * Dm * Γ := by
  set g : A := (Γ : A) with hg
  set gi : A := ((Γ⁻¹ : Aˣ) : A) with hgi
  have h1 : ∀ x : A, star gi * (star g * x) = x := by
    intro x
    rw [← mul_assoc, ← star_mul, Units.mul_inv, star_one, one_mul]
  have h2 : ∀ x : A, g * (gi * x) = x := by
    intro x
    rw [← mul_assoc, Units.mul_inv, one_mul]
  subst hJ
  rw [hd, hd, hds, hK]
  simp only [star_sub, star_mul, hT, mul_add, add_mul, mul_sub, sub_mul, mul_assoc, h1, h2,
    neg_mul, mul_neg, sub_neg_eq_add]
  abel

/-- **Kernel cancellation** (used with `dim:br:transported-flow`): for Hermitian `B` and
`B u = 0`, one has `u^* (X^* B + B X) u = 0`. -/
theorem kernel_cancel {n : Type*} [Fintype n] (B X : Matrix n n ℂ) (hB : B.IsHermitian)
    (u : n → ℂ) (hu : B *ᵥ u = 0) :
    star u ⬝ᵥ ((Xᴴ * B + B * X) *ᵥ u) = 0 := by
  rw [add_mulVec, dotProduct_add, ← mulVec_mulVec, ← mulVec_mulVec, hu, mulVec_zero,
    dotProduct_zero, zero_add, dotProduct_mulVec]
  have : star u ᵥ* B = 0 := by
    rw [← hB.eq, ← star_mulVec, hu, star_zero]
  rw [this, zero_dotProduct]

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [StarRing A] [StarModule ℝ A]
  [ContinuousStar A]

/-- **Normalization ODE invariance** (proof of `gap:eq:normalization`, l. 2735–2742).  If
`Ṗ = X^* P + P X` and `Ẏ = -X Y`, then `d/dt (Y^* P Y) = 0`. -/
theorem hasDerivWithinAt_star_mul_mul {P X Y : ℝ → A} {s : Set ℝ} {t : ℝ}
    (hP : HasDerivWithinAt P (star (X t) * P t + P t * X t) s t)
    (hY : HasDerivWithinAt Y (-(X t * Y t)) s t) :
    HasDerivWithinAt (fun t => star (Y t) * P t * Y t) 0 s t := by
  have h := (hY.star.fun_mul hP).fun_mul hY
  convert h using 1
  simp only [star_neg, star_mul]
  noncomm_ring

/-- **Normalization ODE invariance, integrated** (proof of `gap:eq:normalization`,
l. 2735–2743): along `[a,b]`, if `Ṗ = X^* P + P X` and `Ẏ = -X Y`, then `Y^* P Y` is constant;
in the paper (`a = 0`, `b = 1`, `Y₁ = 1`) this gives `Y₀^* P₀ Y₀ = P₁`. -/
theorem star_mul_mul_const {P X Y : ℝ → A} {a b : ℝ}
    (hP : ∀ t ∈ Set.Icc a b, HasDerivWithinAt P (star (X t) * P t + P t * X t) (Set.Icc a b) t)
    (hY : ∀ t ∈ Set.Icc a b, HasDerivWithinAt Y (-(X t * Y t)) (Set.Icc a b) t) :
    ∀ t ∈ Set.Icc a b, star (Y t) * P t * Y t = star (Y b) * P b * Y b := by
  have hd : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt (fun t => star (Y t) * P t * Y t) 0 (Set.Icc a b) t :=
    fun t ht => hasDerivWithinAt_star_mul_mul (hP t ht) (hY t ht)
  have hc : ContinuousOn (fun t => star (Y t) * P t * Y t) (Set.Icc a b) :=
    fun t ht => (hd t ht).continuousWithinAt
  have key := constant_of_has_deriv_right_zero hc (fun x hx =>
    (hd x (Set.Ico_subset_Icc_self hx)).mono_of_mem_nhdsWithin
      (Filter.mem_of_superset (Icc_mem_nhdsGE hx.2) (Set.Icc_subset_Icc_left hx.1)))
  intro t ht
  by_cases hab : a ≤ b
  · rw [key t ht, key b ⟨hab, le_rfl⟩]
  · exact absurd (ht.1.trans ht.2) hab

end Flow

/-! ## 4. Projection sandwich -/

section Projection

open scoped ComplexOrder

variable {m κ : Type*} [Fintype m] [Fintype κ] [DecidableEq m] [DecidableEq κ]

omit [DecidableEq m] in
/-- Under the frame condition `(1-ε) ≤ F^*F` with `ε < 1`, the Gram matrix `F^*F` is invertible.
Auxiliary for the **projection sandwich** (l. 6555–6570). -/
lemma isUnit_det_gram (F : Matrix m κ ℂ) {ε : ℝ} (hε : ε < 1)
    (hlow : (Fᴴ * F - (1 - ε) • (1 : Matrix κ κ ℂ)).PosSemidef) : IsUnit (Fᴴ * F).det := by
  have hc : ((1 - ε) • (1 : Matrix κ κ ℂ)).PosDef := PosDef.one.smul (by linarith)
  have hpd : (Fᴴ * F).PosDef := by
    have := PosDef.posSemidef_add hlow hc
    rwa [sub_add_cancel] at this
  exact (isUnit_iff_isUnit_det _).1 hpd.isUnit

omit [DecidableEq m] in
/-- **Projection sandwich** (l. 6555–6570), algebraic part: if `(1-ε) ≤ F^*F` with `ε < 1`, then
`Π = F (F^*F)⁻¹ F^*` is an orthogonal projection (`Π^* = Π`, `Π² = Π`) of trace `k = #κ`. -/
theorem frameProj_spec (F : Matrix m κ ℂ) {ε : ℝ} (hε : ε < 1)
    (hlow : (Fᴴ * F - (1 - ε) • (1 : Matrix κ κ ℂ)).PosSemidef) :
    (F * (Fᴴ * F)⁻¹ * Fᴴ)ᴴ = F * (Fᴴ * F)⁻¹ * Fᴴ ∧
      (F * (Fᴴ * F)⁻¹ * Fᴴ) * (F * (Fᴴ * F)⁻¹ * Fᴴ) = F * (Fᴴ * F)⁻¹ * Fᴴ ∧
      (F * (Fᴴ * F)⁻¹ * Fᴴ).trace = Fintype.card κ := by
  have hdet := isUnit_det_gram F hε hlow
  refine ⟨?_, ?_, ?_⟩
  · rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
      conjTranspose_nonsing_inv, (isHermitian_conjTranspose_mul_self F).eq, Matrix.mul_assoc]
  · calc F * (Fᴴ * F)⁻¹ * Fᴴ * (F * (Fᴴ * F)⁻¹ * Fᴴ)
          = F * ((Fᴴ * F)⁻¹ * (Fᴴ * F)) * (Fᴴ * F)⁻¹ * Fᴴ := by
            simp only [Matrix.mul_assoc]
      _ = F * (Fᴴ * F)⁻¹ * Fᴴ := by rw [nonsing_inv_mul _ hdet, Matrix.mul_one]
  · rw [Matrix.mul_assoc, trace_mul_comm, Matrix.mul_assoc, nonsing_inv_mul _ hdet, trace_one]

omit [DecidableEq m] in
/-- **Projection sandwich** (l. 6555–6570), trace part: if
`(1-ε) ≤ F^*F ≤ (1+ε)` (Loewner order) with `0 ≤ ε < 1` and `k = #κ`, then
`k(1-ε) ≤ tr(F F^*) ≤ k(1+ε)`, equivalently
`(1+ε)⁻¹ tr(F F^*) ≤ k = tr Π ≤ (1-ε)⁻¹ tr(F F^*)`. -/
theorem trace_frame_bounds (F : Matrix m κ ℂ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1)
    (hlow : (Fᴴ * F - (1 - ε) • (1 : Matrix κ κ ℂ)).PosSemidef)
    (hup : ((1 + ε) • (1 : Matrix κ κ ℂ) - Fᴴ * F).PosSemidef) :
    (1 - ε) * Fintype.card κ ≤ (F * Fᴴ).trace.re ∧ (F * Fᴴ).trace.re ≤ (1 + ε) * Fintype.card κ ∧
      (1 + ε)⁻¹ * (F * Fᴴ).trace.re ≤ Fintype.card κ ∧
      (Fintype.card κ : ℝ) ≤ (1 - ε)⁻¹ * (F * Fᴴ).trace.re := by
  have h1 := (Complex.le_def.1 hlow.trace_nonneg).1
  have h2 := (Complex.le_def.1 hup.trace_nonneg).1
  rw [trace_mul_comm]
  rw [trace_sub, trace_smul, trace_one, Complex.sub_re, Complex.smul_re, Complex.natCast_re,
    smul_eq_mul, Complex.zero_re] at h1
  rw [trace_sub, trace_smul, trace_one, Complex.sub_re, Complex.smul_re, Complex.natCast_re,
    smul_eq_mul, Complex.zero_re] at h2
  have hl : (1 - ε) * Fintype.card κ ≤ (Fᴴ * F).trace.re := by linarith
  have hu : (Fᴴ * F).trace.re ≤ (1 + ε) * Fintype.card κ := by linarith
  have hp : 0 < 1 - ε := by linarith
  have hp' : 0 < 1 + ε := by linarith
  refine ⟨hl, hu, ?_, ?_⟩
  · rw [inv_mul_le_iff₀ hp']; linarith
  · rw [le_inv_mul_iff₀ hp]; linarith

omit [Fintype m] [DecidableEq m] in
open scoped MatrixOrder Matrix.Norms.L2Operator in
/-- Operator monotonicity of the inverse on scalar bounds: if `a ≤ M ≤ b` (Loewner order) with
`0 < a`, `0 < b`, then `b⁻¹ ≤ M⁻¹ ≤ a⁻¹`.  Auxiliary for the **projection sandwich**
(l. 6555–6570). -/
lemma inv_loewner_sandwich (M : Matrix κ κ ℂ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hlow : (M - a • (1 : Matrix κ κ ℂ)).PosSemidef)
    (hup : (b • (1 : Matrix κ κ ℂ) - M).PosSemidef) :
    (M⁻¹ - b⁻¹ • (1 : Matrix κ κ ℂ)).PosSemidef ∧
      (a⁻¹ • (1 : Matrix κ κ ℂ) - M⁻¹).PosSemidef := by
  have hMpd : M.PosDef := by
    have := PosDef.posSemidef_add hlow (PosDef.one.smul ha)
    rwa [sub_add_cancel] at this
  have scal : ∀ c : ℝ, c ≠ 0 →
      (c • (1 : Matrix κ κ ℂ)) * (c⁻¹ • (1 : Matrix κ κ ℂ)) = 1 := by
    intro c hc
    rw [smul_mul_assoc, mul_smul_comm, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hc, one_smul]
  have scal' : ∀ c : ℝ, c ≠ 0 →
      (c⁻¹ • (1 : Matrix κ κ ℂ)) * (c • (1 : Matrix κ κ ℂ)) = 1 := by
    intro c hc
    simpa only [inv_inv] using scal c⁻¹ (inv_ne_zero hc)
  let Mu : (Matrix κ κ ℂ)ˣ := hMpd.isUnit.unit
  let Au : (Matrix κ κ ℂ)ˣ := ⟨a • 1, a⁻¹ • 1, scal a ha.ne', scal' a ha.ne'⟩
  let Bu : (Matrix κ κ ℂ)ˣ := ⟨b • 1, b⁻¹ • 1, scal b hb.ne', scal' b hb.ne'⟩
  have hMu : (Mu : Matrix κ κ ℂ) = M := hMpd.isUnit.unit_spec
  have hMu' : ((Mu⁻¹ : (Matrix κ κ ℂ)ˣ) : Matrix κ κ ℂ) = M⁻¹ := by
    rw [Matrix.coe_units_inv, hMu]
  have hM0 : (0 : Matrix κ κ ℂ) ≤ M := hMpd.posSemidef.nonneg
  have hA0 : (0 : Matrix κ κ ℂ) ≤ (Au : Matrix κ κ ℂ) := (PosDef.one.smul ha).posSemidef.nonneg
  constructor
  · have h := CStarAlgebra.inv_le_inv (a := Mu) (b := Bu) (by rw [hMu]; exact hM0)
      (by rw [hMu]; exact hup)
    rw [hMu'] at h
    exact h
  · have h := CStarAlgebra.inv_le_inv (a := Au) (b := Mu) hA0 (by rw [hMu]; exact hlow)
    rw [hMu'] at h
    exact h

omit [DecidableEq m] in
open scoped MatrixOrder in
/-- **Projection sandwich** (l. 6555–6559): if `(1-ε) ≤ F^*F ≤ (1+ε)` (Loewner order) with
`0 ≤ ε < 1`, then for `Π = F (F^*F)⁻¹ F^*`,
`(1+ε)⁻¹ F F^* ≤ Π ≤ (1-ε)⁻¹ F F^*` in the Loewner order. -/
theorem frameProj_loewner (F : Matrix m κ ℂ) {ε : ℝ} (hε0 : 0 ≤ ε) (hε : ε < 1)
    (hlow : (Fᴴ * F - (1 - ε) • (1 : Matrix κ κ ℂ)).PosSemidef)
    (hup : ((1 + ε) • (1 : Matrix κ κ ℂ) - Fᴴ * F).PosSemidef) :
    (1 + ε)⁻¹ • (F * Fᴴ) ≤ F * (Fᴴ * F)⁻¹ * Fᴴ ∧
      F * (Fᴴ * F)⁻¹ * Fᴴ ≤ (1 - ε)⁻¹ • (F * Fᴴ) := by
  obtain ⟨h1, h2⟩ := inv_loewner_sandwich (Fᴴ * F) (a := 1 - ε) (b := 1 + ε) (by linarith)
    (by linarith) hlow hup
  constructor
  · rw [Matrix.le_iff]
    have := h1.mul_mul_conjTranspose_same F
    convert this using 1
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]
  · rw [Matrix.le_iff]
    have := h2.mul_mul_conjTranspose_same F
    convert this using 1
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one]

end Projection

/-! ## 5. Root–Gram identity -/

section RootGram

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Lemma `dim:br:root-gram`** (l. 4489–4560), off-diagonal Gram identity.  For the pencil
`B(E) = A - E + R(E)` with `A` and `R(E)` Hermitian (`E` real), kernel vectors
`B(e_i) u_i = 0`, `B(e_j) u_j = 0` at unequal real roots satisfy
`u_i^* u_j = u_i^* ((R(e_i) - R(e_j)) / (e_i - e_j)) u_j`. -/
theorem root_gram_offdiag (Amat : Matrix n n ℂ) (R : ℝ → Matrix n n ℂ) (hA : Amat.IsHermitian)
    (hR : ∀ e, (R e).IsHermitian) {ei ej : ℝ} (hne : ei ≠ ej) {ui uj : n → ℂ}
    (hi : (Amat - (ei : ℂ) • 1 + R ei) *ᵥ ui = 0) (hj : (Amat - (ej : ℂ) • 1 + R ej) *ᵥ uj = 0) :
    star ui ⬝ᵥ uj = star ui ⬝ᵥ ((((ei : ℂ) - ej)⁻¹ • (R ei - R ej)) *ᵥ uj) := by
  set Bi := Amat - (ei : ℂ) • 1 + R ei
  set Bj := Amat - (ej : ℂ) • 1 + R ej
  have hBi : Bi.IsHermitian := by
    refine (hA.sub ?_).add (hR ei)
    simp [IsHermitian, conjTranspose_smul]
  have e1 : star ui ⬝ᵥ (Bi *ᵥ uj) = 0 := by
    rw [dotProduct_mulVec, ← hBi.eq, ← star_mulVec, hi, star_zero, zero_dotProduct]
  have e2 : star ui ⬝ᵥ (Bj *ᵥ uj) = 0 := by rw [hj, dotProduct_zero]
  have hmat : R ei - R ej = Bi - Bj + ((ei : ℂ) - ej) • (1 : Matrix n n ℂ) := by
    simp only [Bi, Bj, sub_smul]; abel
  have key : star ui ⬝ᵥ ((R ei - R ej) *ᵥ uj) = ((ei : ℂ) - ej) * (star ui ⬝ᵥ uj) := by
    rw [hmat, add_mulVec, sub_mulVec, dotProduct_add, dotProduct_sub, e1, e2, smul_mulVec,
      one_mulVec, dotProduct_smul, smul_eq_mul]
    ring
  have hne' : ((ei : ℂ) - ej) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hne)
  rw [smul_mulVec, dotProduct_smul, key, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hne', one_mul]

/-- **Lemma `dim:br:root-gram`** (l. 4560–4575), polynomial divided-difference form.  For
`R(E) = ∑_{k=1}^{K} E^k R_k` with Hermitian `R_k` (here `Rk k` is the coefficient of `E^{k+1}`),
`u_i^* u_j = ∑_k ∑_{ℓ=0}^{k-1} e_i^ℓ e_j^{k-1-ℓ} u_i^* R_k u_j` at unequal real roots: this is
the off-diagonal entry of `G = I + ∑_k ∑_ℓ Λ^ℓ 𝒰^* R_k 𝒰 Λ^{k-1-ℓ}`. -/
theorem root_gram_poly (Amat : Matrix n n ℂ) (K : ℕ) (Rk : ℕ → Matrix n n ℂ)
    (hA : Amat.IsHermitian) (hR : ∀ k, (Rk k).IsHermitian) {ei ej : ℝ} (hne : ei ≠ ej)
    {ui uj : n → ℂ}
    (hi : (Amat - (ei : ℂ) • 1 + ∑ k ∈ Finset.range K, ((ei : ℂ) ^ (k + 1)) • Rk k) *ᵥ ui = 0)
    (hj : (Amat - (ej : ℂ) • 1 + ∑ k ∈ Finset.range K, ((ej : ℂ) ^ (k + 1)) • Rk k) *ᵥ uj = 0) :
    star ui ⬝ᵥ uj = ∑ k ∈ Finset.range K,
      (∑ l ∈ Finset.range (k + 1), (ei : ℂ) ^ l * (ej : ℂ) ^ (k - l)) *
        (star ui ⬝ᵥ (Rk k *ᵥ uj)) := by
  set R : ℝ → Matrix n n ℂ := fun e => ∑ k ∈ Finset.range K, ((e : ℂ) ^ (k + 1)) • Rk k
  have hRh : ∀ e, (R e).IsHermitian := by
    intro e
    simp only [R, IsHermitian, conjTranspose_sum, conjTranspose_smul, (hR _).eq]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp
  rw [root_gram_offdiag Amat R hA hRh hne hi hj]
  have hne' : ((ei : ℂ) - ej) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hne)
  have hdiff : R ei - R ej =
      ∑ k ∈ Finset.range K, (((ei : ℂ) ^ (k + 1)) - ((ej : ℂ) ^ (k + 1))) • Rk k := by
    simp only [R, ← Finset.sum_sub_distrib, ← sub_smul]
  rw [hdiff, Finset.smul_sum, sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_smul, smul_mulVec, dotProduct_smul, smul_eq_mul]
  congr 1
  rw [← Commute.geom_sum₂_mul (Commute.all _ _), Nat.add_sub_cancel,
    mul_comm ((ei : ℂ) - ej)⁻¹, mul_assoc, mul_inv_cancel₀ hne', mul_one]

/-- **Gram bound** (Lemma `dim:br:root-gram`, eq. `dim:br:gram-bound`, l. 4575–4582).
In a normed ring, if `G = 1 + S` with `‖S‖ ≤ d ‖G‖` and `d < 1`, then `‖G‖ ≤ (1 - d)⁻¹`.
(In the lemma `G = 𝒰^*𝒰`, `‖G‖ = ‖𝒰‖²`, and `d = d_* = ∑ k M₀^{k-1} ‖R_k‖`.) -/
theorem gram_bound {B : Type*} [NormedRing B] [NormOneClass B] (G S : B) {d : ℝ} (hd : d < 1)
    (hG : G = 1 + S) (hS : ‖S‖ ≤ d * ‖G‖) : ‖G‖ ≤ (1 - d)⁻¹ := by
  have h : ‖G‖ ≤ 1 + d * ‖G‖ := by
    calc ‖G‖ = ‖1 + S‖ := by rw [hG]
      _ ≤ ‖(1 : B)‖ + ‖S‖ := norm_add_le _ _
      _ ≤ 1 + d * ‖G‖ := by rw [norm_one]; linarith
  rw [← one_div, le_div_iff₀ (by linarith)]
  linarith

end RootGram

/-! ## 6. Boundary inclusion, finite core -/

section Boundary

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

/-- **Woodbury inverse** (proof of `dim:br:boundary-inclusion`, l. 4812–4822).  Let
`K = D + 𝒢^* F 𝒢`, `D - λ` invertible and `T = 𝒢 (D - λ)⁻¹ 𝒢^*`.  If `1 + F T` is invertible,
then `K - λ` is invertible, with inverse
`(D-λ)⁻¹ - (D-λ)⁻¹ 𝒢^* (1 + F T)⁻¹ F 𝒢 (D-λ)⁻¹`. -/
theorem woodbury_mul_eq_one (D : Matrix n n ℂ) (G : Matrix m n ℂ) (F : Matrix m m ℂ) (lam : ℂ)
    (hD : IsUnit (D - lam • 1).det)
    (hW : IsUnit (1 + F * (G * (D - lam • 1)⁻¹ * Gᴴ)).det) :
    (D + Gᴴ * F * G - lam • 1) *
      ((D - lam • 1)⁻¹ - (D - lam • 1)⁻¹ * Gᴴ * (1 + F * (G * (D - lam • 1)⁻¹ * Gᴴ))⁻¹ * F * G *
        (D - lam • 1)⁻¹) = 1 := by
  set Dl := D - lam • (1 : Matrix n n ℂ)
  set Rr := Dl⁻¹
  set W := (1 + F * (G * Rr * Gᴴ))⁻¹
  have hDl : Dl * Rr = 1 := mul_nonsing_inv _ hD
  have hDl' : ∀ Y : Matrix n n ℂ, Dl * (Rr * Y) = Y := by
    intro Y; rw [← Matrix.mul_assoc, hDl, Matrix.one_mul]
  have hWW : (1 + F * (G * Rr * Gᴴ)) * W = 1 := mul_nonsing_inv _ hW
  have e1 : ∀ Z : Matrix m n ℂ,
      W * (F * Z) + F * (G * (Rr * (Gᴴ * (W * (F * Z))))) = F * Z := by
    intro Z
    have := congrArg (· * (F * Z)) hWW
    simpa only [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc] using this
  have e2 : Gᴴ * (W * (F * (G * Rr))) + Gᴴ * (F * (G * (Rr * (Gᴴ * (W * (F * (G * Rr)))))))
      = Gᴴ * (F * (G * Rr)) := by
    rw [← Matrix.mul_add, e1]
  have hK : D + Gᴴ * F * G - lam • 1 = Dl + Gᴴ * F * G := by
    simp only [Dl]; abel
  rw [hK]
  simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_assoc, hDl, hDl']
  rw [← e2]
  abel

/-- **Woodbury inverse, invertibility form** (proof of `dim:br:boundary-inclusion`). -/
theorem woodbury_isUnit (D : Matrix n n ℂ) (G : Matrix m n ℂ) (F : Matrix m m ℂ) (lam : ℂ)
    (hD : IsUnit (D - lam • 1).det)
    (hW : IsUnit (1 + F * (G * (D - lam • 1)⁻¹ * Gᴴ)).det) :
    IsUnit (D + Gᴴ * F * G - lam • 1).det :=
  isUnit_det_of_right_inverse (woodbury_mul_eq_one D G F lam hD hW)

open scoped Matrix.Norms.L2Operator in
/-- **Neumann step of the boundary inclusion** (`dim:br:boundary-inclusion`, l. 4812–4822): with
the `ℓ²` operator norm, if `λ ∉ spec D` and `‖F‖ ‖𝒢 (D-λ)⁻¹ 𝒢^*‖ < 1`, then
`K - λ = D + 𝒢^* F 𝒢 - λ` is invertible. -/
theorem boundary_isUnit_of_norm_lt (D : Matrix n n ℂ) (G : Matrix m n ℂ) (F : Matrix m m ℂ)
    (lam : ℂ) (hD : IsUnit (D - lam • 1).det)
    (hnorm : ‖F‖ * ‖G * (D - lam • 1)⁻¹ * Gᴴ‖ < 1) :
    IsUnit (D + Gᴴ * F * G - lam • 1).det := by
  refine woodbury_isUnit D G F lam hD ?_
  have h : ‖-(F * (G * (D - lam • 1)⁻¹ * Gᴴ))‖ < 1 := by
    rw [norm_neg]; exact (norm_mul_le _ _).trans_lt hnorm
  have := (Units.oneSub _ h).isUnit
  rw [Units.val_oneSub, sub_neg_eq_add] at this
  exact (isUnit_iff_isUnit_det _).1 this

open scoped Matrix.Norms.L2Operator in
/-- **Boundary inclusion, contrapositive form** (`dim:br:boundary-inclusion`, l. 4812–4824): if
`λ` is an eigenvalue of `K = D + 𝒢^* F 𝒢` but not of `D`, and `‖F‖ ≤ ε` with `ε > 0`, then the
boundary resolvent `T = 𝒢 (D-λ)⁻¹ 𝒢^*` has `‖T‖ ≥ ε⁻¹`. -/
theorem boundary_resolvent_norm_ge (D : Matrix n n ℂ) (G : Matrix m n ℂ) (F : Matrix m m ℂ)
    (lam : ℂ) {ε : ℝ} (hε : 0 < ε) (hF : ‖F‖ ≤ ε) (hD : IsUnit (D - lam • 1).det)
    {w : n → ℂ} (hw : w ≠ 0) (hKw : (D + Gᴴ * F * G) *ᵥ w = lam • w) :
    ε⁻¹ ≤ ‖G * (D - lam • 1)⁻¹ * Gᴴ‖ := by
  by_contra hlt
  push Not at hlt
  have hnorm : ‖F‖ * ‖G * (D - lam • 1)⁻¹ * Gᴴ‖ < 1 := by
    calc ‖F‖ * ‖G * (D - lam • 1)⁻¹ * Gᴴ‖ ≤ ε * ‖G * (D - lam • 1)⁻¹ * Gᴴ‖ :=
          mul_le_mul_of_nonneg_right hF (norm_nonneg _)
      _ < ε * ε⁻¹ := mul_lt_mul_of_pos_left hlt hε
      _ = 1 := mul_inv_cancel₀ hε.ne'
  have hU := boundary_isUnit_of_norm_lt D G F lam hD hnorm
  have hinj := mulVec_injective_iff_isUnit.2 ((isUnit_iff_isUnit_det _).2 hU)
  apply hw
  apply hinj
  rw [mulVec_zero, sub_mulVec, hKw, smul_mulVec, one_mulVec, sub_self]

omit [DecidableEq m] in
/-- **Rank-one construction** (proof of `dim:br:boundary-inclusion`, l. 4824–4833).  Let
`T = 𝒢 (D-λ)⁻¹ 𝒢^*`, `T v₀ = μ₀ v₀` with `μ₀ ≠ 0` real and `v₀^* v₀ = 1`.  Put
`V = -μ₀⁻¹ v₀ v₀^*` and `w₀ = (D-λ)⁻¹ 𝒢^* v₀`.  Then `V` is Hermitian,
`(D + 𝒢^* V 𝒢 - λ) w₀ = 0`, and `w₀ ≠ 0` when `𝒢^*` is injective. -/
theorem rank_one_kernel (D : Matrix n n ℂ) (G : Matrix m n ℂ) (lam : ℂ)
    (hD : IsUnit (D - lam • 1).det) (v₀ : m → ℂ) (μ : ℝ) (hμ : μ ≠ 0)
    (hT : (G * (D - lam • 1)⁻¹ * Gᴴ) *ᵥ v₀ = (μ : ℂ) • v₀) (hv : star v₀ ⬝ᵥ v₀ = 1) :
    (D + Gᴴ * ((-(μ : ℂ)⁻¹) • vecMulVec v₀ (star v₀)) * G - lam • 1) *ᵥ
        ((D - lam • 1)⁻¹ *ᵥ (Gᴴ *ᵥ v₀)) = 0 ∧
      ((-(μ : ℂ)⁻¹) • vecMulVec v₀ (star v₀)).IsHermitian ∧
      (Function.Injective Gᴴ.mulVec → (D - lam • 1)⁻¹ *ᵥ (Gᴴ *ᵥ v₀) ≠ 0) := by
  set Dl := D - lam • (1 : Matrix n n ℂ)
  set V := (-(μ : ℂ)⁻¹) • vecMulVec v₀ (star v₀)
  have hμ' : (μ : ℂ) ≠ 0 := by exact_mod_cast hμ
  have hDl : Dl * Dl⁻¹ = 1 := mul_nonsing_inv _ hD
  have hGw : G *ᵥ (Dl⁻¹ *ᵥ (Gᴴ *ᵥ v₀)) = (μ : ℂ) • v₀ := by
    rw [← hT, ← mulVec_mulVec, ← mulVec_mulVec]
  have hVv : V *ᵥ ((μ : ℂ) • v₀) = -v₀ := by
    rw [mulVec_smul, smul_mulVec, vecMulVec_mulVec, hv, MulOpposite.op_one, one_smul, smul_smul,
      mul_neg, mul_inv_cancel₀ hμ', neg_one_smul]
  refine ⟨?_, ?_, ?_⟩
  · have hK : D + Gᴴ * V * G - lam • 1 = Dl + Gᴴ * V * G := by
      simp only [Dl]; abel
    rw [hK, add_mulVec, mulVec_mulVec, hDl, one_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hGw,
      hVv, mulVec_neg, add_neg_cancel]
  · simp only [V, IsHermitian, conjTranspose_smul, conjTranspose_vecMulVec, star_star]
    congr 1
    simp
  · intro hinj h0
    have : Gᴴ *ᵥ v₀ = 0 := by
      have h1 : Dl *ᵥ (Dl⁻¹ *ᵥ (Gᴴ *ᵥ v₀)) = Dl *ᵥ 0 := by rw [h0]
      rw [mulVec_mulVec, hDl, one_mulVec, mulVec_zero] at h1
      exact h1
    have hv0 : v₀ = 0 := hinj (this.trans (mulVec_zero _).symm)
    rw [hv0] at hv
    simp at hv

end Boundary

end MatrixLemmas
end SGD
