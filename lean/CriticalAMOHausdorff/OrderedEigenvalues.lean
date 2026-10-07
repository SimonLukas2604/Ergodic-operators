/-
Copyright (c) 2026. Formalization of
  S. Becker, S. Jitomirskaya, I. Krasovsky, "Critical almost Mathieu operator: hidden
  singularity, gap continuity, and the Hausdorff dimension of the spectrum"
  (arXiv:1909.04429v2).

# Ordered eigenvalues, min–max monotonicity, trace norm and the Lidskii inequality

Matrix-analysis input for §"Finite covers for the spectrum" of the paper:

* the min–max principle in the form used in eq. (`minmax`) (proof of Proposition
  `prop-cover1`, `.tex` l. 1708–1716): if `A ≤ B` in the Loewner order then
  `λ_j(A) ≤ λ_j(B)` for the increasingly ordered eigenvalues (`eig_mono`);
* unitary invariance of ordered eigenvalues (proof of Lemma `lemma-flow`, l. 1373–1374)
  (`eig_unitary_conj`);
* the trace norm `‖·‖_{S_1}` and its basic properties: duality with sign matrices,
  the triangle inequality, unitary invariance, and `‖C‖_{S_1} ≤ √(rank C) ‖C‖_{S_2}`
  (used in the proof of Proposition `prop-phase-variation`, l. 1650–1668);
* the **Lidskii inequality** (l. 1383–1389, cited from Bhatia, §9):
  `∑_j |λ_j(A) - λ_j(B)| ≤ ‖A - B‖_{S_1}` (`lidskii`).

## Conventions

* Matrices are `Matrix (Fin N) (Fin N) ℂ`; the Loewner order `A ≤ B` is expressed as
  `(B - A).PosSemidef` (which is Mathlib's `Matrix.le_iff` for the scoped `MatrixOrder`).
* `eig A : Fin N → ℝ` is the *increasingly ordered* list of eigenvalues of a Hermitian `A`
  (`λ_1 ≤ ⋯ ≤ λ_N` in the paper, here indexed by `Fin N`), defined from Mathlib's
  (decreasingly sorted) `IsHermitian.eigenvalues₀`; it is `0` for non-Hermitian `A`.
* `traceNorm C = ∑ √(eig (Cᴴ C))` is the genuine trace norm (sum of singular values) for every
  matrix; for Hermitian `C` it equals `∑ |λ_j(C)|` (`traceNorm_eq_sum_abs`).  All the
  inequalities are proved for Hermitian matrices, which is all the paper needs (the error
  terms `𝓔(x)` are Hermitian).
* `hsNorm C = (∑ |C_ij|²)^{1/2}` is the Hilbert–Schmidt norm `‖·‖_{S_2}`.

## Proof strategy

Min–max is proved without eigenvectors: the number of eigenvalues `< t` of a Hermitian `A`
equals the maximal dimension of a subspace on which `x ↦ ⟪x, (A - t) x⟫` is negative definite
(Sylvester inertia; the inertia lemmas of §1 are adapted from
`SpectralGapsDimension/MatrixLemmas.lean`, copied here so this file only depends on Mathlib).
Hence `A ≤ B` decreases these counting functions, which is equivalent to `eig A ≤ eig B`.

Lidskii's inequality follows the elementary argument: write `A - B = C₊ - C₋` (Jordan
decomposition, `C_± ≥ 0`, `tr C₊ + tr C₋ = ‖A - B‖_{S_1}`), put `M = B + C₊ = A + C₋ ≥ A, B`;
then `|λ_j(A) - λ_j(B)| ≤ (λ_j(M) - λ_j(A)) + (λ_j(M) - λ_j(B))` and summing gives
`tr C₋ + tr C₊`.

No `sorry`s in this file.
-/
import Mathlib

noncomputable section

open Matrix
open scoped ComplexOrder

namespace CAH
namespace Flow

/-! ## 1. Negative-definite subspaces (inertia) -/

section Inertia

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The real part of the Hermitian form `x ↦ x^* P x`. -/
def hform (P : Matrix n n ℂ) (x : n → ℂ) : ℝ := (star x ⬝ᵥ (P *ᵥ x)).re

/-- Dimensions of subspaces on which the Hermitian form of `P` is negative definite. -/
def negDefDims (P : Matrix n n ℂ) : Set ℕ :=
  {k | ∃ W : Submodule ℂ (n → ℂ), Module.finrank ℂ W = k ∧
      ∀ x ∈ W, x ≠ 0 → hform P x < 0}

lemma hform_conj (P G : Matrix n n ℂ) (x : n → ℂ) :
    hform (Gᴴ * P * G) x = hform P (G *ᵥ x) := by
  unfold hform
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← star_mulVec]

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

lemma hform_diagonal (d : n → ℝ) (x : n → ℂ) :
    hform (diagonal (fun i => (d i : ℂ))) x = ∑ i, d i * Complex.normSq (x i) := by
  unfold hform
  simp only [dotProduct, mulVec_diagonal, Complex.re_sum, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.star_def, mul_left_comm, Complex.re_ofReal_mul, Complex.conj_mul']
  norm_cast
  simp [Complex.normSq_eq_norm_sq]

lemma isGreatest_negDefDims_diagonal (d : n → ℝ) :
    IsGreatest (negDefDims (diagonal (fun i => (d i : ℂ)))) (Fintype.card {i // d i < 0}) := by
  classical
  constructor
  · let ι : ({i // d i < 0} → ℂ) →ₗ[ℂ] (n → ℂ) :=
      LinearMap.pi (fun i => if h : d i < 0 then LinearMap.proj ⟨i, h⟩ else 0)
    have hι : ∀ c i, ι c i = if h : d i < 0 then c ⟨i, h⟩ else 0 := by
      intro c i
      simp only [ι, LinearMap.pi_apply]
      split_ifs <;> simp
    have hinj : Function.Injective ι := by
      intro c c' h
      funext j
      have := congrFun h j.1
      rwa [hι, hι, dif_pos j.2, dif_pos j.2] at this
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
        push_neg at h
        exact hx0 (funext h)
      have hlt : d i * Complex.normSq (ι c i) < 0 := by
        have hdi : d i < 0 := by
          by_contra h
          rw [hι, dif_neg h] at hi
          exact hi rfl
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

/-- Unitary conjugation does not change the negative-definite dimensions of `A - t`. -/
lemma negDefDims_unitary_conj {A U : Matrix n n ℂ} (h1 : Uᴴ * U = 1) (h2 : U * Uᴴ = 1)
    (t : ℝ) :
    negDefDims (U * A * Uᴴ - (t : ℂ) • 1) = negDefDims (A - (t : ℂ) • 1) := by
  have hdet : IsUnit (Uᴴ).det := isUnit_det_of_right_inverse h1
  have e : U * A * Uᴴ - (t : ℂ) • 1 = (Uᴴ)ᴴ * (A - (t : ℂ) • 1) * Uᴴ := by
    rw [conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.mul_one, Matrix.smul_mul, h2]
  rw [e, negDefDims_conj _ _ hdet]

/-- For `U` unitary and `d` real, the number of `i` with `d i < t` is the maximal dimension of
a subspace on which `U diag(d) U^* - t` is negative definite. -/
lemma isGreatest_negDefDims_conjDiag {U : Matrix n n ℂ} (h1 : Uᴴ * U = 1) (h2 : U * Uᴴ = 1)
    (d : n → ℝ) (t : ℝ) :
    IsGreatest (negDefDims (U * diagonal (fun i => (d i : ℂ)) * Uᴴ - (t : ℂ) • 1))
      (Fintype.card {i // d i < t}) := by
  rw [negDefDims_unitary_conj h1 h2]
  have hd : diagonal (fun i => (d i : ℂ)) - (t : ℂ) • 1 =
      diagonal (fun i => ((d i - t : ℝ) : ℂ)) := by
    ext i j
    by_cases h : i = j <;> simp [diagonal_apply, h, one_apply]
  rw [hd]
  have key : IsGreatest (negDefDims (diagonal (fun i => ((d i - t : ℝ) : ℂ))))
      (Fintype.card {i // d i - t < 0}) := isGreatest_negDefDims_diagonal (fun i => d i - t)
  have hc : Fintype.card {i // d i - t < 0} = Fintype.card {i // d i < t} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun i => sub_neg)
  rwa [hc] at key

/-- Spectral theorem in the form `A = U diag(λ) U^*`. -/
lemma spectral_eq {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n ℂ) * diagonal (fun i => (hA.eigenvalues i : ℂ)) *
      (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  have h := hA.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at h
  rw [← star_eq_conjTranspose]
  exact h

lemma eigU_star_mul {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * (hA.eigenvectorUnitary : Matrix n n ℂ) = 1 := by
  rw [← star_eq_conjTranspose]
  exact Unitary.coe_star_mul_self _

lemma eigU_mul_star {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix n n ℂ) * (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ = 1 :=
  mul_eq_one_comm.1 (eigU_star_mul hA)

/-- The number of eigenvalues `< t` of a Hermitian `A` is the maximal dimension of a subspace on
which `A - t` is negative definite. -/
theorem isGreatest_negDefDims_sub {A : Matrix n n ℂ} (hA : A.IsHermitian) (t : ℝ) :
    IsGreatest (negDefDims (A - (t : ℂ) • 1)) (Fintype.card {i // hA.eigenvalues i < t}) := by
  have := isGreatest_negDefDims_conjDiag (eigU_star_mul hA) (eigU_mul_star hA) hA.eigenvalues t
  rwa [← spectral_eq hA] at this

lemma hform_sub_le {A B : Matrix n n ℂ} (h : (B - A).PosSemidef) (t : ℝ) (x : n → ℂ) :
    hform (A - (t : ℂ) • 1) x ≤ hform (B - (t : ℂ) • 1) x := by
  have e : B - (t : ℂ) • 1 = (A - (t : ℂ) • 1) + (B - A) := by abel
  have h0 : 0 ≤ (star x ⬝ᵥ ((B - A) *ᵥ x)).re := h.re_dotProduct_nonneg x
  unfold hform
  rw [e, add_mulVec, dotProduct_add, Complex.add_re]
  linarith

lemma negDefDims_sub_anti {A B : Matrix n n ℂ} (h : (B - A).PosSemidef) (t : ℝ) :
    negDefDims (B - (t : ℂ) • 1) ⊆ negDefDims (A - (t : ℂ) • 1) := by
  rintro k ⟨W, hk, hW⟩
  exact ⟨W, hk, fun x hx hx0 => lt_of_le_of_lt (hform_sub_le h t x) (hW x hx hx0)⟩

/-- If `A ≤ B` then `B` has at most as many eigenvalues `< t` as `A`. -/
theorem card_lt_anti {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : (B - A).PosSemidef) (t : ℝ) :
    Fintype.card {i // hB.eigenvalues i < t} ≤ Fintype.card {i // hA.eigenvalues i < t} :=
  (isGreatest_negDefDims_sub hB t).mono (isGreatest_negDefDims_sub hA t)
    (negDefDims_sub_anti h t)

end Inertia

/-! ## 2. Ordered eigenvalues -/

section Ordered

variable {N : ℕ}

/-- The increasingly ordered eigenvalues `λ_1 ≤ ⋯ ≤ λ_N` of a Hermitian matrix (indexed by
`Fin N`); junk value `0` for non-Hermitian matrices. -/
def eig (A : Matrix (Fin N) (Fin N) ℂ) : Fin N → ℝ :=
  if hA : A.IsHermitian then
    fun j => hA.eigenvalues₀ (Fin.rev (Fin.cast (Fintype.card_fin N).symm j))
  else 0

lemma eig_def {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) (j : Fin N) :
    eig A j = hA.eigenvalues₀ (Fin.rev (Fin.cast (Fintype.card_fin N).symm j)) := by
  simp only [eig, dite_cond_eq_true (eq_true hA)]

/-- The ordered eigenvalues are increasing. -/
theorem eig_monotone (A : Matrix (Fin N) (Fin N) ℂ) : Monotone (eig A) := by
  by_cases hA : A.IsHermitian
  · intro i j hij
    rw [eig_def hA, eig_def hA]
    apply hA.eigenvalues₀_antitone
    rw [Fin.rev_le_rev]
    exact hij
  · simp only [eig, dif_neg hA]
    exact fun _ _ _ => le_rfl

/-- The ordered eigenvalues are a permutation of Mathlib's `IsHermitian.eigenvalues`. -/
theorem exists_perm {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) :
    ∃ σ : Fin N ≃ Fin N, ∀ j, eig A j = hA.eigenvalues (σ j) := by
  refine ⟨((finCongr (Fintype.card_fin N).symm).trans Fin.revPerm).trans
    (Fintype.equivOfCardEq (Fintype.card_fin _)), fun j => ?_⟩
  rw [eig_def hA]
  simp only [IsHermitian.eigenvalues, Equiv.trans_apply, Equiv.symm_apply_apply, finCongr_apply,
    Fin.revPerm_apply]

lemma sum_eig {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) (φ : ℝ → ℝ) :
    ∑ j, φ (eig A j) = ∑ i, φ (hA.eigenvalues i) := by
  obtain ⟨σ, hσ⟩ := exists_perm hA
  simp only [hσ]
  exact Equiv.sum_comp σ (fun i => φ (hA.eigenvalues i))

lemma card_eig_lt {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) (t : ℝ) :
    Fintype.card {j // eig A j < t} = Fintype.card {i // hA.eigenvalues i < t} := by
  obtain ⟨σ, hσ⟩ := exists_perm hA
  exact Fintype.card_congr (σ.subtypeEquiv fun j => by rw [hσ])

lemma range_eig {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) :
    Set.range (eig A) = Set.range hA.eigenvalues := by
  obtain ⟨σ, hσ⟩ := exists_perm hA
  ext μ
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨σ j, (hσ j).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨σ.symm i, by rw [hσ, Equiv.apply_symm_apply]⟩

/-- The (real) spectrum of a Hermitian matrix is the set of its ordered eigenvalues. -/
theorem spectrum_eq_range_eig {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) :
    spectrum ℝ A = Set.range (eig A) := by
  rw [range_eig hA, hA.spectrum_real_eq_range_eigenvalues]

/-- `∑_j λ_j(A) = Re tr A`. -/
theorem sum_eig_eq_trace {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) :
    ∑ j, eig A j = (A.trace).re := by
  rw [show (∑ j, eig A j) = ∑ i, hA.eigenvalues i from sum_eig hA (fun x => x),
    hA.trace_eq_sum_eigenvalues, Complex.re_sum]
  simp

lemma eig_nonneg {P : Matrix (Fin N) (Fin N) ℂ} (hP : P.PosSemidef) (j : Fin N) :
    0 ≤ eig P j := by
  obtain ⟨σ, hσ⟩ := exists_perm hP.isHermitian
  rw [hσ]
  exact hP.eigenvalues_nonneg _

/-- For an increasing `f`, `f j < t` iff `j` is smaller than the number of `i` with `f i < t`. -/
lemma lt_iff_lt_card {f : Fin N → ℝ} (hf : Monotone f) (j : Fin N) (t : ℝ) :
    f j < t ↔ (j : ℕ) < Fintype.card {i // f i < t} := by
  rw [Fintype.card_subtype]
  constructor
  · intro h
    have hsub : Finset.Iic j ⊆ Finset.univ.filter (fun i => f i < t) := by
      intro i hi
      simp only [Finset.mem_Iic] at hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact lt_of_le_of_lt (hf hi) h
    have := Finset.card_le_card hsub
    rw [Fin.card_Iic] at this
    omega
  · intro h
    by_contra hne
    push_neg at hne
    have hsub : Finset.univ.filter (fun i => f i < t) ⊆ Finset.Iio j := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      simp only [Finset.mem_Iio]
      by_contra hij
      push_neg at hij
      exact absurd (lt_of_le_of_lt (le_trans hne (hf hij)) hi) (lt_irrefl _)
    have := Finset.card_le_card hsub
    rw [Fin.card_Iio] at this
    omega

/-- Comparison of increasing functions through their counting functions. -/
lemma le_of_card_le {f g : Fin N → ℝ} (hf : Monotone f) (hg : Monotone g)
    (h : ∀ t, Fintype.card {i // g i < t} ≤ Fintype.card {i // f i < t}) (j : Fin N) :
    f j ≤ g j := by
  by_contra hlt
  push_neg at hlt
  have h1 := (lt_iff_lt_card hg j (f j)).1 hlt
  have h2 := (lt_iff_lt_card hf j (f j)).2 (lt_of_lt_of_le h1 (h _))
  exact lt_irrefl _ h2

/-- Two real tuples with the same counting functions have the same sums `∑ ψ(·)`. -/
lemma sum_comp_eq_of_card {f g : Fin N → ℝ}
    (h : ∀ t, Fintype.card {i // f i < t} = Fintype.card {i // g i < t}) (ψ : ℝ → ℝ) :
    ∑ i, ψ (f i) = ∑ i, ψ (g i) := by
  have hf := Tuple.monotone_sort f
  have hg := Tuple.monotone_sort g
  have cf : ∀ t, Fintype.card {i // (f ∘ Tuple.sort f) i < t} = Fintype.card {i // f i < t} :=
    fun t => Fintype.card_congr ((Tuple.sort f).subtypeEquiv fun i => Iff.rfl)
  have cg : ∀ t, Fintype.card {i // (g ∘ Tuple.sort g) i < t} = Fintype.card {i // g i < t} :=
    fun t => Fintype.card_congr ((Tuple.sort g).subtypeEquiv fun i => Iff.rfl)
  have heq : ∀ j, (f ∘ Tuple.sort f) j = (g ∘ Tuple.sort g) j := fun j =>
    le_antisymm (le_of_card_le hf hg (fun t => le_of_eq (by rw [cf, cg, h])) j)
      (le_of_card_le hg hf (fun t => le_of_eq (by rw [cf, cg, h])) j)
  calc ∑ i, ψ (f i) = ∑ i, ψ (f (Tuple.sort f i)) :=
        (Equiv.sum_comp (Tuple.sort f) (fun i => ψ (f i))).symm
    _ = ∑ i, ψ (g (Tuple.sort g i)) := Finset.sum_congr rfl fun i _ => congrArg ψ (heq i)
    _ = ∑ i, ψ (g i) := Equiv.sum_comp (Tuple.sort g) (fun i => ψ (g i))

/-- **Min–max monotonicity** (eq. `minmax`, l. 1708–1716): if `A ≤ B` in the Loewner order,
i.e. `B - A ≥ 0`, then `λ_j(A) ≤ λ_j(B)` for every `j`. -/
theorem eig_mono {A B : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian)
    (h : (B - A).PosSemidef) (j : Fin N) : eig A j ≤ eig B j :=
  le_of_card_le (eig_monotone A) (eig_monotone B)
    (fun t => by rw [card_eig_lt hA, card_eig_lt hB]; exact card_lt_anti hA hB h t) j

lemma isHermitian_conj {A : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    (U : Matrix (Fin N) (Fin N) ℂ) : (U * A * Uᴴ).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hA.eq, Matrix.mul_assoc]

/-- **Unitary invariance of ordered eigenvalues** (proof of Lemma `lemma-flow`, l. 1373). -/
theorem eig_unitary_conj {A U : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    (h1 : Uᴴ * U = 1) (h2 : U * Uᴴ = 1) : eig (U * A * Uᴴ) = eig A := by
  have hC := isHermitian_conj hA U
  have hcard : ∀ t, Fintype.card {i // hC.eigenvalues i < t} =
      Fintype.card {i // hA.eigenvalues i < t} := fun t =>
    (isGreatest_negDefDims_sub hC t).unique
      (by rw [negDefDims_unitary_conj h1 h2]; exact isGreatest_negDefDims_sub hA t)
  funext j
  apply le_antisymm
  · exact le_of_card_le (eig_monotone _) (eig_monotone _)
      (fun t => le_of_eq (by rw [card_eig_lt hC, card_eig_lt hA, hcard])) j
  · exact le_of_card_le (eig_monotone _) (eig_monotone _)
      (fun t => le_of_eq (by rw [card_eig_lt hC, card_eig_lt hA, hcard])) j

/-- Unitary invariance for `U` in the unitary group. -/
theorem eig_unitary_conj' {A U : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian)
    (hU : U ∈ unitaryGroup (Fin N) ℂ) : eig (U * A * Uᴴ) = eig A := by
  have h2 : U * Uᴴ = 1 := by rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff.1 hU
  exact eig_unitary_conj hA (mul_eq_one_comm.1 h2) h2

end Ordered

/-! ## 3. Functional calculus by hand -/

section Fn

variable {N : ℕ}

/-- `φ(C) = U diag(φ(λ_i)) U^*` for a Hermitian `C = U diag(λ_i) U^*`. -/
def fnH {C : Matrix (Fin N) (Fin N) ℂ} (hC : C.IsHermitian) (φ : ℝ → ℝ) :
    Matrix (Fin N) (Fin N) ℂ :=
  (hC.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) *
    diagonal (fun i => (φ (hC.eigenvalues i) : ℂ)) *
    (hC.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)ᴴ

variable {C : Matrix (Fin N) (Fin N) ℂ}

lemma fnH_id (hC : C.IsHermitian) : fnH hC (fun x => x) = C := (spectral_eq hC).symm

lemma fnH_sub (hC : C.IsHermitian) (φ ψ : ℝ → ℝ) :
    fnH hC (fun x => φ x - ψ x) = fnH hC φ - fnH hC ψ := by
  simp only [fnH]
  rw [← Matrix.sub_mul, ← Matrix.mul_sub]
  congr 2
  ext i j
  by_cases h : i = j <;> simp [diagonal_apply, h]

lemma fnH_add (hC : C.IsHermitian) (φ ψ : ℝ → ℝ) :
    fnH hC (fun x => φ x + ψ x) = fnH hC φ + fnH hC ψ := by
  simp only [fnH]
  rw [← Matrix.add_mul, ← Matrix.mul_add]
  congr 2
  ext i j
  by_cases h : i = j <;> simp [diagonal_apply, h]

lemma fnH_one (hC : C.IsHermitian) : fnH hC (fun _ => 1) = 1 := by
  simp only [fnH, Complex.ofReal_one, diagonal_one, Matrix.mul_one]
  exact eigU_mul_star hC

lemma fnH_mul (hC : C.IsHermitian) (φ ψ : ℝ → ℝ) :
    fnH hC φ * fnH hC ψ = fnH hC (fun x => φ x * ψ x) := by
  simp only [fnH]
  have h1 := eigU_star_mul hC
  set U : Matrix (Fin N) (Fin N) ℂ := (hC.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
  calc U * diagonal (fun i => (φ (hC.eigenvalues i) : ℂ)) * Uᴴ *
        (U * diagonal (fun i => (ψ (hC.eigenvalues i) : ℂ)) * Uᴴ)
      = U * diagonal (fun i => (φ (hC.eigenvalues i) : ℂ)) * (Uᴴ * U) *
        diagonal (fun i => (ψ (hC.eigenvalues i) : ℂ)) * Uᴴ := by
          simp only [Matrix.mul_assoc]
    _ = _ := by
          rw [h1, Matrix.mul_one, Matrix.mul_assoc U, diagonal_mul_diagonal]
          congr 2
          funext i
          push_cast
          rfl

lemma fnH_isHermitian (hC : C.IsHermitian) (φ : ℝ → ℝ) : (fnH hC φ).IsHermitian :=
  isHermitian_conj (isHermitian_diagonal_of_self_adjoint _ (by
    show star _ = _
    funext i
    simp)) _

lemma fnH_posSemidef (hC : C.IsHermitian) {φ : ℝ → ℝ} (hφ : ∀ i, 0 ≤ φ (hC.eigenvalues i)) :
    (fnH hC φ).PosSemidef :=
  (PosSemidef.diagonal (fun i => Complex.zero_le_real.2 (hφ i))).mul_mul_conjTranspose_same _

lemma trace_fnH (hC : C.IsHermitian) (φ : ℝ → ℝ) :
    (fnH hC φ).trace = ∑ i, (φ (hC.eigenvalues i) : ℂ) := by
  simp only [fnH]
  rw [trace_mul_comm, ← Matrix.mul_assoc, eigU_star_mul hC, Matrix.one_mul, trace_diagonal]

lemma re_trace_fnH (hC : C.IsHermitian) (φ : ℝ → ℝ) :
    (fnH hC φ).trace.re = ∑ i, φ (hC.eigenvalues i) := by
  rw [trace_fnH, Complex.re_sum]
  simp

/-- The eigenvalues of `φ(C)` are the `φ(λ_i(C))` (as a multiset). -/
lemma sum_eig_fnH (hC : C.IsHermitian) (φ ψ : ℝ → ℝ) :
    ∑ j, ψ (eig (fnH hC φ) j) = ∑ i, ψ (φ (hC.eigenvalues i)) := by
  have hF := fnH_isHermitian hC φ
  rw [sum_eig hF]
  apply sum_comp_eq_of_card
  intro t
  exact (isGreatest_negDefDims_sub hF t).unique
    (isGreatest_negDefDims_conjDiag (eigU_star_mul hC) (eigU_mul_star hC) _ t)

/-- For `φ ≥ 0` and `D ≥ 0`, `Re tr(φ(C) D) ≥ 0`. -/
lemma re_trace_fnH_mul_nonneg (hC : C.IsHermitian) {φ : ℝ → ℝ} (hφ : ∀ x, 0 ≤ φ x)
    {D : Matrix (Fin N) (Fin N) ℂ} (hD : D.PosSemidef) : 0 ≤ (trace (fnH hC φ * D)).re := by
  set U : Matrix (Fin N) (Fin N) ℂ := (hC.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ)
  have hM : (Uᴴ * D * U).PosSemidef := by
    simpa using hD.conjTranspose_mul_mul_same U
  have e : trace (fnH hC φ * D) =
      trace (diagonal (fun i => (φ (hC.eigenvalues i) : ℂ)) * (Uᴴ * D * U)) := by
    simp only [fnH, Matrix.mul_assoc]
    rw [trace_mul_comm U]
    simp only [Matrix.mul_assoc]
    rfl
  rw [e]
  simp only [Matrix.trace, Matrix.diag_apply, diagonal_mul, Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [Complex.re_ofReal_mul]
  exact mul_nonneg (hφ _) (Complex.nonneg_iff.1 (hM.diag_nonneg (i := i))).1

end Fn

/-! ## 4. Trace norm, duality, triangle inequality, Lidskii -/

section TraceNorm

variable {N : ℕ}

/-- The trace norm `‖C‖_{S_1} = ∑ singular values = ∑ √(eigenvalues of C^* C)`. -/
def traceNorm (C : Matrix (Fin N) (Fin N) ℂ) : ℝ := ∑ j, Real.sqrt (eig (Cᴴ * C) j)

/-- The Hilbert–Schmidt norm `‖C‖_{S_2} = (∑ |C_ij|²)^{1/2}`. -/
def hsNorm (C : Matrix (Fin N) (Fin N) ℂ) : ℝ := Real.sqrt (∑ i, ∑ j, ‖C i j‖ ^ 2)

/-- The sign function used for `sgn(C)` (with `sgn 0 = 1`). -/
def sgnR (x : ℝ) : ℝ := if 0 ≤ x then 1 else -1

lemma sgnR_mul_self (x : ℝ) : sgnR x * x = |x| := by
  unfold sgnR
  split_ifs with h
  · rw [one_mul, abs_of_nonneg h]
  · rw [abs_of_neg (not_le.1 h)]; ring

lemma one_sub_sgnR_nonneg (x : ℝ) : 0 ≤ 1 - sgnR x := by
  unfold sgnR; split_ifs <;> norm_num

lemma one_add_sgnR_nonneg (x : ℝ) : 0 ≤ 1 + sgnR x := by
  unfold sgnR; split_ifs <;> norm_num

lemma pos_sub_neg (x : ℝ) : max x 0 - max (-x) 0 = x := by
  rcases le_total 0 x with h | h
  · rw [max_eq_left h, max_eq_right (by linarith)]; ring
  · rw [max_eq_right h, max_eq_left (by linarith)]; ring

lemma pos_add_neg (x : ℝ) : max x 0 + max (-x) 0 = |x| := by
  rcases le_total 0 x with h | h
  · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h]; ring
  · rw [max_eq_right h, max_eq_left (by linarith), abs_of_nonpos h]; ring

variable {C D : Matrix (Fin N) (Fin N) ℂ}

/-- For Hermitian `C`, `‖C‖_{S_1} = ∑ |λ_i(C)|`. -/
theorem traceNorm_eq_sum_abs (hC : C.IsHermitian) :
    traceNorm C = ∑ i, |hC.eigenvalues i| := by
  unfold traceNorm
  rw [hC.eq]
  have e : C * C = fnH hC (fun x => x * x) := by
    calc C * C = fnH hC (fun x => x) * fnH hC (fun x => x) := by rw [fnH_id]
      _ = fnH hC (fun x => x * x) := fnH_mul hC _ _
  rw [e, sum_eig_fnH hC (fun x => x * x) Real.sqrt]
  simp only [Real.sqrt_mul_self_eq_abs]

/-- For Hermitian `C`, `‖C‖_{S_1} = ∑_j |λ_j(C)|` (ordered eigenvalues). -/
theorem traceNorm_eq_sum_abs_eig (hC : C.IsHermitian) :
    traceNorm C = ∑ j, |eig C j| := by
  rw [traceNorm_eq_sum_abs hC, sum_eig hC (fun x => |x|)]

lemma traceNorm_nonneg (C : Matrix (Fin N) (Fin N) ℂ) : 0 ≤ traceNorm C :=
  Finset.sum_nonneg fun _ _ => Real.sqrt_nonneg _

lemma traceNorm_neg (C : Matrix (Fin N) (Fin N) ℂ) : traceNorm (-C) = traceNorm C := by
  simp [traceNorm]

lemma traceNorm_sub_comm (C D : Matrix (Fin N) (Fin N) ℂ) :
    traceNorm (C - D) = traceNorm (D - C) := by
  rw [← neg_sub, traceNorm_neg]

/-- Unitary invariance of the trace norm. -/
theorem traceNorm_unitary_conj {U : Matrix (Fin N) (Fin N) ℂ} (hC : C.IsHermitian)
    (h1 : Uᴴ * U = 1) (h2 : U * Uᴴ = 1) : traceNorm (U * C * Uᴴ) = traceNorm C := by
  rw [traceNorm_eq_sum_abs_eig (isHermitian_conj hC U), traceNorm_eq_sum_abs_eig hC,
    eig_unitary_conj hC h1 h2]

/-- **Jordan decomposition**: `C = C₊ - C₋` with `C_± ≥ 0` and `tr C₊ + tr C₋ = ‖C‖_{S_1}`. -/
theorem jordan (hC : C.IsHermitian) :
    ∃ Cp Cm : Matrix (Fin N) (Fin N) ℂ, Cp.PosSemidef ∧ Cm.PosSemidef ∧ C = Cp - Cm ∧
      (trace Cp).re + (trace Cm).re = traceNorm C := by
  refine ⟨fnH hC (fun x => max x 0), fnH hC (fun x => max (-x) 0),
    fnH_posSemidef hC (fun _ => le_max_right _ _), fnH_posSemidef hC (fun _ => le_max_right _ _),
    ?_, ?_⟩
  · calc C = fnH hC (fun x => x) := (fnH_id hC).symm
      _ = fnH hC (fun x => max x 0 - max (-x) 0) := by simp only [pos_sub_neg]
      _ = _ := fnH_sub hC _ _
  · rw [re_trace_fnH, re_trace_fnH, ← Finset.sum_add_distrib, traceNorm_eq_sum_abs hC]
    simp only [pos_add_neg]

/-- `Re tr(S P) ≤ tr P` and `-Re tr(S P) ≤ tr P` for `S = sgn(C)` and `P ≥ 0`. -/
lemma abs_re_trace_sgn_mul_le (hC : C.IsHermitian) {P : Matrix (Fin N) (Fin N) ℂ}
    (hP : P.PosSemidef) :
    (trace (fnH hC sgnR * P)).re ≤ (trace P).re ∧
      -(trace (fnH hC sgnR * P)).re ≤ (trace P).re := by
  have h1 := re_trace_fnH_mul_nonneg hC (φ := fun x => 1 - sgnR x) one_sub_sgnR_nonneg hP
  have h2 := re_trace_fnH_mul_nonneg hC (φ := fun x => 1 + sgnR x) one_add_sgnR_nonneg hP
  rw [fnH_sub hC (fun _ => 1) sgnR, fnH_one, Matrix.sub_mul, Matrix.one_mul, trace_sub,
    Complex.sub_re] at h1
  rw [fnH_add hC (fun _ => 1) sgnR, fnH_one, Matrix.add_mul, Matrix.one_mul, trace_add,
    Complex.add_re] at h2
  constructor <;> linarith

/-- **Duality**: for Hermitian `C, D`, `Re tr(sgn(C) D) ≤ ‖D‖_{S_1}`. -/
theorem re_trace_mul_le_traceNorm (hC : C.IsHermitian) (hD : D.IsHermitian) :
    (trace (fnH hC sgnR * D)).re ≤ traceNorm D := by
  obtain ⟨Dp, Dm, hDp, hDm, hdec, htr⟩ := jordan hD
  have e : trace (fnH hC sgnR * D) = trace (fnH hC sgnR * Dp) - trace (fnH hC sgnR * Dm) := by
    rw [← trace_sub, ← Matrix.mul_sub, ← hdec]
  rw [e, Complex.sub_re, ← htr]
  have := (abs_re_trace_sgn_mul_le hC hDp).1
  have := (abs_re_trace_sgn_mul_le hC hDm).2
  linarith

/-- Equality case of the duality: `Re tr(sgn(C) C) = ‖C‖_{S_1}`. -/
theorem re_trace_sgn_mul_self (hC : C.IsHermitian) :
    (trace (fnH hC sgnR * C)).re = traceNorm C := by
  have e : fnH hC sgnR * C = fnH hC (fun x => sgnR x * x) := by
    calc fnH hC sgnR * C = fnH hC sgnR * fnH hC (fun x => x) := by rw [fnH_id hC]
      _ = fnH hC (fun x => sgnR x * x) := fnH_mul hC _ _
  rw [e, re_trace_fnH, traceNorm_eq_sum_abs hC]
  simp only [sgnR_mul_self]

/-- **Triangle inequality** for the trace norm of Hermitian matrices. -/
theorem traceNorm_add_le (hC : C.IsHermitian) (hD : D.IsHermitian) :
    traceNorm (C + D) ≤ traceNorm C + traceNorm D := by
  have hCD := hC.add hD
  rw [← re_trace_sgn_mul_self hCD, Matrix.mul_add, trace_add, Complex.add_re]
  exact add_le_add (re_trace_mul_le_traceNorm hCD hC) (re_trace_mul_le_traceNorm hCD hD)

/-- If `C = P - Q` with `P, Q ≥ 0` then `‖C‖_{S_1} ≤ tr P + tr Q`. -/
theorem traceNorm_le_of_eq_sub {P Q : Matrix (Fin N) (Fin N) ℂ} (hP : P.PosSemidef)
    (hQ : Q.PosSemidef) (hC : C = P - Q) : traceNorm C ≤ (trace P).re + (trace Q).re := by
  have hCh : C.IsHermitian := hC ▸ hP.isHermitian.sub hQ.isHermitian
  rw [← re_trace_sgn_mul_self hCh]
  conv_lhs => rw [show fnH hCh sgnR * C = fnH hCh sgnR * P - fnH hCh sgnR * Q by
    rw [← Matrix.mul_sub, ← hC]]
  rw [trace_sub, Complex.sub_re]
  have := (abs_re_trace_sgn_mul_le hCh hP).1
  have := (abs_re_trace_sgn_mul_le hCh hQ).2
  linarith

/-- **Lidskii inequality** (l. 1383–1389): for Hermitian `A, B`,
`∑_j |λ_j(A) - λ_j(B)| ≤ ‖A - B‖_{S_1}`. -/
theorem lidskii {A B : Matrix (Fin N) (Fin N) ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ∑ j, |eig A j - eig B j| ≤ traceNorm (A - B) := by
  obtain ⟨Cp, Cm, hCp, hCm, hdec, htr⟩ := jordan (hA.sub hB)
  have hM : (B + Cp).IsHermitian := hB.add hCp.isHermitian
  have hMA : B + Cp - A = Cm := by
    have : B + Cp - A = Cp - (A - B) := by abel
    rw [this, hdec]; abel
  have hMB : B + Cp - B = Cp := by abel
  have h1 : ∀ j, eig A j ≤ eig (B + Cp) j := fun j => eig_mono hA hM (by rw [hMA]; exact hCm) j
  have h2 : ∀ j, eig B j ≤ eig (B + Cp) j := fun j => eig_mono hB hM (by rw [hMB]; exact hCp) j
  calc ∑ j, |eig A j - eig B j|
      ≤ ∑ j, ((eig (B + Cp) j - eig A j) + (eig (B + Cp) j - eig B j)) :=
        Finset.sum_le_sum fun j _ => by
          rw [abs_le]; constructor <;> linarith [h1 j, h2 j]
    _ = (∑ j, eig (B + Cp) j - ∑ j, eig A j) + (∑ j, eig (B + Cp) j - ∑ j, eig B j) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    _ = (trace (B + Cp - A)).re + (trace (B + Cp - B)).re := by
        rw [sum_eig_eq_trace hM, sum_eig_eq_trace hA, sum_eig_eq_trace hB, trace_sub, trace_sub,
          Complex.sub_re, Complex.sub_re]
    _ = (trace Cp).re + (trace Cm).re := by rw [hMA, hMB, add_comm]
    _ = traceNorm (A - B) := htr

/-! ### Hilbert–Schmidt bound -/

lemma sum_sq_eigenvalues (hC : C.IsHermitian) :
    ∑ i, hC.eigenvalues i ^ 2 = ∑ i, ∑ j, ‖C i j‖ ^ 2 := by
  have h1 : (trace (C * C)).re = ∑ i, hC.eigenvalues i ^ 2 := by
    have e : C * C = fnH hC (fun x => x * x) := by
      calc C * C = fnH hC (fun x => x) * fnH hC (fun x => x) := by rw [fnH_id]
        _ = fnH hC (fun x => x * x) := fnH_mul hC _ _
    rw [e, re_trace_fnH]
    simp only [sq]
  have h2 : (trace (Cᴴ * C)).re = ∑ i, ∑ j, ‖C i j‖ ^ 2 := by
    simp only [Matrix.trace, Matrix.diag_apply, mul_apply, conjTranspose_apply, Complex.re_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  rw [← h1, ← h2, hC.eq]

/-- `‖C‖_{S_1} ≤ √(rank C) · ‖C‖_{S_2}` for Hermitian `C` (Cauchy–Schwarz over the nonzero
eigenvalues; used in the proof of Proposition `prop-phase-variation`). -/
theorem traceNorm_le_sqrt_rank_mul_hsNorm (hC : C.IsHermitian) :
    traceNorm C ≤ Real.sqrt C.rank * hsNorm C := by
  classical
  rw [traceNorm_eq_sum_abs hC, hsNorm, ← sum_sq_eigenvalues hC,
    ← Real.sqrt_mul (Nat.cast_nonneg _)]
  refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => if hC.eigenvalues i ≠ 0 then (1 : ℝ) else 0) (fun i => |hC.eigenvalues i|)
  have e1 : ∑ i, (if hC.eigenvalues i ≠ 0 then (1 : ℝ) else 0) * |hC.eigenvalues i| =
      ∑ i, |hC.eigenvalues i| :=
    Finset.sum_congr rfl fun i _ => by
      by_cases h : hC.eigenvalues i = 0 <;> simp [h]
  have e2 : ∑ i, (if hC.eigenvalues i ≠ 0 then (1 : ℝ) else 0) ^ 2 = (C.rank : ℝ) := by
    have : ∀ i, (if hC.eigenvalues i ≠ 0 then (1 : ℝ) else 0) ^ 2 =
        if hC.eigenvalues i ≠ 0 then (1 : ℝ) else 0 := fun i => by split_ifs <;> norm_num
    simp only [this]
    rw [Finset.sum_boole, hC.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  have e3 : ∑ i, |hC.eigenvalues i| ^ 2 = ∑ i, hC.eigenvalues i ^ 2 :=
    Finset.sum_congr rfl fun i _ => sq_abs _
  rw [e1, e2, e3] at hcs
  exact hcs

/-- `‖C‖_{S_1} ≤ √r · ‖C‖_{S_2}` for Hermitian `C` of rank `≤ r`. -/
theorem traceNorm_le_sqrt_mul_hsNorm (hC : C.IsHermitian) {r : ℕ} (hr : C.rank ≤ r) :
    traceNorm C ≤ Real.sqrt r * hsNorm C :=
  (traceNorm_le_sqrt_rank_mul_hsNorm hC).trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (by exact_mod_cast hr)) (Real.sqrt_nonneg _))

lemma hsNorm_zero : hsNorm (0 : Matrix (Fin N) (Fin N) ℂ) = 0 := by simp [hsNorm]

lemma continuous_hsNorm : Continuous (hsNorm : Matrix (Fin N) (Fin N) ℂ → ℝ) :=
  Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _
    fun j _ => (continuous_id.matrix_elem i j).norm.pow 2)

/-- Lipschitz continuity of the trace norm on Hermitian matrices. -/
theorem abs_traceNorm_sub_le (hC : C.IsHermitian) (hD : D.IsHermitian) :
    |traceNorm C - traceNorm D| ≤ Real.sqrt N * hsNorm (C - D) := by
  have hCD := hC.sub hD
  have hb : traceNorm (C - D) ≤ Real.sqrt N * hsNorm (C - D) :=
    traceNorm_le_sqrt_mul_hsNorm hCD (by simpa using rank_le_width (C - D))
  have t1 : traceNorm C ≤ traceNorm D + traceNorm (C - D) := by
    have := traceNorm_add_le hD hCD
    rwa [add_sub_cancel] at this
  have t2 : traceNorm D ≤ traceNorm C + traceNorm (C - D) := by
    have := traceNorm_add_le hC (hD.sub hC)
    rwa [add_sub_cancel, ← traceNorm_sub_comm] at this
  rw [abs_sub_le_iff]
  constructor <;> linarith

end TraceNorm

end Flow
end CAH
