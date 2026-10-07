/-
# Square cosine shells and magnetic splitting  (paper §"Square cosine shells")

Formalizes the finite-dimensional linear algebra behind Proposition
`ex-prop:square-splitting` (equations `ex-eq:square-shell`, `ex-eq:KNdiag`, `ex-eq:KNoff`,
`ex-eq:square-energies`) of *continuum_magnetic_spectral_transition.tex*.

* `squareShellMatrix N b` is the compression `K_N = P_N Q_1 P_N` written in the ordered
  Cartesian Hermite basis `|n, N-n⟩`, `0 ≤ n ≤ N`, with diagonal `ex-eq:KNdiag` and
  off-diagonal entries `ex-eq:KNoff`. It is Hermitian (`squareShellMatrix_isHermitian`).
* For an arbitrary tridiagonal matrix on `Fin (N+1)` whose adjacent off-diagonal entries are
  nonzero, the three-term recursion shows that an eigenvector vanishing at the first (resp. last)
  coordinate vanishes identically, and that all eigenspaces have dimension `≤ 1`.
* Consequently, for `b ≠ 0`, `K_N` has `N+1` distinct eigenvalues `ν_{N,a}` and every
  eigenvector has `(v_{N,a})_0 ≠ 0`, `(v_{N,a})_N ≠ 0`.
* The leading shell energy `λ_N = 2√2π(N+1)` (`ex-eq:square-shell`) agrees with
  `harmonicLevel 1 n` for `n.1 + n.2 = N`.
* An abstract asymptotic lemma: two-term expansions with distinct `h²`-coefficients and
  `O(h³)` remainders are separated by `Δ h² / 2` for `h < Δ / (4C)`, as stated after the
  proposition in the paper.

The analytic input (degenerate perturbation theory giving `ex-eq:square-energies`) is not
formalized; it enters only as the explicit hypothesis of `branch_separation`.
-/
import ContinuumMagnetic.Basic

noncomputable section

open Matrix

namespace CMS

/-! ## Tridiagonal matrices with nonzero adjacent off-diagonal entries -/

section Tridiagonal

variable {K : Type*} [Field K] {N : ℕ}

/-- A matrix on `Fin (N+1)` is tridiagonal if `M i j = 0` whenever `|i - j| > 1`. -/
def IsTridiagonal (M : Matrix (Fin (N + 1)) (Fin (N + 1)) K) : Prop :=
  ∀ i j : Fin (N + 1), (i : ℕ) + 1 < j ∨ (j : ℕ) + 1 < i → M i j = 0

/-- All adjacent off-diagonal entries `M_{n,n+1}` and `M_{n+1,n}` are nonzero. -/
def AdjNonzero (M : Matrix (Fin (N + 1)) (Fin (N + 1)) K) : Prop :=
  ∀ i j : Fin (N + 1), (i : ℕ) + 1 = j → M i j ≠ 0 ∧ M j i ≠ 0

variable {M : Matrix (Fin (N + 1)) (Fin (N + 1)) K}

/-- Three-term recursion from the first coordinate: an eigenvector of a tridiagonal matrix
with nonzero adjacent off-diagonal entries whose first coordinate vanishes is zero. -/
theorem IsTridiagonal.eq_zero_of_apply_zero (hT : IsTridiagonal M) (hD : AdjNonzero M)
    {v : Fin (N + 1) → K} {c : K} (hv : M *ᵥ v = c • v) (h0 : v 0 = 0) : v = 0 := by
  have key : ∀ k : ℕ, ∀ i : Fin (N + 1), (i : ℕ) ≤ k → v i = 0 := by
    intro k
    induction k with
    | zero =>
      intro i hi
      have : i = 0 := Fin.ext (by simp only [Fin.val_zero]; omega)
      rw [this, h0]
    | succ k ih =>
      intro i hi
      rcases Nat.lt_or_ge (i : ℕ) (k + 1) with hlt | hge
      · exact ih i (by omega)
      have hik : (i : ℕ) = k + 1 := by omega
      set p : Fin (N + 1) := ⟨k, by omega⟩ with hp
      have hrow := congrFun hv p
      have hvp : v p = 0 := ih p (by simp [hp])
      simp only [Pi.smul_apply, smul_eq_mul, hvp, mul_zero, mulVec, dotProduct] at hrow
      rw [Finset.sum_eq_single i] at hrow
      · exact (mul_eq_zero.mp hrow).resolve_left (hD p i (by simp [hp]; omega)).1
      · intro j _ hji
        by_cases hj : (j : ℕ) ≤ k
        · simp [ih j hj]
        · have hjne : (j : ℕ) ≠ k + 1 := fun h => hji (Fin.ext (by omega))
          rw [hT p j (Or.inl (by simp [hp]; omega)), zero_mul]
      · simp
  funext i
  exact key i i le_rfl

/-- Three-term recursion from the last coordinate: an eigenvector of a tridiagonal matrix
with nonzero adjacent off-diagonal entries whose last coordinate vanishes is zero. -/
theorem IsTridiagonal.eq_zero_of_apply_last (hT : IsTridiagonal M) (hD : AdjNonzero M)
    {v : Fin (N + 1) → K} {c : K} (hv : M *ᵥ v = c • v) (hN : v (Fin.last N) = 0) :
    v = 0 := by
  set M' := M.submatrix (Fin.revPerm : Equiv.Perm (Fin (N + 1))) Fin.revPerm with hM'
  have hT' : IsTridiagonal M' := by
    intro i j hij
    simp only [hM', submatrix_apply, Fin.revPerm_apply]
    exact hT _ _ (by simp only [Fin.val_rev]; omega)
  have hD' : AdjNonzero M' := by
    intro i j hij
    simp only [hM', submatrix_apply, Fin.revPerm_apply]
    have := hD (Fin.rev j) (Fin.rev i) (by simp only [Fin.val_rev]; omega)
    exact ⟨this.2, this.1⟩
  have hv' : M' *ᵥ (v ∘ Fin.revPerm) = c • (v ∘ Fin.revPerm) := by
    rw [hM', submatrix_mulVec_equiv]
    have : (v ∘ Fin.revPerm) ∘ (Fin.revPerm : Equiv.Perm (Fin (N + 1))).symm = v := by
      funext i; simp
    rw [this, hv]
    rfl
  have h0 : (v ∘ Fin.revPerm) 0 = 0 := by simpa using hN
  have := hT'.eq_zero_of_apply_zero hD' hv' h0
  funext i
  have := congrFun this (Fin.rev i)
  simpa using this

/-- Every nonzero eigenvector has nonzero first coordinate. -/
theorem IsTridiagonal.apply_zero_ne_zero (hT : IsTridiagonal M) (hD : AdjNonzero M)
    {v : Fin (N + 1) → K} {c : K} (hv : M *ᵥ v = c • v) (hv0 : v ≠ 0) : v 0 ≠ 0 :=
  fun h => hv0 (hT.eq_zero_of_apply_zero hD hv h)

/-- Every nonzero eigenvector has nonzero last coordinate. -/
theorem IsTridiagonal.apply_last_ne_zero (hT : IsTridiagonal M) (hD : AdjNonzero M)
    {v : Fin (N + 1) → K} {c : K} (hv : M *ᵥ v = c • v) (hv0 : v ≠ 0) :
    v (Fin.last N) ≠ 0 :=
  fun h => hv0 (hT.eq_zero_of_apply_last hD hv h)

/-- Two eigenvectors for the same eigenvalue are proportional: `w = (w₀ / v₀) • v`. -/
theorem IsTridiagonal.eigenvector_proportional (hT : IsTridiagonal M) (hD : AdjNonzero M)
    {v w : Fin (N + 1) → K} {c : K} (hv : M *ᵥ v = c • v) (hw : M *ᵥ w = c • w)
    (hv0 : v ≠ 0) : w = (w 0 / v 0) • v := by
  have hne := hT.apply_zero_ne_zero hD hv hv0
  set u : Fin (N + 1) → K := v 0 • w - w 0 • v with hu
  have hMu : M *ᵥ u = c • u := by
    rw [hu, mulVec_sub, mulVec_smul, mulVec_smul, hw, hv, smul_sub, smul_comm (v 0) c w,
      smul_comm (w 0) c v]
  have hu0 : u 0 = 0 := by simp [hu, mul_comm]
  have huz := hT.eq_zero_of_apply_zero hD hMu hu0
  funext k
  have := congrFun huz k
  simp only [hu, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  simp only [Pi.smul_apply, smul_eq_mul]
  field_simp
  linear_combination this

/-- Every eigenspace of a tridiagonal matrix with nonzero adjacent off-diagonal entries has
dimension at most one. -/
theorem IsTridiagonal.finrank_eigenspace_le_one (hT : IsTridiagonal M) (hD : AdjNonzero M)
    (c : K) : Module.finrank K (Module.End.eigenspace (Matrix.toLin' M) c) ≤ 1 := by
  classical
  by_cases h : ∃ v ∈ Module.End.eigenspace (Matrix.toLin' M) c, v ≠ 0
  · obtain ⟨v, hvmem, hv0⟩ := h
    have hv : M *ᵥ v = c • v := by
      simpa [Module.End.mem_eigenspace_iff] using hvmem
    refine finrank_le_one ⟨v, hvmem⟩ fun ⟨w, hwmem⟩ => ⟨w 0 / v 0, ?_⟩
    have hw : M *ᵥ w = c • w := by
      simpa [Module.End.mem_eigenspace_iff] using hwmem
    ext1
    exact (hT.eigenvector_proportional hD hv hw hv0).symm
  · push Not at h
    refine finrank_le_one 0 fun ⟨w, hwmem⟩ => ⟨0, ?_⟩
    ext1
    simp [h w hwmem]

end Tridiagonal

/-! ## The square-shell matrix `K_N` -/

/-- The diagonal entry `-(π²/2)(n² + (N-n)² + N + 1)` of `K_N` (paper `ex-eq:KNdiag`). -/
def shellDiag (N n : ℕ) : ℝ :=
  -(Real.pi ^ 2 / 2) * ((n : ℝ) ^ 2 + ((N : ℝ) - n) ^ 2 + N + 1)

/-- The real hopping amplitude `b √((n+1)(N-n))`; `(K_N)_{n+1,n} = i · shellHop N b n`
(paper `ex-eq:KNoff`). -/
def shellHop (N : ℕ) (b : ℝ) (n : ℕ) : ℝ :=
  b * Real.sqrt (((n : ℝ) + 1) * ((N : ℝ) - n))

/-- The matrix `K_N = P_N Q_1 P_N` of Proposition `ex-prop:square-splitting` in the ordered
Cartesian Hermite basis `|n, N-n⟩` of the `N`th shell, indexed by `n ∈ Fin (N+1)`. -/
def squareShellMatrix (N : ℕ) (b : ℝ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ :=
  Matrix.of fun i j =>
    if i = j then (shellDiag N i : ℂ)
    else if (i : ℕ) = j + 1 then Complex.I * shellHop N b j
    else if (j : ℕ) = i + 1 then -(Complex.I * shellHop N b i)
    else 0

/-- Diagonal entries (`ex-eq:KNdiag`). -/
theorem squareShellMatrix_diag (N : ℕ) (b : ℝ) (n : Fin (N + 1)) :
    squareShellMatrix N b n n =
      ((-(Real.pi ^ 2 / 2) * ((n : ℝ) ^ 2 + ((N : ℝ) - n) ^ 2 + N + 1) : ℝ) : ℂ) := by
  simp [squareShellMatrix, shellDiag]

/-- Sub-diagonal entries `(K_N)_{n+1,n} = i b √((n+1)(N-n))` (`ex-eq:KNoff`). -/
theorem squareShellMatrix_sub (N : ℕ) (b : ℝ) (i j : Fin (N + 1)) (hij : (i : ℕ) = j + 1) :
    squareShellMatrix N b i j =
      Complex.I * b * Real.sqrt (((j : ℝ) + 1) * ((N : ℝ) - j)) := by
  have hne : i ≠ j := fun h => by rw [h] at hij; omega
  simp [squareShellMatrix, shellHop, hne, hij, mul_assoc]

/-- Super-diagonal entries `(K_N)_{n,n+1} = conj (K_N)_{n+1,n}` (`ex-eq:KNoff`). -/
theorem squareShellMatrix_super (N : ℕ) (b : ℝ) (i j : Fin (N + 1)) (hij : (i : ℕ) = j + 1) :
    squareShellMatrix N b j i = (starRingEnd ℂ) (squareShellMatrix N b i j) := by
  have hne : j ≠ i := fun h => by rw [h] at hij; omega
  have hne' : ¬ ((j : ℕ) = i + 1) := by omega
  rw [squareShellMatrix_sub N b i j hij]
  simp only [squareShellMatrix, Matrix.of_apply, hne, hne', eq_true hij, ↓reduceIte, shellHop,
    map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_mul]
  ring

/-- These are the only nonzero off-diagonal entries: `K_N` is tridiagonal. -/
theorem squareShellMatrix_isTridiagonal (N : ℕ) (b : ℝ) :
    IsTridiagonal (squareShellMatrix N b) := by
  intro i j hij
  have h1 : i ≠ j := fun h => by subst h; omega
  have h2 : (i : ℕ) ≠ j + 1 := by omega
  have h3 : (j : ℕ) ≠ i + 1 := by omega
  simp [squareShellMatrix, h1, h2, h3]

/-- `K_N` is Hermitian. -/
theorem squareShellMatrix_isHermitian (N : ℕ) (b : ℝ) :
    (squareShellMatrix N b).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  by_cases hij : i = j
  · subst hij; simp [squareShellMatrix]
  rcases Nat.lt_trichotomy (i : ℕ) j with h | h | h
  · by_cases hs : (j : ℕ) = i + 1
    · rw [squareShellMatrix_super N b j i hs, Complex.star_def]
    · rw [squareShellMatrix_isTridiagonal N b i j (Or.inl (by omega)),
        squareShellMatrix_isTridiagonal N b j i (Or.inr (by omega)), star_zero]
  · exact absurd (Fin.ext h) hij
  · by_cases hs : (i : ℕ) = j + 1
    · rw [squareShellMatrix_super N b i j hs, Complex.star_def, Complex.conj_conj]
    · rw [squareShellMatrix_isTridiagonal N b i j (Or.inr (by omega)),
        squareShellMatrix_isTridiagonal N b j i (Or.inl (by omega)), star_zero]

/-- For `b ≠ 0` every adjacent off-diagonal entry of `K_N` is nonzero. -/
theorem squareShellMatrix_adjNonzero (N : ℕ) {b : ℝ} (hb : b ≠ 0) :
    AdjNonzero (squareShellMatrix N b) := by
  intro i j hij
  have hpos : 0 < ((i : ℝ) + 1) * ((N : ℝ) - i) := by
    have : (i : ℕ) < N := by have := j.isLt; omega
    have : (i : ℝ) < N := by exact_mod_cast this
    have : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    apply mul_pos <;> linarith
  have hsub : squareShellMatrix N b j i ≠ 0 := by
    rw [squareShellMatrix_sub N b j i hij.symm]
    have : Real.sqrt (((i : ℝ) + 1) * ((N : ℝ) - i)) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
    simp [Complex.I_ne_zero, hb, this]
  refine ⟨?_, hsub⟩
  rw [squareShellMatrix_super N b j i hij.symm]
  simpa using hsub

section Spectrum

variable {N : ℕ} {b : ℝ}

/-- Every nonzero eigenvector of `K_N` (`b ≠ 0`) has nonzero first coordinate
`(v_{N,a})_0 ≠ 0`. -/
theorem squareShell_eigvec_zero_ne_zero (hb : b ≠ 0) {v : Fin (N + 1) → ℂ} {c : ℂ}
    (hv : squareShellMatrix N b *ᵥ v = c • v) (hv0 : v ≠ 0) : v 0 ≠ 0 :=
  (squareShellMatrix_isTridiagonal N b).apply_zero_ne_zero
    (squareShellMatrix_adjNonzero N hb) hv hv0

/-- Every nonzero eigenvector of `K_N` (`b ≠ 0`) has nonzero last coordinate
`(v_{N,a})_N ≠ 0`. -/
theorem squareShell_eigvec_last_ne_zero (hb : b ≠ 0) {v : Fin (N + 1) → ℂ} {c : ℂ}
    (hv : squareShellMatrix N b *ᵥ v = c • v) (hv0 : v ≠ 0) : v (Fin.last N) ≠ 0 :=
  (squareShellMatrix_isTridiagonal N b).apply_last_ne_zero
    (squareShellMatrix_adjNonzero N hb) hv hv0

/-- Every eigenspace of `K_N` (`b ≠ 0`) has dimension at most one. -/
theorem squareShell_finrank_eigenspace_le_one (hb : b ≠ 0) (c : ℂ) :
    Module.finrank ℂ (Module.End.eigenspace (Matrix.toLin' (squareShellMatrix N b)) c) ≤ 1 :=
  (squareShellMatrix_isTridiagonal N b).finrank_eigenspace_le_one
    (squareShellMatrix_adjNonzero N hb) c

private lemma eigvec_eq (hK : (squareShellMatrix N b).IsHermitian) (a : Fin (N + 1)) :
    squareShellMatrix N b *ᵥ ⇑(hK.eigenvectorBasis a) =
      ((hK.eigenvalues a : ℝ) : ℂ) • ⇑(hK.eigenvectorBasis a) := by
  rw [hK.mulVec_eigenvectorBasis, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

private lemma eigvec_ne_zero (hK : (squareShellMatrix N b).IsHermitian) (a : Fin (N + 1)) :
    (⇑(hK.eigenvectorBasis a) : Fin (N + 1) → ℂ) ≠ 0 := by
  intro h
  have h' : hK.eigenvectorBasis a = 0 := by
    ext i; simpa using congrFun h i
  have := (hK.eigenvectorBasis).orthonormal.1 a
  rw [h', norm_zero] at this
  exact zero_ne_one this

/-- **Proposition `ex-prop:square-splitting` (simplicity).** For `b ≠ 0` the eigenvalues
`ν_{N,a}` of the Hermitian matrix `K_N` are pairwise distinct. -/
theorem squareShell_eigenvalues_injective (hb : b ≠ 0)
    (hK : (squareShellMatrix N b).IsHermitian) : Function.Injective hK.eigenvalues := by
  intro i j hij
  by_contra hne
  set e := hK.eigenvectorBasis
  have hv := eigvec_eq hK i
  have hw := eigvec_eq hK j
  rw [← hij] at hw
  have hprop := (squareShellMatrix_isTridiagonal N b).eigenvector_proportional
    (squareShellMatrix_adjNonzero N hb) hv hw (eigvec_ne_zero hK i)
  set α : ℂ := e j 0 / e i 0
  have hej : e j = α • e i := by
    ext k; simpa using congrFun hprop k
  have h0 : inner ℂ (e i) (e j) = 0 := e.orthonormal.2 hne
  rw [hej, inner_smul_right, inner_self_eq_norm_sq_to_K, e.orthonormal.1 i] at h0
  simp only [RCLike.ofReal_one, one_pow, mul_one] at h0
  have : e j = 0 := by rw [hej, h0, zero_smul]
  have h1 := e.orthonormal.1 j
  rw [this, norm_zero] at h1
  exact zero_ne_one h1

/-- **Proposition `ex-prop:square-splitting` (counting).** For `b ≠ 0`, `K_N` has exactly
`N+1` distinct eigenvalues. -/
theorem squareShell_card_eigenvalues (hb : b ≠ 0) (hK : (squareShellMatrix N b).IsHermitian) :
    (Finset.univ.image hK.eigenvalues).card = N + 1 := by
  rw [Finset.card_image_of_injective _ (squareShell_eigenvalues_injective hb hK)]
  simp

/-- The real spectrum of `K_N` (`b ≠ 0`) has exactly `N+1` points. -/
theorem squareShell_spectrum_ncard (hb : b ≠ 0) (hK : (squareShellMatrix N b).IsHermitian) :
    (spectrum ℝ (squareShellMatrix N b)).ncard = N + 1 := by
  rw [hK.spectrum_real_eq_range_eigenvalues,
    Set.ncard_range_of_injective (squareShell_eigenvalues_injective hb hK)]
  simp

/-- **Proposition `ex-prop:square-splitting` (endpoint coordinates).** For `b ≠ 0`, the
normalized eigenvectors `v_{N,a}` of `K_N` satisfy `(v_{N,a})_0 ≠ 0` and `(v_{N,a})_N ≠ 0`. -/
theorem squareShell_eigenvectorBasis_endpoints_ne_zero (hb : b ≠ 0)
    (hK : (squareShellMatrix N b).IsHermitian) (a : Fin (N + 1)) :
    hK.eigenvectorBasis a 0 ≠ 0 ∧ hK.eigenvectorBasis a (Fin.last N) ≠ 0 :=
  ⟨squareShell_eigvec_zero_ne_zero hb (eigvec_eq hK a) (eigvec_ne_zero hK a),
    squareShell_eigvec_last_ne_zero hb (eigvec_eq hK a) (eigvec_ne_zero hK a)⟩

end Spectrum

/-! ## Leading shell energy and separation of branches -/

/-- The leading energy `λ_N = 2ω(N+1) = 2√2π(N+1)` of the `N`th square shell
(paper `ex-eq:square-shell`, `μ = 1`). -/
def squareLevel (N : ℕ) : ℝ := 2 * Real.sqrt 2 * Real.pi * (N + 1)

/-- At `μ = 1` every harmonic level with `n.1 + n.2 = N` equals `λ_N`. -/
theorem harmonicLevel_one_eq_squareLevel (n : ℕ × ℕ) :
    harmonicLevel 1 n = squareLevel (n.1 + n.2) := by
  simp only [harmonicLevel, squareLevel, div_one]
  push_cast
  ring

/-- **Separation of the branches** (consequence of `ex-eq:square-energies`). If two branches
satisfy `|ε(h) - λh - ν h²| ≤ C h³` and `|ε'(h) - λh - ν' h²| ≤ C h³` on `0 < h < h₀`, and
`Δ ≤ |ν - ν'|`, then `|ε(h) - ε'(h)| ≥ Δ h² / 2` whenever additionally `4 C h ≤ Δ`. -/
theorem branch_separation {ε ε' : ℝ → ℝ} {lam ν ν' C Δ h₀ : ℝ}
    (hε : ∀ h, 0 < h → h < h₀ → |ε h - lam * h - ν * h ^ 2| ≤ C * h ^ 3)
    (hε' : ∀ h, 0 < h → h < h₀ → |ε' h - lam * h - ν' * h ^ 2| ≤ C * h ^ 3)
    (hΔ : Δ ≤ |ν - ν'|) {h : ℝ} (hh : 0 < h) (hh₀ : h < h₀) (hC : 4 * C * h ≤ Δ) :
    Δ / 2 * h ^ 2 ≤ |ε h - ε' h| := by
  have e1 := hε h hh hh₀
  have e2 := hε' h hh hh₀
  have hdiff : |ν - ν'| * h ^ 2 ≤ |ε h - ε' h| + 2 * C * h ^ 3 := by
    have : (ν - ν') * h ^ 2 = (ε h - ε' h) - (ε h - lam * h - ν * h ^ 2)
        + (ε' h - lam * h - ν' * h ^ 2) := by ring
    calc |ν - ν'| * h ^ 2 = |(ν - ν') * h ^ 2| := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg h)]
      _ ≤ |ε h - ε' h| + |ε h - lam * h - ν * h ^ 2| + |ε' h - lam * h - ν' * h ^ 2| := by
          rw [this]
          exact (abs_add_le _ _).trans (by gcongr; exact abs_sub _ _)
      _ ≤ |ε h - ε' h| + 2 * C * h ^ 3 := by linarith
  have h2 : 0 ≤ h ^ 2 := sq_nonneg h
  have : 2 * C * h ^ 3 ≤ Δ / 2 * h ^ 2 := by
    have : 2 * C * h ^ 3 = (4 * C * h) / 2 * h ^ 2 := by ring
    rw [this]; gcongr
  nlinarith [mul_le_mul_of_nonneg_right hΔ h2]

/-- **Uniform separation for a finite family of branches.** If `ε_a(h) = λh + ν_a h² + O(h³)`
uniformly on `0 < h < h₀` with pairwise distinct `ν_a`, then there are `c > 0` and `h₁ > 0`
such that `|ε_a(h) - ε_{a'}(h)| ≥ c h²` for all `a ≠ a'` and `0 < h < h₁`. -/
theorem branch_separation_family {ι : Type*} [Fintype ι] {ε : ι → ℝ → ℝ} {ν : ι → ℝ}
    {lam C h₀ : ℝ} (hh₀ : 0 < h₀) (hν : Function.Injective ν)
    (hε : ∀ a h, 0 < h → h < h₀ → |ε a h - lam * h - ν a * h ^ 2| ≤ C * h ^ 3) :
    ∃ c > 0, ∃ h₁ > 0, ∀ a a', a ≠ a' → ∀ h, 0 < h → h < h₁ →
      c * h ^ 2 ≤ |ε a h - ε a' h| := by
  classical
  -- `Δ` is the minimum gap over the finite set of ordered pairs of distinct indices.
  set S : Finset (ι × ι) := Finset.univ.filter fun p => p.1 ≠ p.2
  by_cases hS : S.Nonempty
  swap
  · refine ⟨1, one_pos, h₀, hh₀, fun a a' haa => absurd ?_ hS⟩
    exact ⟨(a, a'), Finset.mem_filter.mpr ⟨Finset.mem_univ _, haa⟩⟩
  set Δ : ℝ := S.inf' hS (fun p => |ν p.1 - ν p.2|) with hΔdef
  have hΔpos : 0 < Δ := by
    rw [hΔdef, Finset.lt_inf'_iff]
    intro p hp
    have : p.1 ≠ p.2 := (Finset.mem_filter.mp hp).2
    exact abs_pos.mpr (sub_ne_zero.mpr (hν.ne this))
  have hΔle : ∀ a a', a ≠ a' → Δ ≤ |ν a - ν a'| := by
    intro a a' haa
    have hp : (a, a') ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, haa⟩
    exact Finset.inf'_le (fun p : ι × ι => |ν p.1 - ν p.2|) hp
  set C' : ℝ := max C 1
  have hC' : 0 < C' := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨Δ / 2, by positivity, min h₀ (Δ / (4 * C')), lt_min hh₀ (by positivity), ?_⟩
  intro a a' haa h hh hh₁
  have hhC : h < Δ / (4 * C') := lt_of_lt_of_le hh₁ (min_le_right _ _)
  have hhh₀ : h < h₀ := lt_of_lt_of_le hh₁ (min_le_left _ _)
  have hbound : ∀ b h, 0 < h → h < h₀ → |ε b h - lam * h - ν b * h ^ 2| ≤ C' * h ^ 3 :=
    fun b h hp hl => (hε b h hp hl).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  refine branch_separation (hbound a) (hbound a') (hΔle a a' haa) hh hhh₀ ?_
  rw [lt_div_iff₀ (by positivity)] at hhC
  linarith

end CMS
