/-
Copyright (c) 2026. Formalization of
  S. Becker, S. Jitomirskaya, I. Krasovsky, "Critical almost Mathieu operator: hidden
  singularity, gap continuity, and the Hausdorff dimension of the spectrum"
  (arXiv:1909.04429v2).

# Floquet–Bloch theory for periodic Jacobi matrices and the band structure of `σ(M_{p/q})`

Paper reference (`Arxiv_version-5.tex`): §6 (tex l. 1037–1040), "the set `σ(M_{v,b,p_n/q_n})`
is a union of `q_n` intervals `[E_1^m, E_2^m]`".  In `MeasureConvergence.lean` this was the
external hypothesis `RationalBands v b α`; here it is **proved** (`rationalBands`), and
Theorem 1.3 is restated without it (`measure_convergence'`).

## Mathematical content
Let `Qβ = P ∈ ℤ`, `Q ≥ 1`, and `v, b` continuous and `1`-periodic.  For each phase `θ` the
Jacobi matrix `H_θ = jacobi v b β θ` has `Q`-periodic coefficients `a_n = b(θ+nβ)`,
`d_n = v(θ+nβ)`.  For `k ∈ ℝ` the **Bloch matrix** `bm Q a d k` is the `Q × Q` matrix of `H`
acting on Bloch sequences `ψ(n+Q) = e^{2πik} ψ(n)` (`bext`); it is Hermitian
(`bm_isHermitian`).

* (⇐) `eig_mem_spectrum`: every eigenvalue of every Bloch matrix lies in `σ(H_θ)` — cut-off
  Bloch waves are approximate eigenvectors.
* (⇒) `mem_bands_of_mem_spectrum`: every `E ∈ σ(H_θ)` is an eigenvalue of some `bm k`,
  `k ∈ [0,1]`.  Proof: a finitely supported approximate eigenvector `φ` is decomposed by a
  *discrete* Floquet transform `ft` at the frequencies `k_j = j/R`; the transform intertwines
  `H` with the Bloch matrices (`ft_jop`) and satisfies an exact discrete Plancherel identity
  (`planch`), so averaging over `j` produces an approximate eigenvector of some `bm k_j`;
  closedness of the band set (continuity of ordered eigenvalues, from Lidskii's inequality
  `CAH.Flow.lidskii`) finishes the proof.
* `sigmaM_eq_bands`: `σ(M_{v,b,β}) = ⋃_{j<Q} λ_j([0,1]²)`, where
  `λ_j(θ,k)` is the `j`-th ordered eigenvalue of the Bloch matrix; each `λ_j([0,1]²)` is a
  continuous image of a compact connected set, hence a closed interval (`image_eq_Icc`).

No `sorry`s and no extra hypotheses (beyond continuity and `1`-periodicity of `v, b`, which
the paper assumes).
-/
import CriticalAMOHausdorff.MeasureConvergence
import CriticalAMOHausdorff.OrderedEigenvalues
import CriticalAMOHausdorff.ContinuedFractions

noncomputable section

open Real Filter Topology Matrix L2
open scoped ComplexConjugate

namespace CAH
namespace FB

/-! ### The exponential `e(t) = e^{2πit}` -/

/-- `e(t) = exp(2πit)`. -/
def ex (t : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * t)

lemma ex_add (s t : ℝ) : ex (s + t) = ex s * ex t := by
  unfold ex; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma ex_zero : ex 0 = 1 := by simp [ex]

lemma norm_ex (t : ℝ) : ‖ex t‖ = 1 := by
  unfold ex
  rw [show 2 * (π : ℂ) * Complex.I * (t : ℂ) = ((2 * π * t : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma conj_ex (t : ℝ) : conj (ex t) = ex (-t) := by
  unfold ex
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  push_cast; ring

lemma ex_neg_mul_ex (t : ℝ) : ex (-t) * ex t = 1 := by
  rw [← ex_add, neg_add_cancel, ex_zero]

lemma conj_ex_mul (t : ℝ) : conj (ex t) * ex t = 1 := by rw [conj_ex, ex_neg_mul_ex]

@[fun_prop]
lemma continuous_ex : Continuous ex := by unfold ex; fun_prop

lemma ex_int (n : ℤ) : ex n = 1 := by
  unfold ex
  rw [show 2 * (π : ℂ) * Complex.I * ((n : ℝ) : ℂ) = n * (2 * π * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

lemma ex_nat_mul (n : ℕ) (t : ℝ) : ex (n * t) = ex t ^ n := by
  unfold ex; rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring

/-- Orthogonality of characters: `∑_{j<R} e(jt/R) = R·[t = 0]` for `|t| < R`. -/
lemma sum_ex {R : ℕ} (hR : 0 < R) {t : ℤ} (ht : |t| < R) :
    ∑ j ∈ Finset.range R, ex (j * t / R) = if t = 0 then (R : ℂ) else 0 := by
  have hR' : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
  split_ifs with h0
  · subst h0; simp [ex_zero]
  · have hζ : ex (t / R) ≠ 1 := by
      intro h1
      unfold ex at h1
      obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h1
      have h2πI : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have h3 : (((t : ℝ) / R : ℝ) : ℂ) = (n : ℂ) := by
        apply mul_left_cancel₀ h2πI
        rw [hn]; ring
      have h4 : (t : ℝ) / R = n := by exact_mod_cast h3
      have h5 : (t : ℝ) = n * R := by field_simp at h4; linarith
      have h6 : t = n * R := by exact_mod_cast h5
      have h7 : |n| * (R : ℤ) < R := by
        rw [h6, abs_mul, abs_of_pos (by exact_mod_cast hR : (0 : ℤ) < R)] at ht; exact ht
      have h8 : n = 0 := by
        by_contra hn0
        have := Int.one_le_abs hn0
        nlinarith
      exact h0 (by rw [h6, h8, zero_mul])
    have hterm : ∀ j : ℕ, ex (j * t / R) = ex (t / R) ^ j := fun j => by
      rw [← ex_nat_mul]; congr 1; ring
    rw [Finset.sum_congr rfl (fun j _ => hterm j), geom_sum_eq hζ, ← ex_nat_mul,
      show (R : ℝ) * (t / R) = ((t : ℤ) : ℝ) by field_simp, ex_int]
    simp

/-! ### Indexing modulo `Q` -/

variable {Q : ℕ} [NeZero Q]

lemma Qpos : (0 : ℤ) < Q := by exact_mod_cast NeZero.pos Q

/-- `n mod Q` as an element of `Fin Q`. -/
def fidx (n : ℤ) : Fin Q :=
  ⟨(n % (Q : ℤ)).toNat, by
    have h1 := Int.emod_nonneg n (Qpos (Q := Q)).ne'
    have h2 := Int.emod_lt_of_pos n (Qpos (Q := Q))
    omega⟩

lemma fidx_val (n : ℤ) : (((fidx n : Fin Q) : ℕ) : ℤ) = n % Q :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (Qpos (Q := Q)).ne')

lemma decomp (n : ℤ) : n = (n / Q) * Q + ((fidx n : Fin Q) : ℕ) := by
  rw [fidx_val]; exact (Int.ediv_mul_add_emod n Q).symm

lemma fidx_coe (r : Fin Q) : fidx ((r : ℕ) : ℤ) = r := by
  apply Fin.ext
  have h := fidx_val (Q := Q) ((r : ℕ) : ℤ)
  rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast r.isLt)] at h
  exact_mod_cast h

lemma ediv_coe (r : Fin Q) : ((r : ℕ) : ℤ) / Q = 0 :=
  Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast r.isLt)

lemma fidx_add (n : ℤ) : fidx (n + Q) = (fidx n : Fin Q) := by
  apply Fin.ext
  have h1 := fidx_val (Q := Q) (n + Q)
  have h2 := fidx_val (Q := Q) n
  rw [Int.add_emod_right] at h1
  omega

lemma ediv_add (n : ℤ) : (n + Q) / (Q : ℤ) = n / Q + 1 := by
  rw [show n + (Q : ℤ) = n + 1 * Q by ring, Int.add_mul_ediv_right _ _ (Qpos (Q := Q)).ne']

/-! ### Periodic Jacobi operators and Bloch matrices -/

/-- The formal Jacobi operator `(Hψ)(n) = a_{n-1} ψ(n-1) + a_n ψ(n+1) + d_n ψ(n)`. -/
def jop (a d : ℤ → ℝ) (ψ : ℤ → ℂ) (n : ℤ) : ℂ :=
  (a (n - 1) : ℂ) * ψ (n - 1) + (a n : ℂ) * ψ (n + 1) + (d n : ℂ) * ψ n

/-- `Q`-periodicity of a coefficient sequence. -/
def Per (Q : ℕ) (a : ℤ → ℝ) : Prop := ∀ n, a (n + Q) = a n

lemma Per.shift {a : ℤ → ℝ} (h : Per Q a) (m n : ℤ) : a (n + m * Q) = a n := by
  induction m using Int.induction_on with
  | zero => simp
  | succ i ih => rw [show n + ((i : ℤ) + 1) * Q = (n + i * Q) + Q by ring, h (n + i * Q), ih]
  | pred i ih =>
    have h1 := h (n + (-(i : ℤ) - 1) * Q)
    rw [show n + (-(i : ℤ) - 1) * Q + Q = n + -(i : ℤ) * Q by ring, ih] at h1
    exact h1.symm

/-- The Bloch extension `ψ(n) = e(k ⌊n/Q⌋) u(n mod Q)` of `u : Fin Q → ℂ`. -/
def bext (Q : ℕ) [NeZero Q] (k : ℝ) (u : Fin Q → ℂ) (n : ℤ) : ℂ :=
  ex (k * ((n / (Q : ℤ) : ℤ) : ℝ)) * u (fidx n)

/-- Bloch sequences with quasi-momentum `k`. -/
def IsBloch (Q : ℕ) (k : ℝ) (ψ : ℤ → ℂ) : Prop := ∀ n, ψ (n + Q) = ex k * ψ n

variable {k : ℝ}

lemma bext_coe (u : Fin Q → ℂ) (r : Fin Q) : bext Q k u ((r : ℕ) : ℤ) = u r := by
  simp [bext, fidx_coe, ediv_coe, ex_zero]

lemma bext_isBloch (u : Fin Q → ℂ) : IsBloch Q k (bext Q k u) := by
  intro n
  unfold bext
  rw [fidx_add, ediv_add]
  push_cast
  rw [mul_add, mul_one, ex_add]
  ring

lemma norm_bext (u : Fin Q → ℂ) (n : ℤ) : ‖bext Q k u n‖ = ‖u (fidx n)‖ := by
  simp [bext, norm_ex]

lemma IsBloch.shift {ψ : ℤ → ℂ} (h : IsBloch Q k ψ) (m n : ℤ) :
    ψ (n + m * Q) = ex (k * m) * ψ n := by
  induction m using Int.induction_on with
  | zero => simp [ex_zero]
  | succ i ih =>
    rw [show n + ((i : ℤ) + 1) * Q = (n + i * Q) + Q by ring, h (n + i * Q), ih, ← mul_assoc,
      ← ex_add]
    congr 2; push_cast; ring
  | pred i ih =>
    have h1 := h (n + (-(i : ℤ) - 1) * Q)
    rw [show n + (-(i : ℤ) - 1) * Q + Q = n + -(i : ℤ) * Q by ring, ih] at h1
    have h2 : ψ (n + (-(i : ℤ) - 1) * Q) = ex (-k) * (ex (k * ((-(i : ℤ) : ℤ) : ℝ)) * ψ n) := by
      rw [h1, ← mul_assoc, ex_neg_mul_ex, one_mul]
    rw [h2, ← mul_assoc, ← ex_add]
    congr 2; push_cast; ring

lemma bloch_eq_bext {ψ : ℤ → ℂ} (h : IsBloch Q k ψ) :
    bext Q k (fun r : Fin Q => ψ ((r : ℕ) : ℤ)) = ψ := by
  funext n
  unfold bext
  conv_rhs => rw [decomp (Q := Q) n]
  rw [add_comm, h.shift]

lemma bloch_ext {ψ χ : ℤ → ℂ} (hψ : IsBloch Q k ψ) (hχ : IsBloch Q k χ)
    (h : ∀ r : Fin Q, ψ ((r : ℕ) : ℤ) = χ ((r : ℕ) : ℤ)) : ψ = χ := by
  rw [← bloch_eq_bext hψ, ← bloch_eq_bext hχ]
  congr 1
  funext r
  exact h r

variable {a d : ℤ → ℝ}

lemma jop_isBloch (ha : Per Q a) (hd : Per Q d) {ψ : ℤ → ℂ} (hψ : IsBloch Q k ψ) :
    IsBloch Q k (jop a d ψ) := by
  intro n
  unfold jop
  rw [show n + (Q : ℤ) - 1 = (n - 1) + Q by ring, show n + (Q : ℤ) + 1 = (n + 1) + Q by ring]
  rw [ha (n - 1), ha n, hd n, hψ (n - 1), hψ (n + 1), hψ n]
  ring

/-- The `Q × Q` Bloch matrix of the periodic Jacobi matrix at quasi-momentum `k`. -/
def bm (Q : ℕ) [NeZero Q] (a d : ℤ → ℝ) (k : ℝ) : Matrix (Fin Q) (Fin Q) ℂ :=
  fun r s => jop a d (bext Q k (Pi.single s 1)) ((r : ℕ) : ℤ)

lemma bext_sum (u : Fin Q → ℂ) (n : ℤ) :
    ∑ s, bext Q k (Pi.single s 1) n * u s = bext Q k u n := by
  have : ∀ s, bext Q k (Pi.single s 1) n * u s =
      if s = fidx n then ex (k * ((n / (Q : ℤ) : ℤ) : ℝ)) * u (fidx n) else 0 := by
    intro s
    by_cases h : s = fidx n
    · subst h; simp [bext]
    · simp [bext, Pi.single_apply, Ne.symm h, h]
  rw [Finset.sum_congr rfl (fun s _ => this s), Finset.sum_ite_eq']
  simp [bext]

lemma bm_mulVec (u : Fin Q → ℂ) :
    bm Q a d k *ᵥ u = fun r : Fin Q => jop a d (bext Q k u) ((r : ℕ) : ℤ) := by
  funext r
  simp only [mulVec, dotProduct, bm, jop, add_mul, Finset.sum_add_distrib, mul_assoc,
    ← Finset.mul_sum, bext_sum]

lemma bm_mulVec_restrict {ψ : ℤ → ℂ} (hψ : IsBloch Q k ψ) :
    bm Q a d k *ᵥ (fun r : Fin Q => ψ ((r : ℕ) : ℤ)) = fun r : Fin Q => jop a d ψ ((r : ℕ) : ℤ) := by
  rw [bm_mulVec, bloch_eq_bext hψ]

lemma isHermitian_of_dot {A : Matrix (Fin Q) (Fin Q) ℂ}
    (h : ∀ u w : Fin Q → ℂ, ∑ r, conj (w r) * (A *ᵥ u) r = ∑ r, conj ((A *ᵥ w) r) * u r) :
    A.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have := h (Pi.single j 1) (Pi.single i 1)
  simp only [mulVec_single_one, Pi.single_apply, apply_ite, map_one, map_zero, ite_mul,
    one_mul, zero_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq,
    Finset.mem_univ, if_true, col_apply] at this
  rw [Complex.star_def, ← this]

lemma sum_shift (G : ℤ → ℂ) (hG : ∀ n, G (n + Q) = G n) :
    ∑ r ∈ Finset.range Q, G ((r : ℤ) + 1) = ∑ r ∈ Finset.range Q, G r := by
  have h1 := Finset.sum_range_succ' (fun r : ℕ => G r) Q
  have h2 := Finset.sum_range_succ (fun r : ℕ => G r) Q
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at h1 h2
  have h3 : G (Q : ℤ) = G 0 := by simpa using hG 0
  have := h1.symm.trans h2
  rw [h3] at this
  exact add_right_cancel this

/-- The Bloch matrices are Hermitian. -/
theorem bm_isHermitian (ha : Per Q a) (hd : Per Q d) (k : ℝ) : (bm Q a d k).IsHermitian := by
  apply isHermitian_of_dot
  intro u w
  set U := bext Q k u
  set W := bext Q k w
  have hU : IsBloch Q k U := bext_isBloch u
  have hW : IsBloch Q k W := bext_isBloch w
  rw [bm_mulVec, bm_mulVec]
  have ew : ∀ r : Fin Q, w r = W ((r : ℕ) : ℤ) := fun r => (bext_coe w r).symm
  have eu : ∀ r : Fin Q, u r = U ((r : ℕ) : ℤ) := fun r => (bext_coe u r).symm
  simp only [ew, eu]
  rw [Fin.sum_univ_eq_sum_range (fun r : ℕ => conj (W r) * jop a d U r),
    Fin.sum_univ_eq_sum_range (fun r : ℕ => conj (jop a d W r) * U r)]
  set G : ℤ → ℂ := fun n => (a (n - 1) : ℂ) * conj (W n) * U (n - 1)
  set G' : ℤ → ℂ := fun n => (a (n - 1) : ℂ) * conj (W (n - 1)) * U n
  set Dg : ℤ → ℂ := fun n => (d n : ℂ) * conj (W n) * U n
  have hc := conj_ex_mul k
  have hG : ∀ n, G (n + Q) = G n := by
    intro n
    simp only [G]
    rw [show n + (Q : ℤ) - 1 = (n - 1) + Q by ring, ha (n - 1), hW n, hU (n - 1), map_mul]
    linear_combination ((a (n - 1) : ℂ) * conj (W n) * U (n - 1)) * hc
  have hG' : ∀ n, G' (n + Q) = G' n := by
    intro n
    simp only [G']
    rw [show n + (Q : ℤ) - 1 = (n - 1) + Q by ring, ha (n - 1), hW (n - 1), hU n, map_mul]
    linear_combination ((a (n - 1) : ℂ) * conj (W (n - 1)) * U n) * hc
  have s1 := sum_shift G hG
  have s2 := sum_shift G' hG'
  have eL : ∑ r ∈ Finset.range Q, conj (W r) * jop a d U r =
      ∑ r ∈ Finset.range Q, G r + ∑ r ∈ Finset.range Q, G' ((r : ℤ) + 1) +
        ∑ r ∈ Finset.range Q, Dg r := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    simp only [jop, G, G', Dg, add_sub_cancel_right]
    ring
  have eR : ∑ r ∈ Finset.range Q, conj (jop a d W r) * U r =
      ∑ r ∈ Finset.range Q, G' r + ∑ r ∈ Finset.range Q, G ((r : ℤ) + 1) +
        ∑ r ∈ Finset.range Q, Dg r := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    simp only [jop, G, G', Dg, add_sub_cancel_right, map_add, map_mul, Complex.conj_ofReal]
    ring
  rw [eL, eR, s1, s2]
  ring

/-! ### Hermitian matrices: approximate eigenvalues and eigenvectors -/

/-- `‖u‖² = ∑_r |u_r|²` on `ℂ^Q`. -/
def ns (u : Fin Q → ℂ) : ℝ := ∑ r, ‖u r‖ ^ 2

lemma ns_nonneg (u : Fin Q → ℂ) : 0 ≤ ns u := Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma ns_cast (x : Fin Q → ℂ) : ((ns x : ℝ) : ℂ) = star x ⬝ᵥ x := by
  simp only [ns, dotProduct, Pi.star_apply]
  push_cast
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Complex.star_def, Complex.conj_mul']

lemma ns_unitary {U : Matrix (Fin Q) (Fin Q) ℂ} (h1 : Uᴴ * U = 1) (x : Fin Q → ℂ) :
    ns (U *ᵥ x) = ns x := by
  apply Complex.ofReal_injective
  rw [ns_cast, ns_cast, star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, h1, one_mulVec]

/-- If `‖(A - E)u‖ ≤ ε‖u‖`, `u ≠ 0`, `A` Hermitian, then `A` has an eigenvalue within `ε`
of `E`. -/
theorem exists_eig_near {A : Matrix (Fin Q) (Fin Q) ℂ} (hA : A.IsHermitian) {E ε : ℝ}
    (hε : 0 ≤ ε) {u : Fin Q → ℂ} (hu : 0 < ns u)
    (h : ns (A *ᵥ u - (E : ℂ) • u) ≤ ε ^ 2 * ns u) : ∃ j, |Flow.eig A j - E| ≤ ε := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨σ, hσ⟩ := Flow.exists_perm hA
  have hlam : ∀ i, ε ^ 2 < (hA.eigenvalues i - E) ^ 2 := by
    intro i
    have := hcon (σ.symm i)
    rw [hσ, Equiv.apply_symm_apply] at this
    nlinarith [abs_nonneg (hA.eigenvalues i - E), sq_abs (hA.eigenvalues i - E)]
  set U : Matrix (Fin Q) (Fin Q) ℂ := (hA.eigenvectorUnitary : Matrix (Fin Q) (Fin Q) ℂ)
  set D : Matrix (Fin Q) (Fin Q) ℂ := diagonal (fun i => (hA.eigenvalues i : ℂ))
  have hspec : A = U * D * Uᴴ := Flow.spectral_eq hA
  have h1 : Uᴴ * U = 1 := Flow.eigU_star_mul hA
  have h2 : U * Uᴴ = 1 := Flow.eigU_mul_star hA
  set w := Uᴴ *ᵥ u
  have hu_eq : u = U *ᵥ w := by rw [mulVec_mulVec, h2, one_mulVec]
  have hAu : A *ᵥ u = U *ᵥ (D *ᵥ w) := by
    rw [hspec, ← mulVec_mulVec, ← mulVec_mulVec]
  have hres : A *ᵥ u - (E : ℂ) • u = U *ᵥ (D *ᵥ w - (E : ℂ) • w) := by
    rw [hAu, mulVec_sub, mulVec_smul, ← hu_eq]
  have hnw : ns u = ns w := by rw [hu_eq, ns_unitary h1]
  have hDw : ns (D *ᵥ w - (E : ℂ) • w) = ∑ i, (hA.eigenvalues i - E) ^ 2 * ‖w i‖ ^ 2 := by
    unfold ns
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Pi.sub_apply, Pi.smul_apply, mulVec_diagonal, smul_eq_mul, ← sub_mul, norm_mul,
      mul_pow, show ((hA.eigenvalues i : ℂ) - (E : ℂ)) = ((hA.eigenvalues i - E : ℝ) : ℂ) by
        push_cast; ring, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hres, ns_unitary h1, hDw, hnw] at h
  have hwpos : 0 < ns w := hnw ▸ hu
  obtain ⟨i₀, hi₀⟩ : ∃ i, w i ≠ 0 := by
    by_contra hall
    push_neg at hall
    have : ns w = 0 := by simp [ns, hall]
    linarith
  have hlt : ∑ i, ε ^ 2 * ‖w i‖ ^ 2 < ∑ i, (hA.eigenvalues i - E) ^ 2 * ‖w i‖ ^ 2 := by
    apply Finset.sum_lt_sum
    · intro i _; exact mul_le_mul_of_nonneg_right (hlam i).le (sq_nonneg _)
    · exact ⟨i₀, Finset.mem_univ _, mul_lt_mul_of_pos_right (hlam i₀)
        (by have := norm_pos_iff.2 hi₀; positivity)⟩
  rw [← Finset.mul_sum] at hlt
  unfold ns at h
  linarith

/-- Every ordered eigenvalue of a Hermitian matrix has a unit eigenvector. -/
theorem exists_eigvec {A : Matrix (Fin Q) (Fin Q) ℂ} (hA : A.IsHermitian) (j : Fin Q) :
    ∃ u : Fin Q → ℂ, ns u = 1 ∧ A *ᵥ u = ((Flow.eig A j : ℝ) : ℂ) • u := by
  obtain ⟨σ, hσ⟩ := Flow.exists_perm hA
  refine ⟨⇑(hA.eigenvectorBasis (σ j)), ?_, ?_⟩
  · have h1 : ‖hA.eigenvectorBasis (σ j)‖ = 1 := (hA.eigenvectorBasis).orthonormal.1 _
    rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h1
    exact h1
  · rw [hA.mulVec_eigenvectorBasis, hσ, Complex.coe_smul]

/-! ### Continuity of ordered eigenvalues -/

/-- Ordered eigenvalues of a continuous Hermitian-matrix-valued map are continuous
(Lidskii + `‖·‖_{S_1} ≤ √N ‖·‖_{S_2}`). -/
theorem continuous_eig {X : Type*} [TopologicalSpace X] {N : ℕ}
    {M : X → Matrix (Fin N) (Fin N) ℂ} (hM : Continuous M) (hH : ∀ x, (M x).IsHermitian)
    (j : Fin N) : Continuous fun x => Flow.eig (M x) j := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have hb : ∀ x, |Flow.eig (M x) j - Flow.eig (M x₀) j| ≤
      √N * Flow.hsNorm (M x - M x₀) := by
    intro x
    have h1 := Flow.lidskii (hH x) (hH x₀)
    have h2 := Flow.traceNorm_le_sqrt_mul_hsNorm ((hH x).sub (hH x₀)) (r := N)
      (rank_le_width _)
    have h3 : |Flow.eig (M x) j - Flow.eig (M x₀) j| ≤
        ∑ i, |Flow.eig (M x) i - Flow.eig (M x₀) i| :=
      Finset.single_le_sum (f := fun i => |Flow.eig (M x) i - Flow.eig (M x₀) i|)
        (fun i _ => abs_nonneg _) (Finset.mem_univ j)
    linarith
  have ht : Tendsto (fun x => √N * Flow.hsNorm (M x - M x₀)) (𝓝 x₀) (𝓝 0) := by
    have : Tendsto (fun x => Flow.hsNorm (M x - M x₀)) (𝓝 x₀)
        (𝓝 (Flow.hsNorm (M x₀ - M x₀))) :=
      (Flow.continuous_hsNorm.comp (hM.sub continuous_const)).tendsto x₀
    rw [sub_self, Flow.hsNorm_zero] at this
    simpa using this.const_mul (√N)
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero (fun x => dist_nonneg) (fun x => by rw [Real.dist_eq]; exact hb x) ht

lemma continuous_bm (a d : ℤ → ℝ) : Continuous fun k : ℝ => bm Q a d k := by
  refine continuous_pi fun r => continuous_pi fun s => ?_
  unfold bm jop bext
  fun_prop

/-! ### Discrete Floquet transform -/

/-- The Floquet transform `φ̃_k(n) = ∑_m e(-km) φ(n + mQ)`. -/
def ft (Q : ℕ) (k : ℝ) (φ : ℤ → ℂ) (n : ℤ) : ℂ := ∑' m : ℤ, ex (-(k * m)) * φ (n + m * Q)

/-- `φ` is supported in `[-N, N]`. -/
def Supp (N : ℕ) (φ : ℤ → ℂ) : Prop := ∀ n : ℤ, (N : ℤ) < |n| → φ n = 0

lemma Supp.mono {N N' : ℕ} {φ : ℤ → ℂ} (h : Supp N φ) (hN : N ≤ N') : Supp N' φ :=
  fun n hn => h n (lt_of_le_of_lt (by exact_mod_cast hN) hn)

lemma abs_le_abs_mul_Q (m : ℤ) : |m| ≤ |m * (Q : ℤ)| := by
  rw [abs_mul, abs_of_pos (Qpos (Q := Q))]
  have : (1 : ℤ) ≤ Q := by have := Qpos (Q := Q); omega
  nlinarith [abs_nonneg m]

lemma big {n m : ℤ} {N : ℕ} (h : (N : ℤ) + |n| < |m|) : (N : ℤ) < |n + m * Q| := by
  have h1 := abs_le_abs_mul_Q (Q := Q) m
  have h2 : |m * (Q : ℤ)| ≤ |n + m * Q| + |n| := by
    have := abs_sub (n + m * Q) n
    simpa using this
  linarith

lemma summable_ft {N : ℕ} {φ : ℤ → ℂ} (hφ : Supp N φ) (k : ℝ) (n : ℤ) :
    Summable (fun m : ℤ => ex (-(k * m)) * φ (n + m * Q)) := by
  apply summable_of_ne_finset_zero (s := Finset.Icc (-((N : ℤ) + |n|)) ((N : ℤ) + |n|))
  intro m hm
  have : (N : ℤ) + |n| < |m| := by
    by_contra hc
    push_neg at hc
    exact hm (Finset.mem_Icc.2 (abs_le.1 hc))
  rw [hφ _ (big this), mul_zero]

lemma ft_isBloch (φ : ℤ → ℂ) : IsBloch Q k (ft Q k φ) := by
  intro n
  unfold ft
  have e : ∀ m : ℤ, ex (-(k * m)) * φ (n + Q + m * Q) =
      ex k * (ex (-(k * ((m + 1 : ℤ) : ℝ))) * φ (n + (m + 1) * Q)) := by
    intro m
    rw [show n + (Q : ℤ) + m * Q = n + (m + 1) * Q by ring, ← mul_assoc, ← ex_add]
    congr 2; push_cast; ring
  rw [tsum_congr e, tsum_mul_left]
  congr 1
  exact (Equiv.addRight (1 : ℤ)).tsum_eq (fun m => ex (-(k * m)) * φ (n + m * Q))

/-- The Floquet transform intertwines the Jacobi operator with itself (hence with the Bloch
matrices). -/
lemma ft_jop (ha : Per Q a) (hd : Per Q d) {N : ℕ} {φ : ℤ → ℂ} (hφ : Supp N φ) :
    ft Q k (jop a d φ) = jop a d (ft Q k φ) := by
  funext n
  unfold ft jop
  have e : ∀ m : ℤ, ex (-(k * m)) * ((a (n + m * Q - 1) : ℂ) * φ (n + m * Q - 1) +
      (a (n + m * Q) : ℂ) * φ (n + m * Q + 1) + (d (n + m * Q) : ℂ) * φ (n + m * Q)) =
      (a (n - 1) : ℂ) * (ex (-(k * m)) * φ (n - 1 + m * Q)) +
      (a n : ℂ) * (ex (-(k * m)) * φ (n + 1 + m * Q)) +
      (d n : ℂ) * (ex (-(k * m)) * φ (n + m * Q)) := by
    intro m
    rw [show n + m * Q - 1 = (n - 1) + m * Q by ring, show n + m * Q + 1 = (n + 1) + m * Q by ring,
      ha.shift, ha.shift, hd.shift]
    ring
  have s1 := (summable_ft (Q := Q) hφ k (n - 1)).mul_left (a (n - 1) : ℂ)
  have s2 := (summable_ft (Q := Q) hφ k (n + 1)).mul_left (a n : ℂ)
  have s3 := (summable_ft (Q := Q) hφ k n).mul_left (d n : ℂ)
  rw [tsum_congr e, (s1.add s2).tsum_add s3, s1.tsum_add s2, tsum_mul_left, tsum_mul_left,
    tsum_mul_left]

lemma ft_sub {N : ℕ} {φ ψ : ℤ → ℂ} (hφ : Supp N φ) (hψ : Supp N ψ) (E : ℂ) (n : ℤ) :
    ft Q k (fun m => ψ m - E * φ m) n = ft Q k ψ n - E * ft Q k φ n := by
  unfold ft
  rw [← tsum_mul_left, ← (summable_ft hψ k n).tsum_sub ((summable_ft (Q := Q) hφ k n).mul_left E)]
  congr 1; funext m; ring

lemma jop_supp {N : ℕ} {φ : ℤ → ℂ} (hφ : Supp N φ) (E : ℂ) :
    Supp (N + 1) (fun n => jop a d φ n - E * φ n) := by
  intro n hn
  have h1 : (N : ℤ) < |n - 1| := by
    rcases lt_abs.1 hn with h | h <;> [exact lt_abs.2 (Or.inl (by push_cast at h; omega));
      exact lt_abs.2 (Or.inr (by push_cast at h; omega))]
  have h2 : (N : ℤ) < |n + 1| := by
    rcases lt_abs.1 hn with h | h <;> [exact lt_abs.2 (Or.inl (by push_cast at h; omega));
      exact lt_abs.2 (Or.inr (by push_cast at h; omega))]
  have h3 : (N : ℤ) < |n| := by push_cast at hn; linarith
  simp only [jop, hφ _ h1, hφ _ h2, hφ _ h3]
  ring

/-! ### Discrete Plancherel identity -/

/-- Core Plancherel identity for the discrete Fourier transform on `[-N₁, N₁]`. -/
lemma core_planch (N1 : ℕ) (c : ℤ → ℂ) :
    ∑ j ∈ Finset.range (2 * N1 + 1),
      ‖∑ m ∈ Finset.Icc (-(N1 : ℤ)) N1, ex (-((j : ℝ) / (2 * N1 + 1 : ℕ) * m)) * c m‖ ^ 2 =
    (2 * N1 + 1 : ℕ) * ∑ m ∈ Finset.Icc (-(N1 : ℤ)) N1, ‖c m‖ ^ 2 := by
  set I := Finset.Icc (-(N1 : ℤ)) N1
  set R : ℕ := 2 * N1 + 1
  set x : ℕ → ℤ → ℂ := fun j m => ex (-((j : ℝ) / R * m))
  have key : ∀ m ∈ I, ∀ m' ∈ I, ∑ j ∈ Finset.range R, conj (x j m) * x j m' =
      if m = m' then (R : ℂ) else 0 := by
    intro m hm m' hm'
    rw [Finset.mem_Icc] at hm hm'
    have ht : |m - m'| < (R : ℤ) := by rw [abs_lt]; push_cast [R]; constructor <;> omega
    have := sum_ex (R := R) (by omega) ht
    simp only [sub_eq_zero] at this
    rw [← this]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [x]
    rw [conj_ex, ← ex_add]
    congr 1
    push_cast
    ring
  apply Complex.ofReal_injective
  push_cast
  simp_rw [← Complex.conj_mul']
  calc ∑ j ∈ Finset.range R, conj (∑ m ∈ I, x j m * c m) * (∑ m ∈ I, x j m * c m)
      = ∑ j ∈ Finset.range R, ∑ m ∈ I, ∑ m' ∈ I,
          conj (c m) * c m' * (conj (x j m) * x j m') := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [map_sum, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun m' _ => ?_))
        rw [map_mul]; ring
    _ = ∑ m ∈ I, ∑ m' ∈ I, conj (c m) * c m' *
          ∑ j ∈ Finset.range R, conj (x j m) * x j m' := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun m _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun m' _ => ?_)
        rw [Finset.mul_sum]
    _ = ∑ m ∈ I, ∑ m' ∈ I, conj (c m) * c m' * (if m = m' then (R : ℂ) else 0) := by
        refine Finset.sum_congr rfl (fun m hm => Finset.sum_congr rfl (fun m' hm' => ?_))
        rw [key m hm m' hm']
    _ = ∑ m ∈ I, conj (c m) * c m * R := by
        refine Finset.sum_congr rfl (fun m hm => ?_)
        simp only [mul_ite, mul_zero]
        rw [Finset.sum_ite_eq]
        simp [hm]
    _ = (R : ℂ) * ∑ m ∈ I, conj (c m) * c m := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun m _ => by ring)

/-- Residue decomposition `n = r + mQ`. -/
lemma resid (N1 : ℕ) (F : ℤ → ℝ) (hF : ∀ n : ℤ, (N1 : ℤ) < |n| → F n = 0) :
    ∑ r ∈ Finset.range Q, ∑ m ∈ Finset.Icc (-(N1 : ℤ)) N1, F (r + m * Q) =
      ∑ n ∈ Finset.Icc (-(N1 : ℤ)) N1, F n := by
  have hQ1 : (1 : ℤ) ≤ Q := by have := Qpos (Q := Q); omega
  rw [← Finset.sum_product' (f := fun (r : ℕ) (m : ℤ) => F (r + m * Q))]
  set g : ℕ × ℤ → ℤ := fun p => (p.1 : ℤ) + p.2 * Q
  have hinj : Set.InjOn g ↑(Finset.range Q ×ˢ Finset.Icc (-(N1 : ℤ)) N1) := by
    rintro ⟨r, m⟩ hp ⟨r', m'⟩ hp' heq
    simp only [Finset.coe_product, Set.mem_prod, Finset.coe_range, Set.mem_Iio,
      Finset.coe_Icc, Set.mem_Icc] at hp hp'
    simp only [g] at heq
    have e1 : (m - m') * (Q : ℤ) = (r' : ℤ) - r := by linarith
    have hm : m - m' = 0 := by
      by_contra hne
      have h1 := Int.one_le_abs hne
      have h2 : |(m - m') * (Q : ℤ)| = |m - m'| * Q := by
        rw [abs_mul, abs_of_pos (Qpos (Q := Q))]
      have h3 : |(r' : ℤ) - r| < Q := by rw [abs_lt]; constructor <;> omega
      rw [e1] at h2
      nlinarith
    have hr : (r : ℤ) = r' := by rw [hm, zero_mul] at e1; linarith
    simp only [Prod.mk.injEq]
    exact ⟨by exact_mod_cast hr, by linarith⟩
  have himg := Finset.sum_image (f := F) hinj
  simp only [g] at himg
  rw [← himg]
  symm
  apply Finset.sum_subset
  · intro n hn
    rw [Finset.mem_Icc] at hn
    rw [Finset.mem_image]
    refine ⟨((fidx (Q := Q) n : ℕ), n / Q), ?_, ?_⟩
    · rw [Finset.mem_product, Finset.mem_range, Finset.mem_Icc]
      have hd := Int.ediv_mul_add_emod n Q
      have h0 := Int.emod_nonneg n (Qpos (Q := Q)).ne'
      have hl := Int.emod_lt_of_pos n (Qpos (Q := Q))
      refine ⟨(fidx n).isLt, ?_, ?_⟩
      · by_contra hc
        push_neg at hc
        have : n / Q ≤ -((N1 : ℤ)) - 1 := by omega
        nlinarith
      · by_contra hc
        push_neg at hc
        nlinarith
    · simp only
      rw [add_comm]
      exact (decomp n).symm
  · intro n _ hn
    apply hF
    by_contra hc
    push_neg at hc
    exact hn (Finset.mem_Icc.2 (abs_le.1 hc))

/-- **Discrete Plancherel identity** for the Floquet transform at the frequencies
`k_j = j/R`, `R = 2N₁ + 1`. -/
theorem planch (N1 : ℕ) {f : ℤ → ℂ} (hf : Supp N1 f) :
    ∑ j ∈ Finset.range (2 * N1 + 1),
      ∑ r : Fin Q, ‖ft Q ((j : ℝ) / (2 * N1 + 1 : ℕ)) f ((r : ℕ) : ℤ)‖ ^ 2 =
    (2 * N1 + 1 : ℕ) * ∑ n ∈ Finset.Icc (-(N1 : ℤ)) N1, ‖f n‖ ^ 2 := by
  have hQ1 : (1 : ℤ) ≤ Q := by have := Qpos (Q := Q); omega
  have hft : ∀ (κ : ℝ) (r : Fin Q), ft Q κ f ((r : ℕ) : ℤ) =
      ∑ m ∈ Finset.Icc (-(N1 : ℤ)) N1, ex (-(κ * m)) * f (((r : ℕ) : ℤ) + m * Q) := by
    intro κ r
    unfold ft
    apply tsum_eq_sum
    intro m hm
    rw [Finset.mem_Icc, not_and_or] at hm
    have hr0 : (0 : ℤ) ≤ ((r : ℕ) : ℤ) := by positivity
    have hrQ : ((r : ℕ) : ℤ) < Q := by exact_mod_cast r.isLt
    have : (N1 : ℤ) < |((r : ℕ) : ℤ) + m * Q| := by
      rcases hm with h | h
      · push_neg at h
        refine lt_abs.2 (Or.inr ?_)
        have : m ≤ -(N1 : ℤ) - 1 := by omega
        nlinarith
      · push_neg at h
        refine lt_abs.2 (Or.inl ?_)
        nlinarith
    rw [hf _ this, mul_zero]
  simp_rw [hft]
  rw [Finset.sum_comm]
  have hcore : ∀ r : Fin Q, ∑ j ∈ Finset.range (2 * N1 + 1),
      ‖∑ m ∈ Finset.Icc (-(N1 : ℤ)) N1, ex (-((j : ℝ) / (2 * N1 + 1 : ℕ) * m)) *
        f (((r : ℕ) : ℤ) + m * Q)‖ ^ 2 =
      (2 * N1 + 1 : ℕ) * ∑ m ∈ Finset.Icc (-(N1 : ℤ)) N1, ‖f (((r : ℕ) : ℤ) + m * Q)‖ ^ 2 :=
    fun r => core_planch N1 (fun m => f (((r : ℕ) : ℤ) + m * Q))
  rw [Finset.sum_congr rfl (fun r _ => hcore r), ← Finset.mul_sum]
  congr 1
  rw [Fin.sum_univ_eq_sum_range
    (fun r : ℕ => ∑ m ∈ Finset.Icc (-(N1 : ℤ)) N1, ‖f ((r : ℤ) + m * Q)‖ ^ 2) Q]
  exact resid N1 (fun n => ‖f n‖ ^ 2) (fun n hn => by rw [hf n hn, norm_zero]; ring)

/-! ### Jacobi matrices with `Q`-periodic coefficients -/

/-- The coefficient sequence `n ↦ f(θ + nβ)`. -/
def cb (f : ℝ → ℝ) (β θ : ℝ) (n : ℤ) : ℝ := f (θ + n * β)

lemma jacobi_eq_jop {v b : ℝ → ℝ} (hv : BddFun v) (hb : BddFun b) (β θ : ℝ) (u : L2 ℤ)
    (n : ℤ) : jacobi v b β θ u n = jop (cb b β θ) (cb v β θ) (⇑u) n := by
  rw [jacobi_apply hv hb]
  simp only [jop, cb, Int.cast_sub, Int.cast_one]

lemma res_apply {v b : ℝ → ℝ} (hv : BddFun v) (hb : BddFun b) (β θ E : ℝ) (u : L2 ℤ)
    (n : ℤ) : (jacobi v b β θ u - (E : ℂ) • u) n =
      jop (cb b β θ) (cb v β θ) (⇑u) n - E * u n := by
  rw [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    jacobi_eq_jop hv hb]

/-- An `ℓ²` vector from a finitely supported function. -/
def toL2 (f : ℤ → ℂ) (s : Finset ℤ) (hs : ∀ n ∉ s, f n = 0) : L2 ℤ :=
  ⟨f, (memℓp_two_iff f).2 (summable_of_ne_finset_zero (s := s) (fun n hn => by simp [hs n hn]))⟩

lemma toL2_apply (f : ℤ → ℂ) (s : Finset ℤ) (hs : ∀ n ∉ s, f n = 0) (n : ℤ) :
    toL2 f s hs n = f n := rfl

lemma norm_sq_eq_sum_of_supp (u : L2 ℤ) {N : ℕ} (hu : Supp N ⇑u) :
    ‖u‖ ^ 2 = ∑ n ∈ Finset.Icc (-(N : ℤ)) N, ‖u n‖ ^ 2 := by
  rw [norm_sq_eq_tsum]
  apply tsum_eq_sum
  intro n hn
  have : (N : ℤ) < |n| := by
    by_contra hc
    push_neg at hc
    exact hn (Finset.mem_Icc.2 (abs_le.1 hc))
  rw [hu n this, norm_zero]; ring

/-- **Floquet–Bloch, (⇐).** Every eigenvalue of every Bloch matrix lies in `σ(H_θ)`. -/
theorem eig_mem_spectrum {v b : ℝ → ℝ} (hv : BddFun v) (hb : BddFun b) {β θ : ℝ}
    (ha : Per Q (cb b β θ)) (hd : Per Q (cb v β θ)) (k : ℝ) (j : Fin Q) :
    Flow.eig (bm Q (cb b β θ) (cb v β θ) k) j ∈ spectrum ℝ (jacobi v b β θ) := by
  set a := cb b β θ
  set d := cb v β θ
  set E := Flow.eig (bm Q a d k) j
  obtain ⟨u, hu1, hu⟩ := exists_eigvec (bm_isHermitian ha hd k) j
  obtain ⟨ψ, hψdef⟩ : ∃ ψ, ψ = bext Q k u := ⟨_, rfl⟩
  have hψ : IsBloch Q k ψ := hψdef ▸ bext_isBloch u
  have hψr : ∀ r : Fin Q, ψ ((r : ℕ) : ℤ) = u r := fun r => by rw [hψdef, bext_coe]
  -- `Hψ = Eψ` pointwise
  have heig : jop a d ψ = fun n => (E : ℂ) * ψ n := by
    apply bloch_ext (jop_isBloch ha hd hψ) (fun n => by
      show (E : ℂ) * ψ (n + Q) = ex k * ((E : ℂ) * ψ n); rw [hψ n]; ring)
    intro r
    have := congrFun hu r
    rw [bm_mulVec, Pi.smul_apply, smul_eq_mul, ← hψdef] at this
    simp only at this ⊢
    rw [this, hψr]
  obtain ⟨r₀, hr₀⟩ : ∃ r, u r ≠ 0 := by
    by_contra hall
    push_neg at hall
    simp [ns, hall] at hu1
  obtain ⟨Mb, hMb⟩ := hb
  obtain ⟨Mv, hMv⟩ := hv
  have hMb0 : 0 ≤ Mb := (abs_nonneg _).trans (hMb 0)
  have hMv0 : 0 ≤ Mv := (abs_nonneg _).trans (hMv 0)
  set Um := ∑ r, ‖u r‖
  have hψb : ∀ n, ‖ψ n‖ ≤ Um := fun n => by
    rw [hψdef, norm_bext]
    exact Finset.single_le_sum (f := fun r => ‖u r‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ _)
  set C := (2 * Mb + Mv + |E|) * Um
  have hU0 : 0 < ‖u r₀‖ := norm_pos_iff.2 hr₀
  refine (AMO.spectrum_real_isClosed _).closure_subset (Metric.mem_closure_iff.2 ?_)
  intro ε hε
  obtain ⟨N0, hN0⟩ := exists_nat_gt (4 * C ^ 2 / ((ε / 2) ^ 2 * ‖u r₀‖ ^ 2))
  set L : ℤ := ((N0 + 1 : ℕ) : ℤ) * Q
  set φf : ℤ → ℂ := fun n => if 0 ≤ n ∧ n < L then ψ n else 0
  have hφs : ∀ n ∉ Finset.Ico 0 L, φf n = 0 := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    simp only [φf]; rw [if_neg hn]
  set φ := toL2 φf (Finset.Ico 0 L) hφs
  have hφb : ∀ n, ‖φf n‖ ≤ Um := fun n => by
    simp only [φf]; split_ifs
    · exact hψb n
    · simp only [norm_zero]; exact Finset.sum_nonneg fun _ _ => norm_nonneg _
  -- residual
  set S4 : Finset ℤ := Finset.Icc (-1) 0 ∪ Finset.Icc (L - 1) L with hS4
  have hres0 : ∀ n ∉ S4, jop a d φf n - E * φf n = 0 := by
    intro n hn
    simp only [S4, Finset.mem_union, Finset.mem_Icc, not_or, not_and_or, not_le] at hn
    have hjψ := congrFun heig n
    simp only [jop] at hjψ
    rcases (by omega : n ≤ -2 ∨ (1 ≤ n ∧ n ≤ L - 2) ∨ L + 1 ≤ n) with h | h | h
    · simp only [jop, φf]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      ring
    · simp only [jop, φf]
      rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
      linear_combination hjψ
    · simp only [jop, φf]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      ring
  have hresb : ∀ n, ‖jop a d φf n - E * φf n‖ ≤ C := by
    intro n
    have ha' : ∀ m, ‖((a m : ℝ) : ℂ)‖ ≤ Mb := fun m => by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hMb _
    have hd' : ∀ m, ‖((d m : ℝ) : ℂ)‖ ≤ Mv := fun m => by
      rw [Complex.norm_real, Real.norm_eq_abs]; exact hMv _
    have hE' : ‖((E : ℝ) : ℂ)‖ = |E| := by rw [Complex.norm_real, Real.norm_eq_abs]
    simp only [jop]
    calc ‖(a (n - 1) : ℂ) * φf (n - 1) + (a n : ℂ) * φf (n + 1) + (d n : ℂ) * φf n -
          (E : ℂ) * φf n‖
        ≤ ‖(a (n - 1) : ℂ)‖ * ‖φf (n - 1)‖ + ‖(a n : ℂ)‖ * ‖φf (n + 1)‖ +
            ‖(d n : ℂ)‖ * ‖φf n‖ + ‖(E : ℂ)‖ * ‖φf n‖ := by
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul (E : ℂ)]
          gcongr
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul]
          gcongr
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ Mb * Um + Mb * Um + Mv * Um + |E| * Um := by
          rw [hE']
          gcongr
          · exact ha' _
          · exact hφb _
          · exact ha' _
          · exact hφb _
          · exact hd' _
          · exact hφb _
          · exact hφb _
      _ = C := by ring
  set res := jacobi v b β θ φ - (E : ℂ) • φ
  have hres_apply : ∀ n, res n = jop a d φf n - E * φf n := fun n => by
    rw [res_apply ⟨Mv, hMv⟩ ⟨Mb, hMb⟩ β θ E φ n]; rfl
  have hresn : ‖res‖ ^ 2 ≤ 4 * C ^ 2 := by
    rw [norm_sq_eq_tsum, tsum_eq_sum (s := S4) (fun n hn => by
      rw [hres_apply, hres0 n hn, norm_zero]; ring)]
    calc ∑ n ∈ S4, ‖res n‖ ^ 2 ≤ ∑ n ∈ S4, C ^ 2 :=
          Finset.sum_le_sum fun n _ => by
            rw [hres_apply]; exact pow_le_pow_left₀ (norm_nonneg _) (hresb n) 2
      _ = S4.card * C ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 4 * C ^ 2 := by
          gcongr
          have h1 := Finset.card_union_le (Finset.Icc (-1 : ℤ) 0) (Finset.Icc (L - 1) L)
          have h2 : (Finset.Icc (-1 : ℤ) 0).card = 2 := by simp
          have h3 : (Finset.Icc (L - 1) L).card = 2 := by
            rw [Int.card_Icc]; omega
          have : S4.card ≤ 4 := by rw [hS4]; omega
          exact_mod_cast this
  -- lower bound on `‖φ‖²`
  have hφn : ((N0 + 1 : ℕ) : ℝ) * ‖u r₀‖ ^ 2 ≤ ‖φ‖ ^ 2 := by
    rw [norm_sq_eq_tsum]
    set g : ℕ → ℤ := fun m => ((r₀ : ℕ) : ℤ) + m * Q
    have hginj : Set.InjOn g ↑(Finset.range (N0 + 1)) := by
      intro m _ m' _ h
      simp only [g] at h
      have : (m : ℤ) * Q = m' * Q := by linarith
      exact_mod_cast mul_right_cancel₀ (Qpos (Q := Q)).ne' this
    have hsum : Summable fun n => ‖φ n‖ ^ 2 := summable_norm_sq φ
    refine le_trans ?_ (hsum.sum_le_tsum ((Finset.range (N0 + 1)).image g)
      (fun _ _ => sq_nonneg _))
    rw [Finset.sum_image hginj]
    have hterm : ∀ m ∈ Finset.range (N0 + 1), ‖φ (g m)‖ ^ 2 = ‖u r₀‖ ^ 2 := by
      intro m hm
      rw [Finset.mem_range] at hm
      have hr0 : (0 : ℤ) ≤ ((r₀ : ℕ) : ℤ) := by positivity
      have hrQ : ((r₀ : ℕ) : ℤ) < Q := by exact_mod_cast r₀.isLt
      have hin : 0 ≤ g m ∧ g m < L := by
        simp only [g, L]
        constructor
        · positivity
        · have : (m : ℤ) + 1 ≤ ((N0 + 1 : ℕ) : ℤ) := by push_cast; omega
          nlinarith
      rw [toL2_apply]
      simp only [φf]
      rw [if_pos hin]
      simp only [g]
      rw [hψ.shift, norm_mul, norm_ex, one_mul, hψr]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hN0' : 4 * C ^ 2 < (ε / 2) ^ 2 * (((N0 + 1 : ℕ) : ℝ) * ‖u r₀‖ ^ 2) := by
    have hpos : 0 < (ε / 2) ^ 2 * ‖u r₀‖ ^ 2 := by positivity
    rw [div_lt_iff₀ hpos] at hN0
    push_cast
    nlinarith
  have hφpos : 0 < ‖φ‖ := by
    have h1 : 0 < ((N0 + 1 : ℕ) : ℝ) * ‖u r₀‖ ^ 2 := by positivity
    have h2 := lt_of_lt_of_le h1 hφn
    by_contra hc
    push_neg at hc
    have : ‖φ‖ = 0 := le_antisymm hc (norm_nonneg _)
    rw [this] at h2
    norm_num at h2
  have hφ0 : φ ≠ 0 := norm_pos_iff.1 hφpos
  have hres_le : ‖res‖ ≤ (ε / 2) * ‖φ‖ := by
    have h1 := mul_le_mul_of_nonneg_left hφn (by positivity : (0 : ℝ) ≤ (ε / 2) ^ 2)
    have : ‖res‖ ^ 2 ≤ ((ε / 2) * ‖φ‖) ^ 2 := by rw [mul_pow]; linarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 this
  obtain ⟨E', hE', hdist⟩ :=
    exists_mem_spectrum_near (jacobi_isSelfAdjoint ⟨Mv, hMv⟩ ⟨Mb, hMb⟩ β θ) hφ0 hres_le
  exact ⟨E', hE', by rw [Real.dist_eq]; linarith⟩

/-- **Floquet–Bloch, (⇒).** Every `E ∈ σ(H_θ)` is an eigenvalue of some Bloch matrix
`bm k`, `k ∈ [0,1]`. -/
theorem mem_bands_of_mem_spectrum {v b : ℝ → ℝ} (hv : BddFun v) (hb : BddFun b) {β θ : ℝ}
    (ha : Per Q (cb b β θ)) (hd : Per Q (cb v β θ)) {E : ℝ}
    (hE : E ∈ spectrum ℝ (jacobi v b β θ)) :
    ∃ j : Fin Q, ∃ k ∈ Set.Icc (0 : ℝ) 1, Flow.eig (bm Q (cb b β θ) (cb v β θ) k) j = E := by
  set a := cb b β θ
  set d := cb v β θ
  set S : Set ℝ := ⋃ j : Fin Q, (fun k => Flow.eig (bm Q a d k) j) '' Set.Icc 0 1
  have hS : IsClosed S := isClosed_iUnion_of_finite (fun j =>
    (isCompact_Icc.image (continuous_eig (continuous_bm a d)
      (fun k => bm_isHermitian ha hd k) j)).isClosed)
  suffices hES : E ∈ S by
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hES
    obtain ⟨k, hk, hkE⟩ := hj
    exact ⟨j, k, hk, hkE⟩
  refine hS.closure_subset (Metric.mem_closure_iff.2 fun ε hε => ?_)
  obtain ⟨φ0, hφ0, h0⟩ := exists_approx_eigen (jacobi_isSelfAdjoint hv hb β θ) hE
    (ε := ε / 8) (by positivity)
  obtain ⟨φ, hφne, ⟨N, hN⟩, hφa⟩ := exists_finsupp_approx (by positivity) hφ0 h0
  set φf : ℤ → ℂ := ⇑φ
  have hφs : Supp N φf := hN
  set gf : ℤ → ℂ := fun n => jop a d φf n - (E : ℂ) * φf n with hgf
  have hgs : Supp (N + 1) gf := jop_supp hφs (E : ℂ)
  have hjs : Supp (N + 1) (jop a d φf) := fun n hn => by
    have := jop_supp (a := a) (d := d) hφs 0 n hn
    simpa using this
  have hφs1 : Supp (N + 1) φf := hφs.mono (by omega)
  set κ : ℕ → ℝ := fun j => (j : ℝ) / ((2 * (N + 1) + 1 : ℕ) : ℝ)
  set Φ : ℕ → Fin Q → ℂ := fun j r => ft Q (κ j) φf ((r : ℕ) : ℤ)
  set Γ : ℕ → Fin Q → ℂ := fun j r => ft Q (κ j) gf ((r : ℕ) : ℤ)
  have hrel : ∀ j, bm Q a d (κ j) *ᵥ Φ j - (E : ℂ) • Φ j = Γ j := by
    intro j
    have h1 := bm_mulVec_restrict (a := a) (d := d) (ft_isBloch (Q := Q) (k := κ j) φf)
    funext r
    have h2 : (bm Q a d (κ j) *ᵥ Φ j) r = jop a d (ft Q (κ j) φf) ((r : ℕ) : ℤ) :=
      congrFun h1 r
    rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h2]
    show jop a d (ft Q (κ j) φf) ((r : ℕ) : ℤ) - (E : ℂ) * ft Q (κ j) φf ((r : ℕ) : ℤ) =
      ft Q (κ j) gf ((r : ℕ) : ℤ)
    rw [← ft_jop ha hd hφs, ← ft_sub hφs1 hjs (E : ℂ)]
  have hPφ := planch (Q := Q) (N + 1) hφs1
  have hPg := planch (Q := Q) (N + 1) hgs
  set g : L2 ℤ := jacobi v b β θ φ - (E : ℂ) • φ
  have hgfun : ∀ n, g n = gf n := fun n => res_apply hv hb β θ E φ n
  have hgsupp : Supp (N + 1) ⇑g := fun n hn => by rw [hgfun]; exact hgs n hn
  have hφn := norm_sq_eq_sum_of_supp φ hφs1
  have hgn := norm_sq_eq_sum_of_supp g hgsupp
  simp only [hgfun] at hgn
  have hgle : ‖g‖ ≤ (ε / 4) * ‖φ‖ := by
    have : 2 * (ε / 8) = ε / 4 := by ring
    rw [← this]; exact hφa
  have hgle2 : ‖g‖ ^ 2 ≤ (ε / 4) ^ 2 * ‖φ‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hgle 2
  have hφpos : 0 < ‖φ‖ := norm_pos_iff.2 hφne
  set R : ℕ := 2 * (N + 1) + 1
  have hRpos : (0 : ℝ) < R := by positivity
  have hsumΦ : ∑ j ∈ Finset.range R, ns (Φ j) = R * ‖φ‖ ^ 2 := by
    rw [hφn]; exact hPφ
  have hsumΓ : ∑ j ∈ Finset.range R, ns (Γ j) = R * ‖g‖ ^ 2 := by
    rw [hgn]; exact hPg
  have hsum : ∑ j ∈ Finset.range R, ns (Γ j) ≤ (ε / 4) ^ 2 * ∑ j ∈ Finset.range R, ns (Φ j) := by
    rw [hsumΓ, hsumΦ]
    nlinarith
  have hpos : 0 < ∑ j ∈ Finset.range R, ns (Φ j) := by rw [hsumΦ]; positivity
  obtain ⟨j, hj, hY, hX⟩ := exists_le_mul_of_sum_le (Finset.range R) (fun j => ns (Γ j))
    (fun j => ns (Φ j)) ((ε / 4) ^ 2) (fun j => ns_nonneg _) hsum hpos
  rw [← hrel j] at hX
  obtain ⟨i, hi⟩ := exists_eig_near (bm_isHermitian ha hd (κ j)) (by positivity : 0 ≤ ε / 4)
    hY hX
  have hκ : κ j ∈ Set.Icc (0 : ℝ) 1 := by
    rw [Finset.mem_range] at hj
    refine ⟨by positivity, ?_⟩
    simp only [κ]
    rw [div_le_one (by positivity)]
    exact_mod_cast hj.le
  refine ⟨_, Set.mem_iUnion.2 ⟨i, ⟨κ j, hκ, rfl⟩⟩, ?_⟩
  rw [Real.dist_eq, abs_sub_comm]
  linarith

/-! ### The band structure of `σ(M_{v,b,p/q})` -/

lemma per_cb {f : ℝ → ℝ} (hfp : Function.Periodic f 1) {β : ℝ} {P : ℤ}
    (hβ : (Q : ℝ) * β = P) (θ : ℝ) : Per Q (cb f β θ) := by
  intro n
  simp only [cb]
  rw [show θ + ((n + Q : ℤ) : ℝ) * β = (θ + n * β) + (P : ℝ) * 1 by
    push_cast; linear_combination hβ]
  exact (hfp.int_mul P) _

lemma cb_fract {f : ℝ → ℝ} (hfp : Function.Periodic f 1) (β θ : ℝ) :
    cb f β (Int.fract θ) = cb f β θ := by
  funext n
  simp only [cb]
  rw [show Int.fract θ + n * β = (θ + n * β) + ((-⌊θ⌋ : ℤ) : ℝ) * 1 by
    rw [Int.fract]; push_cast; ring]
  exact (hfp.int_mul _) _

/-- The `j`-th band function `λ_j(θ, k)`: the `j`-th ordered eigenvalue of the Bloch matrix of
`H_θ` at quasi-momentum `k`. -/
def bandFun (Q : ℕ) [NeZero Q] (v b : ℝ → ℝ) (β : ℝ) (j : Fin Q) (x : ℝ × ℝ) : ℝ :=
  Flow.eig (bm Q (cb b β x.1) (cb v β x.1) x.2) j

lemma continuous_bandFun {v b : ℝ → ℝ} (hvc : Continuous v) (hbc : Continuous b)
    (hvp : Function.Periodic v 1) (hbp : Function.Periodic b 1) {β : ℝ} {P : ℤ}
    (hβ : (Q : ℝ) * β = P) (j : Fin Q) : Continuous (bandFun Q v b β j) := by
  refine continuous_eig (M := fun x : ℝ × ℝ => bm Q (cb b β x.1) (cb v β x.1) x.2) ?_
    (fun x => bm_isHermitian (per_cb hbp hβ _) (per_cb hvp hβ _) _) j
  refine continuous_pi fun r => continuous_pi fun s => ?_
  unfold bm jop bext cb
  fun_prop

/-- The unit square `[0,1]²` of phases and quasi-momenta. -/
def sq01 : Set (ℝ × ℝ) := Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1

/-- A continuous image of `[0,1]²` in `ℝ` is a closed interval. -/
lemma image_eq_Icc {f : ℝ × ℝ → ℝ} (hf : Continuous f) :
    f '' sq01 = Set.Icc (sInf (f '' sq01)) (sSup (f '' sq01)) := by
  have hc : IsCompact (f '' sq01) := (isCompact_Icc.prod isCompact_Icc).image hf
  have hconn : IsConnected (f '' sq01) :=
    ((isConnected_Icc zero_le_one).prod (isConnected_Icc zero_le_one)).image f hf.continuousOn
  apply Set.Subset.antisymm
  · intro y hy
    exact ⟨csInf_le hc.bddBelow hy, le_csSup hc.bddAbove hy⟩
  · exact hconn.isPreconnected.Icc_subset (hc.sInf_mem hconn.nonempty)
      (hc.sSup_mem hconn.nonempty)

/-- **Band structure.** For `Qβ ∈ ℤ` and continuous `1`-periodic `v, b`,
`σ(M_{v,b,β}) = ⋃_{j<Q} λ_j([0,1]²)`. -/
theorem sigmaM_eq_bands {v b : ℝ → ℝ} (hv : BddFun v) (hb : BddFun b) (hvc : Continuous v)
    (hbc : Continuous b) (hvp : Function.Periodic v 1) (hbp : Function.Periodic b 1)
    {β : ℝ} {P : ℤ} (hβ : (Q : ℝ) * β = P) :
    sigmaM v b β = ⋃ j : Fin Q, bandFun Q v b β j '' sq01 := by
  apply Set.Subset.antisymm
  · refine closure_minimal ?_ (isClosed_iUnion_of_finite fun j =>
      ((isCompact_Icc.prod isCompact_Icc).image
        (continuous_bandFun hvc hbc hvp hbp hβ j)).isClosed)
    intro E hE
    obtain ⟨θ, hθ⟩ := Set.mem_iUnion.1 hE
    obtain ⟨j, k, hk, hkE⟩ :=
      mem_bands_of_mem_spectrum hv hb (per_cb hbp hβ θ) (per_cb hvp hβ θ) hθ
    refine Set.mem_iUnion.2 ⟨j, ⟨(Int.fract θ, k),
      ⟨⟨Int.fract_nonneg θ, (Int.fract_lt_one θ).le⟩, hk⟩, ?_⟩⟩
    simp only [bandFun]
    rw [cb_fract hbp, cb_fract hvp]
    exact hkE
  · intro E hE
    obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hE
    obtain ⟨x, -, rfl⟩ := hj
    exact subset_closure (Set.mem_iUnion.2
      ⟨x.1, eig_mem_spectrum hv hb (per_cb hbp hβ x.1) (per_cb hvp hβ x.1) x.2 j⟩)

/-- **`σ(M_{v,b,β})` is a union of `Q` closed intervals** for `Qβ ∈ ℤ`. -/
theorem sigmaM_eq_Icc_union {v b : ℝ → ℝ} (hv : BddFun v) (hb : BddFun b)
    (hvc : Continuous v) (hbc : Continuous b) (hvp : Function.Periodic v 1)
    (hbp : Function.Periodic b 1) {β : ℝ} {P : ℤ} (hβ : (Q : ℝ) * β = P) :
    ∃ E1 E2 : ℕ → ℝ, sigmaM v b β = ⋃ m ∈ Finset.range Q, Set.Icc (E1 m) (E2 m) := by
  refine ⟨fun m => if h : m < Q then sInf (bandFun Q v b β ⟨m, h⟩ '' sq01) else 0,
    fun m => if h : m < Q then sSup (bandFun Q v b β ⟨m, h⟩ '' sq01) else 0, ?_⟩
  rw [sigmaM_eq_bands hv hb hvc hbc hvp hbp hβ]
  ext E
  simp only [Set.mem_iUnion, Finset.mem_range]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨j.1, j.2, ?_⟩
    rw [dif_pos j.2, dif_pos j.2]
    rw [image_eq_Icc (continuous_bandFun hvc hbc hvp hbp hβ j)] at hj
    simpa only [Fin.eta] using hj
  · rintro ⟨m, hm, hE⟩
    refine ⟨⟨m, hm⟩, ?_⟩
    rw [dif_pos hm, dif_pos hm] at hE
    rw [image_eq_Icc (continuous_bandFun hvc hbc hvp hbp hβ _)]
    exact hE

end FB

/-- A function satisfying a Lipschitz inequality is continuous. -/
lemma continuous_of_lip {f : ℝ → ℝ} {K : ℝ} (h : ∀ x y, |f x - f y| ≤ K * |x - y|) :
    Continuous f := by
  rw [Metric.continuous_iff]
  intro x ε hε
  refine ⟨ε / (|K| + 1), by positivity, fun y hy => ?_⟩
  rw [Real.dist_eq] at hy ⊢
  calc |f y - f x| ≤ K * |y - x| := h y x
    _ ≤ |K| * |y - x| := mul_le_mul_of_nonneg_right (le_abs_self K) (abs_nonneg _)
    _ ≤ (|K| + 1) * |y - x| := by nlinarith [abs_nonneg (y - x)]
    _ < (|K| + 1) * (ε / (|K| + 1)) := by
        apply mul_lt_mul_of_pos_left hy; positivity
    _ = ε := by field_simp

/-- **`RationalBands` holds** (Floquet–Bloch theory): for irrational `α`, continuous
`1`-periodic bounded `v, b`, each `σ(M_{v,b,p_n/q_n})` is a union of `q_n` closed
intervals. -/
theorem rationalBands {v b : ℝ → ℝ} (hv : BddFun v) (hb : BddFun b) (hvc : Continuous v)
    (hbc : Continuous b) (hvp : Function.Periodic v 1) (hbp : Function.Periodic b 1) {α : ℝ}
    (hα : Irrational α) : RationalBands v b α := by
  intro n
  haveI : NeZero (qN α n) := ⟨by have := one_le_qN hα n; omega⟩
  have hβ : ((qN α n : ℕ) : ℝ) * (p α n / q α n) = (pZ α n : ℝ) := by
    rw [qN_cast hα, pZ_cast]
    field_simp [(q_pos hα n).ne']
  obtain ⟨E1, E2, hE⟩ := FB.sigmaM_eq_Icc_union hv hb hvc hbc hvp hbp hβ
  exact ⟨qN α n, E1, E2, by rw [qN_cast hα], hE⟩

/-- **Theorem 1.3 (`measure`), eq. (1.5), unconditional.** Let `v, b` be bounded, Lipschitz
and `1`-periodic, `b` with a zero and countably many zeros, and `α` irrational.  Then
`|σ(M_{v,b,p_n/q_n})| → |σ(M_{v,b,α})|`. -/
theorem measure_convergence' {v b : ℝ → ℝ} (hv : BddFun v) (hb : BddFun b) {Kb Kv : ℝ}
    (hKb : 0 ≤ Kb) (hKv : 0 ≤ Kv) (hLb : ∀ x y, |b x - b y| ≤ Kb * |x - y|)
    (hLv : ∀ x y, |v x - v y| ≤ Kv * |x - y|) (hZ : {x | b x = 0}.Countable)
    (hper : Function.Periodic b 1) (hvper : Function.Periodic v 1) (hzero : ∃ x₀, b x₀ = 0)
    {α : ℝ} (hα : Irrational α) :
    Tendsto (fun n => MeasureTheory.volume (sigmaM v b (p α n / q α n))) atTop
      (𝓝 (MeasureTheory.volume (sigmaM v b α))) :=
  measure_convergence hv hb hKb hKv hLb hLv hZ hper hzero hα
    (rationalBands hv hb (continuous_of_lip hLv) (continuous_of_lip hLb) hvper hper hα)

/-- **Another proof of Theorem 1.2, unconditional in the band structure:** if moreover
`|σ(M_{v,b,p_n/q_n})| ≤ C/q_n`, then `|σ(M_{v,b,α})| = 0`. -/
theorem volume_eq_zero_of_small_bands' {v b : ℝ → ℝ} (hv : BddFun v) (hb : BddFun b)
    {Kb Kv : ℝ} (hKb : 0 ≤ Kb) (hKv : 0 ≤ Kv) (hLb : ∀ x y, |b x - b y| ≤ Kb * |x - y|)
    (hLv : ∀ x y, |v x - v y| ≤ Kv * |x - y|) (hZ : {x | b x = 0}.Countable)
    (hper : Function.Periodic b 1) (hvper : Function.Periodic v 1) (hzero : ∃ x₀, b x₀ = 0)
    {α : ℝ} (hα : Irrational α) {C : ℝ}
    (hsmall : ∀ n, MeasureTheory.volume (sigmaM v b (p α n / q α n)) ≤
      ENNReal.ofReal (C / q α n)) :
    MeasureTheory.volume (sigmaM v b α) = 0 :=
  volume_eq_zero_of_small_bands hv hb hKb hKv hLb hLv hZ hper hzero hα
    (rationalBands hv hb (continuous_of_lip hLv) (continuous_of_lip hLb) hvper hper hα) hsmall

end CAH
