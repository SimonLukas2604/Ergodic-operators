/-
Copyright (c) 2026. Formalization of
  S. Becker, S. Jitomirskaya, I. Krasovsky, "Critical almost Mathieu operator: hidden
  singularity, gap continuity, and the Hausdorff dimension of the spectrum"
  (arXiv:1909.04429v2).

# Separation of blocks: Lemma `lemma-subm` and Proposition `prop-blocks`

Paper §"Finite covers for the spectrum", subsection "Separation of blocks"
(`section-separation`, tex l. 1067–1341).

## Realisation of `ℋ = ⊕_k ℂ^{N_k}`

Instead of an abstract `ℓ²`-direct sum we realise `ℋ` as `ℓ²(ℤ)` itself, cut into consecutive
blocks `[c_k, c_{k+1})` by a sequence of cut points `c : ℤ → ℤ` with `c_{k+1} - c_k = N_k ≥ 2`
(`cutEquiv : ℤ ≃ Σ k, Fin N_k`; this is the unitary `U_Id` of the paper, l. 1293).  For a
uniformly bounded family of block matrices `M_k`, `blockOp e M` is the block-diagonal operator
`⊕_k M_k` (§1).  It is multiplicative, unital, and `‖⊕ M_k‖ ≤ sup_k ‖M_k‖`.

For the Jacobi matrix `H = jacobi v b α θ` (1.3), removing the bonds `b(x_k)` between the sites
`c_k - 1` and `c_k`, where `x_k = θ + (c_k - 1) α`, gives `H = D + R` (`jacobi_eq_add`), where
* `D = ⊕_k B̂_{N_k}(x_k)` is block diagonal (`blockMatrix` of `BoundaryResolvent.lean`, (BhN));
* `R = Γ^* F Γ` is the removed-bond operator, `F_k = [[0, b(x_k)], [b(x_k), 0]]`; we realise it as
  the weighted shift `(R u)(c_k) = b(x_k) u(c_k - 1)`, `(R u)(c_k - 1) = b(x_k) u(c_k)`
  (`bondOp`), which satisfies `R = P R P` with `P = ⊕ P_{N_k}` (`bondOp_eq_proj`) and
  `‖R‖ ≤ sup_k |b(x_k)| = ‖F‖` (`norm_bondOp_le`).

## Main results

* `lemma_subm_jacobi` — **Lemma `lemma-subm`** (l. 1124–1205) for `A = H = D + Γ^* F Γ`:
  `σ(H) ⊆ closure (⋃_k ⋃_{V = V^*, ‖V‖ ≤ 2τ} σ(B̂_{N_k}(x_k) + Γ̂^* V Γ̂))` whenever
  `τ ≥ sup_k |b(x_k)|`.  The proof is the paper's: the case `E ∈ σ(D)` is covered by `V = 0`
  together with `σ(D) ⊆ closure ⋃ σ(B_k)` (resolvent of a block-diagonal operator with
  uniformly bounded block resolvents); otherwise `‖G_k(E)‖ ≤ (2τ)⁻¹` for all `k`
  (`norm_bdryResolvent_le`), hence `‖G(E)‖ ≤ (2τ)⁻¹ < τ⁻¹` and the Neumann/ABBA step
  (`isUnit_add_boundary_of_norm_lt`) shows `E ∉ σ(H)`.
* `abs_sub_le_of_deriv_le`, `abs_bond_le` — the mean value bound `|b(x)| ≤ C(b) |J_n|` (l. 1316).
* `prop_blocks` — **Proposition `prop-blocks`** (l. 1318–1327), with the return-time structure
  of the cut points (Lemma `lemma-rt`) taken as explicit hypotheses: gaps `N_k ∈ {q_n, q_{n-1}}`
  and bond phases `x_k ∈ J_n (mod 1)`.  `prop_blocks_periodic` is the literal statement
  (union over `x ∈ J_n`) for `1`-periodic `v, b`.

## Hypotheses added / deviations (documented)

* `prop_blocks` assumes `N_k ≥ 2` explicitly (in the paper this follows from `N_k ∈ {q_n,q_{n-1}}`,
  `n ≥ 3`), and the existence of the cut points with the return-time structure (Lemma `lemma-rt`,
  formalised elsewhere).  The bound `C(b)` is any bound on `|b'|`; `b` is assumed differentiable
  (the paper: `C^1`) and `v, b` bounded (automatic for continuous periodic functions).
* For `b` of period `2` the bond phases `x_k` are only known modulo `1`, and
  `B̂_N(x + 1) ≠ B̂_N(x)` in general; so `prop_blocks` takes the union over `x ∈ J_n + ℤ`.
  For `1`-periodic `v, b` this is the union over `x ∈ J_n` (`prop_blocks_periodic`).
* Matrix norms are `ℓ²` operator norms (scoped `Matrix.Norms.L2Operator`).

No `sorry`s.
-/
import CriticalAMOHausdorff.BoundaryResolvent

noncomputable section

open Matrix L2
open scoped Matrix.Norms.L2Operator

namespace CAH

/-! ## 1. Block-diagonal operators on `ℓ²(ι)` -/

section BlockOp

variable {ι K : Type*} {N : K → ℕ} (e : ι ≃ Σ k, Fin (N k))

/-- The restriction of `u : ι → ℂ` to the `k`-th block, as a vector in `ℂ^{N_k}`. -/
def blockVec (u : ι → ℂ) (k : K) : Fin (N k) → ℂ := fun j => u (e.symm ⟨k, j⟩)

/-- The underlying function of the block-diagonal operator `⊕_k M_k`. -/
def blockFun (M : ∀ k, Matrix (Fin (N k)) (Fin (N k)) ℂ) (u : ι → ℂ) : ι → ℂ :=
  fun n => (M (e n).1 *ᵥ blockVec e u (e n).1) (e n).2

lemma blockFun_symm (M : ∀ k, Matrix (Fin (N k)) (Fin (N k)) ℂ) (u : ι → ℂ)
    (s : Σ k, Fin (N k)) : blockFun e M u (e.symm s) = (M s.1 *ᵥ blockVec e u s.1) s.2 := by
  unfold blockFun
  generalize hs : e (e.symm s) = t
  rw [Equiv.apply_symm_apply] at hs
  subst hs; rfl

lemma blockVec_add (f g : ι → ℂ) (k : K) :
    blockVec e (f + g) k = blockVec e f k + blockVec e g k := rfl

lemma blockVec_smul (a : ℂ) (f : ι → ℂ) (k : K) :
    blockVec e (a • f) k = a • blockVec e f k := rfl

lemma blockVec_sq_le {M : ∀ k, Matrix (Fin (N k)) (Fin (N k)) ℂ} {C : ℝ} (hC : ∀ k, ‖M k‖ ≤ C)
    (hC0 : 0 ≤ C) (y : ∀ k, Fin (N k) → ℂ) (k : K) :
    ∑ i, ‖(M k *ᵥ y k) i‖ ^ 2 ≤ C ^ 2 * ∑ i, ‖y k i‖ ^ 2 := by
  have h := l2_opNorm_mulVec (M k) (WithLp.toLp 2 (y k))
  have h' : ‖(EuclideanSpace.equiv (Fin (N k)) ℂ).symm (M k *ᵥ y k)‖ ≤
      C * ‖(WithLp.toLp 2 (y k) : EuclideanSpace ℂ (Fin (N k)))‖ :=
    h.trans (mul_le_mul_of_nonneg_right (hC k) (norm_nonneg _))
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h' 2
  rw [mul_pow, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at h2
  simpa using h2

lemma summable_blockFun {M : ∀ k, Matrix (Fin (N k)) (Fin (N k)) ℂ} {C : ℝ}
    (hC : ∀ k, ‖M k‖ ≤ C) (hC0 : 0 ≤ C) (u : L2 ι) :
    Summable (fun n => ‖blockFun e M u n‖ ^ 2) ∧
      ∑' n, ‖blockFun e M u n‖ ^ 2 ≤ C ^ 2 * ‖u‖ ^ 2 := by
  set f : (Σ k, Fin (N k)) → ℝ := fun s => ‖u (e.symm s)‖ ^ 2
  set g : (Σ k, Fin (N k)) → ℝ := fun s => ‖blockFun e M u (e.symm s)‖ ^ 2
  have hf : Summable f := (e.symm.summable_iff (f := fun n => ‖u n‖ ^ 2)).2 (summable_norm_sq u)
  have hf' := (summable_sigma_of_nonneg (fun s => by positivity : ∀ s, 0 ≤ f s)).1 hf
  have hfib : ∀ k, ∑ i, g ⟨k, i⟩ ≤ C ^ 2 * ∑ i, f ⟨k, i⟩ := by
    intro k
    simp only [g, f, blockFun_symm]
    exact blockVec_sq_le hC hC0 (blockVec e u) k
  have hgk : Summable fun k => ∑' i, g ⟨k, i⟩ := by
    refine (hf'.2.mul_left (C ^ 2)).of_nonneg_of_le (fun k => by positivity) fun k => ?_
    simpa only [tsum_fintype] using hfib k
  have hg : Summable g :=
    (summable_sigma_of_nonneg (fun s => by positivity : ∀ s, 0 ≤ g s)).2
      ⟨fun k => (Summable.of_finite), hgk⟩
  refine ⟨(e.symm.summable_iff (f := fun n => ‖blockFun e M u n‖ ^ 2)).1 hg, ?_⟩
  rw [← e.symm.tsum_eq (fun n => ‖blockFun e M u n‖ ^ 2), norm_sq_eq_tsum,
    ← e.symm.tsum_eq (fun n => ‖u n‖ ^ 2)]
  change ∑' s, g s ≤ C ^ 2 * ∑' s, f s
  rw [hg.tsum_sigma' (fun k => Summable.of_finite), hf.tsum_sigma' (fun k => Summable.of_finite),
    ← tsum_mul_left]
  refine hgk.tsum_le_tsum (fun k => ?_) (hf'.2.mul_left _)
  simpa only [tsum_fintype] using hfib k

/-- The block-diagonal operator as a linear map, for uniformly bounded blocks. -/
def blockLin (M : ∀ k, Matrix (Fin (N k)) (Fin (N k)) ℂ) {C : ℝ} (hC : ∀ k, ‖M k‖ ≤ C)
    (hC0 : 0 ≤ C) : L2 ι →ₗ[ℂ] L2 ι where
  toFun u := ⟨blockFun e M u, (memℓp_two_iff _).2 (summable_blockFun e hC hC0 u).1⟩
  map_add' u w := by
    ext n
    simp only [blockFun, lp.coeFn_add, Pi.add_apply]
    rw [blockVec_add, mulVec_add]
    rfl
  map_smul' a u := by
    ext n
    simp only [blockFun, lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
    rw [blockVec_smul, mulVec_smul]
    rfl

/-- The block-diagonal operator `⊕_k M_k` on `ℓ²(ι)` (with `ι ≃ Σ k, Fin N_k`).  It is defined to
be `0` if the blocks are not uniformly bounded (a case that never occurs below). -/
def blockOp (M : ∀ k, Matrix (Fin (N k)) (Fin (N k)) ℂ) : L2 ι →L[ℂ] L2 ι :=
  open Classical in
  if h : ∃ C, ∀ k, ‖M k‖ ≤ C then
    (blockLin e M (C := max h.choose 0) (fun k => (h.choose_spec k).trans (le_max_left _ _))
        (le_max_right _ _)).mkContinuous (max h.choose 0) fun u => by
      have key := (summable_blockFun e (C := max h.choose 0)
        (fun k => (h.choose_spec k).trans (le_max_left _ _)) (le_max_right _ _) u).2
      have hsq : ‖blockLin e M (C := max h.choose 0)
          (fun k => (h.choose_spec k).trans (le_max_left _ _)) (le_max_right _ _) u‖ ^ 2 ≤
            (max h.choose 0 * ‖u‖) ^ 2 := by
        rw [norm_sq_eq_tsum, mul_pow]; exact key
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq
  else 0

variable {e}

lemma norm_one_matrix_le (n : Type*) [Fintype n] [DecidableEq n] :
    ‖(1 : Matrix n n ℂ)‖ ≤ 1 := by
  rcases isEmpty_or_nonempty n with h | h
  · rw [Subsingleton.elim (1 : Matrix n n ℂ) 0, norm_zero]; exact zero_le_one
  · exact CStarRing.norm_one.le

/-- Uniformly bounded block families. -/
def BlockBdd (M : ∀ k, Matrix (Fin (N k)) (Fin (N k)) ℂ) : Prop := ∃ C, ∀ k, ‖M k‖ ≤ C

lemma blockOp_apply {M : ∀ k, Matrix (Fin (N k)) (Fin (N k)) ℂ} (hM : BlockBdd M) (u : L2 ι)
    (n : ι) : blockOp e M u n = blockFun e M u n := by
  unfold blockOp
  split_ifs with h
  · rfl
  · exact absurd hM h

lemma norm_blockOp_le {M : ∀ k, Matrix (Fin (N k)) (Fin (N k)) ℂ} {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ k, ‖M k‖ ≤ C) : ‖blockOp e M‖ ≤ C := by
  refine ContinuousLinearMap.opNorm_le_bound _ hC0 fun u => ?_
  have key := (summable_blockFun e hC hC0 u).2
  have hsq : ‖blockOp e M u‖ ^ 2 ≤ (C * ‖u‖) ^ 2 := by
    rw [norm_sq_eq_tsum, mul_pow]
    convert key using 3 with n
    rw [blockOp_apply ⟨C, hC⟩]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

lemma BlockBdd.mul {M M' : ∀ k, Matrix (Fin (N k)) (Fin (N k)) ℂ} (hM : BlockBdd M)
    (hM' : BlockBdd M') : BlockBdd (fun k => M k * M' k) := by
  obtain ⟨C, hC⟩ := hM
  obtain ⟨C', hC'⟩ := hM'
  refine ⟨max C 0 * max C' 0, fun k => (l2_opNorm_mul _ _).trans ?_⟩
  exact mul_le_mul ((hC k).trans (le_max_left _ _)) ((hC' k).trans (le_max_left _ _))
    (norm_nonneg _) (le_max_right _ _)

lemma blockOp_mul {M M' : ∀ k, Matrix (Fin (N k)) (Fin (N k)) ℂ} (hM : BlockBdd M)
    (hM' : BlockBdd M') :
    blockOp e (fun k => M k * M' k) = blockOp e M * blockOp e M' := by
  ext u n
  rw [mul_apply_eq_comp, blockOp_apply (hM.mul hM'), blockOp_apply hM]
  simp only [blockFun]
  rw [← mulVec_mulVec]
  congr 2
  funext j
  simp only [blockVec]
  rw [blockOp_apply hM']
  exact (blockFun_symm e M' u ⟨_, j⟩).symm

lemma blockOp_one : blockOp e (fun k => (1 : Matrix (Fin (N k)) (Fin (N k)) ℂ)) = 1 := by
  have hb : BlockBdd (fun k => (1 : Matrix (Fin (N k)) (Fin (N k)) ℂ)) :=
    ⟨1, fun k => by
      show ‖(1 : Matrix (Fin (N k)) (Fin (N k)) ℂ)‖ ≤ 1
      rcases isEmpty_or_nonempty (Fin (N k)) with h | h
      · rw [Subsingleton.elim (1 : Matrix (Fin (N k)) (Fin (N k)) ℂ) 0, norm_zero]
        exact zero_le_one
      · exact CStarRing.norm_one.le⟩
  ext u n
  rw [blockOp_apply hb, one_apply_eq_self]
  simp only [blockFun, one_mulVec, blockVec]
  rw [Sigma.eta, Equiv.symm_apply_apply]

lemma blockOp_sub_smul {M : ∀ k, Matrix (Fin (N k)) (Fin (N k)) ℂ} (hM : BlockBdd M) (z : ℂ) :
    blockOp e (fun k => M k - z • 1) = blockOp e M - z • 1 := by
  obtain ⟨C, hC⟩ := hM
  have hb : BlockBdd (fun k => M k - z • (1 : Matrix (Fin (N k)) (Fin (N k)) ℂ)) :=
    ⟨C + ‖z‖, fun k => by
      refine (norm_sub_le _ _).trans (add_le_add (hC k) ?_)
      rw [norm_smul]
      rcases isEmpty_or_nonempty (Fin (N k)) with h | h
      · rw [Subsingleton.elim (1 : Matrix (Fin (N k)) (Fin (N k)) ℂ) 0, norm_zero, mul_zero]
        exact norm_nonneg _
      · rw [CStarRing.norm_one, mul_one]⟩
  ext u n
  rw [blockOp_apply hb, _root_.sub_apply, lp.coeFn_sub, Pi.sub_apply,
    blockOp_apply ⟨C, hC⟩]
  simp only [blockFun, sub_mulVec, Pi.sub_apply, smul_mulVec, one_mulVec, Pi.smul_apply,
    blockVec, Sigma.eta, Equiv.symm_apply_apply, _root_.smul_apply, one_apply_eq_self,
    lp.coeFn_smul]

end BlockOp

/-! ## 2. Cut points -/

section Cuts

variable (c : ℤ → ℤ) (hc : ∀ k, c k + 2 ≤ c (k + 1))

/-- The block lengths `N_k = c_{k+1} - c_k`. -/
def cutLen (k : ℤ) : ℕ := (c (k + 1) - c k).toNat

include hc

lemma cutLen_ge (k : ℤ) : 2 ≤ cutLen c k := by
  have := hc k
  unfold cutLen; omega

lemma cutLen_eq (k : ℤ) : (cutLen c k : ℤ) = c (k + 1) - c k := by
  have := hc k
  unfold cutLen; omega

lemma cut_strictMono : StrictMono c :=
  strictMono_int_of_lt_succ fun k => by have := hc k; omega

lemma cut_ge_of_nonneg {k : ℤ} (hk : 0 ≤ k) : c 0 + k ≤ c k := by
  induction k, hk using Int.leInduction with
  | base => simp
  | succ k _ ih => have := hc k; omega

lemma cut_le_of_nonpos {k : ℤ} (hk : k ≤ 0) : c k ≤ c 0 + k := by
  induction k, hk using Int.leInductionDown with
  | base => simp
  | pred k _ ih => have := hc (k - 1); simp only [sub_add_cancel] at this; omega

lemma cut_bijective :
    Function.Bijective (fun s : Σ k, Fin (cutLen c k) => c s.1 + (s.2 : ℕ)) := by
  have hmono := (cut_strictMono c hc).monotone
  constructor
  · rintro ⟨k, i⟩ ⟨k', i'⟩ h
    simp only at h
    have hi := i.2
    have hi' := i'.2
    have hl := cutLen_eq c hc k
    have hl' := cutLen_eq c hc k'
    have hk : k = k' := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · have := hmono (show k + 1 ≤ k' by omega); omega
      · have := hmono (show k' + 1 ≤ k by omega); omega
    subst hk
    have : i = i' := Fin.ext (by omega)
    subst this; rfl
  · intro n
    obtain ⟨k, hk, hmax⟩ := Int.exists_greatest_of_bdd (P := fun k => c k ≤ n)
      ⟨max 0 (n - c 0), fun k hk => by
        rcases le_or_gt 0 k with h | h
        · have := cut_ge_of_nonneg c hc h; omega
        · omega⟩
      ⟨min 0 (n - c 0), by
        have := cut_le_of_nonpos c hc (min_le_left 0 (n - c 0)); omega⟩
    have hk1 : n < c (k + 1) := by
      by_contra h; push Not at h; have := hmax (k + 1) h; omega
    have hl := cutLen_eq c hc k
    refine ⟨⟨k, ⟨(n - c k).toNat, by omega⟩⟩, ?_⟩
    simp only; omega

/-- The identification `ℤ ≃ Σ k, Fin N_k`, `c_k + j ↤ (k, j)` (the unitary `U_Id`, l. 1293). -/
def cutEquiv : ℤ ≃ Σ k, Fin (cutLen c k) := (Equiv.ofBijective _ (cut_bijective c hc)).symm

lemma cutEquiv_symm_apply (s : Σ k, Fin (cutLen c k)) :
    (cutEquiv c hc).symm s = c s.1 + (s.2 : ℕ) := rfl

lemma cutEquiv_spec (n : ℤ) :
    n = c (cutEquiv c hc n).1 + ((cutEquiv c hc n).2 : ℕ) := by
  conv_lhs => rw [← (cutEquiv c hc).symm_apply_apply n]
  rfl

lemma cutEquiv_apply_eq {n k : ℤ} (i : Fin (cutLen c k)) (h : n = c k + (i : ℕ)) :
    cutEquiv c hc n = ⟨k, i⟩ := by
  rw [h]; exact (cutEquiv c hc).apply_symm_apply ⟨k, i⟩

lemma cutEquiv_first_iff (n : ℤ) :
    ((cutEquiv c hc n).2 : ℕ) = 0 ↔ n ∈ Set.range c := by
  constructor
  · intro h; exact ⟨(cutEquiv c hc n).1, by have := cutEquiv_spec c hc n; omega⟩
  · rintro ⟨k, rfl⟩
    have h2 := cutLen_ge c hc k
    rw [cutEquiv_apply_eq c hc (k := k) ⟨0, by omega⟩ (by simp)]

lemma cutEquiv_last_iff (n : ℤ) :
    ((cutEquiv c hc n).2 : ℕ) + 1 = cutLen c (cutEquiv c hc n).1 ↔ n + 1 ∈ Set.range c := by
  constructor
  · intro h
    refine ⟨(cutEquiv c hc n).1 + 1, ?_⟩
    have := cutEquiv_spec c hc n
    have := cutLen_eq c hc (cutEquiv c hc n).1
    omega
  · rintro ⟨k, hk⟩
    have h2 := cutLen_ge c hc (k - 1)
    have hl := cutLen_eq c hc (k - 1)
    simp only [sub_add_cancel] at hl
    rw [cutEquiv_apply_eq c hc (k := k - 1) ⟨cutLen c (k - 1) - 1, by omega⟩ (by simp; omega)]
    simp only; omega

lemma first_iff' (k : ℤ) (i : Fin (cutLen c k)) :
    (i : ℕ) = 0 ↔ c k + ((i : ℕ) : ℤ) ∈ Set.range c := by
  have hmono := cut_strictMono c hc
  have hL := cutLen_eq c hc k
  have hi := i.2
  constructor
  · intro h; exact ⟨k, by omega⟩
  · rintro ⟨k', hk'⟩
    have h1 : k ≤ k' := hmono.le_iff_le.1 (by omega)
    have h2 : k' < k + 1 := hmono.lt_iff_lt.1 (by omega)
    have : k' = k := by omega
    subst this; omega

lemma last_iff' (k : ℤ) (i : Fin (cutLen c k)) :
    (i : ℕ) + 1 = cutLen c k ↔ c k + ((i : ℕ) : ℤ) + 1 ∈ Set.range c := by
  have hmono := cut_strictMono c hc
  have hL := cutLen_eq c hc k
  have hi := i.2
  constructor
  · intro h; exact ⟨k + 1, by omega⟩
  · rintro ⟨k', hk'⟩
    have h1 : k < k' := hmono.lt_iff_lt.1 (by omega)
    have h2 : k' ≤ k + 1 := hmono.le_iff_le.1 (by omega)
    have : k' = k + 1 := by omega
    subst this; omega

lemma not_first_and_last (n : ℤ) : ¬ (n ∈ Set.range c ∧ n + 1 ∈ Set.range c) := by
  rintro ⟨⟨k, hk⟩, ⟨k', hk'⟩⟩
  have hmono := cut_strictMono c hc
  have hlt : k < k' := hmono.lt_iff_lt.1 (by omega)
  have := hmono.monotone (show k + 1 ≤ k' by omega)
  have := hc k
  omega

end Cuts

/-! ## 3. The removed bonds -/

section Bonds

variable (c : ℤ → ℤ) (hc : ∀ k, c k + 2 ≤ c (k + 1))

open Classical in
/-- The involution of `ℤ` exchanging `c_k - 1 ↔ c_k` for every `k` (the endpoints of the removed
bonds) and fixing all other sites. -/
def bondPermFun (n : ℤ) : ℤ :=
  if n ∈ Set.range c then n - 1 else if n + 1 ∈ Set.range c then n + 1 else n

include hc in
lemma bondPermFun_involutive : Function.Involutive (bondPermFun c) := by
  intro n
  unfold bondPermFun
  by_cases h1 : n ∈ Set.range c
  · have h2 : n - 1 ∉ Set.range c := fun h =>
      not_first_and_last c hc (n - 1) ⟨h, by simpa using h1⟩
    rw [if_pos h1, if_neg h2, if_pos (by simpa using h1)]; ring
  · rw [if_neg h1]
    by_cases h3 : n + 1 ∈ Set.range c
    · rw [if_pos h3, if_pos h3]; ring
    · rw [if_neg h3, if_neg h1, if_neg h3]

/-- The bond permutation as an equivalence. -/
def bondPerm : ℤ ≃ ℤ := Function.Involutive.toPerm _ (bondPermFun_involutive c hc)

open Classical in
/-- The weights of the removed-bond operator: `b(x_k)` at the sites `c_k` and `c_k - 1`. -/
def bondWeight (b : ℝ → ℝ) (α θ : ℝ) (n : ℤ) : ℂ :=
  if n ∈ Set.range c then ((b (θ + (n - 1) * α) : ℝ) : ℂ)
  else if n + 1 ∈ Set.range c then ((b (θ + n * α) : ℝ) : ℂ) else 0

/-- The removed-bond operator `R = Γ^* F Γ` (l. 1296–1303):
`(R u)(c_k) = b(x_k) u(c_k - 1)`, `(R u)(c_k - 1) = b(x_k) u(c_k)`, `x_k = θ + (c_k - 1) α`. -/
def bondOp (b : ℝ → ℝ) (α θ : ℝ) : AMO.Op ℤ := weightedShift (bondWeight c b α θ) (bondPerm c hc)

lemma bondWeight_bound {b : ℝ → ℝ} {α θ τ : ℝ} (hτ : 0 ≤ τ)
    (hbond : ∀ k, |b (θ + (c k - 1) * α)| ≤ τ) (n : ℤ) : ‖bondWeight c b α θ n‖ ≤ τ := by
  unfold bondWeight
  split_ifs with h1 h2
  · obtain ⟨k, rfl⟩ := h1
    simpa [Complex.norm_real] using hbond k
  · obtain ⟨k, hk⟩ := h2
    have h := hbond k
    have : (c k : ℝ) - 1 = n := by rw [hk]; push_cast; ring
    rw [this] at h
    simpa [Complex.norm_real] using h
  · simpa using hτ

/-- **`‖R‖ = ‖F‖_𝓕 ≤ τ`** (l. 1305): the removed-bond operator has norm at most `sup_k |b(x_k)|`. -/
lemma norm_bondOp_le {b : ℝ → ℝ} {α θ τ : ℝ} (hτ : 0 ≤ τ)
    (hbond : ∀ k, |b (θ + (c k - 1) * α)| ≤ τ) : ‖bondOp c hc b α θ‖ ≤ τ :=
  norm_weightedShift_le hτ (bondWeight_bound c hτ hbond)

lemma bondWeight_bdd {b : ℝ → ℝ} (hb : BddFun b) (α θ : ℝ) : Bdd (bondWeight c b α θ) := by
  obtain ⟨M, hM⟩ := hb
  exact ⟨max M 0, bondWeight_bound c (le_max_right _ _) fun k => (hM _).trans (le_max_left _ _)⟩

lemma bondOp_apply {b : ℝ → ℝ} (hb : BddFun b) (α θ : ℝ) (u : L2 ℤ) (n : ℤ) :
    bondOp c hc b α θ u n = bondWeight c b α θ n * u (bondPermFun c n) := by
  rw [bondOp, weightedShift_apply (bondWeight_bdd c hb α θ)]
  rfl

/-- The boundary projection `P = ⊕_k P_{N_k}` on `ℓ²(ℤ)`. -/
def bdryProjOp : AMO.Op ℤ := blockOp (cutEquiv c hc) fun k => bdryProj (cutLen c k)

include hc in
lemma bdryProj_blockBdd : BlockBdd fun k => bdryProj (cutLen c k) :=
  ⟨1, fun k => (norm_bdryProj (cutLen_ge c hc k)).le⟩

open Classical in
lemma bdryProjOp_apply (u : L2 ℤ) (n : ℤ) :
    bdryProjOp c hc u n = if n ∈ Set.range c ∨ n + 1 ∈ Set.range c then u n else 0 := by
  obtain ⟨⟨k, i⟩, rfl⟩ := (cutEquiv c hc).symm.surjective n
  have hf := first_iff' c hc k i
  have hl := last_iff' c hc k i
  have hex := not_first_and_last c hc (c k + ((i : ℕ) : ℤ))
  rw [bdryProjOp, blockOp_apply (bdryProj_blockBdd c hc), blockFun_symm,
    bdryProj_mulVec (cutLen_ge c hc _)]
  simp only [blockVec, cutEquiv_symm_apply]
  have hL := cutLen_eq c hc k
  have hi := i.2
  by_cases h1 : c k + ((i : ℕ) : ℤ) ∈ Set.range c
  · have h1' : (i : ℕ) = 0 := hf.2 h1
    have h2 : ¬ c k + ((i : ℕ) : ℤ) + 1 ∈ Set.range c := fun h => hex ⟨h1, h⟩
    have h2' : ¬ (i : ℕ) + 1 = cutLen c k := fun h => h2 (hl.1 h)
    simp only [if_pos h1', if_neg h2', add_zero]
    exact (congrArg (fun m : ℤ => (u : ℤ → ℂ) m) (by omega)).trans (if_pos (Or.inl h1)).symm
  · have h1' : ¬ (i : ℕ) = 0 := fun h => h1 (hf.1 h)
    simp only [if_neg h1', zero_add]
    by_cases h2 : c k + ((i : ℕ) : ℤ) + 1 ∈ Set.range c
    · have h2' := hl.2 h2
      simp only [if_pos h2']
      exact (congrArg (fun m : ℤ => (u : ℤ → ℂ) m) (by omega)).trans (if_pos (Or.inr h2)).symm
    · have h3 : ¬ (c k + ((i : ℕ) : ℤ) ∈ Set.range c ∨ c k + ((i : ℕ) : ℤ) + 1 ∈ Set.range c) := by
        tauto
      simp only [if_neg (fun h => h2 (hl.1 h))]
      exact (if_neg h3).symm

/-- **`R = P R P`**: the removed bonds only connect boundary sites of the blocks, i.e.
`Γ^* F Γ` factors through `Γ`. -/
lemma bondOp_eq_proj {b : ℝ → ℝ} (hb : BddFun b) (α θ : ℝ) :
    bondOp c hc b α θ = bdryProjOp c hc * (bondOp c hc b α θ * bdryProjOp c hc) := by
  ext u n
  simp only [mul_apply_eq_comp]
  rw [bdryProjOp_apply, bondOp_apply c hc hb, bondOp_apply c hc hb, bdryProjOp_apply]
  have hex := not_first_and_last c hc
  unfold bondWeight bondPermFun
  by_cases h1 : n ∈ Set.range c
  · have h2 : n - 1 + 1 ∈ Set.range c := by simpa using h1
    simp [h1, h2]
  · by_cases h2 : n + 1 ∈ Set.range c
    · simp [h1, h2]
    · simp [h1, h2]

end Bonds

/-! ## 4. The block decomposition `H = D + Γ^* F Γ` of the Jacobi matrix -/

section Decomposition

variable (v b : ℝ → ℝ) (α θ : ℝ) (c : ℤ → ℤ) (hc : ∀ k, c k + 2 ≤ c (k + 1))

/-- The bond phases `x_k = θ + (c_k - 1) α`: the removed bond between `c_k - 1` and `c_k` is
`b(x_k)`, and the `k`-th block is `B̂_{N_k}(x_k)`. -/
def bondPhase (k : ℤ) : ℝ := θ + (c k - 1) * α

/-- The blocks `B_k = B̂_{N_k}(x_k)`. -/
def blocks (k : ℤ) : Matrix (Fin (cutLen c k)) (Fin (cutLen c k)) ℂ :=
  blockMatrix v b α (cutLen c k) (bondPhase α θ c k)

/-- The block-diagonal part `D = ⊕_k B̂_{N_k}(x_k)` of the Jacobi matrix. -/
def blockDiagOp : AMO.Op ℤ := blockOp (cutEquiv c hc) (blocks v b α θ c)

lemma norm_blockMatrix_le {v b : ℝ → ℝ} {Mv Mb : ℝ} (hv : ∀ x, |v x| ≤ Mv)
    (hb : ∀ x, |b x| ≤ Mb) (N : ℕ) (x : ℝ) : ‖blockMatrix v b α N x‖ ≤ Mv + 2 * Mb := by
  -- write `B̂ = diag + upper + upper^*` and bound each by the sup of its entries
  have hMv : 0 ≤ Mv := (abs_nonneg _).trans (hv 0)
  have hMb : 0 ≤ Mb := (abs_nonneg _).trans (hb 0)
  set d : Fin N → ℂ := fun i => ((v (x + ((i : ℕ) + 1) * α) : ℝ) : ℂ)
  set U : Matrix (Fin N) (Fin N) ℂ := Matrix.of fun i j =>
    if (j : ℕ) = i + 1 then ((b (x + ((i : ℕ) + 1) * α) : ℝ) : ℂ) else 0
  have hsplit : blockMatrix v b α N x = diagonal d + U + Uᴴ := by
    ext i j
    simp only [blockMatrix, of_apply, Matrix.add_apply, diagonal_apply, U, conjTranspose_apply, d]
    by_cases hij : i = j
    · subst hij; simp
    · have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
      by_cases h1 : (j : ℕ) = i + 1
      · have h2 : ¬ (i : ℕ) = j + 1 := by omega
        simp only [if_neg hij, if_pos h1, if_neg h2, star_zero, zero_add, add_zero]
      · by_cases h3 : (i : ℕ) = j + 1
        · simp only [if_neg hij, if_neg h1, if_pos h3, zero_add, Complex.star_def,
            Complex.conj_ofReal]
        · simp only [if_neg hij, if_neg h1, if_neg h3, star_zero, add_zero]
  have hU : ‖U‖ ≤ Mb := by
    -- `U^* U` is diagonal with entries `|b|^2` or `0`
    have hUU : Uᴴ * U = diagonal fun j : Fin N =>
        if h : 0 < (j : ℕ) then ((b (x + (((j : ℕ) - 1 : ℕ) + 1) * α) : ℝ) : ℂ) ^ 2 else 0 := by
      ext j j'
      simp only [mul_apply, conjTranspose_apply, U, of_apply, diagonal_apply]
      by_cases hjj : j = j'
      · subst hjj
        rw [if_pos rfl]
        split_ifs with h0
        · rw [Finset.sum_eq_single (⟨(j : ℕ) - 1, by omega⟩ : Fin N)]
          · simp only [Fin.val_mk]
            rw [if_pos (by omega), Complex.star_def, Complex.conj_ofReal, sq]
          · intro i _ hi
            have : (j : ℕ) ≠ i + 1 := fun h => hi (Fin.ext (by simp; omega))
            simp only [if_neg this, star_zero, zero_mul]
          · simp
        · refine Finset.sum_eq_zero fun i _ => ?_
          have : (j : ℕ) ≠ i + 1 := by omega
          simp only [if_neg this, star_zero, zero_mul]
      · rw [if_neg hjj]
        refine Finset.sum_eq_zero fun i _ => ?_
        have hjj' : (j : ℕ) ≠ j' := fun h => hjj (Fin.ext h)
        by_cases h1 : (j : ℕ) = i + 1
        · have : ¬ (j' : ℕ) = i + 1 := by omega
          simp only [if_neg this, mul_zero]
        · simp only [if_neg h1, star_zero, zero_mul]
    have h := l2_opNorm_conjTranspose_mul_self U
    rw [hUU, l2_opNorm_diagonal] at h
    have hd : ‖fun j : Fin N =>
        if h : 0 < (j : ℕ) then ((b (x + (((j : ℕ) - 1 : ℕ) + 1) * α) : ℝ) : ℂ) ^ 2 else 0‖ ≤
          Mb ^ 2 := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
      split_ifs
      · rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hb _) 2
      · simp; positivity
    nlinarith [norm_nonneg U]
  have hd : ‖diagonal d‖ ≤ Mv := by
    rw [l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg hMv).2 fun i => ?_
    simpa [d, Complex.norm_real] using hv _
  rw [hsplit]
  calc ‖diagonal d + U + Uᴴ‖ ≤ ‖diagonal d‖ + ‖U‖ + ‖Uᴴ‖ := norm_add₃_le
    _ ≤ Mv + Mb + Mb := by rw [l2_opNorm_conjTranspose]; gcongr
    _ = Mv + 2 * Mb := by ring

variable {v b}

lemma blocks_blockBdd (hv : BddFun v) (hb : BddFun b) :
    BlockBdd (blocks v b α θ c) := by
  obtain ⟨Mv, hMv⟩ := hv
  obtain ⟨Mb, hMb⟩ := hb
  exact ⟨Mv + 2 * Mb, fun k => norm_blockMatrix_le α hMv hMb _ _⟩


/-- **The block decomposition** (l. 1293–1303): `H_{v,b,α,θ} = D + Γ^* F Γ`, where
`D = ⊕_k B̂_{N_k}(x_k)` and `Γ^* F Γ = R` is the removed-bond operator. -/
theorem jacobi_eq_add (hv : BddFun v) (hb : BddFun b) :
    jacobi v b α θ = blockDiagOp v b α θ c hc + bondOp c hc b α θ := by
  ext u n
  obtain ⟨⟨k, i⟩, rfl⟩ := (cutEquiv c hc).symm.surjective n
  have hf := first_iff' c hc k i
  have hl := last_iff' c hc k i
  have hex := not_first_and_last c hc (c k + ((i : ℕ) : ℤ))
  rw [_root_.add_apply, lp.coeFn_add, Pi.add_apply, jacobi_apply hv hb,
    blockDiagOp, blockOp_apply (blocks_blockBdd α θ c hv hb), blockFun_symm,
    bondOp_apply c hc hb]
  simp only [cutEquiv_symm_apply]
  rw [blocks, blockMatrix_mulVec]
  simp only [blockVec, cutEquiv_symm_apply, bondWeight, bondPermFun, bondPhase]
  have hL := cutLen_eq c hc k
  have hi := i.2
  have hcast : (((c k + ((i : ℕ) : ℤ) : ℤ)) : ℝ) = (c k : ℝ) + ((i : ℕ) : ℝ) := by push_cast; ring
  have hx1 : θ + ((c k : ℝ) - 1) * α + (((i : ℕ) : ℝ) + 1) * α =
      θ + (((c k + ((i : ℕ) : ℤ) : ℤ)) : ℝ) * α := by rw [hcast]; ring
  rw [hx1]
  by_cases h1 : (i : ℕ) = 0
  · have h1r := hf.1 h1
    have h2 : ¬ c k + ((i : ℕ) : ℤ) + 1 ∈ Set.range c := fun h => hex ⟨h1r, h⟩
    have h2' : (i : ℕ) + 1 < cutLen c k := by
      rcases lt_or_eq_of_le (Nat.succ_le_of_lt hi) with h | h
      · exact h
      · exact absurd (hl.1 h) h2
    simp only [if_pos h1r]
    rw [dif_pos h2', dif_neg (by omega),
      show c k + (((i : ℕ) + 1 : ℕ) : ℤ) = c k + ((i : ℕ) : ℤ) + 1 by push_cast; ring]
    ring
  · have h1r : ¬ c k + ((i : ℕ) : ℤ) ∈ Set.range c := fun h => h1 (hf.2 h)
    have hpos : 0 < (i : ℕ) := Nat.pos_of_ne_zero h1
    have hx2 : θ + ((c k : ℝ) - 1) * α + ((((i : ℕ) - 1 : ℕ) : ℝ) + 1) * α =
        θ + ((((c k + ((i : ℕ) : ℤ) : ℤ)) : ℝ) - 1) * α := by
      rw [hcast, Nat.cast_sub hpos]; push_cast; ring
    simp only [if_neg h1r]
    rw [dif_pos hpos, hx2,
      show c k + (((i : ℕ) - 1 : ℕ) : ℤ) = c k + ((i : ℕ) : ℤ) - 1 by omega]
    by_cases h2 : c k + ((i : ℕ) : ℤ) + 1 ∈ Set.range c
    · have h2' : ¬ (i : ℕ) + 1 < cutLen c k := by have := hl.2 h2; omega
      simp only [if_pos h2]
      rw [dif_neg h2']
      ring
    · have h2' : (i : ℕ) + 1 < cutLen c k := by
        rcases lt_or_eq_of_le (Nat.succ_le_of_lt hi) with h | h
        · exact h
        · exact absurd (hl.1 h) h2
      simp only [if_neg h2]
      rw [dif_pos h2',
        show c k + (((i : ℕ) + 1 : ℕ) : ℤ) = c k + ((i : ℕ) : ℤ) + 1 by push_cast; ring]
      ring

end Decomposition

/-! ## 5. Lemma `lemma-subm` for the Jacobi matrix -/

section Submersion

variable {v b : ℝ → ℝ} {α θ : ℝ} {c : ℤ → ℤ} (hc : ∀ k, c k + 2 ≤ c (k + 1))

lemma not_mem_spectrum_of_isUnit {T : AMO.Op ℤ} {E : ℝ} (h : IsUnit (T - (E : ℂ) • 1)) :
    E ∉ spectrum ℝ T := by
  rw [spectrum.mem_iff, not_not]
  have : algebraMap ℝ (AMO.Op ℤ) E - T = -(T - (E : ℂ) • 1) := by
    rw [Algebra.algebraMap_eq_smul_one, neg_sub]
    congr 1
  rw [this]; exact h.neg

include hc in
/-- **Lemma `lemma-subm`** (l. 1124–1205), for `A = H_{v,b,α,θ} = D + Γ^* F Γ` cut into blocks
`[c_k, c_{k+1})` of lengths `N_k ≥ 2`: if `τ ≥ ‖F‖ = sup_k |b(x_k)|`, then
`σ(H) ⊆ closure ⋃_k ⋃_{V=V^*, ‖V‖ ≤ 2τ} σ(B̂_{N_k}(x_k) + Γ̂_{N_k}^* V Γ̂_{N_k})`. -/
theorem lemma_subm_jacobi (hv : BddFun v) (hb : BddFun b) {τ : ℝ} (hτ : 0 ≤ τ)
    (hbond : ∀ k, |b (bondPhase α θ c k)| ≤ τ) :
    spectrum ℝ (jacobi v b α θ) ⊆
      closure (⋃ k : ℤ, ⋃ V ∈ {V : Matrix (Fin 2) (Fin 2) ℂ | V.IsHermitian ∧ ‖V‖ ≤ 2 * τ},
        spectrum ℝ (blocks v b α θ c k + (bdry (cutLen c k))ᴴ * V * bdry (cutLen c k))) := by
  intro E hE
  by_contra hcl
  set S := ⋃ k : ℤ, ⋃ V ∈ {V : Matrix (Fin 2) (Fin 2) ℂ | V.IsHermitian ∧ ‖V‖ ≤ 2 * τ},
    spectrum ℝ (blocks v b α θ c k + (bdry (cutLen c k))ᴴ * V * bdry (cutLen c k))
  obtain ⟨ε, hε, hεS⟩ : ∃ ε > 0, ∀ s ∈ S, ε ≤ dist E s := by
    rw [Metric.mem_closure_iff] at hcl
    push Not at hcl
    exact hcl
  have hmemS : ∀ k (V : Matrix (Fin 2) (Fin 2) ℂ), V.IsHermitian → ‖V‖ ≤ 2 * τ →
      ∀ s ∈ spectrum ℝ (blocks v b α θ c k + (bdry (cutLen c k))ᴴ * V * bdry (cutLen c k)),
        s ∈ S := by
    intro k V hV hVn s hs
    exact Set.mem_iUnion.2 ⟨k, Set.mem_iUnion₂.2 ⟨V, ⟨hV, hVn⟩, hs⟩⟩
  -- the blocks are Hermitian and `E` is at distance `≥ ε` from their spectra (case `V = 0`)
  have hBh : ∀ k, (blocks v b α θ c k).IsHermitian := fun k => blockMatrix_isHermitian _ _ _ _ _
  have hdist : ∀ k i, ε ≤ |(hBh k).eigenvalues i - E| := by
    intro k i
    have hs := (hBh k).eigenvalues_mem_spectrum_real i
    have := hεS _ (hmemS k 0 isHermitian_zero (by simp; positivity) _ (by simpa using hs))
    rwa [Real.dist_eq, abs_sub_comm] at this
  have hres := fun k => (hBh k).resolvent_spec hε (hdist k)
  set e := cutEquiv c hc
  set Rk : ∀ k, Matrix (Fin (cutLen c k)) (Fin (cutLen c k)) ℂ :=
    fun k => (blocks v b α θ c k - (E : ℂ) • 1)⁻¹
  have hRbdd : BlockBdd Rk := ⟨ε⁻¹, fun k => (hres k).2⟩
  have hBbdd := blocks_blockBdd α θ c hv hb
  have hBEbdd : BlockBdd fun k => blocks v b α θ c k - (E : ℂ) • 1 := by
    obtain ⟨C, hC⟩ := hBbdd
    refine ⟨C + ‖(E : ℂ)‖, fun k => (norm_sub_le _ _).trans (add_le_add (hC k) ?_)⟩
    rw [norm_smul]
    exact mul_le_of_le_one_right (norm_nonneg _) (norm_one_matrix_le _)
  -- `D - E` is invertible, with inverse `⊕ (B_k - E)⁻¹`
  set D' := blockDiagOp v b α θ c hc - (E : ℂ) • 1
  set Dinv := blockOp e Rk
  have hD' : D' = blockOp e fun k => blocks v b α θ c k - (E : ℂ) • 1 :=
    (blockOp_sub_smul hBbdd _).symm
  have h2 : Dinv * D' = 1 := by
    rw [hD', ← blockOp_mul hRbdd hBEbdd, ← blockOp_one (e := e)]
    congr 1; funext k
    exact nonsing_inv_mul _ (hres k).1
  have h1 : D' * Dinv = 1 := by
    rw [hD', ← blockOp_mul hBEbdd hRbdd, ← blockOp_one (e := e)]
    congr 1; funext k
    exact mul_nonsing_inv _ (hres k).1
  -- the boundary resolvent `P (D-E)⁻¹ P = ⊕ Γ̂^* G_k(E) Γ̂`
  set P := bdryProjOp c hc
  have hPbdd := bdryProj_blockBdd c hc
  have hPDP : P.comp (Dinv.comp P) =
      blockOp e fun k => bdryProj (cutLen c k) * (Rk k * bdryProj (cutLen c k)) := by
    rw [blockOp_mul hPbdd (hRbdd.mul hPbdd), blockOp_mul hRbdd hPbdd]
    rfl
  have hGbound : ‖P.comp (Dinv.comp P)‖ * ‖bondOp c hc b α θ‖ < 1 := by
    rcases eq_or_lt_of_le hτ with h0 | hτpos
    · have : ‖bondOp c hc b α θ‖ = 0 :=
        le_antisymm ((norm_bondOp_le c hc hτ hbond).trans h0.symm.le) (norm_nonneg _)
      rw [this, mul_zero]; exact zero_lt_one
    -- for every block, `‖G_k(E)‖ ≤ (2τ)⁻¹`
    have hGk : ∀ k, ‖bdryProj (cutLen c k) * (Rk k * bdryProj (cutLen c k))‖ ≤ (2 * τ)⁻¹ := by
      intro k
      have hN := cutLen_ge c hc k
      have hG := norm_bdryResolvent_le hN (hBh k) hτpos (hres k).1 fun V hV hVn hEV => by
        have := hεS _ (hmemS k V hV hVn E hEV)
        rw [dist_self] at this; linarith
      have : bdryProj (cutLen c k) * (Rk k * bdryProj (cutLen c k)) =
          (bdry (cutLen c k))ᴴ * bdryResolvent (blocks v b α θ c k) E * bdry (cutLen c k) := by
        simp only [bdryProj, bdryResolvent, Rk, Matrix.mul_assoc]
      rw [this]
      calc _ ≤ ‖(bdry (cutLen c k))ᴴ * bdryResolvent (blocks v b α θ c k) E‖ *
            ‖bdry (cutLen c k)‖ := l2_opNorm_mul _ _
        _ ≤ ‖(bdry (cutLen c k))ᴴ‖ * ‖bdryResolvent (blocks v b α θ c k) E‖ *
            ‖bdry (cutLen c k)‖ := by gcongr; exact l2_opNorm_mul _ _
        _ ≤ (2 * τ)⁻¹ := by rw [norm_bdry hN, norm_conjTranspose_bdry hN]; simpa using hG
    rw [hPDP]
    calc _ ≤ (2 * τ)⁻¹ * τ := mul_le_mul (norm_blockOp_le (by positivity) hGk)
          (norm_bondOp_le c hc hτ hbond) (norm_nonneg _) (by positivity)
      _ = 1 / 2 := by field_simp
      _ < 1 := by norm_num
  have hU := isUnit_add_boundary_of_norm_lt D' Dinv h2 h1 P (bondOp c hc b α θ) P hGbound
  have hEq : D' + P.comp ((bondOp c hc b α θ).comp P) = jacobi v b α θ - (E : ℂ) • 1 := by
    rw [jacobi_eq_add α θ c hc hv hb]
    have := bondOp_eq_proj c hc hb α θ
    simp only [ContinuousLinearMap.mul_def] at this
    rw [← this]
    simp only [D']; abel
  rw [hEq] at hU
  exact not_mem_spectrum_of_isUnit hU hE

end Submersion

/-! ## 6. The mean value bound and Proposition `prop-blocks` -/

/-- **Mean value bound** (l. 1314–1316): if `|b'| ≤ C` then `|b(x) - b(y)| ≤ C |x - y|`. -/
theorem abs_sub_le_of_deriv_le {f : ℝ → ℝ} (hf : Differentiable ℝ f) {C : ℝ}
    (hC : ∀ x, |deriv f x| ≤ C) (x y : ℝ) : |f x - f y| ≤ C * |x - y| := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ) (fun z _ => hf z)
    (fun z _ => by simpa using hC z) convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa [Real.norm_eq_abs] using this

/-- The interval `J_n = [-|δ_{n-1}|, |δ_{n-1}|]` of (`Jn`, l. 1253), `δ_{n-1} = q_{n-1} α - p_{n-1}`
(`= q_{n-1}(α - p_{n-1}/q_{n-1})`). -/
def Jn (α : ℝ) (n : ℕ) : Set ℝ :=
  Set.Icc (-|q α (n - 1) * α - p α (n - 1)|) (|q α (n - 1) * α - p α (n - 1)|)

/-- The length `|J_n| = 2 |δ_{n-1}|`. -/
def JnLen (α : ℝ) (n : ℕ) : ℝ := 2 * |q α (n - 1) * α - p α (n - 1)|

/-- **`|b(x_k)| ≤ C(b) |J_n|`** (l. 1314–1316): if `x ≡ z (mod 1)` with `z ∈ J_n`, `|b'| ≤ C`, and
`b` is `1`-periodic with `b(0) = 0` or `2`-periodic with `b(0) = b(1) = 0`, then
`|b(x)| ≤ C |J_n|`. -/
theorem abs_bond_le {b : ℝ → ℝ} (hbd : Differentiable ℝ b) {C : ℝ} (hC : ∀ x, |deriv b x| ≤ C)
    (hb0 : (Function.Periodic b 1 ∧ b 0 = 0) ∨ (Function.Periodic b 2 ∧ b 0 = 0 ∧ b 1 = 0))
    {α : ℝ} {n : ℕ} {x : ℝ} (hx : ∃ m : ℤ, x - m ∈ Jn α n) : |b x| ≤ C * JnLen α n := by
  obtain ⟨m, hm⟩ := hx
  set z := x - m
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hz : |z| ≤ |q α (n - 1) * α - p α (n - 1)| := abs_le.2 ⟨hm.1, hm.2⟩
  have key : ∀ y0 : ℝ, b y0 = 0 → |b (z + y0)| ≤ C * JnLen α n := by
    intro y0 hy0
    have := abs_sub_le_of_deriv_le hbd hC (z + y0) y0
    rw [hy0, sub_zero, add_sub_cancel_right] at this
    refine this.trans (mul_le_mul_of_nonneg_left ?_ hC0)
    unfold JnLen; linarith [abs_nonneg (q α (n - 1) * α - p α (n - 1))]
  have hxz : x = z + m := by simp [z]
  rcases hb0 with ⟨hper, h0⟩ | ⟨hper, h0, h1⟩
  · have : b x = b (z + 0) := by rw [hxz, add_zero]; simpa using (hper.int_mul m) z
    rw [this]; exact key 0 h0
  · obtain ⟨j, hj | hj⟩ := Int.even_or_odd' m
    · have : b x = b (z + 0) := by
        rw [hxz, hj, add_zero]; push_cast
        simpa [mul_comm] using (hper.int_mul j) z
      rw [this]; exact key 0 h0
    · have : b x = b (z + 1) := by
        rw [hxz, hj]; push_cast
        have := (hper.int_mul j) (z + 1)
        rw [← this]; congr 1; ring
      rw [this]; exact key 1 h1

/-- **Proposition `prop-blocks`** (l. 1318–1327).  Let `v, b` be bounded, `b` differentiable with
`|b'| ≤ C`, and `b` either `1`-periodic with `b(0) = 0` or `2`-periodic with `b(0) = b(1) = 0`.
Suppose the cut points `c_k` (the return times of Lemma `lemma-rt`, taken here as hypotheses)
have gaps `N_k = c_{k+1} - c_k ∈ {q_n, q_{n-1}}`, `N_k ≥ 2`, and bond phases
`x_k = θ + (c_k - 1) α ∈ J_n (mod 1)`.  Then
`σ(H_{v,b,α,θ}) ⊆ closure ⋃_{N ∈ {q_n, q_{n-1}}} ⋃_{x ∈ J_n + ℤ} ⋃_{V = V^*, ‖V‖ ≤ 2 C |J_n|}
  σ(B̂_N(x) + Γ̂_N^* V Γ̂_N)`.
(For `2`-periodic `b`, `x` ranges over `J_n + ℤ` rather than `J_n`; see the file header.) -/
theorem prop_blocks {v b : ℝ → ℝ} (hv : BddFun v) (hb : BddFun b) (hbd : Differentiable ℝ b)
    {C : ℝ} (hC : ∀ x, |deriv b x| ≤ C)
    (hb0 : (Function.Periodic b 1 ∧ b 0 = 0) ∨ (Function.Periodic b 2 ∧ b 0 = 0 ∧ b 1 = 0))
    (α θ : ℝ) (n : ℕ) (c : ℤ → ℤ) (hc : ∀ k, c k + 2 ≤ c (k + 1))
    (hgap : ∀ k, ((c (k + 1) - c k : ℤ) : ℝ) = q α n ∨ ((c (k + 1) - c k : ℤ) : ℝ) = q α (n - 1))
    (hx : ∀ k, ∃ m : ℤ, θ + (c k - 1) * α - m ∈ Jn α n) :
    spectrum ℝ (jacobi v b α θ) ⊆
      closure (⋃ N ∈ {N : ℕ | (N : ℝ) = q α n ∨ (N : ℝ) = q α (n - 1)},
        ⋃ x ∈ {x : ℝ | ∃ m : ℤ, x - m ∈ Jn α n},
        ⋃ V ∈ {V : Matrix (Fin 2) (Fin 2) ℂ | V.IsHermitian ∧ ‖V‖ ≤ 2 * (C * JnLen α n)},
          spectrum ℝ (blockMatrix v b α N x + (bdry N)ᴴ * V * bdry N)) := by
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  have hτ : 0 ≤ C * JnLen α n := mul_nonneg hC0 (by unfold JnLen; positivity)
  refine (lemma_subm_jacobi hc hv hb hτ fun k => abs_bond_le hbd hC hb0 (hx k)).trans
    (closure_mono ?_)
  refine Set.iUnion_subset fun k => ?_
  refine Set.subset_iUnion₂_of_subset (cutLen c k) ?_ ?_
  · have := cutLen_eq c hc k
    have h := hgap k
    rw [← this] at h
    simpa using h
  refine Set.subset_iUnion₂_of_subset (bondPhase α θ c k) (hx k) ?_
  exact subset_rfl

/-- `B̂_N(x + m) = B̂_N(x)` for `1`-periodic `v, b` and `m ∈ ℤ`. -/
lemma blockMatrix_add_int {v b : ℝ → ℝ} (hv : Function.Periodic v 1) (hb : Function.Periodic b 1)
    (α : ℝ) (N : ℕ) (x : ℝ) (m : ℤ) : blockMatrix v b α N (x + m) = blockMatrix v b α N x := by
  have hv' : ∀ y, v (y + m) = v y := fun y => by simpa using (hv.int_mul m) y
  have hb' : ∀ y, b (y + m) = b y := fun y => by simpa using (hb.int_mul m) y
  ext i j
  simp only [blockMatrix, of_apply]
  rw [show x + m + ((i : ℕ) + 1) * α = x + ((i : ℕ) + 1) * α + m by ring,
    show x + m + ((j : ℕ) + 1) * α = x + ((j : ℕ) + 1) * α + m by ring, hv', hb', hb']

/-- **Proposition `prop-blocks`, literal form** for `1`-periodic `v` and `b` with `b(0) = 0`:
`σ(H_{v,b,α,θ}) ⊆ closure ⋃_{ν=1,2} ⋃_{x ∈ J_n} ⋃_{V=V^*, ‖V‖ ≤ 2C(b)|J_n|}
  σ(B̂_{N'_ν}(x) + Γ̂_{N'_ν}^* V Γ̂_{N'_ν})`, `N'_1 = q_n`, `N'_2 = q_{n-1}`. -/
theorem prop_blocks_periodic {v b : ℝ → ℝ} (hv : BddFun v) (hb : BddFun b)
    (hvp : Function.Periodic v 1) (hbp : Function.Periodic b 1) (hb0 : b 0 = 0)
    (hbd : Differentiable ℝ b) {C : ℝ} (hC : ∀ x, |deriv b x| ≤ C)
    (α θ : ℝ) (n : ℕ) (c : ℤ → ℤ) (hc : ∀ k, c k + 2 ≤ c (k + 1))
    (hgap : ∀ k, ((c (k + 1) - c k : ℤ) : ℝ) = q α n ∨ ((c (k + 1) - c k : ℤ) : ℝ) = q α (n - 1))
    (hx : ∀ k, ∃ m : ℤ, θ + (c k - 1) * α - m ∈ Jn α n) :
    spectrum ℝ (jacobi v b α θ) ⊆
      closure (⋃ N ∈ {N : ℕ | (N : ℝ) = q α n ∨ (N : ℝ) = q α (n - 1)},
        ⋃ x ∈ Jn α n,
        ⋃ V ∈ {V : Matrix (Fin 2) (Fin 2) ℂ | V.IsHermitian ∧ ‖V‖ ≤ 2 * (C * JnLen α n)},
          spectrum ℝ (blockMatrix v b α N x + (bdry N)ᴴ * V * bdry N)) := by
  refine (prop_blocks hv hb hbd hC (Or.inl ⟨hbp, hb0⟩) α θ n c hc hgap hx).trans
    (closure_mono ?_)
  refine Set.iUnion₂_subset fun N hN => Set.subset_iUnion₂_of_subset N hN ?_
  refine Set.iUnion₂_subset fun x hx' => ?_
  obtain ⟨m, hm⟩ := hx'
  refine Set.subset_iUnion₂_of_subset (x - m) hm ?_
  have : blockMatrix v b α N x = blockMatrix v b α N (x - m) := by
    rw [← blockMatrix_add_int hvp hbp α N (x - m) m, sub_add_cancel]
  rw [this]

end CAH
