/-
Copyright (c) 2026. Formalization of
  S. Becker, S. Jitomirskaya, I. Krasovsky, "Critical almost Mathieu operator: hidden
  singularity, gap continuity, and the Hausdorff dimension of the spectrum"
  (arXiv:1909.04429v2).

# Last's bound `q|σ(M_{p/q})| ≤ C` and the second proof of Theorem 1.2

Paper reference (`Arxiv_version-5.tex`): eq. (1.6) `bound` (l. 354–358) and §6, l. 1062–1064
("Since for the almost Mathieu operator `|σ(M_{2p_n/q_n})| = |σ(M_{0,2 sin 2π·,p_n/q_n})| ≤ C/q_n`,
we also obtain a proof of Theorem 1.2").  In `RationalBands.lean` the bound was the hypothesis
`hsmall` of `volume_eq_zero_of_small_bands'`; here it is proved.

Literature: [L] Y. Last, *Zero measure spectrum for the almost Mathieu operator*,
Commun. Math. Phys. 164 (1994) 421–432 (`C = 8e`); [JKK] S. Jitomirskaya, L. Konstantinov,
I. Krasovsky, *On the spectrum of critical almost Mathieu operators in the rational case*,
J. Spectral Theory 12 (2022) 11–21, arXiv:2007.01005 (`C = 4π`, via the chiral gauge);
[BHJ] S. Becker, R. Han, S. Jitomirskaya, Invent. Math. 218 (2019) (Lidskii argument).

## Route (that of [JKK], with a coarser constant)
Let `Q` be odd, `β = p/Q`, `gcd(p,Q) = 1`, `ω = e(β)`, `a_r(θ) = 2 sin 2π(θ + rβ)`.

1. *Chambers-type formula* (`chambers_odd`, `chambers_bloch`).  With `s = e(k/Q+θ)`,
   `t = e(k/Q-θ)` the gauge-transformed Bloch matrix `Gst` has entries `-i(sω^r - tω^{-r})`,
   `-i(t^{-1}ω^c - s^{-1}ω^{-c})`.  The polynomial `P = det(ST(E - G)) ∈ ℂ[S,T,E]` has all
   monomials in the diamond `|m₀-Q| + |m₁-Q| + m₂ ≤ Q` (`good_det`), and is invariant under
   `(S,T) ↦ (ω⁻¹S, ω⁻¹T)` (conjugation by `diag(ω^r)`) and `(S,T) ↦ (ωS, ω⁻¹T)` (cyclic
   relabelling).  Hence (`support_cases`) only `S^QT^QE^j`, `S^{2Q}T^Q`, `T^Q`, `S^QT^{2Q}`, `S^Q`
   occur, i.e. `det(E - Bloch(θ,k)) = Φ(E) + c₁e(k+Qθ) + c₂e(-k-Qθ) + c₃e(k-Qθ) + c₄e(-k+Qθ)`.
   This replaces the trigonometric-polynomial argument of [JKK, Lemma 2]; the explicit values
   of the `cᵢ` are not needed.
2. *Alignment* (`align`): the set of values of the `θ,k`-dependent part over all `(θ,k)` is
   already attained on one fibre `θ = θ*` (and on its shifts `θ* + nβ`), so
   `σ(M̂_β) = ⋃_k σ(Bloch(θ₁,k))` for a suitable `θ₁` (cf. [JKK, (16)–(17)]).
3. *One fibre* (`fibre_cover`): the Bloch matrix is a `k`-independent matrix plus a boundary
   coupling `Γ^*V₂Γ`, `‖V₂‖ = |a_{Q-1}(θ₁)|`; `Flow.cover_bdry` (Lidskii) gives `Q` intervals of
   total length `≤ 4|a_{Q-1}(θ₁)|` ([JKK, (23)–(24)]); `θ₁` is chosen so that this bond is
   `≤ 4π/Q` (`exists_small_bond`).
4. `volume_sigmaM_chiral_le_of_odd`: `|σ(M̂_{p/Q})| ≤ 16π/Q` for `Q` odd; with the chiral-gauge
   inclusion `σ(M_α) ⊆ σ(M̂_{α/2})` this gives **Last's bound** `volume_sigmaAMO_le_of_odd`:
   `|σ(M_{p/q})| ≤ 16π/q` for coprime `p, q`, `q` odd.
5. *Even period* `Q = 2N` (Part D–E, `volume_sigmaM_chiral_le_of_even`): here the support of
   `P` also contains `S^{Q±N}T^{Q±N}`, so only the `E`-dependence is taken from the polynomial
   argument (`chambers_E`); `det(Bloch)` is computed explicitly from the bipartite block
   structure (`det_Bc_even`: `(-1)^N |A_e + (-1)^{N-1}e(k)A_o|²`, `A_e = ∏a_{2i}`, `A_o = ∏a_{2i+1}`)
   and the cyclotomic identity gives `|A_e|, |A_o|` (`abs_AEr_odd`, `abs_AEr_even`).  Together:
   `volume_sigmaM_chiral_le` (`|σ(M̂_{p/Q})| ≤ 16π/Q`, all `Q ≥ 1`) and **Last's bound for all
   denominators** `volume_sigmaAMO_le`: `|σ(M_{p/q})| ≤ 16π/q` for coprime `p, q`, `q ≥ 1`.
6. `volume_sigmaAMO_eq_zero'` (**Theorem 1.2, second proof**): Theorem 1.3
   (`measure_convergence'`) for `v = 0`, `b = 2 sin 2π·` along the convergents of `α/2`; one of
   any two consecutive `q_n` is odd, so the limit is `0`.

No `sorry`, no axioms beyond `propext`, `Classical.choice`, `Quot.sound`.
-/
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic
import CriticalAMOHausdorff.RationalBands
import CriticalAMOHausdorff.ChiralSpectrum
import CriticalAMOHausdorff.EigenvalueFlow

set_option autoImplicit false

noncomputable section

open MvPolynomial Matrix Complex
open scoped Pointwise

namespace CAH
namespace LastBound

/-! ### Polynomial bookkeeping in `ℂ[S, T, E]` -/

/-- Polynomials in the three variables `S = X 0`, `T = X 1`, `E = X 2`. -/
abbrev R3 := MvPolynomial (Fin 3) ℂ

/-- The exponent vector of `S^a T^b E^e`. -/
def ev (a b e : ℕ) : Fin 3 →₀ ℕ := Finsupp.single 0 a + Finsupp.single 1 b + Finsupp.single 2 e

@[simp] lemma ev_zero (a b e : ℕ) : ev a b e 0 = a := by simp [ev]
@[simp] lemma ev_one (a b e : ℕ) : ev a b e 1 = b := by simp [ev]
@[simp] lemma ev_two (a b e : ℕ) : ev a b e 2 = e := by simp [ev]

/-- The monomial `x S^a T^b E^e`. -/
def mono (a b e : ℕ) (x : ℂ) : R3 := monomial (ev a b e) x

/-- `f` has all its monomials `S^{m₀} T^{m₁} E^{m₂}` in the "diamond"
`|m₀ - n| + |m₁ - n| + m₂ ≤ n`. -/
def Good (n : ℕ) (f : R3) : Prop :=
  ∀ m ∈ f.support, |(m 0 : ℤ) - n| + |(m 1 : ℤ) - n| + (m 2 : ℤ) ≤ n

lemma good_zero (n : ℕ) : Good n 0 := by simp [Good]

lemma good_add {n : ℕ} {f g : R3} (hf : Good n f) (hg : Good n g) : Good n (f + g) := by
  intro m hm
  rcases Finset.mem_union.1 (support_add hm) with h | h
  · exact hf m h
  · exact hg m h

lemma good_neg {n : ℕ} {f : R3} (hf : Good n f) : Good n (-f) := by
  intro m hm
  rw [support_neg] at hm
  exact hf m hm

lemma good_sub {n : ℕ} {f g : R3} (hf : Good n f) (hg : Good n g) : Good n (f - g) := by
  rw [sub_eq_add_neg]; exact good_add hf (good_neg hg)

lemma good_units_smul {n : ℕ} {f : R3} (hf : Good n f) (u : ℤˣ) : Good n (u • f) := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · simpa using hf
  · rw [Units.neg_smul, one_smul]; exact good_neg hf

lemma good_mul {n n' : ℕ} {f g : R3} (hf : Good n f) (hg : Good n' g) :
    Good (n + n') (f * g) := by
  classical
  intro m hm
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (support_mul f g hm)
  have h1 := hf a ha
  have h2 := hg b hb
  simp only [Finsupp.coe_add, Pi.add_apply]
  push_cast
  have e0 : |((a 0 : ℤ) + b 0) - (n + n')| ≤ |(a 0 : ℤ) - n| + |(b 0 : ℤ) - n'| := by
    rw [show ((a 0 : ℤ) + b 0) - (n + n') = ((a 0 : ℤ) - n) + ((b 0 : ℤ) - n') by ring]
    exact abs_add_le _ _
  have e1 : |((a 1 : ℤ) + b 1) - (n + n')| ≤ |(a 1 : ℤ) - n| + |(b 1 : ℤ) - n'| := by
    rw [show ((a 1 : ℤ) + b 1) - (n + n') = ((a 1 : ℤ) - n) + ((b 1 : ℤ) - n') by ring]
    exact abs_add_le _ _
  linarith

lemma good_one : Good 0 (1 : R3) := by
  intro m hm
  rw [show (1 : R3) = monomial 0 1 from rfl] at hm
  have := support_monomial_subset hm
  rw [Finset.mem_singleton] at this
  subst this
  simp

lemma good_prod {ι : Type*} (s : Finset ι) (f : ι → R3) (hf : ∀ i ∈ s, Good 1 (f i)) :
    Good s.card (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using good_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, add_comm]
    exact good_mul (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma good_sum {ι : Type*} (s : Finset ι) {n : ℕ} (f : ι → R3) (hf : ∀ i ∈ s, Good n (f i)) :
    Good n (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using good_zero n
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact good_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

lemma good_mono {n a b e : ℕ} (x : ℂ)
    (h : |(a : ℤ) - n| + |(b : ℤ) - n| + (e : ℤ) ≤ n) : Good n (mono a b e x) := by
  intro m hm
  have := support_monomial_subset hm
  rw [Finset.mem_singleton] at this
  subst this
  simpa using h

lemma good_ite {n : ℕ} {P : Prop} [Decidable P] {f : R3} (hf : Good n f) :
    Good n (if P then f else 0) := by
  split_ifs
  · exact hf
  · exact good_zero n

/-- The determinant of a matrix with entries in the diamond of size `1` lies in the diamond of
size `Q`. -/
lemma good_det {Q : ℕ} (M : Matrix (Fin Q) (Fin Q) R3) (hM : ∀ r c, Good 1 (M r c)) :
    Good Q M.det := by
  rw [Matrix.det_apply]
  refine good_sum _ _ fun σ _ => good_units_smul ?_ _
  have := good_prod Finset.univ (fun i => M (σ i) i) (fun i _ => hM _ _)
  simpa using this

/-! ### Scaling the variables -/

lemma monomial_eq_C_mul_prod (m : Fin 3 →₀ ℕ) (x : ℂ) :
    (monomial m x : R3) = C x * ∏ i, X i ^ m i := by
  rw [← Finsupp.prod_fintype m (fun i k => (X i : R3) ^ k) (fun i => pow_zero _),
    ← monomial_eq]

/-- Substituting `X i ↦ c i • X i` multiplies the coefficient of `X^m` by `c^m`. -/
lemma coeff_aeval_scale (c : Fin 3 → ℂ) (f : R3) (m : Fin 3 →₀ ℕ) :
    (aeval (fun i => C (c i) * X i) f).coeff m = (∏ i, c i ^ m i) * f.coeff m := by
  classical
  induction f using MvPolynomial.induction_on' with
  | monomial n x =>
    have : aeval (fun i => C (c i) * X i) (monomial n x : R3) =
        monomial n (x * ∏ i, c i ^ n i) := by
      rw [monomial_eq_C_mul_prod, map_mul, aeval_C, map_prod, monomial_eq_C_mul_prod,
        algebraMap_eq]
      simp_rw [map_pow, aeval_X, mul_pow]
      rw [Finset.prod_mul_distrib, C_mul]
      simp only [← map_pow, ← map_prod]
      ring
    rw [this, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h; ring
    · simp
  | add f g hf hg => simp only [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hf, hg, mul_add]

lemma aeval_scale_mono (c : Fin 3 → ℂ) (a b e : ℕ) (x : ℂ) :
    aeval (fun i => C (c i) * X i) (mono a b e x) = mono a b e (x * (c 0 ^ a * c 1 ^ b * c 2 ^ e)) := by
  classical
  ext m
  rw [coeff_aeval_scale, mono, mono, coeff_monomial, coeff_monomial]
  split_ifs with h
  · subst h; simp [Fin.prod_univ_three]; ring
  · simp

lemma eval_mono (x : Fin 3 → ℂ) (a b e : ℕ) (y : ℂ) :
    eval x (mono a b e y) = y * (x 0 ^ a * x 1 ^ b * x 2 ^ e) := by
  rw [mono, monomial_eq_C_mul_prod]
  simp [Fin.prod_univ_three]

lemma C_mul_mono (z : ℂ) (a b e : ℕ) (x : ℂ) : C z * mono a b e x = mono a b e (z * x) := by
  rw [mono, mono, C_mul_monomial]

/-! ### Roots of unity -/

lemma pow_mod_eq {z : ℂ} {Q : ℕ} (hz : z ^ Q = 1) (n : ℕ) : z ^ (n % Q) = z ^ n := by
  conv_rhs => rw [← Nat.mod_add_div n Q, pow_add, pow_mul, hz, one_pow, mul_one]

variable {Q : ℕ} [NeZero Q]

lemma val_add_one (r : Fin Q) : ((r + 1 : Fin Q) : ℕ) = ((r : ℕ) + 1) % Q := by
  rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]

lemma pow_val_add_one {z : ℂ} (hz : z ^ Q = 1) (r : Fin Q) :
    z ^ ((r + 1 : Fin Q) : ℕ) = z ^ (r : ℕ) * z := by
  rw [val_add_one, pow_mod_eq hz, pow_succ]

/-! ### The polynomial matrix `M = ST (E - G)` -/

variable (Q) in
/-- `M(r,c) = [r=c] STE + [c=r+1] i(S²Tω^r - ST²ω^{-r}) + [r=c+1] i(Sω^c - Tω^{-c})`. -/
def Mp (ω : ℂ) : Matrix (Fin Q) (Fin Q) R3 := fun r c =>
  (if r = c then mono 1 1 1 1 else 0) +
  (if c = r + 1 then mono 2 1 0 (I * ω ^ (r : ℕ)) - mono 1 2 0 (I * ω⁻¹ ^ (r : ℕ)) else 0) +
  (if r = c + 1 then mono 1 0 0 (I * ω ^ (c : ℕ)) - mono 0 1 0 (I * ω⁻¹ ^ (c : ℕ)) else 0)

lemma good_Mp (ω : ℂ) (r c : Fin Q) : Good 1 (Mp Q ω r c) := by
  unfold Mp
  refine good_add (good_add (good_ite (good_mono _ (by norm_num))) (good_ite (good_sub
    (good_mono _ (by norm_num)) (good_mono _ (by norm_num))))) (good_ite (good_sub
    (good_mono _ (by norm_num)) (good_mono _ (by norm_num))))

/-- The scaling `S ↦ ω⁻¹S, T ↦ ω⁻¹T`. -/
def sc1 (ω : ℂ) : Fin 3 → ℂ := ![ω⁻¹, ω⁻¹, 1]
/-- The scaling `S ↦ ωS, T ↦ ω⁻¹T`. -/
def sc2 (ω : ℂ) : Fin 3 → ℂ := ![ω, ω⁻¹, 1]

lemma Mp_conj_diag {ω : ℂ} (hω0 : ω ≠ 0) (hω : ω ^ Q = 1) (r c : Fin Q) :
    C (ω ^ (r : ℕ)) * (C (ω⁻¹ ^ (c : ℕ)) * Mp Q ω r c) =
      C (ω ^ 2) * aeval (fun i => C (sc1 ω i) * X i) (Mp Q ω r c) := by
  have hωi : ω⁻¹ ^ Q = 1 := by rw [inv_pow, hω, inv_one]
  simp only [Mp, mul_add, map_add]
  congr 1
  congr 1
  · split_ifs with h
    · subst h
      rw [aeval_scale_mono, C_mul_mono, C_mul_mono, C_mul_mono]
      congr 1
      simp only [sc1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, inv_pow]
      field_simp
    · simp
  · split_ifs with h
    · subst h
      rw [map_sub, aeval_scale_mono, aeval_scale_mono, mul_sub, mul_sub, mul_sub,
        C_mul_mono, C_mul_mono, C_mul_mono, C_mul_mono, C_mul_mono, C_mul_mono,
        pow_val_add_one hωi]
      simp only [sc1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, inv_pow]
      congr 1 <;> congr 1 <;> field_simp <;> ring
    · simp
  · split_ifs with h
    · subst h
      rw [map_sub, aeval_scale_mono, aeval_scale_mono, mul_sub, mul_sub, mul_sub,
        C_mul_mono, C_mul_mono, C_mul_mono, C_mul_mono, C_mul_mono, C_mul_mono,
        pow_val_add_one hω]
      simp only [sc1, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, inv_pow]
      congr 1 <;> congr 1 <;> field_simp <;> ring
    · simp

lemma Mp_shift {ω : ℂ} (hω0 : ω ≠ 0) (hω : ω ^ Q = 1) (r c : Fin Q) :
    Mp Q ω (r + 1) (c + 1) = aeval (fun i => C (sc2 ω i) * X i) (Mp Q ω r c) := by
  have hωi : ω⁻¹ ^ Q = 1 := by rw [inv_pow, hω, inv_one]
  simp only [Mp, map_add, add_left_inj]
  congr 1
  congr 1
  · split_ifs with h
    · rw [aeval_scale_mono]
      congr 1
      simp [sc2, hω0]
    · simp
  · split_ifs with h
    · rw [map_sub, aeval_scale_mono, aeval_scale_mono, pow_val_add_one hω, pow_val_add_one hωi]
      simp only [sc2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, inv_pow]
      congr 1 <;> congr 1 <;> field_simp <;> ring
    · simp
  · split_ifs with h
    · rw [map_sub, aeval_scale_mono, aeval_scale_mono, pow_val_add_one hω, pow_val_add_one hωi]
      simp only [sc2, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons, inv_pow]
      congr 1 <;> congr 1 <;> field_simp <;> ring
    · simp

end LastBound
end CAH

namespace CAH
namespace LastBound

open MvPolynomial Matrix Complex

variable {Q : ℕ} [NeZero Q]

variable (Q) in
/-- `P = det M ∈ ℂ[S,T,E]`. -/
def Pdet (ω : ℂ) : R3 := (Mp Q ω).det

lemma good_Pdet (ω : ℂ) : Good Q (Pdet Q ω) := good_det _ (good_Mp ω)

lemma aeval_det (c : Fin 3 → ℂ) (M : Matrix (Fin Q) (Fin Q) R3) :
    aeval (fun i => C (c i) * X i) M.det = (M.map (aeval (fun i => C (c i) * X i))).det := by
  rw [AlgHom.map_det]; rfl

lemma Pdet_sc1 {ω : ℂ} (hω0 : ω ≠ 0) (hω : ω ^ Q = 1) :
    aeval (fun i => C (sc1 ω i) * X i) (Pdet Q ω) = Pdet Q ω := by
  have h1 := det_mul_column (fun r : Fin Q => C (ω ^ (r : ℕ)))
    (of fun (r c : Fin Q) => C (ω⁻¹ ^ (c : ℕ)) * Mp Q ω r c)
  have h2 := det_mul_row (fun c : Fin Q => C (ω⁻¹ ^ (c : ℕ))) (Mp Q ω)
  simp only [of_apply] at h1
  have hprod : (∏ i : Fin Q, C (ω ^ (i : ℕ))) * (∏ i : Fin Q, C (ω⁻¹ ^ (i : ℕ))) = (1 : R3) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [← C_mul, ← mul_pow, mul_inv_cancel₀ hω0, one_pow, C_1]
  have hM : (of fun (r c : Fin Q) => C (ω ^ (r : ℕ)) * (C (ω⁻¹ ^ (c : ℕ)) * Mp Q ω r c)) =
      (C (ω ^ 2) : R3) • (Mp Q ω).map (aeval (fun i => C (sc1 ω i) * X i)) := by
    ext r c
    rw [of_apply, Mp_conj_diag hω0 hω, Matrix.smul_apply, map_apply, smul_eq_mul]
  rw [hM, h2, ← mul_assoc, hprod, one_mul, det_smul, Fintype.card_fin, ← C_pow, ← pow_mul,
    mul_comm 2 Q, pow_mul, hω, one_pow, C_1, one_mul] at h1
  rw [Pdet, aeval_det]
  exact h1

lemma Pdet_sc2 {ω : ℂ} (hω0 : ω ≠ 0) (hω : ω ^ Q = 1) :
    aeval (fun i => C (sc2 ω i) * X i) (Pdet Q ω) = Pdet Q ω := by
  rw [Pdet, aeval_det, ← det_submatrix_equiv_self (Equiv.addRight (1 : Fin Q)) (Mp Q ω)]
  congr 1
  ext r c
  simp only [map_apply, submatrix_apply, Equiv.coe_addRight]
  rw [Mp_shift hω0 hω]

/-- Exponent constraints on the support of `P`. -/
lemma dvd_of_mem_support {ω : ℂ} (hω0 : ω ≠ 0) (hω : ω ^ Q = 1)
    (hprim : ∀ n : ℤ, ω ^ n = 1 → (Q : ℤ) ∣ n) {m : Fin 3 →₀ ℕ}
    (hm : m ∈ (Pdet Q ω).support) :
    (Q : ℤ) ∣ (m 0 : ℤ) + m 1 ∧ (Q : ℤ) ∣ (m 0 : ℤ) - m 1 := by
  have hc : ((Pdet Q ω)).coeff m ≠ 0 := mem_support_iff.1 hm
  constructor
  · have h := coeff_aeval_scale (sc1 ω) (Pdet Q ω) m
    rw [Pdet_sc1 hω0 hω] at h
    have h' : (∏ i, sc1 ω i ^ m i) = 1 := by
      have := mul_right_cancel₀ hc (h.symm.trans (one_mul _).symm)
      exact this
    simp only [Fin.prod_univ_three, sc1, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, one_pow, mul_one] at h'
    apply hprim
    have : ω ^ ((m 0 : ℤ) + m 1) * (ω⁻¹ ^ m 0 * ω⁻¹ ^ m 1) = 1 := by
      rw [zpow_add₀ hω0, zpow_natCast, zpow_natCast, inv_pow, inv_pow]
      field_simp
    rwa [h', mul_one] at this
  · have h := coeff_aeval_scale (sc2 ω) (Pdet Q ω) m
    rw [Pdet_sc2 hω0 hω] at h
    have h' : (∏ i, sc2 ω i ^ m i) = 1 := mul_right_cancel₀ hc (h.symm.trans (one_mul _).symm)
    simp only [Fin.prod_univ_three, sc2, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, one_pow, mul_one] at h'
    apply hprim
    rw [zpow_sub₀ hω0, zpow_natCast, zpow_natCast, ← h', inv_pow]
    field_simp

/-- **Support of `P` for odd `Q`**: only `S^Q T^Q E^j`, `S^{2Q}T^Q`, `T^Q`, `S^Q T^{2Q}`, `S^Q`. -/
lemma support_cases (hodd : Odd Q) {ω : ℂ} (hω0 : ω ≠ 0) (hω : ω ^ Q = 1)
    (hprim : ∀ n : ℤ, ω ^ n = 1 → (Q : ℤ) ∣ n) {m : Fin 3 →₀ ℕ}
    (hm : m ∈ (Pdet Q ω).support) :
    (m 0 = Q ∧ m 1 = Q) ∨ (m 2 = 0 ∧ ((m 0 = 2 * Q ∧ m 1 = Q) ∨ (m 0 = 0 ∧ m 1 = Q) ∨
      (m 0 = Q ∧ m 1 = 2 * Q) ∨ (m 0 = Q ∧ m 1 = 0))) := by
  obtain ⟨h1, h2⟩ := dvd_of_mem_support hω0 hω hprim hm
  have hg := good_Pdet ω m hm
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  have hQ : (0 : ℤ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  set i : ℤ := (m 0 : ℤ) - Q with hi
  set j : ℤ := (m 1 : ℤ) - Q with hj
  have hi1 := le_abs_self i
  have hi2 := neg_abs_le i
  have hj1 := le_abs_self j
  have hj2 := neg_abs_le j
  have hm2 : (0 : ℤ) ≤ m 2 := by positivity
  have hapos : (Q : ℤ) * a ≤ 3 * Q := by linarith
  have haneg : (Q : ℤ) ≤ Q * a := by linarith
  have hbpos : (Q : ℤ) * b ≤ Q := by linarith
  have hbneg : -(Q : ℤ) ≤ Q * b := by linarith
  have ha1 : a ≤ 3 := by
    by_contra h; push Not at h; nlinarith
  have ha2 : 1 ≤ a := by
    by_contra h; push Not at h; nlinarith
  have hb1 : b ≤ 1 := by
    by_contra h; push Not at h; nlinarith
  have hb2 : -1 ≤ b := by
    by_contra h; push Not at h; nlinarith
  obtain ⟨t, ht⟩ := hodd
  have hQt : (Q : ℤ) = 2 * t + 1 := by exact_mod_cast ht
  rcases abs_cases i with ⟨hi', -⟩ | ⟨hi', -⟩ <;> rcases abs_cases j with ⟨hj', -⟩ | ⟨hj', -⟩ <;>
    rw [hi', hj'] at hg <;> interval_cases a <;> interval_cases b <;> omega

/-- The gauge Bloch matrix in the variables `s = e(k/Q+θ)`, `t = e(k/Q-θ)`. -/
def Gst (Q : ℕ) [NeZero Q] (ω s t : ℂ) : Matrix (Fin Q) (Fin Q) ℂ := fun r c =>
  (if c = r + 1 then -I * (s * ω ^ (r : ℕ) - t * ω⁻¹ ^ (r : ℕ)) else 0) +
  (if r = c + 1 then -I * (t⁻¹ * ω ^ (c : ℕ) - s⁻¹ * ω⁻¹ ^ (c : ℕ)) else 0)

lemma eval_Mp (ω s t E : ℂ) (hs : s ≠ 0) (ht : t ≠ 0) :
    (Mp Q ω).map (eval ![s, t, E]) = (s * t) • ((E • (1 : Matrix (Fin Q) (Fin Q) ℂ)) - Gst Q ω s t) := by
  ext r c
  simp only [map_apply, Mp, Gst, map_add, apply_ite (eval ![s, t, E]), map_sub, eval_mono,
    map_zero, Matrix.smul_apply, Matrix.sub_apply, one_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  split_ifs <;> field_simp <;> ring

lemma eval_Pdet (ω s t E : ℂ) (hs : s ≠ 0) (ht : t ≠ 0) :
    eval ![s, t, E] (Pdet Q ω) = (s * t) ^ Q * ((E • (1 : Matrix (Fin Q) (Fin Q) ℂ)) - Gst Q ω s t).det := by
  rw [Pdet, RingHom.map_det, RingHom.mapMatrix_apply, eval_Mp ω s t E hs ht, det_smul,
    Fintype.card_fin]

lemma ev_ext (m : Fin 3 →₀ ℕ) : m = ev (m 0) (m 1) (m 2) := by
  ext i; fin_cases i <;> simp

lemma ev_inj {a b e a' b' e' : ℕ} (h : ev a b e = ev a' b' e') : a = a' ∧ b = b' ∧ e = e' := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using congrArg (fun m => m 0) h
  · simpa using congrArg (fun m => m 1) h
  · simpa using congrArg (fun m => m 2) h

/-- **Chambers-type formula for the chiral Bloch matrix, odd period** (cf. [JKK, Lemma 3]):
the characteristic polynomial is `Φ(E) + c₁ s^Q + c₂ s^{-Q} + c₃ t^Q + c₄ t^{-Q}`. -/
theorem chambers_odd (hodd : Odd Q) {ω : ℂ} (hω0 : ω ≠ 0) (hω : ω ^ Q = 1)
    (hprim : ∀ n : ℤ, ω ^ n = 1 → (Q : ℤ) ∣ n) :
    ∃ (Φ : ℂ → ℂ) (c₁ c₂ c₃ c₄ : ℂ), ∀ s t E : ℂ, s ≠ 0 → t ≠ 0 →
      ((E • (1 : Matrix (Fin Q) (Fin Q) ℂ)) - Gst Q ω s t).det =
        Φ E + c₁ * s ^ Q + c₂ * (s ^ Q)⁻¹ + c₃ * t ^ Q + c₄ * (t ^ Q)⁻¹ := by
  classical
  set P := Pdet Q ω with hP
  set main : Finset (Fin 3 →₀ ℕ) := P.support.filter (fun m => m 0 = Q ∧ m 1 = Q)
  set v₁ := ev (2 * Q) Q 0
  set v₂ := ev 0 Q 0
  set v₃ := ev Q (2 * Q) 0
  set v₄ := ev Q 0 0
  refine ⟨fun E => ∑ m ∈ main, (P).coeff m * E ^ (m 2), (P).coeff v₁, (P).coeff v₂, (P).coeff v₃,
    (P).coeff v₄, fun s t E hs ht => ?_⟩
  have hQ : 0 < Q := Nat.pos_of_ne_zero (NeZero.ne Q)
  have key0 := eval_Pdet (Q := Q) ω s t E hs ht
  rw [eval_eq', ← Finset.sum_filter_add_sum_filter_not P.support
    (fun m => m 0 = Q ∧ m 1 = Q)] at key0
  set f : (Fin 3 →₀ ℕ) → ℂ := fun d => (P).coeff d * ∏ i, ![s, t, E] i ^ d i with hf
  have key : ∑ d ∈ main, f d +
      ∑ d ∈ P.support.filter (fun m => ¬(m 0 = Q ∧ m 1 = Q)), f d =
      (s * t) ^ Q * ((E • (1 : Matrix (Fin Q) (Fin Q) ℂ)) - Gst Q ω s t).det := key0
  have hmain : ∑ d ∈ main, f d = (s * t) ^ Q * ∑ m ∈ main, (P).coeff m * E ^ (m 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    obtain ⟨-, h0, h1⟩ := Finset.mem_filter.1 hd
    simp only [hf, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, h0, h1]
    ring
  have hsub : P.support.filter (fun m => ¬(m 0 = Q ∧ m 1 = Q)) ⊆ {v₁, v₂, v₃, v₄} := by
    intro d hd
    obtain ⟨hd1, hd2⟩ := Finset.mem_filter.1 hd
    rcases support_cases hodd hω0 hω hprim hd1 with h | ⟨h2, h⟩
    · exact absurd h hd2
    · rw [ev_ext d, h2]
      rcases h with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩ <;> simp [a, b, v₁, v₂, v₃, v₄]
  have hrest : ∑ d ∈ P.support.filter (fun m => ¬(m 0 = Q ∧ m 1 = Q)), f d =
      ∑ d ∈ ({v₁, v₂, v₃, v₄} : Finset _), f d := by
    refine Finset.sum_subset hsub fun d hd hnd => ?_
    have : d ∉ P.support := by
      intro hds
      apply hnd
      refine Finset.mem_filter.2 ⟨hds, ?_⟩
      rintro ⟨h0, h1⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hd
      rcases hd with rfl | rfl | rfl | rfl <;> simp [v₁, v₂, v₃, v₄] at h0 h1 <;> omega
    simp [hf, notMem_support_iff.1 this]
  have hne : ∀ {a b e a' b' e' : ℕ}, a ≠ a' → ev a b e ≠ ev a' b' e' :=
    fun h h' => h (ev_inj h').1
  have hne' : ∀ {a b e a' b' e' : ℕ}, b ≠ b' → ev a b e ≠ ev a' b' e' :=
    fun h h' => h (ev_inj h').2.1
  have h12 : v₁ ≠ v₂ := hne (by omega)
  have h13 : v₁ ≠ v₃ := hne (by omega)
  have h14 : v₁ ≠ v₄ := hne (by omega)
  have h23 : v₂ ≠ v₃ := hne (by omega)
  have h24 : v₂ ≠ v₄ := hne (by omega)
  have h34 : v₃ ≠ v₄ := hne' (by omega)
  rw [hrest, Finset.sum_insert (by simp [h12, h13, h14]), Finset.sum_insert (by simp [h23, h24]),
    Finset.sum_insert (by simp [h34]), Finset.sum_singleton, hmain] at key
  simp only [hf, Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, v₁, v₂, v₃, v₄, ev_zero, ev_one,
    ev_two, pow_zero, mul_one] at key
  have hst : (s * t) ^ Q ≠ 0 := pow_ne_zero _ (mul_ne_zero hs ht)
  apply mul_left_cancel₀ hst
  rw [← key]
  field_simp
  ring

end LastBound
end CAH

/-! ## Part B: the chiral Bloch matrices and the spectral estimate -/

namespace CAH
namespace LastBound

open Real Matrix Complex Set MeasureTheory
open CAH.FB (bext bm jop Per bext_coe bext_isBloch per_cb cb bm_isHermitian bandFun sq01)
open scoped ComplexConjugate

variable {Q : ℕ} [NeZero Q]

/-! ### Fin arithmetic -/

lemma val_add_one' (r : Fin Q) :
    ((r + 1 : Fin Q) : ℕ) = if (r : ℕ) + 1 = Q then 0 else (r : ℕ) + 1 := by
  rw [val_add_one]
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by have := r.2; omega)

lemma eq_add_one_iff (r c : Fin Q) :
    c = r + 1 ↔ (c : ℕ) = if (r : ℕ) + 1 = Q then 0 else (r : ℕ) + 1 := by
  rw [Fin.ext_iff, val_add_one']

/-! ### The corner form of the Bloch matrix -/

/-- Phase of the bond `r ↔ r+1`: `e(k)` across the cell boundary, `1` otherwise. -/
def ph (k : ℝ) (r : Fin Q) : ℂ := if (r : ℕ) + 1 = Q then FB.ex k else 1

/-- The Bloch matrix of a periodic Jacobi matrix with zero diagonal, in corner form. -/
def Bc (a : ℤ → ℝ) (k : ℝ) : Matrix (Fin Q) (Fin Q) ℂ := fun r c =>
  (if c = r + 1 then ph k r * (a (r : ℕ) : ℂ) else 0) +
  (if r = c + 1 then conj (ph k c) * (a (c : ℕ) : ℂ) else 0)

lemma bext_succ (k : ℝ) (u : Fin Q → ℂ) (r : Fin Q) :
    bext Q k u (((r : ℕ) : ℤ) + 1) = ph k r * u (r + 1) := by
  unfold ph
  split_ifs with h
  · have hr1 : r + 1 = 0 := by
      rw [Fin.ext_iff, val_add_one', if_pos h]; rfl
    have : ((r : ℕ) : ℤ) + 1 = (((0 : Fin Q) : ℕ) : ℤ) + Q := by
      simp only [Fin.val_zero, Nat.cast_zero, zero_add]; exact_mod_cast h
    rw [this, bext_isBloch u, bext_coe, hr1]
  · have : ((r : ℕ) : ℤ) + 1 = (((r + 1 : Fin Q) : ℕ) : ℤ) := by
      rw [val_add_one', if_neg h]; push_cast; ring
    rw [this, bext_coe, one_mul]

lemma bext_pred (k : ℝ) (u : Fin Q → ℂ) (c : Fin Q) :
    bext Q k u ((((c + 1 : Fin Q) : ℕ) : ℤ) - 1) = conj (ph k c) * u c := by
  unfold ph
  rw [val_add_one']
  split_ifs with h
  · have e : ((0 : ℕ) : ℤ) - 1 + Q = ((c : ℕ) : ℤ) := by push_cast; omega
    have hb := bext_isBloch (Q := Q) (k := k) u ((0 : ℕ) - 1 : ℤ)
    rw [e, bext_coe] at hb
    rw [hb, ← mul_assoc, FB.conj_ex_mul, one_mul]
  · rw [map_one, one_mul]
    have : (((c : ℕ) + 1 : ℕ) : ℤ) - 1 = ((c : ℕ) : ℤ) := by push_cast; ring
    rw [this, bext_coe]

lemma per_pred {a : ℤ → ℝ} (ha : Per Q a) (c : Fin Q) :
    a ((((c + 1 : Fin Q) : ℕ) : ℤ) - 1) = a ((c : ℕ) : ℤ) := by
  rw [val_add_one']
  split_ifs with h
  · have := ha ((0 : ℕ) - 1 : ℤ)
    rw [← this]; congr 1; push_cast; omega
  · congr 1; push_cast; ring

/-- The library's Bloch matrix `bm` (zero diagonal) is the corner form `Bc`. -/
lemma bm_eq_Bc {a d : ℤ → ℝ} (ha : Per Q a) (hd : ∀ n, d n = 0) (k : ℝ) :
    bm Q a d k = Bc a k := by
  ext r c
  simp only [bm, jop, hd, Complex.ofReal_zero, zero_mul, add_zero, Bc]
  rw [bext_succ, Pi.single_apply]
  have hr : r = (r - 1) + 1 := (sub_add_cancel r 1).symm
  conv_lhs => rw [show ((r : ℕ) : ℤ) - 1 = ((((r - 1 + 1 : Fin Q) : ℕ) : ℤ) - 1) by rw [← hr]]
  rw [bext_pred, per_pred ha, Pi.single_apply]
  rw [add_comm]
  congr 1
  · by_cases h : c = r + 1
    · rw [if_pos h.symm, if_pos h, mul_one]; ring
    · rw [if_neg (Ne.symm h), if_neg h, mul_zero, mul_zero]
  · by_cases h : r = c + 1
    · have : r - 1 = c := by rw [h, add_sub_cancel_right]
      rw [if_pos this, if_pos h, this, mul_one]; ring
    · have : r - 1 ≠ c := fun h' => h (by rw [← h', sub_add_cancel])
      rw [if_neg this, if_neg h, mul_zero, mul_zero]

/-! ### The gauge transformation -/

/-- `2 sin 2πx = -i (e(x) - e(-x))`. -/
lemma two_sin_ex (x : ℝ) : (((2 * Real.sin (2 * π * x)) : ℝ) : ℂ) = -I * (FB.ex x - FB.ex (-x)) := by
  unfold FB.ex
  have h1 : Complex.exp (2 * π * I * x) = Complex.exp (((2 * π * x : ℝ) : ℂ) * I) := by
    congr 1; push_cast; ring
  have h2 : Complex.exp (2 * π * I * ((-x : ℝ) : ℂ)) = Complex.exp (-(((2 * π * x : ℝ) : ℂ)) * I) := by
    congr 1; push_cast; ring
  rw [h1, h2, Complex.ofReal_mul, Complex.ofReal_sin, Complex.sin]
  push_cast
  ring

/-- `ex(β)^n = ex(nβ)` for integer `n`. -/
lemma ex_zpow (β : ℝ) (n : ℤ) : FB.ex β ^ n = FB.ex (n * β) := by
  unfold FB.ex
  rw [← Complex.exp_int_mul]
  congr 1; push_cast; ring

lemma ex_pow (β : ℝ) (n : ℕ) : FB.ex β ^ n = FB.ex (n * β) := (FB.ex_nat_mul n β).symm

lemma ex_inv (t : ℝ) : (FB.ex t)⁻¹ = FB.ex (-t) :=
  inv_eq_of_mul_eq_one_right (by rw [← FB.ex_add, add_neg_cancel, FB.ex_zero])

lemma ex_ne_zero (t : ℝ) : FB.ex t ≠ 0 := by
  intro h; have := FB.norm_ex t; rw [h, norm_zero] at this; exact zero_ne_one this

lemma ex_inv_pow (β : ℝ) (n : ℕ) : (FB.ex β)⁻¹ ^ n = FB.ex (-(n * β)) := by
  rw [ex_inv, ← FB.ex_nat_mul]; congr 1; ring

/-- The chiral bonds `a_n(θ) = 2 sin 2π(θ + nβ)`. -/
abbrev bond (β θ : ℝ) : ℤ → ℝ := cb (fun x => 2 * Real.sin (2 * π * x)) β θ

lemma bond_apply (β θ : ℝ) (n : ℤ) : bond β θ n = 2 * Real.sin (2 * π * (θ + n * β)) := rfl

lemma neg_I_ex_congr {x1 x2 y1 y2 : ℝ} (h1 : x1 = y1) (h2 : x2 = y2) :
    -I * (FB.ex x1 - FB.ex x2) = -I * (FB.ex y1 - FB.ex y2) := by rw [h1, h2]

/-- **Gauge transformation**: `Bc = D G D⁻¹` with `D = diag(e(rk/Q))` and `G = Gst`, evaluated
at `s = e(k/Q + θ)`, `t = e(k/Q - θ)`. -/
lemma Bc_eq_gauge (β θ k : ℝ) :
    Bc (bond β θ) k = diagonal (fun r : Fin Q => FB.ex ((r : ℕ) * k / Q)) *
      Gst Q (FB.ex β) (FB.ex (k / Q + θ)) (FB.ex (k / Q - θ)) *
      diagonal (fun c : Fin Q => FB.ex (-((c : ℕ) * k / Q))) := by
  have hQ : (Q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne Q
  ext r c
  rw [mul_diagonal, diagonal_mul]
  simp only [Bc, Gst, mul_add, add_mul]
  congr 1
  · split_ifs with h
    · have hc := (eq_add_one_iff r c).1 h
      have e1 : FB.ex ((r : ℕ) * k / Q) * (-I * (FB.ex (k / Q + θ) * FB.ex β ^ (r : ℕ) -
          FB.ex (k / Q - θ) * (FB.ex β)⁻¹ ^ (r : ℕ))) * FB.ex (-((c : ℕ) * k / Q)) =
          -I * (FB.ex ((r : ℕ) * k / Q + (k / Q + θ) + (r : ℕ) * β + -((c : ℕ) * k / Q)) -
            FB.ex ((r : ℕ) * k / Q + (k / Q - θ) + -((r : ℕ) * β) + -((c : ℕ) * k / Q))) := by
        rw [ex_pow, ex_inv_pow]; simp only [FB.ex_add]; ring
      rw [e1, bond_apply, two_sin_ex, ph]
      push_cast
      split_ifs at hc ⊢ with h1
      · have hr : ((r : ℕ) : ℝ) = Q - 1 := by
          have : ((r : ℕ) : ℝ) + 1 = Q := by exact_mod_cast h1
          linarith
        have hc0 : ((c : ℕ) : ℝ) = 0 := by exact_mod_cast hc
        rw [show ∀ A : ℝ, FB.ex k * (-I * (FB.ex A - FB.ex (-A))) =
          -I * (FB.ex (k + A) - FB.ex (k + -A)) from fun A => by simp only [FB.ex_add]; ring]
        apply neg_I_ex_congr
        · rw [hr, hc0]; field_simp; ring
        · rw [hr, hc0]; field_simp; ring
      · have hc' : ((c : ℕ) : ℝ) = (r : ℕ) + 1 := by exact_mod_cast hc
        rw [one_mul]
        apply neg_I_ex_congr
        · rw [hc']; field_simp; ring
        · rw [hc']; field_simp; ring
    · simp
  · split_ifs with h
    · have hr := (eq_add_one_iff c r).1 h
      have e1 : FB.ex ((r : ℕ) * k / Q) * (-I * ((FB.ex (k / Q - θ))⁻¹ * FB.ex β ^ (c : ℕ) -
          (FB.ex (k / Q + θ))⁻¹ * (FB.ex β)⁻¹ ^ (c : ℕ))) * FB.ex (-((c : ℕ) * k / Q)) =
          -I * (FB.ex ((r : ℕ) * k / Q + -(k / Q - θ) + (c : ℕ) * β + -((c : ℕ) * k / Q)) -
            FB.ex ((r : ℕ) * k / Q + -(k / Q + θ) + -((c : ℕ) * β) + -((c : ℕ) * k / Q))) := by
        rw [ex_pow, ex_inv_pow, ex_inv, ex_inv]; simp only [FB.ex_add]; ring
      rw [e1, bond_apply, two_sin_ex, ph]
      push_cast
      split_ifs at hr ⊢ with h1
      · have hc : ((c : ℕ) : ℝ) = Q - 1 := by
          have : ((c : ℕ) : ℝ) + 1 = Q := by exact_mod_cast h1
          linarith
        have hr0 : ((r : ℕ) : ℝ) = 0 := by exact_mod_cast hr
        rw [FB.conj_ex, show ∀ A : ℝ, FB.ex (-k) * (-I * (FB.ex A - FB.ex (-A))) =
          -I * (FB.ex (-k + A) - FB.ex (-k + -A)) from fun A => by simp only [FB.ex_add]; ring]
        apply neg_I_ex_congr
        · rw [hc, hr0]; field_simp; ring
        · rw [hc, hr0]; field_simp; ring
      · have hr' : ((r : ℕ) : ℝ) = (c : ℕ) + 1 := by exact_mod_cast hr
        rw [map_one, one_mul]
        apply neg_I_ex_congr
        · rw [hr']; field_simp; ring
        · rw [hr']; field_simp; ring
    · simp

/-! ### Determinants, spectra and reality -/

lemma det_conj_diag (A : Matrix (Fin Q) (Fin Q) ℂ) (d d' : Fin Q → ℂ)
    (hdd : ∀ i, d i * d' i = 1) (E : ℂ) :
    (E • (1 : Matrix (Fin Q) (Fin Q) ℂ) - diagonal d * A * diagonal d').det =
      (E • (1 : Matrix (Fin Q) (Fin Q) ℂ) - A).det := by
  have h1 : E • (1 : Matrix (Fin Q) (Fin Q) ℂ) - diagonal d * A * diagonal d' =
      diagonal d * (E • 1 - A) * diagonal d' := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      diagonal_mul_diagonal]
    congr 1
    rw [show (fun i => d i * d' i) = fun _ => (1 : ℂ) from funext hdd, diagonal_one]
  rw [h1, det_mul, det_mul, det_diagonal, det_diagonal]
  have : (∏ i, d i) * ∏ i, d' i = 1 := by
    rw [← Finset.prod_mul_distrib]; exact Finset.prod_eq_one fun i _ => hdd i
  calc (∏ i, d i) * (E • 1 - A).det * ∏ i, d' i
      = ((∏ i, d i) * ∏ i, d' i) * (E • 1 - A).det := by ring
    _ = _ := by rw [this, one_mul]

lemma mem_spectrum_iff_det {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) (E : ℝ) :
    E ∈ spectrum ℝ A ↔ ((E : ℂ) • (1 : Matrix n n ℂ) - A).det = 0 := by
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul,
    Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not]

lemma det_re_of_herm {A : Matrix (Fin Q) (Fin Q) ℂ} (hA : A.IsHermitian) (E : ℝ) :
    ((((E : ℂ) • (1 : Matrix (Fin Q) (Fin Q) ℂ) - A).det.re : ℝ) : ℂ) =
      ((E : ℂ) • (1 : Matrix (Fin Q) (Fin Q) ℂ) - A).det := by
  have hH : ((E : ℂ) • (1 : Matrix (Fin Q) (Fin Q) ℂ) - A).IsHermitian := by
    refine IsHermitian.sub ?_ hA
    unfold IsHermitian
    rw [conjTranspose_smul, conjTranspose_one, Complex.star_def, Complex.conj_ofReal]
  have := det_conjTranspose ((E : ℂ) • (1 : Matrix (Fin Q) (Fin Q) ℂ) - A)
  rw [hH.eq] at this
  exact Complex.conj_eq_iff_re.1 this.symm

/-- Periodicity of the chiral bond function. -/
lemma periodic_two_sin : Function.Periodic (fun x : ℝ => 2 * Real.sin (2 * π * x)) 1 := by
  intro x
  simp only
  rw [show 2 * π * (x + 1) = 2 * π * x + 2 * π by ring, Real.sin_add_two_pi]

lemma bm_bond_eq {β : ℝ} {P : ℤ} (hβ : (Q : ℝ) * β = P) (θ k : ℝ) :
    bm Q (bond β θ) (cb (fun _ => 0) β θ) k = Bc (bond β θ) k :=
  bm_eq_Bc (per_cb (Q := Q) periodic_two_sin hβ θ) (fun _ => rfl) k

lemma Bc_herm {β : ℝ} {P : ℤ} (hβ : (Q : ℝ) * β = P) (θ k : ℝ) :
    (Bc (Q := Q) (bond β θ) k).IsHermitian := by
  rw [← bm_bond_eq hβ]
  exact bm_isHermitian (per_cb (Q := Q) periodic_two_sin hβ θ)
    (per_cb (Q := Q) (f := fun _ => (0 : ℝ)) (fun _ => rfl) hβ θ) k

/-! ### Chambers-type formula for the Bloch matrices (odd `Q`) -/

lemma prim_of_coprime {p : ℤ} (hcop : IsCoprime p (Q : ℤ)) {β : ℝ} (hβ : (Q : ℝ) * β = p) :
    ∀ n : ℤ, FB.ex β ^ n = 1 → (Q : ℤ) ∣ n := by
  intro n hn
  rw [ex_zpow] at hn
  unfold FB.ex at hn
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 hn
  have h2πI : (2 * (π : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h3 : (((n : ℝ) * β : ℝ) : ℂ) = (m : ℂ) := by
    apply mul_left_cancel₀ h2πI
    rw [hm]; ring
  have h4 : (n : ℝ) * β = m := by exact_mod_cast h3
  have h5 : ((n * p : ℤ) : ℝ) = ((Q * m : ℤ) : ℝ) := by
    push_cast; rw [← hβ, ← h4]; ring
  have h6 : n * p = Q * m := by exact_mod_cast h5
  exact hcop.symm.dvd_of_dvd_mul_right ⟨m, h6⟩

lemma ex_pow_Q {p : ℤ} {β : ℝ} (hβ : (Q : ℝ) * β = p) : FB.ex β ^ Q = 1 := by
  rw [ex_pow, hβ, FB.ex_int]

/-- **Chambers-type formula** (cf. [JKK, (14)]) for the corner-form Bloch matrices of the chiral
operator at `β = p/Q`, `Q` odd. -/
theorem chambers_bloch (hodd : Odd Q) {p : ℤ} (hcop : IsCoprime p (Q : ℤ)) {β : ℝ}
    (hβ : (Q : ℝ) * β = p) :
    ∃ (Φ : ℂ → ℂ) (c₁ c₂ c₃ c₄ : ℂ), ∀ (θ k : ℝ) (E : ℂ),
      (E • (1 : Matrix (Fin Q) (Fin Q) ℂ) - Bc (bond β θ) k).det =
        Φ E + c₁ * FB.ex (k + Q * θ) + c₂ * FB.ex (-(k + Q * θ)) + c₃ * FB.ex (k - Q * θ) +
          c₄ * FB.ex (-(k - Q * θ)) := by
  obtain ⟨Φ, c₁, c₂, c₃, c₄, hch⟩ := chambers_odd hodd (ex_ne_zero β) (ex_pow_Q hβ)
    (prim_of_coprime hcop hβ)
  refine ⟨Φ, c₁, c₂, c₃, c₄, fun θ k E => ?_⟩
  have hQ : (Q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne Q
  rw [Bc_eq_gauge, det_conj_diag _ _ _ (fun i => by rw [← FB.ex_add, add_neg_cancel, FB.ex_zero]),
    hch _ _ E (ex_ne_zero _) (ex_ne_zero _), ex_pow, ex_pow, ex_inv, ex_inv]
  have e1 : (Q : ℝ) * (k / Q + θ) = k + Q * θ := by field_simp
  have e2 : (Q : ℝ) * (k / Q - θ) = k - Q * θ := by field_simp
  rw [e1, e2]

lemma re_pair (c c' : ℂ) (X : ℝ) :
    (c * FB.ex X + c' * FB.ex (-X)).re = ((c + conj c') * FB.ex X).re := by
  rw [← FB.conj_ex, add_mul, Complex.add_re, Complex.add_re]
  congr 1
  rw [show c' * conj (FB.ex X) = conj (conj c' * FB.ex X) by simp, Complex.conj_re]

/-! ### Alignment: the union over phases is a single fibre -/

lemma re_mul_ex (w : ℂ) (x : ℝ) :
    (w * FB.ex x).re = ‖w‖ * Real.cos (2 * π * x + arg w) := by
  conv_lhs => rw [← norm_mul_exp_arg_mul_I w]
  unfold FB.ex
  rw [mul_assoc, ← Complex.exp_add,
    show (arg w : ℂ) * I + 2 * π * I * x = ((2 * π * x + arg w : ℝ) : ℂ) * I by push_cast; ring,
    Complex.re_ofReal_mul, exp_ofReal_mul_I_re]

/-- For `F(x,y) = Re(w₁ e(x)) + Re(w₂ e(y))` there is a shift `θ₀` such that every value of `F`
is attained on the line `(k + θ₀, k - θ₀)`. -/
lemma align (w₁ w₂ : ℂ) : ∃ θ₀ : ℝ, ∀ x y : ℝ, ∃ k : ℝ,
    (w₁ * FB.ex x).re + (w₂ * FB.ex y).re = (w₁ * FB.ex (k + θ₀)).re + (w₂ * FB.ex (k - θ₀)).re := by
  refine ⟨(arg w₂ - arg w₁) / (4 * π), fun x y => ?_⟩
  have hπ : π ≠ 0 := Real.pi_ne_zero
  set M := ‖w₁‖ + ‖w₂‖ with hM
  set γ := (arg w₁ + arg w₂) / 2
  have hform : ∀ k, (w₁ * FB.ex (k + (arg w₂ - arg w₁) / (4 * π))).re +
      (w₂ * FB.ex (k - (arg w₂ - arg w₁) / (4 * π))).re = M * Real.cos (2 * π * k + γ) := by
    intro k
    rw [re_mul_ex, re_mul_ex]
    have h1 : 2 * π * (k + (arg w₂ - arg w₁) / (4 * π)) + arg w₁ = 2 * π * k + γ := by
      field_simp; ring
    have h2 : 2 * π * (k - (arg w₂ - arg w₁) / (4 * π)) + arg w₂ = 2 * π * k + γ := by
      field_simp; ring
    rw [h1, h2]; ring
  have hv : |(w₁ * FB.ex x).re + (w₂ * FB.ex y).re| ≤ M := by
    rw [re_mul_ex, re_mul_ex]
    have c1 := Real.abs_cos_le_one (2 * π * x + arg w₁)
    have c2 := Real.abs_cos_le_one (2 * π * y + arg w₂)
    calc _ ≤ |‖w₁‖ * Real.cos (2 * π * x + arg w₁)| + |‖w₂‖ * Real.cos (2 * π * y + arg w₂)| :=
          abs_add_le _ _
      _ = ‖w₁‖ * |Real.cos (2 * π * x + arg w₁)| + ‖w₂‖ * |Real.cos (2 * π * y + arg w₂)| := by
          rw [abs_mul, abs_mul, abs_norm, abs_norm]
      _ ≤ ‖w₁‖ * 1 + ‖w₂‖ * 1 := by gcongr
      _ = M := by ring
  set v := (w₁ * FB.ex x).re + (w₂ * FB.ex y).re
  by_cases hM0 : M = 0
  · refine ⟨0, ?_⟩
    rw [hform, hM0, zero_mul]
    have := abs_nonneg v
    rw [hM0] at hv
    exact abs_nonpos_iff.1 hv
  · have hMpos : 0 < M := lt_of_le_of_ne (by positivity) (Ne.symm hM0)
    refine ⟨(Real.arccos (v / M) - γ) / (2 * π), ?_⟩
    rw [hform]
    have h1 : 2 * π * ((Real.arccos (v / M) - γ) / (2 * π)) + γ = Real.arccos (v / M) := by
      field_simp; ring
    have hle := abs_le.1 hv
    rw [h1, Real.cos_arccos]
    · field_simp
    · rw [le_div_iff₀ hMpos]; linarith
    · rw [div_le_one hMpos]; linarith

/-! ### A short bond -/

lemma exists_small_bond {p : ℤ} (hcop : IsCoprime p (Q : ℤ)) {β : ℝ} (hβ : (Q : ℝ) * β = p)
    (θ : ℝ) : ∃ n : ℤ, |2 * Real.sin (2 * π * (θ + n * β))| ≤ 4 * π / Q := by
  obtain ⟨u, v, huv⟩ := hcop
  have hQ : (0 : ℝ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  set j : ℤ := -⌊(Q : ℝ) * θ⌋ with hj
  refine ⟨j * u, ?_⟩
  have huv' : (u : ℝ) * p + v * Q = 1 := by exact_mod_cast huv
  have key : θ + ((j * u : ℤ) : ℝ) * β = (θ + j / Q) - ((j * v : ℤ) : ℝ) := by
    have hβ' : β = p / Q := by field_simp; linarith
    rw [hβ']; push_cast; field_simp; linear_combination (j : ℝ) * huv'
  have hy : θ + (j : ℝ) / Q = Int.fract ((Q : ℝ) * θ) / Q := by
    rw [Int.fract, hj]; push_cast; field_simp; ring
  have hf0 := Int.fract_nonneg ((Q : ℝ) * θ)
  have hf1 := Int.fract_lt_one ((Q : ℝ) * θ)
  rw [key, show 2 * π * ((θ + j / Q) - ((j * v : ℤ) : ℝ)) =
      2 * π * (θ + j / Q) - ((j * v : ℤ) : ℝ) * (2 * π) by ring, Real.sin_sub_int_mul_two_pi, hy]
  have hpos : 0 ≤ 2 * π * (Int.fract ((Q : ℝ) * θ) / Q) := by positivity
  calc |2 * Real.sin (2 * π * (Int.fract ((Q : ℝ) * θ) / Q))|
      = 2 * |Real.sin (2 * π * (Int.fract ((Q : ℝ) * θ) / Q))| := by rw [abs_mul, abs_two]
    _ ≤ 2 * |2 * π * (Int.fract ((Q : ℝ) * θ) / Q)| :=
        mul_le_mul_of_nonneg_left Real.abs_sin_le_abs (by norm_num)
    _ = 2 * (2 * π * (Int.fract ((Q : ℝ) * θ) / Q)) := by rw [abs_of_nonneg hpos]
    _ ≤ 4 * π / Q := by
        rw [show 2 * (2 * π * (Int.fract ((Q : ℝ) * θ) / Q)) = 4 * π * Int.fract ((Q : ℝ) * θ) / Q
          by ring]
        rw [div_le_div_iff₀ hQ hQ]
        have := mul_pos Real.pi_pos hQ
        nlinarith

/-! ### One fibre: the boundary-perturbation cover -/

/-- The Bloch matrix with the bond `Q-1 ↔ 0` removed. -/
def A0 (a : ℤ → ℝ) : Matrix (Fin Q) (Fin Q) ℂ := fun r c =>
  (if c = r + 1 ∧ (r : ℕ) + 1 ≠ Q then (a (r : ℕ) : ℂ) else 0) +
  (if r = c + 1 ∧ (c : ℕ) + 1 ≠ Q then (a (c : ℕ) : ℂ) else 0)

/-- The `2 × 2` boundary coupling `[[0, e(-k)A], [e(k)A, 0]]`. -/
def V2 (A k : ℝ) : Matrix (Fin 2) (Fin 2) ℂ := !![0, FB.ex (-k) * A; FB.ex k * A, 0]

lemma A0_herm (a : ℤ → ℝ) : (A0 (Q := Q) a).IsHermitian := by
  ext r c
  simp only [conjTranspose_apply, A0, star_add]
  rw [add_comm]
  congr 1 <;> split_ifs <;> simp [Complex.conj_ofReal]

lemma V2_herm (A k : ℝ) : (V2 A k).IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [V2, conjTranspose_apply, FB.conj_ex, Complex.conj_ofReal]

lemma abs_le_of_mem_spectrum_V2 (A k l : ℝ) (hl : l ∈ spectrum ℝ (V2 A k)) : |l| ≤ |A| := by
  rw [mem_spectrum_iff_det, det_fin_two] at hl
  simp only [V2, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at hl
  simp only [Fin.isValue, ↓reduceIte, mul_one, sub_zero, one_ne_zero, zero_ne_one,
    mul_zero, zero_sub] at hl
  have h2 : (l : ℂ) ^ 2 = (A : ℂ) ^ 2 := by
    have e : FB.ex (-k) * FB.ex k = 1 := FB.ex_neg_mul_ex k
    linear_combination hl + (A : ℂ) ^ 2 * e
  have h3 : l ^ 2 = A ^ 2 := by exact_mod_cast h2
  exact ((sq_eq_sq_iff_abs_eq_abs l A).1 h3).le

lemma V2_eig (A k : ℝ) (i : Fin 2) : |(V2_herm A k).eigenvalues i| ≤ |A| :=
  abs_le_of_mem_spectrum_V2 A k _ ((V2_herm A k).eigenvalues_mem_spectrum_real i)

lemma bdry_entry (A k : ℝ) (r c : Fin Q) :
    ((Flow.bdry Q)ᴴ * V2 A k * Flow.bdry Q) r c =
      (if (r : ℕ) = 0 ∧ (c : ℕ) + 1 = Q then FB.ex (-k) * A else 0) +
      (if (r : ℕ) + 1 = Q ∧ (c : ℕ) = 0 then FB.ex k * A else 0) := by
  simp only [mul_apply, conjTranspose_apply, Fin.sum_univ_two, Flow.bdry, of_apply, V2]
  simp only [Fin.isValue, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one]
  split_ifs <;> simp_all <;> ring

lemma term1 (a : ℤ → ℝ) (k : ℝ) (r c : Fin Q) :
    (if c = r + 1 then ph k r * (a (r : ℕ) : ℂ) else 0) =
      (if c = r + 1 ∧ (r : ℕ) + 1 ≠ Q then (a (r : ℕ) : ℂ) else 0) +
      (if (r : ℕ) + 1 = Q ∧ (c : ℕ) = 0 then FB.ex k * a ((Q - 1 : ℕ) : ℤ) else 0) := by
  have hiff := eq_add_one_iff r c
  unfold ph
  by_cases h : c = r + 1
  · have hc := hiff.1 h
    by_cases hq : (r : ℕ) + 1 = Q
    · rw [if_pos hq] at hc
      have : (r : ℕ) = Q - 1 := by omega
      rw [if_pos h, if_pos hq, if_neg (fun h' => h'.2 hq), if_pos ⟨hq, hc⟩, zero_add, this]
    · rw [if_pos h, if_neg hq, if_pos ⟨h, hq⟩, one_mul, if_neg (fun h' => hq h'.1), add_zero]
  · have hn : ¬((r : ℕ) + 1 = Q ∧ (c : ℕ) = 0) := by
      rintro ⟨hq, hc⟩; exact h (hiff.2 (by rw [if_pos hq, hc]))
    rw [if_neg h, if_neg (fun h' => h h'.1), if_neg hn, add_zero]

lemma term2 (a : ℤ → ℝ) (k : ℝ) (r c : Fin Q) :
    (if r = c + 1 then conj (ph k c) * (a (c : ℕ) : ℂ) else 0) =
      (if r = c + 1 ∧ (c : ℕ) + 1 ≠ Q then (a (c : ℕ) : ℂ) else 0) +
      (if (r : ℕ) = 0 ∧ (c : ℕ) + 1 = Q then FB.ex (-k) * a ((Q - 1 : ℕ) : ℤ) else 0) := by
  have hiff := eq_add_one_iff c r
  unfold ph
  by_cases h : r = c + 1
  · have hr := hiff.1 h
    by_cases hq : (c : ℕ) + 1 = Q
    · rw [if_pos hq] at hr
      have : (c : ℕ) = Q - 1 := by omega
      rw [if_pos h, if_pos hq, if_neg (fun h' => h'.2 hq), if_pos ⟨hr, hq⟩, zero_add, this,
        FB.conj_ex]
    · rw [if_pos h, if_neg hq, if_pos ⟨h, hq⟩, map_one, one_mul, if_neg (fun h' => hq h'.2),
        add_zero]
  · have hn : ¬((r : ℕ) = 0 ∧ (c : ℕ) + 1 = Q) := by
      rintro ⟨hr, hq⟩; exact h (hiff.2 (by rw [if_pos hq, hr]))
    rw [if_neg h, if_neg (fun h' => h h'.1), if_neg hn, add_zero]

lemma Bc_eq_A0_add (a : ℤ → ℝ) (k : ℝ) :
    Bc a k = A0 a + (Flow.bdry Q)ᴴ * V2 (a ((Q - 1 : ℕ) : ℤ)) k * Flow.bdry Q := by
  ext r c
  rw [Matrix.add_apply, bdry_entry]
  simp only [Bc, A0]
  rw [term1, term2]
  ring

/-- **One fibre** (the Lidskii/flow argument of [BHJ], [JKK]): the union over quasi-momenta
`k` of the spectra of the Bloch matrices lies in `Q` intervals of total length
`≤ 4 |a_{Q-1}|`. -/
lemma fibre_cover (a : ℤ → ℝ) :
    ∃ lo hi : Fin Q → ℝ, (∀ j, lo j ≤ hi j) ∧ ∑ j, (hi j - lo j) ≤ 4 * |a ((Q - 1 : ℕ) : ℤ)| ∧
      ∀ k, spectrum ℝ (Bc (Q := Q) a k) ⊆ ⋃ j, Icc (lo j) (hi j) := by
  have hQ1 : 1 ≤ Q := Nat.one_le_iff_ne_zero.2 (NeZero.ne Q)
  have hvar : ∀ (B : ℝ → Matrix (Fin Q) (Fin Q) ℂ) (j : Fin Q),
      eVariationOn (fun x => Flow.eig (B x) j) (Icc (0 : ℝ) 0) = 0 := fun B j =>
    eVariationOn.subsingleton _ (by rw [Icc_self]; exact subsingleton_singleton)
  obtain ⟨lo, hi, hle, hlen, hcov⟩ := Flow.cover_bdry (a := 0) (b := 0) le_rfl hQ1
    (fun _ => A0 a) (abs_nonneg (a ((Q - 1 : ℕ) : ℤ))) le_rfl (fun _ _ => A0_herm a)
    (by simp [hvar])
  refine ⟨lo, hi, hle, by linarith, fun k => ?_⟩
  rw [Bc_eq_A0_add]
  exact hcov 0 ⟨le_rfl, le_rfl⟩ (V2 _ k) (V2_herm _ k) (V2_eig _ k)

end LastBound
end CAH

/-! ## Part C: Last's bound and the second proof of Theorem 1.2 -/

namespace CAH
namespace LastBound

open Real Matrix Complex Set MeasureTheory Filter Topology
open CAH.FB (bm bandFun sq01 cb)
open scoped ComplexConjugate

lemma continuous_two_sin : Continuous (fun x : ℝ => 2 * Real.sin (2 * π * x)) := by fun_prop

/-- **Last-type bound for the chiral operator, odd period** ([JKK, Theorem 1, case I]):
for `Q` odd and `Qβ = p` with `gcd(p, Q) = 1`, `|σ(M̂_β)| ≤ 16π/Q`. -/
theorem volume_sigmaM_chiral_le_of_odd {Q : ℕ} [NeZero Q] (hodd : Odd Q) {p : ℤ}
    (hcop : IsCoprime p (Q : ℤ)) {β : ℝ} (hβ : (Q : ℝ) * β = p) :
    volume (sigmaM (fun _ => 0) (fun x => 2 * Real.sin (2 * π * x)) β) ≤
      ENNReal.ofReal (16 * π / Q) := by
  obtain ⟨Φ, c₁, c₂, c₃, c₄, hch⟩ := chambers_bloch hodd hcop hβ
  set w₁ := c₁ + conj c₂
  set w₂ := c₃ + conj c₄
  set F : ℝ → ℝ → ℝ := fun θ k => (w₁ * FB.ex (k + Q * θ)).re + (w₂ * FB.ex (k - Q * θ)).re
    with hF
  have hspec : ∀ θ k (E : ℝ),
      E ∈ spectrum ℝ (Bc (Q := Q) (bond β θ) k) ↔ (Φ E).re + F θ k = 0 := by
    intro θ k E
    rw [mem_spectrum_iff_det, ← det_re_of_herm (Bc_herm hβ θ k) E, Complex.ofReal_eq_zero, hch]
    rw [show Φ ↑E + c₁ * FB.ex (k + Q * θ) + c₂ * FB.ex (-(k + Q * θ)) + c₃ * FB.ex (k - Q * θ) +
        c₄ * FB.ex (-(k - Q * θ)) = Φ ↑E + (c₁ * FB.ex (k + Q * θ) + c₂ * FB.ex (-(k + Q * θ))) +
        (c₃ * FB.ex (k - Q * θ) + c₄ * FB.ex (-(k - Q * θ))) by ring]
    rw [Complex.add_re, Complex.add_re, re_pair, re_pair, add_assoc]
  obtain ⟨θ₀, hθ₀⟩ := align w₁ w₂
  have hQ : (Q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne Q
  obtain ⟨n, hn⟩ := exists_small_bond hcop hβ (θ₀ / Q + ((Q - 1 : ℕ) : ℝ) * β)
  set θ₁ := θ₀ / Q + n * β with hθ₁
  have hFs : ∀ k, F θ₁ k = (w₁ * FB.ex (k + θ₀)).re + (w₂ * FB.ex (k - θ₀)).re := by
    intro k
    have e1 : k + Q * θ₁ = (k + θ₀) + ((n * p : ℤ) : ℝ) := by
      rw [hθ₁]; push_cast; field_simp; linear_combination (n : ℝ) * hβ
    have e2 : k - Q * θ₁ = (k - θ₀) + ((-(n * p) : ℤ) : ℝ) := by
      rw [hθ₁]; push_cast; field_simp; linear_combination -(n : ℝ) * hβ
    simp only [hF]
    rw [e1, e2, FB.ex_add (k + θ₀), FB.ex_add (k - θ₀), FB.ex_int, FB.ex_int, mul_one, mul_one]
  have hFall : ∀ θ k, ∃ k', F θ k = F θ₁ k' := by
    intro θ k
    obtain ⟨k', hk'⟩ := hθ₀ (k + Q * θ) (k - Q * θ)
    exact ⟨k', by rw [hFs]; exact hk'⟩
  obtain ⟨lo, hi, hle, hlen, hcov⟩ := fibre_cover (Q := Q) (bond β θ₁)
  have hsmall : |bond β θ₁ ((Q - 1 : ℕ) : ℤ)| ≤ 4 * π / Q := by
    rw [bond_apply]
    have e : θ₁ + (((Q - 1 : ℕ) : ℤ) : ℝ) * β = θ₀ / Q + ((Q - 1 : ℕ) : ℝ) * β + n * β := by
      rw [hθ₁]; push_cast; ring
    rw [e]; exact hn
  have hsub : sigmaM (fun _ => 0) (fun x => 2 * Real.sin (2 * π * x)) β ⊆
      ⋃ j, Icc (lo j) (hi j) := by
    rw [FB.sigmaM_eq_bands (Q := Q) (bddFun_const 0) (bddFun_two_sin (2 * π)) continuous_const
      continuous_two_sin (fun _ => rfl) periodic_two_sin hβ]
    intro E hE
    obtain ⟨j, x, -, rfl⟩ : ∃ j, ∃ x ∈ sq01,
        bandFun Q (fun _ => 0) (fun x => 2 * Real.sin (2 * π * x)) β j x = E := by
      simpa only [mem_iUnion, mem_image] using hE
    have hmem : bandFun Q (fun _ => 0) (fun x => 2 * Real.sin (2 * π * x)) β j x ∈
        spectrum ℝ (Bc (Q := Q) (bond β x.1) x.2) := by
      rw [Flow.spectrum_eq_range_eig (Bc_herm hβ x.1 x.2)]
      refine ⟨j, ?_⟩
      rw [← bm_bond_eq hβ]
      rfl
    have h0 := (hspec _ _ _).1 hmem
    obtain ⟨k', hk'⟩ := hFall x.1 x.2
    exact hcov k' ((hspec _ _ _).2 (by rw [← hk']; exact h0))
  calc volume (sigmaM (fun _ => 0) (fun x => 2 * Real.sin (2 * π * x)) β)
      ≤ volume (⋃ j, Icc (lo j) (hi j)) := measure_mono hsub
    _ ≤ ∑ j, volume (Icc (lo j) (hi j)) := measure_iUnion_fintype_le _ _
    _ = ∑ j, ENNReal.ofReal (hi j - lo j) := by simp only [Real.volume_Icc]
    _ = ENNReal.ofReal (∑ j, (hi j - lo j)) :=
        (ENNReal.ofReal_sum_of_nonneg fun j _ => sub_nonneg.2 (hle j)).symm
    _ ≤ ENNReal.ofReal (16 * π / Q) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc ∑ j, (hi j - lo j) ≤ 4 * |bond β θ₁ ((Q - 1 : ℕ) : ℤ)| := hlen
          _ ≤ 4 * (4 * π / Q) := by linarith
          _ = 16 * π / Q := by ring

/-! ### The almost Mathieu operator -/

lemma amo_add_one (α θ : ℝ) : amo (α + 1) θ = amo α θ := by
  have h : ∀ n : ℤ, 2 * Real.cos (2 * π * (θ + n * (α + 1))) =
      2 * Real.cos (2 * π * (θ + n * α)) := by
    intro n
    rw [show 2 * π * (θ + n * (α + 1)) = 2 * π * (θ + n * α) + (n : ℤ) * (2 * π) by ring,
      Real.cos_add_int_mul_two_pi]
  simp only [amo, jacobi, h]

lemma sigmaAMO_add_one (α : ℝ) : sigmaAMO (α + 1) = sigmaAMO α := by
  simp only [sigmaAMO, amo_add_one]

/-- `σ(M_α) ⊆ σ(M̂_{α/2})` (chiral gauge, `amo_spectrum_subset_chiral`). -/
lemma sigmaAMO_subset_chiral (α : ℝ) :
    sigmaAMO α ⊆ sigmaM (fun _ => 0) (fun x => 2 * Real.sin (2 * π * x)) (α / 2) :=
  closure_minimal (iUnion_subset fun θ => amo_spectrum_subset_chiral α θ) isClosed_closure

/-- **Last's bound (1.6), odd denominators** ([L], with the constant `16π` from the argument of
[JKK]): for coprime `p, q` with `q` odd, `|σ(M_{p/q})| ≤ 16π/q`. -/
theorem volume_sigmaAMO_le_of_odd {p : ℤ} {q : ℕ} (hq : Odd q) (hcop : IsCoprime p (q : ℤ)) :
    volume (sigmaAMO (p / q)) ≤ ENNReal.ofReal (16 * π / q) := by
  haveI : NeZero q := ⟨by rintro rfl; simp at hq⟩
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  obtain ⟨m, hmcop, hmα⟩ : ∃ m : ℤ, IsCoprime m (q : ℤ) ∧
      sigmaAMO (p / q) = sigmaAMO (2 * m / q) := by
    rcases Int.even_or_odd p with ⟨m, hm⟩ | ⟨m, hm⟩
    · refine ⟨m, ?_, ?_⟩
      · rw [show p = 2 * m by omega] at hcop; exact hcop.of_mul_left_right
      · congr 1; rw [hm]; push_cast; ring
    · obtain ⟨t, ht⟩ := hq
      refine ⟨m + t + 1, ?_, ?_⟩
      · have h1 : IsCoprime (p + (q : ℤ) * 1) q := hcop.add_mul_left_left 1
        rw [show p + (q : ℤ) * 1 = 2 * (m + t + 1) by rw [hm, ht]; push_cast; ring] at h1
        exact h1.of_mul_left_right
      · rw [← sigmaAMO_add_one]
        congr 1
        rw [show (p : ℝ) = 2 * m + 1 by exact_mod_cast hm]
        have hqt : (q : ℝ) = 2 * t + 1 := by exact_mod_cast ht
        push_cast
        field_simp
        rw [hqt]; ring
  rw [hmα]
  refine (measure_mono (sigmaAMO_subset_chiral _)).trans ?_
  exact volume_sigmaM_chiral_le_of_odd hq hmcop (by field_simp)

/-! ### Second proof of Theorem 1.2 -/

lemma q_ge_half {α : ℝ} (hα : Irrational α) (n : ℕ) : ((n : ℝ) + 1) / 2 ≤ q α n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · have := q_one_le hα 0; push_cast; linarith
    · have := q_one_le hα 1; push_cast; linarith
    · have h1 := q_add_le hα n
      have h2 := ih n (by omega)
      have h3 := q_one_le hα (n + 1)
      push_cast at h2 ⊢; linarith

/-- Among two consecutive continued-fraction denominators one is odd (by (2.4)). -/
lemma exists_odd_qN {α : ℝ} (hα : Irrational α) (N : ℕ) : ∃ n ≥ N, Odd (qN α n) := by
  by_contra h
  push Not at h
  have hev : ∀ n ≥ N, Even (qN α n : ℤ) := fun n hn =>
    (Int.even_coe_nat _).2 (Nat.not_odd_iff_even.1 (h n hn))
  have h1 := hev N le_rfl
  have h2 := hev (N + 1) (by omega)
  have hdet := det_int hα N
  have : Even ((-1 : ℤ) ^ (N + 1)) := by
    rw [← hdet]; exact (h2.mul_right _).sub (h1.mul_left _)
  rcases neg_one_pow_eq_or ℤ (N + 1) with h' | h' <;> rw [h'] at this <;> simp at this

/-- **Theorem 1.2 (`zero`), second proof** (paper §6, tex l. 1062–1064): for irrational `α`,
`|σ(M_α)| = 0`.  Proof: `σ(M_α) ⊆ σ(M̂_{α/2})`; by Theorem 1.3 (`measure_convergence'`)
`|σ(M̂_{p_n/q_n})| → |σ(M̂_{α/2})|` along the convergents of `α/2`, and along the (infinitely many)
odd `q_n` these measures are `≤ 16π/q_n → 0` by Last's bound. -/
theorem volume_sigmaAMO_eq_zero' {α : ℝ} (hα : Irrational α) : volume (sigmaAMO α) = 0 := by
  have hγ : Irrational (α / 2) := by simpa using hα.div_natCast (m := 2) two_ne_zero
  set γ := α / 2 with hγdef
  set b : ℝ → ℝ := fun x => 2 * Real.sin (2 * π * x) with hb
  have hLb : ∀ x y, |b x - b y| ≤ (4 * π) * |x - y| := by
    intro x y
    simp only [hb]
    rw [← mul_sub, abs_mul, abs_two]
    have := Real.abs_sin_sub_sin_le (2 * π * x) (2 * π * y)
    rw [← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at this
    nlinarith [this]
  have hZ : {x | b x = 0}.Countable := by
    refine (Set.countable_range (fun n : ℤ => (n : ℝ) / 2)).mono ?_
    intro x hx
    simp only [hb, Set.mem_setOf_eq] at hx
    have : Real.sin (2 * π * x) = 0 := by linarith
    obtain ⟨n, hn⟩ := Real.sin_eq_zero_iff.1 this
    refine ⟨n, ?_⟩
    have hπ := Real.pi_pos
    simp only
    field_simp
    nlinarith
  have hconv := measure_convergence' (v := fun _ => 0) (b := b) (bddFun_const 0)
    (bddFun_two_sin (2 * π)) (Kb := 4 * π) (Kv := 0) (by positivity) le_rfl hLb
    (by intro x y; simp) hZ periodic_two_sin (fun _ => rfl) ⟨0, by simp [hb]⟩ hγ
  have hle : ∀ ε : ℝ, 0 < ε → volume (sigmaM (fun _ => 0) b γ) ≤ ENNReal.ofReal ε := by
    intro ε hε
    refine isClosed_Iic.mem_of_frequently_of_tendsto ?_ hconv
    rw [Filter.frequently_atTop]
    intro N0
    obtain ⟨N1, hN1⟩ := exists_nat_gt (32 * π / ε)
    obtain ⟨n, hn, hodd⟩ := exists_odd_qN hγ (max N0 N1)
    refine ⟨n, le_of_max_le_left hn, ?_⟩
    haveI : NeZero (qN γ n) := ⟨by have := one_le_qN hγ n; omega⟩
    have hqpos := q_pos hγ n
    have hβ : ((qN γ n : ℕ) : ℝ) * (p γ n / q γ n) = (pZ γ n : ℝ) := by
      rw [qN_cast hγ, pZ_cast]; field_simp
    have h1 := volume_sigmaM_chiral_le_of_odd hodd (isCoprime_pZ_qN hγ n) hβ
    refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [qN_cast hγ]
    have hq := q_ge_half hγ n
    have hn1 : (N1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
    rw [div_le_iff₀ hqpos]
    have h2 : 32 * π / ε < n + 1 := by linarith
    rw [div_lt_iff₀ hε] at h2
    nlinarith
  have h0 : volume (sigmaM (fun _ => 0) b γ) = 0 := by
    refine le_antisymm ?_ zero_le
    refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    rw [zero_add]
    have := hle ε (by exact_mod_cast hε)
    rwa [ENNReal.ofReal_coe_nnreal] at this
  exact measure_mono_null (sigmaAMO_subset_chiral α) h0

end LastBound
end CAH

/-! ## Part D: even period

For `Q = 2N` the support of `P` also contains `S^{Q±N}T^{Q±N}`, so the abstract alignment
argument above is not available; instead the `E`-independent part `det(-Bloch)` is computed
explicitly (cf. [JKK, Lemmas 2–4, case II]): the Bloch matrix is bipartite, its determinant is
`(-1)^N |A_e + (-1)^{N-1} e(k) A_o|²` with `A_e = ∏ a_{2i}`, `A_o = ∏ a_{2i+1}`, and the moduli of
`A_e, A_o` are computed from the cyclotomic identity `∏_{i<M} (1 - xζ^i) = 1 - x^M`. -/

namespace CAH
namespace LastBound

open Real Matrix Complex Set MeasureTheory
open CAH.FB (bm cb per_cb bandFun sq01)
open scoped ComplexConjugate

/-! ### The `E`-dependence for arbitrary `Q` -/

lemma int_eq_zero_of_abs_mul_lt {Q : ℤ} (hQ : 0 < Q) {c : ℤ} (h : |Q * c| < Q) : c = 0 := by
  rw [abs_mul, abs_of_pos hQ] at h
  have : |c| < 1 := by
    by_contra h'; push Not at h'; nlinarith
  exact Int.abs_lt_one_iff.1 this

lemma support_E {Q : ℕ} [NeZero Q] {ω : ℂ} (hω0 : ω ≠ 0) (hω : ω ^ Q = 1)
    (hprim : ∀ n : ℤ, ω ^ n = 1 → (Q : ℤ) ∣ n) {m : Fin 3 →₀ ℕ}
    (hm : m ∈ (Pdet Q ω).support) (h2 : m 2 ≠ 0) : m 0 = Q ∧ m 1 = Q := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := dvd_of_mem_support hω0 hω hprim hm
  have hg := good_Pdet ω m hm
  have hQ : (0 : ℤ) < Q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  have hm2 : (1 : ℤ) ≤ m 2 := by
    have : 0 < m 2 := Nat.pos_of_ne_zero h2
    exact_mod_cast this
  have hs : |((m 0 : ℤ) - Q) + ((m 1 : ℤ) - Q)| < Q :=
    lt_of_le_of_lt (abs_add_le _ _) (by linarith)
  have hd : |((m 0 : ℤ) - Q) - ((m 1 : ℤ) - Q)| < Q :=
    lt_of_le_of_lt (abs_sub _ _) (by linarith)
  have ea : ((m 0 : ℤ) - Q) + ((m 1 : ℤ) - Q) = Q * (a - 2) := by linear_combination ha
  have eb : ((m 0 : ℤ) - Q) - ((m 1 : ℤ) - Q) = Q * b := by linear_combination hb
  rw [ea] at hs
  rw [eb] at hd
  have h1 := int_eq_zero_of_abs_mul_lt hQ hs
  have h2' := int_eq_zero_of_abs_mul_lt hQ hd
  have ha2 : a = 2 := by omega
  subst ha2; subst h2'
  constructor <;> omega

/-- For every `Q`, `det(E - G) - det(-G)` does not depend on `(s,t)`. -/
theorem chambers_E {Q : ℕ} [NeZero Q] {ω : ℂ} (hω0 : ω ≠ 0) (hω : ω ^ Q = 1)
    (hprim : ∀ n : ℤ, ω ^ n = 1 → (Q : ℤ) ∣ n) :
    ∃ Ψ : ℂ → ℂ, ∀ s t E : ℂ, s ≠ 0 → t ≠ 0 →
      ((E • (1 : Matrix (Fin Q) (Fin Q) ℂ)) - Gst Q ω s t).det =
        Ψ E + (((0 : ℂ) • (1 : Matrix (Fin Q) (Fin Q) ℂ)) - Gst Q ω s t).det := by
  classical
  set P := Pdet Q ω
  refine ⟨fun E => ∑ m ∈ P.support.filter (fun m => m 2 ≠ 0), P.coeff m * E ^ (m 2),
    fun s t E hs ht => ?_⟩
  have hE := eval_Pdet (Q := Q) ω s t E hs ht
  have h0 := eval_Pdet (Q := Q) ω s t 0 hs ht
  have hst : (s * t) ^ Q ≠ 0 := pow_ne_zero _ (mul_ne_zero hs ht)
  apply mul_left_cancel₀ hst
  rw [mul_add, ← hE, ← h0]
  suffices h : eval ![s, t, E] P - eval ![s, t, 0] P =
      (s * t) ^ Q * ∑ m ∈ P.support.filter (fun m => m 2 ≠ 0), P.coeff m * E ^ (m 2) by
    linear_combination h
  rw [eval_eq', eval_eq', ← Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun m hm => ?_
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  by_cases h : m 2 = 0
  · simp [h]
  · rw [if_pos h]
    obtain ⟨h0', h1'⟩ := support_E hω0 hω hprim hm h
    rw [h0', h1', zero_pow h]; ring

/-! ### A determinant of a cyclic bidiagonal matrix -/

open Fin.NatCast in
lemma det_cyc {N : ℕ} [NeZero N] (x y : Fin N → ℂ) :
    (of fun i j : Fin N => (if i = j then x i else 0) + (if i = j + 1 then y j else 0)).det =
      ∏ i, x i + (-1) ^ (N - 1) * ∏ i, y i := by
  by_cases hN1 : N = 1
  · subst hN1
    rw [Matrix.det_fin_one]
    have h01 : (0 : Fin 1) = 0 + 1 := rfl
    simp [Fin.prod_univ_one, ← h01]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 2 := ⟨N - 2, by have := NeZero.pos N; omega⟩
  set M := (of fun i j : Fin (n + 2) =>
    (if i = j then x i else 0) + (if i = j + 1 then y j else 0))
  have hne : ∀ i : Fin (n + 2), i ≠ i + 1 := fun i h => by
    have : (1 : Fin (n + 2)) = 0 := by
      have := congrArg (fun z => z - i) h; simpa using this.symm
    exact absurd this (by simp)
  have hne' : ∀ i : Fin (n + 2), i + 1 ≠ i := fun i h => hne i h.symm
  rw [det_apply, Fintype.sum_eq_add 1 (finRotate (n + 2))]
  · rw [Equiv.Perm.sign_one, one_smul, sign_finRotate]
    have e1 : ∏ i, M ((1 : Equiv.Perm (Fin (n + 2))) i) i = ∏ i, x i :=
      Finset.prod_congr rfl fun i _ => by simp [M, hne i]
    have e2 : ∏ i, M (finRotate (n + 2) i) i = ∏ i, y i :=
      Finset.prod_congr rfl fun i _ => by
        rw [finRotate_apply]; simp [M, hne' i]
    rw [e1, e2, Units.smul_def]
    push_cast
    simp
  · intro h
    have := congrArg (fun σ : Equiv.Perm (Fin (n + 2)) => σ 0) h
    rw [finRotate_apply] at this
    simp at this
  · rintro σ ⟨h1, h2⟩
    suffices hp : ∏ i, M (σ i) i = 0 by rw [hp, smul_zero]
    by_contra hp
    have hall : ∀ i, σ i = i ∨ σ i = i + 1 := fun i => by
      by_contra hc
      push Not at hc
      exact hp (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [M, hc.1, hc.2]))
    obtain ⟨j0, hj0⟩ : ∃ j0, σ j0 ≠ j0 := by
      by_contra h; push Not at h; exact h1 (Equiv.ext h)
    have hj0' : σ j0 = j0 + 1 := (hall j0).resolve_left hj0
    have key : ∀ m : ℕ, σ (j0 + (m : Fin (n + 2))) = j0 + (m : Fin (n + 2)) + 1 := by
      intro m
      induction m with
      | zero => simpa using hj0'
      | succ m ih =>
        rcases hall (j0 + ((m + 1 : ℕ) : Fin (n + 2))) with h | h
        · exfalso
          have e : σ (j0 + ((m + 1 : ℕ) : Fin (n + 2))) = σ (j0 + (m : Fin (n + 2))) := by
            rw [h, ih, Nat.cast_succ, add_assoc]
          have := σ.injective e
          push_cast at this
          exact hne' _ (by rw [← add_assoc] at this; exact this)
        · rw [h]
    apply h2
    ext i
    rw [finRotate_apply]
    have := key (i - j0).val
    rw [Fin.cast_val_eq_self, add_sub_cancel] at this
    rw [this]

/-! ### The bipartite structure of the Bloch matrix for `Q = 2N` -/

variable {N : ℕ} [NeZero N]

/-- `(i, b) ↦ 2i + b`. -/
abbrev fpe (N : ℕ) : Fin N × Fin 2 ≃ Fin (N * 2) := finProdFinEquiv

lemma fpe_val (i : Fin N) (b : Fin 2) : ((fpe N (i, b) : Fin (N * 2)) : ℕ) = b + 2 * i := rfl

lemma Bc_parity (a : ℤ → ℝ) (k : ℝ) (r c : Fin (N * 2)) (h : (r : ℕ) % 2 = (c : ℕ) % 2) :
    Bc a k r c = 0 := by
  have h1 : c ≠ r + 1 := by
    intro e
    have := (eq_add_one_iff r c).1 e
    split_ifs at this with h' <;> omega
  have h2 : r ≠ c + 1 := by
    intro e
    have := (eq_add_one_iff c r).1 e
    split_ifs at this with h' <;> omega
  simp [Bc, h1, h2]

/-- The upper off-diagonal block (even rows, odd columns). -/
def blkB (a : ℤ → ℝ) (k : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => Bc a k (fpe N (i, 0)) (fpe N (j, 1))
/-- The lower off-diagonal block (odd rows, even columns). -/
def blkC (a : ℤ → ℝ) (k : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => Bc a k (fpe N (i, 1)) (fpe N (j, 0))

lemma det_Bc_blocks (a : ℤ → ℝ) (k : ℝ) :
    (Bc (Q := N * 2) a k).det =
      (-1) ^ N * ((blkB (N := N) a k).det * (blkC (N := N) a k).det) := by
  set σ : Equiv.Perm (Fin N × Fin 2) := Equiv.prodCongrRight (fun _ => Equiv.swap 0 1)
  have hblk : ((Bc (Q := N * 2) a k).submatrix (fpe N) (fpe N)).submatrix id σ =
      blockDiagonal ![blkB (N := N) a k, blkC (N := N) a k] := by
    ext ⟨i, b⟩ ⟨j, b'⟩
    rw [blockDiagonal_apply']
    simp only [submatrix_apply, id, σ, Equiv.prodCongrRight_apply]
    fin_cases b <;> fin_cases b'
    · simp [blkB, Equiv.swap_apply_left]
    · simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Equiv.swap_apply_right, zero_ne_one,
        ↓reduceIte]
      exact Bc_parity a k _ _ (by rw [fpe_val, fpe_val]; simp <;> omega)
    · simp only [Fin.mk_one, Fin.zero_eta, Fin.isValue, Equiv.swap_apply_left, one_ne_zero,
        ↓reduceIte]
      exact Bc_parity a k _ _ (by rw [fpe_val, fpe_val]; simp <;> omega)
    · simp [blkC, Equiv.swap_apply_right]
  have hsign : (Equiv.Perm.sign σ : ℂ) = (-1) ^ N := by
    rw [Equiv.Perm.sign_prodCongrRight]
    simp [Equiv.Perm.sign_swap (show (0 : Fin 2) ≠ 1 by decide)]
  have := det_permute' σ ((Bc (Q := N * 2) a k).submatrix (fpe N) (fpe N))
  rw [hblk, det_blockDiagonal, Fin.prod_univ_two, det_submatrix_equiv_self, hsign] at this
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at this
  rw [this, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  simp

lemma fpe_add_one_eq (i j : Fin N) : fpe N (j, 1) = fpe N (i, 0) + 1 ↔ i = j := by
  rw [eq_add_one_iff, fpe_val, fpe_val, Fin.ext_iff]
  split_ifs with h
  · simp at h; omega
  · simp; omega

lemma fpe_add_one_eq' (i j : Fin N) (b : Fin 2) (hb : b = 0 ∨ b = 1) :
    fpe N (i, 0) = fpe N (j, 1) + 1 ↔ i = j + 1 := by
  rw [eq_add_one_iff, fpe_val, fpe_val, Fin.ext_iff, val_add_one']
  have hj := j.2
  split_ifs with h1 h2 h2 <;> simp at * <;> omega

lemma fpe_add_one_eq'' (i j : Fin N) : fpe N (j, 0) = fpe N (i, 1) + 1 ↔ j = i + 1 := by
  rw [eq_add_one_iff, fpe_val, fpe_val, Fin.ext_iff, val_add_one']
  have hi := i.2
  split_ifs with h1 h2 h2 <;> simp at * <;> omega

lemma fpe_add_one_eq''' (i j : Fin N) : fpe N (i, 1) = fpe N (j, 0) + 1 ↔ i = j := by
  rw [eq_add_one_iff, fpe_val, fpe_val, Fin.ext_iff]
  split_ifs with h
  · simp at h; omega
  · simp; omega

lemma ph_even (k : ℝ) (i : Fin N) : ph k (fpe N (i, 0)) = 1 := by
  unfold ph; rw [if_neg]; rw [fpe_val]; simp; omega

/-- The boundary phases of the odd bonds. -/
def phO (k : ℝ) (j : Fin N) : ℂ := ph k (fpe N (j, 1))

lemma prod_phO (k : ℝ) : ∏ j : Fin N, phO k j = FB.ex k := by
  have hN := NeZero.pos N
  have : ∀ j : Fin N, phO k j = if j = ⟨N - 1, by omega⟩ then FB.ex k else 1 := by
    intro j
    unfold phO ph
    rw [fpe_val]
    congr 1
    apply propext
    rw [Fin.ext_iff]; simp; omega
  rw [Finset.prod_congr rfl fun j _ => this j, Finset.prod_ite_eq']
  simp

lemma blkB_eq (a : ℤ → ℝ) (k : ℝ) :
    blkB a k = of fun i j : Fin N => (if i = j then (a ((fpe N (i, 0) : ℕ) : ℤ) : ℂ) else 0) +
      (if i = j + 1 then conj (phO k j) * (a ((fpe N (j, 1) : ℕ) : ℤ) : ℂ) else 0) := by
  ext i j
  simp only [blkB, Bc, of_apply, phO]
  rw [ph_even]
  congr 1
  · by_cases h : i = j
    · rw [if_pos ((fpe_add_one_eq i j).2 h), if_pos h, one_mul]
    · rw [if_neg (fun h' => h ((fpe_add_one_eq i j).1 h')), if_neg h]
  · by_cases h : i = j + 1
    · rw [if_pos ((fpe_add_one_eq' i j 0 (Or.inl rfl)).2 h), if_pos h]
    · rw [if_neg (fun h' => h ((fpe_add_one_eq' i j 0 (Or.inl rfl)).1 h')), if_neg h]

lemma blkC_transpose_eq (a : ℤ → ℝ) (k : ℝ) :
    (blkC a k)ᵀ = of fun i j : Fin N => (if i = j then (a ((fpe N (i, 0) : ℕ) : ℤ) : ℂ) else 0) +
      (if i = j + 1 then phO k j * (a ((fpe N (j, 1) : ℕ) : ℤ) : ℂ) else 0) := by
  ext i j
  simp only [transpose_apply, blkC, Bc, of_apply, phO]
  rw [ph_even, map_one, one_mul, add_comm]
  congr 1
  · by_cases h : i = j
    · rw [if_pos ((fpe_add_one_eq''' j i).2 h.symm), if_pos h, h]
    · rw [if_neg (fun h' => h ((fpe_add_one_eq''' j i).1 h').symm), if_neg h]
  · by_cases h : i = j + 1
    · rw [if_pos ((fpe_add_one_eq'' j i).2 h), if_pos h]
    · rw [if_neg (fun h' => h ((fpe_add_one_eq'' j i).1 h')), if_neg h]

/-- Product of the even bonds. -/
def AEr (N : ℕ) (a : ℤ → ℝ) : ℝ := ∏ i : Fin N, a ((fpe N (i, 0) : ℕ) : ℤ)
/-- Product of the odd bonds. -/
def AOr (N : ℕ) (a : ℤ → ℝ) : ℝ := ∏ i : Fin N, a ((fpe N (i, 1) : ℕ) : ℤ)

/-- `det(Bloch) = (-1)^N |A_e + (-1)^{N-1} e(k) A_o|²` for `Q = 2N`. -/
lemma det_Bc_even (a : ℤ → ℝ) (k : ℝ) :
    (Bc (Q := N * 2) a k).det = (-1) ^ N *
      (Complex.normSq ((AEr N a : ℂ) + ((-1 : ℝ) ^ (N - 1) : ℝ) * FB.ex k * (AOr N a : ℂ)) : ℂ) := by
  rw [det_Bc_blocks, ← det_transpose (blkC (N := N) a k), blkB_eq, blkC_transpose_eq, det_cyc,
    det_cyc]
  set z : ℂ := (AEr N a : ℂ) + ((-1 : ℝ) ^ (N - 1) : ℝ) * FB.ex k * (AOr N a : ℂ) with hz
  have hC : ∏ i : Fin N, (a ((fpe N (i, 0) : ℕ) : ℤ) : ℂ) +
      (-1) ^ (N - 1) * ∏ j : Fin N, (phO k j * (a ((fpe N (j, 1) : ℕ) : ℤ) : ℂ)) = z := by
    rw [Finset.prod_mul_distrib, prod_phO, hz, AEr, AOr]
    push_cast; ring
  have hB : ∏ i : Fin N, (a ((fpe N (i, 0) : ℕ) : ℤ) : ℂ) +
      (-1) ^ (N - 1) * ∏ j : Fin N, (conj (phO k j) * (a ((fpe N (j, 1) : ℕ) : ℤ) : ℂ)) =
      conj z := by
    rw [Finset.prod_mul_distrib, ← map_prod, prod_phO, hz, AEr, AOr]
    simp only [map_add, map_mul, map_prod, Complex.conj_ofReal, FB.conj_ex]
    push_cast
    ring
  rw [hB, hC, mul_comm (conj z), Complex.mul_conj]

/-! ### Moduli of the products of bonds -/

lemma norm_two_sin (y : ℝ) : ‖((2 * Real.sin (2 * π * y) : ℝ) : ℂ)‖ = ‖1 - FB.ex (2 * y)‖ := by
  rw [two_sin_ex, norm_mul, norm_neg, Complex.norm_I, one_mul,
    show FB.ex y - FB.ex (-y) = FB.ex (-y) * (FB.ex (2 * y) - 1) by
      rw [mul_sub, ← FB.ex_add, mul_one]; ring_nf,
    norm_mul, FB.norm_ex, one_mul, norm_sub_rev]

lemma prod_one_sub_of_prim {M : ℕ} (hM : 0 < M) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ M) (x : ℂ) :
    ∏ i ∈ Finset.range M, (1 - x * ζ ^ i) = 1 - x ^ M := by
  have h := X_pow_sub_C_eq_prod hζ hM (rfl : x ^ M = x ^ M)
  have := congrArg (Polynomial.eval 1) h
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
    Polynomial.eval_prod, one_pow] at this
  rw [this]
  exact Finset.prod_congr rfl fun i _ => by ring

lemma ex_prim {p : ℤ} {M : ℕ} (hM : M ≠ 0) (hcop : IsCoprime p (M : ℤ)) {t : ℝ}
    (ht : (M : ℝ) * t = p) : IsPrimitiveRoot (FB.ex t) M := by
  have := Complex.isPrimitiveRoot_exp_of_isCoprime p M hM hcop
  unfold FB.ex
  convert this using 3
  have hM' : (M : ℝ) ≠ 0 := by exact_mod_cast hM
  have : t = p / M := by field_simp; linarith
  rw [this]; push_cast; ring

lemma abs_bond (β θ : ℝ) (n : ℤ) : |bond β θ n| = ‖1 - FB.ex (2 * (θ + n * β))‖ := by
  rw [← norm_two_sin, bond_apply, Complex.norm_real, Real.norm_eq_abs]

lemma abs_AEr (β θ : ℝ) :
    |AEr N (bond β θ)| = ‖∏ i ∈ Finset.range N, (1 - FB.ex (2 * θ) * FB.ex (4 * β) ^ i)‖ := by
  rw [AEr, Finset.abs_prod, norm_prod,
    ← Fin.prod_univ_eq_prod_range (fun i => ‖1 - FB.ex (2 * θ) * FB.ex (4 * β) ^ i‖)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [abs_bond, ex_pow, ← FB.ex_add, fpe_val]
  congr 3; push_cast; simp only [Fin.val_zero, Nat.cast_zero]; ring

lemma AOr_eq (β θ : ℝ) : AOr N (bond β θ) = AEr N (bond β (θ + β)) := by
  unfold AOr AEr
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [bond_apply, bond_apply, fpe_val, fpe_val]
  congr 2; push_cast; simp only [Fin.val_zero, Fin.val_one, Nat.cast_zero, Nat.cast_one]; ring

lemma isCoprime_of_two {p : ℤ} (hcop : IsCoprime p ((N * 2 : ℕ) : ℤ)) : IsCoprime p (N : ℤ) := by
  push_cast at hcop; exact hcop.of_mul_right_left

lemma odd_of_coprime {p : ℤ} (hcop : IsCoprime p ((N * 2 : ℕ) : ℤ)) : Odd p := by
  push_cast at hcop
  have h2 : IsCoprime p 2 := hcop.of_mul_right_right
  by_contra h
  obtain ⟨m, hm⟩ := Int.not_odd_iff_even.1 h
  rw [hm, ← two_mul] at h2
  have := (isCoprime_self.1 h2.of_mul_left_left)
  rcases Int.isUnit_iff.1 this with h | h <;> norm_num at h

lemma ex_half_odd {p : ℤ} (hp : Odd p) : FB.ex (p / 2) = -1 := by
  obtain ⟨m, rfl⟩ := hp
  rw [show (((2 * m + 1 : ℤ) : ℝ) / 2) = (m : ℤ) + 1 / 2 by push_cast; ring, FB.ex_add,
    FB.ex_int, one_mul]
  unfold FB.ex
  rw [show 2 * ↑π * I * (((1 / 2 : ℝ)) : ℂ) = π * I by push_cast; ring, Complex.exp_pi_mul_I]

lemma abs_AEr_odd (hN : Odd N) {p : ℤ} (hcop : IsCoprime p ((N * 2 : ℕ) : ℤ)) {β : ℝ}
    (hβ : ((N * 2 : ℕ) : ℝ) * β = p) (θ : ℝ) :
    |AEr N (bond β θ)| = ‖1 - FB.ex (2 * N * θ)‖ := by
  have hc2 : IsCoprime (2 * p) (N : ℤ) := by
    refine IsCoprime.mul_left ?_ (isCoprime_of_two hcop)
    rw [Int.isCoprime_iff_gcd_eq_one]
    have : Nat.Coprime 2 N := Nat.coprime_two_left.2 hN
    simpa [Int.gcd] using this
  have hζ := ex_prim (NeZero.ne N) hc2 (t := 4 * β) (by push_cast at hβ ⊢; linear_combination 2 * hβ)
  rw [abs_AEr, prod_one_sub_of_prim (NeZero.pos N) hζ, ex_pow]
  congr 3; ring

lemma abs_AEr_even (hN : Even N) {p : ℤ} (hcop : IsCoprime p ((N * 2 : ℕ) : ℤ)) {β : ℝ}
    (hβ : ((N * 2 : ℕ) : ℝ) * β = p) (θ : ℝ) :
    |AEr N (bond β θ)| = ‖1 - FB.ex (N * θ)‖ ^ 2 := by
  obtain ⟨M, hM⟩ := hN
  have hM2 : N = 2 * M := by omega
  have hMpos : 0 < M := by have := NeZero.pos N; omega
  have hcM : IsCoprime p (M : ℤ) := by
    have := isCoprime_of_two hcop
    rw [hM2] at this; push_cast at this; exact this.of_mul_right_right
  have hζ := ex_prim (M := M) (by omega) hcM (t := 4 * β)
    (by rw [hM2] at hβ; push_cast at hβ ⊢; linear_combination hβ)
  rw [abs_AEr, hM, Finset.prod_range_add]
  have hper : ∀ x ∈ Finset.range M, (1 - FB.ex (2 * θ) * FB.ex (4 * β) ^ (M + x)) =
      (1 - FB.ex (2 * θ) * FB.ex (4 * β) ^ x) := fun x _ => by
    rw [pow_add, hζ.pow_eq_one, one_mul]
  rw [Finset.prod_congr rfl hper, prod_one_sub_of_prim hMpos hζ, norm_mul, ← sq, ex_pow]
  congr 4; push_cast; ring

/-- The alignment step for even period. -/
lemma align_even (x y x₁ y₁ s : ℝ) (hs : |s| = 1) (h_eq : |x₁| = |y₁|)
    (h_le : |x| + |y| ≤ |x₁| + |y₁|) (k : ℝ) :
    ∃ k', Complex.normSq ((x : ℂ) + (s : ℂ) * FB.ex k * y) =
      Complex.normSq ((x₁ : ℂ) + (s : ℂ) * FB.ex k' * y₁) := by
  set v := ‖(x : ℂ) + (s : ℂ) * FB.ex k * y‖
  set f : ℝ → ℝ := fun k' => ‖(x₁ : ℂ) + (s : ℂ) * FB.ex k' * y₁‖ with hf
  have hfc : Continuous f := by simp only [hf]; fun_prop
  have hv0 : 0 ≤ v := norm_nonneg _
  have hv1 : v ≤ 2 * |x₁| := by
    calc v ≤ ‖(x : ℂ)‖ + ‖(s : ℂ) * FB.ex k * y‖ := norm_add_le _ _
      _ = |x| + |y| := by
          rw [norm_mul, norm_mul, FB.norm_ex, Complex.norm_real, Complex.norm_real,
            Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, hs]; ring
      _ ≤ 2 * |x₁| := by linarith
  have hhalf : FB.ex (1 / 2) = -1 := by
    have := ex_half_odd (p := 1) odd_one; simpa using this
  have hf0 : f 0 = |x₁ + s * y₁| := by
    simp only [hf, FB.ex_zero, mul_one]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
  have hf1 : f (1 / 2) = |x₁ - s * y₁| := by
    simp only [hf, hhalf, mul_neg, mul_one, neg_mul]
    rw [← Complex.ofReal_mul, ← sub_eq_add_neg, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
  have hsy : |s * y₁| = |x₁| := by rw [abs_mul, hs, one_mul, h_eq]
  have hmem : v ∈ Set.uIcc (f 0) (f (1 / 2)) := by
    rw [hf0, hf1]
    rcases abs_eq_abs.1 hsy with h | h
    · rw [h, sub_self, abs_zero, show x₁ + x₁ = 2 * x₁ by ring, abs_mul, abs_two]
      exact Set.mem_uIcc.2 (Or.inr ⟨hv0, hv1⟩)
    · rw [h, show x₁ + -x₁ = 0 by ring, abs_zero, show x₁ - -x₁ = 2 * x₁ by ring, abs_mul,
        abs_two]
      exact Set.mem_uIcc.2 (Or.inl ⟨hv0, hv1⟩)
  obtain ⟨k', -, hk'⟩ := intermediate_value_uIcc hfc.continuousOn hmem
  refine ⟨k', ?_⟩
  rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  simp only [hf] at hk'
  rw [hk']

end LastBound
end CAH

/-! ## Part E: Last's bound for all denominators -/

namespace CAH
namespace LastBound

open Real Matrix Complex Set MeasureTheory
open CAH.FB (bm bandFun sq01 cb)

/-- The two facts about `θ₁ = 1/(4N) + nβ` used in the even-period alignment. -/
lemma even_facts {N : ℕ} [NeZero N] {p : ℤ} (hcop : IsCoprime p ((N * 2 : ℕ) : ℤ)) {β : ℝ}
    (hβ : ((N * 2 : ℕ) : ℝ) * β = p) (n : ℤ) :
    |AEr N (bond β (1 / (4 * N) + n * β))| = |AOr N (bond β (1 / (4 * N) + n * β))| ∧
      ∀ θ, |AEr N (bond β θ)| + |AOr N (bond β θ)| ≤
        |AEr N (bond β (1 / (4 * N) + n * β))| + |AOr N (bond β (1 / (4 * N) + n * β))| := by
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hp := odd_of_coprime hcop
  have hNβ : (N : ℝ) * β = p / 2 := by push_cast at hβ; linarith
  simp only [AOr_eq]
  rcases Nat.even_or_odd N with hNe | hNo
  · simp only [abs_AEr_even hNe hcop hβ]
    have hsq : ∀ w : ℂ, ‖w‖ = 1 → ‖1 - w‖ ^ 2 = 2 - 2 * w.re := fun w hw => by
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      have := Complex.normSq_eq_norm_sq w; rw [hw, Complex.normSq_apply] at this
      simp; nlinarith
    have hsq' : ∀ w : ℂ, ‖w‖ = 1 → ‖1 - -w‖ ^ 2 = 2 + 2 * w.re := fun w hw => by
      have := hsq (-w) (by rw [norm_neg, hw]); rw [this]; simp
    have hshift : ∀ θ, FB.ex (N * (θ + β)) = -FB.ex (N * θ) := fun θ => by
      rw [mul_add, FB.ex_add, hNβ, ex_half_odd hp, mul_neg_one]
    have hre : (FB.ex (N * (1 / (4 * N) + n * β))).re = 0 := by
      rw [show (N : ℝ) * (1 / (4 * N) + n * β) = 1 / 4 + n * (p / 2) by
        rw [mul_add, show (N : ℝ) * (1 / (4 * N)) = 1 / 4 by field_simp,
          show (N : ℝ) * (n * β) = n * (N * β) by ring, hNβ]]
      unfold FB.ex
      rw [show 2 * ↑π * I * (((1 / 4 + ↑n * (↑p / 2)) : ℝ) : ℂ) =
        ((π / 2 + (n * p : ℤ) * π : ℝ) : ℂ) * I by push_cast; ring, exp_ofReal_mul_I_re,
        Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two, Real.sin_int_mul_pi]
      ring
    refine ⟨?_, fun θ => ?_⟩
    · rw [hshift, hsq _ (FB.norm_ex _), hsq' _ (FB.norm_ex _), hre]; norm_num
    · rw [hshift, hshift, hsq _ (FB.norm_ex _), hsq' _ (FB.norm_ex _), hsq _ (FB.norm_ex _),
        hsq' _ (FB.norm_ex _)]
      linarith
  · simp only [abs_AEr_odd hNo hcop hβ]
    have hshift : ∀ θ, FB.ex (2 * N * (θ + β)) = FB.ex (2 * N * θ) := fun θ => by
      rw [show 2 * (N : ℝ) * (θ + β) = 2 * N * θ + (p : ℤ) by push_cast; linarith, FB.ex_add,
        FB.ex_int, mul_one]
    have hle : ∀ w : ℂ, ‖w‖ = 1 → ‖1 - w‖ ≤ 2 := fun w hw => by
      calc ‖1 - w‖ ≤ ‖(1 : ℂ)‖ + ‖w‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_one, hw]; norm_num
    have h1 : FB.ex (2 * N * (1 / (4 * N) + n * β)) = -1 := by
      rw [show 2 * (N : ℝ) * (1 / (4 * N) + n * β) = (n * p : ℤ) + 1 / 2 by
        rw [mul_add, show 2 * (N : ℝ) * (1 / (4 * N)) = 1 / 2 by field_simp; ring,
          show 2 * (N : ℝ) * (n * β) = 2 * n * (N * β) by ring, hNβ]; push_cast; ring,
        FB.ex_add, FB.ex_int, one_mul]
      have := ex_half_odd (p := 1) odd_one; simpa using this
    refine ⟨by rw [hshift], fun θ => ?_⟩
    rw [hshift, hshift, h1]
    have := hle _ (FB.norm_ex (2 * N * θ))
    norm_num
    linarith

/-- **Last-type bound for the chiral operator, even period** ([JKK, Theorem 1, case II]). -/
theorem volume_sigmaM_chiral_le_of_even {N : ℕ} [NeZero N] {p : ℤ}
    (hcop : IsCoprime p ((N * 2 : ℕ) : ℤ)) {β : ℝ} (hβ : ((N * 2 : ℕ) : ℝ) * β = p) :
    volume (sigmaM (fun _ => 0) (fun x => 2 * Real.sin (2 * π * x)) β) ≤
      ENNReal.ofReal (16 * π / (N * 2 : ℕ)) := by
  obtain ⟨Ψ, hΨ⟩ := chambers_E (Q := N * 2) (ex_ne_zero β) (ex_pow_Q hβ) (prim_of_coprime hcop hβ)
  set s : ℝ := (-1) ^ (N - 1)
  have hs : |s| = 1 := by simp [s]
  set z : ℝ → ℝ → ℂ := fun θ k =>
    (AEr N (bond β θ) : ℂ) + (s : ℂ) * FB.ex k * (AOr N (bond β θ) : ℂ) with hz
  have hdiag : ∀ k : ℝ, ∀ i : Fin (N * 2), FB.ex ((i : ℕ) * k / (N * 2 : ℕ)) *
      FB.ex (-((i : ℕ) * k / (N * 2 : ℕ))) = 1 := fun k i => by
    rw [← FB.ex_add, add_neg_cancel, FB.ex_zero]
  have hspec : ∀ θ k (E : ℝ), E ∈ spectrum ℝ (Bc (Q := N * 2) (bond β θ) k) ↔
      Ψ E + (-1) ^ N * (Complex.normSq (z θ k) : ℂ) = 0 := by
    intro θ k E
    rw [mem_spectrum_iff_det, Bc_eq_gauge, det_conj_diag _ _ _ (hdiag k),
      hΨ _ _ _ (ex_ne_zero _) (ex_ne_zero _), ← det_conj_diag _ _ _ (hdiag k) (0 : ℂ),
      ← Bc_eq_gauge, zero_smul, zero_sub, det_neg, Fintype.card_fin,
      Even.neg_one_pow ⟨N, by ring⟩, one_mul, det_Bc_even]
  have hN : (N : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne N
  obtain ⟨n, hn⟩ := exists_small_bond hcop hβ (1 / (4 * N) + ((N * 2 - 1 : ℕ) : ℝ) * β)
  set θ₁ := 1 / (4 * N) + n * β with hθ₁
  obtain ⟨h_eq, h_max⟩ := even_facts hcop hβ n
  have hFall : ∀ θ k, ∃ k', Complex.normSq (z θ k) = Complex.normSq (z θ₁ k') := fun θ k =>
    align_even _ _ _ _ s hs h_eq (h_max θ) k
  obtain ⟨lo, hi, hle, hlen, hcov⟩ := fibre_cover (Q := N * 2) (bond β θ₁)
  have hsmall : |bond β θ₁ ((N * 2 - 1 : ℕ) : ℤ)| ≤ 4 * π / (N * 2 : ℕ) := by
    rw [bond_apply]
    have e : θ₁ + (((N * 2 - 1 : ℕ) : ℤ) : ℝ) * β =
        1 / (4 * N) + ((N * 2 - 1 : ℕ) : ℝ) * β + n * β := by
      rw [hθ₁]; push_cast; ring
    rw [e]; exact hn
  have hsub : sigmaM (fun _ => 0) (fun x => 2 * Real.sin (2 * π * x)) β ⊆
      ⋃ j, Icc (lo j) (hi j) := by
    rw [FB.sigmaM_eq_bands (Q := N * 2) (bddFun_const 0) (bddFun_two_sin (2 * π))
      continuous_const continuous_two_sin (fun _ => rfl) periodic_two_sin hβ]
    intro E hE
    obtain ⟨j, x, -, rfl⟩ : ∃ j, ∃ x ∈ sq01,
        bandFun (N * 2) (fun _ => 0) (fun x => 2 * Real.sin (2 * π * x)) β j x = E := by
      simpa only [mem_iUnion, mem_image] using hE
    have hmem : bandFun (N * 2) (fun _ => 0) (fun x => 2 * Real.sin (2 * π * x)) β j x ∈
        spectrum ℝ (Bc (Q := N * 2) (bond β x.1) x.2) := by
      rw [Flow.spectrum_eq_range_eig (Bc_herm hβ x.1 x.2)]
      refine ⟨j, ?_⟩
      rw [← bm_bond_eq hβ]
      rfl
    have h0 := (hspec _ _ _).1 hmem
    obtain ⟨k', hk'⟩ := hFall x.1 x.2
    exact hcov k' ((hspec _ _ _).2 (by rw [← hk']; exact h0))
  calc volume (sigmaM (fun _ => 0) (fun x => 2 * Real.sin (2 * π * x)) β)
      ≤ volume (⋃ j, Icc (lo j) (hi j)) := measure_mono hsub
    _ ≤ ∑ j, volume (Icc (lo j) (hi j)) := measure_iUnion_fintype_le _ _
    _ = ∑ j, ENNReal.ofReal (hi j - lo j) := by simp only [Real.volume_Icc]
    _ = ENNReal.ofReal (∑ j, (hi j - lo j)) :=
        (ENNReal.ofReal_sum_of_nonneg fun j _ => sub_nonneg.2 (hle j)).symm
    _ ≤ ENNReal.ofReal (16 * π / (N * 2 : ℕ)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc ∑ j, (hi j - lo j) ≤ 4 * |bond β θ₁ ((N * 2 - 1 : ℕ) : ℤ)| := hlen
          _ ≤ 4 * (4 * π / (N * 2 : ℕ)) := by linarith
          _ = 16 * π / (N * 2 : ℕ) := by ring

/-- **Last-type bound for the chiral operator** `Ĥ` (all periods): for `Q ≥ 1`, `Qβ = p`,
`gcd(p, Q) = 1`, `|σ(M̂_β)| ≤ 16π/Q`. -/
theorem volume_sigmaM_chiral_le {Q : ℕ} (hQ : 1 ≤ Q) {p : ℤ} (hcop : IsCoprime p (Q : ℤ))
    {β : ℝ} (hβ : (Q : ℝ) * β = p) :
    volume (sigmaM (fun _ => 0) (fun x => 2 * Real.sin (2 * π * x)) β) ≤
      ENNReal.ofReal (16 * π / Q) := by
  rcases Nat.even_or_odd Q with ⟨N, hN⟩ | hodd
  · have hN' : Q = N * 2 := by omega
    subst hN'
    haveI : NeZero N := ⟨by rintro rfl; simp at hQ⟩
    exact volume_sigmaM_chiral_le_of_even hcop hβ
  · haveI : NeZero Q := ⟨by omega⟩
    exact volume_sigmaM_chiral_le_of_odd hodd hcop hβ

/-- **Last's bound (1.6)** ([L]; constant `16π` via the chiral-gauge argument of [JKK]): for
coprime `p, q` with `q ≥ 1`, `|σ(M_{p/q})| ≤ 16π/q`. -/
theorem volume_sigmaAMO_le {p : ℤ} {q : ℕ} (hq : 1 ≤ q) (hcop : IsCoprime p (q : ℤ)) :
    volume (sigmaAMO (p / q)) ≤ ENNReal.ofReal (16 * π / q) := by
  rcases Nat.even_or_odd q with hqe | hqo
  · -- `p` is odd; use `β = p/(2q)`, period `2q`
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    have hp : Odd p := by
      obtain ⟨r, hr⟩ := hqe
      by_contra h
      obtain ⟨m, hm⟩ := Int.not_odd_iff_even.1 h
      have h2 : IsCoprime (2 * m) (2 * (r : ℤ)) := by
        rw [show 2 * m = p by omega, show 2 * (r : ℤ) = q by rw [hr]; push_cast; ring]
        exact hcop
      have := isCoprime_self.1 (h2.of_mul_left_left.of_mul_right_left)
      rcases Int.isUnit_iff.1 this with h | h <;> norm_num at h
    have hcop2 : IsCoprime p ((q * 2 : ℕ) : ℤ) := by
      push_cast
      refine hcop.mul_right ?_
      rw [Int.isCoprime_iff_gcd_eq_one]
      obtain ⟨m, rfl⟩ := hp
      simp [Int.gcd] <;> omega
    refine (measure_mono (sigmaAMO_subset_chiral _)).trans
      ((volume_sigmaM_chiral_le (Q := q * 2) (by omega) hcop2 (by push_cast; field_simp)).trans
        (ENNReal.ofReal_le_ofReal ?_))
    have : (0 : ℝ) < q := by positivity
    push_cast
    rw [div_le_div_iff₀ (by positivity) this]
    nlinarith [Real.pi_pos]
  · exact volume_sigmaAMO_le_of_odd hqo hcop

end LastBound
end CAH
