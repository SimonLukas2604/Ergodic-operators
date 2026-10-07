/-
Copyright (c) 2026. Formalization of
  S. Becker, S. Jitomirskaya, I. Krasovsky, "Critical almost Mathieu operator: hidden
  singularity, gap continuity, and the Hausdorff dimension of the spectrum"
  (arXiv:1909.04429v2).

# Spectral consequence of the chiral gauge  (paper §3, Theorem 3.1; used in §7, tex l. 1784–1789)

We prove
`amo_spectrum_subset_chiral : σ(H_{α,θ}) ⊆ closure (⋃ₓ σ(Ĥ_{α/2,x}))`
for every `α, θ ∈ ℝ`, as a consequence of Theorem 3.1 (`ChiralGauge.chiral_representation`) at
frequency `α/2`: on even sites `T² + T⁻² + S + S⁻¹` has fibres `H_{α,θ}`, and
`Q = U_1 R U_{1/2}` intertwines it with the decomposable operator with fibres
`H̃_{α/2,β} = Ĥ_{α/2,1/4+α/4+β}`.

## Method (approximate eigenvectors; no direct-integral theory)
1. `E ∈ σ(H_{α,θ})` gives a finitely supported `u ≠ 0` with `‖(H_{α,θ} - E)u‖ ≤ ε‖u‖`
   (`CAH.exists_approx_eigen`, `CAH.exists_finsupp_approx` from `AMSCore`).
2. `Φ(2j,β) = g(β) u(j)`, `Φ(2j+1,β) = 0` with the trigonometric polynomial
   `g(β) = ∑_{k<L} e(k(β-θ))`, which satisfies `|g(β)(e(β-θ) - 1)| ≤ 2` and `∫|g|² = L`.
   Then `‖(T²+T⁻²+S+S⁻¹-E)Φ‖² ≤ (2ε² + 32/L)‖Φ‖²` in `L²(𝕋;ℓ²(ℤ))` (`nrm_Y_le`, `nrm_Phi`).
3. On even-supported trigonometric polynomials (`ERep`) `Q` is isometric (`nrm_opQ`);
   this uses the Plancherel identity for trigonometric polynomials (`parseval`) and the
   isometry of `R` (`nrm_opR`).
4. Averaging over `β` gives a fibre `β` with `‖(Ĥ_{α/2,x} - E)v‖ < δ‖v‖`, `v = (QΦ)(·,β) ≠ 0`
   (`exists_fibre`), whence `dist(E, σ(Ĥ_{α/2,x})) ≤ δ` (`CAH.exists_mem_spectrum_near`).

## Main results
* `parseval` — `∫_0^1 |∑_{m∈s} d_m e(mβ)|² dβ = ∑_{m∈s} |d_m|²`;
* `nrm_opR` — `R` is an isometry of `L²(𝕋;ℓ²(ℤ))` on trigonometric polynomials with finitely
  many nonzero fibres (the Plancherel/unitarity statement for `R` on this dense class);
* `nrm_opQ` — `Q = U_1 R U_{1/2}` is an isometry on even-supported trigonometric polynomials;
* `exists_fibre` — the quantitative fibre statement;
* `amo_spectrum_subset_chiral` — the inclusion of spectra.

There are no `sorry`s and no additional hypotheses in this file.
-/
import CriticalAMOHausdorff.ChiralGauge
import CriticalAMOHausdorff.AMSCore

noncomputable section

open Real Complex MeasureTheory L2
open scoped ComplexConjugate

namespace CAH

open ChiralGauge

/-! ### Exponentials `e(t) = exp(2πit)` -/

/-- `e(t) = exp(2πit)`. -/
def ex (t : ℝ) : ℂ := cexp (2 * π * I * (t : ℂ))

lemma ex_add (s t : ℝ) : ex (s + t) = ex s * ex t := by
  simp only [ex]; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma norm_ex (t : ℝ) : ‖ex t‖ = 1 := by
  rw [ex, show 2 * (π : ℂ) * I * (t : ℂ) = ((2 * π * t : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma ex_int (k : ℤ) : ex k = 1 := by
  rw [ex, show 2 * (π : ℂ) * I * ((k : ℝ) : ℂ) = k * (2 * π * I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I k

lemma conj_ex (t : ℝ) : conj (ex t) = ex (-t) := by
  rw [ex, ex, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat, Complex.ofReal_neg]
  ring

@[fun_prop]
lemma continuous_ex : Continuous ex := by unfold ex; fun_prop

lemma ex_nat_mul (k : ℕ) (t : ℝ) : ex (k * t) = ex t ^ k := by
  induction k with
  | zero => simp [ex]
  | succ k ih => push_cast; rw [add_mul, one_mul, ex_add, ih, pow_succ]

/-- `∫_0^1 e(jβ) dβ = δ_{j0}` for `j ∈ ℤ`. -/
lemma integral_ex_int (j : ℤ) :
    ∫ β in (0 : ℝ)..1, ex (j * β) = if j = 0 then 1 else 0 := by
  split_ifs with hj
  · subst hj; simp [ex]
  · have hc : (2 * π * I * j : ℂ) ≠ 0 := by
      have : (j : ℂ) ≠ 0 := by exact_mod_cast hj
      simp [Real.pi_ne_zero, Complex.I_ne_zero, this]
    have e : ∀ β : ℝ, ex (j * β) = cexp ((2 * π * I * j) * β) := fun β => by
      simp only [ex]; congr 1; push_cast; ring
    simp_rw [e]
    rw [integral_exp_mul_complex hc]
    simp only [Complex.ofReal_one, Complex.ofReal_zero, mul_one, mul_zero, Complex.exp_zero]
    rw [show (2 * π * I * j : ℂ) = j * (2 * π * I) by ring, Complex.exp_int_mul_two_pi_mul_I]
    simp

/-- **Plancherel for trigonometric polynomials.** -/
theorem parseval (s : Finset ℤ) (d : ℤ → ℂ) :
    ∫ β in (0 : ℝ)..1, ‖∑ m ∈ s, d m * ex (m * β)‖ ^ 2 = ∑ m ∈ s, ‖d m‖ ^ 2 := by
  have key : ∀ β : ℝ, ((‖∑ m ∈ s, d m * ex (m * β)‖ ^ 2 : ℝ) : ℂ) =
      ∑ m ∈ s, ∑ m' ∈ s, d m * conj (d m') * ex (((m - m' : ℤ) : ℝ) * β) := by
    intro β
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun m _ => Finset.sum_congr rfl (fun m' _ => ?_))
    rw [map_mul, conj_ex, mul_mul_mul_comm, ← ex_add]
    congr 2; push_cast; ring
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [key]
  rw [Complex.ofReal_sum, intervalIntegral.integral_finsetSum (fun m _ => (by fun_prop :
    Continuous fun β : ℝ => ∑ m' ∈ s, d m * conj (d m') * ex (((m - m' : ℤ) : ℝ) * β)
    ).intervalIntegrable _ _)]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [intervalIntegral.integral_finsetSum (fun m' _ => (by fun_prop : Continuous
    (fun β : ℝ => d m * conj (d m') * ex (((m - m' : ℤ) : ℝ) * β))).intervalIntegrable _ _)]
  simp_rw [intervalIntegral.integral_const_mul, integral_ex_int, sub_eq_zero, mul_ite,
    mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [hm, ↓reduceIte]
  rw [Complex.mul_conj', Complex.ofReal_pow]

/-! ### Trigonometric-polynomial representations -/

/-- The box `[-B, B] ∩ ℤ`. -/
def box (B : ℕ) : Finset ℤ := Finset.Icc (-(B : ℤ)) B

lemma mem_box {B : ℕ} {n : ℤ} : n ∈ box B ↔ -(B : ℤ) ≤ n ∧ n ≤ B := Finset.mem_Icc

lemma box_mono {B B' : ℕ} (h : B ≤ B') : box B ⊆ box B' := by
  intro n hn; rw [mem_box] at hn ⊢; have : (B : ℤ) ≤ B' := by exact_mod_cast h
  omega

/-- `ψ(n,β) = ∑_m c(n,m) e(mβ)` with `c` supported in `[-B,B]²`. -/
structure Rep (ψ : Fn) (B : ℕ) (c : ℤ → ℤ → ℂ) : Prop where
  supp : ∀ n m, c n m ≠ 0 → n ∈ box B ∧ m ∈ box B
  eq : ∀ n β, ψ n β = ∑' m, c n m * ex (m * β)

lemma tsum_box {B : ℕ} {c : ℤ → ℤ → ℂ} (hs : ∀ n m, c n m ≠ 0 → n ∈ box B ∧ m ∈ box B)
    (n : ℤ) (β : ℝ) : ∑' m, c n m * ex (m * β) = ∑ m ∈ box B, c n m * ex (m * β) := by
  apply tsum_eq_sum
  intro m hm
  have : c n m = 0 := by by_contra h'; exact hm (hs n m h').2
  simp [this]

namespace Rep

variable {ψ ψ' : Fn} {B : ℕ} {c c' : ℤ → ℤ → ℂ}

lemma eq_sum (h : Rep ψ B c) (n : ℤ) (β : ℝ) :
    ψ n β = ∑ m ∈ box B, c n m * ex (m * β) := by
  rw [h.eq, tsum_box h.supp]

lemma zero (h : Rep ψ B c) {n : ℤ} (hn : n ∉ box B) (β : ℝ) : ψ n β = 0 := by
  rw [h.eq_sum]
  refine Finset.sum_eq_zero (fun m _ => ?_)
  have : c n m = 0 := by by_contra h'; exact hn (h.supp n m h').1
  simp [this]

lemma continuous (h : Rep ψ B c) (n : ℤ) : Continuous (ψ n) := by
  rw [show ψ n = fun β => ∑ m ∈ box B, c n m * ex (m * β) from funext (h.eq_sum n)]
  fun_prop

lemma mono (h : Rep ψ B c) {B' : ℕ} (hB : B ≤ B') : Rep ψ B' c :=
  ⟨fun n m hnm => ⟨box_mono hB (h.supp n m hnm).1, box_mono hB (h.supp n m hnm).2⟩, h.eq⟩

lemma add (h : Rep ψ B c) (h' : Rep ψ' B c') :
    Rep (ψ + ψ') B (fun n m => c n m + c' n m) := by
  refine ⟨fun n m hnm => ?_, fun n β => ?_⟩
  · by_cases hc : c n m = 0
    · exact h'.supp n m (by simpa [hc] using hnm)
    · exact h.supp n m hc
  · have hs : ∀ n m, c n m + c' n m ≠ 0 → n ∈ box B ∧ m ∈ box B := by
      intro n m hnm
      by_cases hc : c n m = 0
      · exact h'.supp n m (by simpa [hc] using hnm)
      · exact h.supp n m hc
    rw [Pi.add_apply, Pi.add_apply, h.eq_sum, h'.eq_sum, tsum_box hs, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    ring

lemma smul (h : Rep ψ B c) (z : ℂ) : Rep (z • ψ) B (fun n m => z * c n m) := by
  refine ⟨fun n m hnm => h.supp n m (right_ne_zero_of_mul hnm), fun n β => ?_⟩
  rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul, h.eq, ← tsum_mul_left]
  congr 1; funext m; ring

lemma TT (h : Rep ψ B c) : Rep (opT (opT ψ)) (B + 2) (fun n m => c (n + 1 + 1) m) := by
  refine ⟨fun n m hnm => ?_, fun n β => h.eq (n + 1 + 1) β⟩
  obtain ⟨h1, h2⟩ := h.supp _ _ hnm
  rw [mem_box] at h1 h2 ⊢; rw [mem_box]; push_cast; omega

lemma TinvTinv (h : Rep ψ B c) :
    Rep (opTinv (opTinv ψ)) (B + 2) (fun n m => c (n - 1 - 1) m) := by
  refine ⟨fun n m hnm => ?_, fun n β => h.eq (n - 1 - 1) β⟩
  obtain ⟨h1, h2⟩ := h.supp _ _ hnm
  rw [mem_box] at h1 h2 ⊢; rw [mem_box]; push_cast; omega

end Rep

lemma opS_apply_ex (α x : ℝ) (φ : Fn) (n : ℤ) (θ : ℝ) :
    opS α x φ n θ = ex (x * (θ + n * α)) * φ n θ := by
  simp only [opS, ex]; congr 2; push_cast; ring

lemma opU_apply_ex (α x : ℝ) (φ : Fn) (n : ℤ) (θ : ℝ) :
    opU α x φ n θ = ex (n * x * (θ + n * α / 2)) * φ n θ := by
  simp only [opU, ex]; congr 2; push_cast; ring

lemma norm_opU (α x : ℝ) (φ : Fn) (n : ℤ) (θ : ℝ) : ‖opU α x φ n θ‖ = ‖φ n θ‖ := by
  rw [opU_apply_ex, norm_mul, norm_ex, one_mul]

namespace Rep

variable {ψ : Fn} {B : ℕ} {c : ℤ → ℤ → ℂ}

lemma S1 (h : Rep ψ B c) (a : ℝ) :
    Rep (opS a 1 ψ) (B + 1) (fun n m => ex (n * a) * c n (m - 1)) := by
  refine ⟨fun n m hnm => ?_, fun n β => ?_⟩
  · obtain ⟨h1, h2⟩ := h.supp _ _ (right_ne_zero_of_mul hnm)
    rw [mem_box] at h1 h2; rw [mem_box, mem_box]; push_cast; omega
  · rw [opS_apply_ex, h.eq]
    refine Eq.trans ?_ ((Equiv.addRight (1 : ℤ)).tsum_eq _)
    rw [← tsum_mul_left]
    congr 1; funext m
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
    have e : ex (1 * (β + n * a)) * ex (m * β) = ex (n * a) * ex (((m + 1 : ℤ) : ℝ) * β) := by
      rw [← ex_add, ← ex_add]; congr 1; push_cast; ring
    linear_combination (c n m) * e

lemma Sm1 (h : Rep ψ B c) (a : ℝ) :
    Rep (opS a (-1) ψ) (B + 1) (fun n m => ex (-(n * a)) * c n (m + 1)) := by
  refine ⟨fun n m hnm => ?_, fun n β => ?_⟩
  · obtain ⟨h1, h2⟩ := h.supp _ _ (right_ne_zero_of_mul hnm)
    rw [mem_box] at h1 h2; rw [mem_box, mem_box]; push_cast; omega
  · rw [opS_apply_ex, h.eq]
    refine Eq.trans ?_ ((Equiv.subRight (1 : ℤ)).tsum_eq _)
    rw [← tsum_mul_left]
    congr 1; funext m
    simp only [Equiv.subRight_apply, sub_add_cancel]
    have e : ex (-1 * (β + n * a)) * ex (m * β) =
        ex (-(n * a)) * ex (((m - 1 : ℤ) : ℝ) * β) := by
      rw [← ex_add, ← ex_add]; congr 1; push_cast; ring
    linear_combination (c n m) * e

/-- `U_{1/2}` on even-supported trigonometric polynomials. -/
lemma Uhalf (h : Rep ψ B c) (hev : ∀ n m, c n m ≠ 0 → Even n) (a : ℝ) :
    Rep (opU a (1 / 2) ψ) (2 * B)
      (fun n m => ex (((n / 2 : ℤ) : ℝ) ^ 2 * a) * c n (m - n / 2)) := by
  refine ⟨fun n m hnm => ?_, fun n β => ?_⟩
  · obtain ⟨h1, h2⟩ := h.supp _ _ (right_ne_zero_of_mul hnm)
    rw [mem_box] at h1 h2; rw [mem_box, mem_box]; push_cast; omega
  · by_cases hn : Even n
    · obtain ⟨k, rfl⟩ := hn
      have hk : (k + k) / 2 = k := by omega
      rw [hk, opU_apply_ex, h.eq]
      refine Eq.trans ?_ ((Equiv.addRight k).tsum_eq _)
      rw [← tsum_mul_left]
      congr 1; funext m
      simp only [Equiv.coe_addRight, add_sub_cancel_right]
      have e : ex (((k + k : ℤ) : ℝ) * (1 / 2) * (β + ((k + k : ℤ) : ℝ) * a / 2)) *
          ex (m * β) = ex ((k : ℝ) ^ 2 * a) * ex (((m + k : ℤ) : ℝ) * β) := by
        rw [← ex_add, ← ex_add]; congr 1; push_cast; ring
      linear_combination (c (k + k) m) * e
    · have hc0 : ∀ m, c n m = 0 := fun m => by
        by_contra h'; exact hn (hev n m h')
      rw [opU_apply_ex, h.eq]
      simp [hc0]

/-- `∫_0^1 e(-nβ) ψ(k,β) dβ = c(k,n)`. -/
lemma integral (h : Rep ψ B c) (k n : ℤ) :
    ∫ β in (0 : ℝ)..1, cexp (-(2 * π * I * n * β)) * ψ k β = c k n := by
  have hpt : ∀ β : ℝ, cexp (-(2 * π * I * n * β)) * ψ k β =
      ∑ m ∈ box B, c k m * ex (((m - n : ℤ) : ℝ) * β) := by
    intro β
    rw [h.eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    have e : cexp (-(2 * π * I * n * β)) * ex (m * β) = ex (((m - n : ℤ) : ℝ) * β) := by
      rw [show cexp (-(2 * π * I * n * β)) = ex (-(n * β)) by
        simp only [ex]; congr 1; push_cast; ring, ← ex_add]
      congr 1; push_cast; ring
    linear_combination (c k m) * e
  simp_rw [hpt]
  rw [intervalIntegral.integral_finsetSum (fun m _ => (by fun_prop : Continuous
    (fun β : ℝ => c k m * ex (((m - n : ℤ) : ℝ) * β))).intervalIntegrable _ _)]
  simp_rw [intervalIntegral.integral_const_mul, integral_ex_int, sub_eq_zero, mul_ite,
    mul_one, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with hn
  · rfl
  · by_contra h'; exact hn (h.supp k n (Ne.symm h')).2

/-- `R` on trigonometric polynomials. -/
lemma R (h : Rep ψ B c) (a : ℝ) :
    Rep (opR a ψ) B (fun n m => c (-m) n * ex (m * n * a)) := by
  refine ⟨fun n m hnm => ?_, fun n θ => ?_⟩
  · obtain ⟨h1, h2⟩ := h.supp _ _ (left_ne_zero_of_mul hnm)
    rw [mem_box] at h1 h2; rw [mem_box, mem_box]; omega
  · simp only [opR]
    simp_rw [h.integral]
    refine ((Equiv.neg ℤ).tsum_eq _).symm.trans ?_
    congr 1; funext m
    simp only [Equiv.neg_apply]
    have e : cexp (-(2 * π * I * ((-m : ℤ) : ℂ) * ((θ + n * a : ℝ) : ℂ))) =
        ex (m * n * a) * ex (m * θ) := by
      rw [← ex_add]; simp only [ex]; congr 1; push_cast; ring
    rw [e]; ring

end Rep

/-- Even-supported trigonometric polynomials. -/
def ERep (ψ : Fn) (B : ℕ) : Prop :=
  ∃ c, Rep ψ B c ∧ ∀ n m, c n m ≠ 0 → Even n

namespace ERep

variable {ψ ψ' : Fn} {B : ℕ}

lemma mono (h : ERep ψ B) {B' : ℕ} (hB : B ≤ B') : ERep ψ B' := by
  obtain ⟨c, hc, hev⟩ := h; exact ⟨c, hc.mono hB, hev⟩

lemma add (h : ERep ψ B) (h' : ERep ψ' B) : ERep (ψ + ψ') B := by
  obtain ⟨c, hc, hev⟩ := h
  obtain ⟨c', hc', hev'⟩ := h'
  refine ⟨_, hc.add hc', fun n m hnm => ?_⟩
  by_cases h0 : c n m = 0
  · exact hev' n m (by simpa [h0] using hnm)
  · exact hev n m h0

lemma smul (h : ERep ψ B) (z : ℂ) : ERep (z • ψ) B := by
  obtain ⟨c, hc, hev⟩ := h
  exact ⟨_, hc.smul z, fun n m hnm => hev n m (right_ne_zero_of_mul hnm)⟩

lemma TT (h : ERep ψ B) : ERep (opT (opT ψ)) (B + 2) := by
  obtain ⟨c, hc, hev⟩ := h
  refine ⟨_, hc.TT, fun n m hnm => ?_⟩
  have := hev _ _ hnm
  simpa [Int.even_add_one] using this

lemma TinvTinv (h : ERep ψ B) : ERep (opTinv (opTinv ψ)) (B + 2) := by
  obtain ⟨c, hc, hev⟩ := h
  refine ⟨_, hc.TinvTinv, fun n m hnm => ?_⟩
  have := hev _ _ hnm
  simpa [Int.even_sub_one] using this

lemma S1 (h : ERep ψ B) (a : ℝ) : ERep (opS a 1 ψ) (B + 1) := by
  obtain ⟨c, hc, hev⟩ := h
  exact ⟨_, hc.S1 a, fun n m hnm => hev _ _ (right_ne_zero_of_mul hnm)⟩

lemma Sm1 (h : ERep ψ B) (a : ℝ) : ERep (opS a (-1) ψ) (B + 1) := by
  obtain ⟨c, hc, hev⟩ := h
  exact ⟨_, hc.Sm1 a, fun n m hnm => hev _ _ (right_ne_zero_of_mul hnm)⟩

lemma good (h : ERep ψ B) : Good ψ := by
  obtain ⟨c, hc, -⟩ := h
  exact ⟨⟨box B, fun k hk => funext fun β => hc.zero hk β⟩,
    fun k => (hc.continuous k).intervalIntegrable 0 1⟩

end ERep

/-! ### The `L²(𝕋; ℓ²(ℤ))` norm on boxes and the isometry of `Q` -/

/-- `∫_0^1 ∑_{|n| ≤ B} |ψ(n,β)|² dβ`. -/
def nrm (ψ : Fn) (B : ℕ) : ℝ := ∫ β in (0 : ℝ)..1, ∑ n ∈ box B, ‖ψ n β‖ ^ 2

/-- `∑_{|n|,|m| ≤ B} |c(n,m)|²`. -/
def cn (c : ℤ → ℤ → ℂ) (B : ℕ) : ℝ := ∑ n ∈ box B, ∑ m ∈ box B, ‖c n m‖ ^ 2

lemma nrm_eq_cn {ψ : Fn} {B : ℕ} {c : ℤ → ℤ → ℂ} (h : Rep ψ B c) : nrm ψ B = cn c B := by
  unfold nrm cn
  simp_rw [h.eq_sum]
  rw [intervalIntegral.integral_finsetSum (fun n _ => (by fun_prop : Continuous
    (fun β : ℝ => ‖∑ m ∈ box B, c n m * ex (m * β)‖ ^ 2)).intervalIntegrable _ _)]
  exact Finset.sum_congr rfl (fun n _ => parseval _ _)

lemma cn_swap (c : ℤ → ℤ → ℂ) (B : ℕ) (a : ℝ) :
    cn (fun n m => c (-m) n * ex (m * n * a)) B = cn c B := by
  unfold cn
  simp_rw [norm_mul, norm_ex, mul_one]
  rw [Finset.sum_comm]
  refine Finset.sum_nbij' (fun m => -m) (fun m => -m) ?_ ?_ ?_ ?_ ?_
  · intro m hm; simp only [mem_box] at hm ⊢; omega
  · intro m hm; simp only [mem_box] at hm ⊢; omega
  · intro m _; simp
  · intro m _; simp
  · intro m _; rfl

lemma nrm_opU (a x : ℝ) (ψ : Fn) (B : ℕ) : nrm (opU a x ψ) B = nrm ψ B := by
  unfold nrm; simp_rw [norm_opU]

/-- **`R` is an isometry** on trigonometric polynomials (Plancherel). -/
theorem nrm_opR {ψ : Fn} {B : ℕ} {c : ℤ → ℤ → ℂ} (h : Rep ψ B c) (a : ℝ) :
    nrm (opR a ψ) B = nrm ψ B := by
  rw [nrm_eq_cn (h.R a), cn_swap, nrm_eq_cn h]

/-- **`Q = U_1 R U_{1/2}` is an isometry** on even-supported trigonometric polynomials. -/
theorem nrm_opQ {ψ : Fn} {B : ℕ} (h : ERep ψ B) (a : ℝ) :
    nrm (opQ a ψ) (2 * B) = nrm ψ (2 * B) := by
  obtain ⟨c, hc, hev⟩ := h
  have h1 := hc.Uhalf hev a
  show nrm (opU a 1 (opR a (opU a (1 / 2) ψ))) (2 * B) = _
  rw [nrm_opU, nrm_opR h1, nrm_opU]

lemma opQ_zero {ψ : Fn} {B : ℕ} (h : ERep ψ B) (a : ℝ) {n : ℤ} (hn : n ∉ box (2 * B))
    (β : ℝ) : opQ a ψ n β = 0 := by
  obtain ⟨c, hc, hev⟩ := h
  have h2 := (hc.Uhalf hev a).R a
  show opU a 1 (opR a (opU a (1 / 2) ψ)) n β = 0
  rw [opU_apply_ex, h2.zero hn, mul_zero]

lemma continuous_opQ {ψ : Fn} {B : ℕ} (h : ERep ψ B) (a : ℝ) (n : ℤ) :
    Continuous (opQ a ψ n) := by
  obtain ⟨c, hc, hev⟩ := h
  have h2 := ((hc.Uhalf hev a).R a).continuous n
  show Continuous (fun β => opU a 1 (opR a (opU a (1 / 2) ψ)) n β)
  simp_rw [opU_apply_ex]
  fun_prop

lemma opQ_smul (a : ℝ) (z : ℂ) (φ : Fn) : opQ a (z • φ) = z • opQ a φ := by
  simp only [opQ]; rw [opU_smul, opR_smul, opU_smul]

/-! ### Elementary sums -/

lemma sum_even (F : ℤ → ℝ) (B : ℕ) (hodd : ∀ j, F (2 * j + 1) = 0) :
    ∑ n ∈ box (2 * B), F n = ∑ j ∈ box B, F (2 * j) := by
  have hinj : Set.InjOn (fun j : ℤ => 2 * j) (box B) := fun x _ y _ hxy => by
    have : 2 * x = 2 * y := hxy
    omega
  calc ∑ n ∈ box (2 * B), F n = ∑ n ∈ (box B).image (fun j => 2 * j), F n := by
        symm
        apply Finset.sum_subset
        · intro n hn
          simp only [Finset.mem_image, mem_box] at hn
          obtain ⟨j, ⟨h1, h2⟩, rfl⟩ := hn
          rw [mem_box]; push_cast; omega
        · intro n hn hn'
          rcases Int.emod_two_eq_zero_or_one n with h | h
          · exfalso; apply hn'
            rw [Finset.mem_image]
            refine ⟨n / 2, ?_, by show 2 * (n / 2) = n; omega⟩
            rw [mem_box] at hn ⊢; push_cast at hn; omega
          · rw [show n = 2 * (n / 2) + 1 by omega]; exact hodd _
    _ = ∑ j ∈ box B, F (2 * j) := Finset.sum_image hinj

lemma l2_norm_sq_eq_sum (x : L2 ℤ) (s : Finset ℤ) (hx : ∀ n ∉ s, x n = 0) :
    ‖x‖ ^ 2 = ∑ n ∈ s, ‖x n‖ ^ 2 := by
  rw [norm_sq_eq_tsum]
  exact tsum_eq_sum (fun n hn => by simp [hx n hn])

/-- A finitely supported vector of `ℓ²(ℤ)`. -/
def finVec (f : ℤ → ℂ) (s : Finset ℤ) : L2 ℤ := ∑ n ∈ s, lp.single 2 n (f n)

lemma finVec_apply (f : ℤ → ℂ) (s : Finset ℤ) (m : ℤ) :
    finVec f s m = if m ∈ s then f m else 0 := by
  rw [finVec, lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.single_apply, Pi.single_apply]
  exact Finset.sum_ite_eq s m (fun c => f c)

/-- Averaging: if `∫ f < ∫ g` then `f(x) < g(x)` somewhere. -/
lemma exists_lt_of_integral_lt {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∫ x in (0 : ℝ)..1, f x < ∫ x in (0 : ℝ)..1, g x) : ∃ x, f x < g x := by
  by_contra hcon
  push Not at hcon
  have := intervalIntegral.integral_mono_on zero_le_one
    (hg.intervalIntegrable (μ := MeasureTheory.volume) 0 1)
    (hf.intervalIntegrable (μ := MeasureTheory.volume) 0 1) (fun x _ => hcon x)
  linarith

/-! ### The test function -/

/-- `g(β) = ∑_{k < L} e(k(β - θ))`. -/
def gfun (θ : ℝ) (L : ℕ) (β : ℝ) : ℂ := ∑ k ∈ Finset.range L, ex (k * (β - θ))

/-- The frequencies `{0, …, L-1} ⊆ ℤ`. -/
def sL (L : ℕ) : Finset ℤ := (Finset.range L).image (fun k : ℕ => (k : ℤ))

lemma mem_sL {L : ℕ} {m : ℤ} : m ∈ sL L ↔ 0 ≤ m ∧ m < L := by
  simp only [sL, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩; omega
  · intro h; exact ⟨m.toNat, by omega, by omega⟩

lemma gfun_eq (θ : ℝ) (L : ℕ) (β : ℝ) :
    gfun θ L β = ∑ m ∈ sL L, ex (-(m * θ)) * ex (m * β) := by
  rw [gfun, sL, Finset.sum_image (fun x _ y _ h => by exact_mod_cast h)]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← ex_add]; congr 1; push_cast; ring

@[fun_prop]
lemma continuous_gfun (θ : ℝ) (L : ℕ) : Continuous (gfun θ L) := by
  unfold gfun; fun_prop

lemma integral_gfun (θ : ℝ) (L : ℕ) : ∫ β in (0 : ℝ)..1, ‖gfun θ L β‖ ^ 2 = L := by
  simp_rw [gfun_eq]
  rw [parseval]
  simp only [norm_ex, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [sL, Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]

lemma norm_gfun_mul_le (θ : ℝ) (L : ℕ) (β : ℝ) : ‖gfun θ L β * (ex (β - θ) - 1)‖ ≤ 2 := by
  have : gfun θ L β = ∑ k ∈ Finset.range L, ex (β - θ) ^ k := by
    unfold gfun; exact Finset.sum_congr rfl (fun k _ => ex_nat_mul k _)
  rw [this, geom_sum_mul]
  calc ‖ex (β - θ) ^ L - 1‖ ≤ ‖ex (β - θ) ^ L‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, norm_ex, one_pow, norm_one]; norm_num

/-- `Φ(2j,β) = g(β) u(j)`, `Φ(2j+1,β) = 0`. -/
def Phi (θ : ℝ) (L : ℕ) (u : L2 ℤ) : Fn :=
  fun n β => if Even n then gfun θ L β * u (n / 2) else 0

lemma Phi_two_mul (θ : ℝ) (L : ℕ) (u : L2 ℤ) (j : ℤ) (β : ℝ) :
    Phi θ L u (2 * j) β = gfun θ L β * u j := by
  simp only [Phi, even_two_mul, ↓reduceIte]; rw [show 2 * j / 2 = j by omega]

lemma Phi_odd (θ : ℝ) (L : ℕ) (u : L2 ℤ) (j : ℤ) (β : ℝ) : Phi θ L u (2 * j + 1) β = 0 := by
  simp [Phi]

lemma erep_Phi (θ : ℝ) (L N0 : ℕ) (u : L2 ℤ) (hu : ∀ n, n ∉ box N0 → u n = 0) :
    ERep (Phi θ L u) (2 * N0 + L) := by
  refine ⟨fun n m => if Even n ∧ m ∈ sL L then u (n / 2) * ex (-(m * θ)) else 0,
    ⟨fun n m hnm => ?_, fun n β => ?_⟩, fun n m hnm => ?_⟩
  · beta_reduce at hnm
    split_ifs at hnm with h
    · obtain ⟨hn, hm⟩ := h
      have hu0 : u (n / 2) ≠ 0 := left_ne_zero_of_mul hnm
      have h1 : n / 2 ∈ box N0 := by by_contra h'; exact hu0 (hu _ h')
      rw [mem_sL] at hm
      rw [Int.even_iff] at hn
      rw [mem_box] at h1; rw [mem_box, mem_box]; push_cast; omega
    · exact absurd rfl hnm
  · beta_reduce
    rw [tsum_eq_sum (s := sL L) (fun m hm => by simp [hm])]
    simp only [Phi]
    split_ifs with hn
    · rw [gfun_eq, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun m hm => ?_)
      simp only [hn, hm, and_self, ↓reduceIte]; ring
    · simp [hn]
  · beta_reduce at hnm
    split_ifs at hnm with h
    · exact h.1
    · exact absurd rfl hnm

/-! ### The doubled operator on the test function -/

/-- `(T² + T⁻² + S + S⁻¹ - E)Φ` at frequency `α/2`. -/
def Yfun (α θ E : ℝ) (L : ℕ) (u : L2 ℤ) : Fn :=
  opDoubled (α / 2) (Phi θ L u) + (-(E : ℂ)) • Phi θ L u

lemma Yfun_two_mul (α θ E : ℝ) (L : ℕ) (u : L2 ℤ) (j : ℤ) (β : ℝ) :
    Yfun α θ E L u (2 * j) β = gfun θ L β * (amo α β u j - E * u j) := by
  have hφ : ∀ m, Phi θ L u (2 * m) β = (gfun θ L β • u) m := by
    intro m; rw [Phi_two_mul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  have h2 : (2 : ℝ) * (α / 2) = α := by ring
  simp only [Yfun, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [doubled_even β _ _ hφ j, h2, map_smul, hφ j]
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  ring

lemma Yfun_odd (α θ E : ℝ) (L : ℕ) (u : L2 ℤ) (j : ℤ) (β : ℝ) :
    Yfun α θ E L u (2 * j + 1) β = 0 := by
  have hφ : ∀ m, Phi θ L u (2 * m + 1) β = (0 : L2 ℤ) m := by
    intro m; rw [Phi_odd]; simp
  simp only [Yfun, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [doubled_odd β 0 _ hφ j, map_zero, Phi_odd]
  simp

lemma erep_Yfun (α θ E : ℝ) (L N0 : ℕ) (u : L2 ℤ) (hu : ∀ n, n ∉ box N0 → u n = 0) :
    ERep (Yfun α θ E L u) (2 * N0 + L + 2) := by
  have h := erep_Phi θ L N0 u hu
  show ERep (opT (opT (Phi θ L u)) + opTinv (opTinv (Phi θ L u)) + opS (α / 2) 1 (Phi θ L u) +
    opS (α / 2) (-1) (Phi θ L u) + (-(E : ℂ)) • Phi θ L u) _
  exact (((h.TT.add h.TinvTinv).add ((h.S1 _).mono (by omega))).add
    ((h.Sm1 _).mono (by omega))).add ((h.smul _).mono (by omega))

lemma erep_doubled (α θ : ℝ) (L N0 : ℕ) (u : L2 ℤ) (hu : ∀ n, n ∉ box N0 → u n = 0) :
    ERep (opDoubled (α / 2) (Phi θ L u)) (2 * N0 + L + 2) := by
  have h := erep_Phi θ L N0 u hu
  show ERep (opT (opT (Phi θ L u)) + opTinv (opTinv (Phi θ L u)) + opS (α / 2) 1 (Phi θ L u) +
    opS (α / 2) (-1) (Phi θ L u)) _
  exact ((h.TT.add h.TinvTinv).add ((h.S1 _).mono (by omega))).add
    ((h.Sm1 _).mono (by omega))

/-! ### Estimates -/

lemma two_cos_ex (x : ℝ) : (((2 * Real.cos (2 * π * x)) : ℝ) : ℂ) = ex x + ex (-x) := by
  simp only [ex]
  push_cast
  rw [Complex.two_cos]
  congr 1 <;> congr 1 <;> ring

lemma norm_two_cos_sub_le (x y : ℝ) :
    ‖(((2 * Real.cos (2 * π * x)) : ℝ) : ℂ) - (((2 * Real.cos (2 * π * y)) : ℝ) : ℂ)‖ ≤
      2 * ‖ex (x - y) - 1‖ := by
  rw [two_cos_ex, two_cos_ex]
  have h1 : ex x - ex y = ex y * (ex (x - y) - 1) := by
    rw [mul_sub, mul_one, ← ex_add, show y + (x - y) = x by ring]
  have h2 : ex (-x) - ex (-y) = ex (-x) * (1 - ex (x - y)) := by
    rw [mul_sub, mul_one, ← ex_add, show -x + (x - y) = -y by ring]
  calc ‖(ex x + ex (-x)) - (ex y + ex (-y))‖ = ‖(ex x - ex y) + (ex (-x) - ex (-y))‖ := by
        congr 1; ring
    _ ≤ ‖ex x - ex y‖ + ‖ex (-x) - ex (-y)‖ := norm_add_le _ _
    _ = 2 * ‖ex (x - y) - 1‖ := by
        rw [h1, h2, norm_mul, norm_mul, norm_ex, norm_ex, norm_sub_rev 1]; ring

lemma amo_sub_amo (α β θ : ℝ) (u : L2 ℤ) (j : ℤ) :
    amo α β u j - amo α θ u j = ((((2 * Real.cos (2 * π * (β + j * α))) : ℝ) : ℂ) -
      (((2 * Real.cos (2 * π * (θ + j * α))) : ℝ) : ℂ)) * u j := by
  simp only [amo, jacobi_apply bddFun_two_cos (bddFun_const 1)]
  ring

lemma amo_apply_zero (α θ : ℝ) (u : L2 ℤ) (N0 : ℕ) (hu : ∀ n, n ∉ box N0 → u n = 0)
    {j : ℤ} (hj : j ∉ box (N0 + 1)) : amo α θ u j = 0 := by
  simp only [amo, jacobi_apply bddFun_two_cos (bddFun_const 1)]
  rw [mem_box] at hj
  push_cast at hj
  have h1 : u (j - 1) = 0 := hu _ (by rw [mem_box]; omega)
  have h2 : u (j + 1) = 0 := hu _ (by rw [mem_box]; omega)
  have h3 : u j = 0 := hu _ (by rw [mem_box]; omega)
  rw [h1, h2, h3]; simp

lemma nrm_Phi (θ : ℝ) (L N0 B : ℕ) (u : L2 ℤ) (hu : ∀ n, n ∉ box N0 → u n = 0)
    (hB : N0 ≤ B) : nrm (Phi θ L u) (2 * B) = L * ‖u‖ ^ 2 := by
  have hpt : ∀ β, ∑ n ∈ box (2 * B), ‖Phi θ L u n β‖ ^ 2 = ‖gfun θ L β‖ ^ 2 * ‖u‖ ^ 2 := by
    intro β
    refine (sum_even (fun n => ‖Phi θ L u n β‖ ^ 2) B (fun j => by simp [Phi_odd])).trans ?_
    rw [l2_norm_sq_eq_sum u (box B) (fun n hn => hu n (fun h => hn (box_mono hB h))),
      Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    show ‖Phi θ L u (2 * j) β‖ ^ 2 = _
    rw [Phi_two_mul, norm_mul, mul_pow]
  unfold nrm
  simp_rw [hpt]
  rw [intervalIntegral.integral_mul_const, integral_gfun]

lemma nrm_Y_le (α θ E ε : ℝ) (L N0 : ℕ) (u : L2 ℤ) (hu : ∀ n, n ∉ box N0 → u n = 0) (happ : ‖amo α θ u - (E : ℂ) • u‖ ≤ ε * ‖u‖) :
    nrm (Yfun α θ E L u) (2 * (2 * N0 + L + 2)) ≤ (2 * ε ^ 2 * L + 32) * ‖u‖ ^ 2 := by
  set B := 2 * N0 + L + 2 with hBdef
  set w : L2 ℤ := amo α θ u - (E : ℂ) • u with hw
  have hwj : ∀ j, w j = amo α θ u j - E * u j := fun j => by
    rw [hw, lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  have hwz : ∀ j, j ∉ box B → w j = 0 := by
    intro j hj
    have hj' : j ∉ box (N0 + 1) := fun h => hj (box_mono (by omega) h)
    rw [hwj, amo_apply_zero α θ u N0 hu hj', hu j (fun h => hj' (box_mono (by omega) h))]
    simp
  have huz : ∀ j, j ∉ box B → u j = 0 := fun j hj => hu j (fun h => hj (box_mono (by omega) h))
  have hwn : ‖w‖ ^ 2 ≤ ε ^ 2 * ‖u‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) happ 2
  -- pointwise bound
  have hpt : ∀ β, ∑ n ∈ box (2 * B), ‖Yfun α θ E L u n β‖ ^ 2 ≤
      ‖gfun θ L β‖ ^ 2 * (2 * ‖w‖ ^ 2) + 32 * ‖u‖ ^ 2 := by
    intro β
    refine (sum_even (fun n => ‖Yfun α θ E L u n β‖ ^ 2) B
      (fun j => by simp [Yfun_odd])).trans_le ?_
    rw [l2_norm_sq_eq_sum w (box B) hwz,
      l2_norm_sq_eq_sum u (box B) huz, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun j _ => ?_)
    show ‖Yfun α θ E L u (2 * j) β‖ ^ 2 ≤ _
    rw [Yfun_two_mul]
    have hsplit : amo α β u j - E * u j = w j + (amo α β u j - amo α θ u j) := by
      rw [hwj]; ring
    have hD : ‖gfun θ L β * (amo α β u j - amo α θ u j)‖ ≤ 4 * ‖u j‖ := by
      rw [amo_sub_amo, ← mul_assoc, norm_mul, norm_mul]
      have h1 := norm_two_cos_sub_le (β + j * α) (θ + j * α)
      rw [show β + j * α - (θ + j * α) = β - θ by ring] at h1
      have h2 := norm_gfun_mul_le θ L β
      rw [norm_mul] at h2
      have : ‖gfun θ L β‖ * ‖(((2 * Real.cos (2 * π * (β + j * α))) : ℝ) : ℂ) -
          (((2 * Real.cos (2 * π * (θ + j * α))) : ℝ) : ℂ)‖ ≤ 4 := by
        calc _ ≤ ‖gfun θ L β‖ * (2 * ‖ex (β - θ) - 1‖) := by gcongr
          _ = 2 * (‖gfun θ L β‖ * ‖ex (β - θ) - 1‖) := by ring
          _ ≤ 2 * 2 := by gcongr
          _ = 4 := by norm_num
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    have htri : ‖gfun θ L β * (amo α β u j - E * u j)‖ ≤
        ‖gfun θ L β‖ * ‖w j‖ + 4 * ‖u j‖ := by
      rw [hsplit, mul_add]
      calc _ ≤ ‖gfun θ L β * w j‖ + ‖gfun θ L β * (amo α β u j - amo α θ u j)‖ :=
            norm_add_le _ _
        _ ≤ _ := by rw [norm_mul]; gcongr
    have hA := norm_nonneg (gfun θ L β * (amo α β u j - E * u j))
    have hB0 : 0 ≤ ‖gfun θ L β‖ * ‖w j‖ := by positivity
    have hC0 : 0 ≤ ‖u j‖ := norm_nonneg _
    nlinarith [mul_self_nonneg (‖gfun θ L β‖ * ‖w j‖ - 4 * ‖u j‖),
      mul_le_mul htri htri hA (by positivity)]
  have hint : ∫ β in (0 : ℝ)..1, (‖gfun θ L β‖ ^ 2 * (2 * ‖w‖ ^ 2) + 32 * ‖u‖ ^ 2) =
      L * (2 * ‖w‖ ^ 2) + 32 * ‖u‖ ^ 2 := by
    rw [intervalIntegral.integral_add ((by fun_prop : Continuous fun β =>
      ‖gfun θ L β‖ ^ 2 * (2 * ‖w‖ ^ 2)).intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_mul_const, integral_gfun, intervalIntegral.integral_const]
    simp
  obtain ⟨c, hc, -⟩ := erep_Yfun α θ E L N0 u hu
  have hle : nrm (Yfun α θ E L u) (2 * B) ≤ L * (2 * ‖w‖ ^ 2) + 32 * ‖u‖ ^ 2 := by
    rw [← hint]
    unfold nrm
    refine intervalIntegral.integral_mono_on zero_le_one ?_ ?_ (fun β _ => hpt β)
    · exact (continuous_finsetSum _ (fun n _ =>
        (hc.continuous n).norm.pow 2)).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun β =>
        ‖gfun θ L β‖ ^ 2 * (2 * ‖w‖ ^ 2) + 32 * ‖u‖ ^ 2).intervalIntegrable _ _
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  nlinarith

/-! ### The fibre statement and the main theorem -/

/-- **Quantitative fibre statement.**  If `u ≠ 0` is supported in `[-N₀,N₀]` with
`‖(H_{α,θ} - E)u‖ ≤ ε‖u‖`, and `2ε² + 32/L < δ²`, then some chiral fibre `Ĥ_{α/2,x}` has
spectrum within `δ` of `E`. -/
theorem exists_fibre (α θ E ε δ : ℝ) (L N0 : ℕ) (u : L2 ℤ)
    (hu : ∀ n, n ∉ box N0 → u n = 0) (hu0 : u ≠ 0)
    (happ : ‖amo α θ u - (E : ℂ) • u‖ ≤ ε * ‖u‖) (hL : 0 < L) (hδ : 0 < δ)
    (hεL : 2 * ε ^ 2 + 32 / L < δ ^ 2) :
    ∃ x E', E' ∈ spectrum ℝ (chiral (α / 2) x) ∧ |E - E'| ≤ δ := by
  set B := 2 * N0 + L + 2 with hBdef
  have hΦ : ERep (Phi θ L u) B := (erep_Phi θ L N0 u hu).mono (by omega)
  have hY : ERep (Yfun α θ E L u) B := erep_Yfun α θ E L N0 u hu
  set ψ := opQ (α / 2) (Phi θ L u) with hψ
  set χ := opQ (α / 2) (Yfun α θ E L u) with hχ
  -- Theorem 3.1
  have hχeq : χ = opHt (α / 2) ψ + (-(E : ℂ)) • ψ := by
    rw [hχ, Yfun, opQ_add (erep_doubled α θ L N0 u hu).good (hΦ.smul _).good,
      chiral_representation hΦ.good, opQ_smul]
  -- norms
  have hn1 : nrm χ (2 * B) ≤ (2 * ε ^ 2 * L + 32) * ‖u‖ ^ 2 := by
    rw [hχ, nrm_opQ hY]; exact nrm_Y_le α θ E ε L N0 u hu happ
  have hn2 : nrm ψ (2 * B) = L * ‖u‖ ^ 2 := by
    rw [hψ, nrm_opQ hΦ]; exact nrm_Phi θ L N0 B u hu (by omega)
  have hupos : 0 < ‖u‖ ^ 2 := by positivity
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hlt : (2 * ε ^ 2 * L + 32) * ‖u‖ ^ 2 < δ ^ 2 * (L * ‖u‖ ^ 2) := by
    have : 2 * ε ^ 2 * L + 32 < δ ^ 2 * L := by
      have h1 : (2 * ε ^ 2 + 32 / L) * L < δ ^ 2 * L := mul_lt_mul_of_pos_right hεL hLpos
      rwa [add_mul, div_mul_cancel₀ _ hLpos.ne'] at h1
    nlinarith [mul_lt_mul_of_pos_right this hupos]
  -- averaging
  set F1 : ℝ → ℝ := fun β => ∑ n ∈ box (2 * B), ‖χ n β‖ ^ 2 with hF1
  set F2 : ℝ → ℝ := fun β => ∑ n ∈ box (2 * B), ‖ψ n β‖ ^ 2 with hF2
  have hc1 : Continuous F1 :=
    continuous_finsetSum _ (fun n _ => ((continuous_opQ hY (α / 2) n).norm.pow 2))
  have hc2 : Continuous F2 :=
    continuous_finsetSum _ (fun n _ => ((continuous_opQ hΦ (α / 2) n).norm.pow 2))
  have hint : ∫ β in (0 : ℝ)..1, F1 β < ∫ β in (0 : ℝ)..1, δ ^ 2 * F2 β := by
    rw [intervalIntegral.integral_const_mul]
    show nrm χ (2 * B) < δ ^ 2 * nrm ψ (2 * B)
    rw [hn2]; linarith
  obtain ⟨β, hβ0⟩ := exists_lt_of_integral_lt hc1 (continuous_const.mul hc2) hint
  have hβ : F1 β < δ ^ 2 * F2 β := hβ0
  -- the fibre vector
  set v : L2 ℤ := finVec (fun n => ψ n β) (box (2 * B)) with hv
  have hvψ : ∀ m, ψ m β = v m := by
    intro m
    rw [hv, finVec_apply]
    split_ifs with hm
    · rfl
    · exact opQ_zero hΦ (α / 2) hm β
  have hF1nn : 0 ≤ F1 β := Finset.sum_nonneg (fun n _ => by positivity)
  have hvn : ‖v‖ ^ 2 = F2 β := by
    rw [l2_norm_sq_eq_sum v (box (2 * B)) (fun n hn => by rw [← hvψ]; exact opQ_zero hΦ (α / 2) hn β)]
    show _ = ∑ n ∈ box (2 * B), ‖ψ n β‖ ^ 2
    exact Finset.sum_congr rfl (fun n _ => by rw [hvψ])
  set x := 1 / 4 + α / 2 / 2 + β with hx
  set H := chiral (α / 2) x with hH
  have hHv : ∀ n, (H v - (E : ℂ) • v) n = χ n β := by
    intro n
    rw [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, hH, hx,
      ← chiralOp_fibre β v ψ hvψ n, hχeq, Pi.add_apply, Pi.add_apply, Pi.smul_apply,
      Pi.smul_apply, smul_eq_mul, hvψ]
    ring
  have hHn : ‖H v - (E : ℂ) • v‖ ^ 2 = F1 β := by
    rw [l2_norm_sq_eq_sum _ (box (2 * B)) (fun n hn => by
      rw [hHv, hχ]; exact opQ_zero hY (α / 2) hn β)]
    show _ = ∑ n ∈ box (2 * B), ‖χ n β‖ ^ 2
    exact Finset.sum_congr rfl (fun n _ => by rw [hHv])
  have hF2pos : 0 < F2 β := by nlinarith [pow_pos hδ 2]
  have hv0 : v ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hvn; linarith
  have hbound : ‖H v - (E : ℂ) • v‖ ≤ δ * ‖v‖ := by
    have h1 : ‖H v - (E : ℂ) • v‖ ^ 2 ≤ (δ * ‖v‖) ^ 2 := by
      rw [hHn, mul_pow, hvn]; linarith
    have h2 : 0 ≤ δ * ‖v‖ := by positivity
    have := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq h2] at this
  have hsa : IsSelfAdjoint H :=
    jacobi_isSelfAdjoint (bddFun_const 0) (bddFun_two_sin (2 * π)) (α / 2) x
  obtain ⟨E', hE', hd⟩ := exists_mem_spectrum_near hsa hv0 hbound
  exact ⟨x, E', hE', hd⟩

/-- **Spectral consequence of Theorem 3.1** (used in the proof of Theorem 7.11,
tex l. 1784–1789): `σ(H_{α,θ}) ⊆ closure (⋃_x σ(Ĥ_{α/2,x}))`. -/
theorem amo_spectrum_subset_chiral (α θ : ℝ) :
    spectrum ℝ (amo α θ) ⊆ closure (⋃ x : ℝ, spectrum ℝ (chiral (α / 2) x)) := by
  intro E hE
  rw [Metric.mem_closure_iff]
  intro δ hδ
  have hsa : IsSelfAdjoint (amo α θ) :=
    jacobi_isSelfAdjoint bddFun_two_cos (bddFun_const 1) α θ
  obtain ⟨φ, hφ0, hφ⟩ := exists_approx_eigen hsa hE (ε := δ / 8) (by positivity)
  obtain ⟨u, hu0, ⟨N, hN⟩, hu⟩ := exists_finsupp_approx (by positivity) hφ0 hφ
  have hub : ∀ n, n ∉ box N → u n = 0 := by
    intro n hn
    apply hN
    rw [mem_box] at hn
    rcases not_and_or.1 hn with h | h
    · push Not at h; exact lt_of_lt_of_le (by linarith) (neg_le_abs n)
    · push Not at h; exact lt_of_lt_of_le h (le_abs_self n)
  obtain ⟨L, hL⟩ := exists_nat_gt (256 / δ ^ 2)
  have hLpos : (0 : ℝ) < L := lt_trans (by positivity) hL
  have hεL : 2 * (δ / 4) ^ 2 + 32 / L < (δ / 2) ^ 2 := by
    have h1 : 32 / (L : ℝ) < δ ^ 2 / 8 := by
      rw [div_lt_iff₀ hLpos]
      rw [div_lt_iff₀ (by positivity)] at hL
      nlinarith
    nlinarith
  have happ : ‖amo α θ u - (E : ℂ) • u‖ ≤ δ / 4 * ‖u‖ := by
    have : 2 * (δ / 8) = δ / 4 := by ring
    rw [← this]; exact hu
  obtain ⟨x, E', hE', hd⟩ := exists_fibre α θ E (δ / 4) (δ / 2) L N u hub hu0
    happ (by exact_mod_cast hLpos) (by positivity) hεL
  refine ⟨E', Set.mem_iUnion.2 ⟨x, hE'⟩, ?_⟩
  rw [Real.dist_eq]; linarith

end CAH
