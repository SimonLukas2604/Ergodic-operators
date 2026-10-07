/-
Copyright (c) 2026. Formalization of
  S. Becker, S. Jitomirskaya, I. Krasovsky, "Critical almost Mathieu operator: hidden
  singularity, gap continuity, and the Hausdorff dimension of the spectrum"
  (arXiv:1909.04429v2).

# Isospectrality from the chiral gauge  (paper §3, Theorem 3.1 `chiralrepresentthm`)

TeX references (`Arxiv_version-5.tex`): the operators (3.2)–(3.4) and the even/odd splitting of
`T² + T⁻² + S + S⁻¹` into `M_{2α}^{(1)} ⊕ M_{2α}^{(2)}` (lines ~556–616), Theorem 3.1
(lines ~619–627) and its proof (lines ~630–692).  The consequence `σ(M_{2α}) = σ(M̃_α)` of the
unitary equivalence is what §4 (Lemma 4.1 `dn`, lines ~695–737) and §7 use.

`ChiralSpectrum.lean` proves `σ(H_{α,θ}) ⊆ closure ⋃ₓ σ(Ĥ_{α/2,x})`.  Here we prove the reverse
inclusion `chiral_spectrum_subset_amo` and hence the equality of the direct-integral spectra
`sigmaAMO_eq_chiral : σ(M_α) = closure ⋃ₓ σ(Ĥ_{α/2,x}) = σ(M̃_{α/2})`.

## Method (approximate eigenvectors, run backwards)
1. `E ∈ σ(Ĥ_{α/2,x})` gives a finitely supported `u ≠ 0` with `‖(Ĥ_{α/2,x} - E)u‖ ≤ ε‖u‖`.
2. `Ψ(n,β) = g(β)u(n)` with the trigonometric bump `g` centred at `θ₀ = x - 1/4 - α/4`
   (so that `H̃_{α/2,θ₀} = Ĥ_{α/2,x}`).  Then `‖(M̃ - E)Ψ‖² ≤ (2ε²L + 128)‖u‖²`, `‖Ψ‖² = L‖u‖²`
   (`nrm_Xi_le`, `nrm_Psi`).
3. `Q⁻¹Ψ` explicitly: `U_{-1}Ψ` is a trigonometric polynomial (`rep_Um1`), it has an explicit
   `R`-preimage `ρ` (`exists_R_preimage`, the formula for `R⁻¹` on trigonometric polynomials),
   and `Φ = U_{-1/2} ρ` satisfies `QΦ = Ψ`.  `Φ` is not a trigonometric polynomial on odd sites
   (half-integer frequencies), but `U_{1/2}(T²+T⁻²+S+S⁻¹-E)U_{-1/2}` is a polynomial in
   `S^{±1}, T^{±1}` (`U_doubled`), so `U_{1/2}(T²+T⁻²+S+S⁻¹-E)Φ` *is* a trigonometric polynomial
   and the isometry of `R` (`nrm_opR`) applies.  With Theorem 3.1
   (`ChiralGauge.chiral_representation`) we get
   `‖(T²+T⁻²+S+S⁻¹-E)Φ‖ = ‖(M̃-E)Ψ‖` and `‖Φ‖ = ‖Ψ‖`.
4. Averaging over `β` and splitting into even and odd sites (fibres `H_{α,β}` and
   `H_{α,β+α/2}`, `ChiralGauge.doubled_even/odd`) gives a fibre `H_{α,θ'}` and `v ≠ 0` with
   `‖(H_{α,θ'} - E)v‖ < δ‖v‖`.

## Main results
* `exists_R_preimage` — `R` is onto the trigonometric polynomials (explicit `R⁻¹`);
* `U_doubled` — `U_{1/2}(T²+T⁻²+S+S⁻¹) = (e^{-2πiα}S⁻¹T² + e^{2πiα}T⁻²S + S + S⁻¹)U_{1/2}`;
* `exists_amo_fibre` — the quantitative fibre statement;
* `chiral_spectrum_subset_amo` — `σ(Ĥ_{α/2,x}) ⊆ σ(M_α)`;
* `sigmaAMO_eq_chiral` — `σ(M_α) = closure ⋃ₓ σ(Ĥ_{α/2,x})`, i.e. `σ(M_{2α}) = σ(M̃_α)`.

There are no `sorry`s and no additional hypotheses in this file.
-/
import CriticalAMOHausdorff.ChiralSpectrum

noncomputable section

open Real Complex MeasureTheory L2
open scoped ComplexConjugate

namespace CAH

open ChiralGauge

namespace ChiralUnitary

/-! ### Algebra of `U_x` -/

lemma opU_opU (a x y : ℝ) (φ : Fn) : opU a x (opU a y φ) = opU a (x + y) φ := by
  funext n θ
  simp only [opU]
  rw [← mul_assoc, ← Complex.exp_add]; congr 2; push_cast; ring

lemma opU_zero (a : ℝ) (φ : Fn) : opU a 0 φ = φ := by
  funext n θ; simp [opU]

lemma opU_half_neg (a : ℝ) (φ : Fn) : opU a (1 / 2) (opU a (-(1 / 2)) φ) = φ := by
  rw [opU_opU, add_neg_cancel, opU_zero]

lemma opU_one_neg (a : ℝ) (φ : Fn) : opU a 1 (opU a (-1) φ) = φ := by
  rw [opU_opU, add_neg_cancel, opU_zero]

/-- `U_{1/2} T² = e^{-2πiα} S⁻¹ T² U_{1/2}`. -/
lemma U_TT (a : ℝ) (φ : Fn) : opU a (1 / 2) (opT (opT φ)) =
    cexp (-(2 * π * I * a)) • opS a (-1) (opT (opT (opU a (1 / 2) φ))) := by
  rw [U_T, U_T, opT_smul, opS_smul, T_S, opS_smul, opS_opS, smul_smul, smul_smul,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  · congr 1; push_cast; ring
  · norm_num

/-- `U_{1/2} T⁻² = e^{2πiα} T⁻² S U_{1/2}`. -/
lemma U_TinvTinv (a : ℝ) (φ : Fn) : opU a (1 / 2) (opTinv (opTinv φ)) =
    cexp (2 * π * I * a) • opTinv (opTinv (opS a 1 (opU a (1 / 2) φ))) := by
  rw [U_Tinv, U_Tinv, opS_smul, opTinv_smul, S_Tinv, opTinv_smul, opS_opS, smul_smul,
    smul_smul, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  · congr 1; push_cast; ring
  · norm_num

/-- **Conjugation of the doubled operator by `U_{1/2}`:**
`U_{1/2}(T² + T⁻² + S + S⁻¹) = (e^{-2πiα} S⁻¹T² + e^{2πiα} T⁻²S + S + S⁻¹) U_{1/2}`.
The right-hand side preserves trigonometric polynomials. -/
theorem U_doubled (a : ℝ) (φ : Fn) : opU a (1 / 2) (opDoubled a φ) =
    cexp (-(2 * π * I * a)) • opS a (-1) (opT (opT (opU a (1 / 2) φ))) +
      cexp (2 * π * I * a) • opTinv (opTinv (opS a 1 (opU a (1 / 2) φ))) +
      opS a 1 (opU a (1 / 2) φ) + opS a (-1) (opU a (1 / 2) φ) := by
  simp only [opDoubled]
  rw [opU_add, opU_add, opU_add, U_TT, U_TinvTinv, U_S, U_S]

/-! ### Trigonometric polynomials: `U_{-1}` and the inverse of `R` -/

lemma rep_isGood {ψ : Fn} {B : ℕ} {c : ℤ → ℤ → ℂ} (h : Rep ψ B c) : Good ψ :=
  ⟨⟨box B, fun _k hk => funext fun β => h.zero hk β⟩,
    fun k => (h.continuous k).intervalIntegrable 0 1⟩

lemma good_smul {φ : Fn} (hφ : Good φ) (z : ℂ) : Good (z • φ) :=
  good_mul hφ (fun _ _ => z) (fun _ => continuous_const)

lemma good_doubled {a : ℝ} {φ : Fn} (hφ : Good φ) : Good (opDoubled a φ) :=
  good_add (good_add (good_add (good_opT (good_opT hφ)) (good_opTinv (good_opTinv hφ)))
    (good_opS hφ 1)) (good_opS hφ (-1))

/-- `U_{-1}` on trigonometric polynomials (integer frequency shift by `-n`). -/
lemma rep_Um1 {ψ : Fn} {B : ℕ} {c : ℤ → ℤ → ℂ} (h : Rep ψ B c) (a : ℝ) :
    Rep (opU a (-1) ψ) (2 * B) (fun n m => ex (-((n : ℝ) ^ 2 * a / 2)) * c n (m + n)) := by
  refine ⟨fun n m hnm => ?_, fun n β => ?_⟩
  · obtain ⟨h1, h2⟩ := h.supp _ _ (right_ne_zero_of_mul hnm)
    rw [mem_box] at h1 h2; rw [mem_box, mem_box]; push_cast; omega
  · rw [opU_apply_ex, h.eq]
    refine Eq.trans ?_ ((Equiv.subRight n).tsum_eq _)
    rw [← tsum_mul_left]
    congr 1; funext m
    simp only [Equiv.subRight_apply, sub_add_cancel]
    have e : ex ((n : ℝ) * (-1) * (β + n * a / 2)) * ex (m * β) =
        ex (-((n : ℝ) ^ 2 * a / 2)) * ex (((m - n : ℤ) : ℝ) * β) := by
      rw [← ex_add, ← ex_add]; congr 1; push_cast; ring
    linear_combination (c n m) * e

/-- The coefficients of `R⁻¹ψ` for `ψ(n,θ) = ∑_m d(n,m) e(mθ)`. -/
def rinvCoeff (a : ℝ) (d : ℤ → ℤ → ℂ) : ℤ → ℤ → ℂ := fun k n => d n (-k) * ex (k * n * a)

/-- `R⁻¹ψ` on trigonometric polynomials. -/
def rinv (a : ℝ) (d : ℤ → ℤ → ℂ) : Fn := fun k β => ∑' n, rinvCoeff a d k n * ex (n * β)

lemma rep_rinv {B : ℕ} {d : ℤ → ℤ → ℂ} (hd : ∀ n m, d n m ≠ 0 → n ∈ box B ∧ m ∈ box B)
    (a : ℝ) : Rep (rinv a d) B (rinvCoeff a d) := by
  refine ⟨fun k n hkn => ?_, fun k β => rfl⟩
  obtain ⟨h1, h2⟩ := hd _ _ (left_ne_zero_of_mul hkn)
  rw [mem_box] at h1 h2; rw [mem_box, mem_box]; omega

lemma opR_rinv {ψ : Fn} {B : ℕ} {d : ℤ → ℤ → ℂ} (h : Rep ψ B d) (a : ℝ) :
    opR a (rinv a d) = ψ := by
  funext n θ
  rw [((rep_rinv h.supp a).R a).eq, h.eq]
  congr 1; funext m
  simp only [rinvCoeff, neg_neg]
  have e : ex (((-m : ℤ) : ℝ) * n * a) * ex (m * n * a) = 1 := by
    rw [← ex_add, show ((-m : ℤ) : ℝ) * n * a + m * n * a = 0 by push_cast; ring]
    simp [ex]
  linear_combination (d n m * ex (m * θ)) * e

/-- **`R` is onto the trigonometric polynomials** (explicit inverse `rinv`). -/
theorem exists_R_preimage {ψ : Fn} {B : ℕ} {d : ℤ → ℤ → ℂ} (h : Rep ψ B d) (a : ℝ) :
    ∃ (ρ : Fn) (c : ℤ → ℤ → ℂ), Rep ρ B c ∧ opR a ρ = ψ :=
  ⟨rinv a d, rinvCoeff a d, rep_rinv h.supp a, opR_rinv h a⟩

/-- Conjugated doubled operator on a trigonometric polynomial. -/
lemma repE_conj {ρ : Fn} {B : ℕ} {c : ℤ → ℤ → ℂ} (h : Rep ρ B c) (a E : ℝ) :
    ∃ c', Rep (opU a (1 / 2) (opDoubled a (opU a (-(1 / 2)) ρ) +
      (-(E : ℂ)) • opU a (-(1 / 2)) ρ)) (B + 3) c' := by
  rw [opU_add, opU_smul, U_doubled, opU_half_neg]
  have h1 := ((h.TT.Sm1 a).smul (cexp (-(2 * π * I * a)))).mono (B' := B + 3) (by omega)
  have h2 := ((h.S1 a).TinvTinv.smul (cexp (2 * π * I * a))).mono (B' := B + 3) (by omega)
  have h3 := (h.S1 a).mono (B' := B + 3) (by omega)
  have h4 := (h.Sm1 a).mono (B' := B + 3) (by omega)
  have h5 := (h.smul (-(E : ℂ))).mono (B' := B + 3) (by omega)
  exact ⟨_, (((h1.add h2).add h3).add h4).add h5⟩

/-! ### The chiral test function -/

/-- `Ψ(n,β) = g(β) u(n)`. -/
def Psi (θ : ℝ) (L : ℕ) (u : L2 ℤ) : Fn := fun n β => gfun θ L β * u n

lemma rep_Psi (θ : ℝ) (L N0 : ℕ) (u : L2 ℤ) (hu : ∀ n, n ∉ box N0 → u n = 0) :
    Rep (Psi θ L u) (N0 + L) (fun n m => if m ∈ sL L then u n * ex (-(m * θ)) else 0) := by
  refine ⟨fun n m hnm => ?_, fun n β => ?_⟩
  · beta_reduce at hnm
    split_ifs at hnm with hm
    · have hu0 : u n ≠ 0 := left_ne_zero_of_mul hnm
      have h1 : n ∈ box N0 := by by_contra h'; exact hu0 (hu _ h')
      rw [mem_sL] at hm
      rw [mem_box] at h1; rw [mem_box, mem_box]; push_cast; omega
    · exact absurd rfl hnm
  · beta_reduce
    rw [tsum_eq_sum (s := sL L) (fun m hm => by simp [hm])]
    simp only [Psi]
    rw [gfun_eq, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun m hm => ?_)
    simp only [hm, ↓reduceIte]; ring

lemma nrm_Psi (θ : ℝ) (L N0 B : ℕ) (u : L2 ℤ) (hu : ∀ n, n ∉ box N0 → u n = 0)
    (hB : N0 ≤ B) : nrm (Psi θ L u) B = L * ‖u‖ ^ 2 := by
  have hpt : ∀ β, ∑ n ∈ box B, ‖Psi θ L u n β‖ ^ 2 = ‖gfun θ L β‖ ^ 2 * ‖u‖ ^ 2 := by
    intro β
    rw [l2_norm_sq_eq_sum u (box B) (fun n hn => hu n (fun h => hn (box_mono hB h))),
      Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    show ‖gfun θ L β * u j‖ ^ 2 = _
    rw [norm_mul, mul_pow]
  unfold nrm
  simp_rw [hpt]
  rw [intervalIntegral.integral_mul_const, integral_gfun]

/-- `2 sin 2πt` as a complex number. -/
def sn (t : ℝ) : ℂ := ((2 * Real.sin (2 * π * t) : ℝ) : ℂ)

lemma chiral_apply' (a x : ℝ) (u : L2 ℤ) (n : ℤ) :
    chiral a x u n = sn (x + (n - 1) * a) * u (n - 1) + sn (x + n * a) * u (n + 1) := by
  simp only [chiral, jacobi_apply (bddFun_const 0) (bddFun_two_sin _), sn]
  simp

lemma sn_ex (x : ℝ) : sn x = (ex (-x) - ex x) * I := by
  simp only [sn, ex]
  push_cast
  rw [Complex.two_sin]
  ring_nf

lemma norm_sn_sub_le (x y : ℝ) : ‖sn x - sn y‖ ≤ 2 * ‖ex (x - y) - 1‖ := by
  rw [sn_ex, sn_ex]
  have h1 : ex x - ex y = ex y * (ex (x - y) - 1) := by
    rw [mul_sub, mul_one, ← ex_add, show y + (x - y) = x by ring]
  have h2 : ex (-x) - ex (-y) = ex (-x) * (1 - ex (x - y)) := by
    rw [mul_sub, mul_one, ← ex_add, show -x + (x - y) = -y by ring]
  calc ‖(ex (-x) - ex x) * I - (ex (-y) - ex y) * I‖ =
        ‖(ex (-x) - ex (-y)) - (ex x - ex y)‖ := by
        rw [← sub_mul, norm_mul, Complex.norm_I, mul_one]; congr 1; ring
    _ ≤ ‖ex (-x) - ex (-y)‖ + ‖ex x - ex y‖ := norm_sub_le _ _
    _ = 2 * ‖ex (x - y) - 1‖ := by
        rw [h1, h2, norm_mul, norm_mul, norm_ex, norm_ex, norm_sub_rev 1]; ring

lemma norm_g_sn_le (a θ β t : ℝ) (L : ℕ) :
    ‖gfun θ L β * (sn (1 / 4 + a / 2 + β + t) - sn (1 / 4 + a / 2 + θ + t))‖ ≤ 4 := by
  have h1 := norm_sn_sub_le (1 / 4 + a / 2 + β + t) (1 / 4 + a / 2 + θ + t)
  rw [show 1 / 4 + a / 2 + β + t - (1 / 4 + a / 2 + θ + t) = β - θ by ring] at h1
  have h2 := norm_gfun_mul_le θ L β
  rw [norm_mul] at h2
  rw [norm_mul]
  calc ‖gfun θ L β‖ * ‖sn (1 / 4 + a / 2 + β + t) - sn (1 / 4 + a / 2 + θ + t)‖ ≤
        ‖gfun θ L β‖ * (2 * ‖ex (β - θ) - 1‖) := by gcongr
    _ = 2 * (‖gfun θ L β‖ * ‖ex (β - θ) - 1‖) := by ring
    _ ≤ 4 := by linarith

lemma Xi_apply (a θ E : ℝ) (L : ℕ) (u : L2 ℤ) (n : ℤ) (β : ℝ) :
    (opHt a (Psi θ L u) + (-(E : ℂ)) • Psi θ L u) n β =
      gfun θ L β * (chiral a (1 / 4 + a / 2 + β) u n - E * u n) := by
  have hφ : ∀ m, Psi θ L u m β = (gfun θ L β • u) m := by
    intro m; rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]; rfl
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [chiralOp_fibre β _ _ hφ n, map_smul, hφ n]
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  ring

lemma sum_le_norm_sq (x : L2 ℤ) (s : Finset ℤ) : ∑ n ∈ s, ‖x n‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  have h := lp.sum_rpow_le_norm_rpow (E := fun _ : ℤ => ℂ) (p := 2) (by norm_num) x s
  have e : (2 : ENNReal).toReal = ((2 : ℕ) : ℝ) := by norm_num
  simp only [e, Real.rpow_natCast] at h
  exact h

lemma sum_sub_one_le (x : L2 ℤ) (s : Finset ℤ) : ∑ n ∈ s, ‖x (n - 1)‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  have := sum_le_norm_sq x (s.map (Equiv.subRight (1 : ℤ)).toEmbedding)
  rwa [Finset.sum_map] at this

lemma sum_add_one_le (x : L2 ℤ) (s : Finset ℤ) : ∑ n ∈ s, ‖x (n + 1)‖ ^ 2 ≤ ‖x‖ ^ 2 := by
  have := sum_le_norm_sq x (s.map (Equiv.addRight (1 : ℤ)).toEmbedding)
  rwa [Finset.sum_map] at this

lemma nrm_Xi_le (a θ E ε : ℝ) (L B : ℕ) (u : L2 ℤ)
    (happ : ‖chiral a (1 / 4 + a / 2 + θ) u - (E : ℂ) • u‖ ≤ ε * ‖u‖) :
    nrm (opHt a (Psi θ L u) + (-(E : ℂ)) • Psi θ L u) B ≤ (2 * ε ^ 2 * L + 128) * ‖u‖ ^ 2 := by
  set w : L2 ℤ := chiral a (1 / 4 + a / 2 + θ) u - (E : ℂ) • u with hw
  have hwj : ∀ j, w j = chiral a (1 / 4 + a / 2 + θ) u j - E * u j := fun j => by
    rw [hw, lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  have hwn : ‖w‖ ^ 2 ≤ ε ^ 2 * ‖u‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) happ 2
  have hpt : ∀ β, ∑ n ∈ box B, ‖(opHt a (Psi θ L u) + (-(E : ℂ)) • Psi θ L u) n β‖ ^ 2 ≤
      ‖gfun θ L β‖ ^ 2 * (2 * ‖w‖ ^ 2) + 128 * ‖u‖ ^ 2 := by
    intro β
    have hs1 := sum_le_norm_sq w (box B)
    have hs2 := sum_sub_one_le u (box B)
    have hs3 := sum_add_one_le u (box B)
    calc _ ≤ ∑ n ∈ box B, (‖gfun θ L β‖ ^ 2 * (2 * ‖w n‖ ^ 2) + 64 * ‖u (n - 1)‖ ^ 2 +
            64 * ‖u (n + 1)‖ ^ 2) := by
          refine Finset.sum_le_sum (fun n _ => ?_)
          rw [Xi_apply]
          have hsplit : chiral a (1 / 4 + a / 2 + β) u n - E * u n = w n +
              ((sn (1 / 4 + a / 2 + β + (n - 1) * a) - sn (1 / 4 + a / 2 + θ + (n - 1) * a)) *
                u (n - 1) + (sn (1 / 4 + a / 2 + β + n * a) - sn (1 / 4 + a / 2 + θ + n * a)) *
                u (n + 1)) := by
            rw [hwj, chiral_apply', chiral_apply']; ring
          have hb1 := norm_g_sn_le a θ β ((n - 1) * a) L
          have hb2 := norm_g_sn_le a θ β (n * a) L
          set g := gfun θ L β
          have htri : ‖g * (chiral a (1 / 4 + a / 2 + β) u n - E * u n)‖ ≤
              ‖g‖ * ‖w n‖ + 4 * ‖u (n - 1)‖ + 4 * ‖u (n + 1)‖ := by
            rw [hsplit]
            have e : g * (w n + ((sn (1 / 4 + a / 2 + β + (n - 1) * a) -
                sn (1 / 4 + a / 2 + θ + (n - 1) * a)) * u (n - 1) +
                (sn (1 / 4 + a / 2 + β + n * a) - sn (1 / 4 + a / 2 + θ + n * a)) * u (n + 1))) =
                g * w n + (g * (sn (1 / 4 + a / 2 + β + (n - 1) * a) -
                  sn (1 / 4 + a / 2 + θ + (n - 1) * a))) * u (n - 1) +
                (g * (sn (1 / 4 + a / 2 + β + n * a) - sn (1 / 4 + a / 2 + θ + n * a))) *
                  u (n + 1) := by ring
            rw [e]
            refine (norm_add_le _ _).trans ?_
            refine (add_le_add (norm_add_le _ _) le_rfl).trans ?_
            rw [norm_mul g (w n), norm_mul _ (u (n - 1)), norm_mul _ (u (n + 1))]
            linarith [mul_le_mul_of_nonneg_right hb1 (norm_nonneg (u (n - 1))),
              mul_le_mul_of_nonneg_right hb2 (norm_nonneg (u (n + 1)))]
          have hA := norm_nonneg (g * (chiral a (1 / 4 + a / 2 + β) u n - E * u n))
          have hP : 0 ≤ ‖g‖ * ‖w n‖ := by positivity
          have hQ := norm_nonneg (u (n - 1))
          have hR := norm_nonneg (u (n + 1))
          nlinarith [mul_le_mul htri htri hA (by positivity),
            sq_nonneg (‖g‖ * ‖w n‖ - (4 * ‖u (n - 1)‖ + 4 * ‖u (n + 1)‖)),
            sq_nonneg (‖u (n - 1)‖ - ‖u (n + 1)‖)]
      _ = ‖gfun θ L β‖ ^ 2 * (2 * ∑ n ∈ box B, ‖w n‖ ^ 2) +
            64 * ∑ n ∈ box B, ‖u (n - 1)‖ ^ 2 + 64 * ∑ n ∈ box B, ‖u (n + 1)‖ ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
            ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ _ := by
          have := mul_le_mul_of_nonneg_left hs1 (sq_nonneg ‖gfun θ L β‖)
          nlinarith
  have hint : ∫ β in (0 : ℝ)..1, (‖gfun θ L β‖ ^ 2 * (2 * ‖w‖ ^ 2) + 128 * ‖u‖ ^ 2) =
      L * (2 * ‖w‖ ^ 2) + 128 * ‖u‖ ^ 2 := by
    rw [intervalIntegral.integral_add ((by fun_prop : Continuous fun β =>
      ‖gfun θ L β‖ ^ 2 * (2 * ‖w‖ ^ 2)).intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_mul_const, integral_gfun, intervalIntegral.integral_const]
    simp
  have hcont : ∀ n, Continuous (fun β => (opHt a (Psi θ L u) + (-(E : ℂ)) • Psi θ L u) n β) := by
    intro n
    simp only [Xi_apply, chiral_apply', sn]
    fun_prop
  have hle : nrm (opHt a (Psi θ L u) + (-(E : ℂ)) • Psi θ L u) B ≤
      L * (2 * ‖w‖ ^ 2) + 128 * ‖u‖ ^ 2 := by
    rw [← hint]
    unfold nrm
    refine intervalIntegral.integral_mono_on zero_le_one ?_ ?_ (fun β _ => hpt β)
    · exact (continuous_finsetSum _ (fun n _ => (hcont n).norm.pow 2)).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun β =>
        ‖gfun θ L β‖ ^ 2 * (2 * ‖w‖ ^ 2) + 128 * ‖u‖ ^ 2).intervalIntegrable _ _
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hwn hL0]

/-! ### Even/odd splitting of finite sums -/

lemma sum_split (f : ℤ → ℝ) (B : ℕ) (hf : ∀ n, n ∉ box (2 * B) → f n = 0) :
    ∑ n ∈ box (2 * B), f n = ∑ j ∈ box B, f (2 * j) + ∑ j ∈ box B, f (2 * j + 1) := by
  classical
  have hA : Set.InjOn (fun j : ℤ => 2 * j) (box B) := fun x _ y _ h => by
    simp only at h; omega
  have hC : Set.InjOn (fun j : ℤ => 2 * j + 1) (box B) := fun x _ y _ h => by
    simp only at h; omega
  have hdisj : Disjoint ((box B).image (fun j : ℤ => 2 * j))
      ((box B).image (fun j : ℤ => 2 * j + 1)) := by
    rw [Finset.disjoint_left]
    intro n hnA hnC
    simp only [Finset.mem_image] at hnA hnC
    obtain ⟨j, -, rfl⟩ := hnA
    obtain ⟨k, -, hk⟩ := hnC
    omega
  have hsub : box (2 * B) ⊆ (box B).image (fun j : ℤ => 2 * j) ∪
      (box B).image (fun j : ℤ => 2 * j + 1) := by
    intro n hn
    rw [Finset.mem_union, Finset.mem_image, Finset.mem_image]
    rw [mem_box] at hn; push_cast at hn
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · left; exact ⟨n / 2, by rw [mem_box]; omega, by omega⟩
    · right; exact ⟨n / 2, by rw [mem_box]; omega, by omega⟩
  rw [Finset.sum_subset hsub (fun x _ hx => hf x hx), Finset.sum_union hdisj,
    Finset.sum_image hA, Finset.sum_image hC]

/-! ### The fibre statement and the reverse inclusion -/

/-- **Quantitative fibre statement (reverse direction).**  If `u ≠ 0` is supported in
`[-N₀,N₀]` with `‖(Ĥ_{a,1/4+a/2+θ} - E)u‖ ≤ ε‖u‖` (i.e. `‖(H̃_{a,θ} - E)u‖ ≤ ε‖u‖`) and
`2ε² + 128/L < δ²`, then some almost Mathieu fibre `H_{2a,θ'}` has spectrum within `δ` of `E`. -/
theorem exists_amo_fibre (a θ E ε δ : ℝ) (L N0 : ℕ) (u : L2 ℤ)
    (hu : ∀ n, n ∉ box N0 → u n = 0) (hu0 : u ≠ 0)
    (happ : ‖chiral a (1 / 4 + a / 2 + θ) u - (E : ℂ) • u‖ ≤ ε * ‖u‖) (hL : 0 < L)
    (hδ : 0 < δ) (hεL : 2 * ε ^ 2 + 128 / L < δ ^ 2) :
    ∃ θ' E', E' ∈ spectrum ℝ (amo (2 * a) θ') ∧ |E - E'| ≤ δ := by
  obtain ⟨dΨ, hΨ⟩ : ∃ d, Rep (Psi θ L u) (N0 + L) d := ⟨_, rep_Psi θ L N0 u hu⟩
  obtain ⟨ρ, cρ, hρ, hRρ⟩ := exists_R_preimage (rep_Um1 hΨ a) a
  set Bs := 2 * (N0 + L) + 3 with hBs
  set Bm := 2 * (Bs + 1) with hBm
  set Φ := opU a (-(1 / 2)) ρ with hΦdef
  set X := opDoubled a Φ + (-(E : ℂ)) • Φ with hXdef
  set χ := opU a (1 / 2) X with hχdef
  obtain ⟨cχ, hχ⟩ : ∃ c', Rep χ Bs c' := repE_conj hρ a E
  set Ξ := opHt a (Psi θ L u) + (-(E : ℂ)) • Psi θ L u with hΞdef
  -- `QΦ = Ψ` and Theorem 3.1
  have hQΦ : opQ a Φ = Psi θ L u := by
    show opU a 1 (opR a (opU a (1 / 2) (opU a (-(1 / 2)) ρ))) = _
    rw [opU_half_neg, hRρ, opU_one_neg]
  have hΦg : Good Φ := good_opU (rep_isGood hρ) _
  have hQX : opQ a X = Ξ := by
    rw [hXdef, opQ_add (good_doubled hΦg) (good_smul hΦg _), chiral_representation hΦg,
      opQ_smul, hQΦ]
  -- norms
  have hnχ : nrm χ Bm = nrm Ξ Bm := by
    rw [← hQX, ← nrm_opR (hχ.mono (B' := Bm) (by omega)) a, ← nrm_opU a 1 (opR a χ) Bm]
    rfl
  have hnρ : nrm ρ Bm = L * ‖u‖ ^ 2 := by
    rw [← nrm_opR (hρ.mono (B' := Bm) (by omega)) a, hRρ, nrm_opU]
    exact nrm_Psi θ L N0 Bm u hu (by omega)
  have hnΞ : nrm Ξ Bm ≤ (2 * ε ^ 2 * L + 128) * ‖u‖ ^ 2 := nrm_Xi_le a θ E ε L Bm u happ
  have hupos : 0 < ‖u‖ ^ 2 := by positivity
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hlt : (2 * ε ^ 2 * L + 128) * ‖u‖ ^ 2 < δ ^ 2 * (L * ‖u‖ ^ 2) := by
    have : 2 * ε ^ 2 * L + 128 < δ ^ 2 * L := by
      have h1 : (2 * ε ^ 2 + 128 / L) * L < δ ^ 2 * L := mul_lt_mul_of_pos_right hεL hLpos
      rwa [add_mul, div_mul_cancel₀ _ hLpos.ne'] at h1
    nlinarith [mul_lt_mul_of_pos_right this hupos]
  -- averaging
  set F1 : ℝ → ℝ := fun β => ∑ n ∈ box Bm, ‖χ n β‖ ^ 2 with hF1
  set F2 : ℝ → ℝ := fun β => ∑ n ∈ box Bm, ‖ρ n β‖ ^ 2 with hF2
  have hc1 : Continuous F1 :=
    continuous_finsetSum _ (fun n _ => (hχ.continuous n).norm.pow 2)
  have hc2 : Continuous F2 :=
    continuous_finsetSum _ (fun n _ => (hρ.continuous n).norm.pow 2)
  have hint : ∫ β in (0 : ℝ)..1, F1 β < ∫ β in (0 : ℝ)..1, δ ^ 2 * F2 β := by
    rw [intervalIntegral.integral_const_mul]
    show nrm χ Bm < δ ^ 2 * nrm ρ Bm
    rw [hnχ, hnρ]; linarith
  obtain ⟨β, hβ0⟩ := exists_lt_of_integral_lt hc1 (continuous_const.mul hc2) hint
  have hβ : F1 β < δ ^ 2 * F2 β := hβ0
  -- vanishing and norms at the fibre `β`
  have hρz : ∀ n, n ∉ box Bs → ρ n β = 0 :=
    fun n hn => (hρ.mono (B' := Bs) (by omega)).zero hn β
  have hΦz : ∀ n, n ∉ box Bs → Φ n β = 0 := by
    intro n hn
    show opU a (-(1 / 2)) ρ n β = 0
    rw [opU_apply_ex, hρz n hn, mul_zero]
  have hXn : ∀ n, ‖X n β‖ = ‖χ n β‖ := fun n => (norm_opU a (1 / 2) X n β).symm
  have hΦn : ∀ n, ‖Φ n β‖ = ‖ρ n β‖ := fun n => norm_opU a _ ρ n β
  have hXz : ∀ n, n ∉ box Bs → X n β = 0 := by
    intro n hn; rw [← norm_eq_zero, hXn, hχ.zero hn, norm_zero]
  -- even and odd fibre vectors
  set ve : L2 ℤ := finVec (fun j => Φ (2 * j) β) (box Bs) with hve
  set vo : L2 ℤ := finVec (fun j => Φ (2 * j + 1) β) (box Bs) with hvo
  have hφe : ∀ m, Φ (2 * m) β = ve m := by
    intro m; rw [hve, finVec_apply]; split_ifs with hm
    · rfl
    · exact hΦz _ (by rw [mem_box] at hm ⊢; omega)
  have hφo : ∀ m, Φ (2 * m + 1) β = vo m := by
    intro m; rw [hvo, finVec_apply]; split_ifs with hm
    · rfl
    · exact hΦz _ (by rw [mem_box] at hm ⊢; omega)
  have hvez : ∀ n, n ∉ box Bs → ve n = 0 := by
    intro n hn; rw [hve, finVec_apply]; simp [hn]
  have hvoz : ∀ n, n ∉ box Bs → vo n = 0 := by
    intro n hn; rw [hvo, finVec_apply]; simp [hn]
  set Ae : L2 ℤ := amo (2 * a) β ve - (E : ℂ) • ve with hAedef
  set Ao : L2 ℤ := amo (2 * a) (β + a) vo - (E : ℂ) • vo with hAodef
  have hAe : ∀ j, X (2 * j) β = Ae j := by
    intro j
    rw [hXdef]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [doubled_even β ve Φ hφe j, hφe j, hAedef]
    simp only [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    ring
  have hAo : ∀ j, X (2 * j + 1) β = Ao j := by
    intro j
    rw [hXdef]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [doubled_odd β vo Φ hφo j, hφo j, hAodef]
    simp only [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    ring
  have hAez : ∀ j, j ∉ box (Bs + 1) → Ae j = 0 := by
    intro j hj
    rw [hAedef]
    simp only [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    rw [amo_apply_zero (2 * a) β ve Bs hvez hj, hvez j (fun h => hj (box_mono (by omega) h))]
    simp
  have hAoz : ∀ j, j ∉ box (Bs + 1) → Ao j = 0 := by
    intro j hj
    rw [hAodef]
    simp only [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
    rw [amo_apply_zero (2 * a) (β + a) vo Bs hvoz hj,
      hvoz j (fun h => hj (box_mono (by omega) h))]
    simp
  have hF1eq : F1 β = ‖Ae‖ ^ 2 + ‖Ao‖ ^ 2 := by
    show ∑ n ∈ box Bm, ‖χ n β‖ ^ 2 = _
    simp_rw [← hXn]
    refine (sum_split (fun n => ‖X n β‖ ^ 2) (Bs + 1) ?_).trans ?_
    · intro n hn
      show ‖X n β‖ ^ 2 = 0
      rw [hXz n (fun h => hn (box_mono (by omega) h))]; simp
    · rw [l2_norm_sq_eq_sum Ae (box (Bs + 1)) hAez, l2_norm_sq_eq_sum Ao (box (Bs + 1)) hAoz]
      simp only [hAe, hAo]
  have hF2eq : F2 β = ‖ve‖ ^ 2 + ‖vo‖ ^ 2 := by
    show ∑ n ∈ box Bm, ‖ρ n β‖ ^ 2 = _
    simp_rw [← hΦn]
    refine (sum_split (fun n => ‖Φ n β‖ ^ 2) (Bs + 1) ?_).trans ?_
    · intro n hn
      show ‖Φ n β‖ ^ 2 = 0
      rw [hΦz n (fun h => hn (box_mono (by omega) h))]; simp
    · rw [l2_norm_sq_eq_sum ve (box (Bs + 1))
        (fun n hn => hvez n (fun h => hn (box_mono (by omega) h))),
        l2_norm_sq_eq_sum vo (box (Bs + 1))
        (fun n hn => hvoz n (fun h => hn (box_mono (by omega) h)))]
      simp only [hφe, hφo]
  have hβ' : ‖Ae‖ ^ 2 + ‖Ao‖ ^ 2 < δ ^ 2 * (‖ve‖ ^ 2 + ‖vo‖ ^ 2) := by
    rw [← hF1eq, ← hF2eq]; exact hβ
  -- one of the two fibres has an approximate eigenvector
  have key : ∀ (H : Op) (v : L2 ℤ), IsSelfAdjoint H →
      ‖H v - (E : ℂ) • v‖ ^ 2 < δ ^ 2 * ‖v‖ ^ 2 → ∃ E' ∈ spectrum ℝ H, |E - E'| ≤ δ := by
    intro H v hH hlt'
    have hv0 : v ≠ 0 := by
      intro h0; subst h0; simp at hlt'
    have hb : ‖H v - (E : ℂ) • v‖ ≤ δ * ‖v‖ := by
      have h2 : 0 ≤ δ * ‖v‖ := by positivity
      rcases le_or_gt ‖H v - (E : ℂ) • v‖ (δ * ‖v‖) with h | h
      · exact h
      · nlinarith [mul_self_lt_mul_self h2 h]
    exact exists_mem_spectrum_near hH hv0 hb
  rcases lt_or_ge (‖Ae‖ ^ 2) (δ ^ 2 * ‖ve‖ ^ 2) with h | h
  · obtain ⟨E', hE', hd⟩ := key _ ve
      (jacobi_isSelfAdjoint bddFun_two_cos (bddFun_const 1) _ _) h
    exact ⟨β, E', hE', hd⟩
  · have h' : ‖Ao‖ ^ 2 < δ ^ 2 * ‖vo‖ ^ 2 := by nlinarith
    obtain ⟨E', hE', hd⟩ := key _ vo
      (jacobi_isSelfAdjoint bddFun_two_cos (bddFun_const 1) _ _) h'
    exact ⟨β + a, E', hE', hd⟩

end ChiralUnitary

open ChiralUnitary

/-- **Reverse spectral inclusion from Theorem 3.1:**
`σ(Ĥ_{α/2,x}) ⊆ σ(M_α) = closure (⋃_θ σ(H_{α,θ}))` for all `α, x ∈ ℝ`. -/
theorem chiral_spectrum_subset_amo (α x : ℝ) :
    spectrum ℝ (chiral (α / 2) x) ⊆ closure (⋃ θ : ℝ, spectrum ℝ (amo α θ)) := by
  intro E hE
  rw [Metric.mem_closure_iff]
  intro δ hδ
  have hsa : IsSelfAdjoint (chiral (α / 2) x) :=
    jacobi_isSelfAdjoint (bddFun_const 0) (bddFun_two_sin (2 * π)) (α / 2) x
  obtain ⟨φ, hφ0, hφ⟩ := exists_approx_eigen hsa hE (ε := δ / 8) (by positivity)
  obtain ⟨u, hu0, ⟨N, hN⟩, hu⟩ := exists_finsupp_approx (by positivity) hφ0 hφ
  have hub : ∀ n, n ∉ box N → u n = 0 := by
    intro n hn
    apply hN
    rw [mem_box] at hn
    rcases not_and_or.1 hn with h | h
    · push Not at h; exact lt_of_lt_of_le (by linarith) (neg_le_abs n)
    · push Not at h; exact lt_of_lt_of_le h (le_abs_self n)
  obtain ⟨L, hL⟩ := exists_nat_gt (2048 / δ ^ 2)
  have hLpos : (0 : ℝ) < L := lt_trans (by positivity) hL
  have hεL : 2 * (δ / 4) ^ 2 + 128 / L < (δ / 2) ^ 2 := by
    have h1 : 128 / (L : ℝ) < δ ^ 2 / 8 := by
      rw [div_lt_iff₀ hLpos]
      rw [div_lt_iff₀ (by positivity)] at hL
      nlinarith
    nlinarith
  set θ0 := x - 1 / 4 - α / 2 / 2 with hθ0
  have hx : 1 / 4 + α / 2 / 2 + θ0 = x := by rw [hθ0]; ring
  have happ : ‖chiral (α / 2) (1 / 4 + α / 2 / 2 + θ0) u - (E : ℂ) • u‖ ≤ δ / 4 * ‖u‖ := by
    rw [hx, show δ / 4 = 2 * (δ / 8) by ring]; exact hu
  obtain ⟨θ', E', hE', hd⟩ := exists_amo_fibre (α / 2) θ0 E (δ / 4) (δ / 2) L N u hub hu0
    happ (by exact_mod_cast hLpos) (by positivity) hεL
  rw [show 2 * (α / 2) = α by ring] at hE'
  refine ⟨E', Set.mem_iUnion.2 ⟨θ', hE'⟩, ?_⟩
  rw [Real.dist_eq]; linarith

/-- **Isospectrality of the direct integrals (consequence of Theorem 3.1).**
`σ(M_α) = closure (⋃ₓ σ(Ĥ_{α/2,x}))`; since `H̃_{α/2,θ} = Ĥ_{α/2,1/4+α/4+θ}`, the right side is
`σ(M̃_{α/2})`.  Equivalently `σ(M_{2α}) = σ(M̃_α)` (tex l. ~610–627, used in §4 and §7). -/
theorem sigmaAMO_eq_chiral (α : ℝ) :
    sigmaAMO α = closure (⋃ x : ℝ, spectrum ℝ (chiral (α / 2) x)) := by
  unfold sigmaAMO
  apply Set.Subset.antisymm
  · exact closure_minimal (Set.iUnion_subset fun θ => amo_spectrum_subset_chiral α θ)
      isClosed_closure
  · exact closure_minimal (Set.iUnion_subset fun x => chiral_spectrum_subset_amo α x)
      isClosed_closure

end CAH
