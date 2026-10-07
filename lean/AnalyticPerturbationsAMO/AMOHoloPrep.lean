/-
# The AMO first preparation is holomorphic in the energy

For `H = U + U^{-1} + η(V + V^{-1}) + R` the first preparation of `H - E` (Lemma 2.1 with
`a₀ = 1`, `c₀ = 1/4`, `w = η(V + V^{-1}) - E`) extends to complex `E` in the disc `|E| < M`
on which `e^{-s}(2|η|e^ℓ + M) + e^{-2s} ≤ 1/4`:

* `amo_holo_prep`: there are `K(E)`, `L(E)`, `j(E)`, holomorphic on `|E| < M`, with
  `(I + L)(J₀(E) + j)(I + K) = J₀(E) + R`, `‖K‖, ‖L‖, κ‖j‖ ≤ (16/9) e^{-s}‖R‖`, and
  `L = K^*`, `j = j^*` at real `E` (the self-adjoint factorization of Lemma 2.1);
* `amo_coef_deriv_bound`: every Fourier coefficient function `a_r^{(j)}(E; z)` of the Jacobi
  correction (`z` in the strip `|Im z| ≤ ℓ/2π`) satisfies, for real `t` with
  `closedBall t ρ ⊆ {|E| < M}`,
    `|∂_E^n a_r^{(j)}(t; z)| ≤ n! ρ^{-n} κ^{-1} (16/9) e^{-s} ‖R‖`,
  which is the `C²_E` estimate `d-eq:C1` (with the paper's `ρ = 1/4`).

This removes the holomorphy hypothesis on the first-preparation coefficients from the `C²_E`
results.  Everything here is proved.
-/
import AnalyticPerturbationsAMO.ScaledPrepHolo
import AnalyticPerturbationsAMO.FirstPreparation
import AnalyticPerturbationsAMO.EnergyDerivatives
import AnalyticPerturbationsAMO.TailSymbol

noncomputable section

open scoped ComplexConjugate
open Metric

namespace AMO

namespace AMOHolo

variable (ω : Weights) (α η : ℝ)

/-! ### The complex phase coefficient -/

/-- The symbol of `η(V + V^{-1}) - E` for complex `E`. -/
def wsymC (E : ℂ) : Symbol :=
  Pi.single (0, 1) (η : ℂ) + Pi.single (0, -1) (η : ℂ) - Pi.single ((0 : ℤ), (0 : ℤ)) E

lemma wsymC_eq (E : ℂ) : wsymC η E = wsym η 0 - E • Pi.single ((0 : ℤ), (0 : ℤ)) (1 : ℂ) := by
  funext p
  simp only [wsymC, wsym, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply,
    Complex.ofReal_zero, smul_eq_mul]
  split_ifs <;> simp

lemma single00_wsum : WSum ω.s ω.ℓ (Pi.single ((0 : ℤ), (0 : ℤ)) (1 : ℂ)) := single_wsum _ _

lemma single00_hop : HopGE (Pi.single ((0 : ℤ), (0 : ℤ)) (1 : ℂ)) 0 ∧
    HopLE (Pi.single ((0 : ℤ), (0 : ℤ)) (1 : ℂ)) 0 := by
  constructor <;> intro p hp <;> obtain ⟨a, b⟩ := p <;> simp only at hp <;>
    simp [Pi.single_apply, Prod.ext_iff] <;> omega

lemma wsymC_wsum (E : ℂ) : WSum ω.s ω.ℓ (wsymC η E) := by
  rw [wsymC_eq]
  have h1 := wsym_wsum ω.s ω.ℓ η 0
  have h2 := WSum.csmul (single00_wsum ω) E
  unfold WSum at *
  refine (h1.add h2).of_nonneg_of_le (fun p => mul_nonneg (norm_nonneg _) (wt_pos p).le)
    fun p => ?_
  rw [← add_mul]
  exact mul_le_mul_of_nonneg_right (norm_sub_le _ _) (wt_pos p).le

lemma wsymC_hop (E : ℂ) : HopGE (wsymC η E) 0 ∧ HopLE (wsymC η E) 0 := by
  rw [wsymC_eq]
  refine ⟨(wsym_hop η 0).1.sub ((single00_hop).1.smul E), fun p hp => ?_⟩
  simp only [Pi.sub_apply, Pi.smul_apply, (wsym_hop η 0).2 p hp, (single00_hop).2 p hp,
    smul_zero, sub_zero]

/-- `w(E)` as an element of `𝒲_{s,ℓ}`. -/
def wC (E : ℂ) : WA := ω.ofS (wsymC η E) (wsymC_wsum ω η E)

/-- `w(E) = w(0) - E · 1`. -/
lemma wC_eq (E : ℂ) : wC ω η E = wC ω η 0 - E • ω.ofS _ (single00_wsum ω) := by
  apply ω.toS_injective
  rw [ω.toS_sub, ω.toS_smul]
  simp only [wC, Weights.toS_ofS]
  rw [wsymC_eq, wsymC_eq, zero_smul, sub_zero]

lemma wC_diff : Differentiable ℂ (wC ω η) := by
  have : wC ω η = fun E => wC ω η 0 - E • ω.ofS _ (single00_wsum ω) := funext (wC_eq ω η)
  rw [this]
  fun_prop

lemma norm_wC_le (E : ℂ) : ‖wC ω η E‖ ≤ 2 * |η| * Real.exp ω.ℓ + ‖E‖ := by
  rw [wC_eq]
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · rw [wC, Weights.norm_ofS]
    have h := wnorm_wsym_le ω.s ω.ℓ η 0
    have e : wsymC η 0 = wsym η 0 := by rw [wsymC_eq, zero_smul, sub_zero]
    rw [e]; simpa using h
  · rw [norm_smul, Weights.norm_ofS, wnorm_single]
    simp [wt]

/-! ### The family of data -/

variable {ω η}

/-- Lemma 2.1 data with `a₀ = 1`, `c₀ = 1/4` and phase coefficient `w`. -/
def mkData (w : WA) (hge : HopGE (ω.toS w) 0) (hle : HopLE (ω.toS w) 0)
    (hs : Real.exp (-ω.s) * ‖w‖ + Real.exp (-ω.s) * Real.exp (-ω.s) ≤ 1 / 4) :
    ScaledPrep.HData ω where
  a0 := 1
  ha0 := one_pos
  c0 := 1 / 4
  hc0 := by norm_num
  hc1 := by norm_num
  w := w
  w_ge := hge
  w_le := hle
  hsmall := by rw [div_one]; exact hs

lemma toS_wC (E : ℂ) : ω.toS (wC ω η E) = wsymC η E := Weights.toS_ofS _ _ _

variable {M : ℝ}

lemma small_of_lt (hM : Real.exp (-ω.s) * (2 * |η| * Real.exp ω.ℓ + M) +
    Real.exp (-ω.s) * Real.exp (-ω.s) ≤ 1 / 4) {E : ℂ} (hE : ‖E‖ ≤ M) :
    Real.exp (-ω.s) * ‖wC ω η E‖ + Real.exp (-ω.s) * Real.exp (-ω.s) ≤ 1 / 4 := by
  have h := norm_wC_le ω η E
  have : Real.exp (-ω.s) * ‖wC ω η E‖ ≤ Real.exp (-ω.s) * (2 * |η| * Real.exp ω.ℓ + M) :=
    mul_le_mul_of_nonneg_left (h.trans (by linarith)) (Real.exp_pos _).le
  linarith

/-- The data family: `w(E)` on `‖E‖ ≤ M`, frozen at `w(0)` outside. -/
def Dfam (hM0 : 0 ≤ M) (hM : Real.exp (-ω.s) * (2 * |η| * Real.exp ω.ℓ + M) +
    Real.exp (-ω.s) * Real.exp (-ω.s) ≤ 1 / 4) (E : ℂ) : ScaledPrep.HData ω :=
  if h : ‖E‖ ≤ M then
    mkData (wC ω η E) (by rw [toS_wC]; exact (wsymC_hop η E).1)
      (by rw [toS_wC]; exact (wsymC_hop η E).2) (small_of_lt hM h)
  else
    mkData (wC ω η 0) (by rw [toS_wC]; exact (wsymC_hop η 0).1)
      (by rw [toS_wC]; exact (wsymC_hop η 0).2) (small_of_lt hM (by simpa using hM0))

variable (hM0 : 0 ≤ M) (hM : Real.exp (-ω.s) * (2 * |η| * Real.exp ω.ℓ + M) +
    Real.exp (-ω.s) * Real.exp (-ω.s) ≤ 1 / 4)

lemma Dfam_a0 (E : ℂ) : (Dfam hM0 hM E).a0 = 1 := by unfold Dfam; split <;> rfl
lemma Dfam_c0 (E : ℂ) : (Dfam hM0 hM E).c0 = 1 / 4 := by unfold Dfam; split <;> rfl

lemma Dfam_w {E : ℂ} (hE : ‖E‖ ≤ M) : (Dfam hM0 hM E).w = wC ω η E := by
  unfold Dfam; rw [dif_pos hE]; rfl

lemma Dfam_J0 {E : ℂ} (hE : ‖E‖ ≤ M) :
    ω.toS (Dfam hM0 hM E).J0 = u1 + um1 + wsymC η E := by
  rw [ScaledPrep.HData.toS_J0, Dfam_w hM0 hM hE, toS_wC, Dfam_a0]
  simp

lemma Dfam_diff : DifferentiableOn ℂ (fun E => (Dfam hM0 hM E).w) (ball 0 M) := by
  refine ((wC_diff ω η).differentiableOn).congr fun E hE => ?_
  rw [Dfam_w hM0 hM (le_of_lt (by simpa using hE))]

lemma Dfam_κ (E : ℂ) : (Dfam hM0 hM E).κ = (1 - 1 / 4) / 24 * Real.exp (-ω.s) := by
  simp only [ScaledPrep.HData.κ, ScaledPrep.HData.μ, ScaledPrep.HData.lam, Dfam_a0, Dfam_c0,
    div_one]

lemma Dfam_w_sa {t : ℝ} (ht : |t| ≤ M) : ω.star (Dfam hM0 hM t).w = (Dfam hM0 hM t).w := by
  rw [Dfam_w hM0 hM (by simpa using ht)]
  apply ω.toS_injective
  rw [Weights.toS_star, toS_wC]
  have e : wsymC η (t : ℂ) = wsym η t := by unfold wsymC wsym; rfl
  rw [e]
  exact (sstar_eq_iff _).2 (wsym_sa η t)

/-! ### The holomorphic AMO preparation -/

/-- **The AMO first preparation is holomorphic in the energy.** -/
theorem amo_holo_prep {R : Symbol} (hR : WSum ω.s ω.ℓ R)
    (hσ : Real.exp (-ω.s) * wnorm ω.s ω.ℓ R ≤ ScaledPrep.sig0 (1 / 4)) :
    ∃ K L g : ℂ → WA, DifferentiableOn ℂ K (ball 0 M) ∧ DifferentiableOn ℂ L (ball 0 M) ∧
      DifferentiableOn ℂ g (ball 0 M) ∧ ∀ E ∈ ball (0 : ℂ) M,
        ‖K E‖ ≤ 16 / 9 * (Real.exp (-ω.s) * wnorm ω.s ω.ℓ R) ∧
        ‖g E‖ ≤ 16 / 9 * (Real.exp (-ω.s) * wnorm ω.s ω.ℓ R) ∧
        HopGE (ω.toS (K E)) 1 ∧ HopLE (ω.toS (L E)) (-1) ∧
        HopLE (ω.toS ((Dfam hM0 hM E).jOf (g E))) 1 ∧
        HopGE (ω.toS ((Dfam hM0 hM E).jOf (g E))) (-1) ∧
        ω.mul α (ω.mul α (ω.one' + L E) ((Dfam hM0 hM E).J0 + (Dfam hM0 hM E).jOf (g E)))
          (ω.one' + K E) = (Dfam hM0 hM E).J0 + ω.ofS R hR ∧
        (SymbolSelfAdjoint R → E.im = 0 →
          L E = ω.star (K E) ∧
            ω.star ((Dfam hM0 hM E).jOf (g E)) = (Dfam hM0 hM E).jOf (g E)) := by
  set D := Dfam hM0 hM
  set RW := ω.ofS R hR
  have hlam0 : (D 0).lam = Real.exp (-ω.s) := by
    simp only [ScaledPrep.HData.lam, D, Dfam_a0, div_one]
  have hkc0 : (D 0).kc = 7 / 16 := by
    simp only [ScaledPrep.HData.kc, D, Dfam_c0]; norm_num
  have hnR : ‖RW‖ = wnorm ω.s ω.ℓ R := Weights.norm_ofS _ _ _
  have hsm : (D 0).lam * ‖RW‖ ≤ ScaledPrep.sig0 (1 / 4) := by rw [hlam0, hnR]; exact hσ
  obtain ⟨z, hzd, hz⟩ := ScaledPrep.holo_preparation (α := α) D (Dfam_a0 hM0 hM)
    (Dfam_c0 hM0 hM) isOpen_ball (Dfam_diff hM0 hM) RW 0 hsm
  have hρ : (D 0).lam * ‖RW‖ / (1 - (D 0).kc) = 16 / 9 * (Real.exp (-ω.s) * wnorm ω.s ω.ℓ R) := by
    rw [hlam0, hkc0, hnR]; ring
  refine ⟨fun E => (z E).1, fun E => (z E).2.1, fun E => (z E).2.2, hzd.fst, hzd.snd.fst,
    hzd.snd.snd, fun E hE => ?_⟩
  obtain ⟨hzb, -, p1, p2, p3, p4, p5, p6⟩ := hz E hE
  rw [hρ] at hzb
  refine ⟨(norm_fst_le _).trans hzb, ((norm_snd_le _).trans (norm_snd_le _)).trans hzb,
    p1, p2, p3, p4, p5, fun hRsa him => ?_⟩
  have hEt : E = (E.re : ℂ) := by apply Complex.ext <;> simp [him]
  have hwsa : ω.star (D E).w = (D E).w := by
    rw [hEt]
    have hEM : |E.re| ≤ M := by
      have : ‖E‖ < M := by simpa using hE
      calc |E.re| ≤ ‖E‖ := Complex.abs_re_le_norm E
        _ ≤ M := this.le
    exact Dfam_w_sa hM0 hM hEM
  have hRsa' : ω.star RW = RW := by
    apply ω.toS_injective
    rw [Weights.toS_star, Weights.toS_ofS]
    exact (sstar_eq_iff _).2 hRsa
  exact p6 hwsa hRsa'

/-! ### Coefficient functions and `C²_E` bounds -/

/-- The coefficient functional `f ↦ a_r(f; z)` on `𝒲_{s,ℓ}`, `|Im z| ≤ ℓ/2π`. -/
def coefCLM (r : ℤ) {z : ℂ} (hz : |z.im| ≤ ω.ℓ / (2 * Real.pi)) : WA →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun f => coefFn α (ω.toS f) r z
      map_add' := fun f g => by
        rw [ω.toS_add]; exact coefFn_add ω.hs (ω.toS_wsum f) (ω.toS_wsum g) α r hz
      map_smul' := fun c f => by
        rw [ω.toS_smul, RingHom.id_apply, smul_eq_mul]
        unfold coefFn fser
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [← tsum_mul_left]
        congr 1; funext q; ring }
    1 fun f => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]
      refine (norm_coefFn_le ω.hs (ω.toS_wsum f) α r hz).trans
        ((fiber_le_wnorm ω.hs (ω.toS_wsum f) r).trans ?_)
      rw [ω.wnorm_toS]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (Real.exp_le_one_iff.2 (by nlinarith [ω.hs, abs_nonneg ((r : ℝ))]))

include hM0 hM in
/-- **`C²_E` bounds for the AMO first preparation.**  Every coefficient function of the Jacobi
correction `j(E)` and of `K(E)` has real energy derivatives
`|∂_E^n a_r(t; z)| ≤ n! ρ^{-n} B` with `B = κ^{-1} (16/9) e^{-s} ‖R‖` (for `j`), resp.
`B = (16/9) e^{-s} ‖R‖` (for `K`), at every real `t` with `closedBall t ρ ⊆ {|E| < M}`. -/
theorem amo_coef_deriv_bound {R : Symbol} (hR : WSum ω.s ω.ℓ R)
    (hσ : Real.exp (-ω.s) * wnorm ω.s ω.ℓ R ≤ ScaledPrep.sig0 (1 / 4)) :
    ∃ K g : ℂ → WA, ∀ (r : ℤ) {z : ℂ} (hz : |z.im| ≤ ω.ℓ / (2 * Real.pi)) {ρ : ℝ} (hρ : 0 < ρ)
      {t : ℝ} (ht : closedBall (t : ℂ) ρ ⊆ ball 0 M) (n : ℕ),
      ‖iteratedDeriv n (Energy.realRes fun E => coefFn α (ω.toS (K E)) r z) t‖ ≤
          n.factorial * (16 / 9 * (Real.exp (-ω.s) * wnorm ω.s ω.ℓ R)) / ρ ^ n ∧
      ‖iteratedDeriv n (Energy.realRes fun E =>
          coefFn α (ω.toS (((((1 - 1 / 4) / 24 * Real.exp (-ω.s))⁻¹ : ℝ) : ℂ) • g E)) r z) t‖ ≤
          n.factorial * (((1 - 1 / 4) / 24 * Real.exp (-ω.s))⁻¹ *
            (16 / 9 * (Real.exp (-ω.s) * wnorm ω.s ω.ℓ R))) / ρ ^ n := by
  obtain ⟨K, L, g, hK, -, hg, hall⟩ := amo_holo_prep α hM0 hM hR hσ
  refine ⟨K, g, fun r z hz ρ hρ t ht n => ⟨?_, ?_⟩⟩
  · have hd : DifferentiableOn ℂ (fun E => coefCLM α r hz (K E)) (ball 0 M) :=
      (coefCLM α r hz).differentiable.comp_differentiableOn hK
    exact Energy.real_deriv_bound isOpen_ball hd
      (fun E hE => ((coefCLM α r hz).le_of_opNorm_le
        (LinearMap.mkContinuous_norm_le _ zero_le_one _) (K E)).trans
          (by rw [one_mul]; exact (hall E hE).1)) hρ ht n
  · set c : ℝ := ((1 - 1 / 4) / 24 * Real.exp (-ω.s))⁻¹
    have hc : 0 ≤ c := by positivity
    have hd : DifferentiableOn ℂ (fun E => coefCLM α r hz ((c : ℂ) • g E)) (ball 0 M) :=
      (coefCLM α r hz).differentiable.comp_differentiableOn
        (fun E hE => (hg E hE).const_smul (c : ℂ))
    exact Energy.real_deriv_bound isOpen_ball hd
      (fun E hE => ((coefCLM α r hz).le_of_opNorm_le
        (LinearMap.mkContinuous_norm_le _ zero_le_one _) _).trans (by
          rw [one_mul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
          exact mul_le_mul_of_nonneg_left (hall E hE).2.1 hc)) hρ ht n

end AMOHolo

end AMO
