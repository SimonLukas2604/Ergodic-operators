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

* `prepOf`: the `JacobiPrep` built from any small solution `(K, j)` of Lemma 2.1;
* `amo_jacobiPrep_C2`: at every real energy `|t| < M`, `H - t` has an exact Jacobi
  preparation `P_t` with `a_t = 1 + a_1^{(j)}(t)`, `b_t = b_t^{AMO} + a_0^{(j)}(t)`, where the
  error coefficients come from one holomorphic family `j(E)` and satisfy the `C²_E` bounds.

This removes the holomorphy hypothesis on the first-preparation coefficients from the `C²_E`
results.  Everything here is proved.
-/
import AnalyticPerturbationsAMO.ScaledPrepHolo
import AnalyticPerturbationsAMO.FirstPreparation
import AnalyticPerturbationsAMO.EnergyDerivatives
import AnalyticPerturbationsAMO.TailSymbol

noncomputable section

open scoped ComplexConjugate InnerProductSpace
open Metric Complex L2

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

/-! ### From a small solution of Lemma 2.1 to a `JacobiPrep` -/

/-- The Jacobi preparation built from **any** small solution `(K, j)` of the self-adjoint
Lemma 2.1 system (the construction of `exists_jacobiPrep`, with `(K, j)` as input). -/
def prepOf (ω : Weights) (hs : 0 < ω.s) (hℓ : 0 < ω.ℓ) (α η E : ℝ) {R : Symbol}
    (hR : WSum ω.s ω.ℓ R)
    (hc : Real.exp (-ω.s) * (2 * |η| * Real.exp ω.ℓ + |E|) +
      Real.exp (-ω.s) * Real.exp (-ω.s) ≤ 1 / 4)
    (K j : WA) (hjle : HopLE (ω.toS j) 1) (hjge : HopGE (ω.toS j) (-1))
    (hjsa : ω.star j = j)
    (hid : ω.mul α (ω.mul α (ω.star (ω.one' + K)) ((prepData ω η E hc).J0 + j)) (ω.one' + K) =
      (prepData ω η E hc).J0 + ω.ofS R hR)
    (hKj : ‖K‖ + Real.exp (-ω.s) * ‖j‖ ≤ 1 / 4) : JacobiPrep α (H α η R) E := by
  set D := prepData ω η E hc
  set RW := ω.ofS R hR
  have hRW : ω.toS RW = R := Weights.toS_ofS _ _ _
  have hK1 : ‖K‖ < 1 := by
    have : 0 ≤ Real.exp (-ω.s) * ‖j‖ := by positivity
    linarith
  -- the prepared Jacobi symbol
  set S2 := ω.toS (D.J0 + j)
  have hS2eq : S2 = u1 + um1 + wsym η E + ω.toS j := by
    simp only [S2, Weights.toS_add, ScaledPrep.Data.toS_J0, D, prepData, Weights.toS_ofS,
      Complex.ofReal_one, one_smul]
  have hS2w : WSum ω.s ω.ℓ S2 := ω.toS_wsum _
  have hS2sa : SymbolSelfAdjoint S2 := by
    apply (sstar_eq_iff _).1
    rw [← Weights.toS_star, ω.star_add, D.star_J0, hjsa]
  have hS2ge : HopGE S2 (-1) := by
    rw [hS2eq]
    exact (((HopGE_u1.mono (by norm_num)).add HopGE_um1).add
      ((wsym_hop η E).1.mono (by norm_num))).add hjge
  have hS2le : HopLE S2 1 := by
    rw [hS2eq]
    exact ((HopLE_u1.add (HopLE_um1.mono (by norm_num))).add
      ((wsym_hop η E).2.mono (by norm_num))).add hjle
  set w := ω.ℓ / (2 * Real.pi)
  set a := coefFn α S2 1
  set b := coefFn α S2 0
  -- `a = 1 + a_j` is close to `1`
  have hclose : ∀ z ∈ strip w, ‖a z - 1‖ ≤ 1 / 4 := by
    intro z hz
    have hz' : |z.im| ≤ ω.ℓ / (2 * Real.pi) := le_of_lt hz
    have hu1 : WSum ω.s ω.ℓ u1 := ScaledPrep.u1_wsum
    have hum1 : WSum ω.s ω.ℓ um1 := ScaledPrep.um1_wsum
    have hws := wsym_wsum ω.s ω.ℓ η E
    have hj := ω.toS_wsum j
    have hsum : a z = coefFn α u1 1 z + coefFn α um1 1 z + coefFn α (wsym η E) 1 z +
        coefFn α (ω.toS j) 1 z := by
      simp only [a]
      rw [hS2eq, coefFn_add hs.le (((hu1.add' hum1)).add' hws) hj α 1 hz',
        coefFn_add hs.le (hu1.add' hum1) hws α 1 hz', coefFn_add hs.le hu1 hum1 α 1 hz']
    have e1 : coefFn α u1 1 z = 1 := coefFn_single α 1 1 z
    have e2 : coefFn α um1 1 z = 0 :=
      coefFn_of_zero_fiber (fun q => by simp [um1, Pi.single_apply]) z
    have e3 : coefFn α (wsym η E) 1 z = 0 :=
      coefFn_of_zero_fiber (fun q => (wsym_hop η E).2 (1, q) (by norm_num)) z
    rw [hsum, e1, e2, e3, add_zero, add_zero, add_sub_cancel_left]
    calc ‖coefFn α (ω.toS j) 1 z‖ ≤ ∑' q : ℤ, ‖ω.toS j (1, q)‖ * Real.exp (ω.ℓ * |(q : ℝ)|) :=
          norm_coefFn_le hs.le hj α 1 hz'
      _ ≤ Real.exp (-(ω.s * |((1 : ℤ) : ℝ)|)) * wnorm ω.s ω.ℓ (ω.toS j) :=
          fiber_le_wnorm hs.le hj 1
      _ = Real.exp (-ω.s) * ‖j‖ := by rw [ω.wnorm_toS]; simp
      _ ≤ 1 / 4 := by have := norm_nonneg K; linarith
  -- the change of unknown `Q_x = (I + K)_x`
  have hQ := fun x => ScaledPrep.Q_exp_local (ω := ω) α K hK1 x
  let Q : ℝ → (Op ℤ)ˣ := fun x =>
    ⟨op α (ω.toS (ω.one' + K)) x, Classical.choose (hQ x), (Classical.choose_spec (hQ x)).1,
      (Classical.choose_spec (hQ x)).2.1⟩
  have hwpos : 0 < w := by positivity
  -- the factorization
  have hfac : ∀ x : ℝ, H α η R x - algebraMap ℂ (Op ℤ) E =
      star (Q x : Op ℤ) * jacobi α a b x * Q x := by
    intro x
    have hF := ScaledPrep.operator_factorization (α := α) D RW K j hid x
    have hlhs : op α (ω.toS (D.J0 + RW)) x = H α η R x - algebraMap ℂ (Op ℤ) E := by
      have e : ω.toS (D.J0 + RW) = (amo η + R) - Pi.single ((0 : ℤ), (0 : ℤ)) (E : ℂ) := by
        simp only [Weights.toS_add, ScaledPrep.Data.toS_J0, D, prepData, Weights.toS_ofS,
          Complex.ofReal_one, one_smul, hRW]
        rw [show u1 + um1 + wsym η E + R = (u1 + um1 + wsym η E) + R from rfl, amo_eq_wsym]
        abel
      rw [e, op_sub_symbol α ((amo_summable _).add (hR.symbolSummable hs.le hℓ.le)) (symbolSummable_single _ _),
        op_single, W_zero, Algebra.algebraMap_eq_smul_one]
      rfl
    rw [← hlhs, hF, op_eq_jacobi hs.le hℓ.le hS2w hS2sa hS2ge hS2le x]
  have hap : AnalyticOnNhd ℂ a (strip w) := coefFn_analytic hs.le hS2w α 1
  have hbp : AnalyticOnNhd ℂ b (strip w) := coefFn_analytic hs.le hS2w α 0
  have hreal : ∀ t : ℝ, (t : ℂ) ∈ strip w := fun t => by simp [strip, hwpos]
  have hexp : ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ (x : ℝ) (m n : ℤ),
      ‖⟪delta m, (Q x : Op ℤ) (delta n)⟫_ℂ‖ ≤ C * Real.exp (-κ * |((n - m : ℤ) : ℝ)|) ∧
      ‖⟪delta m, ((Q x)⁻¹ : (Op ℤ)ˣ).1 (delta n)⟫_ℂ‖ ≤ C * Real.exp (-κ * |((n - m : ℤ) : ℝ)|) := by
    refine ⟨max ((1 - ‖K‖)⁻¹) ‖ω.one' + K‖ + 1, ω.s, by positivity, hs, fun x m n => ⟨?_, ?_⟩⟩
    · have h := (Classical.choose_spec (hQ x)).2.2.2 m n
      have habs : |((m - n : ℤ) : ℝ)| = |((n - m : ℤ) : ℝ)| := by
        push_cast; exact abs_sub_comm _ _
      rw [habs] at h
      refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
      linarith [le_max_right ((1 - ‖K‖)⁻¹) ‖ω.one' + K‖]
    · have h := (Classical.choose_spec (hQ x)).2.2.1 m n
      have habs : |((m - n : ℤ) : ℝ)| = |((n - m : ℤ) : ℝ)| := by
        push_cast; exact abs_sub_comm _ _
      rw [habs] at h
      refine h.trans (mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le)
      linarith [le_max_left ((1 - ‖K‖)⁻¹) ‖ω.one' + K‖]
  have hane : ∀ t : ℝ, a t ≠ 0 := fun t h => by
    have := hclose t (hreal t)
    rw [h, zero_sub, norm_neg, norm_one] at this
    norm_num at this
  exact {
    Q := Q
    a := a
    b := b
    c := sqrtFn a
    w := w
    w_pos := hwpos
    a_analytic := hap
    b_analytic := hbp
    c_analytic := sqrtFn_analytic hap hclose
    a_periodic := coefFn_add_one α S2 1
    b_periodic := coefFn_add_one α S2 0
    c_periodic := sqrtFn_periodic (coefFn_add_one α S2 1)
    b_real := coefFn_zero_real hS2sa
    a_ne := hane
    c_sq := fun z _ => sqrtFn_sq z
    c_eq_norm := sqrtFn_ofReal
    c_ne := fun z hz => sqrtFn_ne hclose hz
    factor := hfac
    exp_local := hexp }

lemma prepOf_a (ω : Weights) (hs : 0 < ω.s) (hℓ : 0 < ω.ℓ) (α η E : ℝ) {R : Symbol}
    (hR : WSum ω.s ω.ℓ R) (hc) (K j : WA) (hjle hjge hjsa hid hKj) :
    (prepOf ω hs hℓ α η E hR hc K j hjle hjge hjsa hid hKj).a =
      coefFn α (ω.toS ((prepData ω η E hc).J0 + j)) 1 := rfl

lemma prepOf_b (ω : Weights) (hs : 0 < ω.s) (hℓ : 0 < ω.ℓ) (α η E : ℝ) {R : Symbol}
    (hR : WSum ω.s ω.ℓ R) (hc) (K j : WA) (hjle hjge hjsa hid hKj) :
    (prepOf ω hs hℓ α η E hR hc K j hjle hjge hjsa hid hKj).b =
      coefFn α (ω.toS ((prepData ω η E hc).J0 + j)) 0 := rfl


/-! ### The AMO Jacobi preparations with `C²_E` coefficients -/

lemma Cst_quarter_eq : ScaledPrep.Cst (1 / 4) = 33 * (16 / 9) := by
  unfold ScaledPrep.Cst; norm_num

/-- **`d-eq:firstprep` + `d-eq:C1`.**  For `R` self-adjoint with `e^{-s}‖R‖ ≤ σ₁`, there is a
holomorphic family `j(E)` (the Jacobi correction) such that at **every** real energy `|t| < M`
the operator `H - t` has an exact Jacobi preparation `P_t` with coefficients
  `a_t(z) = 1 + a_1^{(j)}(t; z)`,   `b_t(z) = b^{AMO}_t(z) + a_0^{(j)}(t; z)`
(`b^{AMO}_t` the coefficient of `η(V + V^{-1}) - t`), and the error coefficients satisfy
`|∂_E^n a_r^{(j)}(t; z)| ≤ n! ρ^{-n} κ^{-1} (16/9) e^{-s} ‖R‖` whenever
`closedBall t ρ ⊆ {|E| < M}`. -/
theorem amo_jacobiPrep_C2 (ω : Weights) (hs : 0 < ω.s) (hℓ : 0 < ω.ℓ) (α η : ℝ) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : Real.exp (-ω.s) * (2 * |η| * Real.exp ω.ℓ + M) +
      Real.exp (-ω.s) * Real.exp (-ω.s) ≤ 1 / 4) {R : Symbol} (hR : WSum ω.s ω.ℓ R)
    (hRsa : SymbolSelfAdjoint R) (hσ : Real.exp (-ω.s) * wnorm ω.s ω.ℓ R ≤ sig1) :
    ∃ jf : ℂ → WA,
      (∀ (r : ℤ) {z : ℂ} (_ : |z.im| ≤ ω.ℓ / (2 * Real.pi)) {ρ : ℝ} (_ : 0 < ρ) {t : ℝ}
        (_ : closedBall (t : ℂ) ρ ⊆ ball 0 M) (n : ℕ),
        ‖iteratedDeriv n (Energy.realRes fun E => coefFn α (ω.toS (jf E)) r z) t‖ ≤
          n.factorial * (((1 - 1 / 4) / 24 * Real.exp (-ω.s))⁻¹ *
            (16 / 9 * (Real.exp (-ω.s) * wnorm ω.s ω.ℓ R))) / ρ ^ n) ∧
      ∀ t : ℝ, |t| < M → ∃ P : JacobiPrep α (H α η R) t, ∀ z : ℂ,
        |z.im| ≤ ω.ℓ / (2 * Real.pi) →
          P.a z = 1 + coefFn α (ω.toS (jf t)) 1 z ∧
          P.b z = coefFn α (wsym η t) 0 z + coefFn α (ω.toS (jf t)) 0 z := by
  have hσ0 : Real.exp (-ω.s) * wnorm ω.s ω.ℓ R ≤ ScaledPrep.sig0 (1 / 4) :=
    hσ.trans (min_le_left _ _)
  obtain ⟨K, L, g, hK, -, hg, hall⟩ := AMOHolo.amo_holo_prep α hM0 hM hR hσ0
  set c : ℝ := ((1 - 1 / 4) / 24 * Real.exp (-ω.s))⁻¹ with hcdef
  have hc : 0 ≤ c := by positivity
  set σ := Real.exp (-ω.s) * wnorm ω.s ω.ℓ R
  have hjf : ∀ E, (AMOHolo.Dfam hM0 hM E).jOf (g E) = (c : ℂ) • g E := fun E => by
    unfold ScaledPrep.HData.jOf; rw [AMOHolo.Dfam_κ]
  refine ⟨fun E => (c : ℂ) • g E, fun r z hz ρ hρ t ht n => ?_, fun t ht => ?_⟩
  · have hd : DifferentiableOn ℂ (fun E => AMOHolo.coefCLM α r hz ((c : ℂ) • g E)) (ball 0 M) :=
      (AMOHolo.coefCLM α r hz).differentiable.comp_differentiableOn
        (fun E hE => (hg E hE).const_smul (c : ℂ))
    exact Energy.real_deriv_bound isOpen_ball hd
      (fun E hE => ((AMOHolo.coefCLM α r hz).le_of_opNorm_le
        (LinearMap.mkContinuous_norm_le _ zero_le_one _) _).trans (by
          rw [one_mul, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
          exact mul_le_mul_of_nonneg_left (hall E hE).2.1 hc)) hρ ht n
  -- the preparation at the real energy `t`
  have htM : ‖(t : ℂ)‖ ≤ M := by simpa using ht.le
  have hmem : (t : ℂ) ∈ ball (0 : ℂ) M := by simpa using ht
  have hct : Real.exp (-ω.s) * (2 * |η| * Real.exp ω.ℓ + |t|) +
      Real.exp (-ω.s) * Real.exp (-ω.s) ≤ 1 / 4 := by
    have : Real.exp (-ω.s) * (2 * |η| * Real.exp ω.ℓ + |t|) ≤
        Real.exp (-ω.s) * (2 * |η| * Real.exp ω.ℓ + M) :=
      mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
    linarith
  obtain ⟨hKb, hgb, -, -, hjle, hjge, hfac, hreal⟩ := hall t hmem
  obtain ⟨hLK, hjsa⟩ := hreal hRsa (by simp)
  rw [hjf] at hjle hjge hjsa hfac
  have hJ0 : (AMOHolo.Dfam hM0 hM (t : ℂ)).J0 = (prepData ω η t hct).J0 := by
    apply ω.toS_injective
    rw [AMOHolo.Dfam_J0 hM0 hM htM]
    simp only [ScaledPrep.Data.toS_J0, prepData, Weights.toS_ofS, Complex.ofReal_one, one_smul]
    rfl
  have hid : ω.mul α (ω.mul α (ω.star (ω.one' + K t)) ((prepData ω η t hct).J0 + (c : ℂ) • g t))
      (ω.one' + K t) = (prepData ω η t hct).J0 + ω.ofS R hR := by
    rw [← hJ0, ← hfac, hLK, ω.star_add, ω.star_one']
  have hKj : ‖K t‖ + Real.exp (-ω.s) * ‖(c : ℂ) • g t‖ ≤ 1 / 4 := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
    have hec : Real.exp (-ω.s) * c = 32 := by
      rw [hcdef]; field_simp; norm_num
    have h1 : Real.exp (-ω.s) * (c * ‖g t‖) ≤ 32 * (16 / 9 * σ) := by
      rw [← mul_assoc, hec]; exact mul_le_mul_of_nonneg_left hgb (by norm_num)
    have h2 : σ ≤ 1 / (4 * ScaledPrep.Cst (1 / 4)) := hσ.trans (min_le_right _ _)
    rw [Cst_quarter_eq] at h2
    have h3 : 33 * (16 / 9 * σ) ≤ 1 / 4 := by
      rw [le_div_iff₀ (by norm_num)] at h2
      nlinarith
    linarith
  refine ⟨prepOf ω hs hℓ α η t hR hct (K t) ((c : ℂ) • g t) hjle hjge hjsa hid hKj,
    fun z hz => ?_⟩
  rw [prepOf_a, prepOf_b]
  have hS : ω.toS ((prepData ω η t hct).J0 + (c : ℂ) • g t) =
      u1 + um1 + wsym η t + ω.toS ((c : ℂ) • g t) := by
    simp only [ω.toS_add, ScaledPrep.Data.toS_J0, prepData, Weights.toS_ofS, Complex.ofReal_one,
      one_smul]
  have hu1 : WSum ω.s ω.ℓ u1 := ScaledPrep.u1_wsum
  have hum1 : WSum ω.s ω.ℓ um1 := ScaledPrep.um1_wsum
  have hws := wsym_wsum ω.s ω.ℓ η t
  have hj := ω.toS_wsum ((c : ℂ) • g t)
  have hsum : ∀ r : ℤ, coefFn α (u1 + um1 + wsym η t + ω.toS ((c : ℂ) • g t)) r z =
      coefFn α u1 r z + coefFn α um1 r z + coefFn α (wsym η t) r z +
        coefFn α (ω.toS ((c : ℂ) • g t)) r z := fun r => by
    rw [coefFn_add hs.le ((hu1.add' hum1).add' hws) hj α r hz,
      coefFn_add hs.le (hu1.add' hum1) hws α r hz, coefFn_add hs.le hu1 hum1 α r hz]
  rw [hS, hsum, hsum]
  have e1 : coefFn α u1 1 z = 1 := coefFn_single α 1 1 z
  have e2 : coefFn α um1 1 z = 0 :=
    coefFn_of_zero_fiber (fun q => by simp [um1, Pi.single_apply]) z
  have e3 : coefFn α (wsym η t) 1 z = 0 :=
    coefFn_of_zero_fiber (fun q => (wsym_hop η t).2 (1, q) (by norm_num)) z
  have e4 : coefFn α u1 0 z = 0 :=
    coefFn_of_zero_fiber (fun q => by simp [u1, Pi.single_apply]) z
  have e5 : coefFn α um1 0 z = 0 :=
    coefFn_of_zero_fiber (fun q => by simp [um1, Pi.single_apply]) z
  rw [e1, e2, e3, e4, e5]
  constructor <;> ring

end AMO
