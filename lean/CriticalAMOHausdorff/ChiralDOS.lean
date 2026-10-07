/-
Copyright (c) 2026. Formalization of
  S. Becker, S. Jitomirskaya, I. Krasovsky, "Critical almost Mathieu operator: hidden
  singularity, gap continuity, and the Hausdorff dimension of the spectrum"
  (arXiv:1909.04429v2).

# Lemma 4.1 `dn`: `N_{2α} = Ñ_α`  (paper §4, tex lines ~695–737)

Let `ν` be a density of states measure of `θ ↦ H_{2α,θ}` and `ν'` one of
`θ ↦ H̃_{α,θ} = Ĥ_{α,1/4+α/2+θ}`, in the sense of `AMO.IsDOSMeasure`:
`∫ f dν = ∫_0^1 ⟨δ₀, f(H_θ) δ₀⟩ dθ` for bounded continuous `f`.  Then `ν = ν'` (`dn`).  In
particular the integrated densities of states agree (`dn_IDS`).

## Proof
This follows the paper (display (4.1)), with polynomial moments in place of general continuous
`η`.
1. `Δ₀(n,θ) = δ_{n0}` satisfies `QΔ₀ = Δ₀` (`Q_Delta0`), for the unitary `Q` of Theorem 3.1
   (`ChiralL2.chiralrepresentthm`).  Hence
   `⟨Δ₀, (T²+T⁻²+S+S⁻¹)^k Δ₀⟩ = ⟨Δ₀, M̃_α^k Δ₀⟩` (`moment_eq`).
2. Both operators act fibrewise.  On the vectors `toH v` built from families of finitely
   supported vectors with continuous entries, the inner products are `∫_0^1 ⟨δ₀, ·⟩ dθ`
   (`inner_Delta0_toH`, `D_iter`, `M_iter`).  On even sites, `T²+T⁻²+S+S⁻¹` is `H_{2α,θ}`
   (`dfam_even`).  So `∫_0^1 ⟨δ₀, H_{2α,θ}^k δ₀⟩ dθ = ∫_0^1 ⟨δ₀, H̃_{α,θ}^k δ₀⟩ dθ` for all `k`
   (`moment_amo_chiral`).
3. All spectra lie in `[-4,4]`.  Two DOS measures of uniformly bounded self-adjoint families with
   equal moments coincide (`dos_eq_of_moments`).  This uses Weierstrass approximation on
   `[-C,C]` and the fact that bounded continuous functions determine finite measures.

## Main results
* `Q_Delta0` — `QΔ₀ = Δ₀`;
* `moment_amo_chiral` — equality of all moments;
* `dos_eq_of_moments` — DOS measures are determined by their moments;
* `dn` — **Lemma 4.1**, and `dn_IDS`.

There are no `sorry`s and no additional hypotheses in this file.
-/
import CriticalAMOHausdorff.ChiralUnitaryL2
import CriticalAMOHausdorff.MeasureConvergence
import AnalyticPerturbationsAMO.DensityOfStates

noncomputable section

open Real Complex MeasureTheory Set
open scoped ComplexConjugate ENNReal InnerProductSpace BoundedContinuousFunction

namespace CAH

namespace ChiralL2

/-! ### Fibred vectors with continuous entries -/

lemma memLp_of_continuous {g : ℝ → ℂ} (hg : Continuous g) : MemLp g 2 μT := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hg.continuousOn
  refine MemLp.of_bound hg.aestronglyMeasurable C ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact hC x ⟨hx.1.le, hx.2⟩

/-- A continuous function as an element of `L²(𝕋)`. -/
def cL (g : ℝ → ℂ) (hg : Continuous g) : L2T := (memLp_of_continuous hg).toLp g

lemma cL_ae (g : ℝ → ℂ) (hg : Continuous g) : cL g hg =ᵐ[μT] g :=
  (memLp_of_continuous hg).coeFn_toLp

lemma cL_eq_zero (g : ℝ → ℂ) (hg : Continuous g) (h0 : ∀ θ, g θ = 0) : cL g hg = 0 := by
  apply Lp.ext
  filter_upwards [cL_ae g hg, (Lp.coeFn_zero ℂ 2 μT)] with x h1 h2
  rw [h1, h2, h0]; rfl

/-- A family `θ ↦ v(θ,·)` of uniformly finitely supported vectors with continuous entries. -/
def Fam (v : ℝ → ℤ → ℂ) : Prop :=
  (∃ N : ℕ, ∀ θ n, n ∉ box N → v θ n = 0) ∧ ∀ n, Continuous fun θ => v θ n

/-- The element `φ(n,θ) = v(θ,n)` of `L²(𝕋; ℓ²(ℤ))`. -/
def toH (v : ℝ → ℤ → ℂ) (hv : Fam v) : H :=
  ⟨fun n => cL (fun θ => v θ n) (hv.2 n), by
    show Memℓp _ 2
    rw [memℓp_two_iff]
    obtain ⟨N, hN⟩ := hv.1
    refine summable_of_ne_finset_zero (s := box N) (fun n hn => ?_)
    rw [cL_eq_zero _ _ (fun θ => hN θ n hn), norm_zero]
    norm_num⟩

lemma toH_apply (v : ℝ → ℤ → ℂ) (hv : Fam v) (n : ℤ) :
    toH v hv n = cL (fun θ => v θ n) (hv.2 n) := rfl

lemma toH_ae (v : ℝ → ℤ → ℂ) (hv : Fam v) (n : ℤ) : toH v hv n =ᵐ[μT] fun θ => v θ n :=
  cL_ae (fun θ => v θ n) (hv.2 n)

lemma toH_ext {φ : H} {v : ℝ → ℤ → ℂ} (hv : Fam v) (h : ∀ n, φ n =ᵐ[μT] fun θ => v θ n) :
    φ = toH v hv :=
  lp.ext (funext fun n => Lp.ext ((h n).trans (toH_ae v hv n).symm))

/-- `Δ₀(n,θ) = δ_{n0}`. -/
def Delta0 : H := lp.single 2 0 (eL 0)

lemma Delta0_apply (n : ℤ) : Delta0 n = if n = 0 then eL 0 else 0 := by
  by_cases hn : n = 0
  · subst hn; simp [Delta0, lp.single_apply]
  · simp [Delta0, lp.single_apply, hn]

lemma inner_Delta0_toH (v : ℝ → ℤ → ℂ) (hv : Fam v) :
    ⟪Delta0, toH v hv⟫_ℂ = ∫ θ, v θ 0 ∂μT := by
  rw [Delta0, lp.inner_single_left, toH_apply, inner_eL]
  apply integral_congr_ae
  filter_upwards [cL_ae (fun θ => v θ 0) (hv.2 0)] with x hx
  rw [hx]; simp [ex]

lemma fam_delta : Fam (fun _ n => if n = 0 then (1 : ℂ) else 0) :=
  ⟨⟨0, fun θ n hn => by
    rw [mem_box] at hn
    have : n ≠ 0 := by omega
    simp [this]⟩, fun _ => continuous_const⟩

lemma Delta0_eq_toH : Delta0 = toH _ fam_delta := by
  refine toH_ext fam_delta (fun n => ?_)
  rw [Delta0_apply]
  by_cases hn : n = 0
  · subst hn
    filter_upwards [eL_ae 0] with x hx
    simp only [↓reduceIte]; rw [hx]; simp [ex]
  · simp only [hn, ite_false]
    exact (Lp.coeFn_zero ℂ 2 μT)

/-! ### The fibre actions of `T² + T⁻² + S + S⁻¹` and `M̃_α` -/

variable (α : ℝ)

/-- The fibre action of `T² + T⁻² + S + S⁻¹`. -/
def dstep (v : ℝ → ℤ → ℂ) : ℝ → ℤ → ℂ := fun θ n =>
  v θ (n + 1 + 1) + v θ (n - 1 - 1) + ((2 * Real.cos (2 * π * (θ + n * α)) : ℝ) : ℂ) * v θ n

/-- The fibre action of `M̃_α`, i.e. `Ĥ_{α,1/4+α/2+θ}`. -/
def mstep (v : ℝ → ℤ → ℂ) : ℝ → ℤ → ℂ := fun θ n =>
  ((2 * Real.sin (2 * π * (1 / 4 + α / 2 + θ + (n - 1) * α)) : ℝ) : ℂ) * v θ (n - 1) +
    ((2 * Real.sin (2 * π * (1 / 4 + α / 2 + θ + n * α)) : ℝ) : ℂ) * v θ (n + 1)

lemma Fam.dstep {v : ℝ → ℤ → ℂ} (hv : Fam v) : Fam (dstep α v) := by
  obtain ⟨⟨N, hN⟩, hc⟩ := hv
  refine ⟨⟨N + 2, fun θ n hn => ?_⟩, fun n => ?_⟩
  · rw [mem_box] at hn
    push_cast at hn
    simp only [ChiralL2.dstep]
    rw [hN θ (n + 1 + 1) (by rw [mem_box]; omega), hN θ (n - 1 - 1) (by rw [mem_box]; omega),
      hN θ n (by rw [mem_box]; omega)]
    simp
  · have h1 := hc (n + 1 + 1)
    have h2 := hc (n - 1 - 1)
    have h3 := hc n
    simp only [ChiralL2.dstep]
    fun_prop

lemma Fam.mstep {v : ℝ → ℤ → ℂ} (hv : Fam v) : Fam (mstep α v) := by
  obtain ⟨⟨N, hN⟩, hc⟩ := hv
  refine ⟨⟨N + 1, fun θ n hn => ?_⟩, fun n => ?_⟩
  · rw [mem_box] at hn
    push_cast at hn
    simp only [ChiralL2.mstep]
    rw [hN θ (n - 1) (by rw [mem_box]; omega), hN θ (n + 1) (by rw [mem_box]; omega)]
    simp
  · have h1 := hc (n - 1)
    have h2 := hc (n + 1)
    simp only [ChiralL2.mstep]
    fun_prop

lemma D_toH {v : ℝ → ℤ → ℂ} (hv : Fam v) : Dfun α (toH v hv) = toH _ (hv.dstep α) := by
  refine toH_ext (hv.dstep α) (fun n => ?_)
  filter_upwards [Dfun_ae α (toH v hv) n, toH_ae v hv (n + 1 + 1), toH_ae v hv (n - 1 - 1),
    toH_ae v hv n] with θ h1 h2 h3 h4
  rw [h1, h2, h3, h4]; rfl

lemma M_toH {v : ℝ → ℤ → ℂ} (hv : Fam v) : Mfun α (toH v hv) = toH _ (hv.mstep α) := by
  refine toH_ext (hv.mstep α) (fun n => ?_)
  filter_upwards [Mfun_ae α (toH v hv) n, toH_ae v hv (n - 1), toH_ae v hv (n + 1)]
    with θ h1 h2 h3
  rw [h1, h2, h3]; rfl

/-- `θ ↦ D_θ^k δ₀`. -/
def dfam : ℕ → ℝ → ℤ → ℂ
  | 0 => fun _ n => if n = 0 then 1 else 0
  | k + 1 => dstep α (dfam k)

/-- `θ ↦ H̃_{α,θ}^k δ₀`. -/
def mfam : ℕ → ℝ → ℤ → ℂ
  | 0 => fun _ n => if n = 0 then 1 else 0
  | k + 1 => mstep α (mfam k)

lemma fam_dfam : ∀ k, Fam (dfam α k)
  | 0 => fam_delta
  | k + 1 => (fam_dfam k).dstep α

lemma fam_mfam : ∀ k, Fam (mfam α k)
  | 0 => fam_delta
  | k + 1 => (fam_mfam k).mstep α

lemma D_iter (k : ℕ) : (Dfun α)^[k] Delta0 = toH (dfam α k) (fam_dfam α k) := by
  induction k with
  | zero => exact Delta0_eq_toH
  | succ k ih => rw [Function.iterate_succ_apply', ih, D_toH]; rfl

lemma M_iter (k : ℕ) : (Mfun α)^[k] Delta0 = toH (mfam α k) (fam_mfam α k) := by
  induction k with
  | zero => exact Delta0_eq_toH
  | succ k ih => rw [Function.iterate_succ_apply', ih, M_toH]; rfl

/-! ### `QΔ₀ = Δ₀` -/

lemma Uop_Delta0 (x : ℝ) : Uop α x Delta0 = Delta0 := by
  refine lp.ext (funext fun n => ?_)
  rw [Uop_apply, Delta0_apply]
  by_cases hn : n = 0
  · subst hn
    rw [emul_congr (A' := 0) (B' := 0) (by simp) (by simp), emul_apply, emulF_zero]
  · simp only [hn, ite_false, map_zero]

lemma F_eL0 : F (eL 0) = lp.single 2 0 1 := by
  rw [F, LinearIsometryEquiv.trans_apply, eL, LinearIsometryEquiv.symm_apply_apply,
    ← coe_fourierBasis, HilbertBasis.repr_self]

/-- `WΔ₀`. -/
def c0 : Hc := lp.single 2 0 (lp.single 2 0 1)

lemma c0_apply (n m : ℤ) : c0 n m = if n = 0 ∧ m = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst hn
    by_cases hm : m = 0
    · subst hm; simp [c0, lp.single_apply]
    · simp [c0, lp.single_apply, hm]
  · simp [c0, lp.single_apply, hn]

lemma W_Delta0 : Wop Delta0 = c0 := by
  refine lp.ext (funext fun n => ?_)
  rw [Wop_apply, Delta0_apply]
  by_cases hn : n = 0
  · subst hn; simp only [↓reduceIte]; rw [F_eL0]; simp [c0, lp.single_apply]
  · simp only [hn, ↓reduceIte, map_zero]; simp [c0, lp.single_apply, hn]

lemma Pc_c0 : Pc α c0 = c0 := by
  refine lp.ext (funext fun n => lp.ext (funext fun m => ?_))
  rw [Pc_apply, c0_apply, c0_apply]
  by_cases hm : m = 0
  · subst hm
    by_cases hn : n = 0
    · subst hn; simp [ex]
    · simp [hn]
  · have : -m ≠ 0 := neg_ne_zero.2 hm
    simp [hm, this]

lemma R_Delta0 : Rop α Delta0 = Delta0 := by
  rw [Rop_apply, W_Delta0, Pc_c0, ← W_Delta0, LinearIsometryEquiv.symm_apply_apply]

/-- `QΔ₀ = Δ₀` (used in the proof of Lemma 4.1, tex l. ~705). -/
theorem Q_Delta0 : Qop α Delta0 = Delta0 := by
  rw [Qop_apply, Uop_Delta0, R_Delta0, Uop_Delta0]

lemma Q_D_iter (k : ℕ) (φ : H) : Qop α ((Dfun α)^[k] φ) = (Mfun α)^[k] (Qop α φ) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', Q_D, ih]

/-- `⟨Δ₀, (T²+T⁻²+S+S⁻¹)^k Δ₀⟩ = ⟨Δ₀, M̃_α^k Δ₀⟩`, written fibrewise. -/
theorem moment_eq (k : ℕ) : ∫ θ, dfam α k θ 0 ∂μT = ∫ θ, mfam α k θ 0 ∂μT := by
  calc ∫ θ, dfam α k θ 0 ∂μT = ⟪Delta0, toH (dfam α k) (fam_dfam α k)⟫_ℂ :=
        (inner_Delta0_toH _ _).symm
    _ = ⟪Delta0, (Dfun α)^[k] Delta0⟫_ℂ := by rw [D_iter]
    _ = ⟪Qop α Delta0, Qop α ((Dfun α)^[k] Delta0)⟫_ℂ :=
        (LinearIsometryEquiv.inner_map_map _ _ _).symm
    _ = ⟪Delta0, (Mfun α)^[k] Delta0⟫_ℂ := by rw [Q_D_iter, Q_Delta0]
    _ = ⟪Delta0, toH (mfam α k) (fam_mfam α k)⟫_ℂ := by rw [M_iter]
    _ = ∫ θ, mfam α k θ 0 ∂μT := inner_Delta0_toH _ _

/-! ### Identification with `H_{2α,θ}` and `H̃_{α,θ}` -/

lemma delta_apply (n : ℤ) : AMO.delta 0 n = if n = 0 then (1 : ℂ) else 0 := by
  by_cases hn : n = 0
  · subst hn; simp [AMO.delta, lp.single_apply]
  · simp [AMO.delta, lp.single_apply, hn]

/-- **Even sites carry `H_{2α,θ}`:** `D_θ^k δ₀ = P₁⁻¹ H_{2α,θ}^k δ₀`. -/
lemma dfam_even (k : ℕ) (θ : ℝ) : ∀ n : ℤ,
    dfam α k θ (2 * n) = ((amo (2 * α) θ ^ k) (AMO.delta 0)) n ∧ dfam α k θ (2 * n + 1) = 0 := by
  induction k with
  | zero =>
    intro n
    simp only [dfam, pow_zero, ContinuousLinearMap.one_apply, delta_apply]
    constructor
    · by_cases hn : n = 0
      · simp [hn]
      · have : 2 * n ≠ 0 := by omega
        simp [hn, this]
    · have : 2 * n + 1 ≠ 0 := by omega
      simp [this]
  | succ k ih =>
    intro n
    constructor
    · show dstep α (dfam α k) θ (2 * n) = _
      simp only [ChiralL2.dstep]
      rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring, show 2 * n - 1 - 1 = 2 * (n - 1) by ring,
        (ih (n + 1)).1, (ih (n - 1)).1, (ih n).1, pow_succ', ContinuousLinearMap.mul_apply, amo,
        jacobi_apply bddFun_two_cos (bddFun_const 1)]
      rw [show θ + ((2 * n : ℤ) : ℝ) * α = θ + (n : ℝ) * (2 * α) by push_cast; ring]
      push_cast
      ring
    · show dstep α (dfam α k) θ (2 * n + 1) = _
      simp only [ChiralL2.dstep]
      rw [show 2 * n + 1 + 1 + 1 = 2 * (n + 1) + 1 by ring,
        show 2 * n + 1 - 1 - 1 = 2 * (n - 1) + 1 by ring, (ih (n + 1)).2, (ih (n - 1)).2,
        (ih n).2]
      simp

/-- The chiral fibres: `mfam α k θ = H̃_{α,θ}^k δ₀` with `H̃_{α,θ} = Ĥ_{α,1/4+α/2+θ}`. -/
lemma mfam_eq (k : ℕ) (θ : ℝ) : ∀ n : ℤ,
    mfam α k θ n = ((chiral α (1 / 4 + α / 2 + θ) ^ k) (AMO.delta 0)) n := by
  induction k with
  | zero =>
    intro n
    simp only [mfam, pow_zero, ContinuousLinearMap.one_apply, delta_apply]
  | succ k ih =>
    intro n
    show mstep α (mfam α k) θ n = _
    simp only [ChiralL2.mstep]
    rw [ih (n - 1), ih (n + 1), pow_succ', ContinuousLinearMap.mul_apply, chiral,
      jacobi_apply (bddFun_const 0) (bddFun_two_sin _)]
    push_cast
    ring

lemma continuous_dfam (k : ℕ) (n : ℤ) : Continuous fun θ => dfam α k θ n := (fam_dfam α k).2 n

lemma continuous_mfam (k : ℕ) (n : ℤ) : Continuous fun θ => mfam α k θ n := (fam_mfam α k).2 n

/-- **Equality of moments:** `∫_0^1 ⟨δ₀, H_{2α,θ}^k δ₀⟩ dθ = ∫_0^1 ⟨δ₀, H̃_{α,θ}^k δ₀⟩ dθ`. -/
theorem moment_amo_chiral (k : ℕ) :
    ∫ θ in (0 : ℝ)..1, RCLike.re (((amo (2 * α) θ ^ k) (AMO.delta 0)) 0) =
      ∫ θ in (0 : ℝ)..1, RCLike.re (((chiral α (1 / 4 + α / 2 + θ) ^ k) (AMO.delta 0)) 0) := by
  have e1 : ∀ θ, ((amo (2 * α) θ ^ k) (AMO.delta 0)) 0 = dfam α k θ 0 := fun θ => by
    have := (dfam_even α k θ 0).1
    rw [mul_zero] at this
    exact this.symm
  have e2 : ∀ θ, ((chiral α (1 / 4 + α / 2 + θ) ^ k) (AMO.delta 0)) 0 = mfam α k θ 0 :=
    fun θ => (mfam_eq α k θ 0).symm
  simp_rw [e1, e2]
  have i1 : Integrable (fun θ => dfam α k θ 0) μT :=
    ((continuous_dfam α k 0).continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Ioc_subset_Icc_self
  have i2 : Integrable (fun θ => mfam α k θ 0) μT :=
    ((continuous_mfam α k 0).continuousOn.integrableOn_compact isCompact_Icc).mono_set
      Ioc_subset_Icc_self
  rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one,
    integral_re i1, integral_re i2, moment_eq]

end ChiralL2

/-! ### DOS measures are determined by their moments -/

section DOS

open AMO

/-- `t ↦ max (-C) (min C t)`. -/
def clampC (C t : ℝ) : ℝ := max (-C) (min C t)

lemma continuous_clampC (C : ℝ) : Continuous (clampC C) := by
  unfold clampC; fun_prop

lemma clampC_of_abs_le {C t : ℝ} (h : |t| ≤ C) : clampC C t = t := by
  rw [abs_le] at h
  unfold clampC
  rw [min_eq_right h.2, max_eq_right h.1]

lemma clampC_mem {C : ℝ} (hC : 0 ≤ C) (t : ℝ) : clampC C t ∈ Icc (-C) C := by
  unfold clampC
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

/-- `g ∘ clamp` as a bounded continuous function. -/
def bcClamp (C : ℝ) (hC : 0 ≤ C) (g : ℝ → ℝ) (hg : Continuous g) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => g (clampC C t))
    (hg.comp (continuous_clampC C))
    (Classical.choose ((isCompact_Icc (a := -C) (b := C)).exists_bound_of_continuousOn
      hg.continuousOn))
    (fun t => Classical.choose_spec ((isCompact_Icc (a := -C) (b := C)).exists_bound_of_continuousOn
      hg.continuousOn) _ (clampC_mem hC t))

lemma bcClamp_apply (C : ℝ) (hC : 0 ≤ C) (g : ℝ → ℝ) (hg : Continuous g) (t : ℝ) :
    bcClamp C hC g hg t = g (clampC C t) := rfl

variable {Hx Hx' : ℝ → AMO.Op ℤ} {ν ν' : Measure ℝ} {C : ℝ}

lemma cfc_congr_Icc {T : AMO.Op ℤ} (hT : IsSelfAdjoint T) (hTC : ‖T‖ ≤ C) {f g : ℝ → ℝ}
    (hfg : ∀ t, |t| ≤ C → f t = g t) :
    cfc (fun z : ℂ => ((f z.re : ℝ) : ℂ)) T = cfc (fun z : ℂ => ((g z.re : ℝ) : ℂ)) T := by
  have : IsStarNormal T := hT.isStarNormal
  apply cfc_congr
  intro z hz
  have h1 : ‖z‖ ≤ ‖T‖ := spectrum.norm_le_norm_of_mem hz
  have h2 : |z.re| ≤ C := (Complex.abs_re_le_norm z).trans (h1.trans hTC)
  simp only [hfg _ h2]

lemma cfc_pow_re {T : AMO.Op ℤ} (hT : IsSelfAdjoint T) (k : ℕ) :
    cfc (fun z : ℂ => (((z.re) ^ k : ℝ) : ℂ)) T = T ^ k := by
  have : IsStarNormal T := hT.isStarNormal
  rw [cfc_congr (g := fun z : ℂ => z ^ k)]
  · exact cfc_pow_id T k
  intro z hz
  have h := hT.mem_spectrum_eq_re hz
  simp only [Complex.ofReal_pow]
  rw [← h]

lemma inner_delta (u : L2 ℤ) : ⟪delta 0, u⟫_ℂ = u 0 := by
  rw [delta, lp.inner_single_left]; simp

lemma dos_clamp (hν : IsDOSMeasure Hx ν) (hsa : ∀ x, IsSelfAdjoint (Hx x))
    (hC : ∀ x, ‖Hx x‖ ≤ C) (hC0 : 0 ≤ C) (f : ℝ →ᵇ ℝ) :
    ∫ t, f t ∂ν = ∫ t, bcClamp C hC0 f f.continuous t ∂ν := by
  rw [hν.2 f, hν.2 (bcClamp C hC0 f f.continuous)]
  congr 1; funext x
  rw [cfc_congr_Icc (hsa x) (hC x) (f := fun t => f t)
    (g := fun t => bcClamp C hC0 f f.continuous t)
    (fun t ht => by rw [bcClamp_apply, clampC_of_abs_le ht])]

lemma dos_pow (hν : IsDOSMeasure Hx ν) (hsa : ∀ x, IsSelfAdjoint (Hx x))
    (hC : ∀ x, ‖Hx x‖ ≤ C) (hC0 : 0 ≤ C) (k : ℕ) :
    ∫ t, bcClamp C hC0 (fun t => t ^ k) (continuous_pow k) t ∂ν =
      ∫ x in (0 : ℝ)..1, RCLike.re (((Hx x) ^ k) (delta 0) 0) := by
  rw [hν.2]
  congr 1; funext x
  rw [cfc_congr_Icc (hsa x) (hC x)
    (f := fun t => bcClamp C hC0 (fun t => t ^ k) (continuous_pow k) t)
    (g := fun t => t ^ k) (fun t ht => by rw [bcClamp_apply, clampC_of_abs_le ht]),
    cfc_pow_re (hsa x), inner_delta]

lemma dos_poly (hν : IsDOSMeasure Hx ν) (hsa : ∀ x, IsSelfAdjoint (Hx x))
    (hC : ∀ x, ‖Hx x‖ ≤ C) (hC0 : 0 ≤ C) (p : Polynomial ℝ) :
    ∫ t, bcClamp C hC0 (fun t => p.eval t) p.continuous t ∂ν =
      ∑ i ∈ Finset.range (p.natDegree + 1),
        p.coeff i * ∫ x in (0 : ℝ)..1, RCLike.re (((Hx x) ^ i) (delta 0) 0) := by
  have := hν.1
  have e : ∀ t, bcClamp C hC0 (fun t => p.eval t) p.continuous t =
      ∑ i ∈ Finset.range (p.natDegree + 1),
        p.coeff i * bcClamp C hC0 (fun t => t ^ i) (continuous_pow i) t := fun t => by
    rw [bcClamp_apply, Polynomial.eval_eq_sum_range]
    rfl
  simp_rw [e]
  rw [integral_finsetSum _ (fun i _ =>
    ((bcClamp C hC0 (fun t => t ^ i) (continuous_pow i)).integrable ν).const_mul _)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_const_mul, dos_pow hν hsa hC hC0]

/-- **DOS measures with equal moments coincide.**  If `ν`, `ν'` are density of states measures
of uniformly bounded self-adjoint families `H_x`, `H'_x` with
`∫_0^1 ⟨δ₀, H_x^k δ₀⟩ dx = ∫_0^1 ⟨δ₀, H'^k_x δ₀⟩ dx` for all `k`, then `ν = ν'`. -/
theorem dos_eq_of_moments (hν : IsDOSMeasure Hx ν) (hν' : IsDOSMeasure Hx' ν')
    (hsa : ∀ x, IsSelfAdjoint (Hx x)) (hsa' : ∀ x, IsSelfAdjoint (Hx' x))
    (hC : ∀ x, ‖Hx x‖ ≤ C) (hC' : ∀ x, ‖Hx' x‖ ≤ C)
    (hmom : ∀ k : ℕ, ∫ x in (0 : ℝ)..1, RCLike.re (((Hx x) ^ k) (delta 0) 0) =
      ∫ x in (0 : ℝ)..1, RCLike.re (((Hx' x) ^ k) (delta 0) 0)) : ν = ν' := by
  have := hν.1
  have := hν'.1
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have hpoly : ∀ p : Polynomial ℝ,
      ∫ t, bcClamp C hC0 (fun t => p.eval t) p.continuous t ∂ν =
        ∫ t, bcClamp C hC0 (fun t => p.eval t) p.continuous t ∂ν' := by
    intro p
    rw [dos_poly hν hsa hC hC0, dos_poly hν' hsa' hC' hC0]
    simp_rw [hmom]
  -- approximation of a bounded continuous function by polynomials on `[-C, C]`
  have happrox : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (f : ℝ →ᵇ ℝ) (p : Polynomial ℝ)
      (ε : ℝ), (∀ x ∈ Icc (-C) C, |p.eval x - f x| < ε) →
      |∫ t, bcClamp C hC0 f f.continuous t ∂μ -
        ∫ t, bcClamp C hC0 (fun t => p.eval t) p.continuous t ∂μ| ≤ ε := by
    intro μ _ f p ε hp
    rw [← integral_sub ((bcClamp C hC0 f f.continuous).integrable μ)
      ((bcClamp C hC0 (fun t => p.eval t) p.continuous).integrable μ)]
    have h := norm_integral_le_of_norm_le_const (μ := μ) (C := ε)
      (f := fun t => bcClamp C hC0 f f.continuous t -
        bcClamp C hC0 (fun t => p.eval t) p.continuous t)
      (Filter.Eventually.of_forall fun t => by
        rw [bcClamp_apply, bcClamp_apply, Real.norm_eq_abs, abs_sub_comm]
        exact (hp _ (clampC_mem hC0 t)).le)
    simpa using h
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [dos_clamp hν hsa hC hC0 f, dos_clamp hν' hsa' hC' hC0 f]
  refine eq_of_forall_dist_le (fun ε hε => ?_)
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-C) C f f.continuous.continuousOn
    (ε / 2) (by positivity)
  have h1 := happrox ν f p (ε / 2) hp
  have h2 := happrox ν' f p (ε / 2) hp
  rw [Real.dist_eq]
  rw [hpoly p] at h1
  calc |∫ t, bcClamp C hC0 f f.continuous t ∂ν - ∫ t, bcClamp C hC0 f f.continuous t ∂ν'|
      ≤ |∫ t, bcClamp C hC0 f f.continuous t ∂ν -
          ∫ t, bcClamp C hC0 (fun t => p.eval t) p.continuous t ∂ν'| +
        |∫ t, bcClamp C hC0 (fun t => p.eval t) p.continuous t ∂ν' -
          ∫ t, bcClamp C hC0 f f.continuous t ∂ν'| := abs_sub_le _ _ _
    _ ≤ ε / 2 + ε / 2 := by rw [abs_sub_comm] at h2; exact add_le_add h1 h2
    _ = ε := by ring

end DOS

/-! ### Lemma 4.1 -/

lemma norm_amo_le (α θ : ℝ) : ‖amo α θ‖ ≤ 4 := by
  have h := norm_jacobi_le (v := fun x => 2 * Real.cos (2 * π * x)) (b := fun _ => 1)
    (Mv := 2) (Mb := 1) (fun x => by
      rw [abs_mul, show |(2 : ℝ)| = 2 from abs_two]
      nlinarith [abs_cos_le_one (2 * π * x)]) (fun x => by simp) α θ
  unfold amo
  linarith

lemma norm_chiral_le (α θ : ℝ) : ‖chiral α θ‖ ≤ 4 := by
  have h := norm_jacobi_le (v := fun _ => 0) (b := fun x => 2 * Real.sin (2 * π * x))
    (Mv := 0) (Mb := 2) (fun x => by simp) (fun x => by
      rw [abs_mul, show |(2 : ℝ)| = 2 from abs_two]
      nlinarith [abs_sin_le_one (2 * π * x)]) α θ
  unfold chiral
  linarith

/-- **Lemma 4.1 (`dn`): `N_{2α} = Ñ_α`.**  A density of states measure of `θ ↦ H_{2α,θ}` and one
of `θ ↦ H̃_{α,θ} = Ĥ_{α,1/4+α/2+θ}` coincide. -/
theorem dn (α : ℝ) {ν ν' : Measure ℝ}
    (hν : AMO.IsDOSMeasure (fun θ => amo (2 * α) θ) ν)
    (hν' : AMO.IsDOSMeasure (fun θ => chiral α (1 / 4 + α / 2 + θ)) ν') : ν = ν' :=
  dos_eq_of_moments hν hν'
    (fun _ => jacobi_isSelfAdjoint bddFun_two_cos (bddFun_const 1) _ _)
    (fun _ => jacobi_isSelfAdjoint (bddFun_const 0) (bddFun_two_sin (2 * π)) _ _)
    (fun _ => norm_amo_le _ _) (fun _ => norm_chiral_le _ _)
    (fun k => ChiralL2.moment_amo_chiral α k)

/-- **Lemma 4.1, IDS form:** `N_{2α}(E) = Ñ_α(E)` for all `E`. -/
theorem dn_IDS (α : ℝ) {ν ν' : Measure ℝ}
    (hν : AMO.IsDOSMeasure (fun θ => amo (2 * α) θ) ν)
    (hν' : AMO.IsDOSMeasure (fun θ => chiral α (1 / 4 + α / 2 + θ)) ν') (E : ℝ) :
    AMO.IDS ν E = AMO.IDS ν' E := by
  rw [dn α hν hν']

end CAH
