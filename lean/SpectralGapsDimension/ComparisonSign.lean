/-
Copyright (c) 2026. Formalization of
  S. Becker, "Self-dual perturbations of the critical almost Mathieu operator:
  Dry Ten Martini and Hausdorff dimension" (Paper II).

# Theorem 3.6 (`gap:thm:comparison`): reduction to `b ≥ 0`

The comparison operator is `H_b = U + U^{-1} + V + V^{-1} + b D`, `D = ∑_{m,n = ±1} W_{m,n}`
(`AMO.H α 1 (b • Dsym)`).  Explicitly (`Hb_apply`), with `θ_n = x + nα`,
`(H_{b,x} u)_n = A_b(θ_n + α/2) u_{n+1} + A_b(θ_n - α/2) u_{n-1} + 2 cos(2πθ_n) u_n`, where
`A_b(t) = 1 + 2b cos(2πt)` (`hopC`).  So `H_{b,x}` is a Jacobi operator.

* **Sign symmetry.**  The symbol map `R_{r,q} ↦ (-1)^{r+q} R_{r,q}` is implemented by the diagonal
  unitary `Γ = diag((-1)^n)` together with the phase shift `x ↦ x + 1/2`; it sends `amo 1 ↦ -amo 1`
  and fixes `D`.  Hence `H_{-b,x} = Γ (-H_{b,x+1/2}) Γ^{-1}` (`intertwines_neg`), so
  `Σ(H_{-b}) = -Σ(H_b)` (`Sigma_neg`) and the DOS measure is pushed forward by `t ↦ -t`
  (`dos_neg`).
* **Atomless DOS.**  For `|b| < 1/2` the hopping `A_b` never vanishes, so `H_{b,x} - E` is a Jacobi
  operator with nonvanishing hopping (`Hb_sub_eq_jacobi`), `dim ker(H_{b,x} - E) ≤ 2`, and Paper I's
  Lemma 2.8 (`SGD.dos_H_atomless`) makes the DOS atomless (`dos_Hb_atomless`).
* **Labels.**  Under `t ↦ -t` a gap with IDS `{nα}` becomes a gap with IDS `1 - {nα} = {(-n)α}`
  (needs atomlessness at the gap edges; `AMO.AllGapsOpen.map_affine_neg`), so every label of `Λ_α`
  is still open.

Hence `ComparisonClaim` reduces to the case `0 ≤ b < 1/2` (`comparison_of_nonneg`).
-/
import SpectralGapsDimension.Reductions
import SpectralGapsDimension.AtomlessCritical
import ErgodicShared.AffineIsland
import ErgodicShared.UnitaryTransfer
import ErgodicShared.JacobiKernel
import AnalyticPerturbationsAMO.Gauge

noncomputable section

open scoped ComplexConjugate InnerProductSpace
open MeasureTheory Set AMO L2

namespace SGD

/-! ### The comparison operator as a Jacobi operator -/

/-- The hopping `A_b(t) = 1 + b (e(t) + e(-t)) = 1 + 2b cos(2πt)` of `H_b`. -/
def hopC (b t : ℝ) : ℂ := 1 + (b : ℂ) * (e t + e (-t))

lemma smul_Dsym_eq (b : ℂ) :
    b • Dsym = Pi.single (1, 1) b + Pi.single (1, -1) b + Pi.single (-1, 1) b +
      Pi.single (-1, -1) b := by
  funext p
  obtain ⟨r, q⟩ := p
  simp only [Dsym, Pi.smul_apply, Pi.add_apply, smul_eq_mul, Pi.single_apply, Prod.mk.injEq]
  split_ifs <;> simp_all

/-- `H_b = U + U^{-1} + V + V^{-1} + b (W_{1,1} + W_{1,-1} + W_{-1,1} + W_{-1,-1})`. -/
lemma Hb_eq (α b x : ℝ) :
    H α 1 ((b : ℂ) • Dsym) x = U α x + W α x (-1) 0 + V α x + W α x 0 (-1) +
      ((b : ℂ) • W α x 1 1 + (b : ℂ) • W α x 1 (-1) + (b : ℂ) • W α x (-1) 1 +
        (b : ℂ) • W α x (-1) (-1)) := by
  have s := symbolSummable_single
  rw [H_eq α 1 (smul_Dsym_summable b) x, smul_Dsym_eq,
    op_add (((s _ _).add (s _ _)).add (s _ _)) (s _ _), op_add ((s _ _).add (s _ _)) (s _ _),
    op_add (s _ _) (s _ _), op_single, op_single, op_single, op_single]
  simp

/-- **Jacobi form of `H_b`**: `(H_{b,x} u)_n = A_b(θ_n + α/2) u_{n+1} + A_b(θ_n - α/2) u_{n-1}
+ (e(θ_n) + e(-θ_n)) u_n`, `θ_n = x + nα`. -/
lemma Hb_apply (α b x : ℝ) (u : L2 ℤ) (n : ℤ) :
    H α 1 ((b : ℂ) • Dsym) x u n =
      hopC b (x + n * α + α / 2) * u (n + 1) + hopC b (x + n * α - α / 2) * u (n - 1) +
        (e (x + n * α) + e (-(x + n * α))) * u n := by
  rw [Hb_eq]
  simp only [add_apply, FunLike.coe_smul, Pi.smul_apply,
    lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, smul_eq_mul, U_apply, V_apply, W_apply, hopC]
  push_cast
  simp only [mul_zero, zero_mul, zero_div, add_zero, e_zero, one_mul, zero_add, mul_one,
    ← sub_eq_add_neg]
  ring_nf

/-! ### The gauge `Γ = diag((-1)^n)` -/

lemma e_half : e (1 / 2) = -1 := by
  unfold e
  rw [show (((2 * Real.pi * (1 / 2) : ℝ)) : ℂ) * Complex.I = Real.pi * Complex.I by
    push_cast; ring]
  exact Complex.exp_pi_mul_I

lemma e_add_half (t : ℝ) : e (t + 1 / 2) = -e t := by
  rw [e_add, e_half, mul_neg_one]

lemma e_sub_half (t : ℝ) : e (t - 1 / 2) = -e t := by
  rw [show t - 1 / 2 = t + 1 / 2 + ((-1 : ℤ) : ℝ) by push_cast; ring, e_add_int, e_add_half]

lemma hopC_add_half (b t : ℝ) : hopC b (t + 1 / 2) = hopC (-b) t := by
  unfold hopC
  rw [e_add_half, show -(t + 1 / 2) = -t - 1 / 2 by ring, e_sub_half]
  push_cast
  ring

/-- The diagonal operator `Γ = diag(e(n/2)) = diag((-1)^n)`. -/
def gaugeOp : Op ℤ := diagOp (fun n : ℤ => e ((n : ℝ) / 2))

/-- `Γ^{-1} = diag(e(-n/2))`. -/
def gaugeOpInv : Op ℤ := diagOp (fun n : ℤ => e (-((n : ℝ) / 2)))

lemma gaugeOp_apply (u : L2 ℤ) (n : ℤ) : gaugeOp u n = e ((n : ℝ) / 2) * u n :=
  diagOp_apply (bdd_e _) u n

lemma gaugeOpInv_apply (u : L2 ℤ) (n : ℤ) : gaugeOpInv u n = e (-((n : ℝ) / 2)) * u n :=
  diagOp_apply (bdd_e _) u n

lemma star_gaugeOp : star gaugeOp = gaugeOpInv := by
  rw [gaugeOp, star_diagOp (bdd_e _)]
  simp only [conj_e]
  rfl

lemma gaugeOpInv_mul : gaugeOpInv * gaugeOp = 1 := by
  ext u n
  rw [mul_apply_eq_comp, gaugeOpInv_apply, gaugeOp_apply, ← mul_assoc, ← e_add,
    neg_add_cancel, e_zero, one_mul]
  rfl

lemma gaugeOp_mul_inv : gaugeOp * gaugeOpInv = 1 := by
  ext u n
  rw [mul_apply_eq_comp, gaugeOp_apply, gaugeOpInv_apply, ← mul_assoc, ← e_add,
    add_neg_cancel, e_zero, one_mul]
  rfl

/-- `Γ` as a unitary. -/
def gaugeUnitary : unitary (Op ℤ) :=
  ⟨gaugeOp, by
    refine ⟨?_, ?_⟩
    · rw [star_gaugeOp]; exact gaugeOpInv_mul
    · rw [star_gaugeOp]; exact gaugeOp_mul_inv⟩

/-- `Γ` as a linear isometry equivalence of `ℓ²(ℤ)`. -/
def gaugeU : L2 ℤ ≃ₗᵢ[ℂ] L2 ℤ := Unitary.linearIsometryEquiv gaugeUnitary

lemma gaugeU_apply (v : L2 ℤ) : gaugeU v = gaugeOp v := rfl

lemma gaugeU_symm_apply (v : L2 ℤ) : gaugeU.symm v = gaugeOpInv v := by
  rw [LinearIsometryEquiv.symm_apply_eq, gaugeU_apply, ← mul_apply_eq_comp,
    gaugeOp_mul_inv]
  rfl

lemma gaugeU_delta_zero : gaugeU (delta 0) = delta 0 := by
  rw [gaugeU_apply]
  ext n
  rw [gaugeOp_apply]
  by_cases h : n = 0
  · subst h; simp
  · simp [delta, lp.single_apply, Pi.single_eq_of_ne h]

lemma gaugeU_symm_delta_zero : gaugeU.symm (delta 0) = delta 0 := by
  rw [LinearIsometryEquiv.symm_apply_eq, gaugeU_delta_zero]

lemma inner_delta_zero_gaugeU (w : L2 ℤ) : ⟪delta 0, gaugeU w⟫_ℂ = ⟪delta 0, w⟫_ℂ := by
  have h : ⟪delta 0, gaugeU w⟫_ℂ = ⟪gaugeU (delta 0), gaugeU w⟫_ℂ := by
    rw [gaugeU_delta_zero]
  rw [h, LinearIsometryEquiv.inner_map_map]

lemma e_succ_half (n : ℤ) : e (((n + 1 : ℤ) : ℝ) / 2) = -e ((n : ℝ) / 2) := by
  rw [show (((n + 1 : ℤ) : ℝ) / 2) = (n : ℝ) / 2 + 1 / 2 by push_cast; ring, e_add_half]

lemma e_pred_half (n : ℤ) : e (((n - 1 : ℤ) : ℝ) / 2) = -e ((n : ℝ) / 2) := by
  rw [show (((n - 1 : ℤ) : ℝ) / 2) = (n : ℝ) / 2 - 1 / 2 by push_cast; ring, e_sub_half]

/-- **Sign symmetry**: `H_{-b,x} = Γ (-H_{b,x+1/2}) Γ^{-1}`. -/
theorem intertwines_neg (α b x : ℝ) :
    CMS.Intertwines gaugeU (CMS.affineOp 0 (-1) (H α 1 ((b : ℂ) • Dsym) (x + 1 / 2)))
      (H α 1 (((-b : ℝ) : ℂ) • Dsym) x) := by
  intro v
  ext n
  rw [Hb_apply, gaugeU_apply, gaugeU_apply, gaugeOp_apply, gaugeOp_apply, gaugeOp_apply,
    gaugeOp_apply, e_succ_half, e_pred_half]
  simp only [CMS.affineOp, Algebra.algebraMap_eq_smul_one, add_apply,
    FunLike.coe_smul, Pi.smul_apply, one_apply_eq_self, lp.coeFn_add,
    lp.coeFn_smul, Pi.add_apply, smul_eq_mul, Complex.ofReal_zero, zero_mul]
  rw [Hb_apply, show x + 1 / 2 + n * α + α / 2 = (x + n * α + α / 2) + 1 / 2 by ring,
    show x + 1 / 2 + n * α - α / 2 = (x + n * α - α / 2) + 1 / 2 by ring,
    show -(x + 1 / 2 + n * α) = -(x + n * α) - 1 / 2 by ring,
    show x + 1 / 2 + n * α = (x + n * α) + 1 / 2 by ring,
    hopC_add_half, hopC_add_half, e_add_half, e_sub_half]
  push_cast
  ring

/-- `Σ(H_{-b}) = -Σ(H_b)` for irrational `α`. -/
theorem Sigma_neg {α : ℝ} (hα : Irrational α) (b : ℝ) :
    Sigma α 1 (((-b : ℝ) : ℂ) • Dsym) = CMS.affine 0 (-1) '' Sigma α 1 ((b : ℂ) • Dsym) := by
  show spectrum ℝ (H α 1 (((-b : ℝ) : ℂ) • Dsym) 0) = _
  refine ((intertwines_neg α b 0).spectrum_real_eq).trans ?_
  refine (CMS.spectrum_affineOp 0 (-1) (isSelfAdjoint_H α 1 (smul_Dsym_summable b)
      (smul_Dsym_selfAdjoint b) _)).trans ?_
  rw [spectrum_H_eq_Sigma hα (smul_Dsym_summable b) (smul_Dsym_selfAdjoint b)]

lemma H_add_one (α : ℝ) (R : Symbol) (y : ℝ) : H α 1 R (y + 1) = H α 1 R y := by
  have h := op_add_int α (amo ((1 : ℝ) : ℂ) + R) y 1
  rw [Int.cast_one] at h
  exact h

/-- The DOS of `H_{-b}` is the pushforward of that of `H_b` under `t ↦ -t`. -/
theorem dos_neg {α b : ℝ} {ν : Measure ℝ} (hν : IsDOSMeasure (H α 1 ((b : ℂ) • Dsym)) ν) :
    IsDOSMeasure (H α 1 (((-b : ℝ) : ℂ) • Dsym)) (ν.map (CMS.affine 0 (-1))) := by
  have hsa := fun x => isSelfAdjoint_H α 1 (smul_Dsym_summable b) (smul_Dsym_selfAdjoint b) x
  have h1 := hν.map_affine hsa 0 (-1)
  refine ⟨h1.1, fun f => ?_⟩
  rw [h1.2 f]
  set F : ℂ → ℂ := fun z => ((f z.re : ℝ) : ℂ)
  set G : ℝ → ℝ := fun y => RCLike.re ⟪delta 0, cfc F
    (CMS.affineOp 0 (-1) (H α 1 ((b : ℂ) • Dsym) y)) (delta 0)⟫_ℂ with hG
  have hx : ∀ x, RCLike.re ⟪delta 0, cfc F (H α 1 (((-b : ℝ) : ℂ) • Dsym) x) (delta 0)⟫_ℂ =
      G (x + 1 / 2) := by
    intro x
    rw [(intertwines_neg α b x).cfc_eq, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
      gaugeU_symm_delta_zero, inner_delta_zero_gaugeU]
  have hper : Function.Periodic G 1 := by
    intro y
    simp only [hG, H_add_one]
  simp only [hx]
  rw [intervalIntegral.integral_comp_add_right G (1 / 2)]
  have := hper.intervalIntegral_add_eq (1 / 2) 0
  rw [show (0 : ℝ) + 1 / 2 = 1 / 2 by norm_num, show (1 : ℝ) + 1 / 2 = 1 / 2 + 1 by norm_num,
    this, zero_add]

/-! ### Atomless DOS for `|b| < 1/2` -/

lemma norm_hopC_le (b t : ℝ) : ‖hopC b t‖ ≤ 1 + |b| * 2 := by
  unfold hopC
  have h2 : ‖e t + e (-t)‖ ≤ 2 := by
    refine (norm_add_le _ _).trans ?_
    simp only [norm_e]; norm_num
  calc ‖1 + (b : ℂ) * (e t + e (-t))‖ ≤ ‖(1 : ℂ)‖ + ‖(b : ℂ) * (e t + e (-t))‖ := norm_add_le _ _
    _ = 1 + |b| * ‖e t + e (-t)‖ := by
      rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ 1 + |b| * 2 := by gcongr

lemma hopC_ne_zero {b : ℝ} (hb : |b| < 1 / 2) (t : ℝ) : hopC b t ≠ 0 := by
  intro h
  unfold hopC at h
  have h1 : (b : ℂ) * (e t + e (-t)) = -1 := by linear_combination h
  have h2 : ‖(b : ℂ) * (e t + e (-t))‖ ≤ |b| * 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    gcongr
    refine (norm_add_le _ _).trans ?_
    simp only [norm_e]; norm_num
  rw [h1, norm_neg, norm_one] at h2
  linarith

lemma conj_hopC (b t : ℝ) : conj (hopC b t) = hopC b t := by
  unfold hopC
  simp only [map_add, map_mul, map_one, Complex.conj_ofReal, conj_e, neg_neg]
  ring

/-- `e` on `ℂ`: `eC z = exp(2πiz)`. -/
def eC (z : ℂ) : ℂ := Complex.exp (2 * Real.pi * z * Complex.I)

lemma eC_ofReal (t : ℝ) : eC (t : ℂ) = e t := by
  unfold eC e
  congr 1
  push_cast
  ring

/-- The analytic hopping `a(z) = 1 + b(e(z + α/2) + e(-z - α/2))`. -/
def hopA (b α : ℝ) (z : ℂ) : ℂ := 1 + (b : ℂ) * (eC (z + (α / 2 : ℝ)) + eC (-(z + (α / 2 : ℝ))))

/-- The analytic diagonal `c(z) = e(z) + e(-z) - E`. -/
def diagC (E : ℝ) (z : ℂ) : ℂ := eC z + eC (-z) - E

lemma hopA_ofReal (b α t : ℝ) : hopA b α (t : ℂ) = hopC b (t + α / 2) := by
  unfold hopA hopC
  rw [show (t : ℂ) + ((α / 2 : ℝ) : ℂ) = ((t + α / 2 : ℝ) : ℂ) by push_cast; ring,
    show -(((t + α / 2 : ℝ)) : ℂ) = ((-(t + α / 2) : ℝ) : ℂ) by push_cast; ring,
    eC_ofReal, eC_ofReal]

lemma diagC_ofReal (E t : ℝ) : diagC E (t : ℂ) = e t + e (-t) - E := by
  unfold diagC
  rw [show -(t : ℂ) = ((-t : ℝ) : ℂ) by push_cast; ring, eC_ofReal, eC_ofReal]

lemma jacobiBdd_Hb (α b E x : ℝ) : JacobiBdd α (hopA b α) (diagC E) x := by
  refine ⟨⟨1 + |b| * 2, fun n => ?_⟩, ⟨2 + |E|, fun n => ?_⟩⟩
  · dsimp only; rw [hopA_ofReal]; exact norm_hopC_le _ _
  · dsimp only; rw [diagC_ofReal]
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    have : ‖e (x + n * α) + e (-(x + n * α))‖ ≤ 2 := by
      refine (norm_add_le _ _).trans ?_
      simp only [norm_e]; norm_num
    linarith

/-- `H_{b,x} - E` is the Jacobi operator with hopping `hopA` and diagonal `diagC`. -/
theorem Hb_sub_eq_jacobi (α b E x : ℝ) :
    (H α 1 ((b : ℂ) • Dsym) x - (E : ℂ) • 1 : Op ℤ) = jacobi α (hopA b α) (diagC E) x := by
  ext u n
  rw [jacobi_apply (jacobiBdd_Hb α b E x), hopA_ofReal, hopA_ofReal, conj_hopC, diagC_ofReal]
  simp only [sub_apply, FunLike.coe_smul, Pi.smul_apply,
    one_apply_eq_self, lp.coeFn_sub, lp.coeFn_smul, Pi.sub_apply, smul_eq_mul]
  rw [Hb_apply, show x + ((n : ℝ) - 1) * α + α / 2 = x + n * α - α / 2 by ring]
  ring

/-- **Atomless DOS of the comparison operator** for `|b| < 1/2` (Paper I, Lemma 2.8, with the
Jacobi kernel bound `dim ker(H_{b,x} - E) ≤ 2`). -/
theorem dos_Hb_atomless {α b : ℝ} (hb : |b| < 1 / 2) {ν : Measure ℝ}
    (hν : IsDOSMeasure (H α 1 ((b : ℂ) • Dsym)) ν) : ∀ E, ν {E} = 0 := by
  have ha : ∀ x : ℝ, ∀ n : ℤ, hopA b α ((x + n * α : ℝ) : ℂ) ≠ 0 := fun x n => by
    rw [hopA_ofReal]; exact hopC_ne_zero hb _
  refine dos_H_atomless (d := 2) (smul_Dsym_summable b) (smul_Dsym_selfAdjoint b) hν
    (fun x E => ?_) (fun x E => ?_)
  · rw [Hb_sub_eq_jacobi]
    exact CMS.finiteDimensional_ker_jacobi (jacobiBdd_Hb α b E x) (ha x)
  · rw [Hb_sub_eq_jacobi]
    exact CMS.finrank_ker_jacobi_le_two (jacobiBdd_Hb α b E x) (ha x)

/-! ### The sign reduction of Theorem 3.6 -/

/-- **Theorem 3.6 (`gap:thm:comparison`), nonnegative coupling** (stated, not asserted): for every
irrational `α` and `0 ≤ b < 1/2`, `H_b = H_0 + bD` has an open gap of each label in `Λ_α`. -/
def ComparisonNonnegClaim : Prop :=
  ∀ {α : ℝ} (_hα : Irrational α) {b : ℝ} (_hb0 : 0 ≤ b) (_hb : b < 1 / 2),
    AllLabelsOpen α ((b : ℂ) • Dsym)

/-- **Sign reduction of Theorem 3.6**: the case `-1/2 < b < 0` follows from `0 < -b < 1/2` by the
sign symmetry `H_{-b} ≅ -H_b` (phase shift `1/2` and gauge `diag((-1)^n)`), the reflection of the
DOS, atomlessness of the DOS and `1 - {nα} = {(-n)α}`. -/
theorem comparison_of_nonneg (h : ComparisonNonnegClaim) : ComparisonClaim := by
  intro α hα b hb
  obtain ⟨hb1, hb2⟩ := abs_lt.1 hb
  rcases le_or_gt 0 b with hb0 | hb0
  · exact h hα hb0 hb2
  · obtain ⟨ν, hν, hgaps⟩ := h hα (b := -b) (by linarith) (by linarith)
    have hat := dos_Hb_atomless (by rwa [abs_neg]) hν
    have := hν.1
    refine ⟨ν.map (CMS.affine 0 (-1)), ?_, ?_⟩
    · have := dos_neg hν
      rwa [neg_neg] at this
    · have := hgaps.map_affine_neg hat hα 0 (by norm_num : (-1 : ℝ) < 0)
      rw [← Sigma_neg hα, neg_neg] at this
      exact this

end SGD
