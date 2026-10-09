/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Appendix A.3, preliminaries: radial mollifiers and Laplacians of convolutions

* `DF.Distr.moll r` — a smooth radial mollifier supported in `closedBall 0 r` with integral one;
* `DF.Distr.laplacian_conv` — `Δ(F ⋆ g) = F ⋆ Δg` for locally integrable `F` and compactly
  supported `C²` functions `g`;
* `DF.Distr.harmonicAt_mollify` — if `∫ F Δφ = 0` for all test functions `φ` supported in an open
  set `V`, then the mollification `F ⋆ moll r` is harmonic at every `x` with
  `closedBall x r ⊆ V`.
-/
import DamanikFillman.AppA.Radial
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

noncomputable section

open Real Complex Metric Set Filter Topology MeasureTheory Laplacian InnerProductSpace
open scoped Convolution

namespace DF

namespace Distr

/-! ### The mollifier -/

/-- The basic bump `z ↦ smoothTransition (1 - |z|²)`. -/
def bump0 (z : ℂ) : ℝ := Real.smoothTransition (1 - ‖z‖ ^ 2)

lemma contDiff_smoothTransition_two : ContDiff ℝ 2 Real.smoothTransition := by
  have := Real.smoothTransition.contDiff (n := 2)
  exact_mod_cast this

lemma contDiff_bump0 : ContDiff ℝ 2 bump0 :=
  contDiff_smoothTransition_two.comp (contDiff_const.sub (contDiff_norm_sq ℝ))

lemma bump0_nonneg (z : ℂ) : 0 ≤ bump0 z := Real.smoothTransition.nonneg _

lemma bump0_eq_zero {z : ℂ} (hz : 1 ≤ ‖z‖) : bump0 z = 0 :=
  Real.smoothTransition.zero_of_nonpos (by nlinarith)

lemma bump0_zero : bump0 0 = 1 :=
  Real.smoothTransition.one_of_one_le (by simp)

lemma hasCompactSupport_bump0 : HasCompactSupport bump0 :=
  HasCompactSupport.intro (isCompact_closedBall 0 1) fun z hz => bump0_eq_zero (by
    rw [mem_closedBall, dist_zero_right, not_le] at hz
    exact hz.le)

/-- The mass of the basic bump. -/
def bumpMass : ℝ := ∫ z, bump0 z

lemma bumpMass_pos : 0 < bumpMass :=
  contDiff_bump0.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    hasCompactSupport_bump0 bump0_nonneg (x := 0) (by rw [bump0_zero]; exact one_ne_zero)

/-- The mollifier `moll r z = (m r²)⁻¹ bump0 (z / r)`, supported in `closedBall 0 r`. -/
def moll (r : ℝ) (z : ℂ) : ℝ := (bumpMass * r ^ 2)⁻¹ * bump0 (r⁻¹ • z)

lemma contDiff_moll (r : ℝ) : ContDiff ℝ 2 (moll r) :=
  contDiff_const.mul (contDiff_bump0.comp (contDiff_const_smul r⁻¹))

lemma moll_nonneg {r : ℝ} (z : ℂ) : 0 ≤ moll r z :=
  mul_nonneg (inv_nonneg.2 (mul_nonneg bumpMass_pos.le (sq_nonneg r))) (bump0_nonneg _)

lemma norm_inv_smul {r : ℝ} (hr : 0 < r) (z : ℂ) : ‖r⁻¹ • z‖ = r⁻¹ * ‖z‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr]

lemma moll_eq_zero {r : ℝ} (hr : 0 < r) {z : ℂ} (hz : r ≤ ‖z‖) : moll r z = 0 := by
  unfold moll
  rw [bump0_eq_zero, mul_zero]
  rw [norm_inv_smul hr, ← div_eq_inv_mul, le_div_iff₀ hr, one_mul]
  exact hz

lemma moll_le {r : ℝ} (z : ℂ) : moll r z ≤ (bumpMass * r ^ 2)⁻¹ := by
  unfold moll
  exact mul_le_of_le_one_right (inv_nonneg.2 (mul_nonneg bumpMass_pos.le (sq_nonneg r)))
    (Real.smoothTransition.le_one _)

/-- The radial profile of `moll r`. -/
def mollRad (r ρ : ℝ) : ℝ := (bumpMass * r ^ 2)⁻¹ * Real.smoothTransition (1 - (r⁻¹ * ρ) ^ 2)

lemma moll_eq_mollRad {r : ℝ} (hr : 0 < r) (z : ℂ) : moll r z = mollRad r ‖z‖ := by
  simp only [moll, mollRad, bump0, norm_inv_smul hr]

lemma moll_neg {r : ℝ} (hr : 0 < r) (z : ℂ) : moll r (-z) = moll r z := by
  rw [moll_eq_mollRad hr, moll_eq_mollRad hr, norm_neg]

lemma hasCompactSupport_moll {r : ℝ} (hr : 0 < r) : HasCompactSupport (moll r) :=
  HasCompactSupport.intro (isCompact_closedBall 0 r) fun z hz => moll_eq_zero hr (by
    rw [mem_closedBall, dist_zero_right, not_le] at hz
    exact hz.le)

lemma integral_moll {r : ℝ} (hr : 0 < r) : ∫ z, moll r z = 1 := by
  unfold moll
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume bump0 hr.le,
    Complex.finrank_real_complex, smul_eq_mul]
  change (bumpMass * r ^ 2)⁻¹ * (r ^ 2 * bumpMass) = 1
  have := bumpMass_pos.ne'
  field_simp

lemma continuous_moll (r : ℝ) : Continuous (moll r) := (contDiff_moll r).continuous

/-! ### Directional derivatives and Laplacians of convolutions -/

/-- `∂_v (F ⋆ g) = F ⋆ ∂_v g`. -/
lemma Dv_conv {F g : ℂ → ℝ} (hF : LocallyIntegrable F) (hg : ContDiff ℝ 1 g)
    (hgc : HasCompactSupport g) (v : ℂ) :
    Dv (F ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) v =
      F ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (Dv g v) := by
  funext x
  show fderiv ℝ (F ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x v =
    (F ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] fun z => fderiv ℝ g z v) x
  rw [(HasCompactSupport.hasFDerivAt_convolution_right (L := ContinuousLinearMap.lsmul ℝ ℝ)
    hgc hF hg x).fderiv]
  exact convolution_precompR_apply (L := ContinuousLinearMap.lsmul ℝ ℝ) hF
    (hgc.fderiv (𝕜 := ℝ)) (hg.continuous_fderiv one_ne_zero) x v

lemma contDiff_conv {F g : ℂ → ℝ} (hF : LocallyIntegrable F) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) :
    ContDiff ℝ 2 (F ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) := by
  have hg' : ContDiff ℝ ((2 : ℕ∞) : WithTop ℕ∞) g := by exact_mod_cast hg
  have := hgc.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ) hF hg'
  exact_mod_cast this

/-- `Δ (F ⋆ g) = F ⋆ Δ g`. -/
theorem laplacian_conv {F g : ℂ → ℝ} (hF : LocallyIntegrable F) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (x : ℂ) :
    Δ (F ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x =
      (F ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] Δ g) x := by
  rw [laplacian_eq_Dv (contDiff_conv hF hg hgc),
    Dv_conv hF (hg.of_le (by norm_num)) hgc 1,
    Dv_conv hF (contDiff_one_Dv hg 1) (hasCompactSupport_Dv hgc 1) 1,
    Dv_conv hF (hg.of_le (by norm_num)) hgc I,
    Dv_conv hF (contDiff_one_Dv hg I) (hasCompactSupport_Dv hgc I) I]
  have e : Δ g = Dv (Dv g 1) 1 + Dv (Dv g I) I := funext (laplacian_eq_Dv hg)
  rw [e, ConvolutionExistsAt.distrib_add]
  · exact (hasCompactSupport_Dv (hasCompactSupport_Dv hgc 1) 1).convolutionExists_right
      (ContinuousLinearMap.lsmul ℝ ℝ) hF (continuous_Dv (contDiff_one_Dv hg 1) 1) x
  · exact (hasCompactSupport_Dv (hasCompactSupport_Dv hgc I) I).convolutionExists_right
      (ContinuousLinearMap.lsmul ℝ ℝ) hF (continuous_Dv (contDiff_one_Dv hg I) I) x

/-! ### Reflections -/

lemma Dv_reflect {g : ℂ → ℝ} (hg : Differentiable ℝ g) (x v : ℂ) :
    Dv (fun t => g (x - t)) v = fun t => -(Dv g v (x - t)) := by
  funext t
  have h : HasFDerivAt (fun t => g (x - t))
      ((fderiv ℝ g (x - t)).comp (-ContinuousLinearMap.id ℝ ℂ)) t :=
    (hg (x - t)).hasFDerivAt.comp t ((hasFDerivAt_id t).const_sub x)
  show fderiv ℝ (fun t => g (x - t)) t v = -(fderiv ℝ g (x - t) v)
  rw [h.fderiv]
  simp

lemma Dv_neg' (f : ℂ → ℝ) (v : ℂ) : Dv (fun s => -f s) v = fun s => -(Dv f v s) := by
  funext s
  show fderiv ℝ (fun s => -f s) s v = -(fderiv ℝ f s v)
  rw [fderiv_fun_neg]
  rfl

lemma laplacian_reflect {g : ℂ → ℝ} (hg : ContDiff ℝ 2 g) (x t : ℂ) :
    Δ (fun t => g (x - t)) t = Δ g (x - t) := by
  have hψ : ContDiff ℝ 2 (fun t => g (x - t)) := hg.comp (contDiff_const.sub contDiff_id)
  have hd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have key : ∀ v : ℂ, Dv (Dv (fun t => g (x - t)) v) v t = Dv (Dv g v) v (x - t) := by
    intro v
    rw [Dv_reflect hd x v]
    have hd' : Differentiable ℝ (fun s => -Dv g v s) := (differentiable_Dv hg v).neg
    rw [Dv_reflect (g := fun s => -Dv g v s) hd' x v, Dv_neg']
    simp
  rw [laplacian_eq_Dv hψ, laplacian_eq_Dv hg, key 1, key I]

/-! ### Mollification of distributional solutions of `Δ F = 0` -/

/-- The mollification `F ⋆ moll r`. -/
def mollify (F : ℂ → ℝ) (r : ℝ) : ℂ → ℝ :=
  F ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] moll r

lemma mollify_apply (F : ℂ → ℝ) (r : ℝ) (x : ℂ) :
    mollify F r x = ∫ t, F t * moll r (x - t) := by
  simp only [mollify, convolution_lsmul, smul_eq_mul]

lemma contDiff_mollify {F : ℂ → ℝ} (hF : LocallyIntegrable F) {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ 2 (mollify F r) :=
  contDiff_conv hF (contDiff_moll r) (hasCompactSupport_moll hr)

lemma support_moll_reflect_subset {r : ℝ} (hr : 0 < r) (x : ℂ) :
    tsupport (fun t => moll r (x - t)) ⊆ closedBall x r := by
  refine closure_minimal (fun t ht => ?_) isClosed_closedBall
  rw [mem_closedBall, dist_comm, dist_eq_norm]
  by_contra h
  exact ht (moll_eq_zero hr (not_le.1 h).le)

/-- The hypothesis "`Δ F = 0` on `V` in the sense of distributions". -/
def DistribHarmonicOn (F : ℂ → ℝ) (V : Set ℂ) : Prop :=
  ∀ φ : ℂ → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → tsupport φ ⊆ V →
    ∫ z, F z * Δ φ z = 0

/-- Mollifications of distributional solutions of `ΔF = 0` are harmonic. -/
theorem harmonicAt_mollify {F : ℂ → ℝ} (hF : LocallyIntegrable F) {V : Set ℂ} (hV : IsOpen V)
    (hyp : DistribHarmonicOn F V) {r : ℝ} (hr : 0 < r) {x₀ : ℂ} (hx₀ : closedBall x₀ r ⊆ V) :
    HarmonicAt (mollify F r) x₀ := by
  obtain ⟨δ, hδ, hδs⟩ := (isCompact_closedBall x₀ r).exists_thickening_subset_open hV hx₀
  refine ⟨(contDiff_mollify hF hr).contDiffAt, ?_⟩
  filter_upwards [ball_mem_nhds x₀ hδ] with x hx
  rw [Pi.zero_apply, mollify,
    laplacian_conv hF (contDiff_moll r) (hasCompactSupport_moll hr) x, convolution_lsmul]
  simp only [smul_eq_mul]
  have hψ : ContDiff ℝ 2 (fun t => moll r (x - t)) :=
    (contDiff_moll r).comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport (fun t => moll r (x - t)) :=
    (hasCompactSupport_moll hr).comp_homeomorph (Homeomorph.subLeft x)
  have hψs : tsupport (fun t => moll r (x - t)) ⊆ V := by
    refine (support_moll_reflect_subset hr x).trans fun z hz => hδs ?_
    rw [thickening_closedBall hδ hr.le, mem_ball]
    rw [mem_closedBall] at hz
    rw [mem_ball] at hx
    linarith [dist_triangle z x x₀]
  have := hyp _ hψ hψc hψs
  simp only [laplacian_reflect (contDiff_moll r) x] at this
  exact this

end Distr

end DF
