/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Appendix A.3: subharmonic functions have nonnegative distributional Laplacian

`DF.Distr.integral_mul_laplacian_nonneg`: if `u` is (real-valued) subharmonic on an open set
`U` and `φ ≥ 0` is a compactly supported `C²` function with support in `U`, then
`∫ u Δφ ≥ 0`.

Proof: with `M_r f(z) = ∫ f(z + y) moll_r(y) dy`, the operator `M_r` is symmetric, so
`∫ u (M_r φ - φ) = ∫ (M_r u - u) φ ≥ 0` by the sub-mean value inequality; on the other hand
`M_r φ - φ = (Q(r)/4) Δφ + o(Q(r))` uniformly (`taylor_moll`).
-/
import DamanikFillman.AppA.Taylor

noncomputable section

open Real Complex Metric Set Filter Topology MeasureTheory Laplacian InnerProductSpace
open scoped Convolution

namespace DF

namespace Distr

/-! ### The second moment of the mollifier -/

/-- The second moment `Q(r) = ∫ |y|² moll_r(y) dy`. -/
def mollQ (r : ℝ) : ℝ := ∫ y, ‖y‖ ^ 2 * moll r y

lemma mollQ_pos {r : ℝ} (hr : 0 < r) : 0 < mollQ r := by
  have hc : Continuous (fun y : ℂ => ‖y‖ ^ 2 * moll r y) :=
    (continuous_norm.pow 2).mul (continuous_moll r)
  refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (hasCompactSupport_moll hr).mul_left (fun y => mul_nonneg (sq_nonneg _) (moll_nonneg y))
    (x := ((r / 2 : ℝ) : ℂ)) ?_
  have hn : ‖((r / 2 : ℝ) : ℂ)‖ = r / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  refine mul_ne_zero (by rw [hn]; positivity) ?_
  rw [moll_eq_mollRad hr, hn]
  unfold mollRad
  refine mul_ne_zero (inv_ne_zero (mul_pos bumpMass_pos (by positivity)).ne') ?_
  refine (Real.smoothTransition.pos_of_pos ?_).ne'
  have : r⁻¹ * (r / 2) = 1 / 2 := by field_simp
  rw [this]
  norm_num

/-! ### Taylor expansion of the mollification -/

lemma integrable_mul_moll {h : ℂ → ℝ} (hh : Continuous h) {r : ℝ} (hr : 0 < r) :
    Integrable (fun y => h y * moll r y) :=
  (hh.mul (continuous_moll r)).integrable_of_hasCompactSupport (hasCompactSupport_moll hr).mul_left

/-- **Taylor expansion of mollifications**, uniformly in `z`. -/
theorem taylor_moll {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ r : ℝ, 0 < r → r < δ → ∀ z : ℂ,
      |∫ y, φ (z + y) * moll r y - φ z - Δ φ z / 4 * mollQ r| ≤ ε * mollQ r := by
  obtain ⟨δ, hδ, hT⟩ := taylor_circle hφ hφc (ε := ε / (2 * π)) (by positivity)
  refine ⟨δ, hδ, fun r hr hrδ z => ?_⟩
  have hc : Continuous φ := hφ.continuous
  set f : ℂ → ℝ := fun y => (φ (z + y) - φ z - ‖y‖ ^ 2 / 4 * Δ φ z) * moll r y with hf
  set g : ℂ → ℝ := fun y => ‖y‖ ^ 2 * moll r y with hg
  have hfc : Continuous f :=
    (((hc.comp (continuous_const.add continuous_id)).sub continuous_const).sub
      (((continuous_norm.pow 2).div_const 4).mul continuous_const)).mul (continuous_moll r)
  have hgc : Continuous g := (continuous_norm.pow 2).mul (continuous_moll r)
  have hfcs : HasCompactSupport f := (hasCompactSupport_moll hr).mul_left
  have hgcs : HasCompactSupport g := (hasCompactSupport_moll hr).mul_left
  obtain ⟨Cf, hCf⟩ := hfcs.exists_bound_of_continuous hfc
  obtain ⟨Cg, hCg⟩ := hgcs.exists_bound_of_continuous hgc
  have hfs : ∀ y, r < ‖y‖ → f y = 0 := fun y hy => by
    simp only [hf]; rw [moll_eq_zero hr hy.le, mul_zero]
  have hgs : ∀ y, r < ‖y‖ → g y = 0 := fun y hy => by
    simp only [hg]; rw [moll_eq_zero hr hy.le, mul_zero]
  obtain ⟨hIf, hPf⟩ := polar_of_bdd hfc.measurable (C := Cf)
    (fun y => by rw [← Real.norm_eq_abs]; exact hCf y) hfs
  obtain ⟨hIg, hPg⟩ := polar_of_bdd hgc.measurable (C := Cg)
    (fun y => by rw [← Real.norm_eq_abs]; exact hCg y) hgs
  -- expand `∫ f`
  have hexp : ∫ y, f y = ∫ y, φ (z + y) * moll r y - φ z - Δ φ z / 4 * mollQ r := by
    have e : f = fun y => (φ (z + y) * moll r y - φ z * moll r y) -
        Δ φ z / 4 * (‖y‖ ^ 2 * moll r y) := by
      funext y; simp only [hf]; ring
    have iA : Integrable (fun y => φ (z + y) * moll r y) :=
      integrable_mul_moll (hc.comp (continuous_const.add continuous_id)) hr
    have iB : Integrable (fun y => φ z * moll r y) :=
      ((continuous_moll r).integrable_of_hasCompactSupport (hasCompactSupport_moll hr)).const_mul _
    have iC : Integrable (fun y => Δ φ z / 4 * (‖y‖ ^ 2 * moll r y)) :=
      (integrable_mul_moll (continuous_norm.pow 2) hr).const_mul _
    rw [e, integral_sub (iA.sub iB) iC, integral_sub iA iB, integral_const_mul, integral_const_mul,
      integral_moll hr, mul_one, mollQ]
  have hQg : mollQ r = ∫ y, g y := rfl
  rw [← hexp, hPf, hQg, hPg, ← integral_const_mul, ← Real.norm_eq_abs]
  refine norm_integral_le_of_norm_le (hIg.const_mul ε)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun ρ hρ => ?_))
  have hρ0 : (0 : ℝ) < ρ := hρ
  have hk : ∀ θ : ℝ, moll r (ρ * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I)) = mollRad r ρ :=
    fun θ => by rw [moll_eq_mollRad hr, norm_ofReal_mul_e, abs_of_pos hρ0]
  have hn2 : ∀ θ : ℝ, ‖(ρ : ℂ) * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I)‖ ^ 2 = ρ ^ 2 :=
    fun θ => by rw [norm_ofReal_mul_e, abs_of_pos hρ0]
  have hA : ∫ θ in Ioo (-π) π, ρ * f (ρ * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I)) =
      ρ * mollRad r ρ * ∫ θ in Ioo (-π) π, (φ (z + ρ * eθ θ) - φ z - ρ ^ 2 / 4 * Δ φ z) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
    simp only [hf, hk, hn2, eθ]
    ring
  have hB : ∫ θ in Ioo (-π) π, ρ * g (ρ * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I)) =
      2 * π * (ρ ^ 3 * mollRad r ρ) := by
    have : ∀ θ : ℝ, ρ * g (ρ * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I)) =
        ρ ^ 3 * mollRad r ρ := fun θ => by simp only [hg, hk, hn2]; ring
    simp only [this]
    rw [setIntegral_const, Real.volume_real_Ioo_of_le (show -π ≤ π by linarith [pi_pos]),
      smul_eq_mul]
    ring
  show ‖∫ θ in Ioo (-π) π, ρ * f (ρ * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I))‖ ≤
    ε * ∫ θ in Ioo (-π) π, ρ * g (ρ * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I))
  rw [hA, hB, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (mul_nonneg hρ0.le (mollRad_nonneg r ρ))]
  by_cases hρr : ρ < r
  · have h := hT ρ hρ0.le (hρr.trans hrδ) z
    calc ρ * mollRad r ρ * |∫ θ in Ioo (-π) π, (φ (z + ρ * eθ θ) - φ z - ρ ^ 2 / 4 * Δ φ z)|
        ≤ ρ * mollRad r ρ * (2 * π * (ε / (2 * π)) * ρ ^ 2) :=
          mul_le_mul_of_nonneg_left h (mul_nonneg hρ0.le (mollRad_nonneg r ρ))
      _ = ε * (2 * π * (ρ ^ 3 * mollRad r ρ)) := by
          have := Real.pi_pos.ne'
          field_simp
          ring
  · have hk0 : mollRad r ρ = 0 := by
      have := moll_eq_zero hr (z := (ρ : ℂ)) (by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]; exact not_lt.1 hρr)
      rwa [moll_eq_mollRad hr, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0] at this
    simp [hk0]

/-! ### Symmetry of the mollification operator -/

/-- `∫ f · M_r g = ∫ M_r f · g`. -/
theorem integral_mul_mollify_symm {f g : ℂ → ℝ} (hf : Integrable f) (hg : Continuous g)
    (hgc : HasCompactSupport g) {r : ℝ} (hr : 0 < r) :
    ∫ z, f z * ∫ y, g (z + y) * moll r y = ∫ z, (∫ y, f (z + y) * moll r y) * g z := by
  obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hg
  set K : ℂ → ℂ → ℝ := fun z w => f z * g w * moll r (w - z) with hK
  have hmeas : AEStronglyMeasurable (Function.uncurry K) (volume.prod volume) := by
    show AEStronglyMeasurable (fun p : ℂ × ℂ => f p.1 * g p.2 * moll r (p.2 - p.1)) _
    exact ((hf.aestronglyMeasurable.comp_fst (ν := volume)).mul
      (hg.comp continuous_snd).aestronglyMeasurable).mul
      ((continuous_moll r).comp (continuous_snd.sub continuous_fst)).aestronglyMeasurable
  have hmollw : ∀ z : ℂ, Integrable (fun w => moll r (w - z)) := fun z =>
    ((continuous_moll r).comp (continuous_id.sub continuous_const)).integrable_of_hasCompactSupport
      ((hasCompactSupport_moll hr).comp_homeomorph (Homeomorph.subRight z))
  have hintw : ∀ z : ℂ, ∫ w, moll r (w - z) = 1 := fun z => by
    rw [integral_sub_right_eq_self (fun w => moll r w) z, integral_moll hr]
  have hKint : Integrable (Function.uncurry K) (volume.prod volume) := by
    rw [integrable_prod_iff hmeas]
    refine ⟨Eventually.of_forall fun z => ?_, ?_⟩
    · show Integrable (fun w => f z * g w * moll r (w - z))
      refine ((hmollw z).const_mul (|f z| * C)).mono' ?_ (Eventually.of_forall fun w => ?_)
      · exact (continuous_const.mul hg).mul
          ((continuous_moll r).comp (continuous_id.sub continuous_const)) |>.aestronglyMeasurable
      · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (moll_nonneg _)]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by rw [← Real.norm_eq_abs]; exact hC w) (abs_nonneg _))
          (moll_nonneg _)
    · refine (hf.norm.const_mul C).mono' hmeas.norm.integral_prod_right'
        (Eventually.of_forall fun z => ?_)
      show ‖∫ w, ‖f z * g w * moll r (w - z)‖‖ ≤ C * ‖f z‖
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      calc ∫ w, ‖f z * g w * moll r (w - z)‖ ≤ ∫ w, ‖f z‖ * C * moll r (w - z) := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
              ((hmollw z).const_mul _) (Eventually.of_forall fun w => ?_)
            show ‖f z * g w * moll r (w - z)‖ ≤ ‖f z‖ * C * moll r (w - z)
            rw [norm_mul, norm_mul, Real.norm_of_nonneg (moll_nonneg _)]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hC w) (norm_nonneg _))
              (moll_nonneg _)
        _ = C * ‖f z‖ := by rw [integral_const_mul, hintw, mul_one, mul_comm]
  -- rewrite both sides as iterated integrals of `K`
  have hL : ∀ z, f z * ∫ y, g (z + y) * moll r y = ∫ w, K z w := by
    intro z
    have := integral_add_left_eq_self (fun w => g w * moll r (w - z)) z
    simp only [add_sub_cancel_left] at this
    rw [this, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [hK]; ring
  have hR : ∀ z, (∫ y, f (z + y) * moll r y) * g z = ∫ w, K w z := by
    intro z
    have := integral_add_left_eq_self (fun w => f w * moll r (w - z)) z
    simp only [add_sub_cancel_left] at this
    rw [this, ← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [hK]
    rw [show z - w = -(w - z) by ring, moll_neg hr]
    ring
  simp_rw [hL, hR]
  exact integral_integral_swap hKint

/-! ### Nonnegativity of the distributional Laplacian -/

lemma mollify_eq_conv {f : ℂ → ℝ} {r : ℝ} (hr : 0 < r) :
    (fun z => ∫ y, f (z + y) * moll r y) =
      moll r ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f := by
  funext z
  rw [convolution_lsmul, ← integral_neg_eq_self]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [smul_eq_mul]
  rw [moll_neg hr, ← sub_eq_add_neg, mul_comm]

/-- **Subharmonic functions have nonnegative distributional Laplacian.** -/
theorem integral_mul_laplacian_nonneg {u : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hu : SubharmonicOn (fun z => (u z : EReal)) U) {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) (hφ0 : ∀ z, 0 ≤ φ z) :
    0 ≤ ∫ z, u z * Δ φ z := by
  obtain ⟨η, hη, hηU⟩ := hφc.isCompact.exists_cthickening_subset_open hU hφU
  set K' := cthickening η (tsupport φ) with hK'
  have hK'c : IsCompact K' := hφc.isCompact.cthickening
  set v := K'.indicator u with hv
  have hvint : Integrable v :=
    (integrableOn_of_subharmonic hU hu hK'c hηU).integrable_indicator
      isClosed_cthickening.measurableSet
  have hc : Continuous φ := hφ.continuous
  have hΔc := continuous_laplacian hφ
  have hΔ0 : ∀ z, z ∉ tsupport φ → Δ φ z = 0 := fun z hz => laplacian_eq_zero_of_notMem hφ hz
  have hΔs : HasCompactSupport (Δ φ) :=
    HasCompactSupport.intro hφc.isCompact fun z hz => hΔ0 z hz
  obtain ⟨CΔ, hCΔ⟩ := hΔs.exists_bound_of_continuous hΔc
  -- `∫ v Δφ = ∫ u Δφ`
  have hvu : ∫ z, v z * Δ φ z = ∫ z, u z * Δ φ z := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ tsupport φ
    · simp only [hv, indicator_of_mem (self_subset_cthickening _ hz)]
    · simp only [hΔ0 z hz, mul_zero]
  set I := ∫ z, u z * Δ φ z
  set N := ∫ z, |v z| with hN
  have hN0 : 0 ≤ N := integral_nonneg fun _ => abs_nonneg _
  -- the main estimate
  have hmain : ∀ ε > 0, -(4 * ε * N) ≤ I := by
    intro ε hε
    obtain ⟨δ, hδ, hTay⟩ := taylor_moll hφ hφc hε
    set r := min (δ / 2) (η / 2) with hr_def
    have hr : 0 < r := lt_min (by positivity) (by positivity)
    have hrδ : r < δ := (min_le_left _ _).trans_lt (by linarith)
    have hrη : r < η := (min_le_right _ _).trans_lt (by linarith)
    set Mφ : ℂ → ℝ := fun z => ∫ y, φ (z + y) * moll r y with hMφ
    set Mv : ℂ → ℝ := fun z => ∫ y, v (z + y) * moll r y with hMv
    have hMφc : Continuous Mφ := by
      rw [hMφ, mollify_eq_conv hr]
      exact (hasCompactSupport_moll hr).continuous_convolution_left _ (continuous_moll r)
        hc.locallyIntegrable
    have hMφs : HasCompactSupport Mφ := by
      rw [hMφ, mollify_eq_conv hr]
      exact (hasCompactSupport_moll hr).convolution _ hφc
    have hMvc : Continuous Mv := by
      rw [hMv, mollify_eq_conv hr]
      exact (hasCompactSupport_moll hr).continuous_convolution_left _ (continuous_moll r)
        hvint.locallyIntegrable
    obtain ⟨CM, hCM⟩ := hMφs.exists_bound_of_continuous hMφc
    -- symmetry
    have hsym := integral_mul_mollify_symm hvint hc hφc hr
    -- `∫ (M v - v) φ ≥ 0`
    have hpos : ∫ z, v z * φ z ≤ ∫ z, Mv z * φ z := by
      refine integral_mono ?_ ?_ fun z => ?_
      · obtain ⟨Cφ, hCφ⟩ := hφc.exists_bound_of_continuous hc
        exact (hvint.bdd_mul (c := Cφ) hc.aestronglyMeasurable
          (Eventually.of_forall hCφ)).congr (Eventually.of_forall fun z => mul_comm _ _)
      · exact (hMvc.mul hc).integrable_of_hasCompactSupport hφc.mul_left
      · by_cases hz : z ∈ tsupport φ
        · refine mul_le_mul_of_nonneg_right ?_ (hφ0 z)
          have hball : closedBall z r ⊆ K' := fun w hw =>
            mem_cthickening_of_dist_le w z η (tsupport φ) hz
              ((mem_closedBall.1 hw).trans hrη.le)
          have hle := le_integral_moll hU hu hr (hball.trans hηU)
            ((integrableOn_of_subharmonic hU hu hK'c hηU).mono_set hball)
            (Eventually.of_forall fun w => EReal.coe_ne_bot _)
          simp only [EReal.toReal_coe] at hle
          have hv1 : v z = u z := by
            simp only [hv, indicator_of_mem (self_subset_cthickening _ hz)]
          have hv2 : Mv z = ∫ y, u (z + y) * moll r y := by
            refine integral_congr_ae (Eventually.of_forall fun y => ?_)
            by_cases hy : ‖y‖ ≤ r
            · simp only [hv, indicator_of_mem (hball (add_mem_closedBall_of_norm_le hy))]
            · simp only [moll_eq_zero hr (not_le.1 hy).le, mul_zero]
          rw [hv1, hv2]
          exact EReal.coe_le_coe_iff.1 hle
        · simp [image_eq_zero_of_notMem_tsupport hz]
    -- the Taylor expansion
    set err : ℂ → ℝ := fun z => Mφ z - φ z - Δ φ z / 4 * mollQ r with herr
    have herrb : ∀ z, |err z| ≤ ε * mollQ r := fun z => hTay r hr hrδ z
    have herrc : Continuous err :=
      (hMφc.sub hc).sub ((hΔc.div_const 4).mul continuous_const)
    have hint1 : Integrable (fun z => v z * Mφ z) :=
      (hvint.bdd_mul (c := CM) hMφc.aestronglyMeasurable
        (Eventually.of_forall hCM)).congr (Eventually.of_forall fun z => mul_comm _ _)
    have hint2 : Integrable (fun z => v z * φ z) := by
      obtain ⟨Cφ, hCφ⟩ := hφc.exists_bound_of_continuous hc
      exact (hvint.bdd_mul (c := Cφ) hc.aestronglyMeasurable
        (Eventually.of_forall hCφ)).congr (Eventually.of_forall fun z => mul_comm _ _)
    have hint3 : Integrable (fun z => v z * Δ φ z) :=
      (hvint.bdd_mul (c := CΔ) hΔc.aestronglyMeasurable
        (Eventually.of_forall hCΔ)).congr (Eventually.of_forall fun z => mul_comm _ _)
    have hint4 : Integrable (fun z => v z * err z) :=
      (hvint.bdd_mul (c := ε * mollQ r) herrc.aestronglyMeasurable
        (Eventually.of_forall fun z => by rw [Real.norm_eq_abs]; exact herrb z)).congr
        (Eventually.of_forall fun z => mul_comm _ _)
    have hsplit : ∫ z, v z * Mφ z - ∫ z, v z * φ z =
        mollQ r / 4 * ∫ z, v z * Δ φ z + ∫ z, v z * err z := by
      rw [← integral_sub hint1 hint2, ← integral_const_mul, ← integral_add (hint3.const_mul _)
        hint4]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [herr]
      ring
    have herrI : |∫ z, v z * err z| ≤ ε * mollQ r * N := by
      rw [← Real.norm_eq_abs]
      calc ‖∫ z, v z * err z‖ ≤ ∫ z, ε * mollQ r * |v z| := by
            refine norm_integral_le_of_norm_le (hvint.abs.const_mul _)
              (Eventually.of_forall fun z => ?_)
            rw [Real.norm_eq_abs, abs_mul, mul_comm]
            exact mul_le_mul_of_nonneg_right (herrb z) (abs_nonneg _)
        _ = ε * mollQ r * N := by rw [integral_const_mul]
    have hQ := mollQ_pos hr
    have hge : 0 ≤ ∫ z, v z * Mφ z - ∫ z, v z * φ z := by
      rw [show ∫ z, v z * Mφ z = ∫ z, Mv z * φ z from hsym]
      linarith
    rw [hsplit, hvu] at hge
    have h1 : ∫ z, v z * err z ≤ ε * mollQ r * N := (abs_le.1 herrI).2
    have h3 : mollQ r * (-(4 * ε * N)) ≤ mollQ r * I := by linarith
    exact le_of_mul_le_mul_left h3 hQ
  -- conclude
  have hlim : Tendsto (fun n : ℕ => -(4 * (1 / ((n : ℝ) + 1)) * N)) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (4 : ℝ)).mul_const N
    simpa using this.neg
  exact le_of_tendsto' hlim fun n => hmain _ (by positivity)

end Distr

end DF
