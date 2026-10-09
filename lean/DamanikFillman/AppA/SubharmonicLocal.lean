/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Appendix A.3: local properties of subharmonic functions

* `DF.Distr.measurable_indicator_of_usc` — upper semicontinuous functions on open sets are
  measurable (after extension by zero);
* `DF.Distr.trunc_le_integral_moll` — the sub-mean value inequality against the radial
  mollifier, for the truncations `max F (-n)` of a subharmonic `F`;
* `DF.Distr.le_integral_moll` — the same for `F` itself, assuming local integrability:
  `F(z) ≤ ∫ F(z + y) moll_R(y) dy`;
* `DF.Distr.locallyIntegrableOn_of_subharmonic` — real-valued subharmonic functions are locally
  integrable.
-/
import DamanikFillman.AppA.Mollifier
import DamanikFillman.AppA.Subharmonic

noncomputable section

open Real Complex Metric Set Filter Topology MeasureTheory InnerProductSpace

namespace DF

namespace Distr

/-! ### Measurability -/

/-- Upper semicontinuous functions on open sets are measurable (after extension by zero). -/
lemma measurable_indicator_of_usc {g : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hg : UpperSemicontinuousOn g U) : Measurable (U.indicator g) := by
  refine measurable_of_Iio fun a => ?_
  have e : U.indicator g ⁻¹' Iio a = {z | z ∈ U ∧ g z < a} ∪ (Uᶜ ∩ {_z | (0 : ℝ) < a}) := by
    ext z
    by_cases hz : z ∈ U <;> simp [hz, indicator_of_mem, indicator_of_notMem]
  rw [e]
  refine MeasurableSet.union (IsOpen.measurableSet ?_)
    (hU.isClosed_compl.measurableSet.inter (MeasurableSet.const _))
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨hzU, hza⟩
  have h1 := hg z hzU a hza
  rw [hU.nhdsWithin_eq hzU] at h1
  filter_upwards [h1, hU.mem_nhds hzU] with w hw hwU
  exact ⟨hwU, hw⟩

/-- Truncations of upper semicontinuous functions are upper semicontinuous. -/
lemma usc_truncBelow {F : ℂ → EReal} {U : Set ℂ} (hne : ∀ z ∈ U, F z ≠ ⊤)
    (husc : UpperSemicontinuousOn F U) (n : ℕ) :
    UpperSemicontinuousOn (fun z => truncBelow n (F z)) U := by
  intro x hx y hy
  have hn : -(n : ℝ) ≤ truncBelow n (F x) := neg_natCast_le_truncBelow n (F x)
  have hy' : -(n : ℝ) < y := lt_of_le_of_lt hn hy
  have hFx : F x < (y : EReal) :=
    lt_of_le_of_lt (le_truncBelow (hne x hx)) (EReal.coe_lt_coe_iff.2 hy)
  filter_upwards [husc x hx y hFx, self_mem_nhdsWithin] with z hz hzU
  rw [← EReal.coe_lt_coe_iff, truncBelow_eq_coe_max (hne z hzU)]
  refine max_lt hz ?_
  rw [neg_natCast_ereal]
  exact EReal.coe_lt_coe_iff.2 hy'

/-! ### Polar coordinates for bounded measurable functions -/

/-- Polar coordinates for bounded measurable functions with bounded support: integrability of the
radial function and the change of variables formula. -/
theorem polar_of_bdd {f : ℂ → ℝ} (hf : Measurable f) {C R : ℝ} (hC : ∀ z, |f z| ≤ C)
    (hfs : ∀ z, R < ‖z‖ → f z = 0) :
    IntegrableOn (fun ρ : ℝ => ∫ θ in Ioo (-π) π,
        ρ * f (ρ * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I))) (Ioi 0) ∧
      ∫ z, f z = ∫ ρ in Ioi (0 : ℝ), ∫ θ in Ioo (-π) π,
        ρ * f (ρ * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I)) := by
  set R' := max R 0 with hR'
  have hR0 : 0 ≤ R' := le_max_right _ _
  have hfs' : ∀ z, R' < ‖z‖ → f z = 0 := fun z hz => hfs z (lt_of_le_of_lt (le_max_left _ _) hz)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
  set G : ℝ × ℝ → ℝ := fun p => p.1 * f (p.1 * ((Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * I))
    with hG
  have hGm : Measurable G := by
    rw [hG]
    refine measurable_fst.mul (hf.comp ?_)
    exact Continuous.measurable (by fun_prop)
  have hGb : ∀ p, ‖G p‖ ≤ R' * C := by
    intro p
    simp only [hG, norm_mul]
    by_cases hp : ‖p.1‖ ≤ R'
    · exact mul_le_mul hp (hC _) (norm_nonneg _) hR0
    · rw [hfs' _ (by rw [norm_ofReal_mul_e, ← Real.norm_eq_abs]; exact lt_of_not_ge hp),
        norm_zero, mul_zero]
      exact mul_nonneg hR0 hC0
  have hG0 : ∀ p : ℝ × ℝ, R' < p.1 → G p = 0 := by
    intro p hp
    simp only [hG]
    rw [hfs' _ (by rw [norm_ofReal_mul_e, abs_of_pos (hR0.trans_lt hp)]; exact hp), mul_zero]
  have hGint : IntegrableOn G (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) := by
    have h1 : IntegrableOn G (Ioc (0 : ℝ) R' ×ˢ Ioo (-π) π) := by
      refine IntegrableOn.of_bound ?_ hGm.aestronglyMeasurable (R' * C)
        (Eventually.of_forall hGb)
      rw [Measure.volume_eq_prod, Measure.prod_prod]
      simp [ENNReal.mul_lt_top]
    refine h1.of_forall_sdiff_eq_zero (measurableSet_Ioi.prod measurableSet_Ioo) ?_
    rintro ⟨r, θ⟩ ⟨⟨hr, hθ⟩, hn⟩
    apply hG0
    have hr' : (0 : ℝ) < r := hr
    by_contra hle
    push Not at hle
    exact hn ⟨⟨hr', hle⟩, hθ⟩
  have hpol : ∫ z, f z = ∫ p in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, G p := by
    rw [← Complex.integral_comp_polarCoord_symm, polarCoord_target]
    refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun p _ => ?_
    simp only [Complex.polarCoord_symm_apply, smul_eq_mul, hG]
  refine ⟨?_, ?_⟩
  · have h2 : Integrable G ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioo (-π) π))) := by
      rw [Measure.prod_restrict]
      exact hGint
    exact h2.integral_prod_left
  · rw [hpol]
    exact setIntegral_prod (μ := volume) (ν := volume) G hGint

/-! ### The sub-mean value inequality against the mollifier -/

lemma mollRad_nonneg (R ρ : ℝ) : 0 ≤ mollRad R ρ :=
  mul_nonneg (inv_nonneg.2 (mul_nonneg bumpMass_pos.le (sq_nonneg R)))
    (Real.smoothTransition.nonneg _)

lemma add_mem_closedBall_of_norm_le {z y : ℂ} {R : ℝ} (hy : ‖y‖ ≤ R) : z + y ∈ closedBall z R := by
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left]
  exact hy

/-- The sub-mean value inequality for the truncations of a subharmonic function, against the
mollifier. -/
theorem trunc_le_integral_moll {F : ℂ → EReal} {U : Set ℂ} (hU : IsOpen U)
    (hF : SubharmonicOn F U) {z : ℂ} {R : ℝ} (hR : 0 < R) (hzR : closedBall z R ⊆ U) (n : ℕ) :
    truncBelow n (F z) ≤
      ∫ y, U.indicator (fun w => truncBelow n (F w)) (z + y) * moll R y := by
  set T := U.indicator (fun w => truncBelow n (F w)) with hT
  have hTm : Measurable T :=
    measurable_indicator_of_usc hU (usc_truncBelow hF.ne_top hF.usc n)
  obtain ⟨M, hM⟩ := exists_bound_of_usc hF.ne_top hF.usc (isCompact_closedBall z R) hzR
  set B := |M| + n with hB
  have hTb : ∀ y, ‖y‖ ≤ R → |T (z + y)| ≤ B := by
    intro y hy
    have hmem := add_mem_closedBall_of_norm_le (z := z) hy
    rw [hT, indicator_of_mem (hzR hmem)]
    have h1 := neg_natCast_le_truncBelow n (F (z + y))
    have h2 : truncBelow n (F (z + y)) ≤ truncBelow n (M : EReal) :=
      truncBelow_mono (EReal.coe_ne_top _) (hM _ hmem)
    rw [truncBelow_coe] at h2
    rw [abs_le]
    constructor
    · have := abs_nonneg M; linarith
    · refine h2.trans (max_le ?_ ?_)
      · linarith [le_abs_self M, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      · have := abs_nonneg M; have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
  set c := (bumpMass * R ^ 2)⁻¹ with hc
  have hc0 : 0 ≤ c := inv_nonneg.2 (mul_nonneg bumpMass_pos.le (sq_nonneg R))
  -- the integrand
  set f : ℂ → ℝ := fun y => T (z + y) * moll R y with hf
  have hfm : Measurable f := (hTm.comp (measurable_const_add z)).mul (continuous_moll R).measurable
  have hfb : ∀ y, |f y| ≤ B * c := by
    intro y
    simp only [hf, abs_mul, abs_of_nonneg (moll_nonneg y)]
    by_cases hy : ‖y‖ ≤ R
    · exact mul_le_mul (hTb y hy) (moll_le y) (moll_nonneg y)
        ((abs_nonneg _).trans (hTb y hy))
    · rw [moll_eq_zero hR (not_le.1 hy).le, mul_zero]
      exact mul_nonneg ((abs_nonneg _).trans (hTb 0 (by simp [hR.le]))) hc0
  have hfs : ∀ y, R < ‖y‖ → f y = 0 := fun y hy => by
    simp only [hf]; rw [moll_eq_zero hR hy.le, mul_zero]
  obtain ⟨hI1, hP1⟩ := polar_of_bdd hfm hfb hfs
  -- the comparison integrand
  set t := truncBelow n (F z)
  set g : ℂ → ℝ := fun y => t * moll R y with hg
  have hgc : Continuous g := continuous_const.mul (continuous_moll R)
  have hgs : ∀ y, R < ‖y‖ → g y = 0 := fun y hy => by
    simp only [hg]; rw [moll_eq_zero hR hy.le, mul_zero]
  obtain ⟨hI2, hP2⟩ := polar_of_bdd hgc.measurable (C := |t| * c) (fun y => by
      simp only [hg, abs_mul, abs_of_nonneg (moll_nonneg y)]
      exact mul_le_mul_of_nonneg_left (moll_le y) (abs_nonneg _)) hgs
  have hgint : ∫ y, g y = t := by
    simp only [hg]; rw [integral_const_mul, integral_moll hR, mul_one]
  rw [← hgint, hP1, hP2]
  refine setIntegral_mono_on hI2 hI1 measurableSet_Ioi fun ρ hρ => ?_
  have hρ0 : (0 : ℝ) < ρ := hρ
  have hk : ∀ θ : ℝ, moll R (ρ * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I)) = mollRad R ρ :=
    fun θ => by rw [moll_eq_mollRad hR, norm_ofReal_mul_e, abs_of_pos hρ0]
  simp only [hf, hg, hk]
  by_cases hρR : ρ ≤ R
  · have hTθ : ∀ θ : ℝ, T (z + ρ * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I)) =
        truncBelow n (F (circleMap z ρ θ)) := by
      intro θ
      have hmem : z + ρ * ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I) ∈ closedBall z R :=
        add_mem_closedBall_of_norm_le (by rw [norm_ofReal_mul_e, abs_of_pos hρ0]; exact hρR)
      rw [hT, indicator_of_mem (hzR hmem), ofReal_mul_e_eq_circleMap]
      simp only [circleMap, zero_add]
    simp only [hTθ]
    have e1 : (fun θ => ρ * (truncBelow n (F (circleMap z ρ θ)) * mollRad R ρ)) =
        fun θ => (ρ * mollRad R ρ) * truncBelow n (F (circleMap z ρ θ)) := by
      funext θ; ring
    rw [e1, integral_const_mul, integral_Ioo_circleMap (fun w => truncBelow n (F w)),
      setIntegral_const, Real.volume_real_Ioo_of_le (show -π ≤ π by linarith [pi_pos]),
      smul_eq_mul]
    have hsub := hF.truncBelow_le_circleAverage hρ0
      ((closedBall_subset_closedBall hρR).trans hzR) n
    have hρk : 0 ≤ ρ * mollRad R ρ := mul_nonneg hρ0.le (mollRad_nonneg R ρ)
    have := mul_le_mul_of_nonneg_left hsub (mul_nonneg hρk (by positivity : (0 : ℝ) ≤ 2 * π))
    nlinarith [this]
  · have hk0 : mollRad R ρ = 0 := by
      have := moll_eq_zero hR (z := (ρ : ℂ)) (by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0]; exact (not_le.1 hρR).le)
      rwa [moll_eq_mollRad hR, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ0] at this
    simp [hk0]

/-- The sub-mean value inequality against the mollifier, for locally integrable subharmonic
functions which are a.e. finite. -/
theorem le_integral_moll {F : ℂ → EReal} {U : Set ℂ} (hU : IsOpen U) (hF : SubharmonicOn F U)
    {z : ℂ} {R : ℝ} (hR : 0 < R) (hzR : closedBall z R ⊆ U)
    (hint : IntegrableOn (fun w => (F w).toReal) (closedBall z R))
    (hfin : ∀ᵐ w, F w ≠ ⊥) :
    F z ≤ ((∫ y, (F (z + y)).toReal * moll R y : ℝ) : EReal) := by
  set c := (bumpMass * R ^ 2)⁻¹ with hc
  have hFz : F z ≠ ⊤ := hF.ne_top z (hzR (mem_closedBall_self hR.le))
  -- dominated convergence for the truncations
  have hlim : Tendsto (fun n : ℕ => ∫ y, U.indicator (fun w => truncBelow n (F w)) (z + y) *
      moll R y) atTop (𝓝 (∫ y, (F (z + y)).toReal * moll R y)) := by
    refine tendsto_integral_of_dominated_convergence
      (fun y => c * (closedBall z R).indicator (fun w => |(F w).toReal|) (z + y))
      (fun n => ?_) ?_ (fun n => ?_) ?_
    · exact (((measurable_indicator_of_usc hU (usc_truncBelow hF.ne_top hF.usc n)).comp
        (measurable_const_add z)).mul (continuous_moll R).measurable).aestronglyMeasurable
    · have := ((IntegrableOn.integrable_indicator (f := fun w => |(F w).toReal|) hint.abs
        measurableSet_closedBall).comp_add_left z).const_mul c
      exact this
    · have hfin' : ∀ᵐ y : ℂ, F (z + y) ≠ ⊥ :=
        (measurePreserving_add_left volume z).quasiMeasurePreserving.ae hfin
      filter_upwards [hfin'] with y hy
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (moll_nonneg y)]
      by_cases hyR : ‖y‖ ≤ R
      · have hmem := add_mem_closedBall_of_norm_le (z := z) hyR
        have hne := hF.ne_top _ (hzR hmem)
        rw [indicator_of_mem (hzR hmem), indicator_of_mem hmem, mul_comm c]
        refine mul_le_mul ?_ (moll_le y) (moll_nonneg y) (abs_nonneg _)
        -- `|max x (-n)| ≤ |x|` for finite `x`
        obtain ⟨a, ha⟩ : ∃ a : ℝ, F (z + y) = a := ⟨_, (EReal.coe_toReal hne hy).symm⟩
        rw [ha, truncBelow_coe, EReal.toReal_coe]
        rcases le_total a (-(n : ℝ)) with h | h
        · rw [max_eq_right h, abs_neg, abs_of_nonneg (Nat.cast_nonneg n),
            abs_of_nonpos (h.trans (neg_nonpos.2 (Nat.cast_nonneg n)))]
          linarith
        · rw [max_eq_left h]
      · rw [moll_eq_zero hR (not_le.1 hyR).le, mul_zero]
        exact mul_nonneg (inv_nonneg.2 (mul_nonneg bumpMass_pos.le (sq_nonneg R)))
          (indicator_nonneg (fun _ _ => abs_nonneg _) _)
    · have hfin' : ∀ᵐ y : ℂ, F (z + y) ≠ ⊥ :=
        (measurePreserving_add_left volume z).quasiMeasurePreserving.ae hfin
      filter_upwards [hfin'] with y hy
      by_cases hyR : ‖y‖ < R
      · have hmem : z + y ∈ closedBall z R := add_mem_closedBall_of_norm_le hyR.le
        have hne := hF.ne_top _ (hzR hmem)
        simp only [indicator_of_mem (hzR hmem)]
        obtain ⟨a, ha⟩ : ∃ a : ℝ, F (z + y) = a := ⟨_, (EReal.coe_toReal hne hy).symm⟩
        rw [ha]
        simp only [truncBelow_coe, EReal.toReal_coe]
        refine Tendsto.mul_const _ (tendsto_const_nhds.congr' ?_)
        obtain ⟨N, hN⟩ := exists_nat_ge (-a)
        filter_upwards [eventually_ge_atTop N] with n hn
        rw [max_eq_left]
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      · rw [moll_eq_zero hR (not_lt.1 hyR)]
        simp
  have hle : ∀ n : ℕ, F z ≤
      ((∫ y, U.indicator (fun w => truncBelow n (F w)) (z + y) * moll R y : ℝ) : EReal) :=
    fun n => (le_truncBelow hFz).trans
      (EReal.coe_le_coe_iff.2 (trunc_le_integral_moll hU hF hR hzR n))
  exact ge_of_tendsto' ((continuous_coe_real_ereal.tendsto _).comp hlim) hle

/-! ### Local integrability of subharmonic functions -/

lemma bump0_ge {y : ℂ} (hy : ‖y‖ ≤ 1 / 2) : Real.smoothTransition (3 / 4) ≤ bump0 y := by
  unfold bump0
  apply Real.smoothTransition.monotone
  have : ‖y‖ ^ 2 ≤ 1 / 4 := by
    have h0 := norm_nonneg y
    nlinarith
  linarith

lemma moll_ge {R : ℝ} (hR : 0 < R) {y : ℂ} (hy : ‖y‖ ≤ R / 2) :
    (bumpMass * R ^ 2)⁻¹ * Real.smoothTransition (3 / 4) ≤ moll R y := by
  unfold moll
  refine mul_le_mul_of_nonneg_left (bump0_ge ?_)
    (inv_nonneg.2 (mul_nonneg bumpMass_pos.le (sq_nonneg R)))
  rw [norm_inv_smul hR]
  rw [inv_mul_le_iff₀ hR]
  linarith

/-- Real-valued subharmonic functions are integrable on small discs. -/
theorem integrableOn_ball_of_subharmonic {u : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hu : SubharmonicOn (fun z => (u z : EReal)) U) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hcR : closedBall c R ⊆ U) : IntegrableOn u (ball c (R / 2)) := by
  obtain ⟨M0, hM0⟩ := exists_bound_of_usc hu.ne_top hu.usc (isCompact_closedBall c R) hcR
  set M := max M0 0 with hM
  have hMu : ∀ w ∈ closedBall c R, u w ≤ M := fun w hw =>
    (EReal.coe_le_coe_iff.1 (hM0 w hw)).trans (le_max_left _ _)
  have hM0' : 0 ≤ M := le_max_right _ _
  have husc : UpperSemicontinuousOn u U := upperSemicontinuousOn_coe_iff.1 hu.usc
  have hum : Measurable (U.indicator u) := measurable_indicator_of_usc hU husc
  set T : ℕ → ℂ → ℝ := fun n => U.indicator (fun w => truncBelow n (u w : EReal)) with hT
  have hTm : ∀ n, Measurable (T n) := fun n =>
    measurable_indicator_of_usc hU (usc_truncBelow hu.ne_top hu.usc n)
  have hTeq : ∀ n, ∀ w ∈ U, T n w = max (u w) (-(n : ℝ)) := fun n w hw => by
    simp only [hT, indicator_of_mem hw, truncBelow_coe]
  set m₀ := (bumpMass * R ^ 2)⁻¹ * Real.smoothTransition (3 / 4) with hm₀
  have hm₀pos : 0 < m₀ :=
    mul_pos (inv_pos.2 (mul_pos bumpMass_pos (by positivity)))
      (Real.smoothTransition.pos_of_pos (by norm_num))
  set c' := (bumpMass * R ^ 2)⁻¹ with hc'
  have hc'0 : 0 ≤ c' := inv_nonneg.2 (mul_nonneg bumpMass_pos.le (sq_nonneg R))
  -- `M - T n` is nonnegative and bounded on `closedBall c R`
  have hTle : ∀ n, ∀ w ∈ closedBall c R, T n w ≤ M := fun n w hw => by
    rw [hTeq n w (hcR hw)]
    exact max_le (hMu w hw) (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)
  have hTge : ∀ n, ∀ w ∈ closedBall c R, -(n : ℝ) ≤ T n w := fun n w hw => by
    rw [hTeq n w (hcR hw)]; exact le_max_right _ _
  -- key estimate for each truncation
  have hkey : ∀ n : ℕ, ∫ w in ball c (R / 2), (M - T n w) ≤ (M - u c) / m₀ := by
    intro n
    have hsub : max (u c) (-(n : ℝ)) ≤ ∫ y, T n (c + y) * moll R y := by
      have := trunc_le_integral_moll hU hu hR hcR n
      rwa [truncBelow_coe] at this
    -- change variables `w = c + y`
    have hcv : ∫ y, T n (c + y) * moll R y = ∫ w, T n w * moll R (w - c) := by
      rw [← integral_add_left_eq_self (fun w => T n w * moll R (w - c)) c]
      simp only [add_sub_cancel_left]
    rw [hcv] at hsub
    -- integrability of the relevant functions
    have hbd : ∀ w, |(M - T n w) * moll R (w - c)| ≤ (M + n) * c' := by
      intro w
      rw [abs_mul, abs_of_nonneg (moll_nonneg _)]
      by_cases hw : w ∈ closedBall c R
      · refine mul_le_mul ?_ (moll_le _) (moll_nonneg _) (by positivity)
        rw [abs_le]
        constructor
        · linarith [hTle n w hw]
        · linarith [hTge n w hw]
      · rw [moll_eq_zero hR (by
            rw [mem_closedBall, dist_eq_norm, not_le] at hw; exact hw.le), mul_zero]
        positivity
    have hsupp : ∀ w, w ∉ closedBall c R → (M - T n w) * moll R (w - c) = 0 := fun w hw => by
      rw [moll_eq_zero hR (by
        rw [mem_closedBall, dist_eq_norm, not_le] at hw; exact hw.le), mul_zero]
    have hmeas1 : Measurable (fun w => (M - T n w) * moll R (w - c)) :=
      (measurable_const.sub (hTm n)).mul
        ((continuous_moll R).comp (continuous_id.sub continuous_const)).measurable
    have hi1 : Integrable (fun w => (M - T n w) * moll R (w - c)) := by
      refine (integrableOn_iff_integrable_of_support_subset (s := closedBall c R)
        (fun w hw => ?_)).1 ?_
      · by_contra h; exact hw (hsupp w h)
      · exact Measure.integrableOn_of_bounded (M := (M + n) * c')
          measure_closedBall_lt_top.ne hmeas1.aestronglyMeasurable
          (Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact hbd w)
    have hmc : Integrable (fun w => moll R (w - c)) :=
      ((continuous_moll R).comp (continuous_id.sub continuous_const)).integrable_of_hasCompactSupport
        ((hasCompactSupport_moll hR).comp_homeomorph (Homeomorph.subRight c))
    have hi2 : Integrable (fun w => T n w * moll R (w - c)) := by
      have : (fun w => T n w * moll R (w - c)) =
          fun w => M * moll R (w - c) - (M - T n w) * moll R (w - c) := by
        funext w; ring
      rw [this]
      exact (hmc.const_mul M).sub hi1
    -- `∫ (M - T n) moll ≤ M - u c`
    have h1 : ∫ w, (M - T n w) * moll R (w - c) ≤ M - u c := by
      have e : ∫ w, (M - T n w) * moll R (w - c) = M - ∫ w, T n w * moll R (w - c) := by
        have : (fun w => (M - T n w) * moll R (w - c)) =
            fun w => M * moll R (w - c) - T n w * moll R (w - c) := by
          funext w; ring
        rw [this, integral_sub, integral_const_mul,
          integral_sub_right_eq_self (fun w => moll R w) c, integral_moll hR, mul_one]
        · exact hmc.const_mul M
        · exact hi2
      rw [e]
      linarith [le_max_left (u c) (-(n : ℝ))]
    -- restrict to the small ball, where `moll ≥ m₀`
    have h2 : ∫ w in ball c (R / 2), (M - T n w) * m₀ ≤ ∫ w, (M - T n w) * moll R (w - c) := by
      calc ∫ w in ball c (R / 2), (M - T n w) * m₀
          ≤ ∫ w in ball c (R / 2), (M - T n w) * moll R (w - c) := by
            refine setIntegral_mono_on ?_ hi1.integrableOn measurableSet_ball fun w hw => ?_
            · exact Measure.integrableOn_of_bounded (M := (M + n) * m₀)
                measure_ball_lt_top.ne
                ((measurable_const.sub (hTm n)).mul measurable_const).aestronglyMeasurable
                ((ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun w hw => by
                  have hw' : w ∈ closedBall c R :=
                    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)) hw
                  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hm₀pos]
                  refine mul_le_mul_of_nonneg_right ?_ hm₀pos.le
                  rw [abs_le]
                  constructor
                  · linarith [hTle n w hw']
                  · linarith [hTge n w hw']))
            · have hw' : w ∈ closedBall c R :=
                ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)) hw
              refine mul_le_mul_of_nonneg_left (moll_ge hR ?_) (by linarith [hTle n w hw'])
              rw [mem_ball, dist_eq_norm] at hw
              exact hw.le
        _ ≤ ∫ w, (M - T n w) * moll R (w - c) := by
            refine setIntegral_le_integral hi1 (Eventually.of_forall fun w => ?_)
            by_cases hw : w ∈ closedBall c R
            · exact mul_nonneg (by linarith [hTle n w hw]) (moll_nonneg _)
            · simp [hsupp w hw]
    rw [integral_mul_const] at h2
    rw [le_div_iff₀ hm₀pos]
    linarith
  -- monotone convergence
  have hlin : ∫⁻ w in ball c (R / 2), ENNReal.ofReal (M - u w) ≤
      ENNReal.ofReal ((M - u c) / m₀) := by
    have hconv := lintegral_tendsto_of_tendsto_of_monotone (μ := volume.restrict (ball c (R / 2)))
      (f := fun n w => ENNReal.ofReal (M - T n w)) (F := fun w => ENNReal.ofReal (M - u w))
      (fun n => (measurable_const.sub (hTm n)).ennreal_ofReal.aemeasurable)
      ((ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun w hw => by
        intro m k hmk
        have hwU : w ∈ U := hcR (ball_subset_closedBall.trans
          (closedBall_subset_closedBall (by linarith)) hw)
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hTeq m w hwU, hTeq k w hwU]
        have : -(k : ℝ) ≤ -(m : ℝ) := neg_le_neg (by exact_mod_cast hmk)
        linarith [max_le_max (le_refl (u w)) this]))
      ((ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun w hw => by
        have hwU : w ∈ U := hcR (ball_subset_closedBall.trans
          (closedBall_subset_closedBall (by linarith)) hw)
        refine (ENNReal.continuous_ofReal.tendsto _).comp (tendsto_const_nhds.congr' ?_)
        obtain ⟨N, hN⟩ := exists_nat_ge (-u w)
        filter_upwards [eventually_ge_atTop N] with n hn
        rw [hTeq n w hwU, max_eq_left]
        have : (N : ℝ) ≤ n := by exact_mod_cast hn
        linarith))
    refine le_of_tendsto' hconv fun n => ?_
    beta_reduce
    rw [← ofReal_integral_eq_lintegral_ofReal]
    · exact ENNReal.ofReal_le_ofReal (hkey n)
    · exact Measure.integrableOn_of_bounded (M := M + n) measure_ball_lt_top.ne
        (measurable_const.sub (hTm n)).aestronglyMeasurable
        ((ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun w hw => by
          have hw' : w ∈ closedBall c R :=
            ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)) hw
          rw [Real.norm_eq_abs, abs_le]
          constructor
          · linarith [hTle n w hw']
          · linarith [hTge n w hw']))
    · exact (ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun w hw => by
        have hw' : w ∈ closedBall c R :=
          ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)) hw
        simp only [Pi.zero_apply]
        linarith [hTle n w hw'])
  -- conclude
  have hmeas : AEStronglyMeasurable u (volume.restrict (ball c (R / 2))) := by
    refine hum.aestronglyMeasurable.congr ?_
    refine (ae_restrict_iff' measurableSet_ball).2 (Eventually.of_forall fun w hw => ?_)
    exact indicator_of_mem (hcR (ball_subset_closedBall.trans
      (closedBall_subset_closedBall (by linarith)) hw)) u
  have hfin : IntegrableOn (fun w => M - u w) (ball c (R / 2)) := by
    refine ⟨aestronglyMeasurable_const.sub hmeas, ?_⟩
    rw [HasFiniteIntegral]
    calc ∫⁻ w in ball c (R / 2), ‖M - u w‖ₑ
        = ∫⁻ w in ball c (R / 2), ENNReal.ofReal (M - u w) := by
          refine setLIntegral_congr_fun measurableSet_ball fun w hw => ?_
          have hw' : w ∈ closedBall c R :=
            ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith)) hw
          exact Real.enorm_of_nonneg (by linarith [hMu w hw'])
      _ ≤ ENNReal.ofReal ((M - u c) / m₀) := hlin
      _ < ⊤ := ENNReal.ofReal_lt_top
  have : u = fun w => M - (M - u w) := by funext w; ring
  rw [this]
  exact (integrableOn_const measure_ball_lt_top.ne).sub hfin

/-- **Real-valued subharmonic functions are locally integrable.** -/
theorem locallyIntegrableOn_of_subharmonic {u : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hu : SubharmonicOn (fun z => (u z : EReal)) U) : LocallyIntegrableOn u U := by
  intro x hx
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU x hx
  have hcR : closedBall x (ε / 2) ⊆ U := (closedBall_subset_ball (by linarith)).trans hεU
  exact ⟨ball x (ε / 2 / 2), mem_nhdsWithin_of_mem_nhds (ball_mem_nhds x (by positivity)),
    integrableOn_ball_of_subharmonic hU hu (by positivity) hcR⟩

theorem integrableOn_of_subharmonic {u : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hu : SubharmonicOn (fun z => (u z : EReal)) U) {K : Set ℂ} (hK : IsCompact K)
    (hKU : K ⊆ U) : IntegrableOn u K :=
  (locallyIntegrableOn_of_subharmonic hU hu).integrableOn_compact_subset hKU hK

end Distr

end DF
