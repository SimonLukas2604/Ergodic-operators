/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Appendix A.3: bounds on the Riesz decomposition (Theorem A.3.4)

`DF.rieszMeasureBoundStatement_holds`: for a subharmonic `u` on the annulus `A_ρ` with
`|u| ≤ M`, and a Riesz decomposition `u = -Φ_μ + h` on `A_{ρ/2}`, the total mass of `μ` and the
supremum of `|h|` on `A_{ρ/3}` are bounded by `C M`, with `C` depending only on `ρ`.

Proof.
* *Mass*: on `A_{ρ/2}` the measure `μ` coincides with the Riesz measure `ν` of `u` on `A_ρ`
  (both represent `(2π)⁻¹ Δu`, `measure_eq_of_integral_eq`); with a fixed cutoff `φ` equal to `1`
  on `A_{ρ/2}` and supported in `A_ρ`,
  `μ(ℂ) = ν(A_{ρ/2}) ≤ ∫ φ dν = (2π)⁻¹ ∫ u Δφ ≤ (2π)⁻¹ ‖Δφ‖₁ M`.
* *Harmonic part*: by the mean value property `h(z) = ∫ (u + Φ_μ)(z + y) moll_r(y) dy`, and the
  mollified logarithmic kernel is bounded uniformly (`abs_integral_log_mul_le`), whence
  `|h(z)| ≤ M + C' μ(ℂ)`.
-/
import DamanikFillman.AppA.RieszRepresentation

noncomputable section

open Real Complex Metric Set Filter Topology MeasureTheory Laplacian InnerProductSpace

namespace DF

namespace Distr

/-! ### Representations and the distributional Laplacian -/

/-- From `u = -Φ_μ + h` at a point, `Φ_μ` is finite there and `u + Φ_μ = h`. -/
lemma add_toReal_logPotential_of_rep {μ : Measure ℂ} {u h : ℂ → ℝ} {z : ℂ}
    (hz : (u z : EReal) = -logPotential μ z + (h z : EReal)) :
    u z + (logPotential μ z).toReal = h z := by
  have htop : logPotential μ z ≠ ⊤ := by
    intro ht
    rw [ht, EReal.neg_top, EReal.bot_add] at hz
    exact EReal.coe_ne_bot _ hz
  obtain ⟨q, hq⟩ : ∃ q : ℝ, logPotential μ z = q :=
    ⟨_, (EReal.coe_toReal htop (logPotential_ne_bot μ z)).symm⟩
  rw [hq, ← EReal.coe_neg, ← EReal.coe_add, EReal.coe_eq_coe_iff] at hz
  rw [hq, EReal.toReal_coe, hz]
  ring

/-- A Riesz decomposition determines the distributional Laplacian: `∫ u Δψ = 2π ∫ ψ dμ`. -/
theorem integral_mul_laplacian_of_rep {V : Set ℂ} (hV : IsOpen V) {μ : Measure ℂ}
    [IsFiniteMeasure μ] {S : ℝ} (hμS : μ (closedBall 0 S)ᶜ = 0) {u h : ℂ → ℝ}
    (hh : HarmonicOnNhd h V)
    (hrep : ∀ z ∈ V, (u z : EReal) = -logPotential μ z + (h z : EReal)) {ψ : ℂ → ℝ}
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) (hψV : tsupport ψ ⊆ V)
    (hu : IntegrableOn u (tsupport ψ)) :
    ∫ z, u z * Δ ψ z = 2 * π * ∫ z, ψ z ∂μ := by
  obtain ⟨R, -, hR⟩ := exists_support_subset_closedBall hψc
  have hi1 : Integrable (fun z => u z * Δ ψ z) :=
    integrable_u_laplacian hψc.isCompact hu hψ subset_rfl
  have hi2 : Integrable (fun z => (logPotential μ z).toReal * Δ ψ z) :=
    integrable_u_laplacian (isCompact_closedBall 0 R) (integrableOn_logPotential hμS R) hψ hR
  have hharm : ∫ z, h z * Δ ψ z = 0 := integral_harmonic_mul_laplacian hV hh hψ hψc hψV
  have e : ∫ z, h z * Δ ψ z =
      (∫ z, u z * Δ ψ z) + ∫ z, (logPotential μ z).toReal * Δ ψ z := by
    rw [← integral_add hi1 hi2]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ V
    · simp only [← add_toReal_logPotential_of_rep (hrep z hz)]; ring
    · simp only [laplacian_eq_zero_of_notMem hψ fun h' => hz (hψV h'), mul_zero, add_zero]
  rw [hharm, integral_logPotential_mul_laplacian hμS hψ hψc] at e
  linarith

/-! ### Mollified logarithmic potentials -/

/-- Fubini for `∫ Φ_μ g`. -/
theorem integral_logPotential_mul {μ : Measure ℂ} [IsFiniteMeasure μ] {S R M : ℝ}
    (hμS : μ (closedBall 0 S)ᶜ = 0) {g : ℂ → ℝ} (hg : Measurable g) (hgM : ∀ z, ‖g z‖ ≤ M)
    (hgR : ∀ z, R < ‖z‖ → g z = 0) :
    ∫ z, (logPotential μ z).toReal * g z = -∫ w, (∫ z, Real.log ‖z - w‖ * g z) ∂μ := by
  have hI := integrable_prod_log hμS hg hgM hgR
  have hμ := integrable_norm_of_bounded hμS
  have hswap := integral_integral_swap (f := fun w z => Real.log ‖z - w‖ * g z) hI
  have hae : ∀ᵐ z : ℂ ∂volume, (logPotential μ z).toReal * g z =
      -∫ w, Real.log ‖z - w‖ * g z ∂μ := by
    filter_upwards [ae_measure_singleton_eq_zero μ, hI.prod_left_ae] with z hz hzi
    by_cases h0 : g z = 0
    · simp [h0]
    · have hint : Integrable (fun w => Real.log ‖z - w‖) μ := by
        refine (hzi.mul_const (g z)⁻¹).congr (Eventually.of_forall fun w => ?_)
        field_simp
      rw [toReal_logPotential_eq hμ hz hint, integral_mul_const]
      ring
  rw [integral_congr_ae hae, integral_neg, ← hswap]

/-- A uniform bound for the logarithmic kernel integrated against `g`. -/
lemma abs_integral_log_mul_le {S R M : ℝ} {g : ℂ → ℝ} (hgM : ∀ z, ‖g z‖ ≤ M)
    (hgR : ∀ z, R < ‖z‖ → g z = 0) {w : ℂ} (hw : ‖w‖ ≤ S) :
    |∫ z, Real.log ‖z - w‖ * g z| ≤
      M * ∫ z, (ball (0 : ℂ) (R + S + 1)).indicator (fun y => ‖Real.log ‖y‖‖) z := by
  rw [← Real.norm_eq_abs]
  calc ‖∫ z, Real.log ‖z - w‖ * g z‖
      ≤ ∫ z, M * (ball (0 : ℂ) (R + S + 1)).indicator (fun y => ‖Real.log ‖y‖‖) (z - w) :=
        norm_integral_le_of_norm_le ((integrable_indicator_log (R + S + 1) w).const_mul M)
          (Eventually.of_forall fun z => norm_log_mul_le hgM hgR hw z)
    _ = M * ∫ z, (ball (0 : ℂ) (R + S + 1)).indicator (fun y => ‖Real.log ‖y‖‖) z := by
        rw [integral_const_mul, integral_sub_right_eq_self (μ := volume)
          (fun z => (ball (0 : ℂ) (R + S + 1)).indicator (fun y => ‖Real.log ‖y‖‖) z) w]

theorem abs_integral_logPotential_mul_le {μ : Measure ℂ} [IsFiniteMeasure μ] {S R M : ℝ}
    (hμS : μ (closedBall 0 S)ᶜ = 0) {g : ℂ → ℝ} (hg : Measurable g) (hgM : ∀ z, ‖g z‖ ≤ M)
    (hgR : ∀ z, R < ‖z‖ → g z = 0) :
    |∫ z, (logPotential μ z).toReal * g z| ≤
      M * (∫ z, (ball (0 : ℂ) (R + S + 1)).indicator (fun y => ‖Real.log ‖y‖‖) z) *
        μ.real univ := by
  rw [integral_logPotential_mul hμS hg hgM hgR, abs_neg, ← Real.norm_eq_abs]
  have hae : ∀ᵐ w ∂μ, w ∈ closedBall (0 : ℂ) S :=
    measure_eq_zero_iff_ae_notMem.1 hμS |>.mono fun w hw => by simpa using hw
  calc ‖∫ w, (∫ z, Real.log ‖z - w‖ * g z) ∂μ‖
      ≤ ∫ _w, M * (∫ z, (ball (0 : ℂ) (R + S + 1)).indicator (fun y => ‖Real.log ‖y‖‖) z) ∂μ := by
        refine norm_integral_le_of_norm_le (integrable_const _) ?_
        filter_upwards [hae] with w hw
        rw [Real.norm_eq_abs]
        exact abs_integral_log_mul_le hgM hgR (by simpa using hw)
    _ = _ := by rw [integral_const, smul_eq_mul, mul_comm]

end Distr

/-! ### Theorem A.3.4 -/

lemma isOpen_annulus (s : ℝ) : IsOpen (annulus s) :=
  show IsOpen ((fun z : ℂ => ‖z‖) ⁻¹' Ioo (1 - s) (1 + s)) from
    isOpen_Ioo.preimage continuous_norm

open Distr in
/-- **Theorem A.3.4.** -/
theorem rieszMeasureBoundStatement_holds : RieszMeasureBoundStatement := by
  intro ρ hρ hρ1
  set K2 : Set ℂ := (fun z : ℂ => ‖z‖) ⁻¹' Icc (1 - ρ / 2) (1 + ρ / 2) with hK2def
  have hK2 : IsCompact K2 := by
    refine Metric.isCompact_of_isClosed_isBounded (isClosed_Icc.preimage continuous_norm)
      (isBounded_closedBall (x := (0 : ℂ)) (r := 2) |>.subset fun z hz => ?_)
    rw [mem_closedBall, dist_zero_right]
    have := hz.2
    linarith
  have hK2A : K2 ⊆ annulus ρ := fun z hz =>
    ⟨by have := hz.1; linarith, by have := hz.2; linarith⟩
  have hA2K2 : annulus (ρ / 2) ⊆ K2 := fun z hz => ⟨hz.1.le, hz.2.le⟩
  have hA2A : annulus (ρ / 2) ⊆ annulus ρ := hA2K2.trans hK2A
  have hA : IsOpen (annulus ρ) := isOpen_annulus ρ
  obtain ⟨φ, hφ, hφc, hφA, hφ01, δ, -, hφ1⟩ := exists_cutoff hK2 hA hK2A
  have hφK2 : ∀ x ∈ K2, φ x = 1 := fun x hx => hφ1 x (self_subset_cthickening _ hx)
  have hΔc := continuous_laplacian hφ
  have hΔs : HasCompactSupport (Δ φ) :=
    HasCompactSupport.intro hφc.isCompact fun z hz => laplacian_eq_zero_of_notMem hφ hz
  set C1 : ℝ := (2 * π)⁻¹ * ∫ z, |Δ φ z| with hC1
  have hC10 : 0 ≤ C1 := mul_nonneg (by positivity) (integral_nonneg fun _ => abs_nonneg _)
  set r : ℝ := ρ / 6 with hr_def
  have hr : 0 < r := by positivity
  set c : ℝ := (bumpMass * r ^ 2)⁻¹ with hc
  have hc0 : 0 ≤ c := inv_nonneg.2 (mul_nonneg bumpMass_pos.le (sq_nonneg r))
  set C0 : ℝ := ∫ z, (ball (0 : ℂ) (3 + 2 + 1)).indicator (fun y => ‖Real.log ‖y‖‖) z with hC0
  have hC00 : 0 ≤ C0 := integral_nonneg fun _ => indicator_nonneg (fun _ _ => norm_nonneg _) _
  refine ⟨C1 + 1 + c * C0 * C1, fun u M hu hM μ h hμfin hμA2 hh hrep => ?_⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 1 (by
    show 1 - ρ < ‖(1 : ℂ)‖ ∧ ‖(1 : ℂ)‖ < 1 + ρ
    rw [norm_one]; constructor <;> linarith))
  have hA2B : annulus (ρ / 2) ⊆ closedBall 0 2 := fun z hz => by
    rw [mem_closedBall, dist_zero_right]; have := hz.2; linarith
  have hμS : μ (closedBall 0 2)ᶜ = 0 := measure_mono_null (compl_subset_compl.2 hA2B) hμA2
  -- the mass bound
  have hmass : μ.real univ ≤ C1 * M := by
    obtain ⟨ν, hνfin, hν⟩ := exists_rieszMeasure hA hu hφc.isCompact hφA
    haveI := hνfin
    have hA2φ : annulus (ρ / 2) ⊆ tsupport φ := fun x hx => subset_tsupport φ (by
      rw [Function.mem_support, hφK2 x (hA2K2 hx)]; exact one_ne_zero)
    haveI : IsFiniteMeasure (ν.restrict (annulus (ρ / 2))) := ⟨by
      rw [Measure.restrict_apply_univ]
      exact (measure_mono hA2φ).trans_lt hφc.isCompact.measure_lt_top⟩
    have hμν : μ = ν.restrict (annulus (ρ / 2)) := by
      refine measure_eq_of_integral_eq (isOpen_annulus _) hμA2 ?_ fun ψ hψ hψc hψV => ?_
      · rw [Measure.restrict_apply (isOpen_annulus _).isClosed_compl.measurableSet,
          compl_inter_self, measure_empty]
      · rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx =>
          image_eq_zero_of_notMem_tsupport fun h' => hx (hψV h'),
          hν ψ hψ hψc (hψV.trans hA2φ),
          integral_mul_laplacian_of_rep (isOpen_annulus _) hμS hh hrep hψ hψc hψV
            (integrableOn_of_subharmonic hA hu hψc.isCompact (hψV.trans hA2A))]
        have := Real.pi_pos.ne'
        field_simp
    have hφi : Integrable φ ν := hφ.continuous.integrable_of_hasCompactSupport hφc
    have h1 : ν (annulus (ρ / 2)) ≤ ENNReal.ofReal (∫ z, φ z ∂ν) := by
      rw [ofReal_integral_eq_lintegral_ofReal hφi (Eventually.of_forall fun z => (hφ01 z).1),
        ← lintegral_indicator_one (isOpen_annulus _).measurableSet]
      refine lintegral_mono fun z => ?_
      by_cases hz : z ∈ annulus (ρ / 2)
      · simp [hz, hφK2 z (hA2K2 hz)]
      · simp [hz]
    have hu2 : IntegrableOn u (tsupport φ) :=
      integrableOn_of_subharmonic hA hu hφc.isCompact hφA
    have h2 : ∫ z, u z * Δ φ z ≤ M * ∫ z, |Δ φ z| := by
      rw [← integral_const_mul]
      refine integral_mono (integrable_u_laplacian hφc.isCompact hu2 hφ subset_rfl)
        (((hΔc.abs).integrable_of_hasCompactSupport
          (hΔs.comp_left (g := fun x : ℝ => |x|) abs_zero)).const_mul M) fun z => ?_
      by_cases hz : z ∈ tsupport φ
      · calc u z * Δ φ z ≤ |u z * Δ φ z| := le_abs_self _
          _ = |u z| * |Δ φ z| := abs_mul _ _
          _ ≤ M * |Δ φ z| := mul_le_mul_of_nonneg_right (hM z (hφA hz)) (abs_nonneg _)
      · simp [laplacian_eq_zero_of_notMem hφ hz]
    have h3 : ∫ z, φ z ∂ν ≤ C1 * M := by
      rw [hν φ hφ hφc subset_rfl, hC1]
      have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ (2 * π)⁻¹)
      linarith
    rw [hμν, measureReal_def, Measure.restrict_apply_univ]
    exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg hC10 hM0)
      (h1.trans (ENNReal.ofReal_le_ofReal h3))
  refine ⟨hmass.trans (by nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hc0 hC00) hC10) hM0]),
    fun z hz => ?_⟩
  -- the bound on the harmonic part
  have hz' : 1 - ρ / 3 < ‖z‖ ∧ ‖z‖ < 1 + ρ / 3 := hz
  have hball : closedBall z r ⊆ annulus (ρ / 2) := by
    intro w hw
    rw [mem_closedBall, dist_eq_norm] at hw
    have h1 := norm_sub_norm_le w z
    have h2 := norm_sub_norm_le z w
    rw [norm_sub_rev] at h2
    exact ⟨by linarith, by linarith⟩
  have hiu : Integrable (fun y => u (z + y) * moll r y) :=
    integrable_comp_add_mul_moll hr
      (integrableOn_of_subharmonic hA hu (isCompact_closedBall z r) (hball.trans hA2A))
  have hballB : closedBall z r ⊆ closedBall 0 3 := fun w hw => by
    rw [mem_closedBall, dist_eq_norm] at hw
    rw [mem_closedBall, dist_zero_right]
    have := norm_le_insert' w z
    linarith [hz'.2]
  have hiΦ : Integrable (fun y => (logPotential μ (z + y)).toReal * moll r y) :=
    integrable_comp_add_mul_moll hr ((integrableOn_logPotential hμS 3).mono_set hballB)
  -- mean value property
  have hmean : h z = (∫ y, u (z + y) * moll r y) +
      ∫ y, (logPotential μ (z + y)).toReal * moll r y := by
    have := integral_harmonic_mul_radial hr.le (hh.mono hball) (continuous_moll r)
      (moll_eq_mollRad hr) (fun y hy => moll_eq_zero hr hy.le)
    rw [integral_moll hr, mul_one] at this
    rw [← this, ← integral_add hiu hiΦ]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    by_cases hy : ‖y‖ ≤ r
    · have hmem : z + y ∈ annulus (ρ / 2) := hball (add_mem_closedBall_of_norm_le hy)
      simp only [← add_toReal_logPotential_of_rep (hrep _ hmem)]
      ring
    · simp [moll_eq_zero hr (not_le.1 hy).le]
  -- the `u` part
  have hU : |∫ y, u (z + y) * moll r y| ≤ M := by
    have hb : ∀ y, ‖y‖ < r → |u (z + y)| ≤ M := fun y hy =>
      hM _ (hA2A (hball (add_mem_closedBall_of_norm_le hy.le)))
    rw [abs_le]
    exact ⟨le_integral_moll_of_le hr hiu (Eventually.of_forall fun y hy => (abs_le.1 (hb y hy)).1),
      integral_moll_le_of_le hr hiu fun y hy => (abs_le.1 (hb y hy)).2⟩
  -- the potential part
  have hΦ : |∫ y, (logPotential μ (z + y)).toReal * moll r y| ≤ c * C0 * μ.real univ := by
    have e : ∫ y, (logPotential μ (z + y)).toReal * moll r y =
        ∫ x, (logPotential μ x).toReal * moll r (x - z) := by
      have := integral_add_left_eq_self (μ := volume)
        (fun x => (logPotential μ x).toReal * moll r (x - z)) z
      simp only [add_sub_cancel_left] at this
      exact this
    rw [e]
    refine abs_integral_logPotential_mul_le (R := 3) (M := c) hμS
      ((continuous_moll r).comp (continuous_id.sub continuous_const)).measurable
      (fun x => by rw [Real.norm_of_nonneg (moll_nonneg _)]; exact moll_le _)
      (fun x hx => moll_eq_zero hr ?_)
    have := norm_sub_norm_le x z
    have : r ≤ 1 := by rw [hr_def]; linarith
    linarith [hz'.2]
  rw [hmean]
  calc |(∫ y, u (z + y) * moll r y) + ∫ y, (logPotential μ (z + y)).toReal * moll r y|
      ≤ |∫ y, u (z + y) * moll r y| + |∫ y, (logPotential μ (z + y)).toReal * moll r y| :=
        abs_add_le _ _
    _ ≤ M + c * C0 * (C1 * M) := by
        have := mul_le_mul_of_nonneg_left hmass (mul_nonneg hc0 hC00)
        linarith
    _ ≤ (C1 + 1 + c * C0 * C1) * M := by nlinarith [mul_nonneg hC10 hM0]

end DF
