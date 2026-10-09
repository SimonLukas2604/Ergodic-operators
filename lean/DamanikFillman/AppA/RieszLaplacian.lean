/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Appendix A.3: the distributional Laplacian of a logarithmic potential

For a finite measure `μ` with bounded support, the logarithmic potential
`Φ_μ(z) = ∫ log |z - w|⁻¹ dμ(w)` satisfies `ΔΦ_μ = -2πμ` in the sense of distributions:

  `∫ Φ_μ(z) Δφ(z) dz = -2π ∫ φ dμ`

for every compactly supported `C²` function `φ` (`DF.Distr.integral_logPotential_mul_laplacian`).
This combines the fundamental solution (`DF.Distr.integral_log_mul_laplacian`) with Fubini's
theorem; the necessary integrability of `(w, z) ↦ log |z - w| g(z)` is
`DF.Distr.integrable_prod_log`.  We also record that `Φ_μ` is locally integrable.
-/
import DamanikFillman.AppA.Distributional
import DamanikFillman.AppA.Potential

noncomputable section

open Real Complex Metric Set Filter Topology MeasureTheory Laplacian InnerProductSpace

namespace DF

namespace Distr

/-! ### Translations -/

lemma Dv_comp_add (f : ℂ → ℝ) (w v : ℂ) :
    Dv (fun z => f (z + w)) v = fun z => Dv f v (z + w) := by
  funext z
  simp only [Dv]
  rw [fderiv_comp_add_right]

lemma laplacian_comp_add {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) (w z : ℂ) :
    Δ (fun z => φ (z + w)) z = Δ φ (z + w) := by
  have hψ : ContDiff ℝ 2 (fun z => φ (z + w)) := hφ.comp (contDiff_id.add contDiff_const)
  rw [laplacian_eq_Dv hψ, laplacian_eq_Dv hφ]
  rw [Dv_comp_add φ w 1, Dv_comp_add (Dv φ 1) w 1, Dv_comp_add φ w I, Dv_comp_add (Dv φ I) w I]

/-- The translated fundamental solution: `∫ log |z - w| Δφ(z) dz = 2π φ(w)`. -/
theorem integral_log_sub_mul_laplacian {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) (w : ℂ) :
    ∫ z, Real.log ‖z - w‖ * Δ φ z = 2 * π * φ w := by
  have hψ : ContDiff ℝ 2 (fun z => φ (z + w)) := hφ.comp (contDiff_id.add contDiff_const)
  have hψc : HasCompactSupport (fun z => φ (z + w)) :=
    hφc.comp_homeomorph (Homeomorph.addRight w)
  have h := integral_log_mul_laplacian hψ hψc
  simp only [laplacian_comp_add hφ, zero_add] at h
  have ht := integral_add_right_eq_self (μ := volume) (fun z => Real.log ‖z - w‖ * Δ φ z) w
  simp only [add_sub_cancel_right] at ht
  rw [← ht]
  exact h

/-! ### Integrability of the logarithmic kernel against test functions -/

/-- The translated local integrable majorant of `|log |z - w||`. -/
lemma integrable_indicator_log (ρ : ℝ) (w : ℂ) :
    Integrable (fun z => (ball (0 : ℂ) ρ).indicator (fun y => ‖Real.log ‖y‖‖) (z - w)) :=
  (IntegrableOn.integrable_indicator (f := fun y : ℂ => ‖Real.log ‖y‖‖)
    (integrableOn_log_norm ρ).norm measurableSet_ball).comp_sub_right w

lemma norm_log_mul_le {g : ℂ → ℝ} {S R M : ℝ} (hgM : ∀ z, ‖g z‖ ≤ M)
    (hgR : ∀ z, R < ‖z‖ → g z = 0) {w : ℂ} (hw : ‖w‖ ≤ S) (z : ℂ) :
    ‖Real.log ‖z - w‖ * g z‖ ≤
      M * (ball (0 : ℂ) (R + S + 1)).indicator (fun y => ‖Real.log ‖y‖‖) (z - w) := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hgM 0)
  by_cases hz : ‖z‖ ≤ R
  · have hmem : z - w ∈ ball (0 : ℂ) (R + S + 1) := by
      rw [mem_ball, dist_zero_right]
      linarith [norm_sub_le z w]
    rw [indicator_of_mem hmem, norm_mul, mul_comm M]
    exact mul_le_mul_of_nonneg_left (hgM z) (norm_nonneg _)
  · rw [hgR z (lt_of_not_ge hz), mul_zero, norm_zero]
    exact mul_nonneg hM0 (indicator_nonneg (fun _ _ => norm_nonneg _) _)

/-- `(w, z) ↦ log |z - w| g(z)` is integrable for bounded, compactly supported measurable `g`
and finite `μ` with bounded support. -/
theorem integrable_prod_log {μ : Measure ℂ} [IsFiniteMeasure μ] {S R M : ℝ}
    (hμS : μ (closedBall 0 S)ᶜ = 0) {g : ℂ → ℝ} (hg : Measurable g) (hgM : ∀ z, ‖g z‖ ≤ M)
    (hgR : ∀ z, R < ‖z‖ → g z = 0) :
    Integrable (fun p : ℂ × ℂ => Real.log ‖p.2 - p.1‖ * g p.2) (μ.prod volume) := by
  have hae : ∀ᵐ w ∂μ, w ∈ closedBall (0 : ℂ) S :=
    measure_eq_zero_iff_ae_notMem.1 hμS |>.mono fun w hw => by simpa using hw
  have hmeas : AEStronglyMeasurable (fun p : ℂ × ℂ => Real.log ‖p.2 - p.1‖ * g p.2)
      (μ.prod volume) :=
    ((Real.measurable_log.comp (measurable_norm.comp (measurable_snd.sub measurable_fst))).mul
      (hg.comp measurable_snd)).aestronglyMeasurable
  have hint : ∀ w, ‖w‖ ≤ S → Integrable (fun z => Real.log ‖z - w‖ * g z) := by
    intro w hw
    refine ((integrable_indicator_log (R + S + 1) w).const_mul M).mono' ?_
      (Eventually.of_forall fun z => norm_log_mul_le hgM hgR hw z)
    exact ((Real.measurable_log.comp (measurable_norm.comp (measurable_id.sub_const w))).mul
      hg).aestronglyMeasurable
  set C0 : ℝ := ∫ z, (ball (0 : ℂ) (R + S + 1)).indicator (fun y => ‖Real.log ‖y‖‖) z with hC0
  have hbound : ∀ w, ‖w‖ ≤ S → ∫ z, ‖Real.log ‖z - w‖ * g z‖ ≤ M * C0 := by
    intro w hw
    calc ∫ z, ‖Real.log ‖z - w‖ * g z‖
        ≤ ∫ z, M * (ball (0 : ℂ) (R + S + 1)).indicator (fun y => ‖Real.log ‖y‖‖) (z - w) :=
          integral_mono (hint w hw).norm ((integrable_indicator_log (R + S + 1) w).const_mul M)
            (fun z => norm_log_mul_le hgM hgR hw z)
      _ = M * C0 := by
          rw [integral_const_mul, hC0,
            integral_sub_right_eq_self
              (fun z => (ball (0 : ℂ) (R + S + 1)).indicator (fun y => ‖Real.log ‖y‖‖) z) w]
  rw [integrable_prod_iff hmeas]
  refine ⟨hae.mono fun w hw => hint w (by simpa using hw), ?_⟩
  refine (integrable_const (M * C0)).mono' hmeas.norm.integral_prod_right' ?_
  filter_upwards [hae] with w hw
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  exact hbound w (by simpa using hw)

/-! ### `ΔΦ_μ = -2πμ` -/

lemma integrable_norm_of_bounded {μ : Measure ℂ} [IsFiniteMeasure μ] {S : ℝ}
    (hμS : μ (closedBall 0 S)ᶜ = 0) : Integrable (fun w => ‖w‖) μ := by
  have hae : ∀ᵐ w ∂μ, w ∈ closedBall (0 : ℂ) S :=
    measure_eq_zero_iff_ae_notMem.1 hμS |>.mono fun w hw => by simpa using hw
  refine (integrable_const S).mono' continuous_norm.aestronglyMeasurable ?_
  filter_upwards [hae] with w hw
  rw [norm_norm]
  simpa using hw

/-- Almost every point is not an atom of a finite measure. -/
lemma ae_measure_singleton_eq_zero (μ : Measure ℂ) [IsFiniteMeasure μ] :
    ∀ᵐ z : ℂ ∂volume, μ {z} = 0 := by
  have hc : Set.Countable {z : ℂ | 0 < μ {z}} :=
    Measure.countable_meas_pos_of_disjoint_iUnion (As := fun z : ℂ => ({z} : Set ℂ))
      (fun z => measurableSet_singleton z)
      (fun a b h => by simpa [Function.onFun] using h)
  have h0 : volume {z : ℂ | 0 < μ {z}} = 0 := hc.measure_zero _
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with z hz
  simpa using hz

/-- Where `w ↦ log |z - w|` is `μ`-integrable and `z` is not an atom, `Φ_μ(z)` is real and equals
`-∫ log |z - w| dμ(w)`. -/
lemma toReal_logPotential_eq {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : Integrable (fun w => ‖w‖) μ) {z : ℂ} (hz : μ {z} = 0)
    (hint : Integrable (fun w => Real.log ‖z - w‖) μ) :
    (logPotential μ z).toReal = -∫ w, Real.log ‖z - w‖ ∂μ := by
  rw [logPotential_eq_integral hμ hz hint, EReal.toReal_coe, integral_neg]

/-- **`ΔΦ_μ = -2πμ` in the sense of distributions.** -/
theorem integral_logPotential_mul_laplacian {μ : Measure ℂ} [IsFiniteMeasure μ] {S : ℝ}
    (hμS : μ (closedBall 0 S)ᶜ = 0) {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφc : HasCompactSupport φ) :
    ∫ z, (logPotential μ z).toReal * Δ φ z = -(2 * π * ∫ w, φ w ∂μ) := by
  obtain ⟨R, -, hRs⟩ := exists_support_subset_closedBall hφc
  have hΔc := continuous_laplacian hφ
  have hΔcs : HasCompactSupport (Δ φ) :=
    HasCompactSupport.intro (isCompact_closedBall 0 R) fun z hz =>
      laplacian_eq_zero_of_notMem hφ fun h => hz (hRs h)
  obtain ⟨M, hM⟩ := hΔcs.exists_bound_of_continuous hΔc
  have hR : ∀ z, R < ‖z‖ → Δ φ z = 0 := fun z hz =>
    laplacian_eq_zero_of_notMem hφ fun h => by
      have := hRs h
      rw [mem_closedBall, dist_zero_right] at this
      linarith
  have hI := integrable_prod_log hμS hΔc.measurable hM hR
  have hμ := integrable_norm_of_bounded hμS
  -- Fubini
  have hswap := integral_integral_swap (f := fun w z => Real.log ‖z - w‖ * Δ φ z) hI
  simp only [integral_log_sub_mul_laplacian hφ hφc] at hswap
  rw [integral_const_mul] at hswap
  -- identify the inner integral with the potential
  have hae : ∀ᵐ z : ℂ ∂volume, (logPotential μ z).toReal * Δ φ z =
      -∫ w, Real.log ‖z - w‖ * Δ φ z ∂μ := by
    filter_upwards [ae_measure_singleton_eq_zero μ, hI.prod_left_ae] with z hz hzi
    by_cases h0 : Δ φ z = 0
    · simp [h0]
    · have hint : Integrable (fun w => Real.log ‖z - w‖) μ := by
        refine (hzi.mul_const (Δ φ z)⁻¹).congr (Eventually.of_forall fun w => ?_)
        field_simp
      rw [toReal_logPotential_eq hμ hz hint, integral_mul_const]
      ring
  rw [integral_congr_ae hae, integral_neg, ← hswap]

/-- Logarithmic potentials of finite measures with bounded support are locally integrable. -/
theorem integrableOn_logPotential {μ : Measure ℂ} [IsFiniteMeasure μ] {S : ℝ}
    (hμS : μ (closedBall 0 S)ᶜ = 0) (R : ℝ) :
    IntegrableOn (fun z => (logPotential μ z).toReal) (closedBall 0 R) := by
  set g : ℂ → ℝ := (closedBall (0 : ℂ) R).indicator 1 with hg
  have hgm : Measurable g := measurable_one.indicator measurableSet_closedBall
  have hgM : ∀ z, ‖g z‖ ≤ 1 := fun z => by
    rw [hg]
    by_cases hz : z ∈ closedBall (0 : ℂ) R
    · simp [indicator_of_mem hz]
    · simp [indicator_of_notMem hz]
  have hgR : ∀ z, R < ‖z‖ → g z = 0 := fun z hz => by
    rw [hg, indicator_of_notMem]
    rw [mem_closedBall, dist_zero_right]
    exact not_le.2 hz
  have hI := integrable_prod_log hμS hgm hgM hgR
  have hμ := integrable_norm_of_bounded hμS
  -- the inner integrals give an integrable function
  have hJ : Integrable (fun z => ∫ w, Real.log ‖z - w‖ * g z ∂μ) := hI.integral_prod_right
  rw [← integrable_indicator_iff measurableSet_closedBall]
  refine hJ.neg.congr ?_
  filter_upwards [ae_measure_singleton_eq_zero μ, hI.prod_left_ae] with z hz hzi
  by_cases hzR : z ∈ closedBall (0 : ℂ) R
  · have hg1 : g z = 1 := by simp [hg, indicator_of_mem hzR]
    have hint : Integrable (fun w => Real.log ‖z - w‖) μ := by
      simpa [hg1] using hzi
    rw [indicator_of_mem hzR, toReal_logPotential_eq hμ hz hint]
    simp [hg1]
  · have hg0 : g z = 0 := by simp [hg, indicator_of_notMem hzR]
    rw [indicator_of_notMem hzR]
    simp [hg0]

end Distr

end DF
