/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators, I*,
§1.9.1 (pp. 82–83): the Carathéodory representation theorem.

# Main results

* `DF.caratheodory_repr` — Theorem 1.9.3, "only if" direction: an analytic function on the unit
  disk with positive real part has the form `G(z) = i c + ∫_{∂𝔻} (w + z)/(w - z) dν(w)` with
  `c ∈ ℝ` and a finite nonzero measure `ν` on the unit circle;
* `DF.caratheodory_of_repr` — Theorem 1.9.3, "if" direction (Exercise 1.9.3);
* `DF.caratheodoryRepresentationStatement_holds` — the statement
  `DF.CaratheodoryRepresentationStatement` of `DamanikFillman.Ch1.BorelTransform` is proved.

# Proof

As in the book: Mathlib's Poisson integral formula
(`DiffContOnCl.circleAverage_re_herglotzRieszKernel_smul'`) represents `Re G` on the disk of
radius `r < 1` by the measure `ν_r = Re G(r e^{iθ}) dθ / 2π` (transported to the unit circle).
These measures all have mass `Re G(0)`; by compactness of the space of finite measures of bounded
mass on the (compact) unit circle (`isCompact_setOfPred_finiteMeasure_le_of_compactSpace`, the
analogue of Theorems 1.5.8 and 1.5.9) they have a weak cluster point `ν` as `r ↑ 1`, which
represents `Re G`.  An analytic function with vanishing real part is constant (open mapping
theorem), which yields the imaginary constant `i c`.
-/
import DamanikFillman.Ch1.BorelTransform

noncomputable section

open MeasureTheory Filter Topology Set Metric Complex
open scoped ENNReal NNReal

namespace DF

/-- The unit circle, as a (compact) subtype of `ℂ`. -/
abbrev UnitCircle : Type := sphere (0 : ℂ) 1

/-- `θ ↦ e^{iθ}` as a point of the unit circle. -/
def expCircle (θ : ℝ) : UnitCircle := ⟨circleMap 0 1 θ, circleMap_mem_sphere 0 zero_le_one θ⟩

lemma continuous_expCircle : Continuous expCircle :=
  (continuous_circleMap 0 1).subtype_mk _

lemma circleMap_zero_eq_mul (r θ : ℝ) : circleMap 0 r θ = r * (expCircle θ : ℂ) := by
  simp [expCircle, circleMap]

lemma norm_unitCircle (ζ : UnitCircle) : ‖(ζ : ℂ)‖ = 1 := by
  simp

/-! ## Algebra of the Herglotz–Riesz kernel -/

/-- `Re ((w + z)/(w - z)) = (|w|² - |z|²) / |w - z|²`. -/
lemma re_herglotz_kernel (w z : ℂ) :
    ((w + z) / (w - z)).re = (Complex.normSq w - Complex.normSq z) / Complex.normSq (w - z) := by
  rw [Complex.div_re, ← add_div]
  congr 1
  simp only [Complex.normSq_apply, Complex.add_re, Complex.sub_re, Complex.add_im,
    Complex.sub_im]
  ring

lemma sub_ne_zero_of_norm_lt {ζ w : ℂ} (h : ‖w‖ < ‖ζ‖) : ζ - w ≠ 0 := by
  intro h0; rw [sub_eq_zero.1 h0] at h; exact lt_irrefl _ h

/-- Uniform comparison of the kernels at radius `1` and radius `r`. -/
lemma norm_kernel_sub_le {ζ w : ℂ} (hζ : ‖ζ‖ = 1) {r : ℝ} (hr1 : r ≤ 1) (hwr : ‖w‖ < r) :
    ‖(ζ + w) / (ζ - w) - (r * ζ + w) / (r * ζ - w)‖ ≤
      2 * ‖w‖ * (1 - r) / ((1 - ‖w‖) * (r - ‖w‖)) := by
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg _) hwr
  have hrζ : ‖(r : ℂ) * ζ‖ = r := by
    rw [norm_mul, hζ, mul_one, Complex.norm_real, Real.norm_of_nonneg hr0.le]
  have h1 : ζ - w ≠ 0 := sub_ne_zero_of_norm_lt (by rw [hζ]; linarith)
  have h2 : (r : ℂ) * ζ - w ≠ 0 := sub_ne_zero_of_norm_lt (by rw [hrζ]; exact hwr)
  have hid : (ζ + w) / (ζ - w) - (r * ζ + w) / (r * ζ - w) =
      2 * ζ * w * (r - 1) / ((ζ - w) * (r * ζ - w)) := by
    rw [div_sub_div _ _ h1 h2]; congr 1; ring
  rw [hid, norm_div, norm_mul, norm_mul, norm_mul, norm_mul, hζ]
  have hn1 : 1 - ‖w‖ ≤ ‖ζ - w‖ := by
    have := norm_sub_norm_le ζ w; rw [hζ] at this; exact this
  have hn2 : r - ‖w‖ ≤ ‖(r : ℂ) * ζ - w‖ := by
    have := norm_sub_norm_le ((r : ℂ) * ζ) w; rw [hrζ] at this; exact this
  have hr1' : ‖((r : ℂ) - 1)‖ = 1 - r := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (by linarith)]
    ring
  rw [hr1', show ‖(2 : ℂ)‖ = 2 by simp]
  have hpos1 : 0 < 1 - ‖w‖ := by linarith
  have hpos2 : 0 < r - ‖w‖ := by linarith
  apply div_le_div₀ (by have := norm_nonneg w; nlinarith) (le_of_eq (by ring))
    (mul_pos hpos1 hpos2) (mul_le_mul hn1 hn2 hpos2.le (norm_nonneg _))

/-! ## Functions with vanishing real part -/

/-- A holomorphic function on the unit disk with identically vanishing real part is constant. -/
lemma eqOn_of_re_eq_zero {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (ball 0 1))
    (hre : ∀ z ∈ ball (0 : ℂ) 1, (f z).re = 0) : ∀ z ∈ ball (0 : ℂ) 1, f z = f 0 := by
  have han : AnalyticOnNhd ℂ f (ball 0 1) := hf.analyticOnNhd isOpen_ball
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) 1 := mem_ball_self one_pos
  rcases (han 0 h0).eventually_constant_or_nhds_le_map_nhds with h | h
  · intro z hz
    exact han.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      (convex_ball 0 1).isPreconnected h0 h hz
  · exfalso
    have hmem : {w : ℂ | w.re = 0} ∈ 𝓝 (f 0) := by
      apply h
      rw [mem_map]
      exact Filter.mem_of_superset (isOpen_ball.mem_nhds h0) fun z hz => hre z hz
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hmem
    have hp : f 0 + (ε / 2 : ℝ) ∈ ball (f 0) ε := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
        Real.norm_of_nonneg (by positivity)]
      linarith
    have := hball hp
    simp only [mem_ofPred_eq, Complex.add_re, Complex.ofReal_re, hre 0 h0, zero_add] at this
    linarith

/-! ## The Herglotz integral of a measure on the circle -/

/-- `∫ (w + z)/(w - z) dν(w)` for a measure `ν` on `ℂ`. -/
def herglotzIntegral (ν : Measure ℂ) (z : ℂ) : ℂ := ∫ w, (w + z) / (w - z) ∂ν

lemma ae_mem_sphere {ν : Measure ℂ} (hsupp : ν (sphere 0 1)ᶜ = 0) :
    ∀ᵐ w ∂ν, w ∈ sphere (0 : ℂ) 1 := by
  rw [ae_iff]; exact hsupp

lemma herglotzIntegral_eq (ν : Measure ℂ) [IsFiniteMeasure ν] (hsupp : ν (sphere 0 1)ᶜ = 0)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    herglotzIntegral ν z = ν.real univ + 2 * z * resolventTransform ν z := by
  have hsup : ν.support ⊆ sphere 0 1 :=
    Measure.support_subset_of_isClosed isClosed_sphere (ae_mem_sphere hsupp)
  have hzs : z ∉ algebraMap ℂ ℂ '' ν.support := by
    rintro ⟨w, hw, rfl⟩
    have := hsup hw
    simp only [mem_sphere_iff_norm, sub_zero] at this
    simp only [mem_ball_iff_norm, sub_zero, Algebra.algebraMap_self, RingHom.id_apply] at hz
    linarith
  have hint : Integrable (resolvent z) ν := integrable_resolvent hzs
  unfold herglotzIntegral
  rw [resolventTransform_apply, ← integral_const_mul]
  have : (ν.real univ : ℂ) = ∫ _ : ℂ, (1 : ℂ) ∂ν := by simp
  rw [this, ← integral_add (integrable_const _) (hint.const_mul _)]
  apply integral_congr_ae
  filter_upwards [ae_mem_sphere hsupp] with w hw
  have hw1 : ‖w‖ = 1 := by simpa using hw
  have hz1 : ‖z‖ < 1 := by simpa using hz
  have hne : w - z ≠ 0 := sub_ne_zero_of_norm_lt (by rw [hw1]; exact hz1)
  simp only [resolvent, Algebra.algebraMap_self, RingHom.id_apply, Ring.inverse_eq_inv']
  field_simp
  ring

lemma differentiableOn_herglotzIntegral (ν : Measure ℂ) [IsFiniteMeasure ν]
    (hsupp : ν (sphere 0 1)ᶜ = 0) : DifferentiableOn ℂ (herglotzIntegral ν) (ball 0 1) := by
  have hsup : ν.support ⊆ sphere 0 1 :=
    Measure.support_subset_of_isClosed isClosed_sphere (ae_mem_sphere hsupp)
  have hR : DifferentiableOn ℂ (fun z : ℂ => (resolventTransform ν z : ℂ)) (ball 0 1) := by
    refine (analyticOn_resolventTransform (μ := ν)).differentiableOn.mono ?_
    rintro z hz ⟨w, hw, rfl⟩
    have := hsup hw
    simp only [mem_sphere_iff_norm, sub_zero] at this
    simp only [mem_ball_iff_norm, sub_zero, Algebra.algebraMap_self, RingHom.id_apply] at hz
    linarith
  have h2 : DifferentiableOn ℂ
      (fun z : ℂ => (ν.real univ : ℂ) + 2 * z * (resolventTransform ν z : ℂ))
      (ball 0 1) :=
    (differentiableOn_const _).add ((differentiableOn_id.const_mul _).mul hR)
  exact h2.congr fun z hz => herglotzIntegral_eq ν hsupp hz

lemma integrable_herglotz_kernel (ν : Measure ℂ) [IsFiniteMeasure ν]
    (hsupp : ν (sphere 0 1)ᶜ = 0) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    Integrable (fun w => (w + z) / (w - z)) ν := by
  have hz1 : ‖z‖ < 1 := by simpa using hz
  refine Integrable.of_bound (C := (1 + ‖z‖) / (1 - ‖z‖)) ?_ ?_
  · refine (Measurable.div (by fun_prop) (by fun_prop)).aestronglyMeasurable
  · filter_upwards [ae_mem_sphere hsupp] with w hw
    have hw1 : ‖w‖ = 1 := by simpa using hw
    rw [norm_div]
    have hden : 1 - ‖z‖ ≤ ‖w - z‖ := by
      have := norm_sub_norm_le w z; rwa [hw1] at this
    have hnum : ‖w + z‖ ≤ 1 + ‖z‖ := by
      have := norm_add_le w z; rwa [hw1] at this
    exact div_le_div₀ (by positivity) hnum (by linarith) hden

lemma re_herglotzIntegral (ν : Measure ℂ) [IsFiniteMeasure ν]
    (hsupp : ν (sphere 0 1)ᶜ = 0) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    (herglotzIntegral ν z).re = ∫ w, ((w + z) / (w - z)).re ∂ν := by
  unfold herglotzIntegral
  have h := integral_re (integrable_herglotz_kernel ν hsupp hz)
  simp only [RCLike.re_to_complex] at h
  exact h.symm

/-- Theorem 1.9.3, "if" direction (Exercise 1.9.3): a function of the form
`i c + ∫ (w + z)/(w - z) dν(w)` is analytic on the disk with positive real part. -/
theorem caratheodory_of_repr (c : ℝ) (ν : Measure ℂ) [IsFiniteMeasure ν] (hν : ν ≠ 0)
    (hsupp : ν (sphere 0 1)ᶜ = 0) :
    DifferentiableOn ℂ (fun z => c * I + herglotzIntegral ν z) (ball 0 1) ∧
      ∀ z ∈ ball (0 : ℂ) 1, 0 < (c * I + herglotzIntegral ν z).re := by
  refine ⟨(differentiableOn_const _).add (differentiableOn_herglotzIntegral ν hsupp),
    fun z hz => ?_⟩
  have hz1 : ‖z‖ < 1 := by simpa using hz
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, mul_zero,
    Complex.ofReal_im, Complex.I_im, mul_one, sub_self, zero_add]
  rw [re_herglotzIntegral ν hsupp hz]
  have hint : Integrable (fun w => ((w + z) / (w - z)).re) ν :=
    (integrable_herglotz_kernel ν hsupp hz).re
  have hpos : ∀ᵐ w ∂ν, 0 < ((w + z) / (w - z)).re := by
    filter_upwards [ae_mem_sphere hsupp] with w hw
    have hw1 : ‖w‖ = 1 := by simpa using hw
    rw [re_herglotz_kernel, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq, hw1]
    have hne : w - z ≠ 0 := sub_ne_zero_of_norm_lt (by rw [hw1]; exact hz1)
    have : 0 < ‖w - z‖ := norm_pos_iff.2 hne
    apply div_pos _ (by positivity)
    nlinarith [norm_nonneg z]
  rw [integral_pos_iff_support_of_nonneg_ae (hpos.mono fun w hw => hw.le) hint]
  have hsupport : ν (Function.support fun w => ((w + z) / (w - z)).re) = ν univ := by
    apply measure_congr
    filter_upwards [hpos] with w hw
    simp [hw.ne']
  rw [hsupport, Measure.measure_univ_pos]
  exact hν

/-! ## The approximating measures `ν_r` -/

lemma circleMap_mem_ball {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (θ : ℝ) :
    circleMap 0 r θ ∈ ball (0 : ℂ) 1 := by
  rw [mem_ball_iff_norm, sub_zero, norm_circleMap_zero, abs_of_pos hr0]; exact hr1


/-- The density `θ ↦ Re G(r e^{iθ}) / (2π)` on `(0, 2π]`, transported to the unit circle. -/
def nuR (G : ℂ → ℂ) (r : ℝ) : Measure UnitCircle :=
  ((volume.restrict (Ioc 0 (2 * Real.pi))).withDensity
    (fun θ => ENNReal.ofReal ((G (circleMap 0 r θ)).re / (2 * Real.pi)))).map expCircle

section Approx

variable {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G (ball 0 1))
  (hpos : ∀ z ∈ ball (0 : ℂ) 1, 0 < (G z).re)
include hG hpos

omit hpos in
lemma continuous_re_G_circle {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Continuous fun θ => (G (circleMap 0 r θ)).re :=
  Complex.continuous_re.comp (hG.continuousOn.comp_continuous (continuous_circleMap 0 r)
    (circleMap_mem_ball hr0 hr1))

omit hpos in
lemma isFiniteMeasure_nuR {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) : IsFiniteMeasure (nuR G r) := by
  unfold nuR
  have : IsFiniteMeasure ((volume.restrict (Ioc 0 (2 * Real.pi))).withDensity
      (fun θ => ENNReal.ofReal ((G (circleMap 0 r θ)).re / (2 * Real.pi)))) := by
    apply isFiniteMeasure_withDensity_ofReal
    exact (((continuous_re_G_circle hG hr0 hr1).div_const _).integrableOn_Icc.mono_set
      Ioc_subset_Icc_self).2
  infer_instance

/-- Integrals against `ν_r`. -/
lemma integral_nuR {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {φ : UnitCircle → ℝ}
    (hφ : Continuous φ) :
    ∫ ζ, φ ζ ∂(nuR G r) = (2 * Real.pi)⁻¹ *
      ∫ θ in Ioc 0 (2 * Real.pi), (G (circleMap 0 r θ)).re * φ (expCircle θ) := by
  have hc := continuous_re_G_circle hG hr0 hr1
  unfold nuR
  rw [integral_map continuous_expCircle.measurable.aemeasurable hφ.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul ((hc.div_const _).measurable.ennreal_ofReal)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with θ
  rw [ENNReal.toReal_ofReal (div_nonneg (hpos _ (circleMap_mem_ball hr0 hr1 θ)).le
    (by positivity)), smul_eq_mul]
  field_simp

omit hpos in
/-- Poisson representation of `Re G` at radius `r`. -/
lemma re_G_eq_integral {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {w : ℂ} (hw : ‖w‖ < r) :
    (G w).re = (2 * Real.pi)⁻¹ * ∫ θ in Ioc 0 (2 * Real.pi),
      ((circleMap 0 r θ + w) / (circleMap 0 r θ - w)).re * (G (circleMap 0 r θ)).re := by
  have hdc : DiffContOnCl ℂ G (ball 0 r) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball 0 hr0.ne']
    exact hG.mono (closedBall_subset_ball hr1)
  have hP := hdc.circleAverage_re_herglotzRieszKernel_smul' (c := 0)
    (by simpa using hw : w ∈ ball (0 : ℂ) r)
  simp only [sub_zero] at hP
  have hne : ∀ θ, circleMap 0 r θ - w ≠ 0 := fun θ => sub_ne_zero_of_norm_lt (by
    rw [norm_circleMap_zero, abs_of_pos hr0]; exact hw)
  have hcont : Continuous fun θ =>
      ((circleMap 0 r θ + w) / (circleMap 0 r θ - w)).re • G (circleMap 0 r θ) := by
    refine Continuous.smul (Complex.continuous_re.comp ?_)
      (hG.continuousOn.comp_continuous (continuous_circleMap 0 r)
        (circleMap_mem_ball hr0 hr1))
    exact ((continuous_circleMap 0 r).add continuous_const).div
      ((continuous_circleMap 0 r).sub continuous_const) hne
  rw [Real.circleAverage_def, intervalIntegral.integral_of_le (by positivity)] at hP
  have h := congrArg Complex.re hP
  rw [← h, Complex.smul_re, smul_eq_mul]
  congr 1
  have hi : Integrable (fun θ =>
      ((circleMap 0 r θ + w) / (circleMap 0 r θ - w)).re • G (circleMap 0 r θ))
      (volume.restrict (Ioc 0 (2 * Real.pi))) :=
    hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have := integral_re hi
  simp only [RCLike.re_to_complex] at this
  rw [← this]
  congr 1; ext θ
  rw [Complex.real_smul, Complex.re_ofReal_mul]

lemma integral_one_nuR {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∫ _ζ, (1 : ℝ) ∂(nuR G r) = (G 0).re := by
  rw [integral_nuR hG hpos hr0 hr1 continuous_const,
    re_G_eq_integral hG hr0 hr1 (w := 0) (by simpa using hr0)]
  congr 1
  apply integral_congr_ae
  filter_upwards with θ
  have hne : circleMap 0 r θ ≠ 0 := by
    intro h0; have := congrArg norm h0
    rw [norm_circleMap_zero, abs_of_pos hr0, norm_zero] at this; linarith
  simp [div_self hne]

lemma nuR_real_univ {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) : (nuR G r).real univ = (G 0).re := by
  have := integral_one_nuR hG hpos hr0 hr1
  simpa using this

/-- The key estimate: `|∫ Φ_w dν_r - Re G(w)| ≤ Re G(0) δ(r)`. -/
lemma abs_integral_nuR_sub_le {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {w : ℂ} (hw : ‖w‖ < r) :
    |∫ ζ, (((ζ : ℂ) + w) / ((ζ : ℂ) - w)).re ∂(nuR G r) - (G w).re| ≤
      (G 0).re * (2 * ‖w‖ * (1 - r) / ((1 - ‖w‖) * (r - ‖w‖))) := by
  set δ := 2 * ‖w‖ * (1 - r) / ((1 - ‖w‖) * (r - ‖w‖))
  have hwr1 : ‖w‖ < 1 := hw.trans hr1
  have hφ : Continuous fun ζ : UnitCircle => (((ζ : ℂ) + w) / ((ζ : ℂ) - w)).re := by
    refine Complex.continuous_re.comp ((continuous_subtype_val.add continuous_const).div
      (continuous_subtype_val.sub continuous_const) fun ζ => ?_)
    exact sub_ne_zero_of_norm_lt (by rw [norm_unitCircle]; exact hwr1)
  have hc := continuous_re_G_circle hG hr0 hr1
  rw [integral_nuR hG hpos hr0 hr1 hφ, re_G_eq_integral hG hr0 hr1 hw, ← mul_sub]
  have hne : ∀ θ, circleMap 0 r θ - w ≠ 0 := fun θ => sub_ne_zero_of_norm_lt (by
    rw [norm_circleMap_zero, abs_of_pos hr0]; exact hw)
  have hk : Continuous fun θ => ((circleMap 0 r θ + w) / (circleMap 0 r θ - w)).re :=
    Complex.continuous_re.comp (((continuous_circleMap 0 r).add continuous_const).div
      ((continuous_circleMap 0 r).sub continuous_const) hne)
  have i1 : Integrable (fun θ => (G (circleMap 0 r θ)).re *
      (((expCircle θ : ℂ) + w) / ((expCircle θ : ℂ) - w)).re)
      (volume.restrict (Ioc 0 (2 * Real.pi))) :=
    (hc.mul (hφ.comp continuous_expCircle)).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have i2 : Integrable (fun θ => ((circleMap 0 r θ + w) / (circleMap 0 r θ - w)).re *
      (G (circleMap 0 r θ)).re) (volume.restrict (Ioc 0 (2 * Real.pi))) :=
    (hk.mul hc).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  rw [← integral_sub i1 i2, abs_mul, abs_of_pos (by positivity)]
  have hbound : ∀ θ, |(G (circleMap 0 r θ)).re *
      (((expCircle θ : ℂ) + w) / ((expCircle θ : ℂ) - w)).re -
      ((circleMap 0 r θ + w) / (circleMap 0 r θ - w)).re * (G (circleMap 0 r θ)).re| ≤
      (G (circleMap 0 r θ)).re * δ := by
    intro θ
    have hG0 := (hpos _ (circleMap_mem_ball hr0 hr1 θ)).le
    rw [mul_comm (((circleMap 0 r θ + w) / (circleMap 0 r θ - w)).re), ← mul_sub, abs_mul,
      abs_of_nonneg hG0]
    apply mul_le_mul_of_nonneg_left _ hG0
    rw [← Complex.sub_re, circleMap_zero_eq_mul]
    exact (Complex.abs_re_le_norm _).trans
      (norm_kernel_sub_le (norm_unitCircle _) hr1.le hw)
  calc (2 * Real.pi)⁻¹ * |∫ θ in Ioc 0 (2 * Real.pi), ((G (circleMap 0 r θ)).re *
          (((expCircle θ : ℂ) + w) / ((expCircle θ : ℂ) - w)).re -
          ((circleMap 0 r θ + w) / (circleMap 0 r θ - w)).re * (G (circleMap 0 r θ)).re)|
      ≤ (2 * Real.pi)⁻¹ * ∫ θ in Ioc 0 (2 * Real.pi), (G (circleMap 0 r θ)).re * δ := by
        gcongr
        refine (abs_integral_le_integral_abs).trans (integral_mono_of_nonneg
          (Eventually.of_forall fun _ => abs_nonneg _) ?_ (Eventually.of_forall hbound))
        exact (hc.mul_const δ).integrableOn_Icc.mono_set Ioc_subset_Icc_self
    _ = (G 0).re * δ := by
        rw [integral_mul_const, ← mul_assoc, mul_comm _ δ]
        have h := integral_nuR hG hpos hr0 hr1 (φ := fun _ => (1 : ℝ)) continuous_const
        rw [integral_one_nuR hG hpos hr0 hr1] at h
        simp only [mul_one] at h
        rw [h]; ring

end Approx

/-! ## Theorem 1.9.3 -/

/-- Theorem 1.9.3 (Carathéodory representation), "only if" direction. -/
theorem caratheodory_repr (G : ℂ → ℂ) (hG : DifferentiableOn ℂ G (ball 0 1))
    (hpos : ∀ z ∈ ball (0 : ℂ) 1, 0 < (G z).re) :
    ∃ (c : ℝ) (ν : Measure ℂ), IsFiniteMeasure ν ∧ ν ≠ 0 ∧ ν (sphere 0 1)ᶜ = 0 ∧
      ∀ z ∈ ball (0 : ℂ) 1, G z = c * I + ∫ w, (w + z) / (w - z) ∂ν := by
  set C := (G 0).re with hC
  have hC0 : 0 < C := hpos 0 (mem_ball_self one_pos)
  -- the family of approximating finite measures
  have hfin : ∀ r : ℝ, IsFiniteMeasure (if 0 < r ∧ r < 1 then nuR G r else 0) := fun r => by
    split_ifs with h
    · exact isFiniteMeasure_nuR hG h.1 h.2
    · infer_instance
  let u : ℝ → FiniteMeasure UnitCircle := fun r =>
    ⟨if 0 < r ∧ r < 1 then nuR G r else 0, hfin r⟩
  have hu : ∀ r, (h : 0 < r ∧ r < 1) → ((u r : FiniteMeasure UnitCircle) : Measure UnitCircle) =
      nuR G r := fun r h => by
    show (if 0 < r ∧ r < 1 then nuR G r else 0) = _
    simp [h]
  have hu' : ∀ r, ¬ (0 < r ∧ r < 1) →
      ((u r : FiniteMeasure UnitCircle) : Measure UnitCircle) = 0 := fun r h => by
    show (if 0 < r ∧ r < 1 then nuR G r else 0) = _
    simp [h]
  set K := {μ : FiniteMeasure UnitCircle | μ.mass ≤ C.toNNReal}
  have hK : IsCompact K := isCompact_setOfPred_finiteMeasure_le_of_compactSpace _ _
  have huK : map u (𝓝[<] (1 : ℝ)) ≤ 𝓟 K := by
    rw [le_principal_iff, mem_map]
    filter_upwards with r
    simp only [mem_preimage, K, mem_ofPred_eq]
    by_cases h : 0 < r ∧ r < 1
    · have hm : ((u r).mass : ℝ) = C := by
        have h1 : ((u r).mass : ℝ) = ((u r : Measure UnitCircle) univ).toReal := by
          rw [← FiniteMeasure.ennreal_mass]; rfl
        rw [h1, hu r h]
        exact nuR_real_univ hG hpos h.1 h.2
      rw [← NNReal.coe_le_coe, hm, Real.coe_toNNReal _ hC0.le]
    · have h0 : ((u r).mass : ℝ≥0∞) = 0 := by
        rw [FiniteMeasure.ennreal_mass, hu' r h]; rfl
      rw [ENNReal.coe_eq_zero] at h0
      rw [h0]; positivity
  obtain ⟨ν, -, hcl⟩ := hK.exists_mapClusterPt huK
  -- the cluster point represents `Re G`
  have hrepr : ∀ w ∈ ball (0 : ℂ) 1,
      (G w).re = ∫ ζ, (((ζ : ℂ) + w) / ((ζ : ℂ) - w)).re ∂(ν : Measure UnitCircle) := by
    intro w hw
    have hw1 : ‖w‖ < 1 := by simpa using hw
    have hφ : Continuous fun ζ : UnitCircle => (((ζ : ℂ) + w) / ((ζ : ℂ) - w)).re := by
      refine Complex.continuous_re.comp ((continuous_subtype_val.add continuous_const).div
        (continuous_subtype_val.sub continuous_const) fun ζ => ?_)
      exact sub_ne_zero_of_norm_lt (by rw [norm_unitCircle]; exact hw1)
    let Φ : C(UnitCircle, ℝ) := ⟨_, hφ⟩
    have h1 := hcl.tendsto_comp ((FiniteMeasure.continuous_integral_continuousMap Φ).tendsto ν)
    have h2 : Tendsto (fun r => ∫ ζ, Φ ζ ∂(u r : Measure UnitCircle)) (𝓝[<] 1)
        (𝓝 (G w).re) := by
      have hδ : Tendsto (fun r : ℝ => C * (2 * ‖w‖ * (1 - r) / ((1 - ‖w‖) * (r - ‖w‖))))
          (𝓝[<] 1) (𝓝 0) := by
        have hcont : ContinuousAt (fun r : ℝ => C * (2 * ‖w‖ * (1 - r) /
            ((1 - ‖w‖) * (r - ‖w‖)))) 1 := by
          apply ContinuousAt.mul continuousAt_const
          apply ContinuousAt.div (by fun_prop) (by fun_prop)
          have : 0 < (1 - ‖w‖) * (1 - ‖w‖) := by nlinarith
          exact this.ne'
        have := hcont.tendsto
        simp only [sub_self, mul_zero, zero_div] at this
        exact this.mono_left nhdsWithin_le_nhds
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hδ
      have hev : ∀ᶠ r in 𝓝[<] (1 : ℝ), ‖w‖ < r ∧ r < 1 :=
        Ioo_mem_nhdsLT hw1
      filter_upwards [hev] with r ⟨hwr, hr1⟩
      have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg _) hwr
      rw [hu r ⟨hr0, hr1⟩, Real.norm_eq_abs]
      exact abs_integral_nuR_sub_le hG hpos hr0 hr1 hwr
    exact (eq_of_nhds_neBot (h1.clusterPt.mono h2)).symm
  -- transport to `ℂ`
  set ν' : Measure ℂ := (ν : Measure UnitCircle).map Subtype.val
  have hmeas : Measurable (Subtype.val : UnitCircle → ℂ) := measurable_subtype_coe
  have hν'fin : IsFiniteMeasure ν' := inferInstance
  have hsupp : ν' (sphere 0 1)ᶜ = 0 := by
    rw [Measure.map_apply hmeas isClosed_sphere.measurableSet.compl]
    convert measure_empty (μ := (ν : Measure UnitCircle))
    ext ζ; simp
  have hint : ∀ w ∈ ball (0 : ℂ) 1,
      ∫ ζ, (((ζ : ℂ) + w) / ((ζ : ℂ) - w)).re ∂(ν : Measure UnitCircle) =
        ∫ x, ((x + w) / (x - w)).re ∂ν' := fun w hw => by
    rw [integral_map hmeas.aemeasurable]
    exact (Measurable.aestronglyMeasurable (by fun_prop))
  have hν'0 : ν' ≠ 0 := by
    intro h0
    have h := hrepr 0 (mem_ball_self one_pos)
    rw [hint 0 (mem_ball_self one_pos), h0] at h
    simp at h
    linarith
  -- `G - herglotzIntegral` has vanishing real part, hence is constant
  set f := fun z => G z - herglotzIntegral ν' z
  have hf : DifferentiableOn ℂ f (ball 0 1) :=
    hG.sub (differentiableOn_herglotzIntegral ν' hsupp)
  have hfre : ∀ z ∈ ball (0 : ℂ) 1, (f z).re = 0 := by
    intro z hz
    simp only [f, Complex.sub_re]
    rw [re_herglotzIntegral ν' hsupp hz, hrepr z hz, hint z hz, sub_self]
  have hconst := eqOn_of_re_eq_zero hf hfre
  refine ⟨(f 0).im, ν', hν'fin, hν'0, hsupp, fun z hz => ?_⟩
  have h1 := hconst z hz
  have h2 : f 0 = ((f 0).im : ℂ) * I := by
    apply Complex.ext <;> simp [hfre 0 (mem_ball_self one_pos)]
  rw [← h2, ← h1]
  simp only [f, herglotzIntegral]
  ring

/-- The statement `DF.CaratheodoryRepresentationStatement` (Theorem 1.9.3) holds. -/
theorem caratheodoryRepresentationStatement_holds : CaratheodoryRepresentationStatement := by
  intro G
  constructor
  · rintro ⟨hG, hpos⟩
    exact caratheodory_repr G hG hpos
  · rintro ⟨c, ν, hfin, hν, hsupp, hrep⟩
    obtain ⟨h1, h2⟩ := caratheodory_of_repr c ν hν hsupp
    refine ⟨h1.congr fun z hz => ?_, fun z hz => ?_⟩
    · rw [hrep z hz]; rfl
    · rw [hrep z hz]; exact h2 z hz

end DF
