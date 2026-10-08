/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §4.6: potential-theoretic part of the Thouless formula and its applications
(book pp. 332–336)

This file contains the parts of §4.6 that only depend on a probability measure `k` on `ℝ`
(the density of states measure) and on its logarithmic potential, and not on the ergodic
operator family itself.  In the language of Appendix A.2 the Thouless formula (4.6.3) says
`L(z) = -Φ_{dk}(z)`, so every hypothesis of the form "`L ≥ 0`" or "`L = 0` on `Σ`" is stated
here in terms of `Φ_{dk} = DF.logPotential (DF.toC k)`.

## Main definitions
* `DF.toC k` — the push-forward of a measure on `ℝ` to `ℂ`.

## Main results
* `DF.Subharmonic.eq_of_eq_off_real` — two subharmonic functions on `ℂ` that agree off the real
  axis agree everywhere.  This is the step of the proof of Theorem 4.6.1 (Thouless formula)
  that extends the identity from `ℂ \ ℝ` to `ℝ`; the book uses area means
  (Proposition 4.5.2(d)), we use circle means (the circle meets `ℝ` in at most two points).
* `DF.measure_Ioc_le_of_logPotential_nonpos` and `DF.abs_cdf_sub_le_of_logPotential_nonpos` —
  **Theorem 4.6.3 / Remark 4.6.4** (log-Hölder continuity of the IDS) in abstract form: if
  `Φ_{dk} ≤ 0` on `ℝ` (i.e. `L ≥ 0`) and `dk` is carried by `[-R, R]`, `R ≥ 1`, then
  `|k(E₁) - k(E₂)| ≤ log(|E₁| + |E₂| + R) · (log |E₁ - E₂|⁻¹)⁻¹` for `|E₁ - E₂| < 1/2`.
  With `R = 2 + ‖f‖_∞` this is (4.6.8) with the constant (4.6.9).
* `DF.energy_toC_nonpos`, `DF.one_le_capCompact_of_logPotential_nonpos` — **Lemma 4.6.6**:
  `E(dk) ≤ 0`, hence `Cap(Σ) ≥ 1`.
* `DF.le_mutualEnergy_of_ae_le`, `DF.mutualEnergy_le_of_le` — comparison of mutual energies
  with pointwise bounds on potentials (monotone convergence for the truncated kernels).
* `DF.isEquilibriumMeasure_of_logPotential_eq_zero` — **Theorem 4.6.7** in abstract form: if
  `Φ_{dk} = 0` on `Σ` (i.e. `L = 0` on `Σ`), then `dk` is the equilibrium measure of `Σ`, and
  `Cap(Σ) = 1`.  Only the first half of Frostman's theorem (`Φ_ρ ≤ E(ρ)`) is used, taken from
  `DF.FrostmanStatement` (proved: `DF.isEquilibriumMeasure_of_logPotential_eq_zero'`); the book's appeal to uniqueness of equilibrium measures is replaced by
  the direct verification that `dk` minimizes the energy (uniqueness, from
  `DF.EnergyStrictConvexityStatement`, proved in `AppA/EnergyConvexity.lean`, then gives
  `dk = ρ_Σ`: `DF.eq_of_isEquilibriumMeasure_of_logPotential_eq_zero'`).

## Deviations
* The book states Theorem 4.6.3 for the IDS of an ergodic family; the application to the IDS
  is in `DamanikFillman/Ch4/Thouless.lean`.  We use half-open intervals `(E₁, E₂]` since
  `k(E₂) - k(E₁) = dk((E₁, E₂])`.

## Statements
None introduced here.  `DF.FrostmanStatement` and `DF.EnergyStrictConvexityStatement`
(Appendix A.2) appear as hypotheses; both are proved (`DF.frostmanStatement_holds`,
`DF.energyStrictConvexityStatement_holds`), giving the unconditional versions.
-/
import DamanikFillman.AppA.Equilibrium
import DamanikFillman.AppA.FrostmanMain
import DamanikFillman.AppA.EnergyConvexity
import DamanikFillman.AppA.Subharmonic

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal NNReal Real

namespace DF

/-! ### Subharmonic functions that agree off the real axis -/

lemma circleMap_im_eq (c : ℂ) (r θ : ℝ) : (circleMap c r θ).im = c.im + r * Real.sin θ := by
  simp [circleMap, Complex.exp_ofReal_mul_I_im]

lemma countable_setOf_sin_eq (a : ℝ) : {θ : ℝ | Real.sin θ = a}.Countable := by
  by_cases h : ∃ θ₀, Real.sin θ₀ = a
  · obtain ⟨θ₀, rfl⟩ := h
    have hsub : {θ : ℝ | Real.sin θ = Real.sin θ₀} ⊆
        ⋃ k : ℤ, ({2 * k * π + θ₀, (2 * k + 1) * π - θ₀} : Set ℝ) := by
      intro θ hθ
      obtain ⟨k, hk⟩ := Real.sin_eq_sin_iff.1 (Eq.symm hθ)
      simp only [mem_iUnion, mem_insert_iff, mem_singleton_iff]
      exact ⟨k, hk⟩
    exact (countable_iUnion fun k => (Set.toFinite _).countable).mono hsub
  · push Not at h
    exact Set.countable_empty.mono fun θ hθ => (h θ hθ).elim

/-- Extended circle averages only see the values off the real axis. -/
theorem ecircleAverage_congr_of_im_ne_zero {F G : ℂ → EReal}
    (h : ∀ z : ℂ, z.im ≠ 0 → F z = G z) (c : ℂ) {r : ℝ} (hr : r ≠ 0) :
    ecircleAverage F c r = ecircleAverage G c r := by
  unfold ecircleAverage
  congr 1; funext n
  congr 1
  unfold Real.circleAverage
  congr 1
  apply intervalIntegral.integral_congr_ae
  have hnull : volume {θ : ℝ | (circleMap c r θ).im = 0} = 0 := by
    apply Set.Countable.measure_zero
    refine (countable_setOf_sin_eq (-c.im / r)).mono fun θ hθ => ?_
    simp only [mem_ofPred_eq, circleMap_im_eq] at hθ ⊢
    rw [eq_div_iff hr]; linarith
  rw [ae_iff]
  refine measure_mono_null (fun θ hθ => ?_) hnull
  simp only [mem_ofPred_eq, Classical.not_imp] at hθ ⊢
  obtain ⟨_, hne⟩ := hθ
  by_contra him
  exact hne (by rw [h _ him])

/-- If `F ≤ a` on a circle, then the extended circle average is `≤ a`. -/
lemma ecircleAverage_le_of_le {F : ℂ → EReal} {U : Set ℂ} (hne : ∀ z ∈ U, F z ≠ ⊤)
    (husc : UpperSemicontinuousOn F U) {c : ℂ} {r : ℝ} (hS : sphere c |r| ⊆ U) {a : ℝ}
    (ha : ∀ w ∈ sphere c |r|, F w ≤ a) : ecircleAverage F c r ≤ a := by
  obtain ⟨n, hn⟩ := exists_nat_ge (-a)
  refine (iInf_le _ n).trans ?_
  rw [EReal.coe_le_coe_iff]
  refine Real.circleAverage_mono_on_of_le_circle (circleIntegrable_truncBelow hne husc hS n)
    fun w hw => ?_
  have := truncBelow_mono (n := n) (EReal.coe_ne_top a) (ha w hw)
  rw [truncBelow_coe] at this
  exact this.trans (max_le le_rfl (by linarith))

/-- If two subharmonic functions agree off `ℝ`, then `F ≤ G` everywhere. -/
theorem Subharmonic.le_of_eq_off_real {F G : ℂ → EReal} (hF : Subharmonic F)
    (hG : Subharmonic G) (h : ∀ z : ℂ, z.im ≠ 0 → F z = G z) (c : ℂ) : F c ≤ G c := by
  by_contra hlt
  push Not at hlt
  obtain ⟨a, hGa, haF⟩ := EReal.lt_iff_exists_real_btwn.1 hlt
  have husc := hG.usc c (mem_univ c) (a : EReal) hGa
  rw [nhdsWithin_univ, Metric.eventually_nhds_iff] at husc
  obtain ⟨δ, hδ, hball⟩ := husc
  have hr : (0 : ℝ) < δ / 2 := by positivity
  have h1 := hF.submean c (δ / 2) hr (subset_univ _)
  rw [ecircleAverage_congr_of_im_ne_zero h c hr.ne'] at h1
  have h2 : ecircleAverage G c (δ / 2) ≤ a :=
    ecircleAverage_le_of_le (fun z _ => hG.ne_top z (mem_univ z)) hG.usc (subset_univ _)
      fun w hw => (hball (by rw [mem_sphere, abs_of_pos hr] at hw; rw [hw]; linarith)).le
  exact absurd (h1.trans h2) (not_le.2 haF)

/-- Two subharmonic functions on `ℂ` that agree on `ℂ \ ℝ` agree everywhere (the final step of
the proof of Theorem 4.6.1). -/
theorem Subharmonic.eq_of_eq_off_real {F G : ℂ → EReal} (hF : Subharmonic F)
    (hG : Subharmonic G) (h : ∀ z : ℂ, z.im ≠ 0 → F z = G z) : F = G :=
  funext fun c => le_antisymm (hF.le_of_eq_off_real hG h c)
    (hG.le_of_eq_off_real hF (fun z hz => (h z hz).symm) c)

/-! ### Measures on `ℝ` viewed in `ℂ` -/

/-- The push-forward of a measure on `ℝ` to `ℂ` under `x ↦ (x : ℂ)`. -/
def toC (k : Measure ℝ) : Measure ℂ := k.map (fun x : ℝ => (x : ℂ))

lemma measurable_ofReal' : Measurable (fun x : ℝ => (x : ℂ)) := Complex.continuous_ofReal.measurable

instance (k : Measure ℝ) [IsProbabilityMeasure k] : IsProbabilityMeasure (toC k) := by
  unfold toC; infer_instance

instance (k : Measure ℝ) [IsFiniteMeasure k] : IsFiniteMeasure (toC k) := by
  unfold toC; infer_instance

lemma toC_compl_image {k : Measure ℝ} {S : Set ℝ} (hS : IsCompact S) (hk : k Sᶜ = 0) :
    toC k ((fun x : ℝ => (x : ℂ)) '' S)ᶜ = 0 := by
  have hK : IsCompact ((fun x : ℝ => (x : ℂ)) '' S) := hS.image Complex.continuous_ofReal
  rw [toC, Measure.map_apply measurable_ofReal' hK.isClosed.measurableSet.compl]
  convert hk using 2
  ext x; simp [Complex.ofReal_injective.eq_iff]

lemma isCompact_image_ofReal {S : Set ℝ} (hS : IsCompact S) :
    IsCompact ((fun x : ℝ => (x : ℂ)) '' S) := hS.image Complex.continuous_ofReal

lemma toC_mem_M1 {k : Measure ℝ} [IsProbabilityMeasure k] {S : Set ℝ} (hS : IsCompact S)
    (hk : k Sᶜ = 0) : toC k ∈ M1 ((fun x : ℝ => (x : ℂ)) '' S) :=
  ⟨inferInstance, toC_compl_image hS hk⟩

lemma integrable_norm_toC {k : Measure ℝ} [IsFiniteMeasure k] {S : Set ℝ} (hS : IsCompact S)
    (hk : k Sᶜ = 0) : Integrable (fun w => ‖w‖) (toC k) :=
  integrable_norm_of_compact (isCompact_image_ofReal hS) (toC_compl_image hS hk)

/-- The truncated potentials of `toC k`, computed on `ℝ`. -/
lemma integral_logKer_toC (k : Measure ℝ) (N : ℕ) (z : ℂ) :
    ∫ w, logKer N (z - w) ∂(toC k) = ∫ x, logKer N (z - (x : ℂ)) ∂k := by
  rw [toC, integral_map (f := fun w => logKer N (z - w)) measurable_ofReal'.aemeasurable
    ((continuous_logKer N).comp (continuous_const.sub continuous_id)).aestronglyMeasurable]

/-! ### Theorem 4.6.3: log-Hölder continuity -/

/-- **Theorem 4.6.3** (abstract form, one interval): if `dk` is a probability measure carried by
`[-R, R]` with `R ≥ 1`, and `Φ_{dk}(E₁) ≤ 0` (i.e. `L(E₁) ≥ 0` via the Thouless formula), then
for `E₁ < E₂ < E₁ + 1/2`,
`dk((E₁, E₂]) ≤ log(|E₁| + R) / log (E₂ - E₁)⁻¹`. -/
theorem measure_Ioc_le_of_logPotential_nonpos (k : Measure ℝ) [IsProbabilityMeasure k] {R : ℝ}
    (hR : 1 ≤ R) (hk : k (Icc (-R) R)ᶜ = 0) {E₁ E₂ : ℝ} (h12 : E₁ < E₂)
    (h12' : E₂ - E₁ < 1 / 2) (hL : logPotential (toC k) (E₁ : ℂ) ≤ 0) :
    (k (Ioc E₁ E₂)).toReal ≤ Real.log (|E₁| + R) / Real.log (E₂ - E₁)⁻¹ := by
  set δ := E₂ - E₁ with hδ
  have hδpos : 0 < δ := sub_pos.2 h12
  set C := Real.log (|E₁| + R) with hC
  have hC0 : 0 ≤ C := Real.log_nonneg (by have := abs_nonneg E₁; linarith)
  have hlogδ : Real.log δ < 0 := Real.log_neg hδpos (by linarith)
  obtain ⟨N, hN⟩ : ∃ N : ℕ, Real.exp (-(N : ℝ)) ≤ δ := by
    obtain ⟨N, hN⟩ := exists_nat_gt (-Real.log δ)
    exact ⟨N, by rw [← Real.exp_log hδpos]; exact Real.exp_le_exp.2 (by linarith)⟩
  -- the truncated potential at level `N`
  have hN' : ∫ x, logKer N ((E₁ : ℂ) - (x : ℂ)) ∂k ≤ 0 := by
    have := (le_iSup (fun N : ℕ => ((∫ w, logKer N ((E₁ : ℂ) - w) ∂(toC k) : ℝ) : EReal)) N).trans
      hL
    rw [integral_logKer_toC] at this
    exact_mod_cast this
  set g : ℝ → ℝ := fun x => Real.log (max ‖(E₁ : ℂ) - (x : ℂ)‖ (Real.exp (-(N : ℝ))))
  have hgK : ∀ x : ℝ, logKer N ((E₁ : ℂ) - (x : ℂ)) = -g x := fun x => rfl
  have hae : ∀ᵐ x ∂k, x ∈ Icc (-R) R :=
    measure_eq_zero_iff_ae_notMem.1 hk |>.mono fun x hx => by simpa using hx
  set h : ℝ → ℝ := fun x => C + (Ioc E₁ E₂).indicator (fun _ => Real.log δ - C) x
  have hgh : ∀ᵐ x ∂k, g x ≤ h x := by
    filter_upwards [hae] with x hx
    have hnorm : ‖(E₁ : ℂ) - (x : ℂ)‖ = |E₁ - x| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hpos : 0 < max ‖(E₁ : ℂ) - (x : ℂ)‖ (Real.exp (-(N : ℝ))) :=
      lt_max_of_lt_right (Real.exp_pos _)
    simp only [g, h]
    by_cases hxI : x ∈ Ioc E₁ E₂
    · rw [indicator_of_mem hxI]
      ring_nf
      refine Real.log_le_log hpos (max_le ?_ hN)
      rw [hnorm, abs_sub_comm, abs_of_pos (by linarith [hxI.1])]
      linarith [hxI.2]
    · rw [indicator_of_notMem hxI, add_zero]
      refine Real.log_le_log hpos (max_le ?_ ?_)
      · rw [hnorm]
        have := abs_sub E₁ x
        have : |x| ≤ R := abs_le.2 ⟨hx.1, hx.2⟩
        linarith
      · have : Real.exp (-(N : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (by simp)
        have := abs_nonneg E₁; linarith
  have hgint : Integrable g k := by
    have : Integrable (fun x : ℝ => logKer N ((E₁ : ℂ) - (x : ℂ))) k := by
      refine (integrable_const ((N : ℝ) + |E₁| + R)).mono'
        ((continuous_logKer N).comp
          (continuous_const.sub Complex.continuous_ofReal)).aestronglyMeasurable ?_
      filter_upwards [hae] with x hx
      rw [Real.norm_eq_abs]
      refine (abs_logKer_le N _).trans ?_
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      have := abs_sub E₁ x
      have : |x| ≤ R := abs_le.2 ⟨hx.1, hx.2⟩
      linarith
    simpa [hgK] using this.neg
  have hhint : Integrable h k :=
    (integrable_const C).add ((integrable_const _).indicator measurableSet_Ioc)
  have hint_h : ∫ x, h x ∂k = C + (Real.log δ - C) * (k (Ioc E₁ E₂)).toReal := by
    simp only [h]
    rw [integral_add (integrable_const C) ((integrable_const _).indicator measurableSet_Ioc),
      integral_const, integral_indicator_const _ measurableSet_Ioc]
    simp [measureReal_def, mul_comm]
  have h0g : 0 ≤ ∫ x, g x ∂k := by
    have : ∫ x, logKer N ((E₁ : ℂ) - (x : ℂ)) ∂k = -∫ x, g x ∂k := by
      simp_rw [hgK]; exact integral_neg _
    linarith
  have key : 0 ≤ C + (Real.log δ - C) * (k (Ioc E₁ E₂)).toReal :=
    hint_h ▸ h0g.trans (integral_mono_ae hgint hhint hgh)
  set p := (k (Ioc E₁ E₂)).toReal
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  have hlog_inv : Real.log δ⁻¹ = -Real.log δ := Real.log_inv δ
  rw [hlog_inv, le_div_iff₀ (by linarith)]
  nlinarith

/-- The distribution function `E ↦ dk((-∞, E])` of a finite measure on `ℝ`. -/
def cdfR (k : Measure ℝ) (E : ℝ) : ℝ := (k (Iic E)).toReal

lemma cdfR_sub {k : Measure ℝ} [IsFiniteMeasure k] {E₁ E₂ : ℝ} (h : E₁ ≤ E₂) :
    cdfR k E₂ - cdfR k E₁ = (k (Ioc E₁ E₂)).toReal := by
  unfold cdfR
  have hI : Ioc E₁ E₂ = Iic E₂ \ Iic E₁ := by ext; simp [and_comm]
  rw [hI, measure_sdiff (Iic_subset_Iic.2 h) measurableSet_Iic.nullMeasurableSet
    (measure_ne_top _ _), ENNReal.toReal_sub_of_le (measure_mono (Iic_subset_Iic.2 h))
    (measure_ne_top _ _)]

/-- **Theorem 4.6.3 with Remark 4.6.4** (abstract form): if `dk` is a probability measure on
`[-R, R]`, `R ≥ 1`, whose potential is `≤ 0` on `ℝ` (i.e. `L ≥ 0` on `ℝ`), then its distribution
function is log-Hölder continuous:
`|k(E₁) - k(E₂)| ≤ log(|E₁| + |E₂| + R) · (log |E₁ - E₂|⁻¹)⁻¹` for `0 < |E₁ - E₂| < 1/2`. -/
theorem abs_cdfR_sub_le_of_logPotential_nonpos (k : Measure ℝ) [IsProbabilityMeasure k]
    {R : ℝ} (hR : 1 ≤ R) (hk : k (Icc (-R) R)ᶜ = 0)
    (hL : ∀ x : ℝ, logPotential (toC k) (x : ℂ) ≤ 0) {E₁ E₂ : ℝ} (hne : E₁ ≠ E₂)
    (h12 : |E₁ - E₂| < 1 / 2) :
    |cdfR k E₁ - cdfR k E₂| ≤ Real.log (|E₁| + |E₂| + R) * (Real.log |E₁ - E₂|⁻¹)⁻¹ := by
  -- reduce to `a < b`
  have main : ∀ a b : ℝ, a < b → b - a < 1 / 2 →
      |cdfR k a - cdfR k b| ≤ Real.log (|a| + |b| + R) * (Real.log |a - b|⁻¹)⁻¹ := by
    intro a b hab hab'
    have h1 := measure_Ioc_le_of_logPotential_nonpos k hR hk hab hab' (hL a)
    have hpos : 0 < Real.log (b - a)⁻¹ := by
      rw [Real.log_inv]; have := Real.log_neg (sub_pos.2 hab) (by linarith); linarith
    rw [abs_sub_comm (cdfR k a), cdfR_sub hab.le, abs_of_nonneg ENNReal.toReal_nonneg,
      abs_sub_comm a b, abs_of_pos (sub_pos.2 hab), ← div_eq_mul_inv]
    refine h1.trans (div_le_div_of_nonneg_right ?_ hpos.le)
    exact Real.log_le_log (by have := abs_nonneg a; linarith)
      (by have := abs_nonneg b; linarith)
  rcases lt_or_gt_of_ne hne with h | h
  · exact main E₁ E₂ h (by rw [abs_sub_comm, abs_of_pos (sub_pos.2 h)] at h12; exact h12)
  · have := main E₂ E₁ h (by rw [abs_of_pos (sub_pos.2 h)] at h12; exact h12)
    rwa [abs_sub_comm, add_comm |E₂|, abs_sub_comm E₂] at this

/-! ### Lemma 4.6.6 and Theorem 4.6.7: energy, capacity, equilibrium measure -/

/-- `potT μ N z ≤ Φ_μ(z)`. -/
lemma integral_logKer_le_logPotential (μ : Measure ℂ) (N : ℕ) (z : ℂ) :
    ((∫ w, logKer N (z - w) ∂μ : ℝ) : EReal) ≤ logPotential μ z :=
  le_iSup (fun N : ℕ => ((∫ w, logKer N (z - w) ∂μ : ℝ) : EReal)) N

/-- The truncated potentials are integrable against finite measures with finite first moment. -/
lemma integrable_integral_logKer {μ ν : Measure ℂ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : Integrable (fun w => ‖w‖) μ) (hν : Integrable (fun w => ‖w‖) ν) (N : ℕ) :
    Integrable (fun z => ∫ w, logKer N (z - w) ∂μ) ν := by
  set m := μ.real univ
  set M := ∫ w, ‖w‖ ∂μ
  refine ((integrable_const ((N : ℝ) * m + M)).add (hν.const_mul m)).mono'
    (continuous_potTrunc hμ N).aestronglyMeasurable (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs]
  refine (abs_integral_le_integral_abs).trans ?_
  have hb : ∫ w, |logKer N (z - w)| ∂μ ≤ ∫ w, ((N : ℝ) + ‖z‖ + ‖w‖) ∂μ :=
    integral_mono (integrable_logKer hμ N z).abs
      (((integrable_const _).add hμ)) (fun w => abs_logKer_sub_le N z w)
  refine hb.trans (le_of_eq ?_)
  rw [integral_add (integrable_const _) hμ, integral_const, smul_eq_mul]
  simp only [Pi.add_apply, m, M]; ring

/-- If `Φ_μ ≤ c` everywhere then `∫ Φ_μ dν ≤ c` for every probability measure `ν` with finite
first moment. -/
theorem mutualEnergy_le_of_le {μ ν : Measure ℂ} [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun w => ‖w‖) μ) (hν : Integrable (fun w => ‖w‖) ν) {c : ℝ}
    (h : ∀ᵐ z ∂ν, logPotential μ z ≤ c) : mutualEnergy μ ν ≤ c := by
  refine iSup_le fun N => ?_
  rw [EReal.coe_le_coe_iff]
  have : ∫ z, ∫ w, logKer N (z - w) ∂μ ∂ν ≤ ∫ _z, c ∂ν := by
    refine integral_mono_ae (integrable_integral_logKer hμ hν N) (integrable_const c) ?_
    filter_upwards [h] with z hz
    exact_mod_cast (integral_logKer_le_logPotential μ N z).trans hz
  simpa using this

/-- If `Φ_μ ≥ c` holds `ν`-a.e., then `∫ Φ_μ dν ≥ c` (monotone convergence for the truncated
potentials). -/
theorem le_mutualEnergy_of_ae_le {μ ν : Measure ℂ} [IsFiniteMeasure μ] [IsProbabilityMeasure ν]
    (hμ : Integrable (fun w => ‖w‖) μ) (hν : Integrable (fun w => ‖w‖) ν) {c : ℝ}
    (h : ∀ᵐ z ∂ν, (c : EReal) ≤ logPotential μ z) : (c : EReal) ≤ mutualEnergy μ ν := by
  set P : ℕ → ℂ → ℝ := fun N z => ∫ w, logKer N (z - w) ∂μ
  set g : ℕ → ℂ → ℝ := fun N z => min (P N z) c
  set m := μ.real univ
  set M := ∫ w, ‖w‖ ∂μ
  have hm0 : 0 ≤ m := measureReal_nonneg
  -- lower bound for the truncated potentials
  have hlow : ∀ N z, -(m * ‖z‖ + M) ≤ P N z := by
    intro N z
    have : ∫ w, -(‖z‖ + ‖w‖) ∂μ ≤ P N z := by
      refine integral_mono ((integrable_const _).add hμ).neg (integrable_logKer hμ N z)
        (fun w => ?_)
      have := neg_norm_le_logKer N (z - w)
      have := norm_sub_le z w
      linarith
    rw [integral_neg, integral_add (integrable_const _) hμ, integral_const, smul_eq_mul] at this
    simpa [m, M, mul_comm] using this
  have hbound : ∀ N z, ‖g N z‖ ≤ |c| + (m * ‖z‖ + M) := by
    intro N z
    rw [Real.norm_eq_abs, abs_le]
    have hM0 : 0 ≤ M := integral_nonneg fun _ => norm_nonneg _
    constructor
    · have := hlow N z
      have := neg_abs_le c
      have := abs_nonneg c
      have : 0 ≤ m * ‖z‖ := by positivity
      exact le_min (by linarith) (by linarith)
    · have := le_abs_self c
      have : 0 ≤ m * ‖z‖ := by positivity
      exact (min_le_right _ _).trans (by linarith)
  have hlim : Tendsto (fun N => ∫ z, g N z ∂ν) atTop (𝓝 (∫ _z, c ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence (fun z => |c| + (m * ‖z‖ + M))
      (fun N => ((continuous_potTrunc hμ N).min continuous_const).aestronglyMeasurable)
      ((integrable_const _).add ((hν.const_mul m).add (integrable_const _)))
      (fun N => Eventually.of_forall (hbound N)) ?_
    filter_upwards [h] with z hz
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hlt : ((c - ε : ℝ) : EReal) < logPotential μ z :=
      lt_of_lt_of_le (EReal.coe_lt_coe_iff.2 (by linarith)) hz
    obtain ⟨N₀, hN₀⟩ := lt_iSup_iff.1 hlt
    refine ⟨N₀, fun N hN => ?_⟩
    have h1 : c - ε < P N₀ z := EReal.coe_lt_coe_iff.1 hN₀
    have h2 : P N₀ z ≤ P N z := potTrunc_mono hμ z hN
    rw [Real.dist_eq, abs_lt]
    constructor
    · have : c - ε < g N z := lt_min (by linarith) (by linarith)
      linarith
    · have : g N z ≤ c := min_le_right _ _
      linarith
  rw [integral_const, smul_eq_mul, probReal_univ, one_mul] at hlim
  refine le_of_tendsto' ((continuous_coe_real_ereal.tendsto _).comp hlim) fun N => ?_
  refine le_trans ?_ (le_iSup (fun N : ℕ => ((∫ z, ∫ w, logKer N (z - w) ∂μ ∂ν : ℝ) : EReal)) N)
  simp only [Function.comp_apply, EReal.coe_le_coe_iff]
  exact integral_mono (((integrable_const _).add ((hν.const_mul m).add
    (integrable_const _))).mono' ((continuous_potTrunc hμ N).min
      continuous_const).aestronglyMeasurable (Eventually.of_forall (hbound N)))
    (integrable_integral_logKer hμ hν N) (fun z => min_le_left _ _)

/-- **Lemma 4.6.6** (abstract form): if the potential of a probability measure `μ` is `≤ 0`
`μ`-a.e. (by the Thouless formula, `Φ_{dk} = -L ≤ 0`), then `E(μ) ≤ 0`. -/
theorem energy_nonpos_of_ae_logPotential_nonpos {μ : Measure ℂ} [IsProbabilityMeasure μ]
    (hμ : Integrable (fun w => ‖w‖) μ) (h : ∀ᵐ z ∂μ, logPotential μ z ≤ 0) : energy μ ≤ 0 := by
  have := mutualEnergy_le_of_le hμ hμ (c := 0) (by simpa using h)
  simpa [energy] using this

/-- **Lemma 4.6.6**: if `dk` is carried by the compact set `S ⊆ ℝ` and `Φ_{dk} ≤ 0` on `S`
(i.e. `L ≥ 0`), then `E(dk) ≤ 0`. -/
theorem energy_toC_nonpos {k : Measure ℝ} [IsProbabilityMeasure k] {S : Set ℝ}
    (hS : IsCompact S) (hk : k Sᶜ = 0) (hL : ∀ x ∈ S, logPotential (toC k) (x : ℂ) ≤ 0) :
    energy (toC k) ≤ 0 := by
  refine energy_nonpos_of_ae_logPotential_nonpos (integrable_norm_toC hS hk) ?_
  have := measure_eq_zero_iff_ae_notMem.1 (toC_compl_image hS hk)
  filter_upwards [this] with z hz
  simp only [mem_compl_iff, not_not, mem_image] at hz
  obtain ⟨x, hx, rfl⟩ := hz
  exact hL x hx

/-- **Lemma 4.6.6**: `Cap(Σ) ≥ 1`. -/
theorem one_le_capCompact_of_logPotential_nonpos {k : Measure ℝ} [IsProbabilityMeasure k]
    {S : Set ℝ} (hS : IsCompact S) (hk : k Sᶜ = 0)
    (hL : ∀ x ∈ S, logPotential (toC k) (x : ℂ) ≤ 0) :
    1 ≤ capCompact ((fun x : ℝ => (x : ℂ)) '' S) := by
  have h := expNeg_energy_le_capCompact (toC_mem_M1 hS hk)
  refine le_trans ?_ h
  have := expNeg_antitone (energy_toC_nonpos hS hk hL)
  have h0 : expNeg 0 = 1 := by rw [← EReal.coe_zero, expNeg_coe]; simp
  rwa [h0] at this

/-- **Theorem 4.6.7** (abstract form): if the potential of the probability measure `dk`
(carried by the compact `S ⊆ ℝ`) vanishes on `S` — by the Thouless formula this is
`L = 0` on `Σ` — then `dk` is an equilibrium measure of `S`, and `Cap(S) = 1`.  Uses the first
half of Frostman's theorem (Theorem A.2.8). -/
theorem isEquilibriumMeasure_of_logPotential_eq_zero (hFrost : FrostmanStatement)
    {k : Measure ℝ} [IsProbabilityMeasure k] {S : Set ℝ} (hS : IsCompact S) (hk : k Sᶜ = 0)
    (hL : ∀ x ∈ S, logPotential (toC k) (x : ℂ) = 0) :
    IsEquilibriumMeasure ((fun x : ℝ => (x : ℂ)) '' S) (toC k) ∧
      capCompact ((fun x : ℝ => (x : ℂ)) '' S) = 1 := by
  set K := (fun x : ℝ => (x : ℂ)) '' S
  have hK : IsCompact K := isCompact_image_ofReal hS
  have hkM : toC k ∈ M1 K := toC_mem_M1 hS hk
  have hkint := integrable_norm_toC hS hk
  have hE : energy (toC k) ≤ 0 := energy_toC_nonpos hS hk fun x hx => (hL x hx).le
  have hcap : capCompact K ≠ 0 := by
    have := one_le_capCompact_of_logPotential_nonpos hS hk fun x hx => (hL x hx).le
    exact (lt_of_lt_of_le one_pos this).ne'
  obtain ⟨ρ, hρ⟩ := exists_isEquilibriumMeasure hK hcap
  have : IsProbabilityMeasure ρ := hρ.1.1
  have hρint : Integrable (fun w => ‖w‖) ρ := integrable_norm_of_compact hK hρ.1.2
  have hρfin : energy ρ ≠ ⊤ := hρ.energy_ne_top hcap
  set e := (energy ρ).toReal
  have he : energy ρ = (e : EReal) := (EReal.coe_toReal hρfin (energy_ne_bot ρ)).symm
  -- `∫ Φ_ρ dk ≤ E(ρ)` by Frostman (i)
  have h1 : mutualEnergy ρ (toC k) ≤ e :=
    mutualEnergy_le_of_le hρint hkint (Eventually.of_forall fun z =>
      he ▸ (hFrost K ρ hK hcap hρ).1 z)
  -- `∫ Φ_k dρ ≥ 0` since `Φ_k = 0` on `K`
  have h2 : ((0 : ℝ) : EReal) ≤ mutualEnergy (toC k) ρ := by
    refine le_mutualEnergy_of_ae_le hkint hρint ?_
    have := measure_eq_zero_iff_ae_notMem.1 hρ.1.2
    filter_upwards [this] with z hz
    simp only [mem_compl_iff, not_not, K, mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    rw [hL x hx]; rfl
  rw [mutualEnergy_comm hkint hρint] at h2
  have he0 : (0 : EReal) ≤ energy ρ := by
    rw [he]; exact_mod_cast (EReal.coe_le_coe_iff.1 (h2.trans h1))
  have hmin : ∀ ν ∈ M1 K, energy (toC k) ≤ energy ν := fun ν hν =>
    hE.trans (he0.trans (hρ.2 ν hν))
  have hE0 : energy (toC k) = 0 := le_antisymm hE (he0.trans (hρ.2 _ hkM))
  refine ⟨⟨hkM, hmin⟩, ?_⟩
  rw [IsEquilibriumMeasure.capCompact_eq ⟨hkM, hmin⟩, hE0, ← EReal.coe_zero, expNeg_coe]
  simp

/-- **Theorem 4.6.7**: if `L = 0` on `Σ`, then `dk = dρ_Σ` (using uniqueness of equilibrium
measures, which rests on `EnergyStrictConvexityStatement`, Prop. A.2.5). -/
theorem eq_of_isEquilibriumMeasure_of_logPotential_eq_zero (hFrost : FrostmanStatement)
    (hconv : EnergyStrictConvexityStatement) {k : Measure ℝ} [IsProbabilityMeasure k]
    {S : Set ℝ} (hS : IsCompact S) (hk : k Sᶜ = 0)
    (hL : ∀ x ∈ S, logPotential (toC k) (x : ℂ) = 0) {ρ : Measure ℂ}
    (hρ : IsEquilibriumMeasure ((fun x : ℝ => (x : ℂ)) '' S) ρ) : toC k = ρ := by
  obtain ⟨h1, h2⟩ := isEquilibriumMeasure_of_logPotential_eq_zero hFrost hS hk hL
  exact IsEquilibriumMeasure.unique hconv (isCompact_image_ofReal hS) (by rw [h2]; simp) h1 hρ

/-- **Theorem 4.6.7** (abstract form), unconditional: Frostman's theorem is
`DF.frostmanStatement_holds`. -/
theorem isEquilibriumMeasure_of_logPotential_eq_zero' {k : Measure ℝ} [IsProbabilityMeasure k]
    {S : Set ℝ} (hS : IsCompact S) (hk : k Sᶜ = 0)
    (hL : ∀ x ∈ S, logPotential (toC k) (x : ℂ) = 0) :
    IsEquilibriumMeasure ((fun x : ℝ => (x : ℂ)) '' S) (toC k) ∧
      capCompact ((fun x : ℝ => (x : ℂ)) '' S) = 1 :=
  isEquilibriumMeasure_of_logPotential_eq_zero frostmanStatement_holds hS hk hL

/-- **Theorem 4.6.7**, unconditional: if `L = 0` on `Σ`, then `dk = dρ_Σ`. -/
theorem eq_of_isEquilibriumMeasure_of_logPotential_eq_zero' {k : Measure ℝ}
    [IsProbabilityMeasure k] {S : Set ℝ} (hS : IsCompact S) (hk : k Sᶜ = 0)
    (hL : ∀ x ∈ S, logPotential (toC k) (x : ℂ) = 0) {ρ : Measure ℂ}
    (hρ : IsEquilibriumMeasure ((fun x : ℝ => (x : ℂ)) '' S) ρ) : toC k = ρ :=
  eq_of_isEquilibriumMeasure_of_logPotential_eq_zero frostmanStatement_holds
    energyStrictConvexityStatement_holds hS hk hL hρ

end DF
