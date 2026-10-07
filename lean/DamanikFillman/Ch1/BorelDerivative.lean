/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators, I*,
§1.9.1 (pp. 79–84): derivatives of measures and their relation to the Poisson integral.

# Main definitions

* `DF.ballRatio μ E ε = μ((E - ε, E + ε)) / (2ε)`;
* `DF.upperDeriv μ E`, `DF.lowerDeriv μ E` — the upper / lower derivatives `D^±_μ(E)`
  ((1.9.2), (1.9.3)), valued in `ℝ≥0∞`;
* `DF.HasMeasDeriv μ E d` — the symmetric derivative `D_μ(E)` exists and equals `d ∈ [0, ∞]`.

# Main results

* `DF.ae_hasMeasDeriv_rnDeriv` — Theorem 1.9.1(a): Lebesgue-a.e. `D_μ` exists, is finite and
  equals the Radon–Nikodym derivative of `μ` w.r.t. Lebesgue measure (so (1.9.4) holds with
  Mathlib's Lebesgue decomposition `μ = μ.singularPart vol + vol.withDensity (μ.rnDeriv vol)`);
* `DF.singularPart_compl_derivInfSet` — Theorem 1.9.1(b): `{D_μ = ∞}` supports `μ_s`;
* `DF.acPart_compl_derivFinPosSet` — Theorem 1.9.1(c): `{0 < D_μ < ∞}` supports `μ_ac`;
* `DF.ae_exists_hasMeasDeriv` — Theorem 1.9.1(d);
* `DF.lowerDeriv_le_liminf_poisson`, `DF.limsup_poisson_le_upperDeriv` — inequality (1.9.20)
  of Theorem 1.9.4(a), for every `E`;
* `DF.tendsto_poisson_of_hasMeasDeriv` — (1.9.22): if `D_μ(E)` exists then
  `π⁻¹ Im F_μ(E + iε) → D_μ(E)`.

The covering arguments of the book (Vitali, Exercise 1.9.1) are replaced by Mathlib's
Besicovitch differentiation theorem `Besicovitch.ae_tendsto_rnDeriv`.

# Deviations

* Theorem 1.9.1 is stated for locally finite measures as in the book; the Poisson-integral
  results are stated for finite measures.
-/
import DamanikFillman.Ch1.BorelTransform

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace DF

/-! ## Derivatives of measures -/

/-- The symmetric ratio `μ((E - ε, E + ε)) / (2ε)`. -/
def ballRatio (μ : Measure ℝ) (E ε : ℝ) : ℝ≥0∞ := μ (ball E ε) / ENNReal.ofReal (2 * ε)

/-- The upper derivative `D^+_μ(E)` (1.9.2). -/
def upperDeriv (μ : Measure ℝ) (E : ℝ) : ℝ≥0∞ := limsup (ballRatio μ E) (𝓝[>] 0)

/-- The lower derivative `D^-_μ(E)` (1.9.3). -/
def lowerDeriv (μ : Measure ℝ) (E : ℝ) : ℝ≥0∞ := liminf (ballRatio μ E) (𝓝[>] 0)

/-- The derivative `D_μ(E)` exists (as an element of `[0, ∞]`) and equals `d`. -/
def HasMeasDeriv (μ : Measure ℝ) (E : ℝ) (d : ℝ≥0∞) : Prop :=
  Tendsto (ballRatio μ E) (𝓝[>] 0) (𝓝 d)

lemma HasMeasDeriv.lowerDeriv_eq {μ : Measure ℝ} {E : ℝ} {d : ℝ≥0∞} (h : HasMeasDeriv μ E d) :
    lowerDeriv μ E = d := h.liminf_eq

lemma HasMeasDeriv.upperDeriv_eq {μ : Measure ℝ} {E : ℝ} {d : ℝ≥0∞} (h : HasMeasDeriv μ E d) :
    upperDeriv μ E = d := h.limsup_eq

lemma lowerDeriv_le_upperDeriv (μ : Measure ℝ) (E : ℝ) : lowerDeriv μ E ≤ upperDeriv μ E :=
  liminf_le_limsup

/-- Passing from closed balls to open balls in the differentiation of measures. -/
lemma hasMeasDeriv_of_closedBall {μ : Measure ℝ} {E : ℝ} {L : ℝ≥0∞}
    (h : Tendsto (fun r => μ (closedBall E r) / ENNReal.ofReal (2 * r)) (𝓝[>] 0) (𝓝 L)) :
    HasMeasDeriv μ E L := by
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
  · apply ENNReal.le_of_forall_lt_one_mul_le
    intro a ha
    rcases eq_or_ne a 0 with rfl | ha0
    · simp
    have ha' : a ≠ ∞ := ne_top_of_lt ha
    set η := a.toReal with hη
    have hηpos : 0 < η := ENNReal.toReal_pos ha0 ha'
    have hη1 : η < 1 := by
      have := ENNReal.toReal_strict_mono ENNReal.one_ne_top ha; simpa using this
    have hηa : ENNReal.ofReal η = a := ENNReal.ofReal_toReal ha'
    have hcomp : Tendsto (fun r : ℝ => η * r) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have := (continuous_const_mul η).tendsto 0
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact mul_pos hηpos hr
    have h2 := (ENNReal.Tendsto.const_mul (h.comp hcomp) (Or.inr ha'))
    rw [← h2.liminf_eq]
    refine liminf_le_liminf ?_
    · filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
      simp only [Function.comp_apply, ballRatio]
      have hsub : closedBall E (η * r) ⊆ ball E r :=
        closedBall_subset_ball (by nlinarith)
      calc a * (μ (closedBall E (η * r)) / ENNReal.ofReal (2 * (η * r)))
          = μ (closedBall E (η * r)) / ENNReal.ofReal (2 * r) := by
            rw [show 2 * (η * r) = η * (2 * r) by ring, ENNReal.ofReal_mul hηpos.le, hηa,
              ← mul_div_assoc, ENNReal.mul_div_mul_left _ _ ha0 ha']
        _ ≤ μ (ball E r) / ENNReal.ofReal (2 * r) := by gcongr
  · rw [← h.limsup_eq]
    refine limsup_le_limsup ?_
    · filter_upwards with r
      simp only [ballRatio]
      gcongr
      exact ball_subset_closedBall

lemma volume_closedBall_ofReal (E r : ℝ) :
    volume (closedBall E r) = ENNReal.ofReal (2 * r) := Real.volume_closedBall E r

/-- Theorem 1.9.1(a): for Lebesgue-a.e. `E`, `D_μ(E)` exists, is finite, and equals the
Radon–Nikodym derivative `dμ_ac/dE (E)`.  Together with Mathlib's Lebesgue decomposition
`μ = μ.singularPart volume + volume.withDensity (μ.rnDeriv volume)` this is (1.9.4). -/
theorem ae_hasMeasDeriv_rnDeriv (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] :
    ∀ᵐ E ∂volume, HasMeasDeriv μ E (μ.rnDeriv volume E) ∧ μ.rnDeriv volume E < ∞ := by
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv μ volume, Measure.rnDeriv_lt_top μ volume]
    with E hE hlt
  refine ⟨hasMeasDeriv_of_closedBall ?_, hlt⟩
  simpa only [volume_closedBall_ofReal] using hE

/-- The set `Q_∞ = {E : D_μ(E) = ∞}`. -/
def derivInfSet (μ : Measure ℝ) : Set ℝ := {E | HasMeasDeriv μ E ∞}

/-- The set `Q_f = {E : D_μ(E) ∈ (0, ∞)}`. -/
def derivFinPosSet (μ : Measure ℝ) : Set ℝ :=
  {E | ∃ d : ℝ≥0∞, HasMeasDeriv μ E d ∧ 0 < d ∧ d < ∞}

/-- `μ_s`-a.e., the derivative of `μ` is `+∞`. -/
theorem ae_singularPart_hasMeasDeriv_top (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] :
    ∀ᵐ E ∂(μ.singularPart volume), HasMeasDeriv μ E ∞ := by
  set s := μ.singularPart volume
  have h0 : volume.rnDeriv s =ᵐ[s] 0 :=
    Measure.rnDeriv_eq_zero_of_mutuallySingular
      (Measure.mutuallySingular_singularPart μ volume).symm Measure.AbsolutelyContinuous.rfl
  filter_upwards [Besicovitch.ae_tendsto_rnDeriv volume s, h0] with E hE hE0
  rw [hE0, Pi.zero_apply] at hE
  have hinv := tendsto_inv_iff.2 hE
  rw [ENNReal.inv_zero] at hinv
  have hs : Tendsto (fun r => s (closedBall E r) / ENNReal.ofReal (2 * r)) (𝓝[>] 0) (𝓝 ∞) := by
    refine hinv.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r (hr : 0 < r)
    simp only [volume_closedBall_ofReal]
    rw [ENNReal.inv_div (Or.inr ENNReal.ofReal_ne_top)
      (Or.inr (by simpa using (by linarith : (0 : ℝ) < 2 * r)))]
  refine hasMeasDeriv_of_closedBall (tendsto_nhds_top_mono hs ?_)
  filter_upwards with r
  gcongr
  exact Measure.singularPart_le μ volume

/-- Theorem 1.9.1(b): `Q_∞ = {D_μ = ∞}` is a support of the singular part of `μ`. -/
theorem singularPart_compl_derivInfSet (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] :
    μ.singularPart volume (derivInfSet μ)ᶜ = 0 :=
  ae_singularPart_hasMeasDeriv_top μ

/-- Theorem 1.9.1(c): `Q_f = {0 < D_μ < ∞}` is a support of the absolutely continuous part
`μ_ac = volume.withDensity (μ.rnDeriv volume)`. -/
theorem acPart_compl_derivFinPosSet (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] :
    volume.withDensity (μ.rnDeriv volume) (derivFinPosSet μ)ᶜ = 0 := by
  change ∀ᵐ E ∂(volume.withDensity (μ.rnDeriv volume)), E ∈ derivFinPosSet μ
  rw [ae_withDensity_iff (Measure.measurable_rnDeriv μ volume)]
  filter_upwards [ae_hasMeasDeriv_rnDeriv μ] with E hE hne
  exact ⟨_, hE.1, pos_iff_ne_zero.2 hne, hE.2⟩

/-- Theorem 1.9.1(d): the limit defining `D_μ(E)` exists in `[0, ∞]` for Lebesgue-a.e. and for
`μ`-a.e. `E`. -/
theorem ae_exists_hasMeasDeriv (μ : Measure ℝ) [IsLocallyFiniteMeasure μ] :
    (∀ᵐ E ∂volume, ∃ d, HasMeasDeriv μ E d) ∧ (∀ᵐ E ∂μ, ∃ d, HasMeasDeriv μ E d) := by
  have hvol : ∀ᵐ E ∂volume, ∃ d, HasMeasDeriv μ E d :=
    (ae_hasMeasDeriv_rnDeriv μ).mono fun E hE => ⟨_, hE.1⟩
  refine ⟨hvol, ?_⟩
  have h : ∀ᵐ E ∂(μ.singularPart volume + volume.withDensity (μ.rnDeriv volume)),
      ∃ d, HasMeasDeriv μ E d :=
    ae_add_measure_iff.2 ⟨(ae_singularPart_hasMeasDeriv_top μ).mono fun E hE => ⟨_, hE⟩,
      (withDensity_absolutelyContinuous _ _).ae_le hvol⟩
  rwa [← Measure.haveLebesgueDecomposition_add μ volume] at h

/-! ## Comparison of Poisson integrals via balls -/

lemma poisson_superlevel_eq_ball {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) (E : ℝ) :
    {x : ℝ | t < poissonKernel ε (x - E)} =
      ball E (Real.sqrt (ε / (Real.pi * t) - ε ^ 2)) := by
  ext x
  simp only [mem_ofPred_eq, mem_ball, Real.dist_eq]
  rw [Real.lt_sqrt (abs_nonneg _), sq_abs, poissonKernel,
    lt_div_iff₀ (by positivity), lt_sub_iff_add_lt, lt_div_iff₀ (by positivity)]
  constructor <;> intro h <;> nlinarith

lemma ball_inter_ball_same (E a b : ℝ) : ball E a ∩ ball E b = ball E (min a b) := by
  ext x; simp [lt_min_iff]

/-- Comparison principle: if `ν₁(B) ≤ C ν₂(B)` for all balls `B` centred at `E` of radius at
most `r₀`, then the same inequality holds for the Poisson integrals over `B(E, r₀)`.  This is the
layer-cake version of the "standard calculation" behind (1.9.20) (Exercise 1.9.5). -/
theorem lintegral_poisson_ball_le {ν₁ ν₂ : Measure ℝ} {E r₀ ε : ℝ} (hε : 0 < ε) {C : ℝ≥0∞}
    (hC : C ≠ ∞) (h : ∀ r, 0 < r → r ≤ r₀ → ν₁ (ball E r) ≤ C * ν₂ (ball E r)) :
    ∫⁻ x in ball E r₀, ENNReal.ofReal (poissonKernel ε (x - E)) ∂ν₁ ≤
      C * ∫⁻ x in ball E r₀, ENNReal.ofReal (poissonKernel ε (x - E)) ∂ν₂ := by
  have hmeas : Measurable fun x => poissonKernel ε (x - E) :=
    (measurable_poissonKernel ε).comp (measurable_id.sub_const E)
  have hnn : ∀ (ν : Measure ℝ), 0 ≤ᵐ[ν] fun x => poissonKernel ε (x - E) :=
    fun ν => Eventually.of_forall fun x => poissonKernel_nonneg hε.le _
  rw [lintegral_eq_lintegral_meas_lt _ (hnn _) hmeas.aemeasurable,
    lintegral_eq_lintegral_meas_lt _ (hnn _) hmeas.aemeasurable, ← lintegral_const_mul' _ _ hC]
  apply lintegral_mono
  intro t
  simp only [Measure.restrict_apply' measurableSet_ball]
  -- the superlevel set intersected with the ball is again a ball
  obtain ⟨ρ, hρ, hset⟩ : ∃ ρ ≤ r₀,
      {x : ℝ | t < poissonKernel ε (x - E)} ∩ ball E r₀ = ball E ρ := by
    rcases le_or_gt t 0 with ht | ht
    · refine ⟨r₀, le_rfl, ?_⟩
      have : {x : ℝ | t < poissonKernel ε (x - E)} = univ :=
        eq_univ_of_forall fun x => lt_of_le_of_lt ht (poissonKernel_pos hε _)
      rw [this, univ_inter]
    · exact ⟨_, min_le_right _ _, by rw [poisson_superlevel_eq_ball hε ht, ball_inter_ball_same]⟩
  rw [hset]
  rcases le_or_gt ρ 0 with h0 | h0
  · simp [ball_eq_empty.2 h0]
  · exact h _ h0 hρ

/-- Total mass of the Poisson kernel: `∫ P_ε = 1`. -/
lemma integral_poissonKernel {ε : ℝ} (hε : 0 < ε) (E : ℝ) :
    ∫ x, poissonKernel ε (x - E) = 1 := by
  rw [integral_sub_right_eq_self (fun x => poissonKernel ε x) E]
  have h : (fun x => poissonKernel ε x) =
      fun x => (Real.pi * ε)⁻¹ * (1 + (x / ε) ^ 2)⁻¹ := by
    ext x; unfold poissonKernel; field_simp; ring
  rw [h, integral_const_mul, Measure.integral_comp_div (fun x => (1 + x ^ 2)⁻¹) ε,
    integral_univ_inv_one_add_sq, abs_of_pos hε, smul_eq_mul]
  field_simp

lemma integrable_poissonKernel_volume {ε : ℝ} (hε : 0 < ε) (E : ℝ) :
    Integrable (fun x => poissonKernel ε (x - E)) := by
  have h : (fun x => poissonKernel ε x) =
      fun x => (Real.pi * ε)⁻¹ * (1 + (x / ε) ^ 2)⁻¹ := by
    ext x; unfold poissonKernel; field_simp; ring
  have hi : Integrable (fun x => poissonKernel ε x) := by
    rw [h]; exact (integrable_inv_one_add_sq.comp_div hε.ne').const_mul _
  exact hi.comp_sub_right E

lemma lintegral_poissonKernel {ε : ℝ} (hε : 0 < ε) (E : ℝ) :
    ∫⁻ x, ENNReal.ofReal (poissonKernel ε (x - E)) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_poissonKernel_volume hε E)
    (Eventually.of_forall fun x => poissonKernel_nonneg hε.le _), integral_poissonKernel hε E,
    ENNReal.ofReal_one]

/-- `∫_{E-r}^{E+r} P_ε(x - E) dx = (2/π) arctan(r/ε)`. -/
lemma integral_poissonKernel_ball {ε r : ℝ} (hε : 0 < ε) (hr : 0 < r) (E : ℝ) :
    ∫ x in ball E r, poissonKernel ε (x - E) = 2 / Real.pi * Real.arctan (r / ε) := by
  rw [Real.ball_eq_Ioo, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le
    (by linarith), intervalIntegral.integral_comp_sub_right (fun x => poissonKernel ε x)]
  have h : (fun x => poissonKernel ε x) =
      fun x => (Real.pi * ε)⁻¹ * (1 / (1 + (x / ε) ^ 2)) := by
    ext x; unfold poissonKernel; field_simp; ring
  rw [h, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_div (fun x => 1 / (1 + x ^ 2)) hε.ne',
    integral_one_div_one_add_sq, smul_eq_mul]
  simp only [sub_sub_cancel_left, add_sub_cancel_left, neg_div, Real.arctan_neg]
  field_simp
  ring

lemma tendsto_lintegral_poissonKernel_ball {r : ℝ} (hr : 0 < r) (E : ℝ) :
    Tendsto (fun ε => ∫⁻ x in ball E r, ENNReal.ofReal (poissonKernel ε (x - E)))
      (𝓝[>] 0) (𝓝 1) := by
  have heq : ∀ ε, 0 < ε → ∫⁻ x in ball E r, ENNReal.ofReal (poissonKernel ε (x - E)) =
      ENNReal.ofReal (2 / Real.pi * Real.arctan (r / ε)) := fun ε hε => by
    rw [← integral_poissonKernel_ball hε hr E, ofReal_integral_eq_lintegral_ofReal
      ((integrable_poissonKernel_volume hε E).integrableOn)
      (Eventually.of_forall fun x => poissonKernel_nonneg hε.le _)]
  have hlim : Tendsto (fun ε : ℝ => 2 / Real.pi * Real.arctan (r / ε)) (𝓝[>] 0) (𝓝 1) := by
    have h1 : Tendsto (fun ε : ℝ => r / ε) (𝓝[>] 0) atTop :=
      Tendsto.const_mul_atTop hr tendsto_inv_nhdsGT_zero |>.congr fun ε => by ring
    have h2 := (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp h1
    have h3 := h2.const_mul (2 / Real.pi)
    have h4 : (2 / Real.pi * (Real.pi / 2)) = 1 := by field_simp
    rw [h4] at h3
    exact h3
  rw [← ENNReal.ofReal_one]
  refine (ENNReal.tendsto_ofReal hlim).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (heq ε hε).symm

/-! ## Inequality (1.9.20) -/

/-- The "Poisson integral" `π⁻¹ Im F_μ(E + iε)` as an `ℝ≥0∞`-valued function of `ε`. -/
def poissonInt (μ : Measure ℝ) (E ε : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (poissonKernel ε (x - E)) ∂μ

lemma poissonInt_eq (μ : Measure ℝ) [IsFiniteMeasure μ] (E : ℝ) {ε : ℝ} (hε : 0 < ε) :
    poissonInt μ E ε = ENNReal.ofReal ((borelTransform μ (E + ε * Complex.I)).im / Real.pi) :=
  (ofReal_im_div_pi μ E hε).symm

/-- The part of the Poisson integral away from `E` vanishes as `ε ↓ 0` (Exercise 1.9.5(a)). -/
lemma lintegral_poisson_compl_le (μ : Measure ℝ) {E r ε : ℝ} (hε : 0 < ε) (hr : 0 < r) :
    ∫⁻ x in (ball E r)ᶜ, ENNReal.ofReal (poissonKernel ε (x - E)) ∂μ ≤
      ENNReal.ofReal (ε / (Real.pi * r ^ 2)) * μ univ := by
  calc ∫⁻ x in (ball E r)ᶜ, ENNReal.ofReal (poissonKernel ε (x - E)) ∂μ
      ≤ ∫⁻ _ in (ball E r)ᶜ, ENNReal.ofReal (ε / (Real.pi * r ^ 2)) ∂μ := by
        apply setLIntegral_mono measurable_const
        intro x hx
        apply ENNReal.ofReal_le_ofReal
        apply poissonKernel_le_of_le hε hr
        simpa [Real.dist_eq] using hx
    _ ≤ ENNReal.ofReal (ε / (Real.pi * r ^ 2)) * μ univ := by
        rw [setLIntegral_const]; gcongr; exact subset_univ _

lemma tendsto_far_term (μ : Measure ℝ) [IsFiniteMeasure μ] {r : ℝ} (_hr : 0 < r) :
    Tendsto (fun ε => ENNReal.ofReal (ε / (Real.pi * r ^ 2)) * μ univ) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun ε : ℝ => ε / (Real.pi * r ^ 2)) (𝓝[>] 0) (𝓝 0) := by
    have := ((continuous_id.div_const (Real.pi * r ^ 2)).tendsto 0).mono_left
      (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  have h2 := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h)
    (Or.inr (measure_ne_top μ univ))
  simpa using h2

/-- Inequality (1.9.20), upper half: `limsup_{ε↓0} π⁻¹ Im F_μ(E + iε) ≤ D^+_μ(E)`. -/
theorem limsup_poisson_le_upperDeriv (μ : Measure ℝ) [IsFiniteMeasure μ] (E : ℝ) :
    limsup (poissonInt μ E) (𝓝[>] 0) ≤ upperDeriv μ E := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro C hC
  rcases eq_or_ne C ∞ with rfl | hCtop
  · exact le_top
  have hev := eventually_lt_of_limsup_lt hC
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hu0 : (0 : ℝ) < u := hu
  set r₀ := u / 2 with hr₀
  have hr₀pos : 0 < r₀ := by positivity
  have hball : ∀ r, 0 < r → r ≤ r₀ → μ (ball E r) ≤ C * volume (ball E r) := by
    intro r hr hrr
    have hlt : ballRatio μ E r < C := hsub ⟨hr, by linarith⟩
    rw [Real.volume_ball]
    have hpos : ENNReal.ofReal (2 * r) ≠ 0 := by simpa using (by linarith : (0 : ℝ) < 2 * r)
    have := ENNReal.div_le_iff hpos ENNReal.ofReal_ne_top |>.1 hlt.le
    exact this
  have hbound : ∀ ε, 0 < ε →
      poissonInt μ E ε ≤ C + ENNReal.ofReal (ε / (Real.pi * r₀ ^ 2)) * μ univ := by
    intro ε hε
    rw [poissonInt, ← lintegral_add_compl _ (measurableSet_ball (x := E) (ε := r₀))]
    gcongr
    · calc ∫⁻ x in ball E r₀, ENNReal.ofReal (poissonKernel ε (x - E)) ∂μ
          ≤ C * ∫⁻ x in ball E r₀, ENNReal.ofReal (poissonKernel ε (x - E)) ∂volume :=
            lintegral_poisson_ball_le hε hCtop hball
        _ ≤ C * ∫⁻ x, ENNReal.ofReal (poissonKernel ε (x - E)) ∂volume := by
            gcongr; exact Measure.restrict_le_self
        _ = C := by rw [lintegral_poissonKernel hε, mul_one]
    · exact lintegral_poisson_compl_le μ hε hr₀pos
  have hlim : Tendsto (fun ε => C + ENNReal.ofReal (ε / (Real.pi * r₀ ^ 2)) * μ univ)
      (𝓝[>] 0) (𝓝 C) := by
    simpa using tendsto_const_nhds.add (tendsto_far_term μ hr₀pos)
  rw [← hlim.limsup_eq]
  refine limsup_le_limsup ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε using hbound ε hε

/-- Inequality (1.9.20), lower half: `D^-_μ(E) ≤ liminf_{ε↓0} π⁻¹ Im F_μ(E + iε)`. -/
theorem lowerDeriv_le_liminf_poisson (μ : Measure ℝ) [IsFiniteMeasure μ] (E : ℝ) :
    lowerDeriv μ E ≤ liminf (poissonInt μ E) (𝓝[>] 0) := by
  apply le_of_forall_lt_imp_le_of_dense
  intro c hc
  rcases eq_or_ne c 0 with rfl | hc0
  · exact bot_le
  have hctop : c ≠ ∞ := ne_top_of_lt hc
  have hev := eventually_lt_of_lt_liminf hc
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hu0 : (0 : ℝ) < u := hu
  set r₀ := u / 2 with hr₀
  have hr₀pos : 0 < r₀ := by positivity
  have hball : ∀ r, 0 < r → r ≤ r₀ → volume (ball E r) ≤ c⁻¹ * μ (ball E r) := by
    intro r hr hrr
    have hlt : c < ballRatio μ E r := hsub ⟨hr, by linarith⟩
    rw [Real.volume_ball]
    have hpos : ENNReal.ofReal (2 * r) ≠ 0 := by simpa using (by linarith : (0 : ℝ) < 2 * r)
    have h1 : c * ENNReal.ofReal (2 * r) ≤ μ (ball E r) :=
      (ENNReal.le_div_iff_mul_le (Or.inl hpos) (Or.inl ENNReal.ofReal_ne_top)).1 hlt.le
    calc ENNReal.ofReal (2 * r) = c⁻¹ * (c * ENNReal.ofReal (2 * r)) := by
          rw [← mul_assoc, ENNReal.inv_mul_cancel hc0 hctop, one_mul]
      _ ≤ c⁻¹ * μ (ball E r) := by gcongr
  have hbound : ∀ ε, 0 < ε →
      c * ∫⁻ x in ball E r₀, ENNReal.ofReal (poissonKernel ε (x - E)) ∂volume ≤
        poissonInt μ E ε := by
    intro ε hε
    have h1 := lintegral_poisson_ball_le hε (ENNReal.inv_ne_top.2 hc0) hball
    calc c * ∫⁻ x in ball E r₀, ENNReal.ofReal (poissonKernel ε (x - E)) ∂volume
        ≤ c * (c⁻¹ * ∫⁻ x in ball E r₀, ENNReal.ofReal (poissonKernel ε (x - E)) ∂μ) := by
          gcongr
      _ = ∫⁻ x in ball E r₀, ENNReal.ofReal (poissonKernel ε (x - E)) ∂μ := by
          rw [← mul_assoc, ENNReal.mul_inv_cancel hc0 hctop, one_mul]
      _ ≤ poissonInt μ E ε := setLIntegral_le_lintegral _ _
  have hlim := ENNReal.Tendsto.const_mul (tendsto_lintegral_poissonKernel_ball hr₀pos E)
    (a := c) (Or.inl one_ne_zero)
  rw [mul_one] at hlim
  rw [← hlim.liminf_eq]
  refine liminf_le_liminf ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε using hbound ε hε

/-- (1.9.21)/(1.9.22): whenever `D_μ(E)` exists, `π⁻¹ Im F_μ(E + iε) → D_μ(E)`. -/
theorem tendsto_poisson_of_hasMeasDeriv {μ : Measure ℝ} [IsFiniteMeasure μ] {E : ℝ}
    {d : ℝ≥0∞} (h : HasMeasDeriv μ E d) : Tendsto (poissonInt μ E) (𝓝[>] 0) (𝓝 d) := by
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_
  · rw [← h.lowerDeriv_eq]; exact lowerDeriv_le_liminf_poisson μ E
  · rw [← h.upperDeriv_eq]; exact limsup_poisson_le_upperDeriv μ E

/-- Real-valued form of (1.9.22) when `D_μ(E) < ∞`:
`Im F_μ(E + iε) → π D_μ(E)`. -/
theorem tendsto_im_of_hasMeasDeriv {μ : Measure ℝ} [IsFiniteMeasure μ] {E : ℝ}
    {d : ℝ≥0∞} (h : HasMeasDeriv μ E d) (hd : d ≠ ∞) :
    Tendsto (fun ε : ℝ => (borelTransform μ (E + ε * Complex.I)).im) (𝓝[>] 0)
      (𝓝 (Real.pi * d.toReal)) := by
  have h1 := (ENNReal.tendsto_toReal hd).comp (tendsto_poisson_of_hasMeasDeriv h)
  have h2 := h1.const_mul Real.pi
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  simp only [Function.comp_apply, poissonInt_eq μ E hε]
  rw [ENNReal.toReal_ofReal (div_nonneg (borelTransform_im_nonneg μ E hε) Real.pi_pos.le)]
  field_simp

/-- Form of (1.9.22) when `D_μ(E) = ∞`: `Im F_μ(E + iε) → ∞`. -/
theorem tendsto_im_atTop_of_hasMeasDeriv_top {μ : Measure ℝ} [IsFiniteMeasure μ] {E : ℝ}
    (h : HasMeasDeriv μ E ∞) :
    Tendsto (fun ε : ℝ => (borelTransform μ (E + ε * Complex.I)).im) (𝓝[>] 0) atTop := by
  have h1 := tendsto_poisson_of_hasMeasDeriv h
  rw [Filter.tendsto_atTop]
  intro M
  have hM := h1.eventually (lt_mem_nhds (ENNReal.ofReal_lt_top (r := M / Real.pi)))
  filter_upwards [hM, self_mem_nhdsWithin] with ε hε (hε0 : 0 < ε)
  rw [poissonInt_eq μ E hε0] at hε
  have := (ENNReal.ofReal_lt_ofReal_iff'.1 hε).1
  have := (div_lt_div_iff_of_pos_right Real.pi_pos).1 this
  exact this.le

end DF
