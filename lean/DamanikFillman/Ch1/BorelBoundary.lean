/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators, I*,
§1.9.1 and §1.9.3 (pp. 84–89): boundary values of the imaginary part of the Borel transform,
the absolutely continuous / singular parts, and rank-one perturbations at the level of measures.

# Main results

* `DF.ae_tendsto_im_volume`, `DF.ae_tendsto_im_measure` — Theorem 1.9.4(a): `Im F_μ(E + i0)`
  exists Lebesgue-a.e. (finite, equal to `π D_μ(E)`) and `μ`-a.e. (in `[0, ∞]`);
* `DF.acPart_eq_withDensity_imBoundary` — Theorem 1.9.4(b), formula (1.9.23):
  `dμ_ac = π⁻¹ Im F_μ(E + i0) dE`;
* `DF.acPart_compl_imBoundaryPosSet`, `DF.volume_imBoundaryPosSet_diff` — Theorem 1.9.4(b):
  `T₊ = {0 < Im F_μ(E + i0) < ∞}` is an essential support of `μ_ac`;
* `DF.singularPart_not_tendsto_atTop` — Theorem 1.9.4(c), (1.9.24): `μ_s` is supported on
  `{Im F_μ(E + i0) = ∞}`;
* `DF.integral_imBoundary_mul_poisson`, `DF.im_borelTransform_acPart_le` — Proposition 1.9.5;
* `DF.rankOne_singularParts_mutuallySingular` — Proposition 1.9.9, second bullet (proved
  unconditionally);
* `DF.rankOne_acParts_equiv` — Proposition 1.9.9, first bullet, proved assuming the boundary
  value statement for the real part (Theorem 1.9.4(d), see below); the unconditional version is
  `DF.rankOne_acParts_equiv'` in `DamanikFillman.Ch1.BorelHerglotz`.

Proposition 1.9.9 is formulated purely for measures: `ν` is any finite measure whose Borel
transform is `F_μ / (1 + λ F_μ)` on the upper half-plane (this is (1.9.33), proved for operators in
`DF.rankOne_borel`).

# Statements recorded but not proved (`Prop`s)

* `DF.ReBoundaryValueStatement` — Theorem 1.9.4(d), Lebesgue part (proved later, in
  `DamanikFillman.Ch1.BorelHerglotz`, via the Herglotz representation of `√F_μ` and `i √F_μ`);
* `DF.ReBoundaryValueMeasureStatement` — Theorem 1.9.4(d), `μ`-a.e. part (not proved);
* `DF.BoundaryUniquenessStatement` — Theorem 1.9.4(e); proved in
  `DamanikFillman.Ch1.BoundaryUniqueness` (`DF.boundaryUniquenessStatement_holds`) by a
  Phragmén–Lindelöf argument instead of the factorization theory of `H^∞` used in the book.
-/
import DamanikFillman.Ch1.BorelDerivative

noncomputable section

open MeasureTheory Filter Topology Set Metric Complex
open scoped ENNReal

namespace DF

/-- The boundary value `Im F_μ(E + i0) = lim_{ε↓0} Im F_μ(E + iε)` (when it exists; otherwise
this is a junk value). -/
def imBoundary (μ : Measure ℝ) (E : ℝ) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε : ℝ => (borelTransform μ (E + ε * I)).im

/-- Theorem 1.9.4(a), Lebesgue part: for Lebesgue-a.e. `E`, `Im F_μ(E + iε)` converges to the
finite value `π D_μ(E) = π dμ_ac/dE (E)`. -/
theorem ae_tendsto_im_volume (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∀ᵐ (E : ℝ) ∂volume, Tendsto (fun ε : ℝ => (borelTransform μ (E + ε * I)).im) (𝓝[>] 0)
      (𝓝 (Real.pi * (μ.rnDeriv volume E).toReal)) := by
  filter_upwards [ae_hasMeasDeriv_rnDeriv μ] with E hE
  exact tendsto_im_of_hasMeasDeriv hE.1 hE.2.ne

/-- Theorem 1.9.4(a), `μ` part: for `μ`-a.e. `E`, `Im F_μ(E + i0)` exists as an extended real
number. -/
theorem ae_tendsto_im_measure (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∀ᵐ (E : ℝ) ∂μ, (∃ y : ℝ, Tendsto (fun ε : ℝ => (borelTransform μ (E + ε * I)).im) (𝓝[>] 0)
      (𝓝 y)) ∨ Tendsto (fun ε : ℝ => (borelTransform μ (E + ε * I)).im) (𝓝[>] 0) atTop := by
  filter_upwards [(ae_exists_hasMeasDeriv μ).2] with E ⟨d, hd⟩
  rcases eq_or_ne d ∞ with rfl | hne
  · exact Or.inr (tendsto_im_atTop_of_hasMeasDeriv_top hd)
  · exact Or.inl ⟨_, tendsto_im_of_hasMeasDeriv hd hne⟩

lemma imBoundary_ae_eq (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∀ᵐ (E : ℝ) ∂volume, imBoundary μ E = Real.pi * (μ.rnDeriv volume E).toReal := by
  filter_upwards [ae_tendsto_im_volume μ] with E hE
  exact hE.limUnder_eq

/-- Theorem 1.9.4(b), formula (1.9.23): the absolutely continuous part of `μ` has density
`π⁻¹ Im F_μ(E + i0)` with respect to Lebesgue measure. -/
theorem acPart_eq_withDensity_imBoundary (μ : Measure ℝ) [IsFiniteMeasure μ] :
    volume.withDensity (μ.rnDeriv volume) =
      volume.withDensity (fun E => ENNReal.ofReal (imBoundary μ E / Real.pi)) := by
  apply withDensity_congr_ae
  filter_upwards [imBoundary_ae_eq μ, Measure.rnDeriv_lt_top μ volume] with E hE hlt
  rw [hE, mul_div_cancel_left₀ _ Real.pi_ne_zero, ENNReal.ofReal_toReal hlt.ne]

/-- The set `T₊ = {E : 0 < Im F_μ(E + i0) < ∞}`. -/
def imBoundaryPosSet (μ : Measure ℝ) : Set ℝ :=
  {E : ℝ | ∃ y : ℝ, 0 < y ∧
    Tendsto (fun ε : ℝ => (borelTransform μ (E + ε * I)).im) (𝓝[>] 0) (𝓝 y)}

/-- Theorem 1.9.4(b): `T₊` supports `μ_ac`. -/
theorem acPart_compl_imBoundaryPosSet (μ : Measure ℝ) [IsFiniteMeasure μ] :
    volume.withDensity (μ.rnDeriv volume) (imBoundaryPosSet μ)ᶜ = 0 := by
  change ∀ᵐ (E : ℝ) ∂(volume.withDensity (μ.rnDeriv volume)), E ∈ imBoundaryPosSet μ
  rw [ae_withDensity_iff (Measure.measurable_rnDeriv μ volume)]
  filter_upwards [ae_tendsto_im_volume μ, Measure.rnDeriv_lt_top μ volume] with E hE hlt hne
  refine ⟨_, mul_pos Real.pi_pos (ENNReal.toReal_pos hne hlt.ne), hE⟩

/-- Theorem 1.9.4(b): `T₊` is an *essential* support of `μ_ac`: `Leb(T₊ \ S) = 0` for every
support `S` of `μ_ac`. -/
theorem volume_imBoundaryPosSet_diff (μ : Measure ℝ) [IsFiniteMeasure μ] {S : Set ℝ}
    (hS : volume.withDensity (μ.rnDeriv volume) Sᶜ = 0) :
    volume (imBoundaryPosSet μ \ S) = 0 := by
  obtain ⟨T, hTS, hTm, hT0⟩ := exists_measurable_superset_of_null hS
  rw [withDensity_apply_eq_zero' (Measure.measurable_rnDeriv μ volume).aemeasurable] at hT0
  have hN := ae_tendsto_im_volume μ
  rw [ae_iff] at hN
  refine measure_mono_null ?_ (measure_union_null hT0 hN)
  rintro E ⟨⟨y, hy, hEy⟩, hES⟩
  by_cases hgood : Tendsto (fun ε : ℝ => (borelTransform μ (E + ε * I)).im) (𝓝[>] 0)
      (𝓝 (Real.pi * (μ.rnDeriv volume E).toReal))
  · left
    refine ⟨?_, hTS hES⟩
    have := tendsto_nhds_unique hEy hgood
    intro h0
    simp only [h0, ENNReal.toReal_zero, mul_zero] at this
    linarith
  · right; exact hgood

/-- Theorem 1.9.4(c), (1.9.24): the singular part of `μ` is supported on
`{E : Im F_μ(E + i0) = ∞}`. -/
theorem singularPart_not_tendsto_atTop (μ : Measure ℝ) [IsFiniteMeasure μ] :
    μ.singularPart volume
      {E : ℝ | ¬ Tendsto (fun ε : ℝ => (borelTransform μ (E + ε * I)).im) (𝓝[>] 0) atTop} = 0 := by
  have h := ae_singularPart_hasMeasDeriv_top μ
  rw [ae_iff] at h
  refine measure_mono_null ?_ h
  intro E hE hD
  exact hE (tendsto_im_atTop_of_hasMeasDeriv_top hD)

/-- Theorem 1.9.4(d), Lebesgue part, as a statement: `Re F_μ(E + i0)` exists and is finite for
Lebesgue-a.e. `E`.  Proved in `DamanikFillman.Ch1.BorelHerglotz` as
`DF.reBoundaryValueStatement_holds` (via the Herglotz representation of `√F_μ`, as in the
book). -/
def ReBoundaryValueStatement : Prop :=
  ∀ μ : Measure ℝ, IsFiniteMeasure μ →
    ∀ᵐ (E : ℝ) ∂volume, ∃ y : ℝ,
      Tendsto (fun ε : ℝ => (borelTransform μ (E + ε * I)).re) (𝓝[>] 0) (𝓝 y)

/-- Theorem 1.9.4(d), `μ` part, recorded as a statement: `Re F_μ(E + i0)` exists as an extended
real number for `μ`-a.e. `E`. -/
def ReBoundaryValueMeasureStatement : Prop :=
  ∀ μ : Measure ℝ, IsFiniteMeasure μ →
    ∀ᵐ (E : ℝ) ∂μ, (∃ y : ℝ,
      Tendsto (fun ε : ℝ => (borelTransform μ (E + ε * I)).re) (𝓝[>] 0) (𝓝 y)) ∨
      Tendsto (fun ε : ℝ => (borelTransform μ (E + ε * I)).re) (𝓝[>] 0) atTop ∨
      Tendsto (fun ε : ℝ => (borelTransform μ (E + ε * I)).re) (𝓝[>] 0) atBot

/-- Theorem 1.9.4(e), recorded as a statement: two Stieltjes transforms whose boundary values
agree on a set of positive Lebesgue measure coincide. -/
def BoundaryUniquenessStatement : Prop :=
  ∀ (μ ν : Measure ℝ), IsFiniteMeasure μ → IsFiniteMeasure ν → ∀ A : Set ℝ, 0 < volume A →
    (∀ E ∈ A, ∃ w : ℂ,
      Tendsto (fun ε : ℝ => borelTransform μ (E + ε * I)) (𝓝[>] 0) (𝓝 w) ∧
      Tendsto (fun ε : ℝ => borelTransform ν (E + ε * I)) (𝓝[>] 0) (𝓝 w)) →
    ∀ z : ℂ, 0 < z.im → borelTransform μ z = borelTransform ν z

/-! ## Proposition 1.9.5 -/

/-- Proposition 1.9.5 (equality): the Poisson integral of the boundary values of `Im F_μ` is
`Im F_{μ_ac}`. -/
theorem integral_imBoundary_mul_poisson (μ : Measure ℝ) [IsFiniteMeasure μ] (E : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∫ x, imBoundary μ x * poissonKernel ε (E - x) =
      (borelTransform (volume.withDensity (μ.rnDeriv volume)) (E + ε * I)).im := by
  rw [borelTransform_im _ E hε.ne', integral_withDensity_eq_integral_toReal_smul
    (Measure.measurable_rnDeriv μ volume) (Measure.rnDeriv_lt_top μ volume)]
  apply integral_congr_ae
  filter_upwards [imBoundary_ae_eq μ] with x hx
  rw [hx, smul_eq_mul, poissonKernel]
  have : 0 < (x - E) ^ 2 + ε ^ 2 := by positivity
  have h2 : (E - x) ^ 2 = (x - E) ^ 2 := by ring
  rw [h2]
  field_simp

/-- Proposition 1.9.5 (inequality): `Im F_{μ_ac}(z) ≤ Im F_μ(z)`. -/
theorem im_borelTransform_acPart_le (μ : Measure ℝ) [IsFiniteMeasure μ] (E : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    (borelTransform (volume.withDensity (μ.rnDeriv volume)) (E + ε * I)).im ≤
      (borelTransform μ (E + ε * I)).im := by
  have hz : (E + ε * I : ℂ).im ≠ 0 := by simpa using hε.ne'
  have h := borelTransform_add (μ.singularPart volume) (volume.withDensity (μ.rnDeriv volume)) hz
  rw [← Measure.haveLebesgueDecomposition_add μ volume] at h
  rw [h, Complex.add_im]
  have := borelTransform_im_nonneg (μ.singularPart volume) E hε
  linarith

/-! ## Proposition 1.9.9 (rank-one perturbations, measure level) -/

lemma normSq_ge_im_sq (w : ℂ) : w.im ^ 2 ≤ Complex.normSq w := by
  rw [Complex.normSq_apply]; nlinarith [mul_self_nonneg w.re]

/-- If `Im F > 0` and `λ ≠ 0`, then `Im (F / (1 + λ F)) ≤ 1 / (λ² Im F)`. -/
lemma im_div_one_add_mul_le (F : ℂ) {lam : ℝ} (hlam : lam ≠ 0) (hF : 0 < F.im) :
    (F / (1 + lam * F)).im ≤ 1 / (lam ^ 2 * F.im) := by
  rw [im_div_one_add_mul]
  have him : (1 + (lam : ℂ) * F).im = lam * F.im := by simp
  have h1 := normSq_ge_im_sq (1 + (lam : ℂ) * F)
  rw [him] at h1
  have hpos : 0 < (lam * F.im) ^ 2 := by positivity
  calc F.im / Complex.normSq (1 + lam * F) ≤ F.im / (lam * F.im) ^ 2 :=
        div_le_div_of_nonneg_left hF.le hpos h1
    _ = 1 / (lam ^ 2 * F.im) := by field_simp

/-- Proposition 1.9.9, second bullet: if `F_ν = F_μ / (1 + λ F_μ)` on `ℂ₊` with `λ ≠ 0`, then
the singular parts of `μ` and `ν` are mutually singular. -/
theorem rankOne_singularParts_mutuallySingular (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {lam : ℝ} (hlam : lam ≠ 0)
    (hF : ∀ z : ℂ, 0 < z.im →
      borelTransform ν z = borelTransform μ z / (1 + lam * borelTransform μ z)) :
    μ.singularPart volume ⟂ₘ ν.singularPart volume := by
  set A := {E : ℝ | Tendsto (fun ε : ℝ => (borelTransform μ (E + ε * I)).im) (𝓝[>] 0) atTop}
  set B := {E : ℝ | Tendsto (fun ε : ℝ => (borelTransform ν (E + ε * I)).im) (𝓝[>] 0) atTop}
  have hA : μ.singularPart volume Aᶜ = 0 := singularPart_not_tendsto_atTop μ
  have hB : ν.singularPart volume Bᶜ = 0 := singularPart_not_tendsto_atTop ν
  refine Measure.MutuallySingular.mk hA hB ?_
  intro E _
  by_contra hcon
  simp only [mem_union, mem_compl_iff, not_or, not_not] at hcon
  obtain ⟨hEA, hEB⟩ := hcon
  have hEA : Tendsto (fun ε : ℝ => (borelTransform μ (E + ε * I)).im) (𝓝[>] 0) atTop := hEA
  have hEB : Tendsto (fun ε : ℝ => (borelTransform ν (E + ε * I)).im) (𝓝[>] 0) atTop := hEB
  have h1 : ∀ᶠ ε : ℝ in 𝓝[>] 0, 1 / lam ^ 2 < (borelTransform μ (E + ε * I)).im :=
    hEA.eventually (eventually_gt_atTop _)
  have h2 : ∀ᶠ ε : ℝ in 𝓝[>] 0, 1 < (borelTransform ν (E + ε * I)).im :=
    hEB.eventually (eventually_gt_atTop _)
  obtain ⟨ε, hε1, hε2, hε⟩ := (h1.and (h2.and self_mem_nhdsWithin)).exists
  have hε' : (0 : ℝ) < ε := hε
  have hz : 0 < (E + ε * I : ℂ).im := by simpa using hε'
  have hlam2 : 0 < lam ^ 2 := by positivity
  have hFpos : 0 < (borelTransform μ (E + ε * I)).im :=
    lt_trans (by positivity) hε1
  have hle := im_div_one_add_mul_le _ hlam hFpos
  rw [← hF _ hz] at hle
  have : 1 / (lam ^ 2 * (borelTransform μ (E + ε * I)).im) < 1 := by
    rw [div_lt_one (by positivity)]
    rw [div_lt_iff₀ hlam2] at hε1
    linarith
  linarith

/-- One direction of Proposition 1.9.9, first bullet (assuming Theorem 1.9.4(d)). -/
theorem rankOne_acPart_absolutelyContinuous (hRe : ReBoundaryValueStatement)
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (lam : ℝ)
    (hF : ∀ z : ℂ, 0 < z.im →
      borelTransform ν z = borelTransform μ z / (1 + lam * borelTransform μ z)) :
    volume.withDensity (μ.rnDeriv volume) ≪ volume.withDensity (ν.rnDeriv volume) := by
  have key : ∀ᵐ (E : ℝ) ∂volume, μ.rnDeriv volume E ≠ 0 → ν.rnDeriv volume E ≠ 0 := by
    filter_upwards [ae_tendsto_im_volume μ, ae_tendsto_im_volume ν, hRe μ inferInstance,
      Measure.rnDeriv_lt_top μ volume] with E hμ hν ⟨y, hy⟩ hlt hne
    set w : ℂ := y + (Real.pi * (μ.rnDeriv volume E).toReal : ℝ) * I with hw
    have hwim : 0 < w.im := by
      simp only [hw, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
      exact mul_pos Real.pi_pos (ENNReal.toReal_pos hne hlt.ne)
    have hFw : Tendsto (fun ε : ℝ => borelTransform μ (E + ε * I)) (𝓝[>] 0) (𝓝 w) := by
      have h1 := ((Complex.continuous_ofReal.tendsto _).comp hy).add
        (((Complex.continuous_ofReal.tendsto _).comp hμ).mul_const I)
      refine h1.congr fun ε => ?_
      simp only [Function.comp_apply]
      exact Complex.re_add_im _
    have hden : (1 + (lam : ℂ) * w) ≠ 0 := by
      intro h0
      rcases eq_or_ne lam 0 with hl | hl
      · rw [hl] at h0; simp at h0
      · have := congrArg Complex.im h0
        simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, add_zero, zero_add, Complex.zero_im] at this
        rcases mul_eq_zero.1 this with h | h
        · exact hl h
        · linarith
    have hFν : Tendsto (fun ε : ℝ => (borelTransform ν (E + ε * I)).im) (𝓝[>] 0)
        (𝓝 ((w / (1 + lam * w)).im)) := by
      have h1 : Tendsto (fun ε : ℝ => borelTransform μ (E + ε * I) /
          (1 + lam * borelTransform μ (E + ε * I))) (𝓝[>] 0) (𝓝 (w / (1 + lam * w))) :=
        hFw.div (tendsto_const_nhds.add (tendsto_const_nhds.mul hFw)) hden
      have h2 := (Complex.continuous_im.tendsto _).comp h1
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
      simp only [Function.comp_apply]
      rw [hF _ (by simpa using hε)]
    have huniq := tendsto_nhds_unique hν hFν
    rw [im_div_one_add_mul] at huniq
    have hpos : 0 < w.im / Complex.normSq (1 + lam * w) :=
      div_pos hwim (Complex.normSq_pos.2 hden)
    intro h0
    rw [h0, ENNReal.toReal_zero, mul_zero] at huniq
    linarith
  intro s hs
  rw [withDensity_apply_eq_zero' (Measure.measurable_rnDeriv ν volume).aemeasurable] at hs
  rw [withDensity_apply_eq_zero' (Measure.measurable_rnDeriv μ volume).aemeasurable]
  rw [ae_iff] at key
  refine measure_mono_null ?_ (measure_union_null hs key)
  rintro E ⟨hE, hEs⟩
  by_cases h : ν.rnDeriv volume E ≠ 0
  · exact Or.inl ⟨h, hEs⟩
  · exact Or.inr fun himp => h (himp hE)

/-- Proposition 1.9.9, first bullet (assuming Theorem 1.9.4(d), `ReBoundaryValueStatement`):
if `F_ν = F_μ / (1 + λ F_μ)` on `ℂ₊` with `λ ≠ 0`, the absolutely continuous parts of `μ` and `ν`
are equivalent. -/
theorem rankOne_acParts_equiv (hRe : ReBoundaryValueStatement)
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] {lam : ℝ} (hlam : lam ≠ 0)
    (hF : ∀ z : ℂ, 0 < z.im →
      borelTransform ν z = borelTransform μ z / (1 + lam * borelTransform μ z)) :
    volume.withDensity (μ.rnDeriv volume) ≪ volume.withDensity (ν.rnDeriv volume) ∧
      volume.withDensity (ν.rnDeriv volume) ≪ volume.withDensity (μ.rnDeriv volume) := by
  refine ⟨rankOne_acPart_absolutelyContinuous hRe μ ν lam hF,
    rankOne_acPart_absolutelyContinuous hRe ν μ (-lam) fun z hz => ?_⟩
  have hne : (1 + (lam : ℂ) * borelTransform μ z) ≠ 0 := by
    intro h0
    by_cases hμ : μ = 0
    · subst hμ; simp [borelTransform] at h0
    · have hpos := borelTransform_im_pos μ hμ hz
      have := congrArg Complex.im h0
      simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero, zero_add, Complex.zero_im] at this
      rcases mul_eq_zero.1 this with h | h
      · exact hlam h
      · linarith
  rw [hF z hz]
  set F := borelTransform μ z
  have h1 : (1 + ((-lam : ℝ) : ℂ) * (F / (1 + lam * F))) = 1 / (1 + lam * F) := by
    push_cast; field_simp; ring
  rw [h1, div_div_eq_mul_div, div_one, div_mul_cancel₀ _ hne]

end DF
