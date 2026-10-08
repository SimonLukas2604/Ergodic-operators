/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Theorem 2.4.2 (b): generalized eigenfunctions support the spectral measure  (book pp. 161–164)

Main results:
* `DF.inner_borelCalc_eq_integral_density` — for vectors `φ, ψ` and bounded Borel `g`,
  `⟪ψ, g(A) φ⟫ = ∫ g F dμ_φ` with an explicit density `F = DF.matDensity A hA φ ψ ∈ L¹(μ_φ)`
  (built from the Radon–Nikodym derivatives of the four polarization measures; this replaces the
  book's complex measures `μ_{ψ,φ}` and their Radon–Nikodym derivatives);
* `DF.genEigSupport` — proof of `DF.GenEigSupportStatement`: for every `δ > 1/2`,
  `μ(ℝ \ G_δ) = 0` for the canonical spectral measure `μ = μ_{δ₀} + μ_{δ₁}`.

Proof: for the base vector `δ_b` (`b = 0, 1`) let `Fₙ` be the density of `⟪δₙ, g(H) δ_b⟫` with respect
to `μ_b = μ_{δ_b}`. Testing against all bounded Borel `g` gives, `μ_b`-a.e.,
`F_{n+1} + F_{n-1} + V(n) Fₙ = E Fₙ` (from `H δₙ = δ_{n+1} + δ_{n-1} + V(n) δₙ`) and `F_b = 1`;
truncation and Cauchy–Schwarz give `∫ |Fₙ|² dμ_b ≤ 1`. With `wₙ = (1 + |n|)^{-2δ}` summable, the
function `∑ wₙ |Fₙ|²` is `μ_b`-integrable, hence finite a.e., and `n ↦ Fₙ(E)` is a nonzero solution
with `|Fₙ(E)| ≤ C (1 + |n|)^δ`. Consequences: `DF.spectrum_eq_closure_genEig` and the Ishii–Pastur
theorem `DF.ishii_pastur` now hold unconditionally (`DF.spectrum_eq_closure_genEig'`).
-/
import DamanikFillman.Ch2.GenEigenSupport

noncomputable section

open scoped InnerProductSpace ComplexConjugate ENNReal NNReal
open MeasureTheory Set Filter Topology

namespace DF

/-! ### Densities of matrix elements -/

section density

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The density of `g ↦ ⟪ψ, g(A) φ⟫` with respect to `μ_φ`. -/
def matDensity (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (φ ψ : H) (x : ℝ) : ℂ :=
  ∑ k, polC k * (((spectralMeasure A hA (polV ψ φ k)).rnDeriv (spectralMeasure A hA φ) x).toReal : ℂ)

variable {A : H →L[ℂ] H} {hA : IsSelfAdjoint A}

lemma integrable_matDensity (φ ψ : H) :
    Integrable (matDensity A hA φ ψ) (spectralMeasure A hA φ) := by
  unfold matDensity
  refine integrable_finset_sum _ fun k _ => ?_
  exact (Measure.integrable_toReal_rnDeriv.ofReal).const_mul _

lemma measurable_matDensity (φ ψ : H) : Measurable (matDensity A hA φ ψ) := by
  unfold matDensity
  refine Finset.measurable_sum _ fun k _ => ?_
  exact measurable_const.mul
    (Complex.measurable_ofReal.comp (Measure.measurable_rnDeriv _ _).ennreal_toReal)

/-- A bounded Borel function vanishing `μ_φ`-a.e. annihilates `φ`. -/
lemma borelCalc_apply_eq_zero_of_ae {g : ℝ → ℂ} (hg : IsBddBorel g) {φ : H}
    (h0 : g =ᵐ[spectralMeasure A hA φ] 0) : borelCalc A hA g φ = 0 := by
  have h := norm_borelCalc_apply_sq (A := A) (hA := hA) hg φ
  have hint : ∫ x, ‖g x‖ ^ 2 ∂(spectralMeasure A hA φ) = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [h0] with x hx
    simp [hx]
  rw [hint] at h
  exact norm_eq_zero.1 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h)

/-- **Densities of matrix elements**: `⟪ψ, g(A) φ⟫ = ∫ g F dμ_φ`. -/
theorem inner_borelCalc_eq_integral_density {g : ℝ → ℂ} (hg : IsBddBorel g) (φ ψ : H) :
    ⟪ψ, borelCalc A hA g φ⟫_ℂ = ∫ x, g x * matDensity A hA φ ψ x ∂(spectralMeasure A hA φ) := by
  classical
  set μ := spectralMeasure A hA φ with hμ
  set ν : Fin 4 → Measure ℝ := fun k => spectralMeasure A hA (polV ψ φ k) with hν
  -- the singular parts live on `T`, a `μ`-null set
  have hsing : ∀ k, ∃ s : Set ℝ, MeasurableSet s ∧ (ν k).singularPart μ s = 0 ∧ μ sᶜ = 0 :=
    fun k => Measure.mutuallySingular_singularPart (ν k) μ
  choose s hsm hs1 hs2 using hsing
  set T : Set ℝ := ⋃ k, (s k)ᶜ with hT
  have hTm : MeasurableSet T := MeasurableSet.iUnion fun k => (hsm k).compl
  have hμT : μ T = 0 := measure_iUnion_null hs2
  set g' : ℝ → ℂ := Tᶜ.indicator g with hg'
  have hg'B : IsBddBorel g' := by
    obtain ⟨C, hC⟩ := hg.bdd
    refine ⟨hg.meas.indicator hTm.compl, C, fun x => ?_⟩
    by_cases hx : x ∈ Tᶜ
    · simp [hg', indicator_of_mem hx, hC x]
    · simp only [hg', indicator_of_notMem hx, norm_zero]
      exact (norm_nonneg _).trans (hC x)
  have hgg' : g =ᵐ[μ] g' := by
    have : ∀ᵐ x ∂μ, x ∉ T := measure_eq_zero_iff_ae_notMem.1 hμT
    filter_upwards [this] with x hx
    simp [hg', indicator_of_mem (show x ∈ Tᶜ from hx)]
  -- step 1: replace `g` by `g'`
  have hdiff : IsBddBorel (g - g') := by
    obtain ⟨C, hC⟩ := hg.bdd
    obtain ⟨D, hD⟩ := hg'B.bdd
    exact ⟨hg.meas.sub hg'B.meas, C + D, fun x =>
      (norm_sub_le _ _).trans (add_le_add (hC x) (hD x))⟩
  have h1 : borelCalc A hA g φ = borelCalc A hA g' φ := by
    have hsplit : g = g' + (g - g') := (add_sub_cancel g' g).symm
    have hz : borelCalc A hA (g - g') φ = 0 :=
      borelCalc_apply_eq_zero_of_ae hdiff (hgg'.mono fun x hx => by simp [hx])
    conv_lhs => rw [hsplit, borelCalc_add hg'B hdiff, ContinuousLinearMap.add_apply, hz, add_zero]
  -- step 2: polarization
  rw [h1, inner_borelCalc hg'B, sform_eq_sum]
  -- step 3: each polarization measure
  have hk : ∀ k, qform A hA g' (polV ψ φ k) =
      ∫ x, g x * (((ν k).rnDeriv μ x).toReal : ℂ) ∂μ := by
    intro k
    haveI : IsFiniteMeasure ((ν k).singularPart μ) :=
      isFiniteMeasure_of_le _ (Measure.singularPart_le _ _)
    haveI : IsFiniteMeasure (μ.withDensity ((ν k).rnDeriv μ)) :=
      isFiniteMeasure_of_le _ (Measure.withDensity_rnDeriv_le _ _)
    have hdec := Measure.haveLebesgueDecomposition_add (ν k) μ
    unfold qform
    change ∫ x, g' x ∂(ν k) = _
    conv_lhs => rw [hdec]
    rw [integral_add_measure (hg'B.integrable _) (hg'B.integrable _)]
    have hz : ∫ x, g' x ∂((ν k).singularPart μ) = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hs1 k)] with x hx
      have : x ∈ T := mem_iUnion.2 ⟨k, hx⟩
      simp [hg', indicator_of_notMem (show x ∉ Tᶜ from fun h => h this)]
    rw [hz, zero_add, integral_withDensity_eq_integral_toReal_smul (Measure.measurable_rnDeriv _ _)
      (Measure.rnDeriv_lt_top _ _)]
    refine integral_congr_ae ?_
    filter_upwards [hgg'] with x hx
    rw [Complex.real_smul, ← hx, mul_comm]
  simp only [hk]
  -- step 4: assemble
  have hint : ∀ k, Integrable (fun x => g x * (((ν k).rnDeriv μ x).toReal : ℂ)) μ := by
    intro k
    obtain ⟨C, hC⟩ := hg.bdd
    exact (Measure.integrable_toReal_rnDeriv.ofReal).bdd_mul hg.meas.aestronglyMeasurable
      (Eventually.of_forall hC)
  simp only [← integral_const_mul]
  rw [← integral_finset_sum _ fun k _ => (hint k).const_mul (polC k)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [matDensity, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- A function integrable against `μ` and annihilated by all bounded Borel test functions vanishes
`μ`-a.e. -/
lemma ae_eq_zero_of_forall_integral_mul {μ : Measure ℝ} [IsFiniteMeasure μ] {F : ℝ → ℂ}
    (hF : Integrable F μ) (h : ∀ g : ℝ → ℂ, IsBddBorel g → ∫ x, g x * F x ∂μ = 0) :
    F =ᵐ[μ] 0 := by
  refine hF.ae_eq_zero_of_forall_setIntegral_eq_zero fun S hS _ => ?_
  have := h (S.indicator 1) (isBddBorel_indicator hS)
  rw [← this, ← integral_indicator hS]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  by_cases hx : x ∈ S <;> simp [hx]

/-- `∫ |F|² dμ_φ ≤ ‖ψ‖²` for the density `F` of `⟪ψ, · φ⟫`. -/
lemma lintegral_norm_sq_matDensity_le (φ ψ : H) :
    ∫⁻ x, ‖matDensity A hA φ ψ x‖ₑ ^ 2 ∂(spectralMeasure A hA φ) ≤ ENNReal.ofReal (‖ψ‖ ^ 2) := by
  set μ := spectralMeasure A hA φ
  set F := matDensity A hA φ ψ
  have hFm : Measurable F := measurable_matDensity φ ψ
  -- truncations
  set s : ℕ → Set ℝ := fun M => {x | ‖F x‖ ≤ M} with hs
  have hsm : ∀ M, MeasurableSet (s M) := fun M => measurableSet_le hFm.norm measurable_const
  have hbound : ∀ M : ℕ, ∫ x in s M, ‖F x‖ ^ 2 ∂μ ≤ ‖ψ‖ ^ 2 := by
    intro M
    set gM : ℝ → ℂ := (s M).indicator fun x => conj (F x) with hgM
    have hgMB : IsBddBorel gM := by
      refine ⟨(hFm.star).indicator (hsm M), M, fun x => ?_⟩
      by_cases hx : x ∈ s M
      · simpa [hgM, indicator_of_mem hx] using hx
      · simp [hgM, indicator_of_notMem hx]
    have hrep := inner_borelCalc_eq_integral_density (A := A) (hA := hA) hgMB φ ψ
    set I := ∫ x in s M, ‖F x‖ ^ 2 ∂μ with hI
    have hI0 : 0 ≤ I := setIntegral_nonneg (hsm M) fun x _ => by positivity
    have hval : ∫ x, gM x * F x ∂μ = (I : ℂ) := by
      rw [hI, ← integral_complex_ofReal, ← integral_indicator (hsm M)]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ s M
      · simp only [hgM, indicator_of_mem hx, Complex.conj_mul', Complex.ofReal_pow]
      · simp [hgM, indicator_of_notMem hx]
    have hnorm : ‖borelCalc A hA gM φ‖ ^ 2 = I := by
      rw [norm_borelCalc_apply_sq hgMB, hI, ← integral_indicator (hsm M)]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      by_cases hx : x ∈ s M
      · simp [hgM, indicator_of_mem hx]
      · simp [hgM, indicator_of_notMem hx]
    -- `I = |⟪ψ, g_M(A) φ⟫| ≤ ‖ψ‖ √I`
    have hCS : I ≤ ‖ψ‖ * ‖borelCalc A hA gM φ‖ := by
      have := norm_inner_le_norm (𝕜 := ℂ) ψ (borelCalc A hA gM φ)
      rw [hrep, hval, Complex.norm_real, Real.norm_of_nonneg hI0] at this
      exact this
    have hsq : I ^ 2 ≤ ‖ψ‖ ^ 2 * I := by
      calc I ^ 2 ≤ (‖ψ‖ * ‖borelCalc A hA gM φ‖) ^ 2 := pow_le_pow_left₀ hI0 hCS 2
        _ = ‖ψ‖ ^ 2 * I := by rw [mul_pow, hnorm]
    rcases hI0.lt_or_eq with hpos | hzero
    · nlinarith
    · rw [← hzero]; positivity
  -- monotone convergence
  have hmono : Monotone fun M : ℕ => (s M).indicator fun x => ‖F x‖ₑ ^ 2 := by
    intro M N hMN x
    by_cases hx : x ∈ s M
    · have hxN : x ∈ s N := le_trans hx (by exact_mod_cast hMN)
      simp [indicator_of_mem hx, indicator_of_mem hxN]
    · simp [indicator_of_notMem hx]
  have hsup : (fun x => ‖F x‖ₑ ^ 2) =
      fun x => ⨆ M : ℕ, (s M).indicator (fun x => ‖F x‖ₑ ^ 2) x := by
    funext x
    obtain ⟨M, hM⟩ := exists_nat_ge ‖F x‖
    refine le_antisymm (le_iSup_of_le M (by simp [indicator_of_mem (show x ∈ s M from hM)])) ?_
    exact iSup_le fun N => indicator_le_self _ _ x
  rw [hsup, lintegral_iSup (fun M => ((hFm.enorm.pow_const 2).indicator (hsm M))) hmono]
  refine iSup_le fun M => ?_
  rw [lintegral_indicator (hsm M)]
  have hint : IntegrableOn (fun x => ‖F x‖ ^ 2) (s M) μ := by
    refine (integrable_const ((M : ℝ) ^ 2)).mono' (hFm.norm.pow_const 2).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (hsm M)] with x hx
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) hx 2
  have h1 : ∫⁻ x in s M, ‖F x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (∫ x in s M, ‖F x‖ ^ 2 ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x => by positivity)]
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [h1]
  exact ENNReal.ofReal_le_ofReal (hbound M)

end density

/-! ### Schrödinger operators -/

variable {V : ℤ → ℝ}

/-- The density `Fₙ` of `⟪δₙ, g(H) δ_b⟫` with respect to `μ_b = μ_{δ_b}`. -/
def eigDensity (hV : BddPot V) (b n : ℤ) : ℝ → ℂ :=
  matDensity (schr V) (isSelfAdjoint_schr hV) (dlt b) (dlt n)

/-- The spectral measure `μ_b` of `δ_b`. -/
abbrev muB (hV : BddPot V) (b : ℤ) : Measure ℝ :=
  spectralMeasure (schr V) (isSelfAdjoint_schr hV) (dlt b)

lemma eigDensity_rep (hV : BddPot V) (b n : ℤ) {g : ℝ → ℂ} (hg : IsBddBorel g) :
    ⟪dlt n, borelCalc (schr V) (isSelfAdjoint_schr hV) g (dlt b)⟫_ℂ =
      ∫ x, g x * eigDensity hV b n x ∂(muB hV b) :=
  inner_borelCalc_eq_integral_density hg _ _

lemma integrable_eigDensity (hV : BddPot V) (b n : ℤ) :
    Integrable (eigDensity hV b n) (muB hV b) := integrable_matDensity _ _

/-- `F_b = 1` a.e. -/
lemma eigDensity_self_ae (hV : BddPot V) (b : ℤ) : ∀ᵐ x ∂(muB hV b), eigDensity hV b b x = 1 := by
  have h := ae_eq_zero_of_forall_integral_mul ((integrable_eigDensity hV b b).sub
    (integrable_const (1 : ℂ))) fun g hg => by
    have h1 := eigDensity_rep hV b b hg
    rw [inner_borelCalc_self hg] at h1
    have e : (fun x => g x * (eigDensity hV b b - fun _ => (1 : ℂ)) x) =
        fun x => g x * eigDensity hV b b x - g x := by
      funext x; simp only [Pi.sub_apply]; ring
    rw [e, integral_sub ((integrable_eigDensity hV b b).bdd_mul hg.meas.aestronglyMeasurable
      (Eventually.of_forall (hg.bdd.choose_spec))) (hg.integrable _), ← h1, sub_self]
  filter_upwards [h] with x hx
  simpa [sub_eq_zero] using hx

/-- The eigenvalue equation for the densities, `μ_b`-a.e. -/
lemma eigDensity_eq_ae (hV : BddPot V) (b n : ℤ) :
    ∀ᵐ x ∂(muB hV b), eigDensity hV b (n - 1) x + eigDensity hV b (n + 1) x +
      (V n : ℂ) * eigDensity hV b n x = (x : ℂ) * eigDensity hV b n x := by
  set hH := isSelfAdjoint_schr hV
  set F := eigDensity hV b
  have hint : Integrable (fun x => F (n - 1) x + F (n + 1) x + (V n : ℂ) * F n x
      - truncId (schr V) x * F n x) (muB hV b) := by
    refine (((integrable_eigDensity hV b _).add (integrable_eigDensity hV b _)).add
      ((integrable_eigDensity hV b n).const_mul _)).sub ?_
    exact (integrable_eigDensity hV b n).bdd_mul (truncId_continuous.aestronglyMeasurable)
      (Eventually.of_forall norm_truncId_le)
  have h := ae_eq_zero_of_forall_integral_mul hint fun g hg => by
    -- `⟪H δₙ, g(H) δ_b⟫ = ⟪δₙ, H g(H) δ_b⟫`
    have hsym : ⟪schr V (dlt n), borelCalc (schr V) hH g (dlt b)⟫_ℂ =
        ⟪dlt n, borelCalc (schr V) hH (truncId (schr V) * g) (dlt b)⟫_ℂ := by
      rw [borelCalc_mul isBddBorel_truncId hg, borelCalc_truncId, ContinuousLinearMap.mul_apply]
      conv_lhs => rw [← hH.adjoint_eq]
      rw [ContinuousLinearMap.adjoint_inner_left]
    rw [schr_dlt hV, inner_add_left, inner_add_left, inner_smul_left, Complex.conj_ofReal,
      eigDensity_rep hV b _ hg, eigDensity_rep hV b _ hg, eigDensity_rep hV b _ hg,
      eigDensity_rep hV b _ (isBddBorel_truncId.mul hg)] at hsym
    have i1 := (integrable_eigDensity hV b (n - 1)).bdd_mul hg.meas.aestronglyMeasurable
      (Eventually.of_forall hg.bdd.choose_spec)
    have i2 := (integrable_eigDensity hV b (n + 1)).bdd_mul hg.meas.aestronglyMeasurable
      (Eventually.of_forall hg.bdd.choose_spec)
    have i3 := (integrable_eigDensity hV b n).bdd_mul hg.meas.aestronglyMeasurable
      (Eventually.of_forall hg.bdd.choose_spec)
    have i4 := (integrable_eigDensity hV b n).bdd_mul
      (isBddBorel_truncId.mul hg).meas.aestronglyMeasurable
      (Eventually.of_forall (isBddBorel_truncId.mul hg).bdd.choose_spec)
    have : ∫ x, g x * (F (n - 1) x + F (n + 1) x + (V n : ℂ) * F n x
        - truncId (schr V) x * F n x) ∂(muB hV b) =
        (∫ x, g x * F (n - 1) x ∂(muB hV b)) + (∫ x, g x * F (n + 1) x ∂(muB hV b)) +
          (V n : ℂ) * (∫ x, g x * F n x ∂(muB hV b)) -
          ∫ x, (truncId (schr V) * g) x * F n x ∂(muB hV b) := by
      have hY : Integrable (fun x => g x * F (n - 1) x + g x * F (n + 1) x) (muB hV b) :=
        i1.add i2
      have hX : Integrable (fun x => (g x * F (n - 1) x + g x * F (n + 1) x) +
          (V n : ℂ) * (g x * F n x)) (muB hV b) := hY.add (i3.const_mul _)
      have e : (fun x => g x * (F (n - 1) x + F (n + 1) x + (V n : ℂ) * F n x
          - truncId (schr V) x * F n x)) = fun x => ((g x * F (n - 1) x + g x * F (n + 1) x) +
          (V n : ℂ) * (g x * F n x)) - (truncId (schr V) * g) x * F n x := by
        funext x; simp only [Pi.mul_apply]; ring
      rw [e, integral_sub hX i4, integral_add hY (i3.const_mul _), integral_add i1 i2,
        integral_const_mul]
    rw [this, ← hsym, sub_self]
  filter_upwards [h, ae_mem_spectrum (schr V) hH (dlt b)] with x hx hxs
  have htr : truncId (schr V) x = (x : ℂ) := by
    have hle : |x| ≤ ‖schr V‖ := by
      have h1 := spectrum.subset_closedBall_norm_mul (𝕜 := ℝ) (schr V) hxs
      rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at h1
      exact h1.trans (mul_le_of_le_one_right (norm_nonneg _) ContinuousLinearMap.norm_id_le)
    simp only [truncId]
    rw [min_eq_left (abs_le.1 hle).2, max_eq_right (abs_le.1 hle).1]
  simp only [Pi.zero_apply, sub_eq_zero] at hx
  rw [hx, htr]

/-- `∫ |Fₙ|² dμ_b ≤ 1`. -/
lemma lintegral_eigDensity_le (hV : BddPot V) (b n : ℤ) :
    ∫⁻ x, ‖eigDensity hV b n x‖ₑ ^ 2 ∂(muB hV b) ≤ 1 := by
  have := lintegral_norm_sq_matDensity_le (A := schr V) (hA := isSelfAdjoint_schr hV)
    (dlt b) (dlt n)
  rwa [norm_dlt, one_pow, ENNReal.ofReal_one] at this

/-- The weights `wₙ = (1 + |n|)^{-2δ}` are summable for `δ > 1/2`. -/
lemma summable_weight {δ : ℝ} (hδ : 1 / 2 < δ) :
    Summable fun n : ℤ => (1 + |(n : ℝ)|) ^ (-(2 * δ)) := by
  have hb : 1 < 2 * δ := by linarith
  have hg : Summable fun n : ℤ => |(n : ℝ)| ^ (-(2 * δ)) + if n = 0 then 1 else 0 :=
    (Real.summable_abs_int_rpow hb).add (summable_of_ne_finset_zero (s := {0})
      fun n hn => by simp only [Finset.mem_singleton] at hn; simp [hn])
  refine hg.of_nonneg_of_le (fun n => by positivity) fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [Int.cast_zero, abs_zero, add_zero, Real.one_rpow]
    rw [if_pos rfl]
    have : (0 : ℝ) ≤ (0 : ℝ) ^ (-(2 * δ)) := Real.rpow_nonneg le_rfl _
    linarith
  · rw [if_neg hn, add_zero]
    exact Real.rpow_le_rpow_of_nonpos (abs_pos.2 (by exact_mod_cast hn)) (by linarith)
      (by linarith)

/-- **Theorem 2.4.2 (b)**, for the base vector `δ_b`: `μ_b`-a.e. `E` is a generalized eigenvalue
with exponent `δ`. -/
theorem ae_mem_genEigSet (hV : BddPot V) (b : ℤ) {δ : ℝ} (hδ : 1 / 2 < δ) :
    ∀ᵐ x ∂(muB hV b), (x : ℂ) ∈ genEigSet V δ := by
  set w : ℤ → ℝ≥0∞ := fun n => ENNReal.ofReal ((1 + |(n : ℝ)|) ^ (-(2 * δ)))
  set F := eigDensity hV b
  -- `∑ wₙ |Fₙ|²` is integrable, hence finite a.e.
  have hmeas : ∀ n, Measurable fun x => w n * ‖F n x‖ₑ ^ 2 := fun n =>
    measurable_const.mul ((measurable_matDensity _ _).enorm.pow_const 2)
  have hfin : ∫⁻ x, ∑' n, w n * ‖F n x‖ₑ ^ 2 ∂(muB hV b) < ∞ := by
    rw [lintegral_tsum fun n => (hmeas n).aemeasurable]
    calc ∑' n, ∫⁻ x, w n * ‖F n x‖ₑ ^ 2 ∂(muB hV b)
        ≤ ∑' n, w n := ENNReal.tsum_le_tsum fun n => by
          rw [lintegral_const_mul _ ((measurable_matDensity _ _).enorm.pow_const 2)]
          calc w n * ∫⁻ x, ‖F n x‖ₑ ^ 2 ∂(muB hV b) ≤ w n * 1 :=
                mul_le_mul_left' (lintegral_eigDensity_le hV b n) _
            _ = w n := mul_one _
      _ < ∞ := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) (summable_weight hδ)]
          exact ENNReal.ofReal_lt_top
  have hae := ae_lt_top' (AEMeasurable.ennreal_tsum fun n => (hmeas n).aemeasurable) hfin.ne
  have heq : ∀ᵐ x ∂(muB hV b), ∀ n, F (n - 1) x + F (n + 1) x + (V n : ℂ) * F n x =
      (x : ℂ) * F n x := ae_all_iff.2 fun n => eigDensity_eq_ae hV b n
  filter_upwards [hae, heq, eigDensity_self_ae hV b] with x hx hxeq hx1
  set K := (∑' n, w n * ‖F n x‖ₑ ^ 2).toReal
  refine ⟨fun n => F n x, ?_, fun n => hxeq n, Real.sqrt K, fun n => ?_⟩
  · intro h0
    have := congrFun h0 b
    simp only [Pi.zero_apply] at this
    rw [hx1] at this
    exact one_ne_zero this
  · -- `wₙ |Fₙ|² ≤ K`
    have hterm : w n * ‖F n x‖ₑ ^ 2 ≤ ∑' m, w m * ‖F m x‖ₑ ^ 2 :=
      ENNReal.le_tsum (f := fun m => w m * ‖F m x‖ₑ ^ 2) n
    have hwpos : 0 < (1 + |(n : ℝ)|) ^ (-(2 * δ)) := by positivity
    have hreal : (1 + |(n : ℝ)|) ^ (-(2 * δ)) * ‖F n x‖ ^ 2 ≤ K := by
      have := ENNReal.toReal_mono hx.ne hterm
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hwpos.le, ENNReal.toReal_pow,
        toReal_enorm] at this
    have hK0 : 0 ≤ K := ENNReal.toReal_nonneg
    have hbase : 0 < 1 + |(n : ℝ)| := by positivity
    -- `‖Fₙ‖² ≤ K (1 + |n|)^{2δ}`
    have hsq : ‖F n x‖ ^ 2 ≤ (Real.sqrt K * (1 + |(n : ℝ)|) ^ δ) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hK0, ← Real.rpow_natCast ((1 + |(n : ℝ)|) ^ δ) 2,
        ← Real.rpow_mul hbase.le]
      have hinv : (1 + |(n : ℝ)|) ^ (δ * ((2 : ℕ) : ℝ)) * (1 + |(n : ℝ)|) ^ (-(2 * δ)) = 1 := by
        rw [← Real.rpow_add hbase, show δ * ((2 : ℕ) : ℝ) + -(2 * δ) = 0 by push_cast; ring,
          Real.rpow_zero]
      calc ‖F n x‖ ^ 2 = ((1 + |(n : ℝ)|) ^ (δ * ((2 : ℕ) : ℝ)) * (1 + |(n : ℝ)|) ^ (-(2 * δ)))
            * ‖F n x‖ ^ 2 := by rw [hinv, one_mul]
        _ = (1 + |(n : ℝ)|) ^ (δ * ((2 : ℕ) : ℝ)) *
            ((1 + |(n : ℝ)|) ^ (-(2 * δ)) * ‖F n x‖ ^ 2) := by ring
        _ ≤ (1 + |(n : ℝ)|) ^ (δ * ((2 : ℕ) : ℝ)) * K :=
            mul_le_mul_of_nonneg_left hreal (by positivity)
        _ = K * (1 + |(n : ℝ)|) ^ (δ * ((2 : ℕ) : ℝ)) := mul_comm _ _
    have hX : 0 ≤ Real.sqrt K * (1 + |(n : ℝ)|) ^ δ := by positivity
    calc ‖F n x‖ = Real.sqrt (‖F n x‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((Real.sqrt K * (1 + |(n : ℝ)|) ^ δ) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = Real.sqrt K * (1 + |(n : ℝ)|) ^ δ := Real.sqrt_sq hX

end DF

namespace DF

variable {V : ℤ → ℝ}

/-- **Theorem 2.4.2 (b)**: for every `δ > 1/2`, `G_δ` supports the canonical spectral measure. -/
theorem genEigSupport (hV : BddPot V) : GenEigSupportStatement V hV := by
  intro δ hδ
  have h0 := ae_mem_genEigSet hV 0 hδ
  have h1 := ae_mem_genEigSet hV 1 hδ
  rw [ae_iff] at h0 h1
  simp only [canonicalMeasure, Measure.add_apply]
  rw [show (spectralMeasure (schr V) (isSelfAdjoint_schr hV) (dlt 0))
      {E : ℝ | (E : ℂ) ∉ genEigSet V δ} = 0 from h0,
    show (spectralMeasure (schr V) (isSelfAdjoint_schr hV) (dlt 1))
      {E : ℝ | (E : ℂ) ∉ genEigSet V δ} = 0 from h1, add_zero]

/-- **Theorem 2.4.2 (c)**, unconditionally: `σ(H) = closure G`. -/
theorem spectrum_eq_closure_genEig' (hV : BddPot V) :
    spectrum ℝ (schr V) = closure (genEigReal V) :=
  spectrum_eq_closure_genEig hV (genEigSupport hV)

end DF
