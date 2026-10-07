/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Chapter 4 preliminaries: measurable families of self-adjoint operators
(book §4.2, pp. 309–312: Lemma 4.2.1, Exercises 4.2.1, 4.2.3, 4.2.4)

Operator-theoretic tools, stated for an arbitrary complex Hilbert space `H`, used to set up the
ergodic theory of Chapter 4 (`DamanikFillman/Ch4/Setting.lean`).

## Main results
* `DF.integral_eval_spectralMeasure` — moments: `∫ p dμ_φ = Re ⟪φ, p(A) φ⟫` for polynomials `p`.
* `DF.spectralMeasure_unitary_conj` — `μ^{UAU*}_φ = μ^A_{U*φ}` for unitary `U`; consequently
  `DF.borelCalc_unitary_conj`: `g(UAU*) = U g(A) U*` for bounded Borel `g` (Exercise 4.2.1).
* `DF.measurable_spectralMeasure` — if `ω ↦ A_ω` is a uniformly bounded family of self-adjoint
  operators whose moments `ω ↦ ⟪φ, A_ω^k φ⟫` are measurable, then `ω ↦ μ^{A_ω}_φ` is a
  measurable map into the space of measures (Giry σ-algebra).
* `DF.measurable_integral_of_bdd`, `DF.measurable_integral_complex_of_bdd` — integrals of bounded
  measurable functions against a measurable family of finite measures are measurable.
* `DF.measurable_inner_borelCalc` — **Lemma 4.2.1** (first part, in the general form of weak
  measurability of `g(A_ω)` for every bounded Borel `g`): `ω ↦ ⟪φ, g(A_ω) ψ⟫` is measurable.
  The book argues via strong limits of polynomials (Exercise 4.2.3); we go through the
  measurability of the spectral measures, which is equivalent and more convenient.
* `DF.mem_spectrum_iff_specProj` — `E ∈ σ(A)` iff `P(E-ε, E+ε) ≠ 0` for every `ε > 0`
  (used in §4.2, p. 310).

No `Statement` props are introduced in this file.
-/
import DamanikFillman.Ch1.SpectralDecomposition

noncomputable section

open scoped InnerProductSpace ComplexConjugate NNReal ENNReal Topology
open MeasureTheory Set Filter Polynomial

namespace DF

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Moments -/

section Moments

variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)

/-- Moments of spectral measures: `∫ p dμ_φ = Re ⟪φ, p(A) φ⟫` for real polynomials `p`. -/
theorem integral_eval_spectralMeasure (φ : H) (p : ℝ[X]) :
    ∫ x, p.eval x ∂(spectralMeasure A hA φ) = RCLike.re ⟪φ, aeval A p φ⟫_ℂ := by
  rw [integral_spectralMeasure_re A hA φ (Polynomial.continuous p), ← cfc_polynomial p A hA]

/-- Expansion of `⟪φ, p(A) φ⟫` in terms of the moments `⟪φ, Aᵏ φ⟫`. -/
lemma inner_aeval_eq_sum (φ : H) (p : ℝ[X]) :
    ⟪φ, aeval A p φ⟫_ℂ =
      ∑ i ∈ Finset.range (p.natDegree + 1), (p.coeff i : ℂ) * ⟪φ, (A ^ i) φ⟫_ℂ := by
  rw [aeval_eq_sum_range, ContinuousLinearMap.sum_apply, inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousLinearMap.smul_apply, ← Complex.coe_smul, inner_smul_right]

end Moments

/-! ### Unitary conjugation (Exercise 4.2.1) -/

section Conj

variable {A : H →L[ℂ] H} (hA : IsSelfAdjoint A)

/-- Spectral measures under unitary conjugation: `μ^{UAU*}_φ = μ^A_{U*φ}`. -/
theorem spectralMeasure_unitary_conj {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
    (hB : IsSelfAdjoint (U * A * star U)) (φ : H) :
    spectralMeasure (U * A * star U) hB φ = spectralMeasure A hA (star U φ) := by
  symm
  refine spectralMeasure_unique' _ hB φ _ fun f hf => ?_
  rw [integral_spectralMeasure_re A hA _ hf]
  congr 1
  let u : unitary (H →L[ℂ] H) := ⟨U, hU⟩
  have hcont : Continuous (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) u) := by
    have : (⇑(Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) u)) = fun x => U * x * star U :=
      funext fun x => rfl
    rw [this]; fun_prop
  have hc : cfc f (U * A * star U) = U * cfc f A * star U := by
    have := StarAlgHomClass.map_cfc (S := ℂ) (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) u) f A
      hf.continuousOn hcont hA hB
    exact this.symm
  rw [hc, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.star_eq_adjoint]
  exact ContinuousLinearMap.adjoint_inner_left U _ φ

/-- **Exercise 4.2.1**: `g(UAU*) = U g(A) U*` for bounded Borel `g`. -/
theorem borelCalc_unitary_conj {U : H →L[ℂ] H} (hU : U ∈ unitary (H →L[ℂ] H))
    (hB : IsSelfAdjoint (U * A * star U)) {g : ℝ → ℂ} (hg : IsBddBorel g) :
    borelCalc (U * A * star U) hB g = U * borelCalc A hA g * star U := by
  refine borelCalc_eq_of_inner hg fun φ => ?_
  rw [spectralMeasure_unitary_conj hA hU hB, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
    ← inner_borelCalc_self hg]
  exact (ContinuousLinearMap.adjoint_inner_left U _ φ).symm

end Conj

/-! ### Measurable families of finite measures -/

section MeasureFamily

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Integrals of a bounded measurable function against a measurable family of finite measures
depend measurably on the parameter. -/
theorem measurable_integral_of_bdd {ν : Ω → Measure ℝ} [∀ ω, IsFiniteMeasure (ν ω)]
    (hν : Measurable ν) {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, |g x| ≤ C) :
    Measurable fun ω => ∫ x, g x ∂(ν ω) := by
  have hint : ∀ ω, Integrable g (ν ω) := fun ω =>
    (integrable_const C).mono' hg.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x)
  simp_rw [fun ω => integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hint ω)]
  exact (((Measure.measurable_lintegral hg.ennreal_ofReal).comp hν).ennreal_toReal).sub
    (((Measure.measurable_lintegral hg.neg.ennreal_ofReal).comp hν).ennreal_toReal)

/-- Complex version of `measurable_integral_of_bdd`. -/
theorem measurable_integral_complex_of_bdd {ν : Ω → Measure ℝ} [∀ ω, IsFiniteMeasure (ν ω)]
    (hν : Measurable ν) {g : ℝ → ℂ} (hg : IsBddBorel g) :
    Measurable fun ω => ∫ x, g x ∂(ν ω) := by
  obtain ⟨C, hC⟩ := hg.bdd
  have hint : ∀ ω, Integrable g (ν ω) := fun ω => hg.integrable _
  have h1 : Measurable fun ω => ∫ x, (g x).re ∂(ν ω) :=
    measurable_integral_of_bdd hν (Complex.measurable_re.comp hg.meas)
      (fun x => (Complex.abs_re_le_norm _).trans (hC x))
  have h2 : Measurable fun ω => ∫ x, (g x).im ∂(ν ω) :=
    measurable_integral_of_bdd hν (Complex.measurable_im.comp hg.meas)
      (fun x => (Complex.abs_im_le_norm _).trans (hC x))
  have : (fun ω => ∫ x, g x ∂(ν ω)) =
      fun ω => ((∫ x, (g x).re ∂(ν ω) : ℝ) : ℂ) + ((∫ x, (g x).im ∂(ν ω) : ℝ) : ℂ) * Complex.I := by
    funext ω
    rw [← integral_re_add_im (hint ω)]
    rfl
  rw [this]
  exact (Complex.measurable_ofReal.comp h1).add
    ((Complex.measurable_ofReal.comp h2).mul_const _)

end MeasureFamily

/-! ### Measurable families of self-adjoint operators -/

section Family

variable {Ω : Type*} [MeasurableSpace Ω] (A : Ω → H →L[ℂ] H) (hA : ∀ ω, IsSelfAdjoint (A ω))

lemma measurable_integral_eval (φ : H) (hm : ∀ k : ℕ, Measurable fun ω => ⟪φ, (A ω ^ k) φ⟫_ℂ)
    (p : ℝ[X]) : Measurable fun ω => ∫ x, p.eval x ∂(spectralMeasure (A ω) (hA ω) φ) := by
  simp_rw [integral_eval_spectralMeasure, inner_aeval_eq_sum]
  exact RCLike.continuous_re.measurable.comp
    (Finset.measurable_sum _ fun i _ => (hm i).const_mul _)

/-- The spectral measures of a bounded family with measurable moments are concentrated on a
common compact interval. -/
lemma ae_mem_Icc_spectralMeasure {R : ℝ} (hR : ∀ ω, ‖A ω‖ ≤ R) (φ : H) (ω : Ω) :
    ∀ᵐ x ∂(spectralMeasure (A ω) (hA ω) φ), x ∈ Icc (-R) R := by
  filter_upwards [ae_mem_spectrum (A ω) (hA ω) φ] with x hx
  exact abs_le.1 ((abs_le_norm_of_mem_spectrum hx).trans (hR ω))

/-- Integrals of continuous functions against `μ^{A_ω}_φ` are measurable in `ω`
(Weierstrass approximation by polynomials). -/
theorem measurable_integral_continuous {R : ℝ} (hR : ∀ ω, ‖A ω‖ ≤ R) (φ : H)
    (hm : ∀ k : ℕ, Measurable fun ω => ⟪φ, (A ω ^ k) φ⟫_ℂ) {g : ℝ → ℝ} (hg : Continuous g) :
    Measurable fun ω => ∫ x, g x ∂(spectralMeasure (A ω) (hA ω) φ) := by
  have hp : ∀ n : ℕ, ∃ p : ℝ[X], ∀ x ∈ Icc (-R) R, |p.eval x - g x| < 1 / (n + 1) := fun n =>
    exists_polynomial_near_of_continuousOn (-R) R g hg.continuousOn _ (by positivity)
  choose p hp using hp
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    hg.continuousOn
  refine measurable_of_tendsto_metrizable (fun n => measurable_integral_eval A hA φ hm (p n)) ?_
  rw [tendsto_pi_nhds]
  intro ω
  have hsupp := ae_mem_Icc_spectralMeasure A hA hR φ ω
  refine tendsto_integral_of_dominated_convergence (fun _ => K + 1)
    (fun n => (Polynomial.continuous (p n)).aestronglyMeasurable) (integrable_const _)
    (fun n => ?_) ?_
  · filter_upwards [hsupp] with x hx
    have h1 := hp n x hx
    have h2 := hK x hx
    rw [Real.norm_eq_abs] at h2 ⊢
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    calc |(p n).eval x| = |((p n).eval x - g x) + g x| := by ring_nf
      _ ≤ |(p n).eval x - g x| + |g x| := abs_add_le _ _
      _ ≤ K + 1 := by linarith
  · filter_upwards [hsupp] with x hx
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => (hp n x hx).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat

/-- Continuous cutoffs increasing to the indicator of `(-∞, a)`. -/
def cutIio (a : ℝ) (k : ℕ) (x : ℝ) : ℝ := max 0 (min 1 ((k + 1) * (a - x)))

lemma continuous_cutIio (a : ℝ) (k : ℕ) : Continuous (cutIio a k) := by
  unfold cutIio; fun_prop

lemma cutIio_nonneg (a : ℝ) (k : ℕ) (x : ℝ) : 0 ≤ cutIio a k x := le_max_left _ _

lemma cutIio_le_one (a : ℝ) (k : ℕ) (x : ℝ) : cutIio a k x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma cutIio_mono (a : ℝ) (x : ℝ) : Monotone fun k => cutIio a k x := by
  intro k l hkl
  dsimp only
  unfold cutIio
  rcases le_or_gt (a - x) 0 with h | h
  · have h1 : ((k : ℝ) + 1) * (a - x) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    rw [max_eq_left ((min_le_right _ _).trans h1)]
    exact le_max_left _ _
  · have : ((k : ℝ) + 1) * (a - x) ≤ ((l : ℝ) + 1) * (a - x) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hkl 1) h.le
    exact max_le_max le_rfl (min_le_min le_rfl this)

lemma iSup_cutIio (a x : ℝ) :
    ⨆ k : ℕ, ENNReal.ofReal (cutIio a k x) = (Iio a).indicator 1 x := by
  by_cases hx : x < a
  · rw [indicator_of_mem (show x ∈ Iio a from hx), Pi.one_apply]
    refine le_antisymm (iSup_le fun k => ?_) ?_
    · rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (cutIio_le_one a k x)
    · obtain ⟨k, hk⟩ := exists_nat_ge (1 / (a - x))
      refine le_iSup_of_le k (le_of_eq ?_)
      have hax : 0 < a - x := sub_pos.2 hx
      have : 1 ≤ ((k : ℝ) + 1) * (a - x) := by
        rw [div_le_iff₀ hax] at hk; nlinarith
      rw [cutIio, min_eq_left this, max_eq_right zero_le_one, ENNReal.ofReal_one]
  · rw [indicator_of_notMem (show x ∉ Iio a from hx)]
    refine le_antisymm (iSup_le fun k => ?_) zero_le
    have h1 : ((k : ℝ) + 1) * (a - x) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith [not_lt.1 hx])
    rw [cutIio, max_eq_left ((min_le_right _ _).trans h1), ENNReal.ofReal_zero]

/-- `ν(-∞, a) = sup_k ∫ cutIio a k dν` for finite measures. -/
lemma measure_Iio_eq_iSup (ν : Measure ℝ) [IsFiniteMeasure ν] (a : ℝ) :
    ν (Iio a) = ⨆ k : ℕ, ENNReal.ofReal (∫ x, cutIio a k x ∂ν) := by
  have hint : ∀ k, Integrable (cutIio a k) ν := fun k =>
    (integrable_const (1 : ℝ)).mono' (continuous_cutIio a k).aestronglyMeasurable
      (ae_of_all _ fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (cutIio_nonneg a k x)]; exact cutIio_le_one a k x)
  simp_rw [fun k => ofReal_integral_eq_lintegral_ofReal (hint k)
    (ae_of_all _ (cutIio_nonneg a k))]
  rw [← lintegral_iSup (fun k => (continuous_cutIio a k).measurable.ennreal_ofReal)
    (fun k l hkl x => ENNReal.ofReal_le_ofReal (cutIio_mono a x hkl))]
  simp_rw [iSup_cutIio]
  rw [lintegral_indicator_one measurableSet_Iio]

/-- **Measurability of spectral measures.** For a uniformly bounded family of self-adjoint
operators whose moments `⟪φ, A_ω^k φ⟫` are measurable in `ω`, the spectral measure `μ^{A_ω}_φ`
is a measurable function of `ω`. -/
theorem measurable_spectralMeasure {R : ℝ} (hR : ∀ ω, ‖A ω‖ ≤ R) (φ : H)
    (hm : ∀ k : ℕ, Measurable fun ω => ⟪φ, (A ω ^ k) φ⟫_ℂ) :
    Measurable fun ω => spectralMeasure (A ω) (hA ω) φ := by
  refine Measurable.measure_of_isPiSystem
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Iio ℝ)) isPiSystem_Iio ?_ ?_
  · rintro _ ⟨a, rfl⟩
    simp_rw [measure_Iio_eq_iSup]
    exact .iSup fun k => ENNReal.measurable_ofReal.comp
      (measurable_integral_continuous A hA hR φ hm (continuous_cutIio a k))
  · simp_rw [spectralMeasure_univ]
    exact measurable_const

/-- **Lemma 4.2.1** (weak measurability of `g(A_ω)`): if the moments `⟪v, A_ω^k v⟫` are
measurable for all vectors `v`, then `ω ↦ ⟪φ, g(A_ω) ψ⟫` is measurable for every bounded
Borel function `g` (in particular for the spectral projections `χ_I(A_ω)`). -/
theorem measurable_inner_borelCalc {R : ℝ} (hR : ∀ ω, ‖A ω‖ ≤ R)
    (hm : ∀ v : H, ∀ k : ℕ, Measurable fun ω => ⟪v, (A ω ^ k) v⟫_ℂ) {g : ℝ → ℂ}
    (hg : IsBddBorel g) (φ ψ : H) :
    Measurable fun ω => ⟪φ, borelCalc (A ω) (hA ω) g ψ⟫_ℂ := by
  simp_rw [inner_borelCalc hg, sform_eq_sum, qform]
  exact Finset.measurable_sum _ fun k _ =>
    (measurable_integral_complex_of_bdd
      (measurable_spectralMeasure A hA hR _ (hm _)) hg).const_mul _

end Family

/-! ### The spectrum in terms of spectral projections -/

section SpectrumProj

variable {A : H →L[ℂ] H} {hA : IsSelfAdjoint A}

/-- `P(S) = 0` iff `μ_φ(S) = 0` for all `φ`. -/
lemma specProj_eq_zero_iff {S : Set ℝ} (hS : MeasurableSet S) :
    specProj A hA S = 0 ↔ ∀ φ, spectralMeasure A hA φ S = 0 := by
  constructor
  · intro h φ
    rw [← specProj_apply_eq_zero_iff hS, h, ContinuousLinearMap.zero_apply]
  · intro h
    ext φ
    rw [ContinuousLinearMap.zero_apply, specProj_apply_eq_zero_iff hS]
    exact h φ

/-- If `σ(A)` misses `S`, then `P(S) = 0`. -/
lemma specProj_eq_zero_of_disjoint_mf {S : Set ℝ} (hS : MeasurableSet S)
    (hd : Disjoint S (spectrum ℝ A)) : specProj A hA S = 0 :=
  (specProj_eq_zero_iff hS).2 fun φ =>
    measure_mono_null (fun x hx hx' => hd.ne_of_mem hx hx' rfl)
      (spectralMeasure_compl_spectrum A hA φ)

/-- If the spectral projection of a neighbourhood `(E - ε, E + ε)` vanishes, then `E ∉ σ(A)`:
an explicit inverse of `A - E` is `g(A)` with `g(x) = χ_{ℝ∖(E-ε,E+ε)}(x) (x - E)⁻¹`. -/
theorem notMem_spectrum_of_specProj_eq_zero {E ε : ℝ} (hε : 0 < ε)
    (h0 : specProj A hA (Ioo (E - ε) (E + ε)) = 0) : E ∉ spectrum ℝ A := by
  set J := Ioo (E - ε) (E + ε) with hJ
  have hJm : MeasurableSet J := measurableSet_Ioo
  have hEJ : E ∈ J := ⟨by linarith, by linarith⟩
  set g : ℝ → ℂ := Jᶜ.indicator fun x => ((x : ℂ) - E)⁻¹ with hgdef
  have hg : IsBddBorel g := by
    refine ⟨Measurable.indicator (by fun_prop) hJm.compl, 1 / ε, fun x => ?_⟩
    by_cases hx : x ∈ J
    · rw [hgdef, indicator_of_notMem (by simpa using hx)]; simp; positivity
    · rw [hgdef, indicator_of_mem (by simpa using hx), norm_inv, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs]
      have : ε ≤ |x - E| := by
        rw [hJ, mem_Ioo, not_and_or, not_lt, not_lt] at hx
        rcases hx with hx | hx
        · rw [abs_of_nonpos (by linarith)]; linarith
        · rw [abs_of_nonneg (by linarith)]; linarith
      rw [one_div]
      exact inv_anti₀ hε this
  set hf : ℝ → ℂ := truncId A + fun _ => -(E : ℂ) with hfdef
  have hh : IsBddBorel hf := isBddBorel_truncId.add (isBddBorel_const _)
  have hAE : borelCalc A hA hf = A + (-(E : ℂ)) • 1 := by
    rw [borelCalc_add isBddBorel_truncId (isBddBorel_const _), borelCalc_truncId, borelCalc_const]
  have hcompl : borelCalc A hA (Jᶜ.indicator fun _ => (1 : ℂ)) = 1 := by
    have := specProj_add_compl (A := A) (hA := hA) hJm
    rw [h0, zero_add] at this
    exact this
  have hprod : ∀ x ∈ spectrum ℝ A, (g * hf) x =
      Jᶜ.indicator (fun _ => (1 : ℂ)) x := by
    intro x hx
    have hx' := abs_le_norm_of_mem_spectrum hx
    have ht : truncId A x = (x : ℂ) := by
      simp only [truncId]; rw [min_eq_left (abs_le.1 hx').2, max_eq_right (abs_le.1 hx').1]
    simp only [hfdef, Pi.mul_apply, Pi.add_apply, ht]
    by_cases hxJ : x ∈ J
    · rw [hgdef, indicator_of_notMem (by simpa using hxJ), indicator_of_notMem (by simpa using hxJ),
        zero_mul]
    · have hxE : (x : ℂ) - E ≠ 0 := by
        rw [sub_ne_zero, Ne, Complex.ofReal_inj]; rintro rfl; exact hxJ hEJ
      rw [hgdef, indicator_of_mem (by simpa using hxJ), indicator_of_mem (by simpa using hxJ),
        ← sub_eq_add_neg, inv_mul_cancel₀ hxE]
  have h1 : borelCalc A hA g * (A + (-(E : ℂ)) • 1) = 1 := by
    rw [← hAE, ← borelCalc_mul hg hh, ← hcompl]
    exact borelCalc_congr_spectrum (hg.mul hh) (isBddBorel_indicator hJm.compl) hprod
  have h2 : (A + (-(E : ℂ)) • 1) * borelCalc A hA g = 1 := by
    rw [← hAE, borelCalc_comm hh hg, hAE]; exact h1
  intro hmem
  rw [spectrum.mem_iff] at hmem
  apply hmem
  have hu : IsUnit (A + (-(E : ℂ)) • 1) := ⟨⟨_, _, h2, h1⟩, rfl⟩
  have : algebraMap ℝ (H →L[ℂ] H) E - A = -(A + (-(E : ℂ)) • 1) := by
    rw [Algebra.algebraMap_eq_smul_one, neg_add, neg_smul, neg_neg, ← Complex.coe_smul]
    abel
  rw [this]
  exact hu.neg

/-- If `E ∉ σ(A)` then the spectral projection of some neighbourhood of `E` vanishes. -/
theorem exists_specProj_eq_zero_of_notMem {E : ℝ} (hE : E ∉ spectrum ℝ A) :
    ∃ ε > 0, specProj A hA (Ioo (E - ε) (E + ε)) = 0 := by
  have hopen : IsOpen (spectrum ℝ A)ᶜ := (isCompact_spectrum_real A).isClosed.isOpen_compl
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hopen E hE
  refine ⟨ε, hε, specProj_eq_zero_of_disjoint_mf measurableSet_Ioo ?_⟩
  rw [← Real.ball_eq_Ioo]
  exact Set.subset_compl_iff_disjoint_right.1 hball

/-- `E ∈ σ(A)` iff `P(E - ε, E + ε) ≠ 0` for every `ε > 0` (book p. 310). -/
theorem mem_spectrum_iff_specProj (E : ℝ) :
    E ∈ spectrum ℝ A ↔ ∀ ε > 0, specProj A hA (Ioo (E - ε) (E + ε)) ≠ 0 := by
  constructor
  · intro hE ε hε h0
    exact notMem_spectrum_of_specProj_eq_zero hε h0 hE
  · intro h
    by_contra hE
    obtain ⟨ε, hε, h0⟩ := exists_specProj_eq_zero_of_notMem (hA := hA) hE
    exact h ε hε h0

end SpectrumProj

end DF
