/-
Formalization of Damanik–Fillman, *One-Dimensional Ergodic Schrödinger Operators I*, Chapter 1.

# The Borel functional calculus  (book §1.4, Theorem 1.4.14 and the discussion after it,
pp. 30–31)

For a bounded self-adjoint operator `A` on a complex Hilbert space and a bounded Borel function
`f : ℝ → ℂ`, we construct `f(A) = DF.borelCalc A hA f` through its matrix elements (1.4.22):
`⟪φ, f(A) ψ⟫` is the polarization of the quadratic form `φ ↦ ∫ f dμ_φ`.

The key technical tool replacing the complex measures `μ_{φ,ψ}` is an *extension principle*
(`DF.combo_ext`, `DF.combo_ext_density`): a finite complex linear combination of integrals
against finite Borel measures on `ℝ` that vanishes for all compactly supported continuous
functions vanishes for all bounded Borel functions (by Riesz–Markov uniqueness).

Main results
* `DF.borelCalc` — `f(A)` for bounded Borel `f` (Theorem 1.4.14(a));
* `DF.inner_borelCalc_self` — `⟪φ, f(A) φ⟫ = ∫ f dμ_φ` (1.4.22);
* `DF.borelCalc_eq_cfc` — agreement with the continuous functional calculus;
* `DF.borelCalc_add`, `DF.borelCalc_smul`, `DF.borelCalc_one`, `DF.borelCalc_conj`,
  `DF.borelCalc_mul` — `f ↦ f(A)` is a unital `*`-homomorphism (Theorem 1.4.14(b));
* `DF.norm_borelCalc_apply_le` — `‖f(A) φ‖ ≤ sup |f| ‖φ‖`;
* `DF.tendsto_borelCalc_apply` — bounded pointwise convergence gives strong convergence
  (Theorem 1.4.14(c));
* `DF.specProj` — spectral projections `P(S) = χ_S(A)`, with
  `⟪φ, P(S) φ⟫ = μ_φ(S)`, `P(S)² = P(S) = P(S)*`, `P(S ∩ T) = P(S) P(T)`, `P(ℝ) = I`,
  `P(∅) = 0` (p. 31).

Deviations
* Functions are defined on all of `ℝ` (not just on `σ(A)`); only their values on `σ(A)` matter,
  since `μ_φ` is supported on `σ(A)`.

No `Statement` props are introduced in this file.
-/
import DamanikFillman.Ch1.SpectralMeasure

noncomputable section

open scoped InnerProductSpace ComplexConjugate CompactlySupported NNReal ENNReal Topology
open MeasureTheory Set Filter CompactlySupportedContinuousMap

namespace DF

/-! ### Bounded Borel functions -/

/-- A bounded Borel function `ℝ → ℂ` (the book's class `B(σ(A))`). -/
structure IsBddBorel (f : ℝ → ℂ) : Prop where
  meas : Measurable f
  bdd : ∃ C, ∀ x, ‖f x‖ ≤ C

lemma IsBddBorel.integrable {f : ℝ → ℂ} (hf : IsBddBorel f) (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Integrable f μ :=
  let ⟨C, hC⟩ := hf.bdd
  Integrable.of_bound hf.meas.aestronglyMeasurable C (Eventually.of_forall hC)

lemma IsBddBorel.add {f g : ℝ → ℂ} (hf : IsBddBorel f) (hg : IsBddBorel g) :
    IsBddBorel (f + g) := by
  obtain ⟨C, hC⟩ := hf.bdd; obtain ⟨D, hD⟩ := hg.bdd
  exact ⟨hf.meas.add hg.meas, C + D, fun x => (norm_add_le _ _).trans (add_le_add (hC x) (hD x))⟩

lemma IsBddBorel.mul {f g : ℝ → ℂ} (hf : IsBddBorel f) (hg : IsBddBorel g) :
    IsBddBorel (f * g) := by
  obtain ⟨C, hC⟩ := hf.bdd; obtain ⟨D, hD⟩ := hg.bdd
  refine ⟨hf.meas.mul hg.meas, C * D, fun x => ?_⟩
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul (hC x) (hD x) (norm_nonneg _) ((norm_nonneg _).trans (hC x))

lemma IsBddBorel.const_mul {f : ℝ → ℂ} (c : ℂ) (hf : IsBddBorel f) :
    IsBddBorel (fun x => c * f x) := by
  obtain ⟨C, hC⟩ := hf.bdd
  refine ⟨measurable_const.mul hf.meas, ‖c‖ * C, fun x => ?_⟩
  rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hC x) (norm_nonneg _)

lemma IsBddBorel.conj {f : ℝ → ℂ} (hf : IsBddBorel f) : IsBddBorel (fun x => conj (f x)) := by
  obtain ⟨C, hC⟩ := hf.bdd
  exact ⟨Complex.continuous_conj.measurable.comp hf.meas, C, fun x => by simpa using hC x⟩

lemma isBddBorel_const (c : ℂ) : IsBddBorel (fun _ => c) := ⟨measurable_const, ‖c‖, fun _ => le_rfl⟩

lemma isBddBorel_indicator {S : Set ℝ} (hS : MeasurableSet S) :
    IsBddBorel (S.indicator (fun _ => (1 : ℂ))) := by
  refine ⟨measurable_const.indicator hS, 1, fun x => ?_⟩
  by_cases hx : x ∈ S <;> simp [hx]

lemma isBddBorel_of_continuous_of_hasCompactSupport {f : ℝ → ℂ} (hf : Continuous f)
    (hc : HasCompactSupport f) : IsBddBorel f := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuous hf
  exact ⟨hf.measurable, C, hC⟩

/-! ### The extension principle -/

lemma isFiniteMeasure_sum_smul {ι : Type*} [Fintype ι] (ν : ι → Measure ℝ)
    [∀ i, IsFiniteMeasure (ν i)] (c : ι → ℝ≥0∞) (hc : ∀ i, c i ≠ ⊤) :
    IsFiniteMeasure (∑ i, c i • ν i) := by
  constructor
  rw [Measure.coe_finset_sum, Finset.sum_apply]
  refine ENNReal.sum_lt_top.2 fun i _ => ?_
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 (hc i)) (measure_lt_top _ _)

lemma integral_sum_smul {ι : Type*} [Fintype ι] (ν : ι → Measure ℝ) [∀ i, IsFiniteMeasure (ν i)]
    (a : ι → ℝ) (g : ℝ → ℂ) (hg : ∀ i, Integrable g (ν i)) :
    ∫ x, g x ∂(∑ i, ENNReal.ofReal (a i) • ν i) = ∑ i, (max (a i) 0 : ℝ) • ∫ x, g x ∂ν i := by
  rw [integral_finsetSum_measure (fun i _ => (hg i).smul_measure ENNReal.ofReal_ne_top)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_measure, ENNReal.toReal_ofReal']

/-- Extension principle, real coefficients. -/
theorem combo_ext_real {ι : Type*} [Fintype ι] (ν : ι → Measure ℝ) [∀ i, IsFiniteMeasure (ν i)]
    (a : ι → ℝ) (h : ∀ f : C_c(ℝ, ℝ), ∑ i, a i * ∫ x, f x ∂ν i = 0)
    (g : ℝ → ℂ) (hg : ∀ i, Integrable g (ν i)) : ∑ i, (a i : ℂ) * ∫ x, g x ∂ν i = 0 := by
  have := isFiniteMeasure_sum_smul ν (fun i => ENNReal.ofReal (a i)) fun _ => ENNReal.ofReal_ne_top
  have := isFiniteMeasure_sum_smul ν (fun i => ENNReal.ofReal (-a i)) fun _ => ENNReal.ofReal_ne_top
  have hreal : ∀ (b : ι → ℝ) (u : ℝ → ℝ), (∀ i, Integrable u (ν i)) →
      ∫ x, u x ∂(∑ i, ENNReal.ofReal (b i) • ν i) = ∑ i, max (b i) 0 * ∫ x, u x ∂ν i := by
    intro b u hu
    rw [integral_finsetSum_measure (fun i _ => (hu i).smul_measure ENNReal.ofReal_ne_top)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_smul_measure, ENNReal.toReal_ofReal', smul_eq_mul]
  have heq : (∑ i, ENNReal.ofReal (a i) • ν i) = ∑ i, ENNReal.ofReal (-a i) • ν i := by
    refine Measure.ext_of_integral_eq_on_compactlySupported fun f => ?_
    rw [hreal a f (fun i => f.integrable), hreal (fun i => -a i) f (fun i => f.integrable),
      ← sub_eq_zero, ← Finset.sum_sub_distrib]
    refine (Finset.sum_congr rfl fun i _ => ?_).trans (h f)
    rw [← sub_mul, max_zero_sub_eq_self]
  have h1 := integral_sum_smul ν a g hg
  have h2 := integral_sum_smul ν (fun i => -a i) g hg
  rw [heq, h2] at h1
  have : ∑ i, (a i : ℂ) * ∫ x, g x ∂ν i =
      ∑ i, (max (a i) 0 : ℝ) • ∫ x, g x ∂ν i - ∑ i, (max (-a i) 0 : ℝ) • ∫ x, g x ∂ν i := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← sub_smul, max_zero_sub_eq_self, Complex.real_smul]
  rw [this, h1, sub_self]

/-- **Extension principle** (complex coefficients): a combination `∑ cᵢ ∫ f dνᵢ` of finite
measures vanishing on `C_c(ℝ, ℝ)` vanishes for every function integrable for all `νᵢ`. -/
theorem combo_ext {ι : Type*} [Fintype ι] (ν : ι → Measure ℝ) [∀ i, IsFiniteMeasure (ν i)]
    (c : ι → ℂ) (h : ∀ f : C_c(ℝ, ℝ), ∑ i, c i * ((∫ x, f x ∂ν i : ℝ) : ℂ) = 0)
    (g : ℝ → ℂ) (hg : ∀ i, Integrable g (ν i)) : ∑ i, c i * ∫ x, g x ∂ν i = 0 := by
  have hre : ∀ f : C_c(ℝ, ℝ), ∑ i, (c i).re * ∫ x, f x ∂ν i = 0 := by
    intro f
    have := congrArg Complex.re (h f)
    simpa [Complex.re_sum] using this
  have him : ∀ f : C_c(ℝ, ℝ), ∑ i, (c i).im * ∫ x, f x ∂ν i = 0 := by
    intro f
    have := congrArg Complex.im (h f)
    simpa [Complex.im_sum] using this
  have h1 := combo_ext_real ν (fun i => (c i).re) hre g hg
  have h2 := combo_ext_real ν (fun i => (c i).im) him g hg
  calc ∑ i, c i * ∫ x, g x ∂ν i
      = ∑ i, ((c i).re : ℂ) * ∫ x, g x ∂ν i +
          Complex.I * ∑ i, ((c i).im : ℂ) * ∫ x, g x ∂ν i := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        conv_lhs => rw [← Complex.re_add_im (c i)]
        ring
    _ = 0 := by rw [h1, h2, mul_zero, add_zero]

lemma isFiniteMeasure_withDensity_of_le (ν : Measure ℝ) [IsFiniteMeasure ν] (p : ℝ → ℝ≥0)
    (C : ℝ≥0) (hp : ∀ x, p x ≤ C) : IsFiniteMeasure (ν.withDensity fun x => (p x : ℝ≥0∞)) := by
  refine isFiniteMeasure_withDensity ?_
  refine ne_top_of_le_ne_top (b := (C : ℝ≥0∞) * ν univ) (ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top ν univ)) ?_
  calc ∫⁻ x, (p x : ℝ≥0∞) ∂ν ≤ ∫⁻ _, (C : ℝ≥0∞) ∂ν :=
        lintegral_mono fun x => ENNReal.coe_le_coe.2 (hp x)
    _ = C * ν univ := lintegral_const _

/-- The four nonnegative parts of a complex function, `h = p₀ + i p₁ - p₂ - i p₃`. -/
def cplxPart (h : ℝ → ℂ) : Fin 4 → ℝ → ℝ≥0
  | 0 => fun x => Real.toNNReal (h x).re
  | 1 => fun x => Real.toNNReal (h x).im
  | 2 => fun x => Real.toNNReal (-(h x).re)
  | 3 => fun x => Real.toNNReal (-(h x).im)

/-- The coefficients `1, i, -1, -i`. -/
def cplxCoeff : Fin 4 → ℂ := ![1, Complex.I, -1, -Complex.I]

lemma sum_cplxPart (h : ℝ → ℂ) (x : ℝ) :
    ∑ k, cplxCoeff k * ((cplxPart h k x : ℝ) : ℂ) = h x := by
  simp only [Fin.sum_univ_four, cplxCoeff, cplxPart, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Real.coe_toNNReal']
  apply Complex.ext <;> simp <;> ring_nf <;> rw [max_zero_sub_eq_self]

lemma measurable_cplxPart {h : ℝ → ℂ} (hh : Measurable h) (k : Fin 4) :
    Measurable (cplxPart h k) := by
  fin_cases k <;> simp only [cplxPart] <;> fun_prop

lemma cplxPart_le {h : ℝ → ℂ} {C : ℝ} (hC : ∀ x, ‖h x‖ ≤ C) (k : Fin 4) (x : ℝ) :
    cplxPart h k x ≤ Real.toNNReal C := by
  have h1 := (Complex.abs_re_le_norm (h x)).trans (hC x)
  have h2 := (Complex.abs_im_le_norm (h x)).trans (hC x)
  fin_cases k <;> simp only [cplxPart] <;> refine Real.toNNReal_le_toNNReal ?_ <;>
    first
    | linarith [le_abs_self (h x).re, neg_abs_le (h x).re]
    | linarith [le_abs_self (h x).im, neg_abs_le (h x).im]

/-- **Extension principle with bounded Borel densities**: if
`∑ᵢ ∫ f hᵢ dνᵢ = 0` for all `f ∈ C_c(ℝ, ℝ)`, then also `∑ᵢ ∫ g hᵢ dνᵢ = 0` for all bounded Borel
`g`. -/
theorem combo_ext_density {ι : Type*} [Fintype ι] (ν : ι → Measure ℝ)
    [∀ i, IsFiniteMeasure (ν i)] (h : ι → ℝ → ℂ) (hh : ∀ i, IsBddBorel (h i))
    (hyp : ∀ f : C_c(ℝ, ℝ), ∑ i, ∫ x, (f x : ℂ) * h i x ∂ν i = 0)
    (g : ℝ → ℂ) (hg : IsBddBorel g) : ∑ i, ∫ x, g x * h i x ∂ν i = 0 := by
  choose C hC using fun i => (hh i).bdd
  set ρ : ι × Fin 4 → Measure ℝ := fun ik =>
    (ν ik.1).withDensity fun x => (cplxPart (h ik.1) ik.2 x : ℝ≥0∞)
  have hρ : ∀ ik, IsFiniteMeasure (ρ ik) := fun ik =>
    isFiniteMeasure_withDensity_of_le _ _ _ (cplxPart_le (hC ik.1) ik.2)
  -- integrals against `h dν` are combinations of integrals against `ρ`
  have key : ∀ (u : ℝ → ℂ), IsBddBorel u → ∀ i,
      ∫ x, u x * h i x ∂ν i = ∑ k, cplxCoeff k * ∫ x, u x ∂ρ (i, k) := by
    intro u hu i
    have hint : ∀ k, Integrable (fun x => ((cplxPart (h i) k x : ℝ) : ℂ) * u x) (ν i) := by
      intro k
      refine (IsBddBorel.mul ⟨?_, ?_⟩ hu).integrable _
      · exact (Complex.measurable_ofReal.comp
          (measurable_coe_nnreal_real.comp (measurable_cplxPart (hh i).meas k)))
      · exact ⟨C i, fun x => by
          have := cplxPart_le (hC i) k x
          simp only [Complex.norm_real, Real.norm_eq_abs, NNReal.abs_eq]
          calc ((cplxPart (h i) k x : ℝ)) ≤ (Real.toNNReal (C i) : ℝ) := by exact_mod_cast this
            _ = max (C i) 0 := Real.coe_toNNReal' _
            _ ≤ C i := max_le le_rfl ((norm_nonneg _).trans (hC i x))⟩
    have : ∀ k, ∫ x, u x ∂ρ (i, k) = ∫ x, ((cplxPart (h i) k x : ℝ) : ℂ) * u x ∂ν i := by
      intro k
      simp only [ρ]
      rw [integral_withDensity_eq_integral_smul (measurable_cplxPart (hh i).meas k)]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [NNReal.smul_def, Complex.real_smul]
    simp_rw [this, ← integral_const_mul]
    rw [← integral_finsetSum _ fun k _ => (hint k).const_mul (cplxCoeff k)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [← sum_cplxPart (h i) x, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hcomb := combo_ext ρ (fun ik => cplxCoeff ik.2) ?_ g fun ik => hg.integrable _
  · rw [Fintype.sum_prod_type] at hcomb
    rw [← hcomb]
    exact Finset.sum_congr rfl fun i _ => key g hg i
  · intro f
    rw [Fintype.sum_prod_type, ← hyp f]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [key (fun x => (f x : ℂ)) (isBddBorel_of_continuous_of_hasCompactSupport
      (Complex.continuous_ofReal.comp f.continuous)
      (f.hasCompactSupport.comp_left Complex.ofReal_zero)) i]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_complex_ofReal]

/-! ### Polarization for operators -/

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Polarization for an arbitrary bounded operator: `⟪x, T y⟫` in terms of the quadratic form
`v ↦ ⟪v, T v⟫`. -/
lemma inner_polarization (T : H →L[ℂ] H) (x y : H) :
    ⟪x, T y⟫_ℂ = (⟪x + y, T (x + y)⟫_ℂ - ⟪x - y, T (x - y)⟫_ℂ
      - Complex.I * ⟪x + Complex.I • y, T (x + Complex.I • y)⟫_ℂ
      + Complex.I * ⟪x - Complex.I • y, T (x - Complex.I • y)⟫_ℂ) / 4 := by
  simp only [map_add, map_sub, map_smul, inner_add_left, inner_add_right, inner_sub_left,
    inner_sub_right, inner_smul_left, inner_smul_right, Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- An operator on a complex Hilbert space is determined by its quadratic form. -/
lemma op_ext_of_inner_self {S T : H →L[ℂ] H} (h : ∀ x, ⟪x, S x⟫_ℂ = ⟪x, T x⟫_ℂ) : S = T := by
  have := (ext_inner_map (S : H →ₗ[ℂ] H) (T : H →ₗ[ℂ] H)).1 fun x => by
    simp only [ContinuousLinearMap.coe_coe]
    rw [← inner_conj_symm, h x, inner_conj_symm]
  exact ContinuousLinearMap.coe_injective this

/-! ### The quadratic and sesquilinear forms -/

variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A)

/-- The quadratic form `φ ↦ ∫ f dμ_φ`. -/
def qform (f : ℝ → ℂ) (φ : H) : ℂ := ∫ x, f x ∂(spectralMeasure A hA φ)

/-- The polarized form, the book's `∫ f dμ_{φ,ψ}` (1.4.22). -/
def sform (f : ℝ → ℂ) (φ ψ : H) : ℂ :=
  (qform A hA f (φ + ψ) - qform A hA f (φ - ψ) - Complex.I * qform A hA f (φ + Complex.I • ψ)
    + Complex.I * qform A hA f (φ - Complex.I • ψ)) / 4

lemma qform_smul (f : ℝ → ℂ) (c : ℂ) (φ : H) :
    qform A hA f (c • φ) = ((‖c‖ ^ 2 : ℝ) : ℂ) * qform A hA f φ := by
  rw [qform, qform, spectralMeasure_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (by positivity), Complex.real_smul]

lemma qform_neg (f : ℝ → ℂ) (φ : H) : qform A hA f (-φ) = qform A hA f φ := by
  rw [← neg_one_smul ℂ φ, qform_smul]; simp

lemma qform_zero (f : ℝ → ℂ) : qform A hA f 0 = 0 := by
  rw [← zero_smul ℂ (0 : H), qform_smul]; simp

/-- For continuous `f`, the quadratic form is `⟪φ, f(A) φ⟫`. -/
lemma qform_eq_inner_cfc {f : ℝ → ℂ} (hf : Continuous f) (φ : H) :
    qform A hA f φ = ⟪φ, cfc (fun z : ℂ => f z.re) A φ⟫_ℂ :=
  integral_spectralMeasure_complex A hA φ hf

/-- For continuous `f`, the polarized form is `⟪φ, f(A) ψ⟫`. -/
lemma sform_eq_inner_cfc {f : ℝ → ℂ} (hf : Continuous f) (φ ψ : H) :
    sform A hA f φ ψ = ⟪φ, cfc (fun z : ℂ => f z.re) A ψ⟫_ℂ := by
  simp only [sform, qform_eq_inner_cfc A hA hf]
  rw [inner_polarization (cfc (fun z : ℂ => f z.re) A) φ ψ]

/-- The vectors and coefficients of the polarization identity. -/
def polV (u w : H) : Fin 4 → H := ![u + w, u - w, u + Complex.I • w, u - Complex.I • w]

def polC : Fin 4 → ℂ := ![1 / 4, -1 / 4, -Complex.I / 4, Complex.I / 4]

lemma sform_eq_sum (f : ℝ → ℂ) (u w : H) :
    sform A hA f u w = ∑ k, polC k * qform A hA f (polV u w k) := by
  simp [sform, Fin.sum_univ_four, polC, polV]
  ring

/-- Extension principle in terms of the polarized form. -/
lemma sform_ext_density (u w φ : H) (h0 : ℝ → ℂ) (hh0 : IsBddBorel h0)
    (hyp : ∀ f : C_c(ℝ, ℝ),
      sform A hA (fun x => (f x : ℂ)) u w = ∫ x, (f x : ℂ) * h0 x ∂(spectralMeasure A hA φ))
    (g : ℝ → ℂ) (hg : IsBddBorel g) :
    sform A hA g u w = ∫ x, g x * h0 x ∂(spectralMeasure A hA φ) := by
  let ν : Option (Fin 4) → Measure ℝ := fun o => match o with
    | none => spectralMeasure A hA φ
    | some k => spectralMeasure A hA (polV u w k)
  let h : Option (Fin 4) → ℝ → ℂ := fun o => match o with
    | none => h0
    | some k => fun _ => -polC k
  have hν : ∀ o, IsFiniteMeasure (ν o) := fun o => by cases o <;> infer_instance
  have hh : ∀ o, IsBddBorel (h o) := fun o => by
    cases o
    · exact hh0
    · exact isBddBorel_const _
  have key : ∀ u' : ℝ → ℂ, (∑ o, ∫ x, u' x * h o x ∂ν o) =
      ∫ x, u' x * h0 x ∂(spectralMeasure A hA φ) - sform A hA u' u w := by
    intro u'
    rw [Fintype.sum_option, sform_eq_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [h, ν, qform]
    rw [integral_mul_const, mul_neg, mul_comm]
  have := combo_ext_density ν h hh (fun f => by rw [key, hyp f, sub_self]) g hg
  rw [key, sub_eq_zero] at this
  exact this.symm

end Hilbert

end DF
