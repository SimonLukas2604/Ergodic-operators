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

lemma sum_polC_inner (T : H →L[ℂ] H) (u w : H) :
    ∑ k, polC k * ⟪polV u w k, T (polV u w k)⟫_ℂ = ⟪u, T w⟫_ℂ := by
  rw [inner_polarization T u w]
  simp [Fin.sum_univ_four, polC, polV]
  ring

/-- Extension principle for quadratic forms: an identity `∑ cₖ ⟪vₖ, T vₖ⟫ = 0` valid for all
operators `T` gives `∑ cₖ ∫ g dμ_{vₖ} = 0` for all bounded Borel `g`. -/
lemma combo_qform {ι : Type*} [Fintype ι] (v : ι → H) (c : ι → ℂ)
    (hT : ∀ T : H →L[ℂ] H, ∑ k, c k * ⟪v k, T (v k)⟫_ℂ = 0) (g : ℝ → ℂ) (hg : IsBddBorel g) :
    ∑ k, c k * qform A hA g (v k) = 0 := by
  refine combo_ext (fun k => spectralMeasure A hA (v k)) c (fun f => ?_) g
    (fun k => hg.integrable _)
  rw [← hT (cfc (fun z : ℂ => ((f z.re : ℝ) : ℂ)) A)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← integral_complex_ofReal]
  congr 1
  exact qform_eq_inner_cfc A hA (f := fun x => ((f x : ℝ) : ℂ)) (by fun_prop) (v k)

/-- Extension principle for the polarized form. -/
lemma sform_combo {m : ℕ} (s : Fin m → ℂ) (u w : Fin m → H)
    (hT : ∀ T : H →L[ℂ] H, ∑ j, s j * ⟪u j, T (w j)⟫_ℂ = 0) (g : ℝ → ℂ) (hg : IsBddBorel g) :
    ∑ j, s j * sform A hA g (u j) (w j) = 0 := by
  have := combo_qform A hA (fun jk : Fin m × Fin 4 => polV (u jk.1) (w jk.1) jk.2)
    (fun jk => s jk.1 * polC jk.2) (fun T => ?_) g hg
  · rw [Fintype.sum_prod_type] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sform_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  · rw [Fintype.sum_prod_type, ← hT T]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← sum_polC_inner T (u j) (w j), Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring

variable {A hA}

lemma sform_add_right {g : ℝ → ℂ} (hg : IsBddBorel g) (φ ψ₁ ψ₂ : H) :
    sform A hA g φ (ψ₁ + ψ₂) = sform A hA g φ ψ₁ + sform A hA g φ ψ₂ := by
  have := sform_combo A hA ![1, -1, -1] ![φ, φ, φ] ![ψ₁ + ψ₂, ψ₁, ψ₂]
    (fun T => by simp [Fin.sum_univ_three, map_add]) g hg
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at this
  linear_combination this

lemma sform_smul_right {g : ℝ → ℂ} (hg : IsBddBorel g) (c : ℂ) (φ ψ : H) :
    sform A hA g φ (c • ψ) = c * sform A hA g φ ψ := by
  have := sform_combo A hA ![1, -c] ![φ, φ] ![c • ψ, ψ]
    (fun T => by simp [Fin.sum_univ_two, map_smul]) g hg
  norm_num [Fin.sum_univ_two] at this
  linear_combination this

omit [CompleteSpace H] in
lemma polV_aux1 (φ ψ : H) : ψ + Complex.I • φ = Complex.I • (φ - Complex.I • ψ) := by
  rw [smul_sub, smul_smul, Complex.I_mul_I, neg_one_smul, sub_neg_eq_add, add_comm]

omit [CompleteSpace H] in
lemma polV_aux2 (φ ψ : H) : ψ - Complex.I • φ = (-Complex.I) • (φ + Complex.I • ψ) := by
  rw [smul_add, smul_smul, neg_mul, Complex.I_mul_I, neg_neg, one_smul, neg_smul, add_comm,
    sub_eq_add_neg]

lemma qform_conj (g : ℝ → ℂ) (v : H) :
    qform A hA (fun x => conj (g x)) v = conj (qform A hA g v) := integral_conj

/-- Hermitian symmetry of the polarized form. -/
lemma sform_conj_symm (g : ℝ → ℂ) (φ ψ : H) :
    sform A hA g φ ψ = conj (sform A hA (fun x => conj (g x)) ψ φ) := by
  simp only [sform, qform_conj, map_div₀, map_add, map_sub, map_mul, Complex.conj_conj,
    Complex.conj_I, map_ofNat]
  rw [add_comm ψ φ, ← neg_sub φ ψ, qform_neg, polV_aux1 φ ψ, polV_aux2 φ ψ, qform_smul,
    qform_smul]
  simp only [norm_neg, Complex.norm_I, one_pow, Complex.ofReal_one, one_mul]
  ring

lemma sform_add_left {g : ℝ → ℂ} (hg : IsBddBorel g) (φ₁ φ₂ ψ : H) :
    sform A hA g (φ₁ + φ₂) ψ = sform A hA g φ₁ ψ + sform A hA g φ₂ ψ := by
  rw [sform_conj_symm, sform_add_right hg.conj, map_add, ← sform_conj_symm, ← sform_conj_symm]

lemma sform_smul_left {g : ℝ → ℂ} (hg : IsBddBorel g) (c : ℂ) (φ ψ : H) :
    sform A hA g (c • φ) ψ = conj c * sform A hA g φ ψ := by
  rw [sform_conj_symm, sform_smul_right hg.conj, map_mul, ← sform_conj_symm]

lemma norm_qform_le {g : ℝ → ℂ} {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) (v : H) :
    ‖qform A hA g v‖ ≤ C * ‖v‖ ^ 2 := by
  rw [qform, ← spectralMeasure_real_univ A hA v]
  exact MeasureTheory.norm_integral_le_of_norm_le_const (Eventually.of_forall hC)

lemma norm_sform_le {g : ℝ → ℂ} {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) (φ ψ : H) :
    ‖sform A hA g φ ψ‖ ≤ C * (‖φ‖ ^ 2 + ‖ψ‖ ^ 2) := by
  have h1 := norm_qform_le (A := A) (hA := hA) hC (φ + ψ)
  have h2 := norm_qform_le (A := A) (hA := hA) hC (φ - ψ)
  have h3 := norm_qform_le (A := A) (hA := hA) hC (φ + Complex.I • ψ)
  have h4 := norm_qform_le (A := A) (hA := hA) hC (φ - Complex.I • ψ)
  have p1 := parallelogram_law_with_norm ℂ φ ψ
  have p2 := parallelogram_law_with_norm ℂ φ (Complex.I • ψ)
  rw [norm_smul, Complex.norm_I, one_mul] at p2
  rw [sform, norm_div, Complex.norm_ofNat]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 4)]
  calc ‖qform A hA g (φ + ψ) - qform A hA g (φ - ψ) - Complex.I * qform A hA g (φ + Complex.I • ψ)
        + Complex.I * qform A hA g (φ - Complex.I • ψ)‖
      ≤ ‖qform A hA g (φ + ψ)‖ + ‖qform A hA g (φ - ψ)‖ + ‖qform A hA g (φ + Complex.I • ψ)‖
        + ‖qform A hA g (φ - Complex.I • ψ)‖ := by
        refine (norm_add_le _ _).trans ?_
        refine add_le_add ((norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) ?_)) ?_
        · rw [norm_mul, Complex.norm_I, one_mul]
        · rw [norm_mul, Complex.norm_I, one_mul]
    _ ≤ C * ‖φ + ψ‖ ^ 2 + C * ‖φ - ψ‖ ^ 2 + C * ‖φ + Complex.I • ψ‖ ^ 2
        + C * ‖φ - Complex.I • ψ‖ ^ 2 := by gcongr
    _ = C * (‖φ‖ ^ 2 + ‖ψ‖ ^ 2) * 4 := by linear_combination C * p1 + C * p2

lemma norm_sform_le' {g : ℝ → ℂ} (hg : IsBddBorel g) {C : ℝ} (hC : ∀ x, ‖g x‖ ≤ C)
    (φ ψ : H) : ‖sform A hA g φ ψ‖ ≤ 2 * C * ‖φ‖ * ‖ψ‖ := by
  by_cases hφ : φ = 0
  · subst hφ
    have : sform A hA g 0 ψ = 0 := by
      have h := sform_add_left (A := A) (hA := hA) hg 0 0 ψ
      rw [add_zero] at h
      linear_combination -h
    rw [this]; simp
  by_cases hψ : ψ = 0
  · subst hψ
    have : sform A hA g φ 0 = 0 := by
      have h := sform_add_right (A := A) (hA := hA) hg φ 0 0
      rw [add_zero] at h
      linear_combination -h
    rw [this]; simp
  have hφ' : 0 < ‖φ‖ := norm_pos_iff.2 hφ
  have hψ' : 0 < ‖ψ‖ := norm_pos_iff.2 hψ
  set φ' := ((‖φ‖⁻¹ : ℝ) : ℂ) • φ
  set ψ' := ((‖ψ‖⁻¹ : ℝ) : ℂ) • ψ
  have hφ1 : ‖φ'‖ = 1 := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity), inv_mul_cancel₀ hφ'.ne']
  have hψ1 : ‖ψ'‖ = 1 := by
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity), inv_mul_cancel₀ hψ'.ne']
  have hφe : φ = ((‖φ‖ : ℝ) : ℂ) • φ' := by
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hφ'.ne', Complex.ofReal_one, one_smul]
  have hψe : ψ = ((‖ψ‖ : ℝ) : ℂ) • ψ' := by
    rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hψ'.ne', Complex.ofReal_one, one_smul]
  have hb := norm_sform_le (A := A) (hA := hA) hC φ' ψ'
  rw [hφ1, hψ1] at hb
  conv_lhs => rw [hφe, hψe, sform_smul_left hg, sform_smul_right hg, Complex.conj_ofReal,
    norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
    Real.norm_of_nonneg (norm_nonneg _)]
  nlinarith [norm_nonneg (sform A hA g φ' ψ'), mul_pos hφ' hψ']

variable (A hA)

/-- The bounded sesquilinear form `(φ, ψ) ↦ ∫ g dμ_{φ,ψ}` as a continuous map. -/
def sformCLM (g : ℝ → ℂ) (hg : IsBddBorel g) : H →L⋆[ℂ] H →L[ℂ] ℂ :=
  (LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (sform A hA g)
    (sform_add_left hg) (fun c φ ψ => by rw [sform_smul_left hg]; rfl)
    (sform_add_right hg) (fun c φ ψ => by rw [sform_smul_right hg]; rfl)).mkContinuous₂
    (2 * Classical.choose hg.bdd) (norm_sform_le' hg (Classical.choose_spec hg.bdd))

open Classical in
/-- **Borel functional calculus** (Theorem 1.4.14): `g(A)` for a bounded Borel function `g`,
defined by `⟪φ, g(A) ψ⟫ = ∫ g dμ_{φ,ψ}` (1.4.22).  (Junk value `0` if `g` is not bounded
Borel.) -/
def borelCalc (g : ℝ → ℂ) : H →L[ℂ] H :=
  if hg : IsBddBorel g then
    ContinuousLinearMap.adjoint (InnerProductSpace.continuousLinearMapOfBilin (sformCLM A hA g hg))
  else 0

variable {A hA}

/-- Matrix elements of `g(A)`, (1.4.22). -/
theorem inner_borelCalc {g : ℝ → ℂ} (hg : IsBddBorel g) (φ ψ : H) :
    ⟪φ, borelCalc A hA g ψ⟫_ℂ = sform A hA g φ ψ := by
  rw [borelCalc, dif_pos hg, ContinuousLinearMap.adjoint_inner_right,
    InnerProductSpace.continuousLinearMapOfBilin_apply]
  rfl

lemma sform_self (g : ℝ → ℂ) (φ : H) : sform A hA g φ φ = qform A hA g φ := by
  have e1 : φ + φ = (2 : ℂ) • φ := by rw [two_smul]
  have e2 : φ + Complex.I • φ = (1 + Complex.I) • φ := by rw [add_smul, one_smul]
  have e3 : φ - Complex.I • φ = (1 - Complex.I) • φ := by rw [sub_smul, one_smul]
  have n1 : ‖(1 + Complex.I)‖ ^ 2 = 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; norm_num
  have n2 : ‖(1 - Complex.I)‖ ^ 2 = 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; simp; norm_num
  rw [sform, e1, e2, e3, sub_self, qform_zero, qform_smul, qform_smul, qform_smul, n1, n2]
  simp only [Complex.norm_ofNat]
  push_cast
  ring

/-- `⟪φ, g(A) φ⟫ = ∫ g dμ_φ`. -/
theorem inner_borelCalc_self {g : ℝ → ℂ} (hg : IsBddBorel g) (φ : H) :
    ⟪φ, borelCalc A hA g φ⟫_ℂ = ∫ x, g x ∂(spectralMeasure A hA φ) := by
  rw [inner_borelCalc hg, sform_self]; rfl

/-- `g(A)` is characterised by its diagonal matrix elements. -/
theorem borelCalc_eq_of_inner {g : ℝ → ℂ} (hg : IsBddBorel g) {T : H →L[ℂ] H}
    (hT : ∀ φ, ⟪φ, T φ⟫_ℂ = ∫ x, g x ∂(spectralMeasure A hA φ)) : borelCalc A hA g = T :=
  op_ext_of_inner_self fun φ => by rw [inner_borelCalc_self hg, hT]

/-- Agreement with the continuous functional calculus. -/
theorem borelCalc_eq_cfc {g : ℝ → ℂ} (hg : Continuous g) (hb : ∃ C, ∀ x, ‖g x‖ ≤ C) :
    borelCalc A hA g = cfc (fun z : ℂ => g z.re) A :=
  borelCalc_eq_of_inner ⟨hg.measurable, hb⟩ fun φ =>
    (integral_spectralMeasure_complex A hA φ hg).symm

theorem borelCalc_add {f g : ℝ → ℂ} (hf : IsBddBorel f) (hg : IsBddBorel g) :
    borelCalc A hA (f + g) = borelCalc A hA f + borelCalc A hA g :=
  borelCalc_eq_of_inner (hf.add hg) fun φ => by
    rw [_root_.add_apply, inner_add_right, inner_borelCalc_self hf,
      inner_borelCalc_self hg, ← integral_add (hf.integrable _) (hg.integrable _)]
    rfl

theorem borelCalc_const_mul {f : ℝ → ℂ} (hf : IsBddBorel f) (c : ℂ) :
    borelCalc A hA (fun x => c * f x) = c • borelCalc A hA f :=
  borelCalc_eq_of_inner (hf.const_mul c) fun φ => by
    rw [_root_.smul_apply, inner_smul_right, inner_borelCalc_self hf,
      integral_const_mul]

theorem borelCalc_const (c : ℂ) : borelCalc A hA (fun _ => c) = c • 1 :=
  borelCalc_eq_of_inner (isBddBorel_const c) fun φ => by
    rw [_root_.smul_apply, one_apply_eq_self, inner_smul_right,
      inner_self_eq_norm_sq_to_K, integral_const, spectralMeasure_real_univ A hA φ,
      Complex.real_smul, mul_comm]
    push_cast; rfl

theorem borelCalc_one : borelCalc A hA (fun _ => (1 : ℂ)) = 1 := by
  rw [borelCalc_const, one_smul]

theorem borelCalc_conj {f : ℝ → ℂ} (hf : IsBddBorel f) :
    borelCalc A hA (fun x => conj (f x)) = ContinuousLinearMap.adjoint (borelCalc A hA f) :=
  borelCalc_eq_of_inner hf.conj fun φ => by
    rw [ContinuousLinearMap.adjoint_inner_right, ← inner_conj_symm, inner_borelCalc_self hf,
      integral_conj]

/-- Real bounded Borel functions give self-adjoint operators. -/
theorem isSelfAdjoint_borelCalc {f : ℝ → ℂ} (hf : IsBddBorel f) (hr : ∀ x, conj (f x) = f x) :
    IsSelfAdjoint (borelCalc A hA f) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', ← borelCalc_conj hf]
  simp_rw [hr]

/-! ### Multiplicativity -/

omit [CompleteSpace H] in
lemma cc_continuous (F : C_c(ℝ, ℝ)) : Continuous fun x => ((F x : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp F.continuous

omit [CompleteSpace H] in
lemma cc_bound (F : C_c(ℝ, ℝ)) : ∃ D, ∀ x, ‖((F x : ℝ) : ℂ)‖ ≤ D :=
  (F.hasCompactSupport.comp_left Complex.ofReal_zero).exists_bound_of_continuous (cc_continuous F)

omit [CompleteSpace H] in
lemma cc_isBddBorel (F : C_c(ℝ, ℝ)) : IsBddBorel fun x => ((F x : ℝ) : ℂ) :=
  ⟨(cc_continuous F).measurable, cc_bound F⟩

/-- Multiplicativity when the second factor is continuous. -/
lemma borelCalc_mul_of_continuous {f g : ℝ → ℂ} (hf : IsBddBorel f) (hg : Continuous g)
    (hgb : ∃ C, ∀ x, ‖g x‖ ≤ C) :
    borelCalc A hA (f * g) = borelCalc A hA f * borelCalc A hA g := by
  have hgB : IsBddBorel g := ⟨hg.measurable, hgb⟩
  refine borelCalc_eq_of_inner (hf.mul hgB) fun φ => ?_
  rw [ContinuousLinearMap.mul_apply, inner_borelCalc hf]
  refine sform_ext_density (A := A) (hA := hA) φ (borelCalc A hA g φ) φ g hgB (fun F => ?_) f hf
  rw [sform_eq_inner_cfc A hA (f := fun x => ((F x : ℝ) : ℂ)) (cc_continuous F),
    borelCalc_eq_cfc hg hgb, ← ContinuousLinearMap.mul_apply,
    ← cfc_mul (fun z : ℂ => ((F z.re : ℝ) : ℂ)) (fun z : ℂ => g z.re) A (by fun_prop)
      (by fun_prop)]
  exact (integral_spectralMeasure_complex A hA φ
    (f := fun x => ((F x : ℝ) : ℂ) * g x) (by fun_prop)).symm

/-- **Multiplicativity** of the Borel functional calculus (Theorem 1.4.14(b)). -/
theorem borelCalc_mul {f g : ℝ → ℂ} (hf : IsBddBorel f) (hg : IsBddBorel g) :
    borelCalc A hA (f * g) = borelCalc A hA f * borelCalc A hA g := by
  refine borelCalc_eq_of_inner (hf.mul hg) fun φ => ?_
  rw [ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.adjoint_inner_left,
    ← borelCalc_conj hf, inner_borelCalc hg]
  have := sform_ext_density (A := A) (hA := hA) (borelCalc A hA (fun x => conj (f x)) φ) φ φ f hf
    (fun F => ?_) g hg
  · rw [this]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp [mul_comm])
  · have hFc := cc_continuous F
    obtain ⟨C, hC⟩ := cc_bound F
    rw [← inner_borelCalc ⟨hFc.measurable, C, hC⟩, borelCalc_conj hf,
      ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.mul_apply,
      ← borelCalc_mul_of_continuous hf hFc ⟨C, hC⟩,
      inner_borelCalc_self (hf.mul ⟨hFc.measurable, C, hC⟩)]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp [mul_comm])

theorem borelCalc_comm {f g : ℝ → ℂ} (hf : IsBddBorel f) (hg : IsBddBorel g) :
    borelCalc A hA f * borelCalc A hA g = borelCalc A hA g * borelCalc A hA f := by
  rw [← borelCalc_mul hf hg, ← borelCalc_mul hg hf, mul_comm]

/-- `‖f(A) φ‖² = ∫ |f|² dμ_φ`. -/
theorem norm_borelCalc_apply_sq {f : ℝ → ℂ} (hf : IsBddBorel f) (φ : H) :
    ‖borelCalc A hA f φ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂(spectralMeasure A hA φ) := by
  have h : ((‖borelCalc A hA f φ‖ ^ 2 : ℝ) : ℂ) = ∫ x, ((‖f x‖ ^ 2 : ℝ) : ℂ) ∂(spectralMeasure A hA φ) := by
    rw [show ((‖borelCalc A hA f φ‖ ^ 2 : ℝ) : ℂ) = ⟪borelCalc A hA f φ, borelCalc A hA f φ⟫_ℂ by
      rw [inner_self_eq_norm_sq_to_K]; norm_cast, ← ContinuousLinearMap.adjoint_inner_right,
      ← borelCalc_conj hf, ← ContinuousLinearMap.mul_apply, ← borelCalc_mul hf.conj hf,
      inner_borelCalc_self (hf.conj.mul hf)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply]
    rw [Complex.conj_mul']
    push_cast; ring
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

/-- Operator bound: `‖f(A) φ‖ ≤ C ‖φ‖` if `|f| ≤ C`. -/
theorem norm_borelCalc_apply_le {f : ℝ → ℂ} (hf : IsBddBorel f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C)
    (φ : H) : ‖borelCalc A hA f φ‖ ≤ C * ‖φ‖ := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  have h1 := norm_borelCalc_apply_sq (A := A) (hA := hA) hf φ
  have h2 : ∫ x, ‖f x‖ ^ 2 ∂(spectralMeasure A hA φ) ≤ C ^ 2 * ‖φ‖ ^ 2 := by
    rw [← spectralMeasure_real_univ A hA φ]
    have := MeasureTheory.norm_integral_le_of_norm_le_const (μ := spectralMeasure A hA φ)
      (f := fun x => ‖f x‖ ^ 2) (C := C ^ 2) (Eventually.of_forall fun x => by
        rw [norm_pow, norm_norm]; exact pow_le_pow_left₀ (norm_nonneg _) (hC x) 2)
    exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)
  have : ‖borelCalc A hA f φ‖ ^ 2 ≤ (C * ‖φ‖) ^ 2 := by rw [h1, mul_pow]; exact h2
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 this

/-- **Theorem 1.4.14(c)**: if `fₙ → f` pointwise with a uniform bound, then `fₙ(A) → f(A)`
strongly. -/
theorem tendsto_borelCalc_apply {F : ℕ → ℝ → ℂ} {f : ℝ → ℂ} (hF : ∀ n, Measurable (F n))
    (hf : Measurable f) {C : ℝ} (hFC : ∀ n x, ‖F n x‖ ≤ C) (hfC : ∀ x, ‖f x‖ ≤ C)
    (hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x))) (ψ : H) :
    Tendsto (fun n => borelCalc A hA (F n) ψ) atTop (𝓝 (borelCalc A hA f ψ)) := by
  have hFB : ∀ n, IsBddBorel (F n) := fun n => ⟨hF n, C, hFC n⟩
  have hfB : IsBddBorel f := ⟨hf, C, hfC⟩
  have hdiff : ∀ n, IsBddBorel (F n + (fun x => (-1 : ℂ) * f x)) :=
    fun n => (hFB n).add (hfB.const_mul (-1))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have heq : ∀ n, ‖borelCalc A hA (F n) ψ - borelCalc A hA f ψ‖ =
      Real.sqrt (∫ x, ‖F n x - f x‖ ^ 2 ∂(spectralMeasure A hA ψ)) := by
    intro n
    have : borelCalc A hA (F n) ψ - borelCalc A hA f ψ =
        borelCalc A hA (F n + (fun x => (-1 : ℂ) * f x)) ψ := by
      rw [borelCalc_add (hFB n) (hfB.const_mul (-1)), borelCalc_const_mul hfB]
      simp [sub_eq_add_neg]
    rw [this, ← Real.sqrt_sq (norm_nonneg _), norm_borelCalc_apply_sq (hdiff n)]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp [sub_eq_add_neg]
  simp_rw [heq]
  rw [← Real.sqrt_zero]
  refine (Real.continuous_sqrt.tendsto 0).comp ?_
  have := tendsto_integral_of_dominated_convergence (μ := spectralMeasure A hA ψ)
    (F := fun n x => ‖F n x - f x‖ ^ 2) (f := fun _ => (0 : ℝ)) (fun _ => (2 * C) ^ 2)
    (fun n => ((hF n).sub hf).norm.pow_const 2 |>.aestronglyMeasurable)
    (integrable_const _)
    (fun n => Eventually.of_forall fun x => by
      rw [norm_pow, norm_norm]
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      calc ‖F n x - f x‖ ≤ ‖F n x‖ + ‖f x‖ := norm_sub_le _ _
        _ ≤ C + C := add_le_add (hFC n x) (hfC x)
        _ = 2 * C := by ring)
    (Eventually.of_forall fun x => by
      have := ((hlim x).sub (tendsto_const_nhds (x := f x))).norm.pow 2
      simpa using this)
  simpa using this

/-! ### Spectral projections -/

/-- The **spectral projection** `P(S) = χ_S(A)` (p. 31). -/
def specProj (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (S : Set ℝ) : H →L[ℂ] H :=
  borelCalc A hA (S.indicator fun _ => (1 : ℂ))

theorem inner_specProj_self {S : Set ℝ} (hS : MeasurableSet S) (φ : H) :
    ⟪φ, specProj A hA S φ⟫_ℂ = ((spectralMeasure A hA φ).real S : ℂ) := by
  rw [specProj, inner_borelCalc_self (isBddBorel_indicator hS), integral_indicator hS,
    setIntegral_const, Complex.real_smul, mul_one]

theorem specProj_mul {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T) :
    specProj A hA S * specProj A hA T = specProj A hA (S ∩ T) := by
  rw [specProj, specProj, specProj, ← borelCalc_mul (isBddBorel_indicator hS)
    (isBddBorel_indicator hT)]
  congr 1
  funext x
  by_cases h1 : x ∈ S <;> by_cases h2 : x ∈ T <;> simp [h1, h2]

theorem specProj_idem {S : Set ℝ} (hS : MeasurableSet S) :
    specProj A hA S * specProj A hA S = specProj A hA S := by
  rw [specProj_mul hS hS, inter_self]

theorem isSelfAdjoint_specProj {S : Set ℝ} (hS : MeasurableSet S) :
    IsSelfAdjoint (specProj A hA S) :=
  isSelfAdjoint_borelCalc (isBddBorel_indicator hS) fun x => by
    by_cases h : x ∈ S <;> simp [h]

theorem specProj_univ : specProj A hA univ = 1 := by
  rw [specProj, indicator_univ, borelCalc_one]

theorem specProj_empty : specProj A hA ∅ = 0 := by
  rw [specProj, indicator_empty]
  have := borelCalc_const (A := A) (hA := hA) 0
  rw [zero_smul] at this
  exact this

/-- `‖P(S) φ‖² = μ_φ(S)`. -/
theorem norm_specProj_apply_sq {S : Set ℝ} (hS : MeasurableSet S) (φ : H) :
    ‖specProj A hA S φ‖ ^ 2 = (spectralMeasure A hA φ).real S := by
  rw [specProj, norm_borelCalc_apply_sq (isBddBorel_indicator hS)]
  have : (fun x => ‖S.indicator (fun _ => (1 : ℂ)) x‖ ^ 2) = S.indicator fun _ => (1 : ℝ) := by
    funext x; by_cases h : x ∈ S <;> simp [h]
  rw [this, integral_indicator hS, setIntegral_const, smul_eq_mul, mul_one]

/-! ### Spectral measures of `f(A) φ` -/

/-- `dμ_{f(A)φ} = |f|² dμ_φ`. -/
theorem spectralMeasure_borelCalc {f : ℝ → ℂ} (hf : IsBddBorel f) (φ : H) :
    spectralMeasure A hA (borelCalc A hA f φ) =
      (spectralMeasure A hA φ).withDensity fun x => ((‖f x‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨C, hC⟩ := hf.bdd
  have hfin : IsFiniteMeasure ((spectralMeasure A hA φ).withDensity
      fun x => ((‖f x‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞)) :=
    isFiniteMeasure_withDensity_of_le _ _ (Real.toNNReal C ^ 2) fun x => by
      gcongr
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
      exact (hC x).trans (le_max_left _ _)
  symm
  refine spectralMeasure_unique A hA _ _ fun F => ?_
  have hFc := cc_continuous F
  obtain ⟨D, hD⟩ := cc_bound F
  have hFB := cc_isBddBorel F
  rw [integral_withDensity_eq_integral_smul (hf.meas.nnnorm.pow_const 2)]
  -- compute `⟪f(A)φ, F(A) f(A) φ⟫`
  have h1 : ⟪borelCalc A hA f φ, cfc (F : ℝ → ℝ) A (borelCalc A hA f φ)⟫_ℂ =
      ∫ x, ((F x * ‖f x‖ ^ 2 : ℝ) : ℂ) ∂(spectralMeasure A hA φ) := by
    have hc : cfc (F : ℝ → ℝ) A = cfc (fun z : ℂ => ((F z.re : ℝ) : ℂ)) A :=
      cfc_real_eq_complex (F : ℝ → ℝ) hA
    rw [hc, ← borelCalc_eq_cfc (hA := hA) (g := fun x => ((F x : ℝ) : ℂ)) hFc ⟨D, hD⟩,
      ← ContinuousLinearMap.adjoint_inner_right, ← ContinuousLinearMap.mul_apply,
      ← borelCalc_conj hf, ← ContinuousLinearMap.mul_apply, ← borelCalc_mul hf.conj hFB,
      ← borelCalc_mul (hf.conj.mul hFB) hf, inner_borelCalc_self ((hf.conj.mul hFB).mul hf)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Pi.mul_apply]
    rw [mul_comm (conj (f x)), mul_assoc, Complex.conj_mul']
    push_cast; ring
  rw [integral_complex_ofReal] at h1
  have h2 := congrArg Complex.re h1
  simp only [Complex.ofReal_re] at h2
  rw [RCLike.re_to_complex, h2]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [NNReal.smul_def, mul_comm]

/-! ### Dependence only on `σ(A)`, and `A` itself -/

/-- `f(A)` only depends on the values of `f` on `σ(A)`. -/
theorem borelCalc_congr_spectrum {f g : ℝ → ℂ} (hf : IsBddBorel f) (hg : IsBddBorel g)
    (hfg : ∀ x ∈ spectrum ℝ A, f x = g x) : borelCalc A hA f = borelCalc A hA g :=
  borelCalc_eq_of_inner hf fun φ => by
    rw [inner_borelCalc_self hg]
    refine integral_congr_ae ?_
    filter_upwards [ae_mem_spectrum A hA φ] with x hx
    exact (hfg x hx).symm

variable (A) in
/-- The truncated identity `x ↦ max (-‖A‖) (min x ‖A‖)`, which equals `x` on `σ(A)`. -/
def truncId (x : ℝ) : ℂ := ((max (-‖A‖) (min x ‖A‖) : ℝ) : ℂ)

omit [CompleteSpace H] in
lemma truncId_continuous : Continuous (truncId A) := by unfold truncId; fun_prop

omit [CompleteSpace H] in
lemma norm_truncId_le (x : ℝ) : ‖truncId A x‖ ≤ ‖A‖ := by
  rw [truncId, Complex.norm_real, Real.norm_eq_abs]
  exact abs_le.2 ⟨le_max_left _ _, max_le (by linarith [norm_nonneg A]) (min_le_right _ _)⟩

lemma isBddBorel_truncId : IsBddBorel (truncId A) :=
  ⟨truncId_continuous.measurable, ‖A‖, norm_truncId_le⟩

/-- `A = id(A)`: the operator itself is obtained from the (truncated) identity function. -/
theorem borelCalc_truncId : borelCalc A hA (truncId A) = A := by
  rw [borelCalc_eq_cfc truncId_continuous ⟨‖A‖, norm_truncId_le⟩]
  conv_rhs => rw [← cfc_id' ℂ A]
  refine cfc_congr fun z hz => ?_
  have h1 := hA.mem_spectrum_eq_re hz
  have h2 : ‖z‖ ≤ ‖A‖ := by
    have := spectrum.subset_closedBall_norm_mul A hz
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this.trans (mul_le_of_le_one_right (norm_nonneg _)
      (by exact ContinuousLinearMap.norm_id_le))
  have h3 : |z.re| ≤ ‖A‖ := (Complex.abs_re_le_norm z).trans h2
  simp only [truncId]
  rw [min_eq_left (abs_le.1 h3).2, max_eq_right (abs_le.1 h3).1, ← h1]

/-- `f(A)` commutes with `A`. -/
theorem borelCalc_commute {f : ℝ → ℂ} (hf : IsBddBorel f) :
    borelCalc A hA f * A = A * borelCalc A hA f := by
  have e := borelCalc_truncId (hA := hA)
  calc borelCalc A hA f * A = borelCalc A hA f * borelCalc A hA (truncId A) :=
        congrArg (borelCalc A hA f * ·) e.symm
    _ = borelCalc A hA (truncId A) * borelCalc A hA f := borelCalc_comm hf isBddBorel_truncId
    _ = A * borelCalc A hA f := congrArg (· * borelCalc A hA f) e

end Hilbert

end DF
