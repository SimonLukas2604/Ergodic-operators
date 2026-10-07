/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §2.4 (continued)  Spectral measures and generalized eigenvalues  (book pp. 161–164)

Spectral measures are those of `Ch1/SpectralMeasure.lean`; the canonical spectral measure of
`H` is `μ = μ_{δ₀} + μ_{δ₁}` (`DF.canonicalMeasure`, p. 138).  Spectral projections and the
Borel calculus are those of `Ch1/BorelCalculus.lean`.

## Main results
* **Exercise 2.4.1**: `DF.not_mem_spectrum_of_null` — if `μ(I) = 0` for an open interval
  `I ∋ E`, then `E ∉ σ(H)`; i.e. `σ(H) ⊆ supp μ` (`DF.spectrum_subset_support`).  The
  key steps are `DF.specProj_eq_zero_of_null` (`χ_I(H) = 0`, using the cyclicity of
  `{δ₀, δ₁}`, Proposition 2.2.1) and an explicit inverse of `H - E`.
* **Theorem 2.4.2 (b)** is recorded as the statement `DF.GenEigSupportStatement`
  (not proved: the book's proof uses Radon–Nikodym derivatives of the complex measures
  `μ_{n,m}`).
* **Theorem 2.4.2 (c)**: `DF.spectrum_eq_closure_genEig` — assuming
  `DF.GenEigSupportStatement V`, `σ(H) = closure G`; the inclusion `closure G ⊆ σ(H)`
  holds unconditionally (`DF.closure_genEigReal_subset_spectrum`).
-/
import DamanikFillman.Ch2.GenEigen
import DamanikFillman.Ch1.BorelCalculus

noncomputable section

open scoped InnerProductSpace ComplexConjugate
open L2 MeasureTheory Set Filter Topology

namespace DF

variable {V : ℤ → ℝ}

/-- The canonical spectral measure `μ = μ_{δ₀} + μ_{δ₁}` of `H` (p. 138). -/
def canonicalMeasure (V : ℤ → ℝ) (hV : BddPot V) : Measure ℝ :=
  spectralMeasure (schr V) (isSelfAdjoint_schr hV) (dlt 0) +
    spectralMeasure (schr V) (isSelfAdjoint_schr hV) (dlt 1)

lemma commute_aeval {P H : Op} (hPH : P * H = H * P) (p : Polynomial ℂ) :
    P * Polynomial.aeval H p = Polynomial.aeval H p * P := by
  induction p using Polynomial.induction_on with
  | C a =>
    simp only [Polynomial.aeval_C]
    exact (Algebra.commutes a P).symm
  | add p q hp hq => simp only [map_add, mul_add, add_mul, hp, hq]
  | monomial n a ih =>
    have e : Polynomial.aeval H (Polynomial.C a * Polynomial.X ^ (n + 1)) =
        Polynomial.aeval H (Polynomial.C a * Polynomial.X ^ n) * H := by
      simp only [map_mul, map_pow, Polynomial.aeval_X, pow_succ, mul_assoc]
    rw [e, ← mul_assoc, ih, mul_assoc, hPH, ← mul_assoc]

/-- If `μ(I) = 0` (`I` measurable), then `χ_I(H) = 0`. -/
theorem specProj_eq_zero_of_null (hV : BddPot V) {I : Set ℝ} (hI : MeasurableSet I)
    (h0 : spectralMeasure (schr V) (isSelfAdjoint_schr hV) (dlt 0) I = 0)
    (h1 : spectralMeasure (schr V) (isSelfAdjoint_schr hV) (dlt 1) I = 0) :
    specProj (schr V) (isSelfAdjoint_schr hV) I = 0 := by
  set hH := isSelfAdjoint_schr hV
  set P := specProj (schr V) hH I
  have hP0 : P (dlt 0) = 0 := by
    have := norm_specProj_apply_sq (A := schr V) (hA := hH) hI (dlt 0)
    rw [Measure.real, h0, ENNReal.toReal_zero] at this
    exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)
  have hP1 : P (dlt 1) = 0 := by
    have := norm_specProj_apply_sq (A := schr V) (hA := hH) hI (dlt 1)
    rw [Measure.real, h1, ENNReal.toReal_zero] at this
    exact norm_eq_zero.mp (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this)
  have hcomm : P * schr V = schr V * P := borelCalc_commute (isBddBorel_indicator hI)
  have hδ : ∀ m : ℤ, P (dlt m) = 0 := by
    intro m
    obtain ⟨p, q, hpq⟩ := cyclic_pair hV 0 m
    rw [hpq, map_add]
    have e1 := congrArg (fun T : Op => T (dlt 0)) (commute_aeval hcomm p)
    have e2 := congrArg (fun T : Op => T (dlt 1)) (commute_aeval hcomm q)
    simp only [ContinuousLinearMap.mul_apply] at e1 e2
    rw [show (0 : ℤ) + 1 = 1 by norm_num]
    rw [e1, e2, hP0, hP1, map_zero, map_zero, add_zero]
  have hsa := isSelfAdjoint_specProj (A := schr V) (hA := hH) hI
  ext ψ m
  have : P ψ m = ⟪dlt m, P ψ⟫_ℂ := (inner_dlt m _).symm
  rw [this, ← ContinuousLinearMap.adjoint_inner_left, show ContinuousLinearMap.adjoint P = P
    from hsa.adjoint_eq, hδ m, inner_zero_left]
  rfl

lemma mem_spectrum_real_iff_genEig (hV : BddPot V) (E : ℝ) :
    E ∈ spectrum ℝ (schr V) ↔ (E : ℂ) ∈ spectrum ℂ (schr V) :=
  (spectrum.algebraMap_mem_iff ℂ).symm

/-- **Exercise 2.4.1**: if the canonical spectral measure gives zero mass to the open
interval `(E - r, E + r)`, then `E ∉ σ(H)`. -/
theorem not_mem_spectrum_of_null (hV : BddPot V) {E r : ℝ} (hr : 0 < r)
    (h0 : spectralMeasure (schr V) (isSelfAdjoint_schr hV) (dlt 0) (Ioo (E - r) (E + r)) = 0)
    (h1 : spectralMeasure (schr V) (isSelfAdjoint_schr hV) (dlt 1) (Ioo (E - r) (E + r)) = 0) :
    E ∉ spectrum ℝ (schr V) := by
  set hH := isSelfAdjoint_schr hV
  set I := Ioo (E - r) (E + r)
  have hI : MeasurableSet I := measurableSet_Ioo
  have hP := specProj_eq_zero_of_null hV hI h0 h1
  -- `χ_{Iᶜ}(H) = 1`
  have hPc : specProj (schr V) hH Iᶜ = 1 := by
    have hsum : (I.indicator fun _ => (1 : ℂ)) + Iᶜ.indicator (fun _ => 1) = fun _ => 1 := by
      funext x; by_cases hx : x ∈ I <;> simp [hx]
    have := borelCalc_add (A := schr V) (hA := hH) (isBddBorel_indicator hI)
      (isBddBorel_indicator hI.compl)
    rw [hsum, borelCalc_one] at this
    have e2 : specProj (schr V) hH I + specProj (schr V) hH Iᶜ = 1 := this.symm
    rw [hP, zero_add] at e2
    exact e2
  -- the inverse of `H - E`
  set g : ℝ → ℂ := fun x => Iᶜ.indicator (fun x => ((x - E)⁻¹ : ℝ)) x
  have hg : IsBddBorel g := by
    refine ⟨?_, r⁻¹, fun x => ?_⟩
    · exact Measurable.indicator (Complex.measurable_ofReal.comp
        ((measurable_id.sub_const E).inv)) hI.compl
    · simp only [g]
      by_cases hx : x ∈ Iᶜ
      · rw [indicator_of_mem hx, Complex.norm_real, Real.norm_eq_abs, abs_inv]
        have : r ≤ |x - E| := by
          simp only [I, mem_compl_iff, mem_Ioo, not_and_or, not_lt] at hx
          rcases hx with hx | hx
          · rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
          · rw [abs_of_nonneg (by linarith)]; linarith
        exact inv_anti₀ hr this
      · rw [indicator_of_notMem hx]; simp; positivity
  set f : ℝ → ℂ := fun x => truncId (schr V) x - (E : ℂ)
  have hfeq : f = truncId (schr V) + fun _ => -(E : ℂ) := by
    funext x; simp [f, sub_eq_add_neg]
  have hf : IsBddBorel f := by
    rw [hfeq]; exact (isBddBorel_truncId (A := schr V)).add (isBddBorel_const _)
  have hfH : borelCalc (schr V) hH f = schr V - algebraMap ℂ Op E := by
    have := borelCalc_add (A := schr V) (hA := hH) (isBddBorel_truncId (A := schr V)) (isBddBorel_const (-(E : ℂ)))
    rw [show (truncId (schr V) + fun _ => -(E : ℂ)) = f by funext x; simp [f, sub_eq_add_neg],
      borelCalc_truncId, borelCalc_const] at this
    rw [this, Algebra.algebraMap_eq_smul_one, neg_smul, sub_eq_add_neg]
  have hgf : borelCalc (schr V) hH (g * f) = 1 := by
    rw [← hPc, specProj]
    refine borelCalc_congr_spectrum (hg.mul hf) (isBddBorel_indicator hI.compl) fun x hx => ?_
    have htr : truncId (schr V) x = x := by
      have h3 : |x| ≤ ‖schr V‖ := by
        have hz : ((x : ℝ) : ℂ) ∈ spectrum ℂ (schr V) := (mem_spectrum_real_iff_genEig hV x).mp hx
        have := spectrum.subset_closedBall_norm_mul (schr V) hz
        rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] at this
        exact this.trans (mul_le_of_le_one_right (norm_nonneg _)
          (by exact ContinuousLinearMap.norm_id_le))
      simp only [truncId]
      rw [min_eq_left (abs_le.1 h3).2, max_eq_right (abs_le.1 h3).1]
    simp only [Pi.mul_apply, g, f, htr]
    by_cases hxI : x ∈ Iᶜ
    · rw [indicator_of_mem hxI, indicator_of_mem hxI]
      have hne : x - E ≠ 0 := by
        intro h; apply hxI; simp only [I, mem_Ioo]; constructor <;> linarith
      push_cast
      exact inv_mul_cancel₀ (by exact_mod_cast hne)
    · rw [indicator_of_notMem hxI, indicator_of_notMem hxI]; simp
  have hfg : borelCalc (schr V) hH (f * g) = 1 := by rw [mul_comm]; exact hgf
  rw [borelCalc_mul hg hf, hfH] at hgf
  rw [borelCalc_mul hf hg, hfH] at hfg
  intro hEs
  apply hEs
  rw [spectrum.mem_resolventSet_iff, IsScalarTower.algebraMap_apply ℝ ℂ Op E]
  have hu : IsUnit (schr V - algebraMap ℂ Op (E : ℂ)) :=
    ⟨⟨_, borelCalc (schr V) hH g, hfg, hgf⟩, rfl⟩
  have := hu.neg
  rwa [neg_sub] at this

/-- Exercise 2.4.1: `σ(H)` is contained in the support of the canonical spectral measure. -/
theorem spectrum_subset_support (hV : BddPot V) {E : ℝ} (hE : E ∈ spectrum ℝ (schr V))
    {r : ℝ} (hr : 0 < r) : canonicalMeasure V hV (Ioo (E - r) (E + r)) ≠ 0 := by
  intro h
  rw [canonicalMeasure, Measure.add_apply, add_eq_zero] at h
  exact not_mem_spectrum_of_null hV hr h.1 h.2 hE

/-- The real generalized eigenvalues. -/
def genEigReal (V : ℤ → ℝ) : Set ℝ := {E : ℝ | (E : ℂ) ∈ genEigAll V}

/-- **Theorem 2.4.2 (b)** (stated, not proved): for every `δ > 1/2`, `G_δ` is a support of the
canonical spectral measure `μ`: `μ(ℝ \ G_δ) = 0`. -/
def GenEigSupportStatement (V : ℤ → ℝ) (hV : BddPot V) : Prop :=
  ∀ δ : ℝ, 1 / 2 < δ → canonicalMeasure V hV {E : ℝ | (E : ℂ) ∉ genEigSet V δ} = 0

/-- (2.4.14): `closure G ⊆ σ(H)` (from Theorem 2.4.2 (a)). -/
theorem closure_genEigReal_subset_spectrum (hV : BddPot V) :
    closure (genEigReal V) ⊆ spectrum ℝ (schr V) := by
  refine closure_minimal (fun E hE => ?_) (spectrum.isClosed _)
  rw [mem_spectrum_real_iff_genEig hV]
  exact genEigAll_subset_spectrum hV hE

/-- **Theorem 2.4.2 (c)**: assuming Theorem 2.4.2 (b), `σ(H) = closure G`. -/
theorem spectrum_eq_closure_genEig (hV : BddPot V) (hb : GenEigSupportStatement V hV) :
    spectrum ℝ (schr V) = closure (genEigReal V) := by
  refine le_antisymm (fun E hE => ?_) (closure_genEigReal_subset_spectrum hV)
  by_contra hcl
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp isClosed_closure.isOpen_compl E hcl
  apply spectrum_subset_support hV hE hr
  refine measure_mono_null (fun x hx => ?_) (hb 1 (by norm_num))
  simp only [mem_setOf_eq]
  intro hx1
  have hxb : x ∈ Metric.ball E r := by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;> linarith [hx.1, hx.2]
  apply hball hxb
  apply subset_closure
  simp only [genEigReal, genEigAll, mem_setOf_eq, mem_iUnion]
  exact ⟨1, by norm_num, hx1⟩

end DF
