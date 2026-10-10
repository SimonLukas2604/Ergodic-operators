/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators, I*,
§1.11 (pp. 103–107): the Poltoratski–Remling theorem on reflectionless measures.

# Main definitions

* `DF.IsReflectionless μ Σ` — Definition 1.11.1: `Re F_μ(E + i0) = 0` for Lebesgue-a.e. `E ∈ Σ`;
* `DF.lambdaS Σ` — the set `Λ_s` of points at which `Σ` has Lebesgue density zero (1.11.2).

# Main results

* `DF.mem_lambdaS_of_tendsto_im_zero` — the final step (1.11.15) of the proof of Theorem 1.11.2:
  if `Im Λ(E + iε) → 0`, where `Λ = F_{Leb|Σ}`, then `E ∈ Λ_s`;
* `DF.acPart_pos_of_reflectionless` — Exercise 1.11.2, derived from the uniqueness statement
  `DF.BoundaryUniquenessStatement` (Theorem 1.9.4(e)); the unconditional version is
  `DF.acPart_pos_of_reflectionless'` in `DamanikFillman.Ch1.BoundaryUniqueness`.

# Statements

* `DF.PoltoratskiRemlingStatement` — Theorem 1.11.2.  It is proved in
  `DamanikFillman.Ch1.PoltoratskiRemlingProof` (`DF.poltoratskiRemlingStatement_holds`), using
  the Krein representation of `arg F_μ` (Exercise 1.11.4) and Poltoratski's theorem.

# Deviations

* In `DF.mem_lambdaS_of_tendsto_im_zero` we assume `Leb(Σ) < ∞` so that `Λ = F_{Leb|Σ}` is the
  Borel transform of a finite measure (only its imaginary part is used in the book).
-/
import DamanikFillman.Ch1.BorelAlpha
import DamanikFillman.Ch1.BorelBoundary

noncomputable section

open MeasureTheory Filter Topology Set Metric Complex
open scoped ENNReal

namespace DF

/-- Definition 1.11.1: a finite measure `μ` is reflectionless on `Σ` if
`Re F_μ(E + i0) = 0` for Lebesgue-a.e. `E ∈ Σ`. -/
def IsReflectionless (μ : Measure ℝ) (S : Set ℝ) : Prop :=
  ∀ᵐ (E : ℝ) ∂(volume.restrict S),
    Tendsto (fun ε : ℝ => (borelTransform μ (E + ε * I)).re) (𝓝[>] 0) (𝓝 0)

/-- The set `Λ_s = {E : Leb(Σ ∩ (E - δ, E + δ)) / (2δ) → 0}` of (1.11.2). -/
def lambdaS (S : Set ℝ) : Set ℝ :=
  {E | Tendsto (fun δ : ℝ => volume (S ∩ ball E δ) / ENNReal.ofReal (2 * δ)) (𝓝[>] 0) (𝓝 0)}

/-- Theorem 1.11.2 (Poltoratski–Remling), recorded as a statement: if a finite compactly supported
measure `μ` is reflectionless on `Σ`, then its singular part is supported on `Λ_s`. -/
def PoltoratskiRemlingStatement : Prop :=
  ∀ (μ : Measure ℝ), IsFiniteMeasure μ → (∃ R : ℝ, μ (Icc (-R) R)ᶜ = 0) →
    ∀ S : Set ℝ, IsReflectionless μ S → μ.singularPart volume (lambdaS S)ᶜ = 0

/-- The last step of the proof of Theorem 1.11.2, (1.11.15): with `Λ(z) = ∫_Σ dt/(t - z)`,
`Im Λ(E + iε) ≥ Leb(Σ ∩ (E - ε, E + ε)) / (2ε)`, so `Im Λ(E + i0) = 0` forces `E ∈ Λ_s`. -/
theorem mem_lambdaS_of_tendsto_im_zero {S : Set ℝ} (hS : volume S < ∞) {E : ℝ}
    (h : Tendsto (fun ε : ℝ => (borelTransform (volume.restrict S) (E + ε * I)).im) (𝓝[>] 0)
      (𝓝 0)) :
    E ∈ lambdaS S := by
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hS.ne
  have h0 : Tendsto (fun ε : ℝ => ENNReal.ofReal
      ((borelTransform (volume.restrict S) (E + ε * I)).im)) (𝓝[>] 0) (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h0
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have h1 := ofReal_im_ge_ball (volume.restrict S) E hε
  rw [Measure.restrict_apply measurableSet_ball, inter_comm] at h1
  refine le_trans (le_of_eq ?_) h1
  rw [ENNReal.div_eq_inv_mul, ← ENNReal.ofReal_inv_of_pos (by positivity), one_div]

/-- Exercise 1.11.2 (assuming Theorem 1.9.4(e)): if a nonzero finite measure `μ` is reflectionless
on a measurable set `Σ`, then `μ_ac(Q) > 0` for every `Q ⊆ Σ` of positive Lebesgue measure. -/
theorem acPart_pos_of_reflectionless (hU : BoundaryUniquenessStatement) (μ : Measure ℝ)
    [IsFiniteMeasure μ] (hμ : μ ≠ 0) {S : Set ℝ} (hSm : MeasurableSet S)
    (hrefl : IsReflectionless μ S) {Q : Set ℝ} (hQ : Q ⊆ S) (hQpos : 0 < volume Q) :
    0 < volume.withDensity (μ.rnDeriv volume) Q := by
  rw [pos_iff_ne_zero]
  intro h0
  rw [withDensity_apply_eq_zero' (Measure.measurable_rnDeriv μ volume).aemeasurable] at h0
  have hG := ae_tendsto_im_volume μ
  rw [ae_iff] at hG
  have hR := hrefl
  rw [IsReflectionless, ae_restrict_iff' hSm, ae_iff] at hR
  set B := ({x | μ.rnDeriv volume x ≠ 0} ∩ Q) ∪
    {E : ℝ | ¬ Tendsto (fun ε : ℝ => (borelTransform μ (E + ε * I)).im) (𝓝[>] 0)
      (𝓝 (Real.pi * (μ.rnDeriv volume E).toReal))} ∪
    {E : ℝ | ¬ (E ∈ S → Tendsto (fun ε : ℝ => (borelTransform μ (E + ε * I)).re) (𝓝[>] 0)
      (𝓝 0))} with hB
  have hB0 : volume B = 0 := measure_union_null (measure_union_null h0 hG) hR
  set A := Q \ B
  have hA : 0 < volume A := by rwa [measure_sdiff_null hB0]
  have hFA : ∀ E ∈ A, Tendsto (fun ε : ℝ => borelTransform μ (E + ε * I)) (𝓝[>] 0) (𝓝 0) := by
    intro E ⟨hEQ, hEB⟩
    simp only [hB, mem_union, mem_inter_iff, mem_ofPred_eq, not_or, not_not, not_and] at hEB
    obtain ⟨⟨h1, h2⟩, h3⟩ := hEB
    have hf0 : μ.rnDeriv volume E = 0 := by
      by_contra hne; exact h1 hne hEQ
    rw [hf0, ENNReal.toReal_zero, mul_zero] at h2
    have hre := h3 (hQ hEQ)
    have := ((Complex.continuous_ofReal.tendsto _).comp hre).add
      (((Complex.continuous_ofReal.tendsto _).comp h2).mul_const I)
    simp only [Complex.ofReal_zero, zero_mul, add_zero] at this
    refine this.congr fun ε => ?_
    simp only [Function.comp_apply]
    exact Complex.re_add_im _
  have hEq := hU μ 0 inferInstance inferInstance A hA fun E hE =>
    ⟨0, hFA E hE, by simp [borelTransform]⟩
  have hpos := borelTransform_im_pos μ hμ (z := I) (by simp)
  rw [hEq I (by simp)] at hpos
  simp [borelTransform] at hpos

end DF
