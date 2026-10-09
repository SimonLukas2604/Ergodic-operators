/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §3.5: the ergodic decomposition, part 3: the theorem

## Main results

* `DF.ergodicDecompositionStatement_holds` — Theorem 3.5.12: every invariant Borel probability
  measure of a continuous map of a compact metric space is the barycenter of a unique probability
  measure on the ergodic measures.

The decomposing measure is the push-forward of `μ` under the generic-point kernel `x ↦ E(x)`
of `DamanikFillman.Ch3.ErgodicDecompKernel`.  It is concentrated on ergodic measures by the
variance argument of `DamanikFillman.Ch3.ErgodicDecompAux`; uniqueness follows since every
decomposition `m'` satisfies `μ = ∫ ν dm'(ν)` and ergodic `ν` are concentrated on `E⁻¹{ν}`.
-/
import DamanikFillman.Ch3.ErgodicDecompAux

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Set Function Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace DF

namespace ErgDecomp

open Birkhoff

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

attribute [local instance] Classical.propDecidable

lemma abs_le_norm' (f : C(X, ℝ)) (y : X) : |f y| ≤ ‖f‖ := by
  rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm y

lemma abs_integral_le_of_bdd (ν : Measure X) [IsProbabilityMeasure ν] {g : X → ℝ} {c : ℝ}
    (hc : ∀ x, |g x| ≤ c) : |∫ x, g x ∂ν| ≤ c := by
  have h := norm_integral_le_of_norm_le_const (μ := ν) (f := g) (C := c)
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hc x)
  rwa [probReal_univ, mul_one, Real.norm_eq_abs] at h

/-- `ν ↦ ∫ g dν` is measurable on the space of probability measures, for bounded measurable `g`. -/
lemma measurable_integral_P {g : X → ℝ} (hg : Measurable g) {c : ℝ} (hc : ∀ x, |g x| ≤ c) :
    Measurable fun ν : ProbabilityMeasure X => ∫ x, g x ∂(ν : Measure X) := by
  have e : (fun ν : ProbabilityMeasure X => ∫ x, g x ∂(ν : Measure X)) =
      fun ν : ProbabilityMeasure X =>
      (∫⁻ x, ENNReal.ofReal (g x) ∂(ν : Measure X)).toReal -
        (∫⁻ x, ENNReal.ofReal (-g x) ∂(ν : Measure X)).toReal := by
    funext ν
    have := ν.2
    exact integral_eq_lintegral_pos_part_sub_lintegral_neg_part (integrable_of_bdd hg hc)
  rw [e]
  have hcoe : Measurable fun ν : ProbabilityMeasure X => (ν : Measure X) := measurable_subtype_coe
  have h1 : Measurable fun ν : ProbabilityMeasure X =>
      ∫⁻ x, ENNReal.ofReal (g x) ∂(ν : Measure X) :=
    (Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hg)).comp hcoe
  have h2 : Measurable fun ν : ProbabilityMeasure X =>
      ∫⁻ x, ENNReal.ofReal (-g x) ∂(ν : Measure X) :=
    (Measure.measurable_lintegral (ENNReal.measurable_ofReal.comp hg.neg)).comp hcoe
  exact (ENNReal.measurable_toReal.comp h1).sub (ENNReal.measurable_toReal.comp h2)

lemma integrable_integral_P (m : Measure (ProbabilityMeasure X)) [IsFiniteMeasure m]
    {g : X → ℝ} (hg : Measurable g) {c : ℝ} (hc : ∀ x, |g x| ≤ c) :
    Integrable (fun ν : ProbabilityMeasure X => ∫ x, g x ∂(ν : Measure X)) m :=
  Integrable.of_bound (measurable_integral_P hg hc).aestronglyMeasurable c
    (Eventually.of_forall fun ν => by
      have := ν.2
      rw [Real.norm_eq_abs]; exact abs_integral_le_of_bdd _ hc)

/-- Two probability measures agreeing on a dense sequence of continuous functions are equal. -/
lemma eq_of_dense {D : ℕ → C(X, ℝ)} (hD : DenseRange D) {ν ν' : ProbabilityMeasure X}
    (hagree : ∀ i, ∫ z, D i z ∂(ν : Measure X) = ∫ z, D i z ∂(ν' : Measure X)) : ν = ν' := by
  have := ν.2
  have := ν'.2
  refine ProbabilityMeasure.ext_integral fun f => ?_
  refine le_antisymm ?_ ?_ <;> refine le_of_forall_pos_le_add fun ε hε => ?_ <;>
    obtain ⟨i, hi⟩ := hD.exists_dist_lt f (by positivity : 0 < ε / 2) <;>
    rw [dist_eq_norm] at hi <;>
    have a1 := abs_integral_sub_le (ν : Measure X) f (D i) <;>
    have a2 := abs_integral_sub_le (ν' : Measure X) f (D i) <;>
    rw [hagree i] at a1 <;>
    linarith [abs_le.1 a1, abs_le.1 a2]

/-- A bounded function with vanishing variance is a.e. constant. -/
lemma ae_eq_const_of_sq {ν : Measure X} [IsProbabilityMeasure ν] {v : X → ℝ} (hv : Measurable v)
    {c : ℝ} (hc : ∀ x, |v x| ≤ c) (h : ∫ x, v x ^ 2 ∂ν = (∫ x, v x ∂ν) ^ 2) :
    ∀ᵐ x ∂ν, v x = ∫ y, v y ∂ν := by
  set a := ∫ y, v y ∂ν with ha
  have hi : Integrable v ν := integrable_of_bdd hv hc
  have hi2 : Integrable (fun x => v x ^ 2) ν :=
    integrable_of_bdd (hv.pow_const 2) (c := c ^ 2) fun x => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hc x) 2
  have e : (fun x => (v x - a) ^ 2) = fun x => (v x ^ 2 - (2 * a) * v x) + a ^ 2 := by
    funext x; ring
  have hi3 : Integrable (fun x => (v x - a) ^ 2) ν := by
    rw [e]; exact (hi2.sub (hi.const_mul _)).add (integrable_const _)
  have hint : ∫ x, (v x - a) ^ 2 ∂ν = 0 := by
    have i2 : Integrable (fun x => 2 * a * v x) ν := hi.const_mul _
    have i1 : Integrable (fun x => v x ^ 2 - 2 * a * v x) ν := hi2.sub i2
    rw [e, integral_add i1 (integrable_const _), integral_sub hi2 i2, integral_const_mul,
      integral_const, h]
    simp only [probReal_univ, one_smul]
    ring
  have hnn : (0 : X → ℝ) ≤ fun x => (v x - a) ^ 2 := fun x => sq_nonneg _
  have hz := (integral_eq_zero_iff_of_nonneg hnn hi3).1 hint
  filter_upwards [hz] with x hx
  have hx' : (v x - a) ^ 2 = 0 := hx
  have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hx'
  linarith

end ErgDecomp

open ErgDecomp in
/-- **Theorem 3.5.12 (ergodic decomposition).** -/
theorem ergodicDecompositionStatement_holds : ErgodicDecompositionStatement := by
  intro X _ _ _ _ S hS μ hμ
  have := μ.2
  have hSm := hS.measurable
  have hEm : Measurable (E S) := measurable_E hSm
  have hcoe : Measurable fun ν : ProbabilityMeasure X => (ν : Measure X) := measurable_subtype_coe
  obtain ⟨D, hD⟩ := TopologicalSpace.exists_dense_seq C(X, ℝ)
  -- the decomposing measure
  have hmP : IsProbabilityMeasure ((μ : Measure X).map (E S)) :=
    (Measure.isProbabilityMeasure_map_iff hEm.aemeasurable).2 inferInstance
  set m : ProbabilityMeasure (ProbabilityMeasure X) := ⟨(μ : Measure X).map (E S), hmP⟩ with hm
  have hmc : (m : Measure (ProbabilityMeasure X)) = (μ : Measure X).map (E S) := rfl
  -- a measurable set of ergodic measures
  set W : Set (ProbabilityMeasure X) := ⋂ i, ({ν | ∫ y, D i (S y) ∂(ν : Measure X) =
      ∫ y, D i y ∂(ν : Measure X)} ∩ {ν | ∫ y, fstar S (D i) y ^ 2 ∂(ν : Measure X) =
      (∫ y, fstar S (D i) y ∂(ν : Measure X)) ^ 2}) with hWdef
  have hWm : MeasurableSet W := by
    refine MeasurableSet.iInter fun i => (measurableSet_eq_fun ?_ ?_).inter
      (measurableSet_eq_fun ?_ ?_)
    · exact measurable_integral_P ((D i).continuous.measurable.comp hSm)
        fun y => abs_le_norm' (D i) (S y)
    · exact measurable_integral_P (D i).continuous.measurable (abs_le_norm' (D i))
    · exact measurable_integral_P ((measurable_fstar hSm (D i)).pow_const 2)
        (c := ‖D i‖ ^ 2) fun y => by
          rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (abs_fstar_le S (D i) y) 2
    · exact (measurable_integral_P (measurable_fstar hSm (D i)) (abs_fstar_le S (D i))).pow_const 2
  have hW : ∀ ν ∈ W, Ergodic S (ν : Measure X) := by
    intro ν hν
    have := ν.2
    simp only [hWdef, mem_iInter, mem_inter_iff, mem_setOf_eq] at hν
    have hmp : MeasurePreserving S (ν : Measure X) ν := by
      refine ⟨hSm, ?_⟩
      have hP : IsProbabilityMeasure ((ν : Measure X).map S) :=
        (Measure.isProbabilityMeasure_map_iff hSm.aemeasurable).2 inferInstance
      have h := eq_of_dense hD (ν := ⟨(ν : Measure X).map S, hP⟩) (ν' := ν) fun i => by
        show ∫ z, D i z ∂((ν : Measure X).map S) = _
        rw [integral_map hSm.aemeasurable (D i).continuous.aestronglyMeasurable]
        exact (hν i).1
      exact congrArg Subtype.val h
    exact ergodic_of_fstar_const hmp hD fun i =>
      ⟨_, ae_eq_const_of_sq (measurable_fstar hSm (D i)) (abs_fstar_le S (D i)) (hν i).2⟩
  have hEW : ∀ᵐ x ∂(μ : Measure X), E S x ∈ W := by
    have h1 := ae_all_iff.2 fun i => ae_ae_fstar_eq hμ (D i)
    filter_upwards [ae_mem_G hμ, h1] with x hx hfx
    simp only [hWdef, mem_iInter, mem_inter_iff, mem_setOf_eq]
    intro i
    have := (E S x).2
    constructor
    · conv_rhs => rw [← map_E hS hx]
      rw [integral_map hSm.aemeasurable (D i).continuous.aestronglyMeasurable]
    · have e1 : ∫ y, fstar S (D i) y ^ 2 ∂(E S x : Measure X) = fstar S (D i) x ^ 2 := by
        rw [integral_congr_ae (g := fun _ => fstar S (D i) x ^ 2)
          ((hfx i).mono fun y hy => by simp only [hy])]
        simp
      have e2 : ∫ y, fstar S (D i) y ∂(E S x : Measure X) = fstar S (D i) x := by
        rw [integral_congr_ae (g := fun _ => fstar S (D i) x) (hfx i)]
        simp
      rw [e1, e2]
  -- barycenter of `m`
  have hbar : ∀ g : C(X, ℝ), ∫ x, g x ∂(μ : Measure X) =
      ∫ ν, (∫ x, g x ∂(ν : Measure X)) ∂(m : Measure (ProbabilityMeasure X)) := by
    intro g
    rw [hmc, integral_map hEm.aemeasurable
      (measurable_integral_P g.continuous.measurable (abs_le_norm' g)).aestronglyMeasurable]
    have h1 : ∫ x, ∫ y, g y ∂(E S x : Measure X) ∂(μ : Measure X) =
        ∫ x, fstar S g x ∂(μ : Measure X) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_mem_G hμ] with x hx
      exact integral_E_eq_fstar hx g
    have h2 := integral_mul_fstar hμ (ψ := fun _ => (1 : ℝ)) measurable_const (c := 1)
      (fun _ => by simp) (fun _ => rfl) g
    simp only [one_mul] at h2
    rw [h1, h2]
  refine ⟨m, ⟨?_, hbar⟩, ?_⟩
  · -- `m` is concentrated on ergodic measures
    have hm0 : (m : Measure (ProbabilityMeasure X)) Wᶜ = 0 := by
      rw [hmc, Measure.map_apply hEm hWm.compl]
      exact ae_iff.1 hEW
    exact measure_mono_null (fun ν hν hνW => hν (hW ν hνW)) hm0
  · -- uniqueness
    rintro m' ⟨h0', hbar'⟩
    have := m'.2
    have hbind : (m' : Measure (ProbabilityMeasure X)).bind (fun ν => (ν : Measure X)) =
        (μ : Measure X) := by
      symm
      refine ext_of_forall_lintegral_eq_of_IsFiniteMeasure fun f => ?_
      rw [Measure.lintegral_bind hcoe.aemeasurable
        f.continuous.measurable.coe_nnreal_ennreal.aemeasurable,
        lintegral_nnreal_eq f (μ : Measure X), hbar' (nnC f),
        ofReal_integral_eq_lintegral_ofReal
          (integrable_integral_P _ (nnC f).continuous.measurable (abs_le_norm' (nnC f)))
          (Eventually.of_forall fun ν => integral_nonneg fun y => NNReal.coe_nonneg (f y))]
      refine lintegral_congr fun ν => ?_
      have := ν.2
      exact (lintegral_nnreal_eq f _).symm
    apply ProbabilityMeasure.toMeasure_injective
    refine Measure.ext fun B hB => ?_
    rw [hmc, Measure.map_apply hEm hB, ← hbind, Measure.bind_apply (hEm hB) hcoe.aemeasurable,
      ← lintegral_indicator_one hB]
    refine lintegral_congr_ae ?_
    have herg : ∀ᵐ ν ∂(m' : Measure (ProbabilityMeasure X)), Ergodic S (ν : Measure X) :=
      ae_iff.2 h0'
    filter_upwards [herg] with ν hν
    have := ν.2
    have hae := ae_E_eq_of_ergodic hν
    by_cases hνB : ν ∈ B
    · rw [indicator_of_mem hνB, Pi.one_apply, eq_comm]
      refine (prob_compl_eq_zero_iff (hEm hB)).1 ?_
      refine measure_eq_zero_iff_ae_notMem.2 (hae.mono fun y hy => ?_)
      simp only [mem_compl_iff, mem_preimage, not_not, hy.2]
      exact hνB
    · rw [indicator_of_notMem hνB, eq_comm]
      refine measure_eq_zero_iff_ae_notMem.2 (hae.mono fun y hy => ?_)
      simp only [mem_preimage, hy.2]
      exact hνB

end DF
