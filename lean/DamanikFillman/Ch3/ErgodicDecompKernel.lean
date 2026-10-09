/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §3.5: the ergodic decomposition, part 1: the empirical kernel

For a continuous map `S` of a compact metric space `X` we consider the set `G` of points at which
the Birkhoff averages of every continuous function converge, and the limit `E(x)` of the
empirical measures `(1/n) ∑_{i<n} δ_{S^i x}` (for `x ∈ G`; `E(x) = δ_x` otherwise).

## Main results

* `DF.ErgDecomp.integral_E` — `∫ f dE(x) = f*(x)` (the Birkhoff limit) for `x ∈ G`;
* `DF.ErgDecomp.measurable_E` — `x ↦ E(x)` is measurable (Giry σ-algebra);
* `DF.ErgDecomp.ae_mem_G` — `G` has full measure for every invariant probability measure;
* `DF.ErgDecomp.E_comp` — `E(Sx) = E(x)` on `G`;
* `DF.ErgDecomp.map_E` — `E(x)` is `S`-invariant for `x ∈ G`.
-/
import DamanikFillman.Ch3.TopErgodic
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Set Function Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace DF

namespace ErgDecomp

open Birkhoff

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

attribute [local instance] Classical.propDecidable

/-! ### Birkhoff averages of continuous functions -/

lemma birkhoffAverage_sub' (S : X → X) (f g : X → ℝ) (n : ℕ) (x : X) :
    birkhoffAverage ℝ S (fun y => f y - g y) n x =
      birkhoffAverage ℝ S f n x - birkhoffAverage ℝ S g n x := by
  simp only [birkhoffAverage_eq_div, birkhoffSum, Finset.sum_sub_distrib, sub_div]

lemma abs_birkhoffAverage_le (S : X → X) (f : C(X, ℝ)) (n : ℕ) (x : X) :
    |birkhoffAverage ℝ S f n x| ≤ ‖f‖ := by
  rw [birkhoffAverage_eq_div]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [abs_div, abs_of_pos hn', div_le_iff₀ hn']
    unfold birkhoffSum
    calc |∑ k ∈ Finset.range n, f (S^[k] x)| ≤ ∑ k ∈ Finset.range n, |f (S^[k] x)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k ∈ Finset.range n, ‖f‖ := Finset.sum_le_sum fun k _ => by
            rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm _
      _ = ‖f‖ * n := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]

lemma measurable_birkhoffAverage {S : X → X} (hS : Measurable S) {f : X → ℝ}
    (hf : Measurable f) (n : ℕ) : Measurable (birkhoffAverage ℝ S f n) := by
  unfold birkhoffAverage
  exact (measurable_birkhoffSum hS hf n).const_smul ((n : ℝ)⁻¹)

lemma measurable_birkhoffLimit {S : X → X} (hS : Measurable S) {f : X → ℝ}
    (hf : Measurable f) : Measurable (birkhoffLimit S f) :=
  (StronglyMeasurable.limUnder fun n =>
    (measurable_birkhoffAverage hS hf n).stronglyMeasurable).measurable

/-- Convergence of the Birkhoff averages of `f` at `x`. -/
def Conv (S : X → X) (f : X → ℝ) (x : X) : Prop :=
  ∃ L, Tendsto (fun n => birkhoffAverage ℝ S f n x) atTop (𝓝 L)

lemma conv_of_dense {D : ℕ → C(X, ℝ)} (hD : DenseRange D) {S : X → X} {x : X}
    (h : ∀ i, Conv S (D i) x) (f : C(X, ℝ)) : Conv S f x := by
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨i, hi⟩ := hD.exists_dist_lt f (by positivity : 0 < ε / 3)
  obtain ⟨L, hL⟩ := h i
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hL.cauchySeq (ε / 3) (by positivity)
  refine ⟨N, fun m hm n hn => ?_⟩
  rw [dist_eq_norm] at hi
  have h1 := abs_birkhoffAverage_le S (f - D i) m x
  have h2 := abs_birkhoffAverage_le S (f - D i) n x
  have e1 : birkhoffAverage ℝ S (⇑(f - D i)) m x =
      birkhoffAverage ℝ S f m x - birkhoffAverage ℝ S (D i) m x := birkhoffAverage_sub' S f (D i) m x
  have e2 : birkhoffAverage ℝ S (⇑(f - D i)) n x =
      birkhoffAverage ℝ S f n x - birkhoffAverage ℝ S (D i) n x := birkhoffAverage_sub' S f (D i) n x
  rw [e1] at h1
  rw [e2] at h2
  have h3 := hN m hm n hn
  rw [Real.dist_eq] at h3 ⊢
  have a1 := abs_le.1 h1
  have a2 := abs_le.1 h2
  have a3 := abs_lt.1 h3
  rw [abs_lt]
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]

/-- The set of points at which the Birkhoff averages of all continuous functions converge. -/
def G (S : X → X) : Set X := {x | ∀ f : C(X, ℝ), Conv S f x}

lemma G_eq {D : ℕ → C(X, ℝ)} (hD : DenseRange D) (S : X → X) :
    G S = ⋂ i, {x | Conv S (D i) x} := by
  ext x
  simp only [G, mem_iInter, mem_setOf_eq]
  exact ⟨fun h i => h _, fun h f => conv_of_dense hD h f⟩

lemma measurableSet_G {S : X → X} (hS : Measurable S) : MeasurableSet (G S) := by
  obtain ⟨D, hD⟩ := TopologicalSpace.exists_dense_seq C(X, ℝ)
  rw [G_eq hD]
  exact MeasurableSet.iInter fun i => StronglyMeasurable.measurableSet_exists_tendsto
    fun n => (measurable_birkhoffAverage hS (D i).continuous.measurable n).stronglyMeasurable

lemma integrable_cont (μ : Measure X) [IsFiniteMeasure μ] (f : C(X, ℝ)) : Integrable f μ :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma ae_mem_G {S : X → X} {μ : Measure X} [IsFiniteMeasure μ] (hμ : MeasurePreserving S μ μ) :
    ∀ᵐ x ∂μ, x ∈ G S := by
  obtain ⟨D, hD⟩ := TopologicalSpace.exists_dense_seq C(X, ℝ)
  have h : ∀ i, ∀ᵐ x ∂μ, Conv S (D i) x := fun i =>
    (birkhoff_ae_tendsto hμ (integrable_cont μ (D i))).mono fun x hx => ⟨_, hx⟩
  filter_upwards [ae_all_iff.2 h] with x hx
  exact fun f => conv_of_dense hD hx f

lemma tendsto_birkhoffLimit {S : X → X} {x : X} (hx : x ∈ G S) (f : C(X, ℝ)) :
    Tendsto (fun n => birkhoffAverage ℝ S f n x) atTop (𝓝 (birkhoffLimit S f x)) := by
  obtain ⟨L, hL⟩ := hx f
  rw [birkhoffLimit, hL.limUnder_eq]
  exact hL

/-! ### Empirical measures -/

/-- The empirical measure `(n+1)⁻¹ ∑_{i ≤ n} δ_{S^i x}`. -/
def emp (S : X → X) (n : ℕ) (x : X) : Measure X :=
  ((n : ℝ≥0∞) + 1)⁻¹ • ∑ i ∈ Finset.range (n + 1), Measure.dirac (S^[i] x)

lemma emp_univ (S : X → X) (n : ℕ) (x : X) : emp S n x univ = 1 := by
  simp only [emp, Measure.smul_apply, Measure.finsetSum_apply, measure_univ, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by simp) (by simp)

instance (S : X → X) (n : ℕ) (x : X) : IsProbabilityMeasure (emp S n x) := ⟨emp_univ S n x⟩

lemma integral_emp (S : X → X) (n : ℕ) (x : X) (f : C(X, ℝ)) :
    ∫ y, f y ∂(emp S n x) = birkhoffAverage ℝ S f (n + 1) x := by
  rw [emp, integral_smul_measure, integral_finsetSum_measure
    (fun i _ => integrable_cont _ f)]
  simp only [integral_dirac]
  have h : ((n : ℝ≥0∞) + 1).toReal = (n : ℝ) + 1 := by
    rw [ENNReal.toReal_add (ENNReal.natCast_ne_top n) ENNReal.one_ne_top]; simp
  rw [ENNReal.toReal_inv, h, birkhoffAverage, birkhoffSum]
  push_cast
  rfl

/-- The empirical measures as probability measures. -/
def empP (S : X → X) (n : ℕ) (x : X) : ProbabilityMeasure X := ⟨emp S n x, inferInstance⟩

/-! ### The limit kernel -/

/-- The weak limit of the empirical measures. -/
lemma exists_tendsto_empP {S : X → X} {x : X} (hx : x ∈ G S) :
    ∃ ν : ProbabilityMeasure X, Tendsto (fun n => empP S n x) atTop (𝓝 ν) ∧
      ∀ f : C(X, ℝ), ∫ y, f y ∂(ν : Measure X) = birkhoffLimit S f x := by
  have hint : ∀ (ν' : ProbabilityMeasure X) (ψ : ℕ → ℕ), Tendsto ψ atTop atTop →
      Tendsto (fun n => empP S (ψ n) x) atTop (𝓝 ν') →
      ∀ f : C(X, ℝ), ∫ y, f y ∂(ν' : Measure X) = birkhoffLimit S f x := by
    intro ν' ψ hψ h f
    have h1 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 h)
      (BoundedContinuousFunction.mkOfCompact f)
    simp only [BoundedContinuousFunction.mkOfCompact_apply] at h1
    have h2 : Tendsto (fun n => ∫ y, f y ∂(empP S (ψ n) x : Measure X)) atTop
        (𝓝 (birkhoffLimit S f x)) := by
      have := (tendsto_birkhoffLimit hx f).comp ((tendsto_add_atTop_nat 1).comp hψ)
      refine this.congr fun n => ?_
      simp only [Function.comp_apply]
      exact (integral_emp S (ψ n) x f).symm
    exact tendsto_nhds_unique h1 h2
  obtain ⟨ν, ψ, hψ, hν⟩ := CompactSpace.tendsto_subseq (fun n => empP S n x)
  refine ⟨ν, ?_, hint ν ψ hψ.tendsto_atTop hν⟩
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ν', ms, hms, hν'⟩ := CompactSpace.tendsto_subseq (fun n => empP S (ns n) x)
  refine ⟨ms, ?_⟩
  have hν'' := hint ν' (ns ∘ ms) (hns.comp hms.tendsto_atTop) hν'
  have hνν : ν' = ν := by
    have := ν.2
    have := ν'.2
    apply Subtype.ext
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    have := hν'' f.toContinuousMap
    rw [hint ν ψ hψ.tendsto_atTop hν f.toContinuousMap] at this
    exact this
  rw [← hνν]
  exact hν'

/-- The ergodic decomposition kernel `E(x)`. -/
def E (S : X → X) (x : X) : ProbabilityMeasure X :=
  if hx : x ∈ G S then (exists_tendsto_empP hx).choose
  else (⟨Measure.dirac x, inferInstance⟩ : ProbabilityMeasure X)

lemma integral_E {S : X → X} {x : X} (hx : x ∈ G S) (f : C(X, ℝ)) :
    ∫ y, f y ∂(E S x : Measure X) = birkhoffLimit S f x := by
  rw [E, dif_pos hx]
  exact (exists_tendsto_empP hx).choose_spec.2 f

lemma E_of_not_mem {S : X → X} {x : X} (hx : x ∉ G S) :
    (E S x : Measure X) = Measure.dirac x := by
  rw [E, dif_neg hx]; rfl

/-- `E` is measurable for the Giry σ-algebra. -/
lemma measurable_E {S : X → X} (hS : Measurable S) : Measurable (E S) := by
  have hG := measurableSet_G (X := X) hS
  -- integrals of nonnegative bounded continuous functions
  have hlin : ∀ g : X →ᵇ ℝ≥0, Measurable fun x => ∫⁻ y, g y ∂(E S x : Measure X) := by
    intro g
    set g' : C(X, ℝ) := ⟨fun y => (g y : ℝ), NNReal.continuous_coe.comp g.continuous⟩ with hg'
    have heq : (fun x => ∫⁻ y, g y ∂(E S x : Measure X)) = fun x =>
        if x ∈ G S then ENNReal.ofReal (birkhoffLimit S g' x) else (g x : ℝ≥0∞) := by
      funext x
      split_ifs with hx
      · rw [← integral_E hx g', ← toReal_lintegral_coe_eq_integral g,
          ENNReal.ofReal_toReal (lintegral_lt_top_of_nnreal _ g).ne]
      · rw [E_of_not_mem hx, lintegral_dirac]
    rw [heq]
    exact Measurable.ite hG (ENNReal.measurable_ofReal.comp
      (measurable_birkhoffLimit hS g'.continuous.measurable))
      (measurable_coe_nnreal_ennreal.comp g.continuous.measurable)
  -- closed sets
  have hclosed : ∀ F : Set X, IsClosed F → Measurable fun x => (E S x : Measure X) F := by
    intro F hF
    refine measurable_of_tendsto_metrizable (f := fun n x =>
      ∫⁻ y, hF.apprSeq n y ∂(E S x : Measure X)) (fun n => hlin _) ?_
    rw [tendsto_pi_nhds]
    intro x
    exact HasOuterApproxClosed.tendsto_lintegral_apprSeq hF _
  have hmeas : Measurable fun x => (E S x : Measure X) := by
    refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
      (S := {F : Set X | IsClosed F}) ?_ isPiSystem_isClosed ?_
    · rw [BorelSpace.measurable_eq (α := X), borel_eq_generateFrom_isClosed]
    · exact fun F hF => hclosed F hF
  exact hmeas.subtype_mk

/-! ### Invariance -/

lemma birkhoffAverage_succ (S : X → X) (f : X → ℝ) (n : ℕ) (x : X) :
    birkhoffAverage ℝ S f (n + 1) x =
      f x / ((n : ℝ) + 1) + ((n : ℝ) / ((n : ℝ) + 1)) * birkhoffAverage ℝ S f n (S x) := by
  simp only [birkhoffAverage_eq_div, birkhoffSum_succ_apply']
  push_cast
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp

/-- Convergence at `x` and at `S x` are equivalent, with the same limit. -/
lemma tendsto_comp_iff {S : X → X} (f : C(X, ℝ)) (x : X) (L : ℝ) :
    Tendsto (fun n => birkhoffAverage ℝ S f n (S x)) atTop (𝓝 L) ↔
      Tendsto (fun n => birkhoffAverage ℝ S f n x) atTop (𝓝 L) := by
  have h1 : Tendsto (fun n : ℕ => f x / ((n : ℝ) + 1)) atTop (𝓝 0) := by
    have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (f x)
    simpa [div_eq_mul_inv] using this
  have h2 : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 1) :=
    tendsto_natCast_div_add_atTop (1 : ℝ)
  constructor
  · intro h
    rw [← tendsto_add_atTop_iff_nat 1]
    have := h1.add (h2.mul h)
    simp only [zero_add, one_mul] at this
    refine this.congr fun n => ?_
    exact (birkhoffAverage_succ S f n x).symm
  · intro h
    have h' := (tendsto_add_atTop_iff_nat 1).2 h
    -- `A_n(Sx) = ((n+1)/n) (A_{n+1}(x) - f x/(n+1))`
    have h3 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 1) := by
      have : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
      rw [add_zero] at this
      refine this.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp
    have := h3.mul (h'.sub h1)
    simp only [sub_zero, one_mul] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [birkhoffAverage_succ]
    field_simp
    ring

lemma mem_G_comp {S : X → X} {x : X} (hx : x ∈ G S) : S x ∈ G S := fun f => by
  obtain ⟨L, hL⟩ := hx f
  exact ⟨L, (tendsto_comp_iff f x L).2 hL⟩

lemma birkhoffLimit_comp {S : X → X} {x : X} (hx : x ∈ G S) (f : C(X, ℝ)) :
    birkhoffLimit S f (S x) = birkhoffLimit S f x := by
  have h := tendsto_birkhoffLimit hx f
  have h' := (tendsto_comp_iff f x _).2 h
  rw [birkhoffLimit, h'.limUnder_eq]

lemma ProbabilityMeasure.ext_integral {ν ν' : ProbabilityMeasure X}
    (h : ∀ f : C(X, ℝ), ∫ y, f y ∂(ν : Measure X) = ∫ y, f y ∂(ν' : Measure X)) : ν = ν' := by
  have := ν.2
  have := ν'.2
  apply Subtype.ext
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  exact h f.toContinuousMap

lemma E_comp {S : X → X} {x : X} (hx : x ∈ G S) : E S (S x) = E S x :=
  ProbabilityMeasure.ext_integral fun f => by
    rw [integral_E (mem_G_comp hx), integral_E hx, birkhoffLimit_comp hx]

/-- `E(x)` is `S`-invariant. -/
lemma map_E {S : X → X} (hS : Continuous S) {x : X} (hx : x ∈ G S) :
    (E S x : Measure X).map S = E S x := by
  have := (E S x).2
  have : IsProbabilityMeasure ((E S x : Measure X).map S) :=
    (Measure.isProbabilityMeasure_map_iff hS.measurable.aemeasurable).2 inferInstance
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [integral_map hS.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  set g : C(X, ℝ) := f.toContinuousMap.comp ⟨S, hS⟩ with hg
  have h1 : ∫ y, f (S y) ∂(E S x : Measure X) = birkhoffLimit S g x := integral_E hx g
  have h2 : ∫ y, f y ∂(E S x : Measure X) = birkhoffLimit S f.toContinuousMap x :=
    integral_E hx f.toContinuousMap
  rw [h1, h2]
  -- `A_n (f ∘ S) x = A_n f (S x)`
  have e : ∀ n, birkhoffAverage ℝ S g n x = birkhoffAverage ℝ S f.toContinuousMap n (S x) := by
    intro n
    simp only [birkhoffAverage, birkhoffSum, hg, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Function.iterate_succ_apply' S k x, Function.iterate_succ_apply]
  have hlim := (tendsto_comp_iff f.toContinuousMap x _).2
    (tendsto_birkhoffLimit hx f.toContinuousMap)
  have hg' : Tendsto (fun n => birkhoffAverage ℝ S g n x) atTop
      (𝓝 (birkhoffLimit S f.toContinuousMap x)) := hlim.congr fun n => (e n).symm
  rw [birkhoffLimit, hg'.limUnder_eq]

end ErgDecomp

end DF
