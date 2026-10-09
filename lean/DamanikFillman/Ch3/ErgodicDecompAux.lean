/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §3.5: the ergodic decomposition, part 2: conditional expectations and ergodicity

## Main results

* `DF.ErgDecomp.lintegral_E_ae_eq` — `E(x)` disintegrates `μ` along invariant functions:
  `∫ φ dE(x) = φ(x)` for `μ`-a.e. `x` if `φ` is bounded, measurable and `S`-invariant;
* `DF.ErgDecomp.ae_ae_fstar_eq` — for `μ`-a.e. `x`, the Birkhoff limit `f*` is `E(x)`-a.e.
  constant;
* `DF.ErgDecomp.ergodic_of_fstar_const` — an invariant probability measure for which the Birkhoff
  limits of a dense sequence of continuous functions are a.e. constant is ergodic;
* `DF.ErgDecomp.ae_E_eq_of_ergodic` — for ergodic `ν`, `E = ν` holds `ν`-a.e.
-/
import DamanikFillman.Ch3.ErgodicDecompKernel

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Set Function Topology
open scoped ENNReal NNReal BoundedContinuousFunction

namespace DF

namespace ErgDecomp

open Birkhoff

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

attribute [local instance] Classical.propDecidable

/-! ### The Birkhoff limit, made bounded and invariant -/

lemma mem_G_comp_iff {S : X → X} {x : X} : S x ∈ G S ↔ x ∈ G S :=
  ⟨fun h f => by obtain ⟨L, hL⟩ := h f; exact ⟨L, (tendsto_comp_iff f x L).1 hL⟩, mem_G_comp⟩

/-- The Birkhoff limit on `G`, and `0` off `G`. -/
def fstar (S : X → X) (f : C(X, ℝ)) (x : X) : ℝ := if x ∈ G S then birkhoffLimit S f x else 0

lemma measurable_fstar {S : X → X} (hS : Measurable S) (f : C(X, ℝ)) : Measurable (fstar S f) :=
  Measurable.ite (measurableSet_G hS) (measurable_birkhoffLimit hS f.continuous.measurable)
    measurable_const

lemma abs_fstar_le (S : X → X) (f : C(X, ℝ)) (x : X) : |fstar S f x| ≤ ‖f‖ := by
  unfold fstar
  split_ifs with hx
  · exact le_of_tendsto' (tendsto_birkhoffLimit hx f).abs fun n =>
      abs_birkhoffAverage_le S f n x
  · simp

lemma fstar_comp (S : X → X) (f : C(X, ℝ)) (x : X) : fstar S f (S x) = fstar S f x := by
  unfold fstar
  by_cases hx : x ∈ G S
  · rw [if_pos (mem_G_comp hx), if_pos hx, birkhoffLimit_comp hx]
  · rw [if_neg (mt mem_G_comp_iff.1 hx), if_neg hx]

lemma fstar_nonneg (S : X → X) {f : C(X, ℝ)} (hf : ∀ y, 0 ≤ f y) (x : X) : 0 ≤ fstar S f x := by
  unfold fstar
  split_ifs with hx
  · refine ge_of_tendsto' (tendsto_birkhoffLimit hx f) fun n => ?_
    rw [birkhoffAverage_eq_div]
    exact div_nonneg (Finset.sum_nonneg fun k _ => hf _) (Nat.cast_nonneg n)
  · exact le_rfl

lemma integral_E_eq_fstar {S : X → X} {x : X} (hx : x ∈ G S) (f : C(X, ℝ)) :
    ∫ y, f y ∂(E S x : Measure X) = fstar S f x := by
  rw [integral_E hx, fstar, if_pos hx]

lemma iterate_invariant {S : X → X} {ψ : X → ℝ} (hψ : ∀ x, ψ (S x) = ψ x) (k : ℕ) (x : X) :
    ψ (S^[k] x) = ψ x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', hψ, ih]

lemma integrable_of_bdd {μ : Measure X} [IsFiniteMeasure μ] {g : X → ℝ} (hg : Measurable g)
    {c : ℝ} (hc : ∀ x, |g x| ≤ c) : Integrable g μ :=
  Integrable.of_bound hg.aestronglyMeasurable c (Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hc x)

/-! ### Integrals against invariant functions -/

lemma integral_comp_iterate {S : X → X} {μ : Measure X} (hμ : MeasurePreserving S μ μ)
    {g : X → ℝ} (hg : Measurable g) (k : ℕ) : ∫ x, g (S^[k] x) ∂μ = ∫ x, g x ∂μ := by
  have h := hμ.iterate k
  conv_rhs => rw [← h.map_eq]
  rw [integral_map h.measurable.aemeasurable hg.aestronglyMeasurable]

/-- Averages of `g` along orbits have the same integral against invariant functions. -/
lemma integral_mul_birkhoffAverage {S : X → X} {μ : Measure X} [IsFiniteMeasure μ]
    (hμ : MeasurePreserving S μ μ) {ψ g : X → ℝ} (hψm : Measurable ψ) {c c' : ℝ}
    (hψb : ∀ x, |ψ x| ≤ c) (hψ : ∀ x, ψ (S x) = ψ x) (hgm : Measurable g) (hgb : ∀ x, |g x| ≤ c')
    {n : ℕ} (hn : 0 < n) :
    ∫ x, ψ x * birkhoffAverage ℝ S g n x ∂μ = ∫ x, ψ x * g x ∂μ := by
  have hS := hμ.measurable
  have hint : ∀ k, Integrable (fun x => ψ x * g (S^[k] x)) μ := fun k =>
    integrable_of_bdd (hψm.mul (hgm.comp (hS.iterate k))) (c := c * c') fun x => by
      rw [abs_mul]
      exact mul_le_mul (hψb x) (hgb _) (abs_nonneg _) ((abs_nonneg _).trans (hψb x))
  have hk : ∀ k, ∫ x, ψ x * g (S^[k] x) ∂μ = ∫ x, ψ x * g x ∂μ := by
    intro k
    calc ∫ x, ψ x * g (S^[k] x) ∂μ = ∫ x, (fun x => ψ x * g x) (S^[k] x) ∂μ := by
          simp only [iterate_invariant hψ k]
      _ = ∫ x, (fun x => ψ x * g x) x ∂μ :=
          integral_comp_iterate hμ (g := fun x => ψ x * g x) (hψm.mul hgm) k
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  calc ∫ x, ψ x * birkhoffAverage ℝ S g n x ∂μ
      = ∫ x, (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, ψ x * g (S^[k] x) ∂μ := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [birkhoffAverage, birkhoffSum, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ = (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, ∫ x, ψ x * g (S^[k] x) ∂μ := by
        rw [integral_const_mul, integral_finset_sum _ fun k _ => hint k]
    _ = ∫ x, ψ x * g x ∂μ := by
        simp only [hk, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        field_simp

/-- `∫ ψ f* dμ = ∫ ψ f dμ` for invariant bounded `ψ`. -/
lemma integral_mul_fstar {S : X → X} {μ : Measure X} [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving S μ μ) {ψ : X → ℝ} (hψm : Measurable ψ) {c : ℝ}
    (hψb : ∀ x, |ψ x| ≤ c) (hψ : ∀ x, ψ (S x) = ψ x) (f : C(X, ℝ)) :
    ∫ x, ψ x * fstar S f x ∂μ = ∫ x, ψ x * f x ∂μ := by
  have hS := hμ.measurable
  have hψb2 : ∀ x, |ψ x| ≤ max c 0 := fun x => (hψb x).trans (le_max_left _ _)
  have hc : (0 : ℝ) ≤ max c 0 := le_max_right _ _
  have hlim : Tendsto (fun n => ∫ x, ψ x * birkhoffAverage ℝ S f n x ∂μ) atTop
      (𝓝 (∫ x, ψ x * fstar S f x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => max c 0 * ‖f‖) (fun n => ?_)
      (integrable_const _) (fun n => Eventually.of_forall fun x => ?_) ?_
    · exact (hψm.mul (measurable_birkhoffAverage hS f.continuous.measurable n)).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hψb2 x) (abs_birkhoffAverage_le S f n x) (abs_nonneg _) hc
    · filter_upwards [ae_mem_G hμ] with x hx
      have := (tendsto_birkhoffLimit hx f).const_mul (ψ x)
      rwa [fstar, if_pos hx]
  have hconst : ∀ᶠ n in atTop, ∫ x, ψ x * birkhoffAverage ℝ S f n x ∂μ = ∫ x, ψ x * f x ∂μ := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact integral_mul_birkhoffAverage hμ hψm hψb hψ f.continuous.measurable
      (fun x => by rw [← Real.norm_eq_abs]; exact f.norm_coe_le_norm x) hn
  exact tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hconst.mono fun n h => h.symm))

/-! ### The disintegration identity -/

lemma measurable_E_coe {S : X → X} (hS : Measurable S) :
    Measurable fun x => (E S x : Measure X) :=
  measurable_subtype_coe.comp (measurable_E hS)

lemma measurable_lintegral_E {S : X → X} (hS : Measurable S) {φ : X → ℝ≥0∞} (hφ : Measurable φ) :
    Measurable fun x => ∫⁻ y, φ y ∂(E S x : Measure X) :=
  (Measure.measurable_lintegral hφ).comp (measurable_E_coe hS)

/-- The key identity: integrating `E(x)` against `ψ dμ` gives `ψ dμ`, for invariant `ψ ≥ 0`. -/
lemma bind_withDensity {S : X → X} {μ : Measure X} [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving S μ μ) {ψ : X → ℝ} (hψm : Measurable ψ) {c : ℝ}
    (hψ0 : ∀ x, 0 ≤ ψ x) (hψb : ∀ x, ψ x ≤ c) (hψ : ∀ x, ψ (S x) = ψ x) :
    (μ.withDensity fun x => ENNReal.ofReal (ψ x)).bind (fun x => (E S x : Measure X)) =
      μ.withDensity fun x => ENNReal.ofReal (ψ x) := by
  have hS := hμ.measurable
  have hEm := measurable_E_coe (X := X) hS
  have hψm' : Measurable fun x => ENNReal.ofReal (ψ x) := ENNReal.measurable_ofReal.comp hψm
  have hψb' : ∀ x, |ψ x| ≤ c := fun x => by rw [abs_of_nonneg (hψ0 x)]; exact hψb x
  have hfin : IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (ψ x)) :=
    isFiniteMeasure_withDensity_ofReal (integrable_of_bdd hψm hψb').2
  have hfinb : IsFiniteMeasure
      ((μ.withDensity fun x => ENNReal.ofReal (ψ x)).bind (fun x => (E S x : Measure X))) := by
    constructor
    rw [Measure.bind_apply MeasurableSet.univ hEm.aemeasurable]
    simp only [measure_univ, lintegral_const, one_mul]
    exact measure_lt_top _ _
  refine ext_of_forall_lintegral_eq_of_IsFiniteMeasure fun g => ?_
  have hgm : Measurable fun y => (g y : ℝ≥0∞) :=
    measurable_coe_nnreal_ennreal.comp g.continuous.measurable
  set g' : C(X, ℝ) := nnC g with hg'
  have hg'0 : ∀ y, 0 ≤ g' y := fun y => NNReal.coe_nonneg (g y)
  have hg'b : ∀ y, |g' y| ≤ ‖g'‖ := fun y => by
    rw [← Real.norm_eq_abs]; exact g'.norm_coe_le_norm y
  rw [Measure.lintegral_bind hEm.aemeasurable hgm.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ hψm' (measurable_lintegral_E hS hgm),
    lintegral_withDensity_eq_lintegral_mul _ hψm' hgm]
  -- both sides are `ofReal` of real integrals
  have hL : ∀ᵐ x ∂μ, ((fun x => ENNReal.ofReal (ψ x)) * fun x =>
      ∫⁻ y, (g y : ℝ≥0∞) ∂(E S x : Measure X)) x = ENNReal.ofReal (ψ x * fstar S g' x) := by
    filter_upwards [ae_mem_G hμ] with x hx
    have := (E S x).2
    simp only [Pi.mul_apply]
    rw [← integral_E_eq_fstar hx g', ENNReal.ofReal_mul (hψ0 x), hg', lintegral_nnreal_eq]
  have hR : ∀ x, ((fun x => ENNReal.ofReal (ψ x)) * fun y => (g y : ℝ≥0∞)) x =
      ENNReal.ofReal (ψ x * g' x) := fun x => by
    simp only [Pi.mul_apply, hg', nnC, ContinuousMap.coe_mk]
    rw [ENNReal.ofReal_mul (hψ0 x), ENNReal.ofReal_coe_nnreal]
  rw [lintegral_congr_ae hL, lintegral_congr (fun x => hR x),
    ← ofReal_integral_eq_lintegral_ofReal, ← ofReal_integral_eq_lintegral_ofReal,
    integral_mul_fstar hμ hψm hψb' hψ g']
  · exact integrable_of_bdd (hψm.mul g'.continuous.measurable) (c := c * ‖g'‖) fun x => by
      rw [abs_mul]; exact mul_le_mul (hψb' x) (hg'b x) (abs_nonneg _)
        ((abs_nonneg _).trans (hψb' x))
  · exact Eventually.of_forall fun x => mul_nonneg (hψ0 x) (hg'0 x)
  · exact integrable_of_bdd (hψm.mul (measurable_fstar hS g')) (c := c * ‖g'‖) fun x => by
      rw [abs_mul]; exact mul_le_mul (hψb' x) (abs_fstar_le S g' x) (abs_nonneg _)
        ((abs_nonneg _).trans (hψb' x))
  · exact Eventually.of_forall fun x => mul_nonneg (hψ0 x) (fstar_nonneg S hg'0 x)

/-- The disintegration identity for nonnegative measurable `φ`. -/
lemma lintegral_mul_lintegral_E {S : X → X} {μ : Measure X} [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving S μ μ) {ψ : X → ℝ} (hψm : Measurable ψ) {c : ℝ}
    (hψ0 : ∀ x, 0 ≤ ψ x) (hψb : ∀ x, ψ x ≤ c) (hψ : ∀ x, ψ (S x) = ψ x)
    {φ : X → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ x, ENNReal.ofReal (ψ x) * ∫⁻ y, φ y ∂(E S x : Measure X) ∂μ =
      ∫⁻ x, ENNReal.ofReal (ψ x) * φ x ∂μ := by
  have hS := hμ.measurable
  have hψm' : Measurable fun x => ENNReal.ofReal (ψ x) := ENNReal.measurable_ofReal.comp hψm
  have h := congrArg (fun m : Measure X => ∫⁻ y, φ y ∂m) (bind_withDensity hμ hψm hψ0 hψb hψ)
  rw [Measure.lintegral_bind (measurable_E_coe hS).aemeasurable hφ.aemeasurable,
    lintegral_withDensity_eq_lintegral_mul _ hψm' (measurable_lintegral_E hS hφ),
    lintegral_withDensity_eq_lintegral_mul _ hψm' hφ] at h
  exact h

lemma lintegral_E_comp {S : X → X} {φ : X → ℝ≥0∞} (hφ : ∀ x, φ (S x) = φ x) (x : X) :
    ∫⁻ y, φ y ∂(E S (S x) : Measure X) = ∫⁻ y, φ y ∂(E S x : Measure X) := by
  by_cases hx : x ∈ G S
  · rw [E_comp hx]
  · rw [E_of_not_mem hx, E_of_not_mem (mt mem_G_comp_iff.1 hx), lintegral_dirac, lintegral_dirac,
      hφ]

/-- **Conditional expectations**: `∫ φ dE(x) = φ(x)` a.e. for bounded invariant `φ`. -/
theorem lintegral_E_ae_eq {S : X → X} {μ : Measure X} [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving S μ μ) {φ : X → ℝ≥0∞} (hφm : Measurable φ) {C : ℝ≥0∞}
    (hC : C ≠ ⊤) (hφb : ∀ x, φ x ≤ C) (hφ : ∀ x, φ (S x) = φ x) :
    ∀ᵐ x ∂μ, ∫⁻ y, φ y ∂(E S x : Measure X) = φ x := by
  have hS := hμ.measurable
  set h : X → ℝ≥0∞ := fun x => ∫⁻ y, φ y ∂(E S x : Measure X) with hh
  have hhm : Measurable h := measurable_lintegral_E hS hφm
  have hhb : ∀ x, h x ≤ C := fun x => by
    have := (E S x).2
    calc h x ≤ ∫⁻ _y, C ∂(E S x : Measure X) := lintegral_mono fun y => hφb y
      _ = C := by simp
  have hhS : ∀ x, h (S x) = h x := fun x => lintegral_E_comp hφ x
  -- the identity on invariant sets
  have hset : ∀ A : Set X, MeasurableSet A → S ⁻¹' A = A →
      ∫⁻ x in A, h x ∂μ = ∫⁻ x in A, φ x ∂μ := by
    intro A hA hAinv
    have hψ : ∀ x, A.indicator (fun _ => (1 : ℝ)) (S x) = A.indicator (fun _ => (1 : ℝ)) x := by
      intro x
      have : S x ∈ A ↔ x ∈ A := by
        rw [← Set.mem_preimage, hAinv]
      by_cases hx : x ∈ A
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (this.2 hx)]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (mt this.1 hx)]
    have hle : ∀ x, A.indicator (fun _ => (1 : ℝ)) x ≤ 1 := fun x => by
      by_cases hx : x ∈ A
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    have key := lintegral_mul_lintegral_E hμ (measurable_const.indicator hA) (c := 1)
      (fun x => Set.indicator_nonneg (fun _ _ => zero_le_one) x) hle hψ hφm
    have e : ∀ u : X → ℝ≥0∞, (fun x => ENNReal.ofReal (A.indicator (fun _ => (1 : ℝ)) x) * u x) =
        A.indicator u := by
      intro u; funext x
      by_cases hx : x ∈ A
      · simp [Set.indicator_of_mem hx]
      · simp [Set.indicator_of_notMem hx]
    rw [e h, e φ] at key
    rw [← lintegral_indicator hA, ← lintegral_indicator hA]
    exact key
  have hfin : ∀ A, ∫⁻ x in A, h x ∂μ ≠ ⊤ := fun A => by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hC (measure_ne_top (μ.restrict A) univ)) ?_
    calc ∫⁻ x in A, h x ∂μ ≤ ∫⁻ _x in A, C ∂μ := lintegral_mono fun x => hhb x
      _ = C * μ.restrict A univ := lintegral_const C
  have hfin' : ∀ A, ∫⁻ x in A, φ x ∂μ ≠ ⊤ := fun A => by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hC (measure_ne_top (μ.restrict A) univ)) ?_
    calc ∫⁻ x in A, φ x ∂μ ≤ ∫⁻ _x in A, C ∂μ := lintegral_mono fun x => hφb x
      _ = C * μ.restrict A univ := lintegral_const C
  -- `h < φ` and `φ < h` are null
  have hlt : ∀ (u v : X → ℝ≥0∞), Measurable u → Measurable v → (∀ x, u (S x) = u x) →
      (∀ x, v (S x) = v x) → (∀ A, ∫⁻ x in A, u x ∂μ ≠ ⊤) →
      (∀ A, MeasurableSet A → S ⁻¹' A = A → ∫⁻ x in A, u x ∂μ = ∫⁻ x in A, v x ∂μ) →
      μ {x | u x < v x} = 0 := by
    intro u v hu hv huS hvS hufin heq
    have hA : MeasurableSet {x | u x < v x} := measurableSet_lt hu hv
    have hAinv : S ⁻¹' {x | u x < v x} = {x | u x < v x} := by
      ext x; simp only [Set.mem_preimage, Set.mem_setOf_eq, huS, hvS]
    by_contra hne
    have := setLIntegral_strict_mono hA hne hv (hufin _)
      (Eventually.of_forall fun x hx => hx)
    rw [heq _ hA hAinv] at this
    exact lt_irrefl _ this
  have h1 := hlt h φ hhm hφm hhS hφ hfin hset
  have h2 := hlt φ h hφm hhm hφ hhS hfin' (fun A hA hAinv => (hset A hA hAinv).symm)
  have h1' : ∀ᵐ x ∂μ, ¬ h x < φ x := measure_eq_zero_iff_ae_notMem.1 h1
  have h2' : ∀ᵐ x ∂μ, ¬ φ x < h x := measure_eq_zero_iff_ae_notMem.1 h2
  filter_upwards [h1', h2'] with x hx1 hx2
  exact le_antisymm (not_lt.1 hx2) (not_lt.1 hx1)

/-! ### `f*` is `E(x)`-a.e. constant -/

lemma integrable_E {S : X → X} (x : X) {g : X → ℝ} (hg : Measurable g) {c : ℝ}
    (hc : ∀ y, |g y| ≤ c) : Integrable g (E S x : Measure X) := by
  have := (E S x).2
  exact integrable_of_bdd hg hc

/-- Real version of `lintegral_E_ae_eq` for nonnegative bounded invariant `u`. -/
lemma integral_E_ae_eq {S : X → X} {μ : Measure X} [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving S μ μ) {u : X → ℝ} (hum : Measurable u) {c : ℝ} (hu0 : ∀ x, 0 ≤ u x)
    (hub : ∀ x, u x ≤ c) (huS : ∀ x, u (S x) = u x) :
    ∀ᵐ x ∂μ, ∫ y, u y ∂(E S x : Measure X) = u x := by
  have h := lintegral_E_ae_eq hμ (φ := fun x => ENNReal.ofReal (u x))
    (ENNReal.measurable_ofReal.comp hum) ENNReal.ofReal_ne_top
    (fun x => ENNReal.ofReal_le_ofReal (hub x)) (fun x => by simp only [huS])
  filter_upwards [h] with x hx
  have := (E S x).2
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hu0) hum.aestronglyMeasurable, hx,
    ENNReal.toReal_ofReal (hu0 x)]

/-- For `μ`-a.e. `x`, the Birkhoff limit `f*` is `E(x)`-a.e. equal to `f*(x)`. -/
theorem ae_ae_fstar_eq {S : X → X} {μ : Measure X} [IsProbabilityMeasure μ]
    (hμ : MeasurePreserving S μ μ) (f : C(X, ℝ)) :
    ∀ᵐ x ∂μ, ∀ᵐ y ∂(E S x : Measure X), fstar S f y = fstar S f x := by
  have hS := hμ.measurable
  set u : X → ℝ := fun y => fstar S f y + ‖f‖ with hu
  have hum : Measurable u := (measurable_fstar hS f).add measurable_const
  have hu0 : ∀ y, 0 ≤ u y := fun y => by
    have := abs_le.1 (abs_fstar_le S f y); simp only [hu]; linarith
  have hub : ∀ y, u y ≤ 2 * ‖f‖ := fun y => by
    have := abs_le.1 (abs_fstar_le S f y); simp only [hu]; linarith
  have huS : ∀ y, u (S y) = u y := fun y => by simp only [hu, fstar_comp]
  have h1 := integral_E_ae_eq hμ hum hu0 hub huS
  have h2 := integral_E_ae_eq hμ (hum.pow_const 2) (c := (2 * ‖f‖) ^ 2)
    (fun y => sq_nonneg _) (fun y => pow_le_pow_left₀ (hu0 y) (hub y) 2)
    (fun y => by simp only [huS])
  filter_upwards [h1, h2] with x hx1 hx2
  have := (E S x).2
  have hi1 : Integrable u (E S x : Measure X) :=
    integrable_E x hum (c := 2 * ‖f‖) fun y => by rw [abs_of_nonneg (hu0 y)]; exact hub y
  have hi2 : Integrable (fun y => u y ^ 2) (E S x : Measure X) :=
    integrable_E x (hum.pow_const 2) (c := (2 * ‖f‖) ^ 2) fun y => by
      rw [abs_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (hu0 y) (hub y) 2
  -- the variance vanishes
  have hvar : ∫ y, (u y - u x) ^ 2 ∂(E S x : Measure X) = 0 := by
    have e : (fun y => (u y - u x) ^ 2) = fun y => u y ^ 2 - 2 * u x * u y + u x ^ 2 := by
      funext y; ring
    have i2 : Integrable (fun y => 2 * u x * u y) (E S x : Measure X) := hi1.const_mul _
    have i1 : Integrable (fun y => u y ^ 2 - 2 * u x * u y) (E S x : Measure X) := hi2.sub i2
    rw [e, integral_add i1 (integrable_const _), integral_sub hi2 i2, integral_const_mul, hx2, hx1]
    simp only [integral_const, measureReal_univ_eq_one, one_smul]
    ring
  have hz := (integral_eq_zero_iff_of_nonneg (fun y => sq_nonneg (u y - u x))
    (hi2.sub (hi1.const_mul (2 * u x)) |>.add (integrable_const (u x ^ 2)) |>.congr
      (Eventually.of_forall fun y => by simp only [Pi.add_apply, Pi.sub_apply]; ring))).1 hvar
  filter_upwards [hz] with y hy
  simp only [Pi.zero_apply, pow_eq_zero_iff two_ne_zero, sub_eq_zero, hu] at hy
  linarith

/-! ### An ergodicity criterion -/

/-- `|f* - 1_A|` is controlled by `|f - 1_A|` for invariant `A`. -/
lemma integral_abs_fstar_sub_le {S : X → X} {ν : Measure X} [IsProbabilityMeasure ν]
    (hν : MeasurePreserving S ν ν) (f : C(X, ℝ)) {A : Set X} (hA : MeasurableSet A)
    (hAinv : S ⁻¹' A = A) :
    ∫ y, |fstar S f y - A.indicator (fun _ => (1 : ℝ)) y| ∂ν ≤
      ∫ y, |f y - A.indicator (fun _ => (1 : ℝ)) y| ∂ν := by
  have hS := hν.measurable
  set ind : X → ℝ := A.indicator (fun _ => (1 : ℝ)) with hind
  have hindm : Measurable ind := measurable_const.indicator hA
  have hindb : ∀ y, |ind y| ≤ 1 := fun y => by
    by_cases hy : y ∈ A
    · simp [hind, Set.indicator_of_mem hy]
    · simp [hind, Set.indicator_of_notMem hy]
  have hindS : ∀ y, ind (S y) = ind y := fun y => by
    have : S y ∈ A ↔ y ∈ A := by rw [← Set.mem_preimage, hAinv]
    by_cases hy : y ∈ A
    · simp [hind, Set.indicator_of_mem hy, Set.indicator_of_mem (this.2 hy)]
    · simp [hind, Set.indicator_of_notMem hy, Set.indicator_of_notMem (mt this.1 hy)]
  set h : X → ℝ := fun y => |f y - ind y| with hh
  have hhm : Measurable h := (f.continuous.measurable.sub hindm).abs
  have hhb : ∀ y, |h y| ≤ ‖f‖ + 1 := fun y => by
    simp only [hh, abs_abs]
    refine (abs_sub _ _).trans ?_
    have := f.norm_coe_le_norm y
    rw [Real.norm_eq_abs] at this
    linarith [hindb y]
  -- `|A_n f - 1_A| ≤ A_n |f - 1_A|`
  have hpt : ∀ n y, 0 < n →
      |birkhoffAverage ℝ S f n y - ind y| ≤ birkhoffAverage ℝ S h n y := by
    intro n y hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have e : birkhoffAverage ℝ S f n y - ind y =
        birkhoffAverage ℝ S (fun z => f z - ind z) n y := by
      rw [birkhoffAverage_sub']
      congr 1
      rw [birkhoffAverage_eq_div, birkhoffSum]
      simp only [iterate_invariant hindS, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
    rw [e, birkhoffAverage_eq_div, birkhoffAverage_eq_div, abs_div, abs_of_pos hn']
    refine div_le_div_of_nonneg_right ?_ hn'.le
    unfold birkhoffSum
    exact Finset.abs_sum_le_sum_abs _ _
  have hlim : Tendsto (fun n => ∫ y, |birkhoffAverage ℝ S f n y - ind y| ∂ν) atTop
      (𝓝 (∫ y, |fstar S f y - ind y| ∂ν)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => ‖f‖ + 1) (fun n => ?_)
      (integrable_const _) (fun n => Eventually.of_forall fun y => ?_) ?_
    · exact ((measurable_birkhoffAverage hS f.continuous.measurable n).sub
        hindm).abs.aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_abs]
      refine (abs_sub _ _).trans ?_
      linarith [abs_birkhoffAverage_le S f n y, hindb y]
    · filter_upwards [ae_mem_G hν] with y hy
      have := ((tendsto_birkhoffLimit hy f).sub_const (ind y)).abs
      rwa [fstar, if_pos hy]
  refine le_of_tendsto hlim ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  calc ∫ y, |birkhoffAverage ℝ S f n y - ind y| ∂ν ≤ ∫ y, birkhoffAverage ℝ S h n y ∂ν :=
        integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _)
          ((integrable_of_bdd (measurable_birkhoffAverage hS hhm n)
            (c := ‖f‖ + 1) fun y => by
              rw [birkhoffAverage_eq_div]
              rcases Nat.eq_zero_or_pos n with rfl | hn0
              · simp; linarith [norm_nonneg f]
              · have hn0' : (0 : ℝ) < n := by exact_mod_cast hn0
                rw [abs_div, abs_of_pos hn0', div_le_iff₀ hn0']
                unfold birkhoffSum
                refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
                refine (Finset.sum_le_sum fun k _ => hhb _).trans ?_
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]))
          (Eventually.of_forall fun y => hpt n y hn)
    _ = ∫ y, h y ∂ν := by
        have := integral_mul_birkhoffAverage hν (ψ := fun _ => (1 : ℝ)) measurable_const
          (c := 1) (fun _ => by norm_num) (fun _ => rfl) hhm hhb hn
        simpa using this

lemma integral_abs_const_sub_indicator {ν : Measure X} [IsProbabilityMeasure ν] (c : ℝ)
    {A : Set X} (hA : MeasurableSet A) :
    ∫ y, |c - A.indicator (fun _ => (1 : ℝ)) y| ∂ν =
      |c - 1| * ν.real A + |c| * ν.real Aᶜ := by
  have hint : Integrable (fun y => |c - A.indicator (fun _ => (1 : ℝ)) y|) ν :=
    integrable_of_bdd ((measurable_const.sub (measurable_const.indicator hA)).abs)
      (c := |c| + 1) fun y => by
        rw [abs_abs]
        refine (abs_sub _ _).trans ?_
        by_cases hy : y ∈ A
        · simp [Set.indicator_of_mem hy]
        · simp [Set.indicator_of_notMem hy]
  rw [← integral_add_compl hA hint]
  have h1 : ∫ y in A, |c - A.indicator (fun _ => (1 : ℝ)) y| ∂ν = ∫ _y in A, |c - 1| ∂ν :=
    setIntegral_congr_fun hA fun y hy => by simp [Set.indicator_of_mem hy]
  have h2 : ∫ y in Aᶜ, |c - A.indicator (fun _ => (1 : ℝ)) y| ∂ν = ∫ _y in Aᶜ, |c| ∂ν :=
    setIntegral_congr_fun hA.compl fun y hy => by
      simp [Set.indicator_of_notMem (show y ∉ A from hy)]
  rw [h1, h2, setIntegral_const, setIntegral_const, smul_eq_mul, smul_eq_mul]
  ring

/-- **Ergodicity criterion**: an invariant probability measure for which the Birkhoff limits of a
dense sequence of continuous functions are a.e. constant is ergodic. -/
theorem ergodic_of_fstar_const {S : X → X} {ν : Measure X} [IsProbabilityMeasure ν]
    (hν : MeasurePreserving S ν ν) {D : ℕ → C(X, ℝ)} (hD : DenseRange D)
    (hc : ∀ i, ∃ c, ∀ᵐ y ∂ν, fstar S (D i) y = c) : Ergodic S ν := by
  refine Ergodic.of_preimage_eq hν fun A hA hAinv => ?_
  -- `ν(A) (1 - ν(A))`-type quantity is arbitrarily small
  have hsmall : ∀ ε > (0 : ℝ), min (ν.real A) (ν.real Aᶜ) ≤ 3 * ε := by
    intro ε hε
    have hindi : Integrable (A.indicator (fun _ => (1 : ℝ))) ν :=
      integrable_of_bdd (measurable_const.indicator hA) (c := 1) fun y => by
        by_cases hy : y ∈ A
        · simp [Set.indicator_of_mem hy]
        · simp [Set.indicator_of_notMem hy]
    obtain ⟨g, hg, -⟩ := hindi.exists_boundedContinuous_integral_sub_le hε
    obtain ⟨i, hi⟩ := hD.exists_dist_lt g.toContinuousMap hε
    rw [dist_eq_norm] at hi
    obtain ⟨c, hci⟩ := hc i
    have h1 := integral_abs_fstar_sub_le hν (D i) hA hAinv
    have h2 : ∫ y, |D i y - A.indicator (fun _ => (1 : ℝ)) y| ∂ν ≤ 2 * ε := by
      calc ∫ y, |D i y - A.indicator (fun _ => (1 : ℝ)) y| ∂ν
          ≤ ∫ y, (ε + ‖A.indicator (fun _ => (1 : ℝ)) y - g y‖) ∂ν := by
            refine integral_mono (integrable_of_bdd ((D i).continuous.measurable.sub
              (measurable_const.indicator hA)).abs (c := ‖D i‖ + 1) fun y => by
                rw [abs_abs]; refine (abs_sub _ _).trans ?_
                have := (D i).norm_coe_le_norm y; rw [Real.norm_eq_abs] at this
                by_cases hy : y ∈ A
                · simp [Set.indicator_of_mem hy]; linarith
                · simp [Set.indicator_of_notMem hy]; linarith)
              ((integrable_const ε).add (hindi.sub (g.integrable ν)).norm) fun y => ?_
            have h3 : |D i y - g y| ≤ ε := by
              have := (g.toContinuousMap - D i).norm_coe_le_norm y
              rw [norm_sub_rev] at hi
              rw [Real.norm_eq_abs, ContinuousMap.sub_apply, abs_sub_comm] at this
              exact this.trans (hi.le.trans_eq' (by rw [norm_sub_rev]))
            rw [Real.norm_eq_abs]
            calc |D i y - A.indicator (fun _ => (1 : ℝ)) y|
                ≤ |D i y - g y| + |g y - A.indicator (fun _ => (1 : ℝ)) y| := abs_sub_le _ _ _
              _ ≤ ε + |A.indicator (fun _ => (1 : ℝ)) y - g y| := by
                  rw [abs_sub_comm (g y)]; linarith
        _ = ε + ∫ y, ‖A.indicator (fun _ => (1 : ℝ)) y - g y‖ ∂ν := by
            rw [integral_add (integrable_const ε) (hindi.sub (g.integrable ν)).norm]
            simp
        _ ≤ 2 * ε := by linarith
    have h4 : ∫ y, |fstar S (D i) y - A.indicator (fun _ => (1 : ℝ)) y| ∂ν =
        ∫ y, |c - A.indicator (fun _ => (1 : ℝ)) y| ∂ν :=
      integral_congr_ae (hci.mono fun y hy => by simp only [hy])
    rw [h4, integral_abs_const_sub_indicator c hA] at h1
    have h5 : min (ν.real A) (ν.real Aᶜ) ≤ |c - 1| * ν.real A + |c| * ν.real Aᶜ := by
      have hA0 := measureReal_nonneg (μ := ν) (s := A)
      have hAc0 := measureReal_nonneg (μ := ν) (s := Aᶜ)
      have htri : 1 ≤ |c - 1| + |c| := by
        have := abs_sub_abs_le_abs_sub c (c - 1)
        rw [sub_sub_cancel] at this
        have := abs_sub_comm c (c - 1)
        linarith [abs_nonneg c, abs_nonneg (c - 1), abs_sub_le (1 : ℝ) c 0, abs_sub_comm (c - 1) 0]
      rcases le_total (ν.real A) (ν.real Aᶜ) with h | h
      · rw [min_eq_left h]; nlinarith [abs_nonneg c, abs_nonneg (c - 1)]
      · rw [min_eq_right h]; nlinarith [abs_nonneg c, abs_nonneg (c - 1)]
    linarith
  have hmin : min (ν.real A) (ν.real Aᶜ) = 0 := by
    refine le_antisymm ?_ (le_min measureReal_nonneg measureReal_nonneg)
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have := hsmall (ε / 3) (by positivity)
    linarith
  rcases min_eq_iff.1 hmin with ⟨h, -⟩ | ⟨h, -⟩
  · refine eventuallyEmptyOrUniv_iff.2 (Or.inr ?_)
    exact measure_eq_zero_iff_ae_notMem.1 ((measureReal_eq_zero_iff (measure_ne_top ν A)).1 h)
  · refine eventuallyEmptyOrUniv_iff.2 (Or.inl ?_)
    exact (measure_eq_zero_iff_ae_notMem.1
      ((measureReal_eq_zero_iff (measure_ne_top ν Aᶜ)).1 h)).mono fun x hx => not_not.1 hx

/-! ### Generic points of ergodic measures -/

lemma abs_integral_sub_le (ν : Measure X) [IsProbabilityMeasure ν] (f g : C(X, ℝ)) :
    |∫ y, f y ∂ν - ∫ y, g y ∂ν| ≤ ‖f - g‖ := by
  rw [← integral_sub (integrable_cont ν f) (integrable_cont ν g)]
  refine (abs_integral_le_integral_abs).trans ?_
  calc ∫ y, |f y - g y| ∂ν ≤ ∫ _y, ‖f - g‖ ∂ν :=
        integral_mono ((integrable_cont ν (f - g)).abs) (integrable_const _) fun y => by
          rw [← Real.norm_eq_abs]; exact (f - g).norm_coe_le_norm y
    _ = ‖f - g‖ := by simp

/-- For ergodic `ν`, `ν`-a.e. point is generic: `E = ν` holds `ν`-a.e. -/
theorem ae_E_eq_of_ergodic {S : X → X} {ν : ProbabilityMeasure X} (hν : Ergodic S ν) :
    ∀ᵐ y ∂(ν : Measure X), y ∈ G S ∧ E S y = ν := by
  obtain ⟨D, hD⟩ := TopologicalSpace.exists_dense_seq C(X, ℝ)
  have h := fun i => birkhoff_ergodic hν (integrable_cont (ν : Measure X) (D i))
  filter_upwards [ae_mem_G hν.toMeasurePreserving, ae_all_iff.2 h] with y hy hlim
  refine ⟨hy, ProbabilityMeasure.ext_integral fun f => ?_⟩
  have := (E S y).2
  -- both sides are continuous in `f` and agree on the dense sequence
  have hagree : ∀ i, ∫ z, D i z ∂(E S y : Measure X) = ∫ z, D i z ∂(ν : Measure X) := fun i => by
    rw [integral_E hy, hlim i]
  refine le_antisymm ?_ ?_ <;> refine le_of_forall_pos_le_add fun ε hε => ?_ <;>
    obtain ⟨i, hi⟩ := hD.exists_dist_lt f (by positivity : 0 < ε / 2) <;>
    rw [dist_eq_norm] at hi <;>
    have a1 := abs_integral_sub_le (E S y : Measure X) f (D i) <;>
    have a2 := abs_integral_sub_le (ν : Measure X) f (D i) <;>
    rw [hagree i] at a1 <;>
    linarith [abs_le.1 a1, abs_le.1 a2]

end ErgDecomp

end DF
