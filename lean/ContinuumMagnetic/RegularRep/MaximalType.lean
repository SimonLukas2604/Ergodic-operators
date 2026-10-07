/-
# Maximal spectral type from a Hilbert basis

If every vector `b i` of a Hilbert basis has the same spectral measure `ρ` (with respect to the
continuous functional calculus of `T`, `IsSpectralMeasureH`), then every spectral measure of `T`
is absolutely continuous with respect to `ρ`, i.e. `ρ` is a measure of maximal spectral type.

The proof uses only the continuous functional calculus:
* for real `g ∈ C_b(ℝ)`, `Re ⟪v, (g²)(T) v⟫ = ‖g(T) v‖²` (`cfc` is a `⋆`-homomorphism), and
  `‖g(T)‖ ≤ 1` whenever `|g| ≤ 1` (`norm_cfc_le`);
* for closed `C` with `ρ C = 0`, the thickened indicators `g_n ↓ 1_C` give
  `‖g_n(T) (b i)‖² = ∫ g_n² dρ → ρ C = 0`, hence (uniform bound + density of the span of the
  basis) `g_n(T) ψ → 0` for every `ψ`, and `μ C ≤ ∫ g_n² dμ = ‖g_n(T) ψ‖² → 0`;
* inner regularity of finite measures on `ℝ` by closed sets.

Main results:
* `CMS.IsSpectralMeasureH.absolutelyContinuous_of_hilbertBasis` (general Hilbert space);
* `CMS.maximalSpectralType` (same, with the self-adjointness hypothesis of the paper);
* `CMS.IsSpectralMeasure.absolutelyContinuous_of_delta` (on `ℓ²(ι)` with the basis `δ_i`).
-/
import ContinuumMagnetic.UnitaryTransfer

noncomputable section

open scoped ComplexConjugate InnerProductSpace ENNReal NNReal
open MeasureTheory Set Filter Topology BoundedContinuousFunction AMO

namespace CMS

set_option linter.unusedSectionVars false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The operator `g(T)` attached to a real bounded continuous function, via the complex cfc. -/
def realCFC (g : ℝ →ᵇ ℝ) (T : H →L[ℂ] H) : H →L[ℂ] H :=
  cfc (fun z : ℂ => ((g z.re : ℝ) : ℂ)) T

lemma continuous_realFun (g : ℝ →ᵇ ℝ) : Continuous (fun z : ℂ => ((g z.re : ℝ) : ℂ)) := by
  fun_prop

/-- `Re ⟪v, (g²)(T) v⟫ = ‖g(T) v‖²`. -/
lemma re_inner_cfc_mul_self (g : ℝ →ᵇ ℝ) (T : H →L[ℂ] H) (v : H) :
    RCLike.re ⟪v, cfc (fun z : ℂ => (((g * g) z.re : ℝ) : ℂ)) T v⟫_ℂ = ‖realCFC g T v‖ ^ 2 := by
  have hfun : (fun z : ℂ => (((g * g) z.re : ℝ) : ℂ)) =
      fun z => star ((g z.re : ℝ) : ℂ) * ((g z.re : ℝ) : ℂ) := by
    funext z; simp
  have hc := (continuous_realFun g).continuousOn (s := spectrum ℂ T)
  rw [hfun, cfc_mul (fun z : ℂ => star ((g z.re : ℝ) : ℂ)) (fun z : ℂ => ((g z.re : ℝ) : ℂ)) T
    (by simpa using hc) hc, cfc_star, ContinuousLinearMap.star_eq_adjoint,
    mul_apply_eq_comp, ContinuousLinearMap.adjoint_inner_right]
  rw [← realCFC]
  exact inner_self_eq_norm_sq _

lemma norm_realCFC_le (g : ℝ →ᵇ ℝ) (hg : ∀ t, |g t| ≤ 1) (T : H →L[ℂ] H) :
    ‖realCFC g T‖ ≤ 1 :=
  norm_cfc_le zero_le_one fun x _ => by simpa [Complex.norm_real] using hg x.re

/-- The real thickened indicator of `C` at radius `1/(n+1)`. -/
def thickInd (C : Set ℝ) (n : ℕ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun t => ((thickenedIndicator (Nat.one_div_pos_of_nat (n := n)) C t : ℝ≥0) : ℝ))
    (by fun_prop) 1
    (fun t => by
      simpa [Real.norm_eq_abs] using
        (thickenedIndicator_le_one (Nat.one_div_pos_of_nat (n := n)) C t))

lemma thickInd_apply (C : Set ℝ) (n : ℕ) (t : ℝ) :
    thickInd C n t = ((thickenedIndicator (Nat.one_div_pos_of_nat (n := n)) C t : ℝ≥0) : ℝ) :=
  rfl

lemma thickInd_nonneg (C : Set ℝ) (n : ℕ) (t : ℝ) : 0 ≤ thickInd C n t := by
  rw [thickInd_apply]; exact NNReal.coe_nonneg _

lemma thickInd_le_one (C : Set ℝ) (n : ℕ) (t : ℝ) : thickInd C n t ≤ 1 := by
  rw [thickInd_apply]
  exact_mod_cast thickenedIndicator_le_one (Nat.one_div_pos_of_nat (n := n)) C t

lemma thickInd_eq_one (C : Set ℝ) (n : ℕ) {t : ℝ} (ht : t ∈ C) : thickInd C n t = 1 := by
  rw [thickInd_apply, thickenedIndicator_one _ C ht]; rfl

/-- `ν(C) ≤ ∫ (thickInd C n)² dν`. -/
lemma measureReal_le_integral_sq (ν : Measure ℝ) [IsFiniteMeasure ν] {C : Set ℝ}
    (hC : IsClosed C) (n : ℕ) :
    ν.real C ≤ ∫ t, (thickInd C n * thickInd C n) t ∂ν := by
  rw [← integral_indicator_one hC.measurableSet]
  refine integral_mono ((integrable_const (1 : ℝ)).indicator hC.measurableSet)
    (BoundedContinuousFunction.integrable _ _) fun t => ?_
  by_cases ht : t ∈ C
  · simp [ht, thickInd_eq_one C n ht]
  · simp only [ht, not_false_eq_true, indicator_of_notMem, BoundedContinuousFunction.coe_mul,
      Pi.mul_apply]
    exact mul_self_nonneg _

/-- `∫ (thickInd C n)² dν → ν(C)`. -/
lemma tendsto_integral_sq (ν : Measure ℝ) [IsFiniteMeasure ν] {C : Set ℝ} (hC : IsClosed C) :
    Tendsto (fun n => ∫ t, (thickInd C n * thickInd C n) t ∂ν) atTop (𝓝 (ν.real C)) := by
  have h := tendsto_integral_thickenedIndicator_of_isClosed ν hC
    (fun n => Nat.one_div_pos_of_nat (n := n)) tendsto_one_div_add_atTop_nhds_zero_nat
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun n => measureReal_le_integral_sq ν hC n) fun n => ?_
  refine integral_mono (BoundedContinuousFunction.integrable _ _)
    (BoundedContinuousFunction.integrable _ (thickInd C n)) fun t => ?_
  simp only [BoundedContinuousFunction.coe_mul, Pi.mul_apply]
  have h0 := thickInd_nonneg C n t
  have h1 := thickInd_le_one C n t
  rw [← thickInd_apply]
  nlinarith


/-- The square of `‖g(T) v‖` is the integral of `g²` against the spectral measure of `v`. -/
lemma norm_realCFC_sq_eq_integral {T : H →L[ℂ] H} {v : H} {ν : Measure ℝ}
    (hν : IsSpectralMeasureH T v ν) (g : ℝ →ᵇ ℝ) :
    ‖realCFC g T v‖ ^ 2 = ∫ t, (g * g) t ∂ν := by
  rw [hν.2 (g * g), re_inner_cfc_mul_self]

variable {ι : Type*}

/-- Strong convergence `(thickInd C n)(T) v → 0` for every `v`, provided it holds on a Hilbert
basis (uses `‖(thickInd C n)(T)‖ ≤ 1`). -/
lemma tendsto_realCFC_thickInd_of_basis (T : H →L[ℂ] H) (C : Set ℝ) (b : HilbertBasis ι ℂ H)
    (hb : ∀ i, Tendsto (fun n => realCFC (thickInd C n) T (b i)) atTop (𝓝 0)) (v : H) :
    Tendsto (fun n => realCFC (thickInd C n) T v) atTop (𝓝 0) := by
  set A : ℕ → H →L[ℂ] H := fun n => realCFC (thickInd C n) T with hA
  have hA1 : ∀ n, ‖A n‖ ≤ 1 := fun n => norm_realCFC_le _ (fun t => by
    rw [abs_le]; exact ⟨by linarith [thickInd_nonneg C n t], thickInd_le_one C n t⟩) T
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hsum := b.hasSum_repr v
  obtain ⟨F, hF⟩ : ∃ F : Finset ι, dist (∑ i ∈ F, b.repr v i • b i) v < ε / 2 :=
    ((hsum.eventually (Metric.ball_mem_nhds v (by linarith : (0:ℝ) < ε / 2)))).exists
  set w := ∑ i ∈ F, b.repr v i • b i
  have hw : Tendsto (fun n => A n w) atTop (𝓝 0) := by
    have : Tendsto (fun n => ∑ i ∈ F, b.repr v i • A n (b i)) atTop
        (𝓝 (∑ i ∈ F, b.repr v i • (0 : H))) :=
      tendsto_finsetSum F fun i _ => (hb i).const_smul (b.repr v i)
    simpa [w, map_sum, map_smul] using this
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hw (ε / 2) (by linarith)
  refine ⟨N, fun n hn => ?_⟩
  have h1 := hN n hn
  rw [dist_zero_right] at h1 ⊢
  have h2 : ‖A n (v - w)‖ ≤ ‖v - w‖ := by
    calc ‖A n (v - w)‖ ≤ ‖A n‖ * ‖v - w‖ := (A n).le_opNorm _
      _ ≤ 1 * ‖v - w‖ := by gcongr; exact hA1 n
      _ = ‖v - w‖ := one_mul _
  have h3 : ‖v - w‖ < ε / 2 := by rw [← dist_eq_norm, dist_comm]; exact hF
  have : A n v = A n (v - w) + A n w := by rw [← map_add, sub_add_cancel]
  show ‖A n v‖ < ε
  rw [this]
  calc ‖A n (v - w) + A n w‖ ≤ ‖A n (v - w)‖ + ‖A n w‖ := norm_add_le _ _
    _ < ε := by linarith

/-- Core step: closed sets that are `ρ`-null are `μ`-null. -/
lemma measure_isClosed_eq_zero_of_basis {T : H →L[ℂ] H} (b : HilbertBasis ι ℂ H)
    {ρ : Measure ℝ} [IsFiniteMeasure ρ] (hρ : ∀ i, IsSpectralMeasureH T (b i) ρ)
    {ψ : H} {μ : Measure ℝ} (hμ : IsSpectralMeasureH T ψ μ) {C : Set ℝ} (hC : IsClosed C)
    (hρC : ρ C = 0) : μ C = 0 := by
  have := hμ.1
  -- squared norms against basis vectors tend to `ρ(C) = 0`
  have hb : ∀ i, Tendsto (fun n => realCFC (thickInd C n) T (b i)) atTop (𝓝 0) := by
    intro i
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h := tendsto_integral_sq ρ hC
    rw [measureReal_def, hρC, ENNReal.toReal_zero] at h
    simp_rw [← norm_realCFC_sq_eq_integral (hρ i)] at h
    have := h.sqrt
    simpa [Real.sqrt_sq (norm_nonneg _)] using this
  have hψ := tendsto_realCFC_thickInd_of_basis T C b hb ψ
  have hψ2 : Tendsto (fun n => ‖realCFC (thickInd C n) T ψ‖ ^ 2) atTop (𝓝 0) := by
    simpa using ((continuous_norm.tendsto (0 : H)).comp hψ).pow 2
  have hle : μ.real C ≤ 0 := by
    refine ge_of_tendsto' hψ2 fun n => ?_
    rw [norm_realCFC_sq_eq_integral hμ]
    exact measureReal_le_integral_sq μ hC n
  have : μ.real C = 0 := le_antisymm hle measureReal_nonneg
  exact (measureReal_eq_zero_iff (measure_ne_top μ C)).1 this

/-- **Maximal spectral type lemma.**  If every vector of a Hilbert basis `b` has spectral
measure `ρ` (w.r.t. the continuous functional calculus of `T`), then every spectral measure of
`T` is absolutely continuous with respect to `ρ`.  No self-adjointness is needed: for
non-normal `T` the cfc is `0` and all spectral measures vanish. -/
theorem IsSpectralMeasureH.absolutelyContinuous_of_hilbertBasis {T : H →L[ℂ] H}
    (b : HilbertBasis ι ℂ H) {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    (hρ : ∀ i, IsSpectralMeasureH T (b i) ρ) {ψ : H} {μ : Measure ℝ}
    (hμ : IsSpectralMeasureH T ψ μ) : μ ≪ ρ := by
  have := hμ.1
  refine Measure.AbsolutelyContinuous.mk fun B hB hρB => ?_
  rw [hB.measure_eq_iSup_isClosed_of_ne_top (measure_ne_top μ B)]
  refine le_antisymm (iSup_le fun K => iSup_le fun hKB => iSup_le fun hK => ?_) bot_le
  exact (measure_isClosed_eq_zero_of_basis b hρ hμ hK
    (measure_mono_null hKB hρB)).le

/-- Self-adjoint form of the maximal spectral type lemma, as stated in the paper. -/
theorem maximalSpectralType {T : H →L[ℂ] H} (_hT : IsSelfAdjoint T)
    (b : HilbertBasis ι ℂ H) {ρ : Measure ℝ} [IsFiniteMeasure ρ]
    (hρ : ∀ i, IsSpectralMeasureH T (b i) ρ) (ψ : H) (μ : Measure ℝ)
    (hμ : IsSpectralMeasureH T ψ μ) : μ ≪ ρ :=
  hμ.absolutelyContinuous_of_hilbertBasis b hρ

/-- The standard Hilbert basis `(δ_i)` of `ℓ²(ι)`. -/
def stdBasis (ι : Type*) : HilbertBasis ι ℂ (L2 ι) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ (L2 ι))

lemma stdBasis_apply [DecidableEq ι] (i : ι) : stdBasis ι i = AMO.delta i := by
  rw [← (stdBasis ι).repr_symm_single]; rfl

/-- **Maximal spectral type on `ℓ²(ι)`.**  If every `δ_i` has spectral measure `ρ` then every
spectral measure of `T` is absolutely continuous w.r.t. `ρ`. -/
theorem IsSpectralMeasure.absolutelyContinuous_of_delta [DecidableEq ι] {T : Op ι}
    {ρ : Measure ℝ} [IsFiniteMeasure ρ] (hρ : ∀ i, IsSpectralMeasure T (AMO.delta i) ρ)
    {ψ : L2 ι} {μ : Measure ℝ} (hμ : IsSpectralMeasure T ψ μ) : μ ≪ ρ := by
  refine IsSpectralMeasureH.absolutelyContinuous_of_hilbertBasis (stdBasis ι) (fun i => ?_)
    ((isSpectralMeasureH_iff T ψ μ).2 hμ)
  rw [stdBasis_apply, isSpectralMeasureH_iff]
  exact hρ i

end CMS
