/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Appendix A.3, preliminaries: cutoffs, harmonic functions as distributions, uniqueness

* `DF.Distr.exists_cutoff` — smooth cutoff functions `0 ≤ χ ≤ 1`, equal to `1` near a compact set
  `K` and supported in a given open neighbourhood of `K`;
* `DF.Distr.integral_mul_laplacian_symm` — Green's second identity for compactly supported `C²`
  functions;
* `DF.Distr.integral_harmonic_mul_laplacian` — `∫ H Δψ = 0` for `H` harmonic near the support
  of the test function `ψ`;
* `DF.Distr.measure_eq_of_integral_eq` — finite measures carried by an open set `V` are
  determined by their integrals against compactly supported `C²` functions supported in `V`.
-/
import DamanikFillman.AppA.LaplacianNonneg
import Mathlib.Geometry.Manifold.PartitionOfUnity

noncomputable section

open Real Complex Metric Set Filter Topology MeasureTheory Laplacian InnerProductSpace

namespace DF

namespace Distr

/-! ### Smooth cutoffs -/

/-- Smooth cutoff functions. -/
theorem exists_cutoff {K V : Set ℂ} (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ 2 χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ V ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ ∃ δ > 0, ∀ x ∈ cthickening δ K, χ x = 1 := by
  obtain ⟨δ₀, hδ₀, hδ₀V⟩ := hK.exists_cthickening_subset_open hV hKV
  set δ := δ₀ / 3 with hδ
  have hδpos : 0 < δ := by positivity
  have hdisj : Disjoint (thickening (2 * δ) K)ᶜ (cthickening δ K) := by
    rw [disjoint_compl_left_iff_subset]
    exact cthickening_subset_thickening' (by positivity) (by linarith) K
  obtain ⟨f, hf, hfr, hf0, hf1⟩ := exists_contDiff_zero_iff_one_iff_of_isClosed (n := 2)
    isOpen_thickening.isClosed_compl isClosed_cthickening hdisj
  have hsupp : Function.support f ⊆ thickening (2 * δ) K := fun x hx => by
    by_contra h
    exact hx ((hf0 x).1 h)
  have htsupp : tsupport f ⊆ cthickening (2 * δ) K :=
    (closure_mono hsupp).trans (closure_thickening_subset_cthickening _ _)
  have h2δ : cthickening (2 * δ) K ⊆ V :=
    (cthickening_mono (by linarith) K).trans hδ₀V
  refine ⟨f, by exact_mod_cast hf, ?_, htsupp.trans h2δ, fun x => ?_, δ, hδpos,
    fun x hx => (hf1 x).1 hx⟩
  · exact (hK.cthickening : IsCompact (cthickening (2 * δ) K)).of_isClosed_subset
      (isClosed_tsupport f) htsupp
  · have := hfr (Set.mem_range_self x)
    exact ⟨this.1, this.2⟩

/-! ### Green's second identity -/

/-- **Green's second identity** for compactly supported `C²` functions. -/
theorem integral_mul_laplacian_symm {L ψ : ℂ → ℝ} (hL : ContDiff ℝ 2 L) (hLc : HasCompactSupport L)
    (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
    ∫ z, L z * Δ ψ z = ∫ z, Δ L z * ψ z := by
  rw [integral_mul_laplacian (hL.of_le (by norm_num)) hψ hψc]
  have h2 := integral_mul_laplacian (hψ.of_le (by norm_num)) hL hLc
  have e : (fun z => Δ L z * ψ z) = fun z => ψ z * Δ L z := funext fun z => mul_comm _ _
  rw [e, h2]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  ring

/-! ### Harmonic functions as distributions -/

lemma contDiff_cutoff_mul {χ H : ℂ → ℝ} {V : Set ℂ} (hχ : ContDiff ℝ 2 χ)
    (hχV : tsupport χ ⊆ V) (hH : HarmonicOnNhd H V) : ContDiff ℝ 2 (fun z => χ z * H z) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ V
  · exact hχ.contDiffAt.mul (hH x hx).1
  · have hx' : x ∉ tsupport χ := fun h => hx (hχV h)
    have hev : (fun z => χ z * H z) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx'] with z hz
      simp [hz]
    exact contDiffAt_const.congr_of_eventuallyEq hev

/-- `∫ H Δψ = 0` for `H` harmonic on an open set containing the support of `ψ`. -/
theorem integral_harmonic_mul_laplacian {H : ℂ → ℝ} {V : Set ℂ} (hV : IsOpen V)
    (hH : HarmonicOnNhd H V) {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ)
    (hψV : tsupport ψ ⊆ V) : ∫ z, H z * Δ ψ z = 0 := by
  obtain ⟨χ, hχ, hχc, hχV, -, δ, hδ, hχ1⟩ := exists_cutoff hψc.isCompact hV hψV
  set L : ℂ → ℝ := fun z => χ z * H z with hLdef
  have hL : ContDiff ℝ 2 L := contDiff_cutoff_mul hχ hχV hH
  have hLc : HasCompactSupport L := hχc.mul_right
  have h1 : ∫ z, H z * Δ ψ z = ∫ z, L z * Δ ψ z := by
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    by_cases hz : z ∈ tsupport ψ
    · simp only [hLdef, hχ1 z (self_subset_cthickening _ hz), one_mul]
    · simp only [laplacian_eq_zero_of_notMem hψ hz, mul_zero]
  rw [h1, integral_mul_laplacian_symm hL hLc hψ hψc]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ tsupport ψ
  · have hev : L =ᶠ[𝓝 z] H := by
      filter_upwards [ball_mem_nhds z hδ] with w hw
      have : w ∈ cthickening δ (tsupport ψ) :=
        mem_cthickening_of_dist_le w z δ _ hz (mem_ball.1 hw).le
      simp only [hLdef, hχ1 w this, one_mul]
    have hΔ : Δ L z = 0 := by
      rw [laplacian_congr_nhds hev]
      exact (hH z (hψV hz)).2.self_of_nhds
    simp [hΔ]
  · simp [image_eq_zero_of_notMem_tsupport hz]

/-! ### Uniqueness of measures -/

lemma measure_le_of_integral_eq {μ ν : Measure ℂ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {V : Set ℂ} (hV : IsOpen V) (hμV : μ Vᶜ = 0)
    (h : ∀ ψ : ℂ → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ → tsupport ψ ⊆ V →
      ∫ z, ψ z ∂μ = ∫ z, ψ z ∂ν) {O : Set ℂ} (hO : IsOpen O) : μ O ≤ ν O := by
  have h1 : μ O ≤ μ (O ∩ V) := by
    calc μ O ≤ μ (O ∩ V) + μ (O \ V) := measure_le_inter_add_sdiff μ O V
      _ = μ (O ∩ V) := by
        rw [measure_mono_null (fun x hx => hx.2) hμV, add_zero]
  refine h1.trans ?_
  rw [(hO.inter hV).measure_eq_iSup_isCompact μ]
  refine iSup₂_le fun K hK => iSup_le fun hKc => ?_
  obtain ⟨χ, hχ, hχc, hχV, hχ01, δ, hδ, hχ1⟩ := exists_cutoff hKc (hO.inter hV) hK
  have hχi : ∀ ρ : Measure ℂ, [IsFiniteMeasure ρ] → Integrable χ ρ := fun ρ _ =>
    hχ.continuous.integrable_of_hasCompactSupport hχc
  have hK1 : μ K ≤ ENNReal.ofReal (∫ z, χ z ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal (hχi μ) (Eventually.of_forall fun z => (hχ01 z).1),
      ← lintegral_indicator_one hKc.measurableSet]
    refine lintegral_mono fun z => ?_
    by_cases hz : z ∈ K
    · simp [hz, hχ1 z (self_subset_cthickening _ hz)]
    · simp [hz]
  have hK2 : ENNReal.ofReal (∫ z, χ z ∂ν) ≤ ν O := by
    rw [ofReal_integral_eq_lintegral_ofReal (hχi ν) (Eventually.of_forall fun z => (hχ01 z).1)]
    calc ∫⁻ z, ENNReal.ofReal (χ z) ∂ν ≤ ∫⁻ z, O.indicator 1 z ∂ν := by
          refine lintegral_mono fun z => ?_
          by_cases hz : z ∈ O
          · simp only [indicator_of_mem hz, Pi.one_apply]
            exact ENNReal.ofReal_le_one.2 (hχ01 z).2
          · have : z ∉ tsupport χ := fun h' => hz (hχV h').1
            simp [indicator_of_notMem hz, image_eq_zero_of_notMem_tsupport this]
      _ = ν O := lintegral_indicator_one hO.measurableSet
  calc μ K ≤ ENNReal.ofReal (∫ z, χ z ∂μ) := hK1
    _ = ENNReal.ofReal (∫ z, χ z ∂ν) := by rw [h χ hχ hχc ((hχV).trans inter_subset_right)]
    _ ≤ ν O := hK2

/-- Finite measures carried by an open set `V` are determined by their integrals against
compactly supported `C²` functions supported in `V`. -/
theorem measure_eq_of_integral_eq {μ ν : Measure ℂ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {V : Set ℂ} (hV : IsOpen V) (hμV : μ Vᶜ = 0) (hνV : ν Vᶜ = 0)
    (h : ∀ ψ : ℂ → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ → tsupport ψ ⊆ V →
      ∫ z, ψ z ∂μ = ∫ z, ψ z ∂ν) : μ = ν :=
  Measure.OuterRegular.ext_isOpen fun O hO =>
    le_antisymm (measure_le_of_integral_eq hV hμV h hO)
      (measure_le_of_integral_eq hV hνV (fun ψ h1 h2 h3 => (h ψ h1 h2 h3).symm) hO)

end Distr

end DF
