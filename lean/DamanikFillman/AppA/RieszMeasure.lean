/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Appendix A.3: the Riesz measure of a subharmonic function

For a (real-valued) subharmonic function `u` on an open set `U` and a compact set `C ⊆ U`, we
construct a measure `ν`, finite on compacts, with

  `∫ ψ dν = (2π)⁻¹ ∫ u Δψ`

for all compactly supported `C²` functions `ψ` with `tsupport ψ ⊆ C`
(`DF.Distr.exists_rieszMeasure`).

Construction: fix a cutoff `χ` supported in `U` with `χ = 1` near `C`.  The positive functional
`T ψ = (2π)⁻¹ ∫ u Δψ` (`integral_mul_laplacian_nonneg`) satisfies `|T(χ g)| ≤ ‖g‖_∞ T(χ)`;
hence `Λ f = lim T(χ (moll_{r_n} ⋆ f))` exists for `f ∈ C_c(ℂ)`, is linear and positive, and
the Riesz–Markov–Kakutani theorem (`RealRMK.rieszMeasure`) produces `ν`.
-/
import DamanikFillman.AppA.RieszAux
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

noncomputable section

open Real Complex Metric Set Filter Topology MeasureTheory Laplacian InnerProductSpace
open scoped Convolution CompactlySupported

namespace DF

namespace Distr

/-! ### Integrability helpers -/

lemma integrable_mul_of_integrableOn {u g : ℂ → ℝ} {K : Set ℂ} (hK : IsCompact K)
    (hu : IntegrableOn u K) (hg : Continuous g) (hgs : ∀ x, x ∉ K → g x = 0) :
    Integrable (fun x => u x * g x) := by
  have h := hu.mul_continuousOn hg.continuousOn hK
  refine (integrableOn_iff_integrable_of_support_subset ?_).1 h
  intro x hx
  by_contra h'
  exact hx (by simp [hgs x h'])

/-- Supports of functions vanishing where `χ` vanishes. -/
lemma tsupport_subset_of {F χ : ℂ → ℝ} (h : ∀ x, χ x = 0 → F x = 0) :
    tsupport F ⊆ tsupport χ :=
  closure_minimal (fun x hx => subset_tsupport χ fun h0 => hx (h x h0)) isClosed_tsupport

/-! ### The functional `ψ ↦ ∫ u Δψ` -/

/-- `T ψ = ∫ u Δψ`. -/
def Tfun (u ψ : ℂ → ℝ) : ℝ := ∫ z, u z * Δ ψ z

lemma integrable_u_laplacian {u ψ : ℂ → ℝ} {K : Set ℂ} (hK : IsCompact K) (hu : IntegrableOn u K)
    (hψ : ContDiff ℝ 2 ψ) (hψK : tsupport ψ ⊆ K) : Integrable (fun z => u z * Δ ψ z) :=
  integrable_mul_of_integrableOn hK hu (continuous_laplacian hψ) fun x hx =>
    laplacian_eq_zero_of_notMem hψ fun h => hx (hψK h)

lemma Tfun_add {u ψ₁ ψ₂ : ℂ → ℝ} {K : Set ℂ} (hK : IsCompact K) (hu : IntegrableOn u K)
    (h₁ : ContDiff ℝ 2 ψ₁) (h₂ : ContDiff ℝ 2 ψ₂) (h₁K : tsupport ψ₁ ⊆ K)
    (h₂K : tsupport ψ₂ ⊆ K) : Tfun u (ψ₁ + ψ₂) = Tfun u ψ₁ + Tfun u ψ₂ := by
  unfold Tfun
  rw [← integral_add (integrable_u_laplacian hK hu h₁ h₁K) (integrable_u_laplacian hK hu h₂ h₂K)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [h₁.contDiffAt.laplacian_add h₂.contDiffAt]
  ring

lemma Tfun_smul {u ψ : ℂ → ℝ} (c : ℝ) (hψ : ContDiff ℝ 2 ψ) :
    Tfun u (c • ψ) = c * Tfun u ψ := by
  unfold Tfun
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [laplacian_smul c hψ.contDiffAt, smul_eq_mul]
  ring

lemma Tfun_sub {u ψ₁ ψ₂ : ℂ → ℝ} {K : Set ℂ} (hK : IsCompact K) (hu : IntegrableOn u K)
    (h₁ : ContDiff ℝ 2 ψ₁) (h₂ : ContDiff ℝ 2 ψ₂) (h₁K : tsupport ψ₁ ⊆ K)
    (h₂K : tsupport ψ₂ ⊆ K) : Tfun u (ψ₁ - ψ₂) = Tfun u ψ₁ - Tfun u ψ₂ := by
  unfold Tfun
  rw [← integral_sub (integrable_u_laplacian hK hu h₁ h₁K) (integrable_u_laplacian hK hu h₂ h₂K)]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [h₁.contDiffAt.laplacian_sub h₂.contDiffAt]
  ring

/-- The key bound `|T(χ g)| ≤ ‖g‖_∞ T(χ)`. -/
theorem abs_Tfun_mul_le {u : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hu : SubharmonicOn (fun z => (u z : EReal)) U) {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U) (hχ0 : ∀ x, 0 ≤ χ x)
    {g : ℂ → ℝ} (hg : ContDiff ℝ 2 g) {B : ℝ} (hB : ∀ x, |g x| ≤ B) :
    |Tfun u (χ * g)| ≤ B * Tfun u χ := by
  have hK := hχc.isCompact
  have huK : IntegrableOn u (tsupport χ) := integrableOn_of_subharmonic hU hu hK hχU
  have hχg : ContDiff ℝ 2 (χ * g) := hχ.mul hg
  have hBχ : ContDiff ℝ 2 (B • χ) := hχ.const_smul B
  have hs1 : tsupport (χ * g) ⊆ tsupport χ := tsupport_subset_of fun x h0 => by simp [h0]
  have hs2 : tsupport (B • χ) ⊆ tsupport χ := tsupport_subset_of fun x h0 => by simp [h0]
  -- the two nonnegative test functions
  have hpos : ∀ s : ℝ, s = 1 ∨ s = -1 → 0 ≤ Tfun u (B • χ - s • (χ * g)) := by
    intro s hs
    have hsg : ContDiff ℝ 2 (s • (χ * g)) := hχg.const_smul s
    have hs4 : tsupport (B • χ - s • (χ * g)) ⊆ tsupport χ :=
      tsupport_subset_of fun x h0 => by simp [h0]
    refine integral_mul_laplacian_nonneg hU hu (hBχ.sub hsg) ?_ (hs4.trans hχU) ?_
    · exact hχc.of_isClosed_subset isClosed_tsupport hs4
    · intro x
      simp only [Pi.sub_apply, Pi.smul_apply, Pi.mul_apply, smul_eq_mul]
      have hgx := hB x
      rcases hs with rfl | rfl
      · have := (abs_le.1 hgx).2
        nlinarith [hχ0 x]
      · have := (abs_le.1 hgx).1
        nlinarith [hχ0 x]
  have hexp : ∀ s : ℝ, Tfun u (B • χ - s • (χ * g)) = B * Tfun u χ - s * Tfun u (χ * g) := by
    intro s
    rw [Tfun_sub hK huK hBχ (hχg.const_smul s) hs2
      (tsupport_subset_of fun x h0 => by simp [h0]),
      Tfun_smul B hχ, Tfun_smul s hχg]
  have h1 := hpos 1 (Or.inl rfl)
  have h2 := hpos (-1) (Or.inr rfl)
  rw [hexp] at h1 h2
  rw [abs_le]
  constructor <;> linarith

/-! ### Smoothing of continuous functions -/

/-- `S_r f = moll_r ⋆ f`. -/
def smoothen (r : ℝ) (f : ℂ → ℝ) : ℂ → ℝ := moll r ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f

lemma contDiff_smoothen {r : ℝ} (hr : 0 < r) {f : ℂ → ℝ} (hf : Continuous f) :
    ContDiff ℝ 2 (smoothen r f) := by
  have hm : ContDiff ℝ ((2 : ℕ∞) : WithTop ℕ∞) (moll r) := by exact_mod_cast contDiff_moll r
  have := (hasCompactSupport_moll hr).contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) hm hf.locallyIntegrable
  exact_mod_cast this

lemma hasCompactSupport_smoothen {r : ℝ} (hr : 0 < r) {f : ℂ → ℝ} (hfc : HasCompactSupport f) :
    HasCompactSupport (smoothen r f) :=
  (hasCompactSupport_moll hr).convolution _ hfc

lemma support_moll_subset {r : ℝ} (hr : 0 < r) : Function.support (moll r) ⊆ ball 0 r := by
  intro y hy
  rw [mem_ball, dist_zero_right]
  by_contra h
  exact hy (moll_eq_zero hr (not_lt.1 h))

lemma integrable_moll {r : ℝ} (hr : 0 < r) : Integrable (moll r) :=
  (continuous_moll r).integrable_of_hasCompactSupport (hasCompactSupport_moll hr)

lemma dist_smoothen_le {r : ℝ} (hr : 0 < r) {f : ℂ → ℝ} (hf : Continuous f) {x : ℂ} {ε : ℝ}
    (hε : 0 ≤ ε) (h : ∀ y ∈ ball x r, dist (f y) (f x) ≤ ε) : dist (smoothen r f x) (f x) ≤ ε :=
  dist_convolution_le hε (support_moll_subset hr) (fun y => moll_nonneg y) (integral_moll hr)
    hf.aestronglyMeasurable h

lemma smoothen_nonneg {r : ℝ} {f : ℂ → ℝ} (hf : ∀ x, 0 ≤ f x) (x : ℂ) :
    0 ≤ smoothen r f x := by
  unfold smoothen
  rw [convolution_lsmul]
  exact integral_nonneg fun t => smul_nonneg (moll_nonneg t) (hf _)

lemma smoothen_add {r : ℝ} (hr : 0 < r) {f g : ℂ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    smoothen r (f + g) = smoothen r f + smoothen r g := by
  unfold smoothen
  exact ConvolutionExists.distrib_add
    ((hasCompactSupport_moll hr).convolutionExists_left _ (continuous_moll r)
      hf.locallyIntegrable)
    ((hasCompactSupport_moll hr).convolutionExists_left _ (continuous_moll r)
      hg.locallyIntegrable)

lemma smoothen_smul (r c : ℝ) (f : ℂ → ℝ) : smoothen r (c • f) = c • smoothen r f := by
  unfold smoothen
  exact convolution_smul

/-- Uniform approximation by smoothing. -/
lemma tendsto_smoothen_uniform {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ r, 0 < r → r < δ → ∀ x, |smoothen r f x - f x| ≤ ε := by
  obtain ⟨δ, hδ, hδu⟩ := Metric.uniformContinuous_iff.1
    (hfc.uniformContinuous_of_continuous hf) ε hε
  refine ⟨δ, hδ, fun r hr hrδ x => ?_⟩
  rw [← Real.dist_eq]
  refine dist_smoothen_le hr hf hε.le fun y hy => (hδu ?_).le
  rw [mem_ball] at hy
  linarith

/-! ### The approximating sequence -/

/-- The radii `r_n = 1/(n+1)`. -/
def rr (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

lemma rr_pos (n : ℕ) : 0 < rr n := by unfold rr; positivity

lemma tendsto_rr : Tendsto rr atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

/-- The sequence `a_n(f) = (2π)⁻¹ T(χ S_{r_n} f)`. -/
def aSeq (u χ f : ℂ → ℝ) (n : ℕ) : ℝ := (2 * π)⁻¹ * Tfun u (χ * smoothen (rr n) f)

/-- The limit functional. -/
def Λfun (u χ f : ℂ → ℝ) : ℝ := limUnder atTop (aSeq u χ f)

section Construction

variable {u : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U) (hu : SubharmonicOn (fun z => (u z : EReal)) U)
  {χ : ℂ → ℝ} (hχ : ContDiff ℝ 2 χ) (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U)
  (hχ0 : ∀ x, 0 ≤ χ x)

include hU hu hχ hχc hχU hχ0

lemma aSeq_cauchy {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    CauchySeq (aSeq u χ f) := by
  rw [Metric.cauchySeq_iff']
  intro ε hε
  set Tχ := Tfun u χ with hTχ
  have hTχ0 : 0 ≤ Tχ := integral_mul_laplacian_nonneg hU hu hχ hχc hχU hχ0
  set η := ε / (4 * (|(2 * π)⁻¹| * Tχ + 1)) with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨δ, hδ, hδu⟩ := tendsto_smoothen_uniform hf hfc hηpos
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / δ)
  refine ⟨N, fun n hn => ?_⟩
  have hrn : ∀ m, N ≤ m → rr m < δ := by
    intro m hm
    unfold rr
    rw [div_lt_iff₀ (by positivity)]
    have : (N : ℝ) ≤ m := by exact_mod_cast hm
    rw [div_lt_iff₀ hδ] at hN
    nlinarith
  have hK := hχc.isCompact
  have huK : IntegrableOn u (tsupport χ) := integrableOn_of_subharmonic hU hu hK hχU
  have hgn := contDiff_smoothen (rr_pos n) hf
  have hgN := contDiff_smoothen (rr_pos N) hf
  have hsub : χ * smoothen (rr n) f - χ * smoothen (rr N) f =
      χ * (smoothen (rr n) f - smoothen (rr N) f) := by ring
  have hdiff : aSeq u χ f n - aSeq u χ f N =
      (2 * π)⁻¹ * Tfun u (χ * (smoothen (rr n) f - smoothen (rr N) f)) := by
    unfold aSeq
    rw [← mul_sub, ← Tfun_sub hK huK (hχ.mul hgn) (hχ.mul hgN) (tsupport_subset_of fun x h0 => by simp [h0])
      (tsupport_subset_of fun x h0 => by simp [h0]), hsub]
  have hbd := abs_Tfun_mul_le hU hu hχ hχc hχU hχ0 (hgn.sub hgN) (B := 2 * η) fun x => by
    have h1 := hδu (rr n) (rr_pos n) (hrn n hn) x
    have h2 := hδu (rr N) (rr_pos N) (hrn N le_rfl) x
    simp only [Pi.sub_apply]
    calc |smoothen (rr n) f x - smoothen (rr N) f x|
        = |(smoothen (rr n) f x - f x) - (smoothen (rr N) f x - f x)| := by congr 1; ring
      _ ≤ |smoothen (rr n) f x - f x| + |smoothen (rr N) f x - f x| := abs_sub _ _
      _ ≤ 2 * η := by linarith
  rw [Real.dist_eq, hdiff, abs_mul]
  calc |(2 * π)⁻¹| * |Tfun u (χ * (smoothen (rr n) f - smoothen (rr N) f))|
      ≤ |(2 * π)⁻¹| * (2 * η * Tχ) := mul_le_mul_of_nonneg_left hbd (abs_nonneg _)
    _ = 2 * η * (|(2 * π)⁻¹| * Tχ) := by ring
    _ < ε := by
        have h4 : 2 * η * (|(2 * π)⁻¹| * Tχ) ≤ 2 * η * (|(2 * π)⁻¹| * Tχ + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        have h5 : 2 * η * (|(2 * π)⁻¹| * Tχ + 1) = ε / 2 := by
          have : |(2 * π)⁻¹| * Tχ + 1 ≠ 0 := by positivity
          rw [hη]; field_simp; ring
        linarith

lemma aSeq_add {f g : ℂ → ℝ} (hf : Continuous f) (hg : Continuous g) (n : ℕ) :
    aSeq u χ (f + g) n = aSeq u χ f n + aSeq u χ g n := by
  unfold aSeq
  have hK := hχc.isCompact
  have huK : IntegrableOn u (tsupport χ) := integrableOn_of_subharmonic hU hu hK hχU
  rw [smoothen_add (rr_pos n) hf hg, mul_add,
    Tfun_add hK huK (hχ.mul (contDiff_smoothen (rr_pos n) hf))
      (hχ.mul (contDiff_smoothen (rr_pos n) hg)) (tsupport_subset_of fun x h0 => by simp [h0])
      (tsupport_subset_of fun x h0 => by simp [h0])]
  ring

lemma aSeq_smul (c : ℝ) {f : ℂ → ℝ} (hf : Continuous f) (n : ℕ) :
    aSeq u χ (c • f) n = c * aSeq u χ f n := by
  unfold aSeq
  rw [smoothen_smul, mul_smul_comm, Tfun_smul c (hχ.mul (contDiff_smoothen (rr_pos n) hf))]
  ring

lemma aSeq_nonneg {f : ℂ → ℝ} (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) (n : ℕ) :
    0 ≤ aSeq u χ f n := by
  unfold aSeq
  refine mul_nonneg (by positivity) ?_
  refine integral_mul_laplacian_nonneg hU hu (hχ.mul (contDiff_smoothen (rr_pos n) hf))
    hχc.mul_right ((tsupport_subset_of fun x h0 => by simp [h0]).trans hχU) fun x => ?_
  exact mul_nonneg (hχ0 x) (smoothen_nonneg hf0 x)

lemma tendsto_aSeq {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (aSeq u χ f) atTop (𝓝 (Λfun u χ f)) :=
  (aSeq_cauchy hU hu hχ hχc hχU hχ0 hf hfc).tendsto_limUnder

/-- The positive linear functional on `C_c(ℂ, ℝ)`. -/
def Λpos : C_c(ℂ, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀
    { toFun := fun f => Λfun u χ f
      map_add' := fun f g => by
        have h := (tendsto_aSeq hU hu hχ hχc hχU hχ0 (f + g).continuous
          (f + g).hasCompactSupport)
        have h' := (tendsto_aSeq hU hu hχ hχc hχU hχ0 f.continuous f.hasCompactSupport).add
          (tendsto_aSeq hU hu hχ hχc hχU hχ0 g.continuous g.hasCompactSupport)
        refine tendsto_nhds_unique h (h'.congr fun n => ?_)
        simp only [CompactlySupportedContinuousMap.coe_add]
        exact (aSeq_add hU hu hχ hχc hχU hχ0 f.continuous g.continuous n).symm
      map_smul' := fun c f => by
        have h := (tendsto_aSeq hU hu hχ hχc hχU hχ0 (c • f).continuous
          (c • f).hasCompactSupport)
        have h' := (tendsto_aSeq hU hu hχ hχc hχU hχ0 f.continuous
          f.hasCompactSupport).const_mul c
        simp only [RingHom.id_apply, smul_eq_mul]
        refine tendsto_nhds_unique h (h'.congr fun n => ?_)
        simp only [CompactlySupportedContinuousMap.coe_smul]
        exact (aSeq_smul hU hu hχ hχc hχU hχ0 c f.continuous n).symm }
    (fun f hf => by
      have h := tendsto_aSeq hU hu hχ hχc hχU hχ0 f.continuous f.hasCompactSupport
      refine ge_of_tendsto' h fun n => aSeq_nonneg hU hu hχ hχc hχU hχ0 f.continuous
        (fun x => by simpa using CompactlySupportedContinuousMap.le_def.1 hf x) n)

end Construction

/-! ### The Riesz measure -/

/-- **Existence of the Riesz measure.** -/
theorem exists_rieszMeasure {u : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hu : SubharmonicOn (fun z => (u z : EReal)) U) {C : Set ℂ} (hC : IsCompact C)
    (hCU : C ⊆ U) :
    ∃ ν : Measure ℂ, IsFiniteMeasureOnCompacts ν ∧
      ∀ ψ : ℂ → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ → tsupport ψ ⊆ C →
        ∫ z, ψ z ∂ν = (2 * π)⁻¹ * ∫ z, u z * Δ ψ z := by
  obtain ⟨χ, hχ, hχc, hχU, hχ01, δ, hδ, hχ1⟩ := exists_cutoff hC hU hCU
  have hχ0 : ∀ x, 0 ≤ χ x := fun x => (hχ01 x).1
  set Λ := Λpos hU hu hχ hχc hχU hχ0 with hΛ
  refine ⟨RealRMK.rieszMeasure Λ, inferInstance, fun ψ hψ hψc hψC => ?_⟩
  set ψc : C_c(ℂ, ℝ) := ⟨⟨ψ, hψ.continuous⟩, hψc⟩ with hψcdef
  have h1 : ∫ z, ψ z ∂(RealRMK.rieszMeasure Λ) = Λ ψc := RealRMK.integral_rieszMeasure Λ ψc
  rw [h1]
  show Λfun u χ ψ = _
  -- `a_n(ψ) → (2π)⁻¹ ∫ u Δψ`
  have hlim := tendsto_aSeq hU hu hχ hχc hχU hχ0 hψ.continuous hψc
  refine tendsto_nhds_unique hlim ?_
  set K₁ := cthickening δ C with hK₁
  have hK₁c : IsCompact K₁ := hC.cthickening
  have hK₁U : K₁ ⊆ U := fun x hx => hχU (subset_tsupport χ (by
    rw [Function.mem_support, hχ1 x hx]; exact one_ne_zero))
  have huK₁ : IntegrableOn u K₁ := integrableOn_of_subharmonic hU hu hK₁c hK₁U
  -- for small `r`, `χ S_r ψ = S_r ψ`
  have hsupp : ∀ r, 0 < r → r < δ → tsupport (smoothen r ψ) ⊆ K₁ := by
    intro r hr hrδ
    refine closure_minimal (fun x hx => ?_) isClosed_cthickening
    by_contra hxK
    apply hx
    unfold smoothen
    rw [convolution_lsmul]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
    show moll r t • ψ (x - t) = 0
    by_cases ht : ‖t‖ < r
    · have : x - t ∉ tsupport ψ := fun h => hxK (mem_cthickening_of_dist_le x (x - t) δ C
        (hψC h) (by rw [dist_eq_norm, sub_sub_cancel]; linarith))
      rw [image_eq_zero_of_notMem_tsupport this, smul_zero]
    · rw [moll_eq_zero hr (not_lt.1 ht), zero_smul]
  have hΔS : ∀ r, 0 < r → Δ (smoothen r ψ) = smoothen r (Δ ψ) := fun r hr => by
    funext x
    exact laplacian_conv (integrable_moll hr).locallyIntegrable hψ hψc x
  -- the integrals converge
  have hΔc := continuous_laplacian hψ
  have hΔs : HasCompactSupport (Δ ψ) :=
    HasCompactSupport.intro hψc.isCompact fun z hz => laplacian_eq_zero_of_notMem hψ hz
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  set A := ∫ x in K₁, |u x| with hA
  have hA0 : 0 ≤ A := setIntegral_nonneg hK₁c.measurableSet fun _ _ => abs_nonneg _
  set η := ε / (2 * ((2 * π)⁻¹ * A + 1)) with hη
  have hηpos : 0 < η := by positivity
  obtain ⟨δ', hδ', hδ'u⟩ := tendsto_smoothen_uniform hΔc hΔs hηpos
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / min δ δ')
  refine ⟨N, fun n hn => ?_⟩
  have hrn : rr n < min δ δ' := by
    unfold rr
    have hm : 0 < min δ δ' := lt_min hδ hδ'
    rw [div_lt_iff₀ (by positivity)]
    have : (N : ℝ) ≤ n := by exact_mod_cast hn
    rw [div_lt_iff₀ hm] at hN
    nlinarith
  have hr0 := rr_pos n
  have hrδ : rr n < δ := hrn.trans_le (min_le_left _ _)
  have hrδ' : rr n < δ' := hrn.trans_le (min_le_right _ _)
  -- `χ S_r ψ = S_r ψ`
  have hχS : χ * smoothen (rr n) ψ = smoothen (rr n) ψ := by
    funext x
    by_cases hx : x ∈ K₁
    · simp [hχ1 x hx]
    · have : x ∉ tsupport (smoothen (rr n) ψ) := fun h => hx (hsupp _ hr0 hrδ h)
      simp [image_eq_zero_of_notMem_tsupport this]
  rw [Real.dist_eq]
  unfold aSeq Tfun
  rw [hχS, hΔS _ hr0, ← mul_sub, ← integral_sub]
  · rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (2 * π)⁻¹)]
    have hb : |∫ z, (u z * smoothen (rr n) (Δ ψ) z - u z * Δ ψ z)| ≤ η * A := by
      rw [← Real.norm_eq_abs]
      calc ‖∫ z, (u z * smoothen (rr n) (Δ ψ) z - u z * Δ ψ z)‖
          ≤ ∫ z, K₁.indicator (fun z => η * |u z|) z := by
            refine norm_integral_le_of_norm_le
              ((huK₁.abs.const_mul η).integrable_indicator hK₁c.measurableSet)
              (Eventually.of_forall fun z => ?_)
            by_cases hz : z ∈ K₁
            · rw [indicator_of_mem hz, ← mul_sub, norm_mul, Real.norm_eq_abs, mul_comm]
              exact mul_le_mul_of_nonneg_right (hδ'u _ hr0 hrδ' z) (abs_nonneg _)
            · have h1 : smoothen (rr n) (Δ ψ) z = 0 := by
                rw [← hΔS _ hr0]
                exact laplacian_eq_zero_of_notMem (contDiff_smoothen hr0 hψ.continuous)
                  fun h => hz (hsupp _ hr0 hrδ h)
              have h2 : Δ ψ z = 0 := laplacian_eq_zero_of_notMem hψ fun h => hz
                (self_subset_cthickening _ (hψC h))
              rw [indicator_of_notMem hz, h1, h2]
              simp
        _ = η * A := by
            rw [integral_indicator hK₁c.measurableSet, integral_const_mul]
    calc (2 * π)⁻¹ * |∫ z, (u z * smoothen (rr n) (Δ ψ) z - u z * Δ ψ z)|
        ≤ (2 * π)⁻¹ * (η * A) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ < ε := by
          have h4 : (2 * π)⁻¹ * (η * A) ≤ η * ((2 * π)⁻¹ * A + 1) := by nlinarith
          have h5 : η * ((2 * π)⁻¹ * A + 1) = ε / 2 := by
            have : (2 * π)⁻¹ * A + 1 ≠ 0 := by positivity
            rw [hη]; field_simp; ring
          linarith
  · refine integrable_mul_of_integrableOn hK₁c huK₁ ?_ fun z hz => ?_
    · rw [← hΔS _ hr0]; exact continuous_laplacian (contDiff_smoothen hr0 hψ.continuous)
    · rw [← hΔS _ hr0]
      exact laplacian_eq_zero_of_notMem (contDiff_smoothen hr0 hψ.continuous)
        fun h => hz (hsupp _ hr0 hrδ h)
  · exact integrable_mul_of_integrableOn hK₁c huK₁ hΔc fun z hz =>
      laplacian_eq_zero_of_notMem hψ fun h => hz (self_subset_cthickening _ (hψC h))

end Distr

end DF
