/-
# Corollary 1.3 from Theorem 1.1 by Fourier duality

For `λ > 1`, the supercritical operator `U + U^{-1} + λ(V + V^{-1}) + T` is `λ` times the Fourier
dual of the subcritical operator with coupling `λ^{-1}` and perturbation `λ^{-1} 𝓕^{-1}(T)`.
Theorem 1.1 applied to the latter (with the two analytic weights exchanged) gives Cantor
spectrum and all open gaps; we transport them by the scaling `E ↦ λE`.

This file proves the transport (spectra, Cantor sets, IDS measures and gap labels under
scaling, and the duality identity).  The resulting Corollary 1.3 then depends only on
Theorem 1.1 and Corollary 1.2.
-/
import AnalyticPerturbationsAMO.DensityOfStates

noncomputable section

open scoped ComplexConjugate ENNReal
open MeasureTheory Set Filter BoundedContinuousFunction L2

namespace AMO

/-! ### Scaling of spectra, Cantor sets, DOS measures and gaps -/

instance : Nontrivial (Op ℤ) := ⟨⟨0, 1, fun h => by
  have := congrArg (fun T : Op ℤ => T (delta 0)) h
  simp only [ContinuousLinearMap.zero_apply, ContinuousLinearMap.one_apply] at this
  have h2 := congrArg (fun u : L2 ℤ => u 0) this
  simp [delta] at h2⟩⟩

lemma spectrum_real_smul {c : ℝ} (hc : c ≠ 0) (A : Op ℤ) :
    spectrum ℝ (((c : ℝ) : ℂ) • A) = (fun t => c * t) '' spectrum ℝ A := by
  have hne : (spectrum ℂ A).Nonempty := spectrum.nonempty A
  rw [← spectrum.preimage_algebraMap ℂ, ← spectrum.preimage_algebraMap ℂ (a := A),
    spectrum.smul_eq_smul _ _ hne]
  ext t
  simp only [mem_preimage, Complex.coe_algebraMap, mem_image, Set.mem_smul_set, smul_eq_mul]
  constructor
  · rintro ⟨z, hz, hzt⟩
    have hz' : z = ((t / c : ℝ) : ℂ) := by
      push_cast
      rw [eq_div_iff (by exact_mod_cast hc), mul_comm, hzt]
    refine ⟨t / c, by rw [← hz']; exact hz, by field_simp⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, hu, by push_cast; ring⟩

lemma IsCantor.image_mul {K : Set ℝ} (hK : IsCantor K) {c : ℝ} (hc : 0 < c) :
    IsCantor ((fun t => c * t) '' K) := by
  set h := Homeomorph.mulLeft₀ c hc.ne'
  have himg : (fun t => c * t) '' K = h '' K := rfl
  obtain ⟨hne, hcpt, hperf, hint⟩ := hK
  rw [himg]
  refine ⟨hne.image _, hcpt.image h.continuous, ⟨h.isClosedMap _ hperf.closed, ?_⟩, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have := (hperf.acc x hx).map h.continuous.continuousAt h.injective
    rwa [Filter.map_principal] at this
  · rw [← h.image_interior, hint, image_empty]

lemma IsDOSMeasure.map_mul {Hx Hx' : ℝ → Op ℤ} {ν' : Measure ℝ} (hν : IsDOSMeasure Hx' ν')
    {η : ℝ} (hη : 0 < η) (hH : ∀ x, Hx' x = ((η : ℝ) : ℂ) • Hx x)
    (hsa : ∀ x, IsSelfAdjoint (Hx x)) :
    IsDOSMeasure Hx (ν'.map (fun t => η⁻¹ * t)) := by
  have hprob := hν.1
  have hmeas : Measurable fun t : ℝ => η⁻¹ * t := measurable_const.mul measurable_id
  refine ⟨inferInstance, fun f => ?_⟩
  rw [integral_map hmeas.aemeasurable f.continuous.aestronglyMeasurable]
  set g : ℝ →ᵇ ℝ := f.compContinuous ⟨fun t => η⁻¹ * t, continuous_const.mul continuous_id⟩
  have h := hν.2 g
  rw [show (∫ t, f (η⁻¹ * t) ∂ν') = ∫ t, g t ∂ν' from rfl, h]
  congr 1
  funext x
  have hn : IsStarNormal (Hx x) := (hsa x).isStarNormal
  have hη' : IsSelfAdjoint (((η : ℝ) : ℂ)) := by
    rw [IsSelfAdjoint, RCLike.star_def, Complex.conj_ofReal]
  have hn' : IsStarNormal (((η : ℝ) : ℂ) • Hx x) := (IsSelfAdjoint.smul hη' (hsa x)).isStarNormal
  set F : ℂ → ℂ := fun z => ((f z.re : ℝ) : ℂ)
  have hF : Continuous F := Complex.continuous_ofReal.comp (f.continuous.comp Complex.continuous_re)
  have hcomp : cfc (fun z : ℂ => ((f (η⁻¹ * z.re) : ℝ) : ℂ)) (((η : ℝ) : ℂ) • Hx x) =
      cfc F (Hx x) := by
    have := cfc_comp_smul (((η⁻¹ : ℝ) : ℂ)) F (((η : ℝ) : ℂ) • Hx x) hF.continuousOn hn'
    rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hη.ne', Complex.ofReal_one,
      one_smul] at this
    rw [← this]
    congr 1
    funext z
    simp [F, smul_eq_mul, Complex.mul_re]
  rw [hH, show (fun z : ℂ => ((g z.re : ℝ) : ℂ)) = fun z => ((f (η⁻¹ * z.re) : ℝ) : ℂ) from rfl,
    hcomp]

lemma GapOpen.map_mul {S : Set ℝ} {ν : Measure ℝ} {α : ℝ} {n : ℤ} (h : GapOpen S ν α n)
    {c : ℝ} (hc : 0 < c) :
    GapOpen ((fun t => c * t) '' S) (ν.map (fun t => c * t)) α n := by
  obtain ⟨a, b, hab, ha, hb, hgap, hids⟩ := h
  have hmeas : Measurable fun t : ℝ => c * t := measurable_const.mul measurable_id
  refine ⟨c * a, c * b, by nlinarith, ⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩, ?_, ?_⟩
  · ext t
    simp only [mem_inter_iff, mem_Ioo, mem_image, mem_empty_iff_false, iff_false, not_and]
    rintro ⟨h1, h2⟩ ⟨u, hu, rfl⟩
    have : u ∈ Ioo a b ∩ S := ⟨⟨by nlinarith, by nlinarith⟩, hu⟩
    rw [hgap] at this
    exact this
  · intro E hE
    unfold IDS
    rw [Measure.map_apply hmeas measurableSet_Iic]
    have hpre : (fun t => c * t) ⁻¹' Iic E = Iic (E / c) := by
      ext t; simp only [mem_preimage, mem_Iic]; rw [le_div_iff₀ hc, mul_comm]
    rw [hpre]
    exact hids (E / c) ⟨by rw [le_div_iff₀ hc]; nlinarith [hE.1], by
      rw [div_le_iff₀ hc]; nlinarith [hE.2]⟩

lemma AllGapsOpen.map_mul {S : Set ℝ} {ν : Measure ℝ} {α : ℝ} (h : AllGapsOpen S ν α)
    {c : ℝ} (hc : 0 < c) :
    AllGapsOpen ((fun t => c * t) '' S) (ν.map (fun t => c * t)) α :=
  fun n hn => (h n hn).map_mul hc

/-! ### The duality identity -/

lemma op_smul' (α : ℝ) (c : ℂ) {S : Symbol} (hS : SymbolSummable S) (x : ℝ) :
    op α (c • S) x = c • op α S x := by
  unfold op
  rw [← ((summable_op (α := α) hS x).hasSum.const_smul c).tsum_eq]
  congr 1
  funext p
  exact (smul_smul c (S p) (W α x p.1 p.2)).symm

lemma fourier_smul (c : ℂ) (S : Symbol) : fourier (c • S) = c • fourier S := rfl

/-- `𝓕(H_{λ^{-1}, λ^{-1} 𝓕^{-1} T}) = λ^{-1} H_{λ, T}`. -/
theorem Hdual_supercritical {α lam : ℝ} (hlam : 0 < lam) {T : Symbol} (hT : SymbolSummable T)
    (x : ℝ) :
    Hdual α lam⁻¹ (((lam⁻¹ : ℝ) : ℂ) • fourier (fourier (fourier T))) x =
      (((lam⁻¹ : ℝ) : ℂ)) • H α lam T x := by
  unfold Hdual H
  rw [fourier_add, fourier_smul, fourier_amo (by exact_mod_cast (inv_pos.2 hlam).ne')]
  have h4 : fourier (fourier (fourier (fourier T))) = T := fourier_four T
  rw [h4, Complex.ofReal_inv, inv_inv, ← smul_add]
  rw [op_smul' α _ ((amo_summable _).add hT)]

end AMO
