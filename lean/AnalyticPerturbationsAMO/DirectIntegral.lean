/-
# The direct integral `𝓗 = ∫^⊕ H_x dx` and its spectrum  (paper §2.1)

For a norm-continuous family `x ↦ H_x` of self-adjoint operators on `ℓ²(ℤ)` with a common
spectrum `Σ`, the fibrewise operator `(𝓗 u)(x) = H_x u(x)` on `L²((0,1]; ℓ²(ℤ))` satisfies
  `spec 𝓗 = Σ`.
`⊆`: the fibre resolvents assemble into a bounded inverse.  `⊇`: an approximate eigenvector
`v` of one fibre, cut off to a short interval, is an approximate eigenvector of `𝓗`.
We also prove the approximate-eigenvector characterisation of the spectrum of a self-adjoint
operator.  Everything here is proved.
-/
import AnalyticPerturbationsAMO.DensityOfStates

noncomputable section

open scoped ENNReal InnerProductSpace
open MeasureTheory Set Filter Topology L2

namespace AMO

/-! ### Approximate eigenvectors -/

section Approx

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A self-adjoint operator that is bounded below is invertible. -/
lemma isUnit_of_bounded_below {S : E →L[ℂ] E} (hS : IsSelfAdjoint S) {c : ℝ} (hc : 0 < c)
    (hb : ∀ v, c * ‖v‖ ≤ ‖S v‖) : IsUnit S := by
  have hanti : AntilipschitzWith ⟨c⁻¹, (inv_pos.2 hc).le⟩ S := by
    refine S.antilipschitz_of_bound fun v => ?_
    have := hb v
    change ‖v‖ ≤ c⁻¹ * ‖S v‖
    rw [le_inv_mul_iff₀ hc]; exact this
  have hinj : LinearMap.ker (S : E →ₗ[ℂ] E) = ⊥ :=
    LinearMap.ker_eq_bot.2 hanti.injective
  have hclosed : IsClosed (LinearMap.range (S : E →ₗ[ℂ] E) : Set E) :=
    hanti.isClosed_range S.uniformContinuous
  have : CompleteSpace (LinearMap.range (S : E →ₗ[ℂ] E)) := hclosed.completeSpace_coe
  have hperp : (LinearMap.range (S : E →ₗ[ℂ] E))ᗮ = ⊥ := by
    have h := S.orthogonal_range
    rw [← ContinuousLinearMap.star_eq_adjoint, hS.star_eq] at h
    rw [show LinearMap.range (S : E →ₗ[ℂ] E) = S.range from rfl, h]
    exact hinj
  have hsurj : LinearMap.range (S : E →ₗ[ℂ] E) = ⊤ := Submodule.orthogonal_eq_bot_iff.1 hperp
  let e := ContinuousLinearEquiv.ofBijective S hinj hsurj
  refine ⟨⟨S, e.symm, ?_, ?_⟩, rfl⟩
  · ext v; exact e.apply_symm_apply v
  · ext v; exact e.symm_apply_apply v

/-- **Approximate eigenvectors.**  If `T` is self-adjoint and `t ∈ spec T` (real), then for every
`ε > 0` there is a unit vector `v` with `‖(T - t) v‖ < ε`. -/
theorem exists_approx_eigenvector {T : E →L[ℂ] E} (hT : IsSelfAdjoint T) {t : ℝ}
    (ht : (t : ℂ) ∈ spectrum ℂ T) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : E, ‖v‖ = 1 ∧ ‖(T - algebraMap ℂ (E →L[ℂ] E) t) v‖ < ε := by
  by_contra! h
  set S := T - algebraMap ℂ (E →L[ℂ] E) t
  have hSsa : IsSelfAdjoint S := by
    refine hT.sub ?_
    rw [Algebra.algebraMap_eq_smul_one]
    exact IsSelfAdjoint.smul (by simp [IsSelfAdjoint, Complex.conj_ofReal]) (IsSelfAdjoint.one _)
  have hb : ∀ v, ε * ‖v‖ ≤ ‖S v‖ := by
    intro v
    by_cases hv : v = 0
    · simp [hv]
    · have hvn : 0 < ‖v‖ := norm_pos_iff.2 hv
      have := h ((‖v‖⁻¹ : ℂ) • v) (by
        rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm,
          inv_mul_cancel₀ hvn.ne'])
      rw [map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_norm] at this
      rw [le_inv_mul_iff₀ hvn] at this
      linarith
  have hu := isUnit_of_bounded_below hSsa hε hb
  apply spectrum.mem_iff.1 ht
  rw [← neg_sub]
  exact hu.neg

end Approx

/-! ### The direct-integral operator -/

/-- The measure `dx` on `(0, 1]`. -/
abbrev μ01 : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)

/-- The Hilbert space `L²((0,1]; ℓ²(ℤ))`. -/
abbrev DI := Lp (L2 ℤ) 2 μ01

lemma aestronglyMeasurable_apply {F : ℝ → Op ℤ} (hF : Continuous F) (f : DI) :
    AEStronglyMeasurable (fun x => F x (f x)) μ01 := by
  have hg : Continuous (Function.uncurry fun (T : Op ℤ) (v : L2 ℤ) => T v) :=
    (isBoundedBilinearMap_apply (𝕜 := ℂ) (E := L2 ℤ) (F := L2 ℤ)).continuous
  exact hg.comp_aestronglyMeasurable₂ hF.aestronglyMeasurable (Lp.aestronglyMeasurable f)

lemma memLp_apply {F : ℝ → Op ℤ} (hF : Continuous F) {M : ℝ}
    (hM : ∀ x ∈ Icc (0 : ℝ) 1, ‖F x‖ ≤ M) (f : DI) :
    MemLp (fun x => F x (f x)) 2 μ01 := by
  refine (Lp.memLp f).of_le_mul (c := M) (aestronglyMeasurable_apply hF f) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  exact (F x).le_of_opNorm_le (hM x ⟨hx.1.le, hx.2⟩) _

/-- The fibrewise operator `(𝓗 u)(x) = F_x u(x)` on `L²((0,1]; ℓ²(ℤ))`. -/
def dint (F : ℝ → Op ℤ) (hF : Continuous F) (M : ℝ) (hM : ∀ x ∈ Icc (0 : ℝ) 1, ‖F x‖ ≤ M) :
    DI →L[ℂ] DI :=
  LinearMap.mkContinuous
    { toFun := fun f => (memLp_apply hF hM f).toLp _
      map_add' := fun f g => by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_apply hF hM (f + g)),
          MemLp.coeFn_toLp (memLp_apply hF hM f), MemLp.coeFn_toLp (memLp_apply hF hM g),
          Lp.coeFn_add f g, Lp.coeFn_add ((memLp_apply hF hM f).toLp _)
            ((memLp_apply hF hM g).toLp _)] with x h1 h2 h3 h4 h5
        rw [h1, h5, Pi.add_apply, h2, h3, h4, Pi.add_apply, map_add]
      map_smul' := fun c f => by
        apply Lp.ext
        filter_upwards [MemLp.coeFn_toLp (memLp_apply hF hM (c • f)),
          MemLp.coeFn_toLp (memLp_apply hF hM f), Lp.coeFn_smul c f,
          Lp.coeFn_smul c ((memLp_apply hF hM f).toLp _)] with x h1 h2 h3 h4
        simp only [RingHom.id_apply]
        rw [h1, h4, Pi.smul_apply, h2, h3, Pi.smul_apply, map_smul] }
    (max M 0) fun f => by
      refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
      filter_upwards [MemLp.coeFn_toLp (memLp_apply hF hM f), ae_restrict_mem measurableSet_Ioc]
        with x h1 hx
      change ‖((memLp_apply hF hM f).toLp _ : DI) x‖ ≤ _
      rw [h1]
      exact (F x).le_of_opNorm_le ((hM x ⟨hx.1.le, hx.2⟩).trans (le_max_left _ _)) _

variable {F G : ℝ → Op ℤ} {hF : Continuous F} {hG : Continuous G} {M N : ℝ}
  {hM : ∀ x ∈ Icc (0 : ℝ) 1, ‖F x‖ ≤ M} {hN : ∀ x ∈ Icc (0 : ℝ) 1, ‖G x‖ ≤ N}

lemma dint_apply (f : DI) : (dint F hF M hM f : DI) =ᵐ[μ01] fun x => F x (f x) :=
  MemLp.coeFn_toLp (memLp_apply hF hM f)

/-- Multiplicativity: `∫^⊕ F ∘ ∫^⊕ G = ∫^⊕ F G`. -/
lemma dint_comp (hFG : Continuous fun x => F x * G x)
    (hMN : ∀ x ∈ Icc (0 : ℝ) 1, ‖F x * G x‖ ≤ M * N) :
    dint F hF M hM ∘L dint G hG N hN = dint (fun x => F x * G x) hFG (M * N) hMN := by
  ext1 f
  apply Lp.ext
  rw [ContinuousLinearMap.comp_apply]
  filter_upwards [dint_apply (F := F) (hF := hF) (hM := hM) (dint G hG N hN f),
    dint_apply (F := G) (hF := hG) (hM := hN) f,
    dint_apply (F := fun x => F x * G x) (hF := hFG) (hM := hMN) f] with x h1 h2 h3
  rw [h1, h2, h3]
  rfl

/-- The constant identity family gives the identity. -/
lemma dint_one (h1 : Continuous fun _ : ℝ => (1 : Op ℤ))
    (hM1 : ∀ x ∈ Icc (0 : ℝ) 1, ‖(1 : Op ℤ)‖ ≤ 1) :
    dint (fun _ => (1 : Op ℤ)) h1 1 hM1 = 1 := by
  ext1 f
  apply Lp.ext
  filter_upwards [dint_apply (F := fun _ => (1 : Op ℤ)) (hF := h1) (hM := hM1) f] with x h
  rw [h]
  rfl

/-- Subtracting a scalar fibrewise. -/
lemma dint_sub_scalar (z : ℂ) (hFz : Continuous fun x => F x - algebraMap ℂ (Op ℤ) z)
    (hMz : ∀ x ∈ Icc (0 : ℝ) 1, ‖F x - algebraMap ℂ (Op ℤ) z‖ ≤ M + ‖z‖) :
    dint (fun x => F x - algebraMap ℂ (Op ℤ) z) hFz (M + ‖z‖) hMz =
      dint F hF M hM - algebraMap ℂ (DI →L[ℂ] DI) z := by
  ext1 f
  apply Lp.ext
  rw [ContinuousLinearMap.sub_apply]
  filter_upwards [dint_apply (F := fun x => F x - algebraMap ℂ (Op ℤ) z) (hF := hFz) (hM := hMz) f,
    dint_apply (F := F) (hF := hF) (hM := hM) f,
    Lp.coeFn_sub (dint F hF M hM f) (algebraMap ℂ (DI →L[ℂ] DI) z f),
    Lp.coeFn_smul z f] with x h1 h2 h3 h4
  rw [h1, h3, Pi.sub_apply, h2]
  simp only [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply]
  rw [h4]
  rfl

/-- `∫^⊕` depends only on the family. -/
lemma dint_ext {F' : ℝ → Op ℤ} {hF' : Continuous F'} {M' : ℝ}
    {hM' : ∀ x ∈ Icc (0 : ℝ) 1, ‖F' x‖ ≤ M'} (h : ∀ x, F x = F' x) :
    dint F hF M hM = dint F' hF' M' hM' := by
  ext1 f
  apply Lp.ext
  filter_upwards [dint_apply (F := F) (hF := hF) (hM := hM) f,
    dint_apply (F := F') (hF := hF') (hM := hM') f] with x h1 h2
  rw [h1, h2, h x]

set_option maxHeartbeats 1000000 in
/-- **Spectrum of the direct integral.**  If every fibre is self-adjoint with spectrum `S`,
then `spec(∫^⊕ F) = S`. -/
theorem spectrum_dint (hsa : ∀ x, IsSelfAdjoint (F x)) {S : Set ℂ}
    (hS : ∀ x, spectrum ℂ (F x) = S) : spectrum ℂ (dint F hF M hM) = S := by
  ext z
  constructor
  · -- `⊆`: if `z ∉ S`, the fibre resolvents give a bounded inverse
    intro hz
    by_contra hzS
    apply spectrum.mem_iff.1 hz
    have hunit : ∀ x, IsUnit (F x - algebraMap ℂ (Op ℤ) z) := fun x => by
      have : z ∉ spectrum ℂ (F x) := by rw [hS x]; exact hzS
      rw [spectrum.mem_iff, not_not] at this
      rw [← neg_sub]; exact this.neg
    set G : ℝ → Op ℤ := fun x => Ring.inverse (F x - algebraMap ℂ (Op ℤ) z)
    have hFz : Continuous fun x => F x - algebraMap ℂ (Op ℤ) z := hF.sub continuous_const
    have hG : Continuous G := by
      refine continuous_iff_continuousAt.2 fun x => ?_
      obtain ⟨u, hu⟩ := hunit x
      have := NormedRing.inverse_continuousAt u
      rw [hu] at this
      exact this.comp (f := fun y => F y - algebraMap ℂ (Op ℤ) z) hFz.continuousAt
    obtain ⟨N, hN⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      hG.continuousOn
    have hMz : ∀ x ∈ Icc (0 : ℝ) 1, ‖F x - algebraMap ℂ (Op ℤ) z‖ ≤ M + ‖z‖ := by
      intro x hx
      refine (norm_sub_le _ _).trans (add_le_add (hM x hx) ?_)
      rw [Algebra.algebraMap_eq_smul_one, norm_smul]
      exact mul_le_of_le_one_right (norm_nonneg _) norm_one.le
    have h1 : Continuous fun _ : ℝ => (1 : Op ℤ) := continuous_const
    have hM1 : ∀ x ∈ Icc (0 : ℝ) 1, ‖(1 : Op ℤ)‖ ≤ 1 := fun _ _ => norm_one.le
    have hl : dint (fun x => F x - algebraMap ℂ (Op ℤ) z) hFz (M + ‖z‖) hMz ∘L
        dint G hG N hN = 1 := by
      rw [dint_comp (hFz.mul hG) (fun x hx => (norm_mul_le _ _).trans
        (mul_le_mul (hMz x hx) (hN x hx) (norm_nonneg _) ((norm_nonneg _).trans (hMz x hx)))),
        ← dint_one h1 hM1]
      exact dint_ext fun x => Ring.mul_inverse_cancel _ (hunit x)
    have hr : dint G hG N hN ∘L
        dint (fun x => F x - algebraMap ℂ (Op ℤ) z) hFz (M + ‖z‖) hMz = 1 := by
      rw [dint_comp (hG.mul hFz) (fun x hx => (norm_mul_le _ _).trans
        (mul_le_mul (hN x hx) (hMz x hx) (norm_nonneg _) ((norm_nonneg _).trans (hN x hx)))),
        ← dint_one h1 hM1]
      exact dint_ext fun x => Ring.inverse_mul_cancel _ (hunit x)
    have hU : IsUnit (dint F hF M hM - algebraMap ℂ (DI →L[ℂ] DI) z) := by
      rw [← dint_sub_scalar z hFz hMz]
      exact ⟨⟨_, _, hl, hr⟩, rfl⟩
    rw [← neg_sub]
    exact hU.neg
  · -- `⊇`: an approximate eigenvector of one fibre, cut off to a short interval
    intro hzS
    set x₀ : ℝ := 1 / 2
    have hz₀ : z ∈ spectrum ℂ (F x₀) := by rw [hS]; exact hzS
    have hzre : z = (z.re : ℂ) := (hsa x₀).mem_spectrum_eq_re hz₀
    rw [hzre] at hz₀ ⊢
    set t := z.re
    rw [spectrum.mem_iff]
    intro hunit
    have hU : IsUnit (dint F hF M hM - algebraMap ℂ (DI →L[ℂ] DI) t) := by
      rw [← neg_sub]; exact hunit.neg
    obtain ⟨u, hu⟩ := hU
    obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = ‖(↑u⁻¹ : DI →L[ℂ] DI)‖ := ⟨_, rfl⟩
    have hK0 : 0 ≤ K := hKdef ▸ norm_nonneg _
    obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = 1 / (4 * (K + 1)) := ⟨_, rfl⟩
    have hε : 0 < ε := by rw [hεdef]; positivity
    obtain ⟨v, hv1, hv⟩ := exists_approx_eigenvector (hsa x₀) hz₀ hε
    -- continuity of `x ↦ ‖(F x - t) v‖`
    have hc : Continuous fun x => ‖(F x - algebraMap ℂ (Op ℤ) t) v‖ :=
      ((hF.sub continuous_const).clm_apply continuous_const).norm
    obtain ⟨δ, hδ, hball⟩ := Metric.continuous_iff.1 hc x₀ ε hε
    obtain ⟨δ', hδ'def⟩ : ∃ δ' : ℝ, δ' = min δ (1 / 4) := ⟨_, rfl⟩
    have hδ' : 0 < δ' := hδ'def ▸ lt_min hδ (by norm_num)
    have hδ'1 : δ' ≤ δ := hδ'def ▸ min_le_left _ _
    have hδ'2 : δ' ≤ 1 / 4 := hδ'def ▸ min_le_right _ _
    obtain ⟨I, hIdef⟩ : ∃ I : Set ℝ, I = Ioo (x₀ - δ') (x₀ + δ') := ⟨_, rfl⟩
    have hImeas : MeasurableSet I := hIdef ▸ measurableSet_Ioo
    have hIsub : I ⊆ Ioc 0 1 := fun x hx => by
      rw [hIdef, mem_Ioo] at hx
      simp only [x₀] at hx
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hIx : ∀ x ∈ I, ‖(F x - algebraMap ℂ (Op ℤ) t) v‖ < 2 * ε := by
      intro x hx
      have hd : dist x x₀ < δ := by
        rw [Real.dist_eq, abs_lt]
        rw [hIdef, mem_Ioo] at hx
        constructor <;> linarith
      have := hball x hd
      rw [Real.dist_eq] at this
      have h0 := abs_lt.1 this
      linarith [h0.2]
    have hμI : μ01 I = volume I := by
      rw [Measure.restrict_apply hImeas, inter_eq_left.2 hIsub]
    have hμI_ne : μ01 I ≠ ⊤ := by
      rw [hμI, hIdef, Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
    have hμI_pos : 0 < (μ01 I).toReal := by
      rw [hμI, hIdef, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith)]; linarith
    obtain ⟨w, hwdef⟩ : ∃ w : DI, w = indicatorConstLp 2 hImeas hμI_ne v := ⟨_, rfl⟩
    have hw : 0 < ‖w‖ := by
      rw [hwdef, norm_indicatorConstLp (by norm_num) (by norm_num), hv1, one_mul]
      exact Real.rpow_pos_of_pos hμI_pos _
    -- `‖(𝓗 - t) w‖ ≤ 2ε ‖w‖`
    have hFz : Continuous fun x => F x - algebraMap ℂ (Op ℤ) t := hF.sub continuous_const
    have hMz : ∀ x ∈ Icc (0 : ℝ) 1, ‖F x - algebraMap ℂ (Op ℤ) t‖ ≤ M + ‖(t : ℂ)‖ := by
      intro x hx
      refine (norm_sub_le _ _).trans (add_le_add (hM x hx) ?_)
      rw [Algebra.algebraMap_eq_smul_one, norm_smul]
      exact mul_le_of_le_one_right (norm_nonneg _) norm_one.le
    have hDw : ‖(dint F hF M hM - algebraMap ℂ (DI →L[ℂ] DI) t) w‖ ≤ 2 * ε * ‖w‖ := by
      rw [← dint_sub_scalar (t : ℂ) hFz hMz]
      refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
      filter_upwards [dint_apply (F := fun x => F x - algebraMap ℂ (Op ℤ) t) (hF := hFz)
        (hM := hMz) w, hwdef ▸ indicatorConstLp_coeFn (p := 2) (hs := hImeas)
        (hμs := hμI_ne) (c := v)] with x h1 h2
      rw [h1, h2]
      by_cases hx : x ∈ I
      · rw [indicator_of_mem hx, hv1, mul_one]
        exact (hIx x hx).le
      · rw [indicator_of_notMem hx, map_zero, norm_zero, mul_zero]
    have hinv : w = (↑u⁻¹ : DI →L[ℂ] DI) ((dint F hF M hM - algebraMap ℂ (DI →L[ℂ] DI) t) w) := by
      rw [← hu, ← ContinuousLinearMap.mul_apply, Units.inv_mul, ContinuousLinearMap.one_apply]
    have hK : ‖w‖ ≤ K * (2 * ε * ‖w‖) := by
      calc ‖w‖ = ‖(↑u⁻¹ : DI →L[ℂ] DI) ((dint F hF M hM - algebraMap ℂ (DI →L[ℂ] DI) t) w)‖ := by
            rw [← hinv]
        _ ≤ K * ‖(dint F hF M hM - algebraMap ℂ (DI →L[ℂ] DI) t) w‖ := by
            rw [hKdef]; exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ K * (2 * ε * ‖w‖) := mul_le_mul_of_nonneg_left hDw hK0
    have : K * (2 * ε) ≤ 1 / 2 := by
      rw [hεdef, show K * (2 * (1 / (4 * (K + 1)))) = K / (2 * (K + 1)) by field_simp; ring]
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith

end AMO
