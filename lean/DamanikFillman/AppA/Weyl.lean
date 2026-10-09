/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Appendix A.3, preliminaries: Weyl's lemma

**Weyl's lemma** (`DF.Distr.weyl`): an integrable function `F` with `ΔF = 0` on an open set `V`
in the sense of distributions (`DistribHarmonicOn F V`) agrees almost everywhere on `V` with a
harmonic function.

Proof: the mollifications `F ⋆ moll r` are harmonic where defined (`harmonicAt_mollify`); by the
mean value property for radial kernels and Fubini,
`F ⋆ moll r = (F ⋆ moll r) ⋆ moll s = F ⋆ (moll r ⋆ moll s) = (F ⋆ moll s) ⋆ moll r = F ⋆ moll s`
wherever both sides are defined (`mollify_eq_mollify`), so the mollifications patch together to
a harmonic function `h`; by the Lebesgue differentiation theorem `F ⋆ moll r → F` almost
everywhere (`tendsto_mollify`), whence `F = h` a.e. on `V`.
-/
import DamanikFillman.AppA.Mollifier
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Integral.Average

noncomputable section

open Real Complex Metric Set Filter Topology MeasureTheory Laplacian InnerProductSpace
open scoped Convolution

namespace DF

namespace Distr

/-! ### Consistency of the mollifications -/

/-- The mean value property applied to the harmonic mollification. -/
lemma integral_mollify_mul_moll {F : ℂ → ℝ} (hF : LocallyIntegrable F) {V : Set ℂ}
    (hV : IsOpen V) (hyp : DistribHarmonicOn F V) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) {x : ℂ}
    (hx : closedBall x (r + s) ⊆ V) :
    ∫ t, mollify F r t * moll s (x - t) = mollify F r x := by
  have hH : HarmonicOnNhd (mollify F r) (closedBall x s) := fun y hy =>
    harmonicAt_mollify hF hV hyp hr (fun z hz => hx (by
      rw [mem_closedBall] at hz hy ⊢
      linarith [dist_triangle z y x]))
  rw [← integral_add_left_eq_self (fun t => mollify F r t * moll s (x - t)) x]
  simp only [sub_add_cancel_left, moll_neg hs]
  rw [integral_harmonic_mul_radial hs.le hH (continuous_moll s) (moll_eq_mollRad hs)
    (fun y hy => moll_eq_zero hs hy.le), integral_moll hs, mul_one]

/-- Fubini: `(F ⋆ moll r) ⋆ moll s = F ⋆ (moll r ⋆ moll s)`. -/
lemma integral_mollify_mul_moll_eq {F : ℂ → ℝ} (hF : Integrable F) {r s : ℝ} (hs : 0 < s)
    (x : ℂ) :
    ∫ t, mollify F r t * moll s (x - t) =
      ∫ τ, F τ * ∫ u, moll r u * moll s (x - τ - u) := by
  set f : ℂ → ℂ → ℝ := fun t τ => F τ * moll r (t - τ) * moll s (x - t) with hf
  have hψ : Integrable (fun t => moll s (x - t)) :=
    ((continuous_moll s).comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
      ((hasCompactSupport_moll hs).comp_homeomorph (Homeomorph.subLeft x))
  have hint : Integrable (Function.uncurry f) (volume.prod volume) := by
    have hdom : Integrable (fun p : ℂ × ℂ =>
        moll s (x - p.1) * ((bumpMass * r ^ 2)⁻¹ * |F p.2|)) (volume.prod volume) :=
      hψ.mul_prod (hF.abs.const_mul _)
    refine hdom.mono' ?_ (Eventually.of_forall fun p => ?_)
    · show AEStronglyMeasurable
        (fun p : ℂ × ℂ => F p.2 * moll r (p.1 - p.2) * moll s (x - p.1)) (volume.prod volume)
      exact ((hF.aestronglyMeasurable.comp_snd (μ := volume)).mul
        ((continuous_moll r).comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable).mul
        ((continuous_moll s).comp (continuous_const.sub continuous_fst)).aestronglyMeasurable
    · show ‖F p.2 * moll r (p.1 - p.2) * moll s (x - p.1)‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (moll_nonneg _),
        abs_of_nonneg (moll_nonneg _)]
      calc |F p.2| * moll r (p.1 - p.2) * moll s (x - p.1)
          ≤ |F p.2| * (bumpMass * r ^ 2)⁻¹ * moll s (x - p.1) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (moll_le _) (abs_nonneg _))
              (moll_nonneg _)
        _ = moll s (x - p.1) * ((bumpMass * r ^ 2)⁻¹ * |F p.2|) := by ring
  calc ∫ t, mollify F r t * moll s (x - t) = ∫ t, ∫ τ, f t τ := by
        refine integral_congr_ae (Eventually.of_forall fun t => ?_)
        simp only [hf, mollify_apply]
        rw [← integral_mul_const]
    _ = ∫ τ, ∫ t, f t τ := integral_integral_swap hint
    _ = ∫ τ, F τ * ∫ u, moll r u * moll s (x - τ - u) := by
        refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
        simp only [hf]
        rw [← integral_add_right_eq_self (fun t => F τ * moll r (t - τ) * moll s (x - t)) τ,
          ← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        simp only
        rw [add_sub_cancel_right, show x - (u + τ) = x - τ - u by ring]
        ring

lemma integral_moll_mul_moll_comm (r s : ℝ) (w : ℂ) :
    ∫ u, moll r u * moll s (w - u) = ∫ u, moll s u * moll r (w - u) := by
  rw [← integral_sub_left_eq_self (fun u => moll s u * moll r (w - u)) w]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [sub_sub_cancel]
  ring

/-- **Consistency**: `F ⋆ moll r = F ⋆ moll s` wherever both are harmonic. -/
theorem mollify_eq_mollify {F : ℂ → ℝ} (hF : Integrable F) {V : Set ℂ} (hV : IsOpen V)
    (hyp : DistribHarmonicOn F V) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) {x : ℂ}
    (hx : closedBall x (r + s) ⊆ V) : mollify F r x = mollify F s x := by
  have hx' : closedBall x (s + r) ⊆ V := by rwa [add_comm]
  rw [← integral_mollify_mul_moll hF.locallyIntegrable hV hyp hr hs hx,
    ← integral_mollify_mul_moll hF.locallyIntegrable hV hyp hs hr hx',
    integral_mollify_mul_moll_eq hF hs, integral_mollify_mul_moll_eq hF hr]
  refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
  simp only
  rw [integral_moll_mul_moll_comm]

/-! ### Convergence of the mollifications -/

lemma volume_real_closedBall_unit_pos : 0 < volume.real (closedBall (0 : ℂ) 1) :=
  ENNReal.toReal_pos (measure_closedBall_pos volume 0 one_pos).ne'
    measure_closedBall_lt_top.ne

/-- **Lebesgue differentiation for the mollifier**: `F ⋆ moll r → F` almost everywhere. -/
theorem tendsto_mollify {F : ℂ → ℝ} (hF : LocallyIntegrable F) :
    ∀ᵐ x : ℂ, Tendsto (fun r => mollify F r x) (𝓝[>] 0) (𝓝 (F x)) := by
  filter_upwards [(Besicovitch.vitaliFamily (volume : Measure ℂ)).ae_tendsto_average_norm_sub hF]
    with x h₀
  have := h₀.comp (Besicovitch.tendsto_filterAt volume x)
  set c₁ := volume.real (closedBall (0 : ℂ) 1) with hc₁
  have hc₁0 : 0 < c₁ := volume_real_closedBall_unit_pos
  have hpos : ∀ᶠ r in 𝓝[>] (0 : ℝ), 0 < r := eventually_mem_nhdsWithin
  refine (tendsto_integral_smul_of_tendsto_average_norm_sub (c₁ / bumpMass)
    (g := fun r y => moll r (x - y)) this ?_ ?_ ?_ ?_).congr' ?_
  · exact Eventually.of_forall fun r => hF.integrableOn_isCompact (isCompact_closedBall _ _)
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [hpos] with r hr
    rw [integral_sub_left_eq_self (fun y => moll r y) x, integral_moll hr]
  · filter_upwards [hpos] with r hr
    exact (subset_tsupport _).trans (support_moll_reflect_subset hr x)
  · filter_upwards [hpos] with r hr y
    rw [abs_of_nonneg (moll_nonneg _), addHaar_real_closedBall' volume x hr.le,
      Complex.finrank_real_complex, ← hc₁]
    calc moll r (x - y) ≤ (bumpMass * r ^ 2)⁻¹ := moll_le _
      _ = c₁ / bumpMass / (r ^ 2 * c₁) := by
          have := bumpMass_pos.ne'
          have := hr.ne'
          have := hc₁0.ne'
          field_simp
  · refine Eventually.of_forall fun r => ?_
    simp only [mollify_apply, smul_eq_mul, mul_comm]

/-! ### Weyl's lemma -/

/-- **Weyl's lemma.** -/
theorem weyl {F : ℂ → ℝ} (hF : Integrable F) {V : Set ℂ} (hV : IsOpen V)
    (hyp : DistribHarmonicOn F V) :
    ∃ h : ℂ → ℝ, HarmonicOnNhd h V ∧ ∀ᵐ x, x ∈ V → F x = h x := by
  have hrad : ∀ x ∈ V, ∃ r > 0, closedBall x (3 * r) ⊆ V := by
    intro x hx
    obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.1 hV x hx
    refine ⟨ε / 4, by positivity, (closedBall_subset_ball (by linarith)).trans hεV⟩
  choose! ρ hρpos hρV using hrad
  have hcons : ∀ x ∈ V, ∀ r, 0 < r → closedBall x (r + ρ x) ⊆ V →
      mollify F r x = mollify F (ρ x) x := fun x hx r hr hsub =>
    mollify_eq_mollify hF hV hyp hr (hρpos x hx) hsub
  refine ⟨fun x => mollify F (ρ x) x, fun x₀ hx₀ => ?_, ?_⟩
  · set r₀ := ρ x₀
    have hr₀ := hρpos x₀ hx₀
    have heq : (fun x => mollify F (ρ x) x) =ᶠ[𝓝 x₀] mollify F r₀ := by
      filter_upwards [ball_mem_nhds x₀ hr₀] with y hy
      rw [mem_ball] at hy
      have hyB : closedBall y (2 * r₀) ⊆ V := fun z hz => hρV x₀ hx₀ (by
        rw [mem_closedBall] at hz ⊢
        linarith [dist_triangle z y x₀])
      have hyV : y ∈ V := hyB (mem_closedBall_self (by linarith))
      have hy0 := hρpos y hyV
      refine (hcons y hyV r₀ hr₀ ?_).symm
      rcases le_or_gt (ρ y) r₀ with h | h
      · exact (closedBall_subset_closedBall (by linarith)).trans hyB
      · exact (closedBall_subset_closedBall (by linarith)).trans (hρV y hyV)
    refine (harmonicAt_congr_nhds heq).2 ?_
    exact harmonicAt_mollify hF.locallyIntegrable hV hyp hr₀
      ((closedBall_subset_closedBall (by linarith)).trans (hρV x₀ hx₀))
  · filter_upwards [tendsto_mollify hF.locallyIntegrable] with x hx hxV
    have hx0 := hρpos x hxV
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), mollify F r x = mollify F (ρ x) x := by
      filter_upwards [Ioc_mem_nhdsGT hx0] with r hr
      exact hcons x hxV r hr.1
        ((closedBall_subset_closedBall (by linarith [hr.2])).trans (hρV x hxV))
    exact tendsto_nhds_unique hx (tendsto_const_nhds.congr' (hev.mono fun r hr => hr.symm))

end Distr

end DF
