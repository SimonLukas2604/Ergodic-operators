/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Appendix A.3: the Riesz representation of subharmonic functions (Theorem A.3.2)

`DF.rieszRepresentationStatement_holds`: a real-valued subharmonic function `u` on an open set
`U` admits, on every open `U'` with compact closure in `U`, a unique decomposition
`u = -Φ_μ + h` with `μ` a finite measure carried by `U'` and `h` harmonic on `U'`.

Proof.
* *Existence of `μ`*: the Riesz measure `ν` of `u` (`DF.Distr.exists_rieszMeasure`), restricted
  to `U'`, satisfies `∫ ψ dμ = (2π)⁻¹ ∫ u Δψ` for test functions `ψ` supported in `U'`.
* *The harmonic part*: since `ΔΦ_μ = -2πμ` (`integral_logPotential_mul_laplacian`), the function
  `u + Φ_μ` is distributionally harmonic on `U'`; by Weyl's lemma it agrees a.e. with a harmonic
  `h`.
* *Pointwise identity*: comparing the mollified averages `M_r f(z) = ∫ f(z + y) moll_r(y) dy` —
  `u(z) ≤ M_r u(z) → u(z)` (sub-mean value inequality and upper semicontinuity),
  `M_r h(z) = h(z)` (mean value property) and `M_r Φ_μ(z) → Φ_μ(z)` (super-mean value inequality
  and lower semicontinuity) — upgrades the a.e. identity `u = h - Φ_μ` to an identity everywhere
  on `U'`.
* *Uniqueness*: two representations give `∫ ψ dμ₁ = ∫ ψ dμ₂` for all test functions supported in
  `U'` (`integral_harmonic_mul_laplacian`), hence `μ₁ = μ₂` (`measure_eq_of_integral_eq`).
-/
import DamanikFillman.AppA.RieszMeasure
import DamanikFillman.AppA.FourierDecay

noncomputable section

open Real Complex Metric Set Filter Topology MeasureTheory Laplacian InnerProductSpace

namespace DF

namespace Distr

/-! ### Mollified averages -/

lemma integrable_comp_add_mul_moll {f : ℂ → ℝ} {z : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : IntegrableOn f (closedBall z r)) : Integrable (fun y => f (z + y) * moll r y) := by
  have h1 := ((hf.integrable_indicator measurableSet_closedBall).comp_add_left z).bdd_mul
    (c := (bumpMass * r ^ 2)⁻¹) (continuous_moll r).aestronglyMeasurable
    (Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (moll_nonneg y)]; exact moll_le y)
  refine h1.congr (Eventually.of_forall fun y => ?_)
  by_cases hy : ‖y‖ ≤ r
  · simp only [indicator_of_mem (add_mem_closedBall_of_norm_le hy)]
    ring
  · simp [moll_eq_zero hr (not_le.1 hy).le]

lemma integral_moll_le_of_le {f : ℂ → ℝ} {z : ℂ} {r a : ℝ} (hr : 0 < r)
    (hf : Integrable (fun y => f (z + y) * moll r y)) (h : ∀ y, ‖y‖ < r → f (z + y) ≤ a) :
    ∫ y, f (z + y) * moll r y ≤ a := by
  calc ∫ y, f (z + y) * moll r y ≤ ∫ y, a * moll r y := by
        refine integral_mono hf ((integrable_moll hr).const_mul a) fun y => ?_
        by_cases hy : ‖y‖ < r
        · exact mul_le_mul_of_nonneg_right (h y hy) (moll_nonneg y)
        · simp [moll_eq_zero hr (not_lt.1 hy)]
    _ = a := by rw [integral_const_mul, integral_moll hr, mul_one]

lemma le_integral_moll_of_le {f : ℂ → ℝ} {z : ℂ} {r b : ℝ} (hr : 0 < r)
    (hf : Integrable (fun y => f (z + y) * moll r y))
    (h : ∀ᵐ y, ‖y‖ < r → b ≤ f (z + y)) : b ≤ ∫ y, f (z + y) * moll r y := by
  calc b = ∫ y, b * moll r y := by rw [integral_const_mul, integral_moll hr, mul_one]
    _ ≤ ∫ y, f (z + y) * moll r y := by
        refine integral_mono_ae ((integrable_moll hr).const_mul b) hf ?_
        filter_upwards [h] with y hy
        by_cases hy' : ‖y‖ < r
        · exact mul_le_mul_of_nonneg_right (hy hy') (moll_nonneg y)
        · simp [moll_eq_zero hr (not_lt.1 hy')]

/-! ### Logarithmic potentials are a.e. finite -/

lemma ae_logPotential_ne_top {μ : Measure ℂ} [IsFiniteMeasure μ] {S : ℝ}
    (hμS : μ (closedBall 0 S)ᶜ = 0) : ∀ᵐ z, logPotential μ z ≠ ⊤ := by
  have hμ := integrable_norm_of_bounded hμS
  have hn : ∀ n : ℕ, ∀ᵐ z : ℂ, ‖z‖ ≤ n → logPotential μ z ≠ ⊤ := by
    intro n
    set g : ℂ → ℝ := (closedBall (0 : ℂ) n).indicator 1 with hg
    have hgm : Measurable g := measurable_one.indicator measurableSet_closedBall
    have hgM : ∀ z, ‖g z‖ ≤ 1 := fun z => by
      by_cases hz : z ∈ closedBall (0 : ℂ) n
      · simp [hg, indicator_of_mem hz]
      · simp [hg, indicator_of_notMem hz]
    have hgR : ∀ z, (n : ℝ) < ‖z‖ → g z = 0 := fun z hz => by
      rw [hg, indicator_of_notMem]
      rw [mem_closedBall, dist_zero_right]
      exact not_le.2 hz
    have hI := integrable_prod_log hμS hgm hgM hgR
    filter_upwards [ae_measure_singleton_eq_zero μ, hI.prod_left_ae] with z hz hzi hzn
    have hg1 : g z = 1 := by
      simp [hg, indicator_of_mem (show z ∈ closedBall (0 : ℂ) n by
        rw [mem_closedBall, dist_zero_right]; exact hzn)]
    have hint : Integrable (fun w => Real.log ‖z - w‖) μ := by simpa [hg1] using hzi
    rw [logPotential_eq_integral hμ hz hint]
    exact EReal.coe_ne_top _
  rw [← ae_all_iff] at hn
  filter_upwards [hn] with z hz
  obtain ⟨n, hn'⟩ := exists_nat_ge ‖z‖
  exact hz n hn'

end Distr

open Distr in
/-- **Theorem A.3.2 (Riesz representation).** -/
theorem rieszRepresentationStatement_holds : RieszRepresentationStatement := by
  intro U u hU hu U' hU' hcl hclU
  obtain ⟨ν, hνfin, hν⟩ := exists_rieszMeasure hU hu hcl hclU
  haveI := hνfin
  set μ := ν.restrict U' with hμdef
  have hμfin : IsFiniteMeasure μ := ⟨by
    rw [hμdef, Measure.restrict_apply_univ]
    exact (measure_mono subset_closure).trans_lt hcl.measure_lt_top⟩
  have hμU' : μ U'ᶜ = 0 := by
    rw [hμdef, Measure.restrict_apply hU'.isClosed_compl.measurableSet, compl_inter_self,
      measure_empty]
  obtain ⟨S, hS⟩ := hcl.isBounded.subset_closedBall 0
  have hU'S : U' ⊆ closedBall 0 S := subset_closure.trans hS
  have hμS : μ (closedBall 0 S)ᶜ = 0 := measure_mono_null (compl_subset_compl.2 hU'S) hμU'
  have hμ1 := integrable_norm_of_bounded hμS
  -- the defining identity of `μ`
  have hkey : ∀ ψ : ℂ → ℝ, ContDiff ℝ 2 ψ → HasCompactSupport ψ → tsupport ψ ⊆ U' →
      ∫ z, u z * Δ ψ z = 2 * π * ∫ z, ψ z ∂μ := by
    intro ψ hψ hψc hψU'
    have h1 : ∫ z, ψ z ∂μ = ∫ z, ψ z ∂ν := by
      rw [hμdef]
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
      exact image_eq_zero_of_notMem_tsupport fun h => hx (hψU' h)
    rw [h1, hν ψ hψ hψc (hψU'.trans subset_closure)]
    have := Real.pi_pos.ne'
    field_simp
  -- local integrability
  have huC : IntegrableOn u (closure U') := integrableOn_of_subharmonic hU hu hcl hclU
  have hΦS : IntegrableOn (fun z => (logPotential μ z).toReal) (closedBall 0 S) :=
    integrableOn_logPotential hμS S
  -- the distributionally harmonic function `u + Φ_μ`
  set F : ℂ → ℝ := U'.indicator (fun z => u z + (logPotential μ z).toReal) with hFdef
  have hFint : Integrable F :=
    ((huC.mono_set subset_closure).add (hΦS.mono_set hU'S)).integrable_indicator
      hU'.measurableSet
  have hdist : DistribHarmonicOn F U' := by
    intro ψ hψ hψc hψU'
    have hΔ0 : ∀ z, z ∉ U' → Δ ψ z = 0 := fun z hz =>
      laplacian_eq_zero_of_notMem hψ fun h => hz (hψU' h)
    have e : (fun z => F z * Δ ψ z) =
        fun z => u z * Δ ψ z + (logPotential μ z).toReal * Δ ψ z := by
      funext z
      by_cases hz : z ∈ U'
      · simp only [hFdef, indicator_of_mem hz]; ring
      · simp only [hFdef, indicator_of_notMem hz, hΔ0 z hz, mul_zero, add_zero]
    have hi1 : Integrable (fun z => u z * Δ ψ z) :=
      integrable_u_laplacian hcl huC hψ (hψU'.trans subset_closure)
    have hi2 : Integrable (fun z => (logPotential μ z).toReal * Δ ψ z) :=
      integrable_u_laplacian (isCompact_closedBall 0 S) hΦS hψ (hψU'.trans hU'S)
    rw [e, integral_add hi1 hi2, hkey ψ hψ hψc hψU',
      integral_logPotential_mul_laplacian hμS hψ hψc]
    ring
  obtain ⟨h, hh, hae⟩ := weyl hFint hU' hdist
  refine ⟨μ, ⟨hμfin, hμU', h, hh, fun z hz => ?_⟩, ?_⟩
  · ----------------------------------------------------------------------------------------
    -- the pointwise identity
    obtain ⟨r₀, hr₀, hr₀U'⟩ : ∃ r₀ > 0, closedBall z r₀ ⊆ U' := by
      obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU' z hz
      exact ⟨ε / 2, by positivity, (closedBall_subset_ball (by linarith)).trans hεU⟩
    have hzU : closedBall z r₀ ⊆ U := hr₀U'.trans (subset_closure.trans hclU)
    -- a.e. identity near `z`
    have hae' : ∀ᵐ y : ℂ, z + y ∈ U' → u (z + y) + (logPotential μ (z + y)).toReal = h (z + y) := by
      have := (measurePreserving_add_left volume z).quasiMeasurePreserving.ae hae
      filter_upwards [this] with y hy hyU
      have := hy hyU
      simpa [hFdef, indicator_of_mem hyU] using this
    have hfinΦ : ∀ᵐ y : ℂ, logPotential μ (z + y) ≠ ⊤ :=
      (measurePreserving_add_left volume z).quasiMeasurePreserving.ae (ae_logPotential_ne_top hμS)
    -- integrability of the mollified quantities, for `0 < r ≤ r₀`
    have hiu : ∀ r, 0 < r → r ≤ r₀ → Integrable (fun y => u (z + y) * moll r y) :=
      fun r hr hrr => integrable_comp_add_mul_moll hr
        ((huC.mono_set subset_closure).mono_set
          ((closedBall_subset_closedBall hrr).trans hr₀U'))
    have hiΦ : ∀ r, 0 < r → r ≤ r₀ →
        Integrable (fun y => (logPotential μ (z + y)).toReal * moll r y) :=
      fun r hr hrr => integrable_comp_add_mul_moll hr
        (hΦS.mono_set (((closedBall_subset_closedBall hrr).trans hr₀U').trans hU'S))
    -- (A) `M_r u = h(z) - M_r Φ`
    have hA : ∀ r, 0 < r → r ≤ r₀ → ∫ y, u (z + y) * moll r y =
        h z - ∫ y, (logPotential μ (z + y)).toReal * moll r y := by
      intro r hr hrr
      obtain ⟨δ, hδ, hδs⟩ := (isCompact_closedBall z r).exists_thickening_subset_open hU'
        ((closedBall_subset_closedBall hrr).trans hr₀U')
      have hhc : ContinuousOn h (ball z (r + δ)) := fun w hw =>
        (hh w (hδs (by rw [thickening_closedBall hδ hr.le, mem_ball]; rw [mem_ball] at hw;
          linarith))).1.continuousAt.continuousWithinAt
      have hcont := continuous_mul_kernel (continuous_moll r) (fun y hy => moll_eq_zero hr hy.le)
        (show r < r + δ by linarith) hhc
      have hih : Integrable (fun y => h (z + y) * moll r y) :=
        hcont.integrable_of_hasCompactSupport (hasCompactSupport_moll hr).mul_left
      have hmean : ∫ y, h (z + y) * moll r y = h z := by
        rw [integral_harmonic_mul_radial hr.le
          (hh.mono ((closedBall_subset_closedBall hrr).trans hr₀U')) (continuous_moll r)
          (moll_eq_mollRad hr) (fun y hy => moll_eq_zero hr hy.le), integral_moll hr, mul_one]
      rw [← hmean, ← integral_sub hih (hiΦ r hr hrr)]
      refine integral_congr_ae ?_
      filter_upwards [hae'] with y hy
      by_cases hyr : ‖y‖ < r
      · have hmem : z + y ∈ U' := hr₀U' (add_mem_closedBall_of_norm_le (hyr.le.trans hrr))
        rw [← hy hmem]
        ring
      · simp [moll_eq_zero hr (not_lt.1 hyr)]
    -- (B) sub-mean value inequality for `u`
    have hB : ∀ r, 0 < r → r ≤ r₀ → u z ≤ ∫ y, u (z + y) * moll r y := by
      intro r hr hrr
      have := le_integral_moll hU hu hr ((closedBall_subset_closedBall hrr).trans hzU)
        ((huC.mono_set subset_closure).mono_set
          ((closedBall_subset_closedBall hrr).trans hr₀U'))
        (Eventually.of_forall fun w => EReal.coe_ne_bot _)
      simp only [EReal.toReal_coe] at this
      exact EReal.coe_le_coe_iff.1 this
    -- (C) super-mean value inequality for `Φ`
    have hC : ∀ r, 0 < r → r ≤ r₀ →
        ((∫ y, (logPotential μ (z + y)).toReal * moll r y : ℝ) : EReal) ≤ logPotential μ z := by
      intro r hr hrr
      have hsub := subharmonic_neg_logPotential hμ1
      have hint : IntegrableOn (fun w => (-logPotential μ w).toReal) (closedBall z r) := by
        simp only [EReal.toReal_neg_eq]
        exact (hΦS.mono_set (((closedBall_subset_closedBall hrr).trans hr₀U').trans hU'S)).neg
      have hfin : ∀ᵐ w, -logPotential μ w ≠ ⊥ := by
        filter_upwards [ae_logPotential_ne_top hμS] with w hw
        rwa [ne_eq, EReal.neg_eq_bot_iff]
      have := le_integral_moll isOpen_univ hsub hr (subset_univ _) hint hfin
      simp only [EReal.toReal_neg_eq, neg_mul, integral_neg, EReal.coe_neg] at this
      exact EReal.neg_le_neg_iff.1 this
    -- (D) upper semicontinuity of `u`
    have hD : ∀ a : ℝ, u z < a → ∃ ρ > 0, ∀ r, 0 < r → r ≤ ρ →
        ∫ y, u (z + y) * moll r y ≤ a := by
      intro a ha
      have husc := upperSemicontinuousOn_coe_iff.1 hu.usc
      have hev := husc z (hzU (mem_closedBall_self hr₀.le)) a ha
      rw [(hU.nhdsWithin_eq (hzU (mem_closedBall_self hr₀.le)))] at hev
      obtain ⟨ρ, hρ, hρs⟩ := Metric.eventually_nhds_iff.1 hev
      refine ⟨min (ρ / 2) r₀, lt_min (by positivity) hr₀, fun r hr hrρ => ?_⟩
      refine integral_moll_le_of_le hr (hiu r hr (hrρ.trans (min_le_right _ _))) fun y hy => ?_
      refine (hρs ?_).le
      rw [dist_eq_norm, add_sub_cancel_left]
      linarith [min_le_left (ρ / 2) r₀]
    -- (E) lower semicontinuity of `Φ`
    have hE : ∀ b : ℝ, (b : EReal) < logPotential μ z → ∃ ρ > 0, ∀ r, 0 < r → r ≤ ρ →
        b ≤ ∫ y, (logPotential μ (z + y)).toReal * moll r y := by
      intro b hb
      have hlsc := lowerSemicontinuous_logPotential hμ1 z b hb
      obtain ⟨ρ, hρ, hρs⟩ := Metric.eventually_nhds_iff.1 hlsc
      refine ⟨min (ρ / 2) r₀, lt_min (by positivity) hr₀, fun r hr hrρ => ?_⟩
      refine le_integral_moll_of_le hr (hiΦ r hr (hrρ.trans (min_le_right _ _))) ?_
      filter_upwards [hfinΦ] with y hy hyr
      have hlt : (b : EReal) < logPotential μ (z + y) := hρs (by
        rw [dist_eq_norm, add_sub_cancel_left]
        linarith [min_le_left (ρ / 2) r₀])
      have e : ((logPotential μ (z + y)).toReal : EReal) = logPotential μ (z + y) :=
        EReal.coe_toReal hy (logPotential_ne_bot μ _)
      rw [← e, EReal.coe_lt_coe_iff] at hlt
      exact hlt.le
    -- `Φ_μ(z)` is finite
    have hΦtop : logPotential μ z ≠ ⊤ := by
      intro htop
      obtain ⟨ρ, hρ, hρr⟩ := hE (h z - u z + 1) (by rw [htop]; exact EReal.coe_lt_top _)
      set r := min ρ r₀ with hr
      have hr0 : 0 < r := lt_min hρ hr₀
      have h1 := hρr r hr0 (min_le_left _ _)
      have h2 := hB r hr0 (min_le_right _ _)
      rw [hA r hr0 (min_le_right _ _)] at h2
      linarith
    obtain ⟨p, hp⟩ : ∃ p : ℝ, logPotential μ z = p :=
      ⟨_, (EReal.coe_toReal hΦtop (logPotential_ne_bot μ z)).symm⟩
    -- `p = h z - u z`
    have hle : p ≤ h z - u z := by
      refine le_of_forall_ge_of_dense fun b hb => ?_
      obtain ⟨ρ, hρ, hρr⟩ := hE b (by rw [hp]; exact EReal.coe_lt_coe_iff.2 hb)
      set r := min ρ r₀ with hr
      have hr0 : 0 < r := lt_min hρ hr₀
      have h1 := hρr r hr0 (min_le_left _ _)
      have h2 := hB r hr0 (min_le_right _ _)
      rw [hA r hr0 (min_le_right _ _)] at h2
      linarith
    have hge' : h z - p ≤ u z := by
      refine le_of_forall_le_of_dense fun a ha => ?_
      obtain ⟨ρ, hρ, hρr⟩ := hD a ha
      set r := min ρ r₀ with hr
      have hr0 : 0 < r := lt_min hρ hr₀
      have h1 := hρr r hr0 (min_le_left _ _)
      have h3 := hC r hr0 (min_le_right _ _)
      rw [hp, EReal.coe_le_coe_iff] at h3
      rw [hA r hr0 (min_le_right _ _)] at h1
      linarith
    have hge : h z - u z ≤ p := by linarith
    rw [hp, show p = h z - u z from le_antisymm hle hge]
    rw [← EReal.coe_neg, ← EReal.coe_add]
    congr 1
    ring
  · ----------------------------------------------------------------------------------------
    -- uniqueness
    rintro μ' ⟨hμ'fin, hμ'U', h', hh', hid'⟩
    have hμ'S : μ' (closedBall 0 S)ᶜ = 0 := measure_mono_null (compl_subset_compl.2 hU'S) hμ'U'
    have hμ'1 := integrable_norm_of_bounded hμ'S
    -- the pointwise identity for `μ` (proved above) is not available here, so we use the
    -- distributional characterisation of `μ` directly
    have hΦ'S : IntegrableOn (fun z => (logPotential μ' z).toReal) (closedBall 0 S) :=
      integrableOn_logPotential hμ'S S
    refine measure_eq_of_integral_eq hU' hμ'U' hμU' fun ψ hψ hψc hψU' => ?_
    have hΔ0 : ∀ z, z ∉ U' → Δ ψ z = 0 := fun z hz =>
      laplacian_eq_zero_of_notMem hψ fun h => hz (hψU' h)
    -- on `U'`, `u = -Φ_{μ'} + h'`, so `u + Φ_{μ'} = h'`
    have hpt : ∀ z ∈ U', u z + (logPotential μ' z).toReal = h' z := by
      intro z hz
      have hz' := hid' z hz
      have htop : logPotential μ' z ≠ ⊤ := by
        intro ht
        rw [ht, EReal.neg_top, EReal.bot_add] at hz'
        exact EReal.coe_ne_bot _ hz'
      obtain ⟨q, hq⟩ : ∃ q : ℝ, logPotential μ' z = q :=
        ⟨_, (EReal.coe_toReal htop (logPotential_ne_bot μ' z)).symm⟩
      rw [hq, ← EReal.coe_neg, ← EReal.coe_add, EReal.coe_eq_coe_iff] at hz'
      rw [hq, EReal.toReal_coe, hz']
      ring
    have hi1 : Integrable (fun z => u z * Δ ψ z) :=
      integrable_u_laplacian hcl huC hψ (hψU'.trans subset_closure)
    have hi2 : Integrable (fun z => (logPotential μ' z).toReal * Δ ψ z) :=
      integrable_u_laplacian (isCompact_closedBall 0 S) hΦ'S hψ (hψU'.trans hU'S)
    have hharm : ∫ z, h' z * Δ ψ z = 0 := integral_harmonic_mul_laplacian hU' hh' hψ hψc hψU'
    have e : ∫ z, h' z * Δ ψ z =
        (∫ z, u z * Δ ψ z) + ∫ z, (logPotential μ' z).toReal * Δ ψ z := by
      rw [← integral_add hi1 hi2]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      by_cases hz : z ∈ U'
      · simp only [← hpt z hz]; ring
      · simp only [hΔ0 z hz, mul_zero, add_zero]
    rw [hharm, hkey ψ hψ hψc hψU', integral_logPotential_mul_laplacian hμ'S hψ hψc] at e
    have hπ : (0 : ℝ) < 2 * π := by positivity
    have e2 : 2 * π * ((∫ z, ψ z ∂μ') - ∫ z, ψ z ∂μ) = 0 := by linarith
    rcases mul_eq_zero.1 e2 with h0 | h0
    · linarith
    · linarith

end DF
