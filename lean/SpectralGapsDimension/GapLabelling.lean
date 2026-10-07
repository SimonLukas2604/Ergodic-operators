/-
Copyright (c) 2026. Formalization of
  S. Becker, "Self-dual perturbations of the critical almost Mathieu operator:
  Dry Ten Martini and Hausdorff dimension" (Paper II).

# Constancy of comparison labels from the gap-labelling theorem

The proof of Prop 3.9 uses that the IDS of the comparison operator `H_b = H_0 + bD` at a point `c`
of a gap does not change when `b` moves a little (`ComparisonLabelStabilityClaim`; the paper argues
with equivalent spectral projections).  Here this is reduced to the classical **gap-labelling
theorem** for the irrational rotation algebra (Bellissard; Pimsner–Voiculescu, Rieffel), stated as
`GapLabellingClaim`: at a point of the resolvent set the IDS lies in `ℤ + αℤ`.

The reduction (`comparisonLabelStability_of_gapLabelling`) is proved:
1. if `[c, d]` is in the resolvent of `H_b`, then `N_b(c) = ∫ f dν_b` for a fixed continuous cutoff
   `f` (`1` on `(-∞, c]`, `0` on `[d, ∞)`), i.e. `N_b(c) = g(b) := ∫₀¹ re⟪δ₀, f(H_{b,x}) δ₀⟫ dx`;
2. `g` is continuous in `b` (joint continuity of `(b, x) ↦ H_{b,x}` and of the functional calculus);
3. by the persistence of comparison gaps (`comparison_resolvent_persists`), `[c, d]` stays in the
   resolvent for `b` in an interval `J` around `b₀`, where the gap-labelling theorem puts `g(b)` in the
   countable set `ℤ + αℤ`;
4. a continuous function on an interval with countable range is constant.
The DOS measures exist by Paper III's `CMS.exists_isDOSMeasure`.
-/
import SpectralGapsDimension.Reductions
import ErgodicShared.IDSAveraging

noncomputable section

open MeasureTheory Filter Topology Set
open scoped BoundedContinuousFunction InnerProductSpace

namespace SGD

open AMO

/-- **The gap-labelling theorem** for the irrational rotation algebra (Bellissard; Pimsner–Voiculescu,
Rieffel): for irrational `α` and a summable self-adjoint symbol `K`, the IDS of `op α K` at any point
of the resolvent set lies in `ℤ + αℤ`.  (Paper II uses it through Lemma 2.2,
`gap:lem:continuous-field-labels`, and the proof of Prop 3.9.) -/
def GapLabellingClaim : Prop :=
  ∀ {α : ℝ}, Irrational α → ∀ {K : Symbol}, SymbolSummable K → SymbolSelfAdjoint K →
    ∀ {ν : Measure ℝ}, IsDOSMeasure (op α K) ν → ∀ c : ℝ, c ∉ spectrum ℝ (op α K 0) →
      ∃ m n : ℤ, IDS ν c = m + n * α

/-! ### A continuous cutoff -/

/-- `f(t) = 1` for `t ≤ c`, `0` for `t ≥ d`, linear in between. -/
def gapCutoff (c d t : ℝ) : ℝ := max 0 (min 1 ((d - t) / (d - c)))

lemma gapCutoff_continuous (c d : ℝ) : Continuous (gapCutoff c d) :=
  continuous_const.max (continuous_const.min ((continuous_const.sub continuous_id).div_const _))

lemma gapCutoff_nonneg (c d t : ℝ) : 0 ≤ gapCutoff c d t := le_max_left _ _

lemma gapCutoff_le_one (c d t : ℝ) : gapCutoff c d t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma gapCutoff_of_le {c d t : ℝ} (hcd : c < d) (ht : t ≤ c) : gapCutoff c d t = 1 := by
  have h1 : 1 ≤ (d - t) / (d - c) := by
    rw [le_div_iff₀ (by linarith)]; linarith
  simp [gapCutoff, min_eq_left h1]

lemma gapCutoff_of_ge {c d t : ℝ} (hcd : c < d) (ht : d ≤ t) : gapCutoff c d t = 0 := by
  have h0 : (d - t) / (d - c) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  simp [gapCutoff, min_eq_right (h0.trans zero_le_one), max_eq_left h0]

/-- The cutoff as a bounded continuous function. -/
def gapCutoffBCF (c d : ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (gapCutoff c d) (gapCutoff_continuous c d) 1
    (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (gapCutoff_nonneg c d t)]
      exact gapCutoff_le_one c d t)

lemma gapCutoffBCF_apply (c d t : ℝ) : gapCutoffBCF c d t = gapCutoff c d t := rfl

/-- If `ν` gives no mass to `(c, d]`, then `N(c) = ∫ f dν`. -/
lemma IDS_eq_integral_gapCutoff {ν : Measure ℝ} [IsProbabilityMeasure ν] {c d : ℝ} (hcd : c < d)
    (h0 : ν (Ioc c d) = 0) : IDS ν c = ∫ t, gapCutoff c d t ∂ν := by
  have hae : (fun t => gapCutoff c d t) =ᵐ[ν] (Iic c).indicator 1 := by
    refine measure_mono_null (fun t ht => ?_) h0
    by_contra hmem
    apply ht
    show gapCutoff c d t = (Iic c).indicator 1 t
    rcases le_or_gt t c with htc | htc
    · rw [gapCutoff_of_le hcd htc, indicator_of_mem (by exact htc), Pi.one_apply]
    · have htd : d < t := lt_of_not_ge fun h => hmem ⟨htc, h⟩
      rw [gapCutoff_of_ge hcd htd.le, indicator_of_notMem (by simpa using htc)]
  rw [integral_congr_ae hae, integral_indicator_one measurableSet_Iic]
  rfl

/-! ### The label function `g(b)` -/

/-- The comparison family as a function of `(b, x)`. -/
def compFam (α : ℝ) (p : ℝ × ℝ) : Op ℤ := H α 1 ((p.1 : ℂ) • Dsym) p.2

lemma compFam_eq (α : ℝ) (p : ℝ × ℝ) :
    compFam α p = H α 1 0 p.2 + (p.1 : ℂ) • op α Dsym p.2 := by
  unfold compFam H
  have hsplit : amo ((1 : ℝ) : ℂ) + (p.1 : ℂ) • Dsym = (amo ((1 : ℝ) : ℂ) + 0) + (p.1 : ℂ) • Dsym := by
    rw [add_zero]
  rw [hsplit, op_add ((amo_summable _).add (by simpa [SymbolSummable] using summable_zero))
    (smul_Dsym_summable p.1), op_smul' α _ Dsym_summable]

lemma continuous_compFam (α : ℝ) : Continuous (compFam α) := by
  have h0 : SymbolSummable (amo ((1 : ℝ) : ℂ) + 0) := by
    simpa using amo_summable ((1 : ℝ) : ℂ)
  have hH : Continuous fun x => H α 1 0 x := continuous_op h0
  have hD : Continuous fun x => op α Dsym x := continuous_op Dsym_summable
  have : compFam α = fun p => H α 1 0 p.2 + (p.1 : ℂ) • op α Dsym p.2 := funext (compFam_eq α)
  rw [this]
  exact (hH.comp continuous_snd).add
    ((Complex.continuous_ofReal.comp continuous_fst).smul (hD.comp continuous_snd))

lemma compFam_isSelfAdjoint (α : ℝ) (p : ℝ × ℝ) : IsSelfAdjoint (compFam α p) :=
  isSelfAdjoint_H α 1 (smul_Dsym_summable p.1) (smul_Dsym_selfAdjoint p.1) p.2

/-- `g(b) = ∫₀¹ re⟪δ₀, f(H_{b,x}) δ₀⟫ dx`. -/
def labelFun (α c d b : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1,
    RCLike.re ⟪delta 0, cfc (fun z : ℂ => ((gapCutoff c d z.re : ℝ) : ℂ)) (compFam α (b, x))
      (delta 0)⟫_ℂ

lemma continuous_labelFun (α c d : ℝ) : Continuous (labelFun α c d) := by
  have hcfc : Continuous fun p : ℝ × ℝ =>
      cfc (fun z : ℂ => ((gapCutoff c d z.re : ℝ) : ℂ)) (compFam α p) :=
    Continuous.cfc_of_mem_nhdsSet _ (s := univ) univ_mem (continuous_compFam α)
      (fun p => (compFam_isSelfAdjoint α p).isStarNormal)
      ((Complex.continuous_ofReal.comp
        ((gapCutoff_continuous c d).comp Complex.continuous_re)).continuousOn)
  have hF : Continuous fun p : ℝ × ℝ => RCLike.re ⟪delta 0,
      cfc (fun z : ℂ => ((gapCutoff c d z.re : ℝ) : ℂ)) (compFam α p) (delta 0)⟫_ℂ :=
    RCLike.continuous_re.comp (continuous_const.inner (hcfc.clm_apply continuous_const))
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun b x => RCLike.re ⟪delta 0,
      cfc (fun z : ℂ => ((gapCutoff c d z.re : ℝ) : ℂ)) (compFam α (b, x)) (delta 0)⟫_ℂ) hF 0 1

/-- If `[c, d]` is in the resolvent of `H_b`, every DOS measure of `H_b` has `N_b(c) = g(b)`. -/
lemma IDS_eq_labelFun {α : ℝ} (hα : Irrational α) {b c d : ℝ} (hcd : c < d)
    (hres : Icc c d ∩ Sigma α 1 ((b : ℂ) • Dsym) = ∅) {ν : Measure ℝ}
    (hν : IsDOSMeasure (H α 1 ((b : ℂ) • Dsym)) ν) : IDS ν c = labelFun α c d b := by
  haveI := hν.1
  obtain ⟨E', hE'⟩ := Sigma_nonempty α (smul_Dsym_summable b) (smul_Dsym_selfAdjoint b)
  have hSc : ν (Sigma α 1 ((b : ℂ) • Dsym))ᶜ = 0 :=
    (dos_support hα (smul_Dsym_summable b) (smul_Dsym_selfAdjoint b) hν hE' one_pos).2
  have h0 : ν (Ioc c d) = 0 := by
    refine measure_mono_null
      (show Ioc c d ⊆ (Sigma α 1 ((b : ℂ) • Dsym))ᶜ from fun t ht htS => ?_) hSc
    have : t ∈ Icc c d ∩ Sigma α 1 ((b : ℂ) • Dsym) := ⟨⟨ht.1.le, ht.2⟩, htS⟩
    rw [hres] at this
    exact this
  rw [IDS_eq_integral_gapCutoff hcd h0]
  exact hν.2 (gapCutoffBCF c d)

/-! ### Continuous functions with countable range on an interval -/

/-- A function continuous on a preconnected subset of `ℝ` with values in a countable set is
constant there. -/
lemma eq_of_continuousOn_countable {J : Set ℝ} (hJ : IsPreconnected J) {g : ℝ → ℝ}
    (hg : ContinuousOn g J) {S : Set ℝ} (hS : S.Countable) (hgS : ∀ b ∈ J, g b ∈ S)
    {b₁ b₂ : ℝ} (h₁ : b₁ ∈ J) (h₂ : b₂ ∈ J) : g b₁ = g b₂ := by
  have himg : IsPreconnected (g '' J) := hJ.image g hg
  have hsub : g '' J ⊆ S := by rintro _ ⟨b, hb, rfl⟩; exact hgS b hb
  by_contra hne
  wlog hlt : g b₁ < g b₂ generalizing b₁ b₂
  · exact this h₂ h₁ (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne))
  have hIcc : Icc (g b₁) (g b₂) ⊆ S :=
    (himg.ordConnected.out (mem_image_of_mem g h₁) (mem_image_of_mem g h₂)).trans hsub
  have hvol : volume (Icc (g b₁) (g b₂)) = 0 := measure_mono_null hIcc (hS.measure_zero volume)
  rw [Real.volume_Icc] at hvol
  have := ENNReal.ofReal_eq_zero.1 hvol
  linarith

/-- The labels `ℤ + αℤ` form a countable set. -/
lemma countable_labels (α : ℝ) : {t : ℝ | ∃ m n : ℤ, t = m + n * α}.Countable := by
  have : {t : ℝ | ∃ m n : ℤ, t = m + n * α} =
      range (fun p : ℤ × ℤ => (p.1 : ℝ) + p.2 * α) := by
    ext t
    simp only [mem_ofPred_eq, mem_range, Prod.exists]
    constructor
    · rintro ⟨m, n, rfl⟩; exact ⟨m, n, rfl⟩
    · rintro ⟨m, n, rfl⟩; exact ⟨m, n, rfl⟩
  rw [this]
  exact countable_range _

/-! ### The reduction -/

/-- **Constancy of comparison labels from gap labelling**: `ComparisonLabelStabilityClaim` follows
from the gap-labelling theorem (DOS measures exist by `CMS.exists_isDOSMeasure`). -/
theorem comparisonLabelStability_of_gapLabelling (hGL : GapLabellingClaim) :
    ComparisonLabelStabilityClaim := by
  intro α hα b₀ c d hb₀ hcd hgap
  obtain ⟨δ, hδ, hres⟩ := comparison_resolvent_persists hgap
  -- the interval `J` of admissible `b`
  set J : Set ℝ := Ioo (b₀ - δ) (b₀ + δ) ∩ Ioo (-(1 / 2)) (1 / 2) with hJ
  have hJpre : IsPreconnected J := by
    rw [hJ, Ioo_inter_Ioo]; exact isPreconnected_Ioo
  have hb₀J : b₀ ∈ J := ⟨⟨by linarith, by linarith⟩, abs_lt.1 hb₀⟩
  have hmemJ : ∀ b, |b - b₀| < δ → |b| < 1 / 2 → b ∈ J := fun b h1 h2 =>
    ⟨⟨by linarith [(abs_lt.1 h1).1], by linarith [(abs_lt.1 h1).2]⟩, abs_lt.1 h2⟩
  -- on `J`, `g(b)` is a gap label
  have hlab : ∀ b ∈ J, labelFun α c d b ∈ {t : ℝ | ∃ m n : ℤ, t = m + n * α} := by
    intro b hb
    have hb1 : |b - b₀| < δ := abs_lt.2 ⟨by linarith [hb.1.1], by linarith [hb.1.2]⟩
    have hresb := hres b hb1
    have hsa : SymbolSelfAdjoint (amo ((1 : ℝ) : ℂ) + (b : ℂ) • Dsym) := by
      intro p
      have h1 := amo_selfAdjoint (1 : ℝ) p
      simp only [Pi.add_apply, map_add, h1, smul_Dsym_selfAdjoint b p]
    obtain ⟨ν, hν⟩ := CMS.exists_isDOSMeasure α ((amo_summable _).add (smul_Dsym_summable b)) hsa
    have hc : c ∉ spectrum ℝ (op α (amo ((1 : ℝ) : ℂ) + (b : ℂ) • Dsym) 0) := fun hc => by
      have : c ∈ Icc c d ∩ Sigma α 1 ((b : ℂ) • Dsym) := ⟨⟨le_rfl, hcd.le⟩, hc⟩
      rw [hresb] at this
      exact this
    obtain ⟨m, n, hmn⟩ := hGL hα ((amo_summable _).add (smul_Dsym_summable b)) hsa hν c hc
    exact ⟨m, n, (IDS_eq_labelFun hα hcd hresb hν).symm.trans hmn⟩
  have hconst : ∀ b ∈ J, labelFun α c d b = labelFun α c d b₀ := fun b hb =>
    eq_of_continuousOn_countable hJpre (continuous_labelFun α c d).continuousOn
      (countable_labels α) hlab hb hb₀J
  refine ⟨δ, hδ, fun b hb hb' hresb ν ν₀ hν hν₀ => ?_⟩
  rw [IDS_eq_labelFun hα hcd hresb hν, IDS_eq_labelFun hα hcd hgap hν₀,
    hconst b (hmemJ b hb hb')]

end SGD
