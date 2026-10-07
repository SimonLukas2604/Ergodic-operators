/-
Copyright (c) 2026. Formalization of
  S. Becker, "Self-dual perturbations of the critical almost Mathieu operator:
  Dry Ten Martini and Hausdorff dimension" (Paper II).

# Constancy of comparison labels, proved

The proof of Prop 3.9 uses that the IDS of the comparison operator `H_b = H_0 + bD` at a point `c`
of a gap does not change when `b` moves a little (`ComparisonLabelStabilityClaim`). The paper argues
that nearby spectral projections are equivalent. `GapLabelling.lean` reduced this to the
gap-labelling theorem. Here it is **proved outright** (`comparisonLabelStability`), so the
gap-labelling theorem is no longer an input of Paper II:

1. if `[c, d]` is in the resolvent of `H_b`, then `P_b(x) = f(H_{b,x})` (`f` the continuous cutoff,
   `1` on `(-∞, c]` and `0` on `[d, ∞)`) is a projection, and `N_b(c) = τ(P_b) = ∫₀¹⟪δ₀, P_b(x) δ₀⟫dx`
   (`IDS_eq_labelFun`);
2. `x ↦ P_b(x)` is a covariant family, and `(b, x) ↦ P_b(x)` is continuous and `1`-periodic in `x`,
   so `‖P_b(x) - P_{b₀}(x)‖ < 1/3` for all `x` once `b` is close to `b₀` (tube lemma);
3. covariant projection families at uniform distance `< 1/3` have the same trace
   (`CMS.tau_eq_of_norm_sub_lt`: they are similar, `P = V Q V⁻¹`, and `τ(AB) = τ(BA)`).
-/
import SpectralGapsDimension.GapLabelling
import SpectralGapsDimension.ComparisonSign
import ErgodicShared.CovariantTrace

noncomputable section

open MeasureTheory Filter Topology Set
open scoped InnerProductSpace

namespace SGD

open AMO CMS

/-- The gap projection family `P_b(x) = f(H_{b,x})`. -/
def gapProj (α c d b x : ℝ) : Op ℤ :=
  cfc (fun z : ℂ => ((gapCutoff c d z.re : ℝ) : ℂ)) (compFam α (b, x))

lemma continuous_gapProj (α c d : ℝ) : Continuous fun p : ℝ × ℝ => gapProj α c d p.1 p.2 :=
  Continuous.cfc_of_mem_nhdsSet _ (s := univ) univ_mem (continuous_compFam α)
    (fun p => (compFam_isSelfAdjoint α p).isStarNormal)
    ((Complex.continuous_ofReal.comp
      ((gapCutoff_continuous c d).comp Complex.continuous_re)).continuousOn)

lemma shiftU_apply_eq (α x : ℝ) (v : L2 ℤ) : shiftU α v = U α x v := by
  ext n
  rw [shiftU_apply, U_apply]

/-- The comparison family is covariant. -/
lemma compFam_intertwines (α b x : ℝ) :
    Intertwines (shiftU α) (compFam α (b, x)) (compFam α (b, x + α)) := by
  intro v
  have hs : SymbolSummable (amo ((1 : ℝ) : ℂ) + (b : ℂ) • Dsym) :=
    (amo_summable _).add (smul_Dsym_summable b)
  show op α _ (x + α) (shiftU α v) = shiftU α (op α _ x v)
  rw [op_conj_U hs x, shiftU_apply_eq α x, shiftU_apply_eq α x]
  simp only [ContinuousLinearMap.comp_apply]
  rw [← ContinuousLinearMap.comp_apply (W α x (-1) 0) (U α x), Uinv_comp_U]
  rfl

/-- `x ↦ P_b(x)` is a covariant family. -/
lemma isCovFam_gapProj (α c d b : ℝ) : IsCovFam α (gapProj α c d b) where
  cont := (continuous_gapProj α c d).comp (continuous_const.prodMk continuous_id)
  periodic x := by
    unfold gapProj compFam
    rw [H_add_one]
  cov x := (compFam_intertwines α b x).cfc _

/-- If `[c, d]` is in the resolvent of `H_b`, every `P_b(x)` is a projection. -/
lemma isStarProjection_gapProj {α : ℝ} (hα : Irrational α) {b c d : ℝ} (hcd : c < d)
    (hres : Icc c d ∩ Sigma α 1 ((b : ℂ) • Dsym) = ∅) (x : ℝ) :
    IsStarProjection (gapProj α c d b x) := by
  set T := compFam α (b, x) with hT
  have hsa : IsSelfAdjoint T := compFam_isSelfAdjoint α (b, x)
  have hspec : spectrum ℝ T = Sigma α 1 ((b : ℂ) • Dsym) :=
    spectrum_H_eq_Sigma hα (smul_Dsym_summable b) (smul_Dsym_selfAdjoint b) x
  have hcont : Continuous fun z : ℂ => ((gapCutoff c d z.re : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((gapCutoff_continuous c d).comp Complex.continuous_re)
  -- on the spectrum, the cutoff takes the values `0` and `1`
  have h01 : ∀ z ∈ spectrum ℂ T,
      ((gapCutoff c d z.re : ℝ) : ℂ) * ((gapCutoff c d z.re : ℝ) : ℂ) =
        ((gapCutoff c d z.re : ℝ) : ℂ) := by
    intro z hz
    have hzr : z.re ∈ Sigma α 1 ((b : ℂ) • Dsym) := by
      rw [← hspec, ← spectrum.preimage_algebraMap ℂ]
      show ((z.re : ℝ) : ℂ) ∈ spectrum ℂ T
      rwa [← hsa.mem_spectrum_eq_re hz]
    have hnot : z.re ∉ Icc c d := fun h => by
      have : z.re ∈ Icc c d ∩ Sigma α 1 ((b : ℂ) • Dsym) := ⟨h, hzr⟩
      rw [hres] at this
      exact this
    rcases lt_or_ge z.re c with hlt | hge
    · rw [gapCutoff_of_le hcd hlt.le]; simp
    · have hd : d < z.re := lt_of_not_ge fun h => hnot ⟨hge, h⟩
      rw [gapCutoff_of_ge hcd hd.le]; simp
  refine ⟨?_, ?_⟩
  · show gapProj α c d b x * gapProj α c d b x = gapProj α c d b x
    unfold gapProj
    rw [← hT, ← cfc_mul _ _ T hcont.continuousOn hcont.continuousOn]
    exact cfc_congr h01
  · unfold gapProj
    rw [IsSelfAdjoint, ← cfc_star]
    refine cfc_congr fun z _ => ?_
    simp

/-- Uniform closeness of `P_b` to `P_{b₀}` for `b` near `b₀` (tube lemma and periodicity). -/
lemma exists_gapProj_near (α c d b₀ : ℝ) :
    ∃ δ > 0, ∀ b, |b - b₀| < δ → ∀ x, ‖gapProj α c d b x - gapProj α c d b₀ x‖ < 1 / 3 := by
  set F : ℝ × ℝ → ℝ := fun p => ‖gapProj α c d p.1 p.2 - gapProj α c d b₀ p.2‖ with hF
  have hFc : Continuous F :=
    ((continuous_gapProj α c d).sub
      ((continuous_gapProj α c d).comp (continuous_const.prodMk continuous_snd))).norm
  have hN : IsOpen (F ⁻¹' Iio (1 / 3)) := isOpen_Iio.preimage hFc
  have hsub : ({b₀} : Set ℝ) ×ˢ Icc (0 : ℝ) 1 ⊆ F ⁻¹' Iio (1 / 3) := by
    rintro ⟨b, x⟩ ⟨hb, -⟩
    rw [mem_singleton_iff] at hb
    subst hb
    simp [F]
  obtain ⟨u, v, hu, -, hb₀u, hv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_Icc hN hsub
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hu b₀ (hb₀u rfl)
  refine ⟨δ, hδ, fun b hb x => ?_⟩
  have hper : ∀ b', Function.Periodic (gapProj α c d b') 1 := fun b' =>
    (isCovFam_gapProj α c d b').periodic
  have hx : x - ⌊x⌋ * 1 ∈ Icc (0 : ℝ) 1 := by
    rw [mul_one]
    exact ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩
  have hmem : (b, x - ⌊x⌋ * 1) ∈ F ⁻¹' Iio (1 / 3) :=
    huv ⟨hball (by rwa [Metric.mem_ball, Real.dist_eq]), hv hx⟩
  change ‖gapProj α c d b (x - ⌊x⌋ * 1) - gapProj α c d b₀ (x - ⌊x⌋ * 1)‖ < 1 / 3 at hmem
  rwa [(hper b).sub_int_mul_eq, (hper b₀).sub_int_mul_eq] at hmem

lemma labelFun_eq_re_tau (α c d b : ℝ) :
    labelFun α c d b = RCLike.re (tau (gapProj α c d b)) := by
  unfold tau
  show ∫ x in (0 : ℝ)..1, RCLike.re ⟪delta 0, gapProj α c d b x (delta 0)⟫_ℂ = _
  exact intervalIntegral.intervalIntegral_re
    (((isCovFam_gapProj α c d b).continuous_inner _ _).intervalIntegrable _ _)

/-- **Constancy of comparison labels** (proof of Prop 3.9), proved: nearby comparison operators
with `[c, d]` in a common gap have the same IDS at `c`. -/
theorem comparisonLabelStability : ComparisonLabelStabilityClaim := by
  intro α hα b₀ c d _ hcd hgap
  obtain ⟨δ, hδ, hnear⟩ := exists_gapProj_near α c d b₀
  refine ⟨δ, hδ, fun b hb _ hresb ν ν₀ hν hν₀ => ?_⟩
  rw [IDS_eq_labelFun hα hcd hresb hν, IDS_eq_labelFun hα hcd hgap hν₀, labelFun_eq_re_tau,
    labelFun_eq_re_tau, tau_eq_of_norm_sub_lt (isCovFam_gapProj α c d b)
      (isCovFam_gapProj α c d b₀) (isStarProjection_gapProj hα hcd hresb)
      (isStarProjection_gapProj hα hcd hgap) (hnear b hb)]

end SGD
