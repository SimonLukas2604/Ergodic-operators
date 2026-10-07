/-
Copyright (c) 2026. Formalization of
  S. Becker, "Self-dual perturbations of the critical almost Mathieu operator:
  Dry Ten Martini and Hausdorff dimension" (Paper II).

# Reducing the transfer input  (Prop 3.9 `gap:prop:transfer`)

The transfer input of `MainTheorems` is reduced here to smaller, more primitive inputs,
following the paper's proof; the reduction step is proved.

The paper proves Prop 3.9 from
* the displayed identity (`gap:eq:spectral-ids-transfer`) — trace inertia (Paper I Lemma 2.9)
  together with atomlessness of the comparison IDS (Paper I Lemma 2.8):
  `g(E) ∈ spec H_{b(E)}`, `N_R(E) = N_{b(E)}(g(E))`, `τ 1_{E}(H_R) = 0` on `spec H_R`
  (`InertiaTransferClaim`);
* stability of comparison gaps: a closed interval in a comparison gap stays in the resolvent
  for nearby `b` (uniform Neumann bound) and the IDS there does not change (equivalent lower
  projections) (`ComparisonStabilityClaim`);
* the comparison theorem (`ComparisonClaim`).

The rest — the level set `N_R^{-1}(ℓ)` is a compact interval, a nondegenerate one is a gap by
full spectral support (proved in Paper I, `AMO.dos_support`), and a degenerate one contradicts
the continuity of `g` — is proved here (`transfer_of_inertia`).

`PaperIIInputsRefined` bundles the refined inputs and `PaperIIInputsRefined.toInputs` produces
`PaperIIInputs`, so Theorems 1.1, 1.2, 3.10 hold under the refined inputs
(`thm_joint_refined`, `thm_liouville_refined`, `thm_finite_exponent_refined`).
-/
import SpectralGapsDimension.MainTheorems

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace SGD

open AMO

/-! ### The comparison symbol -/

lemma Dsym_summable : SymbolSummable Dsym := by
  unfold SymbolSummable
  apply summable_of_ne_finset_zero (s := {(1, 1), (1, -1), (-1, 1), (-1, -1)})
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
  simp [Dsym, Pi.single_apply, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2]

lemma Dsym_selfAdjoint : SymbolSelfAdjoint Dsym := by
  intro p
  obtain ⟨a, b⟩ := p
  simp only [Dsym, Pi.add_apply, Pi.single_apply, Prod.mk.injEq, Prod.neg_mk, map_add]
  split_ifs <;> simp_all <;> omega

lemma smul_Dsym_summable (b : ℝ) : SymbolSummable ((b : ℂ) • Dsym) := by
  unfold SymbolSummable
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
  exact Dsym_summable.mul_left _

lemma smul_Dsym_selfAdjoint (b : ℝ) : SymbolSelfAdjoint ((b : ℂ) • Dsym) := by
  intro p
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal, Dsym_selfAdjoint p]

/-! ### Transfer from trace inertia -/

/-- **The transferred spectral identity** (`gap:eq:spectral-ids-transfer`), obtained in the
paper from trace inertia (Lemma 3.7 = Paper I Lemma 2.9) and the covariant-IDS lemma (Paper I
Lemma 2.8) for the comparison family: under the hypotheses of Prop 3.9, the DOS measure of `H_R`
has no atom on `spec H_R`, and at every spectral energy `g(E) ∈ spec H_{b(E)}` and
`N_R(E) = N_{b(E)}(g(E))`. -/
def InertiaTransferClaim : Prop :=
  ∀ {α : ℝ} (hα : Irrational α) {R : Symbol} (hR : SelfDual R) (hRs : SymbolSummable R)
    {s : ℝ} (hs : 0 < s) (b g : ℝ → ℝ) (G Ginv : ℝ → Symbol)
    (hG : ∀ E ∈ Sigma α 1 R, NormalForm α s R (G E) (Ginv E) E (b E) (g E) ∧ |b E| < 1 / 2),
    ∃ ν : Measure ℝ, IsDOSMeasure (H α 1 R) ν ∧ ∀ E ∈ Sigma α 1 R, ν {E} = 0 ∧
      g E ∈ Sigma α 1 ((b E : ℂ) • Dsym) ∧
      ∀ νb : Measure ℝ, IsDOSMeasure (H α 1 ((b E : ℂ) • Dsym)) νb → IDS ν E = IDS νb (g E)

/-- **Stability of comparison gaps** (proof of Prop 3.9): if `[c,d]` lies in a gap of `H_{b₀}`,
then for `b` near `b₀` it stays in the resolvent of `H_b` (uniform Neumann bound) and the IDS
at `c` is unchanged (the lower spectral projections vary in norm and are equivalent). -/
def ComparisonStabilityClaim : Prop :=
  ∀ {α : ℝ} (hα : Irrational α) {b₀ c d : ℝ} (hb₀ : |b₀| < 1 / 2) (hcd : c < d)
    (hgap : Icc c d ∩ Sigma α 1 ((b₀ : ℂ) • Dsym) = ∅),
    ∃ δ > 0, ∀ b : ℝ, |b - b₀| < δ → |b| < 1 / 2 →
      Icc c d ∩ Sigma α 1 ((b : ℂ) • Dsym) = ∅ ∧
      ∀ ν ν₀ : Measure ℝ, IsDOSMeasure (H α 1 ((b : ℂ) • Dsym)) ν →
        IsDOSMeasure (H α 1 ((b₀ : ℂ) • Dsym)) ν₀ → IDS ν c = IDS ν₀ c

lemma fract_mem_Ioo {α : ℝ} (hα : Irrational α) {n : ℤ} (hn : n ≠ 0) :
    0 < Int.fract ((n : ℝ) * α) ∧ Int.fract ((n : ℝ) * α) < 1 := by
  refine ⟨lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm fun h => ?_), Int.fract_lt_one _⟩
  have hirr : Irrational ((n : ℝ) * α) := hα.intCast_mul hn
  refine hirr ⟨(⌊(n : ℝ) * α⌋ : ℚ), ?_⟩
  have := Int.self_sub_floor ((n : ℝ) * α)
  push_cast
  rw [Int.fract] at h
  linarith

/-- **Proposition 3.9 (`gap:prop:transfer`), reduced.**  The transfer proposition follows from
the comparison theorem, the transferred spectral identity and the stability of comparison gaps.
The level-set argument and the continuity contradiction of the paper's proof are proved here. -/
theorem transfer_of_inertia (hcompC : ComparisonClaim) (hI : InertiaTransferClaim)
    (hstab : ComparisonStabilityClaim) : TransferClaim := by
  intro α hα _hcomp R hR hRs s hs b g hb hg G Ginv hG
  obtain ⟨ν, hν, hνE⟩ := hI hα hR hRs hs b g G Ginv hG
  haveI := hν.1
  set Sig := Sigma α 1 R with hSig
  obtain ⟨E', hE'⟩ := Sigma_nonempty α hRs hR.1
  have hSc : ν Sigᶜ = 0 := (dos_support hα hRs hR.1 hν hE' one_pos).2
  have hat : ∀ E, ν {E} = 0 := fun E => by
    by_cases hE : E ∈ Sig
    · exact (hνE E hE).1
    · exact measure_mono_null (singleton_subset_iff.2 hE) hSc
  have hsupp : ∀ E ∈ Sig, ∀ ε > 0, 0 < ν (Ioo (E - ε) (E + ε)) :=
    fun E hE ε hε => (dos_support hα hRs hR.1 hν hE hε).1
  refine ⟨ν, hν, fun n hn => ?_⟩
  obtain ⟨hℓ0, hℓ1⟩ := fract_mem_Ioo hα hn
  rcases level_set_dichotomy (spectrum_real_isClosed _) hSc hat hsupp hℓ0 hℓ1 with
    hgap | ⟨E₀, hE₀S, hE₀, hbel, habo⟩
  · exact hgap
  exfalso
  obtain ⟨Em, Ep, hEmS, hEpS, hEm, hEp, hNm, hNp⟩ := exists_seq_sides hSc hat hE₀ hbel habo
  -- the comparison gap with label `ℓ` at `b₀ = b(E₀)`
  have hb₀ : |b E₀| < 1 / 2 := (hG E₀ hE₀S).2
  obtain ⟨ν₀, hν₀, hgaps₀⟩ := hcompC hα hb₀
  obtain ⟨a', b', hab, -, -, hIoo, hIDS⟩ := hgaps₀ n hn
  set c := (2 * a' + b') / 3
  set d := (a' + 2 * b') / 3
  have hcd : c < d := by simp only [c, d]; linarith
  have hgap : Icc c d ∩ Sigma α 1 ((b E₀ : ℂ) • Dsym) = ∅ := by
    refine eq_empty_iff_forall_notMem.2 fun t ⟨ht, htS⟩ => ?_
    have : t ∈ Ioo a' b' ∩ Sigma α 1 ((b E₀ : ℂ) • Dsym) :=
      ⟨⟨by simp only [c] at ht; linarith [ht.1], by simp only [d] at ht; linarith [ht.2]⟩, htS⟩
    rw [hIoo] at this
    exact this
  have hℓc : IDS ν₀ c = Int.fract ((n : ℝ) * α) :=
    hIDS c ⟨by simp only [c]; linarith, by simp only [c]; linarith⟩
  obtain ⟨δ, hδ, hst⟩ := hstab hα hb₀ hcd hgap
  -- at spectral energies with `b(E)` close to `b₀`, `g(E)` avoids `[c, d]` on the correct side
  have key : ∀ E ∈ Sig, |b E - b E₀| < δ →
      (IDS ν E < Int.fract ((n : ℝ) * α) → g E < c) ∧
      (Int.fract ((n : ℝ) * α) < IDS ν E → d < g E) := by
    intro E hE hbE
    have hbE' : |b E| < 1 / 2 := (hG E hE).2
    obtain ⟨hres, hlab⟩ := hst (b E) hbE hbE'
    obtain ⟨νE, hνE', -⟩ := hcompC hα hbE'
    haveI := hνE'.1
    have hc' : IDS νE c = Int.fract ((n : ℝ) * α) := (hlab νE ν₀ hνE' hν₀).trans hℓc
    obtain ⟨E'', hE''⟩ := Sigma_nonempty α (smul_Dsym_summable (b E)) (smul_Dsym_selfAdjoint _)
    have hSb : νE (Sigma α 1 ((b E : ℂ) • Dsym))ᶜ = 0 :=
      (dos_support hα (smul_Dsym_summable _) (smul_Dsym_selfAdjoint _) hνE' hE'' one_pos).2
    have hconst : ∀ t ∈ Icc c d, IDS νE t = Int.fract ((n : ℝ) * α) := by
      intro t ht
      have h0 : νE (Ioc c t) = 0 := by
        refine measure_mono_null
          (show Ioc c t ⊆ (Sigma α 1 ((b E : ℂ) • Dsym))ᶜ from fun x hx hxS => ?_) hSb
        have : x ∈ Icc c d ∩ Sigma α 1 ((b E : ℂ) • Dsym) := ⟨⟨hx.1.le, hx.2.trans ht.2⟩, hxS⟩
        rw [hres] at this
        exact this
      rw [measure_Ioc_eq_IDS] at h0
      have h1 := ENNReal.ofReal_eq_zero.1 h0
      have h2 := IDS_mono (ν := νE) ht.1
      rw [← hc']
      linarith
    have hspec := (hνE E hE).2.1
    have heq := (hνE E hE).2.2 νE hνE'
    constructor
    · intro hlt
      by_contra hge
      push_neg at hge
      by_cases hgd : g E ≤ d
      · have : g E ∈ Icc c d ∩ Sigma α 1 ((b E : ℂ) • Dsym) := ⟨⟨hge, hgd⟩, hspec⟩
        rw [hres] at this
        exact this
      · have h1 := IDS_mono (ν := νE) (le_of_lt (not_le.1 hgd))
        rw [hconst d ⟨hcd.le, le_rfl⟩] at h1
        rw [heq] at hlt
        linarith
    · intro hgt
      by_contra hle
      push_neg at hle
      by_cases hgc : c ≤ g E
      · have : g E ∈ Icc c d ∩ Sigma α 1 ((b E : ℂ) • Dsym) := ⟨⟨hgc, hle⟩, hspec⟩
        rw [hres] at this
        exact this
      · have h1 := IDS_mono (ν := νE) (le_of_lt (not_le.1 hgc))
        rw [hconst c ⟨le_rfl, hcd.le⟩] at h1
        rw [heq] at hgt
        linarith
  -- continuity of `b` and `g` on `Σ` at `E₀`
  have hwithin : ∀ {E : ℕ → ℝ}, (∀ j, E j ∈ Sig) → Tendsto E atTop (𝓝 E₀) →
      Tendsto E atTop (𝓝[Sig] E₀) := fun hS hE =>
    tendsto_nhdsWithin_iff.2 ⟨hE, Eventually.of_forall hS⟩
  have hbclose : ∀ {E : ℕ → ℝ}, (∀ j, E j ∈ Sig) → Tendsto E atTop (𝓝 E₀) →
      ∀ᶠ j in atTop, |b (E j) - b E₀| < δ := fun hS hE => by
    have := ((hb E₀ hE₀S).tendsto.comp (hwithin hS hE))
    have h2 := (Metric.tendsto_nhds.1 this) δ hδ
    filter_upwards [h2] with j hj
    simpa [Real.dist_eq] using hj
  have hlow : ∀ᶠ j in atTop, g (Em j) < c := by
    filter_upwards [hbclose hEmS hEm] with j hj
    exact (key _ (hEmS j) hj).1 (hNm j)
  have hhigh : ∀ᶠ j in atTop, d < g (Ep j) := by
    filter_upwards [hbclose hEpS hEp] with j hj
    exact (key _ (hEpS j) hj).2 (hNp j)
  have hgm : Tendsto (fun j => g (Em j)) atTop (𝓝 (g E₀)) :=
    (hg E₀ hE₀S).tendsto.comp (hwithin hEmS hEm)
  have hgp : Tendsto (fun j => g (Ep j)) atTop (𝓝 (g E₀)) :=
    (hg E₀ hE₀S).tendsto.comp (hwithin hEpS hEp)
  have h1 : g E₀ ≤ c := le_of_tendsto hgm (hlow.mono fun j hj => hj.le)
  have h2 : d ≤ g E₀ := ge_of_tendsto hgp (hhigh.mono fun j hj => hj.le)
  linarith

/-! ### Persistence of comparison gaps (proved)

The first half of `ComparisonStabilityClaim` — a closed interval in a comparison gap stays in the
resolvent of `H_b` for `b` near `b₀` — is proved here from `‖H_b - H_{b₀}‖ ≤ 4|b - b₀|` and
spectral stability for normal operators (Paper I, `AMO.exists_mem_spectrum_dist_le`).  Only the
second half, constancy of the label, remains an input (`ComparisonLabelStabilityClaim`). -/

lemma Dsym_tsum_norm : ∑' p, ‖Dsym p‖ = 4 := by
  rw [tsum_eq_sum (s := {(1, 1), (1, -1), (-1, 1), (-1, -1)})]
  · simp [Dsym, Pi.single_apply]
    norm_num
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
    simp [Dsym, Pi.single_apply, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2]

/-- `‖H_b - H_{b₀}‖ ≤ 4 |b - b₀|` for the comparison family. -/
lemma norm_H_comparison_sub (α b b₀ x : ℝ) :
    ‖H α 1 ((b : ℂ) • Dsym) x - H α 1 ((b₀ : ℂ) • Dsym) x‖ ≤ 4 * |b - b₀| := by
  have hsplit : amo ((1 : ℝ) : ℂ) + (b : ℂ) • Dsym =
      (amo ((1 : ℝ) : ℂ) + (b₀ : ℂ) • Dsym) + ((b - b₀ : ℝ) : ℂ) • Dsym := by
    ext p
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  have h1 : H α 1 ((b : ℂ) • Dsym) x =
      H α 1 ((b₀ : ℂ) • Dsym) x + op α (((b - b₀ : ℝ) : ℂ) • Dsym) x := by
    unfold H
    rw [hsplit, op_add ((amo_summable _).add (smul_Dsym_summable b₀)) (smul_Dsym_summable _)]
  rw [h1, add_sub_cancel_left]
  refine (norm_op_le (smul_Dsym_summable _) x).trans ?_
  have h2 : ∑' p, ‖(((b - b₀ : ℝ) : ℂ) • Dsym) p‖ = |b - b₀| * ∑' p, ‖Dsym p‖ := by
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [tsum_mul_left]
  rw [h2, Dsym_tsum_norm]
  linarith

/-- **Persistence of comparison gaps.**  If `[c, d]` lies in the resolvent of `H_{b₀}`, it lies in
the resolvent of `H_b` for all `b` near `b₀`. -/
theorem comparison_resolvent_persists {α b₀ c d : ℝ}
    (hgap : Icc c d ∩ Sigma α 1 ((b₀ : ℂ) • Dsym) = ∅) :
    ∃ δ > 0, ∀ b : ℝ, |b - b₀| < δ → Icc c d ∩ Sigma α 1 ((b : ℂ) • Dsym) = ∅ := by
  obtain ⟨r, hr, hsep⟩ := Metric.exists_pos_forall_lt_edist isCompact_Icc
    (spectrum_real_isClosed _) (Set.disjoint_iff_inter_eq_empty.2 hgap)
  refine ⟨(r : ℝ) / 4, by positivity, fun b hb => eq_empty_iff_forall_notMem.2 ?_⟩
  rintro E ⟨hE, hES⟩
  have hsa₀ := isSelfAdjoint_H α 1 (smul_Dsym_summable b₀) (smul_Dsym_selfAdjoint b₀) 0
  haveI : IsStarNormal (H α 1 ((b₀ : ℂ) • Dsym) 0) := hsa₀.isStarNormal
  have hEc : (E : ℂ) ∈ spectrum ℂ (H α 1 ((b : ℂ) • Dsym) 0) := by
    have h := hES
    rw [AMO.Sigma, ← spectrum.preimage_algebraMap ℂ] at h
    simpa using h
  obtain ⟨w, hw, hdist⟩ := exists_mem_spectrum_dist_le (a := H α 1 ((b₀ : ℂ) • Dsym) 0) hEc
  have hwre : w = (w.re : ℂ) := hsa₀.mem_spectrum_eq_re hw
  have hwS : w.re ∈ Sigma α 1 ((b₀ : ℂ) • Dsym) := by
    rw [AMO.Sigma, ← spectrum.preimage_algebraMap ℂ]
    simp only [mem_preimage, Complex.coe_algebraMap]
    rw [← hwre]
    exact hw
  have h1 : |E - w.re| ≤ ‖H α 1 ((b₀ : ℂ) • Dsym) 0 - H α 1 ((b : ℂ) • Dsym) 0‖ := by
    have : |E - w.re| = |((E : ℂ) - w).re| := by simp
    rw [this]
    exact (Complex.abs_re_le_norm _).trans hdist
  have h2 : ‖H α 1 ((b₀ : ℂ) • Dsym) 0 - H α 1 ((b : ℂ) • Dsym) 0‖ ≤ 4 * |b - b₀| := by
    rw [norm_sub_rev]
    exact norm_H_comparison_sub α b b₀ 0
  have h3 := hsep E hE w.re hwS
  rw [edist_dist, Real.dist_eq, ← ENNReal.ofReal_coe_nnreal] at h3
  have h4 : (r : ℝ) < |E - w.re| := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg r.2).1 h3
  linarith

/-- **Constancy of comparison labels** (proof of Prop 3.9: "the lower projections at a point of
this interval vary in norm and are equivalent, so their trace remains exactly `ℓ`"): if `[c, d]`
lies in a gap of `H_{b₀}`, then for `b` near `b₀` with `[c, d]` still in the resolvent of `H_b`,
the IDS at `c` is unchanged. -/
def ComparisonLabelStabilityClaim : Prop :=
  ∀ {α : ℝ} (hα : Irrational α) {b₀ c d : ℝ} (hb₀ : |b₀| < 1 / 2) (hcd : c < d)
    (hgap : Icc c d ∩ Sigma α 1 ((b₀ : ℂ) • Dsym) = ∅),
    ∃ δ > 0, ∀ b : ℝ, |b - b₀| < δ → |b| < 1 / 2 →
      Icc c d ∩ Sigma α 1 ((b : ℂ) • Dsym) = ∅ →
      ∀ ν ν₀ : Measure ℝ, IsDOSMeasure (H α 1 ((b : ℂ) • Dsym)) ν →
        IsDOSMeasure (H α 1 ((b₀ : ℂ) • Dsym)) ν₀ → IDS ν c = IDS ν₀ c

theorem comparisonStability_of_label (h : ComparisonLabelStabilityClaim) :
    ComparisonStabilityClaim := by
  intro α hα b₀ c d hb₀ hcd hgap
  obtain ⟨δ₁, hδ₁, hres⟩ := comparison_resolvent_persists hgap
  obtain ⟨δ₂, hδ₂, hlab⟩ := h hα hb₀ hcd hgap
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun b hb hb' => ?_⟩
  have h1 := hres b (hb.trans_le (min_le_left _ _))
  exact ⟨h1, hlab b (hb.trans_le (min_le_right _ _)) hb' h1⟩

/-! ### Refined inputs and the main theorems -/

/-- The refined inputs: `TransferClaim` is replaced by `InertiaTransferClaim` and
`ComparisonLabelStabilityClaim`. -/
structure PaperIIInputsRefined : Prop where
  comparison : ComparisonClaim
  normalization : NormalizationClaim
  inertiaTransfer : InertiaTransferClaim
  comparisonLabelStability : ComparisonLabelStabilityClaim
  infiniteExponent : InfiniteExponentClaim
  brjunoCover : BrjunoCoverClaim
  packetCover : PacketCoverClaim
  atomlessIDS : AtomlessIDSClaim

theorem PaperIIInputsRefined.toInputs (P : PaperIIInputsRefined) : PaperIIInputs where
  comparison := P.comparison
  normalization := P.normalization
  transfer := transfer_of_inertia P.comparison P.inertiaTransfer
    (comparisonStability_of_label P.comparisonLabelStability)
  infiniteExponent := P.infiniteExponent
  brjunoCover := P.brjunoCover
  packetCover := P.packetCover
  atomlessIDS := P.atomlessIDS

/-- **Theorem 1.1** under the refined inputs. -/
theorem thm_joint_refined (P : PaperIIInputsRefined) {α : ℝ} (hα : Irrational α) :
    ∃ Sstar > 0, ∀ S ≥ Sstar, ∃ ρ > 0, ∀ R : Symbol, SelfDual R → WSmall S S R ρ →
      AllLabelsOpen α R ∧ μH[1 / 2] (Sigma α 1 R) < ⊤ ∧ dimH (Sigma α 1 R) ≤ 1 / 2 ∧
        IsCantor (Sigma α 1 R) ∧ volume (Sigma α 1 R) = 0 :=
  thm_joint P.toInputs hα

/-- **Theorem 1.2** under the refined inputs. -/
theorem thm_liouville_refined (P : PaperIIInputsRefined) {α : ℝ} (hα : Irrational α)
    (hL : Liouville α) {S : ℝ} (hS : 0 < S) :
    ∃ ρ > 0, ∀ R : Symbol, SelfDual R → WSmall S S R ρ →
      dimH (Sigma α 1 R) = 0 ∧ IsCantor (Sigma α 1 R) ∧ volume (Sigma α 1 R) = 0 :=
  thm_liouville P.toInputs hα hL hS

/-- **Theorem 3.10** under the refined inputs. -/
theorem thm_finite_exponent_refined (P : PaperIIInputsRefined) {α : ℝ} (hα : Irrational α)
    (hβ : AMO.beta α < ⊤) :
    ∃ Sgap > 0, ∀ S ≥ Sgap, ∃ ρ > 0, ∀ R : Symbol, SelfDual R → WSmall S S R ρ →
      AllLabelsOpen α R :=
  thm_finite_exponent P.toInputs hα hβ

end SGD
