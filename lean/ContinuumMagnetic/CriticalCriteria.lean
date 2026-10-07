/-
# The critical island  (paper Theorem `thm:critical-continuum`, proof in §4.4)

For `μ = 1` and rotation-symmetric wells, Corollary `c-cor:critical` (Lean:
`CMS.fourier_weylSymbol` in `ContinuumMagnetic.Covariance`) makes the exact interaction
self-dual:
`M_h - E_h^0 = a_h (U + U^{-1} + V + V^{-1} + R_h)`, `a_h = f_{1,0} = f_{0,1} ∈ ℝ \ {0}`,
`𝓕(R_h) = R_h`.  This file proves, from the critical input of Papers I and II and the exact
reduction, that

* the island `Σ_h = Φ_h(Σ^crit)`, `Φ_h(E) = E_h^0 + a_h E`, is a Cantor set of measure zero, equal
  to the spectrum of every fibre;
* the full two-dimensional island operator is purely singular continuous (no condition on
  `β(α)`);
* the prepared cocycle has `L(E, y) = 2π|y|` near the real axis;
* for `β(α) > 0` almost every fibre island is purely singular continuous;
* (Paper II) every allowed gap is open — for either sign of `a_h`, using atomlessness of the IDS,
  `𝓗^{1/2}(Σ_h) < ∞`, `dim_H Σ_h ≤ 1/2`, and `dim_H Σ_h = 0` at ordinary Liouville flux.
-/
import ContinuumMagnetic.ScalarCriteria

noncomputable section

open scoped ENNReal NNReal
open MeasureTheory Set Filter AMO

namespace CMS

/-! ### Monotonicity of the analytic norms in the weights -/

lemma _root_.AMO.WSmall.mono_weights {s ℓ s' ℓ' ε : ℝ} {R : Symbol} (hs : s ≤ s') (hℓ : ℓ ≤ ℓ')
    (h : WSmall s' ℓ' R ε) : WSmall s ℓ R ε := by
  have hle : ∀ p : ℤ × ℤ, ‖R p‖ * Real.exp (s * |(p.1 : ℝ)| + ℓ * |(p.2 : ℝ)|) ≤
      ‖R p‖ * Real.exp (s' * |(p.1 : ℝ)| + ℓ' * |(p.2 : ℝ)|) := fun p => by gcongr
  have hsum := h.1.of_nonneg_of_le (fun p => by positivity) hle
  exact ⟨hsum, (hsum.tsum_le_tsum hle h.1).trans_lt h.2⟩

/-! ### Affine maps and Hausdorff measures -/

lemma lipschitz_affine (E₀ a : ℝ) : LipschitzWith ‖a‖₊ (affine E₀ a) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    simp only [affine, Real.dist_eq, coe_nnnorm, Real.norm_eq_abs]
    rw [show E₀ + a * x - (E₀ + a * y) = a * (x - y) by ring, abs_mul]

lemma hausdorffMeasure_affine_lt_top {S : Set ℝ} {d : ℝ} (hd : 0 ≤ d) (h : μH[d] S < ⊤)
    (E₀ a : ℝ) : μH[d] (affine E₀ a '' S) < ⊤ :=
  ((lipschitz_affine E₀ a).hausdorffMeasure_image_le hd S).trans_lt
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg hd ENNReal.coe_ne_top) h)

lemma dimH_affine_le (S : Set ℝ) (E₀ a : ℝ) : dimH (affine E₀ a '' S) ≤ dimH S :=
  (lipschitz_affine E₀ a).dimH_image_le S

/-! ### The critical island symbol -/

/-- The critical island symbol `c = E_h^0 δ₀ + a_h (amo 1 + R)`. -/
def critSym (E₀ a : ℝ) (R : Symbol) : Symbol := affineSym E₀ a (amo 1 + R)

lemma critSym_summable {R : Symbol} (hR : SymbolSummable R) : SymbolSummable (amo 1 + R) :=
  (amo_summable 1).add hR

lemma critSym_selfAdjoint {R : Symbol} (hsa : SymbolSelfAdjoint R) :
    SymbolSelfAdjoint (amo 1 + R) := by
  have h1 : SymbolSelfAdjoint (amo 1) := by simpa using amo_selfAdjoint 1
  intro p
  simp [h1 p, hsa p]

lemma op_critSym (α E₀ a : ℝ) {R : Symbol} (hR : SymbolSummable R) (x : ℝ) :
    op α (critSym E₀ a R) x = affineOp E₀ a (H α 1 R x) :=
  op_affineSym α (critSym_summable hR) E₀ a x

lemma op2_critSym (α E₀ a : ℝ) {R : Symbol} (hR : SymbolSummable R) :
    op2 α (critSym E₀ a R) = affineOp E₀ a (op2 α (amo 1 + R)) :=
  op2_affineSym α (critSym_summable hR) E₀ a

lemma islandSpec_critSym {α E₀ a : ℝ} {R : Symbol} (hα : Irrational α) (hR : SymbolSummable R)
    (hsa : SymbolSelfAdjoint R) (x : ℝ) :
    spectrum ℝ (op α (critSym E₀ a R) x) = affine E₀ a '' Sigma α 1 R := by
  rw [op_critSym α E₀ a hR x, spectrum_affineOp E₀ a (isSelfAdjoint_H α 1 hR hsa x),
    spectrum_H_eq_Sigma hα hR hsa x]

/-! ### Singular continuity from an atomless IDS on a null spectrum -/

/-- If every spectral measure of `K̃` is dominated by an atomless IDS carried by a Lebesgue-null
closed set, then `K̃` is purely singular continuous (paper §4.4, and (hi-eq:type-domination)). -/
lemma purelySC_of_dominated {T : Op (ℤ × ℤ)} {ν : Measure ℝ} {S : Set ℝ}
    (hdom : ∀ ψ, ∃ μ, IsSpectralMeasure T ψ μ ∧ μ ≪ ν) (hat : ∀ t, ν {t} = 0)
    (hS : MeasurableSet S) (hνS : ν Sᶜ = 0) (hvol : volume S = 0) : PurelySC T := by
  intro ψ
  obtain ⟨μ, hμ, hμν⟩ := hdom ψ
  refine ⟨μ, hμ, ?_, fun E _ => hμν (hat E)⟩
  rw [Measure.restrict_univ]
  exact ⟨Sᶜ, hS.compl, hμν hνS, by rwa [compl_compl]⟩

/-! ### Theorem `thm:critical-continuum` -/

variable {Hisl : Type*} [NormedAddCommGroup Hisl] [InnerProductSpace ℂ Hisl] [CompleteSpace Hisl]
  {Hfib : ℝ → Type*} [∀ k, NormedAddCommGroup (Hfib k)] [∀ k, InnerProductSpace ℂ (Hfib k)]
  [∀ k, CompleteSpace (Hfib k)]

/-- **Conclusions of Theorem `thm:critical-continuum`** that need only Paper I. -/
structure CriticalIsland (α E₀ a : ℝ) (R : Symbol)
    (I : IslandReduction α (critSym E₀ a R) Hisl Hfib) : Prop where
  cantor : IsCantor (islandSpec α (critSym E₀ a R))
  every_phase : ∀ x, spectrum ℝ (op α (critSym E₀ a R) x) = islandSpec α (critSym E₀ a R)
  /-- `|Σ_h| = 0`. -/
  null : volume (islandSpec α (critSym E₀ a R)) = 0
  /-- The normalized IDS is atomless. -/
  ids : ∃ ν, IsDOSMeasure (op α (critSym E₀ a R)) ν ∧ ∀ t, ν {t} = 0
  /-- The full two-dimensional island is purely singular continuous, for every irrational flux. -/
  sc2d : PurelySCH I.island
  /-- The prepared cocycle of the signed normalized interaction: `L(E, y) = 2π|y|`
  (paper (2.12)), at the normalized energies `E = (λ - E_h^0)/a_h`. -/
  lyapunov : ∃ ystar > (0 : ℝ), ∀ E ∈ Sigma α 1 R, ∃ P : JacobiPrep α (H α 1 R) E,
    ystar ≤ P.w ∧ ∀ y : ℝ, |y| < ystar → P.L y = 2 * Real.pi * |y|
  /-- If `β(α) > 0`, almost every fibre island is purely singular continuous. -/
  fibres : 0 < beta α → ∀ᵐ k ∂volume, PurelySCH (I.fibre k)

/-- **Theorem `thm:critical-continuum`, Paper I part.**  There are `S > 0`, `ε_c > 0` such that
for every irrational flux, every real `a_h ≠ 0` and every self-dual remainder with
`‖R_h‖_S < ε_c`, every exact reduction of the critical island satisfies `CriticalIsland`. -/
theorem critical_continuum (P : PaperInputs) :
    ∃ S > (0 : ℝ), ∃ εc > (0 : ℝ), ∀ (α E₀ a : ℝ) (R : Symbol), Irrational α → a ≠ 0 →
      SymbolSelfAdjoint R → fourier R = R → WSmall S S R εc →
      ∀ {Hisl : Type} [NormedAddCommGroup Hisl] [InnerProductSpace ℂ Hisl] [CompleteSpace Hisl]
        {Hfib : ℝ → Type} [∀ k, NormedAddCommGroup (Hfib k)]
        [∀ k, InnerProductSpace ℂ (Hfib k)] [∀ k, CompleteSpace (Hfib k)]
        (I : IslandReduction α (critSym E₀ a R) Hisl Hfib), CriticalIsland α E₀ a R I := by
  obtain ⟨S₁, hS₁, ε₁, hε₁, hcrit⟩ := analytic_input_iv P.critical
  obtain ⟨S₂, hS₂, ε₂, hε₂, hids⟩ := P.criticalIDS
  refine ⟨max S₁ S₂, lt_max_of_lt_left hS₁, min ε₁ ε₂, lt_min hε₁ hε₂,
    fun α E₀ a R hα ha hsa hF hsmall => ?_⟩
  intro Hisl _ _ _ Hfib _ _ _ I
  have h₁ : WSmall S₁ S₁ R ε₁ := WSmall.of_le
    (hsmall.mono_weights (le_max_left _ _) (le_max_left _ _)) (min_le_left _ _)
  have h₂ : WSmall S₂ S₂ R ε₂ := WSmall.of_le
    (hsmall.mono_weights (le_max_right _ _) (le_max_right _ _)) (min_le_right _ _)
  have hR : SymbolSummable R := h₁.summable hS₁.le hS₁.le
  obtain ⟨hcantor, hnull, hlyap, hfib⟩ := hcrit α R hα hsa hF h₁
  obtain ⟨ν, hν, hat⟩ := hids α R hα hsa hF h₂
  have hspec := islandSpec_critSym (E₀ := E₀) (a := a) hα hR hsa
  have hSig : islandSpec α (critSym E₀ a R) = affine E₀ a '' Sigma α 1 R := hspec 0
  have hsaH := isSelfAdjoint_H α 1 hR hsa
  have hfun : op α (critSym E₀ a R) = fun x => affineOp E₀ a (H α 1 R x) :=
    funext (op_critSym α E₀ a hR)
  refine ⟨hSig ▸ hcantor.image_affine E₀ ha, fun x => by rw [hspec x, hSig],
    hSig ▸ volume_image_affine ha hnull, ⟨ν.map (affine E₀ a), ?_, ?_⟩, ?_, hlyap, ?_⟩
  · rw [hfun]; exact hν.map_affine hsaH E₀ a
  · intro t
    have hemb : MeasurableEmbedding (affine E₀ a) := (affineHomeomorph E₀ a ha).measurableEmbedding
    rw [hemb.map_apply]
    have : affine E₀ a ⁻¹' {t} = {affine (-E₀ / a) a⁻¹ t} := by
      ext u
      simp only [mem_preimage, mem_singleton_iff]
      constructor
      · rintro rfl; rw [affine_inv ha]
      · rintro rfl; rw [affine_inv' ha]
    rw [this]
    exact hat _
  · -- the full two-dimensional island
    have hK := critSym_summable hR
    have hKsa := critSym_selfAdjoint hsa
    have hcl : IsClosed (Sigma α 1 R) := AMO.spectrum_real_isClosed _
    have hνS : ν (Sigma α 1 R)ᶜ = 0 :=
      dos_compl_eq_zero hν hcl hcantor.1 hsaH (fun x => (spectrum_H_eq_Sigma hα hR hsa x).le)
    have h2 : PurelySC (op2 α (amo 1 + R)) :=
      purelySC_of_dominated (P.regularRep hα hK hKsa hν) hat hcl.measurableSet hνS
        hnull
    have h3 := h2.affineOp (isSelfAdjoint_op2 hK hKsa) E₀ ha
    rw [← op2_critSym α E₀ a hR] at h3
    exact purelySCH_of_purelySC h3 I.reduction
  · intro hβ
    filter_upwards [I.fibre_reduction] with k h2
    have h3 := (hfib hβ ((k + I.θ) / (2 * Real.pi))).affineOp (hsaH _) E₀ ha
    rw [← op_critSym α E₀ a hR] at h3
    exact purelySCH_of_purelySC h3 h2

/-- **Theorem `thm:critical-continuum`, Paper II part** (dry Cantor island and its Hausdorff
size).  For each irrational flux there is a weight `S_*` such that for every `S' ≥ S_*` there is
`ρ > 0` with: every self-dual `R_h` with `‖R_h‖_{S'} < ρ` gives, for either sign of `a_h ≠ 0`,
an island with every internal allowed label `{nα}`, `n ≠ 0`, realized by an open gap,
`𝓗^{1/2}(Σ_h) < ∞` and `dim_H Σ_h ≤ 1/2`.  One threshold works for all labels. -/
theorem critical_continuum_geometry (P : PaperInputs) (α : ℝ) (hα : Irrational α) :
    ∃ Sstar > (0 : ℝ), ∀ S' ≥ Sstar, ∃ ρ > (0 : ℝ), ∀ (E₀ a : ℝ) (R : Symbol), a ≠ 0 →
      SymbolSelfAdjoint R → fourier R = R → WSmall S' S' R ρ →
      (∃ ν, IsDOSMeasure (op α (critSym E₀ a R)) ν ∧
        AllGapsOpen (islandSpec α (critSym E₀ a R)) ν α) ∧
      μH[1 / 2] (islandSpec α (critSym E₀ a R)) < ⊤ ∧
      dimH (islandSpec α (critSym E₀ a R)) ≤ ((1 / 2 : ℝ≥0) : ℝ≥0∞) := by
  obtain ⟨S₂, hS₂, ε₂, hε₂, hids⟩ := P.criticalIDS
  obtain ⟨Sstar, hSstar, hgeo, -⟩ := P.criticalGeometry α hα
  refine ⟨max Sstar S₂, lt_max_of_lt_left hSstar, fun S' hS' => ?_⟩
  obtain ⟨ρ, hρ, hρgeo⟩ := hgeo S' ((le_max_left _ _).trans hS')
  refine ⟨min ρ ε₂, lt_min hρ hε₂, fun E₀ a R ha hsa hF hsmall => ?_⟩
  have h₁ : WSmall S' S' R ρ := WSmall.of_le hsmall (min_le_left _ _)
  have h₂ : WSmall S₂ S₂ R ε₂ := WSmall.of_le
    (hsmall.mono_weights ((le_max_right _ _).trans hS') ((le_max_right _ _).trans hS'))
    (min_le_right _ _)
  have hR : SymbolSummable R := h₂.summable hS₂.le hS₂.le
  obtain ⟨ν, hν, hat⟩ := hids α R hα hsa hF h₂
  obtain ⟨hgaps, hH⟩ := hρgeo R hsa hF h₁
  have hSig : islandSpec α (critSym E₀ a R) = affine E₀ a '' Sigma α 1 R :=
    islandSpec_critSym hα hR hsa 0
  have hsaH := isSelfAdjoint_H α 1 hR hsa
  have hH' : μH[1 / 2] (islandSpec α (critSym E₀ a R)) < ⊤ := by
    rw [hSig]; exact hausdorffMeasure_affine_lt_top (by norm_num) hH E₀ a
  refine ⟨⟨ν.map (affine E₀ a), ?_, ?_⟩, hH', ?_⟩
  · rw [show op α (critSym E₀ a R) = fun x => affineOp E₀ a (H α 1 R x) from
      funext (op_critSym α E₀ a hR)]
    exact hν.map_affine hsaH E₀ a
  · have := hν.1
    rw [hSig]
    exact (hgaps ν hν).map_affine_ne hat hα E₀ ha
  · refine dimH_le_of_hausdorffMeasure_ne_top ?_
    rw [show ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 by norm_num]
    exact hH'.ne

/-- **Theorem `thm:critical-continuum`, ordinary Liouville flux:** `dim_H Σ_h = 0`, for every
fixed weight once `‖R_h‖_{S'}` is small. -/
theorem critical_continuum_liouville (P : PaperInputs) (α : ℝ) (hα : Irrational α)
    (hL : OrdinaryLiouville α) :
    ∀ S' > (0 : ℝ), ∃ ρ > (0 : ℝ), ∀ (E₀ a : ℝ) (R : Symbol), a ≠ 0 →
      SymbolSelfAdjoint R → fourier R = R → WSmall S' S' R ρ →
      dimH (islandSpec α (critSym E₀ a R)) = 0 := by
  obtain ⟨-, -, -, hliou⟩ := P.criticalGeometry α hα
  intro S' hS'
  obtain ⟨ρ, hρ, h⟩ := hliou hL S' hS'
  refine ⟨ρ, hρ, fun E₀ a R ha hsa hF hsmall => ?_⟩
  have hR : SymbolSummable R := hsmall.summable hS'.le hS'.le
  rw [show islandSpec α (critSym E₀ a R) = affine E₀ a '' Sigma α 1 R from
    islandSpec_critSym hα hR hsa 0]
  exact le_antisymm ((dimH_affine_le _ E₀ a).trans (h R hsa hF hsmall).le) zero_le

end CMS
