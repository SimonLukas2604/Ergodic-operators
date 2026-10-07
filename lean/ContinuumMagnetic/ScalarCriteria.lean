/-
# Scalar continuum criteria  (paper §2.1–§2.3 and their proofs in §4)

Theorems `thm:noncritical-continuum`, `thm:continuum-2d-ac`, `thm:continuum-types`,
`thm:continuum-SC` and `thm:critical-continuum`, **proved** from

* the exact reduction of a selected scalar island (paper (2.4)–(2.8)), packaged as the data
  `IslandReduction` below: a unitary `𝒰_h : ℓ²(ℤ²) → Ran P_h` with
  `𝒰_h^* H_h^island 𝒰_h = M̃_h = op2 α c`, and for almost every Bloch phase `k` a unitary
  `𝒰_h(k) : ℓ²(ℤ) → Ran P_h(k)` with `𝒰_h(k)^* H_h(k)|_{Ran P_h(k)} 𝒰_h(k) = M_{h,x(k)}`,
  `x(k) = (k + θ₂)/(2π)` (the axial gauge is included in the unitaries, §4.1);
* the normalization of §4.1: after the axial gauge the symbol is
  `c = E_h^0 δ₀ + t_max K`, with `K = K^sub = amo η + R` if `t₁ > t₂` and
  `K = K^phys = 𝓕(K^sub)` if `t₂ > t₁` (`ScalarIsland`);
* the analytic input of Papers I–II, passed as the hypothesis `P : PaperInputs`
  (`ContinuumMagnetic.AnalyticInput`).

The continuum constructions themselves (existence of the exact reduction and the tunneling
estimates, paper §3) are the content of `ContinuumMagnetic.MainTheorems`.
-/
import ContinuumMagnetic.AnalyticInput
import ContinuumMagnetic.UnitaryTransfer

noncomputable section

open scoped ENNReal
open MeasureTheory Set Filter AMO

namespace CMS

/-! ### Almost every phase -/

/-- A property holding for a.e. phase `x` holds for a.e. Bloch momentum `k`, `x = (k + θ)/(2π)`. -/
lemma ae_phase {P : ℝ → Prop} (h : ∀ᵐ x ∂volume, P x) (θ : ℝ) :
    ∀ᵐ k ∂volume, P ((k + θ) / (2 * Real.pi)) := by
  have hpi : (2 * Real.pi)⁻¹ ≠ 0 := inv_ne_zero (by positivity)
  rw [ae_iff] at h ⊢
  have hpre : {k : ℝ | ¬P ((k + θ) / (2 * Real.pi))} =
      affine (θ / (2 * Real.pi)) (2 * Real.pi)⁻¹ ⁻¹' {x | ¬P x} := by
    ext k
    simp only [mem_setOf_eq, mem_preimage, affine]
    congr! 2
    ring
  rw [hpre]
  exact volume_preimage_affine hpi h

/-! ### Exact reductions -/

variable {Hisl : Type*} [NormedAddCommGroup Hisl] [InnerProductSpace ℂ Hisl] [CompleteSpace Hisl]
  {Hfib : ℝ → Type*} [∀ k, NormedAddCommGroup (Hfib k)] [∀ k, InnerProductSpace ℂ (Hfib k)]
  [∀ k, CompleteSpace (Hfib k)]

/-- **The exact reduction of a scalar island** at fixed `h` (paper (2.4)–(2.8), §4.1–§4.2):
the island operator `H_h^island = H_h|_{Ran 1_{I_h}(H_h)}` is unitarily equivalent to the full
lattice realization `op2 α c`, and almost every physical Bloch fibre restricted to its island
is unitarily equivalent to the phase-`x(k)` fibre `op α c x(k)`. -/
structure IslandReduction (α : ℝ) (c : Symbol) (Hisl : Type*) [NormedAddCommGroup Hisl]
    [InnerProductSpace ℂ Hisl] [CompleteSpace Hisl] (Hfib : ℝ → Type*)
    [∀ k, NormedAddCommGroup (Hfib k)] [∀ k, InnerProductSpace ℂ (Hfib k)]
    [∀ k, CompleteSpace (Hfib k)] where
  /-- The island operator `H_h^island`. -/
  island : Hisl →L[ℂ] Hisl
  /-- The exact global unitary `𝒰_h`. -/
  U : L2 (ℤ × ℤ) ≃ₗᵢ[ℂ] Hisl
  reduction : Intertwines U (op2 α c) island
  /-- The fibre island operators `H_h(k)|_{Ran P_h(k)}`. -/
  fibre : ∀ k, Hfib k →L[ℂ] Hfib k
  /-- The exact fibre unitaries `𝒰_h(k) G_{θ₁}`. -/
  Uk : ∀ k, L2 ℤ ≃ₗᵢ[ℂ] Hfib k
  /-- The constant axial phase `θ₂`. -/
  θ : ℝ
  fibre_reduction : ∀ᵐ k ∂volume, Intertwines (Uk k) (op α c ((k + θ) / (2 * Real.pi))) (fibre k)

/-! ### The normalized island symbol -/

/-- The normalized physical interaction: `K^sub = amo η + R` in the subcritical orientation
(`t₁ > t₂`), and `K^phys = 𝓕(K^sub)` in the supercritical orientation (`t₂ > t₁`). -/
def physSym : Bool → ℝ → Symbol → Symbol
  | true, η, R => amo η + R
  | false, η, R => fourier (amo η + R)

/-- The island symbol `c = E_h^0 δ₀ + t_max K^phys`. -/
def islandSym (E₀ tmax : ℝ) (sub : Bool) (η : ℝ) (R : Symbol) : Symbol :=
  affineSym E₀ tmax (physSym sub η R)

/-- The common island spectrum `Σ_h` (the fibre at phase `0`). -/
def islandSpec (α : ℝ) (c : Symbol) : Set ℝ := spectrum ℝ (op α c 0)

lemma op_physSym_true (α η : ℝ) (R : Symbol) (x : ℝ) : op α (physSym true η R) x = H α η R x :=
  rfl

lemma op_physSym_false (α η : ℝ) (R : Symbol) (x : ℝ) :
    op α (physSym false η R) x = Hdual α η R x := rfl

lemma physSym_summable (sub : Bool) (η : ℝ) {R : Symbol} (hR : SymbolSummable R) :
    SymbolSummable (physSym sub η R) := by
  cases sub
  · exact ((amo_summable η).add hR).fourier
  · exact (amo_summable η).add hR

lemma physSym_selfAdjoint (sub : Bool) (η : ℝ) {R : Symbol} (hsa : SymbolSelfAdjoint R) :
    SymbolSelfAdjoint (physSym sub η R) := by
  have hs : SymbolSelfAdjoint (amo η + R) := by
    intro p
    simp [amo_selfAdjoint η p, hsa p]
  cases sub
  · exact hs.fourier
  · exact hs

lemma isSelfAdjoint_op_physSym (α : ℝ) (sub : Bool) (η : ℝ) {R : Symbol}
    (hR : SymbolSummable R) (hsa : SymbolSelfAdjoint R) (x : ℝ) :
    IsSelfAdjoint (op α (physSym sub η R) x) :=
  isSelfAdjoint_op (physSym_summable sub η hR) (physSym_selfAdjoint sub η hsa) x

lemma op_islandSym (α E₀ tmax : ℝ) (sub : Bool) (η : ℝ) {R : Symbol} (hR : SymbolSummable R)
    (x : ℝ) :
    op α (islandSym E₀ tmax sub η R) x = affineOp E₀ tmax (op α (physSym sub η R) x) :=
  op_affineSym α (physSym_summable sub η hR) E₀ tmax x

lemma op2_islandSym (α E₀ tmax : ℝ) (sub : Bool) (η : ℝ) {R : Symbol} (hR : SymbolSummable R) :
    op2 α (islandSym E₀ tmax sub η R) = affineOp E₀ tmax (op2 α (physSym sub η R)) :=
  op2_affineSym α (physSym_summable sub η hR) E₀ tmax

/-! ### Theorem `thm:noncritical-continuum`: Cantor island, all gaps open -/

/-- The Dry Ten Martini conclusions for a scalar island with symbol `c`: the common island
spectrum is a Cantor set equal to the spectrum of every fibre, and every allowed internal label
`{nα}`, `n ≠ 0`, of the normalized island IDS is an open gap. -/
structure DryIsland (α : ℝ) (c : Symbol) : Prop where
  cantor : IsCantor (islandSpec α c)
  every_phase : ∀ x, spectrum ℝ (op α c x) = islandSpec α c
  gaps : ∃ ν, IsDOSMeasure (op α c) ν ∧ AllGapsOpen (islandSpec α c) ν α

/-- The island spectrum is the affine image of the normalized spectrum `Σ = Σ(K^sub)`. -/
lemma islandSpec_eq (α E₀ tmax : ℝ) (sub : Bool) (η : ℝ) {R : Symbol} (hα : Irrational α)
    (hR : SymbolSummable R) (hsa : SymbolSelfAdjoint R) (hD : SigmaDual α η R = Sigma α η R)
    (x : ℝ) :
    spectrum ℝ (op α (islandSym E₀ tmax sub η R) x) = affine E₀ tmax '' Sigma α η R := by
  rw [op_islandSym α E₀ tmax sub η hR x,
    spectrum_affineOp E₀ tmax (isSelfAdjoint_op_physSym α sub η hR hsa x)]
  congr 1
  cases sub
  · rw [op_physSym_false, spectrum_Hdual_eq_SigmaDual hα hR hsa x, hD]
  · rw [op_physSym_true, spectrum_H_eq_Sigma hα hR hsa x]

/-- The Dry Ten Martini property of `K^sub` transfers to the island, in both orientations. -/
theorem _root_.AMO.DryTenMartini.island {α η E₀ tmax : ℝ} {R : Symbol} (hα : Irrational α)
    (hR : SymbolSummable R) (hsa : SymbolSelfAdjoint R) (htmax : 0 < tmax) (sub : Bool)
    (hD : DryTenMartini α η R) : DryIsland α (islandSym E₀ tmax sub η R) := by
  obtain ⟨hcantor, hdual, ⟨ν, hνH, hνD, hgaps⟩, -⟩ := hD
  have hspec := islandSpec_eq α E₀ tmax sub η hα hR hsa hdual
  have hSig : islandSpec α (islandSym E₀ tmax sub η R) = affine E₀ tmax '' Sigma α η R := hspec 0
  refine ⟨hSig ▸ hcantor.image_affine E₀ htmax.ne', fun x => by rw [hspec x, hSig], ?_⟩
  refine ⟨ν.map (affine E₀ tmax), ?_, hSig ▸ hgaps.map_affine E₀ htmax⟩
  have hfun : op α (islandSym E₀ tmax sub η R) =
      fun x => affineOp E₀ tmax (op α (physSym sub η R) x) :=
    funext (op_islandSym α E₀ tmax sub η hR)
  rw [hfun]
  refine IsDOSMeasure.map_affine ?_ (isSelfAdjoint_op_physSym α sub η hR hsa) E₀ tmax
  cases sub
  · exact hνD
  · exact hνH

/-! ### Theorems `thm:continuum-2d-ac`, `thm:continuum-types`, `thm:continuum-SC` -/

/-- A self-adjoint `op2 α K` whose spectral measures are dominated by an a.c. IDS is purely
absolutely continuous (paper §4.2). -/
lemma purelyAC_op2_of_dominated {α : ℝ} {K : Symbol} {ν : Measure ℝ}
    (hdom : ∀ ψ, ∃ μ, IsSpectralMeasure (op2 α K) ψ μ ∧ μ ≪ ν) (hac : ν ≪ volume) :
    PurelyAC (op2 α K) := fun ψ => by
  obtain ⟨μ, hμ, hμν⟩ := hdom ψ
  exact ⟨μ, hμ, hμν.trans hac⟩

/-- **The off-critical conclusions** for a scalar island at fixed `h` (Theorems
`thm:noncritical-continuum`, `thm:continuum-2d-ac`, `thm:continuum-types`, `thm:continuum-SC`).
Here `Σ = Sigma α η R` is the normalized spectrum `Σ_h^norm`, `Φ_h = affine E₀ tmax`, and `Lsup`
is the prepared exponent `𝓛_h` of the specified Jacobi preparation of the normalized physical
family, with `|𝓛_h - log(t₂/t₁)| ≤ C ε_h` (paper (2.9)). -/
structure OffCriticalIsland (α E₀ tmax : ℝ) (sub : Bool) (η : ℝ) (R : Symbol) (C ε : ℝ)
    (I : IslandReduction α (islandSym E₀ tmax sub η R) Hisl Hfib) : Prop where
  /-- `Σ_h = Φ_h(Σ_h^norm)`. -/
  spec : islandSpec α (islandSym E₀ tmax sub η R) = affine E₀ tmax '' Sigma α η R
  /-- `thm:noncritical-continuum`. -/
  dry : DryIsland α (islandSym E₀ tmax sub η R)
  /-- `thm:continuum-2d-ac`: the full two-dimensional island is purely a.c. in both
  orientations. -/
  ac2d : PurelyACH I.island
  /-- The island has positive measure and dimension one (`thm:continuum-types`). -/
  measure : 0 < volume (islandSpec α (islandSym E₀ tmax sub η R)) ∧
    dimH (islandSpec α (islandSym E₀ tmax sub η R)) = 1
  /-- `thm:continuum-types` (i): subcritical physical orientation, purely a.c. fibres. -/
  fibres_sub : sub = true → ∀ᵐ k ∂volume, PurelyACH (I.fibre k)
  /-- `thm:continuum-types` (ii) and `thm:continuum-SC`: supercritical physical orientation. -/
  fibres_super : sub = false → ∃ Lsup : ℝ → ℝ,
    (∀ E ∈ Sigma α η R, 0 < Lsup E ∧ |Lsup E - Real.log (1 / η)| ≤ C * ε) ∧
    (∀ᵐ k ∂volume, HasCompleteEigenbasisOn (I.fibre k)
      (affine E₀ tmax '' locRegion (Sigma α η R) Lsup α)) ∧
    (∀ᵐ k ∂volume, NoACComponentH (I.fibre k)) ∧
    (∀ᵐ k ∂volume, NoEigenvaluesInH (I.fibre k) (affine E₀ tmax '' scRegion (Sigma α η R) Lsup α)) ∧
    (∀ᵐ k ∂volume, PurelySCOnH (I.fibre k) (affine E₀ tmax '' scRegion (Sigma α η R) Lsup α))

/-- Proof of the off-critical theorems at fixed `h` from the analytic input of Paper I and the
exact reduction. -/
theorem offCriticalIsland_of_input {α η E₀ tmax C ε : ℝ} {R : Symbol} (hα : Irrational α)
    (hR : SymbolSummable R) (hsa : SymbolSelfAdjoint R) (htmax : 0 < tmax) (sub : Bool)
    (hD : DryTenMartini α η R) (hT : SpectralTransition α η R C ε)
    (hreg : RegularRepDominationClaim)
    (I : IslandReduction α (islandSym E₀ tmax sub η R) Hisl Hfib) :
    OffCriticalIsland α E₀ tmax sub η R C ε I := by
  have hdry := hD.island (E₀ := E₀) hα hR hsa htmax sub
  obtain ⟨-, hdual, ⟨ν, hνH, hνD, -⟩, -⟩ := hD
  obtain ⟨ν', hν'H, hν'ac⟩ := hT.ids_ac
  have hνν' : ν = ν' := hνH.unique hν'H
  subst hνν'
  have hK := physSym_summable sub η hR
  have hKsa := physSym_selfAdjoint sub η hsa
  have hνK : IsDOSMeasure (op α (physSym sub η R)) ν := by
    cases sub
    · exact hνD
    · exact hνH
  have hSig : islandSpec α (islandSym E₀ tmax sub η R) = affine E₀ tmax '' Sigma α η R :=
    islandSpec_eq α E₀ tmax sub η hα hR hsa hdual 0
  have hpos := hT.volume_Sigma_pos hα hR hsa
  refine ⟨hSig, hdry, ?_, ?_, ?_, ?_⟩
  · -- the full 2D island
    have h2 : PurelyAC (op2 α (physSym sub η R)) :=
      purelyAC_op2_of_dominated (hreg hα hK hKsa hνK) hν'ac
    have h3 := h2.affineOp (isSelfAdjoint_op2 hK hKsa) E₀ htmax.ne'
    rw [← op2_islandSym α E₀ tmax sub η hR] at h3
    exact purelyACH_of_purelyAC h3 I.reduction
  · rw [hSig]
    have hv : 0 < volume (affine E₀ tmax '' Sigma α η R) := by
      refine pos_iff_ne_zero.2 fun h0 => hpos.1.ne' ?_
      have := volume_preimage_affine (E₀ := E₀) htmax.ne' h0
      rwa [preimage_image_eq _ (affine_injective htmax.ne')] at this
    exact ⟨hv, dimH_eq_one_of_volume_pos hv⟩
  · rintro rfl
    filter_upwards [ae_phase hT.ac I.θ, I.fibre_reduction] with k h1 h2
    have h3 := h1.affineOp (isSelfAdjoint_H α η hR hsa _) E₀ htmax.ne'
    rw [← op_physSym_true, ← op_islandSym α E₀ tmax true η hR] at h3
    exact purelyACH_of_purelyAC h3 h2
  · rintro rfl
    obtain ⟨Lsup, -, hb, hloc, hnoac, hnoe, hsc⟩ := hT.exponent
    have hsaD := isSelfAdjoint_Hdual α η hR hsa
    have hop : ∀ x, affineOp E₀ tmax (Hdual α η R x) = op α (islandSym E₀ tmax false η R) x :=
      fun x => by rw [← op_physSym_false, ← op_islandSym α E₀ tmax false η hR]
    refine ⟨Lsup, hb, ?_, ?_, ?_, ?_⟩
    · filter_upwards [ae_phase hloc I.θ, I.fibre_reduction] with k h1 h2
      have h3 := h1.affineOp (hsaD _) E₀ htmax.ne'
      rw [hop] at h3
      exact hasCompleteEigenbasisOn_of_andersonLocalizedOn h3 h2
    · filter_upwards [ae_phase hnoac I.θ, I.fibre_reduction] with k h1 h2
      have h3 := h1.affineOp (hsaD _) E₀ htmax.ne'
      rw [hop] at h3
      exact noACComponentH_of_noACComponent h3 h2
    · filter_upwards [I.fibre_reduction] with k h2
      have h3 := (hnoe ((k + I.θ) / (2 * Real.pi))).affineOp E₀ htmax.ne'
      rw [hop] at h3
      exact noEigenvaluesInH_of_noEigenvaluesIn h3 h2
    · filter_upwards [ae_phase hsc I.θ, I.fibre_reduction] with k h1 h2
      have h3 := h1.affineOp (hsaD _) E₀ htmax.ne'
      rw [hop] at h3
      exact purelySCOnH_of_purelySCOn h3 h2

/-- **Theorems `thm:noncritical-continuum`–`thm:continuum-SC` at fixed `h`.**  There are
constants `A > 1`, `s₀ > 0` (those of `thm:analytic-input`) such that for every `δ ∈ (0,1)`
there are `ε_*(δ) > 0` and `C > 0` with the following property.  For every irrational flux,
every scalar island in either physical orientation whose normalized coupling and remainder
satisfy `0 < η ≤ 1 - δ` and `ε_h = ‖R‖_{s₀, log(A/η)} < ε_*`, and every exact reduction of it,
all off-critical conclusions hold.  No arithmetic condition beyond irrationality is needed for
the spectral set, the gaps and the two-dimensional absolute continuity. -/
theorem offCritical_continuum (P : PaperInputs) :
    ∃ A > (1 : ℝ), ∃ s₀ > (0 : ℝ), ∀ δ ∈ Ioo (0 : ℝ) 1, ∃ εstar > (0 : ℝ), ∃ C > (0 : ℝ),
      ∀ (α η E₀ tmax : ℝ) (R : Symbol) (sub : Bool), Irrational α → 0 < η → η ≤ 1 - δ →
        0 < tmax → SymbolSelfAdjoint R → WSmall s₀ (Real.log (A / η)) R εstar →
        ∀ {Hisl : Type} [NormedAddCommGroup Hisl] [InnerProductSpace ℂ Hisl] [CompleteSpace Hisl]
          {Hfib : ℝ → Type} [∀ k, NormedAddCommGroup (Hfib k)]
          [∀ k, InnerProductSpace ℂ (Hfib k)] [∀ k, CompleteSpace (Hfib k)]
          (I : IslandReduction α (islandSym E₀ tmax sub η R) Hisl Hfib),
          OffCriticalIsland α E₀ tmax sub η R C (wnorm s₀ (Real.log (A / η)) R) I := by
  obtain ⟨A, hA, s₀, hs₀, hin⟩ := analytic_input P.dryTenMartini P.spectralTransition
  refine ⟨A, hA, s₀, hs₀, fun δ hδ => ?_⟩
  obtain ⟨εstar, hε, C, hC, h⟩ := hin δ hδ
  refine ⟨εstar, hε, C, hC, fun α η E₀ tmax R sub hα hη hηδ htmax hsa hsmall => ?_⟩
  intro Hisl _ _ _ Hfib _ _ _ I
  have hlog : 0 ≤ Real.log (A / η) := Real.log_nonneg (by
    rw [le_div_iff₀ hη]; linarith [hδ.1])
  have hR : SymbolSummable R := hsmall.summable hs₀.le hlog
  obtain ⟨hD, hT⟩ := h α η R hα hη hηδ hsa hsmall
  exact offCriticalIsland_of_input hα hR hsa htmax sub hD hT P.regularRep I

/-! ### In particular: the whole fibre island (paper (2.10)–(2.11)) -/

section Consequences

variable {α E₀ tmax η C ε : ℝ} {R : Symbol}
  {I : IslandReduction α (islandSym E₀ tmax false η R) Hisl Hfib}

/-- `β(α) < log(t₂/t₁) - C ε_h` gives a complete eigenbasis for the whole fibre island, for
a.e. `k` (paper (2.10)); in particular when `β(α) = 0` and `C ε_h < log(t₂/t₁)`. -/
theorem OffCriticalIsland.localized_of_beta_lt
    (h : OffCriticalIsland α E₀ tmax false η R C ε I)
    (hβ : beta α < ENNReal.ofReal (Real.log (1 / η) - C * ε)) :
    ∀ᵐ k ∂volume, HasCompleteEigenbasisOn (I.fibre k) (affine E₀ tmax '' Sigma α η R) := by
  obtain ⟨Lsup, hb, hloc, -⟩ := h.fibres_super rfl
  have hreg : locRegion (Sigma α η R) Lsup α = Sigma α η R :=
    locRegion_eq_of_lt fun E hE => hβ.trans_le (ENNReal.ofReal_le_ofReal (by
      have := (abs_le.1 (hb E hE).2).1; linarith))
  rwa [hreg] at hloc

/-- `β(α) > log(t₂/t₁) + C ε_h` gives pure singular continuity of the whole fibre island for
a.e. `k` (paper (2.11)); in particular when `β(α) = ∞`. -/
theorem OffCriticalIsland.sc_of_beta_gt (h : OffCriticalIsland α E₀ tmax false η R C ε I)
    (hβ : ENNReal.ofReal (Real.log (1 / η) + C * ε) < beta α) :
    ∀ᵐ k ∂volume, PurelySCOnH (I.fibre k) (affine E₀ tmax '' Sigma α η R) := by
  obtain ⟨Lsup, hb, -, -, -, hsc⟩ := h.fibres_super rfl
  have hreg : scRegion (Sigma α η R) Lsup α = Sigma α η R :=
    scRegion_eq_of_gt fun E hE => lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by
      have := (abs_le.1 (hb E hE).2).2; linarith)) hβ
  rwa [hreg] at hsc

theorem OffCriticalIsland.sc_of_beta_top (h : OffCriticalIsland α E₀ tmax false η R C ε I)
    (hβ : beta α = ⊤) :
    ∀ᵐ k ∂volume, PurelySCOnH (I.fibre k) (affine E₀ tmax '' Sigma α η R) :=
  h.sc_of_beta_gt (by rw [hβ]; exact ENNReal.ofReal_lt_top)

end Consequences

end CMS
