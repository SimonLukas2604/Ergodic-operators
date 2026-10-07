/-
# Main results  (paper §1, Theorems 1.1, 1.4, 1.5, 1.6 and Corollaries 1.2, 1.3, 1.7)

The main theorems are stated faithfully as named propositions (`…Claim : Prop`): each
definition records the exact statement without asserting it, so the project contains no
`sorry`.  Their proofs in the paper rest on results that are not in Mathlib: Avila's global theory of one-frequency cocycles
(acceleration, quantization, positive regularity), almost reducibility, Avila–Fayad–Krikorian
rotations reducibility, Avila–Krikorian monotone families, Deninger's Fuglede–Kadison
determinant formula, the Avila–You–Zhou quantitative normal forms, Puig's duality argument,
Kotani theory, Gordon-type arguments, and Gordon–Jitomirskaya–Last–Simon duality.

Everything derivable from them is **proved** as an implication from the claims: Corollary 1.3
(both versions) from Theorem 1.1 / Corollary 1.2, and the "in particular" consequences (e.g. localization on all of `Σ` under `β(α) < log(1/η) - Cε`, singular continuity
on all of `Σ` under `β(α) > log(1/η) + Cε` or `β(α) = ∞`, and self-duality of the critical
operator).
-/
import AnalyticPerturbationsAMO.Supercritical

noncomputable section

open scoped ENNReal
open MeasureTheory Set Filter

namespace AMO

/-- The conclusions of the Dry Ten Martini theorem for `H = U + U^{-1} + η(V + V^{-1}) + R`:
Cantor spectrum, every allowed gap open, the same dry spectrum and IDS for the Fourier dual,
and a subcritical exact preparation at every spectral energy. -/
structure DryTenMartini (α η : ℝ) (R : Symbol) : Prop where
  cantor : IsCantor (Sigma α η R)
  dual_spectrum : SigmaDual α η R = Sigma α η R
  gaps : ∃ ν : Measure ℝ, IsDOSMeasure (H α η R) ν ∧ IsDOSMeasure (Hdual α η R) ν ∧
    AllGapsOpen (Sigma α η R) ν α
  subcritical : ∀ E ∈ Sigma α η R, ∃ P : JacobiPrep α (H α η R) E, P.Subcritical

/-- **Theorem 1.1 (off-critical Dry Ten Martini).**  Fix irrational `α`, `0 < η < 1`,
`s > 0` and `ℓ > log(1/η)`.  There is `ε₀ > 0` such that every self-adjoint `R` with
`‖R‖_{s,ℓ} < ε₀` satisfies the Dry Ten Martini conclusions, with one threshold for all gap
labels.  All spectral-set assertions hold for every phase (`spectrum_H_eq_Sigma`). -/
def DryTenMartiniClaim : Prop :=
  ∀ {α η s ℓ : ℝ}, Irrational α → 0 < η → η < 1 → 0 < s → Real.log (1 / η) < ℓ →
    ∃ ε₀ > 0, ∀ R : Symbol, SymbolSelfAdjoint R → WSmall s ℓ R ε₀ → DryTenMartini α η R

/-- **Corollary 1.2 (frequency-uniform version).** -/
def DryTenMartiniUniformClaim : Prop :=
  ∃ A > (1 : ℝ), ∃ s₀ > (0 : ℝ), ∀ δ ∈ Ioo (0 : ℝ) 1, ∃ εstar > (0 : ℝ),
    ∀ (α η : ℝ) (R : Symbol), Irrational α → 0 < η → η ≤ 1 - δ →
      SymbolSelfAdjoint R → WSmall s₀ (Real.log (A / η)) R εstar → DryTenMartini α η R

/-! ### Corollary 1.3, derived from Theorem 1.1 and Corollary 1.2 -/

lemma SymbolSelfAdjoint.real_smul {R : Symbol} (h : SymbolSelfAdjoint R) (c : ℝ) :
    SymbolSelfAdjoint (((c : ℝ) : ℂ) • R) := by
  intro p
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_ofReal, h p]

lemma WSmall.real_smul {s ℓ ε : ℝ} {R : Symbol} (h : WSmall s ℓ R ε) {c : ℝ} (hc : 0 < c) :
    WSmall s ℓ (((c : ℝ) : ℂ) • R) (c * ε) := by
  have hn : ∀ p, ‖(((c : ℝ) : ℂ) • R) p‖ * Real.exp (s * |(p.1 : ℝ)| + ℓ * |(p.2 : ℝ)|) =
      c * (‖R p‖ * Real.exp (s * |(p.1 : ℝ)| + ℓ * |(p.2 : ℝ)|)) := fun p => by
    rw [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, mul_assoc]
  refine ⟨?_, ?_⟩
  · simp only [hn]; exact h.1.mul_left c
  · unfold wnorm
    simp only [hn]
    rw [tsum_mul_left]
    exact mul_lt_mul_of_pos_left h.2 hc

/-- The perturbation `λ^{-1} 𝓕^{-1}(T)` of the subcritical dual. -/
def dualPert (lam : ℝ) (T : Symbol) : Symbol := (((lam⁻¹ : ℝ) : ℂ)) • fourier (fourier (fourier T))

lemma dualPert_sa {lam : ℝ} {T : Symbol} (hT : SymbolSelfAdjoint T) :
    SymbolSelfAdjoint (dualPert lam T) :=
  hT.fourier.fourier.fourier.real_smul _

lemma dualPert_small {lam s ℓ ε : ℝ} (hlam : 0 < lam) {T : Symbol}
    (hT : WSmall s ℓ T (lam * ε)) : WSmall ℓ s (dualPert lam T) ε := by
  have h3 : WSmall ℓ s (fourier (fourier (fourier T))) (lam * ε) := hT.fourier.fourier.fourier
  have := h3.real_smul (inv_pos.2 hlam)
  rwa [← mul_assoc, inv_mul_cancel₀ hlam.ne', one_mul] at this

/-- The transport: if the subcritical operator `H_{λ^{-1}, λ^{-1}𝓕^{-1}T}` has the Dry Ten
Martini property, then `H_{λ, T}` has Cantor spectrum and all gaps open. -/
theorem supercritical_of_dual {α lam : ℝ} (hlam : 0 < lam) {T : Symbol}
    (hT : SymbolSummable T) (hTsa : SymbolSelfAdjoint T)
    (hD : DryTenMartini α lam⁻¹ (dualPert lam T)) :
    IsCantor (Sigma α lam T) ∧
      ∃ ν : Measure ℝ, IsDOSMeasure (H α lam T) ν ∧ AllGapsOpen (Sigma α lam T) ν α := by
  obtain ⟨hcantor, hdual, ⟨ν', -, hν'D, hgaps⟩, -⟩ := hD
  have hsig : Sigma α lam T = (fun t => lam * t) '' Sigma α lam⁻¹ (dualPert lam T) := by
    have h1 : SigmaDual α lam⁻¹ (dualPert lam T) = (fun t => lam⁻¹ * t) '' Sigma α lam T := by
      unfold SigmaDual Sigma dualPert
      rw [Hdual_supercritical hlam hT 0, spectrum_real_smul (inv_pos.2 hlam).ne']
    rw [hdual] at h1
    rw [h1, Set.image_image]
    simp [mul_inv_cancel_left₀ hlam.ne']
  have hsaH : ∀ x, IsSelfAdjoint (H α lam T x) := isSelfAdjoint_H α lam hT hTsa
  have hDOS := hν'D.map_mul (inv_pos.2 hlam) (fun x => Hdual_supercritical hlam hT x) hsaH
  rw [inv_inv] at hDOS
  refine ⟨hsig ▸ hcantor.image_mul hlam, _, hDOS, ?_⟩
  rw [hsig]
  exact hgaps.map_mul hlam

/-- **Corollary 1.3 (supercritical orientation)**, derived from Theorem 1.1.  For `λ > 1`,
`s > log λ`, `ℓ > 0`, the operator `U + U^{-1} + λ(V + V^{-1}) + T` has Cantor spectrum with all
gaps open whenever `λ^{-1}‖T‖_{s,ℓ}` is small.  No Diophantine or localization hypothesis. -/
theorem dry_ten_martini_supercritical (h11 : DryTenMartiniClaim) {α lam s ℓ : ℝ}
    (hα : Irrational α) (hlam : 1 < lam)
    (hs : Real.log lam < s) (hℓ : 0 < ℓ) :
    ∃ ε₀ > 0, ∀ T : Symbol, SymbolSelfAdjoint T → WSmall s ℓ T (lam * ε₀) →
      IsCantor (Sigma α lam T) ∧
        ∃ ν : Measure ℝ, IsDOSMeasure (H α lam T) ν ∧ AllGapsOpen (Sigma α lam T) ν α := by
  have hlam0 : 0 < lam := zero_lt_one.trans hlam
  have hs0 : 0 < s := (Real.log_pos hlam).trans hs
  obtain ⟨ε₀, hε₀, hthm⟩ := h11 (η := lam⁻¹) (s := ℓ) (ℓ := s) hα
    (inv_pos.2 hlam0) (inv_lt_one_of_one_lt₀ hlam) hℓ (by rw [one_div, inv_inv]; exact hs)
  refine ⟨ε₀, hε₀, fun T hTsa hTsmall => ?_⟩
  exact supercritical_of_dual hlam0 (hTsmall.summable hs0.le hℓ.le) hTsa
    (hthm _ (dualPert_sa hTsa) (dualPert_small hlam0 hTsmall))

/-- **Corollary 1.3, frequency-uniform version**, derived from Corollary 1.2 with the same
constants `A, s₀, ε_*(δ)`. -/
theorem dry_ten_martini_supercritical_uniform (h12 : DryTenMartiniUniformClaim) :
    ∃ A > (1 : ℝ), ∃ s₀ > (0 : ℝ), ∀ δ ∈ Ioo (0 : ℝ) 1, ∃ εstar > (0 : ℝ),
      ∀ (α lam : ℝ) (T : Symbol), Irrational α → 1 < lam → lam⁻¹ ≤ 1 - δ →
        SymbolSelfAdjoint T → WSmall (Real.log (A * lam)) s₀ T (lam * εstar) →
        IsCantor (Sigma α lam T) ∧
          ∃ ν : Measure ℝ, IsDOSMeasure (H α lam T) ν ∧ AllGapsOpen (Sigma α lam T) ν α := by
  obtain ⟨A, hA, s₀, hs₀, hunif⟩ := h12
  refine ⟨A, hA, s₀, hs₀, fun δ hδ => ?_⟩
  obtain ⟨εstar, hε, hthm⟩ := hunif δ hδ
  refine ⟨εstar, hε, fun α lam T hα hlam hlamδ hTsa hTsmall => ?_⟩
  have hlam0 : 0 < lam := zero_lt_one.trans hlam
  have hlog : 0 ≤ Real.log (A * lam) := Real.log_nonneg (by nlinarith)
  have hsmall := dualPert_small hlam0 hTsmall
  rw [show Real.log (A * lam) = Real.log (A / lam⁻¹) by rw [div_inv_eq_mul]] at hsmall
  exact supercritical_of_dual hlam0 (hTsmall.summable hlog hs₀.le) hTsa
    (hthm α lam⁻¹ _ hα (inv_pos.2 hlam0) hlamδ (dualPert_sa hTsa) hsmall)

/-- The two strict arithmetic regions of the dual: `Σ_loc = {𝓛 > β}` and `𝒮 = {𝓛 < β}`. -/
def locRegion (Sig : Set ℝ) (Lsup : ℝ → ℝ) (α : ℝ) : Set ℝ :=
  {E ∈ Sig | beta α < ENNReal.ofReal (Lsup E)}

def scRegion (Sig : Set ℝ) (Lsup : ℝ → ℝ) (α : ℝ) : Set ℝ :=
  {E ∈ Sig | ENNReal.ofReal (Lsup E) < beta α}

/-- The conclusions of Theorems 1.4 and 1.5 for `H = AMO_η + R` with constant `C` and
smallness parameter `ε`.  `Lsup` is the prepared supercritical exponent
`𝓛(E) = ∫ log|a_E| - ∫ log|â_E|`, realised by preparations of `H - E` and `Ĥ - E`. -/
structure SpectralTransition (α η : ℝ) (R : Symbol) (C ε : ℝ) : Prop where
  /-- (i) Purely absolutely continuous spectrum for a.e. phase. -/
  ac : ∀ᵐ x ∂volume, PurelyAC (H α η R x)
  exponent : ∃ Lsup : ℝ → ℝ,
    (∀ E ∈ Sigma α η R, ∃ (P : JacobiPrep α (H α η R) E) (P' : JacobiPrep α (Hdual α η R) E),
      Lsup E = P.logMean - P'.logMean) ∧
    (∀ E ∈ Sigma α η R, 0 < Lsup E ∧ |Lsup E - Real.log (1 / η)| ≤ C * ε) ∧
    /- (ii) Anderson localization of the dual on `Σ_loc` for a.e. phase. -/
    (∀ᵐ x ∂volume, AndersonLocalizedOn (Hdual α η R x) (locRegion (Sigma α η R) Lsup α)) ∧
    /- Theorem 1.5: no a.c. component, no eigenvalues in `𝒮`, singular continuity on `𝒮`. -/
    (∀ᵐ x ∂volume, NoACComponent (Hdual α η R x)) ∧
    (∀ x, NoEigenvaluesIn (Hdual α η R x) (scRegion (Sigma α η R) Lsup α)) ∧
    (∀ᵐ x ∂volume, PurelySCOn (Hdual α η R x) (scRegion (Sigma α η R) Lsup α))
  /-- (iii) The IDS measure is absolutely continuous.  (`|Σ| > 0` and `dim_H Σ = 1` are then
  proved in `SpectralTransition.volume_Sigma_pos`.) -/
  ids_ac : ∃ ν : Measure ℝ, IsDOSMeasure (H α η R) ν ∧ ν ≪ volume

/-- **Theorems 1.4 and 1.5 (spectral types and the arithmetic transition).**  Under the
hypotheses of Theorem 1.1, after decreasing `ε₀`. -/
def SpectralTransitionClaim : Prop :=
  ∀ {α η s ℓ : ℝ}, Irrational α → 0 < η → η < 1 → 0 < s → Real.log (1 / η) < ℓ →
    ∃ ε₀ > 0, ∃ C > 0, ∀ R : Symbol, SymbolSelfAdjoint R → WSmall s ℓ R ε₀ →
      SpectralTransition α η R C (wnorm s ℓ R)

/-- **Theorems 1.4 and 1.5, frequency-uniform version** (hypotheses of Corollary 1.2). -/
def SpectralTransitionUniformClaim : Prop :=
  ∃ A > (1 : ℝ), ∃ s₀ > (0 : ℝ), ∀ δ ∈ Ioo (0 : ℝ) 1, ∃ εstar > (0 : ℝ), ∃ C > (0 : ℝ),
    ∀ (α η : ℝ) (R : Symbol), Irrational α → 0 < η → η ≤ 1 - δ →
      SymbolSelfAdjoint R → WSmall s₀ (Real.log (A / η)) R εstar →
      SpectralTransition α η R C (wnorm s₀ (Real.log (A / η)) R)

/-- **Theorem 1.6 (critical self-dual perturbations).**  Zero-measure Cantor spectrum, the
quantized complexified exponent `L(E, y) = 2π|y|`, and purely singular continuous fibres when
`β(α) > 0`. -/
def CriticalClaim : Prop :=
  ∃ S > (0 : ℝ), ∃ εc > (0 : ℝ), ∀ (α : ℝ) (R : Symbol), Irrational α →
    SymbolSelfAdjoint R → fourier R = R → WSmall S S R εc →
    IsCantor (Sigma α 1 R) ∧ volume (Sigma α 1 R) = 0 ∧
    (∃ ystar > (0 : ℝ), ∀ E ∈ Sigma α 1 R, ∃ P : JacobiPrep α (H α 1 R) E,
      ystar ≤ P.w ∧ ∀ y : ℝ, |y| < ystar → P.L y = 2 * Real.pi * |y|) ∧
    (0 < beta α → ∀ x, PurelySC (H α 1 R x))

/-- **Corollary 1.7 (the two-dimensional operators).**  Off criticality both orientations of
`H̃` are purely absolutely continuous; at criticality `H̃` is purely singular continuous,
with no condition on `β(α)`. -/
def TwoDimensionalClaim : Prop :=
  ∀ {α η s ℓ : ℝ}, Irrational α → 0 < η → η < 1 → 0 < s → Real.log (1 / η) < ℓ →
    ∃ ε₀ > 0, ∀ R : Symbol, SymbolSelfAdjoint R → WSmall s ℓ R ε₀ →
      PurelyAC (op2 α (amo η + R)) ∧ PurelyAC (op2 α (fourier (amo η + R)))

def TwoDimensionalCriticalClaim : Prop :=
  ∃ S > (0 : ℝ), ∃ εc > (0 : ℝ), ∀ (α : ℝ) (R : Symbol), Irrational α →
    SymbolSelfAdjoint R → fourier R = R → WSmall S S R εc →
    PurelySC (op2 α (amo 1 + R))

/-! ### Consequences proved from the main statements -/

section Consequences

variable {α η : ℝ} {R : Symbol} {C ε : ℝ}

/-- If `β(α) < inf_Σ 𝓛`, the localization region is all of `Σ`. -/
lemma locRegion_eq_of_lt {Sig : Set ℝ} {Lsup : ℝ → ℝ}
    (h : ∀ E ∈ Sig, beta α < ENNReal.ofReal (Lsup E)) : locRegion Sig Lsup α = Sig := by
  ext E
  exact ⟨fun hE => hE.1, fun hE => ⟨hE, h E hE⟩⟩

/-- If `β(α) > sup_Σ 𝓛`, the singular-continuity region is all of `Σ`. -/
lemma scRegion_eq_of_gt {Sig : Set ℝ} {Lsup : ℝ → ℝ}
    (h : ∀ E ∈ Sig, ENNReal.ofReal (Lsup E) < beta α) : scRegion Sig Lsup α = Sig := by
  ext E
  exact ⟨fun hE => hE.1, fun hE => ⟨hE, h E hE⟩⟩

/-- **Localization of the dual on the whole spectrum** under the explicit sufficient
condition `β(α) < log(1/η) - Cε` (this includes every `α` with `β(α) = 0` once `Cε` is
small). -/
theorem SpectralTransition.localization_of_beta_lt (hT : SpectralTransition α η R C ε)
    (hβ : beta α < ENNReal.ofReal (Real.log (1 / η) - C * ε)) :
    ∀ᵐ x ∂volume, AndersonLocalizedOn (Hdual α η R x) (Sigma α η R) := by
  obtain ⟨Lsup, -, hbound, hloc, -⟩ := hT.exponent
  have hreg : locRegion (Sigma α η R) Lsup α = Sigma α η R := by
    refine locRegion_eq_of_lt fun E hE => hβ.trans_le (ENNReal.ofReal_le_ofReal ?_)
    have := (hbound E hE).2
    have := (abs_le.1 this).1
    linarith
  filter_upwards [hloc] with x hx
  exact hx.mono hreg

/-- **Singular continuity of the dual on the whole spectrum** under the explicit sufficient
condition `β(α) > log(1/η) + Cε`. -/
theorem SpectralTransition.sc_of_beta_gt (hT : SpectralTransition α η R C ε)
    (hβ : ENNReal.ofReal (Real.log (1 / η) + C * ε) < beta α) :
    ∀ᵐ x ∂volume, PurelySCOn (Hdual α η R x) (Sigma α η R) := by
  obtain ⟨Lsup, -, hbound, -, -, -, hsc⟩ := hT.exponent
  have hreg : scRegion (Sigma α η R) Lsup α = Sigma α η R := by
    refine scRegion_eq_of_gt fun E hE => lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ?_) hβ
    have := (abs_le.1 (hbound E hE).2).2
    linarith
  rw [hreg] at hsc
  exact hsc

/-- In particular the dual is purely singular continuous on `Σ` for a.e. phase when
`β(α) = ∞`. -/
theorem SpectralTransition.sc_of_beta_top (hT : SpectralTransition α η R C ε)
    (hβ : beta α = ⊤) : ∀ᵐ x ∂volume, PurelySCOn (Hdual α η R x) (Sigma α η R) :=
  hT.sc_of_beta_gt (by rw [hβ]; exact ENNReal.ofReal_lt_top)

/-- The localization and singular-continuity regions are disjoint. -/
lemma locRegion_disjoint_scRegion (Sig : Set ℝ) (Lsup : ℝ → ℝ) (α : ℝ) :
    Disjoint (locRegion Sig Lsup α) (scRegion Sig Lsup α) := by
  rw [Set.disjoint_left]
  rintro E ⟨-, h1⟩ ⟨-, h2⟩
  exact lt_asymm h1 h2

/-- At criticality the Fourier-dual family coincides with the original one, so the dual has
the same zero-measure Cantor spectrum. -/
theorem critical_dual_spectrum (α : ℝ) {R : Symbol} (hR : fourier R = R) :
    SigmaDual α 1 R = Sigma α 1 R := by
  unfold SigmaDual Sigma
  rw [Hdual_eq_H_critical α hR]

/-- **Theorem 1.4(iii), in particular:** `|Σ| > 0` and `dim_H Σ = 1`. -/
theorem SpectralTransition.volume_Sigma_pos (hT : SpectralTransition α η R C ε)
    (hα : Irrational α) (hR : SymbolSummable R) (hsa : SymbolSelfAdjoint R) :
    0 < volume (Sigma α η R) ∧ dimH (Sigma α η R) = 1 := by
  obtain ⟨ν, hν, hac⟩ := hT.ids_ac
  exact volume_Sigma_pos_and_dimH hα hR hsa hν hac

/-- Theorem 1.1's spectral sets do not depend on the phase. -/
theorem DryTenMartini.spectrum_eq (hα : Irrational α) (hR : SymbolSummable R)
    (hsa : SymbolSelfAdjoint R) (x : ℝ) : spectrum ℝ (H α η R x) = Sigma α η R :=
  spectrum_H_eq_Sigma hα hR hsa x

end Consequences

end AMO
