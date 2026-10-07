/-
# Inputs from Papers I and II  (paper §2.4, Theorems `thm:analytic-input` and
`thm:critical-geometric-input`)

Paper III uses the following results about the lattice operators
`K = U + U^{-1} + η(V + V^{-1}) + R`, imported from
*Paper I* (Analytic perturbations of the almost Mathieu operator; Lean: `AnalyticPerturbationsAMO`)
and *Paper II* (Self-dual perturbations of the critical almost Mathieu operator).

**Convention.**  Results that are not proved in Lean are stated as named propositions
(`…Claim : Prop`) and are never asserted; every theorem that uses them takes them as explicit
hypotheses.  They are bundled in `PaperInputs`.

* Theorem `thm:analytic-input` (i)–(iv) is Paper I, Corollary 1.2, Theorems 1.4–1.6: the claims
  `AMO.DryTenMartiniUniformClaim`, `AMO.SpectralTransitionUniformClaim`, `AMO.CriticalClaim` of
  `AnalyticPerturbationsAMO.MainTheorems`.  Parts (i)–(iv) are derived from them here.
* Two further facts used by Paper III are not part of the Paper I Lean development and are
  stated here as claims:
  - `regular_rep_domination` — Paper I, Lemma 3.5: every spectral measure of the full lattice
    realization `K̃ = op2 α K` is absolutely continuous with respect to the IDS measure `ν_K`
    (paper (4.4) `eq:full-plane-maximal-type`).  Its proof needs the direct-integral
    decomposition `𝓑 K̃ 𝓑* = ∫^⊕ K_x dx` and the Borel functional calculus;
  - `critical_ids_atomless` — the atomless IDS part of `thm:analytic-input` (iv).
* Theorem `thm:critical-geometric-input` is Paper II, Theorems 1.1–1.2 (all gaps open,
  `𝓗^{1/2}(Σ) < ∞`, `dim_H Σ = 0` at ordinary Liouville frequencies), stated as a claim.

We also prove the *uniqueness of the DOS measure* (two DOS measures of the same family agree),
which is used to identify the IDS of the two Fourier orientations.
-/
import ContinuumMagnetic.AffineIsland

noncomputable section

open scoped ENNReal
open MeasureTheory Set Filter AMO

namespace CMS

/-! ### Arithmetic of the flux -/

/-- `α` is *ordinary Liouville*: `μ_irr(α) = 1 + limsup_j log q_{j+1} / log q_j = ∞`. -/
def OrdinaryLiouville (α : ℝ) : Prop :=
  limsup (fun j : ℕ => ENNReal.ofReal (Real.log (cfDen α (j + 1)) / Real.log (cfDen α j)))
    atTop = ⊤

/-! ### Uniqueness of the DOS measure -/

/-- Two DOS measures of the same family coincide: both are probability measures with the same
integrals of bounded continuous functions. -/
theorem _root_.AMO.IsDOSMeasure.unique {Hx : ℝ → Op ℤ} {ν ν' : Measure ℝ} (h : IsDOSMeasure Hx ν)
    (h' : IsDOSMeasure Hx ν') : ν = ν' := by
  have := h.1
  have := h'.1
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
  rw [h.2 f, h'.2 f]

/-! ### Theorem `thm:analytic-input` from Paper I -/

lemma _root_.AMO.WSmall.of_le {s ℓ ε ε' : ℝ} {R : Symbol} (h : WSmall s ℓ R ε) (hε : ε ≤ ε') :
    WSmall s ℓ R ε' := ⟨h.1, h.2.trans_le hε⟩

/-- The conclusions of Theorems 1.4–1.5 of Paper I only get weaker when the error parameter
grows. -/
lemma _root_.AMO.SpectralTransition.mono {α η C ε ε' : ℝ} {R : Symbol} (h : SpectralTransition α η R C ε)
    (hC : 0 ≤ C) (hε : ε ≤ ε') : SpectralTransition α η R C ε' := by
  obtain ⟨hac, ⟨L, h1, h2, h3, h4, h5, h6⟩, hids⟩ := h
  exact ⟨hac, ⟨L, h1, fun E hE => ⟨(h2 E hE).1,
    (h2 E hE).2.trans (mul_le_mul_of_nonneg_left hε hC)⟩, h3, h4, h5, h6⟩, hids⟩

/-- **Theorem 2.6 (i)** (Paper I, Corollary 1.2): frequency-uniform Dry Ten Martini for both
Fourier orientations, with a common IDS. -/
theorem analytic_input_i (h : DryTenMartiniUniformClaim) :
    ∃ A > (1 : ℝ), ∃ s₀ > (0 : ℝ), ∀ δ ∈ Ioo (0 : ℝ) 1, ∃ εstar > (0 : ℝ),
      ∀ (α η : ℝ) (R : Symbol), Irrational α → 0 < η → η ≤ 1 - δ →
        SymbolSelfAdjoint R → WSmall s₀ (Real.log (A / η)) R εstar → DryTenMartini α η R :=
  h

/-- **Theorem 2.6 (i)–(iii)** in one package: the constants can be chosen so that both
Corollary 1.2 and Theorems 1.4–1.5 of Paper I hold. -/
theorem analytic_input (h₁ : DryTenMartiniUniformClaim) (h₂ : SpectralTransitionUniformClaim) :
    ∃ A > (1 : ℝ), ∃ s₀ > (0 : ℝ), ∀ δ ∈ Ioo (0 : ℝ) 1, ∃ εstar > (0 : ℝ), ∃ C > (0 : ℝ),
      ∀ (α η : ℝ) (R : Symbol), Irrational α → 0 < η → η ≤ 1 - δ →
        SymbolSelfAdjoint R → WSmall s₀ (Real.log (A / η)) R εstar →
        DryTenMartini α η R ∧ SpectralTransition α η R C (wnorm s₀ (Real.log (A / η)) R) := by
  obtain ⟨A, hA, s₀, hs₀, h1⟩ := h₁
  obtain ⟨A', hA', s₀', hs₀', h2⟩ := h₂
  -- Enlarge the weights to the maximum of the two choices.
  refine ⟨max A A', lt_max_of_lt_left hA, max s₀ s₀', lt_max_of_lt_left hs₀, fun δ hδ => ?_⟩
  obtain ⟨ε₁, hε₁, h1'⟩ := h1 δ hδ
  obtain ⟨ε₂, hε₂, C, hC, h2'⟩ := h2 δ hδ
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, C, hC, fun α η R hα hη hηδ hR hsmall => ?_⟩
  have hA0 : 0 < A := zero_lt_one.trans hA
  have hA0' : 0 < A' := zero_lt_one.trans hA'
  have hmono : ∀ {s ℓ s' ℓ' : ℝ}, s ≤ s' → ℓ ≤ ℓ' → ∀ {ε : ℝ},
      WSmall s' ℓ' R ε → WSmall s ℓ R ε ∧ wnorm s ℓ R ≤ wnorm s' ℓ' R := by
    intro s ℓ s' ℓ' hs hℓ ε h
    have hle : ∀ p : ℤ × ℤ, ‖R p‖ * Real.exp (s * |(p.1 : ℝ)| + ℓ * |(p.2 : ℝ)|) ≤
        ‖R p‖ * Real.exp (s' * |(p.1 : ℝ)| + ℓ' * |(p.2 : ℝ)|) := fun p => by
      gcongr
    have hsum := h.1.of_nonneg_of_le (fun p => by positivity) hle
    have hw : wnorm s ℓ R ≤ wnorm s' ℓ' R := hsum.tsum_le_tsum hle h.1
    exact ⟨⟨hsum, hw.trans_lt h.2⟩, hw⟩
  have hlog : ∀ {B : ℝ}, 0 < B → B ≤ max A A' → Real.log (B / η) ≤ Real.log (max A A' / η) :=
    fun hB hle => Real.log_le_log (div_pos hB hη) (div_le_div_of_nonneg_right hle hη.le)
  refine ⟨h1' α η R hα hη hηδ hR ?_, ?_⟩
  · exact WSmall.of_le (hmono (le_max_left _ _) (hlog hA0 (le_max_left _ _)) hsmall).1
      (min_le_left _ _)
  · have small := hmono (le_max_right _ _) (hlog hA0' (le_max_right _ _)) hsmall
    exact (h2' α η R hα hη hηδ hR (WSmall.of_le small.1 (min_le_right _ _))).mono hC.le small.2

/-- **Theorem 2.6 (iv)** (Paper I, Theorem 1.6): critical self-dual perturbations. -/
theorem analytic_input_iv (h : CriticalClaim) :
    ∃ S > (0 : ℝ), ∃ εc > (0 : ℝ), ∀ (α : ℝ) (R : Symbol), Irrational α →
      SymbolSelfAdjoint R → fourier R = R → WSmall S S R εc →
      IsCantor (Sigma α 1 R) ∧ volume (Sigma α 1 R) = 0 ∧
      (∃ ystar > (0 : ℝ), ∀ E ∈ Sigma α 1 R, ∃ P : JacobiPrep α (H α 1 R) E,
        ystar ≤ P.w ∧ ∀ y : ℝ, |y| < ystar → P.L y = 2 * Real.pi * |y|) ∧
      (0 < beta α → ∀ x, PurelySC (H α 1 R x)) :=
  h

/-! ### Inputs not contained in the Paper I formalization -/

/-- **Paper I, Lemma 3.5 (maximal spectral type of the full lattice realization).**  For a
summable self-adjoint Weyl series `K` and irrational `α`, every spectral measure of
`K̃ = op2 α K` on `ℓ²(ℤ²)` is absolutely continuous with respect to the IDS measure `ν_K`
(paper (4.4)–(4.5): `𝟙_B(K̃) = 0 ⟺ ν_K(B) = 0`).

Not formalized: the proof uses the direct integral `𝓑 K̃ 𝓑* = ∫^⊕_𝕋 K_x dx` and the Borel
functional calculus, which Mathlib does not provide. -/
def RegularRepDominationClaim : Prop :=
  ∀ {α : ℝ}, Irrational α → ∀ {K : Symbol}, SymbolSummable K → SymbolSelfAdjoint K →
    ∀ {ν : Measure ℝ}, IsDOSMeasure (op α K) ν →
      ∀ ψ, ∃ μ, IsSpectralMeasure (op2 α K) ψ μ ∧ μ ≪ ν

/-- **Theorem 2.6 (iv), IDS part** (Paper I, Theorem 1.6 and Lemma 2.8): in the critical regime
the IDS measure exists and is atomless.

Not formalized: atomlessness needs the Borel functional calculus (Paper I, Lemma 2.8). -/
def CriticalIDSAtomlessClaim : Prop :=
  ∃ S > (0 : ℝ), ∃ εc > (0 : ℝ), ∀ (α : ℝ) (R : Symbol), Irrational α →
    SymbolSelfAdjoint R → fourier R = R → WSmall S S R εc →
    ∃ ν : Measure ℝ, IsDOSMeasure (H α 1 R) ν ∧ ∀ t, ν {t} = 0

/-- **Theorem 2.7** (Paper II, Theorems 1.1–1.2): for each irrational `α` there is a critical
stability weight `S_*(α)` such that small self-dual perturbations of the critical almost
Mathieu operator have every allowed gap open and `𝓗^{1/2}(Σ) < ∞`; at an ordinary Liouville
frequency, for every weight the dimension is zero.  The radii are chosen before the gap label.

Not formalized here (Paper II). -/
def CriticalGeometricInputClaim : Prop :=
  ∀ α : ℝ, Irrational α → ∃ Sstar > (0 : ℝ),
      (∀ S' ≥ Sstar, ∃ ρ > (0 : ℝ), ∀ R : Symbol, SymbolSelfAdjoint R → fourier R = R →
        WSmall S' S' R ρ →
        (∀ ν : Measure ℝ, IsDOSMeasure (H α 1 R) ν → AllGapsOpen (Sigma α 1 R) ν α) ∧
        μH[1 / 2] (Sigma α 1 R) < ⊤) ∧
      (OrdinaryLiouville α → ∀ S' > (0 : ℝ), ∃ ρL > (0 : ℝ), ∀ R : Symbol,
        SymbolSelfAdjoint R → fourier R = R → WSmall S' S' R ρL →
        dimH (Sigma α 1 R) = 0)

/-- **All analytic input used by Paper III**, as hypotheses: Paper I (Corollary 1.2,
Theorems 1.4–1.6, Lemma 3.5, Lemma 2.8) and Paper II (Theorems 1.1–1.2). -/
structure PaperInputs : Prop where
  dryTenMartini : DryTenMartiniUniformClaim
  spectralTransition : SpectralTransitionUniformClaim
  critical : CriticalClaim
  regularRep : RegularRepDominationClaim
  criticalIDS : CriticalIDSAtomlessClaim
  criticalGeometry : CriticalGeometricInputClaim

end CMS
