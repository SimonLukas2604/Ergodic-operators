/-
# Main results  (paper §1: Theorems `cor:cosine`, `thm:high-energy-spectrum`, `thm:physical-hall`,
Corollary `cor:high-critical-dimension`)

**Structure of the formalization.**  Each main theorem is *proved* here from

1. the scalar criteria (`ContinuumMagnetic.ScalarCriteria`, `ContinuumMagnetic.CriticalCriteria`),
   which in turn rest on the analytic input of Papers I–II (`ContinuumMagnetic.AnalyticInput`);
2. the *exact continuum reductions* of the paper, stated below as named claims
   (`…Claim : Prop`, never asserted; bundled in `ContinuumInputs`):
   * `CosineReductionRectClaim`, `CosineReductionSquareClaim` — §3 (Propositions
     `c-prop:magnetic-carlsson`, `ex-prop:reduction`, `c-prop:exact-cosine-tunneling`,
     `ex-prop:all-rect-split`, Lemma `ex-lem:parity-hopping`, Propositions
     `ex-prop:square-splitting`, `ex-prop:square-tunneling`);
   * `SquareBranchExpansionClaim`, `RectBranchSeparationClaim` — the local branch energies;
   * `LandauReductionClaim` — §5 (Proposition `prop:high-exact-reduction`, Lemma
     `lem:high-weighted-estimates`, §5.4);
   These need semiclassical analysis of unbounded magnetic Schrödinger operators (Agmon
   estimates, Helffer–Sjöstrand multiple wells, WKB, Landau-level compression, Borel functional
   calculus of unbounded operators) that Mathlib does not have.

The link between a reduction and the physical operator is recorded by `RealizesMagnetic`: the
island operator is (isometrically) the restriction of the magnetic Schrödinger expression
`(hD₁)² + (hD₂ - 𝓑x₁)² + V` in the weak sense on test functions.  That the island subspace is
the full spectral subspace `Ran 1_{I_h}(H_h)` cannot be expressed without the spectral theorem
for unbounded operators, and is part of the documented content of the reductions.

No file of the library contains `sorry`: every main theorem is proved with the analytic input
(`PaperInputs`) and the continuum reductions (the claims below) as explicit hypotheses.
-/
import ContinuumMagnetic.CriticalCriteria
import ContinuumMagnetic.Covariance
import ContinuumMagnetic.CosineActions
import ContinuumMagnetic.GoodIndices
import ContinuumMagnetic.HallLabels
import ContinuumMagnetic.SquareShell

noncomputable section

open scoped ENNReal NNReal ComplexConjugate
open MeasureTheory Set Filter Topology AMO

namespace CMS

/-! ### The physical operator -/

/-- `L²(ℝ²)`. -/
abbrev L2Plane := Lp ℂ 2 (volume : Measure (ℝ × ℝ))

/-- Smooth compactly supported test functions. -/
def IsTestFunction (φ : ℝ × ℝ → ℂ) : Prop := ContDiff ℝ ⊤ φ ∧ HasCompactSupport φ

/-- The bounded operator `A` on `H` is isometrically realized inside `L²(ℝ²)` as a restriction of
the magnetic Schrödinger operator `(hD₁)² + (hD₂ - B x₁)² + V` (Landau gauge, paper (1.1),
(1.4)): `⟨ι(Aψ), φ⟩ = ⟨ιψ, H φ⟩` for every test function `φ`. -/
def RealizesMagnetic (B h : ℝ) (V : ℝ × ℝ → ℝ) {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (A : H →L[ℂ] H) : Prop :=
  ∃ ι : H →ₗᵢ[ℂ] L2Plane, ∀ ψ : H, ∀ φ : ℝ × ℝ → ℂ, IsTestFunction φ →
    ∫ x, conj ((ι (A ψ) : ℝ × ℝ → ℂ) x) * φ x = ∫ x, conj ((ι ψ : ℝ × ℝ → ℂ) x) * schr B h V φ x

/-! ### Transport of a reduction along an equality of symbols -/

section Cast

variable {Hisl : Type*} [NormedAddCommGroup Hisl] [InnerProductSpace ℂ Hisl] [CompleteSpace Hisl]
  {Hfib : ℝ → Type*} [∀ k, NormedAddCommGroup (Hfib k)] [∀ k, InnerProductSpace ℂ (Hfib k)]
  [∀ k, CompleteSpace (Hfib k)]

/-- Re-index an exact reduction along an equality of symbols (same operators and unitaries). -/
def IslandReduction.cast {α : ℝ} {c c' : Symbol} (I : IslandReduction α c Hisl Hfib)
    (h : c = c') : IslandReduction α c' Hisl Hfib where
  island := I.island
  U := I.U
  reduction := h ▸ I.reduction
  fibre := I.fibre
  Uk := I.Uk
  θ := I.θ
  fibre_reduction := h ▸ I.fibre_reduction

end Cast

/-! ### Asymptotics along `h ↓ 0` -/

lemma tendsto_atTop_of_mul_tendsto {f : ℝ → ℝ} {L : ℝ} (hL : 0 < L)
    (hf : Tendsto (fun h => h * f h) (𝓝[>] 0) (𝓝 L)) : Tendsto f (𝓝[>] 0) atTop := by
  have h1 := hf.pos_mul_atTop hL tendsto_inv_nhdsGT_zero
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
  field_simp

/-! ### The normalized interaction of a scalar island -/

/-- `η = t_min / t_max`. -/
def couplingRatio (t₁ t₂ : ℝ) : ℝ := min t₁ t₂ / max t₁ t₂

/-- `t_max`. -/
def tMax (t₁ t₂ : ℝ) : ℝ := max t₁ t₂

/-- The oriented normalized remainder `R^oriented / t_max` (paper (2.9)): `R/t₁` if `t₁ > t₂`
and `𝓕⁻¹(R)/t₂` otherwise. -/
def orientedRem (t₁ t₂ : ℝ) (R : Symbol) : Symbol :=
  if t₂ < t₁ then ((1 / t₁ : ℝ) : ℂ) • R else ((1 / t₂ : ℝ) : ℂ) • fourierInv R

lemma axialSymbol_eq_islandSym_sub {E₀ t₁ t₂ : ℝ} (ht : t₂ < t₁) (ht₂ : 0 < t₂) (R : Symbol) :
    axialSymbol E₀ t₁ t₂ R = islandSym E₀ (tMax t₁ t₂) true (couplingRatio t₁ t₂)
      (orientedRem t₁ t₂ R) := by
  have ht₁ : t₁ ≠ 0 := (ht₂.trans ht).ne'
  rw [axialSymbol_eq ht₁, tMax, couplingRatio, orientedRem, if_pos ht, max_eq_left ht.le,
    min_eq_right ht.le]
  rfl

lemma axialSymbol_eq_islandSym_super {E₀ t₁ t₂ : ℝ} (ht : t₁ < t₂) (ht₁ : 0 < t₁) (R : Symbol) :
    axialSymbol E₀ t₁ t₂ R = islandSym E₀ (tMax t₁ t₂) false (couplingRatio t₁ t₂)
      (orientedRem t₁ t₂ R) := by
  have ht₂ : t₂ ≠ 0 := (ht₁.trans ht).ne'
  rw [normalized_phys_eq_fourier ht₁.ne' ht₂, tMax, couplingRatio, orientedRem,
    if_neg (not_lt.2 ht.le), max_eq_right ht.le, min_eq_left ht.le]
  rfl

lemma axialSymbol_eq_critSym {E₀ a : ℝ} (ha : a ≠ 0) (R : Symbol) :
    axialSymbol E₀ a a R = critSym E₀ a (((1 / a : ℝ) : ℂ) • R) := by
  rw [axialSymbol_eq ha, div_self ha]
  rfl

lemma orientedRem_selfAdjoint (t₁ t₂ : ℝ) {R : Symbol} (hR : SymbolSelfAdjoint R) :
    SymbolSelfAdjoint (orientedRem t₁ t₂ R) := by
  unfold orientedRem
  split_ifs
  · exact hR.real_smul _
  · exact hR.fourier.fourier.fourier.real_smul _

/-! ### The low-energy exact reductions (paper §3) -/

/-- The multiplicity `d_λ` of the harmonic level `λ_𝐧` of the cosine well. -/
def harmonicMult (μ : ℝ) (n : ℕ × ℕ) : ℕ :=
  {n' : ℕ × ℕ | harmonicLevel μ n' = harmonicLevel μ n}.ncard

/-- **An exact scalar cosine island** at Planck constant `h` (paper (2.4)–(2.8)): the gauged
exact interaction `c = E_h^0 δ₀ + t₁(δ_{±e₁}) + t₂(δ_{±e₂}) + R_h`, an exact reduction of the
island and its Bloch fibres to it, and the realization of the island operator as a restriction
of `H_h = (-ih∇ - A_𝓑)² + V_μ` along the field path `𝓑 = 2πhγ/μ`. -/
structure CosineIsland (μ γ h : ℝ) where
  E₀ : ℝ
  t₁ : ℝ
  t₂ : ℝ
  R : Symbol
  R_sa : SymbolSelfAdjoint R
  Hisl : Type
  [hisl₁ : NormedAddCommGroup Hisl]
  [hisl₂ : InnerProductSpace ℂ Hisl]
  [hisl₃ : CompleteSpace Hisl]
  Hfib : ℝ → Type
  [hfib₁ : ∀ k, NormedAddCommGroup (Hfib k)]
  [hfib₂ : ∀ k, InnerProductSpace ℂ (Hfib k)]
  [hfib₃ : ∀ k, CompleteSpace (Hfib k)]
  red : IslandReduction (freq γ) (axialSymbol E₀ t₁ t₂ R) Hisl Hfib
  physical : RealizesMagnetic (fieldPath μ γ h) h (cosinePotential μ) red.island

attribute [instance] CosineIsland.hisl₁ CosineIsland.hisl₂ CosineIsland.hisl₃
  CosineIsland.hfib₁ CosineIsland.hfib₂ CosineIsland.hfib₃

/-- The island symbol of a cosine island. -/
def CosineIsland.sym {μ γ h : ℝ} (D : CosineIsland μ γ h) : Symbol :=
  axialSymbol D.E₀ D.t₁ D.t₂ D.R

/-- **Exact reduction for unequal side lengths** (paper §3, Propositions
`c-prop:magnetic-carlsson`/`ex-prop:reduction` (exact reduction and weighted coefficient bounds),
`c-prop:exact-cosine-tunneling`, Lemma `ex-lem:parity-hopping` (axial tunneling
`t_j = e^{-S_j/h + o(1/h)}`), Lemma `c-lem:cosine-actions` (`S₁ = S_cos μ`, `S₂ = S_cos`),
`ex-prop:all-rect-split` (every branch of a fixed harmonic cluster is simple), and the weighted
smallness (2.9) of the oriented remainder in every weight `(s₀, log(A/η_h))`).

For every fixed harmonic level `λ_𝐧` and branch `a < d_λ`, there is a family of exact scalar
islands with these properties.  Not formalized (semiclassical analysis). -/
def CosineReductionRectClaim : Prop :=
  ∀ {μ : ℝ}, 0 < μ → μ ≠ 1 → ∀ {γ : ℝ}, Irrational γ → ∀ (n : ℕ × ℕ) (a : ℕ),
    a < harmonicMult μ n → ∃ D : ∀ h : ℝ, CosineIsland μ γ h,
      (∀ᶠ h in 𝓝[>] 0, 0 < (D h).t₁ ∧ 0 < (D h).t₂) ∧
      Tendsto (fun h => h * Real.log (D h).t₁) (𝓝[>] 0) (𝓝 (-cosineAction₁ μ)) ∧
      Tendsto (fun h => h * Real.log (D h).t₂) (𝓝[>] 0) (𝓝 (-cosineAction₂)) ∧
      ∀ A > (1 : ℝ), ∀ s₀ > (0 : ℝ), ∀ ε > (0 : ℝ), ∀ᶠ h in 𝓝[>] 0,
        WSmall s₀ (Real.log (A / couplingRatio (D h).t₁ (D h).t₂))
          (orientedRem (D h).t₁ (D h).t₂ (D h).R) ε

/-- **Exact reduction for the square well** (`μ = 1`; paper §3, Corollary `c-cor:critical`,
Propositions `ex-prop:square-splitting`, `ex-prop:square-tunneling`): the rotation-compatible
construction gives `f_{1,0} = f_{0,1} = a_h ∈ ℝ \ {0}`, a self-dual remainder
(`𝓕(R_h) = R_h`, cf. `CMS.fourier_weylSymbol`), `-h log|a_h| → S_cos`, and
`‖R_h / a_h‖_S → 0` for every fixed weight `S` (paper (eq:critical-error)).
Not formalized (semiclassical analysis). -/
def CosineReductionSquareClaim : Prop :=
  ∀ {γ : ℝ}, Irrational γ → ∀ (n : ℕ × ℕ) (a : ℕ), a < harmonicMult 1 n → ∃ D : ∀ h : ℝ, CosineIsland 1 γ h,
      (∀ᶠ h in 𝓝[>] 0, (D h).t₁ = (D h).t₂ ∧ (D h).t₁ ≠ 0 ∧ fourier (D h).R = (D h).R) ∧
      Tendsto (fun h => h * Real.log |(D h).t₁|) (𝓝[>] 0) (𝓝 (-cosineAction₂)) ∧
      ∀ S > (0 : ℝ), ∀ ε > (0 : ℝ), ∀ᶠ h in 𝓝[>] 0,
        WSmall S S (((1 / (D h).t₁ : ℝ) : ℂ) • (D h).R) ε

/-! ### Theorem `cor:cosine` (i)–(ii), unequal side lengths -/

/-- The common off-critical family argument: along a family with `log(1/η_h) → ∞` and remainder
small in every weight, the off-critical conclusions hold eventually, and the prepared exponent
exceeds any given level. -/
theorem offCritical_eventually (P : PaperInputs) {α : ℝ} (hα : Irrational α) (sub : Bool) {E₀ tmax η : ℝ → ℝ}
    {R : ℝ → Symbol} (hpos : ∀ᶠ h in 𝓝[>] 0, 0 < tmax h ∧ 0 < η h ∧ SymbolSelfAdjoint (R h))
    (hη : Tendsto (fun h => Real.log (1 / η h)) (𝓝[>] 0) atTop)
    (hR : ∀ A > (1 : ℝ), ∀ s₀ > (0 : ℝ), ∀ ε > (0 : ℝ), ∀ᶠ h in 𝓝[>] 0,
      WSmall s₀ (Real.log (A / η h)) (R h) ε) :
    ∃ C ε : ℝ → ℝ, ∀ B : ℝ, ∀ᶠ h in 𝓝[>] 0, B < Real.log (1 / η h) - C h * ε h ∧
      ∀ {Hisl : Type} [NormedAddCommGroup Hisl] [InnerProductSpace ℂ Hisl] [CompleteSpace Hisl]
        {Hfib : ℝ → Type} [∀ k, NormedAddCommGroup (Hfib k)]
        [∀ k, InnerProductSpace ℂ (Hfib k)] [∀ k, CompleteSpace (Hfib k)]
        (I : IslandReduction α (islandSym (E₀ h) (tmax h) sub (η h) (R h)) Hisl Hfib),
        OffCriticalIsland α (E₀ h) (tmax h) sub (η h) (R h) (C h) (ε h) I := by
  obtain ⟨A, hA, s₀, hs₀, hthm⟩ := offCritical_continuum P
  obtain ⟨εstar, hε, C, hC, hthm⟩ := hthm (1 / 2) ⟨by norm_num, by norm_num⟩
  refine ⟨fun _ => C, fun h => wnorm s₀ (Real.log (A / η h)) (R h), fun B => ?_⟩
  have hsmall := hR A hA s₀ hs₀ εstar hε
  have hbig := hη.eventually_gt_atTop (max (Real.log 2) (B + C * εstar))
  filter_upwards [hpos, hsmall, hbig] with h ⟨htm, hηpos, hsa⟩ hW hlog
  have hη2 : η h ≤ 1 - 1 / 2 := by
    have h1 : Real.log 2 < Real.log (1 / η h) := (le_max_left _ _).trans_lt hlog
    have h2 : 2 < 1 / η h := (Real.log_lt_log_iff (by norm_num) (by positivity)).1 h1
    rw [lt_div_iff₀ hηpos] at h2
    linarith
  refine ⟨?_, fun I => hthm α (η h) (E₀ h) (tmax h) (R h) sub hα hηpos hη2 htm hsa hW I⟩
  have : C * wnorm s₀ (Real.log (A / η h)) (R h) ≤ C * εstar :=
    mul_le_mul_of_nonneg_left hW.2.le hC.le
  have := (le_max_right _ _).trans_lt hlog
  linarith

/-- **Theorem `cor:cosine`, unequal side lengths `μ ≠ 1`.**  For every irrational flux, every
fixed harmonic level and every branch, for all sufficiently small `h` the exact scalar island
`Σ_{λ,a,h}` is a dry Cantor set (every internal allowed label is an open gap), the full
two-dimensional island restriction is purely absolutely continuous, `|Σ| > 0`,
`dim_H Σ = 1`, and the restrictions of almost every Bloch fibre to the island are

* purely absolutely continuous if `μ < 1`;
* Anderson localized (complete eigenbasis) if `μ > 1` and `β(α) < ∞`;
* purely singular continuous if `μ > 1` and `β(α) = ∞`. -/
theorem cosine_rectangular (P : PaperInputs) (hred : CosineReductionRectClaim) {μ : ℝ} (hμ : 0 < μ) (hμ1 : μ ≠ 1) {γ : ℝ} (hγ : Irrational γ)
    (n : ℕ × ℕ) (a : ℕ) (ha : a < harmonicMult μ n) :
    ∃ D : ∀ h : ℝ, CosineIsland μ γ h, ∀ᶠ h in 𝓝[>] 0,
      DryIsland (freq γ) (D h).sym ∧
      PurelyACH (D h).red.island ∧
      0 < volume (islandSpec (freq γ) (D h).sym) ∧ dimH (islandSpec (freq γ) (D h).sym) = 1 ∧
      (μ < 1 → ∀ᵐ k ∂volume, PurelyACH ((D h).red.fibre k)) ∧
      (1 < μ → beta (freq γ) ≠ ⊤ →
        ∀ᵐ k ∂volume, HasCompleteEigenbasisOn ((D h).red.fibre k) (islandSpec (freq γ) (D h).sym)) ∧
      (1 < μ → beta (freq γ) = ⊤ →
        ∀ᵐ k ∂volume, PurelySCOnH ((D h).red.fibre k) (islandSpec (freq γ) (D h).sym)) := by
  obtain ⟨D, hpos, ht₁, ht₂, hR⟩ := hred hμ hμ1 hγ n a ha
  refine ⟨D, ?_⟩
  have hα : Irrational (freq γ) := by unfold freq; exact hγ.neg
  have hS₁ : 0 < cosineAction₁ μ := cosineAction₁_pos hμ
  -- `h log(t_max/t_min) → |S₁ - S₂|`
  have hlogratio : ∀ {u v : ℝ → ℝ} {Su Sv : ℝ}, Su < Sv →
      (∀ᶠ h in 𝓝[>] 0, 0 < u h ∧ 0 < v h) →
      Tendsto (fun h => h * Real.log (u h)) (𝓝[>] 0) (𝓝 (-Su)) →
      Tendsto (fun h => h * Real.log (v h)) (𝓝[>] 0) (𝓝 (-Sv)) →
      Tendsto (fun h => Real.log (u h / v h)) (𝓝[>] 0) atTop := by
    intro u v Su Sv hlt hp hu hv
    refine tendsto_atTop_of_mul_tendsto (L := Sv - Su) (by linarith) ?_
    have := hu.sub hv
    rw [show -Su - -Sv = Sv - Su by ring] at this
    refine this.congr' ?_
    filter_upwards [hp] with h ⟨hu0, hv0⟩
    rw [Real.log_div hu0.ne' hv0.ne']
    ring
  rcases lt_or_gt_of_ne hμ1 with hlt | hgt
  · -- `μ < 1`: `S₁ < S₂`, `t₁ > t₂`, subcritical physical orientation
    have hS : cosineAction₁ μ < cosineAction₂ := by
      unfold cosineAction₁ cosineAction₂
      nlinarith [Scos_pos]
    have hrat := hlogratio hS hpos ht₁ ht₂
    have hord : ∀ᶠ h in 𝓝[>] 0, (D h).t₂ < (D h).t₁ := by
      filter_upwards [hrat.eventually_gt_atTop 0, hpos] with h h1 ⟨h₁, h₂⟩
      have := Real.exp_lt_exp.2 h1
      rw [Real.exp_zero, Real.exp_log (div_pos h₁ h₂), one_lt_div h₂] at this
      exact this
    have hη : Tendsto (fun h => Real.log (1 / couplingRatio (D h).t₁ (D h).t₂)) (𝓝[>] 0)
        atTop := hrat.congr' (by
      filter_upwards [hord] with h hh
      rw [couplingRatio, min_eq_right hh.le, max_eq_left hh.le, one_div_div])
    obtain ⟨C, ε, hfam⟩ := offCritical_eventually P hα true
      (E₀ := fun h => (D h).E₀) (tmax := fun h => tMax (D h).t₁ (D h).t₂)
      (η := fun h => couplingRatio (D h).t₁ (D h).t₂)
      (R := fun h => orientedRem (D h).t₁ (D h).t₂ (D h).R)
      (by
        filter_upwards [hpos] with h ⟨h₁, h₂⟩
        exact ⟨lt_max_of_lt_left h₁, div_pos (lt_min h₁ h₂) (lt_max_of_lt_left h₁),
          orientedRem_selfAdjoint _ _ (D h).R_sa⟩)
      hη hR
    filter_upwards [hfam 0, hord, hpos] with h ⟨_, hoff⟩ hh ⟨_, h₂⟩
    have hsym := axialSymbol_eq_islandSym_sub (E₀ := (D h).E₀) hh h₂ (D h).R
    have H := hoff ((D h).red.cast hsym)
    have hsym' : (D h).sym = islandSym (D h).E₀ (tMax (D h).t₁ (D h).t₂) true
        (couplingRatio (D h).t₁ (D h).t₂) (orientedRem (D h).t₁ (D h).t₂ (D h).R) := hsym
    rw [hsym']
    exact ⟨H.dry, H.ac2d, H.measure.1, H.measure.2, fun _ => H.fibres_sub rfl,
      fun h1 => absurd h1 (not_lt.2 hlt.le), fun h1 => absurd h1 (not_lt.2 hlt.le)⟩
  · -- `μ > 1`: `S₂ < S₁`, `t₂ > t₁`, supercritical physical orientation
    have hS : cosineAction₂ < cosineAction₁ μ := by
      unfold cosineAction₁ cosineAction₂
      nlinarith [Scos_pos]
    have hpos' : ∀ᶠ h in 𝓝[>] 0, 0 < (D h).t₂ ∧ 0 < (D h).t₁ := by
      filter_upwards [hpos] with h ⟨h₁, h₂⟩; exact ⟨h₂, h₁⟩
    have hrat := hlogratio hS hpos' ht₂ ht₁
    have hord : ∀ᶠ h in 𝓝[>] 0, (D h).t₁ < (D h).t₂ := by
      filter_upwards [hrat.eventually_gt_atTop 0, hpos] with h h1 ⟨h₁, h₂⟩
      have := Real.exp_lt_exp.2 h1
      rw [Real.exp_zero, Real.exp_log (div_pos h₂ h₁), one_lt_div h₁] at this
      exact this
    have hη : Tendsto (fun h => Real.log (1 / couplingRatio (D h).t₁ (D h).t₂)) (𝓝[>] 0)
        atTop := hrat.congr' (by
      filter_upwards [hord] with h hh
      rw [couplingRatio, min_eq_left hh.le, max_eq_right hh.le, one_div_div])
    obtain ⟨C, ε, hfam⟩ := offCritical_eventually P hα false
      (E₀ := fun h => (D h).E₀) (tmax := fun h => tMax (D h).t₁ (D h).t₂)
      (η := fun h => couplingRatio (D h).t₁ (D h).t₂)
      (R := fun h => orientedRem (D h).t₁ (D h).t₂ (D h).R)
      (by
        filter_upwards [hpos] with h ⟨h₁, h₂⟩
        exact ⟨lt_max_of_lt_left h₁, div_pos (lt_min h₁ h₂) (lt_max_of_lt_left h₁),
          orientedRem_selfAdjoint _ _ (D h).R_sa⟩)
      hη hR
    filter_upwards [hfam ((beta (freq γ)).toReal), hord, hpos] with h ⟨hβ, hoff⟩ hh ⟨h₁, _⟩
    have hsym := axialSymbol_eq_islandSym_super (E₀ := (D h).E₀) hh h₁ (D h).R
    have H := hoff ((D h).red.cast hsym)
    have hsym' : (D h).sym = islandSym (D h).E₀ (tMax (D h).t₁ (D h).t₂) false
        (couplingRatio (D h).t₁ (D h).t₂) (orientedRem (D h).t₁ (D h).t₂ (D h).R) := hsym
    rw [hsym']
    refine ⟨H.dry, H.ac2d, H.measure.1, H.measure.2,
      fun h1 => absurd h1 (not_lt.2 hgt.le), fun _ hβtop => ?_, fun _ hβtop => ?_⟩
    · rw [H.spec]
      refine H.localized_of_beta_lt ?_
      rw [← ENNReal.ofReal_toReal hβtop]
      exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).2 hβ
    · rw [H.spec]
      exact H.sc_of_beta_top hβtop

/-! ### Theorem `cor:cosine` (i)–(ii), the square well -/

/-- **Theorem `cor:cosine`, square well `μ = 1`.**  For every irrational flux, every fixed
harmonic level and every branch, for all sufficiently small `h`: the island is a Cantor set of
Lebesgue measure zero with every internal allowed label realized by an open gap,
`𝓗^{1/2}(Σ) < ∞` (so `dim_H Σ ≤ 1/2`), the full two-dimensional island restriction is purely
singular continuous, almost every fibre island is purely singular continuous when `β(α) > 0`,
and `dim_H Σ = 0` at ordinary Liouville flux.  One threshold in `h` works for all labels. -/
theorem cosine_square (P : PaperInputs) (hred : CosineReductionSquareClaim) {γ : ℝ}
    (hγ : Irrational γ) (n : ℕ × ℕ) (a : ℕ)
    (ha : a < harmonicMult 1 n) :
    ∃ D : ∀ h : ℝ, CosineIsland 1 γ h, ∀ᶠ h in 𝓝[>] 0,
      IsCantor (islandSpec (freq γ) (D h).sym) ∧
      (∃ ν, IsDOSMeasure (op (freq γ) (D h).sym) ν ∧
        AllGapsOpen (islandSpec (freq γ) (D h).sym) ν (freq γ)) ∧
      volume (islandSpec (freq γ) (D h).sym) = 0 ∧
      μH[1 / 2] (islandSpec (freq γ) (D h).sym) < ⊤ ∧
      dimH (islandSpec (freq γ) (D h).sym) ≤ ((1 / 2 : ℝ≥0) : ℝ≥0∞) ∧
      PurelySCH (D h).red.island ∧
      (0 < beta (freq γ) → ∀ᵐ k ∂volume, PurelySCH ((D h).red.fibre k)) ∧
      (OrdinaryLiouville (freq γ) → dimH (islandSpec (freq γ) (D h).sym) = 0) := by
  obtain ⟨D, hD, -, hsmall⟩ := hred hγ n a ha
  refine ⟨D, ?_⟩
  have hα : Irrational (freq γ) := by unfold freq; exact hγ.neg
  obtain ⟨S, hS, εc, hεc, hcrit⟩ := critical_continuum P
  obtain ⟨Sstar, hSstar, hgeo⟩ := critical_continuum_geometry P (freq γ) hα
  set S' := max Sstar S with hS'
  have hS'pos : 0 < S' := lt_max_of_lt_left hSstar
  obtain ⟨ρ, hρ, hρgeo⟩ := hgeo S' (le_max_left _ _)
  obtain ⟨ρL, hρL, hliou⟩ : ∃ ρL > (0 : ℝ), OrdinaryLiouville (freq γ) →
      ∀ (E₀ a : ℝ) (R : Symbol), a ≠ 0 → SymbolSelfAdjoint R → fourier R = R →
        WSmall S' S' R ρL → dimH (islandSpec (freq γ) (critSym E₀ a R)) = 0 := by
    by_cases hL : OrdinaryLiouville (freq γ)
    · obtain ⟨ρL, hρL, h⟩ := critical_continuum_liouville P _ hα hL S' hS'pos
      exact ⟨ρL, hρL, fun _ => h⟩
    · exact ⟨1, one_pos, fun h => absurd h hL⟩
  filter_upwards [hD, hsmall S' hS'pos (min (min ρ εc) ρL) (lt_min (lt_min hρ hεc) hρL)]
    with h ⟨heq, hne, hF⟩ hW
  have hsym : (D h).sym = critSym (D h).E₀ (D h).t₁ (((1 / (D h).t₁ : ℝ) : ℂ) • (D h).R) := by
    show axialSymbol (D h).E₀ (D h).t₁ (D h).t₂ (D h).R = _
    rw [← heq]
    exact axialSymbol_eq_critSym hne _
  have hsa : SymbolSelfAdjoint (((1 / (D h).t₁ : ℝ) : ℂ) • (D h).R) := (D h).R_sa.real_smul _
  have hF' : fourier (((1 / (D h).t₁ : ℝ) : ℂ) • (D h).R) = ((1 / (D h).t₁ : ℝ) : ℂ) • (D h).R := by
    rw [fourierSym_smul, hF]
  have hWρ := WSmall.of_le hW ((min_le_left _ _).trans (min_le_left _ _))
  have hWc := WSmall.of_le (hW.mono_weights (le_max_right Sstar S) (le_max_right Sstar S))
    ((min_le_left _ _).trans (min_le_right _ _))
  have hWL := WSmall.of_le hW (min_le_right _ _)
  have H := hcrit (freq γ) (D h).E₀ (D h).t₁ _ hα hne hsa hF' hWc ((D h).red.cast hsym)
  obtain ⟨hgaps, hH, hdim⟩ := hρgeo (D h).E₀ (D h).t₁ _ hne hsa hF' hWρ
  rw [hsym]
  exact ⟨H.cantor, hgaps, H.null, hH, hdim, H.sc2d, H.fibres,
    fun hL => hliou hL _ _ _ hne hsa hF' hWL⟩

/-! ### Branch separation in Theorem `cor:cosine` -/

/-- **Proposition `ex-prop:square-splitting`, energy expansion** (degenerate perturbation theory):
at `μ = 1` the `N+1` filled-well branches of the shell `λ_N` satisfy
`ε_{N,a}(h) = λ_N h + ν_{N,a} h² + O(h³)`, with `ν_{N,a}` the eigenvalues of the magnetic
splitting matrix `K_N` at `b = 2πγ` (`CMS.squareShellMatrix`).  Not formalized. -/
def SquareBranchExpansionClaim : Prop :=
  ∀ (N : ℕ) {γ : ℝ}, Irrational γ → ∃ ε : Fin (N + 1) → ℝ → ℝ, ∃ C h₀ : ℝ, 0 < h₀ ∧ ∀ a h, 0 < h → h < h₀ →
      |ε a h - squareLevel N * h -
        (squareShellMatrix_isHermitian N (2 * Real.pi * γ)).eigenvalues a * h ^ 2| ≤ C * h ^ 3

/-- **Square-shell branch separation** `|ε_{N,a}(h) - ε_{N,b}(h)| ≥ c_{N,γ} h²` (`a ≠ b`),
proved from the expansion and the simplicity of the spectrum of `K_N`
(`CMS.squareShell_eigenvalues_injective`, since `b = 2πγ ≠ 0`). -/
theorem square_branch_separation (hexp : SquareBranchExpansionClaim) (N : ℕ) {γ : ℝ}
    (hγ : Irrational γ) :
    ∃ ε : Fin (N + 1) → ℝ → ℝ,
      (∃ C h₀ : ℝ, 0 < h₀ ∧ ∀ a h, 0 < h → h < h₀ →
        |ε a h - squareLevel N * h -
          (squareShellMatrix_isHermitian N (2 * Real.pi * γ)).eigenvalues a * h ^ 2| ≤
            C * h ^ 3) ∧
      ∃ c > (0 : ℝ), ∃ h₁ > (0 : ℝ), ∀ a a', a ≠ a' → ∀ h, 0 < h → h < h₁ →
        c * h ^ 2 ≤ |ε a h - ε a' h| := by
  obtain ⟨ε, C, h₀, hh₀, hexp⟩ := hexp N hγ
  have hb : 2 * Real.pi * γ ≠ 0 := mul_ne_zero (by positivity) hγ.ne_zero
  exact ⟨ε, ⟨C, h₀, hh₀, hexp⟩, branch_separation_family hh₀
    (squareShell_eigenvalues_injective hb _) hexp⟩

/-- **Proposition `ex-prop:all-rect-split`** (`μ ≠ 1`): distinct branches of a fixed harmonic
cluster separate polynomially, `|ε_{λ,a}(h) - ε_{λ,b}(h)| ≥ c h⁴`.  Not formalized. -/
def RectBranchSeparationClaim : Prop :=
  ∀ {μ : ℝ}, 0 < μ → μ ≠ 1 → ∀ {γ : ℝ}, Irrational γ → ∀ (n : ℕ × ℕ), ∃ ε : ℕ → ℝ → ℝ, ∃ c > (0 : ℝ), ∀ a b, a < harmonicMult μ n → b < harmonicMult μ n →
      a ≠ b → ∀ᶠ h in 𝓝[>] 0, c * h ^ 4 ≤ |ε a h - ε b h|

/-! ### High Landau levels (paper §1.4 and §5) -/

section HighLandau

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The high-Landau potential `V = V̄ + 2a_x cos 2πx + 2a_y cos 2πy + W` (paper (hi-eq:model)),
with `W(x,y) = Re ∑ ŵ(m) e^{2πi(m₁x + m₂y)}`. -/
def landauPotential (Vbar ax ay : ℝ) (w : Symbol) (x : ℝ × ℝ) : ℝ :=
  Vbar + 2 * ax * Real.cos (2 * Real.pi * x.1) + 2 * ay * Real.cos (2 * Real.pi * x.2) +
    (fseries w x.1 x.2).re

/-- `T` realizes the Weyl series `c` in the guiding-center representation with dominated spectral
type (paper §5.4, (hi-eq:type-domination)): its spectrum is the common spectrum of the fibres and
every scalar spectral measure is absolutely continuous with respect to the IDS of `c`. -/
structure DominatedRealization (α : ℝ) (c : Symbol) (T : H →L[ℂ] H) : Prop where
  spec : spectrum ℝ T = islandSpec α c
  dom : ∀ ν, IsDOSMeasure (op α c) ν → ∀ ψ, ∃ μ, IsSpectralMeasureH T ψ μ ∧ μ ≪ ν

lemma purelyACH_of_dominated {T : H →L[ℂ] H} {ν : Measure ℝ}
    (hdom : ∀ ψ, ∃ μ, IsSpectralMeasureH T ψ μ ∧ μ ≪ ν) (hac : ν ≪ volume) : PurelyACH T :=
  fun ψ => by
    obtain ⟨μ, hμ, hμν⟩ := hdom ψ
    exact ⟨μ, hμ, hμν.trans hac⟩

lemma purelySCH_of_dominated {T : H →L[ℂ] H} {ν : Measure ℝ} {S : Set ℝ}
    (hdom : ∀ ψ, ∃ μ, IsSpectralMeasureH T ψ μ ∧ μ ≪ ν) (hat : ∀ t, ν {t} = 0)
    (hS : MeasurableSet S) (hνS : ν Sᶜ = 0) (hvol : volume S = 0) : PurelySCH T := by
  intro ψ
  obtain ⟨μ, hμ, hμν⟩ := hdom ψ
  refine ⟨μ, hμ, ?_, fun E _ => hμν (hat E)⟩
  rw [Measure.restrict_univ]
  exact ⟨Sᶜ, hS.compl, hμν hνS, by rwa [compl_compl]⟩

end HighLandau

/-- `a_* = max(a_x, a_y)`. -/
def aStar (ax ay : ℝ) : ℝ := max ax ay

/-- The good-index quantity `|cos(2√(n s_B) - π/4)|` (paper (hi-eq:good-index)). -/
def goodCos (h B : ℝ) (n : ℕ) : ℝ := |Real.cos (2 * √((n : ℝ) * sB h B) - Real.pi / 4)|

/-- **An exact Landau cluster** (paper Proposition `prop:high-exact-reduction`): the restriction
`A_n` of `H` to `Ran Π_n`, `Π_n = 𝟙_{[E_n - hB, E_n + hB]}(H)`, realizes the Weyl series
`E_n + a_* f_n (U + U^{-1} + η(V + V^{-1}) + R_n)` in the oriented guiding-center generators. -/
structure LandauCluster (h B Vbar ax ay : ℝ) (w : Symbol) (n : ℕ) where
  R : Symbol
  R_sa : SymbolSelfAdjoint R
  /-- `f_n ≠ 0`. -/
  formFactor_ne : landauFormFactor n (sB h B) ≠ 0
  Hc : Type
  [hc₁ : NormedAddCommGroup Hc]
  [hc₂ : InnerProductSpace ℂ Hc]
  [hc₃ : CompleteSpace Hc]
  A : Hc →L[ℂ] Hc
  realization : DominatedRealization (alphaB h B)
    (affineSym (landauLevel h B Vbar n) (aStar ax ay * landauFormFactor n (sB h B))
      (amo ((min ax ay / aStar ax ay : ℝ) : ℂ) + R)) A
  physical : RealizesMagnetic B h (landauPotential Vbar ax ay w) A
  /-- The physical Bloch fibres `H(k)|_{Ran Π_n(k)}` (paper Corollary `cor:high-energy-fibres`). -/
  Hfib : ℝ → Type
  [hf₁ : ∀ k, NormedAddCommGroup (Hfib k)]
  [hf₂ : ∀ k, InnerProductSpace ℂ (Hfib k)]
  [hf₃ : ∀ k, CompleteSpace (Hfib k)]
  fibre : ∀ k, Hfib k →L[ℂ] Hfib k
  Uk : ∀ k, L2 ℤ ≃ₗᵢ[ℂ] Hfib k
  θ : ℝ
  /-- Exact fibre reduction: `cos 2πy` produces the hopping and `cos 2πx` the quasiperiodic
  diagonal, so the physical fibre is the subcritical family when `a_y > a_x` and its Fourier dual
  (the supercritical family) when `a_x > a_y` (paper, after Corollary `cor:high-energy-fibres`). -/
  fibre_reduction : ∀ᵐ k ∂volume, Intertwines (Uk k)
    (op (alphaB h B) (islandSym (landauLevel h B Vbar n) (aStar ax ay * landauFormFactor n (sB h B))
      (decide (ax < ay)) (min ax ay / aStar ax ay) R) ((k + θ) / (2 * Real.pi)))
    (fibre k)

attribute [instance] LandauCluster.hc₁ LandauCluster.hc₂ LandauCluster.hc₃
  LandauCluster.hf₁ LandauCluster.hf₂ LandauCluster.hf₃

/-- The cluster `𝒞_n = spec(H) ∩ [E_n - hB, E_n + hB]`. -/
def LandauCluster.cluster {h B Vbar ax ay : ℝ} {w : Symbol} {n : ℕ}
    (D : LandauCluster h B Vbar ax ay w n) : Set ℝ := spectrum ℝ D.A

/-- **Proposition `prop:high-exact-reduction`** with Lemma `lem:high-weighted-estimates` and the
oscillatory form-factor asymptotics `|f_n| ≍ n^{-1/4} |cos(2√(n s_B) - π/4)|` (§5.5): for
`0 < σ < ρ` there are `C > 0` and `δ_n` with `δ_n n^{1/8} → 0` (in the paper `δ_n = C n^{-1/4} log n`) such that for
all large `n` with nonzero oscillation factor there is an exact Landau cluster whose normalized
remainder satisfies `‖R_n‖_σ · |cos(2√(n s_B) - π/4)| ≤ C ‖W‖_ρ / a_* + δ_n`.  In the
rotation-symmetric case the remainder is self-dual.  Not formalized. -/
def LandauReductionClaim : Prop :=
  ∀ {h B Vbar ax ay : ℝ}, 0 < h → 0 < B → 0 < ax → 0 < ay → Irrational (alphaB h B) →
    ∀ {w : Symbol}, SymbolSelfAdjoint w →
    (w 0 = 0 ∧ w (1, 0) = 0 ∧ w (-1, 0) = 0 ∧ w (0, 1) = 0 ∧ w (0, -1) = 0) →
    ∀ {σ ρ : ℝ}, 0 < σ → σ < ρ →
    (Summable fun p : ℤ × ℤ => ‖w p‖ * Real.exp (ρ * |(p.1 : ℝ)| + ρ * |(p.2 : ℝ)|)) →
    ∃ C > (0 : ℝ), ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => δ n * (n : ℝ) ^ (1 / 8 : ℝ)) atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, goodCos h B n ≠ 0 →
      ∃ D : LandauCluster h B Vbar ax ay w n,
        (Summable fun p : ℤ × ℤ => ‖D.R p‖ * Real.exp (σ * |(p.1 : ℝ)| + σ * |(p.2 : ℝ)|)) ∧
        wnorm σ σ D.R * goodCos h B n ≤ C * (wnorm ρ ρ w / aStar ax ay) + δ n ∧
        (ax = ay → AMO.fourier w = w → AMO.fourier D.R = D.R)

/-- The normalized remainder of a good Landau cluster is small: if `‖W‖_ρ ≤ ε a_*` and the
oscillation factor is at least `Kε`, then eventually `‖R_n‖_σ ≤ 2C/K`. -/
lemma landau_remainder_small {C K ε a W d x : ℝ} (hC : 0 < C) (hK : 0 < K) (hε : 0 < ε)
    (ha : 0 < a) (hW : W ≤ ε * a) (hd : d ≤ C * ε) (hx : K * ε ≤ x) {r : ℝ} (hr0 : 0 ≤ r)
    (hr : r * x ≤ C * (W / a) + d) : r ≤ 2 * C / K := by
  have hKε : 0 < K * ε := mul_pos hK hε
  have hWa : W / a ≤ ε := by rw [div_le_iff₀ ha]; linarith
  have h1 : r * (K * ε) ≤ 2 * C * ε := by
    calc r * (K * ε) ≤ r * x := mul_le_mul_of_nonneg_left hx hr0
      _ ≤ C * (W / a) + d := hr
      _ ≤ C * ε + C * ε := by gcongr
      _ = 2 * C * ε := by ring
  rw [le_div_iff₀ hK]
  nlinarith


/-- An atomless measure stays atomless under an affine change of variables. -/
lemma atomless_map_affine {ν : Measure ℝ} (hat : ∀ t, ν {t} = 0) (E₀ : ℝ) {a : ℝ} (ha : a ≠ 0)
    (t : ℝ) : ν.map (affine E₀ a) {t} = 0 := by
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

/-- **Theorem `thm:high-energy-spectrum`.**  There are analytic-input constants `A, s₀, S` such
that for every choice of the analytic reserve `σ` (with `max(s₀, log(A/η)) < σ` if `η < 1`, and
`S < σ` if `η = 1`) and width `ρ > σ`, there are `K > 0` and `ε₀ > 0` with the following property.
If `‖W‖_ρ ≤ ε a_*` with `0 < ε < ε₀`, then for all sufficiently large `n` with
`|cos(2√(n s_B) - π/4)| ≥ Kε`, the cluster `𝒞_n` is

* (i) for `a_x ≠ a_y`: a Cantor set with every internal label `{kα_B}` realized by an open gap,
  `|𝒞_n| > 0`, `dim_H 𝒞_n = 1`, and the restriction of `H` to the cluster is purely a.c.;
* (ii) for `a_x = a_y` and `W(-y,x) = W(x,y)`: a Cantor set of measure zero, and the
  restriction is purely singular continuous.

The good indices have natural density `1 - (2/π) arcsin(Kε)` (`CMS.goodIndex_density`). -/
theorem high_landau (P : PaperInputs) (hred : LandauReductionClaim) :
    ∃ A > (1 : ℝ), ∃ s₀ > (0 : ℝ), ∃ S > (0 : ℝ),
      ∀ {h B Vbar ax ay : ℝ}, 0 < h → 0 < B → 0 < ax → 0 < ay → Irrational (alphaB h B) →
      ∀ {w : Symbol}, SymbolSelfAdjoint w →
      (w 0 = 0 ∧ w (1, 0) = 0 ∧ w (-1, 0) = 0 ∧ w (0, 1) = 0 ∧ w (0, -1) = 0) →
      ∀ {σ ρ : ℝ}, (ax ≠ ay → max s₀ (Real.log (A / (min ax ay / aStar ax ay))) < σ) →
        (ax = ay → S < σ) → σ < ρ →
        (Summable fun p : ℤ × ℤ => ‖w p‖ * Real.exp (ρ * |(p.1 : ℝ)| + ρ * |(p.2 : ℝ)|)) →
      ∃ K > (0 : ℝ), ∃ ε₀ > (0 : ℝ), ∀ ε, 0 < ε → ε < ε₀ → K * ε < 1 →
        wnorm ρ ρ w ≤ ε * aStar ax ay →
        HasNatDensity {n | K * ε ≤ goodCos h B n} (1 - 2 / Real.pi * Real.arcsin (K * ε)) ∧
        ∀ᶠ n in atTop, K * ε ≤ goodCos h B n → ∃ D : LandauCluster h B Vbar ax ay w n,
          (ax ≠ ay → IsCantor D.cluster ∧
            (∃ ν, IsDOSMeasure (op (alphaB h B) (affineSym (landauLevel h B Vbar n)
                (aStar ax ay * landauFormFactor n (sB h B)) (amo ((min ax ay / aStar ax ay : ℝ) : ℂ) + D.R))) ν ∧
              AllGapsOpen D.cluster ν (alphaB h B)) ∧
            0 < volume D.cluster ∧ dimH D.cluster = 1 ∧ PurelyACH D.A) ∧
          (ax = ay → AMO.fourier w = w →
            IsCantor D.cluster ∧ volume D.cluster = 0 ∧ PurelySCH D.A) := by
  obtain ⟨A, hA, s₀, hs₀, hin⟩ := analytic_input P.dryTenMartini P.spectralTransition
  obtain ⟨S₁, hS₁, ε₁, hε₁, hcrit⟩ := analytic_input_iv P.critical
  obtain ⟨S₂, hS₂, ε₂, hε₂, hids⟩ := P.criticalIDS
  refine ⟨A, hA, s₀, hs₀, max S₁ S₂, lt_max_of_lt_left hS₁, ?_⟩
  intro h B Vbar ax ay hh hB hax hay hα w hw hw0 σ ρ hσsub hσcrit hσρ hwρ
  have hastar : 0 < aStar ax ay := lt_max_of_lt_left hax
  have hσ : 0 < σ := by
    by_cases hxy : ax = ay
    · exact (lt_max_of_lt_left hS₁).trans (hσcrit hxy)
    · exact (hs₀.trans_le (le_max_left _ _)).trans (hσsub hxy)
  obtain ⟨C, hC, δ, hδ, -, hred⟩ := hred (Vbar := Vbar) hh hB hax hay hα hw hw0 hσ hσρ hwρ
  have hdens : ∀ ε : ℝ, 0 < ε → ∀ K : ℝ, 0 < K → K * ε < 1 →
      HasNatDensity {n | K * ε ≤ goodCos h B n} (1 - 2 / Real.pi * Real.arcsin (K * ε)) :=
    fun ε hε K hK h1 => goodIndex_density hh hB (by positivity) h1.le
  have hwnorm : ∀ R : Symbol, 0 ≤ wnorm σ σ R := fun R => tsum_nonneg fun p => by positivity
  by_cases hxy : ax = ay
  · ---------------- the rotation-symmetric critical case `η = 1`
    subst hxy
    have hη1 : ((min ax ax / aStar ax ax : ℝ) : ℂ) = 1 := by
      rw [min_self, aStar, max_self, div_self hax.ne', Complex.ofReal_one]
    set ε' := min ε₁ ε₂
    have hε' : 0 < ε' := lt_min hε₁ hε₂
    refine ⟨4 * C / ε', by positivity, 1, one_pos, fun ε hε _ hKε hW =>
      ⟨hdens ε hε _ (by positivity) hKε, ?_⟩⟩
    filter_upwards [hred, hδ.eventually (Iio_mem_nhds (mul_pos hC hε))] with n hn hδn hgood
    have hcos : goodCos h B n ≠ 0 := ((mul_pos (by positivity) hε).trans_le hgood).ne'
    obtain ⟨D, hsum, hbound, hsymm⟩ := hn hcos
    refine ⟨D, fun h' => absurd rfl h', fun _ hFw => ?_⟩
    have hr := landau_remainder_small hC (by positivity) hε hastar hW hδn.le hgood
      (hwnorm D.R) hbound
    have hr' : wnorm σ σ D.R < ε' := by
      have : 2 * C / (4 * C / ε') = ε' / 2 := by field_simp; ring
      rw [this] at hr; linarith
    have hσS : max S₁ S₂ ≤ σ := (hσcrit rfl).le
    have hWσ : WSmall σ σ D.R ε' := ⟨hsum, hr'⟩
    have h₁ : WSmall S₁ S₁ D.R ε₁ := WSmall.of_le
      (hWσ.mono_weights ((le_max_left _ _).trans hσS) ((le_max_left _ _).trans hσS)) (min_le_left _ _)
    have h₂ : WSmall S₂ S₂ D.R ε₂ := WSmall.of_le
      (hWσ.mono_weights ((le_max_right _ _).trans hσS) ((le_max_right _ _).trans hσS))
      (min_le_right _ _)
    have hF := hsymm rfl hFw
    have hR : SymbolSummable D.R := h₁.summable hS₁.le hS₁.le
    obtain ⟨hcantor, hnull, -, -⟩ := hcrit _ D.R hα D.R_sa hF h₁
    obtain ⟨ν, hν, hat⟩ := hids _ D.R hα D.R_sa hF h₂
    set E := landauLevel h B Vbar n
    set a := aStar ax ax * landauFormFactor n (sB h B)
    have ha : a ≠ 0 := mul_ne_zero hastar.ne' D.formFactor_ne
    have hreal := D.realization
    rw [hη1] at hreal
    have hspecx : ∀ x, spectrum ℝ (op (alphaB h B) (critSym E a D.R) x) =
        affine E a '' Sigma (alphaB h B) 1 D.R := islandSpec_critSym hα hR D.R_sa
    have hcl : D.cluster = affine E a '' Sigma (alphaB h B) 1 D.R := hreal.spec.trans (hspecx 0)
    have hsaH := isSelfAdjoint_H (alphaB h B) 1 hR D.R_sa
    have hνc : IsDOSMeasure (op (alphaB h B) (critSym E a D.R)) (ν.map (affine E a)) := by
      rw [show op (alphaB h B) (critSym E a D.R) = fun x => affineOp E a (H (alphaB h B) 1 D.R x)
        from funext (op_critSym _ E a hR)]
      exact hν.map_affine hsaH E a
    have hvol : volume (affine E a '' Sigma (alphaB h B) 1 D.R) = 0 := volume_image_affine ha hnull
    have hclosed : IsClosed (affine E a '' Sigma (alphaB h B) 1 D.R) := by
      rw [← hspecx 0]; exact AMO.spectrum_real_isClosed _
    have hcarried : ν.map (affine E a) (affine E a '' Sigma (alphaB h B) 1 D.R)ᶜ = 0 := by
      refine dos_compl_eq_zero hνc hclosed ((hcantor.image_affine E ha).1) ?_ (fun x => (hspecx x).le)
      intro x
      rw [op_critSym _ E a hR x]
      exact IsSelfAdjoint.affineOp E a (hsaH x)
    refine ⟨hcl ▸ hcantor.image_affine E ha, hcl ▸ hvol, ?_⟩
    exact purelySCH_of_dominated (hreal.dom _ hνc) (atomless_map_affine hat E ha)
      hclosed.measurableSet hcarried hvol
  · ---------------- the off-critical case `η < 1`
    set η := min ax ay / aStar ax ay with hηdef
    have hη0 : 0 < η := div_pos (lt_min hax hay) hastar
    have hη1 : η < 1 := by
      rw [div_lt_one hastar]
      rcases lt_or_gt_of_ne hxy with hlt | hgt
      · rw [min_eq_left hlt.le, aStar, max_eq_right hlt.le]; exact hlt
      · rw [min_eq_right hgt.le, aStar, max_eq_left hgt.le]; exact hgt
    obtain ⟨εs, hεs, Cst, hCst, hthm⟩ := hin (1 - η) ⟨by linarith, by linarith⟩
    refine ⟨4 * C / εs, by positivity, 1, one_pos, fun ε hε _ hKε hW =>
      ⟨hdens ε hε _ (by positivity) hKε, ?_⟩⟩
    filter_upwards [hred, hδ.eventually (Iio_mem_nhds (mul_pos hC hε))] with n hn hδn hgood
    have hcos : goodCos h B n ≠ 0 := ((mul_pos (by positivity) hε).trans_le hgood).ne'
    obtain ⟨D, hsum, hbound, -⟩ := hn hcos
    refine ⟨D, fun _ => ?_, fun h' => absurd h' hxy⟩
    have hr := landau_remainder_small hC (by positivity) hε hastar hW hδn.le hgood
      (hwnorm D.R) hbound
    have hr' : wnorm σ σ D.R < εs := by
      have : 2 * C / (4 * C / εs) = εs / 2 := by field_simp; ring
      rw [this] at hr; linarith
    have hσs := hσsub hxy
    have hsmall : WSmall s₀ (Real.log (A / η)) D.R εs :=
      (WSmall.mono_weights ((le_max_left _ _).trans hσs.le) ((le_max_right _ _).trans hσs.le)
        ⟨hsum, hr'⟩)
    have hlog : 0 ≤ Real.log (A / η) := Real.log_nonneg (by
      rw [le_div_iff₀ hη0]; linarith)
    have hR : SymbolSummable D.R := hsmall.summable hs₀.le hlog
    obtain ⟨hD, hT⟩ := hthm _ η D.R hα hη0 (by linarith) D.R_sa hsmall
    set E := landauLevel h B Vbar n
    set a := aStar ax ay * landauFormFactor n (sB h B)
    have ha : a ≠ 0 := mul_ne_zero hastar.ne' D.formFactor_ne
    have hcl : D.cluster = affine E a '' Sigma (alphaB h B) η D.R :=
      D.realization.spec.trans
        (islandSpec_eq (alphaB h B) E a true η hα hR D.R_sa hD.dual_spectrum 0)
    obtain ⟨ν, hνH, -, hgaps⟩ := hD.gaps
    obtain ⟨ν', hν'H, hac⟩ := hT.ids_ac
    have hνν' : ν = ν' := hνH.unique hν'H
    subst hνν'
    have := hνH.1
    have hat : ∀ t, ν {t} = 0 := fun t => hac (Real.volume_singleton)
    have hsaH := isSelfAdjoint_H (alphaB h B) η hR D.R_sa
    have hνc : IsDOSMeasure (op (alphaB h B) (islandSym E a true η D.R)) (ν.map (affine E a)) := by
      rw [show op (alphaB h B) (islandSym E a true η D.R) =
          fun x => affineOp E a (H (alphaB h B) η D.R x) from
        funext (op_islandSym (alphaB h B) E a true η hR)]
      exact hνH.map_affine hsaH E a
    have hpos := hT.volume_Sigma_pos hα hR D.R_sa
    have hv : 0 < volume (affine E a '' Sigma (alphaB h B) η D.R) := by
      refine pos_iff_ne_zero.2 fun h0 => hpos.1.ne' ?_
      have := volume_preimage_affine (E₀ := E) ha h0
      rwa [preimage_image_eq _ (affine_injective ha)] at this
    rw [hcl]
    exact ⟨hD.cantor.image_affine E ha, ⟨_, hνc, hgaps.map_affine_ne hat hα E ha⟩, hv,
      dimH_eq_one_of_volume_pos hv,
      purelyACH_of_dominated (D.realization.dom _ hνc) (AbsolutelyContinuous.map_affine hac ha)⟩

/-! ### The continuum input as a bundle -/

/-- **All continuum input of Paper III** (§3 and §5), as hypotheses. -/
structure ContinuumInputs : Prop where
  cosineRect : CosineReductionRectClaim
  cosineSquare : CosineReductionSquareClaim
  squareBranches : SquareBranchExpansionClaim
  rectBranches : RectBranchSeparationClaim
  landau : LandauReductionClaim

end CMS
