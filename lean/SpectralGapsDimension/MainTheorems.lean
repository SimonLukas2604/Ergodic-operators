/-
Copyright (c) 2026. Formalization of
  S. Becker, "Self-dual perturbations of the critical almost Mathieu operator:
  Dry Ten Martini and Hausdorff dimension" (Paper II).

# Main results  (paper §1: Theorems 1.1 and 1.2)

The model (eqs. (1.1)–(1.3)) is the critical operator
`H_{α,x} = U + U^{-1} + V_x + V_x^{-1} + R_{α,x}`, i.e. `AMO.H α 1 R x` with the Weyl series
of Paper I, and perturbations `R` that are Hermitian and Fourier self-dual (`SelfDual`):
`R_{-r,-s} = conj R_{r,s}` and `R_{r,s} = R_{s,-r}`.  The isotropic analytic norm is
`‖R‖_S = ∑ |R_{r,s}| e^{S(|r|+|s|)} = AMO.wnorm S S R`; `AMO.WSmall S S R ρ` means
`‖R‖_S < ρ`.  The spectrum is `Σ_α(R) = AMO.Sigma α 1 R` (phase independent for irrational
`α`, Paper I), its labels are measured by the density of states (`AMO.IsDOSMeasure`, whose
distribution function is the IDS `N_R`), and "every label of `Λ_α` is open" is
`AMO.AllGapsOpen`.

## Proof architecture

Paper inputs whose proofs need theory that Mathlib does not have are stated faithfully as
propositions `…Claim : Prop` (not asserted; no axioms are added), bundled in `PaperIIInputs`,
and the main theorems take `P : PaperIIInputs` as a hypothesis:

| Lean | Paper | needs |
|---|---|---|
| `ComparisonClaim` | Thm 3.6 (`gap:thm:comparison`) | Thouless formula, Jitomirskaya–Marx, rooted resolvents |
| `NormalizationClaim` | Prop 3.5 (`gap:prop:normalization`) | annular Riccati analysis, small divisors in `𝒜_s` |
| `TransferClaim` | Prop 3.9 (`gap:prop:transfer`) | Paper I Lemma 2.8, trace inertia in vN algebras |
| `InfiniteExponentClaim` | Prop 5.6 (`gap:prop:infinite-exponent`) | Weyl calculus, Helffer–Sjöstrand, K-theory |
| `BrjunoCoverClaim` | Thm 4.1 (`dim:thm:brjuno`) | singular Jacobi preparation, BJK2026 §§7–8 |
| `PacketCoverClaim` | Prop 4.12 (`dim:prop:packet-cover`) | semiclassical finite compressions |
| `AtomlessIDSClaim` | Thm 2.4 (`dim:thm:center`) + Paper I Lemma 2.8 | Jacobi reduction, atomless IDS |

From these hypotheses, everything else in §§1, 3 (assembly), 6 is **proved**:
* `thm_finite_exponent` (Thm 3.10) from normalization + transfer + comparison, including the
  bound `spec H_R ⊂ [-5,5]` and the monotonicity `‖R‖_B ≤ ‖R‖_S`;
* `thm_liouville` (**Theorem 1.2**) from the packet covers, Lemma 4.17 and the Hausdorff-cost
  computation (`SGD.dimH_eq_zero_of_packetCovers`);
* `thm_joint` (**Theorem 1.1**) by the threshold bookkeeping of §6, the Cauchy–Schwarz cover
  bound on the Brjuno branch, `𝓑 = ∞ ⇒ μ_irr = ∞` (Lemma 4.17) on the other branch, and the
  Cantor assertions.
-/
import SpectralGapsDimension.Liouville
import SpectralGapsDimension.IDSFacts
import AnalyticPerturbationsAMO.Neumann
import AnalyticPerturbationsAMO.DensityOfStates

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace SGD

open AMO

/-! ### The model -/

/-- The symmetry assumptions (1.3): `R = R*` and `𝓕(R) = R`. -/
def SelfDual (R : Symbol) : Prop := SymbolSelfAdjoint R ∧ fourier R = R

/-- `‖R‖_S ≤ ε` (with summability of the weighted series). -/
def NormLe (S : ℝ) (R : Symbol) (ε : ℝ) : Prop := WSum S S R ∧ wnorm S S R ≤ ε

/-- Every allowed internal label `{nα}`, `n ≠ 0`, is realized by an open gap of the critical
operator `H_α(R)`. -/
def AllLabelsOpen (α : ℝ) (R : Symbol) : Prop :=
  ∃ ν : Measure ℝ, IsDOSMeasure (H α 1 R) ν ∧ AllGapsOpen (Sigma α 1 R) ν α

/-- Every allowed internal label is realized by an open gap in the paper's sense (§1): the IDS
equals the label on the open gap (`GapOpenWeak`).  `AllLabelsOpen` additionally asks the label
at the right endpoint, which holds when the IDS is atomless
(`AllGapsOpenWeak.toAllGapsOpen`). -/
def AllLabelsOpenWeak (α : ℝ) (R : Symbol) : Prop :=
  ∃ ν : Measure ℝ, IsDOSMeasure (H α 1 R) ν ∧ AllGapsOpenWeak (Sigma α 1 R) ν α

/-- The symbol of `D = ∑_{m,n = ±1} W_{m,n}` (§3). -/
def Dsym : Symbol :=
  Pi.single (1, 1) 1 + Pi.single (1, -1) 1 + Pi.single (-1, 1) 1 + Pi.single (-1, -1) 1

/-! ### Elementary facts about the norms and the spectrum -/

lemma wt_mono {S S' : ℝ} (hS' : 0 ≤ S') (h : S' ≤ S) (p : ℤ × ℤ) :
    Real.exp (S' * |(p.1 : ℝ)| + S' * |(p.2 : ℝ)|) ≤ Real.exp (S * |(p.1 : ℝ)| + S * |(p.2 : ℝ)|) :=
  Real.exp_le_exp.2 (by gcongr)

/-- Smaller weights give smaller norms: `S' ≤ S ⇒ ‖R‖_{S'} ≤ ‖R‖_S`. -/
lemma wsmall_mono {S S' ρ ρ' : ℝ} {R : Symbol} (h : WSmall S S R ρ) (hS' : 0 ≤ S')
    (hSS : S' ≤ S) (hρ : ρ ≤ ρ') : WSmall S' S' R ρ' := by
  have hle : ∀ p : ℤ × ℤ, ‖R p‖ * Real.exp (S' * |(p.1 : ℝ)| + S' * |(p.2 : ℝ)|) ≤
      ‖R p‖ * Real.exp (S * |(p.1 : ℝ)| + S * |(p.2 : ℝ)|) := fun p =>
    mul_le_mul_of_nonneg_left (wt_mono hS' hSS p) (norm_nonneg _)
  have hs : Summable fun p : ℤ × ℤ => ‖R p‖ * Real.exp (S' * |(p.1 : ℝ)| + S' * |(p.2 : ℝ)|) :=
    h.1.of_nonneg_of_le (fun p => by positivity) hle
  exact ⟨hs, lt_of_le_of_lt (hs.tsum_le_tsum hle h.1) (h.2.trans_le hρ)⟩

lemma wsmall_normLe {S ρ : ℝ} {R : Symbol} (h : WSmall S S R ρ) : NormLe S R ρ :=
  ⟨h.1, h.2.le⟩

/-- `∑ |R_{r,s}| ≤ ‖R‖_S` for `S ≥ 0`. -/
lemma tsum_norm_le_wnorm {S : ℝ} (hS : 0 ≤ S) {R : Symbol} (h : WSum S S R) :
    ∑' p, ‖R p‖ ≤ wnorm S S R := by
  have hR : SymbolSummable R := h.symbolSummable hS hS
  refine hR.tsum_le_tsum (fun p => ?_) h
  exact le_mul_of_one_le_right (norm_nonneg _) (one_le_wt hS hS p)

lemma tsum_norm_amo_one : ∑' p, ‖amo (1 : ℝ) p‖ = 4 := by
  rw [tsum_eq_sum (s := {(1, 0), (-1, 0), (0, 1), (0, -1)})]
  · simp [amo, Pi.single_apply]
    norm_num
  · intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hp
    simp [amo, Pi.single_apply, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2]

/-- `‖H_{α,x}‖ ≤ 4 + ∑ |R_{r,s}|`. -/
lemma norm_H_le (α : ℝ) {R : Symbol} (hR : SymbolSummable R) (x : ℝ) :
    ‖H α 1 R x‖ ≤ 4 + ∑' p, ‖R p‖ := by
  refine (norm_op_le ((amo_summable _).add hR) x).trans ?_
  have h1 : Summable fun p => ‖amo ((1 : ℝ) : ℂ) p‖ := amo_summable _
  have h2 : Summable fun p => ‖R p‖ := hR
  rw [← tsum_norm_amo_one, ← Summable.tsum_add h1 h2]
  exact Summable.tsum_le_tsum (fun p => norm_add_le _ _) ((amo_summable _).add hR) (h1.add h2)

lemma abs_le_norm_of_mem_spectrum {T : Op ℤ} {E : ℝ} (hE : E ∈ spectrum ℝ T) : |E| ≤ ‖T‖ := by
  rw [← spectrum.preimage_algebraMap ℂ] at hE
  have := spectrum.norm_le_norm_of_mem hE
  simpa using this

lemma isCompact_spectrum_real (T : Op ℤ) : IsCompact (spectrum ℝ T) := by
  refine Metric.isCompact_of_isClosed_isBounded (spectrum_real_isClosed T) ?_
  refine (Metric.isBounded_closedBall (x := (0 : ℝ)) (r := ‖T‖)).subset fun E hE => ?_
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  exact abs_le_norm_of_mem_spectrum hE

lemma Sigma_nonempty (α : ℝ) {R : Symbol} (hR : SymbolSummable R)
    (hsa : SymbolSelfAdjoint R) : (Sigma α 1 R).Nonempty :=
  spectrum_real_nonempty (isSelfAdjoint_H α 1 hR hsa 0)

lemma Sigma_subset_Icc {α : ℝ} {R : Symbol} (hR : SymbolSummable R) {c : ℝ}
    (hc : ∑' p, ‖R p‖ ≤ c) : Sigma α 1 R ⊆ Icc (-(4 + c)) (4 + c) := fun E hE => by
  have h1 := abs_le_norm_of_mem_spectrum hE
  have h2 := norm_H_le α hR 0
  exact abs_le.1 (by linarith)

/-- The Cantor assertions: a nonempty compact perfect Lebesgue-null set is a Cantor set. -/
lemma isCantor_Sigma {α : ℝ} {R : Symbol} (hR : SymbolSummable R) (hsa : SymbolSelfAdjoint R)
    (hperf : Perfect (Sigma α 1 R)) (hvol : volume (Sigma α 1 R) = 0) :
    IsCantor (Sigma α 1 R) :=
  ⟨Sigma_nonempty α hR hsa, isCompact_spectrum_real _, hperf,
    Hausdorff.interior_eq_empty_of_volume_eq_zero hvol⟩

/-! ### Paper inputs (stated, not proved here) -/

/-- **Theorem 3.6 (`gap:thm:comparison`).**  For every irrational `α` and every real
`|b| < 1/2`, the isotropic self-dual extended Harper operator `H_b = H_0 + bD` has an open
gap of each label in `Λ_α`. -/
def ComparisonClaim : Prop :=
  ∀ {α : ℝ} (hα : Irrational α) {b : ℝ} (hb : |b| < 1 / 2),
    AllLabelsOpen α ((b : ℂ) • Dsym)

/-- The normalization identity (3.18) at energy `E`, in the rotation algebra `𝒜_s`:
`G^* (H_R - E) G = H_b - g` with `G` invertible and Fourier fixed. -/
def NormalForm (α s : ℝ) (R G Ginv : Symbol) (E b g : ℝ) : Prop :=
  WSum s s G ∧ WSum s s Ginv ∧ fourier G = G ∧
    tmul α G Ginv = one ∧ tmul α Ginv G = one ∧
    tmul α (sstar G) (tmul α (amo (1 : ℝ) + R - (E : ℂ) • one) G) =
      amo (1 : ℝ) + (b : ℂ) • Dsym - (g : ℂ) • one

/-- **Proposition 3.5 (`gap:prop:normalization`).**  If `β(α) < ∞`, there are widths
`0 < s < B` and, for sufficiently small `R ∈ 𝒜_B^{sa,𝓕}`, continuous real `b, g` on `[-5,5]`
and invertible Fourier-fixed `G(E) ∈ 𝒜_s` with `G(E)^*(H_R - E)G(E) = H_{b(E)} - g(E)`,
`|b(E)| < 1/2`, and `sup_{|E| ≤ 5} (‖G - I‖_s + ‖G^{-1} - I‖_s + |b| + |g - E|) ≤ C_α ‖R‖_B`.
The radius and constants are independent of the gap label. -/
def NormalizationClaim : Prop :=
  ∀ {α : ℝ} (hα : Irrational α) (hβ : beta α < ⊤),
    ∃ B s Cα ε : ℝ, 0 < s ∧ s < B ∧ 0 < ε ∧ ∀ R : Symbol, SelfDual R → WSmall B B R ε →
      ∃ b g : ℝ → ℝ, ContinuousOn b (Icc (-5) 5) ∧ ContinuousOn g (Icc (-5) 5) ∧
        ∃ G Ginv : ℝ → Symbol, ∀ E ∈ Icc (-5 : ℝ) 5,
          NormalForm α s R (G E) (Ginv E) E (b E) (g E) ∧ |b E| < 1 / 2 ∧
          wnorm s s (G E - one) + wnorm s s (Ginv E - one) + |b E| + |g E - E| ≤
            Cα * wnorm B B R

/-- **Proposition 3.9 (`gap:prop:transfer`).**  Suppose the normalization identity holds on
`spec H_R` with continuous real `b, g`, `|b| < 1/2`, and invertible factors `G(E)` in the
rotation algebra.  Then every label in `Λ_α` is open for `H_R`.  (The proof combines the
comparison theorem — taken here as the hypothesis `hcomp` — with trace inertia and the
covariant-IDS lemma of Paper I.) -/
def TransferClaim : Prop :=
  ∀ {α : ℝ} (hα : Irrational α)
    (hcomp : ∀ b : ℝ, |b| < 1 / 2 → AllLabelsOpen α ((b : ℂ) • Dsym))
    {R : Symbol} (hR : SelfDual R) (hRs : SymbolSummable R) {s : ℝ} (hs : 0 < s)
    (b g : ℝ → ℝ) (hb : ContinuousOn b (Sigma α 1 R)) (hg : ContinuousOn g (Sigma α 1 R))
    (G Ginv : ℝ → Symbol)
    (hG : ∀ E ∈ Sigma α 1 R, NormalForm α s R (G E) (Ginv E) E (b E) (g E) ∧ |b E| < 1 / 2),
    AllLabelsOpen α R

/-- **Proposition 5.6 (`gap:prop:infinite-exponent`).**  There are fixed `S₀, ε₀ > 0` such
that, at every irrational `α` with `β(α) = ∞`, every Hermitian Fourier-self-dual `R` with
`‖R‖_{S₀} ≤ ε₀` realizes every label in `Λ_α` as an open gap (in the paper's sense,
`AllLabelsOpenWeak`: the IDS equals the label on the open gap; the proposition does not assert
atomlessness of the IDS at the gap edges). -/
def InfiniteExponentClaim : Prop :=
    ∃ S₀ ε₀ : ℝ, 0 < S₀ ∧ 0 < ε₀ ∧ ∀ α : ℝ, Irrational α → beta α = ⊤ →
      ∀ R : Symbol, SelfDual R → NormLe S₀ R ε₀ → AllLabelsOpenWeak α R

/-- **Theorem 4.1 (`dim:thm:brjuno`), cover form.**  For Brjuno `α` there is a width
threshold `S_Br`; for `S ≥ S_Br` there are `ε_* > 0` and `C` such that for every admissible
`R` with `‖R‖_S < ε_*` and every sufficiently large `n`, `Σ_α(R)` is covered by at most
`q_n + q_{n-1}` closed intervals of total length `≤ C / q_n`. -/
def BrjunoCoverClaim : Prop :=
  ∀ {α : ℝ} (hα : Irrational α) (hB : Brjuno α),
    ∃ SBr : ℝ, ∀ S ≥ SBr, ∃ ε C : ℝ, 0 < ε ∧ ∀ R : Symbol, SelfDual R → WSmall S S R ε →
      ∀ᶠ n in atTop, ∃ (m : ℕ) (a b : Fin m → ℝ), (∀ i, a i ≤ b i) ∧
        Sigma α 1 R ⊆ ⋃ i, Icc (a i) (b i) ∧
        (m : ℝ) ≤ cfDen α n + cfDen α (n - 1) ∧ ∑ i, (b i - a i) ≤ C / cfDen α n

/-- **Proposition 4.12 (`dim:prop:packet-cover`).**  Fix irrational `α` and `S > 0`.  For
sufficiently small admissible `R` there are a neighbourhood `|α - p/q| < δ₀` of `α` and `q₀`
such that, for each order `N ≥ 2`, there are constants `C, A, L` with: for every reduced
`p/q` in the neighbourhood with `q ≥ q₀`, every `0 < η ≤ 1` and `h = 2π q² |α - p/q|`
with `0 < h ≤ C^{-1} q^{-L} η^L`, `Σ_α(R)` has a `PacketCover`. -/
def PacketCoverClaim : Prop :=
  ∀ {α : ℝ} (hα : Irrational α) {S : ℝ} (hS : 0 < S),
    ∃ ε > 0, ∀ R : Symbol, SelfDual R → WSmall S S R ε →
      ∃ δ₀ > 0, ∃ q₀ : ℕ, ∀ N : ℕ, 2 ≤ N → ∃ C A L : ℝ, 0 < C ∧ 0 ≤ A ∧ 0 ≤ L ∧
        ∀ r : ℚ, |α - r| < δ₀ → q₀ ≤ r.den → ∀ η : ℝ, 0 < η → η ≤ 1 →
          0 < 2 * Real.pi * (r.den : ℝ) ^ 2 * |α - r| →
          2 * Real.pi * (r.den : ℝ) ^ 2 * |α - r| ≤ C⁻¹ * (r.den : ℝ) ^ (-L) * η ^ L →
          PacketCover (Sigma α 1 R) r.den η (2 * Real.pi * (r.den : ℝ) ^ 2 * |α - r|) C A N

/-- **Atomless IDS** (Paper I Lemma 2.8, applied within the radius of Theorem 2.4
`dim:thm:center`, where `dim ker(H_{α,x} - E) ≤ 2`; this is the input of the paper's Cantor
assertions, §6): for irrational `α` and `S > 0`, small admissible perturbations have an atomless
density of states. -/
def AtomlessIDSClaim : Prop :=
  ∀ {α : ℝ} (hα : Irrational α) {S : ℝ} (hS : 0 < S),
    ∃ ε > 0, ∀ R : Symbol, SelfDual R → WSmall S S R ε →
      ∃ ν : Measure ℝ, IsDOSMeasure (H α 1 R) ν ∧ ∀ E, ν {E} = 0

/-- Perfectness of the spectrum (proof of the Cantor assertions, §6), derived from
`AtomlessIDSClaim`: an isolated point of `Σ` would be an atom, by full support of the DOS. -/
theorem sigmaPerfect_of_atomless (h : AtomlessIDSClaim) {α : ℝ} (hα : Irrational α) {S : ℝ}
    (hS : 0 < S) : ∃ ε > 0, ∀ R : Symbol, SelfDual R → WSmall S S R ε → Perfect (Sigma α 1 R) := by
  obtain ⟨ε, hε, hR⟩ := h hα hS
  refine ⟨ε, hε, fun R hRsd hRS => ?_⟩
  obtain ⟨ν, hν, hat⟩ := hR R hRsd hRS
  exact perfect_of_atomless hα (WSmall.summable hS.le hS.le hRS) hRsd.1 hν hat

/-- The seven inputs of Paper II whose proofs need theory absent from Mathlib, bundled.  They are
stated above as in the paper (some slightly weaker: extra hypotheses or constants chosen later,
never stronger) and are **hypotheses** of the main theorems below (not axioms): Theorems 1.1,
1.2 and 3.10 are proved as implications from them. -/
structure PaperIIInputs : Prop where
  comparison : ComparisonClaim
  normalization : NormalizationClaim
  transfer : TransferClaim
  infiniteExponent : InfiniteExponentClaim
  brjunoCover : BrjunoCoverClaim
  packetCover : PacketCoverClaim
  atomlessIDS : AtomlessIDSClaim

/-! ### Theorem 3.10: gap opening at finite exponential exponent -/

/-- **Theorem 3.10 (`gap:thm:finite-exponent`).**  For irrational `α` with `β(α) < ∞` there
is `S_gap(α) > 0` and, for each `S ≥ S_gap(α)`, a radius `ρ_gap(α,S) > 0` such that every
admissible `R` with `‖R‖_S < ρ_gap` has every label in `Λ_α` open.  Proved from
Propositions 3.5, 3.9 and Theorem 3.6. -/
theorem thm_finite_exponent (P : PaperIIInputs) {α : ℝ} (hα : Irrational α) (hβ : beta α < ⊤) :
    ∃ Sgap > 0, ∀ S ≥ Sgap, ∃ ρ > 0, ∀ R : Symbol, SelfDual R → WSmall S S R ρ →
      AllLabelsOpen α R := by
  obtain ⟨B, s, Cα, ε, hs, hsB, hε, hnorm⟩ := P.normalization hα hβ
  have hB : 0 < B := hs.trans hsB
  refine ⟨B, hB, fun S hS => ⟨min 1 ε, lt_min one_pos hε, fun R hR hRS => ?_⟩⟩
  have hRB : WSmall B B R (min 1 ε) := wsmall_mono hRS hB.le hS le_rfl
  have hRsum : SymbolSummable R := WSmall.summable hB.le hB.le hRB
  obtain ⟨b, g, hb, hg, G, Ginv, hG⟩ := hnorm R hR (wsmall_mono hRB hB.le le_rfl (min_le_right _ _))
  -- `spec H_R ⊂ [-5, 5]`
  have hsub : Sigma α 1 R ⊆ Icc (-5) 5 := by
    have h1 : ∑' p, ‖R p‖ ≤ 1 :=
      (tsum_norm_le_wnorm hB.le hRB.1).trans (hRB.2.le.trans (min_le_left _ _))
    refine (Sigma_subset_Icc hRsum h1).trans ?_
    norm_num
  exact P.transfer hα (fun b' hb' => P.comparison hα hb') hR hRsum hs b g
    (hb.mono hsub) (hg.mono hsub) G Ginv (fun E hE => ⟨(hG E (hsub hE)).1, (hG E (hsub hE)).2.1⟩)

/-! ### Theorem 1.2 -/

/-- **Theorem 1.2 (`thm:liouville`).**  Let `α` be irrational with `μ_irr(α) = ∞` and `S > 0`.
There is `ρ_L(α,S) > 0` such that every admissible `R` with `‖R‖_S < ρ_L` has
`dim_H Σ_α(R) = 0`; the spectrum is a zero-measure Cantor set.  No assumption on `β(α)`. -/
theorem thm_liouville (P : PaperIIInputs) {α : ℝ} (hα : Irrational α) (hL : Liouville α) {S : ℝ} (hS : 0 < S) :
    ∃ ρ > 0, ∀ R : Symbol, SelfDual R → WSmall S S R ρ →
      dimH (Sigma α 1 R) = 0 ∧ IsCantor (Sigma α 1 R) ∧ volume (Sigma α 1 R) = 0 := by
  obtain ⟨ε₁, hε₁, hpack⟩ := P.packetCover hα hS
  obtain ⟨ε₂, hε₂, hperf⟩ := sigmaPerfect_of_atomless P.atomlessIDS hα hS
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun R hR hRS => ?_⟩
  have hR1 := wsmall_mono hRS hS.le le_rfl (min_le_left _ _)
  have hR2 := wsmall_mono hRS hS.le le_rfl (min_le_right _ _)
  obtain ⟨δ₀, hδ₀, q₀, hcov⟩ := hpack R hR hR1
  have hdim : dimH (Sigma α 1 R) = 0 := by
    refine dimH_eq_zero_of_packetCovers
      (fun q h => ∃ r : ℚ, q = r.den ∧ h = 2 * Real.pi * (r.den : ℝ) ^ 2 * |α - r| ∧
        |α - r| < δ₀ ∧ q₀ ≤ r.den) ?_ ?_
    · intro N hN
      obtain ⟨C, A, L, hC, hA, hL', hc⟩ := hcov N hN
      refine ⟨C, A, L, hC, hA, hL', ?_⟩
      rintro q h η ⟨r, rfl, rfl, hr, hq₀⟩ hη0 hη1 hh0 hthr
      exact hc r hr hq₀ η hη0 hη1 hh0 hthr
    · intro M hM Q₀
      obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, q₀ ≤ N₀ ∧ Q₀ ≤ N₀ ∧ δ₀⁻¹ < N₀ ∧ 1 ≤ N₀ := by
        obtain ⟨k, hk⟩ := exists_nat_gt (max Q₀ δ₀⁻¹)
        refine ⟨q₀ + k + 1, by omega, ?_, ?_, by omega⟩ <;> push_cast <;>
          linarith [le_max_left Q₀ δ₀⁻¹, le_max_right Q₀ δ₀⁻¹, (Nat.cast_nonneg q₀ : (0 : ℝ) ≤ q₀)]
      obtain ⟨r, hrden, hr0, hrh⟩ := exists_rat_liouville hα hL hM N₀
      have hden1 : (1 : ℝ) ≤ r.den := by exact_mod_cast r.den_pos
      have hdenN : (N₀ : ℝ) ≤ r.den := by exact_mod_cast hrden
      refine ⟨r.den, 2 * Real.pi * (r.den : ℝ) ^ 2 * |α - r|,
        ⟨r, rfl, rfl, ?_, hN₀.1.trans hrden⟩, hN₀.2.1.trans hdenN, hden1,
        by positivity, hrh⟩
      -- `|α - r| ≤ 1 / q < δ₀`
      have h1 : (r.den : ℝ) ^ (-M) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hden1 (by linarith)
      have h2 : (r.den : ℝ) ≤ 2 * Real.pi * (r.den : ℝ) ^ 2 := by nlinarith [Real.pi_gt_three]
      have h3 : (r.den : ℝ) * |α - r| ≤ 1 := by
        calc (r.den : ℝ) * |α - r| ≤ 2 * Real.pi * (r.den : ℝ) ^ 2 * |α - r| := by gcongr
          _ ≤ 1 := hrh.trans h1
      have h4 : δ₀⁻¹ < r.den := hN₀.2.2.1.trans_le hdenN
      have h5 : 1 < δ₀ * r.den := by
        have := mul_lt_mul_of_pos_left h4 hδ₀
        rwa [mul_inv_cancel₀ hδ₀.ne'] at this
      nlinarith [abs_nonneg (α - r)]
  have hvol : volume (Sigma α 1 R) = 0 :=
    Hausdorff.volume_eq_zero_of_dimH_lt_one (by rw [hdim]; exact zero_lt_one)
  have hRsum : SymbolSummable R := WSmall.summable hS.le hS.le hRS
  exact ⟨hdim, isCantor_Sigma hRsum hR.1 (hperf R hR hR2) hvol, hvol⟩

/-! ### Theorem 1.1 -/

lemma cfDen_le_two_mul {α : ℝ} (n : ℕ) (hn : 1 ≤ n) :
    cfDen α n + cfDen α (n - 1) ≤ 2 * cfDen α n := by
  have : cfDen α (n - 1) ≤ cfDen α n := by
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    exact GenContFract.of_den_mono
  linarith

/-- The `𝓗^{1/2}` assertion on the Brjuno branch: Brjuno covers give `𝓗^{1/2}(Σ) < ∞`. -/
lemma hausdorff_half_lt_top_of_brjuno {α : ℝ} (hα : Irrational α) {K : Set ℝ} {C : ℝ}
    (h : ∀ᶠ n in atTop, ∃ (m : ℕ) (a b : Fin m → ℝ), (∀ i, a i ≤ b i) ∧
        K ⊆ ⋃ i, Icc (a i) (b i) ∧
        (m : ℝ) ≤ cfDen α n + cfDen α (n - 1) ∧ ∑ i, (b i - a i) ≤ C / cfDen α n) :
    μH[1 / 2] K < ⊤ := by
  have hq := cfGrowth hα
  obtain ⟨N, hN⟩ := eventually_atTop.1 h
  have h' : ∀ n, ∃ (m : ℕ) (a b : Fin m → ℝ), N ≤ n → (∀ i, a i ≤ b i) ∧
      K ⊆ ⋃ i, Icc (a i) (b i) ∧
      (m : ℝ) ≤ cfDen α n + cfDen α (n - 1) ∧ ∑ i, (b i - a i) ≤ C / cfDen α n := by
    intro n
    by_cases hn : N ≤ n
    · obtain ⟨m, a, b, hab⟩ := hN n hn
      exact ⟨m, a, b, fun _ => hab⟩
    · exact ⟨0, finZeroElim, finZeroElim, fun h => absurd h hn⟩
  choose m a b hP using h'
  have hle := Hausdorff.hausdorffMeasure_half_le_of_covers (K := K) (C := max C 0)
    (le_max_right _ _) (cfDen α) hq.tendsto_atTop m a b
    (eventually_atTop.2 ⟨N, fun n hn => (hP n hn).1⟩)
    (eventually_atTop.2 ⟨N, fun n hn => (hP n hn).2.1⟩)
    (eventually_atTop.2 ⟨max N 1, fun n hn =>
      ((hP n (le_of_max_le_left hn)).2.2.1).trans (cfDen_le_two_mul n (le_of_max_le_right hn))⟩)
    (eventually_atTop.2 ⟨N, fun n hn => ((hP n hn).2.2.2).trans
      (div_le_div_of_nonneg_right (le_max_left _ _) (hq.pos n).le)⟩)
  exact hle.trans_lt ENNReal.ofReal_lt_top

/-- **Theorem 1.1 (`thm:joint`).**  For every irrational `α` there is a width threshold
`S_*(α) > 0` and, for each `S ≥ S_*(α)`, a radius `ρ_*(α,S) > 0` such that every perturbation
with `R = R*`, `𝓕(R) = R` and `‖R‖_S < ρ_*` has every label in `Λ_α` open and
`𝓗^{1/2}(Σ_α(R)) < ∞`.  In particular `dim_H Σ_α(R) ≤ 1/2`, and the spectrum is a Cantor set
of zero Lebesgue measure. -/
theorem thm_joint (P : PaperIIInputs) {α : ℝ} (hα : Irrational α) :
    ∃ Sstar > 0, ∀ S ≥ Sstar, ∃ ρ > 0, ∀ R : Symbol, SelfDual R → WSmall S S R ρ →
      AllLabelsOpen α R ∧ μH[1 / 2] (Sigma α 1 R) < ⊤ ∧ dimH (Sigma α 1 R) ≤ 1 / 2 ∧
        IsCantor (Sigma α 1 R) ∧ volume (Sigma α 1 R) = 0 := by
  -- the gap thresholds
  obtain ⟨Sgap, hSgap, ρgap, hρgap, hgap⟩ : ∃ Sgap > 0, ∃ ρgap : ℝ → ℝ,
      (∀ S ≥ Sgap, 0 < ρgap S) ∧
      ∀ S ≥ Sgap, ∀ R : Symbol, SelfDual R → WSmall S S R (ρgap S) → AllLabelsOpenWeak α R := by
    by_cases hβ : beta α < ⊤
    · obtain ⟨Sgap, hSgap, h⟩ := thm_finite_exponent P hα hβ
      choose! ρ hρ hρR using h
      refine ⟨Sgap, hSgap, ρ, hρ, fun S hS R hR hRS => ?_⟩
      obtain ⟨ν, hν, hg⟩ := hρR S hS R hR hRS
      exact ⟨ν, hν, AllGapsOpen.weak hg⟩
    · obtain ⟨S₀, ε₀, hS₀, hε₀, h⟩ := P.infiniteExponent
      refine ⟨S₀, hS₀, fun _ => ε₀ / 2, fun _ _ => by positivity, fun S hS R hR hRS => ?_⟩
      exact h α hα (not_lt_top_iff.1 hβ) R hR
        (wsmall_normLe (wsmall_mono hRS hS₀.le hS (half_le_self hε₀.le)))
  -- the dimension thresholds
  obtain ⟨Sdim, hSdim, ρdim, hρdim, hdim⟩ : ∃ Sdim > 0, ∃ ρdim : ℝ → ℝ,
      (∀ S ≥ Sdim, 0 < ρdim S) ∧
      ∀ S ≥ Sdim, ∀ R : Symbol, SelfDual R → WSmall S S R (ρdim S) →
        μH[1 / 2] (Sigma α 1 R) < ⊤ := by
    by_cases hB : Brjuno α
    · obtain ⟨SBr, h⟩ := P.brjunoCover hα hB
      refine ⟨max SBr 1, by positivity, ?_⟩
      choose! ε C hε hcov using fun S (hS : S ≥ max SBr 1) => h S (le_of_max_le_left hS)
      exact ⟨ε, hε, fun S hS R hR hRS =>
        hausdorff_half_lt_top_of_brjuno hα (hcov S hS R hR hRS)⟩
    · have hL : Liouville α :=
        mu_eq_top_of_brjuno_eq_top (cfGrowth hα) (not_lt_top_iff.1 hB)
      refine ⟨1, one_pos, ?_⟩
      choose! ρ hρ hρR using fun S (hS : S ≥ 1) => thm_liouville P hα hL (one_pos.trans_le hS)
      refine ⟨ρ, hρ, fun S hS R hR hRS => ?_⟩
      have h0 : dimH (Sigma α 1 R) = 0 := (hρR S hS R hR hRS).1
      have : μH[((1 / 2 : ℝ≥0) : ℝ)] (Sigma α 1 R) = 0 :=
        hausdorffMeasure_of_dimH_lt (by rw [h0]; norm_num)
      simp only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] at this
      rw [this]; exact ENNReal.zero_lt_top
  -- the Cantor threshold
  refine ⟨max Sgap Sdim, lt_max_of_lt_left hSgap, fun S hS => ?_⟩
  have hS0 : 0 < S := hSgap.trans_le (le_of_max_le_left hS)
  obtain ⟨εc, hεc, hatom⟩ := P.atomlessIDS hα hS0
  have hSg : S ≥ Sgap := le_of_max_le_left hS
  have hSd : S ≥ Sdim := le_of_max_le_right hS
  refine ⟨min (ρgap S) (min (ρdim S) εc),
    lt_min (hρgap S hSg) (lt_min (hρdim S hSd) hεc), fun R hR hRS => ?_⟩
  have hR1 := wsmall_mono hRS hS0.le le_rfl (min_le_left _ _)
  have hR2 := wsmall_mono hRS hS0.le le_rfl ((min_le_right _ _).trans (min_le_left _ _))
  have hR3 := wsmall_mono hRS hS0.le le_rfl ((min_le_right _ _).trans (min_le_right _ _))
  have hH := hdim S hSd R hR hR2
  have hdimH : dimH (Sigma α 1 R) ≤ 1 / 2 := Hausdorff.dimH_le_half hH
  have hvol : volume (Sigma α 1 R) = 0 :=
    Hausdorff.volume_eq_zero_of_dimH_lt_one (hdimH.trans_lt (by norm_num))
  have hRsum : SymbolSummable R := WSmall.summable hS0.le hS0.le hRS
  -- the atomless IDS gives perfectness and the label at the right gap edges
  obtain ⟨ν', hν', hat⟩ := hatom R hR hR3
  obtain ⟨ν, hν, hweak⟩ := hgap S hSg R hR hR1
  obtain rfl := IsDOSMeasure.unique hν' hν
  haveI := hν.1
  obtain ⟨E', hE'⟩ := Sigma_nonempty α hRsum hR.1
  have hSc : ν' (Sigma α 1 R)ᶜ = 0 := (dos_support hα hRsum hR.1 hν hE' one_pos).2
  exact ⟨⟨ν', hν, AllGapsOpenWeak.toAllGapsOpen hweak hSc hat⟩, hH, hdimH,
    isCantor_Sigma hRsum hR.1 (perfect_of_atomless hα hRsum hR.1 hν hat) hvol, hvol⟩

end SGD
