/-
Copyright (c) 2026. Formalization of
  S. Becker, "Self-dual perturbations of the critical almost Mathieu operator:
  Dry Ten Martini and Hausdorff dimension" (Paper II).

# Theorem 2.4 (`dim:thm:center`), preparation form: the large-width case

Paper I's first preparation theorem (`AMO.exists_jacobiPrep`, `FirstPreparation.lean`) produces,
for weights `ω = (s, ℓ)`, an exact analytic Jacobi preparation `H_{α,x} - E = Q_x^* J_x Q_x` as soon
as `e^{-s}(2|η| e^ℓ + |E|) + e^{-2s} ≤ 1/4` and `e^{-s} ‖R‖_{s,ℓ} ≤ σ₁`.

For the critical coupling `η = 1`, spectral energies satisfy `|E| ≤ 5` once `‖R‖_S ≤ 1`
(`SGD.Sigma_subset_Icc`).  With `ω = (S, log (6/5))` the first condition reads
`e^{-S}(12/5 + 5) + e^{-2S} ≤ 1/4`, which holds for `S ≥ 7/2` because `e^{7/2} ≥ 30`; the second
follows from `‖R‖_{S, log(6/5)} ≤ ‖R‖_S < σ₁` (for `S ≥ log (6/5)`).  Hence `JacobiPrepClaim` holds
for every width `S ≥ 7/2` (`jacobiPrep_large_width`), and the general claim reduces to small widths
`0 < S < 7/2` (`jacobiPrep_of_smallWidth`).
-/
import SpectralGapsDimension.PaperIIIInputs
import AnalyticPerturbationsAMO.FirstPreparation
import AnalyticPerturbationsAMO.SharpWidth

noncomputable section

namespace SGD

open AMO

/-- The width threshold `S₀ = 7/2` above which Paper I's first preparation applies directly. -/
def largeWidthThreshold : ℝ := 7 / 2

lemma sig1_pos : 0 < sig1 := by
  unfold sig1
  refine lt_min (ScaledPrep.sig0_pos (by norm_num)) ?_
  have := Cst_quarter_pos
  positivity

/-- `e^{7/2} ≥ 30`, from `e > 2.7182818283` and `e^{1/2} ≥ 3/2`. -/
lemma thirty_le_exp_seven_halves : (30 : ℝ) ≤ Real.exp (7 / 2) := by
  have he := Real.exp_one_gt_d9
  have hh : (1 / 2 : ℝ) + 1 ≤ Real.exp (1 / 2) := Real.add_one_le_exp _
  have hsplit : Real.exp (7 / 2) = Real.exp 1 * Real.exp 1 * Real.exp 1 * Real.exp (1 / 2) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; norm_num
  rw [hsplit]
  have h1 : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 1 * Real.exp 1 * Real.exp 1 := by
    have h0 : (0 : ℝ) ≤ 2.7182818283 := by norm_num
    calc (2.7182818283 : ℝ) ^ 3 = 2.7182818283 * 2.7182818283 * 2.7182818283 := by ring
      _ ≤ Real.exp 1 * Real.exp 1 * Real.exp 1 := by gcongr
  have h2 : (0 : ℝ) ≤ Real.exp 1 * Real.exp 1 * Real.exp 1 := by positivity
  nlinarith

/-- `e^{-S} ≤ 1/30` for `S ≥ 7/2`. -/
lemma exp_neg_le_of_large {S : ℝ} (hS : 7 / 2 ≤ S) : Real.exp (-S) ≤ 1 / 30 := by
  have h1 : Real.exp (-S) ≤ Real.exp (-(7 / 2)) := Real.exp_le_exp.2 (by linarith)
  have h2 : Real.exp (-(7 / 2 : ℝ)) = (Real.exp (7 / 2))⁻¹ := Real.exp_neg _
  have h3 := thirty_le_exp_seven_halves
  rw [h2] at h1
  refine h1.trans ?_
  rw [one_div]
  exact inv_anti₀ (by norm_num) h3

lemma log_six_fifths_pos : 0 < Real.log (6 / 5 : ℝ) := Real.log_pos (by norm_num)

lemma log_six_fifths_le : Real.log (6 / 5 : ℝ) ≤ 1 / 5 := by
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 6 / 5 by norm_num)
  linarith

/-- **Theorem 2.4 (`dim:thm:center`), preparation form, large widths.**  For irrational `α` and
`S ≥ 7/2`, every admissible `R` with `‖R‖_S < min 1 σ₁` admits, at every spectral energy `E`, an
exact analytic Jacobi preparation of `H_α(R) - E` (Paper I, first preparation theorem
`AMO.exists_jacobiPrep`, with weights `(S, log (6/5))` and coupling `η = 1`).  Irrationality is not
used. -/
theorem jacobiPrep_large_width : ∀ {α : ℝ}, Irrational α → ∀ {S : ℝ}, 7 / 2 ≤ S →
    ∃ ε > 0, ∀ R : AMO.Symbol, SelfDual R → AMO.WSmall S S R ε →
      ∀ E ∈ AMO.Sigma α 1 R, Nonempty (AMO.JacobiPrep α (AMO.H α 1 R) E) := by
  intro α _ S hS
  have hS0 : 0 < S := by linarith
  refine ⟨min 1 sig1, lt_min one_pos sig1_pos, fun R hRsd hRS E hE => ?_⟩
  set ℓ : ℝ := Real.log (6 / 5) with hℓdef
  have hℓ0 : 0 < ℓ := log_six_fifths_pos
  have hℓS : ℓ ≤ S := by linarith [log_six_fifths_le]
  let ω : Weights := ⟨S, ℓ, hS0.le, hℓ0.le⟩
  have hWS : WSum S S R := hRS.1
  obtain ⟨hWℓ, hwle⟩ := wnorm_mono (le_refl S) hℓS hWS
  have hRsum : SymbolSummable R := WSmall.summable hS0.le hS0.le hRS
  -- `|E| ≤ 5`
  have hE5 : |E| ≤ 5 := by
    have h1 : ∑' p, ‖R p‖ ≤ 1 :=
      (tsum_norm_le_wnorm hS0.le hWS).trans (hRS.2.le.trans (min_le_left _ _))
    have := Sigma_subset_Icc hRsum h1 hE
    rw [Set.mem_Icc] at this
    exact abs_le.2 ⟨by linarith [this.1], by linarith [this.2]⟩
  have hx := exp_neg_le_of_large hS
  have hx0 : 0 < Real.exp (-S) := Real.exp_pos _
  have heℓ : Real.exp ℓ = 6 / 5 := Real.exp_log (by norm_num)
  have hc : Real.exp (-ω.s) * (2 * |(1 : ℝ)| * Real.exp ω.ℓ + |E|) +
      Real.exp (-ω.s) * Real.exp (-ω.s) ≤ 1 / 4 := by
    show Real.exp (-S) * (2 * |(1 : ℝ)| * Real.exp ℓ + |E|) +
      Real.exp (-S) * Real.exp (-S) ≤ 1 / 4
    rw [heℓ, abs_one]
    have hE0 : 0 ≤ |E| := abs_nonneg _
    nlinarith
  have hσ : Real.exp (-ω.s) * wnorm ω.s ω.ℓ R ≤ sig1 := by
    show Real.exp (-S) * wnorm S ℓ R ≤ sig1
    have hw0 : 0 ≤ wnorm S ℓ R := tsum_nonneg fun p => by positivity
    have hx1 : Real.exp (-S) ≤ 1 := by linarith
    calc Real.exp (-S) * wnorm S ℓ R ≤ 1 * wnorm S ℓ R := by gcongr
      _ = wnorm S ℓ R := one_mul _
      _ ≤ wnorm S S R := hwle
      _ ≤ sig1 := hRS.2.le.trans (min_le_right _ _)
  exact exists_jacobiPrep ω hS0 hℓ0 α 1 E hWℓ hRsd.1 hc hσ

/-- **Theorem 2.4 (`dim:thm:center`), preparation form, small widths** (stated, not asserted):
`JacobiPrepClaim` restricted to widths `0 < S < 7/2`.  Larger widths are covered by
`jacobiPrep_large_width`. -/
def JacobiPrepSmallWidthClaim : Prop :=
  ∀ {α : ℝ} (_hα : Irrational α) {S : ℝ} (_hS : 0 < S) (_hS' : S < 7 / 2),
    ∃ ε > 0, ∀ R : Symbol, SelfDual R → WSmall S S R ε →
      ∀ E ∈ Sigma α 1 R, Nonempty (JacobiPrep α (H α 1 R) E)

/-- `JacobiPrepClaim` (Theorem 2.4) reduces to its small-width case. -/
theorem jacobiPrep_of_smallWidth (h : JacobiPrepSmallWidthClaim) : JacobiPrepClaim := by
  intro α hα S hS
  rcases lt_or_ge S (7 / 2) with hlt | hge
  · exact h hα hS hlt
  · exact jacobiPrep_large_width hα hge

end SGD
