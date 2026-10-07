/-
Copyright (c) 2026. Formalization of
  S. Becker, S. Jitomirskaya, I. Krasovsky, "Critical almost Mathieu operator: hidden
  singularity, gap continuity, and the Hausdorff dimension of the spectrum"
  (arXiv:1909.04429v2).

# Main theorems

* `thm_cover` — **Theorem 7.11** (`thm-cover`, tex l. 1775): for irrational `α` and `n ≥ 4`
  there are `m ≤ q_n + q_{n-1}` closed intervals, independent of `θ`, of total length
  `≤ C/q_n` (`C` absolute) covering `σ(H_{α,θ})` for every `θ`, and also the spectrum
  `σ(M_α)` of the direct integral.
* `dimH_spectrum_le_half` — **Theorem 1.1** (`Hdimthm`): `dim_H σ(H_{α,θ}) ≤ 1/2` for all
  irrational `α` and real `θ` (and even `𝓗^{1/2}(σ(H_{α,θ})) < ∞`).
* `volume_spectrum_eq_zero` — **Theorem 1.2** (`zero`): `|σ(H_{α,θ})| = 0`.  The paper gives
  two other proofs (Kotani theory, §4; Theorem 1.3 + Last's bound, §6); here it follows
  from Theorem 1.1, since `dim_H < 1` forces Lebesgue measure zero.
* the same statements for `σ(M_α)` (`sigmaAMO`), and for the chiral operator `Ĥ`.

Theorem 1.3 (`measure`) is `CAH.measure_convergence` in `MeasureConvergence.lean`.

All results here are proved without `sorry` and without additional hypotheses.
-/
import CriticalAMOHausdorff.BlockCover
import CriticalAMOHausdorff.ChiralSpectrum

noncomputable section

open Real Set MeasureTheory
open scoped ENNReal

namespace CAH

/-- Theorem 7.11 for the chiral operator `Ĥ = H_{0,2 sin(π·),α,θ}`, unconditionally. -/
theorem thm_cover_chiral' {α : ℝ} (hα : Irrational α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n ≥ 4, ∃ (m : ℕ) (a b : Fin m → ℝ), (∀ i, a i ≤ b i) ∧
      (m : ℝ) ≤ q α n + q α (n - 1) ∧ ∑ i, (b i - a i) ≤ C / q α n ∧
      ∀ θ : ℝ, spectrum ℝ (chiralH α θ) ⊆ ⋃ i, Icc (a i) (b i) := by
  obtain ⟨C', hC', hBC⟩ := BlockCover.blockCoverProp_holds
  refine ⟨2 * C', by positivity, fun n hn => ?_⟩
  exact thm_cover_chiral hα hn (hBC α hα n hn)

/-- A finite union of closed intervals is closed. -/
lemma isClosed_iUnion_Icc {m : ℕ} (a b : Fin m → ℝ) : IsClosed (⋃ i, Icc (a i) (b i)) :=
  isClosed_iUnion_of_finite fun _ => isClosed_Icc

/-- **Theorem 7.11** (`thm-cover`).  For irrational `α` there is an absolute constant `C`
such that for every `n ≥ 4` there are `m ≤ q_n + q_{n-1}` closed intervals, independent of
`θ`, of total length `≤ C/q_n`, covering `σ(H_{α,θ})` for all `θ`. -/
theorem thm_cover {α : ℝ} (hα : Irrational α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n ≥ 4, ∃ (m : ℕ) (a b : Fin m → ℝ), (∀ i, a i ≤ b i) ∧
      (m : ℝ) ≤ q α n + q α (n - 1) ∧ ∑ i, (b i - a i) ≤ C / q α n ∧
      ∀ θ : ℝ, spectrum ℝ (amo α θ) ⊆ ⋃ i, Icc (a i) (b i) := by
  -- `σ(H_{α,θ}) ⊆ closure ⋃ₓ σ(Ĥ_{α/2,x})` (chiral gauge) and `Ĥ_{α/2,x} = chiralH α (2x)`.
  obtain ⟨C, hC, hcov⟩ := thm_cover_chiral' hα
  refine ⟨C, hC, fun n hn => ?_⟩
  obtain ⟨m, a, b, hab, hm, hlen, hsub⟩ := hcov n hn
  refine ⟨m, a, b, hab, hm, hlen, fun θ => ?_⟩
  refine (amo_spectrum_subset_chiral α θ).trans ?_
  refine (isClosed_iUnion_Icc a b).closure_subset_iff.2 ?_
  refine iUnion_subset fun x => ?_
  have : chiral (α / 2) x = chiralH α (2 * x) := by
    rw [← chiral_half]; congr 1; ring
  rw [this]
  exact hsub _

/-- Theorem 7.11 for the direct integral: the same intervals cover `σ(M_α)`. -/
theorem thm_cover_sigmaAMO {α : ℝ} (hα : Irrational α) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n ≥ 4, ∃ (m : ℕ) (a b : Fin m → ℝ), (∀ i, a i ≤ b i) ∧
      (m : ℝ) ≤ q α n + q α (n - 1) ∧ ∑ i, (b i - a i) ≤ C / q α n ∧
      sigmaAMO α ⊆ ⋃ i, Icc (a i) (b i) := by
  obtain ⟨C, hC, hcov⟩ := thm_cover hα
  refine ⟨C, hC, fun n hn => ?_⟩
  obtain ⟨m, a, b, hab, hm, hlen, hsub⟩ := hcov n hn
  exact ⟨m, a, b, hab, hm, hlen,
    (isClosed_iUnion_Icc a b).closure_subset_iff.2 (iUnion_subset hsub)⟩

/-- Covers of a set `K` as provided by Theorem 7.11 give `dim_H K ≤ 1/2` and
`𝓗^{1/2}(K) < ∞`. -/
lemma dimH_le_half_of_thm_cover {α : ℝ} (hα : Irrational α) {K : Set ℝ}
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ n ≥ 4, ∃ (m : ℕ) (a b : Fin m → ℝ), (∀ i, a i ≤ b i) ∧
      (m : ℝ) ≤ q α n + q α (n - 1) ∧ ∑ i, (b i - a i) ≤ C / q α n ∧
      K ⊆ ⋃ i, Icc (a i) (b i)) :
    dimH K ≤ 1 / 2 ∧ μH[1 / 2] K < ⊤ := by
  obtain ⟨C, hC, hcov⟩ := h
  have key : ∀ n : ℕ, ∃ (m : ℕ) (a b : Fin m → ℝ), 4 ≤ n → (∀ i, a i ≤ b i) ∧
      (m : ℝ) ≤ q α n + q α (n - 1) ∧ ∑ i, (b i - a i) ≤ C / q α n ∧
      K ⊆ ⋃ i, Icc (a i) (b i) := by
    intro n
    by_cases hn : 4 ≤ n
    · obtain ⟨m, a, b, h1, h2, h3, h4⟩ := hcov n hn
      exact ⟨m, a, b, fun _ => ⟨h1, h2, h3, h4⟩⟩
    · exact ⟨0, Fin.elim0, Fin.elim0, fun h => absurd h hn⟩
  choose m a b h using key
  exact dimH_le_half_of_cfCovers hα hC m a b (fun n hn => (h n hn).1)
    (fun n hn => (h n hn).2.2.2) (fun n hn => (h n hn).2.1) (fun n hn => (h n hn).2.2.1)

/-- **Theorem 1.1** (`Hdimthm`).  For any irrational `α` and real `θ`,
`dim_H σ(H_{α,θ}) ≤ 1/2`; moreover `𝓗^{1/2}(σ(H_{α,θ})) < ∞`. -/
theorem dimH_spectrum_le_half {α : ℝ} (hα : Irrational α) (θ : ℝ) :
    dimH (spectrum ℝ (amo α θ)) ≤ 1 / 2 ∧ μH[1 / 2] (spectrum ℝ (amo α θ)) < ⊤ := by
  obtain ⟨C, hC, hcov⟩ := thm_cover hα
  refine dimH_le_half_of_thm_cover hα ⟨C, hC, fun n hn => ?_⟩
  obtain ⟨m, a, b, h1, h2, h3, h4⟩ := hcov n hn
  exact ⟨m, a, b, h1, h2, h3, h4 θ⟩

/-- Theorem 1.1 for the spectrum `σ(M_α)` of the direct integral. -/
theorem dimH_sigmaAMO_le_half {α : ℝ} (hα : Irrational α) :
    dimH (sigmaAMO α) ≤ 1 / 2 ∧ μH[1 / 2] (sigmaAMO α) < ⊤ :=
  dimH_le_half_of_thm_cover hα (thm_cover_sigmaAMO hα)

/-- Theorem 1.1 for the chiral operator `Ĥ_{α,θ}` of (1.2). -/
theorem dimH_spectrum_chiral_le_half' {α : ℝ} (hα : Irrational α) (θ : ℝ) :
    dimH (spectrum ℝ (chiral α θ)) ≤ 1 / 2 := by
  have h2 : Irrational (2 * α) := by
    simpa using Irrational.natCast_mul hα two_ne_zero
  obtain ⟨C, hC, hcov⟩ := thm_cover_chiral' h2
  have e : chiral α θ = chiralH (2 * α) (2 * θ) := by
    rw [← chiral_half]; congr 1 <;> ring
  rw [e]
  refine (dimH_le_half_of_thm_cover h2 ⟨C, hC, fun n hn => ?_⟩).1
  obtain ⟨m, a, b, h1, h2', h3, h4⟩ := hcov n hn
  exact ⟨m, a, b, h1, h2', h3, h4 _⟩

/-- **Theorem 1.2** (`zero`).  For any irrational `α` and real `θ`, `|σ(H_{α,θ})| = 0`. -/
theorem volume_spectrum_eq_zero {α : ℝ} (hα : Irrational α) (θ : ℝ) :
    volume (spectrum ℝ (amo α θ)) = 0 :=
  SGD.Hausdorff.volume_eq_zero_of_dimH_lt_one
    ((dimH_spectrum_le_half hα θ).1.trans_lt (by norm_num))

/-- Theorem 1.2 for `σ(M_α)`. -/
theorem volume_sigmaAMO_eq_zero {α : ℝ} (hα : Irrational α) : volume (sigmaAMO α) = 0 :=
  SGD.Hausdorff.volume_eq_zero_of_dimH_lt_one
    ((dimH_sigmaAMO_le_half hα).1.trans_lt (by norm_num))

end CAH
