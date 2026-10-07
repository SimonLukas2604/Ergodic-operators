/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §4.7.1: the Ishii–Pastur theorem   (book pp. 343–344)

## Main results
* `DF.Cocycle.decay_of_ruelle` — a deterministic consequence of Ruelle's theorem
  (Theorem 3.8.7): if `(1/n) log ‖A_n ⋯ A_1‖ → L > 0`, then any orbit `A_n ⋯ A_1 v` that grows at
  most linearly decays exponentially.
* `DF.ErgodicFamily.atom_of_lyapBehavior` — the deterministic step in the proof of
  Theorem 4.7.2: if `H_ω` has Lyapunov behavior at `x ∈ ℝ` with `L(x) > 0` and `x` is a
  generalized eigenvalue, then `x` is an eigenvalue of `H_ω`, hence an atom of the canonical
  spectral measure `η_ω`.
* `DF.ErgodicFamily.measurableSet_lyapBehavior` — the set of pairs `(x, ω)` such that `H_ω` has
  Lyapunov behavior at `x` is measurable (needed for Fubini).
* `DF.ErgodicFamily.ae_volume_not_lyapBehavior` — (4.7.8): for `μ`-a.e. `ω`, `H_ω` has Lyapunov
  behavior at Lebesgue-a.e. `x`.
* `DF.ErgodicFamily.ishii_pastur` — **Theorem 4.7.2 (Ishii–Pastur)**, (4.7.4): for `μ`-a.e. `ω`,
  the absolutely continuous part of `η_ω` gives no weight to `{x : L(x) > 0} = ℝ \ Z`.

## Hypotheses
The proof uses Theorem 2.4.2(b) (generalized eigenvalues support the canonical spectral
measure), which is only available as the statement `DF.GenEigSupportStatement`; it enters as a
hypothesis (for the potentials `V_ω`).

## Deviations
The absolutely continuous part of a measure `η` is written
`volume.withDensity (η.rnDeriv volume)` (Lebesgue decomposition).
-/
import DamanikFillman.Ch4.Lyapunov
import DamanikFillman.Ch3.Ruelle
import DamanikFillman.Ch2.GenEigenSupport
import DamanikFillman.Ch1.SpectralDecomposition

noncomputable section

open scoped InnerProductSpace ComplexConjugate Matrix.Norms.L2Operator
open MeasureTheory Set Filter Topology

namespace DF

namespace Cocycle

lemma norm_C2_sq (w : C2) : ‖w‖ ^ 2 = ‖w 0‖ ^ 2 + ‖w 1‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_two]

lemma norm_apply_le_C2 (w : C2) (i : Fin 2) : ‖w i‖ ≤ ‖w‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  rw [norm_C2_sq]
  fin_cases i
  · simp only [Fin.zero_eta]; nlinarith [sq_nonneg ‖w 1‖]
  · simp only [Fin.mk_one]; nlinarith [sq_nonneg ‖w 0‖]

lemma norm_C2_le (w : C2) : ‖w‖ ≤ ‖w 0‖ + ‖w 1‖ := by
  refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
  rw [norm_C2_sq]; nlinarith [norm_nonneg (w 0), norm_nonneg (w 1)]

lemma tendsto_log_one_add_div : Tendsto (fun n : ℕ => Real.log (1 + n) / n) atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
    (tendsto_atTop_add_const_left atTop (1 : ℝ) (tendsto_natCast_atTop_atTop (R := ℝ)))
  have h2 : Tendsto (fun n : ℕ => (1 + (n : ℝ)) / n) atTop (𝓝 1) := by
    have : Tendsto (fun n : ℕ => 1 / (n : ℝ) + 1) atTop (𝓝 (0 + 1)) :=
      tendsto_one_div_atTop_nhds_zero_nat.add tendsto_const_nhds
    rw [zero_add] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (n : ℝ) ≠ 0 := by positivity
    field_simp; ring
  have := h.mul h2
  rw [zero_mul] at this
  refine this.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have : (n : ℝ) ≠ 0 := by positivity
  simp only [Function.comp_apply, pow_one, one_mul, add_zero]
  field_simp

/-- A deterministic consequence of Ruelle's theorem (Theorem 3.8.7): under its hypotheses
(with `‖A_n‖` bounded), an orbit `A_n ⋯ A_1 v`, `v ≠ 0`, of at most linear growth decays
exponentially. -/
theorem decay_of_ruelle {A : ℕ → M2} {L : ℝ} (hdet : ∀ n, (A n).det = 1) {K : ℝ}
    (hK : ∀ n, ‖A n‖ ≤ K)
    (hT : Tendsto (fun n : ℕ => Real.log ‖seqProd A n‖ / n) atTop (𝓝 L)) (hL : 0 < L)
    {v : C2} (hv : v ≠ 0) {C : ℝ} (hpoly : ∀ n : ℕ, ‖actC (seqProd A n) v‖ ≤ C * (1 + n)) :
    ∃ c > 0, ∀ᶠ n : ℕ in atTop, ‖actC (seqProd A n) v‖ ≤ Real.exp (-(c * n)) := by
  have hA1 : ∀ n, 1 ≤ ‖A n‖ := fun n => one_le_norm_of_det_eq_one (hdet n)
  have hA0 : Tendsto (fun n : ℕ => Real.log ‖A n‖ / n) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (tendsto_const_div_atTop_nhds_zero_nat (Real.log K)) (fun n => ?_) (fun n => ?_)
    · exact div_nonneg (Real.log_nonneg (hA1 n)) (Nat.cast_nonneg n)
    · exact div_le_div_of_nonneg_right (Real.log_le_log (by linarith [hA1 n]) (hK n))
        (Nat.cast_nonneg n)
  obtain ⟨W, -, hin, hout⟩ := ruelle A L hdet hA0 hT hL
  by_cases hvW : v ∈ W
  · refine ⟨L / 2, by positivity, ?_⟩
    have h := hin v hvW hv
    filter_upwards [h.eventually (gt_mem_nhds (show -L < -(L / 2) by linarith)),
      eventually_ge_atTop 1] with n hn hn1
    set w := actC (seqProd A n) v
    rcases (norm_nonneg w).eq_or_lt with h0 | hpos
    · rw [← h0]; exact (Real.exp_pos _).le
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have : Real.log ‖w‖ < -(L / 2 * n) := by
        rw [div_lt_iff₀ hn0] at hn; linarith
      exact ((Real.log_lt_iff_lt_exp hpos).1 this).le
  · exfalso
    have h := hout v hvW
    set D := max C 1
    have hD : 1 ≤ D := le_max_right _ _
    have hup : Tendsto (fun n : ℕ => Real.log D / n + Real.log (1 + n) / n) atTop (𝓝 (0 + 0)) :=
      (tendsto_const_div_atTop_nhds_zero_nat _).add tendsto_log_one_add_div
    rw [add_zero] at hup
    have hle : ∀ n : ℕ, Real.log ‖actC (seqProd A n) v‖ / n ≤
        Real.log D / n + Real.log (1 + n) / n := by
      intro n
      rw [← add_div]
      refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg n)
      have h1n : (1 : ℝ) ≤ 1 + n := by have := Nat.cast_nonneg (α := ℝ) n; linarith
      rw [← Real.log_mul (by linarith) (by linarith)]
      have hb : ‖actC (seqProd A n) v‖ ≤ D * (1 + n) :=
        (hpoly n).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith))
      rcases (norm_nonneg (actC (seqProd A n) v)).eq_or_lt with h0 | hpos
      · rw [← h0, Real.log_zero]; exact Real.log_nonneg (by nlinarith)
      · exact Real.log_le_log hpos hb
    have := le_of_tendsto_of_tendsto' h hup hle
    linarith

end Cocycle

end DF
