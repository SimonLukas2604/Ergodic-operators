/-
Copyright (c) 2026. Formalization of
  S. Becker, S. Jitomirskaya, I. Krasovsky, "Critical almost Mathieu operator: hidden
  singularity, gap continuity, and the Hausdorff dimension of the spectrum".

# From spectral covers to `dim_H ≤ 1/2`  (paper §2.1 and §8, tex l.430–439, l.1792–1807)

Theorem 7.11 (`thm-cover`) provides, for every `n ≥ 4`, a cover of the spectrum by
`m ≤ q_n + q_{n-1}` closed intervals of total length `≤ C/q_n`.  Section 8 turns this into
`dim_H σ(H_{α,θ}) ≤ 1/2`:

* `sum_rpow_le_card_rpow_mul` — Hölder's inequality (8.1):
  `∑_{j<m} |I_j|^t ≤ m^{1-t} (∑_j |I_j|)^t` for `0 < t < 1`;
* `hausdorffMeasure_eq_zero_of_cfCovers` — the paper's argument verbatim: for every
  `1/2 < t < 1` the costs `∑ |I_j|^t ≤ C' q_n^{1-2t} → 0`, so `𝓗^t(K) = 0`;
* `dimH_le_half_of_cfCovers` — hence `dim_H K ≤ 1/2`;
* `hausdorffMeasure_half_lt_top_of_cfCovers` — the slightly stronger `𝓗^{1/2}(K) < ∞`
  (Cauchy–Schwarz, via `SGD.Hausdorff.hausdorffMeasure_half_le_of_covers`).

Mathlib's `μH[d]` is the Hausdorff measure built from arbitrary countable covers; on `ℝ`
covers by intervals give the same value, and only "a cover bounds `μH`" is used.
-/
import CriticalAMOHausdorff.Basic
import SpectralGapsDimension.Hausdorff
import SpectralGapsDimension.Arithmetic

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace CAH

/-- Hölder's inequality (8.1): for `0 < t < 1` and nonnegative `x`,
`∑_{i ∈ s} x_i^t ≤ (#s)^{1-t} (∑_{i∈s} x_i)^t`. -/
lemma sum_rpow_le_card_rpow_mul {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    ∑ i ∈ s, x i ^ t ≤ (s.card : ℝ) ^ (1 - t) * (∑ i ∈ s, x i) ^ t := by
  have hpq : (1 / (1 - t)).HolderConjugate (1 / t) := by
    refine ⟨?_, ?_, ?_⟩
    · simp
    · exact one_div_pos.2 (by linarith)
    · exact one_div_pos.2 ht0
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg s hpq (f := fun _ => (1 : ℝ))
    (g := fun i => x i ^ t) (fun _ _ => zero_le_one) (fun i _ => Real.rpow_nonneg (hx i) _)
  simp only [one_mul, Real.one_rpow, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  have e1 : ((s.card : ℝ)) ^ (1 / (1 / (1 - t))) = (s.card : ℝ) ^ (1 - t) := by
    congr 1; field_simp
  have e2 : (∑ i ∈ s, (x i ^ t) ^ (1 / t)) ^ (1 / (1 / t)) = (∑ i ∈ s, x i) ^ t := by
    rw [one_div_one_div]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Real.rpow_mul (hx i), mul_one_div_cancel ht0.ne', Real.rpow_one]
  rwa [e1, e2] at h

/-- Hypotheses of Theorem 7.11: for every `n ≥ n₀`, `K` is covered by `m n ≤ 2 Q_n` closed
intervals `[a_{n,i}, b_{n,i}]` of total length `≤ C/Q_n`, and `Q_n → ∞`. -/
structure CFCovers (K : Set ℝ) (Q : ℕ → ℝ) (C : ℝ) where
  n₀ : ℕ
  m : ℕ → ℕ
  a : ∀ n, Fin (m n) → ℝ
  b : ∀ n, Fin (m n) → ℝ
  le : ∀ n ≥ n₀, ∀ i, a n i ≤ b n i
  cover : ∀ n ≥ n₀, K ⊆ ⋃ i, Icc (a n i) (b n i)
  count : ∀ n ≥ n₀, (m n : ℝ) ≤ 2 * Q n
  length : ∀ n ≥ n₀, ∑ i, (b n i - a n i) ≤ C / Q n

namespace CFCovers

variable {K : Set ℝ} {Q : ℕ → ℝ} {C : ℝ}

/-- **§8.** For `1/2 < t < 1`, `𝓗^t(K) = 0`: by (8.1) the `t`-cost of the `n`-th cover is
`≤ (2Q_n)^{1-t} (C/Q_n)^t = 2^{1-t} C^t Q_n^{1-2t} → 0`. -/
theorem hausdorffMeasure_eq_zero (hc : CFCovers K Q C) (hC : 0 ≤ C)
    (hQ : Tendsto Q atTop atTop) {t : ℝ} (ht : 1 / 2 < t) (ht1 : t < 1) : μH[t] K = 0 := by
  have ht0 : 0 < t := by linarith
  have hQpos : ∀ᶠ n in atTop, 0 < Q n := hQ.eventually_gt_atTop 0
  have hn₀ : ∀ᶠ n in atTop, hc.n₀ ≤ n := eventually_ge_atTop _
  -- the bound `C' Q_n^{1-2t}`
  set C' : ℝ := 2 ^ (1 - t) * C ^ t
  have hcost_le : ∀ᶠ n in atTop,
      ∑ i, (hc.b n i - hc.a n i) ^ t ≤ C' * Q n ^ (1 - 2 * t) := by
    filter_upwards [hQpos, hn₀] with n hQn hn
    have hx : ∀ i, 0 ≤ hc.b n i - hc.a n i := fun i => by linarith [hc.le n hn i]
    have h1 := sum_rpow_le_card_rpow_mul Finset.univ _ hx ht0 ht1
    rw [Finset.card_univ, Fintype.card_fin] at h1
    have hsum0 : 0 ≤ ∑ i, (hc.b n i - hc.a n i) := Finset.sum_nonneg fun i _ => hx i
    calc ∑ i, (hc.b n i - hc.a n i) ^ t
        ≤ (hc.m n : ℝ) ^ (1 - t) * (∑ i, (hc.b n i - hc.a n i)) ^ t := h1
      _ ≤ (2 * Q n) ^ (1 - t) * (C / Q n) ^ t := by
          gcongr
          · exact hc.count n hn
          · exact hc.length n hn
      _ = C' * Q n ^ (1 - 2 * t) := by
          rw [Real.mul_rpow (by norm_num) hQn.le, Real.div_rpow hC hQn.le]
          have : Q n ^ (1 - 2 * t) = Q n ^ (1 - t) / Q n ^ t := by
            rw [← Real.rpow_sub hQn]; ring_nf
          rw [this]
          simp only [C']
          field_simp
  have hlim : Tendsto (fun n => C' * Q n ^ (1 - 2 * t)) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (y := 2 * t - 1) (by linarith)).comp hQ
    simpa [Function.comp_def, neg_sub] using this.const_mul C'
  have hcost : Tendsto (fun n => ∑ i, (hc.b n i - hc.a n i) ^ t) atTop (𝓝 0) := by
    refine squeeze_zero' ?_ hcost_le hlim
    filter_upwards [hn₀] with n hn
    exact Finset.sum_nonneg fun i _ =>
      Real.rpow_nonneg (by linarith [hc.le n hn i]) _
  -- each interval has length `≤ C/Q_n → 0`
  have hδ : Tendsto (fun n => C / Q n) atTop (𝓝 0) := hQ.const_div_atTop C
  refine SGD.Hausdorff.hausdorffMeasure_eq_zero_of_covers ht0.le (fun n => Fin (hc.m n))
    hc.a hc.b (fun n => C / Q n) hδ ?_ ?_ hcost
  · filter_upwards [hn₀] with n hn i
    refine ⟨hc.le n hn i, ?_⟩
    have hx : ∀ j, 0 ≤ hc.b n j - hc.a n j := fun j => by linarith [hc.le n hn j]
    exact (Finset.single_le_sum (fun j _ => hx j) (Finset.mem_univ i)).trans (hc.length n hn)
  · filter_upwards [hn₀] with n hn
    exact hc.cover n hn

/-- **Proof of Theorem 1.1 from Theorem 7.11.** Covers as in `CFCovers` force
`dim_H K ≤ 1/2`. -/
theorem dimH_le_half (hc : CFCovers K Q C) (hC : 0 ≤ C) (hQ : Tendsto Q atTop atTop) :
    dimH K ≤ 1 / 2 := by
  refine le_of_forall_gt fun d hd => ?_
  -- pick `t` with `1/2 < t < min d 1`
  have hhalf : (1 / 2 : ℝ≥0∞) < min d 1 :=
    lt_min hd (by simp)
  obtain ⟨t, ht1, ht2⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hhalf
  have ht1' : (1 / 2 : ℝ) < t := by
    have : ((1 / 2 : ℝ≥0) : ℝ≥0∞) < t := by simpa using ht1
    exact_mod_cast ENNReal.coe_lt_coe.1 this
  have ht2' : (t : ℝ) < 1 := by
    have h := ht2.trans_le (min_le_right _ _)
    exact_mod_cast ENNReal.coe_lt_one_iff.1 h
  have h0 : μH[(t : ℝ)] K = 0 := hc.hausdorffMeasure_eq_zero hC hQ ht1' ht2'
  have := dimH_le_of_hausdorffMeasure_ne_top (d := t) (by rw [h0]; exact ENNReal.zero_ne_top)
  exact this.trans_lt (ht2.trans_le (min_le_left _ _))

/-- The stronger conclusion `𝓗^{1/2}(K) < ∞` (Cauchy–Schwarz instead of Hölder). -/
theorem hausdorffMeasure_half_lt_top (hc : CFCovers K Q C) (hC : 0 ≤ C)
    (hQ : Tendsto Q atTop atTop) : μH[1 / 2] K < ⊤ := by
  have hn₀ : ∀ᶠ n in atTop, hc.n₀ ≤ n := eventually_ge_atTop _
  refine lt_of_le_of_lt (SGD.Hausdorff.hausdorffMeasure_half_le_of_covers hC Q hQ hc.m hc.a hc.b
    ?_ ?_ ?_ ?_) ENNReal.ofReal_lt_top
  · filter_upwards [hn₀] with n hn using hc.le n hn
  · filter_upwards [hn₀] with n hn using hc.cover n hn
  · filter_upwards [hn₀] with n hn using hc.count n hn
  · filter_upwards [hn₀] with n hn using hc.length n hn

end CFCovers

/-- `q_{n-1} ≤ q_n`, so covers by `m ≤ q_n + q_{n-1}` intervals (Theorem 7.11) are covers by
`m ≤ 2 q_n` intervals. -/
lemma q_pred_le (α : ℝ) (n : ℕ) : q α (n - 1) ≤ q α n := by
  rcases n with _ | n
  · rfl
  · exact GenContFract.of_den_mono

/-- `q_n → ∞` for irrational `α`. -/
lemma tendsto_q {α : ℝ} (hα : Irrational α) : Tendsto (q α) atTop atTop :=
  (SGD.cfGrowth hα).tendsto_atTop

/-- **Theorem 1.1 from Theorem 7.11**, in the form used in the paper: if for all `n ≥ 4` the
set `K` is covered by `m_n ≤ q_n + q_{n-1}` closed intervals of total length `≤ C/q_n`,
then `dim_H K ≤ 1/2` (and even `𝓗^{1/2}(K) < ∞`). -/
theorem dimH_le_half_of_cfCovers {α : ℝ} (hα : Irrational α) {K : Set ℝ} {C : ℝ}
    (hC : 0 ≤ C) (m : ℕ → ℕ) (a b : ∀ n, Fin (m n) → ℝ)
    (hab : ∀ n ≥ 4, ∀ i, a n i ≤ b n i)
    (hcov : ∀ n ≥ 4, K ⊆ ⋃ i, Icc (a n i) (b n i))
    (hcount : ∀ n ≥ 4, (m n : ℝ) ≤ q α n + q α (n - 1))
    (hlen : ∀ n ≥ 4, ∑ i, (b n i - a n i) ≤ C / q α n) :
    dimH K ≤ 1 / 2 ∧ μH[1 / 2] K < ⊤ := by
  let hc : CFCovers K (q α) C :=
    { n₀ := 4, m := m, a := a, b := b, le := hab, cover := hcov
      count := fun n hn => (hcount n hn).trans (by linarith [q_pred_le α n])
      length := hlen }
  exact ⟨hc.dimH_le_half hC (tendsto_q hα), hc.hausdorffMeasure_half_lt_top hC (tendsto_q hα)⟩

end CAH
