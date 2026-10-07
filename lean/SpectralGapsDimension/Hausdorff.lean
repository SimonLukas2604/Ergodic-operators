/-
Copyright (c) 2026. Formalization of
  S. Becker, "Self-dual perturbations of the critical almost Mathieu operator:
  Dry Ten Martini and Hausdorff dimension" (Paper II).

# Hausdorff covers  (paper §1 definitions, §4.1 end, §6 "Hausdorff covers and completion")

The paper turns interval covers of the spectrum into Hausdorff bounds in two ways:

* **Brjuno branch** (proof of the dimension assertion of Theorem 1.1, after
  [BJK2026, §8]): covers by `m_n ≤ 2 q_n` intervals of total length `≤ C/q_n` give, by
  Cauchy–Schwarz, `∑ |I|^{1/2} ≤ (m_n ∑|I|)^{1/2} ≤ √(2C)`, hence `𝓗^{1/2}(K) ≤ √(2C)`
  (`hausdorffMeasure_half_le_of_covers`).
* **Liouville branch** (proof of Theorem 1.2): for each `d > 0` covers whose `d`-costs tend to
  `0` give `𝓗^d(K) = 0` (`hausdorffMeasure_eq_zero_of_covers`), hence `dim_H K = 0`.

We also record the elementary consequences used for the Cantor assertions:
`𝓗^{1/2}(K) < ∞ ⇒ dim_H K ≤ 1/2 ⇒ |K| = 0 ⇒ interior K = ∅`.

Mathlib's `μH[d]` is the Hausdorff measure defined with arbitrary countable covers; on `ℝ`,
covers by intervals give the same value, and only the inequality "a cover bounds `μH`" is
used, which is `MeasureTheory.Measure.hausdorffMeasure_le_liminf_sum`.

-/
import Mathlib

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace SGD.Hausdorff

/-- Cauchy–Schwarz in the form `∑_{i ∈ s} √xᵢ ≤ √(#s · ∑_{i ∈ s} xᵢ)`. -/
lemma sum_sqrt_le {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) :
    ∑ i ∈ s, √(x i) ≤ √(s.card * ∑ i ∈ s, x i) := by
  apply Real.le_sqrt_of_sq_le
  have h := sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => √(x i))
  simpa [Real.sq_sqrt (hx _)] using h

lemma ediam_Icc_rpow {a b : ℝ} (d : ℝ) (hd : 0 ≤ d) (hab : a ≤ b) :
    Metric.ediam (Icc a b) ^ d = ENNReal.ofReal ((b - a) ^ d) := by
  rw [Real.ediam_Icc, ENNReal.ofReal_rpow_of_nonneg (by linarith) hd]

/-- **Covers with vanishing cost.**  Let `K ⊆ ℝ` and let `l` be a nontrivial filter.  If,
eventually along `l`, `K` is covered by finitely many intervals `[aᵢ, bᵢ]` of length
`≤ δ → 0`, and the costs `∑ (bᵢ - aᵢ)^d` tend to `0`, then `𝓗^d(K) = 0`. -/
theorem hausdorffMeasure_eq_zero_of_covers {β : Type*} {l : Filter β} [l.NeBot] {K : Set ℝ}
    {d : ℝ} (hd : 0 ≤ d) (ι : β → Type*) [∀ n, Fintype (ι n)] (a b : ∀ n, ι n → ℝ)
    (δ : β → ℝ) (hδ : Tendsto δ l (𝓝 0))
    (hlen : ∀ᶠ n in l, ∀ i, a n i ≤ b n i ∧ b n i - a n i ≤ δ n)
    (hcov : ∀ᶠ n in l, K ⊆ ⋃ i, Icc (a n i) (b n i))
    (hcost : Tendsto (fun n => ∑ i, (b n i - a n i) ^ d) l (𝓝 0)) : μH[d] K = 0 := by
  have hle := Measure.hausdorffMeasure_le_liminf_sum d K (l := l)
    (fun n => ENNReal.ofReal (δ n))
    (by simpa using (ENNReal.tendsto_ofReal hδ))
    (fun n i => Icc (a n i) (b n i))
    (hlen.mono fun n hn i => by
      rw [Real.ediam_Icc]; exact ENNReal.ofReal_le_ofReal (hn i).2) hcov
  have hcost' : Tendsto (fun n => ∑ i, Metric.ediam (Icc (a n i) (b n i)) ^ d) l (𝓝 0) := by
    have h1 : Tendsto (fun n => ENNReal.ofReal (∑ i, (b n i - a n i) ^ d)) l (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal hcost
    refine h1.congr' ?_
    filter_upwards [hlen] with n hn
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Real.rpow_nonneg (by linarith [(hn i).1]) _)]
    exact Finset.sum_congr rfl fun i _ => (ediam_Icc_rpow d hd (hn i).1).symm
  rw [hcost'.liminf_eq] at hle
  exact le_antisymm hle zero_le

/-- **Brjuno covers ⇒ finite `𝓗^{1/2}`** (proof of the dimension assertion of Theorem 1.1,
following [BJK2026, §8]).  Suppose `Q_n → ∞` and, for all large `n`, `K` is covered by
`m_n ≤ 2 Q_n` intervals of total length `≤ C / Q_n`.  Then `𝓗^{1/2}(K) ≤ √(2C)`. -/
theorem hausdorffMeasure_half_le_of_covers {K : Set ℝ} {C : ℝ} (hC : 0 ≤ C) (Q : ℕ → ℝ)
    (hQ : Tendsto Q atTop atTop) (m : ℕ → ℕ) (a b : ∀ n, Fin (m n) → ℝ)
    (hab : ∀ᶠ n in atTop, ∀ i, a n i ≤ b n i)
    (hcov : ∀ᶠ n in atTop, K ⊆ ⋃ i, Icc (a n i) (b n i))
    (hcount : ∀ᶠ n in atTop, (m n : ℝ) ≤ 2 * Q n)
    (hlen : ∀ᶠ n in atTop, ∑ i, (b n i - a n i) ≤ C / Q n) :
    μH[1 / 2] K ≤ ENNReal.ofReal √(2 * C) := by
  have hQpos : ∀ᶠ n in atTop, 0 < Q n := hQ.eventually_gt_atTop 0
  have hr : Tendsto (fun n => ENNReal.ofReal (C / Q n)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (hQ.const_div_atTop C)
  have hle := Measure.hausdorffMeasure_le_liminf_sum (1 / 2) K (l := atTop)
    (fun n => ENNReal.ofReal (C / Q n)) hr (fun n i => Icc (a n i) (b n i))
    (by
      filter_upwards [hab, hlen] with n hn hl i
      rw [Real.ediam_Icc]
      refine ENNReal.ofReal_le_ofReal (le_trans ?_ hl)
      exact Finset.single_le_sum (f := fun i => b n i - a n i)
        (fun j _ => by linarith [hn j]) (Finset.mem_univ i)) hcov
  refine hle.trans (liminf_le_of_frequently_le' (Eventually.frequently ?_))
  filter_upwards [hab, hlen, hcount, hQpos] with n hn hl hc hq
  have hnn : ∀ i, 0 ≤ b n i - a n i := fun i => by linarith [hn i]
  calc ∑ i, Metric.ediam (Icc (a n i) (b n i)) ^ (1 / 2 : ℝ)
      = ENNReal.ofReal (∑ i, √(b n i - a n i)) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => Real.sqrt_nonneg _)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ediam_Icc_rpow _ (by norm_num) (hn i), Real.sqrt_eq_rpow]
    _ ≤ ENNReal.ofReal √(2 * C) := by
        refine ENNReal.ofReal_le_ofReal ((sum_sqrt_le _ _ hnn).trans (Real.sqrt_le_sqrt ?_))
        rw [Finset.card_univ, Fintype.card_fin]
        calc (m n : ℝ) * ∑ i, (b n i - a n i) ≤ (2 * Q n) * (C / Q n) :=
              mul_le_mul hc hl (Finset.sum_nonneg fun i _ => hnn i) (by linarith)
          _ = 2 * C := by field_simp

/-- A set with zero `d`-dimensional Hausdorff measure for every `d > 0` has dimension `0`. -/
theorem dimH_eq_zero_of_forall {K : Set ℝ} (h : ∀ d : ℝ, 0 < d → μH[d] K = 0) :
    dimH K = 0 := by
  refine le_antisymm ?_ zero_le
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  rw [zero_add]
  exact dimH_le_of_hausdorffMeasure_ne_top
    (by rw [h ε (by exact_mod_cast hε)]; exact ENNReal.zero_ne_top)

/-- `𝓗^{1/2}(K) < ∞ ⇒ dim_H K ≤ 1/2` (Theorem 1.1, "in particular"). -/
theorem dimH_le_half {K : Set ℝ} (h : μH[1 / 2] K < ⊤) : dimH K ≤ 1 / 2 := by
  have := dimH_le_of_hausdorffMeasure_ne_top (d := (1 / 2 : ℝ≥0)) (by simpa using h.ne)
  simpa using this

/-- A subset of `ℝ` of Hausdorff dimension `< 1` is Lebesgue-null. -/
theorem volume_eq_zero_of_dimH_lt_one {K : Set ℝ} (h : dimH K < 1) : volume K = 0 := by
  rw [← hausdorffMeasure_real]
  have := hausdorffMeasure_of_dimH_lt (d := (1 : ℝ≥0)) (s := K) (by simpa using h)
  simpa using this

/-- A Lebesgue-null subset of `ℝ` has empty interior. -/
theorem interior_eq_empty_of_volume_eq_zero {K : Set ℝ} (h : volume K = 0) : interior K = ∅ :=
  volume.interior_eq_empty_of_null h

end SGD.Hausdorff
