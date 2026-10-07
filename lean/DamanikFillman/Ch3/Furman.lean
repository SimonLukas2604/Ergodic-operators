/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §3.5.2: Furman's semi-uniform subadditive ergodic theorem (Theorem 3.5.8, book pp. 252–253)

Main result:
* `DF.furman` — **Theorem 3.5.8** (Furman): if `T` is uniquely ergodic with invariant measure
  `μ` and the continuous `f_n` are subadditive, then for every `ε > 0` there is `N` with
  `f_n(ω)/n < inf_k (1/k) ∫ f_k dμ + ε` for all `n ≥ N` and all `ω` (3.5.12).

Deviation: as in our version of Kingman's theorem (`DF.kingman`) we assume the bound
`|f_n| ≤ C n` (which holds e.g. for `f_n = log ‖A_n‖` with `A` a continuous `SL(2)` cocycle).
The general statement is recorded as `DF.FurmanStatement` in `DF.Ch3.TopErgodic`. The proof
follows the book: the covering estimate `DF.Kingman.cover` is combined with the uniform
convergence of Birkhoff averages for uniquely ergodic maps (`DF.tendstoUniformly_of_uniquelyErgodic`)
applied to a continuous minorant (Urysohn) of the indicator of the good set `G_{N,ε}`.
-/
import DamanikFillman.Ch3.Kingman
import DamanikFillman.Ch3.TopErgodic

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Set Function Topology
open scoped ENNReal

namespace DF

variable {Ω : Type*} [MetricSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  {T : Ω → Ω}

lemma continuous_birkhoffSum (hT : Continuous T) {g : Ω → ℝ} (hg : Continuous g) (n : ℕ) :
    Continuous (birkhoffSum T g n) := by
  unfold birkhoffSum
  exact continuous_finset_sum _ fun k _ => hg.comp (hT.iterate k)

/-- **Theorem 3.5.8** (Furman), under the bound `|f_n| ≤ C n`. -/
theorem furman (hT : Continuous T) {μ : Measure Ω} (hμ : invMeasures T = {μ})
    {f : ℕ → C(Ω, ℝ)} (hsub : ∀ n m x, 1 ≤ n → 1 ≤ m → f (n + m) x ≤ f n x + f m (T^[n] x))
    {C : ℝ} (hC : ∀ n x, 1 ≤ n → |f n x| ≤ C * n) :
    ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x,
      f n x / n < (⨅ k : ℕ, (∫ y, f (k + 1) y ∂μ) / (k + 1)) + ε := by
  obtain ⟨hErg, hprob⟩ := UniquelyErgodic.ergodic hμ
  intro ε hε
  set lam := ⨅ k : ℕ, (∫ y, f (k + 1) y ∂μ) / (k + 1)
  have hfm : ∀ n, Measurable (f n) := fun n => (f n).continuous.measurable
  obtain ⟨hae, -⟩ := kingman hErg hfm hsub hC
  -- the reduction to nonpositive sequences, as in the proof of `kingman`
  set f0 : ℕ → Ω → ℝ := fun n x => if n = 0 then 0 else f n x with hf0
  have hf0n : ∀ n x, 1 ≤ n → f0 n x = f n x := fun n x hn => by
    simp only [f0]; rw [if_neg (show n ≠ 0 by omega)]
  have hf0sub : ∀ n m x, f0 (n + m) x ≤ f0 n x + f0 m (T^[n] x) := by
    intro n m x
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [f0]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [f0]
    rw [hf0n _ _ (by omega), hf0n _ _ hn, hf0n _ _ hm]
    exact hsub n m x hn hm
  have hf0C : ∀ n x, |f0 n x| ≤ C * n := by
    intro n x; by_cases hn : n = 0
    · simp [f0, hn]
    · rw [hf0n _ _ (by omega)]; exact hC n x (by omega)
  have hf1C : ∀ x, |f 1 x| ≤ C := fun x => by simpa using hC 1 x le_rfl
  set g : ℕ → Ω → ℝ := fun n x => f0 n x - birkhoffSum T (f 1) n x with hg
  have hS_le : ∀ n x, f0 n x ≤ birkhoffSum T (f 1) n x := by
    intro n
    induction n with
    | zero => intro x; simp [f0]
    | succ n ih =>
      intro x
      have h1 := hf0sub n 1 x
      rw [birkhoffSum_succ_apply]
      have : f0 1 (T^[n] x) = f 1 (T^[n] x) := hf0n 1 _ le_rfl
      linarith [ih x]
  have hgle : ∀ n x, g n x ≤ 0 := fun n x => by simp only [g]; linarith [hS_le n x]
  have hgsub : ∀ n m x, g (n + m) x ≤ g n x + g m (T^[n] x) := by
    intro n m x
    simp only [g, birkhoffSum_add_right_apply]
    linarith [hf0sub n m x]
  have hSabs : ∀ n x, |birkhoffSum T (f 1) n x| ≤ C * n := by
    intro n x
    calc |birkhoffSum T (f 1) n x| ≤ ∑ k ∈ Finset.range n, |f 1 (T^[k] x)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range n, C := Finset.sum_le_sum fun k _ => hf1C _
      _ = C * n := by simp [mul_comm]
  have hglow : ∀ n x, -(2 * C) * n ≤ g n x := by
    intro n x
    have h1 := (abs_le.1 (hf0C n x)).1
    have h2 := (abs_le.1 (hSabs n x)).2
    simp only [g]; linarith
  have hf0c : ∀ n, Continuous (f0 n) := by
    intro n; by_cases hn : n = 0
    · simp only [f0, hn, if_true]; exact continuous_const
    · simp only [f0, hn, if_false]; exact (f n).continuous
  have hgc : ∀ n, Continuous (g n) := fun n =>
    (hf0c n).sub (continuous_birkhoffSum hT (f 1).continuous n)
  have hgm : ∀ n, Measurable (g n) := fun n => (hgc n).measurable
  obtain ⟨c, hc⟩ := Kingman.core hErg hgm hgsub hgle hglow
  set e := ∫ y, f 1 y ∂μ
  have hf1i : Integrable (f 1) μ :=
    (f 1).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hB := birkhoff_ergodic_tendsto hErg hf1i
  have hdecomp : ∀ n x, 1 ≤ n → f n x / n = g n x / n + birkhoffAverage ℝ T (f 1) n x := by
    intro n x hn
    rw [Birkhoff.birkhoffAverage_eq_div]
    simp only [g]
    rw [hf0n n x hn]
    ring
  have hlam : lam = c + e := by
    haveI : (ae μ).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero μ)
    obtain ⟨x, hx1, hx2, hx3⟩ := (hae.and (hc.and hB)).exists
    have : Tendsto (fun n => f n x / n) atTop (𝓝 (c + e)) := by
      refine (hx2.add hx3).congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact (hdecomp n x hn).symm
    exact tendsto_nhds_unique hx1 this
  set δ := ε / 5 with hδ
  have hδpos : 0 < δ := by positivity
  -- uniform convergence of the Birkhoff averages of `f 1`
  obtain ⟨N1, hN1⟩ := eventually_atTop.1
    (Metric.tendstoUniformly_iff.1 (tendstoUniformly_of_uniquelyErgodic hT hμ (f 1)) δ hδpos)
  by_cases hL : 0 < c + δ
  · refine ⟨max N1 1, fun n hn x => ?_⟩
    have hn1 : 1 ≤ n := le_of_max_le_right hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have h1 := hN1 n (le_of_max_le_left hn) x
    rw [Real.dist_eq, abs_lt] at h1
    have hg0 : g n x / n ≤ 0 := div_nonpos_of_nonpos_of_nonneg (hgle n x) hnpos.le
    rw [hdecomp n x hn1, hlam]
    linarith
  push Not at hL
  set L := c + δ with hLdef
  -- the good sets `G_N`
  set G : ℕ → Set Ω := fun N => {y | ∃ k : ℕ, 1 ≤ k ∧ k ≤ N ∧ g k y < k * L}
  have hGo : ∀ N, IsOpen (G N) := by
    intro N
    have : G N = ⋃ k : ℕ, {y | 1 ≤ k ∧ k ≤ N ∧ g k y < k * L} := by ext y; simp [G]
    rw [this]
    refine isOpen_iUnion fun k => ?_
    by_cases hk : 1 ≤ k ∧ k ≤ N
    · simp only [hk.1, hk.2, true_and]
      exact isOpen_lt (hgc k) continuous_const
    · have : {y | 1 ≤ k ∧ k ≤ N ∧ g k y < k * L} = ∅ := by
        ext y; simp only [mem_setOf_eq, mem_empty_iff_false, iff_false]
        exact fun h => hk ⟨h.1, h.2.1⟩
      rw [this]; exact isOpen_empty
  have hGmono : Monotone G := fun N N' hNN' y ⟨k, hk1, hk2, hk3⟩ => ⟨k, hk1, hk2.trans hNN', hk3⟩
  have hGU : ∀ᵐ x ∂μ, x ∈ ⋃ N, G N := by
    filter_upwards [hc] with x hx
    have hev := hx.eventually (gt_mem_nhds (show c < L by linarith))
    obtain ⟨n, hn1, hn2⟩ := (hev.and (eventually_ge_atTop 1)).exists
    refine mem_iUnion.2 ⟨n, n, hn2, le_rfl, ?_⟩
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn2
    rwa [div_lt_iff₀ hnpos, mul_comm] at hn1
  have hGlim : Tendsto (fun N => μ.real (G N)) atTop (𝓝 1) := by
    have hUm : MeasurableSet (⋃ N, G N) := MeasurableSet.iUnion fun N => (hGo N).measurableSet
    have hU1 : μ (⋃ N, G N) = 1 := (prob_compl_eq_zero_iff hUm).1 (ae_iff.1 hGU)
    have := tendsto_measure_iUnion_atTop (μ := μ) hGmono
    rw [hU1] at this
    have := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp this
    exact this.congr fun N => by simp [measureReal_def]
  set η := δ / (2 * (|c| + δ) + 1) with hηdef
  have hη : 0 < η := by positivity
  have h2η : 2 * η * (|c| + δ) ≤ δ := by
    have hpos : 0 < 2 * (|c| + δ) + 1 := by positivity
    have hX : η * (2 * (|c| + δ) + 1) = δ := by rw [hηdef]; exact div_mul_cancel₀ _ hpos.ne'
    nlinarith [hX, hη]
  have hη1 : 0 ≤ 1 - η := by
    have : η ≤ 1 / 2 := by
      rw [hηdef, div_le_iff₀ (by positivity)]; nlinarith [abs_nonneg c]
    linarith
  obtain ⟨N, hN⟩ := (hGlim.eventually (lt_mem_nhds (show 1 - η < 1 by linarith))).exists
  -- a closed `F ⊆ G N` of large measure and a continuous minorant of `1_{G N}`
  have hr : ENNReal.ofReal (1 - η) < μ (G N) := by
    rw [ENNReal.ofReal_lt_iff_lt_toReal hη1 (measure_ne_top _ _)]
    exact hN
  obtain ⟨F, hFG, hFc, hFμ⟩ := (hGo N).exists_lt_isClosed hr
  obtain ⟨φ, hφ0, hφ1, hφI⟩ := exists_continuous_zero_one_of_isClosed (hGo N).isClosed_compl hFc
    (disjoint_compl_left.mono_right hFG)
  have hφle : ∀ y, φ y ≤ (G N).indicator 1 y := fun y => by
    by_cases hy : y ∈ G N
    · simp only [indicator_of_mem hy, Pi.one_apply]; exact (hφI y).2
    · simp only [indicator_of_notMem hy]; exact (hφ0 hy).le
  have hφint : 1 - η < ∫ y, φ y ∂μ := by
    have h1 : 1 - η < μ.real F := by
      rw [measureReal_def]
      exact (ENNReal.ofReal_lt_iff_lt_toReal hη1 (measure_ne_top _ _)).1 hFμ
    calc 1 - η < μ.real F := h1
      _ = ∫ y, F.indicator 1 y ∂μ := (integral_indicator_one hFc.measurableSet).symm
      _ ≤ ∫ y, φ y ∂μ := by
        refine integral_mono ((integrable_const (1 : ℝ)).indicator hFc.measurableSet)
          (φ.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
          fun y => ?_
        by_cases hy : y ∈ F
        · simp only [indicator_of_mem hy, Pi.one_apply]; exact (hφ1 hy).ge
        · simp only [indicator_of_notMem hy]; exact (hφI y).1
  obtain ⟨N2, hN2⟩ := eventually_atTop.1
    (Metric.tendstoUniformly_iff.1 (tendstoUniformly_of_uniquelyErgodic hT hμ φ) η hη)
  obtain ⟨N3, hN3⟩ : ∃ N3 : ℕ, (|c| + δ) * N / δ ≤ N3 := exists_nat_ge _
  refine ⟨max (max N1 N2) (max N3 1), fun n hn x => ?_⟩
  have hnN1 : N1 ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hnN2 : N2 ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hnN3 : N3 ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn1 : 1 ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have h1 := hN1 n hnN1 x
  rw [Real.dist_eq, abs_lt] at h1
  have h2 := hN2 n hnN2 x
  rw [Real.dist_eq, abs_lt] at h2
  have hAφ : 1 - 2 * η < birkhoffAverage ℝ T φ n x := by linarith
  have hcov := Kingman.cover hgsub hgle hL N (G := G N)
    (fun y ⟨k, hk1, hk2, hk3⟩ => ⟨k, hk1, hk2, hk3.le⟩) n x
  have hsubN := Kingman.birkhoffSum_indicator_sub (T := T) (G N) n N x
  have hφS : birkhoffSum T φ n x ≤ birkhoffSum T ((G N).indicator 1) n x :=
    Finset.sum_le_sum fun k _ => hφle _
  have hSφ : birkhoffSum T φ n x = n * birkhoffAverage ℝ T φ n x := by
    rw [Birkhoff.birkhoffAverage_eq_div]; field_simp
  -- `g_n(x) ≤ L n (1 - 2η) - L N`
  have hg1 : g n x ≤ L * (n * (1 - 2 * η)) - L * N := by
    have e1 := mul_le_mul_of_nonpos_left hsubN hL
    have e2 := mul_le_mul_of_nonpos_left (show birkhoffSum T φ n x - N ≤
      birkhoffSum T ((G N).indicator 1) n x - N by linarith) hL
    have e3 := mul_le_mul_of_nonpos_left (show (n : ℝ) * (1 - 2 * η) ≤
      n * birkhoffAverage ℝ T φ n x by nlinarith) hL
    rw [hSφ] at e2
    nlinarith
  have hLabs : -L ≤ |c| + δ := by
    have := neg_abs_le c
    simp only [hLdef]; linarith
  have hN3' : (|c| + δ) * N ≤ δ * n := by
    have := (div_le_iff₀ hδpos).1 (hN3.trans (by exact_mod_cast hnN3 : (N3 : ℝ) ≤ n))
    linarith
  have hg2 : g n x / n ≤ L + 2 * δ := by
    rw [div_le_iff₀ hnpos]
    have e4 : -L * (2 * η) ≤ δ := by nlinarith
    have e5 : -L * N ≤ δ * n := by
      have : -L * N ≤ (|c| + δ) * N := mul_le_mul_of_nonneg_right hLabs (Nat.cast_nonneg _)
      linarith
    nlinarith
  rw [hdecomp n x hn1, hlam]
  simp only [hLdef] at hg2
  linarith

end DF
