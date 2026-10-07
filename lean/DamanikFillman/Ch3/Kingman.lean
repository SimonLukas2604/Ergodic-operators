/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §3.4 Kingman's subadditive ergodic theorem (book pp. 243–247)

Main results:
* `DF.fekete`, `DF.fekete_atBot` — **Lemma 3.4.1** (Fekete): for a subadditive real sequence,
  `a_n / n → inf_{n ≥ 1} a_n / n`; the first lemma treats a finite infimum, the second the
  case `inf = -∞` (Exercise 3.4.1), where `a_n / n → -∞`.
* `DF.Kingman.cover` — the deterministic covering estimate used in the proof (the
  decomposition of `[0, n)` into good blocks and singletons), proved by strong induction;
* `DF.Kingman.core` — Kingman's theorem for nonpositive subadditive sequences;
* `DF.kingman` — **Theorem 3.4.2** (Kingman), in the setting of the book's proof: `T` ergodic,
  `f_n` measurable, subadditive (3.4.2) and `|f_n| ≤ C n`. Then `f_n(ω)/n → f` for a.e. `ω`,
  where `f = inf_{n ≥ 1} E(f_n)/n` (3.4.3)/(3.4.4), and also `E(f_n)/n → f`.

Deviations: as in the book's proof we assume the uniform bound `|f_n| ≤ C n` (the general
integrable case is the book's Exercise 3.4.2 and is not formalized). The sequence is indexed by
`ℕ`; the value `f 0` is irrelevant and the hypotheses are only imposed for indices `≥ 1`.
Instead of the liminf we work with the sets `Lo g t` ("`liminf g_n/n < t`"), which are
backward invariant; ergodicity then makes them null or conull.
-/
import DamanikFillman.Ch3.Birkhoff

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Set Function Topology

namespace DF

/-! ### Lemma 3.4.1 (Fekete) -/

lemma fekete_aux {a : ℕ → ℝ} (ha : ∀ n m, 1 ≤ n → 1 ≤ m → a (n + m) ≤ a n + a m) :
    Subadditive (fun n => if n = 0 then 0 else a n) := by
  intro m n
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  dsimp only
  rw [if_neg (show m + n ≠ 0 by omega), if_neg (show m ≠ 0 by omega),
    if_neg (show n ≠ 0 by omega)]
  exact ha m n hm hn

/-- **Lemma 3.4.1** (Fekete), case of a finite infimum: if `a_{n+m} ≤ a_n + a_m` for `n, m ≥ 1`
and `inf_{n ≥ 1} a_n / n > -∞`, then `a_n / n → inf_{n ≥ 1} a_n / n`. -/
theorem fekete {a : ℕ → ℝ} (ha : ∀ n m, 1 ≤ n → 1 ≤ m → a (n + m) ≤ a n + a m)
    (hbdd : BddBelow (range fun n : ℕ => a (n + 1) / (n + 1))) :
    Tendsto (fun n => a n / n) atTop (𝓝 (⨅ n : ℕ, a (n + 1) / (n + 1))) := by
  set u : ℕ → ℝ := fun n => if n = 0 then 0 else a n with hu_def
  have hu := fekete_aux ha
  have hbu : BddBelow (range fun n => u n / n) := by
    obtain ⟨B, hB⟩ := hbdd
    refine ⟨min B 0, ?_⟩
    rintro _ ⟨n, rfl⟩
    rcases n with _ | n
    · simp [u]
    · have := hB ⟨n, rfl⟩
      simp only [u, Nat.succ_ne_zero, ite_false]
      push_cast
      exact (min_le_left _ _).trans this
  have ht := hu.tendsto_lim hbu
  have heq : (fun n => u n / n) =ᶠ[atTop] (fun n => a n / n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    show (if n = 0 then 0 else a n) / (n : ℝ) = a n / n
    rw [if_neg (show n ≠ 0 by omega)]
  have ht' := ht.congr' heq
  have hlim : hu.lim = ⨅ n : ℕ, a (n + 1) / (n + 1) := by
    apply le_antisymm
    · apply le_ciInf; intro n
      have := hu.lim_le_div hbu (n := n + 1) (by omega)
      simpa [u] using this
    · apply ge_of_tendsto ht'
      filter_upwards [eventually_ge_atTop 1] with n hn
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have := ciInf_le hbdd m
      push_cast
      exact this
  rw [← hlim]; exact ht'

/-- **Lemma 3.4.1** (Fekete), case `inf_{n ≥ 1} a_n / n = -∞` (Exercise 3.4.1): then
`a_n / n → -∞`. -/
theorem fekete_atBot {a : ℕ → ℝ} (ha : ∀ n m, 1 ≤ n → 1 ≤ m → a (n + m) ≤ a n + a m)
    (hnb : ¬ BddBelow (range fun n : ℕ => a (n + 1) / (n + 1))) :
    Tendsto (fun n => a n / n) atTop atBot := by
  set u : ℕ → ℝ := fun n => if n = 0 then 0 else a n
  have hu := fekete_aux ha
  rw [tendsto_atBot]; intro L
  rw [not_bddBelow_iff] at hnb
  obtain ⟨_, ⟨n, rfl⟩, hn⟩ := hnb L
  have := hu.eventually_div_lt_of_div_lt (n := n + 1) (by omega) (L := L)
    (by simpa [u] using hn)
  filter_upwards [this, eventually_ge_atTop 1] with p hp hp1
  rw [if_neg (show p ≠ 0 by omega)] at hp
  exact hp.le

/-! ### Kingman's theorem -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}

namespace Kingman

lemma birkhoffSum_indicator_nonneg (G : Set Ω) (n : ℕ) (x : Ω) :
    0 ≤ birkhoffSum T (G.indicator (1 : Ω → ℝ)) n x :=
  Finset.sum_nonneg fun k _ => indicator_nonneg (fun _ _ => zero_le_one) _

lemma birkhoffSum_indicator_le (G : Set Ω) (n : ℕ) (x : Ω) :
    birkhoffSum T (G.indicator (1 : Ω → ℝ)) n x ≤ n := by
  calc birkhoffSum T (G.indicator (1 : Ω → ℝ)) n x ≤ ∑ k ∈ Finset.range n, (1 : ℝ) := by
        refine Finset.sum_le_sum fun k _ => ?_
        by_cases h : T^[k] x ∈ G <;> simp [h]
    _ = n := by simp

lemma birkhoffSum_indicator_sub (G : Set Ω) (n N : ℕ) (x : Ω) :
    birkhoffSum T (G.indicator (1 : Ω → ℝ)) n x - N ≤
      birkhoffSum T (G.indicator (1 : Ω → ℝ)) (n - N) x := by
  by_cases h : N ≤ n
  · have hn : n = (n - N) + N := by omega
    have := birkhoffSum_indicator_le (T := T) G N (T^[n - N] x)
    have h2 := birkhoffSum_add_right_apply T (G.indicator (1 : Ω → ℝ)) (n - N) N x
    rw [← hn] at h2
    linarith
  · have := birkhoffSum_indicator_le (T := T) G n x
    have := birkhoffSum_indicator_nonneg (T := T) G (n - N) x
    have : (n : ℝ) ≤ N := by exact_mod_cast (by omega : n ≤ N)
    linarith

/-- The covering estimate from the proof of Theorem 3.4.2. If `g` is subadditive and
nonpositive, `L ≤ 0`, and every point of `G` starts a block of length `k ∈ [1, N]` with
`g_k ≤ k L`, then `g_n(x) ≤ L · #{0 ≤ j < n - N : T^j x ∈ G}`. -/
theorem cover {g : ℕ → Ω → ℝ} (hsub : ∀ n m x, g (n + m) x ≤ g n x + g m (T^[n] x))
    (hle : ∀ n x, g n x ≤ 0) {L : ℝ} (hL : L ≤ 0) (N : ℕ) {G : Set Ω}
    (hG : ∀ y ∈ G, ∃ k : ℕ, 1 ≤ k ∧ k ≤ N ∧ g k y ≤ k * L) (n : ℕ) (x : Ω) :
    g n x ≤ L * birkhoffSum T (G.indicator (1 : Ω → ℝ)) (n - N) x := by
  induction n using Nat.strong_induction_on generalizing x with
  | _ n ih =>
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simpa [birkhoffSum] using hle 0 x
  by_cases hx : x ∈ G
  · obtain ⟨k, hk1, hkN, hkx⟩ := hG x hx
    by_cases hkn : k ≤ n
    · have h1 := hsub k (n - k) x
      rw [Nat.add_sub_cancel' hkn] at h1
      have h2 := ih (n - k) (by omega) (T^[k] x)
      have h3 : birkhoffSum T (G.indicator (1 : Ω → ℝ)) (n - N) x ≤
          k + birkhoffSum T (G.indicator (1 : Ω → ℝ)) (n - k - N) (T^[k] x) := by
        by_cases hnk : k ≤ n - N
        · have he : n - N = k + (n - k - N) := by omega
          rw [he, birkhoffSum_add_right_apply]
          have := birkhoffSum_indicator_le (T := T) G k x
          linarith
        · have := birkhoffSum_indicator_le (T := T) G (n - N) x
          have := birkhoffSum_indicator_nonneg (T := T) G (n - k - N) (T^[k] x)
          have : ((n - N : ℕ) : ℝ) ≤ k := by exact_mod_cast (by omega : n - N ≤ k)
          linarith
      have h4 := mul_le_mul_of_nonpos_left h3 hL
      nlinarith
    · have : n - N = 0 := by omega
      rw [this]; simpa [birkhoffSum] using hle n x
  · have h1 := hsub 1 (n - 1) x
    rw [Nat.add_sub_cancel' hn] at h1
    have h2 := ih (n - 1) (by omega) (T x)
    have h3 : birkhoffSum T (G.indicator (1 : Ω → ℝ)) (n - N) x =
        birkhoffSum T (G.indicator (1 : Ω → ℝ)) (n - 1 - N) (T x) := by
      rcases Nat.eq_zero_or_pos (n - N) with h | h
      · rw [h, (by omega : n - 1 - N = 0)]; simp [birkhoffSum]
      · have he : n - N = (n - 1 - N) + 1 := by omega
        rw [he, birkhoffSum_succ_apply', indicator_of_notMem hx, zero_add]
    have := hle 1 x
    simp only [iterate_one] at h1
    rw [h3]; linarith

/-- `Lo g t` is the set of points where `liminf g_n / n < t` (formulated without liminf). -/
def Lo (g : ℕ → Ω → ℝ) (t : ℝ) : Set Ω :=
  {x | ∃ q : ℚ, (q : ℝ) < t ∧ ∃ᶠ n : ℕ in atTop, g n x < (q : ℝ) * n}

lemma measurableSet_Lo {g : ℕ → Ω → ℝ} (hg : ∀ n, Measurable (g n)) (t : ℝ) :
    MeasurableSet (Lo g t) := by
  have : Lo g t = ⋃ q ∈ {q : ℚ | (q : ℝ) < t},
      {x | ∃ᶠ n : ℕ in atTop, g n x < (q : ℝ) * n} := by
    ext x; simp [Lo]
  rw [this]
  refine MeasurableSet.biUnion (to_countable _) fun q _ =>
    Birkhoff.measurableSet_frequently fun n => ?_
  exact measurableSet_lt (hg n) measurable_const

lemma Lo_mono {g : ℕ → Ω → ℝ} {s t : ℝ} (hst : s ≤ t) : Lo g s ⊆ Lo g t :=
  fun _ ⟨q, hq, hfr⟩ => ⟨q, hq.trans_le hst, hfr⟩

lemma preimage_Lo_subset {g : ℕ → Ω → ℝ} (hsub : ∀ n m x, g (n + m) x ≤ g n x + g m (T^[n] x))
    (hle : ∀ n x, g n x ≤ 0) (t : ℝ) : T ⁻¹' Lo g t ⊆ Lo g t := by
  rintro x ⟨q, hq, hfr⟩
  obtain ⟨q', hq'1, hq'2⟩ := exists_rat_btwn hq
  refine ⟨q', hq'2, ?_⟩
  have hev := Birkhoff.eventually_mul_ge (b' := q') (b'' := q) (by exact_mod_cast hq'1) (-q')
  have : ∃ᶠ n in atTop, g (n + 1) x < (q' : ℝ) * ((n + 1 : ℕ) : ℝ) := by
    refine (hfr.and_eventually hev).mono fun n ⟨h1, h2⟩ => ?_
    have h3 := hsub 1 n x
    have h4 := hle 1 x
    rw [add_comm 1 n] at h3
    simp only [iterate_one] at h3
    push_cast
    nlinarith
  exact (tendsto_add_atTop_nat 1).frequently this

lemma mem_Lo_one {g : ℕ → Ω → ℝ} (hle : ∀ n x, g n x ≤ 0) (x : Ω) : x ∈ Lo g 1 := by
  refine ⟨1 / 2, by norm_num, ?_⟩
  refine (eventually_ge_atTop 1).frequently.mono fun n hn => ?_
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have := hle n x
  push_cast
  linarith

lemma notMem_Lo {g : ℕ → Ω → ℝ} {C : ℝ} (hlow : ∀ n x, -C * n ≤ g n x) {t : ℝ} (ht : t ≤ -C)
    (x : Ω) : x ∉ Lo g t := by
  rintro ⟨q, hq, hfr⟩
  obtain ⟨n, hn⟩ := hfr.exists
  have := hlow n x
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- Kingman's theorem for nonpositive subadditive sequences (the core of the proof of
Theorem 3.4.2): `g_n / n` converges a.e. to a constant. -/
theorem core [IsProbabilityMeasure μ] (hT : Ergodic T μ) {g : ℕ → Ω → ℝ}
    (hgm : ∀ n, Measurable (g n)) (hsub : ∀ n m x, g (n + m) x ≤ g n x + g m (T^[n] x))
    (hle : ∀ n x, g n x ≤ 0) {C : ℝ} (hlow : ∀ n x, -C * n ≤ g n x) :
    ∃ c, ∀ᵐ x ∂μ, Tendsto (fun n => g n x / n) atTop (𝓝 c) := by
  have hmp := hT.toMeasurePreserving
  set S := {t : ℝ | ∀ᵐ x ∂μ, x ∈ Lo g t}
  have hdich : ∀ t, (∀ᵐ x ∂μ, x ∈ Lo g t) ∨ (∀ᵐ x ∂μ, x ∉ Lo g t) := by
    intro t
    have hm := measurableSet_Lo hgm t
    have hpre : T ⁻¹' Lo g t =ᵐ[μ] Lo g t :=
      ae_eq_of_subset_of_measure_ge (preimage_Lo_subset hsub hle t)
        (by rw [hmp.measure_preimage hm.nullMeasurableSet])
        (hm.preimage hT.measurable).nullMeasurableSet (measure_ne_top _ _)
    exact hT.toPreErgodic.ae_mem_or_ae_notMem hm.nullMeasurableSet hpre
  have hne : (ae μ).NeBot := ae_neBot.2 (IsProbabilityMeasure.ne_zero μ)
  have h1S : (1 : ℝ) ∈ S := show ∀ᵐ x ∂μ, x ∈ Lo g 1 from Eventually.of_forall (mem_Lo_one hle)
  have hbdd : BddBelow S := by
    refine ⟨-C, fun t ht => ?_⟩
    by_contra h
    push Not at h
    obtain ⟨x, hx⟩ := (show ∀ᵐ x ∂μ, x ∈ Lo g t from ht).exists
    exact notMem_Lo hlow h.le x hx
  set c := sInf S
  have hgt : ∀ t, c < t → ∀ᵐ x ∂μ, x ∈ Lo g t := fun t ht => by
    obtain ⟨s, hs, hst⟩ := exists_lt_of_csInf_lt ⟨1, h1S⟩ ht
    filter_upwards [show ∀ᵐ x ∂μ, x ∈ Lo g s from hs] with x hx using Lo_mono hst.le hx
  have hlt : ∀ t, t < c → ∀ᵐ x ∂μ, x ∉ Lo g t := fun t ht => by
    rcases hdich t with h | h
    · exact absurd (csInf_le hbdd h) (not_le.2 ht)
    · exact h
  -- the a.e. lower bound
  have hlower : ∀ᵐ x ∂μ, ∀ a : ℚ, (a : ℝ) < c → ∀ᶠ n : ℕ in atTop, (a : ℝ) * n ≤ g n x := by
    rw [ae_all_iff]; intro a
    by_cases ha : (a : ℝ) < c
    · obtain ⟨t, ht1, ht2⟩ := exists_between ha
      filter_upwards [hlt t ht2] with x hx _
      have : ¬ ∃ᶠ n : ℕ in atTop, g n x < a * n := fun h => hx ⟨a, ht1, h⟩
      rw [not_frequently] at this
      exact this.mono fun n hn => not_lt.1 hn
    · exact Eventually.of_forall fun x h => absurd h ha
  -- the good sets
  set G : ℕ → ℚ → Set Ω := fun N ε => {y | ∃ k : ℕ, 1 ≤ k ∧ k ≤ N ∧ g k y ≤ k * (c + ε)}
  have hGm : ∀ N ε, MeasurableSet (G N ε) := by
    intro N ε
    have : G N ε = ⋃ k : ℕ, {y | 1 ≤ k ∧ k ≤ N ∧ g k y ≤ k * (c + ε)} := by
      ext y; simp [G]
    rw [this]
    refine MeasurableSet.iUnion fun k => ?_
    by_cases hk : 1 ≤ k ∧ k ≤ N
    · simp only [hk.1, hk.2, true_and]
      exact measurableSet_le (hgm k) measurable_const
    · have : {y | 1 ≤ k ∧ k ≤ N ∧ g k y ≤ k * (c + ε)} = ∅ := by
        ext y; simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun h => hk ⟨h.1, h.2.1⟩
      rw [this]; exact MeasurableSet.empty
  have hBirk : ∀ᵐ x ∂μ, ∀ N : ℕ, ∀ ε : ℚ, Tendsto
      (fun n : ℕ => birkhoffSum T ((G N ε).indicator (1 : Ω → ℝ)) n x / n) atTop
      (𝓝 (μ.real (G N ε))) := by
    rw [ae_all_iff]; intro N; rw [ae_all_iff]; intro ε
    have hi : Integrable ((G N ε).indicator (1 : Ω → ℝ)) μ :=
      (integrable_const (1 : ℝ)).indicator (hGm N ε)
    have := birkhoff_ergodic_tendsto hT hi
    filter_upwards [this] with x hx
    simp only [Birkhoff.birkhoffAverage_eq_div] at hx
    rwa [integral_indicator_one (hGm N ε)] at hx
  have hmeasG : ∀ ε : ℚ, 0 < ε → Tendsto (fun N => μ.real (G N ε)) atTop (𝓝 1) := by
    intro ε hε
    have hmono : Monotone fun N => G N ε := fun N N' hNN' y ⟨k, hk1, hk2, hk3⟩ =>
      ⟨k, hk1, hk2.trans hNN', hk3⟩
    have hU : ∀ᵐ x ∂μ, x ∈ ⋃ N, G N ε := by
      filter_upwards [hgt (c + ε) (by linarith [show (0 : ℝ) < ε by exact_mod_cast hε])]
        with x hx
      obtain ⟨q, hq, hfr⟩ := hx
      obtain ⟨n, hn1, hn2⟩ := (hfr.and_eventually (eventually_ge_atTop 1)).exists
      refine mem_iUnion.2 ⟨n, n, hn2, le_rfl, ?_⟩
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    have hUm : MeasurableSet (⋃ N, G N ε) := MeasurableSet.iUnion fun N => hGm N ε
    have hU1 : μ (⋃ N, G N ε) = 1 := (prob_compl_eq_zero_iff hUm).1 (ae_iff.1 hU)
    have := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [hU1] at this
    have := (ENNReal.tendsto_toReal ENNReal.one_ne_top).comp this
    exact this.congr fun N => by simp [measureReal_def]
  have hupper : ∀ᵐ x ∂μ, ∀ b : ℚ, c < b → ∀ᶠ n : ℕ in atTop, g n x / n < b := by
    filter_upwards [hBirk] with x hx b hb
    have hpos : 0 < min ((b - c) / 4) 1 := lt_min (by linarith) one_pos
    obtain ⟨ε, hε1, hε2⟩ := exists_rat_btwn hpos
    have hεb : (ε : ℝ) < (b - c) / 4 := hε2.trans_le (min_le_left _ _)
    have hε1' : (ε : ℝ) < 1 := hε2.trans_le (min_le_right _ _)
    have hε0 : (0 : ℚ) < ε := by exact_mod_cast hε1
    by_cases hcase : 0 < c + ε
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have : g n x / n ≤ 0 := div_nonpos_of_nonpos_of_nonneg (hle n x) hnpos.le
      linarith
    · push Not at hcase
      set L := c + (ε : ℝ)
      have hLabs : |L| ≤ |c| + 1 := by
        calc |L| ≤ |c| + |(ε : ℝ)| := abs_add_le _ _
          _ ≤ |c| + 1 := by rw [abs_of_pos hε1]; linarith
      have hev := (hmeasG ε hε0).eventually (lt_mem_nhds (show 1 - ε / (|c| + 1) < (1 : ℝ) by
        have : 0 < (ε : ℝ) / (|c| + 1) := by positivity
        linarith))
      obtain ⟨N, hN⟩ := hev.exists
      have hμle : μ.real (G N ε) ≤ 1 := measureReal_le_one
      have hLμ : L * μ.real (G N ε) ≤ L + ε := by
        have h1 : 0 ≤ 1 - μ.real (G N ε) := by linarith
        have h2 : (1 - μ.real (G N ε)) * (|c| + 1) ≤ ε := by
          have hc1 : 0 < |c| + 1 := by positivity
          have := (lt_div_iff₀ hc1).1 (by linarith : 1 - μ.real (G N ε) < ε / (|c| + 1))
          linarith
        have h3 : -L ≤ |c| + 1 := (neg_le_abs L).trans hLabs
        nlinarith
      have hcov : ∀ n, g n x ≤ L * birkhoffSum T ((G N ε).indicator (1 : Ω → ℝ)) (n - N) x :=
        fun n => cover hsub hle hcase N (fun y hy => hy) n x
      have hlim : Tendsto (fun n : ℕ => L * (birkhoffSum T ((G N ε).indicator (1 : Ω → ℝ)) n x
          / n) - L * N / n) atTop (𝓝 (L * μ.real (G N ε) - 0)) :=
        ((hx N ε).const_mul L).sub (tendsto_const_div_atTop_nhds_zero_nat _)
      rw [sub_zero] at hlim
      have hev2 := hlim.eventually (gt_mem_nhds (show L * μ.real (G N ε) < b by
        simp only [L] at hLμ ⊢; linarith))
      filter_upwards [hev2, eventually_ge_atTop 1] with n hn hn1
      have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
      have h1 := hcov n
      have h2 := birkhoffSum_indicator_sub (T := T) (G N ε) n N x
      have h3 := mul_le_mul_of_nonpos_left h2 hcase
      have h4 : g n x / n ≤ L * (birkhoffSum T ((G N ε).indicator (1 : Ω → ℝ)) n x / n)
          - L * N / n := by
        rw [div_le_iff₀ hnpos, sub_mul, div_mul_cancel₀ _ hnpos.ne', mul_assoc,
          div_mul_cancel₀ _ hnpos.ne']
        linarith
      linarith
  refine ⟨c, ?_⟩
  filter_upwards [hlower, hupper] with x hxl hxu
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨a', ha'1, ha'2⟩ := exists_rat_btwn ha
    filter_upwards [hxl a' ha'2, eventually_ge_atTop 1] with n hn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [lt_div_iff₀ hnpos]
    nlinarith
  · obtain ⟨b', hb'1, hb'2⟩ := exists_rat_btwn hb
    filter_upwards [hxu b' hb'1] with n hn
    linarith

lemma integral_comp_mp {S : Ω → Ω} (hS : MeasurePreserving S μ μ) {h : Ω → ℝ}
    (hh : AEStronglyMeasurable h μ) : ∫ x, h (S x) ∂μ = ∫ x, h x ∂μ := by
  rw [← integral_map hS.measurable.aemeasurable (by rwa [hS.map_eq]), hS.map_eq]

end Kingman

open Kingman

/-- **Kingman's subadditive ergodic theorem**, Theorem 3.4.2, under the uniform bound
`|f_n| ≤ C n` used in the book's proof. If `T` is ergodic and the measurable `f_n` satisfy
`f_{n+m}(ω) ≤ f_n(ω) + f_m(Tⁿω)` (3.4.2), then for a.e. `ω`, `f_n(ω)/n` converges to the constant
`f = inf_{n ≥ 1} E(f_n)/n` (3.4.3), (3.4.4); moreover `E(f_n)/n → f` (3.4.10). -/
theorem kingman [IsProbabilityMeasure μ] (hT : Ergodic T μ) {f : ℕ → Ω → ℝ}
    (hfm : ∀ n, Measurable (f n))
    (hsub : ∀ n m x, 1 ≤ n → 1 ≤ m → f (n + m) x ≤ f n x + f m (T^[n] x))
    {C : ℝ} (hC : ∀ n x, 1 ≤ n → |f n x| ≤ C * n) :
    (∀ᵐ x ∂μ, Tendsto (fun n => f n x / n) atTop
        (𝓝 (⨅ n : ℕ, (∫ y, f (n + 1) y ∂μ) / (n + 1)))) ∧
      Tendsto (fun n => (∫ y, f n y ∂μ) / n) atTop
        (𝓝 (⨅ n : ℕ, (∫ y, f (n + 1) y ∂μ) / (n + 1))) := by
  have hmp := hT.toMeasurePreserving
  -- normalise `f 0 = 0`
  set f0 : ℕ → Ω → ℝ := fun n x => if n = 0 then 0 else f n x with hf0
  have hf0m : ∀ n, Measurable (f0 n) := by
    intro n; by_cases hn : n = 0
    · simp only [f0, hn, if_true]; exact measurable_const
    · simp only [f0, hn, ite_false]; exact hfm n
  have hf0sub : ∀ n m x, f0 (n + m) x ≤ f0 n x + f0 m (T^[n] x) := by
    intro n m x
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [f0]
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [f0]
    simp only [f0]
    rw [if_neg (show n + m ≠ 0 by omega), if_neg (show n ≠ 0 by omega),
      if_neg (show m ≠ 0 by omega)]
    exact hsub n m x hn hm
  have hf0C : ∀ n x, |f0 n x| ≤ C * n := by
    intro n x; by_cases hn : n = 0
    · simp [f0, hn]
    · simp only [f0, hn, ite_false]; exact hC n x (by omega)
  have hf1C : ∀ x, |f 1 x| ≤ C := fun x => by simpa using hC 1 x le_rfl
  have hf1i : Integrable (f 1) μ :=
    (integrable_const C).mono' (hfm 1).aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hf1C x)
  -- the reduction to nonpositive sequences
  set g : ℕ → Ω → ℝ := fun n x => f0 n x - birkhoffSum T (f 1) n x with hg
  have hS_le : ∀ n x, f0 n x ≤ birkhoffSum T (f 1) n x := by
    intro n
    induction n with
    | zero => intro x; simp [f0]
    | succ n ih =>
      intro x
      have h1 := hf0sub n 1 x
      rw [birkhoffSum_succ_apply]
      have : f0 1 (T^[n] x) = f 1 (T^[n] x) := by simp [f0]
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
  have hgm : ∀ n, Measurable (g n) := fun n =>
    (hf0m n).sub (Birkhoff.measurable_birkhoffSum hT.measurable (hfm 1) n)
  obtain ⟨c, hc⟩ := core hT hgm hgsub hgle hglow
  have hB := birkhoff_ergodic_tendsto hT hf1i
  -- a.e. convergence of `f n / n`
  have hconv : ∀ᵐ x ∂μ, Tendsto (fun n => f n x / n) atTop (𝓝 (c + ∫ y, f 1 y ∂μ)) := by
    filter_upwards [hc, hB] with x h1 h2
    simp only [Birkhoff.birkhoffAverage_eq_div] at h2
    refine (h1.add h2).congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : f0 n x = f n x := by simp only [f0]; rw [if_neg (show n ≠ 0 by omega)]
    simp only [g]; rw [this]; ring
  -- convergence of the integrals
  have hfi : ∀ n, Integrable (f0 n) μ := fun n =>
    (integrable_const (C * n)).mono' (hf0m n).aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hf0C n x)
  have hint : Tendsto (fun n => (∫ y, f n y ∂μ) / n) atTop (𝓝 (c + ∫ y, f 1 y ∂μ)) := by
    have hdom := tendsto_integral_filter_of_dominated_convergence (μ := μ) (l := atTop)
      (F := fun n x => f n x / n) (f := fun _ => c + ∫ y, f 1 y ∂μ) (fun _ => C)
      (Eventually.of_forall fun n => ((hfm n).div_const _).aestronglyMeasurable)
      (by
        filter_upwards [eventually_ge_atTop 1] with n hn
        refine Eventually.of_forall fun x => ?_
        have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
        rw [Real.norm_eq_abs, abs_div, abs_of_pos hnpos, div_le_iff₀ hnpos]
        exact hC n x hn)
      (integrable_const C) hconv
    rw [integral_const, probReal_univ, one_smul] at hdom
    refine hdom.congr fun n => ?_
    exact integral_div _ _
  -- Fekete for the integrals
  have hf0eq : ∀ k, 1 ≤ k → f0 k = f k := fun k hk => by
    funext x; simp only [f0]; rw [if_neg (show k ≠ 0 by omega)]
  have hfek_sub : ∀ n m, 1 ≤ n → 1 ≤ m →
      ∫ y, f (n + m) y ∂μ ≤ (∫ y, f n y ∂μ) + ∫ y, f m y ∂μ := by
    intro n m hn hm
    rw [← hf0eq _ (by omega), ← hf0eq n hn, ← hf0eq m hm]
    have hcomp : ∫ y, f0 m (T^[n] y) ∂μ = ∫ y, f0 m y ∂μ :=
      integral_comp_mp (hmp.iterate n) (hf0m m).aestronglyMeasurable
    have hcompi : Integrable (fun y => f0 m (T^[n] y)) μ :=
      (hmp.iterate n).integrable_comp_of_integrable (hfi m)
    calc ∫ y, f0 (n + m) y ∂μ ≤ ∫ y, (f0 n y + f0 m (T^[n] y)) ∂μ :=
          integral_mono (hfi _) ((hfi n).add hcompi) fun y => hf0sub n m y
      _ = (∫ y, f0 n y ∂μ) + ∫ y, f0 m (T^[n] y) ∂μ := integral_add (hfi n) hcompi
      _ = (∫ y, f0 n y ∂μ) + ∫ y, f0 m y ∂μ := by rw [hcomp]
  have hfek_bdd : BddBelow (range fun n : ℕ => (∫ y, f (n + 1) y ∂μ) / (n + 1)) := by
    refine ⟨-C, ?_⟩
    rintro _ ⟨n, rfl⟩
    have hnpos : (0 : ℝ) < n + 1 := by positivity
    rw [le_div_iff₀ hnpos]
    have : ∫ y, (-(C * ((n + 1 : ℕ) : ℝ))) ∂μ ≤ ∫ y, f (n + 1) y ∂μ := by
      refine integral_mono (integrable_const _) (by
        rw [← hf0eq (n + 1) (by omega)]; exact hfi (n + 1)) fun y => ?_
      exact (abs_le.1 (hC (n + 1) y (by omega))).1
    rw [integral_const, probReal_univ, one_smul] at this
    push_cast at this
    linarith
  have hfek := fekete (a := fun n => ∫ y, f n y ∂μ) hfek_sub hfek_bdd
  have heq : c + ∫ y, f 1 y ∂μ = ⨅ n : ℕ, (∫ y, f (n + 1) y ∂μ) / (n + 1) :=
    tendsto_nhds_unique hint hfek
  rw [← heq]
  exact ⟨hconv, hint⟩

end DF
