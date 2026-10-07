/-
Formalization of Damanik–Fillman, *One-Dimensional Ergodic Schrödinger Operators I*, Chapter 1.

# Decomposition of measures against Hausdorff measures  (book §1.8.1, pp. 61–65, and
Theorem 1.8.14, p. 71)

We use Mathlib's Hausdorff measure `μH[α]` (Definition 1.8.1; Mathlib builds it from covers by
arbitrary sets, which on `ℝ` is equivalent to covers by intervals).

* `DF.upperDeriv μ α E` — the upper `α`-derivative (1.8.4), defined with closed balls
  `[E-ε, E+ε]` (the book uses open intervals; this changes `D^α_μ` by at most a factor `2^α` and
  does not change the sets `T^α_f`, `T^α_∞`);
* `DF.Tinf`, `DF.Tfin` — the sets `T_∞`, `T_f`;
* **Theorem 1.8.2** (Rogers–Taylor): `DF.hausdorffMeasure_Tinf` (`h^α(T_∞) = 0`, via Mathlib's
  Vitali covering lemma, Lemma 1.8.3) and `DF.measure_inter_Tfin_eq_zero`
  (`μ(S ∩ T_f) = 0` whenever `h^α(S) = 0`);
* `DF.exists_alpha_decomposition` — the decomposition (1.8.13) `μ = μ_{αc} + μ_{αs}` with
  `μ_{αc} ≪ h^α` and `μ_{αs}` carried by an `h^α`-null set;
* `DF.UalphaH` — uniform `α`-Hölder continuity (Definition 1.8.9);
* **Theorem 1.8.14**: `DF.exists_UalphaH_approx`;
* the spectral subspaces `H_{αc}`, `H_{αs}` (1.8.15) with **Theorem 1.8.5**
  (`DF.isClosed_alphaCSubspace`, `DF.apply_mem_alphaCSubspace`, …, `DF.exists_alpha_split`);
* `DF.upperHausdorffDim` — `dim⁺_H(μ)` (Definition 1.8.15).

Deviations: as noted above, closed balls are used in `upperDeriv`; the decomposition is stated
with an `h^α`-null Borel set `N ⊇ T_∞` (so that all pieces are restrictions to measurable
sets) rather than with `T_f`, `T_∞` themselves; the two agree up to `μ`-null sets.

No `Statement` props are introduced in this file.
-/
import DamanikFillman.Ch1.SpectralDecomposition

noncomputable section

open scoped ENNReal NNReal Topology InnerProductSpace
open MeasureTheory Set Filter Metric

namespace DF

section MeasurePart

variable (μ : Measure ℝ) (α : ℝ)

/-- The upper `α`-derivative `D^α_μ(E) = limsup_{ε↓0} μ([E-ε, E+ε]) / (2ε)^α` (1.8.4). -/
def upperDeriv (E : ℝ) : ℝ≥0∞ :=
  limsup (fun ε : ℝ => μ (closedBall E ε) / ENNReal.ofReal ((2 * ε) ^ α)) (𝓝[>] 0)

/-- `T_∞ = {E : D^α_μ(E) = ∞}`. -/
def Tinf : Set ℝ := {E | upperDeriv μ α E = ⊤}

/-- `T_f = {E : D^α_μ(E) < ∞}`. -/
def Tfin : Set ℝ := {E | upperDeriv μ α E < ⊤}

lemma Tfin_eq_compl : Tfin μ α = (Tinf μ α)ᶜ := by
  ext E; simp [Tfin, Tinf, lt_top_iff_ne_top]

/-- Points where `μ` is `r`-Hölder on all rational intervals around `E` of length `≤ 2`. -/
def holderSet (r : ℝ) : Set ℝ :=
  {E | ∀ a b : ℚ, (a : ℝ) < E → E < b → (b : ℝ) - a ≤ 2 →
    μ (Ioo (a : ℝ) b) ≤ ENNReal.ofReal (r * ((b : ℝ) - a) ^ α)}

variable {μ α}

lemma measurableSet_holderSet (r : ℝ) : MeasurableSet (holderSet μ α r) := by
  have : holderSet μ α r = ⋂ a : ℚ, ⋂ b : ℚ, ((Ioi (a : ℝ))ᶜ ∪ (Iio (b : ℝ))ᶜ ∪
      {_E | (b : ℝ) - a ≤ 2 → μ (Ioo (a : ℝ) b) ≤ ENNReal.ofReal (r * ((b : ℝ) - a) ^ α)}) := by
    ext E
    simp only [holderSet, mem_setOf_eq, mem_iInter, mem_union, mem_compl_iff, mem_Ioi, mem_Iio]
    constructor
    · intro h a b
      by_cases h1 : (a : ℝ) < E
      · by_cases h2 : E < (b : ℝ)
        · exact Or.inr (h a b h1 h2)
        · exact Or.inl (Or.inr h2)
      · exact Or.inl (Or.inl h1)
    · intro h a b h1 h2
      rcases h a b with (h' | h') | h'
      · exact absurd h1 h'
      · exact absurd h2 h'
      · exact h'
  rw [this]
  refine MeasurableSet.iInter fun a => MeasurableSet.iInter fun b => ?_
  refine ((measurableSet_Ioi.compl).union (measurableSet_Iio.compl)).union ?_
  exact MeasurableSet.const _

lemma holderSet_mono {r s : ℝ} (hrs : r ≤ s) : holderSet μ α r ⊆ holderSet μ α s := by
  intro E hE a b h1 h2 h3
  refine (hE a b h1 h2 h3).trans (ENNReal.ofReal_le_ofReal ?_)
  have : 0 ≤ ((b : ℝ) - a) ^ α := Real.rpow_nonneg (by linarith) _
  nlinarith

/-- The key Hölder bound on closed intervals around a point of `holderSet`. -/
lemma holderSet_bound {r : ℝ} (hα : 0 < α) {E : ℝ} (hE : E ∈ holderSet μ α r) {c d : ℝ}
    (hc : c ≤ E) (hd : E ≤ d) (hcd : d - c < 2) :
    μ (Icc c d) ≤ ENNReal.ofReal (r * (d - c) ^ α) := by
  have hcont : ContinuousAt (fun η : ℝ => ENNReal.ofReal (r * (d - c + 2 * η) ^ α)) 0 := by
    refine ENNReal.continuous_ofReal.continuousAt.comp ?_
    refine continuousAt_const.mul ?_
    exact (Real.continuousAt_rpow_const _ _ (Or.inr hα.le)).comp (by fun_prop)
  have hlim : Tendsto (fun η : ℝ => ENNReal.ofReal (r * (d - c + 2 * η) ^ α)) (𝓝[>] 0)
      (𝓝 (ENNReal.ofReal (r * (d - c) ^ α))) := by
    have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  refine ge_of_tendsto hlim ?_
  have hsmall : ∀ᶠ η in 𝓝[>] (0 : ℝ), d - c + 2 * η < 2 := by
    have : ContinuousAt (fun η : ℝ => d - c + 2 * η) 0 := by fun_prop
    have h2 := this.tendsto.eventually (gt_mem_nhds (by simpa using hcd))
    exact h2.filter_mono nhdsWithin_le_nhds
  filter_upwards [hsmall, self_mem_nhdsWithin] with η hη hpos
  obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show c - η < c by linarith [mem_Ioi.1 hpos])
  obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show d < d + η by linarith [mem_Ioi.1 hpos])
  have hab : (b : ℝ) - a ≤ d - c + 2 * η := by linarith
  calc μ (Icc c d) ≤ μ (Ioo (a : ℝ) b) := measure_mono fun x hx => ⟨by linarith [hx.1],
        by linarith [hx.2]⟩
    _ ≤ ENNReal.ofReal (r * ((b : ℝ) - a) ^ α) := hE a b (by linarith) (by linarith) (by linarith)
    _ ≤ ENNReal.ofReal (r * (d - c + 2 * η) ^ α) := by
        by_cases hr : 0 ≤ r
        · exact ENNReal.ofReal_le_ofReal
            (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by linarith) hab hα.le) hr)
        · -- if `r < 0` the left side is already `≤ 0`
          have h0 : r * ((b : ℝ) - a) ^ α ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg (le_of_lt (not_le.1 hr))
              (Real.rpow_nonneg (by linarith) _)
          rw [ENNReal.ofReal_of_nonpos h0]
          exact bot_le

lemma measure_singleton_of_mem_holderSet {r : ℝ} (hα : 0 < α) {E : ℝ}
    (hE : E ∈ holderSet μ α r) : μ {E} = 0 := by
  have := holderSet_bound hα hE le_rfl le_rfl (by norm_num)
  rw [Icc_self, sub_self, Real.zero_rpow hα.ne', mul_zero, ENNReal.ofReal_zero] at this
  exact le_antisymm this bot_le

/-- `T_f ⊆ ⋃ₙ holderSet n`. -/
lemma Tfin_subset_iUnion [IsFiniteMeasure μ] (hα : 0 < α) :
    Tfin μ α ⊆ ⋃ n : ℕ, holderSet μ α n := by
  intro E hE
  obtain ⟨R, hR, hRtop⟩ := exists_between (show upperDeriv μ α E < ⊤ from hE)
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), μ (closedBall E ε) / ENNReal.ofReal ((2 * ε) ^ α) < R :=
    eventually_lt_of_limsup_lt hR
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).1 hev
  have hu0 : (0 : ℝ) < u := hu
  set ε₀ := min (u / 2) 1
  have hε₀ : 0 < ε₀ := lt_min (by linarith) one_pos
  have hε₀u : ε₀ < u := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  set M := μ.real univ
  set r : ℝ := max (R.toReal * 2 ^ α) (M / ε₀ ^ α)
  obtain ⟨n, hn⟩ := exists_nat_ge r
  refine mem_iUnion.2 ⟨n, holderSet_mono hn ?_⟩
  intro a b ha hb hab
  set ℓ : ℝ := (b : ℝ) - a
  have hℓ : 0 < ℓ := by simp only [ℓ]; linarith
  have hsub2 : Ioo (a : ℝ) b ⊆ closedBall E ℓ := by
    intro x hx; rw [mem_closedBall, Real.dist_eq, abs_le]
    constructor <;> linarith [hx.1, hx.2]
  by_cases hsm : ℓ < ε₀
  · have hmem : ℓ ∈ Ioo 0 u := ⟨hℓ, by linarith⟩
    have h1 := hsub hmem
    simp only [mem_setOf_eq] at h1
    have hpos : 0 < (2 * ℓ) ^ α := Real.rpow_pos_of_pos (by linarith) _
    rw [ENNReal.div_lt_iff (Or.inl (ENNReal.ofReal_pos.2 hpos).ne')
      (Or.inl ENNReal.ofReal_ne_top)] at h1
    have hRfin : R ≠ ⊤ := hRtop.ne
    calc μ (Ioo (a : ℝ) b) ≤ μ (closedBall E ℓ) := measure_mono hsub2
      _ ≤ R * ENNReal.ofReal ((2 * ℓ) ^ α) := h1.le
      _ = ENNReal.ofReal (R.toReal * 2 ^ α * ℓ ^ α) := by
          rw [← ENNReal.ofReal_toReal hRfin, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg,
            Real.mul_rpow (by norm_num) hℓ.le, mul_assoc, ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
      _ ≤ ENNReal.ofReal (r * ℓ ^ α) := ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hℓ.le _))
  · push Not at hsm
    have hpow : ε₀ ^ α ≤ ℓ ^ α := Real.rpow_le_rpow hε₀.le hsm hα.le
    have hpos : 0 < ε₀ ^ α := Real.rpow_pos_of_pos hε₀ _
    calc μ (Ioo (a : ℝ) b) ≤ μ univ := measure_mono (subset_univ _)
      _ = ENNReal.ofReal M := (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (M / ε₀ ^ α * ℓ ^ α) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
          exact mul_le_mul_of_nonneg_left hpow measureReal_nonneg
      _ ≤ ENNReal.ofReal (r * ℓ ^ α) := ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hℓ.le _))

/-- Bound for a small set meeting `holderSet r`. -/
lemma measure_inter_holderSet_le {r : ℝ} (hα : 0 < α) (hr : 0 ≤ r) (t : Set ℝ)
    (ht : ediam t ≤ 1 / 2) :
    μ (t ∩ holderSet μ α r) ≤ ENNReal.ofReal (r * 2 ^ α) * ⨆ _ : t.Nonempty, ediam t ^ α := by
  rcases (t ∩ holderSet μ α r).eq_empty_or_nonempty with he | ⟨E, hEt, hEH⟩
  · rw [he, measure_empty]; exact bot_le
  have hne : t.Nonempty := ⟨E, hEt⟩
  rw [iSup_pos hne]
  have hfin : ediam t ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) ht
  set d := diam t
  have hd0 : 0 ≤ d := diam_nonneg
  have hd : d ≤ 1 / 2 := by
    have := ENNReal.toReal_mono (by norm_num) ht
    simpa [d, diam] using this
  have hsub : t ⊆ Icc (E - d) (E + d) := by
    intro x hx
    have := dist_le_diam_of_mem' hfin hx hEt
    rw [Real.dist_eq, abs_le] at this
    constructor <;> linarith [this.1, this.2]
  calc μ (t ∩ holderSet μ α r) ≤ μ (Icc (E - d) (E + d)) := measure_mono (inter_subset_left.trans hsub)
    _ ≤ ENNReal.ofReal (r * (E + d - (E - d)) ^ α) :=
        holderSet_bound hα hEH (by linarith) (by linarith) (by linarith)
    _ = ENNReal.ofReal (r * 2 ^ α) * ediam t ^ α := by
        rw [show E + d - (E - d) = 2 * d by ring, Real.mul_rpow (by norm_num) hd0, ← mul_assoc,
          ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_rpow_of_nonneg hd0 hα.le]
        congr 2
        exact ENNReal.ofReal_toReal hfin

/-- **Theorem 1.8.2**, second part: `μ(S ∩ T_f) = 0` whenever `h^α(S) = 0`. -/
theorem measure_inter_Tfin_eq_zero [IsFiniteMeasure μ] (hα : 0 < α) {S : Set ℝ}
    (hS : μH[α] S = 0) : μ (S ∩ Tfin μ α) = 0 := by
  refine measure_mono_null (inter_subset_inter_right S (Tfin_subset_iUnion hα)) ?_
  rw [inter_iUnion]
  refine measure_iUnion_null fun n => ?_
  set r : ℝ := (n : ℝ)
  have hr : 0 ≤ r := Nat.cast_nonneg n
  -- for every `η > 0`, `μ(S ∩ H) ≤ C η`
  have key : ∀ η : ℝ≥0∞, 0 < η → μ (S ∩ holderSet μ α r) ≤ ENNReal.ofReal (r * 2 ^ α) * η := by
    intro η hη
    have h0 := hS
    rw [Measure.hausdorffMeasure_apply] at h0
    have h1 := (ENNReal.iSup_eq_zero.1 h0) (1 / 2)
    rw [ENNReal.iSup_eq_zero] at h1
    have h2 := h1 (by norm_num)
    obtain ⟨t, ht⟩ := iInf_lt_iff.1 (h2.symm ▸ hη : (⨅ (t : ℕ → Set ℝ) (_ : S ⊆ ⋃ n, t n)
      (_ : ∀ n, ediam (t n) ≤ 1 / 2), ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ α) < η)
    obtain ⟨hcov, ht⟩ := iInf_lt_iff.1 ht
    obtain ⟨hdiam, ht⟩ := iInf_lt_iff.1 ht
    calc μ (S ∩ holderSet μ α r) ≤ μ (⋃ n, t n ∩ holderSet μ α r) := by
          refine measure_mono fun x hx => ?_
          obtain ⟨i, hi⟩ := mem_iUnion.1 (hcov hx.1)
          exact mem_iUnion.2 ⟨i, hi, hx.2⟩
      _ ≤ ∑' n, μ (t n ∩ holderSet μ α r) := measure_iUnion_le _
      _ ≤ ∑' n, ENNReal.ofReal (r * 2 ^ α) * ⨆ _ : (t n).Nonempty, ediam (t n) ^ α :=
          ENNReal.tsum_le_tsum fun i => measure_inter_holderSet_le hα hr _ (hdiam i)
      _ = ENNReal.ofReal (r * 2 ^ α) * ∑' n, ⨆ _ : (t n).Nonempty, ediam (t n) ^ α :=
          ENNReal.tsum_mul_left
      _ ≤ ENNReal.ofReal (r * 2 ^ α) * η := mul_le_mul_right ht.le _
  have hlim : Tendsto (fun η : ℝ≥0∞ => ENNReal.ofReal (r * 2 ^ α) * η) (𝓝[>] 0) (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (tendsto_id : Tendsto id (𝓝 (0 : ℝ≥0∞)) (𝓝 0))
      (Or.inr (ENNReal.ofReal_ne_top (r := r * 2 ^ α)))
    have := h.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
    simpa using this
  refine le_antisymm (ge_of_tendsto hlim ?_) bot_le
  filter_upwards [self_mem_nhdsWithin] with η hη
  exact key η hη

/-- The Vitali estimate in the proof of Theorem 1.8.2:
`h^α({E : D^α_μ(E) > s}) ≤ 5^α s⁻¹ μ(ℝ)`. -/
lemma hausdorffMeasure_upper_le [IsFiniteMeasure μ] (hα : 0 < α) {s : ℝ} (hs : 0 < s) :
    μH[α] {E | ∃ᶠ ε in 𝓝[>] (0 : ℝ), ENNReal.ofReal (s * (2 * ε) ^ α) < μ (closedBall E ε)}
      ≤ ENNReal.ofReal (5 ^ α / s) * μ univ := by
  set T := {E | ∃ᶠ ε in 𝓝[>] (0 : ℝ), ENNReal.ofReal (s * (2 * ε) ^ α) < μ (closedBall E ε)}
  set δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδ : ∀ n, 0 < δ n := fun n => by positivity
  have hex : ∀ n, ∀ E ∈ T, ∃ ε, 0 < ε ∧ ε < δ n / 10 ∧
      ENNReal.ofReal (s * (2 * ε) ^ α) < μ (closedBall E ε) := by
    intro n E hE
    obtain ⟨ε, h1, h2⟩ := (Frequently.and_eventually hE
      (Ioo_mem_nhdsGT (show (0 : ℝ) < δ n / 10 by linarith [hδ n]))).exists
    exact ⟨ε, h2.1, h2.2, h1⟩
  choose! ε hε0 hεδ hεμ using hex
  have hv : ∀ n, ∃ u ⊆ T, (u.PairwiseDisjoint fun a => closedBall a (ε n a)) ∧
      ∀ a ∈ T, ∃ b ∈ u, closedBall a (ε n a) ⊆ closedBall b (5 * ε n b) := fun n =>
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall T (fun a => a) (ε n)
      (δ n / 10) (fun a ha => (hεδ n a ha).le) 5 (by norm_num)
  choose u huT hudisj hucov using hv
  have hucount : ∀ n, (u n).Countable := fun n =>
    ((hudisj n).mono fun a => ball_subset_closedBall).countable_of_isOpen
      (fun a _ => isOpen_ball) (fun a ha => nonempty_ball.2 (hε0 n a (huT n ha)))
  have : ∀ n, Countable (u n) := fun n => (hucount n).to_subtype
  have hmain := Measure.hausdorffMeasure_le_liminf_tsum (ι := fun n => u n) α T (l := atTop)
    (fun n => ENNReal.ofReal (δ n)) (by
      have := ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat)
      simpa [δ] using this)
    (fun n i => closedBall (i : ℝ) (5 * ε n i))
    (Eventually.of_forall fun n i => by
      refine (ediam_le_of_forall_dist_le (C := 10 * ε n i) fun x hx y hy => ?_).trans
        (ENNReal.ofReal_le_ofReal ?_)
      · rw [mem_closedBall] at hx hy
        calc dist x y ≤ dist x (i : ℝ) + dist (i : ℝ) y := dist_triangle _ _ _
          _ ≤ 5 * ε n i + 5 * ε n i := add_le_add hx (by rw [dist_comm]; exact hy)
          _ = 10 * ε n i := by ring
      · linarith [hεδ n i (huT n i.2)])
    (Eventually.of_forall fun n => by
      intro E hE
      obtain ⟨b, hb, hsub⟩ := hucov n E hE
      exact mem_iUnion.2 ⟨⟨b, hb⟩, hsub (mem_closedBall_self (hε0 n E hE).le)⟩)
  refine hmain.trans (liminf_le_of_frequently_le' (Frequently.of_forall fun n => ?_))
  -- bound for each scale
  have hterm : ∀ i : u n, ediam (closedBall (i : ℝ) (5 * ε n i)) ^ α ≤
      ENNReal.ofReal (5 ^ α / s) * μ (closedBall (i : ℝ) (ε n i)) := by
    intro i
    have hεi := hε0 n i (huT n i.2)
    have h1 : ediam (closedBall (i : ℝ) (5 * ε n i)) ≤ ENNReal.ofReal (10 * ε n i) := by
      refine ediam_le_of_forall_dist_le fun x hx y hy => ?_
      rw [mem_closedBall] at hx hy
      calc dist x y ≤ dist x (i : ℝ) + dist (i : ℝ) y := dist_triangle _ _ _
        _ ≤ 5 * ε n i + 5 * ε n i := add_le_add hx (by rw [dist_comm]; exact hy)
        _ = 10 * ε n i := by ring
    calc ediam (closedBall (i : ℝ) (5 * ε n i)) ^ α ≤ ENNReal.ofReal (10 * ε n i) ^ α :=
          ENNReal.rpow_le_rpow h1 hα.le
      _ = ENNReal.ofReal (5 ^ α / s) * ENNReal.ofReal (s * (2 * ε n i) ^ α) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hα.le, ← ENNReal.ofReal_mul
            (by positivity)]
          congr 1
          rw [show 10 * ε n i = 5 * (2 * ε n i) by ring, Real.mul_rpow (by norm_num)
            (by positivity)]
          field_simp
      _ ≤ ENNReal.ofReal (5 ^ α / s) * μ (closedBall (i : ℝ) (ε n i)) :=
          mul_le_mul_right (hεμ n i (huT n i.2)).le _
  calc ∑' i : u n, ediam (closedBall (i : ℝ) (5 * ε n i)) ^ α
      ≤ ∑' i : u n, ENNReal.ofReal (5 ^ α / s) * μ (closedBall (i : ℝ) (ε n i)) :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (5 ^ α / s) * μ (⋃ i : u n, closedBall (i : ℝ) (ε n i)) := by
        rw [ENNReal.tsum_mul_left, measure_iUnion (hudisj n).subtype
          (fun i => measurableSet_closedBall)]
    _ ≤ ENNReal.ofReal (5 ^ α / s) * μ univ := mul_le_mul_right (measure_mono (subset_univ _)) _

/-- **Theorem 1.8.2**, first part: `h^α(T_∞) = 0`. -/
theorem hausdorffMeasure_Tinf [IsFiniteMeasure μ] (hα : 0 < α) : μH[α] (Tinf μ α) = 0 := by
  have hsub : ∀ s : ℝ, 0 < s → Tinf μ α ⊆
      {E | ∃ᶠ ε in 𝓝[>] (0 : ℝ), ENNReal.ofReal (s * (2 * ε) ^ α) < μ (closedBall E ε)} := by
    intro s hs E hE
    have h1 : ENNReal.ofReal s < upperDeriv μ α E := by
      rw [show upperDeriv μ α E = ⊤ from hE]; exact ENNReal.ofReal_lt_top
    have h2 := frequently_lt_of_lt_limsup (by isBoundedDefault) h1
    refine (h2.and_eventually self_mem_nhdsWithin).mono fun ε ⟨hε, hpos⟩ => ?_
    have hp : 0 < (2 * ε) ^ α := Real.rpow_pos_of_pos (by linarith [show (0 : ℝ) < ε from hpos]) _
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl (ENNReal.ofReal_pos.2 hp).ne')
      (Or.inl ENNReal.ofReal_ne_top)] at hε
    rwa [ENNReal.ofReal_mul hs.le]
  have hbound : ∀ n : ℕ, μH[α] (Tinf μ α) ≤ ENNReal.ofReal ((5 : ℝ) ^ α / ((n : ℝ) + 1)) * μ univ :=
    fun n => (measure_mono (hsub _ (by positivity))).trans
      (hausdorffMeasure_upper_le hα (by positivity))
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal ((5 : ℝ) ^ α / ((n : ℝ) + 1)) * μ univ) atTop
      (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (5 : ℝ) ^ α / ((n : ℝ) + 1)) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ((5 : ℝ) ^ α)
      rw [mul_zero] at this
      exact this.congr fun n => by rw [mul_one_div]
    have h2 := ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal h1)
      (Or.inr (measure_ne_top μ univ))
    simpa using h2
  exact le_antisymm (ge_of_tendsto' hlim hbound) bot_le

/-! ### The decomposition `μ = μ_{αc} + μ_{αs}` -/

/-- `μ` is `α`-continuous: it gives zero mass to `h^α`-null sets. -/
def IsAlphaContinuous (μ : Measure ℝ) (α : ℝ) : Prop := μ ≪ μH[α]

/-- `μ` is `α`-singular: it is carried by an `h^α`-null set. -/
def IsAlphaSingular (μ : Measure ℝ) (α : ℝ) : Prop := μ ⟂ₘ μH[α]

/-- The decomposition (1.8.13)–(1.8.14): there is a Borel `h^α`-null set `N ⊇ T_∞` such that
`μ = μ|_{Nᶜ} + μ|_N` with `μ|_{Nᶜ}` `α`-continuous and `μ|_N` `α`-singular. -/
theorem exists_alpha_decomposition [IsFiniteMeasure μ] (hα : 0 < α) :
    ∃ N : Set ℝ, MeasurableSet N ∧ μH[α] N = 0 ∧ Tinf μ α ⊆ N ∧
      IsAlphaContinuous (μ.restrict Nᶜ) α ∧ IsAlphaSingular (μ.restrict N) α := by
  refine ⟨toMeasurable μH[α] (Tinf μ α), measurableSet_toMeasurable _ _, ?_,
    subset_toMeasurable _ _, ?_, ?_⟩
  · rw [measure_toMeasurable]; exact hausdorffMeasure_Tinf hα
  · refine Measure.AbsolutelyContinuous.mk fun S hS hS0 => ?_
    rw [Measure.restrict_apply hS]
    refine measure_mono_null (inter_subset_inter_right S ?_) (measure_inter_Tfin_eq_zero hα hS0)
    rw [Tfin_eq_compl]
    exact compl_subset_compl.2 (subset_toMeasurable _ _)
  · refine ⟨(toMeasurable μH[α] (Tinf μ α))ᶜ, (measurableSet_toMeasurable _ _).compl, ?_, ?_⟩
    · rw [Measure.restrict_apply (measurableSet_toMeasurable _ _).compl]; simp
    · rw [compl_compl, measure_toMeasurable]; exact hausdorffMeasure_Tinf hα

/-! ### Uniform `α`-Hölder continuity and Theorem 1.8.14 -/

/-- **Definition 1.8.9**: `μ` is uniformly `α`-Hölder continuous (`UαH`). -/
def UalphaH (μ : Measure ℝ) (α : ℝ) : Prop :=
  ∃ C : ℝ, ∀ a b : ℝ, a ≤ b → b - a ≤ 1 → μ (Icc a b) ≤ ENNReal.ofReal (C * (b - a) ^ α)

lemma UalphaH_restrict_holderSet (hα : 0 < α) (n : ℕ) :
    UalphaH (μ.restrict (holderSet μ α n)) α := by
  refine ⟨n, fun a b hab hb1 => ?_⟩
  rw [Measure.restrict_apply measurableSet_Icc]
  rcases (Icc a b ∩ holderSet μ α n).eq_empty_or_nonempty with he | ⟨E, hE, hEH⟩
  · rw [he, measure_empty]; exact bot_le
  · exact (measure_mono inter_subset_left).trans
      (holderSet_bound hα hEH hE.1 hE.2 (by linarith))

/-- **Theorem 1.8.14**: an `α`-continuous finite measure is, up to arbitrarily small mass,
uniformly `α`-Hölder: `μ = ν₁ + ν₂` with `ν₁ = μ|_S` `UαH`, `ν₂ = μ|_{Sᶜ}` (mutually singular
with `ν₁`) and `ν₂(ℝ) < ε`. -/
theorem exists_UalphaH_approx [IsFiniteMeasure μ] (hα : 0 < α) (hμ : IsAlphaContinuous μ α)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ S : Set ℝ, MeasurableSet S ∧ UalphaH (μ.restrict S) α ∧ μ Sᶜ < ε := by
  have hanti : Antitone fun n : ℕ => (holderSet μ α n)ᶜ := fun m n hmn =>
    compl_subset_compl.2 (holderSet_mono (by exact_mod_cast hmn))
  have hlim := tendsto_measure_iInter_atTop (μ := μ) (s := fun n : ℕ => (holderSet μ α n)ᶜ)
    (fun n => (measurableSet_holderSet (μ := μ) (α := α) (n : ℝ)).compl.nullMeasurableSet) hanti
    ⟨0, measure_ne_top μ _⟩
  have h0 : μ (⋂ n : ℕ, (holderSet μ α n)ᶜ) = 0 := by
    refine measure_mono_null ?_ (hμ (hausdorffMeasure_Tinf (μ := μ) hα))
    intro E hE
    by_contra hE'
    have : E ∈ Tfin μ α := by rw [Tfin_eq_compl]; exact hE'
    obtain ⟨n, hn⟩ := mem_iUnion.1 (Tfin_subset_iUnion hα this)
    exact (mem_iInter.1 hE n) hn
  rw [h0] at hlim
  obtain ⟨n, hn⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  exact ⟨holderSet μ α n, measurableSet_holderSet _, UalphaH_restrict_holderSet hα n, hn⟩

/-- **Definition 1.8.15**: the upper Hausdorff dimension `dim⁺_H(μ)` of a measure, the infimum
of the Hausdorff dimensions of its supports. -/
def upperHausdorffDim (μ : Measure ℝ) : ℝ≥0∞ := ⨅ (S : Set ℝ) (_ : μ Sᶜ = 0), dimH S

/-- If `0 < α < dim⁺_H(μ)` then the `α`-continuous part of `μ` is nonzero. -/
theorem alphaC_ne_zero_of_lt_upperHausdorffDim [IsFiniteMeasure μ] (hα : 0 < α)
    (hlt : ENNReal.ofReal α < upperHausdorffDim μ) {N : Set ℝ} (hN0 : μH[α] N = 0) :
    μ Nᶜ ≠ 0 := by
  intro h
  have hdim : dimH N ≤ ENNReal.ofReal α := by
    have := dimH_le_of_hausdorffMeasure_ne_top (d := α.toNNReal)
      (by rw [Real.coe_toNNReal _ hα.le, hN0]; exact ENNReal.zero_ne_top)
    simpa [ENNReal.ofReal] using this
  have : upperHausdorffDim μ ≤ dimH N := iInf₂_le N h
  exact absurd (this.trans hdim) (not_le.2 hlt)

end MeasurePart

/-! ### `α`-continuous and `α`-singular spectral subspaces (Theorem 1.8.5) -/

section Spectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (α : ℝ)

/-- `H_{αc}` (1.8.15). -/
def alphaCSubspace : Submodule ℂ H where
  carrier := {φ | ∀ S : Set ℝ, MeasurableSet S → μH[α] S = 0 → spectralMeasure A hA φ S = 0}
  add_mem' := fun hφ hψ S hS hS0 => spec_null_add hS (hφ S hS hS0) (hψ S hS hS0)
  zero_mem' := fun S _ _ => spec_null_zero S
  smul_mem' := fun c _ hφ S hS hS0 => spec_null_smul c (hφ S hS hS0)

/-- `H_{αs}` (1.8.15). -/
def alphaSSubspace : Submodule ℂ H where
  carrier := {φ | ∃ N : Set ℝ, MeasurableSet N ∧ μH[α] N = 0 ∧ spectralMeasure A hA φ Nᶜ = 0}
  add_mem' := by
    rintro φ ψ ⟨N, hN, hN0, hφ⟩ ⟨M, hM, hM0, hψ⟩
    refine ⟨N ∪ M, hN.union hM, measure_union_null hN0 hM0,
      spec_null_add (hN.union hM).compl ?_ ?_⟩
    · exact measure_mono_null (compl_subset_compl.2 subset_union_left) hφ
    · exact measure_mono_null (compl_subset_compl.2 subset_union_right) hψ
  zero_mem' := ⟨∅, MeasurableSet.empty, measure_empty, spec_null_zero _⟩
  smul_mem' := by
    rintro c φ ⟨N, hN, hN0, hφ⟩
    exact ⟨N, hN, hN0, spec_null_smul c hφ⟩

variable {A hA α}

theorem isClosed_alphaCSubspace : IsClosed (alphaCSubspace A hA α : Set H) :=
  isSeqClosed_iff_isClosed.1 fun _ _ hφ hlim S hS hS0 =>
    spec_null_of_tendsto hS hlim fun n => hφ n S hS hS0

theorem isClosed_alphaSSubspace : IsClosed (alphaSSubspace A hA α : Set H) := by
  refine isSeqClosed_iff_isClosed.1 fun φ ψ hφ hlim => ?_
  choose N hN hN0 hφN using hφ
  refine ⟨⋃ n, N n, MeasurableSet.iUnion hN, measure_iUnion_null hN0, ?_⟩
  exact spec_null_of_tendsto (MeasurableSet.iUnion hN).compl hlim
    fun n => measure_mono_null (compl_subset_compl.2 (subset_iUnion N n)) (hφN n)

theorem apply_mem_alphaCSubspace {φ : H} (hφ : φ ∈ alphaCSubspace A hA α) :
    A φ ∈ alphaCSubspace A hA α :=
  fun S hS hS0 => spec_null_apply hS (hφ S hS hS0)

theorem apply_mem_alphaSSubspace {φ : H} (hφ : φ ∈ alphaSSubspace A hA α) :
    A φ ∈ alphaSSubspace A hA α := by
  obtain ⟨N, hN, hN0, h⟩ := hφ
  exact ⟨N, hN, hN0, spec_null_apply hN.compl h⟩

theorem alphaC_orthogonal_alphaS {φ ψ : H} (hφ : φ ∈ alphaCSubspace A hA α)
    (hψ : ψ ∈ alphaSSubspace A hA α) : ⟪φ, ψ⟫_ℂ = 0 := by
  obtain ⟨N, hN, hN0, hψN⟩ := hψ
  exact inner_eq_zero_of_spec_null hN (hφ N hN hN0) hψN

/-- **Theorem 1.8.5**: `H = H_{αc} ⊕ H_{αs}` (existence of the splitting; orthogonality is
`alphaC_orthogonal_alphaS`). -/
theorem exists_alpha_split (hα : 0 < α) (φ : H) :
    ∃ c ∈ alphaCSubspace A hA α, ∃ s ∈ alphaSSubspace A hA α, φ = c + s := by
  obtain ⟨N, hN, hN0, -, hc, -⟩ := exists_alpha_decomposition (μ := spectralMeasure A hA φ) hα
  refine ⟨specProj A hA Nᶜ φ, fun S hS hS0 => ?_, specProj A hA N φ, ⟨N, hN, hN0, ?_⟩, ?_⟩
  · rw [spectralMeasure_specProj hN.compl]; exact hc hS0
  · rw [spectralMeasure_specProj hN, Measure.restrict_apply hN.compl]; simp
  · have := congrArg (fun T : H →L[ℂ] H => T φ) (specProj_add_compl (A := A) (hA := hA) hN)
    simp only [_root_.add_apply, one_apply_eq_self] at this
    rw [add_comm]; exact this.symm

end Spectral

end DF
