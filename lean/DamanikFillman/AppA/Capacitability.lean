/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Appendix A.2: Choquet's capacitability theorem for the logarithmic capacity

## Main results

* `DF.capacity_union_mul_inter_le` — strong subadditivity for open sets in a disc of radius `1/4`.
* `DF.capacity_iUnion_le_iSup` — the (outer) capacity is continuous along increasing sequences of
  *arbitrary* sets in a disc of radius `1/4`.  (Choose open sets `Oₙ ⊇ Aₙ` of nearly minimal
  capacity; by strong subadditivity the capacities of `O₀ ∪ ⋯ ∪ Oₙ` exceed `Cap(Aₙ)` at most by
  a factor `∏ (1 + small)`, since `(O₀ ∪ ⋯ ∪ Oₙ) ∩ Oₙ₊₁ ⊇ Aₙ`.)
* `DF.exists_isCompact_le_capCompact` — **Choquet's capacitability theorem**: a Borel set
  `X` in a disc of radius `1/4` with `Cap(X) > t` contains a compact set `K` with
  `Cap(K) ≥ t`.  (`X` is the continuous image of the Baire space `ℕ^ℕ`; choose bounds `Nᵢ` so
  that the images of `{σ : σᵢ ≤ Nᵢ for i < k}` keep capacity `> t`, and take `K` the image of
  the compact set `{σ : σᵢ ≤ Nᵢ for all i}`.)
* `DF.capacitabilityStatement_holds` — `DF.CapacitabilityStatement`; consequently
  `DF.continuousPotentialStatement_holds` (Lemma A.2.10) and `DF.lowerEnvelopeStatement_holds`
  (Theorem A.2.9).
-/
import DamanikFillman.AppA.StrongSubadditivity
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.MetricSpace.PiNat

noncomputable section

open Real Complex Metric Set Filter Topology MeasureTheory
open scoped ENNReal

namespace DF

/-! ### Bounds -/

lemma capCompact_le_one {a : ℂ} {K : Set ℂ} (hKa : K ⊆ closedBall a (1 / 4)) :
    capCompact K ≤ 1 := by
  unfold capCompact
  calc expNeg (⨅ μ ∈ M1 K, energy μ) ≤ expNeg ((0 : ℝ) : EReal) :=
        expNeg_antitone (le_iInf₂ fun μ hμ => by
          rw [EReal.coe_zero]; exact energy_nonneg_of_subset_closedBall hKa hμ.2)
    _ = 1 := by rw [expNeg_coe]; simp

lemma capacity_le_one {a : ℂ} {B : Set ℂ} (hB : B ⊆ ball a (1 / 4)) : capacity B ≤ 1 := by
  refine (capacity_mono hB).trans ?_
  rw [capacity_open_eq isOpen_ball isBounded_ball]
  exact iSup₂_le fun K _ => iSup_le fun hK => capCompact_le_one (hK.trans ball_subset_closedBall)

lemma capacity_ne_top_of_subset {a : ℂ} {B : Set ℂ} (hB : B ⊆ ball a (1 / 4)) :
    capacity B ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (capacity_le_one hB)

lemma capacity_empty : capacity (∅ : Set ℂ) = 0 :=
  le_antisymm ((capacity_mono (empty_subset {(0 : ℂ)})).trans (by
    rw [capacity_eq_capCompact isCompact_singleton,
      capCompact_eq_zero_of_countable isCompact_singleton (countable_singleton 0)])) zero_le

/-! ### Strong subadditivity for open sets -/

/-- Strong subadditivity of the capacity of open sets in a disc of radius `1/4`. -/
theorem capacity_union_mul_inter_le {a : ℂ} {O₁ O₂ : Set ℂ} (h₁ : IsOpen O₁) (h₂ : IsOpen O₂)
    (h₁a : O₁ ⊆ closedBall a (1 / 4)) (h₂a : O₂ ⊆ closedBall a (1 / 4)) :
    capacity (O₁ ∪ O₂) * capacity (O₁ ∩ O₂) ≤ capacity O₁ * capacity O₂ := by
  have hb : ∀ {O : Set ℂ}, O ⊆ closedBall a (1 / 4) → Bornology.IsBounded O :=
    fun h => isBounded_closedBall.subset h
  rw [capacity_open_eq (h₁.union h₂) (hb (union_subset h₁a h₂a)),
    capacity_open_eq (h₁.inter h₂) (hb (inter_subset_left.trans h₁a))]
  simp only [ENNReal.iSup_mul, ENNReal.mul_iSup]
  refine iSup_le fun M => iSup_le fun hM => iSup_le fun hMO => iSup_le fun K =>
    iSup_le fun hK => iSup_le fun hKO => ?_
  suffices key : capCompact K * capCompact M ≤ capacity O₁ * capacity O₂ by
    first
    | exact key
    | (rw [mul_comm]; exact key)
  obtain ⟨K1, K2, hK1, hK2, hK1O, hK2O, rfl⟩ := hK.binary_compact_cover h₁ h₂ hKO
  have hM1 : M ⊆ O₁ := hMO.trans inter_subset_left
  have hM2 : M ⊆ O₂ := hMO.trans inter_subset_right
  calc capCompact (K1 ∪ K2) * capCompact M
      ≤ capCompact ((K1 ∪ M) ∪ (K2 ∪ M)) * capCompact ((K1 ∪ M) ∩ (K2 ∪ M)) :=
        mul_le_mul' (capCompact_mono (union_subset_union subset_union_left subset_union_left))
          (capCompact_mono (subset_inter subset_union_right subset_union_right))
    _ ≤ capCompact (K1 ∪ M) * capCompact (K2 ∪ M) :=
        capCompact_union_mul_inter_le (hK1.union hM) (hK2.union hM)
          (union_subset (hK1O.trans h₁a) (hM1.trans h₁a))
          (union_subset (hK2O.trans h₂a) (hM2.trans h₂a))
    _ ≤ capacity O₁ * capacity O₂ :=
        mul_le_mul' ((capCompact_le_capacity (hK1.union hM)).trans
            (capacity_mono (union_subset hK1O hM1)))
          ((capCompact_le_capacity (hK2.union hM)).trans (capacity_mono (union_subset hK2O hM2)))

/-! ### Continuity along increasing sequences -/

lemma sum_half_pow_succ_le (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ (k + 1) ≤ 1 := by
  calc ∑ k ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ (k + 1)
      = (1 / 2) * ∑ k ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ ≤ (1 / 2) * 2 := by gcongr; exact sum_geometric_two_le _
    _ = 1 := by norm_num

/-- Continuity of the capacity along increasing sequences, when `Cap(A₀) > 0`. -/
lemma capacity_iUnion_le_of_pos {a : ℂ} {A : ℕ → Set ℂ} (hA : Monotone A)
    (hAa : ∀ n, A n ⊆ ball a (1 / 4)) (h0 : capacity (A 0) ≠ 0) :
    capacity (⋃ n, A n) ≤ ⨆ n, capacity (A n) := by
  obtain ⟨L, hL⟩ : ∃ L : ℝ≥0∞, L = ⨆ n, capacity (A n) := ⟨_, rfl⟩
  rw [← hL]
  have hLne : L ≠ ⊤ := by
    rw [hL]
    exact ne_top_of_le_ne_top ENNReal.one_ne_top (iSup_le fun n => capacity_le_one (hAa n))
  obtain ⟨x, hx⟩ : ∃ x : ℕ → ℝ, ∀ n, x n = (capacity (A n)).toReal := ⟨_, fun _ => rfl⟩
  have hxpos : ∀ n, 0 < x n := fun n => by
    rw [hx n]
    exact ENNReal.toReal_pos (fun h => h0 (le_antisymm
      ((capacity_mono (hA (Nat.zero_le n))).trans h.le) zero_le))
      (capacity_ne_top_of_subset (hAa n))
  have hxL : ∀ n, x n ≤ L.toReal := fun n => by
    rw [hx n, hL]
    exact ENNReal.toReal_mono (hL ▸ hLne) (le_iSup (fun n => capacity (A n)) n)
  have hxeq : ∀ n, capacity (A n) = ENNReal.ofReal (x n) := fun n => by
    rw [hx n, ENNReal.ofReal_toReal (capacity_ne_top_of_subset (hAa n))]
  have hUb : ⋃ n, A n ⊆ ball a (1 / 4) := iUnion_subset hAa
  suffices hsuff : ∀ ε : ℝ, 0 < ε → (capacity (⋃ n, A n)).toReal ≤ L.toReal * Real.exp ε by
    have hlim : Tendsto (fun n : ℕ => L.toReal * Real.exp (1 / ((n : ℝ) + 1))) atTop
        (𝓝 (L.toReal * Real.exp 0)) :=
      tendsto_const_nhds.mul ((Real.continuous_exp.tendsto 0).comp
        tendsto_one_div_add_atTop_nhds_zero_nat)
    rw [Real.exp_zero, mul_one] at hlim
    have h1 := ge_of_tendsto' hlim fun n => hsuff _ (by positivity)
    rw [← ENNReal.ofReal_toReal (capacity_ne_top_of_subset hUb), ← ENNReal.ofReal_toReal hLne]
    exact ENNReal.ofReal_le_ofReal h1
  intro ε hε
  obtain ⟨r, hr⟩ : ∃ r : ℕ → ℝ, ∀ k, r k = Real.exp (ε * (1 / 2) ^ (k + 1)) := ⟨_, fun _ => rfl⟩
  have hr1 : ∀ k, 1 < r k := fun k => by
    rw [hr k]; exact Real.one_lt_exp_iff.2 (by positivity)
  -- open sets of nearly minimal capacity
  have hO : ∀ k, ∃ O : Set ℂ, IsOpen O ∧ A k ⊆ O ∧ O ⊆ ball a (1 / 4) ∧
      (capacity O).toReal ≤ x k * r k := by
    intro k
    have hxr : x k < x k * r k := by nlinarith [hxpos k, hr1 k]
    have hlt : capacity (A k) < ENNReal.ofReal (x k * r k) := by
      rw [hxeq k]
      exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [hxpos k])).2 hxr
    obtain ⟨O, hOo, -, hAO, hOc⟩ := exists_open_of_capacity_lt hlt
    refine ⟨O ∩ ball a (1 / 4), hOo.inter isOpen_ball, subset_inter hAO (hAa k),
      inter_subset_right, ?_⟩
    have : capacity (O ∩ ball a (1 / 4)) ≤ ENNReal.ofReal (x k * r k) := by
      rw [capacity_open_eq (hOo.inter isOpen_ball) (isBounded_ball.subset inter_subset_right)]
      exact iSup₂_le fun C hC => iSup_le fun hCO => (hOc C hC (hCO.trans inter_subset_left)).le
    exact ENNReal.toReal_le_of_le_ofReal (by linarith [hxpos k]) this
  choose O hOo hAO hOa hOc using hO
  -- their partial unions
  obtain ⟨W, hW0, hWs⟩ : ∃ W : ℕ → Set ℂ, W 0 = O 0 ∧ ∀ n, W (n + 1) = W n ∪ O (n + 1) :=
    ⟨fun n => Nat.rec (O 0) (fun n Wn => Wn ∪ O (n + 1)) n, rfl, fun n => rfl⟩
  have hWo : ∀ n, IsOpen (W n) := by
    intro n
    induction n with
    | zero => rw [hW0]; exact hOo 0
    | succ n ih => rw [hWs]; exact ih.union (hOo _)
  have hWa : ∀ n, W n ⊆ ball a (1 / 4) := by
    intro n
    induction n with
    | zero => rw [hW0]; exact hOa 0
    | succ n ih => rw [hWs]; exact union_subset ih (hOa _)
  have hOW : ∀ n, O n ⊆ W n := by
    intro n
    cases n with
    | zero => exact le_of_eq hW0.symm
    | succ n => rw [hWs]; exact subset_union_right
  have hWmono : Monotone W := monotone_nat_of_le_succ fun n => by
    rw [hWs n]; exact subset_union_left
  have hss : ∀ n, (capacity (W (n + 1))).toReal * (capacity (W n ∩ O (n + 1))).toReal ≤
      (capacity (W n)).toReal * (capacity (O (n + 1))).toReal := by
    intro n
    have h := capacity_union_mul_inter_le (hWo n) (hOo (n + 1))
      ((hWa n).trans ball_subset_closedBall) ((hOa (n + 1)).trans ball_subset_closedBall)
    rw [← hWs n] at h
    rw [← ENNReal.toReal_mul, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top (capacity_ne_top_of_subset (hWa n))
      (capacity_ne_top_of_subset (hOa _))) h
  have hclaim : ∀ n, (capacity (W n)).toReal ≤
      x n * Real.exp (ε * ∑ k ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ (k + 1)) := by
    intro n
    induction n with
    | zero =>
      rw [hW0, Finset.sum_range_one, ← hr 0]
      exact hOc 0
    | succ n ih =>
      obtain ⟨E, hE⟩ : ∃ E : ℝ,
          E = Real.exp (ε * ∑ k ∈ Finset.range (n + 1), (1 / 2 : ℝ) ^ (k + 1)) := ⟨_, rfl⟩
      rw [← hE] at ih
      have hEpos : 0 < E := by rw [hE]; exact Real.exp_pos _
      rw [Finset.sum_range_succ, mul_add, Real.exp_add, ← hE, ← hr (n + 1)]
      have h2 : x n ≤ (capacity (W n ∩ O (n + 1))).toReal := by
        rw [hx n]
        exact ENNReal.toReal_mono (capacity_ne_top_of_subset (inter_subset_right.trans (hOa _)))
          (capacity_mono (subset_inter ((hAO n).trans (hOW n))
            ((hA (Nat.le_succ n)).trans (hAO (n + 1)))))
      have hcW : 0 ≤ (capacity (W (n + 1))).toReal := ENNReal.toReal_nonneg
      have hxn := hxpos n
      have h4 : (capacity (W (n + 1))).toReal * x n ≤ (x n * E) * (x (n + 1) * r (n + 1)) :=
        calc (capacity (W (n + 1))).toReal * x n
            ≤ (capacity (W (n + 1))).toReal * (capacity (W n ∩ O (n + 1))).toReal :=
              mul_le_mul_of_nonneg_left h2 hcW
          _ ≤ (capacity (W n)).toReal * (capacity (O (n + 1))).toReal := hss n
          _ ≤ (x n * E) * (x (n + 1) * r (n + 1)) :=
              mul_le_mul ih (hOc (n + 1)) ENNReal.toReal_nonneg (mul_pos hxn hEpos).le
      have h5 : (capacity (W (n + 1))).toReal * x n ≤ (x (n + 1) * (E * r (n + 1))) * x n := by
        linarith
      exact le_of_mul_le_mul_right h5 hxn
  have hWb : ∀ n, capacity (W n) ≤ ENNReal.ofReal (L.toReal * Real.exp ε) := fun n => by
    rw [← ENNReal.ofReal_toReal (capacity_ne_top_of_subset (hWa n))]
    refine ENNReal.ofReal_le_ofReal ((hclaim n).trans ?_)
    refine mul_le_mul (hxL n) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le ENNReal.toReal_nonneg
    exact mul_le_of_le_one_right hε.le (sum_half_pow_succ_le n)
  have hWU : capacity (⋃ n, W n) ≤ ENNReal.ofReal (L.toReal * Real.exp ε) :=
    le_of_tendsto' (tendsto_capacity_monotone hWo hWmono
      (isBounded_ball.subset (iUnion_subset hWa))) hWb
  have hAU : capacity (⋃ n, A n) ≤ capacity (⋃ n, W n) :=
    capacity_mono (iUnion_mono fun n => (hAO n).trans (hOW n))
  exact ENNReal.toReal_le_of_le_ofReal (mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)
    (hAU.trans hWU)

/-- **Continuity of the capacity along increasing sequences** of arbitrary sets in a disc of
radius `1/4` (the property of a Choquet capacity). -/
theorem capacity_iUnion_le_iSup {a : ℂ} {A : ℕ → Set ℂ} (hA : Monotone A)
    (hAa : ∀ n, A n ⊆ ball a (1 / 4)) : capacity (⋃ n, A n) ≤ ⨆ n, capacity (A n) := by
  by_cases h : ∃ n0, capacity (A n0) ≠ 0
  · obtain ⟨n0, hn0⟩ := h
    have hA' : Monotone (fun n => A (n + n0)) := fun m n hmn => hA (by omega)
    have h1 := capacity_iUnion_le_of_pos hA' (fun n => hAa _) (by simpa using hn0)
    have hU : ⋃ n, A (n + n0) = ⋃ n, A n := by
      apply subset_antisymm (iUnion_mono' fun n => ⟨n + n0, subset_rfl⟩)
      exact iUnion_mono fun n => hA (Nat.le_add_right n n0)
    rw [hU] at h1
    exact h1.trans (iSup_le fun n => le_iSup (fun n => capacity (A n)) (n + n0))
  · push_neg at h
    have hR : ∀ n, A n ⊆ ball 0 (‖a‖ + 1) := fun n =>
      (hAa n).trans (ball_subset_ball' (by rw [dist_zero_right]; linarith))
    rw [capacity_iUnion_eq_zero' h hR]
    exact zero_le

/-! ### Choquet's capacitability theorem -/

/-- A compact subset of the Baire space contained in an open set: if `U ⊇ {σ : σᵢ ≤ Nᵢ ∀ i}`
then `U ⊇ {σ : σᵢ ≤ Nᵢ ∀ i < k}` for some `k`. -/
lemma exists_bounded_prefix_subset {N : ℕ → ℕ} {U : Set (ℕ → ℕ)} (hU : IsOpen U)
    (hTU : {σ : ℕ → ℕ | ∀ i, σ i ≤ N i} ⊆ U) :
    ∃ k, {σ : ℕ → ℕ | ∀ i < k, σ i ≤ N i} ⊆ U := by
  have hT : IsCompact {σ : ℕ → ℕ | ∀ i, σ i ≤ N i} := by
    have : {σ : ℕ → ℕ | ∀ i, σ i ≤ N i} = Set.pi univ fun i => Iic (N i) := by
      ext σ; simp [Pi.le_def]
    rw [this]
    exact isCompact_univ_pi fun i => (finite_Iic (N i)).isCompact
  have hcyl : ∀ σ : ℕ → ℕ, ∃ n, σ ∈ U → PiNat.cylinder (E := fun _ : ℕ => ℕ) σ n ⊆ U := by
    intro σ
    by_cases hσ : σ ∈ U
    · obtain ⟨c, ⟨x, n, rfl⟩, hσc, hcU⟩ :=
        (PiNat.isTopologicalBasis_cylinders (E := fun _ : ℕ => ℕ)).exists_subset_of_mem_open hσ hU
      refine ⟨n, fun _ => ?_⟩
      rw [PiNat.mem_cylinder_iff_eq.1 hσc]
      exact hcU
    · exact ⟨0, fun h => absurd h hσ⟩
  choose n hn using hcyl
  obtain ⟨t, htT, hcover⟩ := hT.elim_nhds_subcover
    (fun σ : ℕ → ℕ => PiNat.cylinder (E := fun _ : ℕ => ℕ) σ (n σ))
    (fun σ _ => (PiNat.isOpen_cylinder (E := fun _ : ℕ => ℕ) σ (n σ)).mem_nhds
      (PiNat.self_mem_cylinder (E := fun _ : ℕ => ℕ) σ (n σ)))
  refine ⟨t.sup n, fun τ hτ => ?_⟩
  obtain ⟨τ', hτ'⟩ : ∃ τ' : ℕ → ℕ, ∀ i, τ' i = if i < t.sup n then τ i else 0 :=
    ⟨_, fun _ => rfl⟩
  have hτ'T : τ' ∈ {σ : ℕ → ℕ | ∀ i, σ i ≤ N i} := by
    intro i
    rw [hτ' i]
    split_ifs with h
    · exact hτ i h
    · exact Nat.zero_le _
  obtain ⟨σ, hσt, hτ'σ⟩ := mem_iUnion₂.1 (hcover hτ'T)
  have hle : n σ ≤ t.sup n := Finset.le_sup hσt
  refine hn σ (hTU (htT σ hσt)) ?_
  rw [PiNat.mem_cylinder_iff] at hτ'σ ⊢
  intro i hi
  rw [← hτ'σ i hi, hτ' i, if_pos (lt_of_lt_of_le hi hle)]

/-- **Choquet's capacitability theorem** for the logarithmic capacity: a Borel set `X` in a
disc of radius `1/4` with `Cap(X) > t` contains a compact set of capacity `≥ t`. -/
theorem exists_isCompact_le_capCompact {a : ℂ} {X : Set ℂ} (hXa : X ⊆ ball a (1 / 4))
    (hX : MeasurableSet X) {t : ℝ≥0∞} (ht : t < capacity X) :
    ∃ K ⊆ X, IsCompact K ∧ t ≤ capCompact K := by
  have hXan := hX.analyticSet
  rw [AnalyticSet] at hXan
  rcases hXan with hXe | ⟨f, hf, hfX⟩
  · rw [hXe, capacity_empty] at ht
    exact absurd ht (not_lt_zero')
  obtain ⟨S, hS⟩ : ∃ S : ℕ → (ℕ → ℕ) → Set (ℕ → ℕ),
      ∀ k N, S k N = {σ | ∀ i < k, σ i ≤ N i} := ⟨_, fun _ _ => rfl⟩
  have hSX : ∀ k N, f '' S k N ⊆ ball a (1 / 4) := fun k N =>
    (image_subset_range _ _).trans (hfX.le.trans hXa)
  have hS0 : ∀ N, S 0 N = univ := fun N => by
    rw [hS]; ext σ; simp
  have hSsucc : ∀ k N m, S (k + 1) (Function.update N k m) = S k N ∩ {σ | σ k ≤ m} := by
    intro k N m
    rw [hS, hS]
    ext σ
    simp only [mem_setOf_eq, mem_inter_iff]
    constructor
    · intro h
      refine ⟨fun i hi => ?_, ?_⟩
      · have := h i (Nat.lt_succ_of_lt hi)
        rwa [Function.update_of_ne (ne_of_lt hi)] at this
      · have := h k (Nat.lt_succ_self k)
        rwa [Function.update_self] at this
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · rw [Function.update_of_ne (ne_of_lt hi)]; exact h1 i hi
      · rw [Function.update_self]; exact h2
  -- one step of the construction
  have step : ∀ k N, t < capacity (f '' S k N) →
      ∃ m, t < capacity (f '' S (k + 1) (Function.update N k m)) := by
    intro k N hkN
    have hmono : Monotone (fun m : ℕ => f '' (S k N ∩ {σ | σ k ≤ m})) := fun m m' hmm' =>
      image_mono (inter_subset_inter_right _ fun σ hσ => le_trans hσ hmm')
    have hunion : ⋃ m : ℕ, f '' (S k N ∩ {σ | σ k ≤ m}) = f '' S k N := by
      rw [← image_iUnion, ← inter_iUnion,
        show (⋃ m : ℕ, {σ : ℕ → ℕ | σ k ≤ m}) = univ from
          eq_univ_of_forall fun σ => mem_iUnion.2 ⟨σ k, show σ k ≤ σ k from le_rfl⟩, inter_univ]
    have h := capacity_iUnion_le_iSup hmono fun m =>
      (image_mono inter_subset_left).trans (hSX k N)
    rw [hunion] at h
    obtain ⟨m, hm⟩ := lt_iSup_iff.1 (hkN.trans_le h)
    exact ⟨m, by rw [hSsucc]; exact hm⟩
  choose m hm using step
  have h0 : t < capacity (f '' S 0 (fun _ => 0)) := by rw [hS0, image_univ, hfX]; exact ht
  obtain ⟨seq, hseqs⟩ : ∃ seq : (k : ℕ) → {N : ℕ → ℕ // t < capacity (f '' S k N)},
      ∀ k, (seq (k + 1)).1 = Function.update (seq k).1 k (m k (seq k).1 (seq k).2) :=
    ⟨fun k => Nat.rec (motive := fun k => {N : ℕ → ℕ // t < capacity (f '' S k N)})
      ⟨fun _ => 0, h0⟩ (fun k s => ⟨Function.update s.1 k (m k s.1 s.2), hm k s.1 s.2⟩) k,
      fun k => rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ → ℕ, ∀ i, N i = (seq (i + 1)).1 i := ⟨_, fun _ => rfl⟩
  have hagree : ∀ k i, i < k → (seq k).1 i = N i := by
    intro k
    induction k with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
    | succ k ih =>
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · rw [hseqs k, Function.update_of_ne (ne_of_lt hi)]
        exact ih i hi
      · exact (hN _).symm
  have hP : ∀ k, t < capacity (f '' S k N) := by
    intro k
    have hSeq : S k (seq k).1 = S k N := by
      rw [hS, hS]
      ext σ
      simp only [mem_setOf_eq]
      exact forall₂_congr fun i hi => by rw [hagree k i hi]
    rw [← hSeq]
    exact (seq k).2
  -- the compact set
  set T := {σ : ℕ → ℕ | ∀ i, σ i ≤ N i} with hTdef
  have hT : IsCompact T := by
    have : T = Set.pi univ fun i => Iic (N i) := by ext σ; simp [hTdef, Pi.le_def]
    rw [this]
    exact isCompact_univ_pi fun i => (finite_Iic (N i)).isCompact
  have hK : IsCompact (f '' T) := hT.image hf
  refine ⟨f '' T, (image_subset_range _ _).trans hfX.le, hK, ?_⟩
  rw [← capacity_eq_capCompact hK]
  unfold capacity
  refine le_iInf fun O => le_iInf fun hO => le_iInf fun hOb => le_iInf fun hKO => ?_
  obtain ⟨k, hk⟩ := exists_bounded_prefix_subset (hO.preimage hf)
    (fun σ hσ => hKO ⟨σ, hσ, rfl⟩)
  have hsub : f '' S k N ⊆ O := image_subset_iff.2 (by rw [hS]; exact hk)
  rw [← capacity_open_eq hO hOb]
  exact (hP k).le.trans (capacity_mono hsub)

/-! ### The statements -/

/-- **Capacitability** (`DF.CapacitabilityStatement`): a bounded Borel set of positive capacity
contains a compact set of positive capacity. -/
theorem capacitabilityStatement_holds : CapacitabilityStatement := by
  intro X hXb hXm hX
  -- cover `X` by finitely many discs of radius `1/4`
  have htb : TotallyBounded X := hXb.isCompact_closure.totallyBounded.subset subset_closure
  obtain ⟨c, hcfin, hcov⟩ := Metric.totallyBounded_iff.1 htb (1 / 4) (by norm_num)
  obtain ⟨R0, hR0⟩ := hXb.subset_ball 0
  by_cases hex : ∃ y ∈ c, capacity (X ∩ ball y (1 / 4)) ≠ 0
  · obtain ⟨y, -, hy⟩ := hex
    obtain ⟨s, hs0, hs⟩ := exists_between (pos_iff_ne_zero.2 hy)
    obtain ⟨K, hKX, hK, hsK⟩ := exists_isCompact_le_capCompact inter_subset_right
      (hXm.inter isOpen_ball.measurableSet) hs
    exact ⟨K, hKX.trans inter_subset_left, hK, (lt_of_lt_of_le hs0 hsK).ne'⟩
  · push_neg at hex
    exfalso
    apply hX
    rcases c.eq_empty_or_nonempty with hc | hc
    · have : X = ∅ := by
        rw [hc] at hcov
        simpa using hcov
      rw [this, capacity_empty]
    obtain ⟨g, hg⟩ := hcfin.countable.exists_eq_range hc
    have hXsub : X ⊆ ⋃ n, X ∩ ball (g n) (1 / 4) := by
      intro z hz
      obtain ⟨y, hyc, hzy⟩ := mem_iUnion₂.1 (hcov hz)
      rw [hg] at hyc
      obtain ⟨n, rfl⟩ := hyc
      exact mem_iUnion.2 ⟨n, hz, hzy⟩
    refine le_antisymm ((capacity_mono hXsub).trans ?_) zero_le
    rw [capacity_iUnion_eq_zero' (fun n => hex (g n) (by rw [hg]; exact mem_range_self n))
      (fun n => inter_subset_left.trans hR0)]

/-- **Lemma A.2.10** holds. -/
theorem continuousPotentialStatement_holds : ContinuousPotentialStatement :=
  continuousPotentialStatement_of_capacitability capacitabilityStatement_holds

/-- **Theorem A.2.9** (second half) holds. -/
theorem lowerEnvelopeStatement_holds : LowerEnvelopeStatement :=
  lowerEnvelopeStatement_of_capacitability capacitabilityStatement_holds

end DF
