/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Appendix A.2: sets of capacity zero have Hausdorff dimension zero (Theorem A.2.11)

## Main results

* `DF.Frostman.exists_frostman` — **Frostman's lemma**: if `K ⊆ ℂ` is compact and
  `μH[s] K > 0` (`s > 0`), there is a probability measure `p` on `K` with
  `p(B(x, r)) ≤ C r^s` for all balls.
* `DF.Frostman.energy_le_of_ball_le` — such a measure has finite logarithmic energy
  (`E(p) ≤ C/s`, by the layer-cake formula).
* `DF.capacityZeroDimStatement_holds` — **Theorem A.2.11**.

## Proof of Frostman's lemma

We use the dyadic squares `D k B = {z : (⌊2^k Re z⌋, ⌊2^k Im z⌋) = B}`.

* Since `μH[s] K > 0`, every finite cover of `K` by dyadic squares has
  `∑ 2^{-k s} ≥ c > 0` (`exists_content_pos`).
* At level `n`, maximize the total mass of a weighted sum of point masses at points of `K`, one in
  each level-`n` square meeting `K`, subject to `ν(D k B) ≤ 2^{-k s}` for all `k ≤ n`
  (`exists_level_measure`, a compactness argument).  At a maximizer, every level-`n` square lies in
  a saturated square; the maximal saturated squares cover `K`, so the total mass is `≥ c`.
* A ball of radius `r ≤ 2^{-k}` meets at most `9` squares of level `k`, so
  `ν_n(B(x, r)) ≤ 9 (2r)^s`.  Normalize and pass to a weak limit (Prokhorov on `K` and the
  portmanteau theorem).
-/
import DamanikFillman.AppA.Frostman
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.MetricSpace.HausdorffDimension

noncomputable section

open Real Complex Set Filter Topology MeasureTheory Metric
open scoped ENNReal NNReal

namespace DF

namespace Frostman

/-! ### Dyadic squares -/

/-- The index of the level-`k` dyadic square containing `z`. -/
def idx (k : ℕ) (z : ℂ) : ℤ × ℤ := (⌊z.re * 2 ^ k⌋, ⌊z.im * 2 ^ k⌋)

/-- The level-`k` dyadic square with index `B`. -/
def D (k : ℕ) (B : ℤ × ℤ) : Set ℂ := {z | idx k z = B}

/-- The weight `2^{-k s}` of a level-`k` square. -/
def θ (s : ℝ) (k : ℕ) : ℝ := ((2 : ℝ) ^ k)⁻¹ ^ s

lemma θ_nonneg (s : ℝ) (k : ℕ) : 0 ≤ θ s k := Real.rpow_nonneg (by positivity) _

lemma θ_le_one {s : ℝ} (hs : 0 ≤ s) (k : ℕ) : θ s k ≤ 1 :=
  Real.rpow_le_one (by positivity) (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))) hs

lemma measurable_idx (k : ℕ) : Measurable (idx k) := by
  unfold idx
  exact (Int.measurable_floor.comp (by fun_prop)).prodMk (Int.measurable_floor.comp (by fun_prop))

lemma measurableSet_D (k : ℕ) (B : ℤ × ℤ) : MeasurableSet (D k B) :=
  measurable_idx k (measurableSet_singleton B)

lemma floor_mul_two_pow (x : ℝ) {j k : ℕ} (h : j ≤ k) :
    ⌊x * 2 ^ j⌋ = ⌊x * 2 ^ k⌋ / ((2 ^ (k - j) : ℕ) : ℤ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [Nat.add_sub_cancel_left, ← Int.floor_div_natCast]
  congr 1
  push_cast
  rw [pow_add]
  field_simp

lemma idx_eq_of_idx_eq {j k : ℕ} (h : j ≤ k) {z w : ℂ} (hzw : idx k z = idx k w) :
    idx j z = idx j w := by
  simp only [idx, Prod.mk.injEq] at hzw ⊢
  rw [floor_mul_two_pow z.re h, floor_mul_two_pow w.re h, floor_mul_two_pow z.im h,
    floor_mul_two_pow w.im h, hzw.1, hzw.2]
  exact ⟨rfl, rfl⟩

lemma abs_sub_lt_of_idx_eq {k : ℕ} {z w : ℂ} (h : idx k z = idx k w) :
    |z.re - w.re| < ((2 : ℝ) ^ k)⁻¹ ∧ |z.im - w.im| < ((2 : ℝ) ^ k)⁻¹ := by
  simp only [idx, Prod.mk.injEq] at h
  have h1 := Int.abs_sub_lt_one_of_floor_eq_floor h.1
  have h2 := Int.abs_sub_lt_one_of_floor_eq_floor h.2
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  rw [← sub_mul, abs_mul, abs_of_pos hp] at h1 h2
  constructor
  · rw [lt_inv_iff_mul_lt₀ hp]; linarith
  · rw [lt_inv_iff_mul_lt₀ hp]; linarith

lemma ediam_D_le (k : ℕ) (B : ℤ × ℤ) :
    EMetric.diam (D k B) ≤ ENNReal.ofReal (2 * ((2 : ℝ) ^ k)⁻¹) := by
  refine EMetric.diam_le fun z hz w hw => ?_
  rw [edist_dist]
  refine ENNReal.ofReal_le_ofReal ?_
  have h := abs_sub_lt_of_idx_eq (hz.trans hw.symm)
  rw [dist_eq_norm]
  calc ‖z - w‖ ≤ |(z - w).re| + |(z - w).im| := Complex.norm_le_abs_re_add_abs_im _
    _ = |z.re - w.re| + |z.im - w.im| := by simp
    _ ≤ 2 * ((2 : ℝ) ^ k)⁻¹ := by linarith [h.1, h.2]

lemma floor_near {a b : ℝ} (h : |a - b| < 1) : ⌊b⌋ - 1 ≤ ⌊a⌋ ∧ ⌊a⌋ ≤ ⌊b⌋ + 1 := by
  rw [abs_lt] at h
  constructor
  · have : ⌊b⌋ ≤ ⌊a + 1⌋ := Int.floor_le_floor (by linarith)
    rw [Int.floor_add_one] at this; linarith
  · have : ⌊a⌋ ≤ ⌊b + 1⌋ := Int.floor_le_floor (by linarith)
    rw [Int.floor_add_one] at this; linarith

/-- The `3 × 3` block of level-`k` indices around `B`. -/
def nbhd (B : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  Finset.Icc (B.1 - 1) (B.1 + 1) ×ˢ Finset.Icc (B.2 - 1) (B.2 + 1)

lemma card_nbhd (B : ℤ × ℤ) : (nbhd B).card = 9 := by
  simp only [nbhd, Finset.card_product, Int.card_Icc]
  have : B.1 + 1 + 1 - (B.1 - 1) = 3 := by ring
  have h2 : B.2 + 1 + 1 - (B.2 - 1) = 3 := by ring
  rw [this, h2]; rfl

lemma ball_subset {k : ℕ} (x : ℂ) {r : ℝ} (hr : r ≤ ((2 : ℝ) ^ k)⁻¹) :
    ball x r ⊆ ⋃ B ∈ nbhd (idx k x), D k B := by
  intro z hz
  rw [mem_ball, dist_eq_norm] at hz
  have hp : (0 : ℝ) < 2 ^ k := by positivity
  have hre : |z.re * 2 ^ k - x.re * 2 ^ k| < 1 := by
    rw [← sub_mul, abs_mul, abs_of_pos hp]
    have := (Complex.abs_re_le_norm (z - x)).trans_lt (hz.trans_le hr)
    rw [Complex.sub_re] at this
    rwa [lt_inv_iff_mul_lt₀ hp] at this
  have him : |z.im * 2 ^ k - x.im * 2 ^ k| < 1 := by
    rw [← sub_mul, abs_mul, abs_of_pos hp]
    have := (Complex.abs_im_le_norm (z - x)).trans_lt (hz.trans_le hr)
    rw [Complex.sub_im] at this
    rwa [lt_inv_iff_mul_lt₀ hp] at this
  simp only [mem_iUnion, exists_prop]
  refine ⟨idx k z, ?_, rfl⟩
  have h1 := floor_near hre
  have h2 := floor_near him
  simp only [nbhd, idx, Finset.mem_product, Finset.mem_Icc]
  exact ⟨h1, h2⟩

/-! ### Positivity of the dyadic content -/

lemma exists_content_pos {s : ℝ} (hs : 0 < s) {K : Set ℂ} (hK : μH[s] K ≠ 0) :
    ∃ c > 0, ∀ F : Finset (ℕ × (ℤ × ℤ)), K ⊆ (⋃ A ∈ F, D A.1 A.2) →
      c ≤ ∑ A ∈ F, θ s A.1 := by
  by_contra hcon
  push Not at hcon
  have hF : ∀ m : ℕ, ∃ F : Finset (ℕ × (ℤ × ℤ)), K ⊆ (⋃ A ∈ F, D A.1 A.2) ∧
      ∑ A ∈ F, θ s A.1 < 1 / ((m : ℝ) + 1) := fun m => hcon _ (by positivity)
  choose F hFK hFs using hF
  apply hK
  refine le_antisymm ?_ (zero_le _)
  -- covers by the squares of `F m`
  set r : ℕ → ℝ≥0∞ := fun m => ENNReal.ofReal (2 * (1 / ((m : ℝ) + 1)) ^ (1 / s)) with hr
  have hr0 : Tendsto r atTop (𝓝 0) := by
    have h1 : Tendsto (fun m : ℕ => 1 / ((m : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Tendsto (fun m : ℕ => 2 * (1 / ((m : ℝ) + 1)) ^ (1 / s)) atTop (𝓝 0) := by
      have := ((Real.continuousAt_rpow_const 0 (1 / s) (Or.inr (by positivity))).tendsto.comp
        h1).const_mul 2
      simpa [Real.zero_rpow (by positivity : (1 / s) ≠ 0)] using this
    simpa [hr] using (ENNReal.tendsto_ofReal h2)
  have hθ : ∀ m, ∀ A ∈ F m, ((2 : ℝ) ^ A.1)⁻¹ ≤ (1 / ((m : ℝ) + 1)) ^ (1 / s) := by
    intro m A hA
    have h1 : θ s A.1 ≤ 1 / ((m : ℝ) + 1) :=
      (Finset.single_le_sum (fun B _ => θ_nonneg s B.1) hA).trans (hFs m).le
    have h2 := Real.rpow_le_rpow (θ_nonneg s A.1) h1 (by positivity : 0 ≤ 1 / s)
    rwa [θ, ← Real.rpow_mul (by positivity), mul_one_div_cancel hs.ne', Real.rpow_one] at h2
  have key := hausdorffMeasure_le_liminf_sum (X := ℂ) s K r hr0
    (fun m (A : F m) => D A.1.1 A.1.2)
    (Eventually.of_forall fun m A => (ediam_D_le _ _).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (hθ m A.1 A.2) (by norm_num))))
    (Eventually.of_forall fun m z hz => by
      have := hFK m hz
      simp only [mem_iUnion, exists_prop] at this ⊢
      obtain ⟨A, hA, hzA⟩ := this
      exact ⟨⟨A, hA⟩, hzA⟩)
  refine key.trans (le_of_eq ?_)
  -- the sums tend to zero
  have hsum : ∀ m, ∑ A : F m, EMetric.diam (D A.1.1 A.1.2) ^ s ≤
      ENNReal.ofReal (2 ^ s * (1 / ((m : ℝ) + 1))) := by
    intro m
    calc ∑ A : F m, EMetric.diam (D A.1.1 A.1.2) ^ s
        ≤ ∑ A : F m, ENNReal.ofReal (2 ^ s * θ s A.1.1) := by
          refine Finset.sum_le_sum fun A _ => ?_
          refine (ENNReal.rpow_le_rpow (ediam_D_le _ _) hs.le).trans_eq ?_
          rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hs.le, θ,
            Real.mul_rpow (by norm_num) (by positivity)]
      _ = ENNReal.ofReal (2 ^ s * ∑ A : F m, θ s A.1.1) := by
          rw [← ENNReal.ofReal_sum_of_nonneg (fun A _ => by
            have := θ_nonneg s A.1.1; positivity), Finset.mul_sum]
      _ ≤ ENNReal.ofReal (2 ^ s * (1 / ((m : ℝ) + 1))) := by
          refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
          rw [Finset.sum_coe_sort (F m) (fun A => θ s A.1)]
          exact (hFs m).le
  have hlim : Tendsto (fun m : ℕ => ENNReal.ofReal (2 ^ s * (1 / ((m : ℝ) + 1)))) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ((2 : ℝ) ^ s))
    rw [mul_zero] at this
    simpa using ENNReal.tendsto_ofReal this
  refine le_antisymm ?_ (zero_le _)
  calc liminf (fun m => ∑ A : F m, EMetric.diam (D A.1.1 A.1.2) ^ s) atTop
      ≤ liminf (fun m : ℕ => ENNReal.ofReal (2 ^ s * (1 / ((m : ℝ) + 1)))) atTop :=
        liminf_le_liminf (Eventually.of_forall hsum)
    _ = 0 := hlim.liminf_eq

/-! ### The level-`n` measures -/

lemma finite_idx_image {K : Set ℂ} (hK : IsCompact K) (n : ℕ) : (idx n '' K).Finite := by
  obtain ⟨R, hR⟩ := hK.isBounded.exists_norm_le
  have hp : (0 : ℝ) < 2 ^ n := by positivity
  refine ((Set.finite_Icc (⌊-R * 2 ^ n⌋) ⌊R * 2 ^ n⌋).prod
    (Set.finite_Icc (⌊-R * 2 ^ n⌋) ⌊R * 2 ^ n⌋)).subset ?_
  rintro _ ⟨z, hz, rfl⟩
  have h := hR z hz
  have hre := (Complex.abs_re_le_norm z).trans h
  have him := (Complex.abs_im_le_norm z).trans h
  rw [abs_le] at hre him
  simp only [idx, Set.mem_prod, Set.mem_Icc]
  refine ⟨⟨Int.floor_le_floor ?_, Int.floor_le_floor ?_⟩, ⟨Int.floor_le_floor ?_,
    Int.floor_le_floor ?_⟩⟩ <;> nlinarith

lemma exists_level_measure {K : Set ℂ} (hK : IsCompact K) {s c : ℝ} (hs : 0 < s)
    (hc : ∀ F : Finset (ℕ × (ℤ × ℤ)), K ⊆ (⋃ A ∈ F, D A.1 A.2) → c ≤ ∑ A ∈ F, θ s A.1)
    (n : ℕ) :
    ∃ ν : Measure ℂ, ν univ ≠ ⊤ ∧ ν Kᶜ = 0 ∧ ENNReal.ofReal c ≤ ν univ ∧
      ∀ k ≤ n, ∀ B, ν (D k B) ≤ ENNReal.ofReal (θ s k) := by
  classical
  set S : Finset (ℤ × ℤ) := (finite_idx_image hK n).toFinset with hS
  have hmemS : ∀ A, A ∈ S ↔ ∃ z ∈ K, idx n z = A := fun A => by
    rw [hS, Set.Finite.mem_toFinset]; rfl
  -- a point of `K` in each square
  have hpt : ∀ a : S, ∃ z ∈ K, idx n z = a.1 := fun a => (hmemS a.1).1 a.2
  choose pt hptK hptidx using hpt
  -- constraint sums
  set cs : (S → ℝ) → ℕ → ℤ × ℤ → ℝ := fun w k B =>
    ∑ a : S, if idx k (pt a) = B then w a else 0 with hcs
  set P : Set (S → ℝ) := (⋂ a : S, {w | 0 ≤ w a}) ∩
    ⋂ k ∈ Finset.range (n + 1), ⋂ B : ℤ × ℤ, {w | cs w k B ≤ θ s k} with hP
  have hmemP : ∀ w, w ∈ P ↔ (∀ a, 0 ≤ w a) ∧ ∀ k ≤ n, ∀ B, cs w k B ≤ θ s k := by
    intro w
    simp only [hP, mem_inter_iff, mem_iInter, mem_setOf_eq, Finset.mem_range]
    exact and_congr Iff.rfl ⟨fun h k hk B => h k (by omega) B, fun h k hk B => h k (by omega) B⟩
  have hcs_cont : ∀ k B, Continuous fun w : S → ℝ => cs w k B := fun k B => by
    simp only [hcs]
    exact continuous_finset_sum _ fun a _ => by
      split_ifs
      · exact continuous_apply a
      · exact continuous_const
  have hPc : IsClosed P := by
    refine (isClosed_iInter fun a => isClosed_le continuous_const (continuous_apply a)).inter
      (isClosed_biInter fun k _ => isClosed_iInter fun B =>
        isClosed_le (hcs_cont k B) continuous_const)
  have hwle : ∀ w ∈ P, ∀ a, w a ≤ 1 := by
    intro w hw a
    have h := ((hmemP w).1 hw).2 n le_rfl (idx n (pt a))
    have h1 : w a ≤ cs w n (idx n (pt a)) := by
      simp only [hcs]
      refine le_trans (le_of_eq (if_pos rfl).symm) (Finset.single_le_sum (f := fun a' : S =>
        if idx n (pt a') = idx n (pt a) then w a' else 0) (fun a' _ => ?_) (Finset.mem_univ a))
      split_ifs
      · exact ((hmemP w).1 hw).1 a'
      · exact le_rfl
    linarith [θ_le_one hs.le n]
  have hPb : Bornology.IsBounded P := by
    refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, fun w hw => ?_⟩
    rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro a
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [((hmemP w).1 hw).1 a], hwle w hw a⟩
  have hP0 : (0 : S → ℝ) ∈ P := by
    rw [hmemP]
    refine ⟨fun a => le_rfl, fun k _ B => ?_⟩
    simp only [hcs, Pi.zero_apply, ite_self, Finset.sum_const_zero]
    exact θ_nonneg s k
  obtain ⟨w, hwP, hmax⟩ := (Metric.isCompact_of_isClosed_isBounded hPc hPb).exists_isMaxOn
    ⟨0, hP0⟩ (continuous_finset_sum _ fun a _ => continuous_apply a).continuousOn
  obtain ⟨hw0, hwc⟩ := (hmemP w).1 hwP
  -- saturation
  have hsat : ∀ a : S, ∃ k, k ≤ n ∧ cs w k (idx k (pt a)) = θ s k := by
    intro a
    by_contra hcon
    push Not at hcon
    have hslack : ∀ k ∈ Finset.range (n + 1), 0 < θ s k - cs w k (idx k (pt a)) := by
      intro k hk
      have hk' : k ≤ n := by simpa [Nat.lt_succ_iff] using hk
      exact sub_pos.2 (lt_of_le_of_ne (hwc k hk' _) (hcon k hk'))
    set δ := (Finset.range (n + 1)).inf' ⟨0, by simp⟩
      (fun k => θ s k - cs w k (idx k (pt a))) with hδ
    have hδ0 : 0 < δ := (Finset.lt_inf'_iff _).2 hslack
    have hδle : ∀ k ≤ n, δ ≤ θ s k - cs w k (idx k (pt a)) := fun k hk =>
      Finset.inf'_le _ (by simp [Nat.lt_succ_iff, hk])
    set w' : S → ℝ := fun a' => w a' + if a' = a then δ else 0 with hw'
    have hcs' : ∀ k B, cs w' k B = cs w k B + if idx k (pt a) = B then δ else 0 := by
      intro k B
      simp only [hcs, hw']
      rw [← Finset.sum_ite_eq' Finset.univ a (fun a' => if idx k (pt a') = B then δ else 0),
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a' _ => ?_
      by_cases h1 : a' = a
      · subst h1; split_ifs <;> simp
      · simp [h1]
    have hw'P : w' ∈ P := by
      rw [hmemP]
      refine ⟨fun a' => ?_, fun k hk B => ?_⟩
      · simp only [hw']; split_ifs <;> linarith [hw0 a']
      · rw [hcs']
        split_ifs with hB
        · subst hB; linarith [hδle k hk]
        · linarith [hwc k hk B]
    have h1 := hmax hw'P
    simp only [hw', Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
    linarith
  -- the minimal saturated level
  set kmin : S → ℕ := fun a => Nat.find (hsat a) with hkmin
  have hkmin_spec : ∀ a, kmin a ≤ n ∧ cs w (kmin a) (idx (kmin a) (pt a)) = θ s (kmin a) :=
    fun a => Nat.find_spec (hsat a)
  have hkmin_min : ∀ a k, k ≤ n → cs w k (idx k (pt a)) = θ s k → kmin a ≤ k :=
    fun a k hk h => Nat.find_min' (hsat a) ⟨hk, h⟩
  set φ : S → ℕ × (ℤ × ℤ) := fun a => (kmin a, idx (kmin a) (pt a)) with hφ
  set F : Finset (ℕ × (ℤ × ℤ)) := Finset.univ.image φ with hF
  -- `F` covers `K`
  have hFK : K ⊆ ⋃ A ∈ F, D A.1 A.2 := by
    intro z hz
    have hzS : idx n z ∈ S := (hmemS _).2 ⟨z, hz, rfl⟩
    set a : S := ⟨idx n z, hzS⟩
    simp only [mem_iUnion, exists_prop]
    refine ⟨φ a, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    show idx (kmin a) z = idx (kmin a) (pt a)
    exact idx_eq_of_idx_eq (hkmin_spec a).1 (by rw [hptidx]; rfl)
  -- the fibres of `φ`
  have hfib : ∀ A ∈ F, ∀ a : S, φ a = A ↔ idx A.1 (pt a) = A.2 := by
    intro A hA a
    obtain ⟨a₀, -, rfl⟩ := Finset.mem_image.1 hA
    simp only [hφ, Prod.mk.injEq]
    constructor
    · rintro ⟨h1, h2⟩; rw [← h1, h2]
    · intro h
      have hk0 := hkmin_spec a₀
      -- `a` is saturated at level `kmin a₀`
      have hsat_a : cs w (kmin a₀) (idx (kmin a₀) (pt a)) = θ s (kmin a₀) := by rw [h]; exact hk0.2
      have hle : kmin a ≤ kmin a₀ := hkmin_min a _ hk0.1 hsat_a
      have hge : kmin a₀ ≤ kmin a := by
        refine hkmin_min a₀ _ ((hle.trans hk0.1)) ?_
        have he : idx (kmin a) (pt a₀) = idx (kmin a) (pt a) := idx_eq_of_idx_eq hle h.symm
        rw [he]; exact (hkmin_spec a).2
      have heq : kmin a = kmin a₀ := le_antisymm hle hge
      exact ⟨heq, by rw [heq, h]⟩
  have htotal : ∑ a : S, w a = ∑ A ∈ F, θ s A.1 := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := F) (g := φ)
      (fun a _ => Finset.mem_image_of_mem _ (Finset.mem_univ _))]
    refine Finset.sum_congr rfl fun A hA => ?_
    obtain ⟨a₀, -, rfl⟩ := Finset.mem_image.1 hA
    rw [Finset.sum_filter, ← (hkmin_spec a₀).2]
    refine Finset.sum_congr rfl fun a _ => ?_
    exact if_congr (hfib _ hA a) rfl rfl
  -- the measure
  refine ⟨∑ a : S, ENNReal.ofReal (w a) • Measure.dirac (pt a), ?_, ?_, ?_, ?_⟩
  · rw [Measure.finsetSum_apply]
    exact (ENNReal.sum_lt_top.2 fun a _ => by simp).ne
  · rw [Measure.finsetSum_apply]
    refine Finset.sum_eq_zero fun a _ => ?_
    rw [Measure.smul_apply, Measure.dirac_apply' _ hK.isClosed.measurableSet.compl,
      Set.indicator_of_notMem (by simpa using hptK a), smul_zero]
  · rw [Measure.finsetSum_apply]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hw0 a), htotal]
    exact ENNReal.ofReal_le_ofReal (hc F hFK)
  · intro k hk B
    rw [Measure.finsetSum_apply]
    have : ∀ a : S, (ENNReal.ofReal (w a) • Measure.dirac (pt a)) (D k B) =
        ENNReal.ofReal (if idx k (pt a) = B then w a else 0) := by
      intro a
      rw [Measure.smul_apply, Measure.dirac_apply' _ (measurableSet_D k B), smul_eq_mul]
      by_cases h : idx k (pt a) = B
      · rw [Set.indicator_of_mem (show pt a ∈ D k B from h), if_pos h]; simp
      · rw [Set.indicator_of_notMem (show pt a ∉ D k B from h), if_neg h]; simp
    simp_rw [this]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => by split_ifs <;> simp [hw0 a])]
    exact ENNReal.ofReal_le_ofReal (hwc k hk B)

/-! ### Frostman's lemma -/

lemma exists_pow_near {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    ∃ k : ℕ, r ≤ ((2 : ℝ) ^ k)⁻¹ ∧ ((2 : ℝ) ^ k)⁻¹ ≤ 2 * r := by
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near (one_le_one_div hr hr1) (by norm_num : (1 : ℝ) < 2)
  refine ⟨k, ?_, ?_⟩
  · rw [le_inv_comm₀ hr (by positivity), ← one_div]; exact hk1
  · rw [pow_succ] at hk2
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    rw [one_div, inv_lt_iff_one_lt_mul₀ hr] at hk2
    nlinarith

lemma measure_ball_le {ν : Measure ℂ} {s : ℝ} {n k : ℕ} (hk : k ≤ n)
    (hD : ∀ k ≤ n, ∀ B, ν (D k B) ≤ ENNReal.ofReal (θ s k)) (x : ℂ) {r : ℝ}
    (hr : r ≤ ((2 : ℝ) ^ k)⁻¹) : ν (ball x r) ≤ 9 * ENNReal.ofReal (θ s k) := by
  calc ν (ball x r) ≤ ν (⋃ B ∈ nbhd (idx k x), D k B) := measure_mono (ball_subset x hr)
    _ ≤ ∑ B ∈ nbhd (idx k x), ν (D k B) := measure_biUnion_finset_le _ _
    _ ≤ ∑ B ∈ nbhd (idx k x), ENNReal.ofReal (θ s k) := Finset.sum_le_sum fun B _ => hD k hk B
    _ = 9 * ENNReal.ofReal (θ s k) := by rw [Finset.sum_const, card_nbhd, nsmul_eq_mul]; rfl

/-- **Frostman's lemma**. -/
theorem exists_frostman {K : Set ℂ} (hK : IsCompact K) {s : ℝ} (hs : 0 < s)
    (hH : μH[s] K ≠ 0) :
    ∃ p : Measure ℂ, p ∈ M1 K ∧ ∃ C : ℝ, 0 < C ∧
      ∀ x : ℂ, ∀ r : ℝ, 0 < r → p (ball x r) ≤ ENNReal.ofReal (C * r ^ s) := by
  obtain ⟨c, hc0, hc⟩ := exists_content_pos hs hH
  have hlev := fun n => exists_level_measure hK hs hc n
  choose ν hνfin hνK hνc hνD using hlev
  have hνpos : ∀ n, ν n univ ≠ 0 := fun n =>
    ((ENNReal.ofReal_pos.2 hc0).trans_le (hνc n)).ne'
  -- normalized measures
  set p : ℕ → Measure ℂ := fun n => (ν n univ)⁻¹ • ν n with hp
  have hpM1 : ∀ n, p n ∈ M1 K := by
    intro n
    refine ⟨⟨?_⟩, ?_⟩
    · simp only [hp, Measure.smul_apply, smul_eq_mul]
      exact ENNReal.inv_mul_cancel (hνpos n) (hνfin n)
    · simp only [hp, Measure.smul_apply, hνK n, smul_eq_mul, mul_zero]
  have hpball : ∀ n k, k ≤ n → ∀ x : ℂ, ∀ r : ℝ, 0 < r → r ≤ ((2 : ℝ) ^ k)⁻¹ →
      ((2 : ℝ) ^ k)⁻¹ ≤ 2 * r →
      p n (ball x r) ≤ ENNReal.ofReal (9 * 2 ^ s / c * r ^ s) := by
    intro n k hk x r hr hr1 hr2
    simp only [hp, Measure.smul_apply, smul_eq_mul]
    have h1 := measure_ball_le hk (hνD n) x hr1
    have hθ : θ s k ≤ 2 ^ s * r ^ s := by
      rw [θ, ← Real.mul_rpow (by norm_num) hr.le]
      exact Real.rpow_le_rpow (by positivity) hr2 hs.le
    have hinv : (ν n univ)⁻¹ ≤ ENNReal.ofReal c⁻¹ := by
      rw [ENNReal.ofReal_inv_of_pos hc0]
      exact ENNReal.inv_le_inv.2 (hνc n)
    calc (ν n univ)⁻¹ * ν n (ball x r) ≤ ENNReal.ofReal c⁻¹ * (9 * ENNReal.ofReal (θ s k)) :=
          mul_le_mul' hinv h1
      _ = ENNReal.ofReal (c⁻¹ * (9 * θ s k)) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_ofNat]
      _ ≤ ENNReal.ofReal (9 * 2 ^ s / c * r ^ s) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [div_eq_mul_inv]
          have := mul_le_mul_of_nonneg_left hθ (by positivity : (0 : ℝ) ≤ c⁻¹ * 9)
          nlinarith
  -- pass to a weak limit
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have hq := fun n => exists_map_val_eq hK (hpM1 n)
  choose q hq using hq
  obtain ⟨q₀, φ, hφ, hlim⟩ := CompactSpace.tendsto_subseq q
  refine ⟨(q₀ : Measure K).map ((↑) : K → ℂ), map_val_mem_M1 hK q₀,
    max (9 * 2 ^ s / c) 1, lt_max_of_lt_right one_pos, fun x r hr => ?_⟩
  have hmap : ∀ (m : Measure K), m.map ((↑) : K → ℂ) (ball x r) =
      m (((↑) : K → ℂ) ⁻¹' ball x r) :=
    fun m => Measure.map_apply measurable_subtype_coe measurableSet_ball
  rcases le_or_gt r 1 with hr1 | hr1
  · obtain ⟨k, hk1, hk2⟩ := exists_pow_near hr hr1
    have hopen : IsOpen (((↑) : K → ℂ) ⁻¹' ball x r) :=
      isOpen_ball.preimage continuous_subtype_val
    have hle := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hopen
    have hev : ∀ᶠ m in atTop, ((q (φ m) : ProbabilityMeasure K) : Measure K)
        (((↑) : K → ℂ) ⁻¹' ball x r) ≤ ENNReal.ofReal (9 * 2 ^ s / c * r ^ s) := by
      filter_upwards [eventually_ge_atTop k] with m hm
      rw [← hmap, hq]
      exact hpball (φ m) k (hm.trans (hφ.id_le m)) x r hr hk1 hk2
    rw [hmap]
    calc ((q₀ : ProbabilityMeasure K) : Measure K) (((↑) : K → ℂ) ⁻¹' ball x r)
        ≤ _ := hle
      _ ≤ ENNReal.ofReal (9 * 2 ^ s / c * r ^ s) :=
          Filter.liminf_le_of_frequently_le' hev.frequently
      _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _)
          (Real.rpow_nonneg hr.le _))
  · rw [hmap]
    refine (prob_le_one).trans ?_
    rw [ENNReal.one_le_ofReal]
    calc (1 : ℝ) ≤ 1 * r ^ s := by rw [one_mul]; exact Real.one_le_rpow hr1.le hs.le
      _ ≤ max (9 * 2 ^ s / c) 1 * r ^ s :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hr.le _)

/-! ### Finite energy -/

/-- A probability measure with `p(B(x, r)) ≤ C r^s` has truncated energies at most `C / s`. -/
lemma Itr_le_of_ball_le {K : Set ℂ} (hK : IsCompact K) {p : Measure ℂ} (hp : p ∈ M1 K)
    {s C : ℝ} (hs : 0 < s) (hC : 0 < C)
    (hball : ∀ x : ℂ, ∀ r : ℝ, 0 < r → p (ball x r) ≤ ENNReal.ofReal (C * r ^ s)) (N : ℕ) :
    Itr N p p ≤ C / s := by
  have := hp.1
  have hpa := adm_of_M1 hK hp
  have hinner : ∀ z : ℂ, ∫ w, logKer N (z - w) ∂p ≤ C / s := by
    intro z
    have hf := integrable_logKer hpa.2 N z
    set g : ℂ → ℝ := fun w => max (logKer N (z - w)) 0 with hg
    have hgi : Integrable g p := hf.pos_part
    have hgm : Measurable g :=
      ((continuous_logKer N).comp (continuous_const.sub continuous_id)).measurable.max
        measurable_const
    have h1 : ∫ w, logKer N (z - w) ∂p ≤ ∫ w, g w ∂p :=
      integral_mono hf hgi fun w => le_max_left _ _
    refine h1.trans ?_
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun w => le_max_right _ _)
      hgi.aestronglyMeasurable]
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    rw [lintegral_eq_lintegral_meas_lt p (Eventually.of_forall fun w => le_max_right _ _)
      hgm.aemeasurable]
    have hset : ∀ t ∈ Ioi (0 : ℝ), p {w | t < g w} ≤ ENNReal.ofReal (C * rexp (-s * t)) := by
      intro t ht
      have ht' : 0 < t := ht
      refine (measure_mono fun w hw => ?_).trans
        ((hball z (rexp (-t)) (Real.exp_pos _)).trans_eq ?_)
      · simp only [mem_setOf_eq, hg] at hw
        have hlk : t < logKer N (z - w) := by
          rcases le_or_gt (logKer N (z - w)) 0 with h | h
          · rw [max_eq_right h] at hw; linarith
          · rwa [max_eq_left h.le] at hw
        unfold logKer at hlk
        have hpos := max_norm_exp_pos N (z - w)
        have hlt : Real.log (max ‖z - w‖ (rexp (-(N : ℝ)))) < -t := by linarith
        rw [Real.log_lt_iff_lt_exp hpos] at hlt
        rw [mem_ball, dist_comm, dist_eq_norm]
        exact (le_max_left _ _).trans_lt hlt
      · rw [← Real.exp_mul]
        congr 3
        ring
    calc ∫⁻ t in Ioi 0, p {w | t < g w}
        ≤ ∫⁻ t in Ioi 0, ENNReal.ofReal (C * rexp (-s * t)) :=
          setLIntegral_mono' measurableSet_Ioi hset
      _ = ENNReal.ofReal (∫ t in Ioi 0, C * rexp (-s * t)) := by
          rw [ofReal_integral_eq_lintegral_ofReal
            ((exp_neg_integrableOn_Ioi 0 hs).const_mul C)
            (Eventually.of_forall fun t => by positivity)]
      _ = ENNReal.ofReal (C / s) := by
          rw [integral_const_mul, integral_exp_mul_Ioi (by linarith : -s < 0) 0]
          congr 1
          rw [mul_zero, Real.exp_zero, neg_div_neg_eq, mul_one_div]
  calc Itr N p p = ∫ z, ∫ w, logKer N (z - w) ∂p ∂p := rfl
    _ ≤ ∫ _z, C / s ∂p :=
        integral_mono (integrable_potTrunc_wrt hpa hpa N) (integrable_const _) hinner
    _ = C / s := by simp

end Frostman

open Frostman in
/-- **Theorem A.2.11**: compact sets of capacity zero have Hausdorff dimension zero. -/
theorem capacityZeroDimStatement_holds : CapacityZeroDimStatement := by
  intro K hK hcap
  by_contra hne
  obtain ⟨s, hs0, hs⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 (pos_iff_ne_zero.2 hne)
  have hs0' : (0 : ℝ) < s := by
    have : (0 : ℝ≥0) < s := by exact_mod_cast hs0
    exact_mod_cast this
  have hH : μH[(s : ℝ)] K ≠ 0 := by
    rw [hausdorffMeasure_of_lt_dimH hs]; exact ENNReal.top_ne_zero
  obtain ⟨p, hp, C, hC, hball⟩ := exists_frostman hK hs0' hH
  have hE : energy p ≤ ((C / s : ℝ) : EReal) := by
    rw [energy_eq_iSup_Itr]
    exact iSup_le fun N => EReal.coe_le_coe_iff.2 (Itr_le_of_ball_le hK hp hs0' hC hball N)
  have htop : energy p ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hE
  have hpos : expNeg (energy p) ≠ 0 := by
    simp [expNeg, htop, energy_ne_bot p, Real.exp_pos]
  exact hpos (le_antisymm ((expNeg_energy_le_capCompact hp).trans hcap.le) (zero_le _))

end DF
