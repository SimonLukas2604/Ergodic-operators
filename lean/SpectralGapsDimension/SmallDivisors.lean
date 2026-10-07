/-
Copyright (c) 2026. Formalization of
  S. Becker, "Self-dual perturbations of the critical almost Mathieu operator:
  Dry Ten Martini and Hausdorff dimension" (Paper II).

# Small divisors and scalar iteration lemmas of §4.1 (Brjuno part)

This file formalizes the elementary arithmetic and scalar lemmas of
§4.1 ("Singular preparation and covers at Brjuno frequencies"), lines 3355–4500 of
`spectral_gaps_and_dimension.tex`:

* `bezout_identity` — the trigonometric Bezout identity `(dim:br:bezout)` (l. 3724);
* `nint`, `Psi`, `brjunoIntegral` — `‖t‖_𝕋`, `Ψ(N) = max_{1≤m≤N} ‖mα‖⁻¹`,
  `𝔟 = ∫₁^∞ log Ψ(⌊t⌋) / t² dt` (l. 3560–3565);
* `divisor_sum_le`, `divisor_product` — Lemma `dim:br:divisor-product` (l. 3575–3634),
  both the "more precisely" form and the product estimate `(dim:br:product-estimate)`,
  proved by the paper's layer-cake argument;
* `inverse_cutoffs` — Lemma `dim:br:inverse-cutoffs` (l. 4032–4064);
* `scalar_iteration` — the induction behind `(dim:br:geometric-convergence)` (l. 4140–4170);
* `energy_cauchy_sum` — the Cauchy-coefficient sum `(dim:br:energy-smallness)` (l. 4228);
* `divisor_square_sum` — the divisor-square bound `(dim:br:divisor-square)` (l. 4398–4419).
-/
import Mathlib

noncomputable section

open scoped ENNReal
open MeasureTheory Set Filter Topology Real

namespace SGD
namespace SmallDivisors

/-! ### The trigonometric Bezout identity -/

/-- **Identity `(dim:br:bezout)` (l. 3724)** in the proof of Lemma `dim:br:finite-division`.
With `c = 2 cos(φ) g` (the factorized hopping coefficient `c = c_η g` at the phase `x`) and
`c' = 2 cos(φ + δ) g'` (the same at the shifted phase `x + mα_ch`, so that the cosine argument
is `φ + δ_m`), one has, whenever `sin δ ≠ 0` and `g, g' ≠ 0`,
`c · sin(φ+δ) / (2 g sin δ) − c' · sin φ / (2 g' sin δ) = 1`. -/
theorem bezout_identity (φ δ g g' : ℂ) (hδ : Complex.sin δ ≠ 0) (hg : g ≠ 0) (hg' : g' ≠ 0) :
    (2 * Complex.cos φ * g) * Complex.sin (φ + δ) / (2 * g * Complex.sin δ)
      - (2 * Complex.cos (φ + δ) * g') * Complex.sin φ / (2 * g' * Complex.sin δ) = 1 := by
  have key : Complex.sin (φ + δ) * Complex.cos φ - Complex.cos (φ + δ) * Complex.sin φ
      = Complex.sin δ := by
    rw [← Complex.sin_sub]; ring_nf
  have h1 : (2 * g * Complex.sin δ) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero two_ne_zero hg) hδ
  have h2 : (2 * g' * Complex.sin δ) ≠ 0 := by
    apply mul_ne_zero (mul_ne_zero two_ne_zero hg') hδ
  rw [div_sub_div _ _ h1 h2, div_eq_one_iff_eq (mul_ne_zero h1 h2)]
  linear_combination (4 * g * g' * Complex.sin δ) * key

/-! ### Distance to the nearest integer -/

/-- The distance `‖t‖_𝕋` from `t` to the nearest integer (l. 3561). -/
def nint (t : ℝ) : ℝ := |t - round t|

lemma nint_nonneg (t : ℝ) : 0 ≤ nint t := abs_nonneg _

lemma nint_le_half (t : ℝ) : nint t ≤ 1 / 2 := abs_sub_round t

/-- `‖t‖_𝕋 ≤ |t - z|` for every integer `z`. -/
lemma nint_le (t : ℝ) (z : ℤ) : nint t ≤ |t - z| := round_le t z

/-- Subadditivity of `‖·‖_𝕋`. -/
lemma nint_add_le (x y : ℝ) : nint (x + y) ≤ nint x + nint y := by
  calc nint (x + y) ≤ |x + y - ((round x + round y : ℤ) : ℝ)| := nint_le _ _
    _ = |(x - round x) + (y - round y)| := by push_cast; ring_nf
    _ ≤ nint x + nint y := abs_add_le _ _

lemma nint_neg (x : ℝ) : nint (-x) = nint x := by
  apply le_antisymm
  · calc nint (-x) ≤ |-x - ((-round x : ℤ) : ℝ)| := nint_le _ _
      _ = nint x := by
        unfold nint; push_cast
        rw [show -x - -(round x : ℝ) = -(x - round x) by ring, abs_neg]
  · calc nint x ≤ |x - ((-round (-x) : ℤ) : ℝ)| := nint_le _ _
      _ = nint (-x) := by
        unfold nint; push_cast
        rw [show x - -(round (-x) : ℝ) = -(-x - round (-x)) by ring, abs_neg]

lemma nint_sub_le (x y : ℝ) : nint (x - y) ≤ nint x + nint y := by
  have := nint_add_le x (-y)
  rwa [nint_neg, ← sub_eq_add_neg] at this

/-- Jordan's inequality in the form `|sin πt| ≥ 2‖t‖_𝕋` used throughout §4.1. -/
lemma two_mul_nint_le_abs_sin (t : ℝ) : 2 * nint t ≤ |Real.sin (π * t)| := by
  set s := t - round t with hs
  have hnint : nint t = |s| := rfl
  have hsin : Real.sin (π * t) = (-1 : ℝ) ^ (round t) * Real.sin (π * s) := by
    rw [← Real.sin_add_int_mul_pi]; congr 1; rw [hs]; ring
  have habs : |Real.sin (π * t)| = |Real.sin (π * s)| := by
    rw [hsin, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
  have hs2 : |s| ≤ 1 / 2 := abs_sub_round t
  rw [habs, hnint]
  rcases le_total 0 s with h | h
  · rw [abs_of_nonneg h] at hs2 ⊢
    have := Real.mul_le_sin (x := π * s) (mul_nonneg Real.pi_pos.le h)
      (by nlinarith [Real.pi_pos])
    have e : 2 / π * (π * s) = 2 * s := by field_simp
    rw [abs_of_nonneg (by linarith)]
    linarith
  · rw [abs_of_nonpos h] at hs2 ⊢
    have := Real.mul_le_sin (x := π * (-s)) (mul_nonneg Real.pi_pos.le (by linarith))
      (by nlinarith [Real.pi_pos])
    have e : 2 / π * (π * (-s)) = 2 * (-s) := by field_simp
    have e2 : Real.sin (π * s) = - Real.sin (π * (-s)) := by
      rw [mul_neg, Real.sin_neg, neg_neg]
    rw [e2, abs_neg, abs_of_nonneg (by linarith)]
    linarith

/-- For irrational `α` and `m ≥ 1`, `‖mα‖_𝕋 > 0`. -/
lemma nint_pos_of_irrational {α : ℝ} (hα : Irrational α) {m : ℕ} (hm : m ≠ 0) :
    0 < nint (m * α) := by
  unfold nint
  rw [abs_pos, sub_ne_zero]
  exact (hα.natCast_mul hm).ne_int _

lemma abs_sin_pos_of_irrational {α : ℝ} (hα : Irrational α) {m : ℕ} (hm : m ≠ 0) :
    0 < |Real.sin (π * (m * α))| :=
  lt_of_lt_of_le (by linarith [nint_pos_of_irrational hα hm]) (two_mul_nint_le_abs_sin _)

/-! ### The arithmetic functions `Ψ` and `𝔟` -/

/-- `Ψ(N) = max_{1 ≤ m ≤ N} ‖mα‖_𝕋⁻¹` (l. 3560). (For `N = 0` the value is the junk value `0`;
the paper only uses `N ≥ 1`.) -/
def Psi (α : ℝ) (N : ℕ) : ℝ :=
  (((Finset.Icc 1 N).sup fun m : ℕ => Real.toNNReal (nint (m * α))⁻¹ : NNReal) : ℝ)

lemma inv_nint_le_Psi (α : ℝ) {m N : ℕ} (h1 : 1 ≤ m) (hN : m ≤ N) :
    (nint (m * α))⁻¹ ≤ Psi α N := by
  unfold Psi
  calc (nint (m * α))⁻¹ ≤ (Real.toNNReal (nint (m * α))⁻¹ : ℝ) := Real.le_coe_toNNReal _
    _ ≤ _ := NNReal.coe_le_coe.2
        (Finset.le_sup (f := fun m : ℕ => Real.toNNReal (nint (m * α))⁻¹)
          (Finset.mem_Icc.2 ⟨h1, hN⟩))

/-- The Brjuno integral `𝔟 = ∫₁^∞ log Ψ(⌊t⌋) / t² dt` (l. 3561), as a lower Lebesgue integral
in `[0, ∞]` (the integrand is nonnegative since `Ψ ≥ 2`); the paper's hypothesis is `𝔟 < ∞`. -/
def brjunoIntegral (α : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (Real.log (Psi α ⌊t⌋₊) / t ^ 2)

/-! ### Layer-cake tools -/

/-- `∫_c^∞ dt / t² = 1 / c`. -/
lemma lintegral_Ioi_inv_sq {c : ℝ} (hc : 0 < c) :
    ∫⁻ t in Ioi c, ENNReal.ofReal (1 / t ^ 2) = ENNReal.ofReal (1 / c) := by
  have hcongr : EqOn (fun t : ℝ => ENNReal.ofReal (1 / t ^ 2))
      (fun t : ℝ => ENNReal.ofReal (t ^ (-2 : ℝ))) (Ioi c) := by
    intro t ht
    have ht0 : 0 < t := lt_trans hc ht
    simp only
    rw [Real.rpow_neg ht0.le, Real.rpow_two, one_div]
  rw [setLIntegral_congr_fun measurableSet_Ioi hcongr]
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt (by norm_num) hc)]
  · rw [integral_Ioi_rpow_of_lt (by norm_num) hc]
    congr 1
    rw [show (-2 : ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one, neg_div_neg_eq, div_one, one_div]
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (lt_trans hc ht).le _

/-- If `P` contains `(c, ∞)` with `c ≥ 1`, then `1/c ≤ ∫₁^∞ 1_P(t) dt/t²`. -/
lemma ofReal_inv_le_lintegral_indicator {c : ℝ} (hc : 1 ≤ c) (P : Set ℝ)
    (hP : ∀ t, c < t → t ∈ P) :
    ENNReal.ofReal (1 / c) ≤
      ∫⁻ t in Ioi (1 : ℝ), P.indicator (fun t => ENNReal.ofReal (1 / t ^ 2)) t := by
  rw [← lintegral_Ioi_inv_sq (by linarith : (0 : ℝ) < c)]
  calc ∫⁻ t in Ioi c, ENNReal.ofReal (1 / t ^ 2)
        = ∫⁻ t in Ioi c, P.indicator (fun t => ENNReal.ofReal (1 / t ^ 2)) t :=
          setLIntegral_congr_fun measurableSet_Ioi
            (fun t ht => (Set.indicator_of_mem (hP t ht) (fun t => ENNReal.ofReal (1 / t ^ 2))).symm)
    _ ≤ _ := lintegral_mono_set (Ioi_subset_Ioi hc)

/-- Layer-cake / Tonelli: `∫_a^∞ ∫₁^∞ 1_{u < L(t)} dt/t² du = ∫₁^∞ (L(t) - a)₊ / t² dt`. -/
lemma lintegral_layer {L : ℝ → ℝ} (hL : Measurable L) (a : ℝ) :
    ∫⁻ u in Ioi a, ∫⁻ t in Ioi (1 : ℝ),
        {t | u < L t}.indicator (fun t => ENNReal.ofReal (1 / t ^ 2)) t
      = ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal ((L t - a) / t ^ 2) := by
  rw [lintegral_lintegral_swap]
  · refine lintegral_congr fun t => ?_
    have : ∀ u, {t | u < L t}.indicator (fun t => ENNReal.ofReal (1 / t ^ 2)) t
        = (Iio (L t)).indicator (fun _ => ENNReal.ofReal (1 / t ^ 2)) u := by
      intro u; simp only [Set.indicator, Set.mem_ofPred_eq, Set.mem_Iio]
    simp_rw [this]
    rw [lintegral_indicator_const measurableSet_Iio, Measure.restrict_apply measurableSet_Iio,
      Set.inter_comm, Set.Ioi_inter_Iio, Real.volume_Ioo,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1; ring
  · apply Measurable.aemeasurable
    have hS : MeasurableSet {p : ℝ × ℝ | p.1 < L p.2} :=
      measurableSet_lt measurable_fst (hL.comp measurable_snd)
    have hg : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (1 / p.2 ^ 2) :=
      ENNReal.measurable_ofReal.comp ((measurable_snd.pow_const 2).const_div 1)
    convert hg.indicator hS using 1
    funext p
    simp [Function.uncurry, Set.indicator]

/-- A finite set of points of `[lo, lo + n s)` that are pairwise `s`-separated has at most
`n` elements. -/
lemma card_le_of_separated {ι : Type*} (S : Finset ι) (x : ι → ℝ) {lo s : ℝ} {n : ℕ}
    (hs : 0 < s) (hmem : ∀ i ∈ S, lo ≤ x i ∧ x i < lo + n * s)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → s ≤ |x i - x j|) : S.card ≤ n := by
  classical
  have := Finset.card_le_card_of_injOn (s := S) (t := Finset.range n)
    (fun i => ⌊(x i - lo) / s⌋₊) ?_ ?_
  · simpa using this
  · intro i hi
    have h := hmem i hi
    refine Finset.mem_coe.2 (Finset.mem_range.2 ?_)
    rw [Nat.floor_lt (div_nonneg (by linarith [h.1]) hs.le), div_lt_iff₀ hs]
    linarith [h.2]
  · intro i hi j hj hij
    by_contra hne
    have h1 := hsep i hi j hj hne
    simp only at hij
    have hi0 : 0 ≤ (x i - lo) / s := div_nonneg (by linarith [(hmem i hi).1]) hs.le
    have hj0 : 0 ≤ (x j - lo) / s := div_nonneg (by linarith [(hmem j hj).1]) hs.le
    have a1 := Nat.floor_le hi0
    have a2 := Nat.lt_floor_add_one ((x i - lo) / s)
    have b1 := Nat.floor_le hj0
    have b2 := Nat.lt_floor_add_one ((x j - lo) / s)
    rw [hij] at a1 a2
    have h3 : |(x i - lo) / s - (x j - lo) / s| < 1 := by
      rw [abs_lt]; constructor <;> linarith
    rw [← sub_div, abs_div, abs_of_pos hs, div_lt_one hs,
      show x i - lo - (x j - lo) = x i - x j by ring] at h3
    linarith

/-! ### Lemma `dim:br:divisor-product` -/

lemma measurable_log_Psi_floor (α : ℝ) :
    Measurable fun t : ℝ => Real.log (Psi α ⌊t⌋₊) :=
  (measurable_from_nat (f := fun n : ℕ => Real.log (Psi α n))).comp Nat.measurable_floor

/-- **Lemma 4.? (`dim:br:divisor-product`), precise form (l. 3580–3585).**
Let `α` be irrational with `𝔟 < ∞`, `1 ≤ a ≤ b`, and let `m_*` maximize
`f_m = -log|sin(π m α)|` on `[a, b] ∩ ℤ`. Then
`∑_{a ≤ m ≤ b, m ≠ m_*} -log|sin(π m α)| ≤ (b - a) 𝔟`.
The proof is the paper's: separation of the super-level sets of `f`, counting, and
layer-cake integration in `u` (with `1/d(u)` replaced by the equivalent integral
`∫₁^∞ 1_{log Ψ(⌊t⌋) > u} dt/t²`). -/
theorem divisor_sum_le {α : ℝ} (hα : Irrational α) (hb : brjunoIntegral α < ∞)
    {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (mstar : ℕ) (hms : mstar ∈ Finset.Icc a b)
    (hmax : ∀ m ∈ Finset.Icc a b,
      -Real.log |Real.sin (π * (m * α))| ≤ -Real.log |Real.sin (π * (mstar * α))|) :
    ∑ m ∈ (Finset.Icc a b).erase mstar, -Real.log |Real.sin (π * (m * α))|
      ≤ ((b : ℝ) - a) * (brjunoIntegral α).toReal := by
  classical
  set f : ℕ → ℝ := fun m => -Real.log |Real.sin (π * (m * α))| with hf_def
  set L : ℝ → ℝ := fun t => Real.log (Psi α ⌊t⌋₊) with hL_def
  have hLm : Measurable L := measurable_log_Psi_floor α
  set g : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (1 / t ^ 2) with hg_def
  set F : ℝ → ℝ≥0∞ := fun u => ∫⁻ t in Ioi (1 : ℝ), {t | u < L t}.indicator g t with hF_def
  set S₀ := (Finset.Icc a b).erase mstar with hS₀
  have hpos : ∀ m ∈ Finset.Icc a b, 0 < |Real.sin (π * (m * α))| := fun m hm =>
    abs_sin_pos_of_irrational hα (by have := (Finset.mem_Icc.1 hm).1; omega)
  have hf0 : ∀ m ∈ Finset.Icc a b, 0 ≤ f m := by
    intro m hm
    simp only [hf_def, neg_nonneg]
    exact Real.log_nonpos (abs_nonneg _) (Real.abs_sin_le_one _)
  -- super-level sets: `u < f m` forces `2 ‖mα‖ < e^{-u}`
  have hsmall : ∀ m ∈ Finset.Icc a b, ∀ u : ℝ, u < f m → 2 * nint (m * α) < Real.exp (-u) := by
    intro m hm u hu
    have h1 : Real.log |Real.sin (π * (m * α))| < -u := by simp only [hf_def] at hu; linarith
    rw [Real.log_lt_iff_lt_exp (hpos m hm)] at h1
    exact lt_of_le_of_lt (two_mul_nint_le_abs_sin _) h1
  -- the counting estimate, for every level `u`
  have hcount : ∀ u : ℝ, ((S₀.filter fun m => u < f m).card : ℝ≥0∞)
      ≤ ((b - a : ℕ) : ℝ≥0∞) * F u := by
    intro u
    set T := (Finset.Icc a b).filter fun m => u < f m with hT
    have hfilt : S₀.filter (fun m => u < f m) = T.erase mstar := by
      rw [hS₀, Finset.filter_erase]
    rw [hfilt]
    rcases Nat.eq_zero_or_pos (T.erase mstar).card with h0 | hpos'
    · rw [h0]; simp
    obtain ⟨m₁, hm₁⟩ := Finset.card_pos.1 hpos'
    have hm₁T : m₁ ∈ T := Finset.mem_of_mem_erase hm₁
    have hm₁ne : m₁ ≠ mstar := Finset.ne_of_mem_erase hm₁
    have hmsT : mstar ∈ T := by
      rw [hT, Finset.mem_filter] at hm₁T ⊢
      exact ⟨hms, lt_of_lt_of_le hm₁T.2 (hmax m₁ hm₁T.1)⟩
    have hP : ∃ G, ∃ j ∈ T, ∃ k ∈ T, j < k ∧ k - j = G := by
      rcases lt_or_gt_of_ne hm₁ne with h | h
      · exact ⟨_, m₁, hm₁T, mstar, hmsT, h, rfl⟩
      · exact ⟨_, mstar, hmsT, m₁, hm₁T, h, rfl⟩
    classical
    set G := Nat.find hP with hGdef
    obtain ⟨j, hj, k, hk, hjk, hG⟩ := Nat.find_spec hP
    have hmin : ∀ j ∈ T, ∀ k ∈ T, j < k → G ≤ k - j := fun j hj k hk hjk =>
      Nat.find_min' hP ⟨j, hj, k, hk, hjk, rfl⟩
    have hG1 : 1 ≤ G := by rw [← hGdef] at hG; omega
    have hGpos : (0 : ℝ) < G := by exact_mod_cast hG1
    -- separation and counting
    have hTsub : ∀ i ∈ T, i ∈ Finset.Icc a b := fun i hi => (Finset.mem_filter.1 hi).1
    have hcardT : T.card ≤ (b - a) / G + 1 := by
      apply card_le_of_separated T (fun i : ℕ => (i : ℝ)) hGpos (lo := (a : ℝ))
      · intro i hi
        have hi' := Finset.mem_Icc.1 (hTsub i hi)
        refine ⟨by exact_mod_cast hi'.1, ?_⟩
        have hq := Nat.lt_div_mul_add (a := b - a) hG1
        have hnat : i < a + ((b - a) / G + 1) * G := by
          rw [add_mul, one_mul]
          generalize (b - a) / G * G = q at hq ⊢
          omega
        exact_mod_cast hnat
      · intro i hi i' hi' hne
        rcases lt_or_gt_of_ne hne with h | h
        · have := hmin i hi i' hi' h
          have hc : (G : ℝ) + i ≤ i' := by exact_mod_cast (by omega : G + i ≤ i')
          exact le_abs.2 (Or.inr (by linarith))
        · have := hmin i' hi' i hi h
          have hc : (G : ℝ) + i' ≤ i := by exact_mod_cast (by omega : G + i' ≤ i)
          exact le_abs.2 (Or.inl (by linarith))
    have hcardE : (T.erase mstar).card = T.card - 1 := Finset.card_erase_of_mem hmsT
    have hcG : (T.erase mstar).card * G ≤ b - a := by
      rw [hcardE]
      calc (T.card - 1) * G ≤ (b - a) / G * G := Nat.mul_le_mul_right _ (by omega)
        _ ≤ b - a := Nat.div_mul_le_self _ _
    -- the level set of `log Ψ(⌊t⌋)` contains `(G, ∞)`
    have hFG : ENNReal.ofReal (1 / G) ≤ F u := by
      apply ofReal_inv_le_lintegral_indicator (by exact_mod_cast hG1)
      intro t ht
      simp only [Set.mem_ofPred_eq, hL_def]
      have hjI := hTsub j hj
      have hkI := hTsub k hk
      have hj' := hsmall j hjI u (Finset.mem_filter.1 hj).2
      have hk' := hsmall k hkI u (Finset.mem_filter.1 hk).2
      have hGcast : ((G : ℕ) : ℝ) * α = (k : ℝ) * α - (j : ℝ) * α := by
        rw [hGdef, ← hG, Nat.cast_sub hjk.le]; ring
      have hnG : nint ((G : ℝ) * α) < Real.exp (-u) := by
        rw [hGcast]
        have := nint_sub_le ((k : ℝ) * α) ((j : ℝ) * α)
        linarith
      have hnGpos : 0 < nint ((G : ℝ) * α) := nint_pos_of_irrational hα (by omega)
      have hfl : G ≤ ⌊t⌋₊ := Nat.le_floor ht.le
      have hPsi := inv_nint_le_Psi α hG1 hfl
      have hexp : Real.exp u < (nint ((G : ℝ) * α))⁻¹ := by
        rw [show Real.exp u = (Real.exp (-u))⁻¹ by rw [Real.exp_neg, inv_inv]]
        exact inv_strictAnti₀ hnGpos hnG
      have hPsipos : 0 < Psi α ⌊t⌋₊ := lt_of_lt_of_le (inv_pos.2 hnGpos) hPsi
      rw [Real.lt_log_iff_exp_lt hPsipos]
      linarith
    calc ((T.erase mstar).card : ℝ≥0∞)
        = ENNReal.ofReal ((T.erase mstar).card : ℝ) := (ENNReal.ofReal_natCast _).symm
      _ ≤ ENNReal.ofReal (((b - a : ℕ) : ℝ) * (1 / G)) := by
          apply ENNReal.ofReal_le_ofReal
          rw [mul_one_div, le_div_iff₀ hGpos]
          exact_mod_cast hcG
      _ = ((b - a : ℕ) : ℝ≥0∞) * ENNReal.ofReal (1 / G) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
      _ ≤ ((b - a : ℕ) : ℝ≥0∞) * F u := mul_le_mul_of_nonneg_left hFG (by positivity)
  -- layer-cake in `u`
  have hlayer : ENNReal.ofReal (∑ m ∈ S₀, f m) ≤ ((b - a : ℕ) : ℝ≥0∞) * brjunoIntegral α := by
    have hS₀sub : ∀ m ∈ S₀, m ∈ Finset.Icc a b := fun m hm => Finset.mem_of_mem_erase hm
    rw [ENNReal.ofReal_sum_of_nonneg (fun m hm => hf0 m (hS₀sub m hm))]
    have hone : ∀ m ∈ S₀, ENNReal.ofReal (f m)
        = ∫⁻ u in Ioi (0 : ℝ), (Iio (f m)).indicator (fun _ => (1 : ℝ≥0∞)) u := by
      intro m _
      rw [lintegral_indicator_const measurableSet_Iio, one_mul,
        Measure.restrict_apply measurableSet_Iio, Set.inter_comm, Set.Ioi_inter_Iio,
        Real.volume_Ioo, sub_zero]
    rw [Finset.sum_congr rfl hone,
      ← lintegral_finsetSum _ (fun m _ => measurable_const.indicator measurableSet_Iio)]
    calc ∫⁻ u in Ioi (0 : ℝ), ∑ m ∈ S₀, (Iio (f m)).indicator (fun _ => (1 : ℝ≥0∞)) u
        = ∫⁻ u in Ioi (0 : ℝ), ((S₀.filter fun m => u < f m).card : ℝ≥0∞) := by
          refine lintegral_congr fun u => ?_
          simp only [Set.indicator_apply, Set.mem_Iio]
          rw [Finset.sum_boole]
      _ ≤ ∫⁻ u in Ioi (0 : ℝ), ((b - a : ℕ) : ℝ≥0∞) * F u := lintegral_mono hcount
      _ = ((b - a : ℕ) : ℝ≥0∞) * ∫⁻ u in Ioi (0 : ℝ), F u :=
          lintegral_const_mul' _ _ (ENNReal.natCast_ne_top _)
      _ = ((b - a : ℕ) : ℝ≥0∞) * brjunoIntegral α := by
          rw [hF_def, lintegral_layer hLm 0]
          simp only [sub_zero, brjunoIntegral, hL_def]
  have hfin : ((b - a : ℕ) : ℝ≥0∞) * brjunoIntegral α ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hb.ne
  rw [ENNReal.ofReal_le_iff_le_toReal hfin, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    Nat.cast_sub hab] at hlayer
  exact hlayer

/-- **Lemma 4.? (`dim:br:divisor-product`), estimate `(dim:br:product-estimate)`
(l. 3575–3579).** If `α` is irrational and `𝔟 < ∞`, then for `1 ≤ a ≤ b`,
`∏_{m=a}^{b} |sin(π m α)|⁻¹ ≤ Ψ(b) e^{(b-a) 𝔟}`. -/
theorem divisor_product {α : ℝ} (hα : Irrational α) (hb : brjunoIntegral α < ∞)
    {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    ∏ m ∈ Finset.Icc a b, |Real.sin (π * (m * α))|⁻¹
      ≤ Psi α b * Real.exp (((b : ℝ) - a) * (brjunoIntegral α).toReal) := by
  classical
  set f : ℕ → ℝ := fun m => -Real.log |Real.sin (π * (m * α))| with hf_def
  have hpos : ∀ m ∈ Finset.Icc a b, 0 < |Real.sin (π * (m * α))| := fun m hm =>
    abs_sin_pos_of_irrational hα (by have := (Finset.mem_Icc.1 hm).1; omega)
  obtain ⟨mstar, hms, hmax⟩ :=
    Finset.exists_max_image (Finset.Icc a b) f (Finset.nonempty_Icc.2 hab)
  have hsum := divisor_sum_le hα hb ha hab mstar hms hmax
  have hexp : ∀ m ∈ Finset.Icc a b, |Real.sin (π * (m * α))|⁻¹ = Real.exp (f m) := by
    intro m hm
    rw [hf_def, Real.exp_neg, Real.exp_log (hpos m hm)]
  rw [Finset.prod_congr rfl hexp, ← Real.exp_sum, ← Finset.add_sum_erase _ _ hms, Real.exp_add]
  have hms' := Finset.mem_Icc.1 hms
  have hfirst : Real.exp (f mstar) ≤ Psi α b := by
    rw [← hexp mstar hms]
    have hn := nint_pos_of_irrational hα (m := mstar) (by omega)
    calc |Real.sin (π * (mstar * α))|⁻¹ ≤ (nint (mstar * α))⁻¹ := by
          apply inv_anti₀ hn
          linarith [two_mul_nint_le_abs_sin ((mstar : ℝ) * α)]
      _ ≤ Psi α b := inv_nint_le_Psi α (by omega) hms'.2
  exact mul_le_mul hfirst (Real.exp_le_exp.2 hsum) (Real.exp_pos _).le
    (le_trans (Real.exp_pos _).le hfirst)

/-! ### Lemma `dim:br:inverse-cutoffs` -/

/-- The cutoff `N(u) = max{N ≥ 1 : log Λ(N) ≤ u}` (l. 4040 and l. 4054). -/
def cutoff (Λ : ℕ → ℝ) (u : ℝ) : ℕ := sSup {N : ℕ | 1 ≤ N ∧ Real.log (Λ N) ≤ u}

section Cutoff

variable {Λ : ℕ → ℝ} (hΛ1 : ∀ N, 1 ≤ Λ N) (hmono : Monotone Λ)
  (hunb : ¬ BddAbove (Set.range Λ))

include hΛ1 hmono in
lemma log_mono : Monotone fun N => Real.log (Λ N) := fun a _ h =>
  Real.log_le_log (by linarith [hΛ1 a]) (hmono h)

include hΛ1 hmono hunb in
lemma cutoff_bdd (u : ℝ) : BddAbove {N : ℕ | 1 ≤ N ∧ Real.log (Λ N) ≤ u} := by
  obtain ⟨y, ⟨K, rfl⟩, hK⟩ := not_bddAbove_iff.1 hunb (Real.exp u)
  refine ⟨K, fun N hN => ?_⟩
  by_contra h
  push_neg at h
  have h1 : Λ K ≤ Λ N := hmono h.le
  have h2 : u < Real.log (Λ N) := by
    rw [Real.lt_log_iff_exp_lt (by linarith [hΛ1 N])]; linarith
  linarith [hN.2]

include hΛ1 hmono hunb in
lemma le_cutoff_iff {u : ℝ} (hu : Real.log (Λ 1) ≤ u) {N : ℕ} (hN : 1 ≤ N) :
    N ≤ cutoff Λ u ↔ Real.log (Λ N) ≤ u := by
  have hmem : cutoff Λ u ∈ {N : ℕ | 1 ≤ N ∧ Real.log (Λ N) ≤ u} :=
    Nat.sSup_mem ⟨1, le_rfl, hu⟩ (cutoff_bdd hΛ1 hmono hunb u)
  constructor
  · intro h; exact le_trans (log_mono hΛ1 hmono h) hmem.2
  · intro h; exact le_csSup (cutoff_bdd hΛ1 hmono hunb u) ⟨hN, h⟩

include hΛ1 hmono hunb in
lemma one_le_cutoff {u : ℝ} (hu : Real.log (Λ 1) ≤ u) : 1 ≤ cutoff Λ u :=
  (le_cutoff_iff hΛ1 hmono hunb hu le_rfl).2 hu

include hΛ1 hmono hunb in
lemma log_cutoff_le {u : ℝ} (hu : Real.log (Λ 1) ≤ u) : Real.log (Λ (cutoff Λ u)) ≤ u :=
  (le_cutoff_iff hΛ1 hmono hunb hu (one_le_cutoff hΛ1 hmono hunb hu)).1 le_rfl

include hΛ1 hmono hunb in
lemma cutoff_mono {u v : ℝ} (hu : Real.log (Λ 1) ≤ u) (huv : u ≤ v) :
    cutoff Λ u ≤ cutoff Λ v :=
  (le_cutoff_iff hΛ1 hmono hunb (hu.trans huv) (one_le_cutoff hΛ1 hmono hunb hu)).2
    ((log_cutoff_le hΛ1 hmono hunb hu).trans huv)

include hΛ1 hmono hunb in
lemma tendsto_cutoff : Tendsto (cutoff Λ) atTop atTop := by
  rw [tendsto_atTop]
  intro K
  filter_upwards [eventually_ge_atTop (max (Real.log (Λ (max K 1))) (Real.log (Λ 1)))] with u hu
  have h1 : Real.log (Λ 1) ≤ u := le_trans (le_max_right _ _) hu
  exact le_trans (le_max_left K 1)
    ((le_cutoff_iff hΛ1 hmono hunb h1 (le_max_right K 1)).2 (le_trans (le_max_left _ _) hu))

end Cutoff

lemma ofReal_div_max {x y : ℝ} (hy : 0 ≤ y) :
    ENNReal.ofReal (x / y) = ENNReal.ofReal (max x 0 / y) := by
  rcases le_total 0 x with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h, zero_div, ENNReal.ofReal_zero]
    apply ENNReal.ofReal_of_nonpos
    simpa using div_le_div_of_nonneg_right h hy

/-- **Lemma 4.? (`dim:br:inverse-cutoffs`) (l. 4032–4064).**
Let `Λ(N) ≥ 1` be nondecreasing and unbounded with `∫₁^∞ log Λ(⌊t⌋)/t² dt < ∞`. For
`a₀ ≥ log Λ(1)` (this is the "sufficiently large" condition making every `N_j` well defined)
put `N_j = max{N ≥ 1 : log Λ(N) ≤ a₀ + j log 2}`. Then `N_j → ∞` and
`∑_j 1/N_j ≤ 1/N_0 + (2/log 2) ∫₁^∞ (log Λ(⌊t⌋) - a₀)₊/t² dt`; moreover the right-hand side
tends to `0` as `a₀ → ∞`. (Sums and integrals are in `[0, ∞]`; the right-hand side is
finite, so the series converges.)  We take `Λ` monotone on all of `ℕ` with `Λ ≥ 1`; its
value at `0` plays no role. -/
theorem inverse_cutoffs (Λ : ℕ → ℝ) (hΛ1 : ∀ N, 1 ≤ Λ N) (hmono : Monotone Λ)
    (hunb : ¬ BddAbove (Set.range Λ))
    (hint : ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (Real.log (Λ ⌊t⌋₊) / t ^ 2) ≠ ∞) :
    (∀ a₀ : ℝ, Real.log (Λ 1) ≤ a₀ →
      Tendsto (fun j : ℕ => cutoff Λ (a₀ + j * Real.log 2)) atTop atTop ∧
      ∑' j : ℕ, ENNReal.ofReal (1 / (cutoff Λ (a₀ + j * Real.log 2) : ℝ)) ≤
        ENNReal.ofReal (1 / (cutoff Λ a₀ : ℝ)) + ENNReal.ofReal (2 / Real.log 2) *
          ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (max (Real.log (Λ ⌊t⌋₊) - a₀) 0 / t ^ 2)) ∧
    Tendsto (fun a₀ : ℝ => ENNReal.ofReal (1 / (cutoff Λ a₀ : ℝ)) +
        ENNReal.ofReal (2 / Real.log 2) *
          ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (max (Real.log (Λ ⌊t⌋₊) - a₀) 0 / t ^ 2))
      atTop (𝓝 0) := by
  set ℓ : ℕ → ℝ := fun N => Real.log (Λ N) with hℓ
  set L : ℝ → ℝ := fun t => Real.log (Λ ⌊t⌋₊) with hL_def
  have hLm : Measurable L :=
    (measurable_from_nat (f := fun n : ℕ => Real.log (Λ n))).comp Nat.measurable_floor
  have hℓ0 : ∀ N, 0 ≤ ℓ N := fun N => Real.log_nonneg (hΛ1 N)
  have hc : 0 < Real.log 2 := Real.log_pos one_lt_two
  set c := Real.log 2 with hcdef
  refine ⟨fun a₀ ha₀ => ⟨?_, ?_⟩, ?_⟩
  · -- `N_j → ∞`
    rw [tendsto_atTop]
    intro K
    obtain ⟨j₀, hj₀⟩ := exists_nat_gt ((ℓ (max K 1) - a₀) / c)
    filter_upwards [eventually_ge_atTop j₀] with j hj
    have hj' : (j₀ : ℝ) ≤ j := by exact_mod_cast hj
    have h1 : ℓ (max K 1) ≤ a₀ + j * c := by
      rw [div_lt_iff₀ hc] at hj₀
      nlinarith
    have hu : Real.log (Λ 1) ≤ a₀ + j * c := by
      have : (0 : ℝ) ≤ j * c := by positivity
      linarith
    exact le_trans (le_max_left K 1) ((le_cutoff_iff hΛ1 hmono hunb hu (le_max_right K 1)).2 h1)
  · -- the sum bound
    set h : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (1 / (cutoff Λ u : ℝ)) with hh
    set I : ℕ → Set ℝ := fun j => Ioc (a₀ + j * c) (a₀ + (j + 1) * c) with hI
    -- step 1: each term is controlled by an integral over one period
    have hstep : ∀ j : ℕ, ENNReal.ofReal (1 / (cutoff Λ (a₀ + ((j + 1 : ℕ) : ℝ) * c) : ℝ))
        ≤ ENNReal.ofReal (1 / c) * ∫⁻ u in I j, h u := by
      intro j
      set Nn := cutoff Λ (a₀ + ((j + 1 : ℕ) : ℝ) * c)
      have hjc : (0 : ℝ) ≤ j * c := by positivity
      have hlow : ENNReal.ofReal (1 / (Nn : ℝ)) * ENNReal.ofReal c ≤ ∫⁻ u in I j, h u := by
        calc ENNReal.ofReal (1 / (Nn : ℝ)) * ENNReal.ofReal c
            = ∫⁻ _ in I j, ENNReal.ofReal (1 / (Nn : ℝ)) := by
              rw [setLIntegral_const, hI, Real.volume_Ioc]
              congr 2; ring
          _ ≤ ∫⁻ u in I j, h u := by
              apply setLIntegral_mono' measurableSet_Ioc
              intro u hu
              have hu1 : Real.log (Λ 1) ≤ u := by
                have := hu.1; linarith
              have hmon : cutoff Λ u ≤ Nn :=
                cutoff_mono hΛ1 hmono hunb hu1 (by have := hu.2; push_cast; linarith)
              have hpos : (0 : ℝ) < cutoff Λ u := by
                exact_mod_cast one_le_cutoff hΛ1 hmono hunb hu1
              apply ENNReal.ofReal_le_ofReal
              exact one_div_le_one_div_of_le hpos (by exact_mod_cast hmon)
      calc ENNReal.ofReal (1 / (Nn : ℝ))
          = ENNReal.ofReal (1 / c) * (ENNReal.ofReal (1 / (Nn : ℝ)) * ENNReal.ofReal c) := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
            congr 1; field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left hlow (by positivity)
    -- step 2: the periods are disjoint and lie in `(a₀, ∞)`
    have hdisj : Pairwise (Function.onFun Disjoint I) := by
      intro i k hik
      rw [Function.onFun, Set.disjoint_left]
      intro u hu1 hu2
      rcases lt_or_gt_of_ne hik with hlt | hlt
      · have : (i : ℝ) + 1 ≤ k := by exact_mod_cast hlt
        have := mul_le_mul_of_nonneg_right this hc.le
        have := hu1.2; have := hu2.1; linarith
      · have : (k : ℝ) + 1 ≤ i := by exact_mod_cast hlt
        have := mul_le_mul_of_nonneg_right this hc.le
        have := hu1.1; have := hu2.2; linarith
    have hunion : (⋃ j, I j) ⊆ Ioi a₀ := by
      refine iUnion_subset fun j u hu => ?_
      have := hu.1
      have : (0 : ℝ) ≤ j * c := by positivity
      show a₀ < u; linarith
    have hsum1 : ∑' j : ℕ, ENNReal.ofReal (1 / (cutoff Λ (a₀ + ((j + 1 : ℕ) : ℝ) * c) : ℝ))
        ≤ ENNReal.ofReal (1 / c) * ∫⁻ u in Ioi a₀, h u := by
      calc _ ≤ ∑' j : ℕ, ENNReal.ofReal (1 / c) * ∫⁻ u in I j, h u := ENNReal.tsum_le_tsum hstep
        _ = ENNReal.ofReal (1 / c) * ∫⁻ u in ⋃ j, I j, h u := by
            rw [ENNReal.tsum_mul_left, lintegral_iUnion (fun j => measurableSet_Ioc) hdisj]
        _ ≤ _ := mul_le_mul_of_nonneg_left (lintegral_mono_set hunion) (by positivity)
    -- step 3: `1/N(u) ≤ 2/(N(u)+1) ≤ 2 ∫₁^∞ 1_{log Λ(⌊t⌋) > u} dt/t²`
    have hpt : ∀ u ∈ Ioi a₀, h u ≤ ENNReal.ofReal 2 * ∫⁻ t in Ioi (1 : ℝ),
        {t | u < L t}.indicator (fun t => ENNReal.ofReal (1 / t ^ 2)) t := by
      intro u hu
      have hu1 : Real.log (Λ 1) ≤ u := le_trans ha₀ (le_of_lt hu)
      set N := cutoff Λ u with hN
      have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast one_le_cutoff hΛ1 hmono hunb hu1
      have hlow : ENNReal.ofReal (1 / ((N : ℝ) + 1)) ≤ ∫⁻ t in Ioi (1 : ℝ),
          {t | u < L t}.indicator (fun t => ENNReal.ofReal (1 / t ^ 2)) t := by
        apply ofReal_inv_le_lintegral_indicator (by linarith)
        intro t ht
        simp only [Set.mem_ofPred_eq, hL_def]
        have hfl : N + 1 ≤ ⌊t⌋₊ := Nat.le_floor (by push_cast; linarith)
        by_contra hcon
        push_neg at hcon
        have := (le_cutoff_iff hΛ1 hmono hunb hu1 (by omega : 1 ≤ ⌊t⌋₊)).2 hcon
        omega
      calc h u = ENNReal.ofReal (1 / (N : ℝ)) := rfl
        _ ≤ ENNReal.ofReal (2 * (1 / ((N : ℝ) + 1))) := by
            apply ENNReal.ofReal_le_ofReal
            rw [mul_one_div, div_le_div_iff₀ (by linarith) (by linarith)]
            linarith
        _ = ENNReal.ofReal 2 * ENNReal.ofReal (1 / ((N : ℝ) + 1)) :=
            ENNReal.ofReal_mul (by norm_num)
        _ ≤ _ := mul_le_mul_of_nonneg_left hlow (by positivity)
    have hint2 : ∫⁻ u in Ioi a₀, h u ≤ ENNReal.ofReal 2 *
        ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (max (Real.log (Λ ⌊t⌋₊) - a₀) 0 / t ^ 2) := by
      calc ∫⁻ u in Ioi a₀, h u ≤ ∫⁻ u in Ioi a₀, ENNReal.ofReal 2 * ∫⁻ t in Ioi (1 : ℝ),
            {t | u < L t}.indicator (fun t => ENNReal.ofReal (1 / t ^ 2)) t :=
            setLIntegral_mono' measurableSet_Ioi hpt
        _ = ENNReal.ofReal 2 * ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal ((L t - a₀) / t ^ 2) := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_layer hLm a₀]
        _ = _ := by
            congr 1
            refine lintegral_congr fun t => ?_
            exact ofReal_div_max (by positivity)
    -- assemble
    rw [tsum_eq_zero_add' ENNReal.summable]
    simp only [CharP.cast_eq_zero, zero_mul, add_zero]
    refine add_le_add le_rfl ?_
    calc ∑' j : ℕ, ENNReal.ofReal (1 / (cutoff Λ (a₀ + ((j + 1 : ℕ) : ℝ) * c) : ℝ))
        ≤ ENNReal.ofReal (1 / c) * ∫⁻ u in Ioi a₀, h u := hsum1
      _ ≤ ENNReal.ofReal (1 / c) * (ENNReal.ofReal 2 *
          ∫⁻ t in Ioi (1 : ℝ), ENNReal.ofReal (max (Real.log (Λ ⌊t⌋₊) - a₀) 0 / t ^ 2)) :=
          mul_le_mul_of_nonneg_left hint2 (by positivity)
      _ = _ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2; ring
  · -- the right-hand side tends to `0`
    have h1 : Tendsto (fun a₀ : ℝ => ENNReal.ofReal (1 / (cutoff Λ a₀ : ℝ))) atTop (𝓝 0) := by
      have := ENNReal.tendsto_ofReal ((tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_cutoff hΛ1 hmono hunb))))
      simpa [one_div, Function.comp] using this
    have h2 : Tendsto (fun a₀ : ℝ => ∫⁻ t in Ioi (1 : ℝ),
        ENNReal.ofReal (max (Real.log (Λ ⌊t⌋₊) - a₀) 0 / t ^ 2)) atTop (𝓝 0) := by
      have := tendsto_lintegral_filter_of_dominated_convergence
        (μ := volume.restrict (Ioi (1 : ℝ))) (l := atTop) (f := fun _ => (0 : ℝ≥0∞))
        (F := fun a₀ t => ENNReal.ofReal (max (L t - a₀) 0 / t ^ 2))
        (fun t => ENNReal.ofReal (L t / t ^ 2))
        (Eventually.of_forall fun a₀ => ENNReal.measurable_ofReal.comp
          (((hLm.sub measurable_const).max measurable_const).div (measurable_id.pow_const 2)))
        (by
          filter_upwards [eventually_ge_atTop (0 : ℝ)] with a₀ ha₀
          refine Eventually.of_forall fun t => ENNReal.ofReal_le_ofReal ?_
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact max_le (by linarith) (hℓ0 _))
        hint
        (Eventually.of_forall fun t => by
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [eventually_ge_atTop (L t)] with a₀ ha₀
          rw [max_eq_right (by linarith), zero_div, ENNReal.ofReal_zero])
      simpa using this
    have := h1.add (ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (2 / Real.log 2)) h2
      (Or.inr ENNReal.ofReal_ne_top))
    simpa using this

/-! ### The scalar iteration `(dim:br:geometric-convergence)` -/

/-- **Induction `(dim:br:geometric-convergence)` (l. 4140–4170)** in the proof of
Proposition `dim:prop:singular-preparation`. Let `r₀ = 1/16`, and suppose
`ε_{j+1} ≤ C (e^{-D} ε_j + Λ_j² ε_j²)` (this is `(dim:br:iteration-error)` with
`δ_j N_j = D`), `C e^{-D} ≤ r₀/2`, `0 ≤ Λ_j ≤ L₀ 2^j` and `C L₀² ε₀ ≤ r₀/2`.
Then `ε_j ≤ ε₀ r₀^j` and `C Λ_j ε_j ≤ C L₀ ε₀ 8^{-j}` for all `j`. -/
theorem scalar_iteration (C D L₀ : ℝ) (ε Λ : ℕ → ℝ) (hC : 0 ≤ C) (hε : ∀ j, 0 ≤ ε j)
    (hΛ : ∀ j, 0 ≤ Λ j)
    (hrec : ∀ j, ε (j + 1) ≤ C * (Real.exp (-D) * ε j + Λ j ^ 2 * ε j ^ 2))
    (hD : C * Real.exp (-D) ≤ (1 / 16) / 2) (hΛL : ∀ j, Λ j ≤ L₀ * 2 ^ j)
    (hsmall : C * L₀ ^ 2 * ε 0 ≤ (1 / 16) / 2) :
    ∀ j, ε j ≤ ε 0 * (1 / 16) ^ j ∧ C * Λ j * ε j ≤ C * L₀ * ε 0 * (1 / 8) ^ j := by
  have hpq : ∀ j : ℕ, (2 : ℝ) ^ j * (1 / 16) ^ j = (1 / 8) ^ j := by
    intro j; rw [← mul_pow]; norm_num
  have hfirst : ∀ j, ε j ≤ ε 0 * (1 / 16) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      set p : ℝ := 2 ^ j
      set q : ℝ := (1 / 16) ^ j
      have hq0 : 0 ≤ q := by positivity
      have h1 : Λ j ^ 2 ≤ (L₀ * p) ^ 2 := pow_le_pow_left₀ (hΛ j) (hΛL j) 2
      have h2 : ε j ^ 2 ≤ (ε 0 * q) ^ 2 := pow_le_pow_left₀ (hε j) ih 2
      have hpq2 : (p * q) ^ 2 ≤ q := by
        rw [hpq j, ← pow_mul, mul_comm j 2, pow_mul]
        exact pow_le_pow_left₀ (by norm_num) (by norm_num) j
      have hA : 0 ≤ ε 0 * (p * q) ^ 2 := mul_nonneg (hε 0) (sq_nonneg _)
      have hquad : C * Λ j ^ 2 * ε j ^ 2 ≤ (1 / 32) * (ε 0 * q) := by
        calc C * Λ j ^ 2 * ε j ^ 2 ≤ C * (L₀ * p) ^ 2 * (ε 0 * q) ^ 2 :=
              mul_le_mul (mul_le_mul_of_nonneg_left h1 hC) h2 (sq_nonneg _)
                (mul_nonneg hC (sq_nonneg _))
          _ = (C * L₀ ^ 2 * ε 0) * (ε 0 * (p * q) ^ 2) := by ring
          _ ≤ (1 / 32) * (ε 0 * (p * q) ^ 2) :=
              mul_le_mul_of_nonneg_right (by linarith) hA
          _ ≤ (1 / 32) * (ε 0 * q) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hpq2 (hε 0)) (by norm_num)
      have hlin : C * Real.exp (-D) * ε j ≤ (1 / 32) * (ε 0 * q) :=
        mul_le_mul (by linarith) ih (hε j) (by norm_num)
      have := hrec j
      rw [pow_succ]
      have e : C * (Real.exp (-D) * ε j + Λ j ^ 2 * ε j ^ 2)
          = C * Real.exp (-D) * ε j + C * Λ j ^ 2 * ε j ^ 2 := by ring
      rw [e] at this
      linarith
  intro j
  refine ⟨hfirst j, ?_⟩
  calc C * Λ j * ε j ≤ C * (L₀ * 2 ^ j) * (ε 0 * (1 / 16) ^ j) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hΛL j) hC) (hfirst j) (hε j)
          (mul_nonneg hC (le_trans (hΛ j) (hΛL j)))
    _ = C * L₀ * ε 0 * ((2 : ℝ) ^ j * (1 / 16) ^ j) := by ring
    _ = C * L₀ * ε 0 * (1 / 8) ^ j := by rw [hpq j]

/-! ### The Cauchy-coefficient sum `(dim:br:energy-smallness)` -/

/-- **Estimate `(dim:br:energy-smallness)` (l. 4228).** If `0 ≤ ‖R_k‖ ≤ ε 32^{-k}` for all
`k`, then `∑_{k ≥ 1} k 8^{k-1} ‖R_k‖ ≤ (ε/32)(1 - 8/32)^{-2} = ε/18`
(the series is indexed here by `k + 1`, `k ≥ 0`). -/
theorem energy_cauchy_sum (ε : ℝ) (r : ℕ → ℝ) (hr0 : ∀ k, 0 ≤ r k)
    (hr : ∀ k, r k ≤ ε * (1 / 32) ^ k) :
    Summable (fun k : ℕ => ((k : ℝ) + 1) * 8 ^ k * r (k + 1)) ∧
      ∑' k : ℕ, ((k : ℝ) + 1) * 8 ^ k * r (k + 1) ≤ ε / 18 := by
  have hgeom : HasSum (fun n : ℕ => (n : ℝ) * (1 / 4 : ℝ) ^ n) ((1 / 4) / (1 - 1 / 4) ^ 2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one (by norm_num)
  have hshift : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * (1 / 4 : ℝ) ^ (n + 1))
      ((1 / 4) / (1 - 1 / 4) ^ 2) := by
    have := (hasSum_nat_add_iff' (f := fun n : ℕ => (n : ℝ) * (1 / 4 : ℝ) ^ n) 1).2 hgeom
    simpa using this
  have hmaj : HasSum (fun k : ℕ => ((k : ℝ) + 1) * 8 ^ k * (ε * (1 / 32) ^ (k + 1))) (ε / 18) := by
    have := hshift.mul_left (ε / 8)
    convert this using 1
    · funext k
      have h8 : (8 : ℝ) ^ k * (1 / 32) ^ k = (1 / 4) ^ k := by rw [← mul_pow]; norm_num
      push_cast
      rw [pow_succ, pow_succ, ← h8]
      ring
    · norm_num; ring
  have hle : ∀ k : ℕ, ((k : ℝ) + 1) * 8 ^ k * r (k + 1)
      ≤ ((k : ℝ) + 1) * 8 ^ k * (ε * (1 / 32) ^ (k + 1)) :=
    fun k => mul_le_mul_of_nonneg_left (hr _) (by positivity)
  have hnn : ∀ k : ℕ, 0 ≤ ((k : ℝ) + 1) * 8 ^ k * r (k + 1) :=
    fun k => mul_nonneg (by positivity) (hr0 _)
  have hsum : Summable (fun k : ℕ => ((k : ℝ) + 1) * 8 ^ k * r (k + 1)) :=
    Summable.of_nonneg_of_le hnn hle hmaj.summable
  exact ⟨hsum, hasSum_le hle hsum.hasSum hmaj⟩

/-! ### The divisor-square bound `(dim:br:divisor-square)` -/

/-- Abstract form of the sorted-distance argument: if at most `j` of the positive numbers
`x_m` lie below `(j+1) c` for every `j`, then `∑ x_m^{-2} ≤ c^{-2} ∑_{j=1}^{#S} j^{-2}`. -/
lemma sum_inv_sq_le_of_count {ι : Type*} (S : Finset ι) (x : ι → ℝ) {c : ℝ} (hc : 0 < c)
    (hcount : ∀ j : ℕ, (S.filter fun m => x m < ((j : ℝ) + 1) * c).card ≤ j) :
    ∑ m ∈ S, 1 / x m ^ 2 ≤ 1 / c ^ 2 * ∑ j ∈ Finset.range S.card, 1 / ((j : ℝ) + 1) ^ 2 := by
  classical
  suffices H : ∀ n : ℕ, ∀ S : Finset ι, S.card = n →
      (∀ j : ℕ, (S.filter fun m => x m < ((j : ℝ) + 1) * c).card ≤ j) →
      ∑ m ∈ S, 1 / x m ^ 2 ≤ 1 / c ^ 2 * ∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1) ^ 2 from
    H _ S rfl hcount
  intro n
  induction n with
  | zero => intro S hS _; rw [Finset.card_eq_zero.1 hS]; simp
  | succ n ih =>
    intro S hS hcnt
    have hne : S.Nonempty := by rw [← Finset.card_pos, hS]; omega
    obtain ⟨m0, hm0, hmax⟩ := S.exists_max_image x hne
    have hbig : ((n : ℝ) + 1) * c ≤ x m0 := by
      by_contra h
      push_neg at h
      have hall : (S.filter fun m => x m < ((n : ℝ) + 1) * c) = S :=
        Finset.filter_true_of_mem fun m hm => lt_of_le_of_lt (hmax m hm) h
      have := hcnt n
      rw [hall, hS] at this
      omega
    have hpos : 0 < ((n : ℝ) + 1) * c := by positivity
    have h1 : 1 / x m0 ^ 2 ≤ 1 / c ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by
      calc 1 / x m0 ^ 2 ≤ 1 / (((n : ℝ) + 1) * c) ^ 2 :=
            one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hpos.le hbig 2)
        _ = 1 / c ^ 2 * (1 / ((n : ℝ) + 1) ^ 2) := by
            field_simp
    have h2 := ih (S.erase m0) (by rw [Finset.card_erase_of_mem hm0, hS]; rfl)
      (fun j => le_trans (Finset.card_le_card
        (Finset.filter_subset_filter _ (Finset.erase_subset _ _))) (hcnt j))
    rw [← Finset.add_sum_erase S _ hm0, Finset.sum_range_succ, mul_add]
    linarith

/-- `∑_{j=1}^{n} j^{-2} ≤ π²/6`. -/
lemma sum_range_inv_sq_le (n : ℕ) :
    ∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1) ^ 2 ≤ π ^ 2 / 6 := by
  have h := sum_le_hasSum (Finset.range (n + 1)) (fun i _ => by positivity) hasSum_zeta_two
  rw [Finset.sum_range_succ'] at h
  simpa using h

/-- **Estimate `(dim:br:divisor-square)` (l. 4398–4419)** in the proof of Lemma
`dim:br:boundary-rows`. If `Q ≥ 1` and `‖kα‖_𝕋 ≥ 1/(2Q)` for `1 ≤ k < Q` (for `Q = q_n`
this is the continued-fraction separation `‖q_{n-1}α‖ > 1/(q_n + q_{n-1}) ≥ 1/(2q_n)`), then
`∑_{m=1}^{Q-1} sin^{-2}(π m α) ≤ 4 Q² ∑_{j ≥ 1} j^{-2} = (2π²/3) Q²`.
The proof is the paper's: the points `mα` (and `0`) are `1/(2Q)`-separated on the circle, so
the `j`-th smallest distance `t_j` satisfies `t_j ≥ j/(4Q)`, and `|sin πt| ≥ 2‖t‖_𝕋`. -/
theorem divisor_square_sum (α : ℝ) (Q : ℕ) (hQ : 1 ≤ Q)
    (hsep : ∀ k : ℕ, 1 ≤ k → k < Q → 1 / (2 * (Q : ℝ)) ≤ nint (k * α)) :
    ∑ m ∈ Finset.Icc 1 (Q - 1), 1 / Real.sin (π * (m * α)) ^ 2 ≤ 2 * π ^ 2 / 3 * (Q : ℝ) ^ 2 := by
  classical
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
  set S := Finset.Icc 1 (Q - 1) with hS
  set x : ℕ → ℝ := fun m => nint (m * α) with hx
  set c : ℝ := 1 / (4 * Q) with hc
  have hcpos : 0 < c := by positivity
  have hxpos : ∀ m ∈ S, 0 < x m := by
    intro m hm
    have hm' := Finset.mem_Icc.1 hm
    exact lt_of_lt_of_le (by positivity) (hsep m hm'.1 (by omega))
  -- each term: `sin^{-2}(πmα) ≤ (1/4) ‖mα‖^{-2}`
  have hterm : ∀ m ∈ S, 1 / Real.sin (π * (m * α)) ^ 2 ≤ 1 / 4 * (1 / x m ^ 2) := by
    intro m hm
    have h0 := hxpos m hm
    have h1 : (2 * x m) ^ 2 ≤ Real.sin (π * (m * α)) ^ 2 := by
      rw [← sq_abs (Real.sin _)]
      exact pow_le_pow_left₀ (by positivity) (two_mul_nint_le_abs_sin _) 2
    calc 1 / Real.sin (π * (m * α)) ^ 2 ≤ 1 / (2 * x m) ^ 2 :=
          one_div_le_one_div_of_le (by positivity) h1
      _ = 1 / 4 * (1 / x m ^ 2) := by field_simp; ring
  -- the counting estimate
  set y : ℕ → ℝ := fun m => (m : ℝ) * α - round ((m : ℝ) * α) with hy
  have hcount : ∀ j : ℕ, (S.filter fun m => x m < ((j : ℝ) + 1) * c).card ≤ j := by
    intro j
    set T := S.filter fun m => x m < ((j : ℝ) + 1) * c with hT
    set r : ℝ := ((j : ℝ) + 1) * c with hr
    have hrpos : 0 < r := by positivity
    have h0T : 0 ∉ T := by
      intro h
      have := (Finset.mem_Icc.1 (Finset.mem_filter.1 h).1).1
      omega
    have hT' : ∀ m ∈ insert 0 T, m < Q ∧ |y m| < r := by
      intro m hm
      rcases Finset.mem_insert.1 hm with h | h
      · subst h; refine ⟨by omega, ?_⟩; simp [hy, hrpos]
      · have hmS := (Finset.mem_filter.1 h)
        refine ⟨by have := (Finset.mem_Icc.1 hmS.1).2; omega, ?_⟩
        exact hmS.2
    have hcard := card_le_of_separated (insert 0 T) y (lo := -r) (n := j + 1)
      (s := 1 / (2 * Q)) (by positivity)
      (by
        intro m hm
        have := abs_lt.1 (hT' m hm).2
        refine ⟨this.1.le, ?_⟩
        have e : -r + ((j + 1 : ℕ) : ℝ) * (1 / (2 * Q)) = r := by
          rw [hr, hc]; push_cast; field_simp; ring
        rw [e]; exact this.2)
      (by
        have key : ∀ m ∈ insert 0 T, ∀ m' ∈ insert 0 T, m' < m →
            1 / (2 * (Q : ℝ)) ≤ |y m - y m'| := by
          intro m hm m' hm' hlt
          have hmQ := (hT' m hm).1
          calc 1 / (2 * (Q : ℝ)) ≤ nint (((m - m' : ℕ) : ℝ) * α) := hsep _ (by omega) (by omega)
            _ ≤ |((m - m' : ℕ) : ℝ) * α - ((round ((m : ℝ) * α) - round ((m' : ℝ) * α) : ℤ) : ℝ)| :=
                nint_le _ _
            _ = |y m - y m'| := by
                congr 1; rw [hy]; push_cast [Nat.cast_sub hlt.le]; ring
        intro m hm m' hm' hne
        rcases lt_or_gt_of_ne hne with h | h
        · rw [abs_sub_comm]; exact key m' hm' m hm h
        · exact key m hm m' hm' h)
    rw [Finset.card_insert_of_notMem h0T] at hcard
    omega
  have hmain := sum_inv_sq_le_of_count S x hcpos hcount
  have hζ := sum_range_inv_sq_le S.card
  have hc2 : 1 / c ^ 2 = 16 * (Q : ℝ) ^ 2 := by rw [hc]; field_simp; ring
  calc ∑ m ∈ S, 1 / Real.sin (π * (m * α)) ^ 2 ≤ ∑ m ∈ S, 1 / 4 * (1 / x m ^ 2) :=
        Finset.sum_le_sum hterm
    _ = 1 / 4 * ∑ m ∈ S, 1 / x m ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 1 / 4 * (1 / c ^ 2 * (π ^ 2 / 6)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact le_trans hmain (mul_le_mul_of_nonneg_left hζ (by positivity))
    _ = 2 * π ^ 2 / 3 * (Q : ℝ) ^ 2 := by rw [hc2]; ring

end SmallDivisors
end SGD
