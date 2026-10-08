/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Appendix A.1: the Plemelj–Privalov theorem (Theorem A.1.6)

## Main results

* `DF.holderHilbertStatement_holds` — **Theorem A.1.6**: if `g ∈ L²(ℝ)` is uniformly
  `α`-Hölder continuous at scales `≤ 1` (`0 < α < 1`), then so is its Hilbert transform.
  This includes the general case that the book leaves as Exercise A.1.3.

## Proof

* `g` is bounded (`exists_bound_of_holder`): `|g(y)| ≤ |g(u)| + C` for `u ∈ [y, y + 1]`, so
  `|g(y)| ≤ ½ + C + ½ ∫ |g|²`.
* For `δ = |t - s| ≤ 1/3`, compare `Hg` with the truncation `H_{2δ} g`
  (`norm_truncHilbert_sub_le`: an error `O(δ^α)`).  After the change of variables
  `x = y + (t - s)`, `π (H_{2δ} g(t) - H_{2δ} g(s)) = ∫ g(s - y) (k(y + d) - k(y)) dy` with
  `k = 1_{|x| > 2δ} / x`.  Since `∫ 1_{|y| ≤ 1} k(y) dy = 0` (`k` is odd), we may subtract
  `g(s) (k₁(y + d) - k₁(y))`, `k₁ = 1_{|y| ≤ 1} k`, and the resulting integrand is bounded by
  an explicit function `psi` with `∫ psi ≤ K δ^α` (`norm_integrand_le`, `integral_psi_le`).
* For `|t - s| ≤ 1`, use three steps of length `|t - s|/3`.
-/
import DamanikFillman.AppA.Fourier

noncomputable section

open Real Complex Set Filter Topology MeasureTheory
open scoped ENNReal

namespace DF

namespace PlemeljPrivalov

variable {g : ℝ → ℂ}

/-! ### Boundedness -/

lemma exists_bound_of_holder (hg : MemLp g 2) {α C : ℝ} (hα : 0 < α)
    (hC : ∀ y t, |y - t| ≤ 1 → ‖g y - g t‖ ≤ C * |y - t| ^ α) : ∃ M, ∀ y, ‖g y‖ ≤ M := by
  have h1 : Integrable (fun x => ‖g x‖ ^ (2 : ℝ≥0∞).toReal) :=
    hg.integrable_norm_rpow (by norm_num) (by norm_num)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h1
  refine ⟨(1 / 2 + |C|) + (1 / 2) * ∫ x, ‖g x‖ ^ 2, fun y => ?_⟩
  have hpt : ∀ u ∈ Icc y (y + 1), ‖g y‖ ≤ (1 / 2 + |C|) + (1 / 2) * ‖g u‖ ^ 2 := by
    intro u hu
    have hd : |u - y| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [hu.1, hu.2]
    have h := hC u y hd
    have hp : |u - y| ^ α ≤ 1 := Real.rpow_le_one (abs_nonneg _) hd hα.le
    have hCp : C * |u - y| ^ α ≤ |C| := by
      calc C * |u - y| ^ α ≤ |C| * |u - y| ^ α :=
            mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (abs_nonneg _) _)
        _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left hp (abs_nonneg C)
        _ = |C| := mul_one _
    have htri : ‖g y‖ ≤ ‖g u‖ + ‖g u - g y‖ := by
      have := norm_le_norm_add_norm_sub' (g y) (g u)
      rwa [norm_sub_rev] at this
    nlinarith [sq_nonneg (‖g u‖ - 1)]
  have hint : IntegrableOn (fun u => (1 / 2 + |C|) + (1 / 2) * ‖g u‖ ^ 2) (Icc y (y + 1)) :=
    (continuous_const.integrableOn_Icc).add (h1.integrableOn.const_mul _)
  have hmono := setIntegral_mono_on (continuous_const.integrableOn_Icc (a := y) (b := y + 1)
    (f := fun _ : ℝ => ‖g y‖)) hint measurableSet_Icc hpt
  have hv : volume.real (Icc y (y + 1)) = 1 := by
    rw [Real.volume_real_Icc_of_le (by linarith)]; ring
  rw [setIntegral_const, hv, one_smul, integral_add continuous_const.integrableOn_Icc
    (h1.integrableOn.const_mul _), setIntegral_const, hv, one_smul, integral_const_mul] at hmono
  have hle : ∫ u in Icc y (y + 1), ‖g u‖ ^ 2 ≤ ∫ u, ‖g u‖ ^ 2 :=
    setIntegral_le_integral h1 (Eventually.of_forall fun _ => by positivity)
  linarith

/-! ### The truncated kernel -/

/-- The truncated Hilbert kernel `1_{|x| > ε} / x`. -/
def pvKer (ε : ℝ) (x : ℝ) : ℂ := Set.indicator {x : ℝ | ε < |x|} (fun x : ℝ => ((x : ℂ))⁻¹) x

/-- The kernel cut off at `|x| ≤ 1`. -/
def pvCut (ε : ℝ) (x : ℝ) : ℂ := Set.indicator {x : ℝ | |x| ≤ 1} (pvKer ε) x

lemma measurableSet_lt_abs (ε : ℝ) : MeasurableSet {x : ℝ | ε < |x|} :=
  measurableSet_lt measurable_const continuous_abs.measurable

lemma measurableSet_abs_le_one : MeasurableSet {x : ℝ | |x| ≤ 1} :=
  measurableSet_le continuous_abs.measurable measurable_const

lemma measurable_pvKer (ε : ℝ) : Measurable (pvKer ε) :=
  (Complex.measurable_ofReal.inv).indicator (measurableSet_lt_abs ε)

lemma norm_pvKer_le {ε : ℝ} (hε : 0 < ε) (x : ℝ) : ‖pvKer ε x‖ ≤ ε⁻¹ := by
  unfold pvKer
  by_cases h : ε < |x|
  · rw [Set.indicator_of_mem (show x ∈ {x : ℝ | ε < |x|} from h)]
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs]
    exact inv_anti₀ hε h.le
  · rw [Set.indicator_of_notMem (show x ∉ {x : ℝ | ε < |x|} from h), norm_zero]
    positivity

lemma norm_pvKer_le_inv_abs (ε : ℝ) (x : ℝ) : ‖pvKer ε x‖ ≤ |x|⁻¹ := by
  unfold pvKer
  by_cases h : ε < |x|
  · rw [Set.indicator_of_mem (show x ∈ {x : ℝ | ε < |x|} from h)]
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs]
  · rw [Set.indicator_of_notMem (show x ∉ {x : ℝ | ε < |x|} from h), norm_zero]
    positivity

lemma pvKer_neg (ε x : ℝ) : pvKer ε (-x) = -pvKer ε x := by
  unfold pvKer
  by_cases h : ε < |x|
  · rw [Set.indicator_of_mem (show -x ∈ {x : ℝ | ε < |x|} by simpa using h),
      Set.indicator_of_mem (show x ∈ {x : ℝ | ε < |x|} from h)]
    simp only [Complex.ofReal_neg, inv_neg]
  · rw [Set.indicator_of_notMem (show -x ∉ {x : ℝ | ε < |x|} by simpa using h),
      Set.indicator_of_notMem (show x ∉ {x : ℝ | ε < |x|} from h), neg_zero]

lemma pvCut_neg (ε x : ℝ) : pvCut ε (-x) = -pvCut ε x := by
  unfold pvCut
  by_cases h : |x| ≤ 1
  · rw [Set.indicator_of_mem (show -x ∈ {x : ℝ | |x| ≤ 1} by simpa using h),
      Set.indicator_of_mem (show x ∈ {x : ℝ | |x| ≤ 1} from h), pvKer_neg]
  · rw [Set.indicator_of_notMem (show -x ∉ {x : ℝ | |x| ≤ 1} by simpa using h),
      Set.indicator_of_notMem (show x ∉ {x : ℝ | |x| ≤ 1} from h), neg_zero]

lemma pvCut_eq (ε x : ℝ) : pvCut ε x = (if |x| ≤ 1 then (1 : ℂ) else 0) * pvKer ε x := by
  unfold pvCut
  by_cases h : |x| ≤ 1
  · rw [Set.indicator_of_mem (show x ∈ {x : ℝ | |x| ≤ 1} from h), if_pos h, one_mul]
  · rw [Set.indicator_of_notMem (show x ∉ {x : ℝ | |x| ≤ 1} from h), if_neg h, zero_mul]

lemma integral_eq_zero_of_odd {f : ℝ → ℂ} (h : ∀ x, f (-x) = -f x) : ∫ x, f x = 0 := by
  have h1 : ∫ x, f (-x) = ∫ x, f x := integral_neg_eq_self f volume
  have h2 : ∫ x, f (-x) = -∫ x, f x := by
    rw [← integral_neg]
    exact integral_congr_ae (Eventually.of_forall h)
  have h3 : -∫ x, f x = ∫ x, f x := h2.symm.trans h1
  linear_combination -h3 / 2

lemma integrable_pvCut {ε : ℝ} (hε : 0 < ε) : Integrable (pvCut ε) := by
  have hb : {x : ℝ | |x| ≤ 1} = Icc (-1) 1 := by
    ext x; simp [abs_le]
  have : Integrable (Set.indicator {x : ℝ | |x| ≤ 1} (pvKer ε)) := by
    refine (integrable_indicator_iff measurableSet_abs_le_one).2 ?_
    rw [hb]
    exact Integrable.mono' (continuous_const.integrableOn_Icc (f := fun _ : ℝ => ε⁻¹))
      (measurable_pvKer ε).aestronglyMeasurable (Eventually.of_forall (norm_pvKer_le hε))
  exact this

lemma integral_pvCut (ε : ℝ) : ∫ x, pvCut ε x = 0 :=
  integral_eq_zero_of_odd (pvCut_neg ε)

lemma integrable_mul_pvKer (hg : MemLp g 2) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    Integrable (fun x => g (t - x) * pvKer ε x) := by
  have h := (integrableOn_div_id (memLp_comp_sub hg t) hε).integrable_indicator
    (measurableSet_lt_abs ε)
  refine h.congr (Eventually.of_forall fun x => ?_)
  simp only [pvKer]
  by_cases hx : ε < |x|
  · rw [Set.indicator_of_mem (show x ∈ {x : ℝ | ε < |x|} from hx),
      Set.indicator_of_mem (show x ∈ {x : ℝ | ε < |x|} from hx), div_eq_mul_inv]
  · rw [Set.indicator_of_notMem (show x ∉ {x : ℝ | ε < |x|} from hx),
      Set.indicator_of_notMem (show x ∉ {x : ℝ | ε < |x|} from hx), mul_zero]

lemma integrable_mul_pvKer_shift (hg : MemLp g 2) {ε : ℝ} (hε : 0 < ε) (s c : ℝ) :
    Integrable (fun y => g (s - y) * pvKer ε (y + c)) := by
  have h := (integrable_mul_pvKer hg hε (s + c)).comp_add_right c
  refine h.congr (Eventually.of_forall fun y => ?_)
  show g (s + c - (y + c)) * pvKer ε (y + c) = g (s - y) * pvKer ε (y + c)
  rw [show s + c - (y + c) = s - y by ring]

/-- The truncated Hilbert transform at `t`, written around the base point `s`. -/
lemma truncHilbert_eq_integral_shift (t s ε : ℝ) :
    truncHilbert ε g t = (1 / π : ℝ) • ∫ y, g (s - y) * pvKer ε (y + (t - s)) := by
  unfold truncHilbert
  congr 1
  rw [← integral_indicator (measurableSet_lt_abs ε), ← integral_add_right_eq_self _ (t - s)]
  congr 1
  funext y
  unfold pvKer
  have e : t - (y + (t - s)) = s - y := by ring
  by_cases hx : ε < |y + (t - s)|
  · rw [Set.indicator_of_mem (show y + (t - s) ∈ {x : ℝ | ε < |x|} from hx),
      Set.indicator_of_mem (show y + (t - s) ∈ {x : ℝ | ε < |x|} from hx)]
    simp only [e, div_eq_mul_inv]
  · rw [Set.indicator_of_notMem (show y + (t - s) ∉ {x : ℝ | ε < |x|} from hx),
      Set.indicator_of_notMem (show y + (t - s) ∉ {x : ℝ | ε < |x|} from hx), mul_zero]

/-! ### Pointwise bounds -/

/-- Away from the origin the kernel difference is `O(δ / y²)`. -/
lemma pvKer_sub_le_far {d δ y : ℝ} (hδ : |d| = δ) (hy : 3 * δ < |y|) :
    ‖pvKer (2 * δ) (y + d) - pvKer (2 * δ) y‖ ≤ 2 * δ / |y| ^ 2 := by
  have hδ0 : 0 ≤ δ := hδ ▸ abs_nonneg d
  have hy0 : 0 < |y| := by linarith
  have hl : |y| - δ ≤ |y + d| := by
    have := abs_sub_abs_le_abs_sub y (-d)
    rwa [abs_neg, sub_neg_eq_add, hδ] at this
  have hyd0 : 0 < |y + d| := by linarith
  unfold pvKer
  rw [Set.indicator_of_mem (show y + d ∈ {x : ℝ | 2 * δ < |x|} by
      show 2 * δ < |y + d|; linarith),
    Set.indicator_of_mem (show y ∈ {x : ℝ | 2 * δ < |x|} by show 2 * δ < |y|; linarith)]
  have hy' : y ≠ 0 := abs_pos.1 hy0
  have hyd' : y + d ≠ 0 := abs_pos.1 hyd0
  have e : ((((y + d : ℝ) : ℂ))⁻¹ - (((y : ℝ) : ℂ))⁻¹) = (((y + d)⁻¹ - y⁻¹ : ℝ) : ℂ) := by
    push_cast; ring
  rw [e, Complex.norm_real, Real.norm_eq_abs, inv_sub_inv hyd' hy', abs_div, abs_mul,
    show y - (y + d) = -d by ring, abs_neg, hδ, div_le_div_iff₀ (mul_pos hyd0 hy0)
    (pow_pos hy0 2)]
  have h2 : |y| ≤ 2 * |y + d| := by linarith
  nlinarith [mul_le_mul_of_nonneg_left h2 (mul_nonneg hδ0 hy0.le)]

/-- The majorant of the integrand. -/
def psi (α C0 M δ : ℝ) (y : ℝ) : ℝ :=
  Set.indicator (Icc (-(3 * δ)) (3 * δ)) (fun _ => C0 * (3 * δ) ^ α / δ) y +
  Set.indicator (Ioi (3 * δ)) (fun r => 2 * δ * (C0 + M) * r ^ (α - 2)) |y| +
  Set.indicator (Icc (1 - δ) (1 + δ)) (fun _ => 3 / 2 * M) y +
  Set.indicator (Icc (-1 - δ) (-1 + δ)) (fun _ => 3 / 2 * M) y

lemma norm_integrand_le {α C0 M d δ s y : ℝ} (hα : 0 < α) (hC0 : 0 ≤ C0) (hM0 : 0 ≤ M)
    (hC : ∀ y t, |y - t| ≤ 1 → ‖g y - g t‖ ≤ C0 * |y - t| ^ α) (hM : ∀ y, ‖g y‖ ≤ M)
    (hδ : |d| = δ) (hδ0 : 0 < δ) (hδ3 : δ ≤ 1 / 3) :
    ‖g (s - y) * (pvKer (2 * δ) (y + d) - pvKer (2 * δ) y) -
        g s * (pvCut (2 * δ) (y + d) - pvCut (2 * δ) y)‖ ≤ psi α C0 M δ y := by
  have hε : 0 < 2 * δ := by linarith
  have hu : |y + d| ≤ |y| + δ := by
    have := abs_sub_abs_le_abs_sub (y + d) y
    rw [add_sub_cancel_left, hδ] at this; linarith
  have hl : |y| ≤ |y + d| + δ := by
    have := abs_sub_abs_le_abs_sub y (y + d)
    rw [show y - (y + d) = -d by ring, abs_neg, hδ] at this; linarith
  have hψ1 : 0 ≤ Set.indicator (Icc (-(3 * δ)) (3 * δ)) (fun _ => C0 * (3 * δ) ^ α / δ) y :=
    Set.indicator_nonneg (fun _ _ =>
      div_nonneg (mul_nonneg hC0 (Real.rpow_nonneg (by linarith) _)) hδ0.le) _
  have hψ2 : 0 ≤ Set.indicator (Ioi (3 * δ)) (fun r => 2 * δ * (C0 + M) * r ^ (α - 2)) |y| :=
    Set.indicator_nonneg (fun r hr => mul_nonneg (by nlinarith)
      (Real.rpow_nonneg (by have : 3 * δ < r := hr; linarith) _)) _
  have hψ3 : 0 ≤ Set.indicator (Icc (1 - δ) (1 + δ)) (fun _ => 3 / 2 * M) y :=
    Set.indicator_nonneg (fun _ _ => by linarith) _
  have hψ4 : 0 ≤ Set.indicator (Icc (-1 - δ) (-1 + δ)) (fun _ => 3 / 2 * M) y :=
    Set.indicator_nonneg (fun _ _ => by linarith) _
  have hgs : ∀ y : ℝ, |y| ≤ 1 → ‖g (s - y) - g s‖ ≤ C0 * |y| ^ α := by
    intro y hy
    have h := hC (s - y) s (by rw [show s - y - s = -y by ring, abs_neg]; exact hy)
    rwa [show s - y - s = -y by ring, abs_neg] at h
  rw [pvCut_eq, pvCut_eq]
  have hsplit : ∀ (a b P1 P0 c1 c0 : ℂ), a * (P1 - P0) - b * (c1 * P1 - c0 * P0) =
      (a - b * c0) * (P1 - P0) + b * (c0 - c1) * P1 := fun _ _ _ _ _ _ => by ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  -- the main part
  have hT1 : ‖(g (s - y) - g s * (if |y| ≤ 1 then (1 : ℂ) else 0)) *
      (pvKer (2 * δ) (y + d) - pvKer (2 * δ) y)‖ ≤
      Set.indicator (Icc (-(3 * δ)) (3 * δ)) (fun _ => C0 * (3 * δ) ^ α / δ) y +
      Set.indicator (Ioi (3 * δ)) (fun r => 2 * δ * (C0 + M) * r ^ (α - 2)) |y| := by
    rw [norm_mul]
    rcases le_or_gt |y| (3 * δ) with hy | hy
    · have hy1 : |y| ≤ 1 := by linarith
      rw [if_pos hy1, mul_one]
      have hP : ‖pvKer (2 * δ) (y + d) - pvKer (2 * δ) y‖ ≤ 1 / δ := by
        refine (norm_sub_le _ _).trans ?_
        have h1 := norm_pvKer_le hε (y + d)
        have h2 := norm_pvKer_le hε y
        have e : (2 * δ)⁻¹ + (2 * δ)⁻¹ = 1 / δ := by
          rw [← two_mul, mul_inv, ← mul_assoc, mul_inv_cancel₀ two_ne_zero, one_mul, one_div]
        linarith
      have hg1 : ‖g (s - y) - g s‖ ≤ C0 * (3 * δ) ^ α :=
        (hgs y hy1).trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (abs_nonneg _) hy hα.le) hC0)
      have hmem : y ∈ Icc (-(3 * δ)) (3 * δ) := abs_le.1 hy
      simp only [Set.indicator_of_mem hmem]
      calc ‖g (s - y) - g s‖ * ‖pvKer (2 * δ) (y + d) - pvKer (2 * δ) y‖
          ≤ C0 * (3 * δ) ^ α * (1 / δ) :=
            mul_le_mul hg1 hP (norm_nonneg _)
              (mul_nonneg hC0 (Real.rpow_nonneg (by linarith) _))
        _ = C0 * (3 * δ) ^ α / δ := by ring
        _ ≤ _ := le_add_of_nonneg_right hψ2
    · have hK := pvKer_sub_le_far hδ hy
      have hy0 : 0 < |y| := by linarith
      have hmem : |y| ∈ Ioi (3 * δ) := hy
      simp only [Set.indicator_of_mem hmem]
      have hr : |y| ^ (α - 2) = |y| ^ α / |y| ^ 2 := by rw [Real.rpow_sub hy0, Real.rpow_two]
      have hya : 0 ≤ |y| ^ α := Real.rpow_nonneg (abs_nonneg _) _
      have key : ‖g (s - y) - g s * (if |y| ≤ 1 then (1 : ℂ) else 0)‖ ≤
          (C0 + M) * |y| ^ α := by
        by_cases hy1 : |y| ≤ 1
        · rw [if_pos hy1, mul_one]
          refine (hgs y hy1).trans ?_
          nlinarith
        · rw [if_neg hy1, mul_zero, sub_zero]
          have : 1 ≤ |y| ^ α := Real.one_le_rpow (by linarith [not_le.1 hy1]) hα.le
          nlinarith [hM (s - y)]
      calc _ ≤ (C0 + M) * |y| ^ α * (2 * δ / |y| ^ 2) :=
            mul_le_mul key hK (norm_nonneg _) (by nlinarith)
        _ = 2 * δ * (C0 + M) * |y| ^ (α - 2) := by rw [hr]; ring
        _ ≤ _ := le_add_of_nonneg_left hψ1
  -- the cut-off mismatch near `|y| = 1`
  have hloc : 1 - δ ≤ |y| → |y| ≤ 1 + δ →
      3 / 2 * M ≤ Set.indicator (Icc (1 - δ) (1 + δ)) (fun _ => 3 / 2 * M) y +
        Set.indicator (Icc (-1 - δ) (-1 + δ)) (fun _ => 3 / 2 * M) y := by
    intro h1 h2
    rcases le_or_gt 0 y with hy | hy
    · rw [abs_of_nonneg hy] at h1 h2
      simp only [Set.indicator_of_mem (show y ∈ Icc (1 - δ) (1 + δ) from ⟨h1, h2⟩)]
      linarith
    · rw [abs_of_neg hy] at h1 h2
      simp only [Set.indicator_of_mem (show y ∈ Icc (-1 - δ) (-1 + δ) from
        ⟨by linarith, by linarith⟩)]
      linarith
  have hT2 : ‖g s * ((if |y| ≤ 1 then (1 : ℂ) else 0) - (if |y + d| ≤ 1 then (1 : ℂ) else 0)) *
      pvKer (2 * δ) (y + d)‖ ≤
      Set.indicator (Icc (1 - δ) (1 + δ)) (fun _ => 3 / 2 * M) y +
        Set.indicator (Icc (-1 - δ) (-1 + δ)) (fun _ => 3 / 2 * M) y := by
    rw [norm_mul, norm_mul]
    have hP0 := norm_nonneg (pvKer (2 * δ) (y + d))
    have hg0 := norm_nonneg (g s)
    have hgM := hM s
    by_cases h0 : |y| ≤ 1 <;> by_cases h1 : |y + d| ≤ 1
    · rw [if_pos h0, if_pos h1, sub_self, norm_zero, mul_zero, zero_mul]; linarith
    · rw [if_pos h0, if_neg h1, sub_zero, norm_one, mul_one]
      have hyd : 1 < |y + d| := not_le.1 h1
      have hP : ‖pvKer (2 * δ) (y + d)‖ ≤ 1 :=
        (norm_pvKer_le_inv_abs _ _).trans (inv_le_one_of_one_le₀ hyd.le)
      have := hloc (by linarith) (by linarith)
      nlinarith
    · rw [if_neg h0, if_pos h1, zero_sub, norm_neg, norm_one, mul_one]
      have hy1 : 1 < |y| := not_le.1 h0
      have hyd : 2 / 3 ≤ |y + d| := by linarith
      have hP : ‖pvKer (2 * δ) (y + d)‖ ≤ 3 / 2 := by
        have h1 := inv_anti₀ (by norm_num : (0 : ℝ) < 2 / 3) hyd
        have h2 : ((2 : ℝ) / 3)⁻¹ = 3 / 2 := by norm_num
        linarith [norm_pvKer_le_inv_abs (2 * δ) (y + d)]
      have := hloc (by linarith) (by linarith)
      nlinarith
    · rw [if_neg h0, if_neg h1, sub_self, norm_zero, mul_zero, zero_mul]; linarith
  unfold psi
  linarith

/-! ### Integrating the majorant -/

lemma integrable_indicator_Icc_const (a b c : ℝ) :
    Integrable (fun x => Set.indicator (Icc a b) (fun _ => c) x) :=
  (integrable_indicator_iff measurableSet_Icc).2 continuous_const.integrableOn_Icc

lemma integral_indicator_Icc_const {a b c : ℝ} (hab : a ≤ b) :
    ∫ x, Set.indicator (Icc a b) (fun _ => c) x = (b - a) * c := by
  rw [integral_indicator measurableSet_Icc, setIntegral_const, Real.volume_real_Icc_of_le hab,
    smul_eq_mul]

lemma integrable_comp_abs' {f : ℝ → ℝ} (hf : IntegrableOn f (Ioi 0)) :
    Integrable (fun x => f |x|) := by
  have hf' : IntegrableOn (fun x => f |x|) (Ioi 0) :=
    hf.congr_fun (fun x hx => by rw [abs_of_pos (show (0 : ℝ) < x from hx)]) measurableSet_Ioi
  have int_Iic : IntegrableOn (fun x ↦ f |x|) (Iic 0) := by
    rw [← Measure.map_neg_eq_self (volume : Measure ℝ)]
    let m : MeasurableEmbedding fun x : ℝ => -x := (Homeomorph.neg ℝ).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simp_rw [Function.comp_def, abs_neg, neg_preimage, neg_Iic, neg_zero]
    exact Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hf'
  have := int_Iic.union hf'
  rwa [Iic_union_Ioi, integrableOn_univ] at this

lemma integrableOn_rpow_indicator {a B α : ℝ} (ha : 0 < a) (hα : α < 1) :
    IntegrableOn (fun r => Set.indicator (Ioi a) (fun r => B * r ^ (α - 2)) r) (Ioi 0) := by
  have h : Integrable (Set.indicator (Ioi a) (fun r : ℝ => B * r ^ (α - 2))) :=
    (integrable_indicator_iff measurableSet_Ioi).2
      ((integrableOn_Ioi_rpow_of_lt (by linarith) ha).const_mul B)
  exact h.integrableOn

lemma setIntegral_rpow_indicator {a B α : ℝ} (ha : 0 < a) (hα : α < 1) :
    ∫ r in Ioi 0, Set.indicator (Ioi a) (fun r => B * r ^ (α - 2)) r =
      B * (a ^ (α - 1) / (1 - α)) := by
  rw [setIntegral_indicator measurableSet_Ioi,
    show Ioi (0 : ℝ) ∩ Ioi a = Ioi a from inter_eq_right.2 (Ioi_subset_Ioi ha.le),
    integral_const_mul, integral_Ioi_rpow_of_lt (by linarith) ha,
    show α - 2 + 1 = α - 1 by ring]
  have h1 : α - 1 ≠ 0 := by linarith
  have h2 : 1 - α ≠ 0 := by linarith
  field_simp
  ring

lemma integrable_psi {α C0 M δ : ℝ} (hδ0 : 0 < δ) (hα1 : α < 1) :
    Integrable (psi α C0 M δ) := by
  have i2 : Integrable (fun y : ℝ =>
      Set.indicator (Ioi (3 * δ)) (fun r => 2 * δ * (C0 + M) * r ^ (α - 2)) |y|) :=
    integrable_comp_abs' (integrableOn_rpow_indicator (by linarith) hα1)
  exact (((integrable_indicator_Icc_const _ _ _).add i2).add
    (integrable_indicator_Icc_const _ _ _)).add (integrable_indicator_Icc_const _ _ _)

lemma integral_psi_le {α C0 M δ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hC0 : 0 ≤ C0) (hM0 : 0 ≤ M)
    (hδ0 : 0 < δ) (hδ3 : δ ≤ 1 / 3) :
    ∫ y, psi α C0 M δ y ≤ (18 * C0 + 4 * (C0 + M) / (1 - α) + 6 * M) * δ ^ α := by
  have i2 : Integrable (fun y : ℝ =>
      Set.indicator (Ioi (3 * δ)) (fun r => 2 * δ * (C0 + M) * r ^ (α - 2)) |y|) :=
    integrable_comp_abs' (integrableOn_rpow_indicator (by linarith) hα1)
  have i1 := integrable_indicator_Icc_const (-(3 * δ)) (3 * δ) (C0 * (3 * δ) ^ α / δ)
  have i3 := integrable_indicator_Icc_const (1 - δ) (1 + δ) (3 / 2 * M)
  have i4 := integrable_indicator_Icc_const (-1 - δ) (-1 + δ) (3 / 2 * M)
  have i12 : Integrable (fun y : ℝ =>
      Set.indicator (Icc (-(3 * δ)) (3 * δ)) (fun _ => C0 * (3 * δ) ^ α / δ) y +
      Set.indicator (Ioi (3 * δ)) (fun r => 2 * δ * (C0 + M) * r ^ (α - 2)) |y|) := i1.add i2
  have i123 : Integrable (fun y : ℝ =>
      Set.indicator (Icc (-(3 * δ)) (3 * δ)) (fun _ => C0 * (3 * δ) ^ α / δ) y +
      Set.indicator (Ioi (3 * δ)) (fun r => 2 * δ * (C0 + M) * r ^ (α - 2)) |y| +
      Set.indicator (Icc (1 - δ) (1 + δ)) (fun _ => 3 / 2 * M) y) := i12.add i3
  unfold psi
  rw [integral_add i123 i4, integral_add i12 i3, integral_add i1 i2,
    integral_indicator_Icc_const (by linarith), integral_indicator_Icc_const (by linarith),
    integral_indicator_Icc_const (by linarith),
    integral_comp_abs (f := Set.indicator (Ioi (3 * δ)) (fun r => 2 * δ * (C0 + M) *
      r ^ (α - 2))), setIntegral_rpow_indicator (by linarith) hα1]
  -- estimates for the powers
  have h3δ : 0 < 3 * δ := by linarith
  have hD : 0 ≤ δ ^ α := Real.rpow_nonneg hδ0.le _
  have hP : (3 * δ) ^ α ≤ 3 * δ ^ α := by
    rw [Real.mul_rpow (by norm_num) hδ0.le]
    have : (3 : ℝ) ^ α ≤ 3 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hα1.le
      rwa [Real.rpow_one] at this
    nlinarith
  have hQ : δ * (3 * δ) ^ (α - 1) ≤ δ ^ α := by
    rw [Real.rpow_sub_one h3δ.ne']
    have : δ * ((3 * δ) ^ α / (3 * δ)) = (3 * δ) ^ α / 3 := by field_simp
    rw [this]; linarith
  have hδα : δ ≤ δ ^ α := Real.self_le_rpow_of_le_one hδ0.le (by linarith) hα1.le
  have h1α : 0 < 1 - α := by linarith
  have e1 : (3 * δ - -(3 * δ)) * (C0 * (3 * δ) ^ α / δ) = 6 * C0 * (3 * δ) ^ α := by
    field_simp; ring
  have e2 : 2 * (2 * δ * (C0 + M) * ((3 * δ) ^ (α - 1) / (1 - α))) =
      4 * (C0 + M) * (δ * (3 * δ) ^ (α - 1)) / (1 - α) := by ring
  have b2 : 4 * (C0 + M) * (δ * (3 * δ) ^ (α - 1)) / (1 - α) ≤
      4 * (C0 + M) * δ ^ α / (1 - α) :=
    (div_le_div_iff_of_pos_right h1α).2 (mul_le_mul_of_nonneg_left hQ (by linarith))
  have e3 : 4 * (C0 + M) * δ ^ α / (1 - α) = 4 * (C0 + M) / (1 - α) * δ ^ α := by ring
  rw [e1, e2]
  nlinarith

/-! ### The Hölder estimate -/

lemma norm_truncHilbert_sub_le' (hg : MemLp g 2) {α C0 M : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hC0 : 0 ≤ C0) (hM0 : 0 ≤ M)
    (hC : ∀ y t, |y - t| ≤ 1 → ‖g y - g t‖ ≤ C0 * |y - t| ^ α) (hM : ∀ y, ‖g y‖ ≤ M)
    {s t δ : ℝ} (hδ : |t - s| = δ) (hδ0 : 0 < δ) (hδ3 : δ ≤ 1 / 3) :
    ‖truncHilbert (2 * δ) g t - truncHilbert (2 * δ) g s‖ ≤
      (1 / π) * ((18 * C0 + 4 * (C0 + M) / (1 - α) + 6 * M) * δ ^ α) := by
  have hε : 0 < 2 * δ := by linarith
  obtain ⟨d, hd⟩ : ∃ d, d = t - s := ⟨_, rfl⟩
  have hδ' : |d| = δ := by rw [hd]; exact hδ
  rw [truncHilbert_eq_integral_shift t s, truncHilbert_eq_integral_shift s s, ← smul_sub,
    norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / π), ← hd]
  simp only [sub_self, add_zero]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have i1 := integrable_mul_pvKer_shift hg hε s d
  have i0 := integrable_mul_pvKer hg hε s
  have iQ1 : Integrable fun y => pvCut (2 * δ) (y + d) := (integrable_pvCut hε).comp_add_right d
  have iQ0 := integrable_pvCut hε
  have hQ1 : ∫ y, pvCut (2 * δ) (y + d) = 0 := by
    rw [integral_add_right_eq_self (pvCut (2 * δ)) d]; exact integral_pvCut _
  have hQ0 : ∫ y, pvCut (2 * δ) y = 0 := integral_pvCut _
  have e : (∫ y, g (s - y) * pvKer (2 * δ) (y + d)) - ∫ y, g (s - y) * pvKer (2 * δ) y =
      ∫ y, (g (s - y) * (pvKer (2 * δ) (y + d) - pvKer (2 * δ) y) -
        g s * (pvCut (2 * δ) (y + d) - pvCut (2 * δ) y)) := by
    have hfun : (fun y => g (s - y) * (pvKer (2 * δ) (y + d) - pvKer (2 * δ) y) -
        g s * (pvCut (2 * δ) (y + d) - pvCut (2 * δ) y)) =
        fun y => (g (s - y) * pvKer (2 * δ) (y + d) - g (s - y) * pvKer (2 * δ) y) -
          g s * (pvCut (2 * δ) (y + d) - pvCut (2 * δ) y) := funext fun y => by ring
    have i10 : Integrable (fun y => g (s - y) * pvKer (2 * δ) (y + d) -
        g (s - y) * pvKer (2 * δ) y) := i1.sub i0
    have iQ : Integrable (fun y => g s * (pvCut (2 * δ) (y + d) - pvCut (2 * δ) y)) :=
      (iQ1.sub iQ0).const_mul (g s)
    have iQ' : Integrable (fun y => pvCut (2 * δ) (y + d) - pvCut (2 * δ) y) := iQ1.sub iQ0
    rw [hfun, integral_sub i10 iQ, integral_sub i1 i0, integral_const_mul, integral_sub iQ1 iQ0,
      hQ1, hQ0]
    simp
  rw [e]
  refine (norm_integral_le_of_norm_le (integrable_psi hδ0 hα1)
    (Eventually.of_forall fun y => norm_integrand_le hα hC0 hM0 hC hM hδ' hδ0 hδ3)).trans ?_
  exact integral_psi_le hα hα1 hC0 hM0 hδ0 hδ3

/-- The Hölder estimate at scales `≤ 1/3`. -/
lemma holder_small (hg : MemLp g 2) {α C0 M : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hC0 : 0 ≤ C0) (hM0 : 0 ≤ M)
    (hC : ∀ y t, |y - t| ≤ 1 → ‖g y - g t‖ ≤ C0 * |y - t| ^ α) (hM : ∀ y, ‖g y‖ ≤ M)
    {s t : ℝ} (hst0 : 0 < |t - s|) (hst : |t - s| ≤ 1 / 3) :
    ‖hilbertR g t - hilbertR g s‖ ≤
      (1 / π) * (8 * C0 / α + (18 * C0 + 4 * (C0 + M) / (1 - α) + 6 * M)) * |t - s| ^ α := by
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = |t - s| := ⟨_, rfl⟩
  rw [← hδ] at hst0 hst ⊢
  have hε : 0 < 2 * δ := by linarith
  have hε1 : 2 * δ ≤ 1 := by linarith
  have ht := norm_truncHilbert_sub_le hg hα (hC · t) hε hε1
  have hs := norm_truncHilbert_sub_le hg hα (hC · s) hε hε1
  rw [← hilbertR_eq hg hα (hC · t)] at ht
  rw [← hilbertR_eq hg hα (hC · s)] at hs
  have hmid := norm_truncHilbert_sub_le' hg hα hα1 hC0 hM0 hC hM hδ.symm hst0 hst
  have h2 : (2 * δ) ^ α ≤ 2 * δ ^ α := by
    rw [Real.mul_rpow (by norm_num) hst0.le]
    have : (2 : ℝ) ^ α ≤ 2 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hα1.le
      rwa [Real.rpow_one] at this
    nlinarith [Real.rpow_nonneg hst0.le α]
  have hsplit : hilbertR g t - hilbertR g s =
      -(truncHilbert (2 * δ) g t - hilbertR g t) +
        (truncHilbert (2 * δ) g t - truncHilbert (2 * δ) g s) +
        (truncHilbert (2 * δ) g s - hilbertR g s) := by ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  rw [norm_neg]
  have hπ : 0 < 1 / π := by positivity
  have hb : 2 * C0 * ((2 * δ) ^ α / α) ≤ 2 * C0 * (2 * δ ^ α / α) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h2 hα.le) (by linarith)
  have hb' : 1 / π * (2 * C0 * ((2 * δ) ^ α / α)) ≤ 1 / π * (2 * C0 * (2 * δ ^ α / α)) :=
    mul_le_mul_of_nonneg_left hb hπ.le
  have e : 1 / π * (8 * C0 / α + (18 * C0 + 4 * (C0 + M) / (1 - α) + 6 * M)) * δ ^ α =
      1 / π * (2 * C0 * (2 * δ ^ α / α)) + 1 / π * (2 * C0 * (2 * δ ^ α / α)) +
        1 / π * ((18 * C0 + 4 * (C0 + M) / (1 - α) + 6 * M) * δ ^ α) := by ring
  rw [e]
  linarith

end PlemeljPrivalov

open PlemeljPrivalov in
/-- **Theorem A.1.6** (Plemelj–Privalov). -/
theorem holderHilbertStatement_holds : HolderHilbertStatement := by
  intro g α C hg hα hα1 hC
  have hC0 : ∀ y t, |y - t| ≤ 1 → ‖g y - g t‖ ≤ |C| * |y - t| ^ α := fun y t h =>
    (hC y t h).trans (mul_le_mul_of_nonneg_right (le_abs_self C)
      (Real.rpow_nonneg (abs_nonneg _) _))
  obtain ⟨M₀, hM₀⟩ := exists_bound_of_holder hg hα hC
  have hM : ∀ y, ‖g y‖ ≤ |M₀| := fun y => (hM₀ y).trans (le_abs_self _)
  set L := (1 / π) * (8 * |C| / α + (18 * |C| + 4 * (|C| + |M₀|) / (1 - α) + 6 * |M₀|))
    with hL
  have hL0 : 0 ≤ L := by
    have h1α : 0 < 1 - α := by linarith
    positivity
  have hstep : ∀ u v : ℝ, 0 < |v - u| → |v - u| ≤ 1 / 3 →
      ‖hilbertR g v - hilbertR g u‖ ≤ L * |v - u| ^ α := fun u v h0 h1 =>
    holder_small hg hα hα1 (abs_nonneg C) (abs_nonneg M₀) hC0 hM h0 h1
  refine ⟨3 * L, fun s t hst => ?_⟩
  rcases (abs_nonneg (s - t)).lt_or_eq with h0 | h0
  · -- three steps of length `|s - t| / 3`
    set e := (s - t) / 3 with he
    have he0 : |e| = |s - t| / 3 := by rw [he, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    have hstep' : ∀ u, ‖hilbertR g (u + e) - hilbertR g u‖ ≤ L * |e| ^ α := by
      intro u
      have h := hstep u (u + e) (by rw [add_sub_cancel_left, he0]; linarith)
        (by rw [add_sub_cancel_left, he0]; linarith)
      rwa [add_sub_cancel_left] at h
    have hpow : |e| ^ α ≤ |s - t| ^ α :=
      Real.rpow_le_rpow (abs_nonneg _) (by rw [he0]; linarith) hα.le
    have hs : s = t + e + e + e := by rw [he]; ring
    have hsplit : hilbertR g s - hilbertR g t =
        (hilbertR g (t + e + e + e) - hilbertR g (t + e + e)) +
          (hilbertR g (t + e + e) - hilbertR g (t + e)) + (hilbertR g (t + e) - hilbertR g t) := by
      rw [← hs]; ring
    rw [hsplit]
    have h1 := hstep' (t + e + e)
    have h2 := hstep' (t + e)
    have h3 := hstep' t
    have hn : ‖(hilbertR g (t + e + e + e) - hilbertR g (t + e + e)) +
        (hilbertR g (t + e + e) - hilbertR g (t + e)) + (hilbertR g (t + e) - hilbertR g t)‖ ≤
        ‖hilbertR g (t + e + e + e) - hilbertR g (t + e + e)‖ +
          ‖hilbertR g (t + e + e) - hilbertR g (t + e)‖ + ‖hilbertR g (t + e) - hilbertR g t‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    have hLp := mul_le_mul_of_nonneg_left hpow hL0
    linarith
  · rw [← h0, Real.zero_rpow hα.ne', mul_zero]
    have : s = t := by
      have := h0.symm
      rwa [abs_eq_zero, sub_eq_zero] at this
    rw [this, sub_self, norm_zero]

end DF
