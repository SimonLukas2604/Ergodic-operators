/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §2.2.2  Green functions, Weyl solutions, `m`-functions  (book pp. 143–146) and
# Corollary 2.5.2 (book p. 166)

The resolvent is `DF.res (schr V) z = (H - z)⁻¹` (`Ch1/BoundedOperators.lean`) and the Green
function is `G(n, m; z) = ⟨δₙ, (H - z)⁻¹ δₘ⟩` (2.2.24).

## Main results
* `DF.res_dlt_eq` — `(H - z) (H - z)⁻¹ δₘ = δₘ`, pointwise.
* Existence of Weyl solutions for `z ∈ ρ(H)` (discussion before Proposition 2.2.7):
  `DF.exists_weyl_top`, `DF.exists_weyl_bot` (nonzero solutions square-summable at `±∞`);
  uniqueness up to scaling: `DF.wronskian_eq_zero_of_sqSumTop` (in `Ch2/Schrodinger.lean`).
* `DF.wronskian_weyl_ne_zero` — `u⁻` and `u⁺` are linearly independent for `z ∈ ρ(H)`.
* **Proposition 2.2.7**: `DF.green_eq` —
  `G(n, m; z) = u⁻(n ∧ m) u⁺(n ∨ m) / (u⁻(0) u⁺(1) - u⁺(0) u⁻(1))`.
* `DF.weyl_ne_zero_of_im` — for `Im z ≠ 0`, Weyl solutions never vanish (proof of
  Proposition 2.2.8).
* (2.2.26)–(2.2.28), **Proposition 2.2.8**: `DF.mPlus`, `DF.mMinus`, `DF.mPlus_spec`,
  `DF.mMinus_spec`, `DF.mPlus_eq`, `DF.mMinus_eq`.
* **Corollary 2.5.2**: `DF.weyl_top_decay`, `DF.weyl_bot_decay` — the Weyl solutions decay
  exponentially (from the Combes–Thomas estimate).
-/
import DamanikFillman.Ch2.CombesThomas

noncomputable section

open scoped InnerProductSpace ComplexConjugate
open L2 Filter Topology Metric

namespace DF

variable {V : ℤ → ℝ} {z : ℂ}

lemma algebraMap_apply_L2' (z : ℂ) (ψ : L2 ℤ) : (algebraMap ℂ Op z) ψ = z • ψ := by
  simp [Algebra.algebraMap_eq_smul_one]

/-- `(H - z) (H - z)⁻¹ δₘ = δₘ`, evaluated at `n`. -/
theorem res_dlt_eq (hV : BddPot V) (hz : z ∈ resolventSet ℂ (schr V)) (m n : ℤ) :
    res (schr V) z (dlt m) (n - 1) + res (schr V) z (dlt m) (n + 1) +
      (V n : ℂ) * res (schr V) z (dlt m) n =
        z * res (schr V) z (dlt m) n + if n = m then 1 else 0 := by
  have h := congrArg (fun T : Op => T (dlt m)) (sub_mul_res hz)
  simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
    algebraMap_apply_L2', ContinuousLinearMap.one_apply] at h
  have h' := congrArg (fun f : L2 ℤ => f n) h
  simp only [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    schr_apply hV, dlt_apply] at h'
  rw [← h']; ring

/-- The sequence `(H - z)⁻¹ δₘ` solves (2.2.2) away from `m`. -/
lemma res_dlt_solves (hV : BddPot V) (hz : z ∈ resolventSet ℂ (schr V)) (m n : ℤ)
    (hn : n ≠ m) :
    res (schr V) z (dlt m) (n - 1) + res (schr V) z (dlt m) (n + 1) +
      (V n : ℂ) * res (schr V) z (dlt m) n = z * res (schr V) z (dlt m) n := by
  rw [res_dlt_eq hV hz, if_neg hn, add_zero]

lemma res_dlt_at (hV : BddPot V) (hz : z ∈ resolventSet ℂ (schr V)) (m : ℤ) :
    res (schr V) z (dlt m) (m - 1) + res (schr V) z (dlt m) (m + 1) +
      (V m : ℂ) * res (schr V) z (dlt m) m = z * res (schr V) z (dlt m) m + 1 := by
  rw [res_dlt_eq hV hz, if_pos rfl]

/-- A nonzero square-summable solution is impossible for `z ∈ ρ(H)`. -/
theorem eq_zero_of_mem_resolventSet (hV : BddPot V) (hz : z ∈ resolventSet ℂ (schr V))
    {u : ℤ → ℂ} (hu : IsSolution V z u) (hm : Memℓp u 2) : u = 0 := by
  have he := eigen_of_isSolution hV hu hm
  set ψ : L2 ℤ := ⟨u, hm⟩
  have h0 : (schr V - algebraMap ℂ Op z) ψ = 0 := by
    rw [ContinuousLinearMap.sub_apply, he, algebraMap_apply_L2', sub_self]
  have : ψ = 0 := by
    have := congrArg (fun T : Op => T ψ) (res_mul_sub hz)
    simp only [ContinuousLinearMap.mul_apply, h0, map_zero, ContinuousLinearMap.one_apply] at this
    exact this.symm
  funext n
  have := congrArg (fun f : L2 ℤ => f n) this
  simpa [ψ] using this

lemma res_fn (hV : BddPot V) (hz : z ∈ resolventSet ℂ (schr V)) (m : ℤ) :
    ∃ g : ℤ → ℂ, (∀ n, n ≠ m → g (n - 1) + g (n + 1) + (V n : ℂ) * g n = z * g n) ∧
      (g (m - 1) + g (m + 1) + (V m : ℂ) * g m = z * g m + 1) ∧ Memℓp g 2 :=
  ⟨fun n => res (schr V) z (dlt m) n, fun n hn => res_dlt_solves hV hz m n hn,
    res_dlt_at hV hz m, (res (schr V) z (dlt m)).2⟩

/-- Existence of a Weyl solution at `+∞`: for `z ∈ ρ(H)` there is a nonzero solution of
(2.2.2) that is square-summable at `+∞`. -/
theorem exists_weyl_top (hV : BddPot V) (hz : z ∈ resolventSet ℂ (schr V)) :
    ∃ u : ℤ → ℂ, IsSolution V z u ∧ u ≠ 0 ∧ SqSumTop u := by
  obtain ⟨ψ0, s0, a0', m0⟩ := res_fn hV hz 0
  obtain ⟨ψ1, s1, a1', m1⟩ := res_fn hV hz 1
  have hw0 : ∀ n, 0 ≤ n → solAt V z 0 (ψ0 0) (ψ0 1) n = ψ0 n :=
    agree_up (fun n hn => s0 n (by omega)) (isSolution_solAt _ _ _)
      (by simp) (by simpa using solAt_succ (V := V) (z := z) 0 (ψ0 0) (ψ0 1))
  have hw1 : ∀ n, 1 ≤ n → solAt V z 1 (ψ1 1) (ψ1 2) n = ψ1 n :=
    agree_up (fun n hn => s1 n (by omega)) (isSolution_solAt _ _ _)
      (by simp) (by have := solAt_succ (V := V) (z := z) 1 (ψ1 1) (ψ1 2); norm_num at this
                    exact this)
  have sq0 := (sqSumTop_iff_of_eventually hw0).mpr (sqSumTop_of_memℓp m0)
  have sq1 := (sqSumTop_iff_of_eventually hw1).mpr (sqSumTop_of_memℓp m1)
  by_cases h0 : solAt V z 0 (ψ0 0) (ψ0 1) = 0
  · by_cases h1 : solAt V z 1 (ψ1 1) (ψ1 2) = 0
    · exfalso
      have e00 : ψ0 0 = 0 := by rw [← hw0 0 le_rfl, h0]; rfl
      have e01 : ψ0 1 = 0 := by rw [← hw0 1 (by norm_num), h0]; rfl
      have e11 : ψ1 1 = 0 := by rw [← hw1 1 le_rfl, h1]; rfl
      have e12 : ψ1 2 = 0 := by rw [← hw1 2 (by norm_num), h1]; rfl
      norm_num at a0' a1'
      have em1 : ψ0 (-1) = 1 := by rw [e00, e01] at a0'; linear_combination a0'
      have e10 : ψ1 0 = 1 := by rw [e11, e12] at a1'; linear_combination a1'
      have ha0 : ∀ n, n ≤ 0 → solAt V z (-1) (ψ0 (-1)) (ψ0 0) n = ψ0 n :=
        agree_down (fun n hn => s0 n (by omega)) (isSolution_solAt _ _ _)
          (by have := solAt_succ (V := V) (z := z) (-1) (ψ0 (-1)) (ψ0 0); norm_num at this
              exact this) (by simp)
      have ha1 : ∀ n, n ≤ 1 → solAt V z 0 (ψ1 0) (ψ1 1) n = ψ1 n :=
        agree_down (fun n hn => s1 n (by omega)) (isSolution_solAt _ _ _)
          (by have := solAt_succ (V := V) (z := z) 0 (ψ1 0) (ψ1 1); norm_num at this
              exact this) (by simp)
      have sqa0 := (sqSumBot_iff_of_eventually ha0).mpr (sqSumBot_of_memℓp m0)
      have sqa1 := (sqSumBot_iff_of_eventually ha1).mpr (sqSumBot_of_memℓp m1)
      have hW := wronskian_eq_zero_of_sqSumBot (isSolution_solAt (V := V) (z := z) _ _ _)
        (isSolution_solAt (V := V) (z := z) _ _ _) sqa0 sqa1
      rw [← wronskian_const (isSolution_solAt (V := V) (z := z) _ _ _)
        (isSolution_solAt (V := V) (z := z) _ _ _) (-1), wronskian,
        show (-1 : ℤ) + 1 = 0 by norm_num, ha0 (-1) (by norm_num), ha0 0 le_rfl,
        ha1 (-1) (by norm_num), ha1 0 (by norm_num), em1, e10, e00] at hW
      norm_num at hW
    · exact ⟨_, isSolution_solAt _ _ _, h1, sq1⟩
  · exact ⟨_, isSolution_solAt _ _ _, h0, sq0⟩

/-- Existence of a Weyl solution at `-∞`. -/
theorem exists_weyl_bot (hV : BddPot V) (hz : z ∈ resolventSet ℂ (schr V)) :
    ∃ u : ℤ → ℂ, IsSolution V z u ∧ u ≠ 0 ∧ SqSumBot u := by
  obtain ⟨ψ0, s0, a0', m0⟩ := res_fn hV hz 0
  obtain ⟨ψ1, s1, a1', m1⟩ := res_fn hV hz (-1)
  have hv0 : ∀ n, n ≤ 0 → solAt V z (-1) (ψ0 (-1)) (ψ0 0) n = ψ0 n :=
    agree_down (fun n hn => s0 n (by omega)) (isSolution_solAt _ _ _)
      (by have := solAt_succ (V := V) (z := z) (-1) (ψ0 (-1)) (ψ0 0); norm_num at this
          exact this) (by simp)
  have hv1 : ∀ n, n ≤ -1 → solAt V z (-2) (ψ1 (-2)) (ψ1 (-1)) n = ψ1 n :=
    agree_down (fun n hn => s1 n (by omega)) (isSolution_solAt _ _ _)
      (by have := solAt_succ (V := V) (z := z) (-2) (ψ1 (-2)) (ψ1 (-1)); norm_num at this
          exact this) (by simpa using solAt_self (V := V) (z := z) (-2) (ψ1 (-2)) (ψ1 (-1)))
  have sq0 := (sqSumBot_iff_of_eventually hv0).mpr (sqSumBot_of_memℓp m0)
  have sq1 := (sqSumBot_iff_of_eventually hv1).mpr (sqSumBot_of_memℓp m1)
  by_cases h0 : solAt V z (-1) (ψ0 (-1)) (ψ0 0) = 0
  · by_cases h1 : solAt V z (-2) (ψ1 (-2)) (ψ1 (-1)) = 0
    · exfalso
      have e00 : ψ0 0 = 0 := by rw [← hv0 0 le_rfl, h0]; rfl
      have e0m : ψ0 (-1) = 0 := by rw [← hv0 (-1) (by norm_num), h0]; rfl
      have e1m : ψ1 (-1) = 0 := by rw [← hv1 (-1) le_rfl, h1]; rfl
      have e1m2 : ψ1 (-2) = 0 := by rw [← hv1 (-2) (by norm_num), h1]; rfl
      norm_num at a0' a1'
      have e01 : ψ0 1 = 1 := by rw [e00, e0m] at a0'; linear_combination a0'
      have e10 : ψ1 0 = 1 := by rw [e1m, e1m2] at a1'; linear_combination a1'
      have hb0 : ∀ n, 0 ≤ n → solAt V z 0 (ψ0 0) (ψ0 1) n = ψ0 n :=
        agree_up (fun n hn => s0 n (by omega)) (isSolution_solAt _ _ _) (by simp)
          (by simpa using solAt_succ (V := V) (z := z) 0 (ψ0 0) (ψ0 1))
      have hb1 : ∀ n, -1 ≤ n → solAt V z (-1) (ψ1 (-1)) (ψ1 0) n = ψ1 n :=
        agree_up (fun n hn => s1 n (by omega)) (isSolution_solAt _ _ _) (by simp) (by
            have := solAt_succ (V := V) (z := z) (-1) (ψ1 (-1)) (ψ1 0); norm_num at this
            norm_num; exact this)
      have sqb0 := (sqSumTop_iff_of_eventually hb0).mpr (sqSumTop_of_memℓp m0)
      have sqb1 := (sqSumTop_iff_of_eventually hb1).mpr (sqSumTop_of_memℓp m1)
      have hW := wronskian_eq_zero_of_sqSumTop (isSolution_solAt (V := V) (z := z) _ _ _)
        (isSolution_solAt (V := V) (z := z) _ _ _) sqb1 sqb0
      rw [wronskian, zero_add, hb1 0 (by norm_num), hb0 1 (by norm_num), hb0 0 le_rfl,
        e10, e01, e00] at hW
      norm_num at hW
    · exact ⟨_, isSolution_solAt _ _ _, h1, sq1⟩
  · exact ⟨_, isSolution_solAt _ _ _, h0, sq0⟩

lemma sqSumTop_smul {u : ℤ → ℂ} (h : SqSumTop u) (c : ℂ) : SqSumTop (fun n => c * u n) := by
  unfold SqSumTop at *
  refine (h.mul_left (‖c‖ ^ 2)).congr fun n => ?_
  simp [norm_mul, mul_pow]

lemma sqSumBot_smul {u : ℤ → ℂ} (h : SqSumBot u) (c : ℂ) : SqSumBot (fun n => c * u n) := by
  unfold SqSumBot at *
  refine (h.mul_left (‖c‖ ^ 2)).congr fun n => ?_
  simp [norm_mul, mul_pow]

/-- For `z ∈ ρ(H)`, nonzero Weyl solutions `u⁻` (at `-∞`) and `u⁺` (at `+∞`) are linearly
independent: `W = u⁻(0) u⁺(1) - u⁺(0) u⁻(1) ≠ 0`. -/
theorem wronskian_weyl_ne_zero (hV : BddPot V) (hz : z ∈ resolventSet ℂ (schr V))
    {um up : ℤ → ℂ} (hum : IsSolution V z um) (hup : IsSolution V z up) (hum0 : um ≠ 0)
    (hup0 : up ≠ 0) (hum2 : SqSumBot um) (hup2 : SqSumTop up) : wronskian um up 0 ≠ 0 := by
  intro hW
  obtain ⟨a, b, hab, h⟩ := (wronskian_eq_zero_iff hum hup).mp hW
  by_cases hb : b = 0
  · rcases hab with ha | hb'
    · apply hum0; funext n; have := h n; rw [hb, zero_mul, add_zero] at this
      exact (mul_eq_zero.mp this).resolve_left ha
    · exact hb' hb
  · have hup_eq : up = fun n => (-(a / b)) * um n := by
      funext n; have := h n; field_simp; linear_combination this
    have hbot : SqSumBot up := by rw [hup_eq]; exact sqSumBot_smul hum2 _
    exact hup0 (eq_zero_of_mem_resolventSet hV hz hup (memℓp_of_sqSum hup2 hbot))

/-- The candidate `φₘ(n) = u⁻(n ∧ m) u⁺(n ∨ m) / W` for `(H - z)⁻¹ δₘ`. -/
def greenFun (um up : ℤ → ℂ) (m n : ℤ) : ℂ := um (min n m) * up (max n m) / wronskian um up 0

lemma memℓp_greenFun {um up : ℤ → ℂ} (hum2 : SqSumBot um) (hup2 : SqSumTop up) (m : ℤ) :
    Memℓp (greenFun um up m) 2 := by
  apply memℓp_of_sqSum
  · have : ∀ n, m ≤ n → greenFun um up m n = (um m / wronskian um up 0) * up n := by
      intro n hn; simp only [greenFun, min_eq_right hn, max_eq_left hn]; ring
    exact (sqSumTop_iff_of_eventually this).mpr (sqSumTop_smul hup2 _)
  · have : ∀ n, n ≤ m → greenFun um up m n = (up m / wronskian um up 0) * um n := by
      intro n hn; simp only [greenFun, min_eq_left hn, max_eq_right hn]; ring
    exact (sqSumBot_iff_of_eventually this).mpr (sqSumBot_smul hum2 _)

/-- **Proposition 2.2.7**: for `z ∈ ρ(H)` and nonzero Weyl solutions `u⁻`, `u⁺`,
`G(n, m; z) = u⁻(n ∧ m) u⁺(n ∨ m) / (u⁻(0) u⁺(1) - u⁺(0) u⁻(1))` (2.2.25). -/
theorem green_eq (hV : BddPot V) (hz : z ∈ resolventSet ℂ (schr V))
    {um up : ℤ → ℂ} (hum : IsSolution V z um) (hup : IsSolution V z up) (hum0 : um ≠ 0)
    (hup0 : up ≠ 0) (hum2 : SqSumBot um) (hup2 : SqSumTop up) (n m : ℤ) :
    ⟪dlt n, res (schr V) z (dlt m)⟫_ℂ =
      um (min n m) * up (max n m) / (um 0 * up 1 - up 0 * um 1) := by
  have hW := wronskian_weyl_ne_zero hV hz hum hup hum0 hup0 hum2 hup2
  set φ : L2 ℤ := ⟨greenFun um up m, memℓp_greenFun hum2 hup2 m⟩
  have hφ : ∀ k, φ k = greenFun um up m k := fun k => rfl
  -- `(H - z) φ = δₘ`
  have hHφ : (schr V - algebraMap ℂ Op z) φ = dlt m := by
    ext k
    simp only [ContinuousLinearMap.sub_apply, algebraMap_apply_L2', lp.coeFn_sub, Pi.sub_apply,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, schr_apply hV, hφ, dlt_apply]
    rcases lt_trichotomy k m with hk | rfl | hk
    · simp only [greenFun, min_eq_left (by omega : k + 1 ≤ m), max_eq_right (by omega : k + 1 ≤ m),
        min_eq_left (by omega : k - 1 ≤ m), max_eq_right (by omega : k - 1 ≤ m),
        min_eq_left hk.le, max_eq_right hk.le, if_neg hk.ne]
      have := hum k
      field_simp
      linear_combination (up m) * this
    · simp only [greenFun, min_self, max_self, if_pos rfl, ite_true,
        min_eq_right (by omega : k ≤ k + 1), max_eq_left (by omega : k ≤ k + 1),
        min_eq_left (by omega : k - 1 ≤ k), max_eq_right (by omega : k - 1 ≤ k)]
      have h1 := hum k
      have hWk := wronskian_const hum hup k
      rw [wronskian] at hWk
      field_simp
      linear_combination (up k) * h1 + hWk
    · simp only [greenFun, min_eq_right (by omega : m ≤ k + 1), max_eq_left (by omega : m ≤ k + 1),
        min_eq_right (by omega : m ≤ k - 1), max_eq_left (by omega : m ≤ k - 1),
        min_eq_right hk.le, max_eq_left hk.le, if_neg hk.ne']
      have := hup k
      field_simp
      linear_combination (um m) * this
  have hres : res (schr V) z (dlt m) = φ := by
    rw [← hHφ, ← ContinuousLinearMap.mul_apply, res_mul_sub hz, ContinuousLinearMap.one_apply]
  rw [inner_dlt, hres, hφ, greenFun]
  rfl

/-! ### Nonvanishing of Weyl solutions for `Im z ≠ 0` -/

/-- `Im (conj (u k) · u (k+1))`. -/
def flux (u : ℤ → ℂ) (k : ℤ) : ℝ := (u k).re * (u (k + 1)).im - (u k).im * (u (k + 1)).re

lemma flux_step {u : ℤ → ℂ} (hu : IsSolution V z u) (m : ℤ) :
    flux u m - flux u (m - 1) = z.im * ((u m).re ^ 2 + (u m).im ^ 2) := by
  have h := hu m
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im] at hre him
  simp only [flux, sub_add_cancel]
  linear_combination (u m).re * him - (u m).im * hre

lemma flux_sum {u : ℤ → ℂ} (hu : IsSolution V z u) (n0 : ℤ) (h0 : u n0 = 0) (N : ℕ) :
    z.im * ∑ k ∈ Finset.range N, ((u (n0 + 1 + k)).re ^ 2 + (u (n0 + 1 + k)).im ^ 2) =
      flux u (n0 + N) := by
  induction N with
  | zero => simp [flux, h0]
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have := flux_step hu (n0 + 1 + N)
    rw [show n0 + 1 + (N : ℤ) - 1 = n0 + N by ring] at this
    push_cast
    rw [show n0 + ((N : ℤ) + 1) = n0 + 1 + N by ring]
    linarith

lemma tendsto_shift {u : ℤ → ℂ} (h : SqSumTop u) (c : ℤ) :
    Tendsto (fun N : ℕ => u (c + N)) atTop (𝓝 0) := by
  have h0 : Tendsto (fun n : ℕ => u n) atTop (𝓝 0) := tendsto_zero_of_summable_sq h
  have h1 : Tendsto (fun N : ℕ => (c + N).toNat) atTop atTop :=
    tendsto_atTop_atTop.mpr fun b => ⟨b + c.natAbs, fun N hN => by omega⟩
  refine (tendsto_congr' ?_).mp (h0.comp h1)
  rw [Filter.EventuallyEq, Filter.eventually_atTop]
  exact ⟨c.natAbs, fun N hN => by
    simp only [Function.comp]; congr 1; omega⟩

/-- Reflection `n ↦ -n`. -/
lemma isSolution_reflect {u : ℤ → ℂ} (hu : IsSolution V z u) :
    IsSolution (fun n => V (-n)) z (fun n => u (-n)) := by
  intro n
  have := hu (-n)
  simp only
  rw [show -(n - 1) = -n + 1 by ring, show -(n + 1) = -n - 1 by ring]
  linear_combination this

lemma isSolution_zero (V : ℤ → ℝ) (z : ℂ) : IsSolution V z (fun _ => 0) := by
  intro n; simp

/-- Proof of Proposition 2.2.8: for `Im z ≠ 0`, a nonzero solution square-summable at `+∞`
never vanishes. -/
theorem weyl_top_ne_zero (hz : z.im ≠ 0) {u : ℤ → ℂ} (hu : IsSolution V z u)
    (hu2 : SqSumTop u) (hne : u ≠ 0) (n0 : ℤ) : u n0 ≠ 0 := by
  intro h0
  set q := (u (n0 + 1)).re ^ 2 + (u (n0 + 1)).im ^ 2
  have hq0 : 0 ≤ q := by positivity
  have hbound : ∀ N : ℕ, 1 ≤ N → |z.im| * q ≤ |flux u (n0 + N)| := by
    intro N hN
    rw [← flux_sum hu n0 h0 N, abs_mul]
    gcongr
    have hle : q ≤ ∑ k ∈ Finset.range N, ((u (n0 + 1 + k)).re ^ 2 + (u (n0 + 1 + k)).im ^ 2) := by
      have := Finset.single_le_sum (f := fun k : ℕ => (u (n0 + 1 + k)).re ^ 2 +
        (u (n0 + 1 + k)).im ^ 2) (fun k _ => by positivity) (Finset.mem_range.mpr hN)
      simpa [q] using this
    exact hle.trans (le_abs_self _)
  have hA := tendsto_shift hu2 n0
  have hB : Tendsto (fun N : ℕ => u (n0 + N + 1)) atTop (𝓝 0) := by
    have := tendsto_shift hu2 (n0 + 1)
    refine (tendsto_congr fun N => ?_).mp this
    rw [show n0 + 1 + (N : ℤ) = n0 + N + 1 by ring]
  have hre : Continuous Complex.re := Complex.continuous_re
  have him : Continuous Complex.im := Complex.continuous_im
  have hflux : Tendsto (fun N : ℕ => |flux u (n0 + N)|) atTop (𝓝 0) := by
    have := (((hre.tendsto 0).comp hA).mul ((him.tendsto 0).comp hB)).sub
      (((him.tendsto 0).comp hA).mul ((hre.tendsto 0).comp hB))
    simp only [Complex.zero_re, Complex.zero_im, mul_zero, sub_zero] at this
    have := this.abs
    simpa [flux, Function.comp] using this
  have hle : |z.im| * q ≤ 0 :=
    ge_of_tendsto hflux (eventually_atTop.mpr ⟨1, fun N hN => hbound N hN⟩)
  have hzpos : 0 < |z.im| := abs_pos.mpr hz
  have hq : q = 0 := le_antisymm (by nlinarith) hq0
  have h1 : u (n0 + 1) = 0 := by
    apply Complex.ext
    · simp only [Complex.zero_re]; nlinarith [sq_nonneg (u (n0 + 1)).re, sq_nonneg (u (n0 + 1)).im]
    · simp only [Complex.zero_im]; nlinarith [sq_nonneg (u (n0 + 1)).re, sq_nonneg (u (n0 + 1)).im]
  apply hne
  funext n
  rcases le_or_gt n0 n with h | h
  · exact (agree_up (fun k _ => hu k) (isSolution_zero V z) h0.symm h1.symm n h).symm
  · refine (agree_down (b := n0 + 1) (fun k _ => hu k) (isSolution_zero V z) h1.symm
      (by rw [add_sub_cancel_right]; exact h0.symm) n (by omega)).symm

/-- For `Im z ≠ 0`, a nonzero solution square-summable at `-∞` never vanishes. -/
theorem weyl_bot_ne_zero (hz : z.im ≠ 0) {u : ℤ → ℂ} (hu : IsSolution V z u)
    (hu2 : SqSumBot u) (hne : u ≠ 0) (n0 : ℤ) : u n0 ≠ 0 := by
  have hne' : (fun n => u (-n)) ≠ 0 := by
    intro h; apply hne; funext n
    have := congrFun h (-n); simpa using this
  have := weyl_top_ne_zero hz (isSolution_reflect hu) hu2 hne' (-n0)
  simpa using this

lemma mem_resolventSet_of_im (hV : BddPot V) (hz : z.im ≠ 0) :
    z ∈ resolventSet ℂ (schr V) := by
  rw [mem_resolventSet_iff_notMem]
  intro h
  have := (isSelfAdjoint_schr hV).mem_spectrum_eq_re h
  apply hz
  rw [this]; simp

/-! ### `m`-functions: (2.2.26)–(2.2.28) and Proposition 2.2.8 -/

lemma sqSumTop_sub {u v : ℤ → ℂ} (hu : SqSumTop u) (hv : SqSumTop v) :
    SqSumTop (fun n => u n - v n) := by
  unfold SqSumTop at *
  refine ((hu.mul_left 2).add (hv.mul_left 2)).of_nonneg_of_le (fun n => by positivity)
    fun n => ?_
  have := norm_sub_le (u n) (v n)
  nlinarith [norm_nonneg (u n - v n), norm_nonneg (u n), norm_nonneg (v n),
    sq_nonneg (‖u n‖ - ‖v n‖)]

lemma sqSumBot_sub {u v : ℤ → ℂ} (hu : SqSumBot u) (hv : SqSumBot v) :
    SqSumBot (fun n => u n - v n) :=
  sqSumTop_sub (u := fun n => u (-n)) (v := fun n => v (-n)) hu hv

@[simp] lemma u₁_zero : u₁ V z 0 = 0 := by simp [u₁]
@[simp] lemma u₁_one : u₁ V z 1 = 1 := by simp [u₁]
@[simp] lemma u₂_zero : u₂ V z 0 = 1 := by simp [u₂]
@[simp] lemma u₂_one : u₂ V z 1 = 0 := by simp [u₂]

/-- Two solutions agreeing at `0` and `1` coincide. -/
lemma eq_of_isSolution {u v : ℤ → ℂ} (hu : IsSolution V z u) (hv : IsSolution V z v)
    (h0 : u 0 = v 0) (h1 : u 1 = v 1) : u = v := by
  rw [eq_solFrom hu, eq_solFrom hv, h0, h1]

/-- The Weyl–Titchmarsh function `m₊(z)`: the unique `m` with `u₂ - m u₁ ∈ ℓ²` at `+∞`
(2.2.27) (junk value `0` if no such `m` exists). -/
noncomputable def mPlus (V : ℤ → ℝ) (z : ℂ) : ℂ :=
  haveI := Classical.propDecidable
  if h : ∃ m : ℂ, SqSumTop (fun n => u₂ V z n - m * u₁ V z n) then h.choose else 0

/-- The Weyl–Titchmarsh function `m₋(z)`: the unique `m` with `u₁ - m u₂ ∈ ℓ²` at `-∞`
(2.2.28). -/
def mMinus (V : ℤ → ℝ) (z : ℂ) : ℂ :=
  haveI := Classical.propDecidable
  if h : ∃ m : ℂ, SqSumBot (fun n => u₁ V z n - m * u₂ V z n) then h.choose else 0

/-- **Proposition 2.2.8** (for `m₊`): for `Im z ≠ 0` and any nonzero Weyl solution `u⁺`,
`u⁺(0) ≠ 0`, `m₊(z) = -u⁺(1)/u⁺(0)` (2.2.26), `u₂ - m₊ u₁` is square-summable at `+∞`, and
`m₊` is the only scalar with this property. -/
theorem mPlus_eq (hz : z.im ≠ 0) {up : ℤ → ℂ} (hup : IsSolution V z up) (hup0 : up ≠ 0)
    (hup2 : SqSumTop up) :
    up 0 ≠ 0 ∧ mPlus V z = -(up 1) / up 0 ∧
      SqSumTop (fun n => u₂ V z n - mPlus V z * u₁ V z n) ∧
      ∀ m : ℂ, SqSumTop (fun n => u₂ V z n - m * u₁ V z n) → m = mPlus V z := by
  have h0 := weyl_top_ne_zero hz hup hup2 hup0 0
  set m0 := -(up 1) / up 0
  have hs1 : IsSolution V z (u₁ V z) := isSolution_solFrom _ _ _ _
  have hs2 : IsSolution V z (u₂ V z) := isSolution_solFrom _ _ _ _
  have hφ : (fun n => u₂ V z n - m0 * u₁ V z n) = fun n => (up 0)⁻¹ * up n := by
    apply eq_of_isSolution (V := V) (z := z)
    · intro n; have a := hs2 n; have b := hs1 n; simp only
      linear_combination a - m0 * b
    · intro n; have a := hup n; simp only; linear_combination (up 0)⁻¹ * a
    · simp [h0]
    · simp [m0]; field_simp
  have hsq0 : SqSumTop (fun n => u₂ V z n - m0 * u₁ V z n) := by
    rw [hφ]; exact sqSumTop_smul hup2 _
  have huniq : ∀ m : ℂ, SqSumTop (fun n => u₂ V z n - m * u₁ V z n) → m = m0 := by
    intro m hm
    by_contra hne
    have hd := sqSumTop_sub hm hsq0
    have hu1 : SqSumTop (u₁ V z) := by
      have := sqSumTop_smul hd (m0 - m)⁻¹
      refine (sqSumTop_iff_of_eventually (N := 0) fun n _ => ?_).mp this
      have : m0 - m ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
      field_simp; ring
    have hW := wronskian_eq_zero_of_sqSumTop hs1 hup hu1 hup2
    obtain ⟨a, b, hab, h⟩ := (wronskian_eq_zero_iff hs1 hup).mp hW
    have hb : b = 0 := by
      have := h 0; simp at this; exact this.resolve_right h0
    have ha : a = 0 := by have := h 1; simp [hb] at this; exact this
    rcases hab with h' | h' <;> contradiction
  have hex : ∃ m : ℂ, SqSumTop (fun n => u₂ V z n - m * u₁ V z n) := ⟨m0, hsq0⟩
  have hm : mPlus V z = m0 := by
    rw [mPlus, dif_pos hex]; exact huniq _ hex.choose_spec
  refine ⟨h0, hm, by rw [hm]; exact hsq0, fun m h => by rw [hm]; exact huniq m h⟩

/-- **Proposition 2.2.8** (for `m₋`): for `Im z ≠ 0` and any nonzero Weyl solution `u⁻` at
`-∞`, `u⁻(1) ≠ 0`, `m₋(z) = -u⁻(0)/u⁻(1)` (2.2.26), `u₁ - m₋ u₂` is square-summable at `-∞`,
and `m₋` is the only scalar with this property. -/
theorem mMinus_eq (hz : z.im ≠ 0) {um : ℤ → ℂ} (hum : IsSolution V z um) (hum0 : um ≠ 0)
    (hum2 : SqSumBot um) :
    um 1 ≠ 0 ∧ mMinus V z = -(um 0) / um 1 ∧
      SqSumBot (fun n => u₁ V z n - mMinus V z * u₂ V z n) ∧
      ∀ m : ℂ, SqSumBot (fun n => u₁ V z n - m * u₂ V z n) → m = mMinus V z := by
  have h1 := weyl_bot_ne_zero hz hum hum2 hum0 1
  set m0 := -(um 0) / um 1
  have hs1 : IsSolution V z (u₁ V z) := isSolution_solFrom _ _ _ _
  have hs2 : IsSolution V z (u₂ V z) := isSolution_solFrom _ _ _ _
  have hφ : (fun n => u₁ V z n - m0 * u₂ V z n) = fun n => (um 1)⁻¹ * um n := by
    apply eq_of_isSolution (V := V) (z := z)
    · intro n; have a := hs1 n; have b := hs2 n; simp only
      linear_combination a - m0 * b
    · intro n; have a := hum n; simp only; linear_combination (um 1)⁻¹ * a
    · simp [m0]; field_simp
    · simp [h1]
  have hsq0 : SqSumBot (fun n => u₁ V z n - m0 * u₂ V z n) := by
    rw [hφ]; exact sqSumBot_smul hum2 _
  have huniq : ∀ m : ℂ, SqSumBot (fun n => u₁ V z n - m * u₂ V z n) → m = m0 := by
    intro m hm
    by_contra hne
    have hd := sqSumBot_sub hm hsq0
    have hu2 : SqSumBot (u₂ V z) := by
      have := sqSumBot_smul hd (m0 - m)⁻¹
      refine (sqSumBot_iff_of_eventually (N := 0) fun n _ => ?_).mp this
      have : m0 - m ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
      field_simp; ring
    have hW := wronskian_eq_zero_of_sqSumBot hs2 hum hu2 hum2
    obtain ⟨a, b, hab, h⟩ := (wronskian_eq_zero_iff hs2 hum).mp hW
    have hb : b = 0 := by
      have := h 1; simp at this; exact this.resolve_right h1
    have ha : a = 0 := by have := h 0; simp [hb] at this; exact this
    rcases hab with h' | h' <;> contradiction
  have hex : ∃ m : ℂ, SqSumBot (fun n => u₁ V z n - m * u₂ V z n) := ⟨m0, hsq0⟩
  have hm : mMinus V z = m0 := by
    rw [mMinus, dif_pos hex]; exact huniq _ hex.choose_spec
  refine ⟨h1, hm, by rw [hm]; exact hsq0, fun m h => by rw [hm]; exact huniq m h⟩

/-- **Proposition 2.2.8**: for `Im z ≠ 0`, `m₊(z)` is the unique scalar with
`u₂ - m₊ u₁ ∈ ℓ²(ℤ₊)` (2.2.27). -/
theorem mPlus_spec (hV : BddPot V) (hz : z.im ≠ 0) :
    SqSumTop (fun n => u₂ V z n - mPlus V z * u₁ V z n) ∧
      ∀ m : ℂ, SqSumTop (fun n => u₂ V z n - m * u₁ V z n) → m = mPlus V z := by
  obtain ⟨up, h1, h2, h3⟩ := exists_weyl_top hV (mem_resolventSet_of_im hV hz)
  exact (mPlus_eq hz h1 h2 h3).2.2

/-- **Proposition 2.2.8**: for `Im z ≠ 0`, `m₋(z)` is the unique scalar with
`u₁ - m₋ u₂ ∈ ℓ²(ℤ₋)` (2.2.28). -/
theorem mMinus_spec (hV : BddPot V) (hz : z.im ≠ 0) :
    SqSumBot (fun n => u₁ V z n - mMinus V z * u₂ V z n) ∧
      ∀ m : ℂ, SqSumBot (fun n => u₁ V z n - m * u₂ V z n) → m = mMinus V z := by
  obtain ⟨um, h1, h2, h3⟩ := exists_weyl_bot hV (mem_resolventSet_of_im hV hz)
  exact (mMinus_eq hz h1 h2 h3).2.2

/-! ### Corollary 2.5.2: exponential decay of the Weyl solutions -/

lemma exists_ne_zero_01 {u : ℤ → ℂ} (hu : IsSolution V z u) (hne : u ≠ 0) :
    ∃ j : ℤ, (j = 0 ∨ j = 1) ∧ u j ≠ 0 := by
  by_contra h
  push Not at h
  exact hne (eq_zero_of_isSolution hu (h 0 (Or.inl rfl)) (h 1 (Or.inr rfl)))

/-- **Corollary 2.5.2** (at `+∞`): for `z ∈ ρ(H)` every solution square-summable at `+∞`
decays exponentially: `|u⁺(n)| ≤ C e^{-s n}`, `n ≥ 0`. -/
theorem weyl_top_decay (hV : BddPot V) (hz : z ∈ resolventSet ℂ (schr V)) {up : ℤ → ℂ}
    (hup : IsSolution V z up) (hup2 : SqSumTop up) :
    ∃ C s : ℝ, 0 < s ∧ ∀ n : ℕ, ‖up n‖ ≤ C * Real.exp (-s * n) := by
  by_cases hup0 : up = 0
  · exact ⟨0, 1, one_pos, fun n => by simp [hup0]⟩
  obtain ⟨um, hum, hum0, hum2⟩ := exists_weyl_bot hV hz
  have hW := wronskian_weyl_ne_zero hV hz hum hup hum0 hup0 hum2 hup2
  obtain ⟨j, hj, hjne⟩ := exists_ne_zero_01 hum hum0
  have : Nontrivial (L2 ℤ) := ⟨⟨dlt 0, 0, fun h => by
    have := congrArg (fun f : L2 ℤ => f 0) h; simp at this⟩⟩
  have hW' : um 0 * up 1 - up 0 * um 1 ≠ 0 := by simpa [wronskian] using hW
  set ε := infDist z (spectrum ℂ (schr V))
  set η := min (ε / 8) 1
  have hεpos : 0 < ε :=
    ((spectrum.isClosed (schr V)).notMem_iff_infDist_pos (spectrum.nonempty _)).mp
      (mem_resolventSet_iff_notMem.mp hz)
  have hη : 0 < η := lt_min (by positivity) one_pos
  set K := ‖wronskian um up 0‖ / ‖um j‖ * (2 * ε⁻¹) * Real.exp η
  have hK : 0 ≤ K := by positivity
  refine ⟨K + ‖up 0‖, η, hη, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp; positivity
  have hnj : j ≤ (n : ℤ) := by rcases hj with rfl | rfl <;> omega
  have hg := green_eq hV hz hum hup hum0 hup0 hum2 hup2 n j
  rw [min_eq_right hnj, max_eq_left hnj] at hg
  have hupn : up n = wronskian um up 0 * ⟪dlt n, res (schr V) z (dlt j)⟫_ℂ / um j := by
    rw [hg, wronskian, zero_add]; field_simp
  have hct := combes_thomas hV hz n j
  have hexp : Real.exp (-η * |(n : ℝ) - j|) ≤ Real.exp η * Real.exp (-η * n) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have : (n : ℝ) - 1 ≤ |(n : ℝ) - j| := by
      have : (j : ℝ) ≤ 1 := by rcases hj with rfl | rfl <;> norm_num
      exact le_trans (by linarith) (le_abs_self _)
    nlinarith
  have hpos : 0 < ‖um j‖ := norm_pos_iff.mpr hjne
  calc ‖up n‖ = ‖wronskian um up 0‖ / ‖um j‖ * ‖⟪dlt n, res (schr V) z (dlt j)⟫_ℂ‖ := by
        rw [hupn, norm_div, norm_mul]; ring
    _ ≤ ‖wronskian um up 0‖ / ‖um j‖ * (2 * ε⁻¹ * (Real.exp η * Real.exp (-η * n))) := by
        exact mul_le_mul_of_nonneg_left (hct.trans (mul_le_mul_of_nonneg_left hexp (by positivity))) (by positivity)
    _ = K * Real.exp (-η * n) := by ring
    _ ≤ (K + ‖up 0‖) * Real.exp (-η * n) := by gcongr; linarith [norm_nonneg (up 0)]

/-- **Corollary 2.5.2** (at `-∞`): `|u⁻(-n)| ≤ C e^{-s n}`, `n ≥ 0`. -/
theorem weyl_bot_decay (hV : BddPot V) (hz : z ∈ resolventSet ℂ (schr V)) {um : ℤ → ℂ}
    (hum : IsSolution V z um) (hum2 : SqSumBot um) :
    ∃ C s : ℝ, 0 < s ∧ ∀ n : ℕ, ‖um (-n)‖ ≤ C * Real.exp (-s * n) := by
  by_cases hum0 : um = 0
  · exact ⟨0, 1, one_pos, fun n => by simp [hum0]⟩
  obtain ⟨up, hup, hup0, hup2⟩ := exists_weyl_top hV hz
  have hW := wronskian_weyl_ne_zero hV hz hum hup hum0 hup0 hum2 hup2
  obtain ⟨j, hj, hjne⟩ := exists_ne_zero_01 hup hup0
  have : Nontrivial (L2 ℤ) := ⟨⟨dlt 0, 0, fun h => by
    have := congrArg (fun f : L2 ℤ => f 0) h; simp at this⟩⟩
  have hW' : um 0 * up 1 - up 0 * um 1 ≠ 0 := by simpa [wronskian] using hW
  set ε := infDist z (spectrum ℂ (schr V))
  set η := min (ε / 8) 1
  have hεpos : 0 < ε :=
    ((spectrum.isClosed (schr V)).notMem_iff_infDist_pos (spectrum.nonempty _)).mp
      (mem_resolventSet_iff_notMem.mp hz)
  have hη : 0 < η := lt_min (by positivity) one_pos
  set K := ‖wronskian um up 0‖ / ‖up j‖ * (2 * ε⁻¹) * Real.exp η
  have hK : 0 ≤ K := by positivity
  refine ⟨K + ‖um 0‖, η, hη, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp; positivity
  have hnj : -(n : ℤ) ≤ j := by rcases hj with rfl | rfl <;> omega
  have hg := green_eq hV hz hum hup hum0 hup0 hum2 hup2 (-n) j
  rw [min_eq_left hnj, max_eq_right hnj] at hg
  have humn : um (-n) = wronskian um up 0 * ⟪dlt (-n), res (schr V) z (dlt j)⟫_ℂ / up j := by
    rw [hg, wronskian, zero_add]; field_simp
  have hct := combes_thomas hV hz (-n) j
  have hexp : Real.exp (-η * |((-n : ℤ) : ℝ) - j|) ≤ Real.exp η * Real.exp (-η * n) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have : (n : ℝ) - 1 ≤ |((-n : ℤ) : ℝ) - j| := by
      have : (0 : ℝ) ≤ j := by rcases hj with rfl | rfl <;> norm_num
      push_cast
      rw [abs_of_nonpos (by linarith)]
      have : (j : ℝ) ≤ 1 := by rcases hj with rfl | rfl <;> norm_num
      linarith
    nlinarith
  have hpos : 0 < ‖up j‖ := norm_pos_iff.mpr hjne
  calc ‖um (-n)‖ = ‖wronskian um up 0‖ / ‖up j‖ * ‖⟪dlt (-n), res (schr V) z (dlt j)⟫_ℂ‖ := by
        rw [humn, norm_div, norm_mul]; ring
    _ ≤ ‖wronskian um up 0‖ / ‖up j‖ * (2 * ε⁻¹ * (Real.exp η * Real.exp (-η * n))) := by
        exact mul_le_mul_of_nonneg_left (hct.trans (mul_le_mul_of_nonneg_left hexp (by positivity))) (by positivity)
    _ = K * Real.exp (-η * n) := by ring
    _ ≤ (K + ‖um 0‖) * Real.exp (-η * n) := by gcongr; linarith [norm_nonneg (um 0)]

end DF
