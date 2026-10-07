import CriticalAMOHausdorff.ContinuedFractions

/-!
# Exponential small divisors and the scalar cohomological equation

Formalization of the arithmetic part of the proof of Lemma `t-lem:arithmetic-reducibility`
of `analytic_perturbations_amo.tex`:

* `Red.four_norm_le_norm_eT_sub_one` — `|e^{2πit} - 1| ≥ 4‖t‖_𝕋` (Jordan's inequality);
* `Red.small_divisor_norm` / `Red.small_divisor_exp` — the exponential small-divisor estimate
  `(t-eq:exponential-small-divisor)`: for irrational `α` with `β(α) < ∞` and `δ > 0` there is
  `c_δ > 0` with `|e^{2πikα} - 1| ≥ c_δ e^{-(β(α)+δ)|k|}` for `k ≠ 0`;
* `Red.chiHat_bound`, `Red.summable_chiHat_weighted` — the Fourier coefficients
  `χ̂(k) = p̂(k)/(e^{2πikα}-1)` satisfy `|χ̂(k)| ≤ C e^{-(2πh-β-δ)|k|}` and
  `∑ |χ̂(k)| e^{2πh'|k|} < ∞` for `h' < h - (β+δ)/(2π)`;
* `Red.cohomological_eq` — `χ(x+α) - χ(x) = p(x) - p̂(0)`;
* `Red.conj_chi_eq`, `Red.chi_im_eq_zero` — conjugate symmetry of `p̂` makes `χ` real.

Here `β(α) = AMO.beta α` (Paper I), used as the real number `(AMO.beta α).toReal`, and the
continued-fraction denominators are `CAH.q α n = (GenContFract.of α).dens n`. The
best-approximation property is `CAH.abs_delta_le_abs_mul_sub`.
-/

open Real Filter Complex ComplexConjugate

namespace Red

/-- `e(t) = exp(2πit)`. -/
noncomputable def eT (t : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * t)

lemma norm_eT (t : ℝ) : ‖eT t‖ = 1 := by
  rw [eT, show (2 * π * Complex.I * t : ℂ) = ((2 * π * t : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma eT_add (s t : ℝ) : eT (s + t) = eT s * eT t := by
  rw [eT, eT, eT, ← Complex.exp_add]; congr 1; push_cast; ring

lemma eT_zero : eT 0 = 1 := by simp [eT]

lemma eT_neg (t : ℝ) : eT (-t) = conj (eT t) := by
  rw [eT, eT, ← Complex.exp_conj]; congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]; push_cast; ring

lemma eT_sub_one (t : ℝ) :
    eT t - 1 = Complex.exp (π * Complex.I * t) * (2 * Complex.I * Complex.sin (π * t)) := by
  have h1 : Complex.exp (π * Complex.I * t) * Complex.exp (π * Complex.I * t) = eT t := by
    rw [← Complex.exp_add, eT]; ring_nf
  have h2 : Complex.exp (π * Complex.I * t) * Complex.exp (-(π * Complex.I * t)) = 1 := by
    rw [← Complex.exp_add]; simp
  rw [Complex.sin]
  rw [show -((π : ℂ) * t) * Complex.I = -(π * Complex.I * t) by ring,
    show ((π : ℂ) * t) * Complex.I = π * Complex.I * t by ring]
  linear_combination (Complex.I ^ 2) * h1 - (Complex.I ^ 2) * h2 + (eT t - 1) * Complex.I_sq

lemma norm_eT_sub_one (t : ℝ) : ‖eT t - 1‖ = 2 * |Real.sin (π * t)| := by
  rw [eT_sub_one, norm_mul,
    show (π * Complex.I * t : ℂ) = ((π * t : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, one_mul,
    show Complex.sin (π * t) = ((Real.sin (π * t) : ℝ) : ℂ) by push_cast; rfl,
    norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs]
  ring

/-- **Jordan's inequality on the circle**: `|e^{2πit} - 1| ≥ 4‖t‖_𝕋`. -/
theorem four_norm_le_norm_eT_sub_one (t : ℝ) :
    4 * ‖(t : UnitAddCircle)‖ ≤ ‖eT t - 1‖ := by
  rw [norm_eT_sub_one, UnitAddCircle.norm_eq]
  linarith [CAH.two_abs_sub_round_le_abs_sin t]

/-! ### Continued-fraction bookkeeping -/

lemma q_zero (α : ℝ) : CAH.q α 0 = 1 := by
  simp [CAH.q, AMO.cfDen]

lemma qN_zero (α : ℝ) : CAH.qN α 0 = 1 := by
  simp [CAH.qN, q_zero]

lemma qN_lt_qN_succ {α : ℝ} (hα : Irrational α) (m : ℕ) :
    CAH.qN α (m + 1) < CAH.qN α (m + 2) := by
  have := CAH.q_lt_succ hα (m + 1) (by omega)
  rw [← CAH.qN_cast hα, ← CAH.qN_cast hα] at this
  exact_mod_cast this

lemma le_qN_succ {α : ℝ} (hα : Irrational α) : ∀ m : ℕ, m ≤ CAH.qN α (m + 1)
  | 0 => Nat.zero_le _
  | m + 1 => by
    have h1 := le_qN_succ hα m
    have h2 : CAH.qN α (m + 1) < CAH.qN α (m + 1 + 1) := qN_lt_qN_succ hα m
    omega

/-- Every `n ≥ 1` lies in a block `q_j ≤ n < q_{j+1}`. -/
lemma exists_block {α : ℝ} (hα : Irrational α) (n : ℕ) (hn : 1 ≤ n) :
    ∃ j, CAH.qN α j ≤ n ∧ n < CAH.qN α (j + 1) := by
  classical
  have hex : ∃ j, n < CAH.qN α (j + 1) := ⟨n + 1, by have := le_qN_succ hα (n + 1); omega⟩
  refine ⟨Nat.find hex, ?_, Nat.find_spec hex⟩
  rcases h : Nat.find hex with _ | j
  · rw [qN_zero]; exact hn
  · have := Nat.find_min hex (show j < Nat.find hex by omega)
    omega

/-- Best approximation for integers of either sign: `‖kα‖_𝕋 ≥ |δ_j|` for `0 < |k| < q_{j+1}`. -/
lemma abs_delta_le_norm {α : ℝ} (hα : Irrational α) (j : ℕ) (k : ℤ) (hk : k ≠ 0)
    (hk' : k.natAbs < CAH.qN α (j + 1)) :
    |CAH.delta α j| ≤ ‖((k * α : ℝ) : UnitAddCircle)‖ := by
  rw [UnitAddCircle.norm_eq]
  rcases Int.natAbs_eq k with he | he
  · have hpos : (0 : ℤ) < k.natAbs := by omega
    have := CAH.abs_delta_le_abs_mul_sub hα j k.natAbs (round ((k : ℝ) * α)) hpos
      (by exact_mod_cast hk')
    rwa [show ((k.natAbs : ℤ) : ℝ) = (k : ℝ) by rw [← he]] at this
  · have hpos : (0 : ℤ) < k.natAbs := by omega
    have := CAH.abs_delta_le_abs_mul_sub hα j k.natAbs (-round ((k : ℝ) * α)) hpos
      (by exact_mod_cast hk')
    have hk2 : ((k.natAbs : ℤ) : ℝ) = -(k : ℝ) := by
      have h3 : (k : ℝ) = ((-(k.natAbs : ℤ) : ℤ) : ℝ) := congrArg _ he
      rw [h3, Int.cast_neg, neg_neg]
    rw [hk2, show -(k : ℝ) * α - ((-round ((k : ℝ) * α) : ℤ) : ℝ)
      = -((k : ℝ) * α - round ((k : ℝ) * α)) by push_cast; ring, abs_neg] at this
    exact this

/-! ### The exponential small-divisor estimate -/

/-- **Exponential small-divisor estimate** (`t-eq:exponential-small-divisor`, torus-norm form).
If `α` is irrational with `β(α) < ∞`, then for every `δ > 0` there is `c > 0` with
`‖kα‖_𝕋 ≥ c e^{-(β(α)+δ)|k|}` for all `k ≠ 0`. -/
theorem small_divisor_norm {α : ℝ} (hα : Irrational α) (hβ : AMO.beta α ≠ ⊤) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ c > 0, ∀ k : ℤ, k ≠ 0 →
      c * Real.exp (-((AMO.beta α).toReal + δ) * |(k : ℝ)|) ≤ ‖((k * α : ℝ) : UnitAddCircle)‖ := by
  set b := (AMO.beta α).toReal with hb
  have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
  have hlt : AMO.beta α < ENNReal.ofReal (b + δ) := by
    rw [← ENNReal.ofReal_toReal hβ, ← hb]
    exact ENNReal.ofReal_lt_ofReal_iff'.mpr ⟨by linarith, by linarith⟩
  unfold AMO.beta at hlt
  obtain ⟨J, hJ⟩ := eventually_atTop.1 (Filter.eventually_lt_of_limsup_lt hlt)
  have hgrowth : ∀ j ≥ J, CAH.q α (j + 1) ≤ Real.exp ((b + δ) * CAH.q α j) := by
    intro j hj
    have h1 := (ENNReal.ofReal_lt_ofReal_iff'.mp (hJ j hj)).1
    have hq := CAH.q_pos hα j
    have hq1 := CAH.q_pos hα (j + 1)
    rw [div_lt_iff₀ hq] at h1
    rw [← Real.exp_log hq1]
    exact Real.exp_le_exp.2 (by simpa [CAH.q] using h1.le)
  have hanti : Antitone (fun n => |CAH.delta α n|) :=
    antitone_nat_of_succ_le (fun n => (CAH.abs_delta_succ_lt hα n).le)
  have hdJ : 0 < |CAH.delta α J| := by
    have := (CAH.abs_delta_bounds hα J).1
    have := CAH.q_pos hα J
    have := CAH.q_pos hα (J + 1)
    exact lt_trans (by positivity) (CAH.abs_delta_bounds hα J).1
  refine ⟨min (1 / 2) |CAH.delta α J|, lt_min (by norm_num) hdJ, ?_⟩
  intro k hk
  obtain ⟨j, hj1, hj2⟩ := exists_block hα k.natAbs (by omega)
  have hbest := abs_delta_le_norm hα j k hk hj2
  have hkabs : ((k.natAbs : ℕ) : ℝ) = |(k : ℝ)| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hE : Real.exp (-(b + δ) * |(k : ℝ)|) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [abs_nonneg (k : ℝ)])
  rcases lt_or_ge j J with hjJ | hjJ
  · calc min (1 / 2) |CAH.delta α J| * Real.exp (-(b + δ) * |(k : ℝ)|)
        ≤ min (1 / 2) |CAH.delta α J| :=
          mul_le_of_le_one_right (le_min (by norm_num) hdJ.le) hE
      _ ≤ |CAH.delta α J| := min_le_right _ _
      _ ≤ |CAH.delta α j| := hanti hjJ.le
      _ ≤ _ := hbest
  · have hqj : CAH.q α j ≤ |(k : ℝ)| := by
      rw [← CAH.qN_cast hα, ← hkabs]; exact_mod_cast hj1
    have hq := CAH.q_pos hα j
    have hq1 := CAH.q_pos hα (j + 1)
    have hle := CAH.q_le_succ hα j
    have hg : CAH.q α (j + 1) ≤ Real.exp ((b + δ) * |(k : ℝ)|) :=
      (hgrowth j hjJ).trans (Real.exp_le_exp.2 (by nlinarith))
    have hex : Real.exp (-(b + δ) * |(k : ℝ)|) = (Real.exp ((b + δ) * |(k : ℝ)|))⁻¹ := by
      rw [← Real.exp_neg]; ring_nf
    have hpos := Real.exp_pos ((b + δ) * |(k : ℝ)|)
    calc min (1 / 2) |CAH.delta α J| * Real.exp (-(b + δ) * |(k : ℝ)|)
        ≤ 1 / 2 * Real.exp (-(b + δ) * |(k : ℝ)|) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) (Real.exp_pos _).le
      _ ≤ 1 / (CAH.q α (j + 1) + CAH.q α j) := by
          rw [hex, show (1 : ℝ) / 2 * (Real.exp ((b + δ) * |(k : ℝ)|))⁻¹
            = 1 / (2 * Real.exp ((b + δ) * |(k : ℝ)|)) by field_simp]
          exact one_div_le_one_div_of_le (by linarith) (by linarith)
      _ ≤ |CAH.delta α j| := (CAH.abs_delta_bounds hα j).1.le
      _ ≤ _ := hbest

/-- **Exponential small-divisor estimate** (`t-eq:exponential-small-divisor`):
`|e^{2πikα} - 1| ≥ c_δ e^{-(β(α)+δ)|k|}` for `k ≠ 0`. -/
theorem small_divisor_exp {α : ℝ} (hα : Irrational α) (hβ : AMO.beta α ≠ ⊤) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ c > 0, ∀ k : ℤ, k ≠ 0 →
      c * Real.exp (-((AMO.beta α).toReal + δ) * |(k : ℝ)|) ≤ ‖eT (k * α) - 1‖ := by
  obtain ⟨c, hc, h⟩ := small_divisor_norm hα hβ hδ
  refine ⟨4 * c, by positivity, fun k hk => ?_⟩
  have := four_norm_le_norm_eT_sub_one ((k : ℝ) * α)
  have := h k hk
  nlinarith

lemma eT_mul_sub_one_ne_zero {α : ℝ} (hα : Irrational α) {k : ℤ} (hk : k ≠ 0) :
    eT (k * α) - 1 ≠ 0 := by
  intro h0
  have h := four_norm_le_norm_eT_sub_one ((k : ℝ) * α)
  rw [h0, norm_zero, UnitAddCircle.norm_eq] at h
  have : (k : ℝ) * α - round ((k : ℝ) * α) = 0 := by
    have := abs_nonneg ((k : ℝ) * α - round ((k : ℝ) * α))
    exact abs_eq_zero.1 (by linarith)
  exact (hα.intCast_mul hk).ne_int (round ((k : ℝ) * α)) (by linarith)

/-! ### The scalar cohomological equation -/

/-- `∑_{k ∈ ℤ} e^{-ε|k|} < ∞` for `ε > 0`. -/
lemma summable_exp_neg_abs {ε : ℝ} (hε : 0 < ε) :
    Summable (fun k : ℤ => Real.exp (-ε * |(k : ℝ)|)) := by
  have hg : Summable (fun n : ℕ => Real.exp (-ε) ^ n) :=
    summable_geometric_of_lt_one (Real.exp_pos _).le ((Real.exp_lt_exp.2 (show -ε < 0 by linarith)).trans_eq Real.exp_zero)
  apply Summable.of_nat_of_neg
  · refine hg.congr (fun n => ?_)
    rw [← Real.exp_nat_mul]; congr 1; push_cast; rw [abs_of_nonneg (by positivity)]; ring
  · refine hg.congr (fun n => ?_)
    rw [← Real.exp_nat_mul]; congr 1; push_cast; rw [abs_neg, abs_of_nonneg (by positivity)]; ring

/-- The Fourier coefficients of the solution: `χ̂(0) = 0`, `χ̂(k) = p̂(k)/(e(kα) - 1)`. -/
noncomputable def chiHat (α : ℝ) (p : ℤ → ℂ) (k : ℤ) : ℂ :=
  if k = 0 then 0 else p k / (eT (k * α) - 1)

/-- The Fourier series `x ↦ ∑' k, a k e(kx)`. -/
noncomputable def fourierSum (a : ℤ → ℂ) (x : ℝ) : ℂ := ∑' k : ℤ, a k * eT (k * x)

/-- Exponential decay of the solution coefficients:
`|χ̂(k)| ≤ C' e^{-(2πh - β(α) - δ)|k|}`. -/
theorem chiHat_bound {α : ℝ} (hα : Irrational α) (hβ : AMO.beta α ≠ ⊤) {δ : ℝ} (hδ : 0 < δ)
    {p : ℤ → ℂ} {C h : ℝ} (hp : ∀ k : ℤ, ‖p k‖ ≤ C * Real.exp (-(2 * π * h) * |(k : ℝ)|)) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ k : ℤ, ‖chiHat α p k‖ ≤
      C' * Real.exp (-(2 * π * h - (AMO.beta α).toReal - δ) * |(k : ℝ)|) := by
  obtain ⟨c, hc, hsd⟩ := small_divisor_exp hα hβ hδ
  have hC : 0 ≤ C := by
    have := hp 0; simp at this; linarith [norm_nonneg (p 0)]
  refine ⟨C / c, by positivity, fun k => ?_⟩
  by_cases hk : k = 0
  · simp only [chiHat, hk, ↓reduceIte, norm_zero]; positivity
  · simp only [chiHat, hk, ↓reduceIte, norm_div]
    set b := (AMO.beta α).toReal
    have h1 := hsd k hk
    have hE1 := Real.exp_pos (-(b + δ) * |(k : ℝ)|)
    have hd : 0 < c * Real.exp (-(b + δ) * |(k : ℝ)|) := by positivity
    rw [div_le_iff₀ (hd.trans_le h1)]
    have hsplit : Real.exp (-(2 * π * h) * |(k : ℝ)|) =
        Real.exp (-(2 * π * h - b - δ) * |(k : ℝ)|) * Real.exp (-(b + δ) * |(k : ℝ)|) := by
      rw [← Real.exp_add]; ring_nf
    calc ‖p k‖ ≤ C * Real.exp (-(2 * π * h) * |(k : ℝ)|) := hp k
      _ = C / c * Real.exp (-(2 * π * h - b - δ) * |(k : ℝ)|) *
          (c * Real.exp (-(b + δ) * |(k : ℝ)|)) := by
          rw [hsplit]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)

/-- **Weighted summability** (Lemma `t-lem:arithmetic-reducibility`): if `2πh > β(α) + δ`
then `∑_k |χ̂(k)| e^{2πh'|k|} < ∞` for every `h' < h - (β(α)+δ)/(2π)` (in particular for
every `0 < h' < h - (β(α)+δ)/(2π)`). -/
theorem summable_chiHat_weighted {α : ℝ} (hα : Irrational α) (hβ : AMO.beta α ≠ ⊤) {δ : ℝ}
    (hδ : 0 < δ) {p : ℤ → ℂ} {C h : ℝ}
    (hp : ∀ k : ℤ, ‖p k‖ ≤ C * Real.exp (-(2 * π * h) * |(k : ℝ)|))
    {h' : ℝ} (hh' : h' < h - ((AMO.beta α).toReal + δ) / (2 * π)) :
    Summable (fun k : ℤ => ‖chiHat α p k‖ * Real.exp (2 * π * h' * |(k : ℝ)|)) := by
  obtain ⟨C', hC', hb⟩ := chiHat_bound hα hβ hδ hp
  set b := (AMO.beta α).toReal
  have hε : 0 < 2 * π * h - b - δ - 2 * π * h' := by
    have := Real.pi_pos
    rw [lt_sub_iff_add_lt, ← lt_sub_iff_add_lt', div_lt_iff₀ (by positivity)] at hh'
    nlinarith
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((summable_exp_neg_abs hε).mul_left C')
  calc ‖chiHat α p k‖ * Real.exp (2 * π * h' * |(k : ℝ)|)
      ≤ C' * Real.exp (-(2 * π * h - b - δ) * |(k : ℝ)|) * Real.exp (2 * π * h' * |(k : ℝ)|) :=
        mul_le_mul_of_nonneg_right (hb k) (Real.exp_pos _).le
    _ = C' * Real.exp (-(2 * π * h - b - δ - 2 * π * h') * |(k : ℝ)|) := by
        rw [mul_assoc, ← Real.exp_add]; ring_nf

/-- Absolute summability of the coefficients `χ̂` (the case `h' = 0`). -/
theorem summable_norm_chiHat {α : ℝ} (hα : Irrational α) (hβ : AMO.beta α ≠ ⊤) {δ : ℝ}
    (hδ : 0 < δ) {p : ℤ → ℂ} {C h : ℝ}
    (hp : ∀ k : ℤ, ‖p k‖ ≤ C * Real.exp (-(2 * π * h) * |(k : ℝ)|))
    (hh : (AMO.beta α).toReal + δ < 2 * π * h) :
    Summable (fun k : ℤ => ‖chiHat α p k‖) := by
  have h0 : (0 : ℝ) < h - ((AMO.beta α).toReal + δ) / (2 * π) := by
    rw [sub_pos, div_lt_iff₀ (by positivity)]; linarith
  simpa using summable_chiHat_weighted hα hβ hδ hp h0

lemma summable_fourier_of_norm {a : ℤ → ℂ} (ha : Summable (fun k => ‖a k‖)) (x : ℝ) :
    Summable (fun k : ℤ => a k * eT (k * x)) :=
  Summable.of_norm (by simpa [norm_mul, norm_eT] using ha)

/-- **Scalar cohomological equation** (Lemma `t-lem:arithmetic-reducibility`): with
`χ(x) = ∑ χ̂(k) e(kx)` and `p(x) = ∑ p̂(k) e(kx)`, one has `χ(x+α) - χ(x) = p(x) - p̂(0)`. -/
theorem cohomological_eq {α : ℝ} (hα : Irrational α) (hβ : AMO.beta α ≠ ⊤) {δ : ℝ}
    (hδ : 0 < δ) {p : ℤ → ℂ} {C h : ℝ}
    (hp : ∀ k : ℤ, ‖p k‖ ≤ C * Real.exp (-(2 * π * h) * |(k : ℝ)|))
    (hh : (AMO.beta α).toReal + δ < 2 * π * h) (x : ℝ) :
    fourierSum (chiHat α p) (x + α) - fourierSum (chiHat α p) x = fourierSum p x - p 0 := by
  have hχ := summable_norm_chiHat hα hβ hδ hp hh
  have hpos : 0 < h := by
    have := Real.pi_pos
    have : (0 : ℝ) ≤ (AMO.beta α).toReal := ENNReal.toReal_nonneg
    by_contra hneg; have := not_lt.1 hneg; nlinarith
  have hpn : Summable (fun k => ‖p k‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hp
      ((summable_exp_neg_abs (by positivity : 0 < 2 * π * h)).mul_left C)
  have hP := summable_fourier_of_norm hpn x
  unfold fourierSum
  rw [← (summable_fourier_of_norm hχ (x + α)).tsum_sub (summable_fourier_of_norm hχ x),
    hP.tsum_eq_add_tsum_ite 0]
  simp only [Int.cast_zero, zero_mul, eT_zero, mul_one, add_sub_cancel_left]
  congr 1; ext k
  by_cases hk : k = 0
  · simp [chiHat, hk]
  · simp only [chiHat, hk, ↓reduceIte]
    have hd := eT_mul_sub_one_ne_zero hα hk
    rw [mul_add, eT_add]
    field_simp

/-- Conjugate symmetry `χ̂(-k) = conj χ̂(k)` inherited from `p̂`. -/
lemma chiHat_neg {α : ℝ} {p : ℤ → ℂ} (hsym : ∀ k, p (-k) = conj (p k)) (k : ℤ) :
    chiHat α p (-k) = conj (chiHat α p k) := by
  by_cases hk : k = 0
  · simp [chiHat, hk]
  · simp only [chiHat, hk, neg_eq_zero, ↓reduceIte, map_div₀, map_sub, map_one, hsym]
    rw [← eT_neg]; push_cast; ring_nf

/-- **Reality of the solution**: if `p̂(-k) = conj p̂(k)` for all `k` (i.e. `p` is real), then
`conj χ(x) = χ(x)` for every real `x`. -/
theorem conj_chi_eq {α : ℝ} {p : ℤ → ℂ} (hsym : ∀ k, p (-k) = conj (p k)) (x : ℝ) :
    conj (fourierSum (chiHat α p) x) = fourierSum (chiHat α p) x := by
  unfold fourierSum
  rw [Complex.conj_tsum]
  rw [← (Equiv.neg ℤ).tsum_eq (fun k => chiHat α p k * eT (k * x))]
  congr 1; ext k
  simp only [Equiv.neg_apply, map_mul, chiHat_neg hsym, ← eT_neg]
  congr 2; push_cast; ring

/-- `χ` is real-valued when `p` is (`p̂(-k) = conj p̂(k)`). -/
theorem chi_im_eq_zero {α : ℝ} {p : ℤ → ℂ} (hsym : ∀ k, p (-k) = conj (p k)) (x : ℝ) :
    (fourierSum (chiHat α p) x).im = 0 :=
  Complex.conj_eq_iff_im.1 (conj_chi_eq hsym x)

end Red
