/-
# Quantization of acceleration  (paper §2, Theorem `quantized`; Remark `rational`)

* `citer` — complex iterates `A_n(z)`; `perIter A p q` — the period-`q` product
  `A_{(p/q)}(z) = A(z + (q-1)p/q) ⋯ A(z)`.
* `conj_relation` — `A(z) A_{(p/q)}(z) = A_{(p/q)}(z + p/q) A(z)`.
* `trace_perIter_periodic` — for coprime `p, q`, `tr A_{(p/q)}` is `1/q`-periodic.
* `specRad` — spectral radius of a `2 × 2` matrix, and the trace bounds
  `max(0, log(|tr B|/2)) ≤ log ρ(B) ≤ log(1 + |tr B|)` for `det B = 1`.  (The paper writes the
  upper bound as `max(0, log |tr|)`; that is false, e.g. for `tr B = 2i`, but any bound of the
  form `log ρ ≤ log |tr| + O(1)` suffices for the argument.)
* `L_rational` — `L(p/q, A) = (1/q) ∫ log ρ(A_{(p/q)}(x)) dx`.
* `quantized` — **Theorem (acceleration is quantized)**: for irrational `α`, `ω(α, A) ∈ ℤ`.

Proof of the integer part, following the paper:
* (Q1) `fcoef_indep`, `norm_fcoef_le_exp`, `hasSum_fcoef`, `fcoef_eq_zero_of_not_dvd` — Fourier
  coefficients of a bounded holomorphic `1`-periodic function on a strip (contour shift, decay,
  pointwise expansion; only modes divisible by `q` survive for `1/q`-periodic functions).
* `log_le_logMahlerMeasure`, `integral_log_trigP` — the Mahler-measure lower bound
  `∫ log |∑_{|k|≤k₀} b_k e^{2πikqx}| dx ≥ log |b_j| - 2k₀ log 2` (this is the step the paper
  leaves implicit when passing from the trace to `max_k (log|a_k| - 2πkqδ)`).
* (Q2) `rational_estimate`, `L_rational_asymptotics` — `L(p/q, A_t)` equals
  `max(0, max_{|k|≤k₀} (c_k - 2πkt))` up to `O(1/q)`, uniformly in `|t| ≤ ε'`, where
  `c_k = (1/q) log |a_k|` (note the `1/q` normalization).
* (Q3) `HasSupportSlopes.of_tendsto`, `mem_of_hasSupportSlopes` — pointwise limits of convex
  piecewise-linear functions with slopes in a finite set `S` keep supporting lines with slopes in
  `S`, so their right derivatives lie in `S`.
* (Q4) `accel_int` — assembly with `jks_continuity` (applied to `A_t = cshift A t`).
-/
import AvilaGlobal.Background

noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology Complex Set

namespace AvilaGlobal

open AMO

/-- Complex iterates `A_n(z) = A(z + (n-1)α) ⋯ A(z)`. -/
def citer (α : ℝ) (A : ℂ → M2) : ℕ → ℂ → M2
  | 0, _ => 1
  | n + 1, z => A (z + n * α) * citer α A n z

lemma citer_shift (α : ℝ) (A : ℂ → M2) (ε : ℝ) (n : ℕ) (x : ℝ) :
    citer α A n (x + ε * I) = iter α (shift A ε) n x := by
  induction n with
  | zero => simp [citer, iter]
  | succ n ih =>
    simp only [citer, iter, shift, ih]
    congr 1
    push_cast
    ring_nf

/-- The period product `A_{(p/q)}(z) = A(z + (q-1)p/q) ⋯ A(z)`. -/
def perIter (A : ℂ → M2) (p : ℤ) (q : ℕ) : ℂ → M2 := citer ((p : ℝ) / q) A q

lemma periodic_int {A : ℂ → M2} (hper : ∀ z, A (z + 1) = A z) (m : ℤ) (z : ℂ) :
    A (z + (m : ℂ)) = A z := by
  have h : Function.Periodic A 1 := hper
  simpa using (h.int_mul m) z

lemma citer_succ' (α : ℝ) (A : ℂ → M2) (n : ℕ) (z : ℂ) :
    citer α A (n + 1) z = citer α A n (z + α) * A z := by
  induction n generalizing z with
  | zero => simp [citer]
  | succ n ih =>
    rw [citer, ih, citer, ← mul_assoc]
    congr 3
    push_cast
    ring

lemma citer_periodic {A : ℂ → M2} (hper : ∀ z, A (z + 1) = A z) (α : ℝ) (n : ℕ) (z : ℂ) :
    citer α A n (z + 1) = citer α A n z := by
  induction n with
  | zero => rfl
  | succ n ih => rw [citer, citer, ih, add_right_comm, hper]

/-- `A(z) A_{(p/q)}(z) = A_{(p/q)}(z + p/q) A(z)` for `1`-periodic `A`. -/
theorem conj_relation {A : ℂ → M2} (hper : ∀ z, A (z + 1) = A z) (p : ℤ) {q : ℕ} (hq : 0 < q)
    (z : ℂ) :
    A z * perIter A p q z = perIter A p q (z + (p : ℂ) / q) * A z := by
  unfold perIter
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hα : (((p : ℝ) / q : ℝ) : ℂ) = (p : ℂ) / q := by push_cast; ring
  have h1 := citer_succ' ((p : ℝ) / q) A q z
  rw [hα] at h1
  have h2 : citer ((p : ℝ) / q) A (q + 1) z = A z * citer ((p : ℝ) / q) A q z := by
    rw [citer, hα]
    congr 1
    have : (q : ℂ) * ((p : ℂ) / q) = p := by field_simp
    rw [this, periodic_int hper]
  rw [← h2, h1]

/-- For coprime `p, q` (`q ≥ 1`) and an `SL(2,ℂ)`-valued `1`-periodic `A`, the trace of
`A_{(p/q)}` is `1/q`-periodic. -/
theorem trace_perIter_periodic {A : ℂ → M2} (hper : ∀ z, A (z + 1) = A z)
    {p : ℤ} {q : ℕ} (hq : 0 < q) (hpq : IsCoprime p q) (z : ℂ)
    (hdet : ∀ w : ℂ, w.im = z.im → (A w).det = 1) :
    (perIter A p q (z + 1 / q)).trace = (perIter A p q z).trace := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have step : ∀ w : ℂ, w.im = z.im →
      (perIter A p q (w + (p : ℂ) / q)).trace = (perIter A p q w).trace := by
    intro w hw
    have hc := conj_relation hper p hq w
    have hu : IsUnit (A w).det := by rw [hdet w hw]; exact isUnit_one
    have : perIter A p q (w + (p : ℂ) / q) = A w * perIter A p q w * (A w)⁻¹ := by
      rw [hc, mul_assoc, mul_nonsing_inv _ hu, mul_one]
    rw [this, Matrix.trace_mul_comm, ← mul_assoc, nonsing_inv_mul _ hu, one_mul]
  have stepk : ∀ k : ℕ,
      (perIter A p q (z + ((k * ((p : ℝ) / q) : ℝ) : ℂ))).trace = (perIter A p q z).trace := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e : z + ((((k + 1 : ℕ) : ℝ) * ((p : ℝ) / q) : ℝ) : ℂ) =
          (z + ((k * ((p : ℝ) / q) : ℝ) : ℂ)) + (p : ℂ) / q := by push_cast; ring
      rw [e, step _ (by simp), ih]
  have hBper : ∀ (w : ℂ) (m : ℤ), perIter A p q (w + m) = perIter A p q w := by
    intro w m
    have h : Function.Periodic (perIter A p q) 1 := fun w => citer_periodic hper _ _ w
    simpa using (h.int_mul m) w
  obtain ⟨u, v, huv⟩ := hpq
  obtain ⟨t, ht⟩ : ∃ t : ℤ, t = u / (q : ℤ) := ⟨_, rfl⟩
  have hk0 : 0 ≤ u % (q : ℤ) := Int.emod_nonneg _ (by omega)
  set k : ℕ := (u % (q : ℤ)).toNat with hkdef
  have hk : (k : ℤ) = u - q * t := by
    rw [hkdef, Int.toNat_of_nonneg hk0, Int.emod_def, ht]
  have hkC : (k : ℂ) = (u : ℂ) - (q : ℂ) * (t : ℂ) := by exact_mod_cast hk
  have huvC : (u : ℂ) * p + (v : ℂ) * q = 1 := by exact_mod_cast huv
  have hqinv : (q : ℂ) * (q : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hq'
  have E : z + 1 / q + ((-(v + t * p) : ℤ) : ℂ) = z + ((k * ((p : ℝ) / q) : ℝ) : ℂ) := by
    push_cast
    rw [hkC]
    linear_combination (-(q : ℂ)⁻¹) * huvC + ((v : ℂ) + t * p) * hqinv
  rw [← hBper (z + 1 / q) (-(v + t * p)), E, stepk]

/-- The spectral radius `ρ(B) = lim ‖Bⁿ‖^{1/n}`. -/
def specRad (B : M2) : ℝ := limUnder atTop fun n : ℕ => ‖B ^ n‖ ^ (1 / (n : ℝ))

lemma spectralRadius_ne_top (B : M2) : spectralRadius ℂ B ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.coe_ne_top (spectralRadius_le_nnnorm B)

lemma tendsto_specRad (B : M2) :
    Tendsto (fun n : ℕ => ‖B ^ n‖ ^ (1 / (n : ℝ))) atTop (𝓝 (specRad B)) := by
  have h := (ENNReal.tendsto_toReal (spectralRadius_ne_top B)).comp
    (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius B)
  have h' : Tendsto (fun n : ℕ => ‖B ^ n‖ ^ (1 / (n : ℝ))) atTop
      (𝓝 (spectralRadius ℂ B).toReal) := by
    refine h.congr fun n => ?_
    simp only [Function.comp, ← ENNReal.toReal_rpow, ENNReal.coe_toReal, coe_nnnorm]
  rw [specRad, h'.limUnder_eq]
  exact h'

lemma specRad_eq_toReal (B : M2) : specRad B = (spectralRadius ℂ B).toReal := by
  have h := (ENNReal.tendsto_toReal (spectralRadius_ne_top B)).comp
    (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius B)
  have h' : Tendsto (fun n : ℕ => ‖B ^ n‖ ^ (1 / (n : ℝ))) atTop
      (𝓝 (spectralRadius ℂ B).toReal) := by
    refine h.congr fun n => ?_
    simp only [Function.comp, ← ENNReal.toReal_rpow, ENNReal.coe_toReal, coe_nnnorm]
  rw [specRad, h'.limUnder_eq]

lemma mem_spectrum_iff_M2 {B : M2} (hB : B.det = 1) (k : ℂ) :
    k ∈ spectrum ℂ B ↔ k ^ 2 - B.trace * k + 1 = 0 := by
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not]
  have key : (algebraMap ℂ M2 k - B).det = k ^ 2 - B.trace * k + 1 := by
    rw [Matrix.det_fin_two] at hB
    rw [Matrix.det_fin_two, Matrix.trace_fin_two]
    simp [Matrix.algebraMap_matrix_apply]
    linear_combination hB
  rw [key]

lemma specRad_of_roots {B : M2} (hB : B.det = 1) {a b : ℂ} (hab : a * b = 1)
    (hsum : a + b = B.trace) (hb : ‖b‖ ≤ 1) (ha : 1 ≤ ‖a‖) : specRad B = ‖a‖ := by
  have hmem : ∀ k, k ∈ spectrum ℂ B ↔ k = a ∨ k = b := by
    intro k
    rw [mem_spectrum_iff_M2 hB, ← hsum]
    have : k ^ 2 - (a + b) * k + 1 = (k - a) * (k - b) := by linear_combination (-1 : ℂ) * hab
    rw [this, mul_eq_zero, sub_eq_zero, sub_eq_zero]
  have hrad : spectralRadius ℂ B = ‖a‖₊ := by
    apply le_antisymm
    · rw [spectralRadius_eq_of_unital]
      refine iSup₂_le fun k hk => ?_
      rcases (hmem k).1 hk with rfl | rfl
      · exact le_rfl
      · have : ‖k‖₊ ≤ ‖a‖₊ := by
          rw [← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm]; linarith
        exact_mod_cast this
    · rw [spectralRadius_eq_of_unital]
      exact le_iSup₂ (f := fun k _ => (‖k‖₊ : ENNReal)) a ((hmem a).2 (Or.inl rfl))
  rw [specRad_eq_toReal, hrad]
  simp

lemma specRad_aux {B : M2} (hB : B.det = 1) :
    ∃ μ ν : ℂ, μ * ν = 1 ∧ μ + ν = B.trace ∧ ‖ν‖ ≤ 1 ∧ 1 ≤ ‖μ‖ ∧ specRad B = ‖μ‖ := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (B.trace ^ 2 - 4) two_pos
  set t := B.trace
  have hab : (t + s) / 2 * ((t - s) / 2) = 1 := by linear_combination (-1/4 : ℂ) * hs
  have hsum : (t + s) / 2 + (t - s) / 2 = t := by ring
  have hn : ‖(t + s) / 2‖ * ‖(t - s) / 2‖ = 1 := by rw [← norm_mul, hab, norm_one]
  by_cases h : 1 ≤ ‖(t + s) / 2‖
  · have hb : ‖(t - s) / 2‖ ≤ 1 := by
      nlinarith [norm_nonneg ((t - s) / 2)]
    exact ⟨_, _, hab, hsum, hb, h, specRad_of_roots hB hab hsum hb h⟩
  · push Not at h
    have hb : 1 ≤ ‖(t - s) / 2‖ := by
      nlinarith [norm_nonneg ((t - s) / 2), norm_nonneg ((t + s) / 2)]
    have hab' : (t - s) / 2 * ((t + s) / 2) = 1 := by rw [mul_comm]; exact hab
    have hsum' : (t - s) / 2 + (t + s) / 2 = t := by ring
    exact ⟨_, _, hab', hsum', h.le, hb, specRad_of_roots hB hab' hsum' h.le hb⟩

/-- For `B ∈ SL(2,ℂ)`, `ρ(B) = |μ|` where `μ` is an eigenvalue of modulus `≥ 1`, i.e. a root of
`μ² - (tr B) μ + 1 = 0`. -/
theorem specRad_eq {B : M2} (hB : B.det = 1) :
    ∃ μ : ℂ, μ ^ 2 - B.trace * μ + 1 = 0 ∧ 1 ≤ ‖μ‖ ∧ specRad B = ‖μ‖ := by
  obtain ⟨μ, ν, hμν, hsum, -, h1, h2⟩ := specRad_aux hB
  refine ⟨μ, ?_, h1, h2⟩
  rw [← hsum]
  linear_combination (-1 : ℂ) * hμν

/-- Trace bounds for the spectral radius on `SL(2,ℂ)`. -/
theorem log_specRad_bounds {B : M2} (hB : B.det = 1) :
    max 0 (Real.log (‖B.trace‖ / 2)) ≤ Real.log (specRad B) ∧
      Real.log (specRad B) ≤ Real.log (1 + ‖B.trace‖) := by
  obtain ⟨μ, ν, hμν, hsum, hν, hμ, hρ⟩ := specRad_aux hB
  rw [hρ]
  have ht1 : ‖B.trace‖ ≤ 2 * ‖μ‖ := by
    rw [← hsum]; linarith [norm_add_le μ ν]
  have ht2 : ‖μ‖ ≤ 1 + ‖B.trace‖ := by
    have : μ = B.trace - ν := by rw [← hsum]; ring
    rw [this]; linarith [norm_sub_le B.trace ν]
  refine ⟨max_le (Real.log_nonneg hμ) ?_, Real.log_le_log (by linarith) ht2⟩
  rcases eq_or_lt_of_le (norm_nonneg B.trace) with h0 | h0
  · rw [← h0]; simpa using Real.log_nonneg hμ
  · exact Real.log_le_log (by positivity) (by linarith)

lemma one_le_specRad {B : M2} (hB : B.det = 1) : 1 ≤ specRad B := by
  obtain ⟨μ, ν, -, -, -, h1, h2⟩ := specRad_aux hB
  rw [h2]; exact h1

lemma lyapunov_rational_aux {A : ℝ → M2} (hS : IsSLCocycle A) {α : ℝ} {q : ℕ} (hq : 0 < q)
    (p : ℤ) (hαq : (q : ℝ) * α = p) :
    lyapunov α A = (1 / (q : ℝ)) * ∫ x in (0 : ℝ)..1, Real.log (specRad (iter α A q x)) := by
  have hper_iter : ∀ (x : ℝ) (m : ℤ), iter α A q (x + m) = iter α A q x := by
    intro x m
    have h := iter_periodic (α := α) hS.periodic q
    simpa using (h.int_mul m) x
  have hpow : ∀ m : ℕ, ∀ x, iter α A (q * m) x = iter α A q x ^ m := by
    intro m
    induction m with
    | zero => intro x; simp [iter]
    | succ m ih =>
      intro x
      rw [Nat.mul_succ, iter_add, ih, pow_succ']
      congr 1
      have : x + ((q * m : ℕ) : ℝ) * α = x + ((m * p : ℤ) : ℝ) := by
        push_cast
        rw [mul_comm (q : ℝ), mul_assoc, hαq]
      rw [this]
      exact hper_iter x (m * p)
  have hdetB : ∀ x, (iter α A q x).det = 1 := det_iter hS.det_eq_one q
  have hnormpos : ∀ (m : ℕ) x, 0 < ‖iter α A q x ^ m‖ := by
    intro m x
    have : (iter α A q x ^ m).det = 1 := by rw [Matrix.det_pow, hdetB, one_pow]
    exact zero_lt_one.trans_le (one_le_norm_of_det_eq_one this)
  have hnorm1 : ∀ (m : ℕ) x, 1 ≤ ‖iter α A q x ^ m‖ := by
    intro m x
    have : (iter α A q x ^ m).det = 1 := by rw [Matrix.det_pow, hdetB, one_pow]
    exact one_le_norm_of_det_eq_one this
  set F : ℕ → ℝ → ℝ := fun m x => Real.log ‖iter α A q x ^ m‖ / m with hF
  -- pointwise limit
  have hlim : ∀ x, Tendsto (fun m => F m x) atTop (𝓝 (Real.log (specRad (iter α A q x)))) := by
    intro x
    have hρ : 0 < specRad (iter α A q x) := zero_lt_one.trans_le (one_le_specRad (hdetB x))
    have h := ((Real.continuousAt_log hρ.ne').tendsto).comp (tendsto_specRad (iter α A q x))
    refine h.congr fun m => ?_
    simp only [Function.comp, hF]
    rw [Real.log_rpow (hnormpos m x)]
    ring
  have hcont : ∀ m, Continuous (F m) := by
    intro m
    exact (((continuous_iter hS.continuous q).pow m).norm.log
      (fun x => (hnormpos m x).ne')).div_const _
  have hDCT : Tendsto (fun m => ∫ x in (0 : ℝ)..1, F m x) atTop
      (𝓝 (∫ x in (0 : ℝ)..1, Real.log (specRad (iter α A q x)))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun x => Real.log ‖iter α A q x‖) (Eventually.of_forall fun m =>
        (hcont m).aestronglyMeasurable) ?_
      ((hS.continuous_log_norm_iter q).intervalIntegrable _ _)
      (MeasureTheory.ae_of_all _ fun x _ => hlim x)
    rw [eventually_atTop]
    refine ⟨1, fun m hm => MeasureTheory.ae_of_all _ fun x _ => ?_⟩
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have h0 : 0 ≤ F m x := div_nonneg (Real.log_nonneg (hnorm1 m x)) hm'.le
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    simp only [hF]
    rw [div_le_iff₀ hm']
    calc Real.log ‖iter α A q x ^ m‖ ≤ Real.log (‖iter α A q x‖ ^ m) :=
          Real.log_le_log (hnormpos m x) (norm_pow_le _ _)
      _ = Real.log ‖iter α A q x‖ * m := by rw [Real.log_pow]; ring
  have hT1 : Tendsto (fun m : ℕ => lyapSeq α A (q * m) / ((q * m : ℕ) : ℝ)) atTop
      (𝓝 (lyapunov α A)) := by
    refine hS.tendsto_lyapunov.comp ?_
    refine tendsto_atTop_atTop.2 fun b => ⟨b, fun m hm => ?_⟩
    exact le_trans hm (Nat.le_mul_of_pos_left m hq)
  have hT2 := hDCT.const_mul (1 / (q : ℝ))
  refine tendsto_nhds_unique hT1 (hT2.congr' ?_)
  rw [EventuallyEq, eventually_atTop]
  refine ⟨1, fun m hm => ?_⟩
  have hint : lyapSeq α A (q * m) = ∫ x in (0 : ℝ)..1, Real.log ‖iter α A q x ^ m‖ := by
    simp only [lyapSeq, hpow]
  simp only [hF]
  rw [intervalIntegral.integral_div, hint]
  push_cast
  ring

/-- The Lyapunov exponent at a rational frequency:
`L(p/q, A) = (1/q) ∫_𝕋 log ρ(A_{(p/q)}(x)) dx`. -/
theorem L_rational {δ : ℝ} {A : ℂ → M2} (hA : IsAnalyticCocycle δ A) (p : ℤ) {q : ℕ}
    (hq : 0 < q) :
    L ((p : ℝ) / q) A 0 = (1 / (q : ℝ)) * ∫ x in (0 : ℝ)..1, Real.log (specRad (perIter A p q x)) := by
  have hS : IsSLCocycle (shift A 0) := hA.isSLCocycle_shift (by simpa using hA.pos)
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [L, lyapunov_rational_aux hS hq p (by field_simp)]
  congr 1
  refine intervalIntegral.integral_congr fun x _ => ?_
  have h := citer_shift ((p : ℝ) / q) A 0 q x
  simp only [ofReal_zero, zero_mul, add_zero] at h
  simp only [perIter, h]

/-! ### Quantization: piecewise-linear limits, asymptotics, assembly -/

def HasSupportSlopes (S : Finset ℝ) (a b : ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ y ∈ Icc a b, ∃ s ∈ S, ∀ x ∈ Icc a b, g y + s * (x - y) ≤ g x

lemma hasSupportSlopes_sup' {S : Finset ℝ} {a b : ℝ} {ι : Type*} (I : Finset ι)
    (hI : I.Nonempty) (F : ι → ℝ → ℝ)
    (hF : ∀ i ∈ I, ∃ s ∈ S, ∀ x y, F i y + s * (x - y) = F i x) :
    HasSupportSlopes S a b (fun x => I.sup' hI fun i => F i x) := by
  intro y _
  obtain ⟨i, hi, hy⟩ := Finset.exists_mem_eq_sup' hI (fun i => F i y)
  obtain ⟨s, hs, hs'⟩ := hF i hi
  refine ⟨s, hs, fun x _ => ?_⟩
  show I.sup' hI (fun i => F i y) + s * (x - y) ≤ I.sup' hI (fun i => F i x)
  rw [hy, hs']
  exact Finset.le_sup' (fun i => F i x) hi

lemma HasSupportSlopes.max {S : Finset ℝ} {a b : ℝ} {f g : ℝ → ℝ}
    (hf : HasSupportSlopes S a b f) (hg : HasSupportSlopes S a b g) :
    HasSupportSlopes S a b (fun x => max (f x) (g x)) := by
  intro y hy
  rcases le_total (g y) (f y) with h | h
  · obtain ⟨s, hs, H⟩ := hf y hy
    refine ⟨s, hs, fun x hx => ?_⟩
    simp only [max_eq_left h]
    exact (H x hx).trans (le_max_left _ _)
  · obtain ⟨s, hs, H⟩ := hg y hy
    refine ⟨s, hs, fun x hx => ?_⟩
    simp only [max_eq_right h]
    exact (H x hx).trans (le_max_right _ _)

lemma frequently_exists_finset {ι β : Type*} {l : Filter ι} {S : Finset β} {P : ι → β → Prop}
    (h : ∃ᶠ n in l, ∃ s ∈ S, P n s) : ∃ s ∈ S, ∃ᶠ n in l, P n s := by
  by_contra hc
  simp only [not_exists, not_and] at hc
  have : ∀ᶠ n in l, ∀ s ∈ S, ¬ P n s :=
    (Filter.eventually_all_finset S).2 fun s hs => Filter.not_frequently.1 (hc s hs)
  exact Filter.not_frequently.2 (this.mono fun n hn ⟨s, hs, hP⟩ => hn s hs hP) h

lemma HasSupportSlopes.of_tendsto {S : Finset ℝ} {a b : ℝ} {g : ℕ → ℝ → ℝ} {f : ℝ → ℝ}
    (hg : ∀ᶠ n in atTop, HasSupportSlopes S a b (g n))
    (hlim : ∀ x ∈ Icc a b, Tendsto (fun n => g n x) atTop (𝓝 (f x))) :
    HasSupportSlopes S a b f := by
  intro y hy
  have h1 : ∃ᶠ n in atTop, ∃ s ∈ S, ∀ x ∈ Icc a b, g n y + s * (x - y) ≤ g n x :=
    (hg.mono fun n hn => hn y hy).frequently
  obtain ⟨s, hs, hfr⟩ := frequently_exists_finset h1
  refine ⟨s, hs, fun x hx => ?_⟩
  have hT : Tendsto (fun n => (g n y, g n x)) atTop (𝓝 (f y, f x)) :=
    (hlim y hy).prodMk_nhds (hlim x hx)
  have hC : IsClosed {p : ℝ × ℝ | p.1 + s * (x - y) ≤ p.2} :=
    isClosed_le (by fun_prop) (by fun_prop)
  exact hC.mem_of_frequently_of_tendsto (hfr.mono fun n hn => hn x hx) hT

lemma mem_of_hasSupportSlopes {S : Finset ℝ} {e : ℝ} (he : 0 < e) {f : ℝ → ℝ}
    (hf : HasSupportSlopes S (-e) e f) {d : ℝ}
    (hd : Tendsto (fun h => (f h - f 0) / h) (𝓝[>] 0) (𝓝 d)) : d ∈ S := by
  have hev : ∀ᶠ h in 𝓝[>] (0 : ℝ), ∃ s ∈ S, (f h - f 0) / h ≤ s ∧
      s ≤ 2 * ((f (2 * h) - f 0) / (2 * h)) - (f h - f 0) / h := by
    have : Ioo (0 : ℝ) (e / 2) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by linarith)
    filter_upwards [this] with h ⟨h0, h1⟩
    obtain ⟨s, hs, H⟩ := hf h ⟨by linarith, by linarith⟩
    have H0 := H 0 ⟨by linarith, by linarith⟩
    have H2 := H (2 * h) ⟨by linarith, by linarith⟩
    refine ⟨s, hs, ?_, ?_⟩
    · rw [div_le_iff₀ h0]; linarith
    · have : 2 * ((f (2 * h) - f 0) / (2 * h)) - (f h - f 0) / h = (f (2 * h) - f h) / h := by
        field_simp; ring
      rw [this, le_div_iff₀ h0]; linarith
  obtain ⟨s, hs, hfr⟩ := frequently_exists_finset hev.frequently
  have hmul : Tendsto (fun h : ℝ => 2 * h) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have := ((continuous_const_mul (2 : ℝ)).tendsto 0).mono_left
        (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
      show 0 < 2 * h
      linarith
  have hT2 : Tendsto (fun h => 2 * ((f (2 * h) - f 0) / (2 * h)) - (f h - f 0) / h) (𝓝[>] 0)
      (𝓝 (2 * d - d)) := ((hd.comp hmul).const_mul 2).sub hd
  have hT := hd.prodMk_nhds hT2
  have hC : IsClosed {p : ℝ × ℝ | p.1 ≤ s ∧ s ≤ p.2} :=
    (isClosed_le continuous_fst continuous_const).inter (isClosed_le continuous_const continuous_snd)
  obtain ⟨h1, h2⟩ := hC.mem_of_frequently_of_tendsto hfr hT
  have : s = d := le_antisymm (by simp only at h2; linarith) h1
  exact this ▸ hs

/-- The model convex piecewise-linear function `t ↦ max(0, max_{|k| ≤ k₀} (c_k - 2πkt))`. -/
def plModel (k0 : ℕ) (c : ℤ → ℝ) (t : ℝ) : ℝ :=
  max 0 ((Finset.Icc (-(k0 : ℤ)) k0).sup' ⟨0, by simp⟩ fun k => c k - 2 * Real.pi * k * t)

/-- The slopes `2π·{-k₀, …, k₀}`. -/
def plSlopes (k0 : ℕ) : Finset ℝ :=
  (Finset.Icc (-(k0 : ℤ)) k0).image fun k : ℤ => -(2 * Real.pi * k)

lemma hasSupportSlopes_plModel (k0 : ℕ) (c : ℤ → ℝ) (a b : ℝ) :
    HasSupportSlopes (plSlopes k0) a b (plModel k0 c) := by
  have h0 : HasSupportSlopes (plSlopes k0) a b (fun _ => 0) := by
    intro y _
    exact ⟨0, Finset.mem_image.2 ⟨0, by simp, by simp⟩, fun x _ => by simp⟩
  have h1 := hasSupportSlopes_sup' (S := plSlopes k0) (a := a) (b := b)
    (Finset.Icc (-(k0 : ℤ)) k0) ⟨0, by simp⟩ (fun k t => c k - 2 * Real.pi * k * t)
    (fun k hk => ⟨-(2 * Real.pi * k), Finset.mem_image.2 ⟨k, hk, rfl⟩, fun x y => by ring⟩)
  exact h0.max h1

/-! ### (Q1) Fourier coefficients of holomorphic periodic functions -/

/-- `e(z) = exp(2πiz)`. -/
def eC (z : ℂ) : ℂ := Complex.exp (2 * Real.pi * I * z)

lemma norm_eC (z : ℂ) : ‖eC z‖ = Real.exp (-2 * Real.pi * z.im) := by
  unfold eC; rw [Complex.norm_exp]; congr 1; simp [Complex.mul_re]

lemma eC_add (z w : ℂ) : eC (z + w) = eC z * eC w := by
  unfold eC; rw [← Complex.exp_add]; congr 1; ring

lemma eC_intCast (k : ℤ) : eC k = 1 := by
  unfold eC
  rw [show 2 * (Real.pi : ℂ) * I * k = k * (2 * Real.pi * I) by ring,
    Complex.exp_int_mul_two_pi_mul_I]

lemma norm_eC_ofReal (x : ℝ) : ‖eC x‖ = 1 := by simp [norm_eC]

lemma differentiable_eC : Differentiable ℂ eC := by
  unfold eC; fun_prop

lemma eC_eq_one_iff {w : ℂ} : eC w = 1 ↔ ∃ k : ℤ, w = k := by
  unfold eC
  rw [Complex.exp_eq_one_iff]
  have h : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero, I_ne_zero]
  constructor
  · rintro ⟨k, hk⟩; exact ⟨k, mul_left_cancel₀ h (by rw [hk]; ring)⟩
  · rintro ⟨k, rfl⟩; exact ⟨k, by ring⟩

lemma exp_mul_helper (c A B C : ℂ) (h : A = B + C) :
    c * Complex.exp A = Complex.exp B * (c * Complex.exp C) := by
  rw [h, Complex.exp_add]; ring

lemma exp_mul_helper' (c A B C : ℂ) (h : A = B + C) :
    c * Complex.exp A = Complex.exp B * c * Complex.exp C := by
  rw [h, Complex.exp_add]; ring

lemma summable_exp_neg_abs {a : ℝ} (ha : 0 < a) :
    Summable fun n : ℤ => Real.exp (-a * |(n : ℝ)|) := by
  have hg : Summable fun n : ℕ => Real.exp (-a) ^ n :=
    summable_geometric_of_lt_one (Real.exp_pos _).le (Real.exp_lt_one_iff.2 (by linarith))
  refine Summable.of_nat_of_neg ?_ ?_
  · refine hg.congr fun n => ?_
    rw [← Real.exp_nat_mul]; congr 1; push_cast; rw [abs_of_nonneg (Nat.cast_nonneg n)]; ring
  · refine hg.congr fun n => ?_
    rw [← Real.exp_nat_mul]; congr 1; push_cast
    rw [abs_neg, abs_of_nonneg (Nat.cast_nonneg n)]; ring

/-- The `m`-th Fourier coefficient of `g`, computed along the line `Im z = y`. -/
def fcoef (g : ℂ → ℂ) (m : ℤ) (y : ℝ) : ℂ :=
  ∫ x in (0 : ℝ)..1, g (x + y * I) * eC (-(m * (x + y * I)))

/-- Contour shift: the Fourier coefficients of a holomorphic `1`-periodic function do not depend
on the line along which they are computed. -/
lemma fcoef_indep {g : ℂ → ℂ} {ε : ℝ} (hg : DifferentiableOn ℂ g (strip ε))
    (hper : ∀ z, g (z + 1) = g z) (m : ℤ) {y₁ y₂ : ℝ} (h₁ : |y₁| < ε) (h₂ : |y₂| < ε) :
    fcoef g m y₁ = fcoef g m y₂ := by
  set h : ℂ → ℂ := fun z => g z * eC (-(m * z)) with hh
  have hhper : ∀ z, h (z + 1) = h z := by
    intro z
    simp only [hh, hper]
    congr 1
    rw [show -((m : ℂ) * (z + 1)) = -(m * z) + ((-m : ℤ) : ℂ) by push_cast; ring, eC_add,
      eC_intCast, mul_one]
  have hd : DifferentiableOn ℂ h (Set.uIcc ((y₁ : ℂ) * I).re (1 + (y₂ : ℂ) * I).re ×ℂ
      Set.uIcc ((y₁ : ℂ) * I).im (1 + (y₂ : ℂ) * I).im) := by
    refine (hg.mul (differentiable_eC.comp (by fun_prop :
      Differentiable ℂ fun z : ℂ => -((m : ℂ) * z))).differentiableOn).mono ?_
    intro z hz
    rw [mem_reProdIm] at hz
    have him : z.im ∈ Set.uIcc y₁ y₂ := by simpa using hz.2
    show |z.im| < ε
    rw [abs_lt] at h₁ h₂ ⊢
    rcases Set.mem_uIcc.1 him with ⟨a, b⟩ | ⟨a, b⟩ <;> constructor <;> linarith
  have key := integral_boundary_rect_eq_zero_of_differentiableOn h _ _ hd
  have e1 : ((y₁ : ℂ) * I).re = 0 := by simp
  have e2 : ((y₁ : ℂ) * I).im = y₁ := by simp
  have e3 : (1 + (y₂ : ℂ) * I).re = 1 := by simp
  have e4 : (1 + (y₂ : ℂ) * I).im = y₂ := by simp
  rw [e1, e2, e3, e4] at key
  have hv : (∫ y : ℝ in y₁..y₂, h ((1 : ℝ) + y * I)) =
      ∫ y : ℝ in y₁..y₂, h ((0 : ℝ) + y * I) := by
    refine intervalIntegral.integral_congr fun y _ => ?_
    simp only [ofReal_one, ofReal_zero, zero_add]
    rw [add_comm]; exact hhper _
  rw [hv, add_sub_cancel_right, sub_eq_zero] at key
  unfold fcoef
  exact key

lemma norm_fcoef_le {g : ℂ → ℂ} (m : ℤ) (y M : ℝ) (hb : ∀ x : ℝ, ‖g (x + y * I)‖ ≤ M) :
    ‖fcoef g m y‖ ≤ M * Real.exp (2 * Real.pi * m * y) := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
    (f := fun x : ℝ => g (x + y * I) * eC (-(m * (x + y * I))))
    (C := M * Real.exp (2 * Real.pi * m * y)) (fun x _ => by
      rw [norm_mul, norm_eC]
      have : (-((m : ℂ) * (x + y * I))).im = -(m * y) := by simp
      rw [this]
      exact mul_le_mul (hb x) (le_of_eq (by congr 1; ring)) (Real.exp_pos _).le
        ((norm_nonneg _).trans (hb x)))
  simpa [fcoef] using this

/-- **(Q1)** Fourier coefficients of a bounded holomorphic `1`-periodic function on the strip
`|Im z| < ε` decay like `M e^{-2π|m|ε₁}` for every `ε₁ < ε`. -/
lemma norm_fcoef_le_exp {g : ℂ → ℂ} {ε M : ℝ} (hg : DifferentiableOn ℂ g (strip ε))
    (hper : ∀ z, g (z + 1) = g z) (hb : ∀ z ∈ strip ε, ‖g z‖ ≤ M) (m : ℤ) {ε₁ y : ℝ}
    (h0 : 0 ≤ ε₁) (h1 : ε₁ < ε) (hy : |y| < ε) :
    ‖fcoef g m y‖ ≤ M * Real.exp (-2 * Real.pi * |(m : ℝ)| * ε₁) := by
  have hline : ∀ y' : ℝ, |y'| < ε → ∀ x : ℝ, ‖g (x + y' * I)‖ ≤ M := fun y' hy' x =>
    hb _ (mem_strip_shift hy' x)
  rcases le_or_gt 0 (m : ℝ) with hm | hm
  · have hε : |-ε₁| < ε := by rw [abs_neg, abs_of_nonneg h0]; exact h1
    rw [fcoef_indep hg hper m hy hε]
    refine (norm_fcoef_le m _ M (hline _ hε)).trans (le_of_eq ?_)
    rw [abs_of_nonneg hm]; congr 2; ring
  · have hε : |ε₁| < ε := by rw [abs_of_nonneg h0]; exact h1
    rw [fcoef_indep hg hper m hy hε]
    refine (norm_fcoef_le m _ M (hline _ hε)).trans (le_of_eq ?_)
    rw [abs_of_neg hm]; congr 2; ring

/-- **(Q1')** Fourier expansion of a bounded holomorphic `1`-periodic function on its strip. -/
lemma hasSum_fcoef {g : ℂ → ℂ} {ε M : ℝ} (hg : DifferentiableOn ℂ g (strip ε))
    (hper : ∀ z, g (z + 1) = g z) (hb : ∀ z ∈ strip ε, ‖g z‖ ≤ M) {z : ℂ} (hz : |z.im| < ε) :
    HasSum (fun m : ℤ => fcoef g m 0 * eC (m * z)) (g z) := by
  obtain ⟨ε₁, hε₁, hε₁'⟩ := exists_between hz
  have h0 : 0 ≤ ε₁ := (abs_nonneg _).trans hε₁.le
  have hz0 : |(0 : ℝ)| < ε := by rw [abs_zero]; linarith
  have hM : 0 ≤ M := (norm_nonneg _).trans (hb z hz)
  have hz' : z = (z.re : ℂ) + (z.im : ℂ) * I := (re_add_im z).symm
  set y := z.im with hy
  set φ : ℝ → ℂ := fun t => g (t + y * I) with hφ
  have hφper : Function.Periodic φ 1 := fun t => by
    simp only [hφ]; push_cast; rw [add_right_comm, hper]
  have hφc : Continuous φ :=
    hg.continuousOn.comp_continuous (by fun_prop) (fun t => mem_strip_shift hz t)
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  let F : C(AddCircle (1 : ℝ), ℂ) := ⟨hφper.lift, continuous_coinduced_dom.2 hφc⟩
  have hFt : ∀ t : ℝ, F (t : AddCircle (1 : ℝ)) = g (t + y * I) := fun t => rfl
  have hFc : ∀ n : ℤ, fourierCoeff F n = Real.exp (-2 * Real.pi * n * y) * fcoef g n 0 := by
    intro n
    rw [fcoef_indep hg hper n hz0 hz, fourierCoeff_eq_intervalIntegral F n 0, fcoef,
      ← intervalIntegral.integral_const_mul]
    simp only [zero_add, div_one, one_smul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [smul_eq_mul, fourier_coe_apply]
    rw [hFt, Complex.ofReal_exp, eC, mul_comm]
    refine exp_mul_helper _ _ _ _ ?_
    push_cast
    linear_combination (2 * (Real.pi : ℂ) * n * y) * I_sq
  have hsum : Summable (fourierCoeff F) := by
    have ha : 0 < 2 * Real.pi * (ε₁ - |y|) := by have := Real.pi_pos; nlinarith
    refine Summable.of_norm_bounded
      (g := fun n : ℤ => M * Real.exp (-(2 * Real.pi * (ε₁ - |y|)) * |(n : ℝ)|))
      ((summable_exp_neg_abs ha).mul_left M) fun n => ?_
    rw [hFc, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have hc := norm_fcoef_le_exp hg hper hb n h0 hε₁' hz0
    calc Real.exp (-2 * Real.pi * n * y) * ‖fcoef g n 0‖
        ≤ Real.exp (-2 * Real.pi * n * y) * (M * Real.exp (-2 * Real.pi * |(n : ℝ)| * ε₁)) :=
          mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le
      _ = M * Real.exp (-2 * Real.pi * n * y + -2 * Real.pi * |(n : ℝ)| * ε₁) := by
          rw [Real.exp_add]; ring
      _ ≤ M * Real.exp (-(2 * Real.pi * (ε₁ - |y|)) * |(n : ℝ)|) := by
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hM
          nlinarith [neg_le_abs ((n : ℝ) * y), abs_mul (n : ℝ) y, Real.pi_pos,
            abs_nonneg (n : ℝ)]
  have hS := has_pointwise_sum_fourier_series_of_summable hsum (z.re : AddCircle (1 : ℝ))
  have hval : F (z.re : AddCircle (1 : ℝ)) = g z := by rw [hFt, ← hz']
  rw [hval] at hS
  convert hS using 1
  funext n
  rw [hFc, fourier_coe_apply, smul_eq_mul, Complex.ofReal_exp, eC]
  refine exp_mul_helper' _ _ _ _ ?_
  push_cast
  linear_combination (2 * (Real.pi : ℂ) * I * n) * hz' + (2 * (Real.pi : ℂ) * n * y) * I_sq

/-- For a `1/q`-periodic function, only the Fourier modes divisible by `q` survive. -/
lemma fcoef_eq_zero_of_not_dvd {g : ℂ → ℂ} {q : ℕ} (hq : 0 < q)
    (hper : ∀ z, g (z + 1) = g z) (hperq : ∀ x : ℝ, g (x + 1 / q) = g x) {m : ℤ}
    (hm : ¬ (q : ℤ) ∣ m) : fcoef g m 0 = 0 := by
  have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  set h : ℝ → ℂ := fun x => g x * eC (-(m * x)) with hh
  have hhper : Function.Periodic h 1 := fun x => by
    simp only [hh]; push_cast; rw [hper]
    congr 1
    rw [show -((m : ℂ) * (x + 1)) = -(m * x) + ((-m : ℤ) : ℂ) by push_cast; ring, eC_add,
      eC_intCast, mul_one]
  have hfc : fcoef g m 0 = ∫ x in (0 : ℝ)..1, h x := by simp [fcoef, hh]
  have hshift : ∫ x in (0 : ℝ)..1, h (x + 1 / q) = ∫ x in (0 : ℝ)..1, h x := by
    rw [intervalIntegral.integral_comp_add_right h (1 / q : ℝ), zero_add, add_comm (1 : ℝ),
      hhper.intervalIntegral_add_eq (1 / q) 0, zero_add]
  have hpt : ∀ x : ℝ, h (x + 1 / q) = eC (-(m / q)) * h x := by
    intro x
    simp only [hh]; push_cast
    rw [hperq, show -((m : ℂ) * (x + 1 / q)) = -(m * x) + -(m / q) by ring, eC_add]
    ring
  have heq : fcoef g m 0 = eC (-(m / q)) * fcoef g m 0 := by
    rw [hfc, ← intervalIntegral.integral_const_mul, ← hshift]
    exact intervalIntegral.integral_congr fun x _ => hpt x
  have hne : eC (-(m / q)) ≠ 1 := by
    intro he
    obtain ⟨k, hk⟩ := eC_eq_one_iff.1 he
    have h1 : (m : ℂ) = -(k : ℂ) * q := by rw [← hk, neg_neg, div_mul_cancel₀ _ hq']
    have h2 : m = -k * q := by exact_mod_cast h1
    exact hm ⟨-k, by rw [h2]; ring⟩
  have : (1 - eC (-(m / q))) * fcoef g m 0 = 0 := by linear_combination heq
  rcases mul_eq_zero.1 this with h | h
  · exact absurd (sub_eq_zero.1 h).symm hne
  · exact h

/-! ### Mahler measure lower bound for trigonometric polynomials -/

/-- The polynomial `∑_{|k| ≤ k₀} b_k X^{k + k₀}`. -/
def shiftPoly (k0 : ℕ) (b : ℤ → ℂ) : Polynomial ℂ :=
  ∑ k ∈ Finset.Icc (-(k0 : ℤ)) k0, Polynomial.C (b k) * Polynomial.X ^ (k + k0).toNat

/-- The trigonometric polynomial `x ↦ ∑_{|k| ≤ k₀} b_k e^{2πikqx}`. -/
def trigP (k0 q : ℕ) (b : ℤ → ℂ) (x : ℝ) : ℂ :=
  ∑ k ∈ Finset.Icc (-(k0 : ℤ)) k0, b k * eC (k * q * x)

lemma norm_trigP_eq (k0 q : ℕ) (b : ℤ → ℂ) (x : ℝ) :
    ‖trigP k0 q b x‖ = ‖(shiftPoly k0 b).eval (circleMap 0 1 (2 * Real.pi * q * x))‖ := by
  have hev : (shiftPoly k0 b).eval (circleMap 0 1 (2 * Real.pi * q * x)) =
      eC (k0 * q * x) * trigP k0 q b x := by
    simp only [shiftPoly, trigP, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have h0 : (0 : ℤ) ≤ k + k0 := by rw [Finset.mem_Icc] at hk; omega
    have h1 : (((k + k0).toNat : ℤ) : ℂ) = ((k + k0 : ℤ) : ℂ) := by rw [Int.toNat_of_nonneg h0]
    push_cast at h1
    simp only [circleMap, ofReal_one, zero_add, one_mul]
    rw [← Complex.exp_nat_mul, h1]
    simp only [eC]
    refine exp_mul_helper _ _ _ _ ?_
    push_cast
    ring
  rw [hev, norm_mul, norm_eC]
  simp

lemma shiftPoly_coeff (k0 : ℕ) (b : ℤ → ℂ) {j : ℤ} (hj : j ∈ Finset.Icc (-(k0 : ℤ)) k0) :
    (shiftPoly k0 b).coeff (j + k0).toNat = b j := by
  simp only [shiftPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k hk hkj
    rw [if_neg]
    intro h
    apply hkj
    rw [Finset.mem_Icc] at hk hj
    omega
  · intro h; exact absurd hj h

lemma shiftPoly_natDegree (k0 : ℕ) (b : ℤ → ℂ) : (shiftPoly k0 b).natDegree ≤ 2 * k0 := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
  refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
  rw [Finset.mem_Icc] at hk; omega

lemma log_le_logMahlerMeasure (k0 : ℕ) (b : ℤ → ℂ) {j : ℤ}
    (hj : j ∈ Finset.Icc (-(k0 : ℤ)) k0) (hbj : b j ≠ 0) :
    Real.log ‖b j‖ - 2 * k0 * Real.log 2 ≤ (shiftPoly k0 b).logMahlerMeasure := by
  have hQ : shiftPoly k0 b ≠ 0 := by
    intro h; apply hbj; rw [← shiftPoly_coeff k0 b hj, h, Polynomial.coeff_zero]
  have h1 := Polynomial.norm_coeff_le_choose_mul_mahlerMeasure (j + k0).toNat (shiftPoly k0 b)
  rw [shiftPoly_coeff k0 b hj] at h1
  have h2 : ((shiftPoly k0 b).natDegree.choose (j + k0).toNat : ℝ) ≤ 2 ^ (2 * k0) := by
    have := (Nat.choose_le_two_pow (shiftPoly k0 b).natDegree (j + k0).toNat).trans
      (Nat.pow_le_pow_right (by norm_num) (shiftPoly_natDegree k0 b))
    exact_mod_cast this
  have hM : (shiftPoly k0 b).mahlerMeasure = Real.exp (shiftPoly k0 b).logMahlerMeasure := by
    rw [Polynomial.mahlerMeasure, if_pos hQ]
  have h3 : ‖b j‖ ≤ 2 ^ (2 * k0) * Real.exp (shiftPoly k0 b).logMahlerMeasure := by
    rw [← hM]
    exact h1.trans (mul_le_mul_of_nonneg_right h2 (Polynomial.mahlerMeasure_nonneg _))
  have hb : 0 < ‖b j‖ := norm_pos_iff.2 hbj
  have h4 := Real.log_le_log hb h3
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp, Real.log_pow] at h4
  push_cast at h4
  linarith

lemma integral_log_trigP (k0 : ℕ) {q : ℕ} (hq : 0 < q) (b : ℤ → ℂ) :
    IntervalIntegrable (fun x => Real.log ‖trigP k0 q b x‖) MeasureTheory.volume 0 1 ∧
    ∫ x in (0 : ℝ)..1, Real.log ‖trigP k0 q b x‖ = (shiftPoly k0 b).logMahlerMeasure := by
  set H : ℝ → ℝ := fun θ => Real.log ‖(shiftPoly k0 b).eval (circleMap 0 1 θ)‖ with hH
  have hHper : Function.Periodic H (2 * Real.pi) := fun θ => by
    simp only [hH, periodic_circleMap 0 1 θ]
  have hHint0 : IntervalIntegrable H MeasureTheory.volume 0 (0 + 2 * Real.pi) := by
    rw [zero_add]; exact Polynomial.intervalIntegrable_mahlerMeasure _
  have hHint : ∀ a b, IntervalIntegrable H MeasureTheory.volume a b :=
    hHper.intervalIntegrable (by positivity) hHint0
  have hq' : (q : ℝ) ≠ 0 := by positivity
  set c : ℝ := 2 * Real.pi * q with hc
  have hc0 : c ≠ 0 := by rw [hc]; positivity
  have hfun : (fun x => Real.log ‖trigP k0 q b x‖) = fun x => H (c * x) := by
    funext x; rw [norm_trigP_eq]
  rw [hfun]
  constructor
  · have := (hHint 0 c).comp_mul_left (c := c)
    simpa [hc0] using this
  · rw [intervalIntegral.integral_comp_mul_left H hc0, mul_zero, mul_one]
    have hz := hHper.intervalIntegral_add_zsmul_eq (q : ℤ) 0 hHint
    rw [zero_add, zero_add] at hz
    have : (q : ℤ) • (2 * Real.pi) = c := by rw [hc, zsmul_eq_mul]; push_cast; ring
    rw [this] at hz
    rw [hz, Polynomial.logMahlerMeasure_def, Real.circleAverage_def, hc]
    simp only [hH, smul_eq_mul, zsmul_eq_mul, Int.cast_natCast]
    field_simp

/-! ### The trace of the period product and the rational estimate -/

lemma citer_cshift (α : ℝ) (A : ℂ → M2) (t : ℝ) (n : ℕ) (z : ℂ) :
    citer α (cshift A t) n z = citer α A n (z + t * I) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [citer, ih, cshift]
    congr 2
    ring

/-- `L(p/q, A_t) = (1/q) ∫ log ρ(A_{(p/q)}(x + it)) dx`. -/
lemma L_rational_shift {δ : ℝ} {A : ℂ → M2} (hA : IsAnalyticCocycle δ A) (p : ℤ) {q : ℕ}
    (hq : 0 < q) {t : ℝ} (ht : |t| < δ) :
    L ((p : ℝ) / q) A t =
      (1 / (q : ℝ)) * ∫ x in (0 : ℝ)..1, Real.log (specRad (perIter A p q (x + t * I))) := by
  have h := L_rational (hA.cshift ht) p hq
  rw [L_cshift, zero_add] at h
  rw [h]
  simp only [perIter, citer_cshift]

lemma det_citer {δ : ℝ} {A : ℂ → M2} (hA : IsAnalyticCocycle δ A) (α : ℝ) (n : ℕ) {z : ℂ}
    (hz : z ∈ strip δ) : (citer α A n z).det = 1 := by
  induction n with
  | zero => simp [citer]
  | succ n ih =>
    rw [citer, Matrix.det_mul, ih, mul_one]
    apply hA.det_eq_one
    simpa [strip] using hz

lemma differentiableOn_citer {δ : ℝ} {A : ℂ → M2} (hA : IsAnalyticCocycle δ A) (α : ℝ)
    (n : ℕ) : DifferentiableOn ℂ (citer α A n) (strip δ) := by
  induction n with
  | zero =>
    have : citer α A 0 = fun _ => 1 := funext fun z => rfl
    rw [this]; exact differentiableOn_const _
  | succ n ih =>
    have hmaps : MapsTo (fun z : ℂ => z + n * α) (strip δ) (strip δ) := fun z hz => by
      simpa [strip] using hz
    have h1 : DifferentiableOn ℂ (fun z => A (z + n * α)) (strip δ) :=
      hA.holo.comp (differentiableOn_id.add_const _) hmaps
    have : citer α A (n + 1) = fun z => A (z + n * α) * citer α A n z := funext fun z => rfl
    rw [this]
    exact h1.mul ih

lemma differentiableOn_trace {s : Set ℂ} {f : ℂ → M2} (hf : DifferentiableOn ℂ f s) :
    DifferentiableOn ℂ (fun z => (f z).trace) s := by
  let T : M2 →L[ℂ] ℂ := LinearMap.toContinuousLinearMap (Matrix.traceLinearMap (Fin 2) ℂ ℂ)
  have h := T.differentiable.comp_differentiableOn hf
  refine h.congr fun z _ => ?_
  simp [T]

lemma norm_trace_le (B : M2) : ‖B.trace‖ ≤ 2 * ‖B‖ := by
  rw [Matrix.trace_fin_two]
  have h0 := row_sum_le_norm B 0
  have h1 := row_sum_le_norm B 1
  have := norm_add_le (B 0 0) (B 1 1)
  linarith [norm_nonneg (B 0 1), norm_nonneg (B 1 0)]

lemma norm_citer_le {A : ℂ → M2} {α C : ℝ} (hC : 0 ≤ C) {y : ℝ}
    (hb : ∀ w : ℂ, w.im = y → ‖A w‖ ≤ C) (n : ℕ) {z : ℂ} (hz : z.im = y) :
    ‖citer α A n z‖ ≤ C ^ n := by
  induction n with
  | zero => simp [citer]
  | succ n ih =>
    rw [citer, pow_succ']
    exact (norm_mul_le _ _).trans (mul_le_mul (hb _ (by simp [hz])) ih (norm_nonneg _) hC)

lemma exists_bound_strip {δ : ℝ} {A : ℂ → M2} (hA : IsAnalyticCocycle δ A) {ε : ℝ}
    (hε : ε < δ) : ∃ C : ℝ, 1 ≤ C ∧ ∀ z : ℂ, |z.im| ≤ ε → ‖A z‖ ≤ C := by
  have hK : IsCompact (Icc (0 : ℝ) 1 ×ℂ Icc (-ε) ε) := isCompact_Icc.reProdIm isCompact_Icc
  have hsub : Icc (0 : ℝ) 1 ×ℂ Icc (-ε) ε ⊆ strip δ := by
    intro z hz
    rw [mem_reProdIm] at hz
    show |z.im| < δ
    rw [abs_lt]; constructor <;> linarith [hz.2.1, hz.2.2]
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (hA.continuousOn.mono hsub)
  refine ⟨max C 1, le_max_right _ _, fun z hz => ?_⟩
  set n : ℤ := ⌊z.re⌋
  have hz' : A z = A (z - n) := by
    have := periodic_int hA.periodic n (z - n)
    rw [sub_add_cancel] at this
    exact this
  rw [hz']
  refine (hC _ ?_).trans (le_max_left _ _)
  have h1 : (z - (n : ℂ)).re = z.re - n := by simp
  have h2 : (z - (n : ℂ)).im = z.im := by simp
  rw [mem_reProdIm, h1, h2]
  refine ⟨⟨by linarith [Int.floor_le z.re], by linarith [Int.lt_floor_add_one z.re]⟩, ?_⟩
  exact abs_le.1 hz

/-- `t_{p/q}(z) = tr A_{(p/q)}(z)`. -/
def trPer (A : ℂ → M2) (p : ℤ) (q : ℕ) (z : ℂ) : ℂ := (perIter A p q z).trace

lemma intervalIntegrable_log_specRad {B : ℝ → M2} (hB : Continuous B)
    (hdet : ∀ x, (B x).det = 1) {K : ℝ} (hK : ∀ x, Real.log (specRad (B x)) ≤ K) :
    IntervalIntegrable (fun x => Real.log (specRad (B x))) MeasureTheory.volume 0 1 := by
  have hmeas : Measurable fun x => specRad (B x) := by
    refine measurable_of_tendsto_metrizable
      (f := fun n : ℕ => fun x => ‖B x ^ n‖ ^ (1 / (n : ℝ))) (fun n => ?_) ?_
    · exact ((hB.pow n).norm.rpow_const fun _ => Or.inr (by positivity)).measurable
    · exact tendsto_pi_nhds.2 fun x => tendsto_specRad (B x)
  have hm2 : Measurable fun x => Real.log (specRad (B x)) := Real.measurable_log.comp hmeas
  refine (intervalIntegrable_const :
    IntervalIntegrable (fun _ => K) MeasureTheory.volume 0 1).mono_fun hm2.aestronglyMeasurable ?_
  refine MeasureTheory.ae_of_all _ fun x => ?_
  have h0 : 0 ≤ Real.log (specRad (B x)) := Real.log_nonneg (one_le_specRad (hdet x))
  simp only [Real.norm_eq_abs]
  rw [abs_of_nonneg h0]
  exact (hK x).trans (le_abs_self K)

lemma log_specRad_lower {B : M2} (hB : B.det = 1) {P : ℂ} {K : ℝ} (hK : 0 ≤ K)
    (hTP : ‖B.trace - P‖ ≤ K) :
    Real.log ‖P‖ - Real.log (4 * (K + 1)) ≤ Real.log (specRad B) := by
  have hl := (log_specRad_bounds hB).1
  refine le_trans ?_ hl
  rcases lt_or_ge ‖P‖ (2 * (K + 1)) with hP | hP
  · refine le_trans ?_ (le_max_left _ _)
    rcases eq_or_lt_of_le (norm_nonneg P) with h0 | h0
    · rw [← h0, Real.log_zero]
      have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 4 * (K + 1)); linarith
    · have := Real.log_lt_log h0 (hP.trans_le (by linarith : 2 * (K + 1) ≤ 4 * (K + 1)))
      linarith
  · refine le_trans ?_ (le_max_right _ _)
    have hT : ‖P‖ / 2 ≤ ‖B.trace‖ := by
      have := norm_sub_norm_le P B.trace
      rw [norm_sub_rev] at this
      linarith
    have hPpos : 0 < ‖P‖ := by linarith
    have h1 : Real.log (‖P‖ / 4) ≤ Real.log (‖B.trace‖ / 2) :=
      Real.log_le_log (by positivity) (by linarith)
    rw [Real.log_div hPpos.ne' (by norm_num)] at h1
    have h2 := Real.log_le_log (by norm_num) (by linarith : (4 : ℝ) ≤ 4 * (K + 1))
    linarith

lemma log_specRad_upper {B : M2} (hB : B.det = 1) {P : ℂ} {K : ℝ}
    (hTP : ‖B.trace - P‖ ≤ K) : Real.log (specRad B) ≤ Real.log (1 + ‖P‖ + K) := by
  refine (log_specRad_bounds hB).2.trans (Real.log_le_log (by positivity) ?_)
  have h := norm_add_le (B.trace - P) P
  rw [sub_add_cancel] at h
  linarith

/-- The tail constant `K(η) = ∑_m 2 e^{-πη|m|}`. -/
def tailC (η : ℝ) : ℝ := ∑' m : ℤ, 2 * Real.exp (-(Real.pi * η) * |(m : ℝ)|)

lemma tailC_nonneg (η : ℝ) : 0 ≤ tailC η := tsum_nonneg fun m => by positivity

/-- Splitting off the modes `kq`, `|k| ≤ k₀`, of a bounded holomorphic `1/q`-periodic function:
the remainder is bounded by a constant independent of `q`. -/
lemma tail_bound {g : ℂ → ℂ} {ε C η ε₁ t : ℝ} {q k0 : ℕ} (hq : 0 < q)
    (hg : DifferentiableOn ℂ g (strip ε)) (hper : ∀ z, g (z + 1) = g z)
    (hperq : ∀ x : ℝ, g (x + 1 / q) = g x) (hb : ∀ z ∈ strip ε, ‖g z‖ ≤ 2 * C ^ q)
    (hC : 1 ≤ C) (hη : 0 < η) (hk0 : Real.log C ≤ Real.pi * η * (k0 + 1))
    (hε₁ : ε₁ < ε) (ht : |t| + η ≤ ε₁) (x : ℝ) :
    ‖g (x + t * I) - trigP k0 q (fun k => fcoef g (k * q) 0 * eC (k * q * (t * I))) x‖ ≤
      tailC η := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hzim : ((x : ℂ) + t * I).im = t := by simp
  have hz : |((x : ℂ) + t * I).im| < ε := by rw [hzim]; linarith
  have h0 : 0 ≤ ε₁ := by linarith [abs_nonneg t]
  have hS := hasSum_fcoef hg hper hb hz
  set z : ℂ := (x : ℂ) + t * I with hzdef
  set a : ℤ → ℂ := fun m => fcoef g m 0 * eC (m * z) with ha
  set S : Finset ℤ := (Finset.Icc (-(k0 : ℤ)) k0).image (fun k => k * q) with hSdef
  have hfin : HasSum (fun m => if m ∈ S then a m else 0) (∑ m ∈ S, a m) := by
    have : HasSum (fun m => if m ∈ S then a m else 0)
        (∑ m ∈ S, (fun m => if m ∈ S then a m else 0) m) :=
      hasSum_sum_of_ne_finset_zero (fun m hm => if_neg hm)
    have e : (∑ m ∈ S, (fun m => if m ∈ S then a m else 0) m) = ∑ m ∈ S, a m :=
      Finset.sum_congr rfl fun m hm => if_pos hm
    rwa [e] at this
  have hdiff : HasSum (fun m => if m ∈ S then 0 else a m) (g z - ∑ m ∈ S, a m) := by
    have := hS.sub hfin
    convert this using 1
    funext m
    by_cases hm : m ∈ S <;> simp [hm]
  have hP : ∑ m ∈ S, a m = trigP k0 q (fun k => fcoef g (k * q) 0 * eC (k * q * (t * I))) x := by
    rw [hSdef, Finset.sum_image (by
      intro k _ k' _ h
      exact mul_right_cancel₀ (by exact_mod_cast hq.ne' : (q : ℤ) ≠ 0) h)]
    unfold trigP
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [ha, hzdef]
    rw [mul_assoc (fcoef g (k * q) 0), ← eC_add]
    congr 2
    push_cast
    ring
  rw [← hP]
  have hG : HasSum (fun m : ℤ => 2 * Real.exp (-(Real.pi * η) * |(m : ℝ)|)) (tailC η) :=
    ((summable_exp_neg_abs (by positivity)).mul_left 2).hasSum
  refine hdiff.norm_le_of_bounded hG fun m => ?_
  by_cases hm : m ∈ S
  · simp only [if_pos hm, norm_zero]; positivity
  simp only [if_neg hm]
  by_cases hdvd : (q : ℤ) ∣ m
  swap
  · simp only [ha, fcoef_eq_zero_of_not_dvd hq hper hperq hdvd, zero_mul, norm_zero]
    positivity
  obtain ⟨k', rfl⟩ := hdvd
  -- `|k'| > k₀`
  have hk' : (k0 : ℤ) + 1 ≤ |k'| := by
    by_contra hcon
    apply hm
    rw [hSdef, Finset.mem_image]
    refine ⟨k', Finset.mem_Icc.2 ?_, by ring⟩
    have := abs_le.1 (show |k'| ≤ (k0 : ℤ) by omega)
    exact ⟨this.1, this.2⟩
  have hk'R : ((k0 : ℝ) + 1) ≤ |(k' : ℝ)| := by exact_mod_cast hk'
  have habs : |((q * k' : ℤ) : ℝ)| = q * |(k' : ℝ)| := by
    push_cast; rw [abs_mul, Nat.abs_cast]
  -- bound on the coefficient
  have hc := norm_fcoef_le_exp hg hper hb (q * k') (y := 0) h0 hε₁
    (by rw [abs_zero]; linarith [abs_nonneg t])
  have hez : ‖eC (((q * k' : ℤ) : ℂ) * z)‖ = Real.exp (-2 * Real.pi * ((q * k' : ℤ) * t)) := by
    rw [norm_eC]; congr 2; rw [hzdef]; simp
  set m : ℝ := ((q * k' : ℤ) : ℝ) with hmdef
  have hmt : -(m * t) ≤ |m| * |t| := by rw [← abs_mul]; exact neg_le_abs _
  have hCq : C ^ q ≤ Real.exp (Real.pi * η * |m|) := by
    have hCpos : 0 < C := by linarith
    rw [← Real.exp_log hCpos, ← Real.exp_nat_mul]
    refine Real.exp_le_exp.2 ?_
    rw [habs]
    have hlog0 : 0 ≤ Real.log C := Real.log_nonneg hC
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hpe : 0 < Real.pi * η := by positivity
    calc (q : ℝ) * Real.log C ≤ q * (Real.pi * η * (k0 + 1)) :=
          mul_le_mul_of_nonneg_left hk0 hq0
      _ ≤ Real.pi * η * (q * |(k' : ℝ)|) := by
          have := mul_le_mul_of_nonneg_left hk'R (by positivity : (0 : ℝ) ≤ Real.pi * η * q)
          nlinarith
  calc ‖fcoef g (q * k') 0 * eC (((q * k' : ℤ) : ℂ) * z)‖
      = ‖fcoef g (q * k') 0‖ * Real.exp (-2 * Real.pi * (m * t)) := by rw [norm_mul, hez]
    _ ≤ (2 * C ^ q * Real.exp (-2 * Real.pi * |m| * ε₁)) * Real.exp (-2 * Real.pi * (m * t)) :=
        mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
    _ ≤ (2 * Real.exp (Real.pi * η * |m|) * Real.exp (-2 * Real.pi * |m| * ε₁)) *
          Real.exp (-2 * Real.pi * (m * t)) := by gcongr
    _ = 2 * Real.exp (Real.pi * η * |m| + -2 * Real.pi * |m| * ε₁ + -2 * Real.pi * (m * t)) := by
        rw [Real.exp_add, Real.exp_add]; ring
    _ ≤ 2 * Real.exp (-(Real.pi * η) * |m|) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by norm_num)
        have hpi := Real.pi_pos
        have hm0 := abs_nonneg m
        have : |m| * |t| + |m| * η ≤ |m| * ε₁ := by nlinarith
        have h1 := mul_le_mul_of_nonneg_left this hpi.le
        have h2 := mul_le_mul_of_nonneg_left hmt hpi.le
        nlinarith

/-- The intercepts: `c_k = (1/q) log |a_k|` where `a_k` is the `kq`-th Fourier coefficient of
`tr A_{(p/q)}` (or a large negative number when `a_k = 0`). -/
def cfun (A : ℂ → M2) (k0 : ℕ) (ε' : ℝ) (p : ℤ) (q : ℕ) (k : ℤ) : ℝ :=
  if fcoef (trPer A p q) (k * q) 0 = 0 then -(2 * Real.pi * k0 * ε' + 1)
  else (1 / (q : ℝ)) * Real.log ‖fcoef (trPer A p q) (k * q) 0‖

/-- The error constant in `rational_estimate`. -/
def errC (k0 : ℕ) (η : ℝ) : ℝ :=
  max (Real.log ((Finset.Icc (-(k0 : ℤ)) k0).card + 1 + tailC η))
    (2 * k0 * Real.log 2 + Real.log (4 * (tailC η + 1)))

lemma errC_nonneg (k0 : ℕ) (η : ℝ) : 0 ≤ errC k0 η := by
  refine le_max_of_le_right ?_
  have h1 := Real.log_nonneg (by linarith [tailC_nonneg η] : (1 : ℝ) ≤ 4 * (tailC η + 1))
  have h2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  have h3 := mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg (α := ℝ) k0)) h2
  linarith

/-- **(Q2), quantitative form.**  For `p/q` in lowest terms and `|t| ≤ ε'`,
`|L(p/q, A_t) - max(0, max_{|k| ≤ k₀} (c_k - 2πkt))| ≤ errC / q`. -/
lemma rational_estimate {δ : ℝ} {A : ℂ → M2} (hA : IsAnalyticCocycle δ A) {ε' η C : ℝ}
    {k0 : ℕ} (_hε' : 0 < ε') (hη : 0 < η) (hδ : ε' + 2 * η < δ) (hC1 : 1 ≤ C)
    (hC : ∀ z : ℂ, |z.im| ≤ ε' + 2 * η → ‖A z‖ ≤ C)
    (hk0 : Real.log C ≤ Real.pi * η * (k0 + 1))
    (p : ℤ) {q : ℕ} (hq : 0 < q) (hpq : IsCoprime p (q : ℤ)) {t : ℝ} (ht : t ∈ Icc (-ε') ε') :
    |L ((p : ℝ) / q) A t - plModel k0 (cfun A k0 ε' p q) t| ≤ errC k0 η / q := by
  have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hK0 := tailC_nonneg η
  have htabs : |t| ≤ ε' := abs_le.2 ⟨ht.1, ht.2⟩
  have htδ : |t| < δ := by linarith
  have hstrip : strip (ε' + 2 * η) ⊆ strip δ := fun z hz => by
    show |z.im| < δ
    have : |z.im| < ε' + 2 * η := hz
    linarith
  -- the trace function
  have hgd : DifferentiableOn ℂ (trPer A p q) (strip (ε' + 2 * η)) :=
    (differentiableOn_trace (differentiableOn_citer hA _ q)).mono hstrip
  have hgper : ∀ z, trPer A p q (z + 1) = trPer A p q z := fun z => by
    simp only [trPer, perIter, citer_periodic hA.periodic]
  have hgperq : ∀ x : ℝ, trPer A p q (x + 1 / q) = trPer A p q x := fun x =>
    trace_perIter_periodic hA.periodic hq hpq x (fun w hw => hA.det_eq_one w (by
      show |w.im| < δ
      rw [hw, Complex.ofReal_im, abs_zero]; exact hA.pos))
  have hgb : ∀ z ∈ strip (ε' + 2 * η), ‖trPer A p q z‖ ≤ 2 * C ^ q := fun z hz => by
    refine (norm_trace_le _).trans ?_
    have := norm_citer_le (A := A) (α := (p : ℝ) / q) (by linarith : (0 : ℝ) ≤ C) (y := z.im)
      (fun w hw => hC w (by rw [hw]; exact le_of_lt hz)) q rfl
    simp only [perIter]
    linarith
  set b : ℤ → ℂ := fun k => fcoef (trPer A p q) (k * q) 0 * eC (k * q * (t * I)) with hb
  have htail : ∀ x : ℝ, ‖trPer A p q (x + t * I) - trigP k0 q b x‖ ≤ tailC η := fun x =>
    tail_bound hq hgd hgper hgperq hgb hC1 hη hk0 (by linarith : ε' + η < ε' + 2 * η)
      (by linarith : |t| + η ≤ ε' + η) x
  have hdetB : ∀ x : ℝ, (perIter A p q (x + t * I)).det = 1 := fun x =>
    det_citer hA _ q (mem_strip_shift htδ x)
  have hcontB : Continuous fun x : ℝ => perIter A p q (x + t * I) :=
    (differentiableOn_citer hA _ q).continuousOn.comp_continuous (by fun_prop)
      (fun x => mem_strip_shift htδ x)
  have hL := L_rational_shift hA p hq htδ
  set pl := plModel k0 (cfun A k0 ε' p q) t with hpl
  have hpl0 : 0 ≤ pl := le_max_left _ _
  have hle_pl : ∀ k ∈ Finset.Icc (-(k0 : ℤ)) k0,
      cfun A k0 ε' p q k - 2 * Real.pi * k * t ≤ pl := fun k hk =>
    (Finset.le_sup' (fun k => cfun A k0 ε' p q k - 2 * Real.pi * k * t) hk).trans
      (le_max_right _ _)
  have hnormb : ∀ k : ℤ, ‖b k‖ =
      ‖fcoef (trPer A p q) (k * q) 0‖ * Real.exp (-2 * Real.pi * (k * q * t)) := by
    intro k; simp only [hb, norm_mul, norm_eC]; congr 3; simp
  have hlogb : ∀ k : ℤ, fcoef (trPer A p q) (k * q) 0 ≠ 0 →
      Real.log ‖b k‖ = q * (cfun A k0 ε' p q k - 2 * Real.pi * k * t) := by
    intro k hk
    rw [hnormb, Real.log_mul (norm_ne_zero_iff.2 hk) (Real.exp_pos _).ne', Real.log_exp, cfun,
      if_neg hk]
    linear_combination (-Real.log ‖fcoef (trPer A p q) (k * q) 0‖) * mul_one_div_cancel hq'
  have hbk : ∀ k ∈ Finset.Icc (-(k0 : ℤ)) k0, ‖b k‖ ≤ Real.exp (q * pl) := by
    intro k hk
    by_cases hak : fcoef (trPer A p q) (k * q) 0 = 0
    · rw [hnormb, hak, norm_zero, zero_mul]; positivity
    · have hpos : 0 < ‖b k‖ := by
        rw [hnormb]; exact mul_pos (norm_pos_iff.2 hak) (Real.exp_pos _)
      rw [← Real.exp_log hpos, hlogb k hak]
      exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hle_pl k hk) hqpos.le)
  have hPb : ∀ x : ℝ, ‖trigP k0 q b x‖ ≤
      (Finset.Icc (-(k0 : ℤ)) k0).card * Real.exp (q * pl) := by
    intro x
    refine (norm_sum_le _ _).trans ?_
    have : ∀ k ∈ Finset.Icc (-(k0 : ℤ)) k0, ‖b k * eC (k * q * x)‖ ≤ Real.exp (q * pl) := by
      intro k hk
      rw [norm_mul, norm_eC]
      simpa using hbk k hk
    simpa using Finset.sum_le_card_nsmul _ _ _ this
  -- upper bound
  set D : ℝ := (Finset.Icc (-(k0 : ℤ)) k0).card + 1 + tailC η with hD
  have hD0 : 0 < D := by
    rw [hD]; have := Nat.cast_nonneg (α := ℝ) (Finset.Icc (-(k0 : ℤ)) k0).card; linarith
  have hup : ∀ x : ℝ, Real.log (specRad (perIter A p q (x + t * I))) ≤ Real.log D + q * pl := by
    intro x
    refine (log_specRad_upper (hdetB x) (htail x)).trans ?_
    have hE : 1 ≤ Real.exp (q * pl) := Real.one_le_exp (by positivity)
    rw [← Real.log_exp (q * pl), ← Real.log_mul hD0.ne' (Real.exp_pos _).ne']
    refine Real.log_le_log (by linarith [norm_nonneg (trigP k0 q b x)]) ?_
    have hc0 := Nat.cast_nonneg (α := ℝ) (Finset.Icc (-(k0 : ℤ)) k0).card
    rw [hD]
    nlinarith [hPb x]
  have hint1 := intervalIntegrable_log_specRad hcontB hdetB hup
  have hI1 : ∫ x in (0 : ℝ)..1, Real.log (specRad (perIter A p q (x + t * I))) ≤
      Real.log D + q * pl := by
    have := intervalIntegral.integral_mono_on zero_le_one hint1 intervalIntegrable_const
      (fun x _ => hup x)
    simpa using this
  -- lower bound
  obtain ⟨hint2, hI2⟩ := integral_log_trigP k0 hq b
  have hI3 : (shiftPoly k0 b).logMahlerMeasure - Real.log (4 * (tailC η + 1)) ≤
      ∫ x in (0 : ℝ)..1, Real.log (specRad (perIter A p q (x + t * I))) := by
    have := intervalIntegral.integral_mono_on zero_le_one
      (hint2.sub (intervalIntegrable_const :
        IntervalIntegrable (fun _ => Real.log (4 * (tailC η + 1))) MeasureTheory.volume 0 1))
      hint1
      (fun x _ => log_specRad_lower (hdetB x) hK0 (htail x))
    rw [intervalIntegral.integral_sub hint2 intervalIntegrable_const, hI2] at this
    simpa using this
  set Lv := L ((p : ℝ) / q) A t with hLv
  set Iv := ∫ x in (0 : ℝ)..1, Real.log (specRad (perIter A p q (x + t * I))) with hIv
  have hqL : (q : ℝ) * Lv = Iv := by rw [hL]; field_simp
  have hL0 : 0 ≤ Lv := hA.L_nonneg _ htδ
  set E2 : ℝ := 2 * k0 * Real.log 2 + Real.log (4 * (tailC η + 1)) with hE2
  have hE20 : 0 ≤ E2 := by
    have h1 := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 4 * (tailC η + 1))
    have h2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    have h3 := mul_nonneg (mul_nonneg zero_le_two (Nat.cast_nonneg (α := ℝ) k0)) h2
    rw [hE2]; linarith
  have hlow : pl ≤ Lv + E2 / q := by
    refine max_le (by have := div_nonneg hE20 hqpos.le; linarith)
      (Finset.sup'_le _ _ fun j hj => ?_)
    by_cases haj : fcoef (trPer A p q) (j * q) 0 = 0
    · rw [cfun, if_pos haj]
      have hj' : |(j : ℝ)| ≤ k0 := by
        rw [Finset.mem_Icc] at hj
        exact abs_le.2 ⟨by exact_mod_cast hj.1, by exact_mod_cast hj.2⟩
      have hjt : -((j : ℝ) * t) ≤ k0 * ε' := by
        calc -((j : ℝ) * t) ≤ |(j : ℝ) * t| := neg_le_abs _
          _ = |(j : ℝ)| * |t| := abs_mul _ _
          _ ≤ k0 * ε' := mul_le_mul hj' htabs (abs_nonneg _) (Nat.cast_nonneg _)
      have : 0 ≤ E2 / q := div_nonneg hE20 hqpos.le
      have := mul_le_mul_of_nonneg_left hjt (by positivity : (0 : ℝ) ≤ 2 * Real.pi)
      nlinarith [Real.pi_pos]
    · have hbj : b j ≠ 0 := mul_ne_zero haj (Complex.exp_ne_zero _)
      have hM := log_le_logMahlerMeasure k0 b hj hbj
      rw [hlogb j haj] at hM
      have : (q : ℝ) * (cfun A k0 ε' p q j - 2 * Real.pi * j * t) ≤ q * (Lv + E2 / q) := by
        have hqE : (q : ℝ) * (E2 / q) = E2 := by field_simp
        rw [mul_add, hqE, hqL]; linarith
      exact le_of_mul_le_mul_left this hqpos
  have hupp : Lv ≤ pl + Real.log D / q := by
    have : (q : ℝ) * Lv ≤ q * (pl + Real.log D / q) := by
      have hqD : (q : ℝ) * (Real.log D / q) = Real.log D := by field_simp
      rw [mul_add, hqD, hqL]; linarith
    exact le_of_mul_le_mul_left this hqpos
  have hm1 : Real.log D / q ≤ errC k0 η / q :=
    div_le_div_of_nonneg_right (le_max_left _ _) hqpos.le
  have hm2 : E2 / q ≤ errC k0 η / q :=
    div_le_div_of_nonneg_right (le_max_right _ _) hqpos.le
  rw [abs_sub_le_iff]
  constructor <;> linarith

lemma tendsto_den_of_irrational {α : ℝ} (hα : Irrational α) {rs : ℕ → ℚ}
    (hrs : Tendsto (fun n => (rs n : ℝ)) atTop (𝓝 α)) :
    Tendsto (fun n => (rs n).den) atTop atTop := by
  refine tendsto_atTop.2 fun D => ?_
  obtain ⟨r, hr, H⟩ := Metric.eventually_nhds_iff.1
    (hα.eventually_forall_le_dist_cast_rat_of_den_le D)
  have hP := H (y := r / 2) (by rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith)
  have hev := (Metric.tendsto_nhds.1 hrs) (r / 2) (by positivity)
  filter_upwards [hev] with n hn
  by_contra hlt
  have := hP (rs n) (by omega)
  rw [dist_comm] at this
  linarith

/-- **(Q2) Asymptotics of `L(p_n/q_n, A_t)`.**  For rationals `p_n/q_n → α` (irrational),
`L(p_n/q_n, A_t) = max(0, max_{|k| ≤ k₀} (c_{k,n} - 2πkt)) + o(1)` uniformly in `|t| ≤ ε'`,
where `c_{k,n} = (1/q_n) log |a_{k,n}|` and `a_{k,n}` is the `k`-th Fourier coefficient of the
`1/q_n`-periodic function `tr A_{(p_n/q_n)}` (`c_{k,n}` is replaced by a large negative number when
`a_{k,n} = 0`). -/
theorem L_rational_asymptotics {δ : ℝ} {A : ℂ → M2} (hA : IsAnalyticCocycle δ A) {α : ℝ}
    (hα : Irrational α) {rs : ℕ → ℚ} (hrs : Tendsto (fun n => (rs n : ℝ)) atTop (𝓝 α))
    {ε' : ℝ} (hε' : 0 < ε') (hεδ : ε' < δ) :
    ∃ k0 : ℕ, ∃ c : ℕ → ℤ → ℝ,
      TendstoUniformlyOn (fun n t => L (rs n) A t - plModel k0 (c n) t) (fun _ => 0) atTop
        (Icc (-ε') ε') := by
  have hδ := hA.pos
  set η := (δ - ε') / 4 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  obtain ⟨C, hC1, hC⟩ := exists_bound_strip hA (ε := ε' + 2 * η) (by rw [hη]; linarith)
  obtain ⟨k0, hk0⟩ := exists_nat_ge (Real.log C / (Real.pi * η))
  have hpe : 0 < Real.pi * η := by positivity
  have hk0' : Real.log C ≤ Real.pi * η * (k0 + 1) := by
    rw [div_le_iff₀ hpe] at hk0
    nlinarith
  refine ⟨k0, fun n => cfun A k0 ε' (rs n).num (rs n).den, ?_⟩
  have hden := tendsto_den_of_irrational hα hrs
  rw [Metric.tendstoUniformlyOn_iff]
  intro e he
  have hE := errC_nonneg k0 η
  filter_upwards [hden.eventually_ge_atTop (⌈errC k0 η / e⌉₊ + 1)] with n hn t ht
  have hq : 0 < (rs n).den := (rs n).den_pos
  have hcop : IsCoprime (rs n).num ((rs n).den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs]
    simpa using (rs n).reduced
  have hest := rational_estimate hA hε' hη0 (by rw [hη]; linarith) hC1 hC hk0' (rs n).num hq
    hcop ht
  have hqR : (⌈errC k0 η / e⌉₊ : ℝ) + 1 ≤ (rs n).den := by exact_mod_cast hn
  have hceil := Nat.le_ceil (errC k0 η / e)
  have hqpos : (0 : ℝ) < (rs n).den := by exact_mod_cast hq
  have hlt : errC k0 η / (rs n).den < e := by
    rw [div_lt_iff₀ hqpos]
    have h1 := (div_le_iff₀ he).1 hceil
    have h2 := mul_le_mul_of_nonneg_right hqR he.le
    nlinarith
  simp only [Real.dist_eq, zero_sub, abs_neg]
  rw [Rat.cast_def]
  exact lt_of_le_of_lt hest hlt

variable [hH : Hypotheses]
include hH

theorem accel_int {δ : ℝ} {A : ℂ → M2} (hA : IsAnalyticCocycle δ A) {α : ℝ}
    (hα : Irrational α)
    (hlim : Tendsto (fun ε => (L α A ε - L α A 0) / (2 * Real.pi * ε)) (𝓝[>] 0)
      (𝓝 (accel α A))) :
    ∃ k : ℤ, accel α A = k := by
  have hex : ∀ n : ℕ, ∃ r : ℚ, α < r ∧ (r : ℝ) < α + 1 / ((n : ℝ) + 1) := fun n =>
    exists_rat_btwn (by have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
                        linarith)
  choose rs hrs1 hrs2 using hex
  have hrs : Tendsto (fun n => (rs n : ℝ)) atTop (𝓝 α) := by
    have hu : Tendsto (fun n : ℕ => α + 1 / ((n : ℝ) + 1)) atTop (𝓝 α) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add α
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
      (fun n => (hrs1 n).le) (fun n => (hrs2 n).le)
  have hδ := hA.pos
  obtain ⟨k0, c, hu⟩ := L_rational_asymptotics hA hα hrs (ε' := δ / 2) (by linarith)
    (by linarith)
  have hjks : ∀ t ∈ Icc (-(δ / 2)) (δ / 2),
      Tendsto (fun n => L (rs n) A t) atTop (𝓝 (L α A t)) := by
    intro t ht
    have htd : |t| < δ := by rw [abs_lt]; constructor <;> linarith [ht.1, ht.2]
    have hconst : TendstoUniformlyOn (fun _ : ℕ => cshift A t) (cshift A t) atTop
        (strip (δ - |t|)) := fun u hu => Eventually.of_forall fun _ _ _ => refl_mem_uniformity hu
    have h := jks_continuity (hA.cshift htd) hα (fun _ => hA.cshift htd) hrs hconst
    simpa [L_cshift] using h
  have hg : ∀ t ∈ Icc (-(δ / 2)) (δ / 2),
      Tendsto (fun n => plModel k0 (c n) t) atTop (𝓝 (L α A t)) := by
    intro t ht
    have := (hjks t ht).sub (hu.tendsto_at ht)
    simpa using this
  have hS : HasSupportSlopes (plSlopes k0) (-(δ / 2)) (δ / 2) (L α A) :=
    HasSupportSlopes.of_tendsto
      (Eventually.of_forall fun n => hasSupportSlopes_plModel k0 (c n) _ _) hg
  have hpi := Real.pi_pos
  have hd : Tendsto (fun h => (L α A h - L α A 0) / h) (𝓝[>] 0)
      (𝓝 (2 * Real.pi * accel α A)) := by
    refine (hlim.const_mul (2 * Real.pi)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h (hh : 0 < h)
    field_simp
  have hmem := mem_of_hasSupportSlopes (by linarith) hS hd
  obtain ⟨k, -, hk⟩ := Finset.mem_image.1 hmem
  refine ⟨-k, ?_⟩
  have h2 : (2 * Real.pi) * accel α A = (2 * Real.pi) * ((-k : ℤ) : ℝ) := by
    push_cast; linarith
  exact mul_left_cancel₀ (by positivity) h2

/-- **Theorem (acceleration is quantized).**  For irrational `α` and `A` analytic on a strip,
the one-sided limit defining the acceleration exists and is an integer. -/
theorem quantized {δ : ℝ} {A : ℂ → M2} (hA : IsAnalyticCocycle δ A) {α : ℝ} (hα : Irrational α) :
    Tendsto (fun ε => (L α A ε - L α A 0) / (2 * Real.pi * ε)) (𝓝[>] 0) (𝓝 (accel α A)) ∧
      ∃ k : ℤ, accel α A = k := by
  have hfirst : Tendsto (fun ε => (L α A ε - L α A 0) / (2 * Real.pi * ε)) (𝓝[>] 0)
      (𝓝 (accel α A)) := by
    have hc := L_convexOn hA α
    have h0 : (0 : ℝ) ∈ interior (Ioo (-δ) δ) := by
      rw [interior_Ioo]; exact ⟨by linarith [hA.pos], hA.pos⟩
    have hd := (hc.differentiableWithinAt_Ioi_of_mem_interior h0).hasDerivWithinAt
    rw [hasDerivWithinAt_iff_tendsto_slope' (by simp : (0 : ℝ) ∉ Ioi 0)] at hd
    have hT : Tendsto (fun ε => (L α A ε - L α A 0) / (2 * Real.pi * ε)) (𝓝[>] 0)
        (𝓝 (derivWithin (L α A) (Ioi 0) 0 / (2 * Real.pi))) := by
      refine (hd.div_const (2 * Real.pi)).congr fun ε => ?_
      rw [slope_def_field, sub_zero]
      ring
    rw [accel, hT.limUnder_eq]
    exact hT
  exact ⟨hfirst, accel_int hA hα hfirst⟩

end AvilaGlobal
