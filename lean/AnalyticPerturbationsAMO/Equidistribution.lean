/-
# Weyl's uniform equidistribution for irrational rotations

For irrational `α` and a continuous `1`-periodic `f`, the Birkhoff averages
`(1/n) ∑_{k<n} f(x + kα)` converge to `∫_0^1 f` **uniformly in `x`** (unique ergodicity of the
irrational rotation).  Proof: geometric sums for the characters `e(qx)`, `q ≠ 0`, and uniform
density of trigonometric polynomials (Stone–Weierstrass, `span_fourier_closure_eq_top`).
This is the input that replaces Furman's theorem in Lemma 2.5.  Everything here is proved.
-/
import AnalyticPerturbationsAMO.Weyl

noncomputable section

open Complex Finset Filter

namespace AMO

/-- The Birkhoff average `(1/n) ∑_{k<n} f(x + kα)`. -/
def birk (α : ℝ) (f : ℝ → ℂ) (n : ℕ) (x : ℝ) : ℂ := (n : ℂ)⁻¹ * ∑ k ∈ range n, f (x + k * α)

lemma e_natMul (k : ℕ) (t : ℝ) : e (k * t) = e t ^ k := by
  unfold e
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma e_ne_one {q : ℤ} (hq : q ≠ 0) {α : ℝ} (hα : Irrational α) : e (q * α) ≠ 1 := by
  intro h
  unfold e at h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
  have hre : (2 * Real.pi * (q * α) : ℝ) = 2 * Real.pi * n := by
    have := congrArg Complex.im hn
    simp at this
    linarith [this]
  have h2 : (q : ℝ) * α = n := by
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    have := mul_left_cancel₀ hpi (by rw [← mul_assoc]; linarith [hre] : 2 * Real.pi * ((q : ℝ) * α) = 2 * Real.pi * n)
    exact this
  exact (hα.intCast_mul hq).ne_int n h2

lemma norm_geom_sum_le {z : ℂ} (hz : ‖z‖ = 1) (hz1 : z ≠ 1) (n : ℕ) :
    ‖∑ k ∈ range n, z ^ k‖ ≤ 2 / ‖z - 1‖ := by
  rw [geom_sum_eq hz1 n, norm_div]
  gcongr
  calc ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hz, one_pow, norm_one]; norm_num

lemma norm_birk_e {q : ℤ} (hq : q ≠ 0) {α : ℝ} (hα : Irrational α) (n : ℕ) (x : ℝ) :
    ‖birk α (fun y => e (q * y)) n x‖ ≤ (n : ℝ)⁻¹ * (2 / ‖e (q * α) - 1‖) := by
  unfold birk
  have hsum : ∑ k ∈ range n, e (q * (x + k * α)) = e (q * x) * ∑ k ∈ range n, e (q * α) ^ k := by
    rw [mul_sum]
    congr 1
    funext k
    rw [← e_natMul, ← e_add]
    congr 1
    ring
  rw [hsum, norm_mul, norm_mul, norm_e, one_mul, norm_inv, Complex.norm_natCast]
  gcongr
  exact norm_geom_sum_le (norm_e _) (e_ne_one hq hα) n

/-! ### Trigonometric polynomials -/

/-- The trigonometric polynomial `∑_q c_q e(qx)`. -/
def tp (c : ℤ →₀ ℂ) (x : ℝ) : ℂ := ∑ q ∈ c.support, c q * e (q * x)

lemma continuous_tp (c : ℤ →₀ ℂ) : Continuous (tp c) := by
  unfold tp e
  fun_prop

lemma birk_tp (α : ℝ) (c : ℤ →₀ ℂ) (n : ℕ) (x : ℝ) :
    birk α (tp c) n x = ∑ q ∈ c.support, c q * birk α (fun y => e (q * y)) n x := by
  unfold birk tp
  rw [Finset.sum_comm, mul_sum]
  congr 1
  funext q
  rw [mul_sum, mul_sum, mul_sum]
  congr 1
  funext k
  ring

lemma birk_const (α : ℝ) {n : ℕ} (hn : n ≠ 0) (x : ℝ) : birk α (fun y => e ((0 : ℤ) * y)) n x = 1 := by
  unfold birk
  simp only [Int.cast_zero, zero_mul, e_zero, sum_const, card_range, nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (by exact_mod_cast hn)

lemma integral_e (q : ℤ) : ∫ x in (0 : ℝ)..1, e (q * x) = if q = 0 then 1 else 0 := by
  split_ifs with hq
  · subst hq; simp
  · have hc : (2 * Real.pi * q : ℂ) * I ≠ 0 := by
      have : (q : ℂ) ≠ 0 := by exact_mod_cast hq
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [hpi, this, I_ne_zero]
    have h := integral_exp_mul_complex (a := 0) (b := 1) hc
    have he : ∀ x : ℝ, e (q * x) = Complex.exp ((2 * Real.pi * q : ℂ) * I * x) := fun x => by
      unfold e; congr 1; push_cast; ring
    simp only [he]
    rw [h]
    have h1 : Complex.exp ((2 * Real.pi * q : ℂ) * I * ((1 : ℝ) : ℂ)) = 1 := by
      rw [Complex.exp_eq_one_iff]
      exact ⟨q, by push_cast; ring⟩
    rw [h1]
    simp

lemma integral_tp (c : ℤ →₀ ℂ) : ∫ x in (0 : ℝ)..1, tp c x = c 0 := by
  unfold tp
  rw [intervalIntegral.integral_finset_sum (fun q _ => by
    unfold e; exact (by fun_prop : Continuous fun x : ℝ =>
      c q * Complex.exp (((2 * Real.pi * (q * x) : ℝ) : ℂ) * I)).intervalIntegrable 0 1)]
  simp only [intervalIntegral.integral_const_mul, integral_e, mul_ite, mul_one, mul_zero,
    sum_ite_eq', Finsupp.mem_support_iff]
  split_ifs with h
  · rfl
  · push_neg at h; exact h.symm

/-- Birkhoff averages of trigonometric polynomials converge uniformly to the mean. -/
lemma tendsto_birk_tp {α : ℝ} (hα : Irrational α) (c : ℤ →₀ ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ x, ‖birk α (tp c) n x - c 0‖ ≤ ε := by
  set Kc : ℝ := ∑ q ∈ c.support.erase 0, ‖c q‖ * (2 / ‖e (q * α) - 1‖)
  have hK0 : 0 ≤ Kc := sum_nonneg fun q _ => by positivity
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (Kc / ε)
  refine ⟨n₀ + 1, fun n hn x => ?_⟩
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  rw [birk_tp]
  have hsplit : ∑ q ∈ c.support, c q * birk α (fun y => e (q * y)) n x - c 0 =
      ∑ q ∈ c.support.erase 0, c q * birk α (fun y => e (q * y)) n x := by
    by_cases h0 : (0 : ℤ) ∈ c.support
    · rw [← add_sum_erase _ _ h0, birk_const α hn0, mul_one]; ring
    · rw [erase_eq_of_notMem h0, Finsupp.notMem_support_iff.1 h0, sub_zero]
  rw [hsplit]
  calc ‖∑ q ∈ c.support.erase 0, c q * birk α (fun y => e (q * y)) n x‖
      ≤ ∑ q ∈ c.support.erase 0, ‖c q‖ * ((n : ℝ)⁻¹ * (2 / ‖e (q * α) - 1‖)) := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun q hq => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (norm_birk_e (ne_of_mem_erase hq) hα n x) (norm_nonneg _)
    _ = (n : ℝ)⁻¹ * Kc := by
        rw [mul_sum]; congr 1; funext q; ring
    _ ≤ ε := by
        rw [inv_mul_le_iff₀ hnpos]
        have : Kc / ε < n := lt_of_lt_of_le hn₀ (by exact_mod_cast (by omega : n₀ ≤ n))
        rw [div_lt_iff₀ hε] at this
        linarith

/-- Uniform approximation of continuous periodic functions by trigonometric polynomials. -/
lemma exists_tp_approx {f : ℝ → ℂ} (hf : Continuous f) (hp : Function.Periodic f 1) {ε : ℝ}
    (hε : 0 < ε) : ∃ c : ℤ →₀ ℂ, ∀ x, ‖f x - tp c x‖ ≤ ε := by
  have : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  let g : C(AddCircle (1 : ℝ), ℂ) := ⟨hp.lift, continuous_quot_lift _ hf⟩
  have hg : g ∈ (Submodule.span ℂ (Set.range (@_root_.fourier (1 : ℝ)))).topologicalClosure := by
    rw [span_fourier_closure_eq_top]; trivial
  obtain ⟨P, hP, hdist⟩ := Metric.mem_closure_iff.1 hg ε hε
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hP
  refine ⟨c, fun x => ?_⟩
  have hval : (c.sum fun q a => a • _root_.fourier q) (x : AddCircle (1 : ℝ)) = tp c x := by
    simp only [Finsupp.sum, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_smul,
      Pi.smul_apply, smul_eq_mul, tp]
    congr 1
    funext q
    rw [fourier_coe_apply]
    unfold e
    congr 2
    push_cast
    ring
  have hgx : g (x : AddCircle (1 : ℝ)) = f x := rfl
  have h1 : dist (g (x : AddCircle (1 : ℝ)))
      ((c.sum fun q a => a • _root_.fourier q) (x : AddCircle (1 : ℝ))) ≤ ε :=
    (ContinuousMap.dist_apply_le_dist _).trans hdist.le
  rw [hgx, hval, dist_eq_norm] at h1
  exact h1

/-- **Weyl's uniform equidistribution theorem** (complex-valued). -/
theorem weyl_uniform {α : ℝ} (hα : Irrational α) {f : ℝ → ℂ} (hf : Continuous f)
    (hp : Function.Periodic f 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ x, ‖birk α f n x - ∫ y in (0 : ℝ)..1, f y‖ ≤ ε := by
  obtain ⟨c, hc⟩ := exists_tp_approx hf hp (by positivity : 0 < ε / 4)
  obtain ⟨n₀, hn₀⟩ := tendsto_birk_tp hα c (by positivity : 0 < ε / 4)
  refine ⟨n₀ + 1, fun n hn x => ?_⟩
  have hn0 : n ≠ 0 := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  -- `birk f - birk P`
  have h1 : ‖birk α f n x - birk α (tp c) n x‖ ≤ ε / 4 := by
    unfold birk
    rw [← mul_sub, ← sum_sub_distrib, norm_mul, norm_inv, Complex.norm_natCast,
      inv_mul_le_iff₀ hnpos]
    calc ‖∑ k ∈ range n, (f (x + k * α) - tp c (x + k * α))‖
        ≤ ∑ k ∈ range n, ε / 4 := (norm_sum_le _ _).trans (sum_le_sum fun k _ => hc _)
      _ = n * (ε / 4) := by rw [sum_const, card_range, nsmul_eq_mul]
  -- `∫ f - ∫ P`
  have h2 : ‖(∫ y in (0 : ℝ)..1, f y) - c 0‖ ≤ ε / 4 := by
    rw [← integral_tp c, ← intervalIntegral.integral_sub (hf.intervalIntegrable 0 1)
      ((continuous_tp c).intervalIntegrable 0 1)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (f := fun y => f y - tp c y) (C := ε / 4) (fun y _ => hc y)
    simpa using this
  have h3 := hn₀ n (by omega) x
  calc ‖birk α f n x - ∫ y in (0 : ℝ)..1, f y‖
      = ‖(birk α f n x - birk α (tp c) n x) + (birk α (tp c) n x - c 0) -
          ((∫ y in (0 : ℝ)..1, f y) - c 0)‖ := by ring_nf
    _ ≤ ε / 4 + ε / 4 + ε / 4 := by
        refine (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add h1 h3)) h2)
    _ ≤ ε := by linarith

/-- **Weyl's uniform equidistribution theorem** (real-valued). -/
theorem weyl_uniform_real {α : ℝ} (hα : Irrational α) {g : ℝ → ℝ} (hg : Continuous g)
    (hp : Function.Periodic g 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ x,
      |(n : ℝ)⁻¹ * ∑ k ∈ range n, g (x + k * α) - ∫ y in (0 : ℝ)..1, g y| ≤ ε := by
  obtain ⟨n₀, h⟩ := weyl_uniform hα (f := fun y => (g y : ℂ)) (Complex.continuous_ofReal.comp hg)
    (fun y => by simp [hp y]) hε
  refine ⟨n₀, fun n hn x => ?_⟩
  have := h n hn x
  unfold birk at this
  rw [intervalIntegral.integral_ofReal] at this
  have e1 : ((n : ℂ)⁻¹ * ∑ k ∈ range n, (g (x + k * α) : ℂ)) =
      (((n : ℝ)⁻¹ * ∑ k ∈ range n, g (x + k * α) : ℝ) : ℂ) := by push_cast; rfl
  rw [e1, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at this
  exact this

end AMO
