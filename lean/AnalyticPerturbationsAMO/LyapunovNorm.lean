/-
# Independence of the Lyapunov exponent from the matrix norm

`AMO.lyapunov` is defined with the `ℓ^∞` operator norm on `M₂(ℂ)`.  Here we prove that any
continuous function `N` comparable to it, `c‖M‖ ≤ N(M) ≤ C‖M‖`, gives the same limit
`(1/n) ∫ log N(A_n) → L(α, A)`.  In particular this holds for the Euclidean operator norm
`‖M‖₂ = ‖M : ℂ² → ℂ²‖` used in the paper.  Everything here is proved.
-/
import AnalyticPerturbationsAMO.Cocycle

noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace AMO

variable {α : ℝ} {A : ℝ → M2}

/-- **Norm independence.** -/
theorem IsSLCocycle.tendsto_lyapunov_of_equiv (hA : IsSLCocycle A) {N : M2 → ℝ}
    (hN : Continuous N) {c C : ℝ} (hc : 0 < c) (hbd : ∀ M : M2, c * ‖M‖ ≤ N M ∧ N M ≤ C * ‖M‖) :
    Tendsto (fun n : ℕ => (∫ x in (0 : ℝ)..1, Real.log (N (iter α A n x))) / n) atTop
      (𝓝 (lyapunov α A)) := by
  have hpos : ∀ n x, 0 < N (iter α A n x) := fun n x =>
    lt_of_lt_of_le (mul_pos hc (zero_lt_one.trans_le (hA.one_le_norm_iter n x))) (hbd _).1
  have hnpos : ∀ n x, 0 < ‖iter α A n x‖ := fun n x =>
    zero_lt_one.trans_le (hA.one_le_norm_iter n x)
  have hCpos : 0 < C := by
    have h := (hbd 1).1.trans (hbd 1).2
    have h1 : (0 : ℝ) < ‖(1 : M2)‖ := by
      simp
    nlinarith
  have hcontN : ∀ n, Continuous fun x => Real.log (N (iter α A n x)) := fun n =>
    (hN.comp (continuous_iter hA.continuous n)).log (fun x => (hpos n x).ne')
  -- `u_n + log c ≤ v_n ≤ u_n + log C`
  have hlow : ∀ n : ℕ, lyapSeq α A n + Real.log c ≤
      ∫ x in (0 : ℝ)..1, Real.log (N (iter α A n x)) := by
    intro n
    have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
      (zero_le_one : (0 : ℝ) ≤ 1)
      (((hA.continuous_log_norm_iter (α := α) n).add
        (continuous_const (y := Real.log c))).intervalIntegrable 0 1)
      ((hcontN n).intervalIntegrable 0 1) (fun x _ => by
        show Real.log ‖iter α A n x‖ + Real.log c ≤ _
        rw [← Real.log_mul (hnpos n x).ne' hc.ne', mul_comm]
        exact Real.log_le_log (mul_pos hc (hnpos n x)) (hbd _).1)
    simp only [Pi.add_apply] at h
    rw [intervalIntegral.integral_add ((hA.continuous_log_norm_iter n).intervalIntegrable 0 1)
      intervalIntegrable_const, intervalIntegral.integral_const] at h
    simpa [lyapSeq] using h
  have hhigh : ∀ n : ℕ, ∫ x in (0 : ℝ)..1, Real.log (N (iter α A n x)) ≤
      lyapSeq α A n + Real.log C := by
    intro n
    have h := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
      (zero_le_one : (0 : ℝ) ≤ 1)
      ((hcontN n).intervalIntegrable 0 1)
      (((hA.continuous_log_norm_iter (α := α) n).add
        (continuous_const (y := Real.log C))).intervalIntegrable 0 1)
      (fun x _ => by
        show _ ≤ Real.log ‖iter α A n x‖ + Real.log C
        rw [← Real.log_mul (hnpos n x).ne' hCpos.ne', mul_comm]
        exact Real.log_le_log (hpos n x) (hbd _).2)
    simp only [Pi.add_apply] at h
    rw [intervalIntegral.integral_add ((hA.continuous_log_norm_iter n).intervalIntegrable 0 1)
      intervalIntegrable_const, intervalIntegral.integral_const] at h
    simpa [lyapSeq] using h
  -- squeeze
  have hlim := hA.tendsto_lyapunov (α := α)
  have hc' : Tendsto (fun n : ℕ => lyapSeq α A n / n + Real.log c / n) atTop
      (𝓝 (lyapunov α A)) := by
    simpa using hlim.add (tendsto_const_div_atTop_nhds_zero_nat (Real.log c))
  have hC' : Tendsto (fun n : ℕ => lyapSeq α A n / n + Real.log C / n) atTop
      (𝓝 (lyapunov α A)) := by
    simpa using hlim.add (tendsto_const_div_atTop_nhds_zero_nat (Real.log C))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hc' hC' (fun n => ?_) (fun n => ?_)
  · rw [← add_div]; exact div_le_div_of_nonneg_right (hlow n) (Nat.cast_nonneg n)
  · rw [← add_div]; exact div_le_div_of_nonneg_right (hhigh n) (Nat.cast_nonneg n)

/-- The Euclidean operator norm of a `2 × 2` matrix, `‖M‖₂ = ‖M : ℂ² → ℂ²‖`. -/
def euclidNorm (M : M2) : ℝ :=
  ‖(Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) M)‖

open WithLp in
/-- Entries are bounded by the Euclidean operator norm. -/
lemma norm_entry_le_euclidNorm (M : M2) (i j : Fin 2) : ‖M i j‖ ≤ euclidNorm M := by
  have h := (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) M).le_opNorm (toLp 2 (Pi.single j 1))
  rw [toEuclideanCLM_toLp] at h
  have hn : ‖(toLp 2 (Pi.single j (1 : ℂ)) : EuclideanSpace ℂ (Fin 2))‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    fin_cases j <;> simp [Fin.sum_univ_two, Pi.single_apply]
  rw [hn, mul_one] at h
  calc ‖M i j‖ = ‖(toLp 2 (M *ᵥ Pi.single j 1) : EuclideanSpace ℂ (Fin 2)) i‖ := by
        simp
    _ ≤ ‖(toLp 2 (M *ᵥ Pi.single j 1) : EuclideanSpace ℂ (Fin 2))‖ := PiLp.norm_apply_le _ i
    _ ≤ euclidNorm M := h

lemma norm_le_two_euclidNorm (M : M2) : ‖M‖ ≤ 2 * euclidNorm M := by
  have hrow : ∀ i, ‖M i 0‖ + ‖M i 1‖ ≤ 2 * euclidNorm M := fun i => by
    linarith [norm_entry_le_euclidNorm M i 0, norm_entry_le_euclidNorm M i 1]
  have h0 : 0 ≤ euclidNorm M := norm_nonneg _
  rw [linfty_opNorm_def]
  have : ((Finset.univ : Finset (Fin 2)).sup fun i : Fin 2 => ∑ j : Fin 2, ‖M i j‖₊) ≤
      ⟨2 * euclidNorm M, by positivity⟩ := by
    refine Finset.sup_le fun i _ => ?_
    refine NNReal.coe_le_coe.1 ?_
    change _ ≤ 2 * euclidNorm M
    simpa [Fin.sum_univ_two] using hrow i
  exact_mod_cast this

open WithLp in
lemma euclidNorm_le (M : M2) : euclidNorm M ≤ 2 * ‖M‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun v => ?_)
  obtain ⟨x, rfl⟩ : ∃ x, v = toLp 2 x := ⟨ofLp v, rfl⟩
  rw [toEuclideanCLM_toLp]
  have hx : ∀ j, ‖x j‖ ≤ ‖(toLp 2 x : EuclideanSpace ℂ (Fin 2))‖ := fun j =>
    PiLp.norm_apply_le (toLp 2 x) j
  have hcomp : ∀ i, ‖(M *ᵥ x) i‖ ≤ ‖M‖ * ‖(toLp 2 x : EuclideanSpace ℂ (Fin 2))‖ := by
    intro i
    have hr := row_sum_le_norm M i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    calc ‖M i 0 * x 0 + M i 1 * x 1‖ ≤ ‖M i 0‖ * ‖x 0‖ + ‖M i 1‖ * ‖x 1‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ ‖M i 0‖ * ‖(toLp 2 x : EuclideanSpace ℂ (Fin 2))‖ +
          ‖M i 1‖ * ‖(toLp 2 x : EuclideanSpace ℂ (Fin 2))‖ := by
          gcongr
          · exact hx 0
          · exact hx 1
      _ ≤ ‖M‖ * ‖(toLp 2 x : EuclideanSpace ℂ (Fin 2))‖ := by
          rw [← add_mul]
          exact mul_le_mul_of_nonneg_right hr (norm_nonneg _)
  rw [EuclideanSpace.norm_eq, Real.sqrt_le_left (by positivity)]
  simp only [Fin.sum_univ_two]
  have h0 := hcomp 0
  have h1 := hcomp 1
  have hn0 := norm_nonneg ((M *ᵥ x) 0)
  have hn1 := norm_nonneg ((M *ᵥ x) 1)
  set B := ‖M‖ * ‖(toLp 2 x : EuclideanSpace ℂ (Fin 2))‖
  have hB : 0 ≤ B := le_trans hn0 h0
  calc ‖(toLp 2 (M *ᵥ x) : EuclideanSpace ℂ (Fin 2)) 0‖ ^ 2 +
        ‖(toLp 2 (M *ᵥ x) : EuclideanSpace ℂ (Fin 2)) 1‖ ^ 2
      = ‖(M *ᵥ x) 0‖ ^ 2 + ‖(M *ᵥ x) 1‖ ^ 2 := rfl
    _ ≤ B ^ 2 + B ^ 2 := by gcongr
    _ ≤ (2 * ‖M‖ * ‖(toLp 2 x : EuclideanSpace ℂ (Fin 2))‖) ^ 2 := by
        rw [show 2 * ‖M‖ * ‖(toLp 2 x : EuclideanSpace ℂ (Fin 2))‖ = 2 * B by ring]
        nlinarith

/-- The Euclidean and `ℓ^∞` operator norms are equivalent: `‖M‖/2 ≤ ‖M‖₂ ≤ 2‖M‖`. -/
lemma euclidNorm_equiv : ∀ M : M2, (1 / 2 : ℝ) * ‖M‖ ≤ euclidNorm M ∧
    euclidNorm M ≤ 2 * ‖M‖ := fun M =>
  ⟨by linarith [norm_le_two_euclidNorm M], euclidNorm_le M⟩

lemma continuous_euclidNorm : Continuous euclidNorm :=
  (LinearMap.continuous_of_finiteDimensional
    (Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ)).toAlgEquiv.toLinearEquiv.toLinearMap).norm

/-- **The Lyapunov exponent with the Euclidean operator norm** (the paper's convention)
coincides with `AMO.lyapunov`. -/
theorem IsSLCocycle.tendsto_lyapunov_euclid (hA : IsSLCocycle A) :
    Tendsto (fun n : ℕ => (∫ x in (0 : ℝ)..1, Real.log (euclidNorm (iter α A n x))) / n)
      atTop (𝓝 (lyapunov α A)) := by
  exact hA.tendsto_lyapunov_of_equiv continuous_euclidNorm (by norm_num) euclidNorm_equiv

end AMO
