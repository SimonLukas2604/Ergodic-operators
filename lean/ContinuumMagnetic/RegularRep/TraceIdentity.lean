/-
# The trace identity for the regular representation  (paper §4, IDS as spectral measure of `H̃`)

For a summable self-adjoint symbol `K`, let `H_x = op α K x` be the covariant family on `ℓ²(ℤ)`
and `H̃ = op2 α K` its two-dimensional realization on `ℓ²(ℤ²)`.  We prove:

* `⟪δ_p, op2 α S δ_p⟫ = S_{0,0}` for every `p ∈ ℤ²` and `∫₀¹ ⟪δ₀, op α S x δ₀⟫ dx = S_{0,0}`
  (the `(r,q)` term of the fibre has `⟪δ₀, W_{r,q}(x) δ₀⟫ = [r = 0] e(qx)`);
* multiplicativity `op2 α (R ⋆ S) = op2 α R · op2 α S` (mirroring `AMO.op_tmul`);
* hence, via the twisted powers `K^{⋆n}`, `⟪δ_p, P(H̃) δ_p⟫ = ∫₀¹ ⟪δ₀, P(H_x) δ₀⟫ dx` for every
  polynomial `P`;
* by Weierstrass approximation on `[-‖K‖₁, ‖K‖₁]` and `‖cfc g T‖ ≤ sup_{σ(T)} |g|`, the same
  identity for `g(H̃)`, `g` continuous (with continuity of `x ↦ ⟪δ₀, g(H_x) δ₀⟫` obtained as a
  uniform limit of continuous functions);
* **conclusion**: the density of states measure of `x ↦ H_x` is the spectral measure of `H̃` at
  every standard basis vector `δ_p` (`isSpectralMeasure_op2_delta`).
-/
import ContinuumMagnetic.AffineIsland

noncomputable section

open scoped ComplexConjugate InnerProductSpace
open MeasureTheory Set Filter BoundedContinuousFunction AMO L2

namespace CMS

lemma inner_delta_left2 {ι : Type*} [DecidableEq ι] (n : ι) (u : L2 ι) :
    ⟪delta n, u⟫_ℂ = u n := by
  rw [delta, lp.inner_single_left]
  simp

lemma inner_delta_W2_delta (α : ℝ) (k p : ℤ × ℤ) :
    ⟪delta p, W2 α k.1 k.2 (delta p)⟫_ℂ = if k = 0 then 1 else 0 := by
  rw [inner_delta_left2, W2_apply, delta, lp.single_apply, Pi.single_apply]
  by_cases hk : k = 0
  · subst hk; simp
  · have h : ¬ p + (k.1, k.2) = p := by
      intro h
      apply hk
      have : p + (k.1, k.2) = p + 0 := by simpa using h
      simpa using this
    simp [hk, h]

/-- The diagonal matrix element functional `T ↦ ⟪ψ, T ψ⟫` is continuous linear. -/
def diagCLM {ι : Type*} (ψ : L2 ι) : Op ι →L[ℂ] ℂ :=
  (innerSL ℂ ψ).comp (ContinuousLinearMap.apply ℂ (L2 ι) ψ)

lemma diagCLM_apply {ι : Type*} (ψ : L2 ι) (T : Op ι) : diagCLM ψ T = ⟪ψ, T ψ⟫_ℂ := rfl

/-- **Diagonal matrix elements of `op2`.** `⟪δ_p, H̃ δ_p⟫ = S_{0,0}` for every `p ∈ ℤ²`. -/
theorem inner_delta_op2_delta (α : ℝ) {S : Symbol} (hS : SymbolSummable S) (p : ℤ × ℤ) :
    ⟪delta p, op2 α S (delta p)⟫_ℂ = S 0 := by
  have h := (summable_op2 α hS).hasSum.mapL (diagCLM (delta p))
  rw [← diagCLM_apply, op2, h.tsum_eq.symm, tsum_eq_single 0]
  · simp [diagCLM_apply, W2_zero, delta]
  · intro k hk
    simp [diagCLM_apply, inner_delta_W2_delta, hk]

lemma inner_delta_W_delta (α x : ℝ) (k : ℤ × ℤ) :
    ⟪delta 0, W α x k.1 k.2 (delta 0)⟫_ℂ = if k.1 = 0 then e (k.2 * x) else 0 := by
  rw [inner_delta_left2, W_apply, delta, lp.single_apply, Pi.single_apply]
  by_cases hk : k.1 = 0
  · simp [hk]
  · simp [hk]

lemma integral_e_int (q : ℤ) : ∫ x in (0 : ℝ)..1, e (q * x) = if q = 0 then 1 else 0 := by
  by_cases hq : q = 0
  · simp [hq]
  · simp only [hq, ite_false]
    have hc : (2 * Real.pi * q : ℂ) * Complex.I ≠ 0 := by
      have : (q : ℂ) ≠ 0 := by exact_mod_cast hq
      simp [Real.pi_ne_zero, Complex.I_ne_zero, this]
    have : (fun x : ℝ => e (q * x)) = fun x : ℝ => Complex.exp (((2 * Real.pi * q : ℂ) * Complex.I) * x) := by
      funext x; unfold e; congr 1; push_cast; ring
    rw [this, integral_exp_mul_complex hc]
    have h1 : Complex.exp ((2 * Real.pi * q : ℂ) * Complex.I) = 1 := by
      have := e_intCast q
      unfold e at this
      rw [← this]; congr 1; push_cast; ring
    simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero, h1,
      sub_self, zero_div]

/-- **Phase average of the diagonal matrix element.** `∫₀¹ ⟪δ₀, S_x δ₀⟫ dx = S_{0,0}`. -/
theorem integral_inner_delta_op_delta (α : ℝ) {S : Symbol} (hS : SymbolSummable S) :
    ∫ x in (0 : ℝ)..1, ⟪delta 0, op α S x (delta 0)⟫_ℂ = S 0 := by
  have key : HasSum (fun k : ℤ × ℤ => ∫ x in (0 : ℝ)..1, S k * ⟪delta 0, W α x k.1 k.2 (delta 0)⟫_ℂ)
      (∫ x in (0 : ℝ)..1, ⟪delta 0, op α S x (delta 0)⟫_ℂ) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence (fun k _ => ‖S k‖)
      (fun k => ?_) (fun k => ?_) (ae_of_all _ fun _ _ => hS) ?_ (ae_of_all _ fun x _ => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      simp only [inner_delta_W_delta]
      split_ifs
      · unfold e; fun_prop
      · fun_prop
    · refine ae_of_all _ fun x _ => ?_
      rw [norm_mul, inner_delta_W_delta]
      split_ifs <;> simp
    · exact intervalIntegrable_const
    · have h := (summable_op (α := α) hS x).hasSum.mapL (diagCLM (delta 0))
      simpa [op, diagCLM_apply, inner_smul_left, inner_smul_right] using h
  rw [← key.tsum_eq, tsum_eq_single 0]
  · simp [W_zero, delta]
  · intro k hk
    rw [intervalIntegral.integral_const_mul]
    simp only [inner_delta_W_delta]
    split_ifs with h1
    · have h2 : k.2 ≠ 0 := fun h2 => hk (Prod.ext h1 h2)
      rw [integral_e_int]
      simp [h2]
    · simp

/-! ### Multiplicativity of the two-dimensional realization -/

/-- `‖H̃‖ ≤ ∑ |R_{r,q}|`. -/
theorem norm_op2_le (α : ℝ) {R : Symbol} (hR : SymbolSummable R) :
    ‖op2 α R‖ ≤ ∑' p, ‖R p‖ := by
  refine tsum_of_norm_bounded hR.hasSum (fun p => ?_)
  rw [norm_smul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_W2_le _ _ _)

/-- **`op2` is multiplicative**: `op2(R ⋆ S) = op2(R) op2(S)`. -/
theorem op2_tmul (α : ℝ) {R S : Symbol} (hR : SymbolSummable R) (hS : SymbolSummable S) :
    op2 α (tmul α R S) = op2 α R * op2 α S := by
  have hR0 := symbolSummable_iff_wsum_zero.1 hR
  have hS0 := symbolSummable_iff_wsum_zero.1 hS
  have hnR : Summable fun p => ‖R p • W2 α p.1 p.2‖ :=
    hR.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => by
      rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) (norm_W2_le _ _ _))
  have hnS : Summable fun p => ‖S p • W2 α p.1 p.2‖ :=
    hS.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => by
      rw [norm_smul]; exact mul_le_of_le_one_right (norm_nonneg _) (norm_W2_le _ _ _))
  let T : (ℤ × ℤ) × (ℤ × ℤ) → Op (ℤ × ℤ) := fun z =>
    (R z.1 * S z.2 * wphase α z.1 z.2) • W2 α (z.1 + z.2).1 (z.1 + z.2).2
  have hT : ∀ z, (R z.1 • W2 α z.1.1 z.1.2) * (S z.2 • W2 α z.2.1 z.2.2) = T z := by
    intro z
    rw [smul_mul_smul_comm, ContinuousLinearMap.mul_def, W2_mul, smul_smul]
    rfl
  have hTn : Summable fun z => ‖(T ∘ shearEquiv) z‖ := by
    refine (summable_majorant_shear hR0 hS0).of_nonneg_of_le (fun _ => norm_nonneg _)
      (fun z => ?_)
    simp only [Function.comp_apply, T, shearEquiv, Equiv.coe_fn_mk, majorant, wt,
      zero_mul, add_zero, Real.exp_zero, mul_one]
    rw [norm_smul, norm_mul, norm_mul, norm_wphase, mul_one]
    exact mul_le_of_le_one_right (by positivity) (norm_W2_le _ _ _)
  have hTs : Summable (T ∘ shearEquiv) := hTn.of_norm
  unfold op2
  rw [tsum_mul_tsum_of_summable_norm hnR hnS]
  simp only [hT]
  rw [← shearEquiv.tsum_eq]
  show _ = ∑' c, (T ∘ shearEquiv) c
  rw [hTs.tsum_prod]
  congr 1
  funext p
  have hc : Summable fun p₁ => R p₁ * S (p - p₁) * wphase α p₁ (p - p₁) :=
    (summable_tmul_term le_rfl le_rfl hR0 hS0 p).of_norm
  rw [tmul]
  refine (hc.tsum_smul_const (W2 α p.1 p.2)).symm.trans ?_
  congr 1
  funext p₁
  simp [T, shearEquiv]

/-! ### Symbol powers -/

/-- The twisted powers `K^{⋆n}` of a symbol: `K^{⋆0} = δ₀`, `K^{⋆(n+1)} = K ⋆ K^{⋆n}`. -/
def spow (α : ℝ) (K : Symbol) : ℕ → Symbol
  | 0 => Pi.single 0 1
  | n + 1 => tmul α K (spow α K n)

lemma symbolSummable_spow {α : ℝ} {K : Symbol} (hK : SymbolSummable K) (n : ℕ) :
    SymbolSummable (spow α K n) := by
  induction n with
  | zero => exact symbolSummable_single _ _
  | succ n ih =>
    exact (WSum.tmul le_rfl le_rfl (symbolSummable_iff_wsum_zero.1 hK)
      (symbolSummable_iff_wsum_zero.1 ih)).symbolSummable le_rfl le_rfl

/-- `op α (K^{⋆n}) x = (op α K x)^n`. -/
lemma op_spow (α : ℝ) {K : Symbol} (hK : SymbolSummable K) (n : ℕ) (x : ℝ) :
    op α (spow α K n) x = op α K x ^ n := by
  induction n with
  | zero =>
    rw [spow, op_single, pow_zero]
    simp [AMO.W_zero]
  | succ n ih => rw [spow, op_tmul hK (symbolSummable_spow hK n), ih, pow_succ']

/-- `op2 α (K^{⋆n}) = (op2 α K)^n`. -/
lemma op2_spow (α : ℝ) {K : Symbol} (hK : SymbolSummable K) (n : ℕ) :
    op2 α (spow α K n) = op2 α K ^ n := by
  induction n with
  | zero =>
    rw [spow, op2_single, pow_zero]
    simp [W2_zero]
  | succ n ih => rw [spow, op2_tmul α hK (symbolSummable_spow hK n), ih, pow_succ']

/-! ### Polynomials -/

open Polynomial in
lemma inner_aeval_eq_sum {ι : Type*} (ψ : L2 ι) (A : Op ι) (P : ℂ[X]) :
    ⟪ψ, aeval A P ψ⟫_ℂ = ∑ i ∈ Finset.range (P.natDegree + 1), P.coeff i * ⟪ψ, (A ^ i) ψ⟫_ℂ := by
  rw [aeval_eq_sum_range, ← diagCLM_apply, map_sum]
  simp [diagCLM_apply]

lemma continuous_inner_op (α : ℝ) {R : Symbol} (hR : SymbolSummable R) (ψ : L2 ℤ) :
    Continuous fun x => ⟪ψ, op α R x ψ⟫_ℂ :=
  (diagCLM ψ).continuous.comp (continuous_op hR)

open Polynomial in
/-- **Trace identity for polynomials.** For every polynomial `P` and every `p ∈ ℤ²`,
`⟪δ_p, P(H̃) δ_p⟫ = ∫₀¹ ⟪δ₀, P(H_x) δ₀⟫ dx`; both sides equal the `(0,0)` coefficient of the
symbol `∑ Pᵢ K^{⋆i}` of `P(K)`. -/
theorem inner_delta_aeval_op2 (α : ℝ) {K : Symbol} (hK : SymbolSummable K) (P : ℂ[X])
    (p : ℤ × ℤ) :
    ⟪delta p, aeval (op2 α K) P (delta p)⟫_ℂ =
      ∫ x in (0 : ℝ)..1, ⟪delta 0, aeval (op α K x) P (delta 0)⟫_ℂ := by
  simp_rw [inner_aeval_eq_sum]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_const_mul]
    simp_rw [← op_spow α hK i, ← op2_spow α hK i]
    rw [integral_inner_delta_op_delta α (symbolSummable_spow hK i),
      inner_delta_op2_delta α (symbolSummable_spow hK i)]
  · intro i _
    simp_rw [← op_spow α hK i]
    exact ((continuous_inner_op α (symbolSummable_spow hK i) _).const_smul (P.coeff i)
      ).intervalIntegrable _ _

/-! ### Continuous functions: Weierstrass approximation -/

lemma norm_delta {ι : Type*} [DecidableEq ι] (n : ι) : ‖(delta n : L2 ι)‖ = 1 := by
  rw [delta, lp.norm_single (by norm_num)]
  simp

lemma norm_inner_diag_sub_le {ι : Type*} {ψ : L2 ι} (hψ : ‖ψ‖ = 1) (A B : Op ι) :
    ‖⟪ψ, A ψ⟫_ℂ - ⟪ψ, B ψ⟫_ℂ‖ ≤ ‖A - B‖ := by
  rw [← inner_sub_right, ← _root_.sub_apply]
  calc ‖⟪ψ, (A - B) ψ⟫_ℂ‖ ≤ ‖ψ‖ * ‖(A - B) ψ‖ := norm_inner_le_norm _ _
    _ ≤ ‖ψ‖ * (‖A - B‖ * ‖ψ‖) := by gcongr; exact (A - B).le_opNorm ψ
    _ = ‖A - B‖ := by rw [hψ]; ring

open Polynomial in
lemma eval_map_ofReal (q : ℝ[X]) (t : ℝ) :
    (q.map (algebraMap ℝ ℂ)).eval (t : ℂ) = ((q.eval t : ℝ) : ℂ) := by
  rw [eval_map]
  exact eval₂_at_apply (algebraMap ℝ ℂ) t

open Polynomial in
/-- Uniform polynomial approximation inside the functional calculus: if `|q - g| < ε` on
`[-M, M]` and `T` is self-adjoint with `‖T‖ ≤ M`, then `‖g(T) - q(T)‖ ≤ ε`. -/
lemma norm_cfc_sub_aeval_le {ι : Type*} [DecidableEq ι] [Nonempty ι] {T : Op ι} (hT : IsSelfAdjoint T) {M ε : ℝ}
    (hM : ‖T‖ ≤ M) (hε : 0 ≤ ε) {g : ℝ → ℝ} (hg : Continuous g) {q : ℝ[X]}
    (hq : ∀ t ∈ Icc (-M) M, |q.eval t - g t| < ε) :
    ‖cfc (fun z : ℂ => ((g z.re : ℝ) : ℂ)) T - aeval T (q.map (algebraMap ℝ ℂ))‖ ≤ ε := by
  have : IsStarNormal T := hT.isStarNormal
  have : Nontrivial (L2 ι) := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    refine ⟨⟨delta i, 0, fun h => ?_⟩⟩
    have := congrArg norm h
    rw [norm_delta, norm_zero] at this
    exact one_ne_zero this
  rw [← cfc_polynomial (q.map (algebraMap ℝ ℂ)) T,
    ← cfc_sub (fun z : ℂ => ((g z.re : ℝ) : ℂ)) (fun z => (q.map (algebraMap ℝ ℂ)).eval z) T
      (Complex.continuous_ofReal.comp (hg.comp Complex.continuous_re)).continuousOn
      (Polynomial.continuous _).continuousOn]
  refine norm_cfc_le hε fun z hz => ?_
  have hre : z = (z.re : ℂ) := hT.mem_spectrum_eq_re hz
  have hzM : |z.re| ≤ M :=
    (Complex.abs_re_le_norm z).trans ((spectrum.norm_le_norm_of_mem hz).trans hM)
  have hev : (q.map (algebraMap ℝ ℂ)).eval z = ((q.eval z.re : ℝ) : ℂ) := by
    nth_rewrite 1 [hre]
    exact eval_map_ofReal q z.re
  rw [hev, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  exact (hq z.re (abs_le.1 hzM)).le

/-- **Trace identity for continuous functions.** For a summable self-adjoint symbol `K` and a
continuous `g : ℝ → ℝ`, the map `x ↦ ⟪δ₀, g(H_x) δ₀⟫` is continuous, and for every `p ∈ ℤ²`,
`⟪δ_p, g(H̃) δ_p⟫ = ∫₀¹ ⟪δ₀, g(H_x) δ₀⟫ dx`. -/
theorem inner_delta_cfc_op2 (α : ℝ) {K : Symbol} (hK : SymbolSummable K)
    (hsa : SymbolSelfAdjoint K) {g : ℝ → ℝ} (hg : Continuous g) :
    Continuous (fun x => ⟪delta 0, cfc (fun z : ℂ => ((g z.re : ℝ) : ℂ)) (op α K x) (delta 0)⟫_ℂ)
      ∧ ∀ p : ℤ × ℤ, ⟪delta p, cfc (fun z : ℂ => ((g z.re : ℝ) : ℂ)) (op2 α K) (delta p)⟫_ℂ =
        ∫ x in (0 : ℝ)..1,
          ⟪delta 0, cfc (fun z : ℂ => ((g z.re : ℝ) : ℂ)) (op α K x) (delta 0)⟫_ℂ := by
  set M : ℝ := ∑' p, ‖K p‖
  set G : ℂ → ℂ := fun z : ℂ => ((g z.re : ℝ) : ℂ)
  set b : ℝ → ℂ := fun x => ⟪delta 0, cfc G (op α K x) (delta 0)⟫_ℂ
  -- the polynomial approximants
  have approx : ∀ ε > 0, ∃ P : Polynomial ℂ,
      (∀ p : ℤ × ℤ, ‖⟪delta p, cfc G (op2 α K) (delta p)⟫_ℂ -
          ⟪delta p, Polynomial.aeval (op2 α K) P (delta p)⟫_ℂ‖ ≤ ε) ∧
      ∀ x, ‖b x - ⟪delta 0, Polynomial.aeval (op α K x) P (delta 0)⟫_ℂ‖ ≤ ε := by
    intro ε hε
    obtain ⟨q, hq⟩ := exists_polynomial_near_of_continuousOn (-M) M g hg.continuousOn ε hε
    refine ⟨q.map (algebraMap ℝ ℂ), fun p => ?_, fun x => ?_⟩
    · exact (norm_inner_diag_sub_le (norm_delta p) _ _).trans
        (norm_cfc_sub_aeval_le (isSelfAdjoint_op2 hK hsa) (norm_op2_le α hK) hε.le hg hq)
    · exact (norm_inner_diag_sub_le (norm_delta 0) _ _).trans
        (norm_cfc_sub_aeval_le (isSelfAdjoint_op hK hsa x) (norm_op_le hK x) hε.le hg hq)
  have hpcont : ∀ P : Polynomial ℂ,
      Continuous fun x => ⟪delta 0, Polynomial.aeval (op α K x) P (delta 0)⟫_ℂ := fun P =>
    (diagCLM (delta 0)).continuous.comp ((Polynomial.continuous_aeval P).comp (continuous_op hK))
  have hb : Continuous b := by
    refine continuous_of_uniform_approx_of_continuous fun u hu => ?_
    obtain ⟨ε, hε, hεu⟩ := Metric.mem_uniformity_dist.1 hu
    obtain ⟨P, -, hP⟩ := approx (ε / 2) (half_pos hε)
    refine ⟨_, hpcont P, fun x => hεu ?_⟩
    rw [dist_eq_norm]
    exact (hP x).trans_lt (half_lt_self hε)
  refine ⟨hb, fun p => eq_of_forall_dist_le fun ε hε => ?_⟩
  obtain ⟨P, hP1, hP2⟩ := approx (ε / 2) (half_pos hε)
  rw [dist_eq_norm]
  have hint : ∫ x in (0 : ℝ)..1, b x =
      (∫ x in (0 : ℝ)..1, ⟪delta 0, Polynomial.aeval (op α K x) P (delta 0)⟫_ℂ) +
        ∫ x in (0 : ℝ)..1, (b x - ⟪delta 0, Polynomial.aeval (op α K x) P (delta 0)⟫_ℂ) := by
    rw [intervalIntegral.integral_sub (hb.intervalIntegrable _ _)
      ((hpcont P).intervalIntegrable _ _)]
    ring
  have h2 : ‖∫ x in (0 : ℝ)..1,
      (b x - ⟪delta 0, Polynomial.aeval (op α K x) P (delta 0)⟫_ℂ)‖ ≤ ε / 2 := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (fun x _ => hP2 x)
    simpa using this
  change ‖⟪delta p, cfc G (op2 α K) (delta p)⟫_ℂ - ∫ x in (0 : ℝ)..1, b x‖ ≤ ε
  rw [hint, ← inner_delta_aeval_op2 α hK P p]
  calc _ = ‖(⟪delta p, cfc G (op2 α K) (delta p)⟫_ℂ -
          ⟪delta p, Polynomial.aeval (op2 α K) P (delta p)⟫_ℂ) -
        ∫ x in (0 : ℝ)..1, (b x - ⟪delta 0, Polynomial.aeval (op α K x) P (delta 0)⟫_ℂ)‖ := by
        ring_nf
    _ ≤ ε / 2 + ε / 2 := (norm_sub_le _ _).trans (add_le_add (hP1 p) h2)
    _ = ε := add_halves ε

/-! ### Conclusion -/

/-- **Every standard basis vector has the IDS as spectral measure.** If `ν` is the density of
states measure of the covariant family `x ↦ H_x = op α K x`, then `ν` is the spectral measure of
the two-dimensional realization `H̃ = op2 α K` at every `δ_p`, `p ∈ ℤ²`. -/
theorem isSpectralMeasure_op2_delta {α : ℝ} {K : Symbol} (hK : SymbolSummable K)
    (hsa : SymbolSelfAdjoint K) {ν : Measure ℝ} (hν : IsDOSMeasure (op α K) ν) (p : ℤ × ℤ) :
    IsSpectralMeasure (op2 α K) (delta p) ν := by
  have := hν.1
  refine ⟨inferInstance, fun f => ?_⟩
  obtain ⟨hc, heq⟩ := inner_delta_cfc_op2 α hK hsa f.continuous
  rw [hν.2 f, heq p, intervalIntegral.intervalIntegral_re (hc.intervalIntegrable _ _)]

end CMS
