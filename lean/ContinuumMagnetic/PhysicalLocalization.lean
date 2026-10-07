/-
# Physical localization of continuum eigenfunctions

This file formalizes the *physical-localization step* in the proof of
Theorem `thm:continuum-types` (paper §"continuum types", the paragraph beginning
"To prove physical localization"), whose input is the weighted bound
`eq:basis-weight` of Proposition `c-prop:spatial-basis`; the same argument is used in
Lemma `lem:high-spatial-localization` for high energies.

We work in an abstract measure space `(X, ν)` with a measurable "unbounded coordinate"
`x₁ : X → ℝ` (in the paper `X = ℝ × 𝕋` and `x₁` is the first coordinate).  Given functions
`η n` (the Bloch basis vectors `η_{n,h}(·,k)`) with
`‖e^{b_h |x₁ - μ n|} η n‖_{L²} ≤ C_h` and coefficients `|u n| ≤ C e^{-m |n - n₀|}`, and
`0 < b < min(b_h, m/μ)`, `x₀ = μ n₀`, we prove:

* `Ψ = ∑ₙ u n • η n` converges (absolutely) in `L²(ν)` (`physLoc_hasSum`);
* `e^{b |x₁ - x₀|} Ψ ∈ L²` with
  `‖e^{b |x₁ - x₀|} Ψ‖ ≤ C C_h ∑ₙ e^{-(m - bμ)|n - n₀|}` (`physLoc_weighted_memLp`,
  `physLoc_weighted_eLpNorm_le`);
* the paper's form `∫ e^{2b |x₁ - x₀|} |Ψ|² < ∞` (`physLoc_integrable_sq`).

The weighted limit is identified with `e^{b|x₁ - x₀|} Ψ` pointwise a.e. using that an
absolutely convergent series in `Lᵖ` also converges a.e. (`MeasureTheory.Lp.hasSum_coeFn_tsum`).
-/
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.SpecificLimits.Basic

open MeasureTheory Real

noncomputable section

namespace CMS

/-! ### Elementary lemmas -/

/-- The weight inequality `e^{b|t - μ n₀|} ≤ e^{bμ|n - n₀|} e^{b_h |t - μ n|}` for
`0 ≤ b ≤ b_h`, `0 < μ`, from `|t - x₀| ≤ |t - μ n| + μ|n - n₀|`. -/
theorem weight_shift_le {μ b b_h : ℝ} (hμ : 0 < μ) (hb : 0 ≤ b) (hbh : b ≤ b_h)
    (t : ℝ) (n n₀ : ℤ) :
    exp (b * |t - μ * n₀|) ≤ exp (b * μ * |(n : ℝ) - n₀|) * exp (b_h * |t - μ * n|) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have h1 : |t - μ * n₀| ≤ |t - μ * n| + μ * |(n : ℝ) - n₀| := by
    calc |t - μ * n₀| = |(t - μ * n) + μ * ((n : ℝ) - n₀)| := by ring_nf
      _ ≤ |t - μ * n| + |μ * ((n : ℝ) - n₀)| := abs_add_le _ _
      _ = |t - μ * n| + μ * |(n : ℝ) - n₀| := by rw [abs_mul, abs_of_pos hμ]
  have h2 : b * |t - μ * n| ≤ b_h * |t - μ * n| :=
    mul_le_mul_of_nonneg_right hbh (abs_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left h1 hb]

/-- `∑_{n ∈ ℤ} e^{-a|n - n₀|} < ∞` for `a > 0`. -/
theorem summable_exp_neg_abs_int {a : ℝ} (ha : 0 < a) (n₀ : ℤ) :
    Summable (fun n : ℤ => exp (-a * |(n : ℝ) - n₀|)) := by
  have hg : Summable (fun k : ℕ => exp (-a) ^ k) :=
    summable_geometric_of_lt_one (exp_pos _).le (Real.exp_lt_one_iff.mpr (by linarith))
  have h0 : Summable (fun k : ℤ => exp (-a * |(k : ℝ)|)) := by
    apply Summable.of_nat_of_neg
    · refine hg.congr fun k => ?_
      simp only [Int.cast_natCast, Nat.abs_cast]
      rw [← Real.exp_nat_mul]; ring_nf
    · refine hg.congr fun k => ?_
      simp only [Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast]
      rw [← Real.exp_nat_mul]; ring_nf
  refine (h0.comp_injective (sub_left_injective (b := n₀))).congr fun n => ?_
  simp

/-! ### The physical-localization step -/

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- The exponential weight `x ↦ e^{c |x₁ x - a|}` as a complex-valued function. -/
def expWeight (x₁ : X → ℝ) (c a : ℝ) (x : X) : ℂ := (exp (c * |x₁ x - a|) : ℝ)

omit [MeasurableSpace X] in
lemma norm_expWeight (x₁ : X → ℝ) (c a : ℝ) (x : X) :
    ‖expWeight x₁ c a x‖ = exp (c * |x₁ x - a|) := by
  rw [expWeight, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (exp_pos _)]

lemma measurable_expWeight {x₁ : X → ℝ} (hx₁ : Measurable x₁) (c a : ℝ) :
    Measurable (expWeight x₁ c a) := by
  unfold expWeight; fun_prop

/-- If `e^{c|x₁ - a|} f ∈ L²` with `c ≥ 0`, then `f ∈ L²` (the weight is `≥ 1`). -/
theorem memLp_of_weighted {x₁ : X → ℝ} (hx₁ : Measurable x₁) {c a : ℝ} (hc : 0 ≤ c)
    {f : X → ℂ} (hf : MemLp (fun x => expWeight x₁ c a x * f x) 2 ν) : MemLp f 2 ν := by
  have hmeas : AEStronglyMeasurable f ν := by
    have : f = fun x => (expWeight x₁ c a x)⁻¹ * (expWeight x₁ c a x * f x) := by
      funext x
      have : expWeight x₁ c a x ≠ 0 := by
        rw [← norm_ne_zero_iff, norm_expWeight]; exact (exp_pos _).ne'
      field_simp
    rw [this]
    exact ((measurable_expWeight hx₁ c a).inv.aestronglyMeasurable).mul hf.aestronglyMeasurable
  refine hf.of_le hmeas (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, norm_expWeight]
  exact le_mul_of_one_le_left (norm_nonneg _) (one_le_exp (by positivity))

section

variable {x₁ : X → ℝ} {μ b_h b m C C_h : ℝ} {η : ℤ → X → ℂ} {u : ℤ → ℂ} {n₀ : ℤ}

/-- Weighted bound for a single basis function:
`‖e^{b|x₁ - x₀|} η n‖ ≤ e^{bμ|n - n₀|} ‖e^{b_h|x₁ - μ n|} η n‖`, and in particular the
recentred weighted function is in `L²`. -/
theorem weighted_basis_memLp (hx₁ : Measurable x₁) (hμ : 0 < μ) (hb : 0 ≤ b) (hbh : b ≤ b_h)
    (hη : ∀ n : ℤ, MemLp (fun x => expWeight x₁ b_h (μ * n) x * η n x) 2 ν) (n : ℤ) :
    MemLp (fun x => expWeight x₁ b (μ * n₀) x * η n x) 2 ν ∧
      eLpNorm (fun x => expWeight x₁ b (μ * n₀) x * η n x) 2 ν ≤
        ENNReal.ofReal (exp (b * μ * |(n : ℝ) - n₀|)) *
          eLpNorm (fun x => expWeight x₁ b_h (μ * n) x * η n x) 2 ν := by
  have hle : ∀ᵐ x ∂ν, ‖expWeight x₁ b (μ * n₀) x * η n x‖ ≤
      exp (b * μ * |(n : ℝ) - n₀|) * ‖expWeight x₁ b_h (μ * n) x * η n x‖ :=
    Filter.Eventually.of_forall fun x => by
      rw [norm_mul, norm_mul, norm_expWeight, norm_expWeight, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (weight_shift_le hμ hb hbh (x₁ x) n n₀) (norm_nonneg _)
  have hη2 := memLp_of_weighted hx₁ (hb.trans hbh) (hη n)
  have hmeas : AEStronglyMeasurable (fun x => expWeight x₁ b (μ * n₀) x * η n x) ν :=
    (measurable_expWeight hx₁ _ _).aestronglyMeasurable.mul hη2.aestronglyMeasurable
  exact ⟨(hη n).of_le_mul hmeas hle, eLpNorm_le_mul_eLpNorm_of_ae_le_mul hmeas hle 2⟩

end

/-- `‖η‖ ≤ ‖e^{c|x₁ - a|} η‖` in `L²` for `c ≥ 0`. -/
theorem eLpNorm_le_of_weighted {x₁ : X → ℝ} {c a : ℝ} (hc : 0 ≤ c) {f : X → ℂ}
    (hf : AEStronglyMeasurable f ν) :
    eLpNorm f 2 ν ≤ eLpNorm (fun x => expWeight x₁ c a x * f x) 2 ν := by
  refine eLpNorm_mono hf fun x => ?_
  rw [norm_mul, norm_expWeight]
  exact le_mul_of_one_le_left (norm_nonneg _) (one_le_exp (by positivity))

section main

variable {x₁ : X → ℝ} {μ b_h b m C C_h : ℝ} {η : ℤ → X → ℂ} {u : ℤ → ℂ} {n₀ : ℤ}

/-- The basis vectors `η n` as elements of `L²(ν)`. -/
def basisLp (hx₁ : Measurable x₁) (hbh : 0 ≤ b_h)
    (hη : ∀ n : ℤ, MemLp (fun x => expWeight x₁ b_h (μ * n) x * η n x) 2 ν) (n : ℤ) :
    Lp ℂ 2 ν :=
  (memLp_of_weighted hx₁ hbh (hη n)).toLp (η n)

/-- The recentred weighted basis vectors `g n = e^{b|x₁ - x₀|} η n`, `x₀ = μ n₀`, in `L²(ν)`. -/
def weightedBasisLp (hx₁ : Measurable x₁) (hμ : 0 < μ) (hb : 0 ≤ b) (hbh : b ≤ b_h)
    (hη : ∀ n : ℤ, MemLp (fun x => expWeight x₁ b_h (μ * n) x * η n x) 2 ν) (n₀ n : ℤ) :
    Lp ℂ 2 ν :=
  (weighted_basis_memLp (n₀ := n₀) hx₁ hμ hb hbh hη n).1.toLp
    (fun x => expWeight x₁ b (μ * n₀) x * η n x)

/-- The continuum eigenfunction `Ψ = ∑ₙ u n η n` as an element of `L²(ν)`. -/
def physLocSeries (hx₁ : Measurable x₁) (hbh : 0 ≤ b_h)
    (hη : ∀ n : ℤ, MemLp (fun x => expWeight x₁ b_h (μ * n) x * η n x) 2 ν) (u : ℤ → ℂ) :
    Lp ℂ 2 ν :=
  ∑' n, u n • basisLp hx₁ hbh hη n

variable (hx₁ : Measurable x₁) (hμ : 0 < μ) (hb : 0 < b) (hbh : b < b_h) (hbm : b < m / μ)
  (hη : ∀ n : ℤ, MemLp (fun x => expWeight x₁ b_h (μ * n) x * η n x) 2 ν)
  (hC_h : 0 ≤ C_h)
  (hηC : ∀ n : ℤ, eLpNorm (fun x => expWeight x₁ b_h (μ * n) x * η n x) 2 ν ≤
    ENNReal.ofReal C_h)
  (hu : ∀ n : ℤ, ‖u n‖ ≤ C * exp (-m * |(n : ℝ) - n₀|))

include hμ hbm in
lemma physLoc_rate_pos : 0 < m - b * μ := by
  have := (lt_div_iff₀ hμ).1 hbm; linarith

include hμ hb hbm in
lemma physLoc_m_pos : 0 < m := by
  have := physLoc_rate_pos hμ hbm; nlinarith

include hC_h hηC in
lemma norm_basisLp_le (n : ℤ) : ‖basisLp hx₁ (hb.le.trans hbh.le) hη n‖ ≤ C_h := by
  rw [basisLp, Lp.norm_toLp]
  exact ENNReal.toReal_le_of_le_ofReal hC_h
    ((eLpNorm_le_of_weighted (hb.le.trans hbh.le)
      (memLp_of_weighted hx₁ (hb.le.trans hbh.le) (hη n)).aestronglyMeasurable).trans (hηC n))

include hC_h hηC in
/-- `‖e^{b|x₁ - x₀|} η n‖ ≤ C_h e^{bμ|n - n₀|}` (paper, proof of `thm:continuum-types`). -/
theorem norm_weightedBasisLp_le (n : ℤ) :
    ‖weightedBasisLp hx₁ hμ hb.le hbh.le hη n₀ n‖ ≤ exp (b * μ * |(n : ℝ) - n₀|) * C_h := by
  rw [weightedBasisLp, Lp.norm_toLp]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  refine (weighted_basis_memLp hx₁ hμ hb.le hbh.le hη n).2.trans ?_
  rw [ENNReal.ofReal_mul (exp_pos _).le]
  gcongr
  exact hηC n

include hμ hb hC_h hηC hu in
/-- Absolute convergence in the weighted space:
`‖u n‖ ‖e^{b|x₁-x₀|} η n‖ ≤ C C_h e^{-(m - bμ)|n - n₀|}`, which is summable. -/
theorem norm_smul_weightedBasisLp_le (n : ℤ) :
    ‖u n • weightedBasisLp hx₁ hμ hb.le hbh.le hη n₀ n‖ ≤
      C * C_h * exp (-(m - b * μ) * |(n : ℝ) - n₀|) := by
  rw [norm_smul]
  have h1 := norm_weightedBasisLp_le hx₁ hμ hb hbh hη hC_h hηC (n₀ := n₀) n
  calc ‖u n‖ * ‖weightedBasisLp hx₁ hμ hb.le hbh.le hη n₀ n‖
      ≤ C * exp (-m * |(n : ℝ) - n₀|) * (exp (b * μ * |(n : ℝ) - n₀|) * C_h) :=
        mul_le_mul (hu n) h1 (norm_nonneg _) ((norm_nonneg _).trans (hu n))
    _ = C * C_h * (exp (-m * |(n : ℝ) - n₀|) * exp (b * μ * |(n : ℝ) - n₀|)) := by ring
    _ = C * C_h * exp (-(m - b * μ) * |(n : ℝ) - n₀|) := by
        rw [← Real.exp_add]; ring_nf

include hμ hb hbm hC_h hηC hu in
lemma summable_norm_smul_weightedBasisLp :
    Summable (fun n => ‖u n • weightedBasisLp hx₁ hμ hb.le hbh.le hη n₀ n‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (norm_smul_weightedBasisLp_le hx₁ hμ hb hbh hη hC_h hηC hu)
    ((summable_exp_neg_abs_int (physLoc_rate_pos hμ hbm) n₀).mul_left _)

include hμ hb hbm hC_h hηC hu in
lemma summable_norm_smul_basisLp :
    Summable (fun n => ‖u n • basisLp hx₁ (hb.le.trans hbh.le) hη n‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
    ((summable_exp_neg_abs_int (physLoc_m_pos hμ hb hbm) n₀).mul_left (C * C_h))
  rw [norm_smul]
  calc ‖u n‖ * ‖basisLp hx₁ (hb.le.trans hbh.le) hη n‖
      ≤ C * exp (-m * |(n : ℝ) - n₀|) * C_h :=
        mul_le_mul (hu n) (norm_basisLp_le hx₁ hb hbh hη hC_h hηC n) (norm_nonneg _)
          ((norm_nonneg _).trans (hu n))
    _ = C * C_h * exp (-m * |(n : ℝ) - n₀|) := by ring

include hμ hbm hC_h hηC hu in
/-- **`L²` convergence.** The series `Ψ = ∑ₙ u n η n` converges absolutely, hence in `L²(ν)`. -/
theorem physLoc_hasSum :
    HasSum (fun n => u n • basisLp hx₁ (hb.le.trans hbh.le) hη n)
      (physLocSeries hx₁ (hb.le.trans hbh.le) hη u) :=
  (Summable.of_norm (summable_norm_smul_basisLp hx₁ hμ hb hbh hbm hη hC_h hηC hu)).hasSum

include hμ hbm hC_h hηC hu in
/-- **Identification of the weighted limit.** Pointwise a.e.,
`e^{b|x₁ - x₀|} Ψ = ∑ₙ u n e^{b|x₁ - x₀|} η n`, the right side being the (absolutely
convergent) `L²` sum of the weighted basis vectors. -/
theorem physLoc_weighted_ae_eq :
    (fun x => expWeight x₁ b (μ * n₀) x * physLocSeries hx₁ (hb.le.trans hbh.le) hη u x)
      =ᵐ[ν] ⇑(∑' n, u n • weightedBasisLp hx₁ hμ hb.le hbh.le hη n₀ n) := by
  have A := Lp.hasSum_coeFn_tsum (f := fun n => u n • weightedBasisLp hx₁ hμ hb.le hbh.le hη n₀ n)
    (tsum_enorm_ne_top_iff_summable_norm.2
      (summable_norm_smul_weightedBasisLp hx₁ hμ hb hbh hbm hη hC_h hηC hu))
  have B := Lp.hasSum_coeFn_tsum (f := fun n => u n • basisLp hx₁ (hb.le.trans hbh.le) hη n)
    (tsum_enorm_ne_top_iff_summable_norm.2
      (summable_norm_smul_basisLp hx₁ hμ hb hbh hbm hη hC_h hηC hu))
  have Cg : ∀ᵐ x ∂ν, ∀ n, (u n • weightedBasisLp hx₁ hμ hb.le hbh.le hη n₀ n) x =
      u n * (expWeight x₁ b (μ * n₀) x * η n x) := ae_all_iff.2 fun n => by
    filter_upwards [Lp.coeFn_smul (u n) (weightedBasisLp hx₁ hμ hb.le hbh.le hη n₀ n),
      MemLp.coeFn_toLp (weighted_basis_memLp (n₀ := n₀) hx₁ hμ hb.le hbh.le hη n).1] with x h1 h2
    rw [h1, Pi.smul_apply, weightedBasisLp, h2, smul_eq_mul]
  have Cη : ∀ᵐ x ∂ν, ∀ n, (u n • basisLp hx₁ (hb.le.trans hbh.le) hη n) x = u n * η n x :=
    ae_all_iff.2 fun n => by
      filter_upwards [Lp.coeFn_smul (u n) (basisLp hx₁ (hb.le.trans hbh.le) hη n),
        MemLp.coeFn_toLp (memLp_of_weighted hx₁ (hb.le.trans hbh.le) (hη n))] with x h1 h2
      rw [h1, Pi.smul_apply, basisLp, h2, smul_eq_mul]
  filter_upwards [A, B, Cg, Cη] with x hA hB hCg hCη
  simp only [hCg] at hA
  simp only [hCη] at hB
  refine (hB.mul_left (expWeight x₁ b (μ * n₀) x)).unique ?_
  convert hA using 1
  funext n; ring

include hμ hbm hC_h hηC hu in
/-- **Physical localization** (proof of `thm:continuum-types`):
`e^{b|x₁ - x₀|} Ψ ∈ L²(ν)` for `0 < b < min(b_h, m/μ)`, `x₀ = μ n₀`. -/
theorem physLoc_weighted_memLp :
    MemLp (fun x => expWeight x₁ b (μ * n₀) x *
      physLocSeries hx₁ (hb.le.trans hbh.le) hη u x) 2 ν :=
  (Lp.memLp _).ae_eq (physLoc_weighted_ae_eq hx₁ hμ hb hbh hbm hη hC_h hηC hu).symm

include hμ hbm hC_h hηC hu in
/-- **Quantitative physical localization**:
`‖e^{b|x₁ - x₀|} Ψ‖ ≤ C C_h ∑ₙ e^{-(m - bμ)|n - n₀|}`. -/
theorem physLoc_weighted_eLpNorm_le :
    eLpNorm (fun x => expWeight x₁ b (μ * n₀) x *
      physLocSeries hx₁ (hb.le.trans hbh.le) hη u x) 2 ν ≤
      ENNReal.ofReal (C * C_h * ∑' n : ℤ, exp (-(m - b * μ) * |(n : ℝ) - n₀|)) := by
  rw [eLpNorm_congr_ae (physLoc_weighted_ae_eq hx₁ hμ hb hbh hbm hη hC_h hηC hu),
    ← ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _), ← Lp.norm_def]
  apply ENNReal.ofReal_le_ofReal
  have hs := summable_norm_smul_weightedBasisLp hx₁ hμ hb hbh hbm hη hC_h hηC hu
  calc ‖∑' n, u n • weightedBasisLp hx₁ hμ hb.le hbh.le hη n₀ n‖
      ≤ ∑' n, ‖u n • weightedBasisLp hx₁ hμ hb.le hbh.le hη n₀ n‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑' n : ℤ, C * C_h * exp (-(m - b * μ) * |(n : ℝ) - n₀|) :=
        hs.tsum_le_tsum (norm_smul_weightedBasisLp_le hx₁ hμ hb hbh hη hC_h hηC hu)
          ((summable_exp_neg_abs_int (physLoc_rate_pos hμ hbm) n₀).mul_left _)
    _ = C * C_h * ∑' n : ℤ, exp (-(m - b * μ) * |(n : ℝ) - n₀|) := tsum_mul_left

include hμ hbm hC_h hηC hu in
/-- **Physical localization, paper form**: `∫ e^{2b|x₁ - x₀|} |Ψ|² dν < ∞`. -/
theorem physLoc_integrable_sq :
    Integrable (fun x => exp (2 * b * |x₁ x - μ * n₀|) *
      ‖physLocSeries hx₁ (hb.le.trans hbh.le) hη u x‖ ^ 2) ν := by
  have h := physLoc_weighted_memLp hx₁ hμ hb hbh hbm hη hC_h hηC hu
  rw [memLp_two_iff_integrable_sq_norm h.aestronglyMeasurable] at h
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [norm_mul, norm_expWeight, mul_pow, ← Real.exp_nat_mul]
  ring_nf

end main

end CMS
