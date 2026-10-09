/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators, I*,
§1.9.1: boundary values of Borel transforms `μ`-almost everywhere.

# Main results

* `DF.not_reBoundaryValueMeasureStatement` — the recorded statement
  `DF.ReBoundaryValueMeasureStatement` (`Re F_μ(E + i0)` exists in `[-∞, ∞]` for `μ`-a.e. `E`)
  is **false**.  Counterexample: `μ = δ₀ + ∑ₙ rₙ δ_{(-1)ⁿ rₙ}` with `rₙ = 2^{-n²}`.  The atom `0`
  has positive mass, and `Re F_μ(iε) = ∑ₙ (-1)ⁿ rₙ² / (rₙ² + ε²)` is close to the partial sum
  `∑_{n ≤ m} (-1)ⁿ ∈ {0, 1}` at `ε = 2^{-(m² + m + 1)}`, so it oscillates between `0` and `1`.
* `DF.borelBoundaryValueMeasureStatement_holds` — the correct `μ`-a.e. statement: for `μ`-a.e.
  `E`, `F_μ(E + i0)` exists either in `ℂ` or as `∞` (i.e. `|F_μ(E + iε)| → ∞`).  This follows
  from Theorem 1.9.4(a)–(d): the singular part lives where `Im F_μ(E + i0) = ∞`, and the
  absolutely continuous part is absolutely continuous with respect to Lebesgue measure.
-/
import DamanikFillman.Ch1.BorelHerglotz

noncomputable section

open MeasureTheory Filter Topology Set Complex
open scoped ENNReal

namespace DF

namespace ReCounter

/-- The ratio `1/2`. -/
def q : ℝ := 1 / 2

lemma q_pos : 0 < q := by norm_num [q]

lemma q_lt_one : q < 1 := by norm_num [q]

lemma qpow_le {a b : ℕ} (h : a ≤ b) : q ^ b ≤ q ^ a :=
  pow_le_pow_of_le_one q_pos.le q_lt_one.le h

/-- The masses `rₙ = 2^{-n²}`. -/
def r (n : ℕ) : ℝ := q ^ (n ^ 2)

lemma r_pos (n : ℕ) : 0 < r n := pow_pos q_pos _

lemma r_le (n : ℕ) : r n ≤ q ^ n := qpow_le (Nat.le_self_pow two_ne_zero n)

lemma summable_r : Summable r :=
  Summable.of_nonneg_of_le (fun n => (r_pos n).le) r_le
    (summable_geometric_of_lt_one q_pos.le q_lt_one)

/-- The atoms `(-1)ⁿ rₙ`. -/
def xpt (n : ℕ) : ℝ := (-1) ^ n * r n

lemma xpt_sq (n : ℕ) : xpt n ^ 2 = r n ^ 2 := by
  unfold xpt
  rw [mul_pow, ← pow_mul, mul_comm n 2, pow_mul, neg_one_sq, one_pow, one_mul]

/-- The atomic part away from `0`. -/
def νc : Measure ℝ := Measure.sum fun n => ENNReal.ofReal (r n) • Measure.dirac (xpt n)

instance : IsFiniteMeasure νc := by
  constructor
  rw [νc, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => (r_pos n).le) summable_r]
  exact ENNReal.ofReal_lt_top

/-- The counterexample `μ = δ₀ + ∑ₙ rₙ δ_{(-1)ⁿ rₙ}`. -/
def μc : Measure ℝ := Measure.dirac 0 + νc

instance : IsFiniteMeasure μc := by unfold μc; infer_instance

/-- The terms of `Re F_μ(iε)`. -/
def t (ε : ℝ) (n : ℕ) : ℝ := (-1) ^ n * (r n ^ 2 / (r n ^ 2 + ε ^ 2))

lemma re_eq {ε : ℝ} (hε : 0 < ε) :
    (borelTransform μc ((0 : ℝ) + ε * I)).re = ∑' n, t ε n := by
  rw [borelTransform_re μc 0 hε.ne']
  set g : ℝ → ℝ := fun x => (x - 0) / ((x - 0) ^ 2 + ε ^ 2) with hg
  have hgm : Measurable g := by fun_prop
  have hgb : ∀ x, ‖g x‖ ≤ 1 / ε := by
    intro x
    rw [Real.norm_eq_abs, hg]
    simp only [sub_zero]
    rw [abs_div, abs_of_pos (by positivity : 0 < x ^ 2 + ε ^ 2),
      div_le_div_iff₀ (by positivity) hε]
    nlinarith [abs_nonneg x, sq_abs x, sq_nonneg (|x| - ε)]
  have hint : ∀ (ν : Measure ℝ) [IsFiniteMeasure ν], Integrable g ν := fun ν _ =>
    Integrable.of_bound hgm.aestronglyMeasurable (1 / ε) (Eventually.of_forall hgb)
  show ∫ x, g x ∂μc = _
  have hsum : ∫ x, g x ∂νc =
      ∑' n, ∫ x, g x ∂(ENNReal.ofReal (r n) • Measure.dirac (xpt n)) :=
    integral_sum_measure (hint νc)
  rw [μc, integral_add_measure (hint _) (hint νc), integral_dirac, hsum]
  have h0 : g 0 = 0 := by simp [hg]
  rw [h0, zero_add]
  refine tsum_congr fun n => ?_
  rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (r_pos n).le, smul_eq_mul]
  simp only [hg, sub_zero]
  rw [xpt_sq]
  unfold xpt t
  ring

/-- The partial sums `∑_{n ≤ m} (-1)ⁿ` as a series. -/
def c (m n : ℕ) : ℝ := if n ≤ m then (-1) ^ n else 0

lemma c_eq_zero {m n : ℕ} (hn : n ∉ Finset.range (m + 1)) : c m n = 0 := by
  rw [c, if_neg]
  intro h
  exact hn (Finset.mem_range.2 (Nat.lt_succ_of_le h))

lemma tsum_c (m : ℕ) : ∑' n, c m n = ∑ n ∈ Finset.range (m + 1), (-1 : ℝ) ^ n := by
  rw [tsum_eq_sum (s := Finset.range (m + 1)) fun n hn => c_eq_zero hn]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [c, if_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hn))]

lemma summable_c (m : ℕ) : Summable (c m) :=
  summable_of_ne_finset_zero (s := Finset.range (m + 1)) fun n hn => c_eq_zero hn

lemma sum_even (j : ℕ) : ∑ n ∈ Finset.range (2 * j + 1), (-1 : ℝ) ^ n = 1 := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih]
    simp only [pow_succ, pow_mul, neg_one_sq, one_pow]
    ring

lemma sum_odd (j : ℕ) : ∑ n ∈ Finset.range (2 * j + 1 + 1), (-1 : ℝ) ^ n = 0 := by
  rw [Finset.sum_range_succ, sum_even]
  simp only [pow_succ, pow_mul, neg_one_sq, one_pow]
  ring

/-- The heights `εₘ = 2^{-(m² + m + 1)}`, between the scales `r_{m+1}` and `r_m`. -/
def eps (m : ℕ) : ℝ := q ^ (m ^ 2 + m + 1)

lemma eps_pos (m : ℕ) : 0 < eps m := pow_pos q_pos _

lemma tendsto_eps : Tendsto eps atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall eps_pos⟩
  have h1 : Tendsto (fun m : ℕ => m ^ 2 + m + 1) atTop atTop :=
    tendsto_atTop_mono (fun m => (le_trans (Nat.le_add_left m (m ^ 2)) (Nat.le_succ _) :
      id m ≤ m ^ 2 + m + 1)) tendsto_id
  exact (tendsto_pow_atTop_nhds_zero_of_lt_one q_pos.le q_lt_one).comp h1

/-- The error terms. -/
def f (m n : ℕ) : ℝ := t (eps m) n - c m n

lemma eps_sq (m : ℕ) : eps m ^ 2 = q ^ ((m ^ 2 + m + 1) * 2) := by
  unfold eps; rw [← pow_mul]

lemma r_sq (n : ℕ) : r n ^ 2 = q ^ (n ^ 2 * 2) := by
  unfold r; rw [← pow_mul]

lemma abs_f_of_le {m n : ℕ} (h : n ≤ m) :
    |f m n| = eps m ^ 2 / (r n ^ 2 + eps m ^ 2) := by
  have hpos : 0 < r n ^ 2 + eps m ^ 2 := by have := r_pos n; positivity
  have hsplit : r n ^ 2 / (r n ^ 2 + eps m ^ 2) = 1 - eps m ^ 2 / (r n ^ 2 + eps m ^ 2) := by
    rw [eq_sub_iff_add_eq, ← add_div, div_self hpos.ne']
  have e : f m n = -((-1) ^ n * (eps m ^ 2 / (r n ^ 2 + eps m ^ 2))) := by
    rw [f, t, c, if_pos h, hsplit]
    ring
  rw [e, abs_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (div_nonneg (sq_nonneg _) hpos.le)]

lemma abs_f_of_lt {m n : ℕ} (h : m < n) :
    |f m n| = r n ^ 2 / (r n ^ 2 + eps m ^ 2) := by
  have hpos : 0 < r n ^ 2 + eps m ^ 2 := by have := r_pos n; positivity
  rw [f, t, c, if_neg (not_le.2 h), sub_zero, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    one_mul, abs_of_nonneg (div_nonneg (sq_nonneg _) hpos.le)]

lemma abs_f_le {m n : ℕ} (hm : 1 ≤ m) : |f m n| ≤ q ^ n := by
  have hr := r_pos n
  have he := eps_pos m
  rcases le_or_gt n m with h | h
  · rw [abs_f_of_le h, div_le_iff₀ (by positivity)]
    have h1 : eps m ^ 2 ≤ q ^ n * r n ^ 2 := by
      rw [eps_sq, r_sq, ← pow_add]
      exact qpow_le (by nlinarith)
    nlinarith [pow_pos q_pos n, sq_nonneg (eps m)]
  · rw [abs_f_of_lt h, div_le_iff₀ (by positivity)]
    have h1 : r n ^ 2 ≤ q ^ n * eps m ^ 2 := by
      rw [eps_sq, r_sq, ← pow_add]
      have h' : m + 1 ≤ n := h
      exact qpow_le (by nlinarith)
    nlinarith [pow_pos q_pos n, sq_nonneg (r n)]

lemma tendsto_f (n : ℕ) : Tendsto (fun m => f m n) atTop (𝓝 0) := by
  have hr := r_pos n
  have h0 : Tendsto eps atTop (𝓝 0) := tendsto_eps.mono_right nhdsWithin_le_nhds
  have h1 : Tendsto (fun m => eps m ^ 2 / r n ^ 2) atTop (𝓝 0) := by
    simpa using (h0.pow 2).div_const (r n ^ 2)
  refine squeeze_zero_norm' ?_ h1
  filter_upwards [eventually_ge_atTop n] with m hm
  rw [Real.norm_eq_abs, abs_f_of_le hm]
  exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith [sq_nonneg (eps m)])

lemma tendsto_tsum_f : Tendsto (fun m => ∑' n, f m n) atTop (𝓝 0) := by
  have := tendsto_tsum_of_dominated_convergence (f := f) (g := fun _ => (0 : ℝ))
    (bound := fun n => q ^ n) (summable_geometric_of_lt_one q_pos.le q_lt_one) tendsto_f
    (eventually_atTop.2 ⟨1, fun m hm n => by rw [Real.norm_eq_abs]; exact abs_f_le hm⟩)
  simpa using this

lemma re_eps {m : ℕ} (hm : 1 ≤ m) :
    (borelTransform μc ((0 : ℝ) + eps m * I)).re =
      ∑' n, f m n + ∑ n ∈ Finset.range (m + 1), (-1 : ℝ) ^ n := by
  rw [re_eq (eps_pos m), ← tsum_c]
  have hs : Summable (f m) := Summable.of_norm_bounded
    (summable_geometric_of_lt_one q_pos.le q_lt_one)
    fun n => by rw [Real.norm_eq_abs]; exact abs_f_le hm
  rw [← hs.tsum_add (summable_c m)]
  refine tsum_congr fun n => ?_
  rw [f]
  ring

end ReCounter

open ReCounter in
/-- The recorded `μ`-a.e. statement for `Re F_μ(E + i0)` is false. -/
theorem not_reBoundaryValueMeasureStatement : ¬ ReBoundaryValueMeasureStatement := by
  intro h
  have hae := h μc inferInstance
  have hle : Measure.dirac (0 : ℝ) ≤ μc := by
    rw [μc]; exact Measure.le_add_right le_rfl
  have hd := ae_mono hle hae
  rw [ae_dirac_eq] at hd
  have P0 := Filter.eventually_pure.1 hd
  set S : ℝ → ℝ := fun ε => (borelTransform μc ((0 : ℝ) + ε * I)).re with hS
  have h1 : Tendsto (fun j : ℕ => S (eps (2 * (j + 1)))) atTop (𝓝 1) := by
    have hj : Tendsto (fun j : ℕ => 2 * (j + 1)) atTop atTop :=
      tendsto_atTop_mono (fun j => show j ≤ 2 * (j + 1) by omega) tendsto_id
    have := (tendsto_tsum_f.comp hj).add_const 1
    rw [zero_add] at this
    refine this.congr fun j => ?_
    simp only [Function.comp_apply, hS]
    rw [re_eps (by omega), sum_even]
  have h2 : Tendsto (fun j : ℕ => S (eps (2 * j + 1))) atTop (𝓝 0) := by
    have hj : Tendsto (fun j : ℕ => 2 * j + 1) atTop atTop :=
      tendsto_atTop_mono (fun j => show j ≤ 2 * j + 1 by omega) tendsto_id
    have := (tendsto_tsum_f.comp hj).add_const 0
    rw [zero_add] at this
    refine this.congr fun j => ?_
    simp only [Function.comp_apply, hS]
    rw [re_eps (by omega), sum_odd]
  have he1 : Tendsto (fun j : ℕ => eps (2 * (j + 1))) atTop (𝓝[>] 0) :=
    tendsto_eps.comp (tendsto_atTop_mono (fun j => show j ≤ 2 * (j + 1) by omega) tendsto_id)
  have he2 : Tendsto (fun j : ℕ => eps (2 * j + 1)) atTop (𝓝[>] 0) :=
    tendsto_eps.comp (tendsto_atTop_mono (fun j => show j ≤ 2 * j + 1 by omega) tendsto_id)
  rcases P0 with ⟨y, hy⟩ | hy | hy
  · have a1 := tendsto_nhds_unique (hy.comp he1) h1
    have a2 := tendsto_nhds_unique (hy.comp he2) h2
    rw [a1] at a2
    exact one_ne_zero a2
  · exact not_tendsto_atTop_of_tendsto_nhds h1 (hy.comp he1)
  · exact not_tendsto_atBot_of_tendsto_nhds h1 (hy.comp he1)

/-- Theorem 1.9.4, `μ`-a.e. boundary values (corrected form): for `μ`-a.e. `E`, the boundary
value `F_μ(E + i0)` exists in `ℂ ∪ {∞}`. -/
def BorelBoundaryValueMeasureStatement : Prop :=
  ∀ μ : Measure ℝ, IsFiniteMeasure μ →
    ∀ᵐ (E : ℝ) ∂μ, (∃ w : ℂ, Tendsto (fun ε : ℝ => borelTransform μ (E + ε * I)) (𝓝[>] 0) (𝓝 w)) ∨
      Tendsto (fun ε : ℝ => ‖borelTransform μ (E + ε * I)‖) (𝓝[>] 0) atTop

theorem borelBoundaryValueMeasureStatement_holds : BorelBoundaryValueMeasureStatement := by
  intro μ hμ
  have hdec := Measure.haveLebesgueDecomposition_add μ volume
  suffices h : ∀ᵐ (E : ℝ) ∂(μ.singularPart volume + volume.withDensity (μ.rnDeriv volume)),
      (∃ w : ℂ, Tendsto (fun ε : ℝ => borelTransform μ (E + ε * I)) (𝓝[>] 0) (𝓝 w)) ∨
      Tendsto (fun ε : ℝ => ‖borelTransform μ (E + ε * I)‖) (𝓝[>] 0) atTop by
    rwa [← hdec] at h
  rw [ae_add_measure_iff]
  constructor
  · filter_upwards [measure_eq_zero_iff_ae_notMem.1 (singularPart_not_tendsto_atTop μ)] with E hE
    right
    have hE' : Tendsto (fun ε : ℝ => (borelTransform μ (E + ε * I)).im) (𝓝[>] 0) atTop :=
      not_not.1 hE
    exact tendsto_atTop_mono (fun ε => (le_abs_self _).trans (abs_im_le_norm _)) hE'
  · refine (withDensity_absolutelyContinuous _ _).ae_le ?_
    filter_upwards [reBoundaryValueStatement_holds μ hμ, ae_tendsto_im_volume μ] with E hre him
    obtain ⟨y, hy⟩ := hre
    left
    refine ⟨y + (Real.pi * (μ.rnDeriv volume E).toReal : ℝ) * I, ?_⟩
    have := ((continuous_ofReal.tendsto _).comp hy).add
      (((continuous_ofReal.tendsto _).comp him).mul_const I)
    refine this.congr fun ε => ?_
    simp only [Function.comp_apply]
    exact re_add_im _

end DF
