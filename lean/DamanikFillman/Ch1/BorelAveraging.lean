/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators, I*,
§1.9.3 (pp. 90–91): the spectral averaging formula (Simon–Wolff).

# Setting

`μ` is a nonzero finite measure on `ℝ` with Borel transform `F = F_μ`, and `ν : ℝ → Measure ℝ` is a
family of finite measures with `F_{ν_λ} = F / (1 + λ F)` on `ℂ₊` for every `λ ∈ ℝ` (this is the
situation of (1.9.32)–(1.9.33), with `ν_λ = μ_λ` the spectral measure of the rank-one perturbation
`A_λ = A + λ⟨φ, ·⟩φ`; see `DF.rankOne_borel`).

# Main results

* `DF.measurable_rankOne_family` — `λ ↦ ν_λ` is measurable (so it is a kernel);
* `DF.bind_rankOne_eq_volume` — formula (1.9.36): `∫ ν_λ dλ = Lebesgue measure`;
* `DF.lintegral_rankOne_average` — (1.9.36) tested against nonnegative measurable functions;
* `DF.spectral_averaging` — Theorem 1.9.12, (1.9.37): for `f ∈ L¹(ℝ, dE)`, `f ∈ L¹(ν_λ)` for a.e.
  `λ`, `λ ↦ ∫ f dν_λ` is integrable, and `∫ (∫ f dν_λ) dλ = ∫ f dE`.

# Proof

Different from the book's contour-integral / Stone–Weierstrass argument: we first show that
`λ ↦ ν_λ(B)` is measurable (via Poisson averages of half-lines and a Dynkin argument), so that
`M = ∫ ν_λ dλ` is a measure.  An explicit integration in `λ` shows that every Poisson integral of
`M` equals `1`, i.e. equals the Poisson integral of Lebesgue measure.  By (1.9.20) the lower
derivative of `M` is then everywhere `≤ 1`, so `M` has no singular part and density `≤ 1`; since its
Poisson integral is `1`, the density is `1` a.e., i.e. `M = Leb`.
-/
import DamanikFillman.Ch1.BorelDerivative

noncomputable section

open MeasureTheory Filter Topology Set Metric Complex
open scoped ENNReal

namespace DF

/-! ## Elementary facts -/

lemma poissonKernel_neg (ε x : ℝ) : poissonKernel ε (-x) = poissonKernel ε x := by
  simp [poissonKernel]

lemma poissonKernel_sub_comm (ε x y : ℝ) : poissonKernel ε (x - y) = poissonKernel ε (y - x) := by
  rw [← poissonKernel_neg, neg_sub]

lemma measurable_poisson_uncurry (ε : ℝ) :
    Measurable fun p : ℝ × ℝ => ENNReal.ofReal (poissonKernel ε (p.1 - p.2)) :=
  ((measurable_poissonKernel ε).comp (measurable_fst.sub measurable_snd)).ennreal_ofReal

lemma alg_identity (u y t : ℝ) (hy : 0 < y) :
    y / ((1 + t * u) * (1 + t * u) + t * y * (t * y)) =
      ((u ^ 2 + y ^ 2) / y) * (1 + ((u ^ 2 + y ^ 2) / y * t + u / y) ^ 2)⁻¹ := by
  have hd : 0 < (1 + t * u) * (1 + t * u) + t * y * (t * y) := by
    nlinarith [sq_nonneg (1 + t * u), sq_nonneg (t * y), sq_nonneg ((u ^ 2 + y ^ 2) * t + u)]
  have hy' : y ≠ 0 := hy.ne'
  have hA : 0 < u ^ 2 + y ^ 2 := by positivity
  have key : 1 + ((u ^ 2 + y ^ 2) / y * t + u / y) ^ 2 =
      (u ^ 2 + y ^ 2) * ((1 + t * u) * (1 + t * u) + t * y * (t * y)) / y ^ 2 := by
    field_simp; ring
  rw [key, inv_div]
  field_simp

/-- `∫ (Im (w / (1 + λ w)) / π) dλ = 1` for `Im w > 0`. -/
lemma lintegral_im_div_one_add_mul {w : ℂ} (hw : 0 < w.im) :
    ∫⁻ t : ℝ, ENNReal.ofReal ((w / (1 + t * w)).im / Real.pi) = 1 := by
  have hA : 0 < w.re ^ 2 + w.im ^ 2 := by positivity
  have ha : (w.re ^ 2 + w.im ^ 2) / w.im ≠ 0 := by positivity
  have hpt : ∀ t : ℝ, (w / (1 + t * w)).im / Real.pi =
      ((w.re ^ 2 + w.im ^ 2) / w.im / Real.pi) *
        (1 + ((w.re ^ 2 + w.im ^ 2) / w.im * t + w.re / w.im) ^ 2)⁻¹ := by
    intro t
    rw [im_div_one_add_mul, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.add_im, Complex.one_im, Complex.mul_im,
      zero_add, add_zero]
    rw [alg_identity w.re w.im t hw]
    ring
  have hint : Integrable fun t : ℝ =>
      (1 + ((w.re ^ 2 + w.im ^ 2) / w.im * t + w.re / w.im) ^ 2)⁻¹ :=
    ((integrable_inv_one_add_sq.comp_add_right (w.re / w.im)).comp_mul_left' ha)
  have hval : ∫ t : ℝ, (1 + ((w.re ^ 2 + w.im ^ 2) / w.im * t + w.re / w.im) ^ 2)⁻¹ =
      |((w.re ^ 2 + w.im ^ 2) / w.im)⁻¹| * Real.pi := by
    rw [Measure.integral_comp_mul_left (fun s : ℝ => (1 + (s + w.re / w.im) ^ 2)⁻¹),
      integral_add_right_eq_self (fun s : ℝ => (1 + s ^ 2)⁻¹) (w.re / w.im),
      integral_univ_inv_one_add_sq, smul_eq_mul]
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)
    (Eventually.of_forall fun t => by positivity), integral_const_mul, hval,
    abs_of_pos (inv_pos.2 (by positivity : 0 < (w.re ^ 2 + w.im ^ 2) / w.im))]
  rw [← ENNReal.ofReal_one]; congr 1
  field_simp

section Family

variable {μ : Measure ℝ} [IsFiniteMeasure μ] {ν : ℝ → Measure ℝ} [hfin : ∀ t, IsFiniteMeasure (ν t)]

lemma continuous_borelTransform_line (μ : Measure ℝ) [IsFiniteMeasure μ] {ε : ℝ} (hε : 0 < ε) :
    Continuous fun E : ℝ => borelTransform μ (E + ε * I) :=
  (differentiableOn_borelTransform μ).continuousOn.comp_continuous (by fun_prop)
    fun E => by simpa using hε

lemma one_add_mul_ne_zero (hμ : μ ≠ 0) {z : ℂ} (hz : 0 < z.im) (t : ℝ) :
    1 + t * borelTransform μ z ≠ 0 := by
  intro h0
  have hpos := borelTransform_im_pos μ hμ hz
  rcases eq_or_ne t 0 with ht | ht
  · rw [ht] at h0; simp at h0
  · have := congrArg Complex.im h0
    simp only [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, add_zero, zero_add, Complex.zero_im] at this
    rcases mul_eq_zero.1 this with h | h
    · exact ht h
    · linarith

variable (hμ : μ ≠ 0)
  (hν : ∀ (t : ℝ) (z : ℂ), 0 < z.im →
    borelTransform (ν t) z = borelTransform μ z / (1 + t * borelTransform μ z))
include hμ hν

lemma poissonInt_family (t E : ℝ) {ε : ℝ} (hε : 0 < ε) :
    poissonInt (ν t) E ε = ENNReal.ofReal ((borelTransform μ (E + ε * I) /
      (1 + t * borelTransform μ (E + ε * I))).im / Real.pi) := by
  rw [poissonInt_eq (ν t) E hε, hν t _ (by simpa using hε)]

lemma measurable_poissonInt_family_uncurry {ε : ℝ} (hε : 0 < ε) :
    Measurable fun p : ℝ × ℝ => poissonInt (ν p.1) p.2 ε := by
  have h1 : Continuous fun p : ℝ × ℝ => borelTransform μ (p.2 + ε * I) :=
    (continuous_borelTransform_line μ hε).comp continuous_snd
  have h2 : Continuous fun p : ℝ × ℝ => borelTransform μ (p.2 + ε * I) /
      (1 + p.1 * borelTransform μ (p.2 + ε * I)) :=
    h1.div (continuous_const.add ((Complex.continuous_ofReal.comp continuous_fst).mul h1))
      fun p => one_add_mul_ne_zero hμ (by simpa using hε) p.1
  have hc : Continuous fun p : ℝ × ℝ => ENNReal.ofReal ((borelTransform μ (p.2 + ε * I) /
      (1 + p.1 * borelTransform μ (p.2 + ε * I))).im / Real.pi) :=
    ENNReal.continuous_ofReal.comp ((Complex.continuous_im.comp h2).div_const _)
  have : (fun p : ℝ × ℝ => poissonInt (ν p.1) p.2 ε) = fun p => ENNReal.ofReal
      ((borelTransform μ (p.2 + ε * I) / (1 + p.1 * borelTransform μ (p.2 + ε * I))).im /
        Real.pi) := funext fun p => poissonInt_family hμ hν p.1 p.2 hε
  rw [this]; exact hc.measurable

/-! ## Poisson averages of half-lines -/

/-- `g_ε(x) = ∫_{E ≤ a} P_ε(x - E) dE`. -/
def halfLineAvg (a ε x : ℝ) : ℝ≥0∞ := ∫⁻ E in Iic a, ENNReal.ofReal (poissonKernel ε (x - E))

omit [IsFiniteMeasure μ] hfin hμ hν in
lemma lintegral_poisson_swap {ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    ∫⁻ E, ENNReal.ofReal (poissonKernel ε (x - E)) = 1 := by
  simp_rw [poissonKernel_sub_comm ε x]
  exact lintegral_poissonKernel hε x

omit [IsFiniteMeasure μ] hfin hμ hν in
lemma halfLineAvg_le_one {ε : ℝ} (hε : 0 < ε) (a x : ℝ) : halfLineAvg a ε x ≤ 1 := by
  rw [← lintegral_poisson_swap hε x]; exact setLIntegral_le_lintegral _ _

omit [IsFiniteMeasure μ] hfin hμ hν in
lemma tendsto_ball_swap {r : ℝ} (hr : 0 < r) (x : ℝ) :
    Tendsto (fun ε => ∫⁻ E in ball x r, ENNReal.ofReal (poissonKernel ε (x - E))) (𝓝[>] 0)
      (𝓝 1) := by
  simp_rw [poissonKernel_sub_comm _ x]
  exact tendsto_lintegral_poissonKernel_ball hr x

omit [IsFiniteMeasure μ] hfin hμ hν in
lemma halfLineAvg_self {ε : ℝ} (hε : 0 < ε) (a : ℝ) : halfLineAvg a ε a = 2⁻¹ := by
  have hrefl : ∫⁻ E in Ici a, ENNReal.ofReal (poissonKernel ε (a - E)) = halfLineAvg a ε a := by
    have hmp := Measure.measurePreserving_sub_left (volume : Measure ℝ) (2 * a)
    have h := hmp.setLIntegral_comp_preimage (s := Iic a) measurableSet_Iic
      (f := fun E => ENNReal.ofReal (poissonKernel ε (a - E)))
      ((measurable_poissonKernel ε).comp (measurable_const.sub measurable_id)).ennreal_ofReal
    have hpre : (fun h : ℝ => 2 * a - h) ⁻¹' Iic a = Ici a := by
      ext x; simp only [mem_preimage, mem_Iic, mem_Ici]; constructor <;> intro h <;> linarith
    rw [hpre] at h
    rw [halfLineAvg, ← h]
    apply setLIntegral_congr_fun measurableSet_Ici
    intro x _
    dsimp only
    rw [show a - (2 * a - x) = -(a - x) by ring, poissonKernel_neg]
  have hsum : halfLineAvg a ε a + ∫⁻ E in Ioi a, ENNReal.ofReal (poissonKernel ε (a - E)) = 1 := by
    rw [← lintegral_poisson_swap hε a, halfLineAvg, ← compl_Iic,
      lintegral_add_compl _ measurableSet_Iic]
  rw [Measure.restrict_congr_set Ioi_ae_eq_Ici, hrefl] at hsum
  have hne : halfLineAvg a ε a ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top
    (halfLineAvg_le_one hε a a)
  have h2 : 2 * halfLineAvg a ε a = 1 := by rw [two_mul]; exact hsum
  rw [← one_div]
  exact (ENNReal.eq_div_iff (by norm_num) (by norm_num)).2 h2

omit [IsFiniteMeasure μ] hfin hμ hν in
/-- Pointwise limit of the half-line Poisson averages. -/
lemma tendsto_halfLineAvg (a x : ℝ) :
    Tendsto (fun ε => halfLineAvg a ε x) (𝓝[>] 0)
      (𝓝 ((Iio a).indicator 1 x + ({a} : Set ℝ).indicator (fun _ => 2⁻¹) x)) := by
  rcases lt_trichotomy x a with h | h | h
  · simp only [indicator_of_mem (mem_Iio.2 h), Pi.one_apply,
      indicator_of_notMem (show x ∉ ({a} : Set ℝ) by simp [h.ne]), add_zero]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' (tendsto_ball_swap (by linarith : 0 < a - x) x)
      tendsto_const_nhds ?_ ?_
    · filter_upwards with ε
      apply lintegral_mono_set
      intro E hE; rw [mem_ball, Real.dist_eq] at hE
      simp only [mem_Iic]; linarith [le_abs_self (E - x)]
    · filter_upwards [self_mem_nhdsWithin] with ε hε using halfLineAvg_le_one hε a x
  · subst h
    simp only [indicator_of_notMem (show x ∉ Iio x by simp), indicator_of_mem (mem_singleton x),
      zero_add]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε using (halfLineAvg_self hε x).symm
  · simp only [indicator_of_notMem (show x ∉ Iio a by simp [h.le]),
      indicator_of_notMem (show x ∉ ({a} : Set ℝ) by simp [h.ne']), add_zero]
    have hr : 0 < x - a := by linarith
    have hcompl : ∀ ε, 0 < ε → ∫⁻ E in (ball x (x - a))ᶜ,
        ENNReal.ofReal (poissonKernel ε (x - E)) =
          1 - ∫⁻ E in ball x (x - a), ENNReal.ofReal (poissonKernel ε (x - E)) := by
      intro ε hε
      have := lintegral_add_compl (μ := volume)
        (fun E => ENNReal.ofReal (poissonKernel ε (x - E)))
        (measurableSet_ball (x := x) (ε := x - a))
      rw [lintegral_poisson_swap hε x] at this
      have hle : ∫⁻ E in ball x (x - a), ENNReal.ofReal (poissonKernel ε (x - E)) ≤ 1 := by
        rw [← lintegral_poisson_swap hε x]; exact setLIntegral_le_lintegral _ _
      rw [← this, ENNReal.add_sub_cancel_left (ne_top_of_le_ne_top ENNReal.one_ne_top hle)]
    have hlim : Tendsto (fun ε => 1 - ∫⁻ E in ball x (x - a),
        ENNReal.ofReal (poissonKernel ε (x - E))) (𝓝[>] 0) (𝓝 0) := by
      have := ENNReal.Tendsto.sub tendsto_const_nhds (tendsto_ball_swap hr x)
        (Or.inl ENNReal.one_ne_top)
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    rw [← hcompl ε hε]
    apply lintegral_mono_set
    intro E hE
    simp only [mem_Iic] at hE
    simp only [mem_compl_iff, mem_ball, Real.dist_eq, not_lt]
    rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith

/-! ## Measurability of `λ ↦ ν_λ(B)` -/

lemma measurable_lintegral_halfLineAvg {ε : ℝ} (hε : 0 < ε) (a : ℝ) :
    Measurable fun t => ∫⁻ x, halfLineAvg a ε x ∂(ν t) := by
  have hswap : ∀ t, ∫⁻ x, halfLineAvg a ε x ∂(ν t) =
      ∫⁻ E in Iic a, poissonInt (ν t) E ε := by
    intro t
    unfold halfLineAvg poissonInt
    exact lintegral_lintegral_swap
      ((measurable_poisson_uncurry ε).aemeasurable)
  simp_rw [hswap]
  exact (measurable_poissonInt_family_uncurry hμ hν hε).lintegral_prod_right'

lemma measurable_Iio_add_half (a : ℝ) :
    Measurable fun t => ν t (Iio a) + 2⁻¹ * ν t {a} := by
  set εs : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hεs : ∀ n, 0 < εs n := fun n => by positivity
  have hεlim : Tendsto εs atTop (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      tendsto_one_div_add_atTop_nhds_zero_nat (Eventually.of_forall hεs)
  refine measurable_of_tendsto_metrizable
    (fun n => measurable_lintegral_halfLineAvg hμ hν (hεs n) a) (tendsto_pi_nhds.2 fun t => ?_)
  have hgm : ∀ ε, Measurable fun x => halfLineAvg a ε x := fun ε =>
    (measurable_poisson_uncurry ε).lintegral_prod_right'
  have hlim := tendsto_lintegral_of_dominated_convergence (μ := ν t) (fun _ => 1)
    (fun n => hgm (εs n)) (fun n => Eventually.of_forall fun x => halfLineAvg_le_one (hεs n) a x)
    (by simp) (Eventually.of_forall fun x => (tendsto_halfLineAvg a x).comp hεlim)
  convert hlim using 1
  rw [lintegral_add_left (measurable_one.indicator measurableSet_Iio),
    lintegral_indicator measurableSet_Iio, lintegral_indicator (measurableSet_singleton a)]
  simp [Pi.one_apply, mul_comm]

lemma measurable_Iio (a : ℝ) : Measurable fun t => ν t (Iio a) := by
  set as : ℕ → ℝ := fun n => a - 1 / ((n : ℝ) + 1)
  refine measurable_of_tendsto_metrizable (fun n => measurable_Iio_add_half hμ hν (as n))
    (tendsto_pi_nhds.2 fun t => ?_)
  have hmono : Monotone fun n => Iio (as n) := by
    intro m n hmn
    apply Iio_subset_Iio
    simp only [as]
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((m : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  have hU : ⋃ n, Iio (as n) = Iio a := by
    ext x; simp only [mem_iUnion, mem_Iio, as]
    constructor
    · rintro ⟨n, hn⟩; have : 0 < 1 / ((n : ℝ) + 1) := by positivity
      linarith
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (by linarith : 0 < a - x)
      exact ⟨n, by linarith⟩
  have h1 : Tendsto (fun n => ν t (Iio (as n))) atTop (𝓝 (ν t (Iio a))) := by
    rw [← hU]; exact tendsto_measure_iUnion_atTop hmono
  have hinj : Function.Injective as := by
    intro m n h
    simp only [as, sub_right_inj] at h
    have : (m : ℝ) + 1 = n + 1 := by
      have hm : (0 : ℝ) < m + 1 := by positivity
      have hn : (0 : ℝ) < n + 1 := by positivity
      field_simp at h; linarith
    exact_mod_cast (by linarith : (m : ℝ) = n)
  have h2 : Tendsto (fun n => ν t {as n}) atTop (𝓝 0) := by
    apply ENNReal.tendsto_atTop_zero_of_tsum_ne_top
    rw [← measure_iUnion (fun m n hmn => disjoint_singleton.2 (hinj.ne hmn))
      (fun n => measurableSet_singleton _)]
    exact measure_ne_top _ _
  have h3 := h1.add (ENNReal.Tendsto.const_mul (a := 2⁻¹) h2 (Or.inr (by norm_num)))
  simpa using h3

/-- `λ ↦ ν_λ` is measurable. -/
theorem measurable_rankOne_family : Measurable ν := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have huniv : Measurable fun t => ν t univ := by
    have hmono : Monotone fun n : ℕ => Iio (n : ℝ) := fun m n h =>
      Iio_subset_Iio (by exact_mod_cast h)
    have hU : ⋃ n : ℕ, Iio (n : ℝ) = univ := by
      ext x; simp only [mem_iUnion, mem_Iio, mem_univ, iff_true]; exact exists_nat_gt x
    have : (fun t => ν t univ) = fun t => ⨆ n : ℕ, ν t (Iio (n : ℝ)) := by
      ext t; rw [← hU, hmono.measure_iUnion]
    rw [this]
    exact Measurable.iSup fun n => measurable_Iio hμ hν _
  refine MeasurableSpace.induction_on_inter (C := fun s _ => Measurable fun t => ν t s)
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Iio ℝ)) isPiSystem_Iio
    (by simp) ?_ ?_ ?_ s hs
  · rintro _ ⟨a, rfl⟩; exact measurable_Iio hμ hν a
  · intro t htm ht
    have : (fun x => ν x tᶜ) = fun x => ν x univ - ν x t := by
      ext x; rw [measure_compl htm (measure_ne_top _ _)]
    rw [this]; exact huniv.sub ht
  · intro f hdisj hfm hf
    have : (fun x => ν x (⋃ i, f i)) = fun x => ∑' i, ν x (f i) := by
      ext x; exact measure_iUnion hdisj hfm
    rw [this]; exact Measurable.ennreal_tsum hf

/-! ## The averaged measure is Lebesgue measure -/

omit [IsFiniteMeasure μ] hfin hμ hν in
/-- A measure whose Poisson integrals are all equal to `1` is Lebesgue measure. -/
theorem eq_volume_of_poissonInt_eq_one {M : Measure ℝ}
    (h : ∀ E ε : ℝ, 0 < ε → poissonInt M E ε = 1) : M = volume := by
  -- local finiteness
  have hloc : IsLocallyFiniteMeasure M := by
    refine ⟨fun x => ⟨ball x 1, ball_mem_nhds x one_pos, ?_⟩⟩
    have hle : ENNReal.ofReal (1 / (2 * Real.pi)) * M (ball x 1) ≤ 1 := by
      have hPx : Measurable fun y => ENNReal.ofReal (poissonKernel 1 (y - x)) :=
        ((measurable_poissonKernel 1).comp (measurable_id.sub_const x)).ennreal_ofReal
      rw [← h x 1 one_pos, ← setLIntegral_const]
      refine (setLIntegral_mono hPx fun y hy => ?_).trans (setLIntegral_le_lintegral _ _)
      · apply ENNReal.ofReal_le_ofReal
        rw [mem_ball, Real.dist_eq] at hy
        have : (y - x) ^ 2 < 1 := by
          have := abs_lt.1 hy; nlinarith
        simp only [poissonKernel]
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [Real.pi_pos]
    have hpos : ENNReal.ofReal (1 / (2 * Real.pi)) ≠ 0 := by
      rw [ENNReal.ofReal_ne_zero_iff]; positivity
    by_contra hinf
    rw [not_lt, top_le_iff] at hinf
    rw [hinf, ENNReal.mul_top hpos] at hle
    exact absurd hle (by simp)
  -- the lower derivative is at most `1` everywhere
  have hlow : ∀ E, lowerDeriv M E ≤ 1 := by
    intro E
    refine (lowerDeriv_le_liminf_poisson M E).trans (le_of_eq ?_)
    have : Tendsto (poissonInt M E) (𝓝[>] 0) (𝓝 1) :=
      tendsto_const_nhds.congr' (by filter_upwards [self_mem_nhdsWithin] with ε hε
        using (h E ε hε).symm)
    exact this.liminf_eq
  -- no singular part
  have hsing : M.singularPart volume = 0 := by
    have h1 := singularPart_compl_derivInfSet M
    have h2 : (derivInfSet M)ᶜ = univ := by
      rw [compl_eq_univ_sdiff]
      ext E
      simp only [Set.mem_sdiff, mem_univ, true_and, iff_true]
      intro hE
      have := (hE : HasMeasDeriv M E ∞).lowerDeriv_eq
      have := hlow E
      rw [‹lowerDeriv M E = ∞›] at this
      exact absurd this (by simp)
    rw [h2] at h1
    exact Measure.measure_univ_eq_zero.1 h1
  set D := M.rnDeriv volume
  have hM : M = volume.withDensity D := by
    conv_lhs => rw [Measure.haveLebesgueDecomposition_add M volume, hsing, zero_add]
  have hD1 : ∀ᵐ x ∂volume, D x ≤ 1 := by
    filter_upwards [ae_hasMeasDeriv_rnDeriv M] with x hx
    calc D x = lowerDeriv M x := hx.1.lowerDeriv_eq.symm
      _ ≤ 1 := hlow x
  have hDm : Measurable D := Measure.measurable_rnDeriv _ _
  set P : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (poissonKernel 1 (x - 0))
  have hPm : Measurable P := ((measurable_poissonKernel 1).comp
    (measurable_id.sub_const 0)).ennreal_ofReal
  have hPD : ∫⁻ x, P x * D x = 1 := by
    have := h 0 1 one_pos
    rw [poissonInt, hM, lintegral_withDensity_eq_lintegral_mul _ hDm hPm] at this
    rw [← this]; congr 1; ext x; simp only [Pi.mul_apply]; ring
  have hP1 : ∫⁻ x, P x = 1 := lintegral_poissonKernel one_pos 0
  have hsplit : ∫⁻ x, P x = (∫⁻ x, P x * D x) + ∫⁻ x, P x * (1 - D x) := by
    calc ∫⁻ x, P x = ∫⁻ x, (P x * D x + P x * (1 - D x)) := by
          apply lintegral_congr_ae
          filter_upwards [hD1] with x hx
          rw [← mul_add, add_tsub_cancel_of_le hx, mul_one]
      _ = (∫⁻ x, P x * D x) + ∫⁻ x, P x * (1 - D x) := by
          have hPDm : Measurable fun x => P x * D x := hPm.mul hDm
          exact lintegral_add_left (μ := volume) hPDm (fun x => P x * (1 - D x))
  rw [hP1, hPD] at hsplit
  have hzero : ∫⁻ x, P x * (1 - D x) = 0 := by
    have h' : (1 : ℝ≥0∞) + ∫⁻ x, P x * (1 - D x) = 1 + 0 := by rw [add_zero]; exact hsplit.symm
    exact (ENNReal.add_right_inj ENNReal.one_ne_top).1 h'
  have hm2 : Measurable fun x => P x * (1 - D x) := hPm.mul (measurable_const.sub hDm)
  rw [lintegral_eq_zero_iff hm2] at hzero
  have hD : D =ᵐ[volume] 1 := by
    filter_upwards [hzero, hD1] with x hx hx1
    simp only [Pi.mul_apply, Pi.zero_apply, mul_eq_zero] at hx
    rcases hx with hx | hx
    · exfalso
      have := poissonKernel_pos one_pos (x - 0)
      simp only [P, ENNReal.ofReal_eq_zero] at hx
      linarith
    · exact le_antisymm hx1 (tsub_eq_zero_iff_le.1 hx)
  rw [hM, withDensity_congr_ae hD, withDensity_one]

/-- Formula (1.9.36): `∫ ν_λ dλ` is Lebesgue measure. -/
theorem bind_rankOne_eq_volume : (volume : Measure ℝ).bind ν = volume := by
  have hmeas := measurable_rankOne_family hμ hν
  apply eq_volume_of_poissonInt_eq_one
  intro E ε hε
  have hPm : Measurable fun x => ENNReal.ofReal (poissonKernel ε (x - E)) :=
    ((measurable_poissonKernel ε).comp (measurable_id.sub_const E)).ennreal_ofReal
  rw [poissonInt, Measure.lintegral_bind hmeas.aemeasurable hPm.aemeasurable]
  change ∫⁻ t, poissonInt (ν t) E ε = 1
  simp_rw [poissonInt_family hμ hν _ E hε]
  exact lintegral_im_div_one_add_mul (borelTransform_im_pos μ hμ (by simpa using hε))

/-- (1.9.36) tested against nonnegative measurable functions:
`∫ (∫ g dν_λ) dλ = ∫ g dE`. -/
theorem lintegral_rankOne_average {g : ℝ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ t, ∫⁻ x, g x ∂(ν t) = ∫⁻ x, g x := by
  rw [← Measure.lintegral_bind (measurable_rankOne_family hμ hν).aemeasurable hg.aemeasurable,
    bind_rankOne_eq_volume hμ hν]

/-- Theorem 1.9.12 (spectral averaging), formula (1.9.37): for `f ∈ L¹(ℝ, dE)`, `f ∈ L¹(ν_λ)` for
Lebesgue-a.e. `λ`, the function `λ ↦ ∫ f dν_λ` is integrable, and
`∫ (∫ f dν_λ) dλ = ∫ f dE`. -/
theorem spectral_averaging {f : ℝ → ℝ} (hf : Integrable f) :
    (∀ᵐ t ∂volume, Integrable f (ν t)) ∧ Integrable (fun t => ∫ x, f x ∂(ν t)) ∧
      ∫ t, ∫ x, f x ∂(ν t) = ∫ x, f x := by
  have hmeas := measurable_rankOne_family hμ hν
  -- a Borel representative
  set f' := hf.1.mk f
  have hf'm : Measurable f' := hf.1.stronglyMeasurable_mk.measurable
  have hff' : f =ᵐ[volume] f' := hf.1.ae_eq_mk
  have hf'i : Integrable f' := hf.congr hff'
  have hnm : Measurable fun x => ENNReal.ofReal (-f' x) := hf'm.neg.ennreal_ofReal
  obtain ⟨N, hNsub, hNm, hN0⟩ := exists_measurable_superset_of_null (ae_iff.1 hff')
  have hνN : ∀ᵐ t ∂volume, ν t N = 0 := by
    have : ∫⁻ t, ν t N = 0 := by
      have h1 : ∀ t, ν t N = ∫⁻ x, N.indicator 1 x ∂(ν t) := fun t =>
        (lintegral_indicator_one hNm).symm
      simp_rw [h1]
      rw [lintegral_rankOne_average hμ hν (measurable_one.indicator hNm),
        lintegral_indicator_one hNm, hN0]
    exact (lintegral_eq_zero_iff (Measure.measurable_coe hNm |>.comp hmeas)).1 this
  have hae : ∀ᵐ t ∂volume, f =ᵐ[ν t] f' := by
    filter_upwards [hνN] with t ht
    exact measure_mono_null (fun x hx => hNsub hx) ht
  -- finiteness of `∫ |f'| dν_λ`
  have hnorm : ∫⁻ t, ∫⁻ x, ‖f' x‖ₑ ∂(ν t) = ∫⁻ x, ‖f' x‖ₑ :=
    lintegral_rankOne_average hμ hν hf'm.enorm
  have hfin : ∫⁻ t, ∫⁻ x, ‖f' x‖ₑ ∂(ν t) < ∞ := by rw [hnorm]; exact hf'i.2
  have hmeasN : Measurable fun t => ∫⁻ x, ‖f' x‖ₑ ∂(ν t) :=
    (Measure.measurable_lintegral hf'm.enorm).comp hmeas
  have haefin : ∀ᵐ t ∂volume, ∫⁻ x, ‖f' x‖ₑ ∂(ν t) < ∞ := ae_lt_top hmeasN hfin.ne
  have hint' : ∀ᵐ t ∂volume, Integrable f' (ν t) := by
    filter_upwards [haefin] with t ht using ⟨hf'm.aestronglyMeasurable, ht⟩
  -- positive and negative parts
  have hpos : Measurable fun t => ∫⁻ x, ENNReal.ofReal (f' x) ∂(ν t) :=
    (Measure.measurable_lintegral hf'm.ennreal_ofReal).comp hmeas
  have hneg : Measurable fun t => ∫⁻ x, ENNReal.ofReal (-f' x) ∂(ν t) :=
    (Measure.measurable_lintegral hnm).comp hmeas
  have hpos_fin : ∫⁻ t, ∫⁻ x, ENNReal.ofReal (f' x) ∂(ν t) < ∞ := by
    rw [lintegral_rankOne_average hμ hν hf'm.ennreal_ofReal]
    exact lt_of_le_of_lt (lintegral_mono fun x => by
      rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)) hf'i.2
  have hneg_fin : ∫⁻ t, ∫⁻ x, ENNReal.ofReal (-f' x) ∂(ν t) < ∞ := by
    rw [lintegral_rankOne_average hμ hν hnm]
    exact lt_of_le_of_lt (lintegral_mono fun x => by
      rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (neg_le_abs _)) hf'i.2
  have hrepr : ∀ᵐ t ∂volume, ∫ x, f x ∂(ν t) =
      (∫⁻ x, ENNReal.ofReal (f' x) ∂(ν t)).toReal -
        (∫⁻ x, ENNReal.ofReal (-f' x) ∂(ν t)).toReal := by
    filter_upwards [hae, hint'] with t ht hti
    rw [integral_congr_ae ht, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hti]
  have hA : Integrable fun t => (∫⁻ x, ENNReal.ofReal (f' x) ∂(ν t)).toReal :=
    integrable_toReal_of_lintegral_ne_top hpos.aemeasurable hpos_fin.ne
  have hB : Integrable fun t => (∫⁻ x, ENNReal.ofReal (-f' x) ∂(ν t)).toReal :=
    integrable_toReal_of_lintegral_ne_top hneg.aemeasurable hneg_fin.ne
  refine ⟨?_, (hA.sub hB).congr (hrepr.mono fun t ht => ht.symm), ?_⟩
  · filter_upwards [hae, hint'] with t ht hti using hti.congr ht.symm
  · rw [integral_congr_ae hrepr, integral_sub hA hB,
      integral_toReal hpos.aemeasurable (ae_lt_top hpos hpos_fin.ne),
      integral_toReal hneg.aemeasurable (ae_lt_top hneg hneg_fin.ne),
      lintegral_rankOne_average hμ hν hf'm.ennreal_ofReal,
      lintegral_rankOne_average hμ hν hnm,
      integral_congr_ae hff', integral_eq_lintegral_pos_part_sub_lintegral_neg_part hf'i]

end Family

end DF
