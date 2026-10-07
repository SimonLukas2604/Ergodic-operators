/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Appendix A.3 (and §4.5): subharmonic functions   (book pp. 327–331, 418–422)

Subharmonic functions take values in `ℝ ∪ {-∞}`; we model them as `EReal`-valued functions
which never take the value `⊤`.

## The extended circle average

Mathlib's `Real.circleAverage` only handles real-valued (integrable) functions.  For an
`EReal`-valued function `F` we define

  `ecircleAverage F c r = ⨅ n, circleAverage (max F (-n)) c r`,

i.e. the (monotone) limit of the averages of the truncations of `F` at level `-n`.  For upper
semicontinuous `F` (bounded above on the circle) this is the usual extended integral
`(2π)⁻¹ ∫ F(c + r e^{iθ}) dθ ∈ [-∞, ∞)`, by monotone convergence; for real-valued circle
integrable `F` it agrees with `circleAverage` (`ecircleAverage_coe`).

## Main definitions and results

* `DF.SubharmonicOn F U` — `F : ℂ → EReal` is upper semicontinuous on `U`, never `⊤`, and
  satisfies the sub-mean value inequality (4.5.1) on every closed disc contained in `U`
  (definition in §4.5 and §A.3).
* `DF.subharmonicOn_coe_iff` — for real-valued functions the definition reduces to the usual
  one with `Real.circleAverage`.
* `DF.HarmonicOnNhd.subharmonicOn` — harmonic functions are subharmonic.
* `DF.logNorm f` — `log |f|` with value `-∞` at the zeros of `f`;
  `DF.subharmonicOn_logNorm` — `log |f|` is subharmonic for analytic `f` (Exercise 4.5.3),
  proved from Jensen's formula in Mathlib.
* `DF.SubharmonicOn.truncBelow_le_circleAverage` — truncations `max F (-n)` of subharmonic
  functions satisfy the real sub-mean value inequality.
* `DF.subharmonicOn_iInf` — the infimum of a decreasing sequence of (real valued,
  continuous) subharmonic functions is subharmonic (a version of Prop. 4.5.2(c) without the
  positivity assumption).

## Statements (recorded, not proved)

* `DF.RieszRepresentationStatement` — Theorem A.3.2 (Riesz decomposition), cited by the book.
* `DF.RieszMeasureBoundStatement` — Theorem A.3.4, cited by the book.
The Fourier-decay results Lemma A.3.5 and Theorem A.3.1 are in `DamanikFillman/AppA/FourierDecay`.
-/
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLog
import Mathlib.Analysis.Complex.Harmonic.MeanValue
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

noncomputable section

open Real Complex Metric Set Filter Topology MeasureTheory InnerProductSpace

namespace DF

/-! ### Truncation and the extended circle average -/

/-- Truncation of an extended real from below at level `-n`, as a real number. -/
def truncBelow (n : ℕ) (x : EReal) : ℝ := (max x (-(n : EReal))).toReal

lemma neg_natCast_ereal (n : ℕ) : (-(n : EReal)) = ((-(n : ℝ) : ℝ) : EReal) := by
  simp

lemma truncBelow_coe (n : ℕ) (x : ℝ) : truncBelow n (x : EReal) = max x (-(n : ℝ)) := by
  unfold truncBelow
  rw [neg_natCast_ereal]
  rcases le_total x (-(n : ℝ)) with h | h
  · rw [max_eq_right (EReal.coe_le_coe_iff.2 h), max_eq_right h, EReal.toReal_coe]
  · rw [max_eq_left (EReal.coe_le_coe_iff.2 h), max_eq_left h, EReal.toReal_coe]

lemma truncBelow_bot (n : ℕ) : truncBelow n ⊥ = -(n : ℝ) := by
  unfold truncBelow
  rw [neg_natCast_ereal, max_eq_right bot_le, EReal.toReal_coe]

lemma truncBelow_eq_coe_max {n : ℕ} {x : EReal} (hx : x ≠ ⊤) :
    ((truncBelow n x : ℝ) : EReal) = max x (-(n : EReal)) := by
  unfold truncBelow
  rw [neg_natCast_ereal]
  apply EReal.coe_toReal
  · exact ne_of_lt (max_lt (lt_top_iff_ne_top.2 hx) (EReal.coe_lt_top _))
  · exact ne_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe _) (le_max_right _ _))

lemma truncBelow_mono {n : ℕ} {x y : EReal} (hy : y ≠ ⊤) (h : x ≤ y) :
    truncBelow n x ≤ truncBelow n y := by
  have hx : x ≠ ⊤ := ne_top_of_le_ne_top hy h
  rw [← EReal.coe_le_coe_iff, truncBelow_eq_coe_max hx, truncBelow_eq_coe_max hy]
  exact max_le_max h le_rfl

lemma truncBelow_antitone {x : EReal} (hx : x ≠ ⊤) : Antitone (fun n : ℕ => truncBelow n x) := by
  intro m n hmn
  simp only
  rw [← EReal.coe_le_coe_iff, truncBelow_eq_coe_max hx, truncBelow_eq_coe_max hx]
  refine max_le_max le_rfl ?_
  exact EReal.neg_le_neg_iff.2 (by exact_mod_cast hmn)

lemma neg_natCast_le_truncBelow (n : ℕ) (x : EReal) : -(n : ℝ) ≤ truncBelow n x := by
  rcases eq_or_ne x ⊤ with rfl | hx
  · simp [truncBelow]
  · rw [← EReal.coe_le_coe_iff, truncBelow_eq_coe_max hx, ← neg_natCast_ereal]
    exact le_max_right _ _

lemma le_truncBelow {n : ℕ} {x : EReal} (hx : x ≠ ⊤) : x ≤ truncBelow n x := by
  rw [truncBelow_eq_coe_max hx]; exact le_max_left _ _

/-- The extended circle average of `F : ℂ → EReal` over the circle of centre `c` and radius `r`:
the infimum (= decreasing limit) of the averages of the truncations `max F (-n)`. -/
def ecircleAverage (F : ℂ → EReal) (c : ℂ) (r : ℝ) : EReal :=
  ⨅ n : ℕ, ((circleAverage (fun w => truncBelow n (F w)) c r : ℝ) : EReal)

/-- Circle integrability is preserved by truncation from below. -/
lemma circleIntegrable_max_const {f : ℂ → ℝ} {c : ℂ} {r : ℝ} (hf : CircleIntegrable f c r)
    (a : ℝ) : CircleIntegrable (fun w => max (f w) a) c r := by
  unfold CircleIntegrable at *
  exact ⟨hf.1.sup (integrableOn_const measure_Ioc_lt_top.ne),
    hf.2.sup (integrableOn_const measure_Ioc_lt_top.ne)⟩

/-- For real-valued circle-integrable functions the extended circle average is the usual one. -/
theorem ecircleAverage_coe {f : ℂ → ℝ} {c : ℂ} {r : ℝ} (hf : CircleIntegrable f c r) :
    ecircleAverage (fun z => (f z : EReal)) c r = ((circleAverage f c r : ℝ) : EReal) := by
  unfold ecircleAverage
  simp_rw [truncBelow_coe]
  set a : ℕ → ℝ := fun n => circleAverage (fun w => max (f w) (-(n : ℝ))) c r with ha
  have hanti : Antitone a := by
    intro m n hmn
    apply circleAverage_mono (circleIntegrable_max_const hf _) (circleIntegrable_max_const hf _)
    intro x _
    exact max_le_max le_rfl (neg_le_neg (by exact_mod_cast hmn))
  have hlim : Tendsto a atTop (𝓝 (circleAverage f c r)) := by
    simp only [ha, circleAverage, smul_eq_mul]
    refine Tendsto.const_mul _ ?_
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun θ => |f (circleMap c r θ)|) ?_ ?_ hf.abs ?_
    · exact Eventually.of_forall fun n => ((circleIntegrable_max_const hf _).def'.aestronglyMeasurable)
    · refine Eventually.of_forall fun n => Eventually.of_forall fun θ _ => ?_
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · have := neg_abs_le (f (circleMap c r θ))
        exact this.trans (le_max_left _ _)
      · exact max_le (le_abs_self _) (by have := abs_nonneg (f (circleMap c r θ)); simp; linarith)
    · refine Eventually.of_forall fun θ _ => ?_
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop ⌈-f (circleMap c r θ)⌉₊] with n hn
      have : -(n : ℝ) ≤ f (circleMap c r θ) := by
        have := (Nat.le_ceil (-f (circleMap c r θ))).trans (Nat.cast_le.2 hn)
        linarith
      exact (max_eq_left this).symm
  have h1 : Tendsto (fun n => (a n : EReal)) atTop (𝓝 ((circleAverage f c r : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.tendsto _).comp hlim
  have h2 : Tendsto (fun n => (a n : EReal)) atTop (𝓝 (⨅ n, (a n : EReal))) :=
    tendsto_atTop_iInf (fun m n hmn => EReal.coe_le_coe_iff.2 (hanti hmn))
  exact tendsto_nhds_unique h2 h1

/-! ### Subharmonic functions -/

/-- `F : ℂ → ℝ ∪ {-∞}` is subharmonic on `U` (book §4.5, §A.3): it is upper semicontinuous on
`U` and satisfies the sub-mean value inequality on every closed disc contained in `U`. -/
structure SubharmonicOn (F : ℂ → EReal) (U : Set ℂ) : Prop where
  ne_top : ∀ z ∈ U, F z ≠ ⊤
  usc : UpperSemicontinuousOn F U
  submean : ∀ c : ℂ, ∀ r : ℝ, 0 < r → closedBall c r ⊆ U → F c ≤ ecircleAverage F c r

/-- `F` is subharmonic on the whole plane. -/
abbrev Subharmonic (F : ℂ → EReal) : Prop := SubharmonicOn F univ

lemma SubharmonicOn.mono {F : ℂ → EReal} {U V : Set ℂ} (h : SubharmonicOn F U) (hVU : V ⊆ U) :
    SubharmonicOn F V :=
  ⟨fun z hz => h.ne_top z (hVU hz), h.usc.mono hVU,
    fun c r hr hb => h.submean c r hr (hb.trans hVU)⟩

lemma upperSemicontinuousOn_coe_iff {f : ℂ → ℝ} {U : Set ℂ} :
    UpperSemicontinuousOn (fun z => (f z : EReal)) U ↔ UpperSemicontinuousOn f U := by
  constructor
  · intro h x hx y hy
    filter_upwards [h x hx y (EReal.coe_lt_coe_iff.2 hy)] with z hz
    exact EReal.coe_lt_coe_iff.1 hz
  · intro h x hx y hy
    induction y using EReal.rec with
    | bot => exact absurd hy (not_lt_bot)
    | coe y => filter_upwards [h x hx y (EReal.coe_lt_coe_iff.1 hy)] with z hz
               exact EReal.coe_lt_coe_iff.2 hz
    | top => exact Eventually.of_forall fun z => EReal.coe_lt_top _

/-- For real-valued functions which are integrable over the relevant circles, subharmonicity
is the usual condition `f c ≤ circleAverage f c r`. -/
theorem subharmonicOn_coe_iff {f : ℂ → ℝ} {U : Set ℂ}
    (hint : ∀ c : ℂ, ∀ r : ℝ, 0 < r → closedBall c r ⊆ U → CircleIntegrable f c r) :
    SubharmonicOn (fun z => (f z : EReal)) U ↔
      UpperSemicontinuousOn f U ∧
        ∀ c : ℂ, ∀ r : ℝ, 0 < r → closedBall c r ⊆ U → f c ≤ circleAverage f c r := by
  constructor
  · intro h
    refine ⟨upperSemicontinuousOn_coe_iff.1 h.usc, fun c r hr hb => ?_⟩
    have := h.submean c r hr hb
    rwa [ecircleAverage_coe (hint c r hr hb), EReal.coe_le_coe_iff] at this
  · rintro ⟨h1, h2⟩
    refine ⟨fun z _ => EReal.coe_ne_top _, upperSemicontinuousOn_coe_iff.2 h1,
      fun c r hr hb => ?_⟩
    rw [ecircleAverage_coe (hint c r hr hb), EReal.coe_le_coe_iff]; exact h2 c r hr hb

/-- Harmonic functions are subharmonic. -/
theorem subharmonicOn_of_harmonicOnNhd {f : ℂ → ℝ} {U : Set ℂ} (hf : HarmonicOnNhd f U) :
    SubharmonicOn (fun z => (f z : EReal)) U := by
  have hint : ∀ c : ℂ, ∀ r : ℝ, 0 < r → closedBall c r ⊆ U → CircleIntegrable f c r := by
    intro c r hr hb
    apply ContinuousOn.circleIntegrable'
    have : sphere c |r| ⊆ U := by
      rw [abs_of_pos hr]; exact sphere_subset_closedBall.trans hb
    exact (hf.mono this).continuousOn
  refine (subharmonicOn_coe_iff hint).2 ⟨hf.continuousOn.upperSemicontinuousOn, ?_⟩
  intro c r hr hb
  rw [(hf.mono (by rwa [abs_of_pos hr])).circleAverage_eq]

/-! ### Truncations, and decreasing limits -/

/-- An upper semicontinuous function with values in `[-∞, ∞)` is bounded above on compact
sets. -/
lemma exists_bound_of_usc {F : ℂ → EReal} {U S : Set ℂ} (hne : ∀ z ∈ U, F z ≠ ⊤)
    (husc : UpperSemicontinuousOn F U) (hS : IsCompact S) (hSU : S ⊆ U) :
    ∃ M : ℝ, ∀ z ∈ S, F z ≤ M := by
  rcases S.eq_empty_or_nonempty with rfl | hne'
  · exact ⟨0, by simp⟩
  obtain ⟨a, haS, ha⟩ := (husc.mono hSU).exists_isMaxOn hne' hS
  exact ⟨(F a).toReal, fun z hz => (ha hz).trans (EReal.le_coe_toReal (hne a (hSU haS)))⟩

/-- Truncations of an upper semicontinuous function are integrable over circles. -/
lemma circleIntegrable_truncBelow {F : ℂ → EReal} {U : Set ℂ} (hne : ∀ z ∈ U, F z ≠ ⊤)
    (husc : UpperSemicontinuousOn F U) {c : ℂ} {r : ℝ} (hS : sphere c |r| ⊆ U) (n : ℕ) :
    CircleIntegrable (fun w => truncBelow n (F w)) c r := by
  obtain ⟨M, hM⟩ := exists_bound_of_usc hne husc (isCompact_sphere c |r|) hS
  have hmeas : Measurable (fun θ => F (circleMap c r θ)) := by
    have : UpperSemicontinuous (fun θ => F (circleMap c r θ)) := by
      rw [← upperSemicontinuousOn_univ_iff]
      exact husc.comp (continuous_circleMap c r).continuousOn
        (fun θ _ => hS (circleMap_mem_sphere' c r θ))
    exact this.measurable
  have hm2 : Measurable (fun θ => truncBelow n (F (circleMap c r θ))) :=
    measurable_ereal_toReal.comp (hmeas.max measurable_const)
  unfold CircleIntegrable
  refine (intervalIntegrable_const (c := |M| + n)).mono_fun' hm2.aestronglyMeasurable
    (Eventually.of_forall fun θ => ?_)
  have hFθ := hM _ (circleMap_mem_sphere' c r θ)
  have h1 := neg_natCast_le_truncBelow n (F (circleMap c r θ))
  have h2 : truncBelow n (F (circleMap c r θ)) ≤ truncBelow n (M : EReal) :=
    truncBelow_mono (EReal.coe_ne_top _) hFθ
  rw [truncBelow_coe] at h2
  simp only [Real.norm_eq_abs, abs_le]
  constructor
  · have := abs_nonneg M; linarith
  · refine h2.trans (max_le (by linarith [le_abs_self M, (Nat.cast_nonneg n : (0:ℝ) ≤ n)])
      (by have := abs_nonneg M; have := (Nat.cast_nonneg n : (0:ℝ) ≤ n); linarith))

/-- The truncations `max F (-n)` of a subharmonic function satisfy the (real) sub-mean value
inequality. -/
lemma SubharmonicOn.truncBelow_le_circleAverage {F : ℂ → EReal} {U : Set ℂ}
    (hF : SubharmonicOn F U) {c : ℂ} {r : ℝ} (hr : 0 < r) (hb : closedBall c r ⊆ U) (n : ℕ) :
    truncBelow n (F c) ≤ circleAverage (fun w => truncBelow n (F w)) c r := by
  have hint := circleIntegrable_truncBelow hF.ne_top hF.usc
    (by rw [abs_of_pos hr]; exact sphere_subset_closedBall.trans hb) n
  rw [← EReal.coe_le_coe_iff, truncBelow_eq_coe_max (hF.ne_top c (hb (mem_closedBall_self hr.le)))]
  refine max_le ((hF.submean c r hr hb).trans (iInf_le _ n)) ?_
  rw [neg_natCast_ereal, EReal.coe_le_coe_iff]
  have := circleAverage_mono (circleIntegrable_const (-(n : ℝ)) c r) hint
    (fun x _ => neg_natCast_le_truncBelow n (F x))
  rwa [circleAverage_const] at this

/-- The infimum of a decreasing sequence of continuous real-valued functions satisfying the
sub-mean value inequality on discs in `U` is subharmonic on `U` (cf. Prop. 4.5.2(c); no sign
condition is needed). -/
theorem subharmonicOn_iInf {u : ℕ → ℂ → ℝ} {U : Set ℂ} (hcont : ∀ N, Continuous (u N))
    (hanti : ∀ z, Antitone (fun N => u N z))
    (hsub : ∀ N c r, 0 < r → closedBall c r ⊆ U → u N c ≤ circleAverage (u N) c r) :
    SubharmonicOn (fun z => ⨅ N, (u N z : EReal)) U := by
  set F : ℂ → EReal := fun z => ⨅ N, (u N z : EReal) with hFdef
  have hne : ∀ z, F z ≠ ⊤ := fun z =>
    ne_top_of_le_ne_top (EReal.coe_ne_top (u 0 z)) (iInf_le _ 0)
  have husc : UpperSemicontinuous F := upperSemicontinuous_iInf fun N =>
    (continuous_coe_real_ereal.comp (hcont N)).upperSemicontinuous
  refine ⟨fun z _ => hne z, husc.upperSemicontinuousOn U, fun c r hr hb => le_iInf fun n => ?_⟩
  have hintN : ∀ N, CircleIntegrable (u N) c r := fun N =>
    (hcont N).continuousOn.circleIntegrable'
  have htend : Tendsto (fun N => circleAverage (fun w => max (u N w) (-(n : ℝ))) c r) atTop
      (𝓝 (circleAverage (fun w => truncBelow n (F w)) c r)) := by
    simp only [circleAverage, smul_eq_mul]
    refine Tendsto.const_mul _ ?_
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun θ => |u 0 (circleMap c r θ)| + n) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun N =>
        (((hcont N).comp (continuous_circleMap c r)).max continuous_const).aestronglyMeasurable
    · refine Eventually.of_forall fun N => Eventually.of_forall fun θ _ => ?_
      have h0 : u N (circleMap c r θ) ≤ u 0 (circleMap c r θ) := hanti _ (Nat.zero_le N)
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      rw [Real.norm_eq_abs, abs_le]
      constructor
      · have := abs_nonneg (u 0 (circleMap c r θ))
        exact le_trans (by linarith) (le_max_right _ _)
      · exact max_le (by linarith [le_abs_self (u 0 (circleMap c r θ))])
          (by have := abs_nonneg (u 0 (circleMap c r θ)); linarith)
    · exact ((continuous_abs.comp ((hcont 0).comp (continuous_circleMap c r))).add
        continuous_const).intervalIntegrable _ _
    · refine Eventually.of_forall fun θ _ => ?_
      set w := circleMap c r θ
      have h1 : Tendsto (fun N => (u N w : EReal)) atTop (𝓝 (F w)) :=
        tendsto_atTop_iInf (fun a b hab => EReal.coe_le_coe_iff.2 (hanti w hab))
      have h2 : Tendsto (fun N => max (u N w : EReal) (-(n : EReal))) atTop
          (𝓝 (max (F w) (-(n : EReal)))) :=
        ((continuous_id.max continuous_const).tendsto _).comp h1
      have hb1 : max (F w) (-(n : EReal)) ≠ ⊤ :=
        ne_of_lt (max_lt (lt_top_iff_ne_top.2 (hne w))
          (by rw [neg_natCast_ereal]; exact EReal.coe_lt_top _))
      have hb2 : max (F w) (-(n : EReal)) ≠ ⊥ :=
        ne_of_gt (lt_of_lt_of_le (by rw [neg_natCast_ereal]; exact EReal.bot_lt_coe _)
          (le_max_right _ _))
      have h3 := (EReal.tendsto_toReal hb1 hb2).comp h2
      refine h3.congr fun N => ?_
      simp only [Function.comp]
      exact truncBelow_coe n (u N w)
  have hle : ∀ N, F c ≤ ((circleAverage (fun w => max (u N w) (-(n : ℝ))) c r : ℝ) : EReal) := by
    intro N
    refine (iInf_le _ N).trans ?_
    rw [EReal.coe_le_coe_iff]
    exact (hsub N c r hr hb).trans (circleAverage_mono (hintN N)
      (circleIntegrable_max_const (hintN N) _) fun x _ => le_max_left _ _)
  exact ge_of_tendsto' ((continuous_coe_real_ereal.tendsto _).comp htend) hle

/-! ### `log |f|` for analytic `f` (Exercise 4.5.3) -/

/-- `log |f(z)|` as an element of `ℝ ∪ {-∞}`, with the value `-∞` at the zeros of `f`. -/
def logNorm (f : ℂ → ℂ) (z : ℂ) : EReal :=
  if f z = 0 then ⊥ else ((Real.log ‖f z‖ : ℝ) : EReal)

lemma logNorm_ne_top (f : ℂ → ℂ) (z : ℂ) : logNorm f z ≠ ⊤ := by
  unfold logNorm; split_ifs <;> simp

lemma logNorm_of_ne_zero {f : ℂ → ℂ} {z : ℂ} (h : f z ≠ 0) :
    logNorm f z = ((Real.log ‖f z‖ : ℝ) : EReal) := by
  simp [logNorm, h]

lemma upperSemicontinuousAt_logNorm {f : ℂ → ℂ} {z : ℂ} (hf : ContinuousAt f z) :
    UpperSemicontinuousAt (logNorm f) z := by
  intro y hy
  by_cases h0 : f z = 0
  · induction y using EReal.rec with
    | bot => exact absurd hy (not_lt_bot)
    | top => exact Eventually.of_forall fun w => lt_top_iff_ne_top.2 (logNorm_ne_top f w)
    | coe a =>
      have ht : Tendsto (fun w => ‖f w‖) (𝓝 z) (𝓝 0) := by
        have := hf.norm.tendsto; rwa [h0, norm_zero] at this
      filter_upwards [ht.eventually (gt_mem_nhds (Real.exp_pos a))] with w hw
      by_cases hw0 : f w = 0
      · simp [logNorm, hw0]
      · rw [logNorm_of_ne_zero hw0, EReal.coe_lt_coe_iff]
        exact (Real.log_lt_iff_lt_exp (norm_pos_iff.2 hw0)).2 hw
  · have hc : ContinuousAt (fun w => ((Real.log ‖f w‖ : ℝ) : EReal)) z :=
      continuous_coe_real_ereal.continuousAt.comp (hf.norm.log (norm_ne_zero_iff.2 h0))
    have h1 : ∀ᶠ w in 𝓝 z, ((Real.log ‖f w‖ : ℝ) : EReal) < y := by
      apply hc.eventually (gt_mem_nhds _)
      rwa [logNorm_of_ne_zero h0] at hy
    have h2 : ∀ᶠ w in 𝓝 z, f w ≠ 0 := hf.eventually_ne h0
    filter_upwards [h1, h2] with w hw1 hw2
    rwa [logNorm_of_ne_zero hw2]

/-- Jensen's formula yields the sub-mean value inequality for `log |f|` (real version with
Mathlib's convention `log 0 = 0`), provided `f c ≠ 0`. -/
lemma log_norm_le_circleAverage {f : ℂ → ℂ} {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hf : AnalyticOnNhd ℂ f (closedBall c r)) (hfc : f c ≠ 0) :
    Real.log ‖f c‖ ≤ circleAverage (fun w => Real.log ‖f w‖) c r := by
  have h1 : AnalyticOnNhd ℂ f (closedBall c |r|) := by rwa [abs_of_pos hr]
  rw [h1.circleAverage_log_norm hr.ne' hfc, le_add_iff_nonneg_left]
  apply finsum_nonneg
  intro u
  by_cases hu : u ∈ closedBall c |r|
  · refine mul_nonneg (by exact_mod_cast (MeromorphicOn.AnalyticOnNhd.divisor_nonneg h1) u) ?_
    by_cases huc : u = c
    · subst huc; simp
    · apply Real.log_nonneg
      rw [← div_eq_mul_inv, one_le_div (norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm huc)))]
      rw [mem_closedBall, dist_eq_norm, abs_of_pos hr] at hu
      rwa [norm_sub_rev]
  · simp [hu]

/-- **Exercise 4.5.3.** If `f` is analytic on (a neighbourhood of) `U`, then `log |f|` is
subharmonic on `U`. -/
theorem subharmonicOn_logNorm {f : ℂ → ℂ} {U : Set ℂ} (hf : AnalyticOnNhd ℂ f U) :
    SubharmonicOn (logNorm f) U := by
  refine ⟨fun z _ => logNorm_ne_top f z,
    fun z hz => (upperSemicontinuousAt_logNorm (hf z hz).continuousAt).upperSemicontinuousWithinAt U,
    fun c r hr hb => ?_⟩
  by_cases hfc : f c = 0
  · simp [logNorm, hfc]
  rw [logNorm_of_ne_zero hfc]
  have hfb : AnalyticOnNhd ℂ f (closedBall c r) := hf.mono hb
  have hJ := log_norm_le_circleAverage hr hfb hfc
  have h1 : AnalyticOnNhd ℂ f (closedBall c |r|) := by rwa [abs_of_pos hr]
  have hint : CircleIntegrable (fun w => Real.log ‖f w‖) c r :=
    (h1.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
  refine le_iInf fun n => ?_
  rw [EReal.coe_le_coe_iff]
  refine hJ.trans (le_of_le_of_eq (circleAverage_mono hint (circleIntegrable_max_const hint (-(n : ℝ)))
    (fun x _ => le_max_left _ _)) ?_)
  -- the truncation of `logNorm f` agrees with `max (log ‖f‖) (-n)` off the zeros of `f`
  apply circleAverage_congr_codiscreteWithin _ hr.ne'
  have hz : f ⁻¹' {0}ᶜ ∈ codiscreteWithin (closedBall c |r|) :=
    h1.preimage_zero_mem_codiscreteWithin hfc (by simp)
      (isConnected_closedBall (abs_nonneg r))
  filter_upwards [codiscreteWithin_mono sphere_subset_closedBall hz] with w hw
  simp only [mem_preimage, mem_compl_iff, mem_singleton_iff] at hw
  rw [logNorm_of_ne_zero hw, truncBelow_coe]

/-- `log |z - w|` is subharmonic on `ℂ`. -/
theorem subharmonic_logNorm_sub (w : ℂ) : Subharmonic (logNorm (fun z => z - w)) :=
  subharmonicOn_logNorm (fun z _ => by fun_prop)

end DF
