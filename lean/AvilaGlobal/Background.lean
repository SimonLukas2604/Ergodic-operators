/-
# Inputs used by the paper

The results the paper quotes from the literature, or calls "easily seen", without proof, each
stated in the exact form in which it is used.  Convexity (`L_convexOn`) is **proved** here;
the others are collected in the class `Hypotheses` (stated, not asserted) and every theorem
depending on them carries `[Hypotheses]`.

* `L_convexOn` — `ε ↦ L(α, A_ε)` is convex (§1.2, "easily seen to be a convex function";
  it follows from subharmonicity of `log ‖A_n‖`).
* `jks_continuity` — **Theorem [JKS]** (Bourgain–Jitomirskaya [BJ1], Jitomirskaya–Koslover–
  Schulteis [JKS]): `(α, A) ↦ L(α, A)` is continuous at every `(α, A)` with `α` irrational,
  for convergence `α_n → α` (arbitrary real, possibly rational, `α_n`) and `A_n → A`
  uniformly on a strip.
* `uh_smooth_family` — the property of uniformly hyperbolic
  cocycles quoted in §1.2 (normally hyperbolic theory [HPS]): `L` is
  real-analytic in real-analytic families at fixed frequency and `C^∞` jointly in frequency
  and parameters.

Openness of `𝒰ℋ` and Johnson's theorem, also quoted in §1.2, are **proved** in `UHOpen.lean`
and `Johnson.lean`.
-/
import AvilaGlobal.Basic

noncomputable section

open scoped Matrix.Norms.Operator ContDiff
open Matrix Filter Topology Complex Set

namespace AvilaGlobal

open AMO

/-- A real-analytic family of real-analytic potentials, parametrised by an open subset `U` of a
real normed space `P`: `(λ, z) ↦ v_λ(z)` is real-analytic on `U × {|Im z| < δ}` and each `v_λ`
is a real-analytic potential on the strip. -/
structure IsAnalyticFamily {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] (δ : ℝ)
    (U : Set P) (v : P → ℂ → ℂ) : Prop where
  isOpen : IsOpen U
  pot : ∀ p ∈ U, IsRealAnalyticPotential δ (v p)
  analytic : AnalyticOnNhd ℝ (fun q : P × ℂ => v q.1 q.2) (U ×ˢ strip δ)

/-- A real-analytic family of analytic `SL(2,ℂ)` cocycles. -/
structure IsAnalyticCocycleFamily {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (δ : ℝ) (U : Set P) (A : P → ℂ → M2) : Prop where
  isOpen : IsOpen U
  cocycle : ∀ p ∈ U, IsAnalyticCocycle δ (A p)
  analytic : AnalyticOnNhd ℝ (fun q : P × ℂ => A q.1 q.2) (U ×ˢ strip δ)

/-! ### Convexity of `ε ↦ L(α, A_ε)` -/

/-! ### Convexity from a one-dimensional sub-mean-value property -/

/-- Maximum principle for continuous functions with the sub-mean property
`w t ≤ (2π)⁻¹ ∫₀^{2π} w (t + r sin θ) dθ`. -/
lemma submean_max_principle {w : ℝ → ℝ} {p q : ℝ} (hpq : p ≤ q)
    (hw : ContinuousOn w (Icc p q)) (hp : w p ≤ 0) (hq : w q ≤ 0)
    (hsub : ∀ t r, 0 < r → p < t - r → t + r < q →
      w t ≤ (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, w (t + r * Real.sin θ)) :
    ∀ t ∈ Icc p q, w t ≤ 0 := by
  by_contra! h
  obtain ⟨t1, ht1, hpos⟩ := h
  obtain ⟨tm, htm, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hpq) hw
  have hmax' : ∀ x ∈ Icc p q, w x ≤ w tm := isMaxOn_iff.1 hmax
  set M := w tm with hMdef
  have hM : 0 < M := hpos.trans_le (hmax' t1 ht1)
  set S := Icc p q ∩ w ⁻¹' {M} with hSdef
  have hScl : IsClosed S := hw.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hS : IsCompact S := isCompact_Icc.of_isClosed_subset hScl inter_subset_left
  have hne : S.Nonempty := ⟨tm, htm, rfl⟩
  have h0 := hS.sInf_mem hne
  set t0 := sInf S with ht0
  obtain ⟨⟨hpt0, ht0q⟩, hwt0⟩ := h0
  simp only [mem_preimage, mem_singleton_iff] at hwt0
  have hpt0' : p < t0 := by
    rcases hpt0.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hwt0; linarith
  have ht0q' : t0 < q := by
    rcases ht0q.lt_or_eq with h | h
    · exact h
    · exfalso; rw [h] at hwt0; linarith
  set r := min (t0 - p) (q - t0) / 2 with hr
  have hr0 : 0 < r := by have := lt_min (sub_pos.2 hpt0') (sub_pos.2 ht0q'); linarith
  have hr1 : r < t0 - p := by have := min_le_left (t0 - p) (q - t0); linarith
  have hr2 : r < q - t0 := by have := min_le_right (t0 - p) (q - t0); linarith
  have hmem : ∀ θ, t0 + r * Real.sin θ ∈ Icc p q := by
    intro θ
    have h1 := Real.neg_one_le_sin θ
    have h2 := Real.sin_le_one θ
    constructor <;> nlinarith
  have hsubt := hsub t0 r hr0 (by linarith) (by linarith)
  have hcont : ContinuousOn (fun θ => w (t0 + r * Real.sin θ)) (Icc 0 (2 * Real.pi)) :=
    (hw.comp_continuous (by fun_prop) hmem).continuousOn
  have hpi := Real.two_pi_pos
  have hval : w (t0 - r) = M := by
    by_contra hne'
    have hlt : w (t0 - r) < M := lt_of_le_of_ne (hmax' _ ⟨by linarith, by linarith⟩) hne'
    have hs : Real.sin (3 * Real.pi / 2) = -1 := by
      rw [show 3 * Real.pi / 2 = Real.pi / 2 + Real.pi by ring, Real.sin_add_pi,
        Real.sin_pi_div_two]
    have := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
      hpi hcont continuousOn_const (fun θ _ => hmax' _ (hmem θ))
      ⟨3 * Real.pi / 2, ⟨by positivity, by linarith [Real.pi_pos]⟩, by
        simp only [hs, mul_neg_one, ← sub_eq_add_neg]; exact hlt⟩
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
    rw [hwt0, le_inv_mul_iff₀ hpi] at hsubt
    nlinarith
  have hle : t0 ≤ t0 - r := csInf_le hS.bddBelow ⟨⟨by linarith, by linarith⟩, hval⟩
  linarith

/-- A continuous function on `(-δ, δ)` with the sub-mean property
`f t ≤ (2π)⁻¹ ∫₀^{2π} f (t + r sin θ) dθ` is convex. -/
lemma convexOn_of_submean {δ : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Ioo (-δ) δ))
    (hsub : ∀ t r, 0 < r → -δ < t - r → t + r < δ →
      f t ≤ (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, f (t + r * Real.sin θ)) :
    ConvexOn ℝ (Ioo (-δ) δ) f := by
  have key : ∀ x ∈ Ioo (-δ) δ, ∀ y ∈ Ioo (-δ) δ, x < y → ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      a + b = 1 → f (a • x + b • y) ≤ a • f x + b • f y := by
    intro x hx y hy hxy a b ha hb hab
    have hyx : y - x ≠ 0 := sub_ne_zero.2 hxy.ne'
    set m := (f y - f x) / (y - x) with hm
    set ℓ : ℝ → ℝ := fun t => f x + m * (t - x) with hℓ
    set w : ℝ → ℝ := fun t => f t - ℓ t with hw
    have hsubset : Icc x y ⊆ Ioo (-δ) δ := Icc_subset_Ioo hx.1 hy.2
    have hwc : ContinuousOn w (Icc x y) :=
      (hf.mono hsubset).sub (by fun_prop)
    have hwx : w x ≤ 0 := by simp [w, ℓ]
    have hwy : w y ≤ 0 := by
      simp only [w, ℓ, m]
      rw [div_mul_cancel₀ _ hyx]
      linarith
    have hwsub : ∀ t r, 0 < r → x < t - r → t + r < y →
        w t ≤ (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, w (t + r * Real.sin θ) := by
      intro t r hr h1 h2
      have hmem : ∀ θ, t + r * Real.sin θ ∈ Ioo (-δ) δ := by
        intro θ
        have h3 := Real.neg_one_le_sin θ
        have h4 := Real.sin_le_one θ
        constructor <;> nlinarith [hx.1, hy.2]
      have hfi : IntervalIntegrable (fun θ => f (t + r * Real.sin θ)) MeasureTheory.volume
          0 (2 * Real.pi) :=
        (hf.comp_continuous (by fun_prop) hmem).intervalIntegrable _ _
      have hℓeq : ∀ θ, ℓ (t + r * Real.sin θ) = ℓ t + (m * r) * Real.sin θ := by
        intro θ; simp only [ℓ]; ring
      have hℓi : ∫ θ in (0 : ℝ)..2 * Real.pi, ℓ (t + r * Real.sin θ)
          = 2 * Real.pi * ℓ t := by
        simp_rw [hℓeq]
        rw [intervalIntegral.integral_add intervalIntegrable_const
          ((Real.continuous_sin.const_mul _).intervalIntegrable _ _),
          intervalIntegral.integral_const_mul, integral_sin, Real.cos_two_pi, Real.cos_zero,
          intervalIntegral.integral_const, smul_eq_mul]
        ring
      have hli : IntervalIntegrable (fun θ => ℓ (t + r * Real.sin θ)) MeasureTheory.volume
          0 (2 * Real.pi) := by
        apply Continuous.intervalIntegrable
        simp only [ℓ]; fun_prop
      have hft := hsub t r hr (by linarith [hx.1]) (by linarith [hy.2])
      simp only [w]
      rw [intervalIntegral.integral_sub hfi hli, hℓi, mul_sub]
      have hpi := Real.two_pi_pos
      rw [← mul_assoc, inv_mul_cancel₀ hpi.ne', one_mul]
      linarith
    have hz : a • x + b • y ∈ Icc x y := by
      simp only [smul_eq_mul]
      have ha' : a = 1 - b := by linarith
      subst ha'
      constructor <;> nlinarith
    have := submean_max_principle hxy.le hwc hwx hwy hwsub _ hz
    simp only [w, ℓ, m, smul_eq_mul] at this ⊢
    have ha' : a = 1 - b := by linarith
    subst ha'
    have e : f x + (f y - f x) / (y - x) * ((1 - b) * x + b * y - x) =
        (1 - b) * f x + b * f y := by
      field_simp
      ring
    linarith
  refine ⟨convex_Ioo _ _, fun x hx y hy a b ha hb hab => ?_⟩
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · exact key x hx y hy hxy a b ha hb hab
  · rw [← add_smul, hab, one_smul, ← add_smul, hab, one_smul]
  · have := key y hy x hx hxy b a hb ha (by linarith)
    rwa [add_comm (b • y), add_comm (b • f y)] at this

/-- A pointwise limit of convex functions is convex. -/
lemma convexOn_of_tendsto {s : Set ℝ} {g : ℕ → ℝ → ℝ} {f : ℝ → ℝ} (hs : Convex ℝ s)
    (hg : ∀ n, ConvexOn ℝ s (g n))
    (hlim : ∀ x ∈ s, Tendsto (fun n => g n x) atTop (𝓝 (f x))) :
    ConvexOn ℝ s f := by
  refine ⟨hs, fun x hx y hy a b ha hb hab => ?_⟩
  have hz := hs hx hy ha hb hab
  exact le_of_tendsto_of_tendsto' (hlim _ hz)
    (((hlim x hx).const_smul a).add ((hlim y hy).const_smul b))
    (fun n => (hg n).2 hx hy ha hb hab)



/-- The complexified iterate `z ↦ A(z + (n-1)α) ⋯ A(z)`. -/
def cIter (α : ℝ) (A : ℂ → M2) : ℕ → ℂ → M2
  | 0, _ => 1
  | n + 1, z => A (z + ((n * α : ℝ) : ℂ)) * cIter α A n z

lemma iter_shift_eq (α : ℝ) (A : ℂ → M2) (ε : ℝ) (n : ℕ) (x : ℝ) :
    iter α (shift A ε) n x = cIter α A n (x + ε * I) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [iter, cIter, shift, ih]
    congr 2
    push_cast
    ring

lemma add_real_mem_strip {δ : ℝ} {z : ℂ} (hz : z ∈ strip δ) (t : ℝ) :
    z + (t : ℂ) ∈ strip δ := by
  simpa [strip] using hz

lemma IsAnalyticCocycle.cIter_diff {δ : ℝ} {A : ℂ → M2} (hA : IsAnalyticCocycle δ A) (α : ℝ)
    (n : ℕ) : DifferentiableOn ℂ (cIter α A n) (strip δ) := by
  induction n with
  | zero => exact differentiableOn_const _
  | succ n ih =>
    have h1 : DifferentiableOn ℂ (fun z => A (z + ((n * α : ℝ) : ℂ))) (strip δ) :=
      hA.holo.comp (differentiableOn_id.add_const _) (fun z hz => add_real_mem_strip hz _)
    exact h1.mul ih

lemma IsAnalyticCocycle.cIter_det {δ : ℝ} {A : ℂ → M2} (hA : IsAnalyticCocycle δ A) (α : ℝ)
    (n : ℕ) {z : ℂ} (hz : z ∈ strip δ) : (cIter α A n z).det = 1 := by
  induction n with
  | zero => simp [cIter]
  | succ n ih => rw [cIter, det_mul, hA.det_eq_one _ (add_real_mem_strip hz _), ih, one_mul]

lemma IsAnalyticCocycle.cIter_periodic {δ : ℝ} {A : ℂ → M2} (hA : IsAnalyticCocycle δ A)
    (α : ℝ) (n : ℕ) (z : ℂ) : cIter α A n (z + 1) = cIter α A n z := by
  induction n with
  | zero => rfl
  | succ n ih => rw [cIter, cIter, ih, add_right_comm, hA.periodic]

/-- The `(i, j)` entry as a continuous linear functional on `M₂(ℂ)`. -/
def entryCLM (i j : Fin 2) : M2 →L[ℂ] ℂ :=
  LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℂ ℂ i j)

@[simp] lemma entryCLM_apply (i j : Fin 2) (M : M2) : entryCLM i j M = M i j := rfl

lemma exists_row_norm_eq (M : M2) : ∃ i, ‖M‖ = ‖M i 0‖ + ‖M i 1‖ := by
  obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin 2))
    Finset.univ_nonempty (fun i : Fin 2 => ∑ j : Fin 2, ‖M i j‖₊)
  refine ⟨i, ?_⟩
  have h : ‖M‖₊ = ∑ j : Fin 2, ‖M i j‖₊ := by rw [Matrix.linfty_opNNNorm_def, hi]
  have h' : ((‖M‖₊ : NNReal) : ℝ) = ((∑ j : Fin 2, ‖M i j‖₊ : NNReal) : ℝ) := by rw [h]
  simpa [Fin.sum_univ_two] using h'

lemma mul_conj_div_norm (a : ℂ) : a * ((starRingEnd ℂ) a / (‖a‖ : ℂ)) = (‖a‖ : ℂ) := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · have hn : (‖a‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 ha
    rw [← mul_div_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq, div_eq_iff hn]
    push_cast
    ring

lemma norm_conj_div_norm_le (a : ℂ) : ‖(starRingEnd ℂ) a / (‖a‖ : ℂ)‖ ≤ 1 := by
  have : ‖(starRingEnd ℂ) a / (‖a‖ : ℂ)‖ = ‖a‖ / ‖a‖ := by simp
  rw [this]
  exact div_self_le_one _

/-- Sub-mean-value property of `log ‖F‖` for a holomorphic matrix function with `‖F‖ ≥ 1`. -/
lemma log_norm_le_circleAverage {δ : ℝ} {F : ℂ → M2} (hF : DifferentiableOn ℂ F (strip δ))
    (hF1 : ∀ z ∈ strip δ, 1 ≤ ‖F z‖) {c : ℂ} {r : ℝ} (hr : 0 < r) (hc : |c.im| + r < δ) :
    Real.log ‖F c‖ ≤ Real.circleAverage (fun z => Real.log ‖F z‖) c r := by
  have hball : Metric.closedBall c |r| ⊆ strip δ := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm, abs_of_pos hr] at hz
    have h1 : |z.im - c.im| ≤ ‖z - c‖ := by
      simpa using Complex.abs_im_le_norm (z - c)
    have h2 : |z.im| ≤ |c.im| + |z.im - c.im| := by
      have := abs_add_le c.im (z.im - c.im)
      simpa using this
    show |z.im| < δ
    linarith
  have hcs : c ∈ strip δ := hball (Metric.mem_closedBall_self (abs_nonneg r))
  obtain ⟨i, hi⟩ := exists_row_norm_eq (F c)
  set v : Fin 2 → ℂ := fun j => (starRingEnd ℂ) (F c i j) / (‖F c i j‖ : ℂ) with hv
  set h : ℂ → ℂ := fun z => entryCLM i 0 (F z) * v 0 + entryCLM i 1 (F z) * v 1 with hh
  have hdiff : DifferentiableOn ℂ h (strip δ) :=
    (((entryCLM i 0).differentiable.comp_differentiableOn hF).mul_const _).add
      (((entryCLM i 1).differentiable.comp_differentiableOn hF).mul_const _)
  have han : AnalyticOnNhd ℂ h (Metric.closedBall c |r|) :=
    (hdiff.analyticOnNhd (isOpen_strip δ)).mono hball
  have hhc : h c = ((‖F c‖ : ℝ) : ℂ) := by
    simp only [hh, hv, entryCLM_apply, mul_conj_div_norm, hi]
    push_cast
    ring
  have hhle : ∀ z, ‖h z‖ ≤ ‖F z‖ := by
    intro z
    simp only [hh, entryCLM_apply]
    calc ‖F z i 0 * v 0 + F z i 1 * v 1‖ ≤ ‖F z i 0‖ * ‖v 0‖ + ‖F z i 1‖ * ‖v 1‖ := by
          refine (norm_add_le _ _).trans ?_
          rw [norm_mul, norm_mul]
      _ ≤ ‖F z i 0‖ * 1 + ‖F z i 1‖ * 1 := by
          gcongr
          · exact norm_conj_div_norm_le _
          · exact norm_conj_div_norm_le _
      _ ≤ ‖F z‖ := by simpa using row_sum_le_norm (F z) i
  have hnc : ‖h c‖ = ‖F c‖ := by
    rw [hhc, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  have hc0 : h c ≠ 0 := by
    intro h0
    have := hF1 c hcs
    rw [← hnc, h0, norm_zero] at this
    linarith
  have jensen := han.circleAverage_log_norm hr.ne' hc0
  have hsum : 0 ≤ ∑ᶠ u, MeromorphicOn.divisor h (Metric.closedBall c |r|) u *
      Real.log (r * ‖c - u‖⁻¹) := by
    apply finsum_nonneg
    intro u
    by_cases hu : u ∈ Metric.closedBall c |r|
    · apply mul_nonneg
      · exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg han u
      · rcases eq_or_ne ‖c - u‖ 0 with h0 | h0
        · simp [h0]
        · apply Real.log_nonneg
          rw [Metric.mem_closedBall, dist_eq_norm, abs_of_pos hr, norm_sub_rev] at hu
          rw [← div_eq_mul_inv, le_div_iff₀ (lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0))]
          linarith
    · simp [Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hu]
  have hint1 : CircleIntegrable (fun z => Real.log ‖h z‖) c r :=
    (han.mono Metric.sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
  have hcontu : ContinuousOn (fun z => Real.log ‖F z‖) (strip δ) :=
    hF.continuousOn.norm.log (fun z hz => (zero_lt_one.trans_le (hF1 z hz)).ne')
  have hint2 : CircleIntegrable (fun z => Real.log ‖F z‖) c r :=
    ContinuousOn.circleIntegrable' (hcontu.mono (Metric.sphere_subset_closedBall.trans hball))
  have hmono : Real.circleAverage (fun z => Real.log ‖h z‖) c r ≤
      Real.circleAverage (fun z => Real.log ‖F z‖) c r := by
    apply Real.circleAverage_mono hint1 hint2
    intro z hz
    have hzs : z ∈ strip δ := hball (Metric.sphere_subset_closedBall hz)
    rcases eq_or_ne (h z) 0 with h0 | h0
    · simp only [h0, norm_zero, Real.log_zero]
      exact Real.log_nonneg (hF1 z hzs)
    · exact Real.log_le_log (norm_pos_iff.2 h0) (hhle z)
  rw [← hnc]
  rw [jensen] at hmono
  linarith

/-- Horizontal averages of a periodic function with the sub-mean property satisfy a
one-dimensional sub-mean property. -/
lemma submean_horizontal {δ : ℝ} {u : ℂ → ℝ} (hu : ContinuousOn u (strip δ))
    (hper : ∀ z, u (z + 1) = u z)
    (hsub : ∀ c : ℂ, ∀ r : ℝ, 0 < r → |c.im| + r < δ → u c ≤ Real.circleAverage u c r)
    (t r : ℝ) (hr : 0 < r) (h1 : -δ < t - r) (h2 : t + r < δ) :
    (∫ x in (0 : ℝ)..1, u (x + t * I)) ≤ (2 * Real.pi)⁻¹ *
      ∫ θ in (0 : ℝ)..2 * Real.pi,
        ∫ x in (0 : ℝ)..1, u (x + ((t + r * Real.sin θ : ℝ) : ℂ) * I) := by
  have htr : |t| + r < δ := by
    rcases abs_cases t with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
  set G : ℝ → ℝ → ℝ := fun x θ => u (circleMap ((x : ℂ) + t * I) r θ) with hG
  have hcm : ∀ x θ : ℝ, circleMap ((x : ℂ) + t * I) r θ =
      ((x + r * Real.cos θ : ℝ) : ℂ) + ((t + r * Real.sin θ : ℝ) : ℂ) * I := by
    intro x θ
    apply Complex.ext <;>
      simp [circleMap, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
        Complex.cos_ofReal_re, Complex.sin_ofReal_re]
  have hmemS : ∀ x θ : ℝ,
      ((x + r * Real.cos θ : ℝ) : ℂ) + ((t + r * Real.sin θ : ℝ) : ℂ) * I ∈ strip δ := by
    intro x θ
    apply mem_strip_shift
    have h3 := Real.neg_one_le_sin θ
    have h4 := Real.sin_le_one θ
    rw [abs_lt]
    constructor <;> nlinarith
  have hGc : Continuous (Function.uncurry G) := by
    have : Function.uncurry G = fun p : ℝ × ℝ =>
        u (((p.1 + r * Real.cos p.2 : ℝ) : ℂ) + ((t + r * Real.sin p.2 : ℝ) : ℂ) * I) := by
      funext p
      simp only [Function.uncurry, hG, hcm]
    rw [this]
    exact hu.comp_continuous (by fun_prop) (fun p => hmemS p.1 p.2)
  have ht : |t| < δ := by linarith
  have hline : Continuous fun x : ℝ => u ((x : ℂ) + t * I) :=
    hu.comp_continuous (by fun_prop) (mem_strip_shift ht)
  calc (∫ x in (0 : ℝ)..1, u (x + t * I))
      ≤ ∫ x in (0 : ℝ)..1, (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, G x θ := by
        apply intervalIntegral.integral_mono_on zero_le_one (hline.intervalIntegrable _ _)
        · exact (continuous_const.mul
            (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hGc _ _)
            ).intervalIntegrable _ _
        · intro x _
          have := hsub ((x : ℂ) + t * I) r hr (by simpa using htr)
          rw [Real.circleAverage_def, smul_eq_mul] at this
          exact this
    _ = (2 * Real.pi)⁻¹ * ∫ θ in (0 : ℝ)..2 * Real.pi, ∫ x in (0 : ℝ)..1, G x θ := by
        rw [intervalIntegral.integral_const_mul,
          MeasureTheory.intervalIntegral_intervalIntegral_swap]
        exact (hGc.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_uIcc)).mono_set
          (prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)
    _ = _ := by
        congr 1
        apply intervalIntegral.integral_congr
        intro θ _
        set g : ℝ → ℝ := fun y => u ((y : ℂ) + ((t + r * Real.sin θ : ℝ) : ℂ) * I) with hg
        have hgp : Function.Periodic g 1 := by
          intro y
          show u (((y + 1 : ℝ) : ℂ) + _) = u ((y : ℂ) + _)
          rw [Complex.ofReal_add, Complex.ofReal_one, add_right_comm, hper]
        have hGg : ∀ x, G x θ = g (x + r * Real.cos θ) := by
          intro x
          simp only [hG, hg, hcm]
        show ∫ x in (0 : ℝ)..1, G x θ = ∫ x in (0 : ℝ)..1, g x
        simp_rw [hGg]
        rw [intervalIntegral.integral_comp_add_right, zero_add,
          show (1 : ℝ) + r * Real.cos θ = r * Real.cos θ + 1 by ring,
          hgp.intervalIntegral_add_eq (r * Real.cos θ) 0, zero_add]

lemma continuousOn_horizontal {δ : ℝ} {u : ℂ → ℝ} (hu : ContinuousOn u (strip δ)) :
    ContinuousOn (fun t : ℝ => ∫ x in (0 : ℝ)..1, u (x + t * I)) (Ioo (-δ) δ) := by
  intro t0 ht0
  have hη : |t0| < δ := abs_lt.2 ht0
  set η := (|t0| + δ) / 2 with hηdef
  have hη1 : |t0| < η := by linarith
  have hη2 : η < δ := by linarith
  set cl : ℝ → ℝ := fun s => max (-η) (min η s) with hcl
  have hclc : Continuous cl := continuous_const.max (continuous_const.min continuous_id)
  have hcl_mem : ∀ s, |cl s| < δ := by
    intro s
    rw [abs_lt]
    constructor
    · exact lt_of_lt_of_le (by linarith) (le_max_left _ _)
    · exact lt_of_le_of_lt (max_le (by linarith [abs_nonneg t0]) (min_le_left _ _)) hη2
  have hcont : Continuous fun s : ℝ => ∫ x in (0 : ℝ)..1, u (x + (cl s : ℂ) * I) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    show Continuous fun p : ℝ × ℝ => u ((p.2 : ℂ) + (cl p.1 : ℂ) * I)
    exact hu.comp_continuous (by fun_prop) (fun p => mem_strip_shift (hcl_mem p.1) p.2)
  have heq : (fun s : ℝ => ∫ x in (0 : ℝ)..1, u (x + (cl s : ℂ) * I)) =ᶠ[𝓝 t0]
      fun s : ℝ => ∫ x in (0 : ℝ)..1, u (x + s * I) := by
    have : Ioo (-η) η ∈ 𝓝 t0 :=
      Ioo_mem_nhds (by linarith [neg_abs_le t0]) (by linarith [le_abs_self t0])
    filter_upwards [this] with s hs
    have : cl s = s := by
      simp only [hcl]
      rw [min_eq_right hs.2.le, max_eq_right hs.1.le]
    rw [this]
  exact (hcont.continuousAt.congr heq).continuousWithinAt


/-- `ε ↦ ∫₀¹ log ‖A_n(x + iε)‖ dx` is convex on the strip. -/
lemma IsAnalyticCocycle.convexOn_lyapSeq {δ : ℝ} {A : ℂ → M2} (hA : IsAnalyticCocycle δ A)
    (α : ℝ) (n : ℕ) : ConvexOn ℝ (Ioo (-δ) δ) (fun ε => lyapSeq α (shift A ε) n) := by
  set u : ℂ → ℝ := fun z => Real.log ‖cIter α A n z‖ with hu
  have hF := hA.cIter_diff α n
  have hF1 : ∀ z ∈ strip δ, 1 ≤ ‖cIter α A n z‖ := fun z hz =>
    one_le_norm_of_det_eq_one (hA.cIter_det α n hz)
  have huc : ContinuousOn u (strip δ) :=
    hF.continuousOn.norm.log (fun z hz => (zero_lt_one.trans_le (hF1 z hz)).ne')
  have hper : ∀ z, u (z + 1) = u z := fun z => by simp only [hu, hA.cIter_periodic]
  have hsub : ∀ c : ℂ, ∀ r : ℝ, 0 < r → |c.im| + r < δ → u c ≤ Real.circleAverage u c r :=
    fun c r hr hc => log_norm_le_circleAverage hF hF1 hr hc
  have heq : (fun ε => lyapSeq α (shift A ε) n) =
      fun ε : ℝ => ∫ x in (0 : ℝ)..1, u (x + ε * I) := by
    funext ε
    simp only [lyapSeq, iter_shift_eq, hu]
  rw [heq]
  apply convexOn_of_submean (continuousOn_horizontal huc)
  intro t r hr h1 h2
  exact submean_horizontal huc hper hsub t r hr h1 h2

/-- Convexity of `ε ↦ L(α, A_ε)` on the strip of analyticity (§1.2). -/
theorem L_convexOn {δ : ℝ} {A : ℂ → M2} (hA : IsAnalyticCocycle δ A) (α : ℝ) :
    ConvexOn ℝ (Ioo (-δ) δ) (L α A) := by
  refine convexOn_of_tendsto (convex_Ioo _ _)
    (g := fun n ε => lyapSeq α (shift A ε) n / n) (fun n => ?_)
    (fun ε hε => hA.tendsto_L α (abs_lt.2 hε))
  have := (hA.convexOn_lyapSeq α n).smul (inv_nonneg.2 (Nat.cast_nonneg (α := ℝ) n))
  simpa [div_eq_inv_mul, smul_eq_mul] using this

/-! ### The hypotheses that are not formalized

The class `Hypotheses` collects, as *stated but not asserted* propositions, the inputs of the
paper that are not proved in this formalization:

* `jks` — **Theorem [JKS]** (Bourgain–Jitomirskaya [BJ1], Jitomirskaya–Koslover–Schulteis
  [JKS]): continuity of `(α, A) ↦ L(α, A)` at irrational `α`, jointly, for `αₙ → α` (arbitrary
  reals) and `Aₙ → A` uniformly on a strip.  (The paper's Theorem `con` is the case `Aₙ = A`.)
* `uhSmooth` — the property of uniformly hyperbolic cocycles quoted in §1.2 from normally
  hyperbolic theory [HPS]: on `𝒰ℋ` the Lyapunov exponent is `C^∞` jointly in the frequency and
  the parameters.  (Real-analytic dependence at fixed frequency is proved in `UHAnalytic.lean`.)

Every theorem that depends on one of these carries the instance argument `[Hypotheses]` in its
statement. -/

/-- The unformalized inputs (see the section docstring). -/
class Hypotheses : Prop where
  /-- **Theorem [JKS]**. -/
  jks : ∀ {δ : ℝ} {A : ℂ → M2}, IsAnalyticCocycle δ A → ∀ {α : ℝ}, Irrational α →
    ∀ {αs : ℕ → ℝ} {As : ℕ → ℂ → M2}, (∀ n, IsAnalyticCocycle δ (As n)) →
      Tendsto αs atTop (𝓝 α) → TendstoUniformlyOn As A atTop (strip δ) →
        Tendsto (fun n => L (αs n) (As n) 0) atTop (𝓝 (L α A 0))
  /-- `C^∞` dependence on `𝒰ℋ`, jointly in the frequency and the parameters [HPS]. -/
  uhSmooth : ∀ {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {δ : ℝ} {U : Set P}
    {A : P → ℂ → M2}, IsAnalyticCocycleFamily δ U A → ∀ {α₀ : ℝ} {p₀ : P}, p₀ ∈ U →
      UH α₀ (A p₀) →
        ∃ W ∈ 𝓝 (α₀, p₀), ContDiffOn ℝ ∞ (fun q : ℝ × P => L q.1 (A q.2) 0) W

section Hypotheses

variable [H : Hypotheses]
include H

/-- **Theorem [JKS]** (continuity of the Lyapunov exponent at irrational frequencies). -/
theorem jks_continuity {δ : ℝ} {A : ℂ → M2} (hA : IsAnalyticCocycle δ A) {α : ℝ}
    (hα : Irrational α) {αs : ℕ → ℝ} {As : ℕ → ℂ → M2} (hAs : ∀ n, IsAnalyticCocycle δ (As n))
    (hαs : Tendsto αs atTop (𝓝 α)) (hconv : TendstoUniformlyOn As A atTop (strip δ)) :
    Tendsto (fun n => L (αs n) (As n) 0) atTop (𝓝 (L α A 0)) :=
  H.jks hA hα hAs hαs hconv

/-- `C^∞` dependence on `𝒰ℋ`, jointly in the frequency and the parameters. -/
theorem uh_smooth_family {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {δ : ℝ}
    {U : Set P} {A : P → ℂ → M2} (hA : IsAnalyticCocycleFamily δ U A) {α₀ : ℝ} {p₀ : P}
    (hp₀ : p₀ ∈ U) (hUH : UH α₀ (A p₀)) :
    ∃ W ∈ 𝓝 (α₀, p₀), ContDiffOn ℝ ∞ (fun q : ℝ × P => L q.1 (A q.2) 0) W :=
  H.uhSmooth hA hp₀ hUH

end Hypotheses

end AvilaGlobal
