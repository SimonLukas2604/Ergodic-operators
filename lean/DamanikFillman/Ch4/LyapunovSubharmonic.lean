/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §4.5 Subharmonicity of the Lyapunov exponent   (book pp. 327–331)

We use the notion of subharmonic function `DF.SubharmonicOn` / `DF.Subharmonic` from
`DamanikFillman/AppA/Subharmonic.lean` (Definition 4.5.1; functions `ℂ → ℝ ∪ {-∞}` are modelled
as `EReal`-valued functions).

## Main results
* `DF.log_norm_le_circleAverage_matrix`, `DF.subharmonic_log_norm_matrix` —
  **Proposition 4.5.2(a)** for `2 × 2` matrices with entire entries and `‖M(z)‖ ≥ 1` (e.g.
  `SL(2, ℂ)`-valued): `z ↦ log ‖M(z)‖` is subharmonic.  As in the book, the proof writes
  `log ‖M(z)‖` as a supremum of the subharmonic functions `log |⟨v, M(z) w⟩|`.
* `DF.continuous_integral_of_locally_bdd`, `DF.integral_le_circleAverage_integral` —
  **Proposition 4.5.2(b)** (in the version needed here: `G(·, x)` continuous and satisfying the
  sub-mean value inequality, `|G|` locally bounded): `z ↦ ∫ G(z, x) dν(x)` is continuous and
  satisfies the sub-mean value inequality (Fubini).
* `E.subharmonic_integral_log_norm_An` — `z ↦ E(log ‖A^n_z‖)` is subharmonic.
* `E.subharmonic_lyap` — **Theorem 4.5.3**: the Lyapunov exponent is subharmonic.  As in the
  book, `L = inf_N 2^{-N} E log ‖A^{2^N}_z‖` is a decreasing limit of continuous subharmonic
  functions (Proposition 4.5.2(c), `DF.subharmonicOn_iInf` of Appendix A).
* `E.upperSemicontinuous_lyap` — `L` is upper semicontinuous (p. 327).

## Deviations
* Proposition 4.5.2(b) is proved for continuous (rather than upper semicontinuous) integrands
  with locally bounded absolute value, which covers the application to `log ‖A^n_z(ω)‖`.

No `Statement` props are introduced in this file.
-/
import DamanikFillman.Ch4.Lyapunov
import DamanikFillman.AppA.Subharmonic

noncomputable section

open scoped Matrix.Norms.L2Operator InnerProductSpace ComplexConjugate
open MeasureTheory Set Filter Topology Matrix Real Metric

namespace DF

/-! ### Proposition 4.5.2(a) -/

lemma inner_toEuclideanCLM_eq_sum (M : Matrix (Fin 2) (Fin 2) ℂ)
    (x y : EuclideanSpace ℂ (Fin 2)) :
    ⟪y, Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) M x⟫_ℂ =
      ∑ i, ∑ j, conj (y i) * (M i j * x j) := by
  rw [show x = WithLp.toLp 2 (WithLp.ofLp x) from rfl, Matrix.toEuclideanCLM_toLp]
  simp [PiLp.inner_apply, Fin.sum_univ_two, Matrix.mulVec, dotProduct]
  ring

lemma continuous_of_entries {M : ℂ → Matrix (Fin 2) (Fin 2) ℂ}
    (hM : ∀ i j, Continuous fun z => M z i j) : Continuous M :=
  continuous_pi fun i => continuous_pi fun j => hM i j

/-- **Proposition 4.5.2(a)** (sub-mean value inequality): if the entries of `M : ℂ → M₂(ℂ)` are
entire and `‖M(z)‖ ≥ 1`, then `log ‖M(c)‖ ≤ (2π)⁻¹ ∫ log ‖M(c + r e^{iθ})‖ dθ`. -/
theorem log_norm_le_circleAverage_matrix {M : ℂ → Matrix (Fin 2) (Fin 2) ℂ}
    (hM : ∀ i j, Differentiable ℂ fun z => M z i j) (h1 : ∀ z, 1 ≤ ‖M z‖) (c : ℂ) {r : ℝ}
    (hr : 0 < r) : Real.log ‖M c‖ ≤ circleAverage (fun z => Real.log ‖M z‖) c r := by
  have hcont : Continuous M := continuous_of_entries fun i j => (hM i j).continuous
  have hlogc : Continuous fun z => Real.log ‖M z‖ :=
    hcont.norm.log fun z => by linarith [h1 z]
  have hint : CircleIntegrable (fun z => Real.log ‖M z‖) c r :=
    hlogc.continuousOn.circleIntegrable'
  set X := circleAverage (fun z => Real.log ‖M z‖) c r
  have key : ∀ s, 0 < s → s < ‖M c‖ → Real.log s ≤ X := by
    intro s hs hsM
    set A := Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (M c)
    have hA : ‖A‖ = ‖M c‖ := l2_opNorm_toEuclideanCLM _
    obtain ⟨x, hx1, hxs⟩ := A.exists_lt_apply_of_lt_opNorm (hA ▸ hsM)
    set y := A x
    set a := ‖y‖
    have ha : 0 < a := hs.trans hxs
    set g : ℂ → ℂ := fun z => ⟪y, Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (M z) x⟫_ℂ / a
      with hgdef
    have hg : Differentiable ℂ g := by
      have : g = fun z => (∑ i, ∑ j, conj (y i) * (M z i j * x j)) / a := by
        funext z; exact congrArg (· / (a : ℂ)) (inner_toEuclideanCLM_eq_sum (M z) x y)
      rw [this]
      refine Differentiable.div_const ?_ _
      refine Differentiable.fun_sum fun i _ => Differentiable.fun_sum fun j _ => ?_
      exact ((hM i j).mul_const _).const_mul _
    have hgc : ‖g c‖ = a := by
      simp only [hgdef, norm_div, Complex.norm_real, Real.norm_eq_abs]
      rw [show Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (M c) x = y from rfl,
        inner_self_eq_norm_sq_to_K, abs_of_pos ha]
      rw [norm_pow, RCLike.norm_ofReal, abs_of_pos ha]
      field_simp
    have hgle : ∀ z, Real.log ‖g z‖ ≤ Real.log ‖M z‖ := by
      intro z
      by_cases hz : g z = 0
      · rw [hz, norm_zero, Real.log_zero]; exact Real.log_nonneg (h1 z)
      · apply Real.log_le_log (norm_pos_iff.2 hz)
        simp only [hgdef, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
        rw [div_le_iff₀ ha]
        calc ‖⟪y, Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (M z) x⟫_ℂ‖
            ≤ ‖y‖ * ‖Matrix.toEuclideanCLM (n := Fin 2) (𝕜 := ℂ) (M z) x‖ := norm_inner_le_norm _ _
          _ ≤ ‖y‖ * (‖M z‖ * ‖x‖) := by
              gcongr
              rw [← l2_opNorm_toEuclideanCLM]
              exact ContinuousLinearMap.le_opNorm _ _
          _ ≤ ‖y‖ * (‖M z‖ * 1) := by gcongr
          _ = ‖M z‖ * a := by ring
    have hgan : AnalyticOnNhd ℂ g (closedBall c r) := fun z _ => hg.analyticAt z
    have hJ := log_norm_le_circleAverage hr hgan (by rw [← norm_ne_zero_iff, hgc]; exact ha.ne')
    have hgint : CircleIntegrable (fun z => Real.log ‖g z‖) c r := by
      have h1' : AnalyticOnNhd ℂ g (closedBall c |r|) := fun z _ => hg.analyticAt z
      exact (h1'.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm
    calc Real.log s ≤ Real.log ‖g c‖ := Real.log_le_log hs (hgc ▸ hxs.le)
      _ ≤ circleAverage (fun w => Real.log ‖g w‖) c r := hJ
      _ ≤ X := circleAverage_mono hgint hint fun z _ => hgle z
  by_contra hlt
  push Not at hlt
  have hMc : 0 < ‖M c‖ := lt_of_lt_of_le one_pos (h1 c)
  set s := Real.exp ((X + Real.log ‖M c‖) / 2)
  have hs1 : s < ‖M c‖ := by
    rw [← Real.exp_log hMc]; exact Real.exp_lt_exp.2 (by linarith)
  have := key s (Real.exp_pos _) hs1
  rw [Real.log_exp] at this
  linarith

/-- **Proposition 4.5.2(a)**: `z ↦ log ‖M(z)‖` is subharmonic for `M` with entire entries and
`‖M(z)‖ ≥ 1` (e.g. `det M(z) = 1`). -/
theorem subharmonic_log_norm_matrix {M : ℂ → Matrix (Fin 2) (Fin 2) ℂ}
    (hM : ∀ i j, Differentiable ℂ fun z => M z i j) (h1 : ∀ z, 1 ≤ ‖M z‖) :
    Subharmonic (fun z => ((Real.log ‖M z‖ : ℝ) : EReal)) := by
  have hcont : Continuous M := continuous_of_entries fun i j => (hM i j).continuous
  have hlogc : Continuous fun z => Real.log ‖M z‖ :=
    hcont.norm.log fun z => by linarith [h1 z]
  refine (subharmonicOn_coe_iff fun c r _ _ => hlogc.continuousOn.circleIntegrable').2
    ⟨hlogc.continuousOn.upperSemicontinuousOn, fun c r hr _ =>
      log_norm_le_circleAverage_matrix hM h1 c hr⟩

/-! ### Proposition 4.5.2(b): averages of subharmonic functions -/

section Average

variable {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν]
  {G : ℂ → X → ℝ}

/-- Continuity of parameter integrals with locally bounded integrand. -/
theorem continuous_integral_of_locally_bdd (hcont : ∀ x, Continuous fun z => G z x)
    (hmeas : ∀ z, Measurable (G z))
    (hbdd : ∀ c : ℂ, ∀ R : ℝ, ∃ C, ∀ z ∈ closedBall c R, ∀ x, |G z x| ≤ C) :
    Continuous fun z => ∫ x, G z x ∂ν := by
  rw [continuous_iff_continuousAt]
  intro z₀
  obtain ⟨C, hC⟩ := hbdd z₀ 1
  refine continuousAt_of_dominated (bound := fun _ => C)
    (Eventually.of_forall fun z => (hmeas z).aestronglyMeasurable) ?_ (integrable_const C)
    (ae_of_all _ fun x => (hcont x).continuousAt)
  filter_upwards [closedBall_mem_nhds z₀ one_pos] with z hz
  exact ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC z hz x

lemma measurable_uncurry_circle (hcont : ∀ x, Continuous fun z => G z x)
    (hmeas : ∀ z, Measurable (G z)) (c : ℂ) (r : ℝ) :
    Measurable (Function.uncurry fun θ x => G (circleMap c r θ) x) :=
  measurable_uncurry_of_continuous_of_measurable
    (fun x => (hcont x).comp (continuous_circleMap c r)) (fun θ => hmeas _)

/-- Fubini for circle averages of parameter integrals. -/
theorem circleAverage_integral (hcont : ∀ x, Continuous fun z => G z x)
    (hmeas : ∀ z, Measurable (G z))
    (hbdd : ∀ c : ℂ, ∀ R : ℝ, ∃ C, ∀ z ∈ closedBall c R, ∀ x, |G z x| ≤ C) (c : ℂ) (r : ℝ) :
    circleAverage (fun z => ∫ x, G z x ∂ν) c r = ∫ x, circleAverage (fun z => G z x) c r ∂ν := by
  obtain ⟨C, hC⟩ := hbdd c |r|
  have hmem : ∀ θ, circleMap c r θ ∈ closedBall c |r| := fun θ =>
    sphere_subset_closedBall (circleMap_mem_sphere' c r θ)
  have hu := measurable_uncurry_circle hcont hmeas c r
  have hint : Integrable (Function.uncurry fun θ x => G (circleMap c r θ) x)
      ((volume.restrict (Ioc 0 (2 * π))).prod ν) := by
    refine (integrable_const C).mono' hu.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs]; exact hC _ (hmem p.1) p.2
  simp only [circleAverage, smul_eq_mul]
  rw [integral_const_mul]
  congr 1
  rw [intervalIntegral.integral_of_le (by positivity)]
  simp_rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
  exact integral_integral_swap hint

/-- **Proposition 4.5.2(b)** (sub-mean value inequality for averages). -/
theorem integral_le_circleAverage_integral (hcont : ∀ x, Continuous fun z => G z x)
    (hmeas : ∀ z, Measurable (G z))
    (hbdd : ∀ c : ℂ, ∀ R : ℝ, ∃ C, ∀ z ∈ closedBall c R, ∀ x, |G z x| ≤ C) (c : ℂ) (r : ℝ)
    (hsub : ∀ x, G c x ≤ circleAverage (fun z => G z x) c r) :
    ∫ x, G c x ∂ν ≤ circleAverage (fun z => ∫ x, G z x ∂ν) c r := by
  rw [circleAverage_integral ν hcont hmeas hbdd c r]
  obtain ⟨C, hC⟩ := hbdd c |r|
  have hmem : ∀ θ, circleMap c r θ ∈ closedBall c |r| := fun θ =>
    sphere_subset_closedBall (circleMap_mem_sphere' c r θ)
  have h1 : Integrable (G c) ν :=
    (integrable_const C).mono' (hmeas c).aestronglyMeasurable (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs]; exact hC c (mem_closedBall_self (abs_nonneg r)) x)
  have hu := measurable_uncurry_circle hcont hmeas c r
  have hm2 : StronglyMeasurable fun x => ∫ θ, (Function.uncurry fun θ x =>
      G (circleMap c r θ) x) (θ, x) ∂(volume.restrict (Ioc 0 (2 * π))) :=
    hu.stronglyMeasurable.integral_prod_left
  have h2 : Integrable (fun x => circleAverage (fun z => G z x) c r) ν := by
    refine (integrable_const C).mono' ?_ (ae_of_all _ fun x => ?_)
    · have : (fun x => circleAverage (fun z => G z x) c r) = fun x => (2 * π)⁻¹ *
          ∫ θ, (Function.uncurry fun θ x => G (circleMap c r θ) x) (θ, x)
            ∂(volume.restrict (Ioc 0 (2 * π))) := by
        funext x
        simp only [circleAverage, smul_eq_mul, Function.uncurry_apply_pair]
        rw [intervalIntegral.integral_of_le (by positivity)]
      rw [this]
      exact (hm2.const_mul _).aestronglyMeasurable
    · have hci : CircleIntegrable (fun z => G z x) c r :=
        (hcont x).continuousOn.circleIntegrable'
      have hb1 := circleAverage_mono hci (circleIntegrable_const C c r)
        (fun z hz => (abs_le.1 (hC z (sphere_subset_closedBall hz) x)).2)
      have hb2 := circleAverage_mono (circleIntegrable_const (-C) c r) hci
        (fun z hz => (abs_le.1 (hC z (sphere_subset_closedBall hz) x)).1)
      rw [circleAverage_const] at hb1 hb2
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨hb2, hb1⟩
  exact integral_mono h1 h2 hsub

end Average

/-! ### Theorem 4.5.3 -/

namespace ErgodicFamily

variable {Ω : Type*} [MeasurableSpace Ω] (E : ErgodicFamily Ω)

lemma differentiable_An_entry (n : ℕ) (ω : Ω) (i j : Fin 2) :
    Differentiable ℂ fun z => E.An z n ω i j := by
  induction n generalizing i j with
  | zero =>
    show Differentiable ℂ fun _ => (1 : Cocycle.M2) i j
    exact differentiable_const _
  | succ n ih =>
    simp only [An_succ, Matrix.mul_apply, Fin.sum_univ_two]
    have hAz : ∀ i k, Differentiable ℂ fun z => E.Az z ((⇑E.T)^[n] ω) i k := by
      intro i k; fin_cases i <;> fin_cases k <;> simp [Az, transfer] <;> fun_prop
    exact ((hAz i 0).mul (ih 0 j)).add ((hAz i 1).mul (ih 1 j))

lemma continuous_log_norm_An (n : ℕ) (ω : Ω) :
    Continuous fun z => Real.log ‖E.An z n ω‖ :=
  (continuous_of_entries fun i j => (E.differentiable_An_entry n ω i j).continuous).norm.log
    fun z => by linarith [E.one_le_norm_An z n ω]

lemma abs_log_norm_An_le_ball (n : ℕ) (c : ℂ) (R : ℝ) :
    ∃ C, ∀ z ∈ closedBall c R, ∀ ω, |Real.log ‖E.An z n ω‖| ≤ C := by
  refine ⟨n * Real.log (‖c‖ + |R| + E.fBound + 1), fun z hz ω => ?_⟩
  rw [abs_of_nonneg (E.log_norm_An_nonneg z n ω)]
  refine (E.log_norm_An_le z n ω).trans ?_
  have hf := E.fBound_nonneg
  have hz' : ‖z‖ ≤ ‖c‖ + |R| := by
    rw [mem_closedBall, dist_eq_norm] at hz
    have := norm_sub_norm_le z c
    linarith [le_abs_self R]
  gcongr

/-- The averaged quantity `z ↦ E(log ‖A^n_z‖)`. -/
def avgLogNorm (n : ℕ) (z : ℂ) : ℝ := ∫ ω, Real.log ‖E.An z n ω‖ ∂E.μ

lemma continuous_avgLogNorm (n : ℕ) : Continuous (E.avgLogNorm n) :=
  continuous_integral_of_locally_bdd E.μ (E.continuous_log_norm_An n)
    (fun z => (E.measurable_An z n).norm.log) (E.abs_log_norm_An_le_ball n)

lemma avgLogNorm_le_circleAverage (n : ℕ) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    E.avgLogNorm n c ≤ circleAverage (E.avgLogNorm n) c r :=
  integral_le_circleAverage_integral E.μ (E.continuous_log_norm_An n)
    (fun z => (E.measurable_An z n).norm.log) (E.abs_log_norm_An_le_ball n) c r
    (fun ω => log_norm_le_circleAverage_matrix (E.differentiable_An_entry n ω)
      (fun z => E.one_le_norm_An z n ω) c hr)

/-- `z ↦ E(log ‖A^n_z(ω)‖)` is subharmonic (Proposition 4.5.2(a),(b)). -/
theorem subharmonic_avgLogNorm (n : ℕ) :
    Subharmonic (fun z => ((E.avgLogNorm n z : ℝ) : EReal)) :=
  (subharmonicOn_coe_iff fun c r _ _ => (E.continuous_avgLogNorm n).continuousOn.circleIntegrable').2
    ⟨(E.continuous_avgLogNorm n).continuousOn.upperSemicontinuousOn,
      fun c r hr _ => E.avgLogNorm_le_circleAverage n c hr⟩

lemma integral_comp_iterate {g : Ω → ℝ} (hg : Measurable g) (m : ℕ) :
    ∫ ω, g ((⇑E.T)^[m] ω) ∂E.μ = ∫ ω, g ω ∂E.μ := by
  have hmp : MeasurePreserving ((⇑E.T)^[m]) E.μ E.μ := E.measurePreserving_T.iterate m
  have := integral_map (μ := E.μ) hmp.measurable.aemeasurable (f := g) hg.aestronglyMeasurable
  rw [hmp.map_eq] at this
  exact this.symm

/-- Subadditivity: `E log ‖A^{2m}_z‖ ≤ 2 E log ‖A^m_z‖`. -/
lemma avgLogNorm_two_mul_le (m : ℕ) (z : ℂ) :
    E.avgLogNorm (m + m) z ≤ 2 * E.avgLogNorm m z := by
  unfold avgLogNorm
  have hle : ∀ ω, Real.log ‖E.An z (m + m) ω‖ ≤
      Real.log ‖E.An z m ((⇑E.T)^[m] ω)‖ + Real.log ‖E.An z m ω‖ := by
    intro ω
    rw [E.An_add]
    have h1 := E.one_le_norm_An z m ((⇑E.T)^[m] ω)
    have h2 := E.one_le_norm_An z m ω
    rw [← Real.log_mul (by positivity) (by positivity)]
    refine Real.log_le_log ?_ (norm_mul_le _ _)
    have := E.one_le_norm_An z (m + m) ω
    rw [E.An_add] at this
    linarith
  have hint := E.integrable_log_norm_An z m
  have hint' : Integrable (fun ω => Real.log ‖E.An z m ((⇑E.T)^[m] ω)‖) E.μ :=
    (E.measurePreserving_T.iterate m).integrable_comp_of_integrable hint
  calc ∫ ω, Real.log ‖E.An z (m + m) ω‖ ∂E.μ
      ≤ ∫ ω, (Real.log ‖E.An z m ((⇑E.T)^[m] ω)‖ + Real.log ‖E.An z m ω‖) ∂E.μ :=
        integral_mono (E.integrable_log_norm_An z _) (hint'.add hint) hle
    _ = 2 * ∫ ω, Real.log ‖E.An z m ω‖ ∂E.μ := by
        rw [integral_add hint' hint,
          E.integral_comp_iterate (g := fun ω => Real.log ‖E.An z m ω‖)
            (E.measurable_An z m).norm.log]
        ring

/-- The dyadic approximants `F_N(z) = 2^{-N} E log ‖A^{2^N}_z‖`. -/
def dyadicLyap (N : ℕ) (z : ℂ) : ℝ := ((2 : ℝ) ^ N)⁻¹ * E.avgLogNorm (2 ^ N) z

lemma dyadicLyap_antitone (z : ℂ) : Antitone fun N => E.dyadicLyap N z := by
  refine antitone_nat_of_succ_le fun N => ?_
  unfold dyadicLyap
  have h := E.avgLogNorm_two_mul_le (2 ^ N) z
  rw [← two_mul, ← pow_succ'] at h
  rw [pow_succ, mul_inv]
  have h2 : (0 : ℝ) < ((2 : ℝ) ^ N)⁻¹ := by positivity
  calc ((2 : ℝ) ^ N)⁻¹ * 2⁻¹ * E.avgLogNorm (2 ^ (N + 1)) z
      ≤ ((2 : ℝ) ^ N)⁻¹ * 2⁻¹ * (2 * E.avgLogNorm (2 ^ N) z) := by gcongr
    _ = ((2 : ℝ) ^ N)⁻¹ * E.avgLogNorm (2 ^ N) z := by ring

lemma tendsto_dyadicLyap (z : ℂ) :
    Tendsto (fun N => E.dyadicLyap N z) atTop (𝓝 (E.lyap z)) := by
  have h := (E.tendsto_integral_lyap z).comp
    (tendsto_pow_atTop_atTop_of_one_lt (one_lt_two : 1 < 2))
  refine h.congr fun N => ?_
  simp only [Function.comp, dyadicLyap, avgLogNorm]
  push_cast
  ring

lemma lyap_eq_iInf_dyadic (z : ℂ) :
    ((E.lyap z : ℝ) : EReal) = ⨅ N, ((E.dyadicLyap N z : ℝ) : EReal) := by
  refine le_antisymm (le_iInf fun N => EReal.coe_le_coe_iff.2 ?_) ?_
  · have := E.lyap_le z (2 ^ N) (Nat.one_le_two_pow)
    unfold dyadicLyap avgLogNorm
    push_cast at this
    rw [inv_mul_eq_div]; exact this
  · have ht : Tendsto (fun N => ((E.dyadicLyap N z : ℝ) : EReal)) atTop (𝓝 (E.lyap z : EReal)) :=
      (continuous_coe_real_ereal.tendsto _).comp (E.tendsto_dyadicLyap z)
    exact ge_of_tendsto' ht fun N => iInf_le _ N

/-- **Theorem 4.5.3.** The Lyapunov exponent `z ↦ L(z)` is subharmonic on `ℂ`. -/
theorem subharmonic_lyap : Subharmonic (fun z => ((E.lyap z : ℝ) : EReal)) := by
  have h := subharmonicOn_iInf (U := univ) (u := fun N z => E.dyadicLyap N z)
    (fun N => continuous_const.mul (E.continuous_avgLogNorm _))
    (fun z => E.dyadicLyap_antitone z)
    (fun N c r hr _ => by
      unfold dyadicLyap
      have hs := circleAverage_fun_smul (a := ((2 : ℝ) ^ N)⁻¹) (f := E.avgLogNorm (2 ^ N))
        (c := c) (R := r)
      simp only [smul_eq_mul] at hs
      rw [hs]
      exact mul_le_mul_of_nonneg_left (E.avgLogNorm_le_circleAverage _ c hr) (by positivity))
  have heq : (fun z => ((E.lyap z : ℝ) : EReal)) = fun z => ⨅ N, ((E.dyadicLyap N z : ℝ) : EReal) :=
    funext E.lyap_eq_iInf_dyadic
  rw [heq]; exact h

/-- The Lyapunov exponent is upper semicontinuous (p. 327). -/
theorem upperSemicontinuous_lyap : UpperSemicontinuous E.lyap := by
  have h := (E.subharmonic_lyap).usc
  rw [upperSemicontinuousOn_univ_iff] at h
  rw [← upperSemicontinuousOn_univ_iff]
  exact upperSemicontinuousOn_coe_iff.1 (h.upperSemicontinuousOn univ)

end ErgodicFamily

end DF
