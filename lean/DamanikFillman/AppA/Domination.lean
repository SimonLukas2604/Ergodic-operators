/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Appendix A.2: a domination principle for equilibrium potentials

This file prepares the proof of Choquet's capacitability theorem for the logarithmic capacity
(`DamanikFillman/AppA/Capacitability.lean`).

## Main results

* `DF.le_of_submean_compl` — a maximum principle for upper semicontinuous functions satisfying
  the sub-mean value inequality off a closed set `S` (bounded above by `c` near `S` and near
  `∞`).  (Perturb by `ε |z|²`, which has strictly larger circle averages, and look at a maximum.)
* `DF.toReal_logPotential_le_of_subset` — the **domination principle** for equilibrium
  potentials: if `L ⊆ K` are compact sets of positive capacity in a disc of radius `1/4`, with
  equilibrium measures `σ` and `ρ`, then `Φ_σ ≤ Φ_ρ + E(σ) - E(ρ)` off the exceptional set
  `{Φ_ρ < E(ρ)} ∩ K` (a set of capacity zero).  Restrict `σ` to a compact set `S` avoiding the
  exceptional set, of mass `m` close to `1`; then `Φ_{σ|S} - m Φ_ρ` satisfies the sub-mean value
  inequality off `S`, is at most `E(σ) - m E(ρ)` near `S` and tends to `0` at `∞`.
-/
import DamanikFillman.AppA.LowerEnvelope

noncomputable section

open Real Complex Metric Set Filter Topology MeasureTheory
open scoped ENNReal

namespace DF

/-! ### A maximum principle -/

/-- The circle averages of `|z|²`. -/
lemma circleAverage_norm_sq (c : ℂ) (r : ℝ) :
    circleAverage (fun z => ‖z‖ ^ 2) c r = ‖c‖ ^ 2 + r ^ 2 := by
  have h1 : ∀ z ∈ sphere c |r|,
      ‖z‖ ^ 2 = (‖c‖ ^ 2 + r ^ 2) + (2 * (starRingEnd ℂ c) * (z - c)).re := by
    intro z hz
    rw [mem_sphere, dist_eq_norm] at hz
    have h2 : ‖z - c‖ ^ 2 = r ^ 2 := by rw [hz, sq_abs]
    have e : ‖z‖ ^ 2 = ‖c‖ ^ 2 + ‖z - c‖ ^ 2 + (2 * (starRingEnd ℂ c) * (z - c)).re := by
      simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
        Complex.conj_re, Complex.conj_im, Complex.sub_re, Complex.sub_im, Complex.re_ofNat,
        Complex.im_ofNat]
      ring
    rw [e, h2]
  rw [circleAverage_congr_sphere h1]
  have hharm : InnerProductSpace.HarmonicOnNhd
      (fun z : ℂ => (2 * (starRingEnd ℂ c) * (z - c)).re) (closedBall c |r|) := by
    intro z _
    have hd : Differentiable ℂ (fun z : ℂ => 2 * (starRingEnd ℂ c) * (z - c)) := by fun_prop
    exact (hd.analyticAt z).harmonicAt_re
  rw [circleAverage_fun_add (circleIntegrable_const _ c r)
    (hharm.continuousOn.mono sphere_subset_closedBall).circleIntegrable', circleAverage_const,
    hharm.circleAverage_eq]
  simp

/-- **Maximum principle** for upper semicontinuous functions satisfying the sub-mean value
inequality on small circles off a closed set `S`: if `f ≤ c` near `S` and near `∞`, then
`f ≤ c` off `S`. -/
theorem le_of_submean_compl {S : Set ℂ} (hS : IsClosed S) {f : ℂ → ℝ}
    (husc : UpperSemicontinuousOn f Sᶜ)
    (hsub : ∀ z ∉ S, ∃ r0 > 0, ∀ r, 0 < r → r < r0 →
      CircleIntegrable f z r ∧ f z ≤ circleAverage f z r)
    {c : ℝ} (hbd : ∀ z0 ∈ S, ∀ᶠ z in 𝓝 z0, z ∉ S → f z ≤ c) {R : ℝ}
    (hR : ∀ z, R < ‖z‖ → f z ≤ c) : ∀ z ∉ S, f z ≤ c := by
  intro z1 hz1
  by_contra hgt
  push_neg at hgt
  set η := f z1 - c with hη
  have hηpos : 0 < η := by rw [hη]; linarith
  set R' : ℝ := |R| + 1 with hR'
  set ε : ℝ := η / (2 * (R' ^ 2 + 1)) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  set φ : ℂ → ℝ := fun z => ε * min (‖z‖ ^ 2) (R' ^ 2) with hφ
  have hφc : Continuous φ := continuous_const.mul ((continuous_norm.pow 2).min continuous_const)
  have hφnn : ∀ z, 0 ≤ φ z := fun z =>
    mul_nonneg hεpos.le (le_min (sq_nonneg _) (sq_nonneg _))
  have hφle : ∀ z, φ z < η := by
    intro z
    have h1 : min (‖z‖ ^ 2) (R' ^ 2) ≤ R' ^ 2 := min_le_right _ _
    have h2 : ε * R' ^ 2 < η := by
      rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [sq_nonneg R']
    calc φ z ≤ ε * R' ^ 2 := mul_le_mul_of_nonneg_left h1 hεpos.le
      _ < η := h2
  set g : ℂ → ℝ := fun z => f z + φ z with hg
  have hgdef : ∀ z, g z = f z + φ z := fun z => rfl
  have hgusc : UpperSemicontinuousOn g Sᶜ :=
    husc.add hφc.continuousOn.upperSemicontinuousOn
  have hgz1 : c + η ≤ g z1 := by
    have := hφnn z1
    rw [hgdef z1]
    linarith
  set A := {z | z ∉ S ∧ g z1 ≤ g z} with hAdef
  have hAsub : A ⊆ closedBall 0 |R| := by
    intro z hz
    rw [mem_closedBall, dist_zero_right]
    by_contra h
    push_neg at h
    have h1 := hR z (lt_of_le_of_lt (le_abs_self R) h)
    have h2 := hφle z
    have h4 := hz.2
    have h5 := hgdef z
    linarith
  have hAclosed : IsClosed A := by
    refine isClosed_of_closure_subset fun x hx => ?_
    rw [mem_closure_iff_nhds] at hx
    by_cases hxS : x ∈ S
    · exfalso
      obtain ⟨z, hz1', hz2⟩ := hx _ (hbd x hxS)
      have h1 := hz1' hz2.1
      have h2 := hφle z
      have h4 := hz2.2
      have h5 := hgdef z
      linarith
    · refine ⟨hxS, ?_⟩
      by_contra hlt
      push_neg at hlt
      have hev : ∀ᶠ z in 𝓝 x, g z < g z1 := by
        have := hgusc x hxS (g z1) hlt
        rwa [nhdsWithin_eq_nhds.2 (hS.isOpen_compl.mem_nhds hxS)] at this
      obtain ⟨z, hz1', hz2⟩ := hx _ hev
      have : g z < g z1 := hz1'
      linarith [hz2.2]
  have hAcpt : IsCompact A := (isCompact_closedBall 0 |R|).of_isClosed_subset hAclosed hAsub
  obtain ⟨z2, hz2A, hmax⟩ := UpperSemicontinuousOn.exists_isMaxOn (show A.Nonempty from ⟨z1, hz1, le_rfl⟩) hAcpt
    (hgusc.mono fun z hz => hz.1)
  have hle : ∀ z ∉ S, g z ≤ g z2 := by
    intro z hz
    by_cases h : g z1 ≤ g z
    · exact isMaxOn_iff.1 hmax z ⟨hz, h⟩
    · push_neg at h
      linarith [hz2A.2]
  have hz2R : ‖z2‖ ≤ |R| := by
    have := hAsub hz2A
    rwa [mem_closedBall, dist_zero_right] at this
  obtain ⟨r0, hr0, hsub2⟩ := hsub z2 hz2A.1
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hS.isOpen_compl z2 hz2A.1
  set r := min (r0 / 2) (min (δ / 2) (1 / 2)) with hr
  have hrpos : 0 < r := lt_min (by linarith) (lt_min (by linarith) (by norm_num))
  have hrr0 : r < r0 := (min_le_left _ _).trans_lt (by linarith)
  have hrδ : r < δ := ((min_le_right _ _).trans (min_le_left _ _)).trans_lt (by linarith)
  have hr1 : r ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨hint, hfle⟩ := hsub2 r hrpos hrr0
  have hsph : ∀ z ∈ sphere z2 |r|, z ∉ S ∧ ‖z‖ ≤ |R| + 1 / 2 := by
    intro z hz
    rw [mem_sphere, dist_eq_norm, abs_of_pos hrpos] at hz
    refine ⟨fun hzS => hball (by rw [mem_ball, dist_eq_norm, hz]; exact hrδ) hzS, ?_⟩
    have := norm_le_norm_add_norm_sub' z z2
    linarith
  have hφeq : ∀ z ∈ sphere z2 |r|, φ z = ε * ‖z‖ ^ 2 := by
    intro z hz
    have h := (hsph z hz).2
    have : ‖z‖ ^ 2 ≤ R' ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (h.trans (by rw [hR']; linarith)) 2
    simp only [hφ, min_eq_left this]
  have hφavg : circleAverage φ z2 r = ε * (‖z2‖ ^ 2 + r ^ 2) := by
    rw [circleAverage_congr_sphere hφeq]
    have := circleAverage_fun_smul (a := ε) (f := fun z : ℂ => ‖z‖ ^ 2) (c := z2) (R := r)
    simp only [smul_eq_mul] at this
    rw [this, circleAverage_norm_sq]
  have hφint : CircleIntegrable φ z2 r := hφc.continuousOn.circleIntegrable'
  have hgavg : circleAverage g z2 r = circleAverage f z2 r + ε * (‖z2‖ ^ 2 + r ^ 2) := by
    rw [← hφavg]
    exact circleAverage_fun_add hint hφint
  have hgle : circleAverage g z2 r ≤ g z2 :=
    circleAverage_mono_on_of_le_circle (hint.add hφint) fun z hz => hle z (hsph z hz).1
  have hφz2 : φ z2 = ε * ‖z2‖ ^ 2 := by
    have : ‖z2‖ ^ 2 ≤ R' ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hz2R.trans (by rw [hR']; linarith)) 2
    simp only [hφ, min_eq_left this]
  have hgz2 : g z2 = f z2 + ε * ‖z2‖ ^ 2 := by rw [hgdef z2, hφz2]
  have h1 : ε * r ^ 2 ≤ 0 := by linarith
  have h2 : 0 < ε * r ^ 2 := by positivity
  linarith

/-! ### Elementary bounds for potentials -/

lemma norm_sub_le_of_mem_closedBall {a z w : ℂ} {r s : ℝ} (hz : z ∈ closedBall a r)
    (hw : w ∈ closedBall a s) : ‖z - w‖ ≤ r + s := by
  rw [mem_closedBall, dist_eq_norm] at hz hw
  calc ‖z - w‖ = ‖(z - a) - (w - a)‖ := by rw [sub_sub_sub_cancel_right]
    _ ≤ ‖z - a‖ + ‖w - a‖ := norm_sub_le _ _
    _ ≤ r + s := add_le_add hz hw

lemma ereal_toReal_le {x : EReal} {a : ℝ} (h : x ≤ a) (hx : x ≠ ⊥) : x.toReal ≤ a := by
  simpa using EReal.toReal_le_toReal h hx (EReal.coe_ne_top a)

lemma ereal_le_toReal {x : EReal} {a : ℝ} (h : (a : EReal) ≤ x) (hx : x ≠ ⊤) :
    a ≤ x.toReal := by
  simpa using EReal.toReal_le_toReal h (EReal.coe_ne_bot a) hx

/-- `logKer 0 (z - w) ≥ 0` if `|z - w| ≤ 1`. -/
lemma logKer_zero_nonneg {y : ℂ} (hy : ‖y‖ ≤ 1) : 0 ≤ logKer 0 y := by
  unfold logKer
  have h1 : max ‖y‖ (Real.exp (-((0 : ℕ) : ℝ))) ≤ 1 := max_le hy (by simp)
  have := Real.log_nonpos (max_norm_exp_pos 0 y).le h1
  linarith

lemma potT_zero_nonneg {μ : Measure ℂ} {K : Set ℂ} (hμK : μ Kᶜ = 0) {z : ℂ}
    (hz : ∀ w ∈ K, ‖z - w‖ ≤ 1) : 0 ≤ potT μ 0 z := by
  refine integral_nonneg_of_ae ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hμK] with w hw
  exact logKer_zero_nonneg (hz w (by simpa using hw))

/-- Potentials are nonnegative at points of distance `≤ 1` from a set carrying the measure. -/
lemma logPotential_nonneg_of_near {μ : Measure ℂ} {K : Set ℂ} (hμK : μ Kᶜ = 0) {z : ℂ}
    (hz : ∀ w ∈ K, ‖z - w‖ ≤ 1) : 0 ≤ logPotential μ z := by
  refine le_trans ?_ (le_iSup (fun N : ℕ => ((∫ w, logKer N (z - w) ∂μ : ℝ) : EReal)) 0)
  exact EReal.coe_nonneg.2 (potT_zero_nonneg hμK hz)

/-- Measures carried by a disc of radius `1/4` have nonnegative energy. -/
lemma energy_nonneg_of_subset_closedBall {μ : Measure ℂ} {a : ℂ} {K : Set ℂ}
    (hKa : K ⊆ closedBall a (1 / 4)) (hμK : μ Kᶜ = 0) : 0 ≤ energy μ := by
  refine le_trans ?_ (Itr_le_energy μ 0)
  refine EReal.coe_nonneg.2 (integral_nonneg_of_ae ?_)
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hμK] with z hz
  have hzK : z ∈ K := by simpa using hz
  exact potT_zero_nonneg hμK fun w hw =>
    (norm_sub_le_of_mem_closedBall (hKa hzK) (hKa hw)).trans (by norm_num)

lemma logKer_le_neg_log {N : ℕ} {y : ℂ} {s : ℝ} (hs : 0 < s) (hy : s ≤ ‖y‖) :
    logKer N y ≤ -Real.log s := by
  unfold logKer
  exact neg_le_neg (Real.log_le_log hs (hy.trans (le_max_left _ _)))

/-- Upper bound for a potential at a point at distance `≥ s` from the carrier. -/
lemma logPotential_le_of_dist {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : Integrable (fun w => ‖w‖) μ) {K : Set ℂ} (hμK : μ Kᶜ = 0) {z : ℂ} {s : ℝ}
    (hs : 0 < s) (h : ∀ w ∈ K, s ≤ ‖z - w‖) :
    logPotential μ z ≤ ((μ.real univ * (-Real.log s) : ℝ) : EReal) := by
  refine iSup_le fun N => EReal.coe_le_coe_iff.2 ?_
  have := integral_mono_ae (μ := μ) (integrable_logKer hμ N z) (integrable_const (-Real.log s))
    ((measure_eq_zero_iff_ae_notMem.1 hμK).mono fun w hw =>
      logKer_le_neg_log hs (h w (by simpa using hw)))
  rwa [integral_const, smul_eq_mul] at this

/-- Lower bound for a potential at a point at distance between `1` and `s` from the carrier. -/
lemma le_logPotential_of_dist {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : Integrable (fun w => ‖w‖) μ) {K : Set ℂ} (hμK : μ Kᶜ = 0) {z : ℂ} {s : ℝ}
    (h1 : ∀ w ∈ K, 1 ≤ ‖z - w‖) (h2 : ∀ w ∈ K, ‖z - w‖ ≤ s) :
    ((μ.real univ * (-Real.log s) : ℝ) : EReal) ≤ logPotential μ z := by
  refine le_trans ?_ (le_iSup (fun N : ℕ => ((∫ w, logKer N (z - w) ∂μ : ℝ) : EReal)) 0)
  rw [EReal.coe_le_coe_iff]
  have := integral_mono_ae (μ := μ) (integrable_const (-Real.log s)) (integrable_logKer hμ 0 z)
    ((measure_eq_zero_iff_ae_notMem.1 hμK).mono fun w hw => by
      have hwK : w ∈ K := by simpa using hw
      have hpos : 0 < ‖z - w‖ := lt_of_lt_of_le one_pos (h1 w hwK)
      show -Real.log s ≤ logKer 0 (z - w)
      rw [logKer_of_le (by simpa using h1 w hwK)]
      exact neg_le_neg (Real.log_le_log hpos (h2 w hwK)))
  rwa [integral_const, smul_eq_mul] at this

/-- The real sub-mean value property of `-Φ_μ`, for potentials bounded above. -/
lemma submean_neg_toReal_logPotential {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : Integrable (fun w => ‖w‖) μ) {A : ℝ} (hA : ∀ w, logPotential μ w ≤ A) :
    UpperSemicontinuous (fun w => -(logPotential μ w).toReal) ∧
      ∀ (c : ℂ) (r : ℝ), 0 < r → CircleIntegrable (fun w => -(logPotential μ w).toReal) c r ∧
        -(logPotential μ c).toReal ≤ circleAverage (fun w => -(logPotential μ w).toReal) c r := by
  have hF := subharmonic_neg_logPotential hμ
  have hfin : ∀ w, logPotential μ w ≠ ⊤ := fun w =>
    ne_top_of_le_ne_top (EReal.coe_ne_top A) (hA w)
  have hcoe : ∀ w, ((-(logPotential μ w).toReal : ℝ) : EReal) = -logPotential μ w := fun w => by
    rw [EReal.coe_neg, EReal.coe_toReal (hfin w) (logPotential_ne_bot μ w)]
  obtain ⟨n, hn⟩ := exists_nat_ge A
  have htr : ∀ w, truncBelow n (-logPotential μ w) = -(logPotential μ w).toReal := by
    intro w
    apply EReal.coe_injective
    have hne : -logPotential μ w ≠ ⊤ := fun h =>
      logPotential_ne_bot μ w (EReal.neg_eq_top_iff.1 h)
    rw [truncBelow_eq_coe_max hne, hcoe w]
    apply max_eq_left
    rw [← hcoe w, neg_natCast_ereal, EReal.coe_le_coe_iff, neg_le_neg_iff]
    exact (ereal_toReal_le (hA w) (logPotential_ne_bot μ w)).trans hn
  have hfun : (fun w => truncBelow n (-logPotential μ w)) =
      fun w => -(logPotential μ w).toReal := funext htr
  refine ⟨?_, fun c r hr => ⟨?_, ?_⟩⟩
  · rw [← upperSemicontinuousOn_univ_iff]
    refine upperSemicontinuousOn_coe_iff.1 ?_
    simpa only [hcoe] using hF.usc
  · rw [← hfun]
    exact circleIntegrable_truncBelow hF.ne_top hF.usc (subset_univ _) n
  · have := hF.truncBelow_le_circleAverage hr (subset_univ (closedBall c r)) n
    rwa [hfun, htr c] at this

/-! ### The domination principle -/

/-- **Domination principle** for equilibrium potentials: if `L ⊆ K` are compact sets of
positive capacity in a disc of radius `1/4` with equilibrium measures `σ` and `ρ`, then
`Φ_σ ≤ Φ_ρ + E(σ) - E(ρ)` off the set `{Φ_ρ < E(ρ)} ∩ K` (which has capacity zero). -/
theorem toReal_logPotential_le_of_subset {a : ℂ} {K L : Set ℂ} (hK : IsCompact K)
    (hL : IsCompact L) (hLK : L ⊆ K) (hKa : K ⊆ closedBall a (1 / 4))
    (hcapL : capCompact L ≠ 0) {ρ σ : Measure ℂ} (hρ : IsEquilibriumMeasure K ρ)
    (hσ : IsEquilibriumMeasure L σ) {z : ℂ}
    (hz : z ∉ {w ∈ K | logPotential ρ w < energy ρ}) :
    (logPotential σ z).toReal ≤
      (logPotential ρ z).toReal + ((energy σ).toReal - (energy ρ).toReal) := by
  have hcapK : capCompact K ≠ 0 := fun h =>
    hcapL (le_antisymm ((capCompact_mono hLK).trans h.le) zero_le)
  haveI := hρ.1.1
  haveI := hσ.1.1
  have hρa := adm_of_M1 hK hρ.1
  have hσa := adm_of_M1 hL hσ.1
  set VK := (energy ρ).toReal with hVK
  set VL := (energy σ).toReal with hVL
  have hρE : energy ρ = (VK : EReal) := hρ.energy_eq_coe hcapK
  have hσE : energy σ = (VL : EReal) := hσ.energy_eq_coe hcapL
  have hVKL : VK ≤ VL := by
    have := hρ.2 σ (M1_mono hLK hσ.1)
    rwa [hρE, hσE, EReal.coe_le_coe_iff] at this
  have hVK0 : 0 ≤ VK := by
    have := energy_nonneg_of_subset_closedBall hKa hρ.1.2
    rw [hρE] at this
    exact EReal.coe_nonneg.1 this
  have hρle : ∀ w, logPotential ρ w ≤ VK := fun w => by
    rw [← hρE]; exact hρ.logPotential_le_energy hK hcapK w
  have hσle : ∀ w, logPotential σ w ≤ VL := fun w => by
    rw [← hσE]; exact hσ.logPotential_le_energy hL hcapL w
  have hρfin : ∀ w, logPotential ρ w = (((logPotential ρ w).toReal : ℝ) : EReal) := fun w =>
    (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top VK) (hρle w))
      (logPotential_ne_bot ρ w)).symm
  have hσK : σ Kᶜ = 0 := measure_mono_null (compl_subset_compl.2 hLK) hσ.1.2
  by_cases hzK : z ∈ K
  · have hge : VK ≤ (logPotential ρ z).toReal := by
      have h1 : ¬ logPotential ρ z < energy ρ := fun h => hz ⟨hzK, h⟩
      push_neg at h1
      rw [hρE] at h1
      exact ereal_le_toReal h1 (ne_top_of_le_ne_top (EReal.coe_ne_top VK) (hρle z))
    have := ereal_toReal_le (hσle z) (logPotential_ne_bot σ z)
    linarith
  -- the exceptional set is `σ`-null
  set E := {w ∈ K | logPotential ρ w < energy ρ} with hEdef
  have hlscρ := lowerSemicontinuous_logPotential hρa.2
  have hEm : MeasurableSet E := hK.measurableSet.inter (hlscρ.measurable measurableSet_Iio)
  have hσE0 : σ E = 0 := measure_eq_zero_of_capacity_eq_zero hσa.2 (hσ.energy_ne_top hcapL)
    hEm (hρ.capacity_lt_eq_zero hK hcapK)
  have hσL : σ L = 1 := (prob_compl_eq_zero_iff hL.measurableSet).1 hσ.1.2
  -- the distance from `z` to `K`
  obtain ⟨d, hd, hdK⟩ : ∃ d > 0, ∀ w ∈ K, d ≤ ‖z - w‖ := by
    obtain ⟨d, hd, hball⟩ := Metric.isOpen_iff.1 hK.isClosed.isOpen_compl z hzK
    refine ⟨d, hd, fun w hw => ?_⟩
    by_contra hlt
    push_neg at hlt
    exact hball (by rw [mem_ball, dist_eq_norm, norm_sub_rev]; exact hlt) hw
  set Q := (logPotential ρ z).toReal with hQ
  set P := (logPotential σ z).toReal with hP
  set B := |Real.log d| + VK + |Q| with hB
  have hB0 : 0 ≤ B := by positivity
  suffices key : ∀ η : ℝ, 0 < η → η < 1 → ∀ δ : ℝ, 0 < δ → P ≤ Q + (VL - VK) + δ + η * B by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    set η := min (1 / 2) (ε / (2 * (B + 1))) with hηdef
    have hη0 : 0 < η := lt_min (by norm_num) (by positivity)
    have hη1 : η < 1 := (min_le_left _ _).trans_lt (by norm_num)
    have hηB : η * B ≤ ε / 2 := by
      have h1 : η ≤ ε / (2 * (B + 1)) := min_le_right _ _
      calc η * B ≤ ε / (2 * (B + 1)) * B := mul_le_mul_of_nonneg_right h1 hB0
        _ ≤ ε / 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
          linarith
    have := key η hη0 hη1 (ε / 2) (by positivity)
    linarith
  intro η hη0 hη1 δ hδ
  -- a compact set `S ⊆ L \ E` of mass `m > 1 - η`
  have hLEm : MeasurableSet (L \ E) := hL.measurableSet.diff hEm
  have hσLE : σ (L \ E) = 1 := by rw [measure_sdiff_null hσE0, hσL]
  obtain ⟨S, hSsub, hS, hσS⟩ := hLEm.exists_isCompact_lt_add (μ := σ)
    (by rw [hσLE]; exact ENNReal.one_ne_top) (ε := ENNReal.ofReal η)
    (ENNReal.ofReal_pos.2 hη0).ne'
  rw [hσLE] at hσS
  set m := (σ S).toReal with hm
  have hm1 : m ≤ 1 := by
    rw [hm]
    have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := σ) (s := S))
    simpa using this
  have hmη : 1 - η < m := by
    have := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top
      (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩)).2 hσS
    rw [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hη0.le, ENNReal.toReal_one] at this
    rw [hm]; linarith
  have hm0 : 0 ≤ m := ENNReal.toReal_nonneg
  have hSL : S ⊆ L := fun x hx => (hSsub hx).1
  have hSK : S ⊆ K := hSL.trans hLK
  have hSE : ∀ x ∈ S, VK ≤ (logPotential ρ x).toReal := by
    intro x hx
    have h1 : ¬ logPotential ρ x < energy ρ := fun h => (hSsub hx).2 ⟨hSK hx, h⟩
    push_neg at h1
    rw [hρE] at h1
    exact ereal_le_toReal h1 (ne_top_of_le_ne_top (EReal.coe_ne_top VK) (hρle x))
  -- the measures `σ|S`, `σ|Sᶜ` and `m ρ`
  set σS := σ.restrict S with hσSdef
  set σR := σ.restrict Sᶜ with hσRdef
  set cS : ℝ≥0∞ := σ S with hcS
  have hctop : cS ≠ ⊤ := measure_ne_top _ _
  set ρm := cS • ρ with hρmdef
  haveI : IsFiniteMeasure ρm := ρ.smul_finite hctop
  have hρma : Integrable (fun w => ‖w‖) ρm := hρa.2.smul_measure hctop
  have hσSa : Integrable (fun w => ‖w‖) σS := hσa.2.restrict
  have hσRa : Integrable (fun w => ‖w‖) σR := hσa.2.restrict
  have hσSS : σS Sᶜ = 0 := by
    rw [hσSdef, Measure.restrict_apply hS.measurableSet.compl, compl_inter_self, measure_empty]
  have hσSK : σS Kᶜ = 0 := measure_mono_null (compl_subset_compl.2 hSK) hσSS
  have hσRK : σR Kᶜ = 0 :=
    le_antisymm ((Measure.restrict_apply_le _ _).trans hσK.le) zero_le
  have hρmK : ρm Kᶜ = 0 := by
    rw [hρmdef, Measure.smul_apply, hρ.1.2, smul_zero]
  have hσsplit : ∀ w, logPotential σ w = logPotential σS w + logPotential σR w := by
    intro w
    rw [← logPotential_add hσSa hσRa w, hσSdef, hσRdef,
      Measure.restrict_add_restrict_compl hS.measurableSet]
  have hρmeq : ∀ w, logPotential ρm w = ((m * (logPotential ρ w).toReal : ℝ) : EReal) :=
    fun w => logPotential_smul_of_eq hρa.2 hctop (hρfin w)
  have hρmle : ∀ w, logPotential ρm w ≤ ((m * VK : ℝ) : EReal) := by
    intro w
    rw [hρmeq w, EReal.coe_le_coe_iff]
    exact mul_le_mul_of_nonneg_left (ereal_toReal_le (hρle w) (logPotential_ne_bot ρ w)) hm0
  have hρmreal : ∀ w, (logPotential ρm w).toReal = m * (logPotential ρ w).toReal := fun w => by
    rw [hρmeq w, EReal.toReal_coe]
  have hσSreal : σS.real univ = m := by
    rw [measureReal_def, hσSdef, Measure.restrict_apply_univ]
  have hρmreal' : ρm.real univ = m := by
    rw [measureReal_def, hρmdef, Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
  -- the function `f = Φ_{σ|S} - m Φ_ρ`
  have hharm := harmonicOnNhd_logPotential (μ := σS) hS hσSS
  obtain ⟨hgusc, hgsub⟩ := submean_neg_toReal_logPotential hρma hρmle
  set f : ℂ → ℝ := fun w => (logPotential σS w).toReal + -(logPotential ρm w).toReal with hfdef
  have hfusc : UpperSemicontinuousOn f Sᶜ :=
    hharm.continuousOn.upperSemicontinuousOn.add (hgusc.upperSemicontinuousOn _)
  have hfsub : ∀ w ∉ S, ∃ r0 > 0, ∀ r, 0 < r → r < r0 →
      CircleIntegrable f w r ∧ f w ≤ circleAverage f w r := by
    intro w hw
    obtain ⟨r0, hr0, hball⟩ := Metric.isOpen_iff.1 hS.isClosed.isOpen_compl w hw
    refine ⟨r0, hr0, fun r hr hrr0 => ?_⟩
    have hcb : closedBall w |r| ⊆ Sᶜ := fun x hx => hball (by
      rw [mem_closedBall, abs_of_pos hr] at hx
      rw [mem_ball]; linarith)
    have hh := hharm.mono hcb
    have hint1 : CircleIntegrable (fun w => (logPotential σS w).toReal) w r :=
      (hh.continuousOn.mono sphere_subset_closedBall).circleIntegrable'
    obtain ⟨hint2, hle2⟩ := hgsub w r hr
    refine ⟨hint1.add hint2, ?_⟩
    simp only [hfdef]
    rw [circleAverage_fun_add hint1 hint2, hh.circleAverage_eq]
    linarith
  set c := VL - m * VK + δ with hc
  have hbd : ∀ z0 ∈ S, ∀ᶠ w in 𝓝 z0, w ∉ S → f w ≤ c := by
    intro z0 hz0
    have hlsc := lowerSemicontinuous_logPotential hρma
    have hz0v : ((m * VK - δ : ℝ) : EReal) < logPotential ρm z0 := by
      rw [hρmeq z0, EReal.coe_lt_coe_iff]
      have := mul_le_mul_of_nonneg_left (hSE z0 hz0) hm0
      linarith
    filter_upwards [hlsc z0 _ hz0v, ball_mem_nhds z0 (by norm_num : (0 : ℝ) < 1 / 2)]
      with w hw1 hw2 _
    -- `Φ_{σ|S}(w) ≤ Φ_σ(w) ≤ E(σ)` since `Φ_{σ|Sᶜ}(w) ≥ 0`
    have hwa : w ∈ closedBall a (3 / 4) := by
      have h1 := hKa (hSK hz0)
      rw [mem_ball, dist_eq_norm] at hw2
      rw [mem_closedBall, dist_eq_norm] at h1 ⊢
      have := norm_sub_le_norm_sub_add_norm_sub w z0 a
      linarith
    have hR0 : 0 ≤ logPotential σR w := logPotential_nonneg_of_near hσRK fun x hx =>
      (norm_sub_le_of_mem_closedBall hwa (hKa hx)).trans (by norm_num)
    have hS1 : logPotential σS w ≤ VL := by
      have := hσle w
      rw [hσsplit w] at this
      exact (le_add_of_nonneg_right hR0).trans this
    have h1 := ereal_toReal_le hS1 (logPotential_ne_bot σS w)
    have h2 : m * VK - δ < (logPotential ρm w).toReal := by
      have hne : logPotential ρm w ≠ ⊤ :=
        ne_top_of_le_ne_top (EReal.coe_ne_top _) (hρmle w)
      rw [← EReal.coe_lt_coe_iff, EReal.coe_toReal hne (logPotential_ne_bot ρm w)]
      exact hw1
    simp only [hfdef, hc]
    linarith
  -- behaviour at `∞`
  have hcδ : δ ≤ c := by
    have : m * VK ≤ VK := mul_le_of_le_one_left hVK0 hm1
    rw [hc]; linarith
  have hfar : ∀ w, ‖a‖ + 5 / 4 + 1 / (2 * δ) < ‖w‖ → f w ≤ c := by
    intro w hw
    set t := ‖w - a‖ with ht
    have hta : ‖w‖ - ‖a‖ ≤ t := norm_sub_norm_le w a
    have ht1 : 5 / 4 + 1 / (2 * δ) < t := by linarith
    have hdist1 : ∀ x ∈ K, t - 1 / 4 ≤ ‖w - x‖ := by
      intro x hx
      have h1 := hKa hx
      rw [mem_closedBall, dist_eq_norm] at h1
      have := norm_sub_le_norm_sub_add_norm_sub w x a
      linarith
    have hdist2 : ∀ x ∈ K, ‖w - x‖ ≤ t + 1 / 4 := by
      intro x hx
      have h1 := hKa hx
      rw [mem_closedBall, dist_eq_norm] at h1
      have := norm_sub_le_norm_sub_add_norm_sub w a x
      rw [norm_sub_rev a x] at this
      linarith
    have hpos : 0 < t - 1 / 4 := by
      have : 0 < 1 / (2 * δ) := by positivity
      linarith
    have ht2 : 1 ≤ t - 1 / 4 := by
      have : 0 < 1 / (2 * δ) := by positivity
      linarith
    have hup := logPotential_le_of_dist hσSa hσSK hpos hdist1
    have hlow := le_logPotential_of_dist hρma hρmK (fun x hx => ht2.trans (hdist1 x hx)) hdist2
    rw [hσSreal] at hup
    rw [hρmreal'] at hlow
    have h1 := ereal_toReal_le hup (logPotential_ne_bot σS w)
    have h2 := ereal_le_toReal hlow (ne_top_of_le_ne_top (EReal.coe_ne_top _) (hρmle w))
    -- `m (log (t + 1/4) - log (t - 1/4)) ≤ (1/2) / (t - 1/4) < δ`
    have hlog : Real.log (t + 1 / 4) - Real.log (t - 1 / 4) ≤ (1 / 2) / (t - 1 / 4) := by
      have htp : (0 : ℝ) < t + 1 / 4 := by linarith
      rw [← Real.log_div htp.ne' hpos.ne']
      have := Real.log_le_sub_one_of_pos (div_pos htp hpos)
      have e : (t + 1 / 4) / (t - 1 / 4) - 1 = (1 / 2) / (t - 1 / 4) := by
        rw [div_sub_one hpos.ne']
        congr 1
        ring
      linarith
    have hlog0 : 0 ≤ Real.log (t + 1 / 4) - Real.log (t - 1 / 4) :=
      sub_nonneg.2 (Real.log_le_log hpos (by linarith))
    have hsmall : (1 / 2) / (t - 1 / 4) < δ := by
      rw [div_lt_iff₀ hpos]
      have h3 : 1 / (2 * δ) < t - 1 / 4 := by linarith
      rw [div_lt_iff₀ (by positivity)] at h3
      linarith
    have hm' : m * (Real.log (t + 1 / 4) - Real.log (t - 1 / 4)) ≤
        Real.log (t + 1 / 4) - Real.log (t - 1 / 4) := mul_le_of_le_one_left hlog0 hm1
    simp only [hfdef]
    linarith
  have hmax := le_of_submean_compl hS.isClosed hfusc hfsub hbd hfar z
    (fun hzS => hzK (hSK hzS))
  -- back to `Φ_σ(z)`
  have hσSz : logPotential σS z ≠ ⊤ := (logPotential_lt_top_of_dist hσSa hσSK hd hdK).ne
  have hσRz : logPotential σR z ≠ ⊤ := (logPotential_lt_top_of_dist hσRa hσRK hd hdK).ne
  have hPsplit : P = (logPotential σS z).toReal + (logPotential σR z).toReal := by
    rw [hP, hσsplit z, EReal.toReal_add hσSz (logPotential_ne_bot σS z) hσRz
      (logPotential_ne_bot σR z)]
  have hRbound : (logPotential σR z).toReal ≤ (1 - m) * |Real.log d| := by
    have h1 := logPotential_le_of_dist hσRa hσRK hd hdK
    have h2 := ereal_toReal_le h1 (logPotential_ne_bot σR z)
    have hσR1 : σR.real univ = 1 - m := by
      rw [measureReal_def, hσRdef, Measure.restrict_apply_univ, measure_compl hS.measurableSet
        (measure_ne_top _ _), measure_univ, ENNReal.toReal_sub_of_le prob_le_one
        ENNReal.one_ne_top, ENNReal.toReal_one]
    rw [hσR1] at h2
    have h3 : (1 - m) * (-Real.log d) ≤ (1 - m) * |Real.log d| :=
      mul_le_mul_of_nonneg_left (neg_le_abs _) (by linarith)
    linarith
  have hmaxz : (logPotential σS z).toReal - m * Q ≤ c := by
    have := hmax
    simp only [hfdef, hρmreal z] at this
    rw [hQ]; linarith
  have h1m : 0 ≤ 1 - m := by linarith
  have k1 : m * Q - m * VK ≤ Q - VK + (1 - m) * (|Q| + VK) := by
    nlinarith [mul_nonneg h1m (by linarith [neg_abs_le Q] : 0 ≤ |Q| + Q)]
  have k2 : (1 - m) * B ≤ η * B := mul_le_mul_of_nonneg_right (by linarith) hB0
  rw [hc] at hmaxz
  rw [hB] at k2 ⊢
  linarith [k1, k2, hRbound, hPsplit, hmaxz]

end DF
