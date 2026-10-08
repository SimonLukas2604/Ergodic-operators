/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Appendix A.2: Frostman's theorem (Theorem A.2.8)   (book pp. 415–416)

## Main results

* `DF.lt_of_harmonicOnNhd_compl` — a maximum principle for functions harmonic off a closed set
  `S`: if `f < c` near `S` (outside `S`) and near `∞`, then `f < c` on `Sᶜ`. (A maximum on the
  compact set `{f ≥ f(z₁)}` is a local maximum of `‖exp F‖` for a local holomorphic primitive
  `F` with `Re F = f`, so the maximum set is clopen.)
* `DF.logKer_le_log_two_add` — the nearest-point estimate for the truncated kernels.
* `DF.IsEquilibriumMeasure.eventually_logPotential_lt` — the continuity principle at points of
  `supp ρ`: `limsup_{z → z₀} Φ_ρ(z) ≤ E(ρ)`. (Split `ρ` into its parts on a small closed ball
  `B ∋ z₀` and off it; the part off `B` has continuous potential near `z₀`, the part on `B` has
  small mass, and its potential at `z` is at most `ρ(B) log 2` plus its potential at the nearest
  point of its support.)
* `DF.exists_logPotential_lt_of_far` — `Φ_μ(z) → -∞` as `z → ∞`.
* `DF.IsEquilibriumMeasure.logPotential_le_energy` — **Theorem A.2.8 (i)**: `Φ_ρ ≤ E(ρ)` on `ℂ`.
* `DF.capacity_iUnion_eq_zero` — countable unions of compact sets of capacity zero (in a fixed
  ball) have capacity zero;
* `DF.IsEquilibriumMeasure.capacity_lt_eq_zero` — **Theorem A.2.8 (ii)**: the compact sublevel
  sets `{Φ_ρ ≤ E(ρ) - 1/n} ∩ K` have capacity zero by the first variation
  (`DF.exists_energy_lt_of_variation`), hence so does their union;
* `DF.frostmanStatement_holds` — the Statement `DF.FrostmanStatement`.
-/
import DamanikFillman.AppA.Frostman
import Mathlib.Analysis.Complex.AbsMax

noncomputable section

open Real Complex Metric Set Filter Topology MeasureTheory
open scoped ENNReal

namespace DF

/-! ### A maximum principle -/

/-- Maximum principle for functions harmonic off a closed set `S`. -/
theorem lt_of_harmonicOnNhd_compl {S : Set ℂ} (hS : IsClosed S) {f : ℂ → ℝ}
    (hf : InnerProductSpace.HarmonicOnNhd f Sᶜ) {c : ℝ}
    (hbd : ∀ z0 ∈ S, ∀ᶠ z in 𝓝 z0, z ∉ S → f z < c) {R : ℝ}
    (hR : ∀ z, R < ‖z‖ → f z < c) : ∀ z ∉ S, f z < c := by
  intro z1 hz1
  by_contra hge
  push_neg at hge
  have hcont : ∀ z ∉ S, ContinuousAt f z := fun z hz => (hf z hz).1.continuousAt
  set A := {z | z ∉ S ∧ f z1 ≤ f z} with hAdef
  have hAsub : A ⊆ closedBall 0 R := by
    intro z hz
    rw [mem_closedBall, dist_zero_right]
    by_contra hzR
    push_neg at hzR
    have := hR z hzR
    linarith [hz.2]
  have hAclosed : IsClosed A := by
    refine isClosed_of_closure_subset fun x hx => ?_
    rw [mem_closure_iff_nhds] at hx
    by_cases hxS : x ∈ S
    · exfalso
      obtain ⟨z, hz1', hz2⟩ := hx _ (hbd x hxS)
      have := hz1' hz2.1
      linarith [hz2.2]
    · refine ⟨hxS, ?_⟩
      by_contra hlt
      push_neg at hlt
      have hev : ∀ᶠ z in 𝓝 x, f z < f z1 := (hcont x hxS).eventually (Iio_mem_nhds hlt)
      obtain ⟨z, hz1', hz2⟩ := hx _ hev
      have : f z < f z1 := hz1'
      linarith [hz2.2]
  have hAcpt : IsCompact A := (isCompact_closedBall 0 R).of_isClosed_subset hAclosed hAsub
  have hAcont : ContinuousOn f A := fun z hz => (hcont z hz.1).continuousWithinAt
  obtain ⟨z2, hz2A, hmax⟩ := hAcpt.exists_isMaxOn ⟨z1, hz1, le_rfl⟩ hAcont
  have hle : ∀ z ∉ S, f z ≤ f z2 := by
    intro z hz
    by_cases h : f z1 ≤ f z
    · exact isMaxOn_iff.1 hmax z ⟨hz, h⟩
    · push_neg at h
      linarith [hz2A.2]
  set Z := {z | z ∉ S ∧ f z = f z2} with hZdef
  have hZA : Z ⊆ A := fun z hz => ⟨hz.1, by rw [hz.2]; exact hz2A.2⟩
  have hZopen : IsOpen Z := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hS.isOpen_compl z hz.1
    have hfb : InnerProductSpace.HarmonicOnNhd f (ball z ε) := fun x hx => hf x (hball hx)
    obtain ⟨F, hFa, hFeq⟩ := hfb.exists_analyticOnNhd_ball_re_eq
    have hd : ∀ᶠ y in 𝓝 z, DifferentiableAt ℂ (fun y => Complex.exp (F y)) y := by
      filter_upwards [ball_mem_nhds z hε] with y hy
      exact (hFa y hy).differentiableAt.cexp
    have hnorm : ∀ y ∈ ball z ε, ‖Complex.exp (F y)‖ = Real.exp (f y) := by
      intro y hy
      rw [Complex.norm_exp]
      congr 1
      exact hFeq hy
    have hloc : IsLocalMax (norm ∘ fun y => Complex.exp (F y)) z := by
      filter_upwards [ball_mem_nhds z hε] with y hy
      simp only [Function.comp_apply]
      rw [hnorm y hy, hnorm z (mem_ball_self hε), hz.2]
      exact Real.exp_le_exp.2 (hle y (hball hy))
    have hev := Complex.eventually_eq_of_isLocalMax_norm hd hloc
    filter_upwards [hev, ball_mem_nhds z hε] with y hy1 hy2
    refine ⟨hball hy2, ?_⟩
    have := congrArg norm hy1
    rw [hnorm y hy2, hnorm z (mem_ball_self hε), Real.exp_eq_exp] at this
    rw [this, hz.2]
  have hZclosed : IsClosed Z := by
    refine isClosed_of_closure_subset fun x hx => ?_
    have hxA : x ∈ A := hAclosed.closure_subset (closure_mono hZA hx)
    refine ⟨hxA.1, ?_⟩
    by_contra hne
    have hev : ∀ᶠ y in 𝓝 x, f y ≠ f z2 := (hcont x hxA.1).eventually (isOpen_ne.mem_nhds hne)
    rw [mem_closure_iff_nhds] at hx
    obtain ⟨y, hy1, hy2⟩ := hx _ hev
    exact hy1 hy2.2
  rcases isClopen_iff.1 ⟨hZclosed, hZopen⟩ with h0 | h0
  · have : z2 ∈ Z := ⟨hz2A.1, rfl⟩
    rw [h0] at this
    exact this
  · have hmem : ((R + 1 : ℝ) : ℂ) ∈ Z := by rw [h0]; exact mem_univ _
    have := hAsub (hZA hmem)
    rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs] at this
    linarith [le_abs_self (R + 1)]

/-! ### Kernel estimates -/

/-- Nearest-point estimate: if `‖y‖ ≤ 2 ‖x‖` then `logKer N x ≤ log 2 + logKer N y`. -/
lemma logKer_le_log_two_add (N : ℕ) {x y : ℂ} (h : ‖y‖ ≤ 2 * ‖x‖) :
    logKer N x ≤ Real.log 2 + logKer N y := by
  unfold logKer
  set e := Real.exp (-(N : ℝ)) with he
  have he0 : 0 < e := Real.exp_pos _
  have hy0 : 0 < max ‖y‖ e := lt_max_of_lt_right he0
  have h1 : max ‖y‖ e / 2 ≤ max ‖x‖ e := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    refine max_le (h.trans ?_) ?_
    · rw [mul_comm]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by norm_num)
    · nlinarith [le_max_right ‖x‖ e]
  have := Real.log_le_log (by positivity) h1
  rw [Real.log_div hy0.ne' two_ne_zero] at this
  linarith

/-- The truncated potential agrees with the potential at large truncation levels, away from the
support. -/
lemma potT_eq_toReal_of_dist {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : Integrable (fun w => ‖w‖) μ) {C : Set ℂ} (hμC : μ Cᶜ = 0) {y : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (hyC : ∀ w ∈ C, δ ≤ ‖y - w‖) {N : ℕ} (hN : Real.exp (-(N : ℝ)) ≤ δ) :
    potT μ N y = (logPotential μ y).toReal := by
  rw [logPotential_eq_integral_of_dist hμ hμC hδ hyC, EReal.toReal_coe]
  have hae : ∀ᵐ w ∂μ, w ∈ C := measure_eq_zero_iff_ae_notMem.1 hμC |>.mono fun w hw => by
    simpa using hw
  exact integral_congr_ae (hae.mono fun w hw => logKer_of_le (hN.trans (hyC w hw)))

lemma exists_exp_neg_le {δ : ℝ} (hδ : 0 < δ) : ∃ N : ℕ, Real.exp (-(N : ℝ)) ≤ δ := by
  obtain ⟨N, hN⟩ := exists_nat_gt (-Real.log δ)
  exact ⟨N, by rw [← Real.exp_log hδ]; exact Real.exp_le_exp.2 (by linarith)⟩

/-- `Φ_μ(z) → -∞` as `z → ∞`, for probability measures carried by a compact set. -/
theorem exists_logPotential_lt_of_far {μ : Measure ℂ} [IsProbabilityMeasure μ] {K : Set ℂ}
    (hK : IsCompact K) (hμK : μ Kᶜ = 0) (c : ℝ) :
    ∃ R, ∀ z, R < ‖z‖ → (logPotential μ z).toReal < c := by
  have hμ := integrable_norm_of_compact hK hμK
  obtain ⟨R0, hR0⟩ := hK.isBounded.subset_closedBall 0
  set R1 := max R0 0
  refine ⟨R1 + Real.exp (-c), fun z hz => ?_⟩
  set d := ‖z‖ - R1 with hd
  have hd0 : Real.exp (-c) < d := by rw [hd]; linarith
  have hdpos : 0 < d := lt_trans (Real.exp_pos _) hd0
  have hdist : ∀ w ∈ K, d ≤ ‖z - w‖ := by
    intro w hw
    have h1 : ‖w‖ ≤ R1 := by
      have := hR0 hw
      rw [mem_closedBall, dist_zero_right] at this
      exact this.trans (le_max_left _ _)
    have := norm_sub_norm_le z w
    rw [hd]
    linarith
  obtain ⟨N, hN⟩ := exists_exp_neg_le hdpos
  rw [← potT_eq_toReal_of_dist hμ hμK hdpos hdist hN]
  have hae : ∀ᵐ w ∂μ, w ∈ K := measure_eq_zero_iff_ae_notMem.1 hμK |>.mono fun w hw => by
    simpa using hw
  have hle : potT μ N z ≤ -Real.log d := by
    have := integral_mono_ae (integrable_logKer hμ N z) (integrable_const (-Real.log d))
      (hae.mono fun w hw => by
        show logKer N (z - w) ≤ -Real.log d
        rw [logKer_of_le (hN.trans (hdist w hw))]
        exact neg_le_neg (Real.log_le_log hdpos (hdist w hw)))
    rwa [integral_const, smul_eq_mul, measureReal_def, measure_univ, ENNReal.toReal_one,
      one_mul] at this
  have hlog : -c < Real.log d := (Real.lt_log_iff_exp_lt hdpos).2 hd0
  linarith

/-! ### The continuity principle -/

section Continuity

variable {K : Set ℂ} {ρ : Measure ℂ}

/-- The continuity principle at points of `supp ρ` for an equilibrium measure:
`Φ_ρ < c` near `z₀ ∈ supp ρ` whenever `c > E(ρ)`. -/
theorem IsEquilibriumMeasure.eventually_logPotential_lt (hK : IsCompact K)
    (hcap : capCompact K ≠ 0) (h : IsEquilibriumMeasure K ρ) {z0 : ℂ} (hz0 : z0 ∈ ρ.support)
    {c : ℝ} (hc : (energy ρ).toReal < c) :
    ∀ᶠ z in 𝓝 z0, (logPotential ρ z).toReal < c := by
  set E := (energy ρ).toReal with hEdef
  have hρa := adm_of_M1 hK h.1
  haveI := h.1.1
  set ε := c - E with hεdef
  have hε : 0 < ε := by linarith
  -- `z₀` is not an atom
  have hatom : ρ {z0} = 0 := by
    by_contra hne
    exact h.energy_ne_top hcap (energy_eq_top_of_atom hρa.2 hne)
  -- a closed ball of small mass
  have htend : Tendsto (fun n : ℕ => ρ (closedBall z0 (1 / ((n : ℝ) + 1)))) atTop
      (𝓝 (ρ {z0})) := by
    have hinter : (⋂ n : ℕ, closedBall z0 (1 / ((n : ℝ) + 1))) = {z0} := by
      ext x
      simp only [mem_iInter, mem_closedBall, mem_singleton_iff]
      constructor
      · intro hx
        by_contra hne
        have hpos : 0 < dist x z0 := dist_pos.2 hne
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
        linarith [hx n]
      · rintro rfl n
        rw [dist_self]
        positivity
    rw [← hinter]
    refine tendsto_measure_iInter_atTop (fun n => isClosed_closedBall.measurableSet.nullMeasurableSet)
      (fun m n hmn => closedBall_subset_closedBall ?_) ⟨0, measure_ne_top _ _⟩
    have : (m : ℝ) ≤ n := by exact_mod_cast hmn
    exact one_div_le_one_div_of_le (by positivity) (by linarith)
  rw [hatom] at htend
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpos' : (0 : ℝ≥0∞) < ENNReal.ofReal (ε / (4 * Real.log 2)) :=
    ENNReal.ofReal_pos.2 (by positivity)
  obtain ⟨n, hn⟩ := (htend.eventually (gt_mem_nhds hpos')).exists
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = 1 / ((n : ℝ) + 1) := ⟨_, rfl⟩
  have hr : 0 < r := by rw [hrdef]; positivity
  obtain ⟨B, hBdef⟩ : ∃ B : Set ℂ, B = closedBall z0 r := ⟨_, rfl⟩
  rw [← hrdef, ← hBdef] at hn
  have hBm : MeasurableSet B := by rw [hBdef]; exact isClosed_closedBall.measurableSet
  have hm1 : (ρ B).toReal * Real.log 2 < ε / 4 := by
    have h1 := (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).2 hn
    rw [ENNReal.toReal_ofReal (by positivity)] at h1
    calc (ρ B).toReal * Real.log 2 < ε / (4 * Real.log 2) * Real.log 2 :=
          mul_lt_mul_of_pos_right h1 hlog2
      _ = ε / 4 := by field_simp
  have hi1 : Integrable (fun w => ‖w‖) (ρ.restrict B) := hρa.2.restrict
  have hi2 : Integrable (fun w => ‖w‖) (ρ.restrict Bᶜ) := hρa.2.restrict
  -- the potential of the part off `B` is continuous at `z₀`
  set K2 := K ∩ (ball z0 r)ᶜ with hK2def
  have hK2 : IsCompact K2 := hK.inter_right isOpen_ball.isClosed_compl
  have hμ2K2 : ρ.restrict Bᶜ K2ᶜ = 0 := by
    rw [hK2def, compl_inter, compl_compl]
    refine measure_union_null ?_ ?_
    · exact le_antisymm ((Measure.restrict_le_self (s := Bᶜ) (μ := ρ) Kᶜ).trans h.1.2.le)
        zero_le
    · rw [Measure.restrict_apply isOpen_ball.measurableSet]
      refine measure_mono_null (fun x hx => ?_) measure_empty
      exact (hx.2 (by rw [hBdef]; exact ball_subset_closedBall hx.1)).elim
  obtain ⟨P2, hP2def⟩ : ∃ P2 : ℂ → ℝ, P2 = fun y => (logPotential (ρ.restrict Bᶜ) y).toReal :=
    ⟨_, rfl⟩
  have hP2 : InnerProductSpace.HarmonicOnNhd P2 K2ᶜ := by
    rw [hP2def]; exact harmonicOnNhd_logPotential hK2 hμ2K2
  have hz0K2 : z0 ∈ K2ᶜ := by
    rw [hK2def, compl_inter, compl_compl]; exact Or.inr (mem_ball_self hr)
  obtain ⟨s, hs, hsP⟩ := Metric.continuousAt_iff.1 (hP2 z0 hz0K2).1.continuousAt (ε / 8)
    (by positivity)
  -- distances to the part off `B`
  have hμ2C : ρ.restrict Bᶜ Bᶜᶜ = 0 := by
    rw [Measure.restrict_apply' hBm.compl, compl_inter_self, measure_empty]
  have hdist2 : ∀ y, ‖y - z0‖ < r / 2 → ∀ w ∈ Bᶜ, r / 2 ≤ ‖y - w‖ := by
    intro y hy w hw
    have hw' : r < ‖w - z0‖ := by
      rw [hBdef, mem_compl_iff, mem_closedBall, dist_eq_norm, not_le] at hw
      exact hw
    have := norm_sub_le_norm_sub_add_norm_sub w y z0
    rw [norm_sub_rev w y] at this
    linarith
  obtain ⟨N0, hN0⟩ := exists_exp_neg_le (half_pos hr)
  have hP2eq : ∀ y, ‖y - z0‖ < r / 2 → ∀ N, N0 ≤ N → potT (ρ.restrict Bᶜ) N y = P2 y := by
    intro y hy N hN
    rw [hP2def]
    exact potT_eq_toReal_of_dist hi2 hμ2C (half_pos hr) (hdist2 y hy)
      ((Real.exp_le_exp.2 (neg_le_neg (by exact_mod_cast hN))).trans hN0)
  -- support of the part on `B`
  have hsupp1 : (ρ.restrict B).support ⊆ ρ.support :=
    Measure.support_mono Measure.restrict_le_self
  have hsupp1B : (ρ.restrict B).support ⊆ B :=
    Measure.support_subset_of_isClosed (by rw [hBdef]; exact isClosed_closedBall)
      (ae_restrict_mem hBm)
  have hz0s1 : z0 ∈ (ρ.restrict B).support := by
    rw [Measure.mem_support_iff_forall] at hz0 ⊢
    intro U hU
    have h1 := hz0 (U ∩ ball z0 r) (inter_mem hU (ball_mem_nhds z0 hr))
    calc 0 < ρ (U ∩ ball z0 r) := h1
      _ ≤ ρ.restrict B U := by
        rw [Measure.restrict_apply' hBm]
        exact measure_mono (inter_subset_inter_right _ (by rw [hBdef]; exact ball_subset_closedBall))
  have hcpt1 : IsCompact (ρ.restrict B).support :=
    (by rw [hBdef]; exact isCompact_closedBall z0 r : IsCompact B).of_isClosed_subset
      Measure.isClosed_support hsupp1B
  -- the neighbourhood
  set s' := min s (r / 2) with hs'def
  have hs' : 0 < s' := lt_min hs (by positivity)
  filter_upwards [ball_mem_nhds z0 (half_pos hs')] with z hz
  have hz' : ‖z - z0‖ < s' / 2 := by rwa [mem_ball, dist_eq_norm] at hz
  obtain ⟨zs, hzs, hmin⟩ := hcpt1.exists_isMinOn ⟨z0, hz0s1⟩
    (continuous_const.dist continuous_id : Continuous fun w => dist z w).continuousOn
  have hmin' : ∀ w ∈ (ρ.restrict B).support, ‖z - zs‖ ≤ ‖z - w‖ := fun w hw => by
    have := isMinOn_iff.1 hmin w hw
    simpa only [dist_eq_norm] using this
  have hzzs : ‖z - zs‖ < s' / 2 := lt_of_le_of_lt (hmin' z0 hz0s1) hz'
  have hzs0 : ‖zs - z0‖ < s' := by
    calc ‖zs - z0‖ ≤ ‖zs - z‖ + ‖z - z0‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ < s' / 2 + s' / 2 := add_lt_add (by rw [norm_sub_rev]; exact hzzs) hz'
      _ = s' := by ring
  have hs's : s' ≤ s := min_le_left _ _
  have hs'r : s' ≤ r / 2 := min_le_right _ _
  have hzr : ‖z - z0‖ < r / 2 := by linarith
  have hzsr : ‖zs - z0‖ < r / 2 := by linarith
  have hP2z : |P2 z - P2 z0| < ε / 8 := by
    have := hsP (show dist z z0 < s by rw [dist_eq_norm]; linarith)
    rwa [Real.dist_eq] at this
  have hP2zs : |P2 zs - P2 z0| < ε / 8 := by
    have := hsP (show dist zs z0 < s by rw [dist_eq_norm]; linarith)
    rwa [Real.dist_eq] at this
  have hP2diff : P2 z - P2 zs < ε / 4 := by
    have h1 := (abs_lt.1 hP2z).2
    have h2 := (abs_lt.1 hP2zs).1
    linarith
  -- `Φ_ρ(zs) ≤ E`
  have hzsE : ∀ N, potT ρ N zs ≤ E := by
    intro N
    have h1 := h.logPotential_le_of_mem_support hK hcap (hsupp1 hzs)
    rw [h.energy_eq_coe hcap] at h1
    exact EReal.coe_le_coe_iff.1
      ((le_iSup (fun N : ℕ => ((potT ρ N zs : ℝ) : EReal)) N).trans h1)
  -- the nearest-point estimate
  have hb1 : ∀ N, potT (ρ.restrict B) N z ≤
      (ρ B).toReal * Real.log 2 + potT (ρ.restrict B) N zs := by
    intro N
    have hae : ∀ᵐ w ∂(ρ.restrict B), w ∈ (ρ.restrict B).support := Measure.support_mem_ae
    have hint2 := (integrable_const (Real.log 2)).add (integrable_logKer hi1 N zs)
    have hkey : ∀ᵐ w ∂(ρ.restrict B), logKer N (z - w) ≤ Real.log 2 + logKer N (zs - w) :=
      hae.mono fun w hw => logKer_le_log_two_add N (by
        have h1 := hmin' w hw
        have h2 : ‖zs - w‖ ≤ ‖zs - z‖ + ‖z - w‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        rw [norm_sub_rev zs z] at h2
        linarith)
    calc potT (ρ.restrict B) N z ≤ ∫ w, (Real.log 2 + logKer N (zs - w)) ∂(ρ.restrict B) :=
          integral_mono_ae (integrable_logKer hi1 N z) hint2 hkey
      _ = (ρ B).toReal * Real.log 2 + potT (ρ.restrict B) N zs := by
          rw [integral_add (integrable_const _) (integrable_logKer hi1 N zs), integral_const,
            smul_eq_mul, measureReal_def, Measure.restrict_apply_univ]
  have hbound : ∀ N, N0 ≤ N → potT ρ N z ≤ E + 3 * ε / 4 := by
    intro N hN
    have e1 := (integral_add_compl hBm (integrable_logKer hρa.2 N z)).symm
    have e2 := (integral_add_compl hBm (integrable_logKer hρa.2 N zs)).symm
    have h1 := hb1 N
    have h2 := hzsE N
    have h3 := hP2eq z hzr N hN
    have h4 := hP2eq zs hzsr N hN
    show ∫ w, logKer N (z - w) ∂ρ ≤ E + 3 * ε / 4
    have h2' : ∫ w, logKer N (zs - w) ∂ρ ≤ E := h2
    rw [e1]
    rw [e2] at h2'
    change potT (ρ.restrict B) N z + potT (ρ.restrict Bᶜ) N z ≤ E + 3 * ε / 4
    change potT (ρ.restrict B) N zs + potT (ρ.restrict Bᶜ) N zs ≤ E at h2'
    linarith
  have hle : logPotential ρ z ≤ ((E + 3 * ε / 4 : ℝ) : EReal) := by
    refine iSup_le fun N => ?_
    rw [EReal.coe_le_coe_iff]
    exact (potTrunc_mono hρa.2 z (le_max_left N N0)).trans (hbound _ (le_max_right _ _))
  have := EReal.toReal_le_toReal hle (logPotential_ne_bot ρ z) (EReal.coe_ne_top _)
  rw [EReal.toReal_coe] at this
  linarith

/-- **Theorem A.2.8 (i)** (Frostman): `Φ_ρ ≤ E(ρ)` on all of `ℂ`. -/
theorem IsEquilibriumMeasure.logPotential_le_energy (hK : IsCompact K) (hcap : capCompact K ≠ 0)
    (h : IsEquilibriumMeasure K ρ) (z : ℂ) : logPotential ρ z ≤ energy ρ := by
  by_cases hz : z ∈ ρ.support
  · exact h.logPotential_le_of_mem_support hK hcap hz
  haveI := h.1.1
  have hρa := adm_of_M1 hK h.1
  set S := ρ.support with hSdef
  have hSK : S ⊆ K := Measure.support_subset_of_isClosed hK.isClosed (mem_ae_iff.2 h.1.2)
  have hScpt : IsCompact S := hK.of_isClosed_subset Measure.isClosed_support hSK
  have hρS : ρ Sᶜ = 0 := Measure.measure_compl_support
  have hharm := harmonicOnNhd_logPotential (μ := ρ) hScpt hρS
  set E := (energy ρ).toReal with hEdef
  -- `Φ_ρ(z)` is finite
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hScpt.isClosed.isOpen_compl z hz
  have hdist : ∀ w ∈ S, δ ≤ ‖z - w‖ := by
    intro w hw
    by_contra hlt
    push_neg at hlt
    exact hball (by rw [mem_ball, dist_eq_norm, norm_sub_rev]; exact hlt) hw
  have hfin : logPotential ρ z ≠ ⊤ := (logPotential_lt_top_of_dist hρa.2 hρS hδ hdist).ne
  rw [h.energy_eq_coe hcap, ← EReal.coe_toReal hfin (logPotential_ne_bot ρ z),
    EReal.coe_le_coe_iff]
  by_contra hgt
  push_neg at hgt
  obtain ⟨R, hR⟩ := exists_logPotential_lt_of_far hK h.1.2 (logPotential ρ z).toReal
  have := lt_of_harmonicOnNhd_compl (S := S) hScpt.isClosed hharm
    (c := (logPotential ρ z).toReal)
    (fun z0 hz0 => (h.eventually_logPotential_lt hK hcap hz0 hgt).mono fun y hy _ => hy) hR z hz
  exact lt_irrefl _ this

end Continuity

/-! ### Countable unions of compact sets of capacity zero -/

lemma iint_normSum_le {ν : Measure ℂ} [IsProbabilityMeasure ν] {C : Set ℂ} (hνC : ν Cᶜ = 0)
    {R : ℝ} (hR : ∀ z ∈ C, ‖z‖ ≤ R) : ∫ z, ∫ w, (‖z‖ + ‖w‖) ∂ν ∂ν ≤ 2 * R := by
  have hae : ∀ᵐ w ∂ν, w ∈ C := measure_eq_zero_iff_ae_notMem.1 hνC |>.mono fun w hw => by
    simpa using hw
  have hin : ∀ z ∈ C, ∫ w, (‖z‖ + ‖w‖) ∂ν ≤ 2 * R := by
    intro z hz
    have := integral_mono_of_nonneg
      (Eventually.of_forall fun w => add_nonneg (norm_nonneg z) (norm_nonneg w) :
        0 ≤ᵐ[ν] fun w => ‖z‖ + ‖w‖)
      (integrable_const (2 * R)) (hae.mono fun w hw => by
        show ‖z‖ + ‖w‖ ≤ 2 * R
        linarith [hR z hz, hR w hw])
    rwa [integral_const, smul_eq_mul, measureReal_def, measure_univ, ENNReal.toReal_one,
      one_mul] at this
  have := integral_mono_of_nonneg
    (Eventually.of_forall fun z => integral_nonneg fun w => add_nonneg (norm_nonneg z)
      (norm_nonneg w) : 0 ≤ᵐ[ν] fun z => ∫ w, (‖z‖ + ‖w‖) ∂ν)
    (integrable_const (2 * R)) (hae.mono fun z hz => hin z hz)
  rwa [integral_const, smul_eq_mul, measureReal_def, measure_univ, ENNReal.toReal_one,
    one_mul] at this

lemma exists_open_of_capacity_lt {B : Set ℂ} {ε : ℝ≥0∞} (h : capacity B < ε) :
    ∃ O : Set ℂ, IsOpen O ∧ Bornology.IsBounded O ∧ B ⊆ O ∧
      ∀ C, IsCompact C → C ⊆ O → capCompact C < ε := by
  unfold capacity at h
  simp only [iInf_lt_iff] at h
  obtain ⟨O, hO, hOb, hBO, hlt⟩ := h
  exact ⟨O, hO, hOb, hBO, fun C hC hCO =>
    lt_of_le_of_lt ((le_iSup (fun _ : C ⊆ O => capCompact C) hCO).trans
      ((le_iSup (fun _ : IsCompact C => ⨆ (_ : C ⊆ O), capCompact C) hC).trans
        (le_iSup (fun C' => ⨆ (_ : IsCompact C') (_ : C' ⊆ O), capCompact C') C))) hlt⟩

/-- A countable union of compact sets of capacity zero (inside a fixed ball) has capacity zero.
(A probability measure on a compact `C ⊆ ⋃_{i ∈ t} Cᵢ` with energy `E` puts mass
`mᵢ ≤ ((E + 2R)/aᵢ)^{1/2}` on `Cᵢ` if `Cap(Cᵢ) ≤ e^{-aᵢ}`; with `aᵢ = A 4^{i+1}` these masses
cannot add up to `1` unless `E ≥ A - 2R`.) -/
theorem capacity_iUnion_eq_zero {L : ℕ → Set ℂ} (hL : ∀ n, IsCompact (L n))
    (h0 : ∀ n, capCompact (L n) = 0) {R0 : ℝ} (hsub : ∀ n, L n ⊆ ball 0 R0) :
    capacity (⋃ n, L n) = 0 := by
  have key : ∀ A : ℝ, 0 < A →
      capacity (⋃ n, L n) ≤ ENNReal.ofReal (Real.exp (-(A - 2 * R0))) := by
    intro A hA
    obtain ⟨a, hadef⟩ : ∃ a : ℕ → ℝ, ∀ i, a i = A * ((2 : ℝ) ^ (i + 1)) ^ 2 :=
      ⟨_, fun i => rfl⟩
    have hU : ∀ n, ∃ O : Set ℂ, IsOpen O ∧ Bornology.IsBounded O ∧ L n ⊆ O ∧
        ∀ C, IsCompact C → C ⊆ O → capCompact C < ENNReal.ofReal (Real.exp (-a n)) := by
      intro n
      refine exists_open_of_capacity_lt ?_
      rw [capacity_eq_capCompact (hL n), h0 n]
      exact ENNReal.ofReal_pos.2 (Real.exp_pos _)
    choose U hUo hUb hLU hUc using hU
    obtain ⟨V, hVdef⟩ : ∃ V : ℕ → Set ℂ, V = fun n => U n ∩ ball 0 R0 := ⟨_, rfl⟩
    have hVo : ∀ n, IsOpen (V n) := fun n => by rw [hVdef]; exact (hUo n).inter isOpen_ball
    have hVU : ∀ n, V n ⊆ U n := fun n => by rw [hVdef]; exact inter_subset_left
    have hVb : ∀ n, V n ⊆ ball 0 R0 := fun n => by rw [hVdef]; exact inter_subset_right
    have hLV : ∀ n, L n ⊆ V n := fun n => by rw [hVdef]; exact subset_inter (hLU n) (hsub n)
    unfold capacity
    refine iInf_le_of_le (⋃ n, V n) (iInf_le_of_le (isOpen_iUnion hVo)
      (iInf_le_of_le (Metric.isBounded_ball.subset (iUnion_subset hVb))
        (iInf_le_of_le (iUnion_mono hLV) ?_)))
    refine iSup_le fun C => iSup_le fun hC => iSup_le fun hCO => ?_
    obtain ⟨t, ht⟩ := hC.elim_finite_subcover V hVo hCO
    obtain ⟨Ci, hCic, hCiV, hCeq⟩ := hC.finite_compact_cover t V (fun i _ => hVo i) ht
    have hR : ∀ z ∈ C, ‖z‖ ≤ R0 := by
      intro z hz
      obtain ⟨n, hn⟩ := mem_iUnion.1 (hCO hz)
      have := hVb n hn
      rw [mem_ball, dist_zero_right] at this
      exact this.le
    rw [show ENNReal.ofReal (Real.exp (-(A - 2 * R0))) = expNeg ((A - 2 * R0 : ℝ) : EReal) by
      rw [expNeg_coe]]
    show expNeg (⨅ μ ∈ M1 C, energy μ) ≤ _
    refine expNeg_antitone (le_iInf₂ fun ν hν => ?_)
    haveI := hν.1
    by_cases htop : energy ν = ⊤
    · rw [htop]; exact le_top
    obtain ⟨E', hE'⟩ : ∃ E' : ℝ, energy ν = (E' : EReal) :=
      ⟨_, (EReal.coe_toReal htop (energy_ne_bot ν)).symm⟩
    rw [hE', EReal.coe_le_coe_iff]
    by_contra hlt
    push_neg at hlt
    have hνa : Adm ν := ⟨inferInstance, integrable_norm_of_compact hC hν.2⟩
    obtain ⟨X, hX⟩ : ∃ X : ℝ, X = E' + ∫ z, ∫ w, (‖z‖ + ‖w‖) ∂ν ∂ν := ⟨_, rfl⟩
    have hXA : X < A := by
      have := iint_normSum_le hν.2 hR
      rw [hX]
      linarith
    have hItr : ∀ N, Itr N ν ν ≤ E' := fun N => by
      have := Itr_le_energy ν N
      rwa [hE', EReal.coe_le_coe_iff] at this
    have hmass : ∀ i ∈ t, (ν (Ci i)).toReal < (1 / 2 : ℝ) ^ (i + 1) := by
      intro i _
      obtain ⟨m, hm⟩ : ∃ m : ℝ, m = (ν (Ci i)).toReal := ⟨_, rfl⟩
      rw [← hm]
      have hm0 : 0 ≤ m := by rw [hm]; exact ENNReal.toReal_nonneg
      rcases hm0.eq_or_lt with hm0' | hmpos
      · rw [← hm0']; positivity
      have hνCi : ν (Ci i) ≠ 0 := fun h => by
        rw [hm, h, ENNReal.toReal_zero] at hmpos
        exact lt_irrefl _ hmpos
      set c : ℝ≥0∞ := (ν (Ci i))⁻¹ with hc
      have hcR : c.toReal = m⁻¹ := by rw [hc, ENNReal.toReal_inv, ← hm]
      set η := c • ν.restrict (Ci i) with hη
      have hηM : η ∈ M1 (Ci i) := by
        refine ⟨⟨?_⟩, ?_⟩
        · simp only [hη, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul, hc]
          exact ENNReal.inv_mul_cancel hνCi (measure_ne_top _ _)
        · simp only [hη, Measure.smul_apply, smul_eq_mul]
          rw [Measure.restrict_apply (hCic i).measurableSet.compl, compl_inter_self,
            measure_empty, mul_zero]
      have hItrη : ∀ N, Itr N η η ≤ m⁻¹ * (m⁻¹ * X) := by
        intro N
        rw [hη, Itr_smul_left, Itr_smul_right, hcR]
        have h1 := Itr_restrict_le hνa (Ci i) N
        have h2 := hItr N
        have hm1 : 0 ≤ m⁻¹ := inv_nonneg.2 hm0
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hm1) hm1
        rw [hX]
        linarith
      have hEη : energy η ≤ ((m⁻¹ * (m⁻¹ * X) : ℝ) : EReal) :=
        iSup_le fun N => EReal.coe_le_coe_iff.2 (hItrη N)
      have hηne : energy η ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hEη
      have hcapi : capCompact (Ci i) < ENNReal.ofReal (Real.exp (-a i)) :=
        hUc i (Ci i) (hCic i) ((hCiV i).trans (hVU i))
      have h1 := (expNeg_energy_le_capCompact hηM).trans hcapi.le
      obtain ⟨e, he⟩ : ∃ e : ℝ, energy η = (e : EReal) :=
        ⟨_, (EReal.coe_toReal hηne (energy_ne_bot η)).symm⟩
      rw [he, expNeg_coe, ENNReal.ofReal_le_ofReal_iff (Real.exp_pos _).le,
        Real.exp_le_exp] at h1
      have h2 : e ≤ m⁻¹ * (m⁻¹ * X) := by
        rw [he] at hEη
        exact EReal.coe_le_coe_iff.1 hEη
      have h3 : a i * m ^ 2 ≤ X := by
        have := mul_le_mul_of_nonneg_right (show a i ≤ m⁻¹ * (m⁻¹ * X) by linarith)
          (sq_nonneg m)
        calc a i * m ^ 2 ≤ m⁻¹ * (m⁻¹ * X) * m ^ 2 := this
          _ = X := by field_simp
      have h4 : ((2 : ℝ) ^ (i + 1) * m) ^ 2 < 1 := by
        have h5 : A * ((2 : ℝ) ^ (i + 1) * m) ^ 2 < A * 1 := by
          rw [mul_one]
          calc A * ((2 : ℝ) ^ (i + 1) * m) ^ 2 = a i * m ^ 2 := by rw [hadef]; ring
            _ ≤ X := h3
            _ < A := hXA
        exact lt_of_mul_lt_mul_left h5 hA.le
      have h5 : (2 : ℝ) ^ (i + 1) * m < 1 :=
        (pow_lt_one_iff_of_nonneg (by positivity) two_ne_zero).1 h4
      have h6 : (0 : ℝ) < 2 ^ (i + 1) := by positivity
      rw [one_div_pow, lt_div_iff₀ h6]
      linarith
    have hνC : ν C = 1 := (prob_compl_eq_zero_iff hC.measurableSet).1 hν.2
    have hsum : (1 : ℝ) ≤ ∑ i ∈ t, (ν (Ci i)).toReal := by
      have h1 : ν C ≤ ∑ i ∈ t, ν (Ci i) := by
        rw [hCeq]
        exact measure_biUnion_finset_le t Ci
      have h2 := ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun i _ => measure_ne_top _ _) h1
      rwa [hνC, ENNReal.toReal_one, ENNReal.toReal_sum (fun i _ => measure_ne_top _ _)] at h2
    have hne : t.Nonempty := by
      by_contra hemp
      rw [Finset.not_nonempty_iff_eq_empty] at hemp
      rw [hemp, Finset.sum_empty] at hsum
      linarith
    have hlt' := Finset.sum_lt_sum_of_nonempty hne hmass
    have hgeom : ∑ i ∈ t, (1 / 2 : ℝ) ^ (i + 1) ≤ 1 := by
      obtain ⟨M, hM⟩ : ∃ M, t ⊆ Finset.range M :=
        ⟨t.sup id + 1, fun i hi =>
          Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hi))⟩
      calc ∑ i ∈ t, (1 / 2 : ℝ) ^ (i + 1) ≤ ∑ i ∈ Finset.range M, (1 / 2 : ℝ) ^ (i + 1) :=
            Finset.sum_le_sum_of_subset_of_nonneg hM (fun _ _ _ => by positivity)
        _ = (1 / 2) * ∑ i ∈ Finset.range M, (1 / 2 : ℝ) ^ i := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
        _ ≤ (1 / 2) * 2 := by gcongr; exact sum_geometric_two_le M
        _ = 1 := by norm_num
    linarith
  have htend : Tendsto (fun n : ℕ => -(((n : ℝ) + 1) - 2 * R0)) atTop atBot := by
    refine tendsto_neg_atTop_atBot.comp (tendsto_atTop_atTop.2 fun b => ?_)
    obtain ⟨N, hN⟩ := exists_nat_ge (b + 2 * R0)
    exact ⟨N, fun n hn => by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith⟩
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (-(((n : ℝ) + 1) - 2 * R0))))
      atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal (Real.tendsto_exp_atBot.comp htend)
  exact le_antisymm (le_of_tendsto' hlim fun n : ℕ => key ((n : ℝ) + 1) (by positivity)) zero_le

/-! ### Theorem A.2.8 (ii) -/

/-- **Theorem A.2.8 (ii)** (Frostman): `Φ_ρ ≥ E(ρ)` quasi-everywhere on `K`. -/
theorem IsEquilibriumMeasure.capacity_lt_eq_zero {K : Set ℂ} {ρ : Measure ℂ} (hK : IsCompact K)
    (hcap : capCompact K ≠ 0) (h : IsEquilibriumMeasure K ρ) :
    capacity {z ∈ K | logPotential ρ z < energy ρ} = 0 := by
  haveI := h.1.1
  have hρa := adm_of_M1 hK h.1
  have hEeq := h.energy_eq_coe hcap
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = (energy ρ).toReal := ⟨_, rfl⟩
  rw [← hE] at hEeq
  obtain ⟨L, hLdef⟩ : ∃ L : ℕ → Set ℂ,
      L = fun n : ℕ => K ∩ logPotential ρ ⁻¹' Iic ((E - 1 / ((n : ℝ) + 1) : ℝ) : EReal) :=
    ⟨_, rfl⟩
  have hLc : ∀ n, IsCompact (L n) := fun n => by
    rw [hLdef]
    exact hK.inter_right ((lowerSemicontinuous_logPotential hρa.2).isClosed_preimage _)
  have hL0 : ∀ n, capCompact (L n) = 0 := by
    intro n
    rw [capCompact_eq_zero_iff]
    intro ν hν
    by_contra hνt
    haveI := hν.1
    have hνK : ν ∈ M1 K := M1_mono (by rw [hLdef]; exact inter_subset_left) hν
    have hνa := adm_of_M1 hK hνK
    have hB : ∀ N, Itr N ν ν ≤ (energy ν).toReal := fun N => by
      have := Itr_le_energy ν N
      rwa [(EReal.coe_toReal hνt (energy_ne_bot ν)).symm, EReal.coe_le_coe_iff] at this
    have hγ : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hae : ∀ᵐ z ∂ν, z ∈ L n := measure_eq_zero_iff_ae_notMem.1 hν.2 |>.mono fun z hz => by
      simpa using hz
    have hI : ∀ N, 0 ≤ N → Itr N ρ ν ≤ (energy ρ).toReal - 1 / ((n : ℝ) + 1) := by
      intro N _
      rw [← hE]
      have := integral_mono_ae (integrable_potTrunc_wrt hρa hνa N)
        (integrable_const (E - 1 / ((n : ℝ) + 1)))
        (hae.mono fun z hz => by
          have h1 : ((potT ρ N z : ℝ) : EReal) ≤ logPotential ρ z :=
            le_iSup (fun N : ℕ => ((potT ρ N z : ℝ) : EReal)) N
          have h2 : logPotential ρ z ≤ ((E - 1 / ((n : ℝ) + 1) : ℝ) : EReal) := by
            rw [hLdef] at hz
            exact hz.2
          exact EReal.coe_le_coe_iff.1 (h1.trans h2))
      rwa [integral_const, smul_eq_mul, measureReal_def, measure_univ, ENNReal.toReal_one,
        one_mul] at this
    obtain ⟨μ, hμ, hlt⟩ := exists_energy_lt_of_variation hK h.1 hνK hγ (h.Itr_le hcap) hB hI
    have := h.2 μ hμ
    rw [h.energy_eq_coe hcap] at this
    exact absurd (lt_of_le_of_lt this hlt) (lt_irrefl _)
  obtain ⟨R0, hR0⟩ := hK.isBounded.subset_ball 0
  have hLsub : ∀ n, L n ⊆ ball 0 R0 := fun n => by
    rw [hLdef]; exact inter_subset_left.trans hR0
  refine le_antisymm ((capacity_mono ?_).trans (capacity_iUnion_eq_zero hLc hL0 hLsub).le)
    zero_le
  intro z hz
  obtain ⟨hzK, hzlt⟩ := hz
  rw [hEeq] at hzlt
  have hnt : logPotential ρ z ≠ ⊤ := ne_top_of_lt hzlt
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ, logPotential ρ z = (φ : EReal) :=
    ⟨_, (EReal.coe_toReal hnt (logPotential_ne_bot ρ z)).symm⟩
  rw [hφ, EReal.coe_lt_coe_iff] at hzlt
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hzlt)
  refine mem_iUnion.2 ⟨n, ?_⟩
  rw [hLdef]
  refine ⟨hzK, ?_⟩
  show logPotential ρ z ≤ _
  rw [hφ, EReal.coe_le_coe_iff]
  linarith

/-- **Theorem A.2.8** (Frostman): the Statement `DF.FrostmanStatement`. -/
theorem frostmanStatement_holds : FrostmanStatement := fun _ _ hK hcap h =>
  ⟨h.logPotential_le_energy hK hcap, h.capacity_lt_eq_zero hK hcap⟩

end DF
