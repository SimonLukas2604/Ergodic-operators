/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Appendix A.2: the continuity principle and Lemma A.2.10 for compact sets

## Main results

* `DF.logPotential_add`, `DF.logPotential_smul_of_eq` — additivity and homogeneity of `Φ_μ`;
* `DF.logPotential_eq_top_of_atom` — `Φ_μ = +∞` at atoms of `μ`;
* `DF.restrict_potential_continuousOn` — if `Φ_μ` is finite and continuous on a compact set `L`,
  then so is `Φ_{μ|L}` (both `Φ_{μ|L}` and `Φ_{μ|Lᶜ}` are lower semicontinuous, and their sum
  is continuous on `L`);
* `DF.continuous_logPotential_of_carrier` — the **continuity principle** (Evans–Vasilesco): if
  `η` is carried by a compact set `S` and `Φ_η` is finite and continuous on `S`, then `Φ_η` is
  finite and continuous on all of `ℂ` (nearest-point estimate, as in the proof of Frostman's
  theorem);
* `DF.exists_continuous_potential_of_compact` — **Lemma A.2.10 for compact sets**: a compact set
  of positive capacity carries a probability measure with continuous potential.  (Restrict the
  equilibrium measure to a compact subset of `{Φ_ρ = E(ρ)}` of positive mass.)
-/
import DamanikFillman.AppA.FrostmanMain

noncomputable section

open Real Complex Metric Set Filter Topology MeasureTheory
open scoped ENNReal

namespace DF

variable {μ ν : Measure ℂ}

lemma tendsto_potT [IsFiniteMeasure μ] (hμ : Integrable (fun w => ‖w‖) μ) (z : ℂ) :
    Tendsto (fun N : ℕ => ((potT μ N z : ℝ) : EReal)) atTop (𝓝 (logPotential μ z)) :=
  tendsto_atTop_iSup fun _ _ hmn => EReal.coe_le_coe_iff.2 (potTrunc_mono hμ z hmn)

/-- Additivity of the logarithmic potential. -/
theorem logPotential_add [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : Integrable (fun w => ‖w‖) μ) (hν : Integrable (fun w => ‖w‖) ν) (z : ℂ) :
    logPotential (μ + ν) z = logPotential μ z + logPotential ν z := by
  have h1 := tendsto_potT hμ z
  have h2 := tendsto_potT hν z
  have h3 := tendsto_potT (hμ.add_measure hν) z
  have hsum : Tendsto (fun N : ℕ => ((potT μ N z : ℝ) : EReal) + ((potT ν N z : ℝ) : EReal))
      atTop (𝓝 (logPotential μ z + logPotential ν z)) :=
    (EReal.continuousAt_add (Or.inr (logPotential_ne_bot ν z))
      (Or.inl (logPotential_ne_bot μ z))).tendsto.comp (h1.prodMk_nhds h2)
  refine tendsto_nhds_unique h3 (hsum.congr fun N => ?_)
  rw [← EReal.coe_add]
  congr 1
  exact (integral_add_measure (integrable_logKer hμ N z) (integrable_logKer hν N z)).symm

/-- Homogeneity of the logarithmic potential at points where it is finite. -/
theorem logPotential_smul_of_eq [IsFiniteMeasure μ] (hμ : Integrable (fun w => ‖w‖) μ)
    {c : ℝ≥0∞} (hc : c ≠ ⊤) {z : ℂ} {a : ℝ} (ha : logPotential μ z = a) :
    logPotential (c • μ) z = ((c.toReal * a : ℝ) : EReal) := by
  have : IsFiniteMeasure (c • μ) := μ.smul_finite hc
  have h1 := tendsto_potT hμ z
  rw [ha] at h1
  have h1' : Tendsto (fun N : ℕ => potT μ N z) atTop (𝓝 a) := EReal.tendsto_coe.1 h1
  have h2 : Tendsto (fun N : ℕ => ((c.toReal * potT μ N z : ℝ) : EReal)) atTop
      (𝓝 ((c.toReal * a : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.tendsto _).comp (h1'.const_mul _)
  refine tendsto_nhds_unique (tendsto_potT (hμ.smul_measure hc) z) (h2.congr fun N => ?_)
  congr 1
  simp only [potT, integral_smul_measure, smul_eq_mul]

/-- The potential is `+∞` at an atom. -/
theorem logPotential_eq_top_of_atom [IsFiniteMeasure μ] (hμ : Integrable (fun w => ‖w‖) μ)
    {a : ℂ} (ha : μ {a} ≠ 0) : logPotential μ a = ⊤ := by
  set m := μ.real {a} with hmdef
  have hm : 0 < m := ENNReal.toReal_pos ha (measure_ne_top μ _)
  have hint : Integrable (fun w => ‖a - w‖) μ :=
    ((integrable_const ‖a‖).add hμ).mono' (continuous_const.sub continuous_id).norm.aestronglyMeasurable
      (Eventually.of_forall fun w => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact norm_sub_le a w)
  set C := ∫ w, ‖a - w‖ ∂μ
  have key : ∀ N : ℕ, m * N - C ≤ potT μ N a := by
    intro N
    have hle : ∀ w, ({a} : Set ℂ).indicator (fun _ => (N : ℝ)) w - ‖a - w‖ ≤ logKer N (a - w) := by
      intro w
      by_cases hw : w = a
      · subst hw; simp [logKer_zero]
      · rw [Set.indicator_of_notMem (by simpa using hw), zero_sub]
        exact neg_norm_le_logKer N (a - w)
    have hi1 : Integrable (({a} : Set ℂ).indicator (fun _ => (N : ℝ))) μ :=
      (integrable_const _).indicator (measurableSet_singleton a)
    have := integral_mono (hi1.sub hint) (integrable_logKer hμ N a) hle
    rw [integral_sub hi1 hint, integral_indicator_const _ (measurableSet_singleton a),
      smul_eq_mul] at this
    calc m * N - C = μ.real {a} * N - C := rfl
      _ ≤ potT μ N a := this
  refine EReal.eq_top_iff_forall_lt _ |>.2 fun y => ?_
  obtain ⟨N, hN⟩ := exists_nat_gt ((y + C + 1) / m)
  refine lt_of_lt_of_le ?_ (le_iSup (fun N : ℕ => ((potT μ N a : ℝ) : EReal)) N)
  rw [EReal.coe_lt_coe_iff]
  have h5 := key N
  have h6 : y + C + 1 < m * N := by rwa [div_lt_iff₀ hm, mul_comm] at hN
  linarith

/-- Lower semicontinuity of the real part of a lower semicontinuous potential, on a set where it
is finite. -/
lemma lowerSemicontinuousOn_toReal [IsFiniteMeasure μ] (hμ : Integrable (fun w => ‖w‖) μ)
    {L : Set ℂ} (hfin : ∀ z ∈ L, logPotential μ z ≠ ⊤) :
    LowerSemicontinuousOn (fun z => (logPotential μ z).toReal) L := by
  intro x hx y hy
  have hxe : logPotential μ x = (((logPotential μ x).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal (hfin x hx) (logPotential_ne_bot μ x)).symm
  have h1 : (y : EReal) < logPotential μ x := by rw [hxe]; exact EReal.coe_lt_coe_iff.2 hy
  have h2 := (lowerSemicontinuous_logPotential hμ) x y h1
  filter_upwards [nhdsWithin_le_nhds h2, self_mem_nhdsWithin] with x' hx' hx'L
  rw [← EReal.coe_toReal (hfin x' hx'L) (logPotential_ne_bot μ x')] at hx'
  exact EReal.coe_lt_coe_iff.1 hx'

/-- If `Φ_μ` is finite and continuous on a measurable set `L`, so is `Φ_{μ|L}`. -/
theorem restrict_potential_continuousOn [IsFiniteMeasure μ] (hμ : Integrable (fun w => ‖w‖) μ)
    {L : Set ℂ} (hLm : MeasurableSet L) {f : ℂ → ℝ} (hf : ContinuousOn f L)
    (heq : ∀ z ∈ L, logPotential μ z = f z) :
    (∀ z ∈ L, logPotential (μ.restrict L) z ≠ ⊤) ∧
      ContinuousOn (fun z => (logPotential (μ.restrict L) z).toReal) L := by
  have h1 : Integrable (fun w => ‖w‖) (μ.restrict L) := hμ.restrict
  have h2 : Integrable (fun w => ‖w‖) (μ.restrict Lᶜ) := hμ.restrict
  have hsplit : ∀ z, logPotential μ z =
      logPotential (μ.restrict L) z + logPotential (μ.restrict Lᶜ) z := by
    intro z
    conv_lhs => rw [← Measure.restrict_add_restrict_compl (μ := μ) hLm]
    exact logPotential_add h1 h2 z
  -- finiteness of both parts on `L`
  have hfin : ∀ z ∈ L, logPotential (μ.restrict L) z ≠ ⊤ ∧
      logPotential (μ.restrict Lᶜ) z ≠ ⊤ := by
    intro z hz
    have h := heq z hz
    rw [hsplit] at h
    constructor
    · intro ht
      rw [ht, EReal.top_add_of_ne_bot (logPotential_ne_bot _ z)] at h
      exact EReal.coe_ne_top _ h.symm
    · intro ht
      rw [ht, EReal.add_top_of_ne_bot (logPotential_ne_bot _ z)] at h
      exact EReal.coe_ne_top _ h.symm
  refine ⟨fun z hz => (hfin z hz).1, ?_⟩
  set g1 : ℂ → ℝ := fun z => (logPotential (μ.restrict L) z).toReal with hg1
  set g2 : ℂ → ℝ := fun z => (logPotential (μ.restrict Lᶜ) z).toReal with hg2
  have hsum : ∀ z ∈ L, g1 z = f z - g2 z := by
    intro z hz
    have h := heq z hz
    rw [hsplit, ← EReal.coe_toReal (hfin z hz).1 (logPotential_ne_bot _ z),
      ← EReal.coe_toReal (hfin z hz).2 (logPotential_ne_bot _ z), ← EReal.coe_add,
      EReal.coe_eq_coe_iff] at h
    simp only [hg1, hg2]
    linarith
  have hl1 := lowerSemicontinuousOn_toReal h1 (fun z hz => (hfin z hz).1)
  have hl2 := lowerSemicontinuousOn_toReal h2 (fun z hz => (hfin z hz).2)
  intro x hx
  refine tendsto_order.2 ⟨fun a ha => hl1 x hx a ha, fun b hb => ?_⟩
  set δ := b - g1 x with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hfx := (hf x hx).eventually (Metric.ball_mem_nhds (f x) (half_pos hδpos))
  have hg2x := hl2 x hx (g2 x - δ / 2) (by linarith)
  filter_upwards [hfx, hg2x, self_mem_nhdsWithin] with x' hx'1 hx'2 hx'L
  rw [mem_ball, Real.dist_eq] at hx'1
  rw [hsum x' hx'L]
  have := hsum x hx
  have := (abs_lt.1 hx'1).2
  linarith

/-- **The continuity principle** (Evans–Vasilesco): if `η` is carried by a compact set `S` and
`Φ_η` is finite and continuous on `S`, then `Φ_η` is finite and continuous on `ℂ`. -/
theorem continuous_logPotential_of_carrier {η : Measure ℂ} [IsFiniteMeasure η] {S : Set ℂ}
    (hS : IsCompact S) (hηS : η Sᶜ = 0) (hfin : ∀ z ∈ S, logPotential η z ≠ ⊤)
    (hcont : ContinuousOn (fun z => (logPotential η z).toReal) S) :
    (∀ z, logPotential η z ≠ ⊤) ∧ Continuous (fun z => (logPotential η z).toReal) := by
  have hηa := integrable_norm_of_compact hS hηS
  have hharm := harmonicOnNhd_logPotential (μ := η) hS hηS
  -- finiteness off `S`
  have hfin' : ∀ z, z ∉ S → logPotential η z ≠ ⊤ := by
    intro z hz
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hS.isClosed.isOpen_compl z hz
    have hdist : ∀ w ∈ S, δ ≤ ‖z - w‖ := by
      intro w hw
      by_contra hlt
      push Not at hlt
      exact hball (by rw [mem_ball, dist_eq_norm, norm_sub_rev]; exact hlt) hw
    exact (logPotential_lt_top_of_dist hηa hηS hδ hdist).ne
  -- the upper estimate at points of `S`
  have hupper : ∀ z0 ∈ S, ∀ ε > (0 : ℝ), ∀ᶠ z in 𝓝 z0,
      logPotential η z ≤ (((logPotential η z0).toReal + 3 * ε / 4 : ℝ) : EReal) := by
    intro z0 hz0S ε hε
    set Φ0 := (logPotential η z0).toReal with hΦ0
    have hatom : η {z0} = 0 := by
      by_contra hne
      exact hfin z0 hz0S (logPotential_eq_top_of_atom hηa hne)
    -- a closed ball of small mass
    have htend : Tendsto (fun n : ℕ => η (closedBall z0 (1 / ((n : ℝ) + 1)))) atTop
        (𝓝 (η {z0})) := by
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
      refine tendsto_measure_iInter_atTop
        (fun n => isClosed_closedBall.measurableSet.nullMeasurableSet)
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
    have hm1 : (η B).toReal * Real.log 2 < ε / 4 := by
      have h1 := (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).2 hn
      rw [ENNReal.toReal_ofReal (by positivity)] at h1
      calc (η B).toReal * Real.log 2 < ε / (4 * Real.log 2) * Real.log 2 :=
            mul_lt_mul_of_pos_right h1 hlog2
        _ = ε / 4 := by field_simp
    have hi1 : Integrable (fun w => ‖w‖) (η.restrict B) := hηa.restrict
    have hi2 : Integrable (fun w => ‖w‖) (η.restrict Bᶜ) := hηa.restrict
    -- the potential of the part off `B` is continuous at `z₀`
    set K2 := S ∩ (ball z0 r)ᶜ with hK2def
    have hK2 : IsCompact K2 := hS.inter_right isOpen_ball.isClosed_compl
    have hμ2K2 : η.restrict Bᶜ K2ᶜ = 0 := by
      rw [hK2def, compl_inter, compl_compl]
      refine measure_union_null ?_ ?_
      · exact le_antisymm ((Measure.restrict_le_self (s := Bᶜ) (μ := η) Sᶜ).trans hηS.le)
          zero_le
      · rw [Measure.restrict_apply isOpen_ball.measurableSet]
        refine measure_mono_null (fun x hx => ?_) measure_empty
        exact (hx.2 (by rw [hBdef]; exact ball_subset_closedBall hx.1)).elim
    obtain ⟨P2, hP2def⟩ : ∃ P2 : ℂ → ℝ,
        P2 = fun y => (logPotential (η.restrict Bᶜ) y).toReal := ⟨_, rfl⟩
    have hP2 : InnerProductSpace.HarmonicOnNhd P2 K2ᶜ := by
      rw [hP2def]; exact harmonicOnNhd_logPotential hK2 hμ2K2
    have hz0K2 : z0 ∈ K2ᶜ := by
      rw [hK2def, compl_inter, compl_compl]; exact Or.inr (mem_ball_self hr)
    obtain ⟨s, hs, hsP⟩ := Metric.continuousAt_iff.1 (hP2 z0 hz0K2).1.continuousAt (ε / 8)
      (by positivity)
    -- continuity of `Φ_η` along `S` at `z₀`
    obtain ⟨s1, hs1, hs1P⟩ := Metric.continuousWithinAt_iff.1 (hcont z0 hz0S) (ε / 4)
      (by positivity)
    -- distances to the part off `B`
    have hμ2C : η.restrict Bᶜ Bᶜᶜ = 0 := by
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
    have hP2eq : ∀ y, ‖y - z0‖ < r / 2 → ∀ N, N0 ≤ N → potT (η.restrict Bᶜ) N y = P2 y := by
      intro y hy N hN
      rw [hP2def]
      exact potT_eq_toReal_of_dist hi2 hμ2C (half_pos hr) (hdist2 y hy)
        ((Real.exp_le_exp.2 (neg_le_neg (by exact_mod_cast hN))).trans hN0)
    -- the compact set of nearest points
    set SB := S ∩ B with hSBdef
    have hSBc : IsCompact SB := hS.inter_right (by rw [hBdef]; exact isClosed_closedBall)
    have hz0SB : z0 ∈ SB := ⟨hz0S, by rw [hBdef]; exact mem_closedBall_self hr.le⟩
    have haeSB : ∀ᵐ w ∂(η.restrict B), w ∈ SB := by
      have h1 : ∀ᵐ w ∂(η.restrict B), w ∈ B := ae_restrict_mem hBm
      have h2 : ∀ᵐ w ∂(η.restrict B), w ∈ S :=
        ae_restrict_of_ae (measure_eq_zero_iff_ae_notMem.1 hηS |>.mono fun w hw => by
          simpa using hw)
      filter_upwards [h1, h2] with w hw1 hw2
      exact ⟨hw2, hw1⟩
    -- the neighbourhood
    set s' := min (min s s1) (r / 2) with hs'def
    have hs' : 0 < s' := lt_min (lt_min hs hs1) (by positivity)
    filter_upwards [ball_mem_nhds z0 (half_pos hs')] with z hz
    have hz' : ‖z - z0‖ < s' / 2 := by rwa [mem_ball, dist_eq_norm] at hz
    obtain ⟨zs, hzs, hmin⟩ := hSBc.exists_isMinOn ⟨z0, hz0SB⟩
      (continuous_const.dist continuous_id : Continuous fun w => dist z w).continuousOn
    have hmin' : ∀ w ∈ SB, ‖z - zs‖ ≤ ‖z - w‖ := fun w hw => by
      have := isMinOn_iff.1 hmin w hw
      simpa only [dist_eq_norm] using this
    have hzzs : ‖z - zs‖ < s' / 2 := lt_of_le_of_lt (hmin' z0 hz0SB) hz'
    have hzs0 : ‖zs - z0‖ < s' := by
      calc ‖zs - z0‖ ≤ ‖zs - z‖ + ‖z - z0‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ < s' / 2 + s' / 2 := add_lt_add (by rw [norm_sub_rev]; exact hzzs) hz'
        _ = s' := by ring
    have hs's : s' ≤ s := (min_le_left _ _).trans (min_le_left _ _)
    have hs's1 : s' ≤ s1 := (min_le_left _ _).trans (min_le_right _ _)
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
    -- `Φ_η(zs) ≤ Φ_η(z₀) + ε/4`
    have hzsE : ∀ N, potT η N zs ≤ Φ0 + ε / 4 := by
      intro N
      have h1 : (logPotential η zs).toReal < Φ0 + ε / 4 := by
        have := hs1P hzs.1 (show dist zs z0 < s1 by rw [dist_eq_norm]; linarith)
        rw [Real.dist_eq] at this
        linarith [(abs_lt.1 this).2]
      have h2 : ((potT η N zs : ℝ) : EReal) ≤ logPotential η zs :=
        le_iSup (fun N : ℕ => ((potT η N zs : ℝ) : EReal)) N
      rw [← EReal.coe_toReal (hfin zs hzs.1) (logPotential_ne_bot η zs),
        EReal.coe_le_coe_iff] at h2
      linarith
    -- the nearest-point estimate
    have hb1 : ∀ N, potT (η.restrict B) N z ≤
        (η B).toReal * Real.log 2 + potT (η.restrict B) N zs := by
      intro N
      have hint2 := (integrable_const (Real.log 2)).add (integrable_logKer hi1 N zs)
      have hkey : ∀ᵐ w ∂(η.restrict B), logKer N (z - w) ≤ Real.log 2 + logKer N (zs - w) :=
        haeSB.mono fun w hw => logKer_le_log_two_add N (by
          have h1 := hmin' w hw
          have h2 : ‖zs - w‖ ≤ ‖zs - z‖ + ‖z - w‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
          rw [norm_sub_rev zs z] at h2
          linarith)
      calc potT (η.restrict B) N z ≤ ∫ w, (Real.log 2 + logKer N (zs - w)) ∂(η.restrict B) :=
            integral_mono_ae (integrable_logKer hi1 N z) hint2 hkey
        _ = (η B).toReal * Real.log 2 + potT (η.restrict B) N zs := by
            rw [integral_add (integrable_const _) (integrable_logKer hi1 N zs), integral_const,
              smul_eq_mul, measureReal_def, Measure.restrict_apply_univ]
    have hbound : ∀ N, N0 ≤ N → potT η N z ≤ Φ0 + 3 * ε / 4 := by
      intro N hN
      have e1 := (integral_add_compl hBm (integrable_logKer hηa N z)).symm
      have e2 := (integral_add_compl hBm (integrable_logKer hηa N zs)).symm
      have h1 := hb1 N
      have h2 := hzsE N
      have h3 := hP2eq z hzr N hN
      have h4 := hP2eq zs hzsr N hN
      show ∫ w, logKer N (z - w) ∂η ≤ Φ0 + 3 * ε / 4
      have h2' : ∫ w, logKer N (zs - w) ∂η ≤ Φ0 + ε / 4 := h2
      rw [e1]
      rw [e2] at h2'
      change potT (η.restrict B) N z + potT (η.restrict Bᶜ) N z ≤ Φ0 + 3 * ε / 4
      change potT (η.restrict B) N zs + potT (η.restrict Bᶜ) N zs ≤ Φ0 + ε / 4 at h2'
      linarith
    refine iSup_le fun N => ?_
    rw [EReal.coe_le_coe_iff]
    exact (potTrunc_mono hηa z (le_max_left N N0)).trans (hbound _ (le_max_right _ _))
  -- finiteness everywhere
  have hfinall : ∀ z, logPotential η z ≠ ⊤ := by
    intro z
    by_cases hz : z ∈ S
    · exact hfin z hz
    · exact hfin' z hz
  refine ⟨hfinall, continuous_iff_continuousAt.2 fun z0 => ?_⟩
  by_cases hz0 : z0 ∈ S
  · refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
    · have hz0e : logPotential η z0 = (((logPotential η z0).toReal : ℝ) : EReal) :=
        (EReal.coe_toReal (hfinall z0) (logPotential_ne_bot η z0)).symm
      have h1 : (a : EReal) < logPotential η z0 := by rw [hz0e]; exact EReal.coe_lt_coe_iff.2 ha
      filter_upwards [(lowerSemicontinuous_logPotential hηa) z0 a h1] with z hz
      rw [← EReal.coe_toReal (hfinall z) (logPotential_ne_bot η z)] at hz
      exact EReal.coe_lt_coe_iff.1 hz
    · set ε := b - (logPotential η z0).toReal with hε
      have hεpos : 0 < ε := by rw [hε]; linarith
      filter_upwards [hupper z0 hz0 ε hεpos] with z hz
      rw [← EReal.coe_toReal (hfinall z) (logPotential_ne_bot η z), EReal.coe_le_coe_iff] at hz
      linarith
  · exact (hharm z0 hz0).1.continuousAt

/-- **Lemma A.2.10 for compact sets**: a compact set of positive capacity carries a probability
measure with continuous (in particular finite) potential. -/
theorem exists_continuous_potential_of_compact {K : Set ℂ} (hK : IsCompact K)
    (hcap : capCompact K ≠ 0) :
    ∃ η : Measure ℂ, IsProbabilityMeasure η ∧ η Kᶜ = 0 ∧
      ∃ f : ℂ → ℝ, Continuous f ∧ ∀ z, logPotential η z = f z := by
  obtain ⟨ρ, hρ⟩ := exists_isEquilibriumMeasure hK hcap
  haveI := hρ.1.1
  have hρa := adm_of_M1 hK hρ.1
  set E := (energy ρ).toReal with hEdef
  have hEeq : energy ρ = (E : EReal) := hρ.energy_eq_coe hcap
  have hlsc := lowerSemicontinuous_logPotential hρa.2
  -- `Φ_ρ = E(ρ)` holds `ρ`-a.e.
  set Bad := {z ∈ K | logPotential ρ z < energy ρ} with hBad
  have hBadm : MeasurableSet Bad :=
    hK.measurableSet.inter (hlsc.measurable measurableSet_Iio)
  have hρBad : ρ Bad = 0 :=
    measure_eq_zero_of_capacity_eq_zero hρa.2 (hρ.energy_ne_top hcap) hBadm
      (hρ.capacity_lt_eq_zero hK hcap)
  set G := {z ∈ K | logPotential ρ z = energy ρ} with hG
  have hGm : MeasurableSet G :=
    hK.measurableSet.inter (hlsc.measurable (measurableSet_singleton _))
  have hKGB : K ⊆ G ∪ Bad := by
    intro z hz
    rcases (hρ.logPotential_le_energy hK hcap z).lt_or_eq with h | h
    · exact Or.inr ⟨hz, h⟩
    · exact Or.inl ⟨hz, h⟩
  have hρK : ρ K = 1 := (prob_compl_eq_zero_iff hK.measurableSet).1 hρ.1.2
  have hρG : 0 < ρ G := by
    rw [pos_iff_ne_zero]
    intro h0
    have := measure_mono (μ := ρ) hKGB
    rw [hρK] at this
    have h2 := this.trans (measure_union_le G Bad)
    rw [h0, hρBad, add_zero] at h2
    exact absurd h2 (by norm_num)
  obtain ⟨L, hLG, hL, hρL⟩ := hGm.exists_lt_isCompact hρG
  -- `Φ_{ρ|L}` is finite and continuous on `L`
  obtain ⟨hfinL, hcL⟩ := restrict_potential_continuousOn hρa.2 hL.measurableSet (f := fun _ => E)
    continuousOn_const (fun z hz => by rw [(hLG hz).2, hEeq])
  have hηS : ρ.restrict L Lᶜ = 0 := by
    rw [Measure.restrict_apply hL.measurableSet.compl, compl_inter_self, measure_empty]
  obtain ⟨hfin, hcont⟩ := continuous_logPotential_of_carrier hL hηS hfinL hcL
  -- normalize
  have hρL0 : ρ L ≠ 0 := hρL.ne'
  have hρLtop : ρ L ≠ ⊤ := measure_ne_top _ _
  set c : ℝ≥0∞ := (ρ L)⁻¹ with hcdef
  have hctop : c ≠ ⊤ := ENNReal.inv_ne_top.2 hρL0
  have hLK : L ⊆ K := fun z hz => (hLG hz).1
  refine ⟨c • ρ.restrict L, ⟨?_⟩, ?_, fun z => c.toReal * (logPotential (ρ.restrict L) z).toReal,
    continuous_const.mul hcont, fun z => ?_⟩
  · simp only [Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul, hcdef]
    exact ENNReal.inv_mul_cancel hρL0 hρLtop
  · simp only [Measure.smul_apply, smul_eq_mul]
    rw [Measure.restrict_apply hK.measurableSet.compl]
    rw [show Kᶜ ∩ L = ∅ from by
      ext x; simp only [mem_inter_iff, mem_compl_iff, mem_empty_iff_false, iff_false, not_and]
      intro hx hxL; exact hx (hLK hxL)]
    simp
  · exact logPotential_smul_of_eq hρa.2.restrict hctop
      (EReal.coe_toReal (hfin z) (logPotential_ne_bot _ z)).symm

end DF
