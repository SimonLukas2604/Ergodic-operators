/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Appendix A.2: the lower envelope theorem (Theorem A.2.9) and Lemma A.2.10

## Main results

* `DF.capCompact_eq_zero_of_subset_exceptional` — **Theorem A.2.9, second half, inner form**: if
  finite measures `νₙ` carried by a compact set `K` converge weakly to `ν`, then every compact
  subset of the exceptional set `{Φ_ν < liminf Φ_{νₙ}}` has capacity zero.  (Test against a
  measure `η` with continuous potential on such a compact set (Lemma A.2.10 for compact sets) and
  apply Fatou's lemma to `Φ_{νₙ}`, using `∫ Φ_{νₙ} dη = ∫ Φ_η dνₙ → ∫ Φ_η dν = ∫ Φ_ν dη`.)
* `DF.CapacitabilityStatement` — Borel sets are capacitable (in the form needed here): a bounded
  Borel set of positive (outer) capacity contains a compact set of positive capacity.  This is
  Choquet's capacitability theorem for the logarithmic capacity, which the book uses implicitly.
* `DF.continuousPotentialStatement_of_capacitability`,
  `DF.lowerEnvelopeStatement_of_capacitability` — `DF.ContinuousPotentialStatement`
  (Lemma A.2.10) and `DF.LowerEnvelopeStatement` (Theorem A.2.9) follow from it.
-/
import DamanikFillman.AppA.ContinuousPotential

noncomputable section

open Real Complex Metric Set Filter Topology MeasureTheory
open scoped ENNReal BoundedContinuousFunction

namespace DF

/-- Continuous functions are integrable against finite measures carried by a compact set. -/
lemma integrable_of_continuous_carrier {ρ : Measure ℂ} [IsFiniteMeasure ρ] {Q : Set ℂ}
    (hQ : IsCompact Q) (hρQ : ρ Qᶜ = 0) {g : ℂ → ℝ} (hg : Continuous g) : Integrable g ρ := by
  obtain ⟨C, hC⟩ := hQ.exists_bound_of_continuousOn hg.continuousOn
  refine Integrable.of_bound hg.aestronglyMeasurable C ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hρQ] with w hw
  exact hC w (by simpa using hw)

/-- Weak convergence of measures carried by a compact set, tested against continuous functions. -/
lemma tendsto_integral_of_continuous {K : Set ℂ} (hK : IsCompact K) {νs : ℕ → Measure ℂ}
    {ν : Measure ℂ} (hνs : ∀ n, νs n Kᶜ = 0) (hν : ν Kᶜ = 0)
    (hconv : ∀ f : ℂ →ᵇ ℝ, Tendsto (fun n => ∫ w, f w ∂(νs n)) atTop (𝓝 (∫ w, f w ∂ν)))
    {g : ℂ → ℝ} (hg : Continuous g) :
    Tendsto (fun n => ∫ w, g w ∂(νs n)) atTop (𝓝 (∫ w, g w ∂ν)) := by
  obtain ⟨Cg, hCg⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  set g' : ℂ → ℝ := fun w => max (min (g w) |Cg|) (-|Cg|) with hg'
  have hg'c : Continuous g' := (hg.min continuous_const).max continuous_const
  have hg'b : ∀ w, ‖g' w‖ ≤ |Cg| := fun w => by
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨le_max_right _ _, max_le (min_le_right _ _) (by linarith [abs_nonneg Cg])⟩
  set G : ℂ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup g' hg'c |Cg| hg'b
  have hGK : ∀ w ∈ K, G w = g w := fun w hw => by
    show max (min (g w) |Cg|) (-|Cg|) = g w
    have := hCg w hw
    rw [Real.norm_eq_abs] at this
    have this' : |g w| ≤ |Cg| := this.trans (le_abs_self _)
    rw [min_eq_left ((le_abs_self _).trans this'), max_eq_left (neg_le_of_abs_le this')]
  have hint : ∀ ρ : Measure ℂ, ρ Kᶜ = 0 → ∫ w, G w ∂ρ = ∫ w, g w ∂ρ := fun ρ hρ =>
    integral_congr_ae (by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hρ] with w hw
      exact hGK w (by simpa using hw))
  have := hconv G
  rw [hint ν hν] at this
  simpa only [hint _ (hνs _)] using this

/-- **Theorem A.2.9, second half, inner form**: every compact subset of the exceptional set of
the lower envelope theorem has capacity zero. -/
theorem capCompact_eq_zero_of_subset_exceptional {K : Set ℂ} (hK : IsCompact K)
    {νs : ℕ → Measure ℂ} {ν : Measure ℂ} [∀ n, IsFiniteMeasure (νs n)] [IsFiniteMeasure ν]
    (hνs : ∀ n, νs n Kᶜ = 0) (hν : ν Kᶜ = 0)
    (hconv : ∀ f : ℂ →ᵇ ℝ, Tendsto (fun n => ∫ w, f w ∂(νs n)) atTop (𝓝 (∫ w, f w ∂ν)))
    {L : Set ℂ} (hL : IsCompact L)
    (hLsub : ∀ z ∈ L, logPotential ν z < liminf (fun n => logPotential (νs n) z) atTop) :
    capCompact L = 0 := by
  by_contra hcap
  obtain ⟨η, hηp, hηL, f, hf, hΦ⟩ := exists_continuous_potential_of_compact hL hcap
  have hηa : Integrable (fun w => ‖w‖) η := integrable_norm_of_compact hL hηL
  -- bounds on the masses
  have hmass : Tendsto (fun n => (νs n).real univ) atTop (𝓝 (ν.real univ)) := by
    have := tendsto_integral_of_continuous hK hνs hν hconv (g := fun _ => (1 : ℝ))
      continuous_const
    simpa using this
  obtain ⟨M0, hM0⟩ := hmass.bddAbove_range
  set M := max M0 0 with hMdef
  have hM0' : 0 ≤ M := le_max_right _ _
  have hMn : ∀ n, (νs n).real univ ≤ M := fun n => (hM0 ⟨n, rfl⟩).trans (le_max_left _ _)
  have hMν : ν.real univ ≤ M := le_of_tendsto' hmass hMn
  -- a common radius
  obtain ⟨R0, hR0⟩ := (hK.union hL).isBounded.subset_closedBall 0
  set R := max R0 0 with hRdef
  have hR0' : 0 ≤ R := le_max_right _ _
  have hnorm : ∀ w ∈ K ∪ L, ‖w‖ ≤ R := fun w hw => by
    have := hR0 hw
    rw [mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  set c : ℝ := 2 * R * M with hcdef
  -- lower bound for the truncated potentials on `L`
  have hlow : ∀ (ρ : Measure ℂ) [IsFiniteMeasure ρ], ρ Kᶜ = 0 → ρ.real univ ≤ M →
      ∀ N, ∀ z ∈ L, -c ≤ potT ρ N z := by
    intro ρ _ hρ hρM N z hz
    have hae : ∀ᵐ w ∂ρ, -(2 * R) ≤ logKer N (z - w) := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hρ] with w hw
      have hw' : w ∈ K := by simpa using hw
      have h1 := neg_norm_le_logKer N (z - w)
      have h2 := norm_sub_le z w
      linarith [hnorm z (Or.inr hz), hnorm w (Or.inl hw')]
    have := integral_mono_ae (integrable_const (-(2 * R)))
      (integrable_logKer (integrable_norm_of_compact hK hρ) N z) hae
    rw [integral_const, smul_eq_mul] at this
    have hρ0 : 0 ≤ ρ.real univ := measureReal_nonneg
    show -(2 * R * M) ≤ ∫ w, logKer N (z - w) ∂ρ
    nlinarith
  -- the integrals of the potentials against `η`
  have hIA : ∀ (ρ : Measure ℂ) [IsFiniteMeasure ρ], ρ Kᶜ = 0 → ρ.real univ ≤ M →
      ∫⁻ z, (⨆ N : ℕ, ENNReal.ofReal (potT ρ N z + c)) ∂η =
        ENNReal.ofReal (∫ w, f w ∂ρ + c) := by
    intro ρ _ hρ hρM
    have hρa := integrable_norm_of_compact hK hρ
    rw [lintegral_iSup (f := fun N z => ENNReal.ofReal (potT ρ N z + c))
      (fun N => ENNReal.measurable_ofReal.comp
        ((continuous_potTrunc hρa N).add continuous_const).measurable)
      (fun m n hmn z => ENNReal.ofReal_le_ofReal (by
        have := potTrunc_mono hρa z hmn
        simp only at this
        linarith))]
    have heach : ∀ N : ℕ, ∫⁻ z, ENNReal.ofReal (potT ρ N z + c) ∂η =
        ENNReal.ofReal ((∫ z, potT η N z ∂ρ) + c) := by
      intro N
      have hi : Integrable (fun z => potT ρ N z + c) η :=
        integrable_of_continuous_carrier hL hηL ((continuous_potTrunc hρa N).add continuous_const)
      rw [← ofReal_integral_eq_lintegral_ofReal hi
        (by
          filter_upwards [measure_eq_zero_iff_ae_notMem.1 hηL] with z hz
          have := hlow ρ hρ hρM N z (by simpa using hz)
          simp only [Pi.zero_apply]
          linarith)]
      congr 1
      rw [integral_add (integrable_of_continuous_carrier hL hηL (continuous_potTrunc hρa N))
        (integrable_const c), integral_const, probReal_univ, one_smul]
      congr 1
      exact Itr_comm ⟨inferInstance, hρa⟩ ⟨inferInstance, hηa⟩ N
    simp_rw [heach]
    have htend : Tendsto (fun N : ℕ => ∫ z, potT η N z ∂ρ) atTop (𝓝 (∫ w, f w ∂ρ)) := by
      refine integral_tendsto_of_tendsto_of_monotone
        (fun N => integrable_of_continuous_carrier hK hρ (continuous_potTrunc hηa N))
        (integrable_of_continuous_carrier hK hρ hf)
        (Eventually.of_forall fun z => potTrunc_mono hηa z) (Eventually.of_forall fun z => ?_)
      have := tendsto_potT hηa z
      rw [hΦ z] at this
      exact EReal.tendsto_coe.1 this
    have hmono : Monotone fun N : ℕ => ENNReal.ofReal ((∫ z, potT η N z ∂ρ) + c) := by
      intro m n hmn
      refine ENNReal.ofReal_le_ofReal ?_
      have := integral_mono (integrable_of_continuous_carrier hK hρ (continuous_potTrunc hηa m))
        (integrable_of_continuous_carrier hK hρ (continuous_potTrunc hηa n))
        (fun z => potTrunc_mono hηa z hmn)
      linarith
    exact tendsto_nhds_unique (tendsto_atTop_iSup hmono)
      ((ENNReal.continuous_ofReal.tendsto _).comp (htend.add_const c))
  set A : ℕ → ℂ → ℝ≥0∞ := fun n z => ⨆ N : ℕ, ENNReal.ofReal (potT (νs n) N z + c) with hAdef
  set B : ℂ → ℝ≥0∞ := fun z => ⨆ N : ℕ, ENNReal.ofReal (potT ν N z + c) with hBdef
  have hAm : ∀ n, Measurable (A n) := fun n =>
    Measurable.iSup fun N => ENNReal.measurable_ofReal.comp
      ((continuous_potTrunc (integrable_norm_of_compact hK (hνs n)) N).add
        continuous_const).measurable
  have hA : ∀ n, ∫⁻ z, A n z ∂η = ENNReal.ofReal (∫ w, f w ∂(νs n) + c) := fun n =>
    hIA (νs n) (hνs n) (hMn n)
  have hB : ∫⁻ z, B z ∂η = ENNReal.ofReal (∫ w, f w ∂ν + c) := hIA ν hν hMν
  have hlim : Tendsto (fun n => ∫⁻ z, A n z ∂η) atTop (𝓝 (∫⁻ z, B z ∂η)) := by
    simp_rw [hA, hB]
    exact (ENNReal.continuous_ofReal.tendsto _).comp
      ((tendsto_integral_of_continuous hK hνs hν hconv hf).add_const c)
  have hfatou := lintegral_liminf_le (μ := η) (u := atTop) hAm
  rw [hlim.liminf_eq] at hfatou
  -- the strict pointwise inequality on `L`
  have hstrict : ∀ᵐ z ∂η, B z < liminf (fun n => A n z) atTop := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hηL] with z hz
    have hzL : z ∈ L := by simpa using hz
    have h1 := hLsub z hzL
    have hfin : logPotential ν z ≠ ⊤ := ne_top_of_lt h1
    set a := (logPotential ν z).toReal with hadef
    have ha : logPotential ν z = a := (EReal.coe_toReal hfin (logPotential_ne_bot ν z)).symm
    rw [ha] at h1
    obtain ⟨q, hq1, hq2⟩ := EReal.lt_iff_exists_real_btwn.1 h1
    have hq1' : a < q := EReal.coe_lt_coe_iff.1 hq1
    have hpot : ∀ N, potT ν N z ≤ a := fun N => by
      have : ((potT ν N z : ℝ) : EReal) ≤ logPotential ν z :=
        le_iSup (fun N : ℕ => ((potT ν N z : ℝ) : EReal)) N
      rw [ha] at this
      exact EReal.coe_le_coe_iff.1 this
    have hac : -c ≤ a := (hlow ν hν hMν 0 z hzL).trans (hpot 0)
    have hev := eventually_lt_of_lt_liminf hq2
    have hAge : ENNReal.ofReal (q + c) ≤ liminf (fun n => A n z) atTop := by
      refine Filter.le_liminf_of_le (by isBoundedDefault) ?_
      filter_upwards [hev] with n hn
      obtain ⟨N, hN⟩ := lt_iSup_iff.1 hn
      have hN' : q < potT (νs n) N z := EReal.coe_lt_coe_iff.1 hN
      exact (ENNReal.ofReal_le_ofReal (by linarith)).trans
        (le_iSup (fun N : ℕ => ENNReal.ofReal (potT (νs n) N z + c)) N)
    have hBle : B z ≤ ENNReal.ofReal (a + c) :=
      iSup_le fun N => ENNReal.ofReal_le_ofReal (by linarith [hpot N])
    have hlt : ENNReal.ofReal (a + c) < ENNReal.ofReal (q + c) :=
      (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 (by linarith)
    exact hBle.trans_lt (hlt.trans_le hAge)
  have hBfin : ∫⁻ z, B z ∂η ≠ ⊤ := by rw [hB]; exact ENNReal.ofReal_ne_top
  have := lintegral_strict_mono (μ := η) (IsProbabilityMeasure.ne_zero η)
    (Measurable.liminf hAm).aemeasurable hBfin hstrict
  exact absurd (this.trans_le hfatou) (lt_irrefl _)

/-- **Capacitability of Borel sets** (in the form used in Appendix A.2): a bounded Borel set of
positive capacity contains a compact set of positive capacity.  This is Choquet's
capacitability theorem for the logarithmic capacity (the definitions (A.2.2)–(A.2.3) of the
capacity of a general set agree with the inner capacity on Borel sets).  Recorded as a
statement. -/
def CapacitabilityStatement : Prop :=
  ∀ X : Set ℂ, Bornology.IsBounded X → MeasurableSet X → capacity X ≠ 0 →
    ∃ K ⊆ X, IsCompact K ∧ capCompact K ≠ 0

/-- **Lemma A.2.10**, from capacitability. -/
theorem continuousPotentialStatement_of_capacitability (hcap : CapacitabilityStatement) :
    ContinuousPotentialStatement := by
  intro X hb hm hX
  obtain ⟨K, hKX, hK, hcapK⟩ := hcap X hb hm hX
  obtain ⟨η, hη, hηK, f, hf, hΦ⟩ := exists_continuous_potential_of_compact hK hcapK
  exact ⟨η, hη, measure_mono_null (compl_subset_compl.2 hKX) hηK, f, hf, hΦ⟩

/-- **Theorem A.2.9, second half**, from capacitability. -/
theorem lowerEnvelopeStatement_of_capacitability (hcap : CapacitabilityStatement) :
    LowerEnvelopeStatement := by
  intro K νs ν hK hfin hνfin hνs hν _ hconv
  haveI : ∀ n, IsFiniteMeasure (νs n) := hfin
  haveI := hνfin
  have hle := fun z => logPotential_le_liminf hK hνs hν hconv z
  set Bad := {z | liminf (fun n => logPotential (νs n) z) atTop ≠ logPotential ν z} with hBad
  have hBad' : Bad = {z | logPotential ν z < liminf (fun n => logPotential (νs n) z) atTop} := by
    ext z
    simp only [hBad, mem_setOf_eq]
    exact ⟨fun h => lt_of_le_of_ne (hle z) (Ne.symm h), fun h => ne_of_gt h⟩
  -- the exceptional set lies in `K`
  have hBadK : Bad ⊆ K := by
    intro z hz
    by_contra hzK
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hK.isClosed.isOpen_compl z hzK
    have hdist : ∀ w ∈ K, δ ≤ ‖z - w‖ := by
      intro w hw
      by_contra hlt
      push Not at hlt
      exact hball (by rw [mem_ball, dist_eq_norm, norm_sub_rev]; exact hlt) hw
    obtain ⟨N, hN⟩ := exists_exp_neg_le hδ
    have hpot : ∀ (ρ : Measure ℂ) [IsFiniteMeasure ρ], ρ Kᶜ = 0 →
        logPotential ρ z = ((potT ρ N z : ℝ) : EReal) := by
      intro ρ _ hρ
      have hρa := integrable_norm_of_compact hK hρ
      rw [potT_eq_toReal_of_dist hρa hρ hδ hdist hN]
      exact (EReal.coe_toReal (logPotential_lt_top_of_dist hρa hρ hδ hdist).ne
        (logPotential_ne_bot ρ z)).symm
    have htend : Tendsto (fun n => potT (νs n) N z) atTop (𝓝 (potT ν N z)) :=
      tendsto_integral_of_continuous hK hνs hν hconv
        ((continuous_logKer N).comp (continuous_const.sub continuous_id))
    have htend' : Tendsto (fun n => logPotential (νs n) z) atTop (𝓝 (logPotential ν z)) := by
      rw [hpot ν hν]
      refine ((continuous_coe_real_ereal.tendsto _).comp htend).congr fun n => ?_
      exact (hpot (νs n) (hνs n)).symm
    exact hz htend'.liminf_eq
  have hb : Bornology.IsBounded Bad := hK.isBounded.subset hBadK
  have hm : MeasurableSet Bad := by
    rw [hBad']
    exact measurableSet_lt
      (lowerSemicontinuous_logPotential (integrable_norm_of_compact hK hν)).measurable
      (Measurable.liminf fun n =>
        (lowerSemicontinuous_logPotential (integrable_norm_of_compact hK (hνs n))).measurable)
  by_contra hne
  obtain ⟨L, hLB, hL, hLcap⟩ := hcap Bad hb hm hne
  refine hLcap (capCompact_eq_zero_of_subset_exceptional hK hνs hν hconv hL fun z hz => ?_)
  have := hLB hz
  rw [hBad'] at this
  exact this

end DF
