/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Appendix A.2: logarithmic potential theory in the plane   (book pp. 410–418)

## Conventions

The logarithmic kernel `log |z - w|⁻¹` takes the value `+∞` on the diagonal, and Mathlib's
`Real.log` has `log 0 = 0`.  We therefore work, as the book does in (A.2.4)–(A.2.5), with the
truncated kernels

  `logKer N x = log (min (e^N, |x|⁻¹)) = min (N, -log |x|)`   (`logKer N 0 = N`)

and *define* the potential and the energies as the suprema over `N` of the truncated
integrals (values in `EReal`).  By monotone convergence these suprema are the usual
(extended) integrals; `logPotential_eq_integral` makes this precise for the potential.

The measures considered are finite Borel measures on `ℂ` with finite first moment
(`Integrable (‖·‖) μ`); this includes all compactly supported finite measures
(`integrable_norm_of_compact`), which is the book's setting.

## Main definitions

* `DF.logKer N` — truncated kernel (A.2.4);
* `DF.logPotential μ` — the logarithmic potential `Φ_μ` (Definition A.2.1);
* `DF.mutualEnergy μ ν` — `∫ Φ_μ dν`, and `DF.energy μ = mutualEnergy μ μ` (Definition A.2.1);
* `DF.M1 K` — Borel probability measures supported in `K`;
* `DF.capCompact K` — capacity of a compact set (A.2.1), with the convention `e^{-∞} = 0`;
* `DF.capacity B` — capacity of a general set via (A.2.2)–(A.2.3).

## Main results

* Proposition A.2.2:
  (a) `logPotential_ne_bot`, `logPotential_eq_integral_of_dist`, `logPotential_lt_top_of_dist`;
  (b) `lowerSemicontinuous_logPotential` and `harmonicOnNhd_logPotential` (harmonic off the
      support);
  (c) `mutualEnergy_comm`;
  (d) `capCompact_mono`, `capacity_mono` (and `capCompact_le_capacity`);
  (f) `measure_eq_zero_of_capacity_eq_zero`.
* `logPotential_eq_integral` — `Φ_μ(z) = ∫ log|z-w|⁻¹ dμ(w)` whenever the latter makes sense.
* `subharmonic_neg_logPotential` — `-Φ_μ` is subharmonic on `ℂ` (used for the Thouless
  formula, §4.6).
* Example A.2.3: `energy_eq_top_of_atom`, `capCompact_eq_zero_of_countable`.
* `capCompact_eq_zero_iff`, `expNeg_energy_le_capCompact` — `Cap(K) = 0` iff all `μ ∈ M1(K)`
  have infinite energy; `e^{-E(μ)} ≤ Cap(K)` (used in Lemma 4.6.6).
* Theorem A.2.9, first half: `logPotential_le_liminf`.
* Definition A.2.7 / Theorem A.2.6: `IsEquilibriumMeasure`, `IsEquilibriumMeasure.capCompact_eq`
  ((A.2.8)), `IsEquilibriumMeasure.unique` (uniqueness, from Prop. A.2.5).  Existence (via
  Lemma A.2.4) is proved in `DamanikFillman/AppA/Equilibrium.lean`.

## Statements (recorded as `Prop`s, not proved here)

* `EnergyStrictConvexityStatement` — Prop. A.2.5 (the book only sketches the proof);
* `EquilibriumExistenceStatement` — Thm. A.2.6, existence (proved in `Equilibrium.lean`:
  `equilibriumExistenceStatement_holds`);
* `CapacityRegularityStatement` — Prop. A.2.2(e) and consistency of (A.2.1) with (A.2.2)–(A.2.3);
* `FrostmanStatement` — Thm. A.2.8;
* `LowerEnvelopeStatement` — Thm. A.2.9, second half (equality q.e.);
* `ContinuousPotentialStatement` — Lemma A.2.10 (the book cites the literature);
* `CapacityZeroDimStatement` — Thm. A.2.11 (cited).
-/
import DamanikFillman.AppA.Subharmonic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.ContinuousMap.Bounded.Normed

noncomputable section

open Real Complex Metric Set Filter Topology MeasureTheory
open scoped ENNReal BoundedContinuousFunction

namespace DF

/-! ### The truncated logarithmic kernel -/

/-- The truncated logarithmic kernel `logKer N x = -log (max |x| e^{-N}) = min (N, log |x|⁻¹)`
(book (A.2.4)). -/
def logKer (N : ℕ) (x : ℂ) : ℝ := -Real.log (max ‖x‖ (Real.exp (-(N : ℝ))))

lemma max_norm_exp_pos (N : ℕ) (x : ℂ) : 0 < max ‖x‖ (Real.exp (-(N : ℝ))) :=
  lt_max_of_lt_right (Real.exp_pos _)

lemma continuous_logKer (N : ℕ) : Continuous (logKer N) := by
  unfold logKer
  exact ((continuous_norm.max continuous_const).log fun x => (max_norm_exp_pos N x).ne').neg

lemma logKer_le (N : ℕ) (x : ℂ) : logKer N x ≤ N := by
  unfold logKer
  have := Real.log_le_log (Real.exp_pos _) (le_max_right ‖x‖ (Real.exp (-(N : ℝ))))
  rw [Real.log_exp] at this
  linarith

lemma logKer_zero (N : ℕ) : logKer N 0 = N := by
  simp [logKer, max_eq_right (Real.exp_pos _).le]

lemma logKer_of_le {N : ℕ} {x : ℂ} (h : Real.exp (-(N : ℝ)) ≤ ‖x‖) :
    logKer N x = -Real.log ‖x‖ := by
  simp [logKer, max_eq_left h]

lemma logKer_mono (x : ℂ) : Monotone (fun N : ℕ => logKer N x) := by
  intro m n hmn
  simp only [logKer, neg_le_neg_iff]
  apply Real.log_le_log (max_norm_exp_pos n x)
  exact max_le_max le_rfl (Real.exp_le_exp.2 (neg_le_neg (by exact_mod_cast hmn)))

lemma logKer_neg (N : ℕ) (x : ℂ) : logKer N (-x) = logKer N x := by
  simp [logKer]

lemma logKer_sub_comm (N : ℕ) (z w : ℂ) : logKer N (z - w) = logKer N (w - z) := by
  rw [← logKer_neg, neg_sub]

lemma neg_norm_le_logKer (N : ℕ) (x : ℂ) : -‖x‖ ≤ logKer N x := by
  unfold logKer
  have h1 : Real.log (max ‖x‖ (Real.exp (-(N : ℝ)))) ≤ max ‖x‖ (Real.exp (-(N : ℝ))) - 1 :=
    Real.log_le_sub_one_of_pos (max_norm_exp_pos N x)
  have h2 : Real.exp (-(N : ℝ)) ≤ 1 := Real.exp_le_one_iff.2 (by simp)
  have h3 : max ‖x‖ (Real.exp (-(N : ℝ))) ≤ ‖x‖ + 1 :=
    max_le (by linarith) (by linarith [norm_nonneg x])
  linarith

lemma abs_logKer_le (N : ℕ) (x : ℂ) : |logKer N x| ≤ N + ‖x‖ := by
  rw [abs_le]
  constructor
  · have := neg_norm_le_logKer N x; have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith
  · have := logKer_le N x; linarith [norm_nonneg x]

/-- `-logKer N x` is the truncation of `log |x|` at level `-N`. -/
lemma neg_logKer_eq_truncBelow (N : ℕ) (x : ℂ) :
    -logKer N x = truncBelow N (logNorm id x) := by
  by_cases hx : x = 0
  · subst hx
    simp [logNorm, truncBelow_bot, logKer_zero]
  · rw [logNorm_of_ne_zero (by simpa using hx), truncBelow_coe]
    simp only [logKer, neg_neg, id]
    rcases le_total ‖x‖ (Real.exp (-(N : ℝ))) with h | h
    · rw [max_eq_right h, Real.log_exp, max_eq_right]
      rw [← Real.log_exp (-(N : ℝ))]
      exact Real.log_le_log (norm_pos_iff.2 hx) h
    · rw [max_eq_left h, max_eq_left]
      rw [← Real.log_exp (-(N : ℝ))]
      exact Real.log_le_log (Real.exp_pos _) h

/-! ### Measures with finite first moment -/

/-- Compactly supported finite measures have finite first moment. -/
lemma integrable_norm_of_compact {μ : Measure ℂ} [IsFiniteMeasure μ] {K : Set ℂ}
    (hK : IsCompact K) (hμK : μ Kᶜ = 0) : Integrable (fun w => ‖w‖) μ := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine (integrable_const R).mono' continuous_norm.aestronglyMeasurable ?_
  have : ∀ᵐ w ∂μ, w ∈ K := measure_eq_zero_iff_ae_notMem.1 hμK |>.mono fun w hw => by
    simpa using hw
  filter_upwards [this] with w hw
  have := hR hw
  simpa [mem_closedBall, dist_zero_right] using this

variable {μ ν : Measure ℂ}

lemma integrable_logKer [IsFiniteMeasure μ] (hμ : Integrable (fun w => ‖w‖) μ) (N : ℕ) (z : ℂ) :
    Integrable (fun w => logKer N (z - w)) μ := by
  refine ((integrable_const ((N : ℝ) + ‖z‖)).add hμ).mono'
    ((continuous_logKer N).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs]
  refine (abs_logKer_le N _).trans ?_
  have := norm_sub_le z w
  simp only [Pi.add_apply]; linarith

/-- The truncated potential `z ↦ ∫ logKer N (z - w) dμ(w)` is continuous. -/
lemma continuous_potTrunc [IsFiniteMeasure μ] (hμ : Integrable (fun w => ‖w‖) μ) (N : ℕ) :
    Continuous (fun z => ∫ w, logKer N (z - w) ∂μ) := by
  rw [continuous_iff_continuousAt]
  intro z₀
  refine continuousAt_of_dominated (bound := fun w => (N : ℝ) + (‖z₀‖ + 1) + ‖w‖) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun z =>
      ((continuous_logKer N).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · filter_upwards [ball_mem_nhds z₀ one_pos] with z hz
    refine Eventually.of_forall fun w => ?_
    rw [Real.norm_eq_abs]
    refine (abs_logKer_le N _).trans ?_
    have h1 := norm_sub_le z w
    have h2 : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have := norm_le_norm_add_norm_sub' z z₀
      rw [mem_ball, dist_eq_norm] at hz; linarith
    linarith
  · exact (integrable_const _).add hμ
  · exact Eventually.of_forall fun w =>
      ((continuous_logKer N).comp (continuous_id.sub continuous_const)).continuousAt

/-! ### Potentials and energies -/

/-- The logarithmic potential `Φ_μ(z) = ∫ log |z - w|⁻¹ dμ(w)` (Definition A.2.1), defined as the
supremum of the truncated potentials. -/
def logPotential (μ : Measure ℂ) (z : ℂ) : EReal :=
  ⨆ N : ℕ, ((∫ w, logKer N (z - w) ∂μ : ℝ) : EReal)

/-- The mutual energy `∫ Φ_μ dν = ∫∫ log |z - w|⁻¹ dμ(w) dν(z)`, defined as the supremum of the
truncated double integrals. -/
def mutualEnergy (μ ν : Measure ℂ) : EReal :=
  ⨆ N : ℕ, ((∫ z, ∫ w, logKer N (z - w) ∂μ ∂ν : ℝ) : EReal)

/-- The logarithmic energy `E(μ) = ∫ Φ_μ dμ` (Definition A.2.1). -/
def energy (μ : Measure ℂ) : EReal := mutualEnergy μ μ

lemma potTrunc_mono [IsFiniteMeasure μ] (hμ : Integrable (fun w => ‖w‖) μ) (z : ℂ) :
    Monotone (fun N : ℕ => ∫ w, logKer N (z - w) ∂μ) := fun m n hmn =>
  integral_mono (integrable_logKer hμ m z) (integrable_logKer hμ n z)
    (fun _ => logKer_mono _ hmn)

/-- Prop. A.2.2(b), first half: `Φ_μ` is lower semicontinuous. -/
theorem lowerSemicontinuous_logPotential [IsFiniteMeasure μ]
    (hμ : Integrable (fun w => ‖w‖) μ) : LowerSemicontinuous (logPotential μ) :=
  lowerSemicontinuous_iSup fun N =>
    (continuous_coe_real_ereal.comp (continuous_potTrunc hμ N)).lowerSemicontinuous

/-- Prop. A.2.2(a), second half: `Φ_μ(z) > -∞` for every `z`. -/
theorem logPotential_ne_bot (μ : Measure ℂ) (z : ℂ) : logPotential μ z ≠ ⊥ :=
  ne_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe _)
    (le_iSup (fun N : ℕ => ((∫ w, logKer N (z - w) ∂μ : ℝ) : EReal)) 0))

/-- If `z` has distance at least `δ > 0` from a set carrying `μ`, then `Φ_μ(z)` is given by the
(convergent) integral of `log |z - w|⁻¹`. -/
theorem logPotential_eq_integral_of_dist [IsFiniteMeasure μ] (hμ : Integrable (fun w => ‖w‖) μ)
    {K : Set ℂ} (hμK : μ Kᶜ = 0) {z : ℂ} {δ : ℝ} (hδ : 0 < δ) (hzK : ∀ w ∈ K, δ ≤ ‖z - w‖) :
    logPotential μ z = ((∫ w, -Real.log ‖z - w‖ ∂μ : ℝ) : EReal) := by
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, Real.exp (-(N₀ : ℝ)) ≤ δ := by
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (-Real.log δ)
    exact ⟨N₀, by rw [← Real.exp_log hδ]; exact Real.exp_le_exp.2 (by linarith)⟩
  have hae : ∀ᵐ w ∂μ, w ∈ K := measure_eq_zero_iff_ae_notMem.1 hμK |>.mono fun w hw => by
    simpa using hw
  have heq : ∀ N, N₀ ≤ N → ∫ w, logKer N (z - w) ∂μ = ∫ w, -Real.log ‖z - w‖ ∂μ := by
    intro N hN
    refine integral_congr_ae (hae.mono fun w hw => logKer_of_le ?_)
    refine le_trans ?_ ((hN₀.trans (hzK w hw)))
    exact Real.exp_le_exp.2 (neg_le_neg (by exact_mod_cast hN))
  apply le_antisymm
  · refine iSup_le fun N => ?_
    rw [EReal.coe_le_coe_iff, ← heq (max N N₀) (le_max_right _ _)]
    exact potTrunc_mono hμ z (le_max_left _ _)
  · rw [← heq N₀ le_rfl]
    exact le_iSup (fun N : ℕ => ((∫ w, logKer N (z - w) ∂μ : ℝ) : EReal)) N₀

/-- Prop. A.2.2(a), first half: off the support, `Φ_μ` is finite. -/
theorem logPotential_lt_top_of_dist [IsFiniteMeasure μ] (hμ : Integrable (fun w => ‖w‖) μ)
    {K : Set ℂ} (hμK : μ Kᶜ = 0) {z : ℂ} {δ : ℝ} (hδ : 0 < δ) (hzK : ∀ w ∈ K, δ ≤ ‖z - w‖) :
    logPotential μ z < ⊤ := by
  rw [logPotential_eq_integral_of_dist hμ hμK hδ hzK]; exact EReal.coe_lt_top _

/-- Monotone convergence: whenever `w ↦ log |z - w|` is `μ`-integrable and `z` is not an atom of
`μ`, the potential `Φ_μ(z)` equals `∫ log |z - w|⁻¹ dμ(w)`. -/
theorem logPotential_eq_integral [IsFiniteMeasure μ] (hμ : Integrable (fun w => ‖w‖) μ) {z : ℂ}
    (hz : μ {z} = 0) (hint : Integrable (fun w => Real.log ‖z - w‖) μ) :
    logPotential μ z = ((∫ w, -Real.log ‖z - w‖ ∂μ : ℝ) : EReal) := by
  have hlim : Tendsto (fun N : ℕ => ∫ w, logKer N (z - w) ∂μ) atTop
      (𝓝 (∫ w, -Real.log ‖z - w‖ ∂μ)) := by
    refine integral_tendsto_of_tendsto_of_monotone (fun N => integrable_logKer hμ N z) hint.neg
      (Eventually.of_forall fun _w N M hNM => logKer_mono _ hNM) ?_
    have hae : ∀ᵐ w ∂μ, w ≠ z := by
      rw [ae_iff]; simpa using hz
    filter_upwards [hae] with w hw
    have hpos : 0 < ‖z - w‖ := norm_pos_iff.2 (sub_ne_zero.2 hw.symm)
    apply tendsto_const_nhds.congr'
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (-Real.log ‖z - w‖)
    filter_upwards [eventually_ge_atTop N₀] with N hN
    symm; apply logKer_of_le
    rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.2 (by have : (N₀ : ℝ) ≤ N := by exact_mod_cast hN
                                linarith)
  have h1 : Tendsto (fun N : ℕ => ((∫ w, logKer N (z - w) ∂μ : ℝ) : EReal)) atTop
      (𝓝 ((∫ w, -Real.log ‖z - w‖ ∂μ : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.tendsto _).comp hlim
  have h2 : Tendsto (fun N : ℕ => ((∫ w, logKer N (z - w) ∂μ : ℝ) : EReal)) atTop
      (𝓝 (logPotential μ z)) :=
    tendsto_atTop_iSup fun m n hmn => EReal.coe_le_coe_iff.2 (potTrunc_mono hμ z hmn)
  exact tendsto_nhds_unique h2 h1

/-! ### Subharmonicity of `-Φ_μ` -/

lemma ereal_neg_iSup {ι : Sort*} (f : ι → EReal) : -(⨆ i, f i) = ⨅ i, -f i := by
  apply le_antisymm
  · exact le_iInf fun i => EReal.neg_le_neg_iff.2 (le_iSup f i)
  · have : ⨆ i, f i ≤ -(⨅ i, -f i) :=
      iSup_le fun i => EReal.le_neg.2 (iInf_le (fun i => -f i) i)
    exact EReal.le_neg.1 this

lemma norm_circleMap_le (c : ℂ) (r θ : ℝ) : ‖circleMap c r θ‖ ≤ ‖c‖ + |r| := by
  have : circleMap c r θ = c + circleMap 0 r θ := by simp [circleMap]
  rw [this]
  exact (norm_add_le _ _).trans (by simp)

/-- Fubini on circles for the truncated kernel. -/
lemma circleAverage_negPotTrunc [IsFiniteMeasure μ] (hμ : Integrable (fun w => ‖w‖) μ) (N : ℕ)
    (c : ℂ) (r : ℝ) :
    circleAverage (fun z => ∫ w, -logKer N (z - w) ∂μ) c r =
      ∫ w, circleAverage (fun z => -logKer N (z - w)) c r ∂μ := by
  simp only [circleAverage, smul_eq_mul]
  rw [integral_const_mul]
  congr 1
  rw [intervalIntegral.integral_of_le two_pi_pos.le]
  simp_rw [intervalIntegral.integral_of_le two_pi_pos.le]
  refine integral_integral_swap ?_
  have hcont : Continuous (fun p : ℝ × ℂ => -logKer N (circleMap c r p.1 - p.2)) :=
    ((continuous_logKer N).comp (((continuous_circleMap c r).comp continuous_fst).sub
      continuous_snd)).neg
  refine Integrable.mono' (g := fun p : ℝ × ℂ => 1 * (((N : ℝ) + ‖c‖ + |r|) + ‖p.2‖))
    ((integrable_const (1 : ℝ)).mul_prod ((integrable_const _).add hμ))
    hcont.aestronglyMeasurable (Eventually.of_forall fun p => ?_)
  simp only [Function.uncurry, norm_neg, Real.norm_eq_abs, one_mul]
  refine (abs_logKer_le N _).trans ?_
  have h1 := norm_sub_le (circleMap c r p.1) p.2
  have h2 := norm_circleMap_le c r p.1
  linarith

/-- `-Φ_μ` is subharmonic on `ℂ`.  This is the potential-theoretic input for the
subharmonicity part of the Thouless formula (§4.6): `-Φ_μ(z) = ∫ log |z - w| dμ(w)`. -/
theorem subharmonic_neg_logPotential [IsFiniteMeasure μ] (hμ : Integrable (fun w => ‖w‖) μ) :
    Subharmonic (fun z => -logPotential μ z) := by
  have hfun : (fun z => -logPotential μ z) =
      fun z => ⨅ N : ℕ, (((fun N z => ∫ w, -logKer N (z - w) ∂μ) N z : ℝ) : EReal) := by
    funext z
    simp only [logPotential, ereal_neg_iSup, integral_neg, EReal.coe_neg]
  rw [hfun]
  refine subharmonicOn_iInf (fun N => ?_) (fun z => ?_) (fun N c r hr _ => ?_)
  · simp_rw [integral_neg]; exact (continuous_potTrunc hμ N).neg
  · intro m n hmn
    simp only [integral_neg, neg_le_neg_iff]
    exact potTrunc_mono hμ z hmn
  · rw [circleAverage_negPotTrunc hμ N c r]
    refine integral_mono ((integrable_logKer hμ N c).neg) ?_ (fun w => ?_)
    · -- integrability of the circle averages (bounded continuous in `w` up to a linear term)
      refine ((integrable_const ((N : ℝ) + ‖c‖ + |r|)).add hμ).mono' ?_
        (Eventually.of_forall fun w => ?_)
      · have : Continuous (fun w => circleAverage (fun z => -logKer N (z - w)) c r) := by
          simp only [circleAverage, smul_eq_mul]
          refine continuous_const.mul ?_
          refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
            (f := fun w θ => -logKer N (circleMap c r θ - w)) ?_ continuous_const
          exact ((continuous_logKer N).comp
            (((continuous_circleMap c r).comp continuous_snd).sub continuous_fst)).neg
        exact this.aestronglyMeasurable
      · rw [Real.norm_eq_abs]
        refine (abs_circleAverage_le_circleAverage_abs).trans ?_
        refine circleAverage_mono_on_of_le_circle ?_ (fun z hz => ?_)
        · exact ((continuous_logKer N).comp (continuous_id.sub continuous_const)).neg.abs
            |>.continuousOn.circleIntegrable'
        · show |-logKer N (z - w)| ≤ _
          rw [abs_neg]
          refine (abs_logKer_le N _).trans ?_
          have h1 := norm_sub_le z w
          have h2 : ‖z‖ ≤ ‖c‖ + |r| := by
            rw [mem_sphere, dist_eq_norm] at hz
            have := norm_le_norm_add_norm_sub' z c
            linarith
          simp only [Pi.add_apply]
          linarith
    · -- sub-mean value inequality for the truncated kernel, from subharmonicity of `log |z - w|`
      have h := (subharmonic_logNorm_sub w).truncBelow_le_circleAverage hr (subset_univ (closedBall c r)) N
      have e1 : ∀ z, truncBelow N (logNorm (fun z => z - w) z) = -logKer N (z - w) := by
        intro z
        rw [neg_logKer_eq_truncBelow]
        simp [logNorm]
      simp only [e1] at h
      exact h

/-! ### Double integrals of the truncated kernel -/

/-- Integrability on products, for continuous functions with linear growth. -/
lemma integrable_prod_of_bound [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : Integrable (fun w => ‖w‖) μ) (hν : Integrable (fun w => ‖w‖) ν) {F : ℂ × ℂ → ℝ}
    (hF : Continuous F) (C : ℝ) (hb : ∀ p, |F p| ≤ C + 2 * ‖p.1‖ + 2 * ‖p.2‖) :
    Integrable F (ν.prod μ) := by
  have h1 : Integrable (fun p : ℂ × ℂ => (2 * ‖p.1‖) * (1 : ℝ)) (ν.prod μ) :=
    (hν.const_mul 2).mul_prod (integrable_const 1)
  have h2 : Integrable (fun p : ℂ × ℂ => (1 : ℝ) * (2 * ‖p.2‖)) (ν.prod μ) :=
    (integrable_const 1).mul_prod (hμ.const_mul 2)
  refine (((integrable_const C).add h1).add h2).mono' hF.aestronglyMeasurable
    (Eventually.of_forall fun p => ?_)
  simp only [Real.norm_eq_abs, Pi.add_apply, mul_one, one_mul]
  exact hb p

/-- The nonnegative kernel `logKer N (z - w) + |z| + |w|`. -/
def posKer (N : ℕ) (z w : ℂ) : ℝ := logKer N (z - w) + ‖z‖ + ‖w‖

lemma posKer_nonneg (N : ℕ) (z w : ℂ) : 0 ≤ posKer N z w := by
  unfold posKer
  have := neg_norm_le_logKer N (z - w)
  have := norm_sub_le z w
  linarith

lemma continuous_posKer (N : ℕ) : Continuous (fun p : ℂ × ℂ => posKer N p.1 p.2) := by
  unfold posKer
  exact (((continuous_logKer N).comp (continuous_fst.sub continuous_snd)).add
    continuous_fst.norm).add continuous_snd.norm

lemma abs_posKer_le (N : ℕ) (z w : ℂ) : |posKer N z w| ≤ N + 2 * ‖z‖ + 2 * ‖w‖ := by
  rw [abs_of_nonneg (posKer_nonneg N z w)]
  unfold posKer
  have := logKer_le N (z - w)
  have := norm_nonneg z; have := norm_nonneg w
  linarith

lemma abs_logKer_sub_le (N : ℕ) (z w : ℂ) : |logKer N (z - w)| ≤ N + ‖z‖ + ‖w‖ := by
  have := abs_logKer_le N (z - w); have := norm_sub_le z w; linarith

lemma integrable_posKer_prod [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : Integrable (fun w => ‖w‖) μ) (hν : Integrable (fun w => ‖w‖) ν) (N : ℕ) :
    Integrable (fun p : ℂ × ℂ => posKer N p.1 p.2) (ν.prod μ) :=
  integrable_prod_of_bound hμ hν (continuous_posKer N) N fun p => abs_posKer_le N p.1 p.2

lemma integrable_logKer_prod [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : Integrable (fun w => ‖w‖) μ) (hν : Integrable (fun w => ‖w‖) ν) (N : ℕ) :
    Integrable (fun p : ℂ × ℂ => logKer N (p.1 - p.2)) (ν.prod μ) :=
  integrable_prod_of_bound hμ hν ((continuous_logKer N).comp (continuous_fst.sub continuous_snd))
    N fun p => by
      have := abs_logKer_sub_le N p.1 p.2
      have := norm_nonneg p.1; have := norm_nonneg p.2
      linarith

lemma integrable_normSum_prod [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : Integrable (fun w => ‖w‖) μ) (hν : Integrable (fun w => ‖w‖) ν) :
    Integrable (fun p : ℂ × ℂ => ‖p.1‖ + ‖p.2‖) (ν.prod μ) :=
  integrable_prod_of_bound hμ hν (continuous_fst.norm.add continuous_snd.norm) 0 fun p => by
    rw [abs_of_nonneg (by positivity)]
    have := norm_nonneg p.1; have := norm_nonneg p.2
    linarith

lemma integrable_posKer_left [IsFiniteMeasure μ] (hμ : Integrable (fun w => ‖w‖) μ) (N : ℕ)
    (z : ℂ) : Integrable (fun w => posKer N z w) μ := by
  refine ((integrable_const ((N : ℝ) + 2 * ‖z‖)).add (hμ.const_mul 2)).mono'
    ((continuous_posKer N).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
    (Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs]
  have := abs_posKer_le N z w
  simp only [Pi.add_apply] at *
  linarith

/-- Splitting the truncated double integral into a nonnegative part and a part independent of
`N`. -/
lemma iint_logKer_eq [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : Integrable (fun w => ‖w‖) μ) (hν : Integrable (fun w => ‖w‖) ν) (N : ℕ) :
    ∫ z, ∫ w, logKer N (z - w) ∂μ ∂ν =
      (∫ z, ∫ w, posKer N z w ∂μ ∂ν) - ∫ z, ∫ w, (‖z‖ + ‖w‖) ∂μ ∂ν := by
  rw [← integral_sub (integrable_posKer_prod hμ hν N).integral_prod_left
    (integrable_normSum_prod hμ hν).integral_prod_left]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  rw [← integral_sub (integrable_posKer_left hμ N z)
    (by exact (integrable_const ‖z‖).add hμ : Integrable (fun w => ‖z‖ + ‖w‖) μ)]
  congr 1; funext w; simp only [posKer]; ring

/-- Monotonicity of the nonnegative double integral in both measures. -/
lemma iint_posKer_mono [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : Integrable (fun w => ‖w‖) μ) (hν : Integrable (fun w => ‖w‖) ν)
    {μ' ν' : Measure ℂ} (hμ' : μ' ≤ μ) (hν' : ν' ≤ ν) (N : ℕ) :
    ∫ z, ∫ w, posKer N z w ∂μ' ∂ν' ≤ ∫ z, ∫ w, posKer N z w ∂μ ∂ν := by
  have : IsFiniteMeasure μ' := isFiniteMeasure_of_le μ hμ'
  have : IsFiniteMeasure ν' := isFiniteMeasure_of_le ν hν'
  have hμ'' := hμ.mono_measure hμ'
  have hν'' := hν.mono_measure hν'
  calc ∫ z, ∫ w, posKer N z w ∂μ' ∂ν' ≤ ∫ z, ∫ w, posKer N z w ∂μ ∂ν' :=
        integral_mono (integrable_posKer_prod hμ'' hν'' N).integral_prod_left
          (integrable_posKer_prod hμ hν'' N).integral_prod_left
          (fun z => integral_mono_measure hμ'
            (Eventually.of_forall fun w => posKer_nonneg N z w) (integrable_posKer_left hμ N z))
    _ ≤ _ := integral_mono_measure hν'
          (Eventually.of_forall fun z => integral_nonneg fun w => posKer_nonneg N z w)
          (integrable_posKer_prod hμ hν N).integral_prod_left

lemma iint_normSum_nonneg (μ ν : Measure ℂ) : 0 ≤ ∫ z, ∫ w, (‖z‖ + ‖w‖) ∂μ ∂ν :=
  integral_nonneg fun _ => integral_nonneg fun _ => by positivity

/-- Prop. A.2.2(c): `∫ Φ_μ dν = ∫ Φ_ν dμ`. -/
theorem mutualEnergy_comm [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : Integrable (fun w => ‖w‖) μ) (hν : Integrable (fun w => ‖w‖) ν) :
    mutualEnergy μ ν = mutualEnergy ν μ := by
  unfold mutualEnergy
  congr 1; funext N; congr 1
  rw [integral_integral_swap (integrable_logKer_prod hμ hν N)]
  congr 1; funext w; congr 1; funext z
  exact logKer_sub_comm N z w

lemma energy_ne_bot (μ : Measure ℂ) : energy μ ≠ ⊥ :=
  ne_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe _)
    (le_iSup (fun N : ℕ => ((∫ z, ∫ w, logKer N (z - w) ∂μ ∂μ : ℝ) : EReal)) 0))

lemma iint_logKer_le_energy (μ : Measure ℂ) (N : ℕ) :
    ((∫ z, ∫ w, logKer N (z - w) ∂μ ∂μ : ℝ) : EReal) ≤ energy μ :=
  le_iSup (fun N : ℕ => ((∫ z, ∫ w, logKer N (z - w) ∂μ ∂μ : ℝ) : EReal)) N

/-! ### Capacity -/

/-- `M1(K)`: Borel probability measures on `ℂ` carried by `K`. -/
def M1 (K : Set ℂ) : Set (Measure ℂ) := {μ | IsProbabilityMeasure μ ∧ μ Kᶜ = 0}

/-- `x ↦ e^{-x}` on `[-∞, ∞]`, with `e^{-∞} = 0` (for `x = ⊤`) and `e^{∞} = ∞`. -/
def expNeg (x : EReal) : ℝ≥0∞ :=
  if x = ⊤ then 0 else if x = ⊥ then ⊤ else ENNReal.ofReal (Real.exp (-x.toReal))

@[simp] lemma expNeg_top : expNeg ⊤ = 0 := by simp [expNeg]
@[simp] lemma expNeg_bot : expNeg ⊥ = ⊤ := by simp [expNeg]
@[simp] lemma expNeg_coe (x : ℝ) : expNeg x = ENNReal.ofReal (Real.exp (-x)) := by
  simp [expNeg]

lemma expNeg_antitone : Antitone expNeg := by
  intro x y hxy
  induction x using EReal.rec with
  | bot => simp
  | top => rw [top_le_iff.1 hxy]
  | coe x =>
    induction y using EReal.rec with
    | bot => exact absurd hxy (by simp)
    | top => simp
    | coe y =>
      simp only [expNeg_coe]
      exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (neg_le_neg (EReal.coe_le_coe_iff.1 hxy)))

lemma expNeg_eq_zero_iff {x : EReal} : expNeg x = 0 ↔ x = ⊤ := by
  induction x using EReal.rec with
  | bot => simp
  | top => simp
  | coe x => simp [Real.exp_pos]

/-- The logarithmic capacity of a compact set (A.2.1):
`Cap(K) = exp(-inf {E(μ) : μ ∈ M1(K)})`, with `e^{-∞} = 0`. -/
def capCompact (K : Set ℂ) : ℝ≥0∞ := expNeg (⨅ μ ∈ M1 K, energy μ)

/-- The capacity of a general (bounded) set via inner regularity on bounded open sets (A.2.2)
and outer regularity (A.2.3). -/
def capacity (B : Set ℂ) : ℝ≥0∞ :=
  ⨅ (O : Set ℂ) (_ : IsOpen O) (_ : Bornology.IsBounded O) (_ : B ⊆ O),
    ⨆ (K : Set ℂ) (_ : IsCompact K) (_ : K ⊆ O), capCompact K

/-- `e^{-E(μ)} ≤ Cap(K)` for every `μ ∈ M1(K)`. -/
theorem expNeg_energy_le_capCompact {K : Set ℂ} {μ : Measure ℂ} (hμ : μ ∈ M1 K) :
    expNeg (energy μ) ≤ capCompact K :=
  expNeg_antitone (iInf₂_le μ hμ)

/-- A compact set has capacity zero iff every probability measure on it has infinite energy. -/
theorem capCompact_eq_zero_iff {K : Set ℂ} : capCompact K = 0 ↔ ∀ μ ∈ M1 K, energy μ = ⊤ := by
  simp only [capCompact, expNeg_eq_zero_iff, iInf_eq_top]

lemma M1_mono {K L : Set ℂ} (h : K ⊆ L) : M1 K ⊆ M1 L := fun _ hμ =>
  ⟨hμ.1, measure_mono_null (compl_subset_compl.2 h) hμ.2⟩

/-- Prop. A.2.2(d) for compact sets. -/
theorem capCompact_mono {K L : Set ℂ} (h : K ⊆ L) : capCompact K ≤ capCompact L :=
  expNeg_antitone (biInf_mono (M1_mono h))

/-- Prop. A.2.2(d): capacity is monotone. -/
theorem capacity_mono {A B : Set ℂ} (h : A ⊆ B) : capacity A ≤ capacity B := by
  unfold capacity
  exact le_iInf fun O => le_iInf fun hO => le_iInf fun hOb => le_iInf fun hBO =>
    iInf_le_of_le O (iInf_le_of_le hO (iInf_le_of_le hOb (iInf_le_of_le (h.trans hBO) le_rfl)))

/-- For a compact set, the capacity defined via (A.2.2)–(A.2.3) dominates the one from (A.2.1).
(Equality is part of `CapacityRegularityStatement`.) -/
theorem capCompact_le_capacity {K : Set ℂ} (hK : IsCompact K) : capCompact K ≤ capacity K := by
  unfold capacity
  exact le_iInf fun O => le_iInf fun _ => le_iInf fun _ => le_iInf fun hKO =>
    le_iSup_of_le K (le_iSup_of_le hK (le_iSup_of_le hKO le_rfl))

/-! ### Example A.2.3: atoms -/

/-- Example A.2.3: a measure with an atom has infinite energy. -/
theorem energy_eq_top_of_atom [IsFiniteMeasure μ] (hμ : Integrable (fun w => ‖w‖) μ) {a : ℂ}
    (ha : μ {a} ≠ 0) : energy μ = ⊤ := by
  set m := μ.real {a} with hmdef
  have hm : 0 < m := ENNReal.toReal_pos ha (measure_ne_top μ _)
  set C := ∫ z, ∫ w, (‖z‖ + ‖w‖) ∂μ ∂μ
  have key : ∀ N : ℕ, m * m * N - C ≤ ∫ z, ∫ w, logKer N (z - w) ∂μ ∂μ := by
    intro N
    rw [iint_logKer_eq hμ hμ N]
    have h1 := iint_posKer_mono hμ hμ (Measure.restrict_le_self (s := {a}))
      (Measure.restrict_le_self (s := {a})) N
    have h2 : ∫ z, ∫ w, posKer N z w ∂(μ.restrict {a}) ∂(μ.restrict {a}) =
        m * (m * posKer N a a) := by
      simp only [integral_singleton, smul_eq_mul, hmdef]
    have h3 : (N : ℝ) ≤ posKer N a a := by
      simp only [posKer, sub_self, logKer_zero]; have := norm_nonneg a; linarith
    have h4 : m * m * N ≤ m * (m * posKer N a a) := by
      rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left h3 (by positivity)
    linarith
  unfold energy mutualEnergy
  refine EReal.eq_top_iff_forall_lt _ |>.2 fun y => ?_
  obtain ⟨N, hN⟩ := exists_nat_gt ((y + C + 1) / (m * m))
  refine lt_of_lt_of_le ?_ (le_iSup _ N)
  rw [EReal.coe_lt_coe_iff]
  have h5 := key N
  have h6 : y + C + 1 < m * m * N := by
    rwa [div_lt_iff₀ (by positivity), mul_comm] at hN
  linarith

/-- Example A.2.3: countable compact sets have capacity zero. -/
theorem capCompact_eq_zero_of_countable {K : Set ℂ} (hK : IsCompact K) (hKc : K.Countable) :
    capCompact K = 0 := by
  rw [capCompact_eq_zero_iff]
  rintro μ ⟨hprob, hμK⟩
  have hμ := integrable_norm_of_compact hK hμK
  obtain ⟨a, -, ha⟩ : ∃ a ∈ K, μ {a} ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : μ K = 0 := by
      rw [← Set.biUnion_of_singleton K]
      exact (measure_biUnion_null_iff hKc).2 h
    have h1 : μ univ ≤ μ K + μ Kᶜ := by
      rw [← union_compl_self K]; exact measure_union_le _ _
    rw [h0, hμK, measure_univ, zero_add] at h1
    exact absurd h1 (by simp)
  exact energy_eq_top_of_atom hμ ha

/-! ### Proposition A.2.2(f) -/

/-- Prop. A.2.2(f): a finite measure of finite logarithmic energy gives no weight to Borel sets
of capacity zero. -/
theorem measure_eq_zero_of_capacity_eq_zero [IsFiniteMeasure μ]
    (hμ : Integrable (fun w => ‖w‖) μ) (hE : energy μ ≠ ⊤) {B : Set ℂ} (hB : MeasurableSet B)
    (hcap : capacity B = 0) : μ B = 0 := by
  by_contra hne
  obtain ⟨K, hKB, hK, hμK⟩ := hB.exists_lt_isCompact (pos_iff_ne_zero.2 hne)
  have hμKne : μ K ≠ 0 := hμK.ne'
  have hμKtop : μ K ≠ ⊤ := measure_ne_top _ _
  set c : ℝ≥0∞ := (μ K)⁻¹ with hc
  set η : Measure ℂ := c • μ.restrict K with hη
  have hηM : η ∈ M1 K := by
    refine ⟨⟨?_⟩, ?_⟩
    · simp only [hη, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul, hc]
      exact ENNReal.inv_mul_cancel hμKne hμKtop
    · simp only [hη, Measure.smul_apply, smul_eq_mul]
      rw [Measure.restrict_apply hK.measurableSet.compl, compl_inter_self, measure_empty,
        mul_zero]
  have : IsProbabilityMeasure η := hηM.1
  have hμK' : Integrable (fun w => ‖w‖) (μ.restrict K) := hμ.restrict
  set E0 := (energy μ).toReal
  have hE0 : energy μ = (E0 : EReal) := (EReal.coe_toReal hE (energy_ne_bot μ)).symm
  set C := ∫ z, ∫ w, (‖z‖ + ‖w‖) ∂μ ∂μ
  have key : ∀ N : ℕ, ∫ z, ∫ w, logKer N (z - w) ∂η ∂η ≤ c.toReal * (c.toReal * (E0 + C)) := by
    intro N
    have e1 : ∫ z, ∫ w, logKer N (z - w) ∂η ∂η =
        c.toReal * (c.toReal * ∫ z, ∫ w, logKer N (z - w) ∂(μ.restrict K) ∂(μ.restrict K)) := by
      simp only [hη, integral_smul_measure, smul_eq_mul, integral_const_mul]
    have e2 : ∫ z, ∫ w, logKer N (z - w) ∂(μ.restrict K) ∂(μ.restrict K) ≤ E0 + C := by
      rw [iint_logKer_eq hμK' hμK' N]
      have h1 := iint_posKer_mono hμ hμ (Measure.restrict_le_self (s := K))
        (Measure.restrict_le_self (s := K)) N
      have h2 := iint_normSum_nonneg (μ.restrict K) (μ.restrict K)
      have h3 : ∫ z, ∫ w, logKer N (z - w) ∂μ ∂μ ≤ E0 := by
        have := iint_logKer_le_energy μ N
        rwa [hE0, EReal.coe_le_coe_iff] at this
      rw [iint_logKer_eq hμ hμ N] at h3
      linarith
    rw [e1]
    have hc0 : 0 ≤ c.toReal := ENNReal.toReal_nonneg
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e2 hc0) hc0
  have hEη : energy η ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top (c.toReal * (c.toReal * (E0 + C))))
      (iSup_le fun N => EReal.coe_le_coe_iff.2 (key N))
  have h1 : expNeg (energy η) ≠ 0 := fun h => hEη (expNeg_eq_zero_iff.1 h)
  have h2 : capCompact K ≠ 0 := fun h => h1 (le_antisymm
    ((expNeg_energy_le_capCompact hηM).trans h.le) zero_le)
  exact h2 (le_antisymm ((capCompact_le_capacity hK).trans
    ((capacity_mono hKB).trans hcap.le)) zero_le)

/-! ### Theorem A.2.9, first half -/

/-- Theorem A.2.9, first half (lower envelope inequality): if finite measures `νₙ`, all carried
by a fixed compact set `K`, converge weakly to `ν`, then `Φ_ν(z) ≤ liminf Φ_{νₙ}(z)` for every
`z`.  (The book also assumes `sup νₙ(K) < ∞`; this is not needed for this half.) -/
theorem logPotential_le_liminf {K : Set ℂ} (hK : IsCompact K) {νs : ℕ → Measure ℂ}
    {ν : Measure ℂ} [∀ n, IsFiniteMeasure (νs n)] [IsFiniteMeasure ν]
    (hνs : ∀ n, νs n Kᶜ = 0) (hν : ν Kᶜ = 0)
    (hconv : ∀ f : ℂ →ᵇ ℝ, Tendsto (fun n => ∫ w, f w ∂(νs n)) atTop (𝓝 (∫ w, f w ∂ν)))
    (z : ℂ) : logPotential ν z ≤ liminf (fun n => logPotential (νs n) z) atTop := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  refine iSup_le fun N => ?_
  set M : ℝ := ‖z‖ + |R|
  set g : ℂ → ℝ := fun w => max (logKer N (z - w)) (-M) with hg
  have hgc : Continuous g :=
    ((continuous_logKer N).comp (continuous_const.sub continuous_id)).max continuous_const
  have hgb : ∀ w, ‖g w‖ ≤ N + M := by
    intro w
    have hM : 0 ≤ M := by positivity
    rw [Real.norm_eq_abs, abs_le]
    constructor
    · have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      exact le_trans (by linarith) (le_max_right _ _)
    · exact max_le (by have := logKer_le N (z - w); linarith) (by
        have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; linarith)
  set G : ℂ →ᵇ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup g hgc (N + M) hgb
  have hgK : ∀ w ∈ K, g w = logKer N (z - w) := by
    intro w hw
    refine max_eq_left (le_trans ?_ (neg_norm_le_logKer N (z - w)))
    have h1 := norm_sub_le z w
    have h2 : ‖w‖ ≤ |R| := by
      have := hR hw
      rw [mem_closedBall, dist_zero_right] at this
      exact this.trans (le_abs_self R)
    linarith
  have hint : ∀ (ρ : Measure ℂ), ρ Kᶜ = 0 → ∫ w, G w ∂ρ = ∫ w, logKer N (z - w) ∂ρ := by
    intro ρ hρ
    refine integral_congr_ae ?_
    have : ∀ᵐ w ∂ρ, w ∈ K := measure_eq_zero_iff_ae_notMem.1 hρ |>.mono fun w hw => by
      simpa using hw
    filter_upwards [this] with w hw
    exact hgK w hw
  have htend := hconv G
  rw [hint ν hν] at htend
  simp_rw [hint _ (hνs _)] at htend
  have h1 : Tendsto (fun n => ((∫ w, logKer N (z - w) ∂(νs n) : ℝ) : EReal)) atTop
      (𝓝 ((∫ w, logKer N (z - w) ∂ν : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.tendsto _).comp htend
  rw [← h1.liminf_eq]
  exact liminf_le_liminf (Eventually.of_forall fun n =>
    le_iSup (fun N : ℕ => ((∫ w, logKer N (z - w) ∂(νs n) : ℝ) : EReal)) N)

/-! ### Equilibrium measures (Theorem A.2.6, Definition A.2.7) -/

/-- `ρ` is an equilibrium measure of `K`: it minimizes the energy over `M1(K)`
(Definition A.2.7; cf. Definition 4.6.5). -/
def IsEquilibriumMeasure (K : Set ℂ) (ρ : Measure ℂ) : Prop :=
  ρ ∈ M1 K ∧ ∀ ν ∈ M1 K, energy ρ ≤ energy ν

lemma IsEquilibriumMeasure.energy_eq_iInf {K : Set ℂ} {ρ : Measure ℂ}
    (h : IsEquilibriumMeasure K ρ) : energy ρ = ⨅ μ ∈ M1 K, energy μ :=
  le_antisymm (le_iInf₂ h.2) (iInf₂_le ρ h.1)

/-- (A.2.8): `E(ρ_K) = -log Cap(K)`, i.e. `Cap(K) = e^{-E(ρ_K)}`. -/
theorem IsEquilibriumMeasure.capCompact_eq {K : Set ℂ} {ρ : Measure ℂ}
    (h : IsEquilibriumMeasure K ρ) : capCompact K = expNeg (energy ρ) := by
  rw [capCompact, h.energy_eq_iInf]

/-- An equilibrium measure of a set of positive capacity has finite energy. -/
theorem IsEquilibriumMeasure.energy_ne_top {K : Set ℂ} {ρ : Measure ℂ}
    (h : IsEquilibriumMeasure K ρ) (hcap : capCompact K ≠ 0) : energy ρ ≠ ⊤ := by
  intro htop; apply hcap; rw [h.capCompact_eq, htop, expNeg_top]

/-- **Proposition A.2.5** (strict convexity of the energy), stated for probability measures on a
compact set: if `μ ≠ ν` have finite energy, then `E(μ/2 + ν/2) < E(μ)/2 + E(ν)/2`.  The book
only sketches the proof (via Fourier transforms of measures); recorded as a statement. -/
def EnergyStrictConvexityStatement : Prop :=
  ∀ K : Set ℂ, IsCompact K → ∀ μ ∈ M1 K, ∀ ν ∈ M1 K, energy μ ≠ ⊤ → energy ν ≠ ⊤ → μ ≠ ν →
    energy ((1 / 2 : ℝ≥0∞) • μ + (1 / 2 : ℝ≥0∞) • ν) <
      (((energy μ).toReal + (energy ν).toReal) / 2 : ℝ)

/-- **Theorem A.2.6, uniqueness**, deduced from strict convexity (Prop. A.2.5). -/
theorem IsEquilibriumMeasure.unique (hconv : EnergyStrictConvexityStatement) {K : Set ℂ}
    (hK : IsCompact K) (hcap : capCompact K ≠ 0) {ρ ρ' : Measure ℂ}
    (h : IsEquilibriumMeasure K ρ) (h' : IsEquilibriumMeasure K ρ') : ρ = ρ' := by
  by_contra hne
  have hfin := h.energy_ne_top hcap
  have heq : energy ρ' = energy ρ := le_antisymm (h'.2 ρ h.1) (h.2 ρ' h'.1)
  have hfin' : energy ρ' ≠ ⊤ := heq ▸ hfin
  have hmix : (1 / 2 : ℝ≥0∞) • ρ + (1 / 2 : ℝ≥0∞) • ρ' ∈ M1 K := by
    have := h.1.1; have := h'.1.1
    refine ⟨⟨?_⟩, ?_⟩
    · simp [ENNReal.inv_two_add_inv_two]
    · simp [h.1.2, h'.1.2]
  have hlt := hconv K hK ρ h.1 ρ' h'.1 hfin hfin' hne
  have hle := h.2 _ hmix
  rw [heq] at hlt
  have he : energy ρ = ((energy ρ).toReal : EReal) :=
    (EReal.coe_toReal hfin (energy_ne_bot ρ)).symm
  have h2 : (((energy ρ).toReal + (energy ρ).toReal) / 2 : ℝ) = (energy ρ).toReal := by ring
  rw [h2, ← he] at hlt
  exact absurd (lt_of_le_of_lt hle hlt) (lt_irrefl _)

/-- **Theorem A.2.6, existence**: a compact set of positive capacity carries a probability
measure of minimal energy.  The book's proof uses weak-* compactness of `M1(K)` and the weak-*
lower semicontinuity of the energy (Lemma A.2.4).  Recorded as a statement. -/
def EquilibriumExistenceStatement : Prop :=
  ∀ K : Set ℂ, IsCompact K → capCompact K ≠ 0 → ∃ ρ, IsEquilibriumMeasure K ρ

/-! ### Harmonicity off the support (Prop. A.2.2(b), second half) -/

/-- Prop. A.2.2(b), second half: the potential of a compactly supported finite measure is
harmonic off its support.  Near a point `z₀ ∉ K` we write
`log |z - w| = log |z₀ - w| + Re log (1 + (z - z₀)/(z₀ - w))` and differentiate under the
integral sign. -/
theorem harmonicOnNhd_logPotential [IsFiniteMeasure μ] {K : Set ℂ} (hK : IsCompact K)
    (hμK : μ Kᶜ = 0) :
    InnerProductSpace.HarmonicOnNhd (fun z => (logPotential μ z).toReal) Kᶜ := by
  have hμ := integrable_norm_of_compact hK hμK
  have hae : ∀ᵐ w ∂μ, w ∈ K := measure_eq_zero_iff_ae_notMem.1 hμK |>.mono fun w hw => by
    simpa using hw
  intro z0 hz0
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hK.isClosed.isOpen_compl z0 hz0
  have hdist : ∀ w ∈ K, ε ≤ ‖z0 - w‖ := by
    intro w hw
    by_contra h
    push Not at h
    exact hball (by rw [mem_ball, dist_eq_norm, norm_sub_rev]; exact h) hw
  set s := ball z0 (ε / 2) with hs
  have hzs : ∀ z ∈ s, ‖z - z0‖ < ε / 2 := fun z hz => by rwa [hs, mem_ball, dist_eq_norm] at hz
  have hdist' : ∀ z ∈ s, ∀ w ∈ K, ε / 2 ≤ ‖z - w‖ := by
    intro z hz w hw
    have h1 := hdist w hw
    have h2 := hzs z hz
    have h3 : ‖z0 - w‖ ≤ ‖z0 - z‖ + ‖z - w‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    rw [norm_sub_rev z0 z] at h3
    linarith
  have hne : ∀ w ∈ K, z0 - w ≠ 0 := fun w hw h => by
    have := hdist w hw; rw [h, norm_zero] at this; linarith
  set L : ℂ → ℂ → ℂ := fun z w => Complex.log (1 + (z - z0) / (z0 - w)) with hL
  have hsmall : ∀ z ∈ s, ∀ w ∈ K, ‖(z - z0) / (z0 - w)‖ ≤ 1 / 2 := by
    intro z hz w hw
    rw [norm_div, div_le_iff₀ (norm_pos_iff.2 (hne w hw))]
    have := hzs z hz; have := hdist w hw
    linarith
  have hslit : ∀ z ∈ s, ∀ w ∈ K, 1 + (z - z0) / (z0 - w) ∈ slitPlane := by
    intro z hz w hw
    refine Or.inl ?_
    have h1 := Complex.abs_re_le_norm ((z - z0) / (z0 - w))
    have h2 := hsmall z hz w hw
    rw [Complex.add_re, Complex.one_re]
    have := neg_abs_le ((z - z0) / (z0 - w)).re
    linarith
  have hreL : ∀ z ∈ s, ∀ w ∈ K, (L z w).re = Real.log ‖z - w‖ - Real.log ‖z0 - w‖ := by
    intro z hz w hw
    have hzw : z - w ≠ 0 := fun h => by
      have := hdist' z hz w hw; rw [h, norm_zero] at this; linarith
    have : 1 + (z - z0) / (z0 - w) = (z - w) / (z0 - w) := by
      field_simp [hne w hw]; ring
    simp only [hL, this, Complex.log_re, norm_div]
    rw [Real.log_div (norm_ne_zero_iff.2 hzw) (norm_ne_zero_iff.2 (hne w hw))]
  have hderiv : ∀ z ∈ s, ∀ w ∈ K, HasDerivAt (fun z => L z w) (1 / (z - w)) z := by
    intro z hz w hw
    have hzw : z - w ≠ 0 := fun h => by
      have := hdist' z hz w hw; rw [h, norm_zero] at this; linarith
    have h1 : HasDerivAt (fun z => 1 + (z - z0) / (z0 - w)) (1 / (z0 - w)) z := by
      have := ((hasDerivAt_id z).sub_const z0).div_const (z0 - w)
      simpa using this.const_add 1
    have h2 := h1.clog (hslit z hz w hw)
    convert h2 using 1
    have e : (1 : ℂ) + (z - z0) / (z0 - w) = (z - w) / (z0 - w) := by
      field_simp [hne w hw]; ring
    rw [e, div_div_div_cancel_right₀ (hne w hw)]
  have hmeasL : ∀ z, AEStronglyMeasurable (L z) μ := fun z =>
    (Complex.measurable_log.comp (measurable_const.add
      (measurable_const.div (measurable_const.sub measurable_id)))).aestronglyMeasurable
  have hintL : ∀ z ∈ s, Integrable (L z) μ := by
    intro z hz
    refine Integrable.of_bound (hmeasL z) (3 / 4) (hae.mono fun w hw => ?_)
    have := norm_log_one_add_half_le_self (hsmall z hz w hw)
    have h2 := hsmall z hz w hw
    simp only [hL]
    linarith
  have hG : DifferentiableOn ℂ (fun z => ∫ w, L z w ∂μ) s := by
    intro z hz
    have hsn : s ∈ 𝓝 z := isOpen_ball.mem_nhds hz
    have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := L)
      (F' := fun z w => 1 / (z - w)) (x₀ := z) (bound := fun _ => 2 / ε) hsn
      (Eventually.of_forall fun x => hmeasL x) (hintL z hz)
      ((measurable_const.div (measurable_const.sub measurable_id)).aestronglyMeasurable)
      (hae.mono fun w hw x hx => ?_) (integrable_const _)
      (hae.mono fun w hw x hx => hderiv x hx w hw)
    · exact this.2.differentiableAt.differentiableWithinAt
    · rw [norm_div, norm_one, div_le_div_iff₀ (by linarith [hdist' x hx w hw]) hε]
      have := hdist' x hx w hw
      linarith
  have hGa : AnalyticAt ℂ (fun z => ∫ w, L z w ∂μ) z0 :=
    hG.analyticAt (isOpen_ball.mem_nhds (mem_ball_self (half_pos hε)))
  have hre := hGa.harmonicAt_re
  set C0 := ∫ w, -Real.log ‖z0 - w‖ ∂μ
  have hlogint : Integrable (fun w => -Real.log ‖z0 - w‖) μ := by
    refine ((integrable_const (‖z0‖ + 1 / ε)).add hμ).mono'
      ((Real.measurable_log.comp (measurable_const.sub measurable_id).norm).neg.aestronglyMeasurable)
      (hae.mono fun w hw => ?_)
    have hpos : 0 < ‖z0 - w‖ := norm_pos_iff.2 (hne w hw)
    have h1 := Real.log_le_sub_one_of_pos hpos
    have h2 := Real.log_le_sub_one_of_pos (inv_pos.2 hpos)
    rw [Real.log_inv] at h2
    have h3 : ‖z0 - w‖⁻¹ ≤ 1 / ε := by
      rw [one_div]; exact inv_anti₀ hε (hdist w hw)
    have h4 := norm_sub_le z0 w
    simp only [Real.norm_eq_abs, abs_neg, Pi.add_apply]
    rw [abs_le]
    constructor <;> linarith [inv_pos.2 hpos]
  have heq : (fun z => (logPotential μ z).toReal) =ᶠ[𝓝 z0]
      (fun z => C0 - (∫ w, L z w ∂μ).re) := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self (half_pos hε))] with z hz
    rw [logPotential_eq_integral_of_dist hμ hμK (half_pos hε) (hdist' z hz), EReal.toReal_coe]
    have h1 : ∫ w, -Real.log ‖z - w‖ ∂μ = ∫ w, (-Real.log ‖z0 - w‖ - (L z w).re) ∂μ := by
      refine integral_congr_ae (hae.mono fun w hw => ?_)
      simp only
      rw [hreL z hz w hw]; ring
    have hre_int : Integrable (fun w => (L z w).re) μ := (hintL z hz).re
    rw [h1, integral_sub hlogint hre_int]
    congr 1
    exact integral_re (hintL z hz)
  rw [InnerProductSpace.harmonicAt_congr_nhds heq]
  exact (InnerProductSpace.harmonicAt_const C0).sub hre

/-! ### Further statements of Appendix A.2 (recorded, not proved) -/

/-- Prop. A.2.2(e) together with the consistency of (A.2.1) and (A.2.2)–(A.2.3) on compact sets:
capacity is continuous along decreasing sequences of compact sets and increasing sequences of
bounded open sets. -/
def CapacityRegularityStatement : Prop :=
  (∀ K : Set ℂ, IsCompact K → capacity K = capCompact K) ∧
  (∀ K : ℕ → Set ℂ, (∀ n, IsCompact (K n)) → Antitone K →
     Tendsto (fun n => capacity (K n)) atTop (𝓝 (capacity (⋂ n, K n)))) ∧
  (∀ O : ℕ → Set ℂ, (∀ n, IsOpen (O n)) → Monotone O → Bornology.IsBounded (⋃ n, O n) →
     Tendsto (fun n => capacity (O n)) atTop (𝓝 (capacity (⋃ n, O n))))

/-- **Theorem A.2.8 (Frostman)**: for the equilibrium measure `ρ` of a compact set of positive
capacity, `Φ_ρ ≤ E(ρ)` everywhere, with equality quasi-everywhere on `K`. -/
def FrostmanStatement : Prop :=
  ∀ (K : Set ℂ) (ρ : Measure ℂ), IsCompact K → capCompact K ≠ 0 → IsEquilibriumMeasure K ρ →
    (∀ z, logPotential ρ z ≤ energy ρ) ∧ capacity {z ∈ K | logPotential ρ z < energy ρ} = 0

/-- **Theorem A.2.9, second half**: in the situation of `logPotential_le_liminf` (with
`sup νₙ(K) < ∞`), equality holds quasi-everywhere. -/
def LowerEnvelopeStatement : Prop :=
  ∀ (K : Set ℂ) (νs : ℕ → Measure ℂ) (ν : Measure ℂ), IsCompact K →
    (∀ n, IsFiniteMeasure (νs n)) → IsFiniteMeasure ν → (∀ n, νs n Kᶜ = 0) → ν Kᶜ = 0 →
    (∃ C, ∀ n, νs n K ≤ C) →
    (∀ f : ℂ →ᵇ ℝ, Tendsto (fun n => ∫ w, f w ∂(νs n)) atTop (𝓝 (∫ w, f w ∂ν))) →
    capacity {z | liminf (fun n => logPotential (νs n) z) atTop ≠ logPotential ν z} = 0

/-- **Lemma A.2.10**: a bounded Borel set of positive capacity carries a probability measure
with continuous (in particular finite) potential. -/
def ContinuousPotentialStatement : Prop :=
  ∀ X : Set ℂ, Bornology.IsBounded X → MeasurableSet X → capacity X ≠ 0 →
    ∃ η : Measure ℂ, IsProbabilityMeasure η ∧ η Xᶜ = 0 ∧
      ∃ f : ℂ → ℝ, Continuous f ∧ ∀ z, logPotential η z = f z

/-- **Theorem A.2.11**: compact sets of capacity zero have Hausdorff dimension zero. -/
def CapacityZeroDimStatement : Prop :=
  ∀ K : Set ℂ, IsCompact K → capCompact K = 0 → dimH K = 0

end DF
