/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators, I*,
§1.9.2 (pp. 85–88): power-law growth of boundary values of the Borel transform.

# Main definitions

* `DF.upperAlphaDeriv α μ E` — the upper `α`-derivative
  `D^α_μ(E) = limsup_{ε↓0} μ((E - ε, E + ε)) / (2ε)^α` (p. 86);
* `DF.alphaQ α μ E = limsup_{ε↓0} ε^{1-α} Im F_μ(E + iε)` (1.9.26);
* `DF.alphaR α μ E = limsup_{ε↓0} ε^{1-α} |F_μ(E + iε)|` (1.9.27);
  all three valued in `ℝ≥0∞`.

# Main results

* `DF.ofReal_two_rpow_mul_upperAlphaDeriv_le` — `2^{α-1} D^α_μ(E) ≤ Q^α_μ(E)` (p. 87);
* `DF.alphaQ_le_alphaR` — `Q^α_μ(E) ≤ R^α_μ(E)`;
* `DF.alphaR_lt_top_of_upperAlphaDeriv_lt_top` — for `0 < α < 1`, `D^α_μ(E) < ∞` implies
  `R^α_μ(E) < ∞`;
* `DF.upperAlphaDeriv_lt_top_iff` — Proposition 1.9.7 (del Rio–Jitomirskaya–Last–Simon).

# Deviation in the proof

The book bounds `R^α` by a Fubini/change-of-variables computation (1.9.28)–(1.9.29); we use the
layer-cake formula instead: the superlevel sets of `x ↦ |x - z|⁻¹` are intervals centred at
`E = Re z` whose radius at level `t` is at most `1/t`, which gives
`∫ |x - z|⁻¹ dμ ≤ K ∫_0^{1/ε} t^{-α} dt = K ε^{α-1} / (1 - α)`.
-/
import DamanikFillman.Ch1.BorelDerivative

noncomputable section

open MeasureTheory Filter Topology Set Metric Complex
open scoped ENNReal

namespace DF

/-- The upper `α`-derivative `D^α_μ(E) = limsup_{ε↓0} μ((E-ε, E+ε)) / (2ε)^α`. -/
def upperAlphaDeriv (α : ℝ) (μ : Measure ℝ) (E : ℝ) : ℝ≥0∞ :=
  limsup (fun ε : ℝ => μ (ball E ε) / ENNReal.ofReal ((2 * ε) ^ α)) (𝓝[>] 0)

/-- `Q^α_μ(E) = limsup_{ε↓0} ε^{1-α} Im F_μ(E + iε)` (1.9.26). -/
def alphaQ (α : ℝ) (μ : Measure ℝ) (E : ℝ) : ℝ≥0∞ :=
  limsup (fun ε : ℝ => ENNReal.ofReal (ε ^ (1 - α) * (borelTransform μ (E + ε * I)).im))
    (𝓝[>] 0)

/-- `R^α_μ(E) = limsup_{ε↓0} ε^{1-α} |F_μ(E + iε)|` (1.9.27). -/
def alphaR (α : ℝ) (μ : Measure ℝ) (E : ℝ) : ℝ≥0∞ :=
  limsup (fun ε : ℝ => ENNReal.ofReal (ε ^ (1 - α)) * ‖borelTransform μ (E + ε * I)‖ₑ)
    (𝓝[>] 0)

/-- `Q^α_μ(E) ≤ R^α_μ(E)`. -/
theorem alphaQ_le_alphaR (α : ℝ) (μ : Measure ℝ) (E : ℝ) : alphaQ α μ E ≤ alphaR α μ E := by
  refine limsup_le_limsup ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  rw [ENNReal.ofReal_mul (by positivity), ← ofReal_norm_eq_enorm]
  gcongr
  exact (le_abs_self _).trans (Complex.abs_im_le_norm _)

/-- Lower bound for the imaginary part: `Im F_μ(E + iε) ≥ μ((E - ε, E + ε)) / (2ε)`. -/
lemma ofReal_im_ge_ball (μ : Measure ℝ) [IsFiniteMeasure μ] (E : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ENNReal.ofReal (1 / (2 * ε)) * μ (ball E ε) ≤
      ENNReal.ofReal ((borelTransform μ (E + ε * I)).im) := by
  have hint : Integrable (fun x => ε / ((x - E) ^ 2 + ε ^ 2)) μ := by
    have := integrable_poissonKernel μ hε E
    refine (this.const_mul Real.pi).congr (Eventually.of_forall fun x => ?_)
    simp only [poissonKernel]
    field_simp
  rw [borelTransform_im μ E hε.ne', ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun x => by positivity)]
  calc ENNReal.ofReal (1 / (2 * ε)) * μ (ball E ε)
      = ∫⁻ _ in ball E ε, ENNReal.ofReal (1 / (2 * ε)) ∂μ := by rw [setLIntegral_const]
    _ ≤ ∫⁻ x in ball E ε, ENNReal.ofReal (ε / ((x - E) ^ 2 + ε ^ 2)) ∂μ := by
        apply setLIntegral_mono (by fun_prop)
        intro x hx
        apply ENNReal.ofReal_le_ofReal
        have hx' : (x - E) ^ 2 < ε ^ 2 := by
          rw [mem_ball, Real.dist_eq] at hx
          have := sq_lt_sq' (by linarith [abs_nonneg (x - E), neg_abs_le (x - E)]) hx
          simpa [sq_abs] using this
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
    _ ≤ ∫⁻ x, ENNReal.ofReal (ε / ((x - E) ^ 2 + ε ^ 2)) ∂μ := setLIntegral_le_lintegral _ _

/-- `2^{α-1} D^α_μ(E) ≤ Q^α_μ(E)` (book p. 87). -/
theorem ofReal_two_rpow_mul_upperAlphaDeriv_le (α : ℝ) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (E : ℝ) : ENNReal.ofReal (2 ^ (α - 1)) * upperAlphaDeriv α μ E ≤ alphaQ α μ E := by
  rw [upperAlphaDeriv, ← ENNReal.limsup_const_mul_of_ne_top ENNReal.ofReal_ne_top]
  refine limsup_le_limsup ?_
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  have h1 := ofReal_im_ge_ball μ E hε
  have hpos : 0 < (2 * ε) ^ α := by positivity
  calc ENNReal.ofReal (2 ^ (α - 1)) * (μ (ball E ε) / ENNReal.ofReal ((2 * ε) ^ α))
      = ENNReal.ofReal (ε ^ (1 - α)) * (ENNReal.ofReal (1 / (2 * ε)) * μ (ball E ε)) := by
        rw [ENNReal.div_eq_inv_mul, ← ENNReal.ofReal_inv_of_pos hpos, ← mul_assoc,
          ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 2
        rw [Real.mul_rpow (by norm_num) hε.le, Real.rpow_sub (by norm_num : (0 : ℝ) < 2),
          Real.rpow_sub hε, Real.rpow_one, Real.rpow_one]
        field_simp
    _ ≤ ENNReal.ofReal (ε ^ (1 - α)) * ENNReal.ofReal ((borelTransform μ (E + ε * I)).im) := by
        gcongr
    _ = ENNReal.ofReal (ε ^ (1 - α) * (borelTransform μ (E + ε * I)).im) := by
        rw [ENNReal.ofReal_mul (by positivity)]

/-! ### Upper bound for `R^α` -/

lemma inv_norm_superlevel_eq_ball {ε t : ℝ} (hε : 0 < ε) (ht : 0 < t) (E : ℝ) :
    {x : ℝ | t < 1 / Real.sqrt ((x - E) ^ 2 + ε ^ 2)} =
      ball E (Real.sqrt ((1 / t) ^ 2 - ε ^ 2)) := by
  ext x
  simp only [mem_setOf_eq, mem_ball, Real.dist_eq]
  have hq : 0 < (x - E) ^ 2 + ε ^ 2 := by positivity
  rw [lt_one_div ht (Real.sqrt_pos.2 hq), Real.sqrt_lt' (by positivity),
    Real.lt_sqrt (abs_nonneg _), sq_abs]
  constructor <;> intro h <;> linarith

lemma enorm_inv_sub (x E ε : ℝ) (hε : 0 < ε) :
    ‖((x : ℂ) - (E + ε * I))⁻¹‖ₑ = ENNReal.ofReal (1 / Real.sqrt ((x - E) ^ 2 + ε ^ 2)) := by
  rw [← ofReal_norm_eq_enorm, norm_inv, Complex.norm_def, Complex.normSq_apply, one_div]
  congr 3
  simp; ring

/-- From `D^α_μ(E) < ∞` and finiteness of `μ`, a global bound `μ(B(E, ρ)) ≤ K ρ^α`. -/
lemma exists_ball_le_of_upperAlphaDeriv_lt_top {α : ℝ} (hα : 0 < α) (μ : Measure ℝ)
    [IsFiniteMeasure μ] {E : ℝ} (h : upperAlphaDeriv α μ E < ∞) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ ρ, 0 < ρ → μ (ball E ρ) ≤ ENNReal.ofReal (K * ρ ^ α) := by
  obtain ⟨c, hc, -⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 h
  have hev := eventually_lt_of_limsup_lt hc
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hu0 : (0 : ℝ) < u := hu
  refine ⟨max ((c : ℝ) * 2 ^ α) (μ.real univ / u ^ α), le_max_of_le_right (by positivity),
    fun ρ hρ => ?_⟩
  rcases lt_or_ge ρ u with hρu | hρu
  · have hlt : μ (ball E ρ) / ENNReal.ofReal ((2 * ρ) ^ α) < c := hsub ⟨hρ, hρu⟩
    have hpos : ENNReal.ofReal ((2 * ρ) ^ α) ≠ 0 := by
      rw [ENNReal.ofReal_ne_zero_iff]; positivity
    have h1 := (ENNReal.div_le_iff hpos ENNReal.ofReal_ne_top).1 hlt.le
    calc μ (ball E ρ) ≤ (c : ℝ≥0∞) * ENNReal.ofReal ((2 * ρ) ^ α) := h1
      _ = ENNReal.ofReal ((c : ℝ) * 2 ^ α * ρ ^ α) := by
          rw [ENNReal.ofReal_coe_nnreal.symm, ← ENNReal.ofReal_mul (by positivity),
            Real.mul_rpow (by norm_num) hρ.le, mul_assoc]
      _ ≤ _ := by gcongr; exact le_max_left _ _
  · calc μ (ball E ρ) ≤ μ univ := measure_mono (subset_univ _)
      _ = ENNReal.ofReal (μ.real univ) := (ofReal_measureReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (μ.real univ / u ^ α * ρ ^ α) := by
          apply ENNReal.ofReal_le_ofReal
          have hu' : 0 < u ^ α := by positivity
          rw [div_mul_eq_mul_div, le_div_iff₀ hu']
          gcongr
          exact measureReal_nonneg
      _ ≤ _ := by gcongr; exact le_max_right _ _

lemma lintegral_rpow_neg_Ioo {α a : ℝ} (hα : α < 1) (ha : 0 < a) :
    ∫⁻ t in Ioo 0 a, ENNReal.ofReal (t ^ (-α)) = ENNReal.ofReal (a ^ (1 - α) / (1 - α)) := by
  have hint : IntervalIntegrable (fun t : ℝ => t ^ (-α)) volume 0 a :=
    intervalIntegrable_rpow' (by linarith)
  have hint' : IntegrableOn (fun t : ℝ => t ^ (-α)) (Ioc 0 a) := hint.1
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc, ← ofReal_integral_eq_lintegral_ofReal hint'
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => Real.rpow_nonneg ht.1.le _),
    ← intervalIntegral.integral_of_le ha.le, integral_rpow (Or.inl (by linarith))]
  congr 1
  rw [show -α + 1 = 1 - α by ring, Real.zero_rpow (by linarith), sub_zero]

/-- The key estimate: `ε^{1-α} |F_μ(E + iε)| ≤ K / (1 - α)` when `μ(B(E, ρ)) ≤ K ρ^α`. -/
lemma enorm_borelTransform_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (μ : Measure ℝ)
    [IsFiniteMeasure μ] {E K : ℝ} (hK : 0 ≤ K)
    (hball : ∀ ρ, 0 < ρ → μ (ball E ρ) ≤ ENNReal.ofReal (K * ρ ^ α)) {ε : ℝ} (hε : 0 < ε) :
    ENNReal.ofReal (ε ^ (1 - α)) * ‖borelTransform μ (E + ε * I)‖ₑ ≤
      ENNReal.ofReal (K / (1 - α)) := by
  set f : ℝ → ℝ := fun x => 1 / Real.sqrt ((x - E) ^ 2 + ε ^ 2) with hf
  have hfm : Measurable f := by rw [hf]; fun_prop
  have h1 : ‖borelTransform μ (E + ε * I)‖ₑ ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
    unfold borelTransform
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    congr 1; ext x; exact enorm_inv_sub x E ε hε
  have h2 : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤
      ∫⁻ t in Ioo 0 (1 / ε), ENNReal.ofReal (K * t ^ (-α)) := by
    rw [lintegral_eq_lintegral_meas_lt μ (Eventually.of_forall fun x => by positivity)
      hfm.aemeasurable]
    have hsplit : Ioi (0 : ℝ) = Ioo 0 (1 / ε) ∪ Ici (1 / ε) := by
      ext t; simp only [mem_Ioi, mem_union, mem_Ioo, mem_Ici]
      constructor
      · intro ht; by_cases h : t < 1 / ε
        · exact Or.inl ⟨ht, h⟩
        · exact Or.inr (not_lt.1 h)
      · rintro (h | h)
        · exact h.1
        · exact lt_of_lt_of_le (by positivity) h
    rw [hsplit]
    refine (lintegral_union_le _ _ _).trans ?_
    have hzero : ∫⁻ t in Ici (1 / ε), μ {x | t < f x} = 0 := by
      apply setLIntegral_eq_zero_of_forall_eq_zero measurableSet_Ici fun t ht => ?_
      have : {x | t < f x} = ∅ := by
        ext x
        simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_lt, hf]
        refine le_trans ?_ ht
        rw [one_div_le_one_div (Real.sqrt_pos.2 (by positivity)) hε]
        calc ε = Real.sqrt (ε ^ 2) := (Real.sqrt_sq hε.le).symm
          _ ≤ _ := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (x - E)])
      rw [this, measure_empty]
    rw [hzero, add_zero]
    apply setLIntegral_mono (by fun_prop)
    intro t ht
    rw [show {x | t < f x} = ball E (Real.sqrt ((1 / t) ^ 2 - ε ^ 2)) from
      inv_norm_superlevel_eq_ball hε ht.1 E]
    have hρpos : 0 < Real.sqrt ((1 / t) ^ 2 - ε ^ 2) := by
      apply Real.sqrt_pos.2
      have : ε < 1 / t := by rw [lt_one_div hε ht.1]; exact ht.2
      nlinarith
    refine (hball _ hρpos).trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul_of_nonneg_left _ hK
    have hρle : Real.sqrt ((1 / t) ^ 2 - ε ^ 2) ≤ 1 / t := by
      rw [Real.sqrt_le_left (by have := ht.1; positivity)]
      nlinarith
    calc Real.sqrt ((1 / t) ^ 2 - ε ^ 2) ^ α ≤ (1 / t) ^ α :=
          Real.rpow_le_rpow hρpos.le hρle hα0.le
      _ = t ^ (-α) := by rw [one_div, Real.inv_rpow ht.1.le, Real.rpow_neg ht.1.le]
  have h3 : ∫⁻ t in Ioo 0 (1 / ε), ENNReal.ofReal (K * t ^ (-α)) =
      ENNReal.ofReal K * ENNReal.ofReal ((1 / ε) ^ (1 - α) / (1 - α)) := by
    simp_rw [ENNReal.ofReal_mul hK]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_rpow_neg_Ioo hα1 (by positivity)]
  calc ENNReal.ofReal (ε ^ (1 - α)) * ‖borelTransform μ (E + ε * I)‖ₑ
      ≤ ENNReal.ofReal (ε ^ (1 - α)) *
          (ENNReal.ofReal K * ENNReal.ofReal ((1 / ε) ^ (1 - α) / (1 - α))) := by
        rw [← h3]; gcongr; exact h1.trans h2
    _ = ENNReal.ofReal (K / (1 - α)) := by
        rw [← ENNReal.ofReal_mul hK, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [one_div, Real.inv_rpow hε.le]
        have : 0 < ε ^ (1 - α) := by positivity
        field_simp

/-- For `0 < α < 1`, finiteness of `D^α_μ(E)` implies finiteness of `R^α_μ(E)`. -/
theorem alphaR_lt_top_of_upperAlphaDeriv_lt_top {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (μ : Measure ℝ) [IsFiniteMeasure μ] {E : ℝ} (h : upperAlphaDeriv α μ E < ∞) :
    alphaR α μ E < ∞ := by
  obtain ⟨K, hK, hball⟩ := exists_ball_le_of_upperAlphaDeriv_lt_top hα0 μ h
  refine lt_of_le_of_lt ?_ (ENNReal.ofReal_lt_top (r := K / (1 - α)))
  refine limsup_le_of_le ?_ ?_
  · isBoundedDefault
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact enorm_borelTransform_le hα0 hα1 μ hK hball hε

/-- Proposition 1.9.7: for `0 < α < 1` and every `E`,
`D^α_μ(E) < ∞ ⟺ Q^α_μ(E) < ∞ ⟺ R^α_μ(E) < ∞`. -/
theorem upperAlphaDeriv_lt_top_iff {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (μ : Measure ℝ)
    [IsFiniteMeasure μ] (E : ℝ) :
    (upperAlphaDeriv α μ E < ∞ ↔ alphaQ α μ E < ∞) ∧
      (alphaQ α μ E < ∞ ↔ alphaR α μ E < ∞) := by
  have hDQ : alphaQ α μ E < ∞ → upperAlphaDeriv α μ E < ∞ := by
    intro hQ
    have h := (ofReal_two_rpow_mul_upperAlphaDeriv_le α μ E).trans_lt hQ
    have h2 : ENNReal.ofReal (2 ^ (α - 1)) ≠ 0 := by
      rw [ENNReal.ofReal_ne_zero_iff]; positivity
    exact (ENNReal.mul_lt_top_iff.1 h).elim (fun h' => h'.2)
      (fun h' => (h'.elim (fun h'' => absurd h'' h2) fun h'' => h'' ▸ ENNReal.zero_lt_top))
  have hRD := alphaR_lt_top_of_upperAlphaDeriv_lt_top hα0 hα1 μ (E := E)
  have hQR := alphaQ_le_alphaR α μ E
  exact ⟨⟨fun hD => hQR.trans_lt (hRD hD), hDQ⟩,
    ⟨fun hQ => hRD (hDQ hQ), fun hR => hQR.trans_lt hR⟩⟩

end DF
