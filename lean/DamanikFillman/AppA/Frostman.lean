/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Appendix A.2: Frostman's theorem (Theorem A.2.8)   (book pp. 415–416, 418)

## Main results

* `DF.Itr` — the truncated mutual energies `∫∫ logKer N (z - w) dμ(w) dν(z)`, which are
  bilinear and symmetric (`Itr_add_left`, `Itr_add_right`, `Itr_smul_left`, `Itr_smul_right`,
  `Itr_comm`).
* `DF.exists_energy_lt_of_variation` — the first-variation argument: if a probability measure
  `ν` on `K` satisfies `∫ Φ_ρ dν < E(ρ)` (at the truncated level), then `(1 - t)ρ + tν` has
  smaller energy than `ρ` for small `t > 0`.
* `DF.IsEquilibriumMeasure.ae_logPotential_le` — `Φ_ρ ≤ E(ρ)` holds `ρ`-a.e.;
* `DF.IsEquilibriumMeasure.logPotential_le_of_mem_support` — `Φ_ρ ≤ E(ρ)` on `supp ρ`;
* `DF.IsEquilibriumMeasure.eventually_logPotential_le` — the continuity principle at points of
  `supp ρ` (`limsup Φ_ρ ≤ E(ρ)`), proved with the nearest-point estimate;
* `DF.IsEquilibriumMeasure.logPotential_le` — **Theorem A.2.8 (i)**: `Φ_ρ ≤ E(ρ)` on `ℂ`
  (maximum principle for the harmonic function `Φ_ρ` off `supp ρ`);
* `DF.capCompact_le_of_union` — a subadditivity estimate for the capacity of finite unions of
  compact sets, and `DF.capacity_iUnion_eq_zero` — countable unions of compact sets of capacity
  zero (inside a fixed bounded set) have capacity zero;
* `DF.IsEquilibriumMeasure.capacity_lt_eq_zero` — **Theorem A.2.8 (ii)**;
* `DF.frostmanStatement_holds`.
-/
import DamanikFillman.AppA.Equilibrium
import Mathlib.MeasureTheory.Measure.Support

noncomputable section

open Real Complex Metric Set Filter Topology MeasureTheory
open scoped ENNReal

namespace DF

/-! ### Truncated mutual energies -/

/-- Admissible measures: finite with finite first moment. -/
def Adm (μ : Measure ℂ) : Prop := IsFiniteMeasure μ ∧ Integrable (fun w => ‖w‖) μ

lemma adm_of_M1 {K : Set ℂ} (hK : IsCompact K) {μ : Measure ℂ} (hμ : μ ∈ M1 K) : Adm μ := by
  have := hμ.1
  exact ⟨inferInstance, integrable_norm_of_compact hK hμ.2⟩

lemma Adm.add {μ ν : Measure ℂ} (hμ : Adm μ) (hν : Adm ν) : Adm (μ + ν) := by
  have := hμ.1; have := hν.1
  exact ⟨inferInstance, hμ.2.add_measure hν.2⟩

lemma Adm.smul {μ : Measure ℂ} (hμ : Adm μ) {c : ℝ≥0∞} (hc : c ≠ ⊤) : Adm (c • μ) := by
  have := hμ.1
  exact ⟨μ.smul_finite hc, hμ.2.smul_measure hc⟩

lemma Adm.restrict {μ : Measure ℂ} (hμ : Adm μ) (s : Set ℂ) : Adm (μ.restrict s) := by
  have := hμ.1
  exact ⟨inferInstance, hμ.2.restrict⟩

/-- Truncated mutual energy `∫∫ logKer N (z - w) dμ(w) dν(z)` ("`∫ Φ_μ dν` at level `N`"). -/
def Itr (N : ℕ) (μ ν : Measure ℂ) : ℝ := ∫ z, ∫ w, logKer N (z - w) ∂μ ∂ν

lemma mutualEnergy_eq_iSup_Itr (μ ν : Measure ℂ) :
    mutualEnergy μ ν = ⨆ N : ℕ, ((Itr N μ ν : ℝ) : EReal) := rfl

lemma energy_eq_iSup_Itr (μ : Measure ℂ) : energy μ = ⨆ N : ℕ, ((Itr N μ μ : ℝ) : EReal) := rfl

lemma Itr_le_energy (μ : Measure ℂ) (N : ℕ) : ((Itr N μ μ : ℝ) : EReal) ≤ energy μ :=
  iint_logKer_le_energy μ N

lemma integrable_potTrunc_wrt {μ ν : Measure ℂ} (hμ : Adm μ) (hν : Adm ν) (N : ℕ) :
    Integrable (fun z => ∫ w, logKer N (z - w) ∂μ) ν := by
  have := hμ.1; have := hν.1
  exact (integrable_logKer_prod hμ.2 hν.2 N).integral_prod_left

lemma Itr_add_left {μ₁ μ₂ ν : Measure ℂ} (h₁ : Adm μ₁) (h₂ : Adm μ₂) (hν : Adm ν) (N : ℕ) :
    Itr N (μ₁ + μ₂) ν = Itr N μ₁ ν + Itr N μ₂ ν := by
  have := h₁.1; have := h₂.1
  unfold Itr
  rw [← integral_add (integrable_potTrunc_wrt h₁ hν N) (integrable_potTrunc_wrt h₂ hν N)]
  congr 1; funext z
  exact integral_add_measure (integrable_logKer h₁.2 N z) (integrable_logKer h₂.2 N z)

lemma Itr_add_right {μ ν₁ ν₂ : Measure ℂ} (hμ : Adm μ) (h₁ : Adm ν₁) (h₂ : Adm ν₂) (N : ℕ) :
    Itr N μ (ν₁ + ν₂) = Itr N μ ν₁ + Itr N μ ν₂ :=
  integral_add_measure (integrable_potTrunc_wrt hμ h₁ N) (integrable_potTrunc_wrt hμ h₂ N)

lemma Itr_smul_left (μ ν : Measure ℂ) (c : ℝ≥0∞) (N : ℕ) :
    Itr N (c • μ) ν = c.toReal * Itr N μ ν := by
  unfold Itr
  simp only [integral_smul_measure, smul_eq_mul, integral_const_mul]

lemma Itr_smul_right (μ ν : Measure ℂ) (c : ℝ≥0∞) (N : ℕ) :
    Itr N μ (c • ν) = c.toReal * Itr N μ ν := by
  unfold Itr
  simp only [integral_smul_measure, smul_eq_mul]

lemma Itr_comm {μ ν : Measure ℂ} (hμ : Adm μ) (hν : Adm ν) (N : ℕ) :
    Itr N μ ν = Itr N ν μ := by
  have := hμ.1; have := hν.1
  unfold Itr
  rw [integral_integral_swap (integrable_logKer_prod hμ.2 hν.2 N)]
  congr 1; funext w; congr 1; funext z
  exact logKer_sub_comm N z w

lemma Itr_mono {μ ν : Measure ℂ} (hμ : Adm μ) (hν : Adm ν) {N M : ℕ} (h : N ≤ M) :
    Itr N μ ν ≤ Itr M μ ν := by
  have := hμ.1
  exact integral_mono (integrable_potTrunc_wrt hμ hν N) (integrable_potTrunc_wrt hμ hν M)
    fun z => integral_mono (integrable_logKer hμ.2 N z) (integrable_logKer hμ.2 M z)
      fun w => logKer_mono _ h

lemma Itr_zero_left (ν : Measure ℂ) (N : ℕ) : Itr N 0 ν = 0 := by simp [Itr]

/-- A bound for the energies of a restriction (cf. the proof of Prop. A.2.2(f)). -/
lemma Itr_restrict_le {μ : Measure ℂ} (hμ : Adm μ) (s : Set ℂ) (N : ℕ) :
    Itr N (μ.restrict s) (μ.restrict s) ≤
      Itr N μ μ + ∫ z, ∫ w, (‖z‖ + ‖w‖) ∂μ ∂μ := by
  have := hμ.1
  have hs := (hμ.restrict s).2
  unfold Itr
  rw [iint_logKer_eq hs hs N, iint_logKer_eq hμ.2 hμ.2 N]
  have h1 := iint_posKer_mono hμ.2 hμ.2 (Measure.restrict_le_self (s := s))
    (Measure.restrict_le_self (s := s)) N
  have h2 := iint_normSum_nonneg (μ.restrict s) (μ.restrict s)
  linarith

/-! ### The first variation -/

lemma energy_toReal_eq {μ : Measure ℂ} (h : energy μ ≠ ⊤) :
    energy μ = ((energy μ).toReal : EReal) :=
  (EReal.coe_toReal h (energy_ne_bot μ)).symm

/-- **First variation.** Let `ρ, ν ∈ M1(K)`, with all truncated energies of `ρ` bounded by `E`,
those of `ν` bounded by `B`, and `∫ Φ_ρ dν ≤ E - γ` (at all large truncation levels), `γ > 0`.
Then some `μ ∈ M1(K)` has energy `< E`. -/
theorem exists_energy_lt_of_variation {K : Set ℂ} (hK : IsCompact K) {ρ ν : Measure ℂ}
    (hρ : ρ ∈ M1 K) (hν : ν ∈ M1 K) {E γ B : ℝ} (hγ : 0 < γ) (hE : ∀ N, Itr N ρ ρ ≤ E)
    (hB : ∀ N, Itr N ν ν ≤ B) {N₀ : ℕ} (hI : ∀ N, N₀ ≤ N → Itr N ρ ν ≤ E - γ) :
    ∃ μ ∈ M1 K, energy μ < E := by
  have hρa := adm_of_M1 hK hρ
  have hνa := adm_of_M1 hK hν
  have := hρ.1; have := hν.1
  set t : ℝ := min (1 / 2) (γ / (2 * (|B - E| + 1))) with ht
  have ht0 : 0 < t := lt_min (by norm_num) (by positivity)
  have ht1 : t ≤ 1 / 2 := min_le_left _ _
  have ht2 : t * |B - E| < γ := by
    have h1 : t ≤ γ / (2 * (|B - E| + 1)) := min_le_right _ _
    have h2 : t * (|B - E| + 1) ≤ γ / 2 := by
      calc t * (|B - E| + 1) ≤ γ / (2 * (|B - E| + 1)) * (|B - E| + 1) := by gcongr
        _ = γ / 2 := by field_simp
    nlinarith [abs_nonneg (B - E)]
  set a : ℝ≥0∞ := ENNReal.ofReal (1 - t)
  set b : ℝ≥0∞ := ENNReal.ofReal t
  have ha : a.toReal = 1 - t := ENNReal.toReal_ofReal (by linarith)
  have hb : b.toReal = t := ENNReal.toReal_ofReal ht0.le
  set μ := a • ρ + b • ν with hμdef
  have hμM : μ ∈ M1 K := by
    refine ⟨⟨?_⟩, ?_⟩
    · simp only [hμdef, Measure.add_apply, Measure.smul_apply, measure_univ, smul_eq_mul,
        mul_one, a, b]
      rw [← ENNReal.ofReal_add (by linarith) ht0.le]; simp
    · simp [hμdef, hρ.2, hν.2]
  refine ⟨μ, hμM, ?_⟩
  have haρ : Adm (a • ρ) := hρa.smul ENNReal.ofReal_ne_top
  have hbν : Adm (b • ν) := hνa.smul ENNReal.ofReal_ne_top
  have hexp : ∀ N, Itr N μ μ = (1 - t) ^ 2 * Itr N ρ ρ + 2 * t * (1 - t) * Itr N ρ ν +
      t ^ 2 * Itr N ν ν := by
    intro N
    rw [hμdef, Itr_add_left haρ hbν (haρ.add hbν), Itr_add_right haρ haρ hbν,
      Itr_add_right hbν haρ hbν, Itr_smul_left, Itr_smul_left, Itr_smul_left, Itr_smul_left,
      Itr_smul_right, Itr_smul_right, Itr_smul_right, Itr_smul_right, ha, hb,
      Itr_comm hνa hρa N]
    ring
  set δ : ℝ := 2 * t * (1 - t) * γ - t ^ 2 * (B - E) with hδ
  have hδpos : 0 < δ := by
    have h1 : t ^ 2 * (B - E) ≤ t ^ 2 * |B - E| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
    have h2 : t ^ 2 * |B - E| < t * γ := by
      have := mul_lt_mul_of_pos_left ht2 ht0; nlinarith
    have h3 : t * γ ≤ 2 * t * (1 - t) * γ := by
      nlinarith [mul_nonneg (mul_nonneg ht0.le hγ.le) (by linarith : (0:ℝ) ≤ 1 - 2 * t)]
    linarith
  have hbound : ∀ N, N₀ ≤ N → Itr N μ μ ≤ E - δ := by
    intro N hN
    rw [hexp]
    have h1 := hE N; have h2 := hI N hN; have h3 := hB N
    have c1 : 0 ≤ (1 - t) ^ 2 := by positivity
    have c2 : 0 ≤ 2 * t * (1 - t) := by nlinarith
    have c3 : 0 ≤ t ^ 2 := by positivity
    calc (1 - t) ^ 2 * Itr N ρ ρ + 2 * t * (1 - t) * Itr N ρ ν + t ^ 2 * Itr N ν ν
        ≤ (1 - t) ^ 2 * E + 2 * t * (1 - t) * (E - γ) + t ^ 2 * B := by gcongr
      _ = E - δ := by rw [hδ]; ring
  have hμa : Adm μ := haρ.add hbν
  have hle : energy μ ≤ ((E - δ : ℝ) : EReal) := by
    refine iSup_le fun N => ?_
    rw [EReal.coe_le_coe_iff]
    exact (Itr_mono hμa hμa (le_max_left N N₀)).trans (hbound _ (le_max_right _ _))
  exact lt_of_le_of_lt hle (EReal.coe_lt_coe_iff.2 (by linarith))

/-! ### `Φ_ρ ≤ E(ρ)` almost everywhere and on the support -/

section Variational

variable {K : Set ℂ} {ρ : Measure ℂ}

/-- The truncated potential of `ρ`. -/
abbrev potT (ρ : Measure ℂ) (N : ℕ) (z : ℂ) : ℝ := ∫ w, logKer N (z - w) ∂ρ

lemma logPotential_eq_iSup_potT (ρ : Measure ℂ) (z : ℂ) :
    logPotential ρ z = ⨆ N : ℕ, ((potT ρ N z : ℝ) : EReal) := rfl

lemma IsEquilibriumMeasure.energy_eq_coe (hcap : capCompact K ≠ 0)
    (h : IsEquilibriumMeasure K ρ) :
    energy ρ = (((energy ρ).toReal : ℝ) : EReal) :=
  energy_toReal_eq (h.energy_ne_top hcap)

lemma IsEquilibriumMeasure.Itr_le (hcap : capCompact K ≠ 0) (h : IsEquilibriumMeasure K ρ)
    (N : ℕ) : Itr N ρ ρ ≤ (energy ρ).toReal := by
  have := Itr_le_energy ρ N
  rwa [h.energy_eq_coe hcap, EReal.coe_le_coe_iff] at this

/-- The variational inequality: `ρ{Φ_ρ^N > E(ρ) + δ} = 0` for every truncation level `N`. -/
theorem IsEquilibriumMeasure.measure_potT_gt (hK : IsCompact K) (hcap : capCompact K ≠ 0)
    (h : IsEquilibriumMeasure K ρ) (N₀ : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ρ {z | (energy ρ).toReal + δ < potT ρ N₀ z} = 0 := by
  set E := (energy ρ).toReal with hEdef
  have hρa := adm_of_M1 hK h.1
  have := h.1.1
  by_contra hA0
  set A := {z | E + δ < potT ρ N₀ z} with hAdef
  have hAm : MeasurableSet A :=
    (isOpen_lt continuous_const (continuous_potTrunc hρa.2 N₀)).measurableSet
  set a := ρ.real A with hadef
  have ha0 : 0 < a := ENNReal.toReal_pos hA0 (measure_ne_top _ _)
  have hab : a + ρ.real Aᶜ = 1 := by
    rw [hadef, measureReal_add_measureReal_compl hAm, probReal_univ]
  have hE : ∀ N, Itr N ρ ρ ≤ E := h.Itr_le hcap
  have hTN : ∀ N, N₀ ≤ N → ∀ z ∈ A, E + δ < potT ρ N z := fun N hN z hz =>
    lt_of_lt_of_le hz (potTrunc_mono hρa.2 z hN)
  have hIA : ∀ N, N₀ ≤ N → (E + δ) * a ≤ Itr N ρ (ρ.restrict A) := by
    intro N hN
    exact setIntegral_ge_of_const_le_real hAm (measure_ne_top _ _)
      (fun z hz => (hTN N hN z hz).le) (integrable_potTrunc_wrt hρa hρa N).integrableOn
  have hsplit : ∀ N, Itr N ρ ρ = Itr N ρ (ρ.restrict A) + Itr N ρ (ρ.restrict Aᶜ) := by
    intro N
    have := Itr_add_right hρa (hρa.restrict A) (hρa.restrict Aᶜ) N
    rwa [Measure.restrict_add_restrict_compl hAm] at this
  set b := ρ.real Aᶜ with hbdef
  have hb0 : 0 < b := by
    by_contra hb
    have hb' : b = 0 := le_antisymm (not_lt.1 hb) measureReal_nonneg
    have hnull : ρ Aᶜ = 0 := by
      rwa [hbdef, measureReal_eq_zero_iff] at hb'
    have h1 : Itr N₀ ρ (ρ.restrict Aᶜ) = 0 := by
      rw [Measure.restrict_eq_zero.2 hnull]; simp [Itr]
    have h2 := hIA N₀ le_rfl
    have h3 := hsplit N₀
    have h4 := hE N₀
    have ha1 : a = 1 := by linarith
    rw [ha1] at h2
    linarith
  have hAc0 : ρ Aᶜ ≠ 0 := fun h0 => by
    have : b = 0 := by rw [hbdef, measureReal_def, h0, ENNReal.toReal_zero]
    linarith
  set c : ℝ≥0∞ := (ρ Aᶜ)⁻¹ with hc
  have hctop : c ≠ ⊤ := ENNReal.inv_ne_top.2 hAc0
  have hcR : c.toReal = b⁻¹ := by rw [hc, ENNReal.toReal_inv]; rfl
  set ν := c • ρ.restrict Aᶜ with hνdef
  have hνM : ν ∈ M1 K := by
    refine ⟨⟨?_⟩, ?_⟩
    · simp only [hνdef, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul, hc]
      exact ENNReal.inv_mul_cancel hAc0 (measure_ne_top _ _)
    · simp only [hνdef, Measure.smul_apply, smul_eq_mul]
      rw [Measure.restrict_apply hK.isClosed.measurableSet.compl,
        measure_mono_null inter_subset_left h.1.2, mul_zero]
  set C := ∫ z, ∫ w, (‖z‖ + ‖w‖) ∂ρ ∂ρ
  have hB : ∀ N, Itr N ν ν ≤ b⁻¹ * (b⁻¹ * (E + C)) := by
    intro N
    rw [hνdef, Itr_smul_left, Itr_smul_right, hcR]
    have := Itr_restrict_le hρa Aᶜ N
    have := hE N
    have hb1 : 0 ≤ b⁻¹ := inv_nonneg.2 hb0.le
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by linarith) hb1) hb1
  have hI : ∀ N, N₀ ≤ N → Itr N ρ ν ≤ E - δ * a / b := by
    intro N hN
    rw [hνdef, Itr_smul_right, hcR]
    have h1 := hsplit N
    have h2 := hIA N hN
    have h3 := hE N
    have hb' : b = 1 - a := by linarith
    have key : Itr N ρ (ρ.restrict Aᶜ) ≤ E * b - δ * a := by
      rw [hb']
      have e1 : (E + δ) * a = E * a + δ * a := by ring
      have e2 : E * (1 - a) - δ * a = E - E * a - δ * a := by ring
      rw [e1] at h2; rw [e2]; linarith
    rw [show E - δ * a / b = b⁻¹ * (E * b - δ * a) by field_simp]
    exact mul_le_mul_of_nonneg_left key (inv_nonneg.2 hb0.le)
  obtain ⟨μ, hμ, hlt⟩ := exists_energy_lt_of_variation hK h.1 hνM (by positivity) hE hB hI
  have := h.2 μ hμ
  rw [h.energy_eq_coe hcap] at this
  exact absurd (lt_of_le_of_lt this hlt) (lt_irrefl _)

/-- `Φ_ρ ≤ E(ρ)` holds `ρ`-almost everywhere (proof of Theorem A.2.8). -/
theorem IsEquilibriumMeasure.ae_logPotential_le (hK : IsCompact K) (hcap : capCompact K ≠ 0)
    (h : IsEquilibriumMeasure K ρ) : ∀ᵐ z ∂ρ, logPotential ρ z ≤ energy ρ := by
  rw [ae_iff]
  refine measure_mono_null (t := ⋃ N : ℕ, ⋃ m : ℕ,
    {z | (energy ρ).toReal + 1 / ((m : ℝ) + 1) < potT ρ N z}) ?_ ?_
  · intro z hz
    simp only [mem_ofPred_eq, not_le] at hz
    rw [h.energy_eq_coe hcap, logPotential_eq_iSup_potT, lt_iSup_iff] at hz
    obtain ⟨N, hN⟩ := hz
    rw [EReal.coe_lt_coe_iff] at hN
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.2 hN)
    simp only [mem_iUnion, mem_ofPred_eq]
    exact ⟨N, m, by linarith⟩
  · exact measure_iUnion_null fun N => measure_iUnion_null fun m =>
      h.measure_potT_gt hK hcap N (by positivity)

/-- `Φ_ρ ≤ E(ρ)` on the support of `ρ` (lower semicontinuity). -/
theorem IsEquilibriumMeasure.logPotential_le_of_mem_support (hK : IsCompact K)
    (hcap : capCompact K ≠ 0) (h : IsEquilibriumMeasure K ρ) {z : ℂ} (hz : z ∈ ρ.support) :
    logPotential ρ z ≤ energy ρ := by
  have hρa := adm_of_M1 hK h.1
  have := hρa.1
  by_contra hlt
  push Not at hlt
  have hev := lowerSemicontinuous_logPotential hρa.2 z _ hlt
  have hpos := (Measure.mem_support_iff_forall z).1 hz _ hev
  have hnull : ρ {y | energy ρ < logPotential ρ y} = 0 := by
    have := h.ae_logPotential_le hK hcap
    rw [ae_iff] at this
    simpa [not_le] using this
  exact absurd hnull (pos_iff_ne_zero.1 hpos)

end Variational

end DF
