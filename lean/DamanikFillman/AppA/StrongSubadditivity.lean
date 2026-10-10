/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Appendix A.2: strong subadditivity of the logarithmic capacity

## Main results

* `DF.integral_toReal_logPotential_comm` — `∫ Φ_μ dν = ∫ Φ_ν dμ` for measures with bounded
  potentials carried by a compact set.
* `DF.capCompact_union_mul_inter_le` — **strong subadditivity**: for compact sets in a disc of
  radius `1/4`, `Cap(K₁ ∪ K₂) Cap(K₁ ∩ K₂) ≤ Cap(K₁) Cap(K₂)`, i.e. the Robin constants
  `V = -log Cap` satisfy `V(K₁) + V(K₂) ≤ V(K₁ ∪ K₂) + V(K₁ ∩ K₂)`.
* `DF.capacity_union_mul_inter_le` — the same inequality for open sets.

## Proof

Let `ρ₁, ρ₂, ρ_∪, ρ_∩` be the equilibrium measures, with Robin constants `V₁, V₂, V_∪, V_∩`.
Since `Φ_{ρ_∪} = V_∪` quasi-everywhere on `K₁ ∪ K₂ ⊇ K₁ ∩ K₂`,
`V_∪ = ∫ Φ_{ρ_∪} dρ_∩ = ∫ Φ_{ρ_∩} dρ_∪`.  By the domination principle
(`DF.toReal_logPotential_le_of_subset`), `Φ_{ρ_∩} ≤ Φ_{ρ_i} + V_∩ - V_i` quasi-everywhere, and
`Φ_{ρ_j} = V_j` quasi-everywhere on `K_j`; hence `Φ_{ρ_∩} ≤ Φ_{ρ₁} + Φ_{ρ₂} + V_∩ - V₁ - V₂`
`ρ_∪`-a.e.  Integrating against `ρ_∪` and using `∫ Φ_{ρ_j} dρ_∪ = ∫ Φ_{ρ_∪} dρ_j ≤ V_∪` gives
`V_∪ ≤ 2 V_∪ + V_∩ - V₁ - V₂`.
-/
import DamanikFillman.AppA.Domination

noncomputable section

open Real Complex Metric Set Filter Topology MeasureTheory
open scoped ENNReal

namespace DF

/-! ### Integrals of potentials -/

/-- Potentials bounded above are integrable against finite measures carried by a compact
set. -/
lemma integrable_toReal_logPotential {μ ν : Measure ℂ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {K : Set ℂ} (hK : IsCompact K) (hμK : μ Kᶜ = 0) (hνK : ν Kᶜ = 0) {A : ℝ}
    (hA : ∀ z, logPotential μ z ≤ A) : Integrable (fun z => (logPotential μ z).toReal) ν := by
  have hμ := integrable_norm_of_compact hK hμK
  have h0 : Integrable (fun z => potT μ 0 z) ν :=
    integrable_of_continuous_carrier hK hνK (continuous_potTrunc hμ 0)
  have hg : Integrable (fun z => |potT μ 0 z| + |A|) ν := h0.abs.add (integrable_const |A|)
  refine hg.mono'
    (measurable_ereal_toReal.comp (lowerSemicontinuous_logPotential hμ).measurable).aestronglyMeasurable
    (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_le]
  have hle : (logPotential μ z).toReal ≤ A := ereal_toReal_le (hA z) (logPotential_ne_bot μ z)
  have hge : potT μ 0 z ≤ (logPotential μ z).toReal :=
    ereal_le_toReal (le_iSup (fun N : ℕ => ((potT μ N z : ℝ) : EReal)) 0)
      (ne_top_of_le_ne_top (EReal.coe_ne_top A) (hA z))
  have h1 := neg_abs_le (potT μ 0 z)
  have h2 := le_abs_self A
  have h3 := abs_nonneg (potT μ 0 z)
  constructor <;> linarith

/-- `∫ Φ_μ dν` is the limit of the truncated mutual energies. -/
lemma tendsto_Itr_integral {μ ν : Measure ℂ} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {K : Set ℂ} (hK : IsCompact K) (hμK : μ Kᶜ = 0) (hνK : ν Kᶜ = 0) {A : ℝ}
    (hA : ∀ z, logPotential μ z ≤ A) :
    Tendsto (fun N => Itr N μ ν) atTop (𝓝 (∫ z, (logPotential μ z).toReal ∂ν)) := by
  have hμ := integrable_norm_of_compact hK hμK
  show Tendsto (fun N : ℕ => ∫ z, potT μ N z ∂ν) atTop _
  refine integral_tendsto_of_tendsto_of_monotone
    (fun N => integrable_of_continuous_carrier hK hνK (continuous_potTrunc hμ N))
    (integrable_toReal_logPotential hK hμK hνK hA)
    (Eventually.of_forall fun z => potTrunc_mono hμ z) (Eventually.of_forall fun z => ?_)
  have h := tendsto_potT hμ z
  rw [← EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top A) (hA z))
    (logPotential_ne_bot μ z)] at h
  exact EReal.tendsto_coe.1 h

/-- Symmetry of the mutual energy, for measures with bounded potentials. -/
lemma integral_toReal_logPotential_comm {μ ν : Measure ℂ} [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {K : Set ℂ} (hK : IsCompact K) (hμK : μ Kᶜ = 0) (hνK : ν Kᶜ = 0)
    {A B : ℝ} (hA : ∀ z, logPotential μ z ≤ A) (hB : ∀ z, logPotential ν z ≤ B) :
    ∫ z, (logPotential μ z).toReal ∂ν = ∫ z, (logPotential ν z).toReal ∂μ := by
  have hμ : Adm μ := ⟨inferInstance, integrable_norm_of_compact hK hμK⟩
  have hν : Adm ν := ⟨inferInstance, integrable_norm_of_compact hK hνK⟩
  exact tendsto_nhds_unique (tendsto_Itr_integral hK hμK hνK hA)
    ((tendsto_Itr_integral hK hνK hμK hB).congr fun N => Itr_comm hν hμ N)

/-- Measures of finite energy do not charge the exceptional set of an equilibrium measure. -/
lemma IsEquilibriumMeasure.ae_notMem_exceptional {K : Set ℂ} (hK : IsCompact K)
    (hcap : capCompact K ≠ 0) {ρ : Measure ℂ} (hρ : IsEquilibriumMeasure K ρ) {ν : Measure ℂ}
    [IsFiniteMeasure ν] (hνa : Integrable (fun w => ‖w‖) ν) (hνE : energy ν ≠ ⊤) :
    ∀ᵐ z ∂ν, z ∉ {w ∈ K | logPotential ρ w < energy ρ} := by
  haveI := hρ.1.1
  have hρa := adm_of_M1 hK hρ.1
  have hEm : MeasurableSet {w ∈ K | logPotential ρ w < energy ρ} :=
    hK.measurableSet.inter ((lowerSemicontinuous_logPotential hρa.2).measurable measurableSet_Iio)
  exact measure_eq_zero_iff_ae_notMem.1
    (measure_eq_zero_of_capacity_eq_zero hνa hνE hEm (hρ.capacity_lt_eq_zero hK hcap))

/-- `∫ Φ_ρ dν = E(ρ)` for probability measures `ν` of finite energy carried by `K`. -/
lemma integral_toReal_logPotential_eq_energy {K : Set ℂ} (hK : IsCompact K)
    (hcap : capCompact K ≠ 0) {ρ : Measure ℂ} (hρ : IsEquilibriumMeasure K ρ) {ν : Measure ℂ}
    [IsProbabilityMeasure ν] (hνa : Integrable (fun w => ‖w‖) ν) (hνE : energy ν ≠ ⊤)
    (hνK : ν Kᶜ = 0) :
    ∫ z, (logPotential ρ z).toReal ∂ν = (energy ρ).toReal := by
  have hae : ∀ᵐ z ∂ν, (logPotential ρ z).toReal = (energy ρ).toReal := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hνK,
      hρ.ae_notMem_exceptional hK hcap hνa hνE] with z hzK hzE
    have hzK' : z ∈ K := by simpa using hzK
    have h1 : ¬ logPotential ρ z < energy ρ := fun h => hzE ⟨hzK', h⟩
    push_neg at h1
    rw [le_antisymm (hρ.logPotential_le_energy hK hcap z) h1]
  rw [integral_congr_ae hae]
  simp

/-! ### Strong subadditivity -/

/-- **Strong subadditivity** of the logarithmic capacity on compact sets of diameter `≤ 1/2`:
`Cap(K₁ ∪ K₂) Cap(K₁ ∩ K₂) ≤ Cap(K₁) Cap(K₂)`. -/
theorem capCompact_union_mul_inter_le {a : ℂ} {K₁ K₂ : Set ℂ} (h₁ : IsCompact K₁)
    (h₂ : IsCompact K₂) (h₁a : K₁ ⊆ closedBall a (1 / 4)) (h₂a : K₂ ⊆ closedBall a (1 / 4)) :
    capCompact (K₁ ∪ K₂) * capCompact (K₁ ∩ K₂) ≤ capCompact K₁ * capCompact K₂ := by
  by_cases hci : capCompact (K₁ ∩ K₂) = 0
  · rw [hci, mul_zero]; exact zero_le
  have hu : IsCompact (K₁ ∪ K₂) := h₁.union h₂
  have hi : IsCompact (K₁ ∩ K₂) := h₁.inter_right h₂.isClosed
  have hc1 : capCompact K₁ ≠ 0 := fun h =>
    hci (le_antisymm ((capCompact_mono inter_subset_left).trans h.le) zero_le)
  have hc2 : capCompact K₂ ≠ 0 := fun h =>
    hci (le_antisymm ((capCompact_mono inter_subset_right).trans h.le) zero_le)
  have hcu : capCompact (K₁ ∪ K₂) ≠ 0 := fun h =>
    hc1 (le_antisymm ((capCompact_mono subset_union_left).trans h.le) zero_le)
  obtain ⟨ρ1, hρ1⟩ := exists_isEquilibriumMeasure h₁ hc1
  obtain ⟨ρ2, hρ2⟩ := exists_isEquilibriumMeasure h₂ hc2
  obtain ⟨ρu, hρu⟩ := exists_isEquilibriumMeasure hu hcu
  obtain ⟨ρi, hρi⟩ := exists_isEquilibriumMeasure hi hci
  haveI := hρ1.1.1
  haveI := hρ2.1.1
  haveI := hρu.1.1
  haveI := hρi.1.1
  have hρ1a := adm_of_M1 h₁ hρ1.1
  have hρ2a := adm_of_M1 h₂ hρ2.1
  have hρua := adm_of_M1 hu hρu.1
  have hρia := adm_of_M1 hi hρi.1
  have hEu : energy ρu ≠ ⊤ := hρu.energy_ne_top hcu
  have hEi : energy ρi ≠ ⊤ := hρi.energy_ne_top hci
  have hE1 : energy ρ1 ≠ ⊤ := hρ1.energy_ne_top hc1
  have hE2 : energy ρ2 ≠ ⊤ := hρ2.energy_ne_top hc2
  obtain ⟨V1, hV1⟩ : ∃ V : ℝ, energy ρ1 = V := ⟨_, hρ1.energy_eq_coe hc1⟩
  obtain ⟨V2, hV2⟩ : ∃ V : ℝ, energy ρ2 = V := ⟨_, hρ2.energy_eq_coe hc2⟩
  obtain ⟨Vu, hVu⟩ : ∃ V : ℝ, energy ρu = V := ⟨_, hρu.energy_eq_coe hcu⟩
  obtain ⟨Vi, hVi⟩ : ∃ V : ℝ, energy ρi = V := ⟨_, hρi.energy_eq_coe hci⟩
  have hle1 : ∀ z, logPotential ρ1 z ≤ V1 := fun z => by
    have := hρ1.logPotential_le_energy h₁ hc1 z; rwa [hV1] at this
  have hle2 : ∀ z, logPotential ρ2 z ≤ V2 := fun z => by
    have := hρ2.logPotential_le_energy h₂ hc2 z; rwa [hV2] at this
  have hleu : ∀ z, logPotential ρu z ≤ Vu := fun z => by
    have := hρu.logPotential_le_energy hu hcu z; rwa [hVu] at this
  have hlei : ∀ z, logPotential ρi z ≤ Vi := fun z => by
    have := hρi.logPotential_le_energy hi hci z; rwa [hVi] at this
  have hρ1u : ρ1 (K₁ ∪ K₂)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 subset_union_left) hρ1.1.2
  have hρ2u : ρ2 (K₁ ∪ K₂)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 subset_union_right) hρ2.1.2
  have hρiu : ρi (K₁ ∪ K₂)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.2 (inter_subset_left.trans subset_union_left)) hρi.1.2
  have hρuu : ρu (K₁ ∪ K₂)ᶜ = 0 := hρu.1.2
  -- `V_∪ = ∫ Φ_{ρ_∪} dρ_∩ = ∫ Φ_{ρ_∩} dρ_∪`
  have e1 : ∫ z, (logPotential ρu z).toReal ∂ρi = Vu := by
    rw [integral_toReal_logPotential_eq_energy hu hcu hρu hρia.2 hEi hρiu, hVu,
      EReal.toReal_coe]
  have e2 : ∫ z, (logPotential ρi z).toReal ∂ρu = ∫ z, (logPotential ρu z).toReal ∂ρi :=
    integral_toReal_logPotential_comm hu hρiu hρuu hlei hleu
  -- `∫ Φ_{ρ_j} dρ_∪ ≤ V_∪`
  have hbound : ∀ (ρ : Measure ℂ) [IsProbabilityMeasure ρ], ρ (K₁ ∪ K₂)ᶜ = 0 →
      ∀ V : ℝ, (∀ z, logPotential ρ z ≤ V) → ∫ z, (logPotential ρ z).toReal ∂ρu ≤ Vu := by
    intro ρ _ hρK V hV
    rw [integral_toReal_logPotential_comm hu hρK hρuu hV hleu]
    calc ∫ z, (logPotential ρu z).toReal ∂ρ ≤ ∫ _z, Vu ∂ρ :=
          integral_mono (integrable_toReal_logPotential hu hρuu hρK hleu) (integrable_const _)
            fun z => ereal_toReal_le (hleu z) (logPotential_ne_bot _ _)
      _ = Vu := by simp
  have e41 := hbound ρ1 hρ1u V1 hle1
  have e42 := hbound ρ2 hρ2u V2 hle2
  -- the pointwise inequality, `ρ_∪`-a.e.
  have ae3 : ∀ᵐ z ∂ρu, (logPotential ρi z).toReal ≤
      ((logPotential ρ1 z).toReal + (logPotential ρ2 z).toReal) + (Vi - V1 - V2) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hρuu,
      hρ1.ae_notMem_exceptional h₁ hc1 hρua.2 hEu,
      hρ2.ae_notMem_exceptional h₂ hc2 hρua.2 hEu] with z hzu hz1 hz2
    have hzu' : z ∈ K₁ ∪ K₂ := by simpa using hzu
    have hd2 := toReal_logPotential_le_of_subset h₂ hi inter_subset_right h₂a hci hρ2 hρi hz2
    have hd1 := toReal_logPotential_le_of_subset h₁ hi inter_subset_left h₁a hci hρ1 hρi hz1
    rw [hVi, hV2, EReal.toReal_coe, EReal.toReal_coe] at hd2
    rw [hVi, hV1, EReal.toReal_coe, EReal.toReal_coe] at hd1
    have hup1 := ereal_toReal_le (hle1 z) (logPotential_ne_bot _ _)
    have hup2 := ereal_toReal_le (hle2 z) (logPotential_ne_bot _ _)
    rcases hzu' with hzK | hzK
    · have h : ¬ logPotential ρ1 z < energy ρ1 := fun h => hz1 ⟨hzK, h⟩
      push_neg at h
      rw [hV1] at h
      have := ereal_le_toReal h (ne_top_of_le_ne_top (EReal.coe_ne_top V1) (hle1 z))
      linarith
    · have h : ¬ logPotential ρ2 z < energy ρ2 := fun h => hz2 ⟨hzK, h⟩
      push_neg at h
      rw [hV2] at h
      have := ereal_le_toReal h (ne_top_of_le_ne_top (EReal.coe_ne_top V2) (hle2 z))
      linarith
  have hint1 := integrable_toReal_logPotential hu hρ1u hρuu hle1
  have hint2 := integrable_toReal_logPotential hu hρ2u hρuu hle2
  have hinti := integrable_toReal_logPotential hu hρiu hρuu hlei
  have hint12 : Integrable (fun z => (logPotential ρ1 z).toReal + (logPotential ρ2 z).toReal)
      ρu := hint1.add hint2
  have hmono := integral_mono_ae hinti (hint12.add (integrable_const (Vi - V1 - V2))) ae3
  rw [integral_add hint12 (integrable_const _), integral_add hint1 hint2] at hmono
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hmono
  have key : V1 + V2 ≤ Vu + Vi := by linarith
  -- conclusion
  rw [hρu.capCompact_eq, hρi.capCompact_eq, hρ1.capCompact_eq, hρ2.capCompact_eq, hV1, hV2,
    hVu, hVi, expNeg_coe, expNeg_coe, expNeg_coe, expNeg_coe,
    ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ← Real.exp_add, ← Real.exp_add]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith))

end DF
