/-
# Diophantine rotation numbers and the probability integral transform

(Paper I, `analytic_perturbations_amo.tex`: Lemma `t-lem:reducibility` — the step
"`N_*(dN) = dt` on `[0,1]`" — and the proof of Lemma `t-lem:arithmetic-reducibility` —
the Borel–Cantelli argument `|𝕋 \ Θ_α| = 0`, the removal of `{r : 4r ∈ 2αℤ + ℤ}`, and the
transfer of these Lebesgue-null exclusions to `dN`-null sets of energies via `ρ = (1 - N)/2`.)

Main results:

* `Red.ae_mem_ThetaTau`, `Red.volume_compl_ThetaSet`, `Red.volume_Icc_diff_ThetaTau`:
  almost every `r` lies in `Θ_α`;
* `Red.ThetaTau_add_int`, `Red.ThetaSet_add_int`: invariance under `r ↦ r + k`, `k ∈ ℤ`;
* `Red.volume_resonant4` : `{r | 4r ∈ 2αℤ + ℤ}` is Lebesgue-null;
* `Red.map_cdf_eq_volume` : probability integral transform `ν.map F = Leb|[0,1]`
  for a continuous CDF `F`;
* `Red.measure_rho_preimage_null`, `Red.measure_rho_notMem_ThetaSet`,
  `Red.measure_rho_resonant4` : the corresponding `dN`-null energy sets.
-/
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.Order.Round

noncomputable section

open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal

namespace Red

/-! ### Distance to the integers and the Diophantine sets -/

/-- `‖t‖_𝕋 = |t - round t|`, the distance from `t` to `ℤ`. -/
def torusDist (t : ℝ) : ℝ := |t - round t|

lemma torusDist_nonneg (t : ℝ) : 0 ≤ torusDist t := abs_nonneg _

lemma torusDist_add_int (t : ℝ) (n : ℤ) : torusDist (t + n) = torusDist t := by
  unfold torusDist; rw [round_add_intCast]; push_cast; ring_nf

lemma exists_int_of_torusDist_eq_zero {t : ℝ} (h : torusDist t = 0) : ∃ m : ℤ, t = m :=
  ⟨round t, by unfold torusDist at h; linarith [abs_eq_zero.mp h]⟩

/-- For fixed `τ`: the set of `r` with `‖2r + kα‖_𝕋 ≥ κ (1+|k|)^{-τ}` for all `k ∈ ℤ`,
for some `κ > 0`. -/
def ThetaTau (α τ : ℝ) : Set ℝ :=
  {r | ∃ κ > 0, ∀ k : ℤ, κ * (1 + |(k : ℝ)|) ^ (-τ) ≤ torusDist (2 * r + k * α)}

/-- The paper's `Θ_α = ⋃_{κ>0, τ>1} {r : ‖2r + kα‖_𝕋 ≥ κ(1+|k|)^{-τ} (k ∈ ℤ)}`
(proof of Lemma `t-lem:arithmetic-reducibility`). -/
def ThetaSet (α : ℝ) : Set ℝ := ⋃ (τ : ℝ) (_ : 1 < τ), ThetaTau α τ

lemma ThetaTau_subset_ThetaSet (α : ℝ) {τ : ℝ} (hτ : 1 < τ) : ThetaTau α τ ⊆ ThetaSet α :=
  fun _ hr => mem_iUnion₂.2 ⟨τ, hτ, hr⟩

/-- `Θ_{α,τ}` is invariant under integer translation. -/
theorem ThetaTau_add_int {α τ r : ℝ} (k : ℤ) (hr : r ∈ ThetaTau α τ) :
    r + k ∈ ThetaTau α τ := by
  obtain ⟨κ, hκ, h⟩ := hr
  refine ⟨κ, hκ, fun j => ?_⟩
  have : 2 * (r + k) + j * α = (2 * r + j * α) + ((2 * k : ℤ) : ℝ) := by push_cast; ring
  rw [this, torusDist_add_int]; exact h j

/-- `Θ_α` is invariant under integer translation. -/
theorem ThetaSet_add_int {α r : ℝ} (k : ℤ) (hr : r ∈ ThetaSet α) : r + k ∈ ThetaSet α := by
  obtain ⟨τ, hτ, h⟩ := mem_iUnion₂.1 hr
  exact mem_iUnion₂.2 ⟨τ, hτ, ThetaTau_add_int k h⟩

/-! ### Borel–Cantelli -/

/-- Measure bound for one resonance strip, localized to `[-N, N]`. -/
lemma volume_strip_le (c ε : ℝ) (hε1 : ε ≤ 1) (N : ℕ) :
    volume ({r : ℝ | torusDist (2 * r + c) < ε} ∩ Icc (-(N : ℝ)) N) ≤
      ((4 * N + 3 : ℕ) : ℝ≥0∞) * ENNReal.ofReal ε := by
  set T : Finset ℤ := Finset.Icc (⌊c⌋ - 2 * N - 1) (⌊c⌋ + 2 * N + 1)
  have hsub : {r : ℝ | torusDist (2 * r + c) < ε} ∩ Icc (-(N : ℝ)) N ⊆
      ⋃ m ∈ T, Ioo ((m - c - ε) / 2) ((m - c + ε) / 2) := by
    rintro r ⟨hr, hr1, hr2⟩
    simp only [mem_ofPred_eq, torusDist, abs_lt] at hr
    have hfl := Int.floor_le c
    have hfl' := Int.lt_floor_add_one c
    refine mem_iUnion₂.2 ⟨round (2 * r + c), ?_, ?_, ?_⟩
    · simp only [T, Finset.mem_Icc]
      constructor
      · have : ((⌊c⌋ - 2 * N - 1 : ℤ) : ℝ) < round (2 * r + c) := by push_cast; linarith
        exact (Int.cast_lt.mp this).le
      · have : ((round (2 * r + c) : ℤ) : ℝ) < ((⌊c⌋ + 2 * N + 2 : ℤ) : ℝ) := by
          push_cast; linarith
        have := Int.cast_lt.mp this; omega
    · linarith
    · linarith
  calc _ ≤ volume (⋃ m ∈ T, Ioo ((m - c - ε) / 2) ((m - c + ε) / 2)) := measure_mono hsub
    _ ≤ ∑ m ∈ T, volume (Ioo ((m - c - ε) / 2) ((m - c + ε) / 2)) :=
        measure_biUnion_finset_le _ _
    _ = ∑ _m ∈ T, ENNReal.ofReal ε := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Real.volume_Ioo]; congr 1; ring
    _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul]
        congr 2
        simp only [T, Int.card_Icc]; omega

lemma eps_pos (τ : ℝ) (k : ℤ) : 0 < (1 + |(k : ℝ)|) ^ (-τ) :=
  Real.rpow_pos_of_pos (by positivity) _

lemma eps_le_one {τ : ℝ} (hτ : 0 ≤ τ) (k : ℤ) : (1 + |(k : ℝ)|) ^ (-τ) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by linarith [abs_nonneg (k : ℝ)]) (by linarith)

lemma summable_eps {τ : ℝ} (hτ : 1 < τ) : Summable fun k : ℤ => (1 + |(k : ℝ)|) ^ (-τ) := by
  have h1 := Real.summable_abs_int_rpow hτ
  have h2 : Summable fun k : ℤ => if k = 0 then (1 : ℝ) else 0 :=
    summable_of_ne_finset_zero (s := {0}) (fun k hk => by simp_all)
  refine Summable.of_nonneg_of_le (fun k => (eps_pos τ k).le) (fun k => ?_) (h1.add h2)
  show (1 + |(k : ℝ)|) ^ (-τ) ≤ |(k : ℝ)| ^ (-τ) + (if k = 0 then 1 else 0)
  by_cases hk : k = 0
  · subst hk
    have h0 : (1 + |((0 : ℤ) : ℝ)|) ^ (-τ) = 1 := by simp
    rw [h0, ite_eq_left rfl]
    linarith [Real.rpow_nonneg (abs_nonneg ((0 : ℤ) : ℝ)) (-τ)]
  · rw [ite_eq_right hk, add_zero]
    have hpos : 0 < |(k : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hk)
    exact Real.rpow_le_rpow_of_nonpos hpos (by linarith) (by linarith)

lemma exists_pos_le_finset (T : Finset ℤ) (f : ℤ → ℝ) (hf : ∀ k ∈ T, 0 < f k) :
    ∃ κ > 0, κ ≤ 1 ∧ ∀ k ∈ T, κ ≤ f k := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, one_pos, le_rfl, by simp⟩
  | insert a s _ ih =>
    obtain ⟨κ, hκ, hκ1, h⟩ := ih (fun k hk => hf k (Finset.mem_insert_of_mem hk))
    refine ⟨min κ (f a), lt_min hκ (hf a (Finset.mem_insert_self a s)),
      (min_le_left _ _).trans hκ1, fun k hk => ?_⟩
    rcases Finset.mem_insert.1 hk with rfl | hk
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (h k hk)

/-- **Borel–Cantelli** (proof of Lemma `t-lem:arithmetic-reducibility`): for `τ > 1`, almost
every `r ∈ ℝ` satisfies `inf_k (1+|k|)^τ ‖2r + kα‖_𝕋 > 0`, i.e. lies in `Θ_{α,τ}`. -/
theorem ae_mem_ThetaTau (α : ℝ) {τ : ℝ} (hτ : 1 < τ) : ∀ᵐ r : ℝ, r ∈ ThetaTau α τ := by
  set ε : ℤ → ℝ := fun k => (1 + |(k : ℝ)|) ^ (-τ) with hε
  set s : ℕ → ℤ → Set ℝ := fun N k =>
    {r : ℝ | torusDist (2 * r + k * α) < ε k} ∩ Icc (-(N : ℝ)) N
  have hN : ∀ N : ℕ, ∀ᵐ r : ℝ, ∀ᶠ k in cofinite, r ∉ s N k := by
    intro N
    have hsum : ∑' k, volume (s N k) ≠ ∞ := by
      refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum fun k =>
        volume_strip_le (k * α) (ε k) (eps_le_one (by linarith) k) N)
      rw [ENNReal.tsum_mul_left, ← ENNReal.ofReal_tsum_of_nonneg (fun k => (eps_pos τ k).le)
        (summable_eps hτ)]
      exact ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
    have h0 := measure_limsup_cofinite_eq_zero hsum
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with r hr
    rw [mem_limsup_iff_frequently_mem, not_frequently] at hr
    exact hr
  have hc : ∀ᵐ r : ℝ, ∀ k : ℤ, torusDist (2 * r + k * α) ≠ 0 := by
    rw [ae_all_iff]; intro k
    rw [ae_iff]; push Not
    refine measure_mono_null (t := range fun m : ℤ => ((m : ℝ) - k * α) / 2) ?_
      ((countable_range _).measure_zero _)
    intro r hr
    obtain ⟨m, hm⟩ := exists_int_of_torusDist_eq_zero hr
    exact ⟨m, by simp only; linarith⟩
  filter_upwards [ae_all_iff.2 hN, hc] with r hr hr0
  set N := ⌈|r|⌉₊
  have hrN : r ∈ Icc (-(N : ℝ)) N := by
    have := Nat.le_ceil |r|
    exact ⟨by linarith [neg_abs_le r], by linarith [le_abs_self r]⟩
  have hfin := Filter.eventually_cofinite.1 (hr N)
  obtain ⟨κ, hκ, hκ1, hκT⟩ := exists_pos_le_finset hfin.toFinset
    (fun k => torusDist (2 * r + k * α))
    (fun k _ => lt_of_le_of_ne (torusDist_nonneg _) (hr0 k).symm)
  refine ⟨κ, hκ, fun k => ?_⟩
  have hε1 : ε k ≤ 1 := eps_le_one (by linarith) k
  have hεpos : 0 < ε k := eps_pos τ k
  by_cases hk : k ∈ hfin.toFinset
  · calc κ * ε k ≤ κ * 1 := by gcongr
      _ ≤ _ := by rw [mul_one]; exact hκT k hk
  · rw [Set.Finite.mem_toFinset, mem_ofPred_eq, not_not] at hk
    have : ¬ torusDist (2 * r + k * α) < ε k := fun h => hk ⟨h, hrN⟩
    push Not at this
    calc κ * ε k ≤ 1 * ε k := by gcongr
      _ ≤ _ := by rw [one_mul]; exact this

/-- `|ℝ \ Θ_{α,τ}| = 0` for `τ > 1`. -/
theorem volume_compl_ThetaTau (α : ℝ) {τ : ℝ} (hτ : 1 < τ) : volume (ThetaTau α τ)ᶜ = 0 :=
  ae_iff.1 (ae_mem_ThetaTau α hτ)

/-- `|[0,1] \ Θ_{α,τ}| = 0` for `τ > 1`. -/
theorem volume_Icc_diff_ThetaTau (α : ℝ) {τ : ℝ} (hτ : 1 < τ) :
    volume (Icc (0 : ℝ) 1 \ ThetaTau α τ) = 0 :=
  measure_mono_null (fun _ h => h.2) (volume_compl_ThetaTau α hτ)

/-- `|ℝ \ Θ_α| = 0` (proof of Lemma `t-lem:arithmetic-reducibility`). -/
theorem volume_compl_ThetaSet (α : ℝ) : volume (ThetaSet α)ᶜ = 0 :=
  measure_mono_null (compl_subset_compl.2 (ThetaTau_subset_ThetaSet α one_lt_two))
    (volume_compl_ThetaTau α one_lt_two)

/-- Almost every `r` lies in `Θ_α`. -/
theorem ae_mem_ThetaSet (α : ℝ) : ∀ᵐ r : ℝ, r ∈ ThetaSet α :=
  ae_iff.2 (volume_compl_ThetaSet α)

/-- The second resonance set `{r : 4r ∈ 2αℤ + ℤ}` is countable. -/
theorem countable_resonant4 (α : ℝ) :
    {r : ℝ | ∃ j m : ℤ, 4 * r = 2 * α * j + m}.Countable := by
  refine (countable_range fun p : ℤ × ℤ => (2 * α * p.1 + p.2) / 4).mono ?_
  rintro r ⟨j, m, h⟩
  exact ⟨(j, m), by simp only; linarith⟩

/-- The second resonance set `{r : 4r ∈ 2αℤ + ℤ}` is Lebesgue-null. -/
theorem volume_resonant4 (α : ℝ) : volume {r : ℝ | ∃ j m : ℤ, 4 * r = 2 * α * j + m} = 0 :=
  (countable_resonant4 α).measure_zero _

/-! ### Probability integral transform -/

lemma toReal_Iic_eq_cdf (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    (fun t => (ν (Iic t)).toReal) = cdf ν := by
  funext t; rw [cdf_eq_real]; rfl

/-- For `0 ≤ c < 1` and continuous CDF `F`, `ν {F ≤ c} = c`. -/
lemma measure_cdf_le (ν : Measure ℝ) [IsProbabilityMeasure ν] (hF : Continuous (cdf ν))
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) : ν (cdf ν ⁻¹' Iic c) = ENNReal.ofReal c := by
  set S := cdf ν ⁻¹' Iic c
  rcases S.eq_empty_or_nonempty with hS | hS
  · rcases hc0.eq_or_lt with rfl | hpos
    · rw [hS]; simp
    · exfalso
      obtain ⟨t, ht⟩ := ((tendsto_order.1 (tendsto_cdf_atBot ν)).2 c hpos).exists
      have : t ∈ S := (show cdf ν t ≤ c from ht.le)
      rw [hS] at this; exact this
  · obtain ⟨t1, ht1⟩ := eventually_atTop.1 ((tendsto_order.1 (tendsto_cdf_atTop ν)).1 c hc1)
    have hbdd : BddAbove S := ⟨t1, fun t ht => by
      by_contra h; push Not at h
      exact absurd (ht1 t h.le) (not_lt.2 ht)⟩
    have hclosed : IsClosed S := isClosed_le hF continuous_const
    set ts := sSup S
    have hts : ts ∈ S := hclosed.csSup_mem hS hbdd
    have hSeq : S = Iic ts := by
      ext t; constructor
      · intro ht; exact le_csSup hbdd ht
      · intro ht; exact (monotone_cdf ν ht).trans hts
    have hval : cdf ν ts = c := by
      refine le_antisymm hts ?_
      rcases hc0.eq_or_lt with rfl | hpos
      · exact cdf_nonneg ν ts
      · obtain ⟨a, ha⟩ := ((tendsto_order.1 (tendsto_cdf_atBot ν)).2 c hpos).exists
        obtain ⟨t0, ht0⟩ := intermediate_value_univ a t1 hF ⟨ha.le, (ht1 t1 le_rfl).le⟩
        have : t0 ∈ S := (show cdf ν t0 ≤ c from ht0.le)
        rw [← ht0]; exact monotone_cdf ν (le_csSup hbdd this)
    rw [hSeq, ← ofReal_cdf, hval]

/-- **Probability integral transform** (Lemma `t-lem:reducibility`, "`N_*(dN) = dt` on
`[0,1]`"): if the CDF `F t = ν(-∞, t]` of a probability measure `ν` on `ℝ` is continuous,
then `F_* ν` is Lebesgue measure on `[0,1]`. -/
theorem map_cdf_eq_volume (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hF : Continuous fun t => (ν (Iic t)).toReal) :
    ν.map (fun t => (ν (Iic t)).toReal) = volume.restrict (Icc 0 1) := by
  rw [toReal_Iic_eq_cdf] at hF ⊢
  have hmeas : Measurable (cdf ν) := (monotone_cdf ν).measurable
  refine Measure.ext_of_Iic _ _ fun c => ?_
  rw [Measure.map_apply hmeas measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
  rcases lt_or_ge c 0 with hc | hc
  · have h1 : cdf ν ⁻¹' Iic c = ∅ :=
      eq_empty_of_forall_notMem fun t ht => by
        have := cdf_nonneg ν t; simp only [mem_preimage, mem_Iic] at ht; linarith
    have h2 : Iic c ∩ Icc (0 : ℝ) 1 = ∅ :=
      eq_empty_of_forall_notMem fun t ht => by
        linarith [show t ≤ c from ht.1, show 0 ≤ t from ht.2.1]
    rw [h1, h2]; simp
  rcases lt_or_ge c 1 with hc1 | hc1
  · have h2 : Iic c ∩ Icc (0 : ℝ) 1 = Icc 0 c := by
      ext t; simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact ⟨h2, h1, by linarith⟩
    rw [h2, Real.volume_Icc, sub_zero, measure_cdf_le ν hF hc hc1]
  · have h1 : cdf ν ⁻¹' Iic c = univ :=
      eq_univ_of_forall fun t => (cdf_le_one ν t).trans hc1
    have h2 : Iic c ∩ Icc (0 : ℝ) 1 = Icc 0 1 := by
      ext t; simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨_, h⟩; exact h
      · rintro ⟨h1, h2⟩; exact ⟨by linarith, h1, h2⟩
    rw [h1, h2, Real.volume_Icc, measure_univ]; simp

/-! ### Transfer to energies via `ρ = (1 - N)/2` -/

/-- If `ρ = (1 - F)/2` with `F` the (continuous) CDF of `ν` and `S` is Lebesgue-null, then
`ν {E | ρ(E) ∈ S} = 0` (Lemmas `t-lem:reducibility` and `t-lem:arithmetic-reducibility`). -/
theorem measure_rho_preimage_null (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hF : Continuous fun t => (ν (Iic t)).toReal) {S : Set ℝ} (hS : volume S = 0) :
    ν {E | (1 - (ν (Iic E)).toReal) / 2 ∈ S} = 0 := by
  set F := fun t => (ν (Iic t)).toReal
  have hmeas : Measurable F := by
    rw [show F = cdf ν from toReal_Iic_eq_cdf ν]; exact (monotone_cdf ν).measurable
  set T := (fun u : ℝ => (-1 / 2 : ℝ) * u) ⁻¹' ((· + 1 / 2) ⁻¹' S)
  have hT : volume T = 0 := by
    simp only [T]
    rw [Real.volume_preimage_mul_left (by norm_num), measure_preimage_add_right, hS, mul_zero]
  have hset : {E | (1 - F E) / 2 ∈ S} = F ⁻¹' T := by
    ext E; simp only [T, mem_ofPred_eq, mem_preimage]
    constructor <;> intro h <;> convert h using 1 <;> ring
  change ν {E | (1 - F E) / 2 ∈ S} = 0
  rw [hset]
  refine nonpos_iff_eq_zero.1 ?_
  calc ν (F ⁻¹' T) ≤ ν.map F T := Measure.le_map_apply hmeas.aemeasurable T
    _ = volume.restrict (Icc 0 1) T := by rw [map_cdf_eq_volume ν hF]
    _ ≤ volume T := Measure.restrict_apply_le _ _
    _ = 0 := hT

/-- `dN {E | ρ(E) ∉ Θ_{α,τ}} = 0` for `τ > 1`. -/
theorem measure_rho_notMem_ThetaTau (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hF : Continuous fun t => (ν (Iic t)).toReal) (α : ℝ) {τ : ℝ} (hτ : 1 < τ) :
    ν {E | (1 - (ν (Iic E)).toReal) / 2 ∉ ThetaTau α τ} = 0 :=
  measure_rho_preimage_null ν hF (S := (ThetaTau α τ)ᶜ) (volume_compl_ThetaTau α hτ)

/-- `dN {E | ρ(E) ∉ Θ_α} = 0`. -/
theorem measure_rho_notMem_ThetaSet (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hF : Continuous fun t => (ν (Iic t)).toReal) (α : ℝ) :
    ν {E | (1 - (ν (Iic E)).toReal) / 2 ∉ ThetaSet α} = 0 :=
  measure_rho_preimage_null ν hF (S := (ThetaSet α)ᶜ) (volume_compl_ThetaSet α)

/-- `dN {E | 4ρ(E) ∈ 2αℤ + ℤ} = 0`. -/
theorem measure_rho_resonant4 (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hF : Continuous fun t => (ν (Iic t)).toReal) (α : ℝ) :
    ν {E | ∃ j m : ℤ, 4 * ((1 - (ν (Iic E)).toReal) / 2) = 2 * α * j + m} = 0 :=
  measure_rho_preimage_null ν hF (S := {r | ∃ j m : ℤ, 4 * r = 2 * α * j + m})
    (volume_resonant4 α)

end Red
