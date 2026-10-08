/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §3.9.1: Birkhoff's ergodic theorem for flows (Theorem 3.9.2)

Main results:
* `DF.FlowBirkhoff.ae_mem_or_ae_notMem` — for an ergodic flow, a measurable set which is
  invariant *up to null sets* under every `ϕ_t` is null or conull (the strictly invariant set
  `{x : ϕ_s x ∈ E for a.e. s}` differs from `E` by a null set, by Fubini);
* `DF.FlowBirkhoff.ae_eq_const_of_ae_invariant` — the corresponding statement for functions;
* `DF.flowBirkhoff` — **Theorem 3.9.2**: the Statement `DF.FlowBirkhoffStatement`.

Proof: with `F(x) = ∫₀¹ f(ϕ_s x) ds` the Birkhoff sums of `F` under the time-one map `ϕ₁` are
`∫₀ⁿ f(ϕ_s x) ds`, so Theorem 3.3.1 gives convergence along integer times; the increments over
`[n, t]`, `t < n + 1`, are controlled by `∫ₙⁿ⁺¹ |f(ϕ_s x)| ds = o(n)` (Birkhoff for `|f|`). The
limit is invariant (a.e.) under every `ϕ_t`, hence a.e. constant, and the constant is
`∫ F = ∫ f`. Joint measurability of `(s, x) ↦ ϕ_s x` is automatic since `ℝ` is second
countable.
-/
import DamanikFillman.Ch3.Flows
import DamanikFillman.Ch3.Birkhoff

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Set Function Topology

namespace DF

namespace FlowBirkhoff

/-! ### Real analysis -/

/-- Convergence of `(1/t) ∫₀ᵗ h` from convergence along integers, given that the unit
increments of `∫ |h|` are `o(n)`. -/
lemma tendsto_of_nat (h : ℝ → ℝ) (hloc : ∀ a b, IntervalIntegrable h volume a b) {L : ℝ}
    (h2 : Tendsto (fun n : ℕ => (∫ s in (0 : ℝ)..n, h s) / n) atTop (𝓝 L))
    (h3 : Tendsto (fun n : ℕ => (∫ s in (n : ℝ)..n + 1, |h s|) / (n + 1)) atTop (𝓝 0)) :
    Tendsto (fun t : ℝ => (1 / t) * ∫ s in (0 : ℝ)..t, h s) atTop (𝓝 L) := by
  have hP : Tendsto (fun t : ℝ => ((⌊t⌋₊ : ℝ) / t) * ((∫ s in (0 : ℝ)..⌊t⌋₊, h s) / ⌊t⌋₊))
      atTop (𝓝 (1 * L)) :=
    tendsto_nat_floor_div_atTop.mul (h2.comp tendsto_nat_floor_atTop)
  have hQ : Tendsto (fun t : ℝ => (1 / t) * ∫ s in (⌊t⌋₊ : ℝ)..t, h s) atTop (𝓝 0) := by
    have hb : Tendsto (fun t : ℝ =>
        2 * ((∫ s in (⌊t⌋₊ : ℝ)..⌊t⌋₊ + 1, |h s|) / (⌊t⌋₊ + 1))) atTop (𝓝 (2 * 0)) :=
      (h3.comp tendsto_nat_floor_atTop).const_mul 2
    rw [mul_zero] at hb
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
    have hn : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le (by linarith)
    have hn1 : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
    have hn0 : (0 : ℝ) ≤ ⌊t⌋₊ := Nat.cast_nonneg _
    have hI : |∫ s in (⌊t⌋₊ : ℝ)..t, h s| ≤ ∫ s in (⌊t⌋₊ : ℝ)..⌊t⌋₊ + 1, |h s| :=
      (intervalIntegral.abs_integral_le_integral_abs hn).trans
        (intervalIntegral.integral_mono_interval le_rfl hn hn1.le
          (Eventually.of_forall fun s => abs_nonneg _) (hloc _ _).abs)
    have hJ : 0 ≤ ∫ s in (⌊t⌋₊ : ℝ)..⌊t⌋₊ + 1, |h s| :=
      intervalIntegral.integral_nonneg (by linarith) fun s _ => abs_nonneg _
    have ht0 : 0 < t := by linarith
    have hinv : 1 / t ≤ 2 / ((⌊t⌋₊ : ℝ) + 1) := by
      rw [div_le_div_iff₀ ht0 (by positivity)]
      linarith
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / t)]
    calc 1 / t * |∫ s in (⌊t⌋₊ : ℝ)..t, h s|
        ≤ 1 / t * ∫ s in (⌊t⌋₊ : ℝ)..⌊t⌋₊ + 1, |h s| := by gcongr
      _ ≤ 2 / ((⌊t⌋₊ : ℝ) + 1) * ∫ s in (⌊t⌋₊ : ℝ)..⌊t⌋₊ + 1, |h s| := by gcongr
      _ = 2 * ((∫ s in (⌊t⌋₊ : ℝ)..⌊t⌋₊ + 1, |h s|) / (⌊t⌋₊ + 1)) := by ring
  have hPQ := hP.add hQ
  rw [one_mul, add_zero] at hPQ
  refine hPQ.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht
  have hn1 : 1 ≤ ⌊t⌋₊ := Nat.le_floor (by simpa using ht)
  have hn0 : ((⌊t⌋₊ : ℕ) : ℝ) ≠ 0 := by positivity
  have ht0 : t ≠ 0 := by positivity
  beta_reduce
  rw [← intervalIntegral.integral_add_adjacent_intervals (hloc 0 ⌊t⌋₊) (hloc ⌊t⌋₊ t)]
  have e1 : (⌊t⌋₊ : ℝ) / t * ((∫ s in (0 : ℝ)..⌊t⌋₊, h s) / ⌊t⌋₊) =
      1 / t * ∫ s in (0 : ℝ)..⌊t⌋₊, h s := by
    field_simp
  rw [e1, mul_add]

/-- Time averages are unchanged by a shift of the time origin. -/
lemma tendsto_shift (h : ℝ → ℝ) (hloc : ∀ a b, IntervalIntegrable h volume a b) (r : ℝ)
    {L : ℝ} (hL : Tendsto (fun t : ℝ => (1 / t) * ∫ s in (0 : ℝ)..t, h s) atTop (𝓝 L)) :
    Tendsto (fun t : ℝ => (1 / t) * ∫ s in (0 : ℝ)..t, h (s + r)) atTop (𝓝 L) := by
  have e : ∀ t : ℝ, ∫ s in (0 : ℝ)..t, h (s + r) =
      (∫ s in (0 : ℝ)..t + r, h s) - ∫ s in (0 : ℝ)..r, h s := by
    intro t
    rw [intervalIntegral.integral_comp_add_right h r, zero_add,
      intervalIntegral.integral_interval_sub_left (hloc _ _) (hloc _ _)]
  have h1 : Tendsto (fun t : ℝ => ((t + r) / t) * ((1 / (t + r)) * ∫ s in (0 : ℝ)..t + r, h s))
      atTop (𝓝 (1 * L)) := by
    refine Tendsto.mul ?_ (hL.comp (tendsto_atTop_add_const_right _ r tendsto_id))
    have : Tendsto (fun t : ℝ => 1 + r * t⁻¹) atTop (𝓝 (1 + r * 0)) :=
      tendsto_const_nhds.add (tendsto_const_nhds.mul tendsto_inv_atTop_zero)
    rw [mul_zero, add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    rw [add_div, div_self ht.ne', div_eq_mul_inv]
  have h2 : Tendsto (fun t : ℝ => (1 / t) * ∫ s in (0 : ℝ)..r, h s) atTop (𝓝 0) := by
    simpa using tendsto_inv_atTop_zero.mul_const (∫ s in (0 : ℝ)..r, h s)
  have h12 := h1.sub h2
  rw [one_mul, sub_zero] at h12
  refine h12.congr' ?_
  filter_upwards [eventually_gt_atTop (max 0 (-r))] with t ht
  have ht0 : 0 < t := lt_of_le_of_lt (le_max_left _ _) ht
  have htr : 0 < t + r := by linarith [le_max_right 0 (-r)]
  have ht0' := ht0.ne'
  have htr' := htr.ne'
  beta_reduce
  rw [e t]
  field_simp

/-- If the Birkhoff averages of `u` converge at `x`, then `u(Tⁿx) = o(n)`. -/
lemma tendsto_term_div {α : Type*} (T : α → α) (u : α → ℝ) (x : α) {L : ℝ}
    (h : Tendsto (fun n => birkhoffAverage ℝ T u n x) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => u (T^[n] x) / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  have key : ∀ n : ℕ, u (T^[n] x) / ((n : ℝ) + 1) = birkhoffAverage ℝ T u (n + 1) x -
      ((n : ℝ) / ((n : ℝ) + 1)) * birkhoffAverage ℝ T u n x := by
    intro n
    simp only [birkhoffAverage, birkhoffSum_succ_apply, smul_eq_mul]
    push_cast
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have : (n : ℝ) ≠ 0 := by positivity
      field_simp
      try ring
  have := (h.comp (tendsto_add_atTop_nat 1)).sub
    ((tendsto_natCast_div_add_atTop (1 : ℝ)).mul h)
  rw [one_mul, sub_self] at this
  exact this.congr fun n => (key n).symm

/-! ### Flows -/

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  {ϕ : Flow ℝ X} {μ : Measure X}

lemma measurable_flow (ϕ : Flow ℝ X) : Measurable fun p : X × ℝ => ϕ p.2 p.1 :=
  (ϕ.continuous continuous_snd continuous_fst).measurable

lemma iterate_one (ϕ : Flow ℝ X) (n : ℕ) (x : X) : (ϕ 1)^[n] x = ϕ n x := by
  induction n with
  | zero => simp [Flow.map_zero_apply]
  | succ n ih => rw [iterate_succ_apply', ih, ← Flow.map_add, Nat.cast_succ, add_comm]

/-- The average of `g` over the orbit segment `ϕ_{[0,1]} x`. -/
def avgF (ϕ : Flow ℝ X) (g : X → ℝ) (x : X) : ℝ := ∫ s in (0 : ℝ)..1, g (ϕ s x)

lemma avgF_flow (g : X → ℝ) (x : X) (r : ℝ) :
    avgF ϕ g (ϕ r x) = ∫ s in r..r + 1, g (ϕ s x) := by
  unfold avgF
  have : (fun s => g (ϕ s (ϕ r x))) = fun s => g (ϕ (s + r) x) :=
    funext fun s => by rw [Flow.map_add]
  rw [this, intervalIntegral.integral_comp_add_right (fun s => g (ϕ s x)) r, zero_add, add_comm]

lemma integral_comp_flow (hmp : ∀ t, MeasurePreserving (ϕ t) μ μ) (t : ℝ) {h : X → ℝ}
    (hh : AEStronglyMeasurable h μ) : ∫ x, h (ϕ t x) ∂μ = ∫ x, h x ∂μ := by
  have := integral_map (μ := μ) (hmp t).measurable.aemeasurable
    (by rw [(hmp t).map_eq]; exact hh)
  rw [(hmp t).map_eq] at this
  exact this.symm

lemma integrable_prod [SFinite μ] (hmp : ∀ t, MeasurePreserving (ϕ t) μ μ) {g : X → ℝ} (hg : Integrable g μ)
    (hgm : Measurable g) (a b : ℝ) :
    Integrable (fun p : X × ℝ => g (ϕ p.2 p.1)) (μ.prod (volume.restrict (Ioc a b))) := by
  have hm : AEStronglyMeasurable (fun p : X × ℝ => g (ϕ p.2 p.1))
      (μ.prod (volume.restrict (Ioc a b))) := (hgm.comp (measurable_flow ϕ)).aestronglyMeasurable
  refine (integrable_prod_iff' hm).2 ⟨Eventually.of_forall fun s => ?_, ?_⟩
  · exact (hmp s).integrable_comp_of_integrable hg
  · have : (fun s : ℝ => ∫ x, ‖g (ϕ (x, s).2 (x, s).1)‖ ∂μ) = fun _ => ∫ x, ‖g x‖ ∂μ :=
      funext fun s => integral_comp_flow hmp s (h := fun y => ‖g y‖) hg.1.norm
    rw [this]
    exact integrable_const _

lemma avgF_eq (g : X → ℝ) (x : X) :
    avgF ϕ g x = ∫ s, g (ϕ s x) ∂(volume.restrict (Ioc (0 : ℝ) 1)) :=
  intervalIntegral.integral_of_le zero_le_one

lemma integrable_avgF [SFinite μ] (hmp : ∀ t, MeasurePreserving (ϕ t) μ μ) {g : X → ℝ} (hg : Integrable g μ)
    (hgm : Measurable g) : Integrable (avgF ϕ g) μ := by
  have := (integrable_prod hmp hg hgm 0 1).integral_prod_left
  exact this.congr (Eventually.of_forall fun x => (avgF_eq g x).symm)

lemma measurable_avgF {g : X → ℝ} (hgm : Measurable g) : Measurable (avgF ϕ g) := by
  have := StronglyMeasurable.integral_prod_right (ν := volume.restrict (Ioc (0 : ℝ) 1))
    (f := fun x s => g (ϕ s x)) (hgm.comp (measurable_flow ϕ)).stronglyMeasurable
  have e : avgF ϕ g = fun x => ∫ s, g (ϕ s x) ∂(volume.restrict (Ioc (0 : ℝ) 1)) :=
    funext fun x => avgF_eq g x
  rw [e]
  exact this.measurable

lemma integral_avgF [SFinite μ] (hmp : ∀ t, MeasurePreserving (ϕ t) μ μ) {g : X → ℝ} (hg : Integrable g μ)
    (hgm : Measurable g) : ∫ x, avgF ϕ g x ∂μ = ∫ y, g y ∂μ := by
  simp_rw [avgF_eq]
  rw [integral_integral_swap (f := fun x s => g (ϕ s x)) (integrable_prod hmp hg hgm 0 1)]
  have : (fun s : ℝ => ∫ x, g (ϕ s x) ∂μ) = fun _ => ∫ x, g x ∂μ :=
    funext fun s => integral_comp_flow hmp s hg.1
  rw [this, integral_const]
  simp

lemma ae_locInt [SFinite μ] (hmp : ∀ t, MeasurePreserving (ϕ t) μ μ) {g : X → ℝ} (hg : Integrable g μ)
    (hgm : Measurable g) :
    ∀ᵐ x ∂μ, ∀ a b : ℝ, IntervalIntegrable (fun s => g (ϕ s x)) volume a b := by
  have h := ae_all_iff.2 fun N : ℕ => (integrable_prod hmp hg hgm (-N) N).prod_right_ae
  filter_upwards [h] with x hx a b
  obtain ⟨N, hN⟩ := exists_nat_gt (max |a| |b|)
  rw [intervalIntegrable_iff]
  refine (show IntegrableOn (fun s => g (ϕ s x)) (Ioc (-(N : ℝ)) N) volume from hx N).mono_set
    fun s hs => ?_
  have hs' := Set.uIoc_subset_uIcc hs
  rw [Set.mem_uIcc] at hs'
  have ha := le_abs_self a
  have ha' := neg_abs_le a
  have hb := le_abs_self b
  have hb' := neg_abs_le b
  have hm1 := le_max_left |a| |b|
  have hm2 := le_max_right |a| |b|
  constructor <;> rcases hs' with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> linarith

/-! ### Ergodicity up to null sets -/

/-- For an ergodic flow, measurable sets invariant up to null sets under every `ϕ_t` are null or
conull. -/
theorem ae_mem_or_ae_notMem [SFinite μ] (hE : FlowErgodic ϕ μ) {E : Set X} (hEm : MeasurableSet E)
    (hinv : ∀ t, ∀ᵐ x ∂μ, (ϕ t x ∈ E ↔ x ∈ E)) : (∀ᵐ x ∂μ, x ∈ E) ∨ (∀ᵐ x ∂μ, x ∉ E) := by
  set S : Set (X × ℝ) := {p | ϕ p.2 p.1 ∉ E} with hSdef
  have hS : MeasurableSet S := (measurable_flow ϕ hEm).compl
  set E' : Set X := {x | ∀ᵐ s ∂(volume : Measure ℝ), ϕ s x ∈ E} with hE'def
  have hE'm : MeasurableSet E' := by
    have : E' = (fun x => (volume : Measure ℝ) (Prod.mk x ⁻¹' S)) ⁻¹' {0} := by
      ext x
      simp only [hE'def, mem_setOf_eq, mem_preimage, mem_singleton_iff]
      exact ae_iff
    rw [this]
    exact measurable_measure_prodMk_left hS (measurableSet_singleton 0)
  have hE'inv : ∀ t, ϕ t ⁻¹' E' = E' := by
    intro t
    ext x
    simp only [hE'def, mem_preimage, mem_setOf_eq]
    simp_rw [← Flow.map_add]
    constructor
    · intro h
      have := (measurePreserving_add_right (volume : Measure ℝ) (-t)).quasiMeasurePreserving.ae h
      filter_upwards [this] with s hs
      simpa using hs
    · intro h
      exact (measurePreserving_add_right (volume : Measure ℝ) t).quasiMeasurePreserving.ae h
  have hne : (volume : Measure ℝ) ≠ 0 := by
    rw [← Measure.measure_univ_pos]
    simp
  haveI : (ae (volume : Measure ℝ)).NeBot := ae_neBot.2 hne
  have hmeasD : MeasurableSet {p : X × ℝ | p.1 ∈ E ↔ ϕ p.2 p.1 ∈ E} :=
    measurableSet_setOf.2 ((measurableSet_setOf.1 (measurable_fst hEm)).iff
      (measurableSet_setOf.1 (measurable_flow ϕ hEm)))
  have hae : ∀ᵐ x ∂μ, ∀ᵐ s ∂(volume : Measure ℝ), (x ∈ E ↔ ϕ s x ∈ E) := by
    rw [Measure.ae_ae_comm (p := fun x s => (x ∈ E ↔ ϕ s x ∈ E)) hmeasD]
    exact Eventually.of_forall fun s => (hinv s).mono fun x hx => hx.symm
  have hEE' : ∀ᵐ x ∂μ, (x ∈ E ↔ x ∈ E') := by
    filter_upwards [hae] with x hx
    constructor
    · intro hxE
      exact hx.mono fun s hs => hs.1 hxE
    · intro hxE'
      by_contra hxE
      obtain ⟨s, hs1, hs2⟩ := (hx.and (show ∀ᵐ s ∂(volume : Measure ℝ), ϕ s x ∈ E from hxE')).exists
      exact hxE (hs1.2 hs2)
  rcases hE.2 E' hE'm hE'inv with h0 | h0
  · right
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0, hEE'] with x hx hxx
    exact fun hxE => hx (hxx.1 hxE)
  · left
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0, hEE'] with x hx hxx
    exact hxx.2 (by simpa using hx)

/-- For an ergodic flow, measurable functions invariant (a.e.) under every `ϕ_t` are a.e.
constant. -/
theorem ae_eq_const_of_ae_invariant [SFinite μ] (hE : FlowErgodic ϕ μ) {G : X → ℝ} (hG : Measurable G)
    (hinv : ∀ t, ∀ᵐ x ∂μ, G (ϕ t x) = G x) : ∃ c, ∀ᵐ x ∂μ, G x = c := by
  obtain ⟨c, hc⟩ := Filter.exists_eventuallyEq_const_of_forall_separating (l := ae μ) (f := G)
    MeasurableSet fun U hU => ae_mem_or_ae_notMem hE (hG hU) fun t =>
      (hinv t).mono fun x hx => by
        show G (ϕ t x) ∈ U ↔ G x ∈ U
        rw [hx]
  exact ⟨c, hc⟩

/-! ### Theorem 3.9.2 -/

theorem tendsto_of_measurable [IsProbabilityMeasure μ] (hE : FlowErgodic ϕ μ) {g : X → ℝ}
    (hg : Integrable g μ) (hgm : Measurable g) :
    ∀ᵐ x ∂μ, Tendsto (fun t : ℝ => (1 / t) * ∫ s in (0 : ℝ)..t, g (ϕ s x)) atTop
      (𝓝 (∫ y, g y ∂μ)) := by
  have hmp : ∀ t, MeasurePreserving (ϕ t) μ μ := hE.1
  have hTm : MeasurePreserving (ϕ 1) μ μ := hmp 1
  have hag : Integrable (fun y => |g y|) μ := hg.abs
  have hagm : Measurable (fun y => |g y|) := continuous_abs.measurable.comp hgm
  have hFi : Integrable (avgF ϕ g) μ := integrable_avgF hmp hg hgm
  have hAi : Integrable (avgF ϕ fun y => |g y|) μ := integrable_avgF hmp hag hagm
  have hFm : Measurable (avgF ϕ g) := measurable_avgF hgm
  have hFint : ∫ x, avgF ϕ g x ∂μ = ∫ y, g y ∂μ := integral_avgF hmp hg hgm
  have hloc := ae_locInt hmp hg hgm
  have hBF := birkhoff_ae_tendsto hTm hFi
  have hBA := birkhoff_ae_tendsto hTm hAi
  -- Birkhoff sums of `F` are integrals over `[0, n]`
  have hsum : ∀ x, (∀ a b : ℝ, IntervalIntegrable (fun s => g (ϕ s x)) volume a b) →
      ∀ n : ℕ, birkhoffSum (ϕ 1) (avgF ϕ g) n x = ∫ s in (0 : ℝ)..n, g (ϕ s x) := by
    intro x hx n
    have hk : ∀ k : ℕ, avgF ϕ g ((ϕ 1)^[k] x) =
        ∫ s in (k : ℝ)..((k + 1 : ℕ) : ℝ), g (ϕ s x) := by
      intro k
      rw [iterate_one, avgF_flow, Nat.cast_succ]
    have hadj := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
      (f := fun s => g (ϕ s x)) (a := fun k : ℕ => (k : ℝ)) (n := n) (fun k _ => hx _ _)
    simp only [Nat.cast_zero] at hadj
    rw [birkhoffSum, ← hadj]
    exact Finset.sum_congr rfl fun k _ => hk k
  -- the limit along continuous time
  set G := birkhoffLimit (ϕ 1) (avgF ϕ g) with hGdef
  have hgood : ∀ᵐ x ∂μ, (∀ a b : ℝ, IntervalIntegrable (fun s => g (ϕ s x)) volume a b) ∧
      Tendsto (fun t : ℝ => (1 / t) * ∫ s in (0 : ℝ)..t, g (ϕ s x)) atTop (𝓝 (G x)) := by
    filter_upwards [hloc, hBF, hBA] with x hx hF hA
    refine ⟨hx, tendsto_of_nat _ hx ?_ ?_⟩
    · refine hF.congr fun n => ?_
      rw [Birkhoff.birkhoffAverage_eq_div, hsum x hx n]
    · have := tendsto_term_div (ϕ 1) (avgF ϕ fun y => |g y|) x hA
      refine this.congr fun n => ?_
      rw [iterate_one, avgF_flow]
  -- invariance of the limit
  have hGinv : ∀ t, ∀ᵐ x ∂μ, G (ϕ t x) = G x := by
    intro t
    filter_upwards [hgood, (hmp t).quasiMeasurePreserving.ae hgood] with x hx hxt
    refine tendsto_nhds_unique hxt.2 ?_
    have := tendsto_shift (fun s => g (ϕ s x)) hx.1 t hx.2
    simp_rw [← Flow.map_add]
    exact this
  -- `G` is a.e. constant
  have hGm : AEStronglyMeasurable G μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (Birkhoff.integrable_birkhoffAverage hTm hFi n).aestronglyMeasurable) hBF
  set G' := hGm.mk G
  have hGG' : G =ᵐ[μ] G' := hGm.ae_eq_mk
  have hG'inv : ∀ t, ∀ᵐ x ∂μ, G' (ϕ t x) = G' x := by
    intro t
    filter_upwards [hGinv t, hGG', (hmp t).quasiMeasurePreserving.ae hGG'] with x h1 h2 h3
    rw [← h3, h1, h2]
  obtain ⟨c, hc⟩ := ae_eq_const_of_ae_invariant hE hGm.stronglyMeasurable_mk.measurable hG'inv
  have hcG : ∀ᵐ x ∂μ, G x = c := by
    filter_upwards [hGG', hc] with x h1 h2
    exact h1.trans h2
  -- the constant is `∫ F = ∫ g`
  have htc : ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ (ϕ 1) (avgF ϕ g) n x) atTop (𝓝 c) := by
    filter_upwards [hBF, hcG] with x h1 h2
    rwa [h2] at h1
  have hneg : ∀ᵐ x ∂μ,
      Tendsto (fun n => birkhoffAverage ℝ (ϕ 1) (-avgF ϕ g) n x) atTop (𝓝 (-c)) := by
    filter_upwards [htc] with x h1
    convert h1.neg using 2 with n
    simp [Birkhoff.birkhoffAverage_eq_div, Birkhoff.birkhoffSum_neg', neg_div]
  have h1 := Birkhoff.le_integral_of_tendsto hTm hFi hFm htc
  have h2 := Birkhoff.le_integral_of_tendsto hTm hFi.neg hFm.neg hneg
  have h3 : ∫ x, (-avgF ϕ g) x ∂μ = -∫ x, avgF ϕ g x ∂μ := by
    simp only [Pi.neg_apply]; exact integral_neg _
  have hc' : c = ∫ y, g y ∂μ := by rw [← hFint]; linarith
  filter_upwards [hgood, hcG] with x hx hxc
  rw [← hc', ← hxc]
  exact hx.2

end FlowBirkhoff

open FlowBirkhoff in
/-- **Theorem 3.9.2** (Birkhoff's ergodic theorem for flows). -/
theorem flowBirkhoff : FlowBirkhoffStatement := by
  intro X _ _ _ ϕ μ _ hE f hf
  set g := hf.aemeasurable.mk f
  have hgm : Measurable g := hf.aemeasurable.measurable_mk
  have hfg : f =ᵐ[μ] g := hf.aemeasurable.ae_eq_mk
  have hg : Integrable g μ := hf.congr hfg
  have hmp : ∀ t, MeasurePreserving (ϕ t) μ μ := hE.1
  -- `f ∘ ϕ_s = g ∘ ϕ_s` for a.e. `s`, for a.e. `x`
  set N := toMeasurable μ {x | f x ≠ g x}
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : μ N = 0 := by rw [measure_toMeasurable]; exact ae_iff.1 hfg
  have hmeas : MeasurableSet {p : X × ℝ | ϕ p.2 p.1 ∉ N} := (measurable_flow ϕ hNm).compl
  have hae : ∀ᵐ x ∂μ, ∀ᵐ s ∂(volume : Measure ℝ), ϕ s x ∉ N := by
    rw [Measure.ae_ae_comm (p := fun x s => ϕ s x ∉ N) hmeas]
    refine Eventually.of_forall fun s => measure_eq_zero_iff_ae_notMem.1 ?_
    show μ (ϕ s ⁻¹' N) = 0
    rw [(hmp s).measure_preimage hNm.nullMeasurableSet, hN0]
  filter_upwards [tendsto_of_measurable hE hg hgm, hae] with x hx hxN
  have hint : ∀ t : ℝ, ∫ s in (0 : ℝ)..t, f (ϕ s x) = ∫ s in (0 : ℝ)..t, g (ϕ s x) := by
    intro t
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hxN] with s hs _
    by_contra hne
    exact hs (subset_toMeasurable _ _ hne)
  simp_rw [hint, integral_congr_ae hfg]
  exact hx

end DF
