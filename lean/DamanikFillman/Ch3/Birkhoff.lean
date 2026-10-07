/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §3.3 The Birkhoff pointwise ergodic theorem (book pp. 238–243)

Main results:
* `DF.Birkhoff.setIntegral_nonneg_maxSum` — the maximal ergodic lemma (Garsia's form), the
  key ingredient of the proof;
* `DF.Birkhoff.setIntegral_nonneg_of_invariant` — the maximal lemma localised to an invariant
  set on which some Birkhoff sum is positive;
* `DF.birkhoff_ae_tendsto` — **Theorem 3.3.1**, first part: for `f ∈ L¹` and a measure
  preserving `T` of a finite measure space, the Birkhoff averages converge a.e. to a finite
  limit `DF.birkhoffLimit T f`;
* `DF.birkhoffLimit_comp_ae` — the limit is `T`-invariant a.e.;
* `DF.birkhoff_ergodic` — **Theorem 3.3.1**, second part (3.3.2): if `T` is ergodic (and `μ`
  a probability measure) the limit is a.e. equal to `E(f) = ∫ f dμ`.

Deviation from the book: the book follows Katznelson–Weiss; we instead use the classical
route through the maximal ergodic lemma (Garsia's proof), which is shorter to formalize.
The statements are the same.
-/
import Mathlib

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Set Function Topology

namespace DF

namespace Birkhoff

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}

/-! ### Elementary facts about Birkhoff sums -/

lemma birkhoffSum_eq_sum (T : Ω → Ω) (g : Ω → ℝ) (n : ℕ) :
    birkhoffSum T g n = ∑ k ∈ Finset.range n, g ∘ T^[k] := by
  ext x; simp [birkhoffSum, Finset.sum_apply]

lemma measurable_birkhoffSum (hT : Measurable T) {g : Ω → ℝ} (hg : Measurable g) (n : ℕ) :
    Measurable (birkhoffSum T g n) := by
  unfold birkhoffSum
  exact Finset.measurable_sum _ fun k _ => hg.comp (hT.iterate k)

lemma integrable_birkhoffSum (hT : MeasurePreserving T μ μ) {g : Ω → ℝ} (hg : Integrable g μ)
    (n : ℕ) : Integrable (birkhoffSum T g n) μ := by
  unfold birkhoffSum
  exact integrable_finsetSum _ fun k _ => (hT.iterate k).integrable_comp_of_integrable hg

lemma birkhoffSum_const (T : Ω → Ω) (c : ℝ) (n : ℕ) (x : Ω) :
    birkhoffSum T (fun _ => c) n x = n * c := by
  simp [birkhoffSum]

lemma birkhoffSum_sub_const (T : Ω → Ω) (g : Ω → ℝ) (c : ℝ) (n : ℕ) (x : Ω) :
    birkhoffSum T (fun y => g y - c) n x = birkhoffSum T g n x - n * c := by
  simp [birkhoffSum, Finset.sum_sub_distrib]

lemma birkhoffSum_const_sub (T : Ω → Ω) (g : Ω → ℝ) (c : ℝ) (n : ℕ) (x : Ω) :
    birkhoffSum T (fun y => c - g y) n x = n * c - birkhoffSum T g n x := by
  simp [birkhoffSum, Finset.sum_sub_distrib]

lemma birkhoffSum_neg' (T : Ω → Ω) (g : Ω → ℝ) (n : ℕ) (x : Ω) :
    birkhoffSum T (-g) n x = - birkhoffSum T g n x := by
  simp [birkhoffSum]

lemma birkhoffAverage_eq_div (T : Ω → Ω) (g : Ω → ℝ) (n : ℕ) (x : Ω) :
    birkhoffAverage ℝ T g n x = birkhoffSum T g n x / n := by
  simp [birkhoffAverage, div_eq_inv_mul]

lemma iterate_mem_iff {E : Set Ω} (hinv : T ⁻¹' E = E) (k : ℕ) (x : Ω) :
    T^[k] x ∈ E ↔ x ∈ E := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply, ih]
    conv_rhs => rw [← hinv]
    rfl

/-! ### The maximal ergodic lemma -/

/-- `maxSum T g N x = max (0, S_1 g x, …, S_N g x)` where `S_k g` are the Birkhoff sums. -/
def maxSum (T : Ω → Ω) (g : Ω → ℝ) : ℕ → Ω → ℝ
  | 0 => fun _ => 0
  | N + 1 => fun x => max (maxSum T g N x) (birkhoffSum T g (N + 1) x)

variable {g : Ω → ℝ}

lemma maxSum_nonneg (N : ℕ) (x : Ω) : 0 ≤ maxSum T g N x := by
  induction N with
  | zero => simp [maxSum]
  | succ N ih => exact ih.trans (le_max_left _ _)

lemma le_maxSum {k N : ℕ} (hk : k ≤ N) (x : Ω) : birkhoffSum T g k x ≤ maxSum T g N x := by
  induction N with
  | zero => obtain rfl : k = 0 := by omega
            simp [maxSum]
  | succ N ih =>
    rcases Nat.lt_or_ge k (N + 1) with h | h
    · exact (ih (by omega)).trans (le_max_left _ _)
    · obtain rfl : k = N + 1 := by omega
      exact le_max_right _ _

lemma exists_eq_maxSum (N : ℕ) (x : Ω) : ∃ k ≤ N, maxSum T g N x = birkhoffSum T g k x := by
  induction N with
  | zero => exact ⟨0, le_rfl, by simp [maxSum]⟩
  | succ N ih =>
    obtain ⟨k, hk, he⟩ := ih
    simp only [maxSum]
    rcases le_total (maxSum T g N x) (birkhoffSum T g (N + 1) x) with h | h
    · exact ⟨N + 1, le_rfl, max_eq_right h⟩
    · exact ⟨k, by omega, by rw [max_eq_left h, he]⟩

lemma maxSum_mono (x : Ω) : Monotone fun N => maxSum T g N x :=
  monotone_nat_of_le_succ fun _ => le_max_left _ _

lemma maxSum_le_add {N : ℕ} {x : Ω} (h : 0 < maxSum T g N x) :
    maxSum T g N x ≤ g x + maxSum T g N (T x) := by
  obtain ⟨k, hk, he⟩ := exists_eq_maxSum (T := T) (g := g) N x
  rcases k with _ | j
  · simp [he] at h
  · rw [he, birkhoffSum_succ_apply']
    have := le_maxSum (T := T) (g := g) (k := j) (N := N) (by omega) (T x)
    linarith

lemma measurable_maxSum (hT : Measurable T) (hg : Measurable g) (N : ℕ) :
    Measurable (maxSum T g N) := by
  induction N with
  | zero => exact measurable_const
  | succ N ih => exact ih.max (measurable_birkhoffSum hT hg _)

lemma integrable_maxSum (hT : MeasurePreserving T μ μ) (hg : Integrable g μ) (N : ℕ) :
    Integrable (maxSum T g N) μ := by
  induction N with
  | zero => exact integrable_zero _ _ _
  | succ N ih => exact ih.sup (integrable_birkhoffSum hT hg _)

/-- **Maximal ergodic lemma** (Garsia): `∫_{max_{k ≤ N} S_k g > 0} g dμ ≥ 0`. -/
theorem setIntegral_nonneg_maxSum (hT : MeasurePreserving T μ μ) (hg : Integrable g μ)
    (hgm : Measurable g) (N : ℕ) :
    0 ≤ ∫ x in {x | 0 < maxSum T g N x}, g x ∂μ := by
  set M := maxSum T g N with hMdef
  set P := {x | 0 < M x}
  have hMm : Measurable M := measurable_maxSum hT.measurable hgm N
  have hMi : Integrable M μ := integrable_maxSum hT hg N
  have hMTi : Integrable (M ∘ T) μ := hT.integrable_comp_of_integrable hMi
  have hP : MeasurableSet P := measurableSet_lt measurable_const hMm
  -- `∫_P g ≥ ∫_P (M - M ∘ T)`
  have h1 : ∫ x in P, (M x - M (T x)) ∂μ ≤ ∫ x in P, g x ∂μ := by
    refine setIntegral_mono_on (hMi.sub hMTi).integrableOn hg.integrableOn hP ?_
    intro x hx
    have := maxSum_le_add (T := T) (g := g) (N := N) (x := x) hx
    linarith
  have h2 : ∫ x in P, (M x - M (T x)) ∂μ = ∫ x in P, M x ∂μ - ∫ x in P, M (T x) ∂μ :=
    integral_sub hMi.integrableOn hMTi.integrableOn
  have h3 : ∫ x in P, M x ∂μ = ∫ x, M x ∂μ := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    have h0 := maxSum_nonneg (T := T) (g := g) N x
    simp only [P, mem_ofPred_eq, not_lt] at hx
    exact le_antisymm hx h0
  have h4 : ∫ x in P, M (T x) ∂μ ≤ ∫ x, M (T x) ∂μ :=
    setIntegral_le_integral hMTi (Eventually.of_forall fun x => maxSum_nonneg _ _)
  have h5 : ∫ x, M (T x) ∂μ = ∫ x, M x ∂μ := by
    rw [← integral_map hT.measurable.aemeasurable (by rw [hT.map_eq]; exact hMm.aestronglyMeasurable),
      hT.map_eq]
  linarith

/-- The maximal lemma localised to a strictly invariant measurable set `E` on which, at every
point, some Birkhoff sum of `g` is positive: then `∫_E g ≥ 0`. -/
theorem setIntegral_nonneg_of_invariant (hT : MeasurePreserving T μ μ) (hg : Integrable g μ)
    (hgm : Measurable g) {E : Set Ω} (hE : MeasurableSet E) (hinv : T ⁻¹' E = E)
    (hpos : ∀ x ∈ E, ∃ n, 0 < birkhoffSum T g n x) : 0 ≤ ∫ x in E, g x ∂μ := by
  set h := E.indicator g with hh
  have hhm : Measurable h := hgm.indicator hE
  have hhi : Integrable h μ := hg.indicator hE
  have hS : ∀ n x, birkhoffSum T h n x = E.indicator (birkhoffSum T g n) x := by
    intro n x
    by_cases hx : x ∈ E
    · rw [indicator_of_mem hx]
      simp only [birkhoffSum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hh, indicator_of_mem ((iterate_mem_iff hinv k x).2 hx)]
    · rw [indicator_of_notMem hx]
      simp only [birkhoffSum]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [hh, indicator_of_notMem (by rwa [iterate_mem_iff hinv k x])]
  have hM : ∀ N x, maxSum T h N x = E.indicator (maxSum T g N) x := by
    intro N x
    induction N with
    | zero => simp [maxSum]
    | succ N ih =>
      simp only [maxSum, ih, hS]
      by_cases hx : x ∈ E
      · simp [indicator_of_mem hx]
      · simp [indicator_of_notMem hx]
  set P : ℕ → Set Ω := fun N => {x | 0 < maxSum T h N x}
  have hPm : ∀ N, MeasurableSet (P N) := fun N =>
    measurableSet_lt measurable_const (measurable_maxSum hT.measurable hhm N)
  have hPmono : Monotone P := fun N N' hNN' x hx =>
    lt_of_lt_of_le hx (maxSum_mono x hNN')
  have hU : (⋃ N, P N) = E := by
    ext x
    simp only [mem_iUnion, P, mem_ofPred_eq, hM]
    constructor
    · rintro ⟨N, hN⟩
      by_contra hx
      rw [indicator_of_notMem hx] at hN
      exact lt_irrefl _ hN
    · intro hx
      obtain ⟨n, hn⟩ := hpos x hx
      exact ⟨n, by rw [indicator_of_mem hx]; exact hn.trans_le (le_maxSum le_rfl x)⟩
  have hlim := tendsto_setIntegral_of_monotone (μ := μ) (f := h) hPm hPmono hhi.integrableOn
  rw [hU] at hlim
  have hnn : ∀ N, 0 ≤ ∫ x in P N, h x ∂μ := fun N =>
    setIntegral_nonneg_maxSum hT hhi hhm N
  have := ge_of_tendsto' hlim hnn
  rwa [hh, setIntegral_indicator hE, inter_self] at this

/-! ### Upcrossing sets -/

/-- `Hi T f b` is the set of points where `limsup S_n f / n > b` (formulated without limsup). -/
def Hi (T : Ω → Ω) (f : Ω → ℝ) (b : ℝ) : Set Ω :=
  {x | ∃ q : ℚ, b < q ∧ ∃ᶠ n in atTop, (q : ℝ) * n < birkhoffSum T f n x}

lemma measurableSet_frequently {P : ℕ → Ω → Prop} (hP : ∀ n, MeasurableSet {x | P n x}) :
    MeasurableSet {x | ∃ᶠ n in atTop, P n x} := by
  have : {x | ∃ᶠ n in atTop, P n x} = ⋂ N : ℕ, ⋃ n ≥ N, {x | P n x} := by
    ext x; simp [frequently_atTop]
  rw [this]
  exact MeasurableSet.iInter fun N => MeasurableSet.iUnion fun n => MeasurableSet.iUnion
    fun _ => hP n

lemma measurableSet_Hi (hT : Measurable T) {f : Ω → ℝ} (hf : Measurable f) (b : ℝ) :
    MeasurableSet (Hi T f b) := by
  have : Hi T f b = ⋃ q ∈ {q : ℚ | b < q},
      {x | ∃ᶠ n in atTop, (q : ℝ) * n < birkhoffSum T f n x} := by
    ext x; simp [Hi]
  rw [this]
  refine MeasurableSet.biUnion (to_countable _) fun q _ => measurableSet_frequently fun n => ?_
  exact measurableSet_lt measurable_const (measurable_birkhoffSum hT hf n)

/-- Eventually `(b' - b'') n ≥ c` for `b'' < b'`. -/
lemma eventually_mul_ge {b' b'' : ℝ} (h : b'' < b') (c : ℝ) :
    ∀ᶠ n : ℕ in atTop, c ≤ (b' - b'') * n := by
  obtain ⟨N, hN⟩ := exists_nat_ge (c / (b' - b''))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hpos : 0 < b' - b'' := sub_pos.2 h
  rw [div_le_iff₀ hpos] at hN
  have : (N : ℝ) ≤ n := by exact_mod_cast hn
  nlinarith

/-- The sets `Hi T f b` are strictly `T`-invariant. -/
lemma preimage_Hi (f : Ω → ℝ) (b : ℝ) : T ⁻¹' (Hi T f b) = Hi T f b := by
  ext x
  simp only [Hi, mem_preimage, mem_ofPred_eq]
  constructor
  · rintro ⟨q, hq, hfr⟩
    obtain ⟨q', hq'1, hq'2⟩ := exists_rat_btwn hq
    refine ⟨q', hq'1, ?_⟩
    have hev := eventually_mul_ge (b' := q) (b'' := q') (by exact_mod_cast hq'2) (q' - f x)
    have : ∃ᶠ n in atTop, (q' : ℝ) * ((n + 1 : ℕ) : ℝ) < birkhoffSum T f (n + 1) x := by
      refine (hfr.and_eventually hev).mono fun n ⟨h1, h2⟩ => ?_
      rw [birkhoffSum_succ_apply']
      push_cast
      nlinarith
    exact (tendsto_add_atTop_nat 1).frequently this
  · rintro ⟨q, hq, hfr⟩
    obtain ⟨q', hq'1, hq'2⟩ := exists_rat_btwn hq
    refine ⟨q', hq'1, ?_⟩
    have hev := eventually_mul_ge (b' := q) (b'' := q') (by exact_mod_cast hq'2) (f x - q)
    rw [frequently_atTop] at hfr ⊢
    intro N
    obtain ⟨N', hN'⟩ := (eventually_atTop.1 hev)
    obtain ⟨n, hn, hn'⟩ := hfr (max N N' + 1)
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    refine ⟨m, by omega, ?_⟩
    have h2 := hN' m (by omega)
    rw [birkhoffSum_succ_apply'] at hn'
    push_cast at hn'
    nlinarith

lemma exists_pos_of_mem_Hi {f : Ω → ℝ} {b : ℝ} {x : Ω} (hx : x ∈ Hi T f b) :
    ∃ n, 0 < birkhoffSum T (fun y => f y - b) n x := by
  obtain ⟨q, hq, hfr⟩ := hx
  obtain ⟨n, hn1, hn2⟩ := (hfr.and_eventually (eventually_ge_atTop 1)).exists
  refine ⟨n, ?_⟩
  rw [birkhoffSum_sub_const]
  have : (1 : ℝ) ≤ n := by exact_mod_cast hn2
  nlinarith

variable [IsFiniteMeasure μ]

/-- If `T` preserves `μ` and `E` is invariant, `μ`-integrable functions with Birkhoff sums
eventually beyond level `b` on `E` have `∫_E f ≥ b μ(E)`. -/
lemma integral_ge_of_subset_Hi (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hf : Integrable f μ)
    (hfm : Measurable f) {E : Set Ω} (hE : MeasurableSet E) (hinv : T ⁻¹' E = E) {b : ℝ}
    (hsub : E ⊆ Hi T f b) : b * μ.real E ≤ ∫ x in E, f x ∂μ := by
  have h := setIntegral_nonneg_of_invariant hT (hf.sub (integrable_const b))
    (hfm.sub measurable_const) hE hinv fun x hx => exists_pos_of_mem_Hi (hsub hx)
  simp only [Pi.sub_apply] at h
  rw [integral_sub hf.integrableOn (integrable_const b).integrableOn, setIntegral_const,
    smul_eq_mul] at h
  linarith

lemma Hi_neg_iff {f : Ω → ℝ} {a : ℝ} {x : Ω} :
    x ∈ Hi T (-f) (-a) ↔ ∃ q : ℚ, (q : ℝ) < a ∧ ∃ᶠ n in atTop, birkhoffSum T f n x < q * n := by
  simp only [Hi, mem_ofPred_eq, birkhoffSum_neg']
  constructor
  · rintro ⟨q, hq, hfr⟩
    exact ⟨-q, by push_cast; linarith, hfr.mono fun n hn => by push_cast; linarith⟩
  · rintro ⟨q, hq, hfr⟩
    exact ⟨-q, by push_cast; linarith, hfr.mono fun n hn => by push_cast; linarith⟩

/-- The set where `liminf < a < b < limsup` is null. -/
lemma measure_Hi_inter_Hi (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hf : Integrable f μ)
    (hfm : Measurable f) {a b : ℝ} (hab : a < b) :
    μ (Hi T (-f) (-a) ∩ Hi T f b) = 0 := by
  set E := Hi T (-f) (-a) ∩ Hi T f b
  have hE : MeasurableSet E :=
    (measurableSet_Hi hT.measurable hfm.neg _).inter (measurableSet_Hi hT.measurable hfm _)
  have hinv : T ⁻¹' E = E := by simp only [E, preimage_inter, preimage_Hi]
  have h1 := integral_ge_of_subset_Hi hT hf hfm hE hinv (b := b) inter_subset_right
  have h2 := integral_ge_of_subset_Hi hT hf.neg hfm.neg hE hinv (b := -a) inter_subset_left
  have h3 : ∫ x in E, (-f) x ∂μ = - ∫ x in E, f x ∂μ := by
    simp only [Pi.neg_apply]; exact integral_neg _
  rw [h3] at h2
  have h4 : μ.real E ≤ 0 := by nlinarith [measureReal_nonneg (μ := μ) (s := E)]
  have h5 : μ.real E = 0 := le_antisymm h4 measureReal_nonneg
  rwa [measureReal_eq_zero_iff] at h5

/-- The set where `limsup = +∞` is null. -/
lemma measure_iInter_Hi (hT : MeasurePreserving T μ μ) {f : Ω → ℝ} (hf : Integrable f μ)
    (hfm : Measurable f) : μ (⋂ k : ℕ, Hi T f k) = 0 := by
  set E := ⋂ k : ℕ, Hi T f k
  have hE : MeasurableSet E := MeasurableSet.iInter fun k => measurableSet_Hi hT.measurable hfm _
  have hinv : T ⁻¹' E = E := by simp only [E, preimage_iInter, preimage_Hi]
  have hA : ∫ x in E, f x ∂μ ≤ ∫ x, |f x| ∂μ :=
    (setIntegral_mono hf.integrableOn hf.abs.integrableOn (fun x => le_abs_self _)).trans
      (setIntegral_le_integral hf.abs (Eventually.of_forall fun x => abs_nonneg _))
  have hbd : ∀ k : ℕ, (k : ℝ) * μ.real E ≤ ∫ x, |f x| ∂μ := fun k =>
    (integral_ge_of_subset_Hi hT hf hfm hE hinv (iInter_subset _ k)).trans hA
  have h0 : μ.real E = 0 := by
    by_contra hne
    have hpos : 0 < μ.real E := lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)
    obtain ⟨k, hk⟩ := exists_nat_gt ((∫ x, |f x| ∂μ) / μ.real E)
    have := hbd k
    rw [div_lt_iff₀ hpos] at hk
    linarith
  rwa [measureReal_eq_zero_iff] at h0

/-! ### A deterministic lemma on real sequences -/

/-- If `s n / n` is not frequently above every level, not frequently below every level, and
there is no pair of rationals `a < b` which are crossed infinitely often from both sides, then
`s n / n` converges. -/
lemma tendsto_of_not_upcross (s : ℕ → ℝ)
    (h1 : ∃ k : ℕ, ¬ ∃ q : ℚ, (k : ℝ) < q ∧ ∃ᶠ n : ℕ in atTop, (q : ℝ) * n < s n)
    (h2 : ∃ k : ℕ, ¬ ∃ q : ℚ, (q : ℝ) < -k ∧ ∃ᶠ n : ℕ in atTop, s n < q * n)
    (h3 : ∀ a b : ℚ, a < b → ¬ ((∃ q : ℚ, (q : ℝ) < a ∧ ∃ᶠ n : ℕ in atTop, s n < q * n) ∧
        (∃ q : ℚ, (b : ℝ) < q ∧ ∃ᶠ n : ℕ in atTop, (q : ℝ) * n < s n))) :
    ∃ L, Tendsto (fun n => s n / n) atTop (𝓝 L) := by
  set u := fun n : ℕ => s n / n
  obtain ⟨k₁, hk₁⟩ := h1
  obtain ⟨k₂, hk₂⟩ := h2
  -- eventual bounds
  have hub : ∀ᶠ n : ℕ in atTop, u n ≤ k₁ + 1 := by
    have : ¬ ∃ᶠ n : ℕ in atTop, (((k₁ + 1 : ℕ) : ℚ) : ℝ) * (n : ℝ) < s n := fun hfr =>
      hk₁ ⟨(k₁ + 1 : ℕ), by push_cast; linarith, by exact_mod_cast hfr⟩
    rw [not_frequently] at this
    filter_upwards [this, eventually_ge_atTop 1] with n hn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    simp only [u]; rw [div_le_iff₀ hnpos]; push_cast at hn; linarith
  have hlb : ∀ᶠ n : ℕ in atTop, -(k₂ : ℝ) - 1 ≤ u n := by
    have : ¬ ∃ᶠ n : ℕ in atTop, s n < (((-(k₂ : ℤ) - 1 : ℤ) : ℚ) : ℝ) * (n : ℝ) := fun hfr =>
      hk₂ ⟨((-(k₂ : ℤ) - 1 : ℤ) : ℚ), by push_cast; linarith, by exact_mod_cast hfr⟩
    rw [not_frequently] at this
    filter_upwards [this, eventually_ge_atTop 1] with n hn hn1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    simp only [u]; rw [le_div_iff₀ hnpos]; push_cast at hn; linarith
  have hB1 : IsBoundedUnder (· ≤ ·) atTop u := ⟨_, hub⟩
  have hB2 : IsBoundedUnder (· ≥ ·) atTop u := ⟨_, hlb⟩
  have hle : liminf u atTop ≤ limsup u atTop := liminf_le_limsup hB1 hB2
  refine ⟨limsup u atTop, ?_⟩
  refine tendsto_of_liminf_eq_limsup ?_ rfl hB1 hB2
  by_contra hne
  have hlt : liminf u atTop < limsup u atTop := lt_of_le_of_ne hle hne
  obtain ⟨r2, h12, h23⟩ := exists_rat_btwn hlt
  obtain ⟨r1, h01, h02⟩ := exists_rat_btwn h12
  obtain ⟨r3, h03, h04⟩ := exists_rat_btwn h23
  obtain ⟨r4, h05, h06⟩ := exists_rat_btwn h04
  refine h3 r2 r3 (by exact_mod_cast h03) ⟨⟨r1, h02, ?_⟩, ⟨r4, h05, ?_⟩⟩
  · have := frequently_lt_of_liminf_lt hB1.isCoboundedUnder_ge h01
    refine (this.and_eventually (eventually_ge_atTop 1)).mono fun n ⟨hn, hn1⟩ => ?_
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    simp only [u] at hn; rwa [div_lt_iff₀ hnpos] at hn
  · have := frequently_lt_of_lt_limsup hB2.isCoboundedUnder_le h06
    refine (this.and_eventually (eventually_ge_atTop 1)).mono fun n ⟨hn, hn1⟩ => ?_
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    simp only [u] at hn; rwa [lt_div_iff₀ hnpos] at hn

/-! ### The theorem for measurable integrable functions -/

theorem ae_tendsto_of_measurable (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Integrable f μ) (hfm : Measurable f) :
    ∀ᵐ x ∂μ, ∃ L, Tendsto (fun n => birkhoffAverage ℝ T f n x) atTop (𝓝 L) := by
  have h1 : ∀ᵐ x ∂μ, x ∉ ⋂ k : ℕ, Hi T f k :=
    measure_eq_zero_iff_ae_notMem.1 (measure_iInter_Hi hT hf hfm)
  have h2 : ∀ᵐ x ∂μ, x ∉ ⋂ k : ℕ, Hi T (-f) k :=
    measure_eq_zero_iff_ae_notMem.1 (measure_iInter_Hi hT hf.neg hfm.neg)
  have h3 : ∀ᵐ x ∂μ, ∀ a b : ℚ, a < b → x ∉ Hi T (-f) (-(a : ℝ)) ∩ Hi T f b := by
    rw [ae_all_iff]; intro a; rw [ae_all_iff]; intro b
    by_cases hab : a < b
    · filter_upwards [measure_eq_zero_iff_ae_notMem.1
        (measure_Hi_inter_Hi hT hf hfm (a := a) (b := b) (by exact_mod_cast hab))] with x hx _
        using hx
    · exact Eventually.of_forall fun x h => absurd h hab
  filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
  simp only [birkhoffAverage_eq_div]
  apply tendsto_of_not_upcross
  · simp only [mem_iInter, not_forall] at hx1
    obtain ⟨k, hk⟩ := hx1; exact ⟨k, hk⟩
  · simp only [mem_iInter, not_forall] at hx2
    obtain ⟨k, hk⟩ := hx2
    refine ⟨k, fun h => hk ?_⟩
    have : ((k : ℕ) : ℝ) = -(-(k : ℝ)) := by ring
    rw [this, Hi_neg_iff]; exact h
  · intro a b hab ⟨ha, hb⟩
    exact hx3 a b hab ⟨Hi_neg_iff.2 ha, hb⟩

omit [IsFiniteMeasure μ] in
lemma ae_birkhoffSum_eq (hT : MeasurePreserving T μ μ) {f g : Ω → ℝ} (hfg : f =ᵐ[μ] g) :
    ∀ᵐ x ∂μ, ∀ n, birkhoffSum T f n x = birkhoffSum T g n x := by
  have : ∀ᵐ x ∂μ, ∀ k, f (T^[k] x) = g (T^[k] x) := by
    rw [ae_all_iff]; intro k
    exact (hT.iterate k).quasiMeasurePreserving.ae_eq_comp hfg
  filter_upwards [this] with x hx n
  simp only [birkhoffSum]; exact Finset.sum_congr rfl fun k _ => hx k

omit [IsFiniteMeasure μ] in
lemma integrable_birkhoffAverage (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Integrable f μ) (n : ℕ) : Integrable (birkhoffAverage ℝ T f n) μ := by
  have := (integrable_birkhoffSum hT hf n).div_const (n : ℝ)
  convert this using 1
  funext x; exact birkhoffAverage_eq_div _ _ _ _

end Birkhoff

open Birkhoff

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {T : Ω → Ω}

/-- The pointwise limit `f*` of the Birkhoff averages (3.3.1) (a junk value is used at points
where the limit does not exist). -/
def birkhoffLimit (T : Ω → Ω) (f : Ω → ℝ) (x : Ω) : ℝ :=
  limUnder atTop fun n => birkhoffAverage ℝ T f n x

/-- **Birkhoff's ergodic theorem**, Theorem 3.3.1 (existence and finiteness of the limit):
for a measure preserving `T` of a finite measure space and `f ∈ L¹`, the Birkhoff averages
`(1/N) ∑_{n<N} f(Tⁿω)` converge for a.e. `ω` to the finite limit `birkhoffLimit T f ω`. -/
theorem birkhoff_ae_tendsto [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T f n x) atTop (𝓝 (birkhoffLimit T f x)) := by
  set g := hf.aemeasurable.mk f
  have hgm : Measurable g := hf.aemeasurable.measurable_mk
  have hfg : f =ᵐ[μ] g := hf.aemeasurable.ae_eq_mk
  have hg : Integrable g μ := hf.congr hfg
  filter_upwards [ae_tendsto_of_measurable hT hg hgm, ae_birkhoffSum_eq hT hfg] with x hL hx
  obtain ⟨L, hL⟩ := hL
  have : (fun n => birkhoffAverage ℝ T f n x) = fun n => birkhoffAverage ℝ T g n x := by
    funext n; simp [birkhoffAverage, hx n]
  rw [← this] at hL
  exact tendsto_nhds_limUnder ⟨L, hL⟩

/-- Theorem 3.3.1: the limit `f*` is `T`-invariant, `f*(Tω) = f*(ω)` for a.e. `ω`. -/
theorem birkhoffLimit_comp_ae [IsFiniteMeasure μ] (hT : MeasurePreserving T μ μ) {f : Ω → ℝ}
    (hf : Integrable f μ) : ∀ᵐ x ∂μ, birkhoffLimit T f (T x) = birkhoffLimit T f x := by
  have h := birkhoff_ae_tendsto hT hf
  filter_upwards [h, hT.quasiMeasurePreserving.ae h] with x hx hTx
  have key : ∀ n : ℕ, birkhoffAverage ℝ T f (n + 1) x =
      f x / ((n : ℝ) + 1) + ((n : ℝ) / ((n : ℝ) + 1)) * birkhoffAverage ℝ T f n (T x) := by
    intro n
    simp only [birkhoffAverage_eq_div, birkhoffSum_succ_apply']
    push_cast
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have : (n : ℝ) ≠ 0 := by positivity
      field_simp
  have lim1 : Tendsto (fun n : ℕ => birkhoffAverage ℝ T f (n + 1) x) atTop
      (𝓝 (birkhoffLimit T f x)) := hx.comp (tendsto_add_atTop_nat 1)
  have lim2 : Tendsto (fun n : ℕ => f x / ((n : ℝ) + 1) +
      ((n : ℝ) / ((n : ℝ) + 1)) * birkhoffAverage ℝ T f n (T x)) atTop
      (𝓝 (0 + 1 * birkhoffLimit T f (T x))) := by
    refine Tendsto.add ?_ ((tendsto_natCast_div_add_atTop (1 : ℝ)).mul hTx)
    exact tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  simp only [← key] at lim2
  rw [zero_add, one_mul] at lim2
  exact tendsto_nhds_unique lim2 lim1

namespace Birkhoff

lemma le_integral_of_tendsto [IsProbabilityMeasure μ] (hT : MeasurePreserving T μ μ)
    {f : Ω → ℝ} (hf : Integrable f μ) (hfm : Measurable f) {c : ℝ}
    (hc : ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T f n x) atTop (𝓝 c)) :
    c ≤ ∫ x, f x ∂μ := by
  by_contra hlt
  push Not at hlt
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hlt
  obtain ⟨b, hb1, hb2⟩ := exists_between hq1
  set E := Hi T f b
  have hae : ∀ᵐ x ∂μ, x ∈ E := by
    filter_upwards [hc] with x hx
    refine ⟨q, hb2, ?_⟩
    have hev : ∀ᶠ n in atTop, (q : ℝ) < birkhoffAverage ℝ T f n x :=
      hx.eventually (lt_mem_nhds hq2)
    refine (hev.and (eventually_ge_atTop 1)).frequently.mono fun n ⟨h1, h2⟩ => ?_
    rwa [birkhoffAverage_eq_div, lt_div_iff₀ (by exact_mod_cast h2 : (0 : ℝ) < n)] at h1
  have hE := measurableSet_Hi hT.measurable hfm b
  have hint := integral_ge_of_subset_Hi hT hf hfm hE (preimage_Hi f b) subset_rfl
  have h0 : μ Eᶜ = 0 := ae_iff.1 hae
  have h1 : μ E = 1 := (prob_compl_eq_zero_iff hE).1 h0
  have hμE : μ.real E = 1 := by simp [measureReal_def, h1]
  have hres : μ.restrict E = μ := Measure.restrict_eq_self_of_ae_mem hae
  rw [hμE, hres] at hint
  linarith

end Birkhoff

/-- **Birkhoff's ergodic theorem**, Theorem 3.3.1 (3.3.2), ergodic case: if `T` is ergodic,
then `f* = E(f)` almost everywhere. -/
theorem birkhoff_ergodic [IsProbabilityMeasure μ] (hT : Ergodic T μ) {f : Ω → ℝ}
    (hf : Integrable f μ) : ∀ᵐ x ∂μ, birkhoffLimit T f x = ∫ y, f y ∂μ := by
  have hmp := hT.toMeasurePreserving
  have htend := birkhoff_ae_tendsto hmp hf
  have hmeas : AEStronglyMeasurable (birkhoffLimit T f) μ :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n => (integrable_birkhoffAverage hmp hf n).aestronglyMeasurable) htend
  obtain ⟨c, hc⟩ := hT.ae_eq_const_of_ae_eq_comp_ae hmeas (birkhoffLimit_comp_ae hmp hf)
  have htc : ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T f n x) atTop (𝓝 c) := by
    filter_upwards [htend, hc] with x h1 h2
    rwa [h2] at h1
  set g := hf.aemeasurable.mk f
  have hgm : Measurable g := hf.aemeasurable.measurable_mk
  have hfg : f =ᵐ[μ] g := hf.aemeasurable.ae_eq_mk
  have hg : Integrable g μ := hf.congr hfg
  have htg : ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T g n x) atTop (𝓝 c) := by
    filter_upwards [htc, ae_birkhoffSum_eq hmp hfg] with x h1 h2
    convert h1 using 2 with n
    simp [birkhoffAverage, h2 n]
  have hneg : ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T (-g) n x) atTop (𝓝 (-c)) := by
    filter_upwards [htg] with x h1
    convert h1.neg using 2 with n
    simp [birkhoffAverage_eq_div, birkhoffSum_neg', neg_div]
  have h1 := le_integral_of_tendsto hmp hg hgm htg
  have h2 := le_integral_of_tendsto hmp hg.neg hgm.neg hneg
  have h3 : ∫ x, (-g) x ∂μ = - ∫ x, g x ∂μ := by simp only [Pi.neg_apply]; exact integral_neg _
  have hfc : c = ∫ y, f y ∂μ := by rw [integral_congr_ae hfg]; linarith
  filter_upwards [hc] with x hx
  rw [hx, ← hfc]; rfl

/-- Convenient form of Theorem 3.3.1 in the ergodic case: the Birkhoff averages converge a.e.
to the space average `E(f)`. -/
theorem birkhoff_ergodic_tendsto [IsProbabilityMeasure μ] (hT : Ergodic T μ) {f : Ω → ℝ}
    (hf : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => birkhoffAverage ℝ T f n x) atTop (𝓝 (∫ y, f y ∂μ)) := by
  filter_upwards [birkhoff_ae_tendsto hT.toMeasurePreserving hf, birkhoff_ergodic hT hf]
    with x h1 h2
  rwa [h2] at h1

end DF
