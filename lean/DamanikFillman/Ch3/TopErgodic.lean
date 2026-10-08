/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §3.5 Ergodicity in the topological setting (book pp. 247–266)

Throughout, `Ω` is a compact metric space with its Borel σ-algebra and `T : Ω → Ω` is
continuous (Definition 3.5.1 asks for a homeomorphism; continuity suffices for what is proved
here).

Main definitions:
* `DF.invMeasures T` — `M₁(Ω, T)`, the `T`-invariant Borel probability measures (3.5.1);
* `DF.ergMeasures T` — `E₁(Ω, T)`, the ergodic ones;
* `DF.UniquelyErgodic T` — `M₁(Ω, T)` is a singleton.

Main results:
* `DF.invMeasures_nonempty`, `DF.convex_invMeasures`, `DF.isCompact_invProbMeasures` —
  **Proposition 3.5.3(a)** (non-emptiness is the Krylov–Bogolyubov theorem, taken from Mathlib);
* `DF.ergodic_iff_mem_extremePoints` — **Proposition 3.5.3(b)** (from Mathlib);
* `DF.Ergodic.mutuallySingular` — **Proposition 3.5.3(c)**, proved via Birkhoff's theorem;
* `DF.ae_dense_orbit` — **Proposition 3.5.5** (full support ergodic measures have a.e. dense
  orbits);
* `DF.UniquelyErgodic.ergodic` — the unique invariant measure is ergodic;
* `DF.tendstoUniformly_of_uniquelyErgodic`, `DF.uniquelyErgodic_of_tendsto`,
  `DF.uniquelyErgodic_iff` — **Proposition 3.5.6** together with Remark 3.5.7 (pointwise
  convergence to constants already suffices for unique ergodicity).

Deviations: in the converse direction of Proposition 3.5.6 we use the Krylov–Bogolyubov theorem
instead of the Riesz representation theorem to produce the invariant measure.

Statements:
* `DF.ErgodicMeasureExistsStatement` — `E₁(Ω, T) ≠ ∅` (second half of Proposition 3.5.3(b));
  **proved** in `DamanikFillman.Ch3.Generic` (`DF.ergodicMeasureExists`), by a nested-faces
  argument replacing the Krein–Milman theorem;
* `DF.FurmanStatement` — Theorem 3.5.8 (Furman) in full generality; the version with the bound
  `|f_n| ≤ C n` is proved in `DamanikFillman.Ch3.Furman` (`DF.furman`), the general statement
  in `DamanikFillman.Ch3.FurmanGeneral` (`DF.furmanStatement`);
* `DF.ErgodicDecompositionStatement` — Theorem 3.5.12 (ergodic decomposition), stated only.
-/
import DamanikFillman.Ch3.Birkhoff

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Set Function Topology BoundedContinuousFunction
open scoped ENNReal

namespace DF

/-! ### Mutual singularity of ergodic measures (no topology needed) -/

section measurable

variable {Ω : Type*} [MeasurableSpace Ω] {T : Ω → Ω}

/-- **Proposition 3.5.3(c)**: distinct ergodic probability measures are mutually singular. -/
theorem Ergodic.mutuallySingular {μ ν : Measure Ω} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : Ergodic T μ) (hν : Ergodic T ν) (hne : μ ≠ ν) : μ ⟂ₘ ν := by
  obtain ⟨E, hE, hμν⟩ : ∃ E, MeasurableSet E ∧ μ E ≠ ν E := by
    by_contra h
    push Not at h
    exact hne (Measure.ext fun s hs => h s hs)
  set f : Ω → ℝ := E.indicator 1
  have hfi : ∀ ρ : Measure Ω, [IsFiniteMeasure ρ] → Integrable f ρ := fun ρ _ =>
    (integrable_const (1 : ℝ)).indicator hE
  have hint : ∀ ρ : Measure Ω, ∫ x, f x ∂ρ = ρ.real E := fun ρ => integral_indicator_one hE
  have hneq : ∫ x, f x ∂μ ≠ ∫ x, f x ∂ν := by
    rw [hint, hint]
    intro h
    exact hμν ((ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).1 h)
  have hμlim := birkhoff_ergodic_tendsto hμ (hfi μ)
  have hνlim := birkhoff_ergodic_tendsto hν (hfi ν)
  set B := {x | Tendsto (fun n => birkhoffAverage ℝ T f n x) atTop (𝓝 (∫ x, f x ∂ν))}
  have hνB : ν Bᶜ = 0 := ae_iff.1 hνlim
  set S := toMeasurable ν Bᶜ
  refine ⟨Sᶜ, (measurableSet_toMeasurable _ _).compl, ?_, ?_⟩
  · have hsub : Sᶜ ⊆ {x | ¬ Tendsto (fun n => birkhoffAverage ℝ T f n x) atTop
        (𝓝 (∫ x, f x ∂μ))} := by
      intro x hx hx'
      have hxB : x ∈ B := by
        by_contra hxB
        exact hx (subset_toMeasurable ν Bᶜ hxB)
      exact hneq (tendsto_nhds_unique hx' hxB)
    exact measure_mono_null hsub (ae_iff.1 hμlim)
  · rw [compl_compl, measure_toMeasurable]; exact hνB

end measurable

/-! ### Dense orbits (Proposition 3.5.5) -/

section dense

variable {Ω : Type*} [TopologicalSpace Ω] [SecondCountableTopology Ω] [MeasurableSpace Ω]
  [OpensMeasurableSpace Ω] {T : Ω → Ω}

/-- **Proposition 3.5.5**: if `μ` is ergodic and has full support (every nonempty open set has
positive measure), then `μ`-a.e. point has a dense forward orbit. -/
theorem ae_dense_orbit {μ : Measure Ω} [IsProbabilityMeasure μ] [μ.IsOpenPosMeasure]
    (hT : Ergodic T μ) : ∀ᵐ x ∂μ, Dense (range fun n : ℕ => T^[n] x) := by
  set 𝓑 := TopologicalSpace.countableBasis Ω
  have hB := TopologicalSpace.isBasis_countableBasis Ω
  have hvisit : ∀ᵐ x ∂μ, ∀ U ∈ 𝓑, U.Nonempty → ∃ n, T^[n] x ∈ U := by
    rw [ae_ball_iff (TopologicalSpace.countable_countableBasis Ω)]
    intro U hU
    have hUo : IsOpen U := TopologicalSpace.isOpen_of_mem_countableBasis hU
    by_cases hne : U.Nonempty
    · have hpos : 0 < μ.real U := by
        rw [measureReal_def]
        exact ENNReal.toReal_pos (hUo.measure_pos μ hne).ne' (measure_ne_top _ _)
      have hint : Integrable (U.indicator (1 : Ω → ℝ)) μ :=
        (integrable_const (1 : ℝ)).indicator hUo.measurableSet
      filter_upwards [birkhoff_ergodic_tendsto hT hint] with x hx _
      rw [integral_indicator_one hUo.measurableSet] at hx
      by_contra hcon
      push Not at hcon
      have hzero : ∀ n, birkhoffAverage ℝ T (U.indicator (1 : Ω → ℝ)) n x = 0 := by
        intro n
        simp [birkhoffAverage, birkhoffSum, indicator_of_notMem (hcon _)]
      simp only [hzero] at hx
      exact hpos.ne (tendsto_nhds_unique tendsto_const_nhds hx)
    · exact Eventually.of_forall fun x h => absurd h hne
  filter_upwards [hvisit] with x hx
  rw [dense_iff_inter_open]
  intro U hU ⟨y, hy⟩
  obtain ⟨V, hV, hyV, hVU⟩ := hB.exists_subset_of_mem_open hy hU
  obtain ⟨n, hn⟩ := hx V hV ⟨y, hyV⟩
  exact ⟨_, hVU hn, n, rfl⟩

end dense

/-! ### Invariant measures on compact metric spaces -/

variable {Ω : Type*} [MetricSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  {T : Ω → Ω}

/-- `M₁(Ω, T)`: the `T`-invariant Borel probability measures (3.5.1). -/
def invMeasures (T : Ω → Ω) : Set (Measure Ω) :=
  {μ | MeasurePreserving T μ μ ∧ IsProbabilityMeasure μ}

/-- `E₁(Ω, T)`: the `T`-ergodic Borel probability measures. -/
def ergMeasures (T : Ω → Ω) : Set (Measure Ω) :=
  {μ | Ergodic T μ ∧ IsProbabilityMeasure μ}

/-- **Proposition 3.5.3(a)**: `M₁(Ω, T)` is nonempty (Krylov–Bogolyubov). -/
theorem invMeasures_nonempty [Nonempty Ω] (hT : Continuous T) : (invMeasures T).Nonempty := by
  obtain ⟨μ, h1, -, h3⟩ := exists_measurePreserving_probabilityMeasure hT
  exact ⟨μ, h1, h3⟩

/-- **Proposition 3.5.3(a)**: `M₁(Ω, T)` is convex. -/
theorem convex_invMeasures (hT : Continuous T) : Convex ℝ≥0∞ (invMeasures T) := by
  intro μ hμ ν hν a b ha hb hab
  obtain ⟨h1, h2⟩ := hμ
  obtain ⟨h3, h4⟩ := hν
  refine ⟨⟨hT.measurable, ?_⟩, ⟨?_⟩⟩
  · rw [Measure.map_add _ _ hT.measurable, Measure.map_smul, Measure.map_smul, h1.map_eq,
      h3.map_eq]
    all_goals exact hT.measurable.aemeasurable
  · simp [hab]

/-- **Proposition 3.5.3(a)**: `M₁(Ω, T)` is compact in the weak-* topology (as a subset of the
space of Borel probability measures). -/
theorem isCompact_invProbMeasures (hT : Continuous T) :
    IsCompact {μ : ProbabilityMeasure Ω | MeasurePreserving T μ μ} := by
  have : {μ : ProbabilityMeasure Ω | MeasurePreserving T μ μ} = {μ | μ.map T = μ} := by
    ext μ
    simp only [mem_setOf_eq]
    constructor
    · intro h
      apply Subtype.ext
      show ((μ.map T : ProbabilityMeasure Ω) : Measure Ω) = μ
      rw [ProbabilityMeasure.toMeasure_map, h.map_eq]
    · intro h
      refine ⟨hT.measurable, ?_⟩
      have := congrArg (fun ρ : ProbabilityMeasure Ω => (ρ : Measure Ω)) h
      simpa using this
  rw [this]
  exact (isClosed_eq (ProbabilityMeasure.continuous_map hT) continuous_id).isCompact

/-- **Proposition 3.5.3(b)**: an invariant probability measure is ergodic iff it is an extreme
point of `M₁(Ω, T)` (Mathlib's `Ergodic.iff_mem_extremePoints`). -/
theorem ergodic_iff_mem_extremePoints {μ : Measure Ω} [IsProbabilityMeasure μ] :
    Ergodic T μ ↔ μ ∈ extremePoints ℝ≥0∞ (invMeasures T) :=
  Ergodic.iff_mem_extremePoints

/-- Second half of **Proposition 3.5.3(b)**: `E₁(Ω, T)` is nonempty (the book uses the
Krein–Milman theorem). Stated, not proved. -/
def ErgodicMeasureExistsStatement : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [Nonempty X] [MeasurableSpace X] [BorelSpace X]
    (S : X → X), Continuous S → (ergMeasures S).Nonempty

/-! ### Unique ergodicity (Proposition 3.5.6) -/

/-- `T` is *uniquely ergodic* if `M₁(Ω, T)` consists of a single measure. -/
def UniquelyErgodic (T : Ω → Ω) : Prop := ∃ μ : Measure Ω, invMeasures T = {μ}

/-- The unique invariant measure of a uniquely ergodic map is ergodic. -/
theorem UniquelyErgodic.ergodic {μ : Measure Ω} (h : invMeasures T = {μ}) :
    Ergodic T μ ∧ IsProbabilityMeasure μ := by
  have hμ : μ ∈ invMeasures T := by rw [h]; rfl
  haveI := hμ.2
  refine ⟨Ergodic.of_mem_extremePoints ?_, hμ.2⟩
  have : {ν | MeasurePreserving T ν ν ∧ IsProbabilityMeasure ν} = invMeasures T := rfl
  rw [this, h, extremePoints_singleton]
  rfl

omit [CompactSpace Ω] in
lemma integral_birkhoffAverage_of_invariant {ν : Measure Ω} [IsProbabilityMeasure ν]
    (hν : MeasurePreserving T ν ν) {f : Ω → ℝ} (hf : Integrable f ν) (n : ℕ) (hn : n ≠ 0) :
    ∫ x, birkhoffAverage ℝ T f n x ∂ν = ∫ x, f x ∂ν := by
  simp only [Birkhoff.birkhoffAverage_eq_div]
  rw [integral_div, Birkhoff.birkhoffSum_eq_sum]
  simp only [Finset.sum_apply]
  rw [integral_finsetSum]
  · have : ∀ k ∈ Finset.range n, ∫ x, (f ∘ T^[k]) x ∂ν = ∫ x, f x ∂ν := fun k _ => by
      simp only [comp_apply]
      rw [← integral_map (hν.iterate k).measurable.aemeasurable
        (by rw [(hν.iterate k).map_eq]; exact hf.aestronglyMeasurable), (hν.iterate k).map_eq]
    rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  · exact fun k _ => (hν.iterate k).integrable_comp_of_integrable hf

/-- **Remark 3.5.7 / converse of Proposition 3.5.6**: if for every continuous `f` the Birkhoff
averages converge pointwise everywhere to a constant `c f`, then every invariant probability
measure `ν` satisfies `∫ f dν = c f`. -/
theorem integral_eq_of_tendsto {c : C(Ω, ℝ) → ℝ}
    (hc : ∀ (f : C(Ω, ℝ)) (x : Ω), Tendsto (fun n => birkhoffAverage ℝ T f n x) atTop (𝓝 (c f)))
    {ν : Measure Ω} (hν : ν ∈ invMeasures T) (f : C(Ω, ℝ)) : ∫ x, f x ∂ν = c f := by
  haveI := hν.2
  have hfi : Integrable f ν := f.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  obtain ⟨C, hC⟩ := (isCompact_range f.continuous).isBounded.exists_norm_le
  have hlim := tendsto_integral_filter_of_dominated_convergence (μ := ν) (l := atTop)
    (F := fun n x => birkhoffAverage ℝ T f n x) (f := fun _ => c f) (fun _ => C)
    (Eventually.of_forall fun n =>
      (Birkhoff.integrable_birkhoffAverage hν.1 hfi n).aestronglyMeasurable)
    (Eventually.of_forall fun n => Eventually.of_forall fun x => by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp only [birkhoffAverage_zero, Pi.zero_apply, norm_zero]
        exact (norm_nonneg _).trans (hC _ ⟨x, rfl⟩)
      · rw [Birkhoff.birkhoffAverage_eq_div, norm_div, Real.norm_natCast,
          div_le_iff₀ (by exact_mod_cast hn)]
        calc ‖birkhoffSum T f n x‖ ≤ ∑ k ∈ Finset.range n, ‖f (T^[k] x)‖ := norm_sum_le _ _
          _ ≤ ∑ k ∈ Finset.range n, C := Finset.sum_le_sum fun k _ => hC _ ⟨_, rfl⟩
          _ = C * n := by simp [mul_comm])
    (integrable_const C) (Eventually.of_forall fun x => hc f x)
  rw [integral_const, probReal_univ, one_smul] at hlim
  refine tendsto_nhds_unique (hlim.congr' ?_) tendsto_const_nhds |>.symm
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact integral_birkhoffAverage_of_invariant hν.1 hfi n (by omega)

/-- **Proposition 3.5.6** (converse direction, in the strengthened form of Remark 3.5.7): if for
every continuous `f` the Birkhoff averages converge at every point to a constant, then `T` is
uniquely ergodic. -/
theorem uniquelyErgodic_of_tendsto [Nonempty Ω] (hT : Continuous T) {c : C(Ω, ℝ) → ℝ}
    (hc : ∀ (f : C(Ω, ℝ)) (x : Ω), Tendsto (fun n => birkhoffAverage ℝ T f n x) atTop
      (𝓝 (c f))) : UniquelyErgodic T := by
  obtain ⟨μ, hμ⟩ := invMeasures_nonempty hT
  refine ⟨μ, Set.eq_singleton_iff_unique_mem.2 ⟨hμ, fun ν hν => ?_⟩⟩
  haveI := hμ.2; haveI := hν.2
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro g
  have h1 := integral_eq_of_tendsto hc hν g.toContinuousMap
  have h2 := integral_eq_of_tendsto hc hμ g.toContinuousMap
  exact h1.trans h2.symm

/-- **Proposition 3.5.6** (forward direction): if `T` is uniquely ergodic with invariant measure
`μ`, then for every continuous `f` the Birkhoff averages converge to `∫ f dμ` uniformly on `Ω`. -/
theorem tendstoUniformly_of_uniquelyErgodic (hT : Continuous T) {μ : Measure Ω}
    (hμ : invMeasures T = {μ}) (f : C(Ω, ℝ)) :
    TendstoUniformly (fun n x => birkhoffAverage ℝ T f n x) (fun _ => ∫ x, f x ∂μ) atTop := by
  have hμmem : μ ∈ invMeasures T := by rw [hμ]; rfl
  haveI := hμmem.2
  haveI : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  by_contra hcon
  rw [not_eventually] at hcon
  set P : ℕ → Prop := fun n => 1 ≤ n ∧ ∃ x, ε ≤ dist (∫ x, f x ∂μ) (birkhoffAverage ℝ T f n x)
  have hP : ∃ᶠ n in atTop, P n := by
    refine (hcon.and_eventually (eventually_ge_atTop 1)).mono fun n ⟨hn, hn1⟩ => ⟨hn1, ?_⟩
    push Not at hn
    exact hn
  classical
  set xs : ℕ → Ω := fun n => if h : P n then h.2.choose else Classical.arbitrary Ω
  have hxs : ∀ n, P n → ε ≤ dist (∫ x, f x ∂μ) (birkhoffAverage ℝ T f n (xs n)) := by
    intro n hn
    simp only [xs, dif_pos hn]
    exact hn.2.choose_spec
  set F : Filter ℕ := atTop ⊓ 𝓟 {n | P n}
  haveI hF : F.NeBot := frequently_iff_neBot.1 hP
  set u : ℕ → ProbabilityMeasure Ω := fun n => (empiricalMeasure T (xs n) (n - 1)).toProbabilityMeasure
  obtain ⟨ν, -, hν⟩ := isCompact_univ.exists_mapClusterPt (f := F) (u := u) (by simp)
  -- integrals against the empirical measures are Birkhoff averages
  have hu : ∀ (g : Ω → ℝ) (n : ℕ), 1 ≤ n →
      ∫ y, g y ∂(u n : Measure Ω) = birkhoffAverage ℝ T g n (xs n) := by
    intro g n hn
    show ∫ y, g y ∂(empiricalMeasure T (xs n) (n - 1)) = _
    rw [integral_empiricalMeasure_eq_birkhoffaverage, Nat.sub_add_cancel hn,
      birkhoffAverage_apply_congr_ring (R := NNReal) (S := ℝ)]
  -- the cluster point is invariant
  have hνinv : MeasurePreserving T ν ν := by
    refine ⟨hT.measurable, ?_⟩
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro g
    rw [integral_map hT.aemeasurable g.continuous.aestronglyMeasurable]
    refine ProbabilityMeasure.integral_comp_eq_integral_of_mapClusterPt hT hν ?_
    obtain ⟨C, hC⟩ := (isCompact_range g.continuous).isBounded.exists_norm_le
    have hbound : ∀ n, 1 ≤ n → |(∫ y, (g ∘ T) y ∂(u n : Measure Ω)) - ∫ y, g y ∂(u n : Measure Ω)|
        ≤ 2 * C / n := by
      intro n hn
      rw [hu _ n hn, hu _ n hn, birkhoffAverage_comp_apply,
        birkhoffAverage_apply_sub_birkhoffAverage, smul_eq_mul, abs_mul, abs_inv,
        Nat.abs_cast, ← div_eq_inv_mul]
      gcongr
      calc |g (T^[n] (xs n)) - g (xs n)| ≤ |g (T^[n] (xs n))| + |g (xs n)| := abs_sub _ _
        _ ≤ C + C := add_le_add (hC _ ⟨_, rfl⟩) (hC _ ⟨_, rfl⟩)
        _ = 2 * C := by ring
    have h0 : Tendsto (fun n : ℕ => 2 * C / n) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    refine squeeze_zero_norm' ?_ (h0.mono_left inf_le_left)
    filter_upwards [(eventually_ge_atTop 1).filter_mono inf_le_left] with n hn
    exact hbound n hn
  have hνμ : (ν : Measure Ω) = μ := by
    have : (ν : Measure Ω) ∈ invMeasures T := ⟨hνinv, inferInstance⟩
    rw [hμ] at this
    exact this
  -- contradiction with the choice of the points `xs n`
  have hcont := ProbabilityMeasure.continuous_integral_continuousMap (X := Ω) f
  have hnhds : {ρ : ProbabilityMeasure Ω | dist (∫ x, f x ∂(ρ : Measure Ω)) (∫ x, f x ∂μ) < ε}
      ∈ 𝓝 ν := by
    refine (isOpen_lt (continuous_dist.comp (hcont.prodMk continuous_const))
      continuous_const).mem_nhds ?_
    show dist (∫ x, f x ∂(ν : Measure Ω)) (∫ x, f x ∂μ) < ε
    rw [hνμ, dist_self]; exact hε
  obtain ⟨n, hn1, hn2⟩ := (hν.frequently hnhds |>.and_eventually
    (show ∀ᶠ n in F, P n from (mem_inf_of_right (mem_principal_self _)))).exists
  simp only [hu f n hn2.1] at hn1
  have := hxs n hn2
  rw [dist_comm] at this
  linarith

/-- **Proposition 3.5.6**: `T` is uniquely ergodic iff for every continuous `f` the Birkhoff
averages converge uniformly on `Ω` to a constant. -/
theorem uniquelyErgodic_iff [Nonempty Ω] (hT : Continuous T) :
    UniquelyErgodic T ↔ ∀ f : C(Ω, ℝ), ∃ c : ℝ,
      TendstoUniformly (fun n x => birkhoffAverage ℝ T f n x) (fun _ => c) atTop := by
  constructor
  · rintro ⟨μ, hμ⟩ f
    exact ⟨_, tendstoUniformly_of_uniquelyErgodic hT hμ f⟩
  · intro h
    choose c hc using h
    exact uniquelyErgodic_of_tendsto hT fun f x => (hc f).tendsto_at x

/-! ### Furman's theorem and the ergodic decomposition (stated) -/

/-- **Theorem 3.5.8** (Furman). If `T` is uniquely ergodic with invariant measure `μ` and the
continuous `f_n` are subadditive, then `limsup f_n(ω)/n ≤ inf_n (1/n) ∫ f_n dμ` uniformly in `ω`:
for every `ε > 0` there is `N` with `f_n(ω)/n < inf_k (1/k) ∫ f_k dμ + ε` for `n ≥ N` and all
`ω` (3.5.12). Proved as `DF.furmanStatement` (`Ch3/FurmanGeneral.lean`). -/
def FurmanStatement : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (S : X → X) (μ : Measure X), Continuous S → invMeasures S = {μ} →
    ∀ f : ℕ → C(X, ℝ), (∀ n m x, 1 ≤ n → 1 ≤ m → f (n + m) x ≤ f n x + f m (S^[n] x)) →
      ∀ ε > (0 : ℝ), ∃ N, ∀ n ≥ N, ∀ x,
        f n x / n < (⨅ k : ℕ, (∫ y, f (k + 1) y ∂μ) / (k + 1)) + ε

/-- **Theorem 3.5.12** (ergodic decomposition). For every `μ ∈ M₁(Ω, T)` there is a unique Borel
probability measure `m` on `M₁(Ω, T)` (viewed inside the space of probability measures) giving
full mass to the ergodic measures and with `∫ g dμ = ∫ (∫ g dν) dm(ν)` for all continuous `g`.
Stated, not proved. -/
def ErgodicDecompositionStatement : Prop :=
  ∀ (X : Type) [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    (S : X → X), Continuous S → ∀ μ : ProbabilityMeasure X, MeasurePreserving S μ μ →
    ∃! m : ProbabilityMeasure (ProbabilityMeasure X),
      (m : Measure (ProbabilityMeasure X)) {ν | ¬ Ergodic S (ν : Measure X)} = 0 ∧
      (∀ g : C(X, ℝ), ∫ x, g x ∂(μ : Measure X) =
        ∫ ν, (∫ x, g x ∂(ν : Measure X)) ∂(m : Measure (ProbabilityMeasure X)))

end DF
