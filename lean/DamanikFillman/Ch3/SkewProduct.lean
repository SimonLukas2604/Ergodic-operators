/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Lemma 3.5.10 and Theorem 3.5.11(b): unique ergodicity of skew products  (book §3.5)

Main results:
* `DF.exists_ergodic_maximizer` — for continuous `f`, some ergodic measure maximises `ν ↦ ∫ f dν`
  over `M₁(Ω, T)` (the nested-faces argument of `DF.ergMeasures_nonempty`, started at `f`);
* `DF.invMeasures_eq_singleton_of_ergMeasures` — if `μ` is the only ergodic measure, then `T` is
  uniquely ergodic;
* `DF.skewProductUniquelyErgodic` — **Lemma 3.5.10** (Furstenberg): proof of
  `DF.SkewProductUniquelyErgodicStatement`;
* `DF.skewShiftUniquelyErgodic` — **Theorem 3.5.11(b)**: proof of
  `DF.SkewShiftUniquelyErgodicStatement`.

Proof of Lemma 3.5.10 (as in the book): the set `Gen` of `μ₁ × μ₂`-generic points has full
measure (`DF.ae_isGeneric`) and is invariant under the fibre translations `(x, g) ↦ (x, g + c)`,
which commute with the skew product and preserve `μ₁ × μ₂`. Hence `Gen = A × G` with
`μ₁(A) = 1`. An ergodic invariant `ν` projects to an invariant measure of `T₁`, i.e. to `μ₁`, so
`ν(Gen) = 1`; a point that is generic for both `ν` and `μ₁ × μ₂` forces `ν = μ₁ × μ₂`.
-/
import DamanikFillman.Ch3.Generic
import DamanikFillman.Ch3.SkewShiftErgodic

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Set Function Topology
open scoped ENNReal

namespace DF

section maximizer

variable {Ω : Type*} [MetricSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  {T : Ω → Ω}

/-- Convergence of Birkhoff averages for a dense family of continuous functions implies it for all
continuous functions. -/
lemma tendsto_birkhoffAverage_of_dense {D : Set C(Ω, ℝ)} (hDd : Dense D) (μ : Measure Ω)
    [IsProbabilityMeasure μ] {x : Ω}
    (hx : ∀ g ∈ D, Tendsto (fun n => birkhoffAverage ℝ T g n x) atTop (𝓝 (∫ y, g y ∂μ)))
    (f : C(Ω, ℝ)) :
    Tendsto (fun n => birkhoffAverage ℝ T f n x) atTop (𝓝 (∫ y, f y ∂μ)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨g, hgD, hfg⟩ := hDd.exists_dist_lt f (by positivity : 0 < ε / 3)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 (hx g hgD) (ε / 3) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h2 := hN n hn
  have h3 := abs_birkhoffAverage_sub_le (T := T) f g n x
  have h4 := abs_integral_sub_le μ f g
  rw [Real.dist_eq] at h2 ⊢
  calc |birkhoffAverage ℝ T f n x - ∫ y, f y ∂μ|
      = |(birkhoffAverage ℝ T f n x - birkhoffAverage ℝ T g n x) +
          (birkhoffAverage ℝ T g n x - ∫ y, g y ∂μ) - (∫ y, f y ∂μ - ∫ y, g y ∂μ)| := by ring_nf
    _ ≤ |birkhoffAverage ℝ T f n x - birkhoffAverage ℝ T g n x| +
          |birkhoffAverage ℝ T g n x - ∫ y, g y ∂μ| + |∫ y, f y ∂μ - ∫ y, g y ∂μ| :=
        (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ < ε / 3 + ε / 3 + ε / 3 := by linarith
    _ = ε := by ring

/-- A measure lying in all the nested faces of a family with dense range is ergodic. -/
theorem ergodic_of_mem_faceSeq {g : ℕ → C(Ω, ℝ)} (hg : DenseRange g) {μ : ProbabilityMeasure Ω}
    (hμk : ∀ k, μ ∈ faceSeq T g k) : Ergodic T (μ : Measure Ω) := by
  classical
  set F := faceSeq T g
  set I : ProbabilityMeasure Ω → C(Ω, ℝ) → ℝ := fun ν f => ∫ x, f x ∂(ν : Measure Ω)
  have hdet : ∀ ν : ProbabilityMeasure Ω, (∀ k, I ν (g k) = I μ (g k)) →
      (ν : Measure Ω) = μ := by
    intro ν hν
    have hlip : ∀ ρ : ProbabilityMeasure Ω, LipschitzWith 1 fun f : C(Ω, ℝ) => I ρ f :=
      fun ρ => LipschitzWith.of_dist_le_mul fun f f' => by
        rw [NNReal.coe_one, one_mul, Real.dist_eq]
        exact abs_integral_sub_le (ρ : Measure Ω) f f'
    have heq : (fun f => I ν f) = fun f => I μ f := by
      refine Continuous.ext_on hg (hlip ν).continuous (hlip μ).continuous ?_
      rintro f ⟨k, rfl⟩
      exact hν k
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    exact congrFun heq f.toContinuousMap
  refine Ergodic.of_mem_extremePoints ?_
  refine ⟨⟨hμk 0, inferInstance⟩, ?_⟩
  rintro ν₁ ⟨h₁, hp₁⟩ ν₂ ⟨h₂, hp₂⟩ ⟨a, b, ha, hb, hab, hseg⟩
  set P₁ : ProbabilityMeasure Ω := ⟨ν₁, hp₁⟩
  set P₂ : ProbabilityMeasure Ω := ⟨ν₂, hp₂⟩
  have ha1 : a ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (hab ▸ le_self_add)
  have hb1 : b ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (hab ▸ le_add_self)
  have hab' : a.toReal + b.toReal = 1 := by
    rw [← ENNReal.toReal_add ha1 hb1, hab, ENNReal.toReal_one]
  have ha' : 0 < a.toReal := ENNReal.toReal_pos ha.ne' ha1
  have hb' : 0 < b.toReal := ENNReal.toReal_pos hb.ne' hb1
  have hint : ∀ f : C(Ω, ℝ), I μ f = a.toReal * I P₁ f + b.toReal * I P₂ f := by
    intro f
    simp only [I]
    rw [← hseg, integral_add_measure, integral_smul_measure, integral_smul_measure, smul_eq_mul,
      smul_eq_mul]
    · rfl
    · exact (integrable_continuousMap ν₁ f).smul_measure ha1
    · exact (integrable_continuousMap ν₂ f).smul_measure hb1
  have hmem : ∀ k, P₁ ∈ F k ∧ P₂ ∈ F k := by
    intro k
    induction k with
    | zero => exact ⟨h₁, h₂⟩
    | succ k ih =>
      have hμmax : ∀ ν ∈ F k, I ν (g k) ≤ I μ (g k) := (hμk (k + 1)).2
      have e1 := hμmax P₁ ih.1
      have e2 := hμmax P₂ ih.2
      have e3 := hint (g k)
      have hsum : a.toReal * (I μ (g k) - I P₁ (g k)) + b.toReal * (I μ (g k) - I P₂ (g k)) = 0 := by
        linear_combination (I μ (g k)) * hab' + e3
      have hn1 : 0 ≤ a.toReal * (I μ (g k) - I P₁ (g k)) := mul_nonneg ha'.le (by linarith)
      have hn2 : 0 ≤ b.toReal * (I μ (g k) - I P₂ (g k)) := mul_nonneg hb'.le (by linarith)
      obtain ⟨z1, z2⟩ := (add_eq_zero_iff_of_nonneg hn1 hn2).1 hsum
      have h1 : I P₁ (g k) = I μ (g k) := by
        rcases mul_eq_zero.1 z1 with h | h
        · exact absurd h ha'.ne'
        · linarith
      have h2 : I P₂ (g k) = I μ (g k) := by
        rcases mul_eq_zero.1 z2 with h | h
        · exact absurd h hb'.ne'
        · linarith
      exact ⟨⟨ih.1, fun ν hν => (hμmax ν hν).trans h1.ge⟩,
        ⟨ih.2, fun ν hν => (hμmax ν hν).trans h2.ge⟩⟩
  have hval : ∀ (P : ProbabilityMeasure Ω), (∀ k, P ∈ F k) → ∀ k, I P (g k) = I μ (g k) := by
    intro P hP k
    exact le_antisymm ((hμk (k + 1)).2 P (hP k)) ((hP (k + 1)).2 μ (hμk k))
  exact hdet P₁ (hval P₁ fun k => (hmem k).1)

/-- For continuous `f`, an ergodic measure maximises `ν ↦ ∫ f dν` over `M₁(Ω, T)`. -/
theorem exists_ergodic_maximizer [Nonempty Ω] (hT : Continuous T) (f : C(Ω, ℝ)) :
    ∃ μ ∈ ergMeasures T, ∀ ν ∈ invMeasures T, ∫ x, f x ∂ν ≤ ∫ x, f x ∂μ := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense C(Ω, ℝ)
  obtain ⟨g₀, hg₀⟩ := hDc.exists_eq_range hDd.nonempty
  set g : ℕ → C(Ω, ℝ) := fun k => Nat.casesOn k f g₀ with hgdef
  have hg : DenseRange g := by
    refine Dense.mono ?_ hDd
    rw [hg₀]
    rintro _ ⟨k, rfl⟩
    exact ⟨k + 1, rfl⟩
  have hF := faceSeq_compact_nonempty hT g
  obtain ⟨μ, hμ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (faceSeq T g) (faceSeq_succ_subset g) (fun k => (hF k).2) (hF 0).1
    (fun k => (hF k).1.isClosed)
  have hμk : ∀ k, μ ∈ faceSeq T g k := mem_iInter.1 hμ
  refine ⟨μ, ⟨ergodic_of_mem_faceSeq hg hμk, inferInstance⟩, fun ν hν => ?_⟩
  haveI := hν.2
  exact (hμk 1).2 ⟨ν, hν.2⟩ hν.1

/-- If `μ` is invariant and is the only ergodic measure, then `M₁(Ω, T) = {μ}`. -/
theorem invMeasures_eq_singleton_of_ergMeasures [Nonempty Ω] (hT : Continuous T) {μ : Measure Ω}
    (hμ : μ ∈ invMeasures T) (herg : ∀ ν ∈ ergMeasures T, ν = μ) : invMeasures T = {μ} := by
  refine Set.eq_singleton_iff_unique_mem.2 ⟨hμ, fun ν hν => ?_⟩
  haveI := hμ.2; haveI := hν.2
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have key : ∀ f : C(Ω, ℝ), ∫ x, f x ∂ν ≤ ∫ x, f x ∂μ := by
    intro f
    obtain ⟨ρ, hρ, hmax⟩ := exists_ergodic_maximizer hT f
    rw [← herg ρ hρ]
    exact hmax ν hν
  have h1 := key f.toContinuousMap
  have h2 := key (-f.toContinuousMap)
  simp only [ContinuousMap.neg_apply, integral_neg, neg_le_neg_iff] at h2
  exact le_antisymm h1 h2

end maximizer

/-! ### Lemma 3.5.10 -/

section skew

variable {X G : Type} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
  [AddCommGroup G] [MetricSpace G] [CompactSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G]
  [BorelSpace G]

/-- The skew product `(x, g) ↦ (T₁ x, φ x + g)`. -/
def skewProd (T₁ : X → X) (φ : C(X, G)) (p : X × G) : X × G := (T₁ p.1, φ p.1 + p.2)

/-- The fibre translation `(x, g) ↦ (x, g + c)`. -/
def fibreShift (c : G) (p : X × G) : X × G := (p.1, p.2 + c)

lemma skewProd_fibreShift (T₁ : X → X) (φ : C(X, G)) (c : G) (p : X × G) :
    skewProd T₁ φ (fibreShift c p) = fibreShift c (skewProd T₁ φ p) := by
  simp [skewProd, fibreShift, add_assoc]

lemma iterate_skewProd_fibreShift (T₁ : X → X) (φ : C(X, G)) (c : G) (n : ℕ) (p : X × G) :
    (skewProd T₁ φ)^[n] (fibreShift c p) = fibreShift c ((skewProd T₁ φ)^[n] p) := by
  induction n generalizing p with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply, iterate_succ_apply, skewProd_fibreShift, ih]

lemma continuous_fibreShift (c : G) : Continuous (fibreShift (X := X) c) :=
  continuous_fst.prodMk (continuous_snd.add continuous_const)

/-- Birkhoff averages commute with fibre translations. -/
lemma birkhoffAverage_fibreShift (T₁ : X → X) (φ : C(X, G)) (c : G) (f : C(X × G, ℝ)) (n : ℕ)
    (p : X × G) :
    birkhoffAverage ℝ (skewProd T₁ φ) f n (fibreShift c p) =
      birkhoffAverage ℝ (skewProd T₁ φ) (f.comp ⟨fibreShift c, continuous_fibreShift c⟩) n p := by
  simp only [birkhoffAverage, birkhoffSum, iterate_skewProd_fibreShift, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk]

theorem skewProductUniquelyErgodic : SkewProductUniquelyErgodicStatement := by
  intro X G _ _ _ _ _ _ _ _ _ _ T₁ μ₁ φ μ₂ _ _ hT₁ hμ₁ hE
  set S : X × G → X × G := fun p => (T₁ p.1, φ p.1 + p.2) with hSdef
  have hS : Continuous S := (hT₁.comp continuous_fst).prodMk
    ((φ.continuous.comp continuous_fst).add continuous_snd)
  have hμ₁mem : μ₁ ∈ invMeasures T₁ := by rw [hμ₁]; rfl
  haveI : IsProbabilityMeasure μ₁ := hμ₁mem.2
  haveI : Nonempty X := nonempty_of_isProbabilityMeasure μ₁
  set μ := μ₁.prod μ₂ with hμdef
  have hμmem : μ ∈ invMeasures S := ⟨hE.toMeasurePreserving, inferInstance⟩
  refine invMeasures_eq_singleton_of_ergMeasures hS hμmem fun ν hν => ?_
  haveI := hν.2
  -- the `μ`-generic points
  set Gen : Set (X × G) := {p | ∀ f : C(X × G, ℝ),
    Tendsto (fun n => birkhoffAverage ℝ S f n p) atTop (𝓝 (∫ y, f y ∂μ))} with hGen
  have hGen_ae : ∀ᵐ p ∂μ, p ∈ Gen := ae_isGeneric hE
  -- `Gen` is invariant under fibre translations
  have hshift : ∀ (c : G) (p : X × G), p ∈ Gen → fibreShift c p ∈ Gen := by
    intro c p hp f
    have hfc := hp (f.comp ⟨fibreShift c, continuous_fibreShift c⟩)
    have hmp : MeasurePreserving (fibreShift (X := X) c) μ μ :=
      (MeasurePreserving.id μ₁).prod (measurePreserving_add_right μ₂ c)
    have hemb : MeasurableEmbedding (fibreShift (X := X) c) :=
      ((Homeomorph.refl X).prodCongr (Homeomorph.addRight c)).measurableEmbedding
    have hint : ∫ y, (f.comp ⟨fibreShift c, continuous_fibreShift c⟩) y ∂μ = ∫ y, f y ∂μ :=
      hmp.integral_comp hemb f
    rw [hint] at hfc
    show Tendsto (fun n => birkhoffAverage ℝ (skewProd T₁ φ) f n (fibreShift c p)) atTop _
    simp only [birkhoffAverage_fibreShift]
    exact hfc
  -- `ν` gives full mass to `Gen`
  have hfst : MeasurePreserving Prod.fst ν μ₁ := by
    have hm : Measure.map Prod.fst ν ∈ invMeasures T₁ := by
      refine ⟨⟨hT₁.measurable, ?_⟩, ?_⟩
      · rw [Measure.map_map hT₁.measurable measurable_fst]
        have : T₁ ∘ Prod.fst = Prod.fst ∘ S := rfl
        rw [this, ← Measure.map_map measurable_fst hS.measurable, hν.1.toMeasurePreserving.map_eq]
      · exact ⟨by rw [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ,
          measure_univ]⟩
    rw [hμ₁] at hm
    exact ⟨measurable_fst, hm⟩
  -- `Gen` is measurable
  have hGm : MeasurableSet Gen := by
    obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense C(X × G, ℝ)
    -- reduce to a countable dense family, as in `ae_isGeneric`
    have hGD : Gen = ⋂ f ∈ D, {p | Tendsto (fun n => birkhoffAverage ℝ S f n p) atTop
        (𝓝 (∫ y, f y ∂μ))} := by
      ext p
      simp only [hGen, mem_setOf_eq, mem_iInter]
      constructor
      · intro h f _; exact h f
      · intro h f
        exact tendsto_birkhoffAverage_of_dense hDd μ (fun g hg => h g hg) f
    rw [hGD]
    refine MeasurableSet.biInter hDc fun f _ => measurableSet_tendsto _ fun n => ?_
    change Measurable (((n : ℝ)⁻¹) • birkhoffSum S f n)
    exact (Birkhoff.measurable_birkhoffSum hS.measurable f.continuous.measurable n).const_smul _
  set A : Set X := {x | (x, (0 : G)) ∈ Gen} with hA
  have hGA : Gen = Prod.fst ⁻¹' A := by
    ext ⟨x, g⟩
    simp only [mem_preimage, hA, mem_setOf_eq]
    constructor
    · intro h
      have := hshift (-g) (x, g) h
      simpa [fibreShift] using this
    · intro h
      have := hshift g (x, 0) h
      simpa [fibreShift] using this
  have hAm : MeasurableSet A := by
    have : A = (fun x : X => (x, (0 : G))) ⁻¹' Gen := rfl
    rw [this]
    exact hGm.preimage (measurable_id.prodMk measurable_const)
  have hμA : μ₁ Aᶜ = 0 := by
    have h1 : μ Genᶜ = 0 := ae_iff.1 hGen_ae
    rw [hGA, ← preimage_compl, ← Set.prod_univ, hμdef, Measure.prod_prod, measure_univ,
      mul_one] at h1
    exact h1
  have hνGen : ∀ᵐ p ∂ν, p ∈ Gen := by
    rw [hGA]
    have h0 : ν (Prod.fst ⁻¹' Aᶜ) = 0 := by
      rw [← Measure.map_apply measurable_fst hAm.compl, hfst.map_eq]
      exact hμA
    exact (measure_eq_zero_iff_ae_notMem.1 h0).mono fun p hp => by simpa using hp
  -- a point generic for both measures
  have hboth := (ae_isGeneric hν.1).and hνGen
  obtain ⟨p, hpν, hpμ⟩ := hboth.exists
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  exact tendsto_nhds_unique (hpν f.toContinuousMap) (hpμ f.toContinuousMap)

end skew

/-! ### Theorem 3.5.11(b) -/

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

/-- **Theorem 3.5.11(b)**: for irrational `α` the skew-shift on `𝕋²` is uniquely ergodic, with
Lebesgue measure as its unique invariant measure (Lemma 3.5.10 applied to the irrational rotation,
which is uniquely ergodic by Proposition 3.5.9, and Theorem 3.2.15). -/
theorem skewShiftUniquelyErgodic : SkewShiftUniquelyErgodicStatement := by
  intro α hα
  have hrot : Continuous (rotation α) := continuous_id.add continuous_const
  have hE : Ergodic (fun p : UnitAddCircle × UnitAddCircle =>
      (rotation α p.1, (ContinuousMap.id UnitAddCircle) p.1 + p.2))
      ((volume : Measure UnitAddCircle).prod volume) := by
    have := skewShiftErgodic α hα
    rwa [Measure.volume_eq_prod] at this
  have h := skewProductUniquelyErgodic UnitAddCircle UnitAddCircle (rotation α) volume
    (ContinuousMap.id UnitAddCircle) volume hrot (rotation_invMeasures hα) hE
  rw [Measure.volume_eq_prod]
  exact h

end DF
