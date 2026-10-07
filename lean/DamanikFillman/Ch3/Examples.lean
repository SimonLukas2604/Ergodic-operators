/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §3.2 Definitions and examples; examples from §3.5 and §3.6

Definitions (Examples 3.2.2–3.2.12): circle rotations `DF.rotation`, the skew-shift
`DF.skewShift`, expanding maps `DF.expandingMap`, the cat map `DF.catMap`, the bilateral and
unilateral shifts `DF.shiftZ`, `DF.shiftN`, subshifts `DF.IsSubshift`, cylinder sets
`DF.cylinder`, topological Markov chains `DF.markovSubshift`. Ergodicity (Definition 3.2.13) is
Mathlib's `Ergodic`.

Main results:
* `DF.ergodic_rotation_iff` — **Theorem 3.2.14** for `d = 1`: the rotation by `α` is
  Lebesgue-ergodic iff `α` is irrational;
* `DF.ergodic_expandingMap` — **Theorem 3.2.18** (from Mathlib's `AddCircle.ergodic_nsmul`);
* `DF.isSubshift_markovSubshift` — topological Markov chains are subshifts (Example 3.2.12);
* `DF.rotation_invMeasures` — **Proposition 3.5.9**: an irrational rotation is uniquely ergodic
  with Lebesgue measure as its unique invariant measure (via Weyl's equidistribution theorem from
  `AnalyticPerturbationsAMO.Equidistribution`);
* `DF.rotation_minimal` — **Theorem 3.6.6(a)** for `d = 1`.

Statements: `DF.TorusTranslationErgodicStatement` (Theorem 3.2.14 for general `d`; **proved** in
`DamanikFillman.Ch3.TorusErgodic`, `DF.torusTranslationErgodic`), `DF.SkewShiftErgodicStatement`
(Theorem 3.2.15; **proved** in `DamanikFillman.Ch3.SkewShiftErgodic`, `DF.skewShiftErgodic`),
`DF.CatMapErgodicStatement` (Theorem 3.2.16, stated only), `DF.BernoulliShiftErgodicStatement`
(Theorem 3.2.17; **proved** in `DamanikFillman.Ch3.Bernoulli`, `DF.bernoulliShiftErgodic`),
`DF.SkewProductUniquelyErgodicStatement` (Lemma 3.5.10; **proved** in
`DamanikFillman.Ch3.SkewProduct`, `DF.skewProductUniquelyErgodic`) and
`DF.SkewShiftUniquelyErgodicStatement` (Theorem 3.5.11(b); **proved** in
`DamanikFillman.Ch3.SkewProduct`, `DF.skewShiftUniquelyErgodic`).
-/
import DamanikFillman.Ch3.Minimal
import AnalyticPerturbationsAMO.Equidistribution

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Set Function Topology

namespace DF

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨UnitAddCircle.measure_univ⟩

/-! ### Translations, skew-shifts, expanding maps, the cat map -/

/-- Example 3.2.3 (`d = 1`): the rotation `ω ↦ ω + α` of the circle `𝕋 = ℝ/ℤ`. -/
def rotation (α : ℝ) : UnitAddCircle → UnitAddCircle := fun x => x + α

/-- Example 3.2.3: the translation `ω ↦ ω + α` of the torus `𝕋^d`. -/
def torusTranslation {d : ℕ} (α : Fin d → ℝ) : (Fin d → UnitAddCircle) → (Fin d → UnitAddCircle) :=
  fun x i => x i + α i

/-- Example 3.2.6: the skew-shift `(ω₁, ω₂) ↦ (ω₁ + α, ω₁ + ω₂)` on `𝕋²`. -/
def skewShift (α : ℝ) : UnitAddCircle × UnitAddCircle → UnitAddCircle × UnitAddCircle :=
  fun x => (x.1 + α, x.1 + x.2)

/-- Example 3.2.7: the expanding map `ω ↦ m ω` of the circle. -/
def expandingMap (m : ℕ) : UnitAddCircle → UnitAddCircle := fun x => m • x

/-- Example 3.2.8: Arnold's cat map `(ω₁, ω₂) ↦ (2ω₁ + ω₂, ω₁ + ω₂)` on `𝕋²`. -/
def catMap : UnitAddCircle × UnitAddCircle → UnitAddCircle × UnitAddCircle :=
  fun x => (2 • x.1 + x.2, x.1 + x.2)

lemma irrational_iff_addOrderOf (α : ℝ) : Irrational α ↔ addOrderOf (α : UnitAddCircle) = 0 := by
  rw [addOrderOf_eq_zero_iff, AddCircle.not_isOfFinAddOrder_iff_forall_rat_ne_div, div_one]
  simp only [Irrational, mem_range, not_exists]

/-- **Theorem 3.2.14** (`d = 1`): Lebesgue measure is ergodic for the rotation by `α` iff `α` is
irrational (i.e. `1, α` are rationally independent). -/
theorem ergodic_rotation_iff (α : ℝ) : Ergodic (rotation α) volume ↔ Irrational α := by
  rw [irrational_iff_addOrderOf]
  exact AddCircle.ergodic_add_right

/-- **Theorem 3.2.18**: for `m ≥ 2`, Lebesgue measure is ergodic for `ω ↦ mω`. -/
theorem ergodic_expandingMap {m : ℕ} (hm : 2 ≤ m) : Ergodic (expandingMap m) volume :=
  AddCircle.ergodic_nsmul hm

/-- **Theorem 3.2.14** for general `d`: Lebesgue measure on `𝕋^d` is ergodic for the
translation by `α` iff `1, α₁, …, α_d` are rationally independent. Proved in `DF.torusTranslationErgodic`. -/
def TorusTranslationErgodicStatement : Prop :=
  ∀ (d : ℕ) (α : Fin d → ℝ), Ergodic (torusTranslation α) volume ↔
    ∀ (k₀ : ℤ) (k : Fin d → ℤ), (k₀ : ℝ) = ∑ i, k i * α i → k₀ = 0 ∧ ∀ i, k i = 0

/-- **Theorem 3.2.15**: for irrational `α`, Lebesgue measure on `𝕋²` is ergodic for the
skew-shift. Proved in `DF.skewShiftErgodic`. -/
def SkewShiftErgodicStatement : Prop :=
  ∀ α : ℝ, Irrational α → Ergodic (skewShift α) volume

/-- **Theorem 3.2.16**: Lebesgue measure on `𝕋²` is ergodic for the cat map. Stated, not
proved. -/
def CatMapErgodicStatement : Prop := Ergodic catMap volume

/-! ### Shifts and subshifts -/

/-- Example 3.2.9: the bilateral shift `(Tω)_n = ω_{n+1}` on `A^ℤ`. -/
def shiftZ {A : Type*} (ω : ℤ → A) : ℤ → A := fun n => ω (n + 1)

/-- Example 3.2.10: the unilateral shift `(Tω)_n = ω_{n+1}` on `A^ℕ`. -/
def shiftN {A : Type*} (ω : ℕ → A) : ℕ → A := fun n => ω (n + 1)

/-- **Theorem 3.2.17**: the shifts on `A^ℤ` and `A^ℕ` are ergodic with respect to the product
measures `ν^ℤ`, `ν^ℕ`. Proved in `DF.bernoulliShiftErgodic`. -/
def BernoulliShiftErgodicStatement : Prop :=
  ∀ (A : Type) [MeasurableSpace A] (ν : Measure A) [IsProbabilityMeasure ν],
    Ergodic (shiftZ (A := A)) (Measure.infinitePi fun _ : ℤ => ν) ∧
      Ergodic (shiftN (A := A)) (Measure.infinitePi fun _ : ℕ => ν)

/-- Example 3.2.11: a *subshift* over the finite alphabet `A` is a compact (i.e. closed)
shift-invariant subset of `A^ℤ` (with the product of the discrete topologies). -/
def IsSubshift {A : Type*} [TopologicalSpace A] (Ω : Set (ℤ → A)) : Prop :=
  IsClosed Ω ∧ shiftZ ⁻¹' Ω = Ω

/-- The cylinder set `Ξ^I_u = {ω : ω_ℓ = u_ℓ, j ≤ ℓ ≤ k}` (3.2.11), for `I = [j, k]` and a word
`u` indexed by `I`. -/
def cylinder {A : Type*} (j k : ℤ) (u : ℤ → A) : Set (ℤ → A) :=
  {ω | ∀ ℓ, j ≤ ℓ → ℓ ≤ k → ω ℓ = u ℓ}

/-- Example 3.2.12: the topological Markov chain `Ω_M = {ω : M_{ω_n, ω_{n+1}} = 1 ∀ n}`
(3.2.12) of a `0/1` transition matrix `M`. -/
def markovSubshift {A : Type*} (M : Matrix A A ℕ) : Set (ℤ → A) :=
  {ω | ∀ n, M (ω n) (ω (n + 1)) = 1}

/-- Example 3.2.12: a topological Markov chain is a subshift. -/
theorem isSubshift_markovSubshift {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    (M : Matrix A A ℕ) : IsSubshift (markovSubshift M) := by
  refine ⟨?_, ?_⟩
  · have : markovSubshift M = ⋂ n : ℤ, {ω : ℤ → A | M (ω n) (ω (n + 1)) = 1} := by
      ext ω; simp [markovSubshift]
    rw [this]
    refine isClosed_iInter fun n => ?_
    have hc : Continuous fun ω : ℤ → A => (ω n, ω (n + 1)) :=
      (continuous_apply n).prodMk (continuous_apply (n + 1))
    exact (isClosed_discrete {p : A × A | M p.1 p.2 = 1}).preimage hc
  · ext ω
    simp only [markovSubshift, mem_preimage, mem_setOf_eq, shiftZ]
    constructor
    · intro h n
      have := h (n - 1)
      simpa using this
    · intro h n
      exact h (n + 1)

/-! ### Unique ergodicity and minimality of irrational rotations -/

lemma rotation_iterate (α t : ℝ) (k : ℕ) :
    (rotation α)^[k] (t : UnitAddCircle) = ((t + k * α : ℝ) : UnitAddCircle) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [iterate_succ_apply', ih, rotation, ← AddCircle.coe_add]
    congr 1
    push_cast
    ring

/-- **Proposition 3.5.9**: an irrational rotation of the circle is uniquely ergodic, and
(normalized) Lebesgue measure is its unique invariant Borel probability measure. -/
theorem rotation_invMeasures {α : ℝ} (hα : Irrational α) :
    invMeasures (rotation α) = {(volume : Measure UnitAddCircle)} := by
  have hT : Continuous (rotation α) := continuous_id.add continuous_const
  have hc : ∀ (f : C(UnitAddCircle, ℝ)) (x : UnitAddCircle),
      Tendsto (fun n => birkhoffAverage ℝ (rotation α) f n x) atTop (𝓝 (∫ y, f y)) := by
    intro f x
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective x
    set g : ℝ → ℝ := fun s => f (s : UnitAddCircle)
    have hg : Continuous g := f.continuous.comp continuous_quotient_mk'
    have hp : Periodic g 1 := fun s => by
      simp only [g]
      congr 1
      exact AddCircle.coe_add_period 1 s
    have hint : ∫ y in (0 : ℝ)..1, g y = ∫ y, f y := by
      have := UnitAddCircle.intervalIntegral_preimage 0 f
      simpa using this
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨n₀, hn₀⟩ := AMO.weyl_uniform_real hα hg hp (half_pos hε)
    refine ⟨n₀, fun n hn => ?_⟩
    have h1 := hn₀ n hn t
    have heq : birkhoffAverage ℝ (rotation α) f n (t : UnitAddCircle) =
        (n : ℝ)⁻¹ * ∑ k ∈ Finset.range n, g (t + k * α) := by
      simp only [birkhoffAverage, birkhoffSum, smul_eq_mul, g]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      show f ((rotation α)^[k] (t : UnitAddCircle)) = f ((t + k * α : ℝ) : UnitAddCircle)
      rw [rotation_iterate]
    rw [Real.dist_eq, heq, ← hint]
    linarith
  obtain ⟨μ, hμ⟩ := uniquelyErgodic_of_tendsto hT hc
  have hvol : (volume : Measure UnitAddCircle) ∈ invMeasures (rotation α) :=
    ⟨measurePreserving_add_right volume (α : UnitAddCircle), inferInstance⟩
  rw [hμ] at hvol ⊢
  rw [hvol]

/-- **Theorem 3.6.6(a)** (`d = 1`): an irrational rotation of the circle is minimal. -/
theorem rotation_minimal {α : ℝ} (hα : Irrational α) :
    IsMinimalSys (Homeomorph.addRight (α : UnitAddCircle)) := by
  have h : invMeasures (Homeomorph.addRight (α : UnitAddCircle)) =
      {(volume : Measure UnitAddCircle)} := rotation_invMeasures hα
  rw [minimal_iff_fullSupport _ h]
  intro U hU hne
  exact hU.measure_pos volume hne

/-- **Lemma 3.5.10**: if `T₁` is uniquely ergodic on the compact metric space `Ω₁` with invariant
measure `μ₁`, `Ω₂` is a compact metrizable abelian group with Haar probability measure `μ₂`, and
`φ : Ω₁ → Ω₂` is continuous, then ergodicity of `μ₁ × μ₂` for the skew-product
`(ω₁, ω₂) ↦ (T₁ω₁, φ(ω₁) + ω₂)` (3.5.15) implies its unique ergodicity. Proved in `DF.skewProductUniquelyErgodic`. -/
def SkewProductUniquelyErgodicStatement : Prop :=
  ∀ (X G : Type) [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]
    [AddCommGroup G] [MetricSpace G] [CompactSpace G] [IsTopologicalAddGroup G] [MeasurableSpace G]
    [BorelSpace G] (T₁ : X → X) (μ₁ : Measure X) (φ : C(X, G)) (μ₂ : Measure G)
    [μ₂.IsAddHaarMeasure] [IsProbabilityMeasure μ₂], Continuous T₁ → invMeasures T₁ = {μ₁} →
    Ergodic (fun p : X × G => (T₁ p.1, φ p.1 + p.2)) (μ₁.prod μ₂) →
    invMeasures (fun p : X × G => (T₁ p.1, φ p.1 + p.2)) = {μ₁.prod μ₂}

/-- **Theorem 3.5.11(b)**: for irrational `α` the skew-shift on `𝕋²` is uniquely ergodic with
Lebesgue measure as unique invariant measure. Proved in `DF.skewShiftUniquelyErgodic`. -/
def SkewShiftUniquelyErgodicStatement : Prop :=
  ∀ α : ℝ, Irrational α → invMeasures (skewShift α) = {volume}

end DF
