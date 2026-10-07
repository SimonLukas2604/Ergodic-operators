/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §3.5 (continued): generic points and existence of ergodic measures

Setting: `Ω` a compact metric space with its Borel σ-algebra.

Main results:
* `DF.ae_isGeneric` — **Remark 3.5.7**: if `μ` is `T`-ergodic, then `μ`-a.e. point is
  `μ`-generic, i.e. the Birkhoff averages of *every* continuous function converge to its
  integral (the quantifiers are reversed using separability of `C(Ω)`, cf. the remark after
  Theorem 3.9.2);
* `DF.ergMeasures_nonempty` — **Proposition 3.5.3(b)**, second half: `E₁(Ω, T) ≠ ∅`.

Deviation: instead of the Krein–Milman theorem we produce an extreme point of `M₁(Ω, T)` by
successively maximising `ν ↦ ∫ gₖ dν` over a countable dense family `(gₖ)` of `C(Ω)` (a nested
sequence of nonempty compact faces); any measure in the intersection is extreme, hence ergodic by
`DF.ergodic_iff_mem_extremePoints`. This proves `DF.ErgodicMeasureExistsStatement`
(`DF.ergodicMeasureExists`).
-/
import DamanikFillman.Ch3.TopErgodic

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Set Function Topology
open scoped ENNReal

namespace DF

variable {Ω : Type*} [MetricSpace Ω] [CompactSpace Ω] [MeasurableSpace Ω] [BorelSpace Ω]
  {T : Ω → Ω}

lemma integrable_continuousMap (μ : Measure Ω) [IsFiniteMeasure μ] (f : C(Ω, ℝ)) :
    Integrable f μ :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

lemma abs_integral_sub_le (μ : Measure Ω) [IsProbabilityMeasure μ] (f g : C(Ω, ℝ)) :
    |∫ x, f x ∂μ - ∫ x, g x ∂μ| ≤ dist f g := by
  rw [← integral_sub (integrable_continuousMap μ f) (integrable_continuousMap μ g)]
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => f x - g x) (C := dist f g)
    (Eventually.of_forall fun x => by
      rw [← dist_eq_norm]; exact ContinuousMap.dist_apply_le_dist x)
  rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this

lemma abs_birkhoffAverage_sub_le (f g : C(Ω, ℝ)) (n : ℕ) (x : Ω) :
    |birkhoffAverage ℝ T f n x - birkhoffAverage ℝ T g n x| ≤ dist f g := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [dist_nonneg]
  rw [Birkhoff.birkhoffAverage_eq_div, Birkhoff.birkhoffAverage_eq_div, ← sub_div, abs_div,
    Nat.abs_cast, div_le_iff₀ (by exact_mod_cast hn)]
  simp only [birkhoffSum, ← Finset.sum_sub_distrib]
  calc |∑ k ∈ Finset.range n, (f (T^[k] x) - g (T^[k] x))|
      ≤ ∑ k ∈ Finset.range n, |f (T^[k] x) - g (T^[k] x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range n, dist f g := Finset.sum_le_sum fun k _ => by
        rw [← Real.dist_eq]; exact ContinuousMap.dist_apply_le_dist _
    _ = dist f g * n := by simp [mul_comm]

/-- **Remark 3.5.7**: if `μ` is ergodic, then `μ`-a.e. `ω` is `μ`-generic: for every continuous
`f`, `(1/n) ∑_{k<n} f(Tᵏω) → ∫ f dμ` (3.5.10). -/
theorem ae_isGeneric {μ : Measure Ω} [IsProbabilityMeasure μ] (hT : Ergodic T μ) :
    ∀ᵐ x ∂μ, ∀ f : C(Ω, ℝ),
      Tendsto (fun n => birkhoffAverage ℝ T f n x) atTop (𝓝 (∫ y, f y ∂μ)) := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense C(Ω, ℝ)
  have h1 : ∀ᵐ x ∂μ, ∀ g ∈ D,
      Tendsto (fun n => birkhoffAverage ℝ T g n x) atTop (𝓝 (∫ y, g y ∂μ)) :=
    (ae_ball_iff hDc).2 fun g _ => birkhoff_ergodic_tendsto hT (integrable_continuousMap μ g)
  filter_upwards [h1] with x hx f
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

/-! ### Existence of ergodic measures -/

/-- The nested faces: `F₀ = M₁(Ω, T)` and `F_{k+1}` is the set of maximisers of `ν ↦ ∫ gₖ dν`
on `Fₖ`. -/
def faceSeq (T : Ω → Ω) (g : ℕ → C(Ω, ℝ)) : ℕ → Set (ProbabilityMeasure Ω)
  | 0 => {ν | MeasurePreserving T ν ν}
  | k + 1 => {μ | μ ∈ faceSeq T g k ∧ ∀ ν ∈ faceSeq T g k,
      ∫ x, g k x ∂(ν : Measure Ω) ≤ ∫ x, g k x ∂(μ : Measure Ω)}

lemma faceSeq_succ_subset (g : ℕ → C(Ω, ℝ)) (k : ℕ) : faceSeq T g (k + 1) ⊆ faceSeq T g k :=
  fun _ h => h.1

lemma faceSeq_compact_nonempty [Nonempty Ω] (hT : Continuous T) (g : ℕ → C(Ω, ℝ)) (k : ℕ) :
    IsCompact (faceSeq T g k) ∧ (faceSeq T g k).Nonempty := by
  induction k with
  | zero =>
    refine ⟨isCompact_invProbMeasures hT, ?_⟩
    obtain ⟨μ, hμ, hμp⟩ := invMeasures_nonempty hT
    exact ⟨⟨μ, hμp⟩, hμ⟩
  | succ k ih =>
    have hc : Continuous fun ν : ProbabilityMeasure Ω => ∫ x, g k x ∂(ν : Measure Ω) :=
      ProbabilityMeasure.continuous_integral_continuousMap (X := Ω) (g k)
    have heq : faceSeq T g (k + 1) = faceSeq T g k ∩
        ⋂ ν ∈ faceSeq T g k, {μ | ∫ x, g k x ∂(ν : Measure Ω) ≤ ∫ x, g k x ∂(μ : Measure Ω)} := by
      ext μ; simp [faceSeq]
    refine ⟨?_, ?_⟩
    · rw [heq]
      exact ih.1.inter_right (isClosed_biInter fun ν _ => isClosed_le continuous_const hc)
    · obtain ⟨μ, hμ, hmax⟩ := ih.1.exists_isMaxOn ih.2 hc.continuousOn
      exact ⟨μ, hμ, fun ν hν => hmax hν⟩

/-- **Proposition 3.5.3(b)** (second half): every continuous map of a nonempty compact metric
space has an ergodic invariant Borel probability measure. -/
theorem ergMeasures_nonempty [Nonempty Ω] (hT : Continuous T) : (ergMeasures T).Nonempty := by
  classical
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense C(Ω, ℝ)
  obtain ⟨g, hg⟩ := hDc.exists_eq_range hDd.nonempty
  set F := faceSeq T g
  have hF := faceSeq_compact_nonempty hT g
  obtain ⟨μ, hμ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed F
    (faceSeq_succ_subset g) (fun k => (hF k).2) (hF 0).1 (fun k => (hF k).1.isClosed)
  have hμk : ∀ k, μ ∈ F k := mem_iInter.1 hμ
  set I : ProbabilityMeasure Ω → C(Ω, ℝ) → ℝ := fun ν f => ∫ x, f x ∂(ν : Measure Ω)
  -- integrals determine probability measures, via the dense family `g`
  have hdet : ∀ ν : ProbabilityMeasure Ω, (∀ k, I ν (g k) = I μ (g k)) →
      (ν : Measure Ω) = μ := by
    intro ν hν
    have hlip : ∀ ρ : ProbabilityMeasure Ω, LipschitzWith 1 fun f : C(Ω, ℝ) => I ρ f :=
      fun ρ => LipschitzWith.of_dist_le_mul fun f f' => by
        rw [NNReal.coe_one, one_mul, Real.dist_eq]
        exact abs_integral_sub_le (ρ : Measure Ω) f f'
    have heq : (fun f => I ν f) = fun f => I μ f := by
      refine Continuous.ext_on hDd (hlip ν).continuous (hlip μ).continuous ?_
      rintro f hf
      rw [hg] at hf
      obtain ⟨k, rfl⟩ := hf
      exact hν k
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    exact congrFun heq f.toContinuousMap
  refine ⟨μ, Ergodic.of_mem_extremePoints ?_, inferInstance⟩
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
  -- both `P₁` and `P₂` lie in every face
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

/-- The Statement `DF.ErgodicMeasureExistsStatement` holds. -/
theorem ergodicMeasureExists : ErgodicMeasureExistsStatement :=
  fun _ _ _ _ _ _ _ hS => ergMeasures_nonempty hS

end DF
