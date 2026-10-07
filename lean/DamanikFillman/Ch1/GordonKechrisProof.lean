/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators, I*,
§1.12 (pp. 107–113): proof of the Gordon–Kechris theorem (Theorem 1.12.2).

# Main results

* `DF.exists_weak_subseq` — bounded sequences in a separable Hilbert space have weakly convergent
  subsequences (from the sequential Banach–Alaoglu theorem in Mathlib);
* `DF.measurableSet_exists_eigen` — Lemma 1.12.6(a)/(c) and (1.12.6) (Exercise 1.12.2): the set of
  `ω` for which `A_ω` has an eigenvector in `K ∩ X(ω)^⊥` is measurable, `K` an intersection of two
  closed balls not containing `0`;
* `DF.exists_measurable_minVec` — Lemma 1.12.5/1.12.6(d): measurable choice of the shortest vector;
* `DF.gordonKechris` — Theorem 1.12.2; hence `DF.gordonKechrisStatement_holds`.

# Deviations

* The convex sets used in the construction are intersections of two closed balls (this covers all
  sets used in the book's proof: the balls `B_n` and their intersections with arbitrary closed
  balls).
* In Lemma 1.12.5 we use the selection rule "least `l` such that `B(e_l, 2^{-m})` meets `Z(ω)` and
  `Z(ω)` has no point of norm `≤ ‖e_l‖ - 3 · 2^{-m}`", which avoids measurability of the distance
  function `d(ω)`.
-/
import DamanikFillman.Ch1.GordonKechris

noncomputable section

open MeasureTheory Filter Topology Set Metric

namespace DF

variable {Ω : Type*} [MeasurableSpace Ω]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]

/-! ## Weak sequential compactness -/

/-- Bounded sequences have weakly convergent subsequences. -/
theorem exists_weak_subseq {s : ℕ → H} {R : ℝ} (hs : ∀ n, ‖s n‖ ≤ R) :
    ∃ (ψ : H) (φ : ℕ → ℕ), StrictMono φ ∧
      ∀ v : H, Tendsto (fun k => inner ℂ v (s (φ k))) atTop (𝓝 (inner ℂ v ψ)) := by
  let x : ℕ → WeakDual ℂ H := fun n => StrongDual.toWeakDual (InnerProductSpace.toDual ℂ H (s n))
  have hx : ∀ n, x n ∈ WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℂ H) R := by
    intro n
    simp only [x, mem_preimage, StrongDual.toStrongDual_toWeakDual, mem_closedBall, dist_zero_right,
      LinearIsometryEquiv.norm_map]
    exact hs n
  obtain ⟨a, -, φ, hφ, hlim⟩ := WeakDual.isSeqCompact_closedBall (𝕜 := ℂ) (E := H) (0 : StrongDual ℂ H) R hx
  refine ⟨(InnerProductSpace.toDual ℂ H).symm (WeakDual.toStrongDual a), φ, hφ, fun v => ?_⟩
  have h1 := ((WeakDual.eval_continuous v).tendsto a).comp hlim
  have h2 : a v = inner ℂ ((InnerProductSpace.toDual ℂ H).symm (WeakDual.toStrongDual a)) v := by
    rw [← InnerProductSpace.toDual_apply_apply, LinearIsometryEquiv.apply_symm_apply]; rfl
  rw [h2] at h1
  have h3 := (Complex.continuous_conj.tendsto _).comp h1
  rw [inner_conj_symm] at h3
  refine h3.congr fun k => ?_
  simp [x, Function.comp_def, InnerProductSpace.toDual_apply_apply]

/-- Weak limits of sequences that are eventually close to a closed ball stay in the ball. -/
lemma mem_closedBall_of_weak {s : ℕ → H} {ψ c : H} {ρ : ℝ} {δ : ℕ → ℝ}
    (hw : ∀ v, Tendsto (fun k => inner ℂ v (s k)) atTop (𝓝 (inner ℂ v ψ)))
    (hδ : Tendsto δ atTop (𝓝 0)) (hs : ∀ k, ‖s k - c‖ ≤ ρ + δ k) : ‖ψ - c‖ ≤ ρ := by
  have h1 : Tendsto (fun k => (inner ℂ (ψ - c) (s k - c)).re) atTop
      (𝓝 (inner ℂ (ψ - c) (ψ - c)).re) := by
    have := (hw (ψ - c)).sub (tendsto_const_nhds (x := inner ℂ (ψ - c) c))
    have h' := (Complex.continuous_re.tendsto _).comp this
    simp only [Function.comp_def, ← inner_sub_right] at h'
    exact h'
  have h2 : ∀ k, (inner ℂ (ψ - c) (s k - c)).re ≤ ‖ψ - c‖ * (ρ + δ k) := fun k =>
    (Complex.re_le_norm _).trans ((norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hs k) (norm_nonneg _)))
  have hlim : Tendsto (fun k => ‖ψ - c‖ * (ρ + δ k)) atTop (𝓝 (‖ψ - c‖ * ρ)) := by
    simpa using tendsto_const_nhds.mul (tendsto_const_nhds.add hδ)
  have h3 : (inner ℂ (ψ - c) (ψ - c)).re ≤ ‖ψ - c‖ * ρ := le_of_tendsto_of_tendsto' h1 hlim h2
  have hρ : 0 ≤ ρ := by
    have : Tendsto (fun k => ρ + δ k) atTop (𝓝 ρ) := by simpa using tendsto_const_nhds.add hδ
    exact ge_of_tendsto' this fun k => (norm_nonneg _).trans (hs k)
  have hsq : (inner ℂ (ψ - c) (ψ - c)).re = ‖ψ - c‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]; rfl
  rw [hsq] at h3
  rcases eq_or_lt_of_le (norm_nonneg (ψ - c)) with h | h
  · rw [← h]; exact hρ
  · nlinarith

/-! ## Measurability of the existence of eigenvectors (Lemma 1.12.6, (1.12.6)) -/

/-- The set `Z = {ψ ∈ K : ψ ⊥ χ_j for all j, ψ an eigenvector of A}` (eigenvalue equation only;
for `0 ∉ K` all its elements are genuine eigenvectors). -/
def EigenSet (A : H →L[ℂ] H) (K : Set H) {k : ℕ} (χ : Fin k → H) : Set H :=
  {ψ | ψ ∈ K ∧ (∀ j, inner ℂ ψ (χ j) = 0) ∧ ∃ E : ℝ, A ψ = (E : ℂ) • ψ}

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
lemma vecMeasurable_const (v : H) : VecMeasurable (fun _ : Ω => v) := fun _ => measurable_const

/-- Lemma 1.12.6(a) (with (1.12.6), Exercise 1.12.2): for `K` an intersection of two closed balls
not containing `0`, the set of `ω` such that `A_ω` has an eigenvector in `K ∩ X(ω)^⊥` is
measurable. -/
theorem measurableSet_exists_eigen {A : Ω → H →L[ℂ] H} (hA : WeaklyMeasurable A) {k : ℕ}
    {χ : Fin k → Ω → H} (hχ : ∀ j, VecMeasurable (χ j)) (a c : H) (ρ r : ℝ) :
    MeasurableSet {ω | (EigenSet (A ω) (closedBall a ρ ∩ closedBall c r)
      (fun j => χ j ω)).Nonempty} := by
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq H
  let P : Ω → Prop := fun ω => ∃ R : ℕ, ∀ n : ℕ, ∃ q : ℚ, ∃ i : ℕ,
    |(q : ℝ)| ≤ R ∧ ‖d i - a‖ < ρ + 1 / ((n : ℝ) + 1) ∧ ‖d i - c‖ < r + 1 / ((n : ℝ) + 1) ∧
      ‖A ω (d i) - (q : ℂ) • d i‖ < 1 / ((n : ℝ) + 1) ∧
      ∀ j, ‖inner ℂ (d i) (χ j ω)‖ < 1 / ((n : ℝ) + 1)
  have hP : Measurable P := by
    refine Measurable.exists fun R => Measurable.forall fun n => Measurable.exists fun q =>
      Measurable.exists fun i => measurable_const.and (measurable_const.and
        (measurable_const.and (Measurable.and ?_ (Measurable.forall fun j => ?_))))
    · have hv : VecMeasurable fun ω => A ω (d i) - (q : ℂ) • d i :=
        (hA.vecMeasurable_apply (d i)).sub (vecMeasurable_const _)
      exact measurableSet_setOfPred.1
        (measurableSet_lt (measurable_norm_of_vecMeasurable hv) measurable_const)
    · exact measurableSet_setOfPred.1
        (measurableSet_lt (hχ j (d i)).norm measurable_const)
  convert measurableSet_setOfPred.2 hP using 1
  ext ω
  simp only [mem_ofPred_eq]
  constructor
  · -- an eigenvector gives good approximants
    rintro ⟨ψ, ⟨hψa, hψc⟩, horth, E0, hE⟩
    rw [mem_closedBall, dist_eq_norm] at hψa hψc
    refine ⟨⌈|E0|⌉₊ + 1, fun n => ?_⟩
    set ε : ℝ := 1 / ((n : ℝ) + 1)
    have hε : 0 < ε := by positivity
    set C : ℝ := ‖A ω‖ + ‖ψ‖ + (⌈|E0|⌉₊ + 1 : ℕ) + ∑ j, ‖χ j ω‖ + 1
    have hC : 1 ≤ C := by
      have : 0 ≤ ∑ j, ‖χ j ω‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
      have h2 : (0 : ℝ) ≤ ((⌈|E0|⌉₊ + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
      simp only [C]; linarith [norm_nonneg (A ω), norm_nonneg ψ]
    have hC0 : 0 < C := by linarith
    set δ : ℝ := min (ε / C) 1
    have hδ : 0 < δ := lt_min (by positivity) one_pos
    have hδε : δ * C ≤ ε := by
      calc δ * C ≤ ε / C * C := by gcongr; exact min_le_left _ _
        _ = ε := by field_simp
    have hδ1 : δ ≤ 1 := min_le_right _ _
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show E0 - δ < E0 + δ by linarith)
    obtain ⟨i, hi⟩ := hd.exists_dist_lt ψ hδ
    rw [dist_eq_norm] at hi
    have hqR : |(q : ℝ)| ≤ (⌈|E0|⌉₊ + 1 : ℕ) := by
      have h1 : |E0| ≤ ⌈|E0|⌉₊ := Nat.le_ceil _
      push_cast
      rw [abs_le]; constructor <;> linarith [neg_abs_le E0, le_abs_self E0]
    have hdi : ‖d i - ψ‖ < δ := by rw [norm_sub_rev]; exact hi
    have hsumle : ∀ j, ‖χ j ω‖ ≤ ∑ j, ‖χ j ω‖ := fun j =>
      Finset.single_le_sum (f := fun j => ‖χ j ω‖) (fun j _ => norm_nonneg _) (Finset.mem_univ j)
    refine ⟨q, i, hqR, ?_, ?_, ?_, fun j => ?_⟩
    · calc ‖d i - a‖ ≤ ‖d i - ψ‖ + ‖ψ - a‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ < δ + ρ := by linarith
        _ ≤ ρ + ε := by nlinarith
    · calc ‖d i - c‖ ≤ ‖d i - ψ‖ + ‖ψ - c‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ < δ + r := by linarith
        _ ≤ r + ε := by nlinarith
    · have heq : A ω (d i) - (q : ℂ) • d i =
          A ω (d i - ψ) + ((E0 : ℂ) - q) • ψ + (q : ℂ) • (ψ - d i) := by
        rw [map_sub, hE, sub_smul, smul_sub]; abel
      rw [heq]
      have hq : |E0 - q| < δ := by rw [abs_lt]; constructor <;> linarith
      calc ‖A ω (d i - ψ) + ((E0 : ℂ) - q) • ψ + (q : ℂ) • (ψ - d i)‖
          ≤ ‖A ω (d i - ψ)‖ + ‖((E0 : ℂ) - q) • ψ‖ + ‖(q : ℂ) • (ψ - d i)‖ :=
            norm_add₃_le
        _ ≤ ‖A ω‖ * δ + δ * ‖ψ‖ + (⌈|E0|⌉₊ + 1 : ℕ) * δ := by
            gcongr
            · exact (ContinuousLinearMap.le_opNorm _ _).trans
                (mul_le_mul_of_nonneg_left hdi.le (norm_nonneg _))
            · rw [norm_smul, ← Complex.ofReal_ratCast, ← Complex.ofReal_sub, Complex.norm_real,
                Real.norm_eq_abs]
              exact mul_le_mul_of_nonneg_right hq.le (norm_nonneg _)
            · rw [norm_smul, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs,
                norm_sub_rev]
              exact mul_le_mul hqR hdi.le (norm_nonneg _) (by positivity)
        _ < δ * C := by
            have : 0 ≤ ∑ j, ‖χ j ω‖ := Finset.sum_nonneg fun j _ => norm_nonneg _
            simp only [C]; nlinarith
        _ ≤ ε := hδε
    · have : inner ℂ (d i) (χ j ω) = inner ℂ (d i - ψ) (χ j ω) := by
        rw [inner_sub_left, horth j, sub_zero]
      rw [this]
      calc ‖inner ℂ (d i - ψ) (χ j ω)‖ ≤ ‖d i - ψ‖ * ‖χ j ω‖ := norm_inner_le_norm _ _
        _ ≤ δ * ∑ j, ‖χ j ω‖ := mul_le_mul hdi.le (hsumle j) (norm_nonneg _) hδ.le
        _ < δ * C := by
            apply mul_lt_mul_of_pos_left _ hδ
            simp only [C]; linarith [norm_nonneg (A ω), norm_nonneg ψ]
        _ ≤ ε := hδε
  · -- weak limits of approximants are eigenvectors
    rintro ⟨R, hR⟩
    choose q i hqR hia hic hAq hχq using hR
    set s : ℕ → H := fun n => d (i n)
    have hsb : ∀ n, ‖s n‖ ≤ ‖a‖ + ρ + 1 := by
      intro n
      have h1 := hia n
      have h2 : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
      calc ‖s n‖ = ‖(d (i n) - a) + a‖ := by simp [s]
        _ ≤ ‖d (i n) - a‖ + ‖a‖ := norm_add_le _ _
        _ ≤ ‖a‖ + ρ + 1 := by linarith
    obtain ⟨ψ, φ₁, hφ₁, hw₁⟩ := exists_weak_subseq hsb
    obtain ⟨E, -, φ₂, hφ₂, hE⟩ := tendsto_subseq_of_bounded (x := fun k => ((q (φ₁ k) : ℚ) : ℝ))
      (Metric.isBounded_Icc (-(R : ℝ)) R) (fun k => abs_le.1 (hqR (φ₁ k)))
    set φ := φ₁ ∘ φ₂
    have hφ : StrictMono φ := hφ₁.comp hφ₂
    have hw : ∀ v, Tendsto (fun k => inner ℂ v (s (φ k))) atTop (𝓝 (inner ℂ v ψ)) :=
      fun v => (hw₁ v).comp hφ₂.tendsto_atTop
    have hδ : Tendsto (fun k => 1 / ((φ k : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    refine ⟨ψ, ⟨?_, ?_⟩, fun j => ?_, E, ?_⟩
    · rw [mem_closedBall, dist_eq_norm]
      exact mem_closedBall_of_weak hw hδ fun k => (hia (φ k)).le
    · rw [mem_closedBall, dist_eq_norm]
      exact mem_closedBall_of_weak hw hδ fun k => (hic (φ k)).le
    · -- orthogonality
      have h1 := hw (χ j ω)
      have h2 : Tendsto (fun k => inner ℂ (χ j ω) (s (φ k))) atTop (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_) hδ
        rw [← inner_conj_symm, Complex.norm_conj]; exact (hχq (φ k) j).le
      have := tendsto_nhds_unique h1 h2
      rw [← inner_conj_symm, this, map_zero]
    · -- eigenvalue equation
      have hE' : Tendsto (fun k => ((q (φ k) : ℚ) : ℂ)) atTop (𝓝 (E : ℂ)) := by
        have := (Complex.continuous_ofReal.tendsto _).comp hE
        refine this.congr fun k => ?_
        simp [φ, Function.comp_def]
      have key : ∀ v : H, inner ℂ v (A ω ψ - (E : ℂ) • ψ) = 0 := by
        intro v
        have h1 : Tendsto (fun k => inner ℂ (ContinuousLinearMap.adjoint (A ω) v) (s (φ k)) -
            ((q (φ k) : ℚ) : ℂ) * inner ℂ v (s (φ k))) atTop
            (𝓝 (inner ℂ (ContinuousLinearMap.adjoint (A ω) v) ψ - (E : ℂ) * inner ℂ v ψ)) :=
          (hw _).sub (hE'.mul (hw v))
        have h2 : Tendsto (fun k => inner ℂ (ContinuousLinearMap.adjoint (A ω) v) (s (φ k)) -
            ((q (φ k) : ℚ) : ℂ) * inner ℂ v (s (φ k))) atTop (𝓝 0) := by
          rw [tendsto_zero_iff_norm_tendsto_zero]
          refine squeeze_zero (fun _ => norm_nonneg _) (fun k => ?_)
            (by simpa using hδ.const_mul ‖v‖)
          rw [ContinuousLinearMap.adjoint_inner_left, ← inner_smul_right, ← inner_sub_right]
          exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
            (by simpa [s, one_div] using (hAq (φ k)).le) (norm_nonneg _))
        have := tendsto_nhds_unique h1 h2
        rw [ContinuousLinearMap.adjoint_inner_left, ← inner_smul_right, ← inner_sub_right] at this
        exact this
      have := key (A ω ψ - (E : ℂ) • ψ)
      rw [inner_self_eq_zero, sub_eq_zero] at this
      exact this

/-! ## Shortest vectors (Lemma 1.12.5) -/

open Classical in
/-- The shortest vector of a set (if a shortest vector exists; `0` otherwise). -/
def minVec (S : Set H) : H :=
  if h : ∃ v ∈ S, ∀ w ∈ S, ‖v‖ ≤ ‖w‖ then h.choose else 0

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
lemma minVec_spec {S : Set H} (h : ∃ v ∈ S, ∀ w ∈ S, ‖v‖ ≤ ‖w‖) :
    minVec S ∈ S ∧ ∀ w ∈ S, ‖minVec S‖ ≤ ‖w‖ := by
  rw [minVec, dif_pos h]; exact h.choose_spec

section Agreeable

variable {T : H →L[ℂ] H} {a : H} {ρ : ℝ} {k : ℕ} {χ : Fin k → H}

omit [TopologicalSpace.SeparableSpace H] in
/-- Eigenvectors in an agreeable ball share their eigenvalue. -/
lemma eigen_of_mem_eigenSet (hT : IsSelfAdjoint T)
    (hK : ∀ φ ∈ closedBall a ρ, ∀ ψ ∈ closedBall a ρ, inner ℂ φ ψ ≠ 0)
    {ψ₀ ψ : H} {E₀ : ℝ} (h₀ : ψ₀ ∈ closedBall a ρ) (hE₀ : T ψ₀ = (E₀ : ℂ) • ψ₀)
    (hψ : ψ ∈ EigenSet T (closedBall a ρ) χ) : T ψ = (E₀ : ℂ) • ψ := by
  obtain ⟨hψK, -, E, hE⟩ := hψ
  by_cases hEE : E = E₀
  · rw [hE, hEE]
  · exact absurd (inner_eq_zero_of_eigen hT hE hE₀ hEE) (hK ψ hψK ψ₀ h₀)

omit [TopologicalSpace.SeparableSpace H] in
lemma eigenSet_eq (hT : IsSelfAdjoint T)
    (hK : ∀ φ ∈ closedBall a ρ, ∀ ψ ∈ closedBall a ρ, inner ℂ φ ψ ≠ 0)
    {ψ₀ : H} {E₀ : ℝ} (h₀ : ψ₀ ∈ closedBall a ρ) (hE₀ : T ψ₀ = (E₀ : ℂ) • ψ₀) :
    EigenSet T (closedBall a ρ) χ =
      closedBall a ρ ∩ {ψ | ∀ j, inner ℂ ψ (χ j) = 0} ∩ {ψ | T ψ = (E₀ : ℂ) • ψ} := by
  ext ψ
  constructor
  · intro hψ
    exact ⟨⟨hψ.1, hψ.2.1⟩, eigen_of_mem_eigenSet hT hK h₀ hE₀ hψ⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, E₀, h3⟩

omit [TopologicalSpace.SeparableSpace H] in
lemma convex_closed_eigenSet (hT : IsSelfAdjoint T)
    (hK : ∀ φ ∈ closedBall a ρ, ∀ ψ ∈ closedBall a ρ, inner ℂ φ ψ ≠ 0)
    (hne : (EigenSet T (closedBall a ρ) χ).Nonempty) :
    Convex ℝ (EigenSet T (closedBall a ρ) χ) ∧ IsClosed (EigenSet T (closedBall a ρ) χ) := by
  obtain ⟨ψ₀, h₀, -, E₀, hE₀⟩ := hne
  rw [eigenSet_eq hT hK h₀ hE₀]
  refine ⟨((convex_closedBall a ρ).inter ?_).inter ?_, (isClosed_closedBall.inter ?_).inter ?_⟩
  · intro x hx y hy s t _ _ _ j
    simp only [mem_ofPred_eq] at hx hy
    rw [← Complex.coe_smul, ← Complex.coe_smul, inner_add_left, inner_smul_left, inner_smul_left,
      hx j, hy j]; simp
  · intro x hx y hy s t _ _ _
    simp only [mem_ofPred_eq] at hx hy ⊢
    rw [← Complex.coe_smul, ← Complex.coe_smul, map_add, map_smul, map_smul, hx, hy,
      smul_comm (s : ℂ), smul_comm (t : ℂ), smul_add]
  · simp only [setOf_forall]
    exact isClosed_iInter fun j => isClosed_eq (by fun_prop) continuous_const
  · exact isClosed_eq T.continuous (continuous_const.smul continuous_id)

omit [TopologicalSpace.SeparableSpace H] in
/-- Existence of a shortest vector, and the uniform-convexity estimate
`‖z - v‖² ≤ 2‖z‖² - 2‖v‖²`. -/
lemma exists_min_eigenSet (hT : IsSelfAdjoint T)
    (hK : ∀ φ ∈ closedBall a ρ, ∀ ψ ∈ closedBall a ρ, inner ℂ φ ψ ≠ 0)
    (hne : (EigenSet T (closedBall a ρ) χ).Nonempty) :
    ∃ v ∈ EigenSet T (closedBall a ρ) χ, ∀ w ∈ EigenSet T (closedBall a ρ) χ, ‖v‖ ≤ ‖w‖ := by
  obtain ⟨hconv, hcl⟩ := convex_closed_eigenSet hT hK hne
  let _ : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  obtain ⟨v, hv, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hcl.isComplete hconv (0 : H)
  refine ⟨v, hv, fun w hw => ?_⟩
  have := ciInf_le (f := fun w : EigenSet T (closedBall a ρ) χ => ‖(0 : H) - w‖)
    ⟨0, by rintro _ ⟨x, rfl⟩; exact norm_nonneg _⟩ ⟨w, hw⟩
  rw [← hmin] at this
  simpa using this

omit [TopologicalSpace.SeparableSpace H] in
lemma uniform_convexity (hT : IsSelfAdjoint T)
    (hK : ∀ φ ∈ closedBall a ρ, ∀ ψ ∈ closedBall a ρ, inner ℂ φ ψ ≠ 0)
    {v z : H} (hv : v ∈ EigenSet T (closedBall a ρ) χ)
    (hmin : ∀ w ∈ EigenSet T (closedBall a ρ) χ, ‖v‖ ≤ ‖w‖)
    (hz : z ∈ EigenSet T (closedBall a ρ) χ) : ‖z - v‖ ^ 2 ≤ 2 * ‖z‖ ^ 2 - 2 * ‖v‖ ^ 2 := by
  obtain ⟨hconv, -⟩ := convex_closed_eigenSet hT hK ⟨v, hv⟩
  have hmid : (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • v ∈ EigenSet T (closedBall a ρ) χ :=
    hconv hz hv (by norm_num) (by norm_num) (by norm_num)
  have h1 := hmin _ hmid
  have h2 : ‖(1 / 2 : ℝ) • z + (1 / 2 : ℝ) • v‖ = ‖z + v‖ / 2 := by
    rw [← smul_add, norm_smul]; norm_num; ring
  rw [h2] at h1
  have hpar := parallelogram_law_with_norm ℂ z v
  nlinarith [norm_nonneg v, norm_nonneg (z + v)]

end Agreeable

/-- Lemma 1.12.5 / Lemma 1.12.6(d): the shortest eigenvector in `B ∩ X(ω)^⊥` depends measurably on
`ω` (for an agreeable closed ball `B`). -/
theorem vecMeasurable_minVec {A : Ω → H →L[ℂ] H} (hA : WeaklyMeasurable A)
    (hsa : ∀ ω, IsSelfAdjoint (A ω)) {k : ℕ} {χ : Fin k → Ω → H} (hχ : ∀ j, VecMeasurable (χ j))
    (a : H) (ρ : ℝ) (hK : ∀ φ ∈ closedBall a ρ, ∀ ψ ∈ closedBall a ρ, inner ℂ φ ψ ≠ 0) :
    VecMeasurable fun ω => minVec (EigenSet (A ω) (closedBall a ρ) (fun j => χ j ω)) := by
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq H
  set Z : Ω → Set H := fun ω => EigenSet (A ω) (closedBall a ρ) (fun j => χ j ω)
  have hhit : ∀ (c : H) (r : ℝ), MeasurableSet {ω | (Z ω ∩ closedBall c r).Nonempty} := by
    intro c r
    have : {ω | (Z ω ∩ closedBall c r).Nonempty} =
        {ω | (EigenSet (A ω) (closedBall a ρ ∩ closedBall c r) (fun j => χ j ω)).Nonempty} := by
      ext ω
      simp only [mem_ofPred_eq]
      constructor <;> rintro ⟨ψ, h⟩ <;> refine ⟨ψ, ?_⟩ <;>
        simp only [Z, EigenSet, mem_inter_iff, mem_ofPred_eq] at h ⊢ <;> tauto
    rw [this]; exact measurableSet_exists_eigen hA hχ a c ρ r
  have hΩZ : MeasurableSet {ω | (Z ω).Nonempty} := by
    have : {ω | (Z ω).Nonempty} = {ω | (Z ω ∩ closedBall a ρ).Nonempty} := by
      ext ω
      simp only [mem_ofPred_eq]
      constructor
      · rintro ⟨ψ, hψ⟩; exact ⟨ψ, hψ, hψ.1⟩
      · rintro ⟨ψ, hψ, -⟩; exact ⟨ψ, hψ⟩
    rw [this]; exact hhit a ρ
  set δ : ℕ → ℝ := fun m => (1 / 2 : ℝ) ^ m
  have hδpos : ∀ m, 0 < δ m := fun m => by positivity
  -- the selection condition
  let C : ℕ → ℕ → Ω → Prop := fun m l ω =>
    (Z ω ∩ closedBall (e l) (δ m)).Nonempty ∧ ¬ (Z ω ∩ closedBall 0 (‖e l‖ - 3 * δ m)).Nonempty
  have hCm : ∀ m l, MeasurableSet {ω | C m l ω} := fun m l =>
    (hhit _ _).inter (hhit _ _).compl
  have hmin : ∀ ω, (Z ω).Nonempty → ∃ v ∈ Z ω, ∀ w ∈ Z ω, ‖v‖ ≤ ‖w‖ := fun ω hne =>
    exists_min_eigenSet (hsa ω) hK hne
  have hex : ∀ m ω, (Z ω).Nonempty → ∃ l, C m l ω := by
    intro m ω hne
    obtain ⟨hv, hvmin⟩ := minVec_spec (hmin ω hne)
    set v := minVec (Z ω)
    obtain ⟨l, hl⟩ := he.exists_dist_lt v (hδpos m)
    rw [dist_comm, dist_eq_norm] at hl
    refine ⟨l, ⟨v, hv, by rw [mem_closedBall, dist_eq_norm, norm_sub_rev]; exact hl.le⟩, ?_⟩
    rintro ⟨z, hz, hz'⟩
    rw [mem_closedBall, dist_zero_right] at hz'
    have h1 := hvmin z hz
    have h2 : ‖e l‖ ≤ ‖v‖ + ‖e l - v‖ := by
      calc ‖e l‖ = ‖v + (e l - v)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    have := hδpos m
    linarith
  classical
  let L : ℕ → Ω → ℕ := fun m ω => if h : (Z ω).Nonempty then Nat.find (hex m ω h) else 0
  have hLm : ∀ m, Measurable (L m) := by
    intro m
    refine measurable_to_countable' fun l => ?_
    have : L m ⁻¹' {l} = ({ω | (Z ω).Nonempty} ∩ ({ω | C m l ω} ∩ ⋂ l' ∈ Finset.range l,
        {ω | C m l' ω}ᶜ)) ∪ ({ω | (Z ω).Nonempty}ᶜ ∩ {_ω | l = 0}) := by
      ext ω
      simp only [L, mem_preimage, mem_singleton_iff, mem_union, mem_inter_iff, mem_ofPred_eq,
        mem_iInter, Finset.mem_range, mem_compl_iff]
      by_cases h : (Z ω).Nonempty
      · rw [dif_pos h, Nat.find_eq_iff]
        simp [h]
      · rw [dif_neg h]; simp [h, eq_comm]
    rw [this]
    refine (hΩZ.inter ((hCm m l).inter (MeasurableSet.biInter (to_countable _) fun l' _ =>
      (hCm m l').compl))).union (hΩZ.compl.inter (MeasurableSet.const _))
  -- convergence of the approximants
  have hconv : ∀ ω, (Z ω).Nonempty →
      Tendsto (fun m => e (L m ω)) atTop (𝓝 (minVec (Z ω))) := by
    intro ω hne
    obtain ⟨hv, hvmin⟩ := minVec_spec (hmin ω hne)
    set v := minVec (Z ω)
    set g : ℕ → ℝ := fun m => δ m + Real.sqrt (2 * ((‖v‖ + 4 * δ m) ^ 2 - ‖v‖ ^ 2))
    have hg : Tendsto g atTop (𝓝 0) := by
      have hδ0 : Tendsto δ atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      have : Continuous fun t : ℝ => t + Real.sqrt (2 * ((‖v‖ + 4 * t) ^ 2 - ‖v‖ ^ 2)) := by
        fun_prop
      have h2 : Tendsto g atTop
          (𝓝 (0 + Real.sqrt (2 * ((‖v‖ + 4 * 0) ^ 2 - ‖v‖ ^ 2)))) := (this.tendsto 0).comp hδ0
      have h3 : (0 : ℝ) + Real.sqrt (2 * ((‖v‖ + 4 * 0) ^ 2 - ‖v‖ ^ 2)) = 0 := by simp
      rwa [h3] at h2
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun m => ?_) hg
    have hC := Nat.find_spec (hex m ω hne)
    have hLeq : L m ω = Nat.find (hex m ω hne) := by simp only [L, dif_pos hne]
    rw [← hLeq] at hC
    obtain ⟨⟨z, hz, hzl⟩, hno⟩ := hC
    rw [mem_closedBall, dist_eq_norm] at hzl
    have hvlow : ‖e (L m ω)‖ - 3 * δ m < ‖v‖ := by
      by_contra hh; push Not at hh
      exact hno ⟨v, hv, by rw [mem_closedBall, dist_zero_right]; exact hh⟩
    have hzn : ‖z‖ ≤ ‖v‖ + 4 * δ m := by
      have : ‖z‖ ≤ ‖e (L m ω)‖ + ‖z - e (L m ω)‖ := by
        calc ‖z‖ = ‖e (L m ω) + (z - e (L m ω))‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      linarith
    have huc := uniform_convexity (hsa ω) hK hv hvmin hz
    have hzv : ‖z - v‖ ≤ Real.sqrt (2 * ((‖v‖ + 4 * δ m) ^ 2 - ‖v‖ ^ 2)) := by
      apply Real.le_sqrt_of_sq_le
      have : ‖z‖ ^ 2 ≤ (‖v‖ + 4 * δ m) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzn 2
      linarith
    calc ‖e (L m ω) - v‖ ≤ ‖e (L m ω) - z‖ + ‖z - v‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ g m := by
          simp only [g]; rw [norm_sub_rev] at hzl; linarith
  -- conclude
  intro ψ
  have hmeasG : ∀ m, Measurable fun ω =>
      if (Z ω).Nonempty then inner ℂ ψ (e (L m ω)) else 0 := by
    intro m
    refine Measurable.ite hΩZ ?_ measurable_const
    exact (measurable_from_nat (f := fun l => inner ℂ ψ (e l))).comp (hLm m)
  refine measurable_of_tendsto_metrizable hmeasG (tendsto_pi_nhds.2 fun ω => ?_)
  by_cases hne : (Z ω).Nonempty
  · simp only [if_pos hne]
    exact ((continuous_const.inner continuous_id).tendsto _).comp (hconv ω hne)
  · simp only [if_neg hne]
    have : minVec (Z ω) = 0 := by
      rw [minVec, dif_neg]
      rintro ⟨v, hv, -⟩; exact hne ⟨v, hv⟩
    simp only [Z] at this
    rw [this, inner_zero_right]
    exact tendsto_const_nhds

/-! ## The construction (proof of Theorem 1.12.2) -/

/-- `Z = {ψ ∈ B : ψ ⊥ v_i (i < k), ψ an eigenvector}` with the vectors given as a sequence. -/
def EigenSetN (T : H →L[ℂ] H) (B : Set H) (k : ℕ) (v : ℕ → H) : Set H :=
  {ψ | ψ ∈ B ∧ (∀ i < k, inner ℂ ψ (v i) = 0) ∧ ∃ E : ℝ, T ψ = (E : ℂ) • ψ}

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
lemma eigenSetN_eq (T : H →L[ℂ] H) (B : Set H) (k : ℕ) (v : ℕ → H) :
    EigenSetN T B k v = EigenSet T B (fun i : Fin k => v i) := by
  ext ψ
  simp only [EigenSetN, EigenSet, mem_ofPred_eq, Fin.forall_iff]

/-- Normalization. -/
def nvec (z : H) : H := ((‖z‖ : ℂ))⁻¹ • z

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
lemma norm_nvec {z : H} (hz : z ≠ 0) : ‖nvec z‖ = 1 := by
  rw [nvec, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
    inv_mul_cancel₀ (norm_ne_zero_iff.2 hz)]

open Classical in
/-- One step of the construction: if `A` has an eigenvector in `B ∩ X^⊥`, append the normalized
shortest one. -/
def gkStep (T : H →L[ℂ] H) (B : Set H) (st : ℕ × (ℕ → H)) : ℕ × (ℕ → H) :=
  if (EigenSetN T B st.1 st.2).Nonempty then
    (st.1 + 1, Function.update st.2 st.1 (nvec (minVec (EigenSetN T B st.1 st.2))))
  else st

/-- The state `(k_n, (ϕ_1, …, ϕ_{k_n}))` after `n` steps. -/
def gkState (T : H →L[ℂ] H) (u : ℕ → H) : ℕ → ℕ × (ℕ → H)
  | 0 => (0, fun _ => 0)
  | n + 1 => gkStep T (closedBall (u n) (1 / 2)) (gkState T u n)

section Pointwise

variable (T : H →L[ℂ] H) (u : ℕ → H)

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
lemma gkState_succ (n : ℕ) : gkState T u (n + 1) =
    gkStep T (closedBall (u n) (1 / 2)) (gkState T u n) := rfl

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
lemma count_succ_le (n : ℕ) : (gkState T u (n + 1)).1 ≤ (gkState T u n).1 + 1 := by
  rw [gkState_succ, gkStep]; split_ifs <;> simp

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
lemma count_mono : Monotone fun n => (gkState T u n).1 := by
  refine monotone_nat_of_le_succ fun n => ?_
  simp only [gkState_succ, gkStep]; split_ifs <;> simp

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
lemma stable_succ {n i : ℕ} (hi : i < (gkState T u n).1) :
    (gkState T u (n + 1)).2 i = (gkState T u n).2 i := by
  simp only [gkState_succ, gkStep]
  split_ifs
  · simp [Function.update_of_ne hi.ne]
  · rfl

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
lemma stable_le {n n' i : ℕ} (hn : n ≤ n') (hi : i < (gkState T u n).1) :
    (gkState T u n').2 i = (gkState T u n).2 i := by
  induction n', hn using Nat.le_induction with
  | base => rfl
  | succ m hm ih =>
    rw [stable_succ T u (lt_of_lt_of_le hi (count_mono T u hm)), ih]

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
lemma unchanged_succ {n j : ℕ} (hj : (gkState T u (n + 1)).1 ≤ j) :
    (gkState T u (n + 1)).2 j = (gkState T u n).2 j := by
  revert hj
  simp only [gkState_succ, gkStep]
  split_ifs
  · intro hj
    simp only at hj
    simp [Function.update_of_ne (show j ≠ (gkState T u n).1 by omega)]
  · intro _; rfl

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
/-- Each entry of the state is eventually constant. -/
lemma eventually_const (j : ℕ) :
    ∃ n₀, ∀ n ≥ n₀, (gkState T u n).2 j = (gkState T u n₀).2 j := by
  by_cases h : ∃ n₀, j < (gkState T u n₀).1
  · obtain ⟨n₀, hn₀⟩ := h
    exact ⟨n₀, fun n hn => stable_le T u hn hn₀⟩
  · push Not at h
    refine ⟨0, fun n _ => ?_⟩
    induction n with
    | zero => rfl
    | succ m ih => rw [unchanged_succ T u (h (m + 1)), ih (Nat.zero_le _)]

/-- The final vectors `ϕ_{j+1} = lim_n (state n)_j`. -/
def finVec (j : ℕ) : H := limUnder atTop fun n => (gkState T u n).2 j

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
lemma tendsto_finVec (j : ℕ) :
    Tendsto (fun n => (gkState T u n).2 j) atTop (𝓝 (finVec T u j)) := by
  obtain ⟨n₀, h⟩ := eventually_const T u j
  have ht : Tendsto (fun n => (gkState T u n).2 j) atTop (𝓝 ((gkState T u n₀).2 j)) :=
    tendsto_atTop_of_eventually_const h
  rwa [finVec, ht.limUnder_eq]

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
lemma finVec_eq {n j : ℕ} (hj : j < (gkState T u n).1) : finVec T u j = (gkState T u n).2 j := by
  have ht : Tendsto (fun n => (gkState T u n).2 j) atTop (𝓝 ((gkState T u n).2 j)) :=
    tendsto_atTop_of_eventually_const fun n' hn' => stable_le T u hn' hj
  exact tendsto_nhds_unique (tendsto_finVec T u j) ht

/-- The eigenvalue attached to `finVec i`. -/
def finE (i : ℕ) : ℝ := (inner ℂ (finVec T u i) (T (finVec T u i))).re

/-- `N = sup_n k_n`. -/
def gkCount : ℕ∞ := ⨆ n, ((gkState T u n).1 : ℕ∞)

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
lemma le_gkCount_iff (m : ℕ) : (m : ℕ∞) ≤ gkCount T u ↔ ∃ n, m ≤ (gkState T u n).1 := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · exact absurd (hc 0) (by omega)
    have : gkCount T u ≤ ((m - 1 : ℕ) : ℕ∞) :=
      iSup_le fun n => by exact_mod_cast Nat.le_sub_one_of_lt (hc n)
    have := h.trans this
    norm_cast at this
    omega
  · rintro ⟨n, hn⟩
    exact le_iSup_of_le n (by exact_mod_cast hn)

variable {T u}
variable (hT : IsSelfAdjoint T) (hu : ∀ n, ‖u n‖ = 1)
include hT hu

lemma agreeable_ball (n : ℕ) :
    ∀ φ ∈ closedBall (u n) (1 / 2), ∀ ψ ∈ closedBall (u n) (1 / 2), inner ℂ φ ψ ≠ 0 :=
  (isAgreeable_closedBall (hu n)).2.2.2.2

omit hT in
lemma zero_not_mem_ball (n : ℕ) : (0 : H) ∉ closedBall (u n) (1 / 2) := by
  intro h
  rw [mem_closedBall, dist_eq_norm, zero_sub, norm_neg, hu n] at h
  norm_num at h

/-- The minimizer in a nonempty `Z`. -/
lemma minVec_mem {n k : ℕ} {v : ℕ → H}
    (hne : (EigenSetN T (closedBall (u n) (1 / 2)) k v).Nonempty) :
    minVec (EigenSetN T (closedBall (u n) (1 / 2)) k v) ∈
      EigenSetN T (closedBall (u n) (1 / 2)) k v := by
  rw [eigenSetN_eq] at hne ⊢
  exact (minVec_spec (exists_min_eigenSet hT (agreeable_ball hT hu n) hne)).1

/-- Invariants: the constructed vectors are orthonormal eigenvectors. -/
lemma gk_invariant (n : ℕ) :
    (∀ i < (gkState T u n).1, ∀ j < (gkState T u n).1,
      inner ℂ ((gkState T u n).2 i) ((gkState T u n).2 j) = if i = j then 1 else 0) ∧
    (∀ i < (gkState T u n).1, ∃ E : ℝ, T ((gkState T u n).2 i) = (E : ℂ) • (gkState T u n).2 i) := by
  induction n with
  | zero => simp [gkState]
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih
    rw [gkState_succ, gkStep]
    split_ifs with hne
    · set k := (gkState T u n).1
      set v := (gkState T u n).2
      set ζ := minVec (EigenSetN T (closedBall (u n) (1 / 2)) k v)
      obtain ⟨hζB, hζorth, Eζ, hEζ⟩ := minVec_mem hT hu hne
      have hζ0 : ζ ≠ 0 := fun h => zero_not_mem_ball hu n (h ▸ hζB)
      have hw1 : inner ℂ (nvec ζ) (nvec ζ) = 1 := by
        rw [inner_self_eq_norm_sq_to_K, norm_nvec hζ0]; simp
      have hworth : ∀ i < k, inner ℂ (nvec ζ) (v i) = 0 := fun i hi => by
        rw [nvec, inner_smul_left, hζorth i hi, mul_zero]
      refine ⟨fun i hi j hj => ?_, fun i hi => ?_⟩
      · simp only at hi hj
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl <;>
          rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
        · simp only [Function.update_of_ne hi.ne, Function.update_of_ne hj.ne]
          exact ih1 i hi j hj
        · simp only [Function.update_of_ne hi.ne, Function.update_self, if_neg hi.ne]
          rw [← inner_conj_symm, hworth i hi, map_zero]
        · simp only [Function.update_of_ne hj.ne, Function.update_self, if_neg hj.ne']
          exact hworth j hj
        · simp only [Function.update_self, if_pos rfl]; exact hw1
      · simp only at hi
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · simp only [Function.update_of_ne hi.ne]; exact ih2 i hi
        · refine ⟨Eζ, ?_⟩
          show T (Function.update v k (nvec ζ) k) = (Eζ : ℂ) • Function.update v k (nvec ζ) k
          rw [Function.update_self, nvec, map_smul, hEζ, smul_comm]
    · exact ⟨ih1, ih2⟩

lemma finVec_orthonormal {i j : ℕ} (hi : ((i + 1 : ℕ) : ℕ∞) ≤ gkCount T u)
    (hj : ((j + 1 : ℕ) : ℕ∞) ≤ gkCount T u) :
    inner ℂ (finVec T u i) (finVec T u j) = if i = j then 1 else 0 := by
  obtain ⟨n₁, hn₁⟩ := (le_gkCount_iff T u _).1 hi
  obtain ⟨n₂, hn₂⟩ := (le_gkCount_iff T u _).1 hj
  set n := max n₁ n₂
  have hi' : i < (gkState T u n).1 :=
    lt_of_lt_of_le (by omega) ((count_mono T u (le_max_left n₁ n₂)).trans' hn₁)
  have hj' : j < (gkState T u n).1 :=
    lt_of_lt_of_le (by omega) ((count_mono T u (le_max_right n₁ n₂)).trans' hn₂)
  rw [finVec_eq T u hi', finVec_eq T u hj']
  exact (gk_invariant hT hu n).1 i hi' j hj'

lemma finVec_eigen {i : ℕ} (hi : ((i + 1 : ℕ) : ℕ∞) ≤ gkCount T u) :
    T (finVec T u i) = ((inner ℂ (finVec T u i) (T (finVec T u i))).re : ℂ) • finVec T u i := by
  obtain ⟨n, hn⟩ := (le_gkCount_iff T u _).1 hi
  have hi' : i < (gkState T u n).1 := by omega
  obtain ⟨E, hE⟩ := (gk_invariant hT hu n).2 i hi'
  rw [← finVec_eq T u hi'] at hE
  have h1 := finVec_orthonormal hT hu hi hi
  rw [if_pos rfl] at h1
  rw [hE, inner_smul_right, h1, mul_one]
  simp

/-- The key consequence of the construction (Claim 3 of the book): a unit eigenvector cannot be
orthogonal to all constructed vectors. -/
lemma not_orthogonal_all (hdense : ∀ φ : H, ‖φ‖ = 1 → ∃ n, ‖u n - φ‖ ≤ 1 / 2) {φ : H}
    (hφ : ‖φ‖ = 1) {E : ℝ} (hE : T φ = (E : ℂ) • φ)
    (horth : ∀ i, ((i + 1 : ℕ) : ℕ∞) ≤ gkCount T u → inner ℂ φ (finVec T u i) = 0) : False := by
  obtain ⟨n, hn⟩ := hdense φ hφ
  have hφB : φ ∈ closedBall (u n) (1 / 2) := by
    rw [mem_closedBall, dist_eq_norm, norm_sub_rev]; exact hn
  set k := (gkState T u n).1
  set v := (gkState T u n).2
  have hmem : φ ∈ EigenSetN T (closedBall (u n) (1 / 2)) k v := by
    refine ⟨hφB, fun i hi => ?_, E, hE⟩
    have hcount : ((i + 1 : ℕ) : ℕ∞) ≤ gkCount T u :=
      (le_gkCount_iff T u _).2 ⟨n, hi⟩
    show inner ℂ φ ((gkState T u n).2 i) = 0
    rw [← finVec_eq T u hi]
    exact horth i hcount
  have hne : (EigenSetN T (closedBall (u n) (1 / 2)) k v).Nonempty := ⟨φ, hmem⟩
  set ζ := minVec (EigenSetN T (closedBall (u n) (1 / 2)) k v)
  obtain ⟨hζB, -, -⟩ := minVec_mem hT hu hne
  have hstate : gkState T u (n + 1) = (k + 1, Function.update v k (nvec ζ)) := by
    rw [gkState_succ, gkStep, if_pos hne]
  have hk : k < (gkState T u (n + 1)).1 := by rw [hstate]; simp
  have hfin : finVec T u k = nvec ζ := by
    rw [finVec_eq T u hk, hstate]; simp
  have hcount : ((k + 1 : ℕ) : ℕ∞) ≤ gkCount T u :=
    (le_gkCount_iff T u _).2 ⟨n + 1, by rw [hstate]⟩
  have h0 := horth k hcount
  rw [hfin, nvec, inner_smul_right] at h0
  have hζ0 : ζ ≠ 0 := fun h => zero_not_mem_ball hu n (h ▸ hζB)
  have hc : ((‖ζ‖ : ℂ))⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast (norm_ne_zero_iff.2 hζ0))
  rcases mul_eq_zero.1 h0 with h | h
  · exact hc h
  · exact agreeable_ball hT hu n φ hφB ζ hζB h

/-- Claim 3 of the book: the constructed eigenvectors with eigenvalue `λ` span a dense subspace of
the eigenspace `ker (T - λ)`. -/
lemma closure_span_eq_ker (hdense : ∀ φ : H, ‖φ‖ = 1 → ∃ n, ‖u n - φ‖ ≤ 1 / 2) (lam : ℝ) :
    Submodule.topologicalClosure
      (Submodule.span ℂ (finVec T u '' {i | ((i + 1 : ℕ) : ℕ∞) ≤ gkCount T u ∧ lam = finE T u i})) =
      LinearMap.ker ((T - (lam : ℂ) • (1 : H →L[ℂ] H) : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
  set S := finVec T u '' {i | ((i + 1 : ℕ) : ℕ∞) ≤ gkCount T u ∧ lam = finE T u i}
  set Kr := LinearMap.ker ((T - (lam : ℂ) • (1 : H →L[ℂ] H) : H →L[ℂ] H) : H →ₗ[ℂ] H)
  have hSK : Submodule.span ℂ S ≤ Kr := by
    rw [Submodule.span_le]
    rintro _ ⟨i, ⟨hi, hlam⟩, rfl⟩
    simp only [SetLike.mem_coe, Kr, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply]
    rw [finVec_eigen hT hu hi]
    simp only [finE] at hlam
    rw [hlam, sub_self]
  have hKcl : IsClosed (Kr : Set H) :=
    (T - (lam : ℂ) • (1 : H →L[ℂ] H)).isClosed_ker
  have hle : (Submodule.span ℂ S).topologicalClosure ≤ Kr :=
    Submodule.topologicalClosure_minimal _ hSK hKcl
  refine le_antisymm hle fun x hx => ?_
  set W := (Submodule.span ℂ S).topologicalClosure
  have : CompleteSpace W := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  obtain ⟨y, hy, z, hz, rfl⟩ := W.exists_add_mem_mem_orthogonal x
  suffices hz0 : z = 0 by rw [hz0, add_zero]; exact hy
  by_contra hz0
  have hzK : z ∈ Kr := by
    have h1 := Kr.sub_mem hx (hle hy)
    simpa using h1
  have hzE : T z = (lam : ℂ) • z := by
    have := hzK
    simp only [Kr, LinearMap.mem_ker, ContinuousLinearMap.coe_coe, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, sub_eq_zero] at this
    exact this
  refine not_orthogonal_all hT hu hdense (φ := nvec z) (norm_nvec hz0) (E := lam) ?_ ?_
  · rw [nvec, map_smul, hzE, smul_comm]
  · intro i hi
    rw [nvec, inner_smul_left]
    by_cases hlam : lam = finE T u i
    · have hmem : finVec T u i ∈ W :=
        Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, ⟨hi, hlam⟩, rfl⟩)
      have := (Submodule.mem_orthogonal W z).1 hz _ hmem
      rw [← inner_conj_symm, this]; simp
    · have := inner_eq_zero_of_eigen hT hzE (finVec_eigen hT hu hi) hlam
      rw [this, mul_zero]

/-- The number of constructed vectors is the number of eigenvalues counted with multiplicity. -/
lemma eigenCount_eq (hdense : ∀ φ : H, ‖φ‖ = 1 → ∃ n, ‖u n - φ‖ ≤ 1 / 2) :
    eigenCount T = gkCount T u := by
  apply le_antisymm
  · refine iSup₂_le fun n ⟨w, hwo, hwe⟩ => ?_
    rcases eq_or_ne (gkCount T u) ⊤ with htop | htop
    · rw [htop]; exact le_top
    obtain ⟨N₀, hN₀⟩ := ENat.ne_top_iff_exists.1 htop
    set V := Submodule.span ℂ (Set.range fun i : Fin N₀ => finVec T u i)
    have : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
    have hVcl : IsClosed (V : Set H) := Submodule.closed_of_finiteDimensional V
    have hwV : ∀ a, w a ∈ V := by
      intro a
      obtain ⟨E, hE⟩ := hwe a
      have hker : w a ∈ LinearMap.ker
          ((T - (E : ℂ) • (1 : H →L[ℂ] H) : H →L[ℂ] H) : H →ₗ[ℂ] H) := by
        simp [hE]
      rw [← closure_span_eq_ker hT hu hdense E] at hker
      refine Submodule.topologicalClosure_minimal _ ?_ hVcl hker
      rw [Submodule.span_le]
      rintro _ ⟨i, ⟨hi, -⟩, rfl⟩
      rw [← hN₀] at hi
      have hi' : i < N₀ := by exact_mod_cast (show ((i + 1 : ℕ) : ℕ∞) ≤ N₀ from hi)
      exact Submodule.subset_span ⟨⟨i, hi'⟩, rfl⟩
    let w' : Fin n → V := fun a => ⟨w a, hwV a⟩
    have hli : LinearIndependent ℂ w' :=
      LinearIndependent.of_comp V.subtype hwo.linearIndependent
    have h1 := hli.fintype_card_le_finrank
    have h2 := finrank_range_le_card (R := ℂ) (fun i : Fin N₀ => finVec T u i)
    simp only [Fintype.card_fin] at h1 h2
    rw [← hN₀]
    exact_mod_cast h1.trans h2
  · refine iSup_le fun n => ?_
    obtain ⟨h1, h2⟩ := gk_invariant hT hu n
    refine le_iSup₂_of_le (f := fun (m : ℕ) (_ : ∃ v : Fin m → H, Orthonormal ℂ v ∧
      ∀ i, ∃ E : ℝ, T (v i) = (E : ℂ) • v i) => (m : ℕ∞)) (gkState T u n).1
      ⟨fun i => (gkState T u n).2 i, ?_, fun i => h2 i i.2⟩ le_rfl
    rw [orthonormal_iff_ite]
    intro i j
    rw [h1 i i.2 j j.2]
    simp [Fin.ext_iff]

end Pointwise

/-! ## Measurability of the construction -/

omit [CompleteSpace H] [TopologicalSpace.SeparableSpace H] in
lemma vecMeasurable_nvec {z : Ω → H} (hz : VecMeasurable z) (hzn : Measurable fun ω => ‖z ω‖) :
    VecMeasurable fun ω => nvec (z ω) := fun ψ => by
  simp only [nvec, inner_smul_right]
  exact ((Complex.measurable_ofReal.comp hzn).inv).mul (hz ψ)

open Classical in
lemma gkStep_vec_eq (T : H →L[ℂ] H) (B : Set H) (st : ℕ × (ℕ → H)) (j : ℕ) :
    (gkStep T B st).2 j = if (EigenSetN T B st.1 st.2).Nonempty ∧ st.1 = j then
      nvec (minVec (EigenSetN T B j st.2)) else st.2 j := by
  unfold gkStep
  by_cases h : (EigenSetN T B st.1 st.2).Nonempty
  · rw [if_pos h]
    by_cases hj : st.1 = j
    · subst hj; simp [h]
    · simp [h, hj, Function.update_of_ne (Ne.symm hj)]
  · simp [h]

open Classical in
/-- The construction is measurable (Claim 1 of the book). -/
lemma gk_measurable {A : Ω → H →L[ℂ] H} (hA : WeaklyMeasurable A)
    (hsa : ∀ ω, IsSelfAdjoint (A ω)) {u : ℕ → H} (hu : ∀ n, ‖u n‖ = 1) (n : ℕ) :
    Measurable (fun ω => (gkState (A ω) u n).1) ∧
      ∀ j, VecMeasurable (fun ω => (gkState (A ω) u n).2 j) := by
  induction n with
  | zero => exact ⟨measurable_const, fun j => vecMeasurable_const _⟩
  | succ n ih =>
    obtain ⟨hK, hV⟩ := ih
    set B := closedBall (u n) (1 / 2)
    have hZk : ∀ k₀ : ℕ, MeasurableSet
        {ω | (EigenSetN (A ω) B k₀ (gkState (A ω) u n).2).Nonempty} := by
      intro k₀
      have := measurableSet_exists_eigen hA (χ := fun (i : Fin k₀) ω => (gkState (A ω) u n).2 i)
        (fun i => hV i) (u n) (u n) (1 / 2) (1 / 2)
      simp only [inter_self] at this
      convert this using 3 with ω
      rw [eigenSetN_eq]
    have hS : MeasurableSet
        {ω | (EigenSetN (A ω) B (gkState (A ω) u n).1 (gkState (A ω) u n).2).Nonempty} := by
      have : {ω | (EigenSetN (A ω) B (gkState (A ω) u n).1 (gkState (A ω) u n).2).Nonempty} =
          ⋃ k₀ : ℕ, ({ω | (gkState (A ω) u n).1 = k₀} ∩
            {ω | (EigenSetN (A ω) B k₀ (gkState (A ω) u n).2).Nonempty}) := by
        ext ω; simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
        constructor
        · intro h; exact ⟨_, rfl, h⟩
        · rintro ⟨k₀, rfl, h⟩; exact h
      rw [this]
      exact MeasurableSet.iUnion fun k₀ => (hK (measurableSet_singleton k₀)).inter (hZk k₀)
    refine ⟨?_, fun j => ?_⟩
    · have : (fun ω => (gkState (A ω) u (n + 1)).1) = fun ω =>
          if (EigenSetN (A ω) B (gkState (A ω) u n).1 (gkState (A ω) u n).2).Nonempty then
            (gkState (A ω) u n).1 + 1 else (gkState (A ω) u n).1 := by
        ext ω; rw [gkState_succ, gkStep]; split_ifs <;> rfl
      rw [this]
      exact Measurable.ite hS (hK.add_const 1) hK
    · have heq : (fun ω => (gkState (A ω) u (n + 1)).2 j) = fun ω =>
          if (EigenSetN (A ω) B (gkState (A ω) u n).1 (gkState (A ω) u n).2).Nonempty ∧
            (gkState (A ω) u n).1 = j then
            nvec (minVec (EigenSetN (A ω) B j (gkState (A ω) u n).2))
          else (gkState (A ω) u n).2 j := by
        ext ω; rw [gkState_succ, gkStep_vec_eq]
      rw [heq]
      have hmin : VecMeasurable fun ω => minVec (EigenSetN (A ω) B j (gkState (A ω) u n).2) := by
        have := vecMeasurable_minVec hA hsa (χ := fun (i : Fin j) ω => (gkState (A ω) u n).2 i)
          (fun i => hV i) (u n) (1 / 2) (isAgreeable_closedBall (hu n)).2.2.2.2
        convert this using 3 with ω
        rw [eigenSetN_eq]
      have hnv := vecMeasurable_nvec hmin (measurable_norm_of_vecMeasurable hmin)
      intro ψ
      have hset : MeasurableSet {ω | (EigenSetN (A ω) B (gkState (A ω) u n).1
          (gkState (A ω) u n).2).Nonempty ∧ (gkState (A ω) u n).1 = j} :=
        hS.inter (hK (measurableSet_singleton j))
      have : (fun ω => inner ℂ ψ (if (EigenSetN (A ω) B (gkState (A ω) u n).1
          (gkState (A ω) u n).2).Nonempty ∧ (gkState (A ω) u n).1 = j then
            nvec (minVec (EigenSetN (A ω) B j (gkState (A ω) u n).2))
          else (gkState (A ω) u n).2 j)) = fun ω =>
          if (EigenSetN (A ω) B (gkState (A ω) u n).1 (gkState (A ω) u n).2).Nonempty ∧
            (gkState (A ω) u n).1 = j then
            inner ℂ ψ (nvec (minVec (EigenSetN (A ω) B j (gkState (A ω) u n).2)))
          else inner ℂ ψ ((gkState (A ω) u n).2 j) := by
        ext ω; split_ifs <;> rfl
      rw [this]
      exact Measurable.ite hset (hnv ψ) (hV j ψ)

/-! ## Theorem 1.12.2 -/

/-- Theorem 1.12.2 (Gordon–Kechris): a weakly measurable family of bounded self-adjoint operators on
a separable Hilbert space admits a measurable enumeration of eigenelements. -/
theorem gordonKechris {A : Ω → H →L[ℂ] H} (hA : WeaklyMeasurable A)
    (hsa : ∀ ω, IsSelfAdjoint (A ω)) : Nonempty (MeasurableEigenEnumeration A) := by
  by_cases hH : ∃ x : H, x ≠ 0
  · -- a dense sequence of unit vectors
    obtain ⟨x₀, hx₀⟩ := hH
    have : Nonempty (sphere (0 : H) 1) :=
      ⟨⟨nvec x₀, by rw [mem_sphere_zero_iff_norm]; exact norm_nvec hx₀⟩⟩
    obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq (sphere (0 : H) 1)
    set u : ℕ → H := fun n => (d n : H)
    have hu : ∀ n, ‖u n‖ = 1 := fun n => by
      have := (d n).2; rwa [mem_sphere_zero_iff_norm] at this
    have hdense : ∀ φ : H, ‖φ‖ = 1 → ∃ n, ‖u n - φ‖ ≤ 1 / 2 := by
      intro φ hφ
      obtain ⟨n, hn⟩ := hd.exists_dist_lt (⟨φ, by simpa using hφ⟩ : sphere (0 : H) 1)
        (by norm_num : (0 : ℝ) < 1 / 2)
      refine ⟨n, ?_⟩
      rw [← dist_eq_norm, dist_comm]; exact hn.le
    have hmeas := gk_measurable hA hsa hu
    have hϕ : ∀ i, VecMeasurable fun ω => finVec (A ω) u i := by
      intro i ψ
      exact measurable_of_tendsto_metrizable (fun n => (hmeas n).2 i ψ)
        (tendsto_pi_nhds.2 fun ω =>
          ((continuous_const.inner continuous_id).tendsto _).comp (tendsto_finVec (A ω) u i))
    have hcount : ∀ ω, eigenCount (A ω) = gkCount (A ω) u := fun ω =>
      eigenCount_eq (hsa ω) hu hdense
    refine ⟨{
      E := fun m ω => finE (A ω) u (m - 1)
      ϕ := fun m ω => finVec (A ω) u (m - 1)
      measurableSet_count := fun m => ?_
      measurable_E := fun m => ?_
      measurable_ϕ := fun m => hϕ (m - 1)
      eigen := fun m hm ω hω => ?_
      basis := fun ω lam _ => ?_ }⟩
    · simp_rw [hcount, le_gkCount_iff]
      have : {ω | ∃ n, m ≤ (gkState (A ω) u n).1} = ⋃ n, {ω | m ≤ (gkState (A ω) u n).1} := by
        ext; simp
      rw [this]
      exact MeasurableSet.iUnion fun n => (hmeas n).1 measurableSet_Ici
    · exact Complex.measurable_re.comp (measurable_inner_apply hA (hϕ _) (hϕ _))
    · rw [hcount] at hω
      have h1 : ((m - 1 + 1 : ℕ) : ℕ∞) ≤ gkCount (A ω) u := by
        rwa [Nat.sub_add_cancel hm]
      exact finVec_eigen (hsa ω) hu h1
    · rw [hcount ω]
      constructor
      · rw [orthonormal_iff_ite]
        rintro ⟨i, hi1, hiN, -⟩ ⟨j, hj1, hjN, -⟩
        have h1 : ((i - 1 + 1 : ℕ) : ℕ∞) ≤ gkCount (A ω) u := by rwa [Nat.sub_add_cancel hi1]
        have h2 : ((j - 1 + 1 : ℕ) : ℕ∞) ≤ gkCount (A ω) u := by rwa [Nat.sub_add_cancel hj1]
        simp only
        rw [finVec_orthonormal (hsa ω) hu h1 h2]
        congr 1
        simp only [Subtype.mk.injEq, eq_iff_iff]
        omega
      · rw [← closure_span_eq_ker (hsa ω) hu hdense lam]
        congr 2
        ext x
        simp only [mem_range, Subtype.exists, mem_image, mem_setOf_eq]
        constructor
        · rintro ⟨m, ⟨hm1, hmN, hlam⟩, rfl⟩
          exact ⟨m - 1, ⟨by rwa [Nat.sub_add_cancel hm1], hlam⟩, rfl⟩
        · rintro ⟨i, ⟨hiN, hlam⟩, rfl⟩
          exact ⟨i + 1, ⟨by omega, hiN, by simpa using hlam⟩, by simp⟩
  · -- the trivial space
    push Not at hH
    have hcount : ∀ T : H →L[ℂ] H, eigenCount T = 0 := by
      intro T
      refine le_antisymm (iSup₂_le fun n hn' => ?_) bot_le
      obtain ⟨v, hv, -⟩ := hn'
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · exfalso
        have := hv.1 ⟨0, hn⟩
        rw [hH (v ⟨0, hn⟩), norm_zero] at this
        exact zero_ne_one this
    refine ⟨{
      E := fun _ _ => 0
      ϕ := fun _ _ => 0
      measurableSet_count := fun m => by simp only [hcount]; exact MeasurableSet.const _
      measurable_E := fun _ => measurable_const
      measurable_ϕ := fun _ => vecMeasurable_const _
      eigen := fun m hm ω hω => ?_
      basis := fun ω lam h => absurd (hH h.choose) h.choose_spec.1 }⟩
    · rw [hcount] at hω
      exact absurd hω (by simp; omega)

/-- The statement `DF.GordonKechrisStatement` (Theorem 1.12.2) holds. -/
theorem gordonKechrisStatement_holds (Ω : Type*) [MeasurableSpace Ω]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] : GordonKechrisStatement Ω H :=
  fun _ hA hsa => gordonKechris hA hsa

end DF
