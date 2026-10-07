/-
Formalization of Damanik–Fillman, *One-Dimensional Ergodic Schrödinger Operators I*, Chapter 1.

# Singular Weyl sequences and the essential spectrum  (book §1.4, Definition 1.4.23,
Theorem 1.4.24, Corollary 1.4.25, pp. 36–37)

* `DF.IsSingularWeylSequence` — Definition 1.4.23;
* `DF.mem_essSpectrum_iff` — **Theorem 1.4.24**: for self-adjoint `A`, `z ∈ σ_ess(A)` iff there
  is a singular Weyl sequence for `A` at `z`;
* `DF.essSpectrum_add_finiteRank` — **Corollary 1.4.25**: the essential spectrum is invariant
  under self-adjoint finite-rank perturbations.

Auxiliary results: the spectral Chebyshev inequality `DF.measureReal_far_le`, and
`DF.specProj_Ioo_ne_zero` (every spectral point carries spectral mass in each of its
neighbourhoods).

No `Statement` props are introduced in this file.
-/
import DamanikFillman.Ch1.SpectralDecomposition
import DamanikFillman.Ch1.BoundedOperators

noncomputable section

open scoped InnerProductSpace ComplexConjugate Topology
open MeasureTheory Set Filter Metric

namespace DF

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →L[ℂ] H} {hA : IsSelfAdjoint A}

/-- **Definition 1.4.23**: a singular Weyl sequence for `A` at `z`. -/
def IsSingularWeylSequence (A : H →L[ℂ] H) (z : ℂ) (ψ : ℕ → H) : Prop :=
  Orthonormal ℂ ψ ∧ Tendsto (fun n => ‖(A - algebraMap ℂ (H →L[ℂ] H) z) (ψ n)‖) atTop (𝓝 0)

lemma IsSingularWeylSequence.isWeylSequence {z : ℂ} {ψ : ℕ → H}
    (h : IsSingularWeylSequence A z ψ) : IsWeylSequence A z ψ := ⟨h.1.1, h.2⟩

/-! ### Preliminaries -/

lemma algebraMap_real_eq (E : ℝ) :
    algebraMap ℝ (H →L[ℂ] H) E = algebraMap ℂ (H →L[ℂ] H) (E : ℂ) := by
  ext v
  simp [Algebra.algebraMap_eq_smul_one, Complex.coe_smul]

/-- `∫ (x - E)² dμ_ψ = ‖(A - E) ψ‖²`. -/
lemma integral_sq_sub (E : ℝ) (ψ : H) :
    ∫ x, (x - E) ^ 2 ∂(spectralMeasure A hA ψ) =
      ‖(A - algebraMap ℂ (H →L[ℂ] H) (E : ℂ)) ψ‖ ^ 2 := by
  have h := integral_spectralMeasure_re A hA ψ (f := fun x => (x - E) ^ 2) (by fun_prop)
  have hcfc : cfc (fun x : ℝ => (x - E) ^ 2) A = (A - algebraMap ℝ (H →L[ℂ] H) E) ^ 2 := by
    rw [cfc_pow (fun x : ℝ => x - E) 2 A, cfc_sub (fun x : ℝ => x) (fun _ => E) A, cfc_id' ℝ A,
      cfc_const E A]
  rw [h, hcfc, algebraMap_real_eq, pow_two, ContinuousLinearMap.mul_apply]
  set B := A - algebraMap ℂ (H →L[ℂ] H) (E : ℂ)
  have hB : IsSelfAdjoint B := hA.sub (by
    rw [IsSelfAdjoint, ← algebraMap_star_comm, Complex.star_def, Complex.conj_ofReal])
  have hs := hB.isSymmetric ψ (B ψ)
  simp only [ContinuousLinearMap.coe_coe] at hs
  rw [← hs, inner_self_eq_norm_sq_to_K]
  norm_cast

/-- Spectral Chebyshev inequality: `δ² μ_ψ{|x - E| ≥ δ} ≤ ‖(A - E) ψ‖²`. -/
lemma measureReal_far_le (E : ℝ) {δ : ℝ} (hδ : 0 < δ) (ψ : H) :
    δ ^ 2 * (spectralMeasure A hA ψ).real {x | δ ≤ |x - E|} ≤
      ‖(A - algebraMap ℂ (H →L[ℂ] H) (E : ℂ)) ψ‖ ^ 2 := by
  rw [← integral_sq_sub]
  have := mul_meas_ge_le_integral_of_nonneg (μ := spectralMeasure A hA ψ)
    (f := fun x => (x - E) ^ 2) (Eventually.of_forall fun x => sq_nonneg _)
    (integrable_spectralMeasure A hA ψ (by fun_prop)) (δ ^ 2)
  have hset : {x : ℝ | δ ≤ |x - E|} = {x | δ ^ 2 ≤ (x - E) ^ 2} := by
    ext x
    simp only [mem_setOf_eq]
    rw [← sq_abs (x - E)]
    exact (pow_le_pow_iff_left₀ hδ.le (abs_nonneg _) two_ne_zero).symm
  rwa [hset]

lemma specProj_eq_zero_of_disjoint {S : Set ℝ} (hS : MeasurableSet S)
    (h : ∀ x ∈ S, x ∉ spectrum ℝ A) : specProj A hA S = 0 := by
  ext ψ
  rw [ContinuousLinearMap.zero_apply, specProj_apply_eq_zero_iff hS]
  exact measure_mono_null (fun x hx => h x hx) (spectralMeasure_compl_spectrum A hA ψ)

lemma mem_spectrum_real_iff (x : ℝ) : x ∈ spectrum ℝ A ↔ (x : ℂ) ∈ spectrum ℂ A :=
  (spectrum.algebraMap_mem_iff ℂ).symm

/-- Every point of the spectrum carries spectral mass in each of its neighbourhoods. -/
lemma specProj_Ioo_ne_zero [Nontrivial H] {E : ℝ} (hE : (E : ℂ) ∈ spectrum ℂ A) {ε : ℝ}
    (hε : 0 < ε) : specProj A hA (Ioo (E - ε) (E + ε)) ≠ 0 := by
  intro h0
  obtain ⟨ψ, hψ1, hψ⟩ := exists_unit_norm_sub_lt hA (E : ℂ) (ε := ε / 2) (by positivity)
  rw [infDist_zero_of_mem hE, zero_add] at hψ
  have hcheb := measureReal_far_le (hA := hA) E hε ψ
  have hS : {x : ℝ | ε ≤ |x - E|} = (Ioo (E - ε) (E + ε))ᶜ := by
    ext x; simp only [mem_setOf_eq, mem_compl_iff, mem_Ioo, not_and_or, not_lt, le_abs]
    constructor
    · rintro (h | h)
      · right; linarith
      · left; linarith
    · rintro (h | h)
      · right; linarith
      · left; linarith
  have hsum : (spectralMeasure A hA ψ).real (Ioo (E - ε) (E + ε)) +
      (spectralMeasure A hA ψ).real (Ioo (E - ε) (E + ε))ᶜ = 1 := by
    rw [measureReal_add_measureReal_compl measurableSet_Ioo, spectralMeasure_real_univ, hψ1,
      one_pow]
  have hzero : (spectralMeasure A hA ψ).real (Ioo (E - ε) (E + ε)) = 0 := by
    rw [← norm_specProj_apply_sq measurableSet_Ioo, h0, ContinuousLinearMap.zero_apply,
      norm_zero, sq, mul_zero]
  rw [hS] at hcheb
  have : ‖(A - algebraMap ℂ (H →L[ℂ] H) (E : ℂ)) ψ‖ ^ 2 < (ε / 2) ^ 2 :=
    pow_lt_pow_left₀ hψ (norm_nonneg _) two_ne_zero
  nlinarith

/-- An orthonormal sequence tends to zero weakly (Bessel). -/
lemma tendsto_inner_orthonormal {ψ : ℕ → H} (hψ : Orthonormal ℂ ψ) (x : H) :
    Tendsto (fun n => ⟪x, ψ n⟫_ℂ) atTop (𝓝 0) := by
  have hs := hψ.inner_products_summable x
  have h1 := hs.tendsto_atTop_zero
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
  simp only [Function.comp_def, Real.sqrt_zero] at h2
  refine h2.congr fun n => ?_
  rw [Real.sqrt_sq (norm_nonneg _), norm_inner_symm]

/-- A sequence in a finite-dimensional subspace which tends to zero weakly tends to zero. -/
lemma tendsto_zero_of_finiteDimensional {K : Submodule ℂ H} [FiniteDimensional ℂ K]
    {v : ℕ → H} (hv : ∀ n, v n ∈ K) (hw : ∀ k ∈ K, Tendsto (fun n => ⟪k, v n⟫_ℂ) atTop (𝓝 0)) :
    Tendsto v atTop (𝓝 0) := by
  set b := stdOrthonormalBasis ℂ K
  have hsq : ∀ n, ‖v n‖ ^ 2 = ∑ i, ‖⟪(b i : H), v n⟫_ℂ‖ ^ 2 := by
    intro n
    have := b.sum_sq_norm_inner_right ⟨v n, hv n⟩
    exact this.symm
  have h2 : Tendsto (fun n => ‖v n‖ ^ 2) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset (Fin (Module.finrank ℂ K)))
      fun i _ => ((hw (b i) (b i).2).norm).pow 2
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero] at this
    exact this.congr fun n => (hsq n).symm
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h3 := (Real.continuous_sqrt.tendsto 0).comp h2
  simp only [Function.comp_def, Real.sqrt_zero] at h3
  exact h3.congr fun n => Real.sqrt_sq (norm_nonneg _)

/-- Finite-rank operators map orthonormal sequences to null sequences. -/
lemma tendsto_finiteRank_orthonormal {R : H →L[ℂ] H}
    (hR : FiniteDimensional ℂ (LinearMap.range (R : H →ₗ[ℂ] H))) {ψ : ℕ → H}
    (hψ : Orthonormal ℂ ψ) : Tendsto (fun n => R (ψ n)) atTop (𝓝 0) := by
  refine tendsto_zero_of_finiteDimensional (K := LinearMap.range (R : H →ₗ[ℂ] H))
    (fun n => LinearMap.mem_range_self _ _) fun k _ => ?_
  have := tendsto_inner_orthonormal hψ (ContinuousLinearMap.adjoint R k)
  refine this.congr fun n => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]

/-! ### Theorem 1.4.24 -/

/-- **Theorem 1.4.24**, "if" direction: a singular Weyl sequence at `z` forces
`z ∈ σ_ess(A)`. -/
theorem mem_essSpectrum_of_singular (hA : IsSelfAdjoint A) {z : ℂ} {ψ : ℕ → H}
    (hψ : IsSingularWeylSequence A z ψ) : z ∈ essSpectrum A := by
  have hz := mem_spectrum_of_isWeylSequence hψ.isWeylSequence
  refine ⟨hz, ?_⟩
  rintro ⟨-, -, hfin, δ, hδ, hball⟩
  have hzE : z = (z.re : ℂ) := hA.mem_spectrum_eq_re hz
  set E := z.re
  set K := LinearMap.ker ((A - algebraMap ℂ (H →L[ℂ] H) z : H →L[ℂ] H) : H →ₗ[ℂ] H)
  set P := specProj A hA {E}
  set Q := specProj A hA ({E} : Set ℝ)ᶜ
  have hPQ : ∀ v, P v + Q v = v := fun v => by
    have := congrArg (fun T : H →L[ℂ] H => T v)
      (specProj_add_compl (A := A) (hA := hA) (measurableSet_singleton E))
    simpa using this
  -- the far part tends to zero
  have hQ : Tendsto (fun n => Q (ψ n)) atTop (𝓝 0) := by
    have hsub : ∀ n, ‖Q (ψ n)‖ ^ 2 ≤ ‖(A - algebraMap ℂ (H →L[ℂ] H) z) (ψ n)‖ ^ 2 / δ ^ 2 := by
      intro n
      rw [norm_specProj_apply_sq (measurableSet_singleton E).compl, le_div_iff₀ (by positivity),
        mul_comm, hzE]
      refine le_trans ?_ (measureReal_far_le (hA := hA) E hδ (ψ n))
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hsub' : ({E} : Set ℝ)ᶜ ⊆ {x | δ ≤ |x - E|} ∪ (spectrum ℝ A)ᶜ := ?_
      · calc (spectralMeasure A hA (ψ n)).real ({E} : Set ℝ)ᶜ
            ≤ (spectralMeasure A hA (ψ n)).real ({x | δ ≤ |x - E|} ∪ (spectrum ℝ A)ᶜ) :=
              measureReal_mono hsub' (measure_ne_top _ _)
          _ ≤ (spectralMeasure A hA (ψ n)).real {x | δ ≤ |x - E|} +
              (spectralMeasure A hA (ψ n)).real (spectrum ℝ A)ᶜ := measureReal_union_le _ _
          _ = (spectralMeasure A hA (ψ n)).real {x | δ ≤ |x - E|} := by
              rw [measureReal_def (s := (spectrum ℝ A)ᶜ), spectralMeasure_compl_spectrum,
                ENNReal.toReal_zero, add_zero]
      intro x hx
      simp only [mem_union, mem_setOf_eq, mem_compl_iff]
      by_cases hxs : x ∈ spectrum ℝ A
      · left
        by_contra hlt; push Not at hlt
        have hmem : (x : ℂ) ∈ ball z δ ∩ spectrum ℂ A := by
          refine ⟨?_, (mem_spectrum_real_iff x).1 hxs⟩
          rw [mem_ball, hzE, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real]
          exact hlt
        rw [hball, mem_singleton_iff, hzE] at hmem
        exact hx (Complex.ofReal_injective hmem)
      · right; exact hxs
    have h2 : Tendsto (fun n => ‖Q (ψ n)‖ ^ 2) atTop (𝓝 0) := by
      refine squeeze_zero (fun n => sq_nonneg _) hsub ?_
      have := (hψ.2.pow 2).div_const (δ ^ 2)
      simpa using this
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have h3 := (Real.continuous_sqrt.tendsto 0).comp h2
    simp only [Function.comp_def, Real.sqrt_zero] at h3
    exact h3.congr fun n => Real.sqrt_sq (norm_nonneg _)
  -- the eigen-part tends to zero
  have hPK : ∀ v, P v ∈ K := by
    intro v
    simp only [K, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.sub_apply]
    rw [hzE, apply_specProj_singleton E v, Algebra.algebraMap_eq_smul_one,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, sub_self]
  have hP : Tendsto (fun n => P (ψ n)) atTop (𝓝 0) := by
    refine tendsto_zero_of_finiteDimensional (K := K) (fun n => hPK _) fun k hk => ?_
    have hkP : P k = k := by
      rw [← eigen_iff_specProj_singleton]
      have : (A - algebraMap ℂ (H →L[ℂ] H) z) k = 0 := hk
      rw [ContinuousLinearMap.sub_apply, sub_eq_zero, hzE, Algebra.algebraMap_eq_smul_one,
        ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply] at this
      exact this
    refine (tendsto_inner_orthonormal hψ.1 k).congr fun n => ?_
    have hs := (isSelfAdjoint_specProj (A := A) (hA := hA)
      (measurableSet_singleton E)).isSymmetric k (ψ n)
    simp only [ContinuousLinearMap.coe_coe] at hs
    rw [← hs, hkP]
  have hsum : Tendsto (fun n => P (ψ n) + Q (ψ n)) atTop (𝓝 0) := by
    simpa using hP.add hQ
  simp_rw [hPQ] at hsum
  have h1 := hsum.norm
  rw [norm_zero] at h1
  have : (fun n => ‖ψ n‖) = fun _ => (1 : ℝ) := funext fun n => hψ.1.1 n
  rw [this] at h1
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h1)

/-- **Theorem 1.4.24**, "only if" direction. -/
theorem exists_singular_of_mem_essSpectrum [Nontrivial H] (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z ∈ essSpectrum A) :
    ∃ ψ : ℕ → H, IsSingularWeylSequence A z ψ := by
  obtain ⟨hzσ, hzd⟩ := hz
  have hzE : z = (z.re : ℂ) := hA.mem_spectrum_eq_re hzσ
  set E := z.re
  set K := LinearMap.ker ((A - algebraMap ℂ (H →L[ℂ] H) z : H →L[ℂ] H) : H →ₗ[ℂ] H)
  by_cases hfin : FiniteDimensional ℂ K
  · -- `z` is not an isolated point of the spectrum
    have hacc : ∀ r > 0, ∃ x ∈ spectrum ℝ A, 0 < |x - E| ∧ |x - E| < r := by
      intro r hr
      by_contra hno
      push Not at hno
      have hiso : ball z r ∩ spectrum ℂ A = {z} := by
        ext w
        simp only [mem_inter_iff, mem_ball, mem_singleton_iff]
        constructor
        · rintro ⟨hw, hws⟩
          have hwr : w = (w.re : ℂ) := hA.mem_spectrum_eq_re hws
          have hxs : w.re ∈ spectrum ℝ A := (mem_spectrum_real_iff _).2 (hwr ▸ hws)
          have hd : |w.re - E| < r := by
            rw [hwr, hzE, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real] at hw
            exact hw
          have h0 := hno w.re hxs
          have : |w.re - E| = 0 := by
            by_contra hne
            exact absurd hd (not_lt.2 (h0 (lt_of_le_of_ne (abs_nonneg _) (Ne.symm hne))))
          rw [abs_eq_zero, sub_eq_zero] at this
          rw [hwr, this, ← hzE]
        · rintro rfl; exact ⟨mem_ball_self hr, hzσ⟩
      by_cases hker : K = ⊥
      · -- no eigenvectors: the spectral projection of a punctured neighbourhood vanishes
        apply specProj_Ioo_ne_zero (hA := hA) (hzE ▸ hzσ) hr
        have hsplit : Ioo (E - r) (E + r) = {E} ∪ (Ioo (E - r) (E + r) \ {E}) := by
          ext x; simp only [mem_union, mem_singleton_iff, mem_diff]
          constructor
          · intro h; by_cases hx : x = E
            · left; exact hx
            · right; exact ⟨h, hx⟩
          · rintro (rfl | ⟨h, _⟩)
            · constructor <;> linarith
            · exact h
        rw [hsplit, specProj_union (measurableSet_singleton E)
          (measurableSet_Ioo.diff (measurableSet_singleton E)) (by simp)]
        have h1 : specProj A hA {E} = 0 := by
          ext v
          have hmem : specProj A hA {E} v ∈ K := by
            simp only [K, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
              ContinuousLinearMap.sub_apply]
            rw [hzE, apply_specProj_singleton E v, Algebra.algebraMap_eq_smul_one,
              ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, sub_self]
          rw [hker, Submodule.mem_bot] at hmem
          rw [hmem, ContinuousLinearMap.zero_apply]
        have h2 : specProj A hA (Ioo (E - r) (E + r) \ {E}) = 0 := by
          refine specProj_eq_zero_of_disjoint (measurableSet_Ioo.diff (measurableSet_singleton E))
            fun x hx hxs => ?_
          have := hno x hxs
          have hne : 0 < |x - E| := abs_pos.2 (sub_ne_zero.2 hx.2)
          have hlt : |x - E| < r := by
            rw [abs_lt]; constructor <;> linarith [hx.1.1, hx.1.2]
          exact absurd hlt (not_lt.2 (this hne))
        rw [h1, h2, add_zero]
      · exact hzd ⟨hzσ, hker, hfin, r, hr, hiso⟩
    -- construct disjoint spectral windows accumulating at `E`
    have hX : ∀ r : ℝ, ∃ x : ℝ, 0 < r → x ∈ spectrum ℝ A ∧ 0 < |x - E| ∧ |x - E| < r := by
      intro r
      by_cases hr : 0 < r
      · obtain ⟨x, hx⟩ := hacc r hr; exact ⟨x, fun _ => hx⟩
      · exact ⟨0, fun h => absurd h hr⟩
    choose X hXp using hX
    let rr : ℕ → ℝ := fun n => Nat.rec 1 (fun _ r => |X r - E| / 3) n
    have hrr0 : rr 0 = 1 := rfl
    have hrrS : ∀ k, rr (k + 1) = |X (rr k) - E| / 3 := fun k => rfl
    have hrpos : ∀ k, 0 < rr k := by
      intro k; induction k with
      | zero => rw [hrr0]; norm_num
      | succ k ih => rw [hrrS]; exact div_pos (hXp _ ih).2.1 (by norm_num)
    set x : ℕ → ℝ := fun k => X (rr k)
    set d : ℕ → ℝ := fun k => |x k - E|
    have hd0 : ∀ k, 0 < d k := fun k => (hXp _ (hrpos k)).2.1
    have hdr : ∀ k, d k < rr k := fun k => (hXp _ (hrpos k)).2.2
    have hxs : ∀ k, x k ∈ spectrum ℝ A := fun k => (hXp _ (hrpos k)).1
    have hrr_le : ∀ k, rr k ≤ (1 / 3 : ℝ) ^ k := by
      intro k; induction k with
      | zero => rw [hrr0]; norm_num
      | succ k ih =>
        rw [hrrS, pow_succ]
        have := hdr k
        simp only [d, x] at this
        linarith
    have hanti' : ∀ k j, j < k → rr k ≤ d j / 3 := by
      intro k
      induction k with
      | zero => intro j hj; omega
      | succ k ih =>
        intro j hjk
        rcases Nat.lt_succ_iff_lt_or_eq.1 hjk with h | h
        · have h1 := ih j h
          have h2 := hdr k
          have h3 := hrpos k
          have h4 : rr (k + 1) = d k / 3 := hrrS k
          linarith
        · subst h; exact (hrrS j).le
    have hanti : ∀ j k, j < k → rr k ≤ d j / 3 := fun j k h => hanti' k j h
    set U : ℕ → Set ℝ := fun k => Ioo (x k - d k / 3) (x k + d k / 3)
    have hUdisj : ∀ j k, j ≠ k → U j ∩ U k = ∅ := by
      have key : ∀ j k, j < k → U j ∩ U k = ∅ := by
        intro j k hjk
        ext y
        simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
        rintro ⟨⟨h1, h2⟩, h3, h4⟩
        have hk := (hdr k).trans_le (hanti j k hjk)
        -- `|y - E| ≥ 2 d_j/3` on `U j` and `< 4 d_k / 3` on `U k`
        have hyj : 2 * d j / 3 ≤ |y - E| := by
          simp only [d] at h1 h2 ⊢
          rcases le_or_gt 0 (x j - E) with hs | hs
          · rw [abs_of_nonneg hs] at h1 h2 ⊢
            rw [le_abs]; left; linarith
          · rw [abs_of_neg hs] at h1 h2 ⊢
            rw [le_abs]; right; linarith
        have hyk : |y - E| < 4 * d k / 3 := by
          simp only [d] at h3 h4 hk ⊢
          rw [abs_lt]
          rcases le_or_gt 0 (x k - E) with hs | hs
          · rw [abs_of_nonneg hs] at h3 h4 ⊢; constructor <;> linarith
          · rw [abs_of_neg hs] at h3 h4 ⊢; constructor <;> linarith
        have := hd0 j
        linarith
      intro j k hjk
      rcases lt_or_gt_of_ne hjk with h | h
      · exact key j k h
      · rw [inter_comm]; exact key k j h
    have hPne : ∀ k, specProj A hA (U k) ≠ 0 := by
      intro k
      have h := specProj_Ioo_ne_zero (hA := hA) ((mem_spectrum_real_iff _).1 (hxs k))
        (by linarith [hd0 k] : 0 < d k / 3)
      exact h
    have hv : ∀ k, ∃ v : H, specProj A hA (U k) v ≠ 0 := by
      intro k; by_contra hno; push Not at hno
      exact hPne k (ContinuousLinearMap.ext hno)
    choose v hv using hv
    set w : ℕ → H := fun k => specProj A hA (U k) (v k)
    set ψ : ℕ → H := fun k => ((‖w k‖⁻¹ : ℝ) : ℂ) • w k
    have hwpos : ∀ k, 0 < ‖w k‖ := fun k => norm_pos_iff.2 (hv k)
    have hPψ : ∀ k, specProj A hA (U k) (ψ k) = ψ k := by
      intro k
      simp only [ψ, w, map_smul]
      rw [← ContinuousLinearMap.mul_apply, specProj_idem measurableSet_Ioo]
    refine ⟨ψ, ⟨fun k => ?_, fun j k hjk => ?_⟩, ?_⟩
    · simp only [ψ]
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
        inv_mul_cancel₀ (hwpos k).ne']
    · show ⟪ψ j, ψ k⟫_ℂ = 0
      have hs := (isSelfAdjoint_specProj (A := A) (hA := hA) (S := U j)
        measurableSet_Ioo).isSymmetric (ψ j) (specProj A hA (U k) (ψ k))
      simp only [ContinuousLinearMap.coe_coe] at hs
      rw [← hPψ j, ← hPψ k, hs, ← ContinuousLinearMap.mul_apply, specProj_mul measurableSet_Ioo measurableSet_Ioo,
        hUdisj j k hjk, specProj_empty, ContinuousLinearMap.zero_apply, inner_zero_right]
    · -- the Weyl property
      have hbound : ∀ k, ‖(A - algebraMap ℂ (H →L[ℂ] H) z) (ψ k)‖ ^ 2 ≤
          (4 * d k / 3) ^ 2 := by
        intro k
        rw [hzE, ← integral_sq_sub (hA := hA)]
        have hsupp : spectralMeasure A hA (ψ k) (U k)ᶜ = 0 := by
          rw [← hPψ k, spectralMeasure_specProj measurableSet_Ioo,
            Measure.restrict_apply measurableSet_Ioo.compl]
          simp
        have hae : ∀ᵐ y ∂(spectralMeasure A hA (ψ k)), (y - E) ^ 2 ≤ (4 * d k / 3) ^ 2 := by
          rw [ae_iff]
          refine measure_mono_null (fun y hy => ?_) hsupp
          intro hyU
          apply hy
          simp only [U, mem_Ioo] at hyU
          have : |y - E| ≤ 4 * d k / 3 := by
            simp only [d] at hyU ⊢
            rw [abs_le]
            rcases le_or_gt 0 (x k - E) with hs | hs
            · rw [abs_of_nonneg hs] at hyU ⊢; constructor <;> linarith [hyU.1, hyU.2]
            · rw [abs_of_neg hs] at hyU ⊢; constructor <;> linarith [hyU.1, hyU.2]
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) this 2
        calc ∫ y, (y - E) ^ 2 ∂(spectralMeasure A hA (ψ k))
            ≤ ∫ _, (4 * d k / 3) ^ 2 ∂(spectralMeasure A hA (ψ k)) :=
              integral_mono_ae (integrable_spectralMeasure A hA _ (by fun_prop))
                (integrable_const _) hae
          _ = (4 * d k / 3) ^ 2 := by
              rw [integral_const, spectralMeasure_real_univ, smul_eq_mul]
              simp only [ψ]
              rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by positivity),
                inv_mul_cancel₀ (hwpos k).ne', one_pow, one_mul]
      have hlim : Tendsto (fun k => 4 * d k / 3) atTop (𝓝 0) := by
        have h1 : Tendsto (fun k : ℕ => 4 * (1 / 3 : ℝ) ^ k / 3) atTop (𝓝 0) := by
          have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 3)
            (by norm_num)).const_mul (4 : ℝ)
          simpa using this.div_const 3
        refine squeeze_zero (fun k => by linarith [hd0 k]) (fun k => ?_) h1
        have := (hdr k).trans_le (hrr_le k)
        linarith
      refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) hlim
      have := hbound k
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by linarith [hd0 k]) two_ne_zero).1 this
  · -- infinite-dimensional eigenspace: an orthonormal sequence of eigenvectors
    have hinf : (Module.Basis.ofVectorSpaceIndex ℂ K).Infinite := fun h =>
      hfin (FiniteDimensional.of_finite_basis (Module.Basis.ofVectorSpace ℂ K) h)
    set e := hinf.natEmbedding
    set f : ℕ → K := fun n => Module.Basis.ofVectorSpace ℂ K (e n)
    have hli : LinearIndependent ℂ f :=
      (Module.Basis.ofVectorSpace ℂ K).linearIndependent.comp _ e.injective
    set g := InnerProductSpace.gramSchmidtNormed ℂ f
    have hg := InnerProductSpace.gramSchmidtNormed_orthonormal hli
    refine ⟨fun n => (g n : H), ⟨fun n => ?_, fun i j hij => ?_⟩, ?_⟩
    · rw [← hg.1 n]; rfl
    · show ⟪(g i : H), (g j : H)⟫_ℂ = 0
      exact hg.2 hij
    · have : ∀ n, (A - algebraMap ℂ (H →L[ℂ] H) z) (g n : H) = 0 := fun n => (g n).2
      simp_rw [this, norm_zero]
      exact tendsto_const_nhds

/-- **Theorem 1.4.24**: for self-adjoint `A` (on a nontrivial space), `z ∈ σ_ess(A)` iff
there is a singular Weyl sequence for `A` at `z`. -/
theorem mem_essSpectrum_iff [Nontrivial H] (hA : IsSelfAdjoint A) (z : ℂ) :
    z ∈ essSpectrum A ↔ ∃ ψ : ℕ → H, IsSingularWeylSequence A z ψ :=
  ⟨exists_singular_of_mem_essSpectrum hA, fun ⟨_, h⟩ => mem_essSpectrum_of_singular hA h⟩

/-- **Corollary 1.4.25**: the essential spectrum is invariant under self-adjoint finite-rank
perturbations. -/
theorem essSpectrum_add_finiteRank [Nontrivial H] (hA : IsSelfAdjoint A) {R : H →L[ℂ] H}
    (hR : IsSelfAdjoint R)
    (hfin : FiniteDimensional ℂ (LinearMap.range (R : H →ₗ[ℂ] H))) :
    essSpectrum (A + R) = essSpectrum A := by
  have hAR : IsSelfAdjoint (A + R) := hA.add hR
  have key : ∀ (B S : H →L[ℂ] H) (hB : IsSelfAdjoint B) (hBS : IsSelfAdjoint (B + S)),
      FiniteDimensional ℂ (LinearMap.range (S : H →ₗ[ℂ] H)) →
      essSpectrum B ⊆ essSpectrum (B + S) := by
    intro B S hB hBS hS z hz
    obtain ⟨ψ, hψ, hlim⟩ := exists_singular_of_mem_essSpectrum hB hz
    refine mem_essSpectrum_of_singular hBS ⟨hψ, ?_⟩
    have hS0 := (tendsto_finiteRank_orthonormal hS hψ).norm
    rw [norm_zero] at hS0
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using hlim.add hS0)
    have : (B + S - algebraMap ℂ (H →L[ℂ] H) z) (ψ n) =
        (B - algebraMap ℂ (H →L[ℂ] H) z) (ψ n) + S (ψ n) := by
      simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply]; abel
    rw [this]; exact norm_add_le _ _
  refine (Set.Subset.antisymm ?_ (key A R hA hAR hfin))
  have hfin' : FiniteDimensional ℂ (LinearMap.range ((-R : H →L[ℂ] H) : H →ₗ[ℂ] H)) := by
    have : LinearMap.range ((-R : H →L[ℂ] H) : H →ₗ[ℂ] H) =
        LinearMap.range (R : H →ₗ[ℂ] H) := by
      rw [ContinuousLinearMap.coe_neg, LinearMap.range_neg]
    rw [this]; exact hfin
  have := key (A + R) (-R) hAR (by simpa using hA) hfin'
  simpa using this

end DF
