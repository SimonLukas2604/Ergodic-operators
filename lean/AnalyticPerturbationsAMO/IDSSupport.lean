/-
# The density of states has full support on `Σ`  (paper Lemma 2.8, support part)

For a norm-continuous, `1`-periodic, covariant (`K_{x+α} = U K_x U^*`) family of self-adjoint
operators on `ℓ²(ℤ)` with common spectrum `Σ`, every open interval meeting `Σ` has positive
density-of-states measure.  Together with `dos_compl_eq_zero` this identifies the support of the
IDS measure with `Σ`.  Everything here is proved.

Proof (as in the paper): take a bump `f ≥ 0` around `E ∈ Σ` and `g = √f`.  If the interval had
measure zero then `x ↦ ‖g(K_x) δ₀‖²` would vanish identically; covariance moves `δ₀` to every
`δ_n`, so `g(K_x) = 0`, contradicting `g(E) > 0` with `E ∈ spec K_x`.
-/
import AnalyticPerturbationsAMO.DensityOfStates

noncomputable section

open scoped ENNReal InnerProductSpace ComplexConjugate
open MeasureTheory Set Filter Metric BoundedContinuousFunction L2

namespace AMO

/-! ### Basis vectors and the shift -/

lemma U_delta (α x : ℝ) (n : ℤ) : U α x (delta (n + 1)) = delta n := by
  ext k
  rw [U_apply, delta, delta, lp.single_apply, lp.single_apply]
  simp [Pi.single_apply]

lemma Uinv_delta (α x : ℝ) (n : ℤ) : W α x (-1) 0 (delta n) = delta (n + 1) := by
  rw [← U_delta α x n, ← ContinuousLinearMap.comp_apply, Uinv_comp_U]
  rfl

lemma norm_U_apply (α x : ℝ) (u : L2 ℤ) : ‖U α x u‖ = ‖u‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sq_eq_tsum, norm_sq_eq_tsum]
  simp only [U_apply]
  exact (Equiv.addRight (1 : ℤ)).tsum_eq (fun n => ‖u n‖ ^ 2)

/-- An operator on `ℓ²(ℤ)` vanishing on every `δ_n` is zero. -/
lemma eq_zero_of_delta {T : Op ℤ} (h : ∀ n, T (delta n) = 0) : T = 0 := by
  ext1 u
  have hs := (lp.hasSum_single (E := fun _ : ℤ => ℂ) (p := 2) (by norm_num) u).mapL T
  have hterm : ∀ n : ℤ, T (lp.single 2 n (u n)) = 0 := by
    intro n
    have : lp.single 2 n (u n) = u n • delta n := by
      ext k
      simp [delta, lp.single_apply, Pi.single_apply]
    rw [this, map_smul, h, smul_zero]
  simp only [hterm] at hs
  exact hs.unique hasSum_zero

/-- `U` as an element of the unitary group. -/
lemma U_mem_unitary (α x : ℝ) : U α x ∈ unitary (Op ℤ) := by
  have hs : star (U α x) = W α x (-1) 0 := by
    rw [U, star_W]; rfl
  refine ⟨?_, ?_⟩
  · rw [hs]; exact Uinv_comp_U α x
  · rw [hs]; exact U_comp_Uinv α x

/-! ### The bump function -/

/-- The bump `f(t) = max(0, ε - |t - E|)`. -/
def bump (E ε : ℝ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun t => max 0 (ε - |t - E|))
    (continuous_const.max (continuous_const.sub (continuous_id.sub continuous_const).abs))
    (max ε 0) (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_max_left _ _)]
      exact max_le (le_max_right _ _) (by
        have := abs_nonneg (t - E)
        exact le_max_of_le_left (by linarith)))

lemma bump_apply (E ε t : ℝ) : bump E ε t = max 0 (ε - |t - E|) := rfl

lemma bump_eq_zero_of_not_mem {E ε t : ℝ} (ht : t ∉ Ioo (E - ε) (E + ε)) : bump E ε t = 0 := by
  rw [bump_apply]
  apply max_eq_left
  simp only [mem_Ioo, not_and_or, not_lt] at ht
  rcases ht with h | h
  · have := neg_le_abs (t - E)
    linarith
  · have := le_abs_self (t - E)
    linarith

/-! ### Full support -/

/-- **The DOS measure charges every open interval meeting the spectrum.** -/
theorem dos_pos_of_mem {α : ℝ} {Hx : ℝ → Op ℤ} {ν : Measure ℝ} (hν : IsDOSMeasure Hx ν)
    (hcont : Continuous Hx) (hsa : ∀ x, IsSelfAdjoint (Hx x))
    (hper : ∀ x, Hx (x + 1) = Hx x)
    (hcov : ∀ x, Hx (x + α) = U α x * Hx x * star (U α x))
    {S : Set ℝ} (hS : IsCompact S) (hspec : ∀ x, spectrum ℝ (Hx x) = S)
    {E : ℝ} (hE : E ∈ S) {ε : ℝ} (hε : 0 < ε) :
    0 < ν (Ioo (E - ε) (E + ε)) := by
  have hprob := hν.1
  rw [pos_iff_ne_zero]
  intro hnull
  set G : ℂ → ℂ := fun z => ((Real.sqrt (bump E ε z.re) : ℝ) : ℂ) with hG
  have hGc : Continuous G := by
    simp only [hG]
    exact Complex.continuous_ofReal.comp
      (Real.continuous_sqrt.comp ((bump E ε).continuous.comp Complex.continuous_re))
  have hnormal : ∀ x, IsStarNormal (Hx x) := fun x => (hsa x).isStarNormal
  -- spectra of `H_x` lie in the compact set `ofReal '' S`
  have hspecC : ∀ x, spectrum ℂ (Hx x) ⊆ (fun t : ℝ => (t : ℂ)) '' S := by
    intro x z hz
    refine ⟨z.re, ?_, ((hsa x).mem_spectrum_eq_re hz).symm⟩
    rw [← hspec x, ← spectrum.preimage_algebraMap ℂ]
    simp only [mem_preimage, Complex.coe_algebraMap]
    rwa [← (hsa x).mem_spectrum_eq_re hz]
  have hScpt : IsCompact ((fun t : ℝ => (t : ℂ)) '' S) := hS.image Complex.continuous_ofReal
  -- `g(H_x) = cfc G (H_x)` and the function `x ↦ ‖g(H_x) δ₀‖²`
  set gH : ℝ → Op ℤ := fun x => cfc G (Hx x) with hgH
  have hgH_cont : Continuous gH :=
    Continuous.cfc' hScpt G hcont hspecC hGc.continuousOn (fun x => hnormal x)
  have hstar : ∀ x, star (gH x) = gH x := by
    intro x
    simp only [hgH]
    rw [← cfc_star]
    congr 1
    funext z
    simp [hG]
  -- `∫ bump dν = ∫ ‖g(H_x) δ₀‖²`
  have hsq : ∀ x, RCLike.re ⟪delta 0, cfc (fun z : ℂ => ((bump E ε z.re : ℝ) : ℂ)) (Hx x)
      (delta 0)⟫_ℂ = ‖gH x (delta 0)‖ ^ 2 := by
    intro x
    have hmul : cfc (fun z : ℂ => ((bump E ε z.re : ℝ) : ℂ)) (Hx x) = gH x * gH x := by
      simp only [hgH]
      rw [← cfc_mul G G (Hx x) hGc.continuousOn hGc.continuousOn]
      congr 1
      funext z
      simp only [hG]
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt]
      rw [bump_apply]; exact le_max_left _ _
    rw [hmul, ContinuousLinearMap.mul_apply]
    have : ⟪delta 0, gH x (gH x (delta 0))⟫_ℂ = ⟪gH x (delta 0), gH x (delta 0)⟫_ℂ := by
      rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
        hstar x]
    rw [this, inner_self_eq_norm_sq_to_K]
    norm_cast
  have hint0 : ∫ x in (0 : ℝ)..1, ‖gH x (delta 0)‖ ^ 2 = 0 := by
    have h := hν.2 (bump E ε)
    simp only [hsq] at h
    rw [← h]
    refine integral_eq_zero_of_ae ?_
    have : {t | bump E ε t ≠ 0} ⊆ Ioo (E - ε) (E + ε) := fun t ht => by
      by_contra hn; exact ht (bump_eq_zero_of_not_mem hn)
    exact measure_mono_null this hnull
  -- hence `g(H_x) δ₀ = 0` for every phase
  have hφc : Continuous fun x => ‖gH x (delta 0)‖ ^ 2 :=
    ((hgH_cont.clm_apply continuous_const).norm).pow 2
  have hφper : ∀ x, ‖gH (x + 1) (delta 0)‖ ^ 2 = ‖gH x (delta 0)‖ ^ 2 := fun x => by
    simp only [hgH, hper]
  have hzero0 : ∀ x, gH x (delta 0) = 0 := by
    by_contra hne
    push_neg at hne
    obtain ⟨y, hy⟩ := hne
    -- the support of `φ` is open, periodic, and meets `(0, 1)`
    set φ := fun x => ‖gH x (delta 0)‖ ^ 2
    have hφy : 0 < φ y := by simp only [φ]; positivity
    have hφ1 : Function.Periodic φ 1 := hφper
    set y' := Int.fract y
    have hφy' : 0 < φ y' := by
      have h := (hφ1.int_mul (-⌊y⌋)) y
      rw [show y + ((-⌊y⌋ : ℤ) : ℝ) * 1 = y' by
        rw [mul_one, Int.cast_neg, ← sub_eq_add_neg]; rfl] at h
      rw [h]
      exact hφy
    -- a small interval inside `(0,1)` where `φ > 0`
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (isOpen_lt continuous_const hφc) y' hφy'
    set a := y' + min (δ / 2) ((1 - y') / 2)
    have hy'0 : 0 ≤ y' := Int.fract_nonneg y
    have hy'1 : y' < 1 := Int.fract_lt_one y
    have hIoo : Ioo y' a ⊆ Function.support φ ∩ Ioc 0 1 := by
      intro t ht
      have hmin1 : min (δ / 2) ((1 - y') / 2) ≤ δ / 2 := min_le_left _ _
      have hmin2 : min (δ / 2) ((1 - y') / 2) ≤ (1 - y') / 2 := min_le_right _ _
      have hmem : t ∈ Metric.ball y' δ := by
        rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith [ht.1])]
        linarith [ht.2]
      exact ⟨(show 0 < φ t from hball hmem).ne', ⟨by linarith [ht.1], by linarith [ht.2]⟩⟩
    have hpos : 0 < ∫ x in (0 : ℝ)..1, φ x := by
      rw [intervalIntegral.integral_pos_iff_support_of_nonneg_ae
        (Eventually.of_forall fun x => by simp only [φ, Pi.zero_apply]; positivity)
        (hφc.intervalIntegrable 0 1)]
      refine ⟨zero_lt_one, lt_of_lt_of_le ?_ (measure_mono hIoo)⟩
      rw [Real.volume_Ioo, ENNReal.ofReal_pos]
      have : 0 < min (δ / 2) ((1 - y') / 2) := lt_min (by linarith) (by linarith)
      linarith
    rw [hint0] at hpos
    exact lt_irrefl _ hpos
  -- covariance: `g(H_x) δ_n = 0` for all `n`
  have hconj : ∀ x, gH (x + α) = U α x * gH x * star (U α x) := by
    intro x
    have hu := U_mem_unitary α x
    have h := StarAlgHomClass.map_cfc (Unitary.conjStarAlgAut ℂ (Op ℤ) ⟨U α x, hu⟩) G (Hx x)
      hGc.continuousOn (by
        change Continuous fun T : Op ℤ => U α x * T * star (U α x)
        fun_prop) (hnormal x) (by
        simp only [Unitary.conjStarAlgAut_apply]
        rw [← hcov]; exact hnormal _)
    simp only [Unitary.conjStarAlgAut_apply] at h
    simp only [hgH]
    rw [hcov, ← h]
  have hall : ∀ n : ℤ, ∀ x, gH x (delta n) = 0 := by
    intro n
    induction n using Int.induction_on with
    | zero => exact hzero0
    | succ n ih =>
      intro x
      have h := ih (x + α)
      rw [hconj] at h
      have hs : star (U α x) = W α x (-1) 0 := by rw [U, star_W]; rfl
      rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hs, Uinv_delta] at h
      have := norm_U_apply α x (gH x (delta (n + 1)))
      rw [h, norm_zero] at this
      exact norm_eq_zero.1 this.symm
    | pred n ih =>
      intro x
      have h := ih (x - α)
      have hx : x = (x - α) + α := by ring
      rw [hx, hconj, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply]
      have hs : star (U α (x - α)) = W α (x - α) (-1) 0 := by rw [U, star_W]; rfl
      rw [hs, show -(n : ℤ) - 1 = -(n : ℤ) - 1 from rfl, Uinv_delta]
      rw [show -(n : ℤ) - 1 + 1 = -(n : ℤ) by ring, h, map_zero]
  -- contradiction with `g(E) > 0`, `E ∈ spec H_0`
  have hg0 : gH 0 = 0 := eq_zero_of_delta (fun n => hall n 0)
  have hEspec : (E : ℂ) ∈ spectrum ℂ (Hx 0) := by
    have : E ∈ spectrum ℝ (Hx 0) := by rw [hspec 0]; exact hE
    rw [← spectrum.preimage_algebraMap ℂ] at this
    simpa using this
  have hle := norm_apply_le_norm_cfc G (Hx 0) hEspec hGc.continuousOn (hnormal 0)
  rw [show cfc G (Hx 0) = gH 0 from rfl, hg0, norm_zero] at hle
  have : 0 < ‖G E‖ := by
    simp only [hG, Complex.ofReal_re, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.sqrt_pos, bump_apply]
    simp [hε]
  linarith

/-- **Lemma 2.8 (support).**  For `H_x = AMO_η + R_x` with irrational `α`, every open interval
around a point of `Σ` has positive density-of-states measure; with `dos_compl_eq_zero` the
support of the IDS measure is exactly `Σ`. -/
theorem dos_support {α η : ℝ} {R : Symbol} (hα : Irrational α) (hR : SymbolSummable R)
    (hsa : SymbolSelfAdjoint R) {ν : Measure ℝ} (hν : IsDOSMeasure (H α η R) ν)
    {E : ℝ} (hE : E ∈ Sigma α η R) {ε : ℝ} (hε : 0 < ε) :
    0 < ν (Ioo (E - ε) (E + ε)) ∧ ν (Sigma α η R)ᶜ = 0 := by
  have hs : SymbolSummable (amo η + R) := (amo_summable η).add hR
  have hSA : ∀ x, IsSelfAdjoint (H α η R x) := isSelfAdjoint_H α η hR hsa
  have hcpt : IsCompact (Sigma α η R) := by
    have hb : Bornology.IsBounded (spectrum ℂ (H α η R 0)) := (spectrum.isCompact _).isBounded
    unfold Sigma
    rw [← spectrum.preimage_algebraMap ℂ]
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (spectrum.isClosed (𝕜 := ℂ) _).preimage (by
        simp only [Complex.coe_algebraMap]; exact Complex.continuous_ofReal)
    · obtain ⟨C, hC⟩ := hb.subset_closedBall 0
      refine (Metric.isBounded_closedBall (x := (0 : ℝ)) (r := C)).subset fun t ht => ?_
      have := hC ht
      simp only [Metric.mem_closedBall, dist_zero_right, Complex.coe_algebraMap,
        Complex.norm_real] at this ⊢
      exact this
  refine ⟨dos_pos_of_mem (α := α) hν (continuous_op hs) hSA (fun x => by
      have := op_add_int α (amo (η : ℂ) + R) x 1
      simp only [Int.cast_one] at this
      exact this) (fun x => ?_) hcpt
      (fun x => spectrum_H_eq_Sigma hα hR hsa x) hE hε,
    dos_compl_eq_zero hν (spectrum_real_isClosed _) (spectrum_real_nonempty (hSA 0)) hSA
      (fun x => (spectrum_H_eq_Sigma hα hR hsa x).le)⟩
  have hst : star (U α x) = W α x (-1) 0 := by rw [U, star_W]; rfl
  rw [hst]
  exact op_conj_U hs x

end AMO
