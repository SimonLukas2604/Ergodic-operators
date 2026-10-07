/-
Copyright (c) 2026. Formalization of
  S. Becker, S. Jitomirskaya, I. Krasovsky, "Critical almost Mathieu operator: hidden
  singularity, gap continuity, and the Hausdorff dimension of the spectrum"
  (arXiv:1909.04429v2).

# The Avron–van Mouche–Simon argument for Jacobi matrices  (paper §5, proof of Thm 5.2)

Paper references (`Arxiv_version-5.tex`):
* "For any `ε > 0` we can find a non-zero `φ_ε` with `‖(H - E)φ_ε‖ ≤ ε‖φ_ε‖`"
  (tex l. 840–843): `exists_approx_eigen` (approximate eigenvectors of self-adjoint
  operators), together with the truncation `exists_finsupp_approx`;
* "By the spectral theorem, there exists `E'` in the spectrum … with
  `|E' - E| ≤ ‖(H' - E)ψ‖/‖ψ‖`" (tex l. 960–963): `exists_mem_spectrum_near`;
* the estimates (5.7)–(5.10) of the proof (unnumbered displays tex l. 914–945, and (5.11)
  `Hphi`): `ams_quant_core`;
* the operator-difference bound in (5.12) (`contin`, tex l. 965–975):
  `norm_jacobi_sub_le`, with `b, v` Lipschitz (they are `C¹` and periodic in the paper);
* (5.13) (`cont-med`, tex l. 978–981): `ams_estimate`;
* passage from the fibre spectrum to `σ(M_{v,b,α})`, using a phase `θ` with
  `b(θ + kα) ≠ 0` for all `k` (tex l. 839): `infDist_sigmaM_le`.

## Implicit hypotheses made explicit
* `v, b` are bounded and Lipschitz (`C¹` periodic functions are);
* the zero set of `b` is countable (the paper assumes at most finitely many zeros per
  period, tex l. 1019–1020 and after (1.3)); this guarantees the existence of phases `θ`
  arbitrarily close to any given one with `b(θ + kα) ≠ 0` for all `k ∈ ℤ`.

Everything in this file is proved completely (no `sorry`).
-/
import CriticalAMOHausdorff.Basic
import CriticalAMOHausdorff.TestFunctions
import AnalyticPerturbationsAMO.Spectrum
import AnalyticPerturbationsAMO.DensityOfStates

noncomputable section

open Real L2 Filter Topology
open scoped InnerProductSpace ComplexConjugate

namespace CAH

/-! ### Multiplication operators -/

/-- The diagonal (multiplication) operator `(f φ)(n) = f(n) φ(n)`. -/
def mulOp (f : ℤ → ℝ) : Op := weightedShift (fun n => ((f n : ℝ) : ℂ)) (Equiv.refl ℤ)

lemma bdd_ofReal {f : ℤ → ℝ} {M : ℝ} (hf : ∀ n, |f n| ≤ M) :
    Bdd (fun n => ((f n : ℝ) : ℂ)) :=
  ⟨M, fun n => by simpa [Complex.norm_real] using hf n⟩

lemma mulOp_apply {f : ℤ → ℝ} {M : ℝ} (hf : ∀ n, |f n| ≤ M) (u : L2 ℤ) (n : ℤ) :
    mulOp f u n = (f n : ℂ) * u n := by
  rw [mulOp, weightedShift_apply (bdd_ofReal hf)]
  rfl

/-! ### Self-adjointness of the Jacobi matrix -/

theorem jacobi_isSelfAdjoint {v b : ℝ → ℝ} (hv : BddFun v) (hb : BddFun b) (α θ : ℝ) :
    IsSelfAdjoint (jacobi v b α θ) := by
  have e1 : star (weightedShift (fun n : ℤ => ((b (θ + (n - 1) * α) : ℝ) : ℂ))
      (Equiv.addRight (-1))) = weightedShift (fun n : ℤ => ((b (θ + n * α) : ℝ) : ℂ))
      (Equiv.addRight 1) := by
    rw [star_weightedShift (bdd_comp hb _)]
    apply weightedShift_congr
    · intro i; simp
    · intro i; simp
  have e2 : star (weightedShift (fun n : ℤ => ((b (θ + n * α) : ℝ) : ℂ))
      (Equiv.addRight 1)) = weightedShift (fun n : ℤ => ((b (θ + (n - 1) * α) : ℝ) : ℂ))
      (Equiv.addRight (-1)) := by
    rw [star_weightedShift (bdd_comp hb _)]
    apply weightedShift_congr
    · intro i; simp [sub_eq_add_neg]
    · intro i; simp
  have e3 : star (weightedShift (fun n : ℤ => ((v (θ + n * α) : ℝ) : ℂ))
      (Equiv.refl ℤ)) = weightedShift (fun n : ℤ => ((v (θ + n * α) : ℝ) : ℂ))
      (Equiv.refl ℤ) := by
    rw [star_weightedShift (bdd_comp hv _)]
    apply weightedShift_congr
    · intro i; simp
    · intro i; simp
  unfold IsSelfAdjoint jacobi
  set X := weightedShift (fun n : ℤ => ((b (θ + (n - 1) * α) : ℝ) : ℂ)) (Equiv.addRight (-1))
  set Y := weightedShift (fun n : ℤ => ((b (θ + n * α) : ℝ) : ℂ)) (Equiv.addRight 1)
  set Z := weightedShift (fun n : ℤ => ((v (θ + n * α) : ℝ) : ℂ)) (Equiv.refl ℤ)
  have hsum : star (X + Y + Z) = star X + star Y + star Z :=
    (star_add (X + Y) Z).trans (congrArg (· + star Z) (star_add X Y))
  rw [hsum, e1, e2, e3]
  abel

/-! ### Approximate eigenvectors -/

lemma algebraMap_apply_L2 (E : ℝ) (φ : L2 ℤ) : (algebraMap ℝ Op E) φ = (E : ℂ) • φ := by
  rw [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, Complex.coe_smul]
  rfl

lemma isSelfAdjoint_algebraMap_real (E : ℝ) : IsSelfAdjoint (algebraMap ℝ Op E) := by
  rw [IsScalarTower.algebraMap_apply ℝ ℂ Op E]
  refine IsSelfAdjoint.algebraMap Op ?_
  show star ((algebraMap ℝ ℂ) E) = (algebraMap ℝ ℂ) E
  simp

lemma isUnit_of_isUnit_mul_self {M : Type*} [Monoid M] {a : M} (h : IsUnit (a * a)) :
    IsUnit a := by
  obtain ⟨u, hu⟩ := h
  have hl : (↑u⁻¹ * a) * a = 1 := by rw [mul_assoc, ← hu, Units.inv_mul]
  have hr : a * (a * ↑u⁻¹) = 1 := by rw [← mul_assoc, ← hu, Units.mul_inv]
  have heq : ↑u⁻¹ * a = a * ↑u⁻¹ := by
    calc ↑u⁻¹ * a = (↑u⁻¹ * a) * (a * (a * ↑u⁻¹)) := by rw [hr, mul_one]
      _ = ((↑u⁻¹ * a) * a) * (a * ↑u⁻¹) := by simp only [mul_assoc]
      _ = a * ↑u⁻¹ := by rw [hl, one_mul]
  exact ⟨⟨a, a * ↑u⁻¹, hr, by rw [← heq]; exact hl⟩, rfl⟩

/-- **Approximate eigenvectors.** If `H` is self-adjoint and `E ∈ σ(H)`, then for every
`ε > 0` there is `φ ≠ 0` with `‖(H - E)φ‖ ≤ ε‖φ‖` (tex l. 840–843). -/
theorem exists_approx_eigen {H : Op} (hH : IsSelfAdjoint H) {E : ℝ} (hE : E ∈ spectrum ℝ H)
    {ε : ℝ} (hε : 0 < ε) : ∃ φ : L2 ℤ, φ ≠ 0 ∧ ‖H φ - (E : ℂ) • φ‖ ≤ ε * ‖φ‖ := by
  by_contra hcon
  push_neg at hcon
  set T : Op := H - algebraMap ℝ Op E with hTdef
  have hTapp : ∀ φ, T φ = H φ - (E : ℂ) • φ := fun φ => by
    rw [hTdef, ContinuousLinearMap.sub_apply, algebraMap_apply_L2]
  have hbelow : ∀ φ, ε * ‖φ‖ ≤ ‖T φ‖ := by
    intro φ
    by_cases h : φ = 0
    · simp [h]
    · rw [hTapp]; exact (hcon φ h).le
  have hTsa : IsSelfAdjoint T :=
    (star_sub H (algebraMap ℝ Op E)).trans
      (congrArg₂ (· - ·) hH.star_eq (isSelfAdjoint_algebraMap_real E).star_eq)
  -- `T` is bounded below, hence injective with closed range; its range is dense since
  -- `(ran T)ᗮ = ker T* = ker T = 0`.  So `T` is invertible.
  have hanti : AntilipschitzWith (ε⁻¹).toNNReal T := by
    refine ContinuousLinearMap.antilipschitz_of_bound T (fun φ => ?_)
    rw [Real.coe_toNNReal _ (inv_nonneg.2 hε.le), ← div_eq_inv_mul, le_div_iff₀ hε]
    linarith [hbelow φ]
  have hker : T.ker = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    exact hanti.injective
  have hclosed : IsClosed (T.range : Set (L2 ℤ)) :=
    hanti.isClosed_range T.uniformContinuous
  have hrange : T.range = ⊤ := by
    have := hclosed.completeSpace_coe
    rw [← T.range.orthogonal_orthogonal, Submodule.eq_top_iff']
    intro v w hw
    have h1 : w ∈ (ContinuousLinearMap.adjoint T).ker := by
      rw [← ContinuousLinearMap.orthogonal_range]; exact hw
    have h2 : T w = 0 := by
      have h3 : (ContinuousLinearMap.adjoint T) w = 0 := h1
      rwa [← ContinuousLinearMap.star_eq_adjoint, hTsa.star_eq] at h3
    have hw0 : w = 0 := hanti.injective (by rw [h2, map_zero])
    rw [hw0]
    exact inner_zero_left _
  have hTunit : IsUnit T := by
    refine ⟨(ContinuousLinearEquiv.unitsEquiv ℂ (L2 ℤ)).symm
      (ContinuousLinearEquiv.ofBijective T hker hrange), ?_⟩
    first
    | rfl
    | (ext φ; rfl)
    | (ext φ; simp [ContinuousLinearEquiv.coe_ofBijective])
  apply spectrum.mem_iff.1 hE
  have : algebraMap ℝ Op E - H = -T := by rw [hTdef]; abel
  rw [this]
  exact hTunit.neg

/-- **Spectral theorem step (tex l. 960–963).** If `H` is self-adjoint and
`‖(H - E)ψ‖ ≤ r‖ψ‖` with `ψ ≠ 0`, then there is `E' ∈ σ(H)` with `|E - E'| ≤ r`.
(Proof: `E` is an eigenvalue of the rank-one perturbation `H + P`, `‖P‖ ≤ r`, and the
spectrum of the normal operator `H` is `‖P‖`-close to that of `H + P`.) -/
theorem exists_mem_spectrum_near {H : Op} (hH : IsSelfAdjoint H) {E r : ℝ} {ψ : L2 ℤ}
    (hψ : ψ ≠ 0) (h : ‖H ψ - (E : ℂ) • ψ‖ ≤ r * ‖ψ‖) :
    ∃ E' ∈ spectrum ℝ H, |E - E'| ≤ r := by
  have hψn : 0 < ‖ψ‖ := norm_pos_iff.2 hψ
  have hin0 : ⟪ψ, ψ⟫_ℂ ≠ 0 := inner_self_ne_zero.2 hψ
  set u : L2 ℤ := (⟪ψ, ψ⟫_ℂ)⁻¹ • ((E : ℂ) • ψ - H ψ) with hu
  set P : Op := (innerSL ℂ ψ).smulRight u with hP
  have hPψ : P ψ = (E : ℂ) • ψ - H ψ := by
    rw [hP, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, hu, smul_smul,
      mul_inv_cancel₀ hin0, one_smul]
  have hspecB : (E : ℂ) ∈ spectrum ℂ (H + P) := by
    rw [spectrum.mem_iff]
    rintro ⟨w, hw⟩
    apply hψ
    have h0 : (algebraMap ℂ Op (E : ℂ) - (H + P)) ψ = 0 := by
      rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply, hPψ,
        Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply]
      abel
    rw [← hw] at h0
    calc ψ = ((↑w⁻¹ * ↑w : Op)) ψ := by rw [Units.inv_mul]; rfl
      _ = 0 := by rw [ContinuousLinearMap.mul_apply, h0, map_zero]
  have := hH.isStarNormal
  obtain ⟨z, hz, hdist⟩ := AMO.exists_mem_spectrum_dist_le (a := H) (b := H + P) hspecB
  have hnormP : ‖H - (H + P)‖ ≤ r := by
    rw [sub_add_cancel_left, norm_neg, hP, ContinuousLinearMap.norm_smulRight_apply,
      innerSL_apply_norm, hu, norm_smul, norm_sub_rev, norm_inv, inner_self_eq_norm_sq_to_K,
      norm_pow, RCLike.norm_ofReal, abs_norm]
    calc ‖ψ‖ * ((‖ψ‖ ^ 2)⁻¹ * ‖H ψ - (E : ℂ) • ψ‖)
        ≤ ‖ψ‖ * ((‖ψ‖ ^ 2)⁻¹ * (r * ‖ψ‖)) := by gcongr
      _ = r := by field_simp
  have hzre : z = (z.re : ℂ) := hH.mem_spectrum_eq_re hz
  refine ⟨z.re, ?_, ?_⟩
  · rw [← spectrum.algebraMap_mem_iff ℂ]
    rw [hzre] at hz
    simpa using hz
  · have h1 : |E - z.re| = |((E : ℂ) - z).re| := by simp
    rw [h1]
    exact (Complex.abs_re_le_norm _).trans (hdist.trans hnormP)

/-- The truncation `∑_{i ∈ s} φ(i) δ_i`. -/
def trunc (φ : L2 ℤ) (s : Finset ℤ) : L2 ℤ := ∑ i ∈ s, lp.single 2 i (φ i)

lemma trunc_apply (φ : L2 ℤ) (s : Finset ℤ) (n : ℤ) :
    trunc φ s n = if n ∈ s then φ n else 0 := by
  rw [trunc, lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.single_apply, Pi.single_apply]
  exact Finset.sum_ite_eq s n (fun c => φ c)

lemma tendsto_trunc (φ : L2 ℤ) : Tendsto (trunc φ) atTop (𝓝 φ) := by
  have hsum := lp.hasSum_single (E := fun _ : ℤ => ℂ) (p := 2) ENNReal.ofNat_ne_top φ
  unfold HasSum at hsum
  exact hsum

lemma trunc_support (φ : L2 ℤ) (s : Finset ℤ) :
    ∀ n : ℤ, ((s.sup Int.natAbs : ℕ) : ℤ) < |n| → trunc φ s n = 0 := by
  intro n hn
  rw [trunc_apply, if_neg]
  intro hns
  have h1 : n.natAbs ≤ s.sup Int.natAbs := Finset.le_sup (f := Int.natAbs) hns
  have h2 : |n| = (n.natAbs : ℤ) := Int.abs_eq_natAbs n
  omega

lemma exists_trunc_close (φ : L2 ℤ) {η : ℝ} (hη : 0 < η) :
    ∃ s : Finset ℤ, ‖trunc φ s - φ‖ ≤ η := by
  obtain ⟨s, hs⟩ := ((tendsto_trunc φ).eventually (Metric.closedBall_mem_nhds φ hη)).exists
  exact ⟨s, by rw [← dist_eq_norm]; exact hs⟩

/-- **Truncation.** An approximate eigenvector can be replaced by a finitely supported one
(at the cost of a factor `2` in the tolerance). -/
theorem exists_finsupp_approx {H : Op} {E ε : ℝ} (hε : 0 < ε) {φ : L2 ℤ} (hφ : φ ≠ 0)
    (h : ‖H φ - (E : ℂ) • φ‖ ≤ ε * ‖φ‖) :
    ∃ ψ : L2 ℤ, ψ ≠ 0 ∧ (∃ N : ℕ, ∀ n : ℤ, (N : ℤ) < |n| → ψ n = 0) ∧
      ‖H ψ - (E : ℂ) • ψ‖ ≤ 2 * ε * ‖ψ‖ := by
  have hφn : 0 < ‖φ‖ := norm_pos_iff.2 hφ
  set C : ℝ := ‖H‖ + |E| with hC
  have hC0 : 0 ≤ C := by positivity
  set η : ℝ := ε * ‖φ‖ / (C + 2 * ε + 1) with hηdef
  have hη : 0 < η := by positivity
  have hηle : (C + 2 * ε) * η ≤ ε * ‖φ‖ := by
    rw [hηdef, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith [mul_pos hε hφn]
  have hηφ : η < ‖φ‖ := by
    rw [hηdef, div_lt_iff₀ (by positivity)]
    nlinarith [mul_pos hε hφn]
  obtain ⟨s, hs⟩ := exists_trunc_close φ hη
  set ψ := trunc φ s
  have hψn : ‖φ‖ - η ≤ ‖ψ‖ := by
    have := norm_sub_norm_le φ ψ
    rw [norm_sub_rev] at hs
    linarith
  have hdiff : ‖(H ψ - (E : ℂ) • ψ) - (H φ - (E : ℂ) • φ)‖ ≤ C * η := by
    have e : (H ψ - (E : ℂ) • ψ) - (H φ - (E : ℂ) • φ) = H (ψ - φ) - (E : ℂ) • (ψ - φ) := by
      rw [map_sub, smul_sub]; abel
    rw [e]
    calc ‖H (ψ - φ) - (E : ℂ) • (ψ - φ)‖ ≤ ‖H (ψ - φ)‖ + ‖(E : ℂ) • (ψ - φ)‖ := norm_sub_le _ _
      _ ≤ ‖H‖ * ‖ψ - φ‖ + |E| * ‖ψ - φ‖ := by
          rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
          gcongr
          exact H.le_opNorm _
      _ = C * ‖ψ - φ‖ := by rw [hC]; ring
      _ ≤ C * η := mul_le_mul_of_nonneg_left hs hC0
  have htot : ‖H ψ - (E : ℂ) • ψ‖ ≤ ε * ‖φ‖ + C * η := by
    have := norm_le_insert' (H ψ - (E : ℂ) • ψ) (H φ - (E : ℂ) • φ)
    linarith [norm_sub_norm_le (H ψ - (E : ℂ) • ψ) (H φ - (E : ℂ) • φ)]
  refine ⟨ψ, fun h0 => ?_, ⟨_, trunc_support φ s⟩, ?_⟩
  · rw [h0, norm_zero] at hψn; linarith
  · nlinarith

/-! ### Pointwise bounds and the operator difference -/

/-- A pointwise bound by shifted copies gives an `ℓ²` bound. -/
lemma norm_le_of_pointwise {x ψ : L2 ℤ} {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (h : ∀ n, ‖x n‖ ≤ a * ‖ψ (n - 1)‖ + a * ‖ψ (n + 1)‖ + c * ‖ψ n‖) :
    ‖x‖ ≤ (2 * a + c) * ‖ψ‖ := by
  have hs1 : Summable (fun n : ℤ => ‖ψ (n - 1)‖ ^ 2) :=
    (summable_norm_sq ψ).comp_injective (sub_left_injective (b := (1 : ℤ)))
  have hs2 : Summable (fun n : ℤ => ‖ψ (n + 1)‖ ^ 2) :=
    (summable_norm_sq ψ).comp_injective (add_left_injective (1 : ℤ))
  have hs3 := summable_norm_sq ψ
  have e1 : ∑' n : ℤ, ‖ψ (n - 1)‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [norm_sq_eq_tsum]; exact (Equiv.subRight (1 : ℤ)).tsum_eq (fun n => ‖ψ n‖ ^ 2)
  have e2 : ∑' n : ℤ, ‖ψ (n + 1)‖ ^ 2 = ‖ψ‖ ^ 2 := by
    rw [norm_sq_eq_tsum]; exact (Equiv.addRight (1 : ℤ)).tsum_eq (fun n => ‖ψ n‖ ^ 2)
  have hpt : ∀ n, ‖x n‖ ^ 2 ≤ (2 * a + c) *
      (a * ‖ψ (n - 1)‖ ^ 2 + a * ‖ψ (n + 1)‖ ^ 2 + c * ‖ψ n‖ ^ 2) := by
    intro n
    set s := ‖ψ (n - 1)‖
    set t := ‖ψ (n + 1)‖
    set u := ‖ψ n‖
    have h0 : 0 ≤ ‖x n‖ := norm_nonneg _
    have h1 : ‖x n‖ ^ 2 ≤ (a * s + a * t + c * u) ^ 2 := pow_le_pow_left₀ h0 (h n) 2
    have h2 : (2 * a + c) * (a * s ^ 2 + a * t ^ 2 + c * u ^ 2) - (a * s + a * t + c * u) ^ 2
        = a * a * (s - t) ^ 2 + a * c * (s - u) ^ 2 + a * c * (t - u) ^ 2 := by ring
    have h3 : 0 ≤ a * a * (s - t) ^ 2 + a * c * (s - u) ^ 2 + a * c * (t - u) ^ 2 := by
      positivity
    linarith
  have hsq : ‖x‖ ^ 2 ≤ ((2 * a + c) * ‖ψ‖) ^ 2 := by
    rw [norm_sq_eq_tsum x]
    calc ∑' n, ‖x n‖ ^ 2
        ≤ ∑' n, (2 * a + c) * (a * ‖ψ (n - 1)‖ ^ 2 + a * ‖ψ (n + 1)‖ ^ 2 + c * ‖ψ n‖ ^ 2) :=
          Summable.tsum_le_tsum hpt (summable_norm_sq x)
            ((((hs1.mul_left a).add (hs2.mul_left a)).add (hs3.mul_left c)).mul_left _)
      _ = (2 * a + c) * (a * ‖ψ‖ ^ 2 + a * ‖ψ‖ ^ 2 + c * ‖ψ‖ ^ 2) := by
          rw [Summable.tsum_mul_left _ (((hs1.mul_left a).add (hs2.mul_left a)).add
            (hs3.mul_left c)), Summable.tsum_add ((hs1.mul_left a).add (hs2.mul_left a))
            (hs3.mul_left c), Summable.tsum_add (hs1.mul_left a) (hs2.mul_left a),
            Summable.tsum_mul_left _ hs1, Summable.tsum_mul_left _ hs2,
            Summable.tsum_mul_left _ hs3, e1, e2, ← norm_sq_eq_tsum]
      _ = ((2 * a + c) * ‖ψ‖) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-- **Operator difference.** If the coefficients of two Jacobi matrices differ by at most
`δb`, `δv` at all sites seen by `ψ`, then `‖(H' - H)ψ‖ ≤ (2δb + δv)‖ψ‖`. -/
theorem norm_jacobi_sub_le {v b v' b' : ℝ → ℝ} (hv : BddFun v) (hb : BddFun b)
    (hv' : BddFun v') (hb' : BddFun b') {α θ α' θ' : ℝ} {ψ : L2 ℤ} {δb δv : ℝ}
    (hδb : 0 ≤ δb) (hδv : 0 ≤ δv)
    (h : ∀ k : ℤ, ψ k ≠ 0 →
      |b' (θ' + k * α') - b (θ + k * α)| ≤ δb ∧
      |b' (θ' + ((k : ℝ) - 1) * α') - b (θ + ((k : ℝ) - 1) * α)| ≤ δb ∧
      |v' (θ' + k * α') - v (θ + k * α)| ≤ δv) :
    ‖jacobi v' b' α' θ' ψ - jacobi v b α θ ψ‖ ≤ (2 * δb + δv) * ‖ψ‖ := by
  apply norm_le_of_pointwise hδb hδv
  intro n
  rw [lp.coeFn_sub, Pi.sub_apply, jacobi_apply hv' hb', jacobi_apply hv hb]
  have e : ((b' (θ' + (n - 1) * α') : ℂ) * ψ (n - 1) + (b' (θ' + n * α') : ℂ) * ψ (n + 1) +
        (v' (θ' + n * α') : ℂ) * ψ n) -
      ((b (θ + (n - 1) * α) : ℂ) * ψ (n - 1) + (b (θ + n * α) : ℂ) * ψ (n + 1) +
        (v (θ + n * α) : ℂ) * ψ n) =
      ((b' (θ' + (n - 1) * α') - b (θ + (n - 1) * α) : ℝ) : ℂ) * ψ (n - 1) +
      ((b' (θ' + n * α') - b (θ + n * α) : ℝ) : ℂ) * ψ (n + 1) +
      ((v' (θ' + n * α') - v (θ + n * α) : ℝ) : ℂ) * ψ n := by
    push_cast; ring
  rw [e]
  have key : ∀ (d : ℝ) (z : ℂ) (δ : ℝ), 0 ≤ δ → (z ≠ 0 → abs d ≤ δ) →
      ‖(d : ℂ) * z‖ ≤ δ * ‖z‖ := by
    intro d z δ hδ hd
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    by_cases hz : z = 0
    · simp [hz]
    · exact mul_le_mul_of_nonneg_right (hd hz) (norm_nonneg _)
  have t1 := key (b' (θ' + (n - 1) * α') - b (θ + (n - 1) * α)) (ψ (n - 1)) δb hδb
    (fun hz => by have := (h (n - 1) hz).1; push_cast at this; exact this)
  have t2 := key (b' (θ' + n * α') - b (θ + n * α)) (ψ (n + 1)) δb hδb
    (fun hz => by have := (h (n + 1) hz).2.1; push_cast at this; simpa using this)
  have t3 := key (v' (θ' + n * α') - v (θ + n * α)) (ψ n) δv hδv (fun hz => (h n hz).2.2)
  set z1 := ((b' (θ' + (n - 1) * α') - b (θ + (n - 1) * α) : ℝ) : ℂ) * ψ (n - 1)
  set z2 := ((b' (θ' + n * α') - b (θ + n * α) : ℝ) : ℂ) * ψ (n + 1)
  set z3 := ((v' (θ' + n * α') - v (θ + n * α) : ℝ) : ℂ) * ψ n
  have h3 := norm_add_le (z1 + z2) z3
  have h4 := norm_add_le z1 z2
  linarith

/-! ### The commutator `[f, H]` -/

lemma comm_apply {v b : ℝ → ℝ} (hv : BddFun v) (hb : BddFun b) (α θ : ℝ) {f : ℤ → ℝ}
    {M : ℝ} (hf : ∀ n, |f n| ≤ M) (u : L2 ℤ) (n : ℤ) :
    (mulOp f (jacobi v b α θ u) - jacobi v b α θ (mulOp f u)) n =
      (((f n - f (n - 1)) * b (θ + ((n : ℝ) - 1) * α) : ℝ) : ℂ) * u (n - 1) +
      (((f n - f (n + 1)) * b (θ + n * α) : ℝ) : ℂ) * u (n + 1) := by
  rw [lp.coeFn_sub, Pi.sub_apply, mulOp_apply hf, jacobi_apply hv hb, jacobi_apply hv hb]
  simp only [mulOp_apply hf]
  push_cast
  ring

/-! ### The quantitative core of the AMS argument -/

/-- The weights `1/|b(θ + kα)|`. -/
def bw (b : ℝ → ℝ) (α θ : ℝ) (k : ℤ) : ℝ := 1 / |b (θ + k * α)|

/-- **Quantitative core of the proof of Theorem 5.2** ((5.7)–(5.11), tex l. 914–951).
Let `θ` be a phase with `b(θ + kα) ≠ 0` for all `k`, `φ ≠ 0` finitely supported with
`‖(H - E)φ‖ ≤ ε‖φ‖`, and `S > 0` a lower bound for all `S_{±,m}`.  Then for some centre
`m`, `ψ = f_{m,L} φ ≠ 0` is supported in `|k - m| < L` and
`‖(H - E)ψ‖ ≤ (2√2 ε + 4√2/S)‖ψ‖`. -/
theorem ams_quant_core {v b : ℝ → ℝ} (hv : BddFun v) (hb : BddFun b) {α θ : ℝ}
    (hgood : ∀ k : ℤ, b (θ + k * α) ≠ 0) {L : ℕ} (hL : 1 ≤ L) {S : ℝ} (hS : 0 < S)
    (hSle : ∀ m : ℤ, S ≤ Splus (bw b α θ) L m) {E ε : ℝ} (hε : 0 ≤ ε) {φ : L2 ℤ}
    (hφ : φ ≠ 0) {N : ℕ} (hsupp : ∀ n : ℤ, (N : ℤ) < |n| → φ n = 0)
    (happ : ‖jacobi v b α θ φ - (E : ℂ) • φ‖ ≤ ε * ‖φ‖) :
    ∃ m : ℤ, mulOp (testFn (bw b α θ) L m) φ ≠ 0 ∧
      (∀ k : ℤ, mulOp (testFn (bw b α θ) L m) φ k ≠ 0 → |k - m| < L) ∧
      ‖jacobi v b α θ (mulOp (testFn (bw b α θ) L m) φ) -
          (E : ℂ) • mulOp (testFn (bw b α θ) L m) φ‖ ≤
        (2 * √2 * ε + 4 * √2 / S) * ‖mulOp (testFn (bw b α θ) L m) φ‖ := by
  set bk : ℤ → ℝ := fun k => b (θ + k * α) with hbk
  have hbk0 : ∀ k, bk k ≠ 0 := hgood
  set w : ℤ → ℝ := bw b α θ with hwdef
  have hwbk : w = fun k => 1 / |bk k| := rfl
  have hw : ∀ k, 0 < w k := fun k => by
    have := abs_pos.2 (hgood k); simp only [hwdef, bw]; positivity
  set f : ℤ → ℤ → ℝ := fun m => testFn w L m with hfdef
  have hf1 : ∀ m n, |f m n| ≤ 1 := fun m n =>
    abs_le.2 ⟨by linarith [testFn_nonneg hw hL m n], testFn_le_one hw hL m n⟩
  set H := jacobi v b α θ with hH
  set g : L2 ℤ := H φ - (E : ℂ) • φ with hg
  set C : ℤ → L2 ℤ := fun m => mulOp (f m) (H φ) - H (mulOp (f m) φ) with hC
  have hdecomp : ∀ m, H (mulOp (f m) φ) - (E : ℂ) • mulOp (f m) φ = mulOp (f m) g - C m := by
    intro m
    simp only [hg, hC, map_sub, map_smul]
    abel
  set B : Finset ℤ := Finset.Icc (-(N : ℤ) - L) (N + L) with hB
  -- summability and the basic identity `∑_m ‖f_m u‖² = ∑_n (∑_m f_m(n)²) |u_n|²`
  have hsumm : ∀ u : L2 ℤ, Summable (fun n => (∑ m ∈ B, f m n ^ 2) * ‖u n‖ ^ 2) := by
    intro u
    have hs : Summable (fun n => (2 * (L : ℝ) + 1) * ‖u n‖ ^ 2) :=
      (summable_norm_sq u).mul_left _
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hs
    exact mul_le_mul_of_nonneg_right (sum_sq_testFn_le hw hL B n) (sq_nonneg _)
  have hsumsq : ∀ u : L2 ℤ, ∑ m ∈ B, ‖mulOp (f m) u‖ ^ 2 =
      ∑' n, (∑ m ∈ B, f m n ^ 2) * ‖u n‖ ^ 2 := by
    intro u
    simp_rw [norm_sq_eq_tsum (mulOp _ u)]
    rw [← Summable.tsum_finsetSum (fun m _ => summable_norm_sq _)]
    congr 1
    funext n
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [mulOp_apply (hf1 m), norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  -- lower bound for `∑_m ‖f_m φ‖²`
  have hY : ((L : ℝ) + 1) / 2 * ‖φ‖ ^ 2 ≤ ∑ m ∈ B, ‖mulOp (f m) φ‖ ^ 2 := by
    rw [hsumsq φ, norm_sq_eq_tsum φ, ← Summable.tsum_mul_left _ (summable_norm_sq φ)]
    refine Summable.tsum_le_tsum (fun n => ?_) ((summable_norm_sq φ).mul_left _) (hsumm φ)
    by_cases h0 : φ n = 0
    · simp [h0]
    · have hn : |n| ≤ N := by
        by_contra hc; exact h0 (hsupp n (lt_of_not_ge hc))
      have hBn : Finset.Icc (n - L) (n + L) ⊆ B := by
        intro x hx
        rw [Finset.mem_Icc] at hx ⊢
        have := abs_le.1 hn
        constructor <;> omega
      exact mul_le_mul_of_nonneg_right (le_sum_sq_testFn hw hL hBn) (sq_nonneg _)
  -- upper bound for `∑_m ‖f_m g‖²`
  have hG : ∑ m ∈ B, ‖mulOp (f m) g‖ ^ 2 ≤ (2 * L + 1) * ‖g‖ ^ 2 := by
    rw [hsumsq g, norm_sq_eq_tsum g, ← Summable.tsum_mul_left _ (summable_norm_sq g)]
    refine Summable.tsum_le_tsum (fun n => ?_) (hsumm g) ((summable_norm_sq g).mul_left _)
    exact mul_le_mul_of_nonneg_right (sum_sq_testFn_le hw hL B n) (sq_nonneg _)
  -- the commutator sum
  set D : ℤ → ℤ → ℝ := fun m j => (f m j - f m (j + 1)) * bk j with hD
  have hDsum : ∀ j, ∑ m ∈ B, D m j ^ 2 ≤ 2 * L / S ^ 2 := fun j =>
    sum_sq_testFn_sub_succ_mul_le (b := bk) hbk0 hL hS hSle B j
  have hCpt : ∀ m n, ‖C m n‖ ^ 2 ≤
      2 * D m (n - 1) ^ 2 * ‖φ (n - 1)‖ ^ 2 + 2 * D m n ^ 2 * ‖φ (n + 1)‖ ^ 2 := by
    intro m n
    have hc := comm_apply hv hb α θ (hf1 m) φ n
    have hd1 : (f m n - f m (n - 1)) * b (θ + ((n : ℝ) - 1) * α) = -D m (n - 1) := by
      simp only [hD, hbk, sub_add_cancel]; push_cast; ring
    have hd2 : (f m n - f m (n + 1)) * b (θ + n * α) = D m n := rfl
    simp only [hC]
    rw [hc, hd1, hd2]
    have h1 : ‖(((-D m (n - 1) : ℝ)) : ℂ) * φ (n - 1) + ((D m n : ℝ) : ℂ) * φ (n + 1)‖ ≤
        |D m (n - 1)| * ‖φ (n - 1)‖ + |D m n| * ‖φ (n + 1)‖ := by
      refine (norm_add_le _ _).trans (le_of_eq ?_)
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_neg]
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : (|D m (n - 1)| * ‖φ (n - 1)‖ + |D m n| * ‖φ (n + 1)‖) ^ 2 ≤
        2 * D m (n - 1) ^ 2 * ‖φ (n - 1)‖ ^ 2 + 2 * D m n ^ 2 * ‖φ (n + 1)‖ ^ 2 := by
      nlinarith [sq_nonneg (|D m (n - 1)| * ‖φ (n - 1)‖ - |D m n| * ‖φ (n + 1)‖),
        sq_abs (D m (n - 1)), sq_abs (D m n)]
    exact h2.trans h3
  have hs1 : Summable (fun n : ℤ => ‖φ (n - 1)‖ ^ 2) :=
    (summable_norm_sq φ).comp_injective (sub_left_injective (b := (1 : ℤ)))
  have hs2 : Summable (fun n : ℤ => ‖φ (n + 1)‖ ^ 2) :=
    (summable_norm_sq φ).comp_injective (add_left_injective (1 : ℤ))
  have e1 : ∑' n : ℤ, ‖φ (n - 1)‖ ^ 2 = ‖φ‖ ^ 2 := by
    rw [norm_sq_eq_tsum]; exact (Equiv.subRight (1 : ℤ)).tsum_eq (fun n => ‖φ n‖ ^ 2)
  have e2 : ∑' n : ℤ, ‖φ (n + 1)‖ ^ 2 = ‖φ‖ ^ 2 := by
    rw [norm_sq_eq_tsum]; exact (Equiv.addRight (1 : ℤ)).tsum_eq (fun n => ‖φ n‖ ^ 2)
  have hCs : ∑ m ∈ B, ‖C m‖ ^ 2 ≤ 8 * L / S ^ 2 * ‖φ‖ ^ 2 := by
    simp_rw [norm_sq_eq_tsum (C _)]
    rw [← Summable.tsum_finsetSum (fun m _ => summable_norm_sq _)]
    have hR : Summable (fun n : ℤ => 2 * (2 * L / S ^ 2) * ‖φ (n - 1)‖ ^ 2 +
        2 * (2 * L / S ^ 2) * ‖φ (n + 1)‖ ^ 2) :=
      (hs1.mul_left _).add (hs2.mul_left _)
    calc ∑' n, ∑ m ∈ B, ‖C m n‖ ^ 2
        ≤ ∑' n : ℤ, (2 * (2 * L / S ^ 2) * ‖φ (n - 1)‖ ^ 2 +
            2 * (2 * L / S ^ 2) * ‖φ (n + 1)‖ ^ 2) := by
          refine Summable.tsum_le_tsum (fun n => ?_)
            (summable_sum (fun m _ => (summable_norm_sq (C m)))) hR
          refine (Finset.sum_le_sum (fun m _ => hCpt m n)).trans ?_
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum,
            ← Finset.mul_sum]
          have := hDsum (n - 1)
          have := hDsum n
          gcongr
      _ = 8 * L / S ^ 2 * ‖φ‖ ^ 2 := by
          rw [Summable.tsum_add (hs1.mul_left _) (hs2.mul_left _),
            Summable.tsum_mul_left _ hs1, Summable.tsum_mul_left _ hs2, e1, e2]
          ring
  -- the sum of `X_m = ‖(H - E) f_m φ‖²`
  have hXs : ∑ m ∈ B, ‖H (mulOp (f m) φ) - (E : ℂ) • mulOp (f m) φ‖ ^ 2 ≤
      2 * ∑ m ∈ B, ‖mulOp (f m) g‖ ^ 2 + 2 * ∑ m ∈ B, ‖C m‖ ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun m _ => ?_)
    rw [hdecomp m]
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (mulOp (f m) g) (C m)) 2
    nlinarith [sq_nonneg (‖mulOp (f m) g‖ - ‖C m‖)]
  have hg2 : ‖g‖ ^ 2 ≤ ε ^ 2 * ‖φ‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) happ 2
  have hφpos : 0 < ‖φ‖ := norm_pos_iff.2 hφ
  set c : ℝ := 8 * ε ^ 2 + 32 / S ^ 2 with hc
  have hfinal : ∑ m ∈ B, ‖H (mulOp (f m) φ) - (E : ℂ) • mulOp (f m) φ‖ ^ 2 ≤
      c * ∑ m ∈ B, ‖mulOp (f m) φ‖ ^ 2 := by
    have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg L
    have key : 2 * ((2 * L + 1) * (ε ^ 2 * ‖φ‖ ^ 2)) + 2 * (8 * L / S ^ 2 * ‖φ‖ ^ 2) ≤
        c * (((L : ℝ) + 1) / 2 * ‖φ‖ ^ 2) := by
      have : c * (((L : ℝ) + 1) / 2 * ‖φ‖ ^ 2) -
          (2 * ((2 * L + 1) * (ε ^ 2 * ‖φ‖ ^ 2)) + 2 * (8 * L / S ^ 2 * ‖φ‖ ^ 2)) =
          (2 * ε ^ 2 + 16 / S ^ 2) * ‖φ‖ ^ 2 := by
        rw [hc]; field_simp; ring
      have : 0 ≤ (2 * ε ^ 2 + 16 / S ^ 2) * ‖φ‖ ^ 2 := by positivity
      linarith
    have hc0 : 0 ≤ c := by positivity
    calc _ ≤ 2 * ∑ m ∈ B, ‖mulOp (f m) g‖ ^ 2 + 2 * ∑ m ∈ B, ‖C m‖ ^ 2 := hXs
      _ ≤ 2 * ((2 * L + 1) * (ε ^ 2 * ‖φ‖ ^ 2)) + 2 * (8 * L / S ^ 2 * ‖φ‖ ^ 2) := by
          have := mul_le_mul_of_nonneg_left hg2 (by positivity : (0 : ℝ) ≤ 2 * L + 1)
          linarith
      _ ≤ c * (((L : ℝ) + 1) / 2 * ‖φ‖ ^ 2) := key
      _ ≤ c * ∑ m ∈ B, ‖mulOp (f m) φ‖ ^ 2 := mul_le_mul_of_nonneg_left hY hc0
  have hpos : 0 < ∑ m ∈ B, ‖mulOp (f m) φ‖ ^ 2 := lt_of_lt_of_le (by positivity) hY
  obtain ⟨m, -, hYm, hXm⟩ := exists_le_mul_of_sum_le B
    (fun m => ‖H (mulOp (f m) φ) - (E : ℂ) • mulOp (f m) φ‖ ^ 2)
    (fun m => ‖mulOp (f m) φ‖ ^ 2) c (fun m => sq_nonneg _) hfinal hpos
  refine ⟨m, ?_, ?_, ?_⟩
  · intro h0
    have hYm' : 0 < ‖mulOp (f m) φ‖ ^ 2 := hYm
    rw [h0, norm_zero] at hYm'
    norm_num at hYm'
  · intro k hk
    by_contra hc'
    apply hk
    rw [mulOp_apply (hf1 m)]
    simp only [hfdef]
    rw [testFn_eq_zero_of_le_abs hw hL (by omega)]
    simp
  · have hs2' : (√2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hcle : c ≤ (2 * √2 * ε + 4 * √2 / S) ^ 2 := by
      have e : (2 * √2 * ε + 4 * √2 / S) ^ 2 = (√2) ^ 2 * (2 * ε + 4 / S) ^ 2 := by ring
      rw [e, hs2', hc]
      have : 2 * (2 * ε + 4 / S) ^ 2 = 8 * ε ^ 2 + 32 / S ^ 2 + 32 * (ε / S) := by ring
      have : 0 ≤ ε / S := div_nonneg hε hS.le
      linarith
    have hsq : ‖H (mulOp (f m) φ) - (E : ℂ) • mulOp (f m) φ‖ ^ 2 ≤
        ((2 * √2 * ε + 4 * √2 / S) * ‖mulOp (f m) φ‖) ^ 2 := by
      rw [mul_pow]
      exact hXm.trans (mul_le_mul_of_nonneg_right hcle (sq_nonneg _))
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

/-! ### The estimate (5.13) -/

/-- **(5.13) (`cont-med`).** Let `v, b` be bounded and Lipschitz (constants `Kv`, `Kb`),
`θ` a phase with `b(θ + kα) ≠ 0` for all `k`, `E ∈ σ(H_{v,b,α,θ})`, `L ≥ 1`, and `S > 0` a
lower bound for all the sums `S_{+,m} = ∑_{k=m}^{m+L-1} 1/|b(θ+kα)|`.  Then for every `β`
and `ε > 0` there are a phase `θ̂` and `E' ∈ σ(H_{v,b,β,θ̂})` with
`|E - E'| ≤ (2Kb + Kv) L |α - β| + 4√2/S + ε`. -/
theorem ams_estimate {v b : ℝ → ℝ} (hv : BddFun v) (hb : BddFun b) {Kb Kv : ℝ}
    (hKb : 0 ≤ Kb) (hKv : 0 ≤ Kv) (hLb : ∀ x y, |b x - b y| ≤ Kb * |x - y|)
    (hLv : ∀ x y, |v x - v y| ≤ Kv * |x - y|) {α θ : ℝ} (hgood : ∀ k : ℤ, b (θ + k * α) ≠ 0)
    {E : ℝ} (hE : E ∈ spectrum ℝ (jacobi v b α θ)) {L : ℕ} (hL : 1 ≤ L) {S : ℝ} (hS : 0 < S)
    (hSle : ∀ m : ℤ, S ≤ Splus (bw b α θ) L m) (β : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ θ' E' : ℝ, E' ∈ spectrum ℝ (jacobi v b β θ') ∧
      |E - E'| ≤ (2 * Kb + Kv) * L * |α - β| + 4 * √2 / S + ε := by
  obtain ⟨φ₀, hφ₀, h₀⟩ := exists_approx_eigen (jacobi_isSelfAdjoint hv hb α θ) hE
    (ε := ε / 8) (by positivity)
  obtain ⟨φ, hφ, ⟨N, hN⟩, hφa⟩ := exists_finsupp_approx (by positivity) hφ₀ h₀
  obtain ⟨m, hψ, hψsupp, hψa⟩ := ams_quant_core hv hb hgood hL hS hSle
    (ε := 2 * (ε / 8)) (by positivity) hφ hN hφa
  set ψ := mulOp (testFn (bw b α θ) L m) φ
  set θ' := θ + m * (α - β)
  set δ := |α - β|
  have hdiff : ‖jacobi v b β θ' ψ - jacobi v b α θ ψ‖ ≤
      (2 * (Kb * L * δ) + Kv * L * δ) * ‖ψ‖ := by
    refine norm_jacobi_sub_le hv hb hv hb (by positivity) (by positivity) (fun k hk => ?_)
    have hkm := hψsupp k hk
    have hkm' : |(k : ℝ) - m| ≤ L - 1 := by
      have : |k - m| ≤ (L : ℤ) - 1 := by omega
      have := (Int.cast_le (R := ℝ)).2 this
      push_cast at this
      exact this
    have hx : ∀ t : ℝ, |t - m| ≤ L → |b (θ' + t * β) - b (θ + t * α)| ≤ Kb * L * δ := by
      intro t ht
      refine (hLb _ _).trans ?_
      have : θ' + t * β - (θ + t * α) = (m - t) * (α - β) := by simp only [θ']; ring
      rw [this, abs_mul, abs_sub_comm, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ht (abs_nonneg _)) hKb
    refine ⟨hx k (by linarith), hx ((k : ℝ) - 1) ?_, ?_⟩
    · have : (k : ℝ) - 1 - m = ((k : ℝ) - m) - 1 := by ring
      rw [this]
      calc |(k : ℝ) - m - 1| ≤ |(k : ℝ) - m| + |(1 : ℝ)| := abs_sub _ _
        _ ≤ L := by rw [abs_one]; linarith
    · refine (hLv _ _).trans ?_
      have : θ' + k * β - (θ + k * α) = (m - k) * (α - β) := by simp only [θ']; ring
      rw [this, abs_mul, abs_sub_comm, mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith)
        (abs_nonneg _)) hKv
  have htot : ‖jacobi v b β θ' ψ - (E : ℂ) • ψ‖ ≤
      ((2 * Kb + Kv) * L * δ + (2 * √2 * (2 * (ε / 8)) + 4 * √2 / S)) * ‖ψ‖ := by
    calc ‖jacobi v b β θ' ψ - (E : ℂ) • ψ‖
        = ‖(jacobi v b β θ' ψ - jacobi v b α θ ψ) + (jacobi v b α θ ψ - (E : ℂ) • ψ)‖ := by
          congr 1; abel
      _ ≤ ‖jacobi v b β θ' ψ - jacobi v b α θ ψ‖ + ‖jacobi v b α θ ψ - (E : ℂ) • ψ‖ :=
          norm_add_le _ _
      _ ≤ (2 * (Kb * L * δ) + Kv * L * δ) * ‖ψ‖ +
          (2 * √2 * (2 * (ε / 8)) + 4 * √2 / S) * ‖ψ‖ := add_le_add hdiff hψa
      _ = _ := by ring
  obtain ⟨E', hE', hdist⟩ := exists_mem_spectrum_near (jacobi_isSelfAdjoint hv hb β θ') hψ htot
  refine ⟨θ', E', hE', hdist.trans ?_⟩
  have hs : √2 ≤ 2 := by
    rw [show (2 : ℝ) = √4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have : 2 * √2 * (2 * (ε / 8)) ≤ ε := by nlinarith
  linarith

/-! ### From fibres to `σ(M_{v,b,α})` -/

/-- Phases with `b(θ + kα) ≠ 0` for all `k ∈ ℤ` are dense, if `b` has countably many
zeros. -/
lemma exists_good_phase {b : ℝ → ℝ} (hZ : {x | b x = 0}.Countable) (α θ₀ : ℝ) {η : ℝ}
    (hη : 0 < η) : ∃ θ, |θ - θ₀| < η ∧ ∀ k : ℤ, b (θ + k * α) ≠ 0 := by
  set Bad : Set ℝ := ⋃ k : ℤ, (fun x => x - k * α) '' {x | b x = 0}
  have hBad : Bad.Countable := Set.countable_iUnion fun k => hZ.image _
  obtain ⟨θ, hθ, hdist⟩ := (hBad.dense_compl ℝ).exists_dist_lt θ₀ hη
  refine ⟨θ, by rw [abs_sub_comm]; exact hdist, fun k hk => hθ ?_⟩
  exact Set.mem_iUnion.2 ⟨k, ⟨θ + k * α, hk, by ring⟩⟩

/-- Spectral stability under a change of phase (for Lipschitz coefficients). -/
lemma exists_mem_spectrum_phase {v b : ℝ → ℝ} (hv : BddFun v) (hb : BddFun b) {Kb Kv : ℝ}
    (hKb : 0 ≤ Kb) (hKv : 0 ≤ Kv) (hLb : ∀ x y, |b x - b y| ≤ Kb * |x - y|)
    (hLv : ∀ x y, |v x - v y| ≤ Kv * |x - y|) {α θ₀ θ E₀ : ℝ}
    (hE₀ : E₀ ∈ spectrum ℝ (jacobi v b α θ₀)) {η : ℝ} (hη : 0 < η) :
    ∃ E₁ ∈ spectrum ℝ (jacobi v b α θ), |E₀ - E₁| ≤ (2 * Kb + Kv) * |θ - θ₀| + η := by
  obtain ⟨φ, hφ, hφa⟩ := exists_approx_eigen (jacobi_isSelfAdjoint hv hb α θ₀) hE₀ hη
  have hdiff : ‖jacobi v b α θ φ - jacobi v b α θ₀ φ‖ ≤
      (2 * (Kb * |θ - θ₀|) + Kv * |θ - θ₀|) * ‖φ‖ := by
    refine norm_jacobi_sub_le hv hb hv hb (by positivity) (by positivity) (fun k _ => ?_)
    refine ⟨(hLb _ _).trans (le_of_eq ?_), (hLb _ _).trans (le_of_eq ?_),
      (hLv _ _).trans (le_of_eq ?_)⟩ <;> ring_nf
  have htot : ‖jacobi v b α θ φ - (E₀ : ℂ) • φ‖ ≤ ((2 * Kb + Kv) * |θ - θ₀| + η) * ‖φ‖ := by
    calc ‖jacobi v b α θ φ - (E₀ : ℂ) • φ‖
        = ‖(jacobi v b α θ φ - jacobi v b α θ₀ φ) + (jacobi v b α θ₀ φ - (E₀ : ℂ) • φ)‖ := by
          congr 1; abel
      _ ≤ _ := norm_add_le _ _
      _ ≤ (2 * (Kb * |θ - θ₀|) + Kv * |θ - θ₀|) * ‖φ‖ + η * ‖φ‖ := add_le_add hdiff hφa
      _ = _ := by ring
  exact exists_mem_spectrum_near (jacobi_isSelfAdjoint hv hb α θ) hφ htot

/-- **Distance from `σ(M_{v,b,α})` to `σ(M_{v,b,β})`** (the conclusion of (5.13) after
`ε ↓ 0`, using `S_min ≥ S`).  Here `S` is a lower bound for all sums
`∑_{k=m}^{m+L-1} 1/|b(θ+kα)|` over all phases `θ` with no zero of `b` on the orbit. -/
theorem infDist_sigmaM_le {v b : ℝ → ℝ} (hv : BddFun v) (hb : BddFun b) {Kb Kv : ℝ}
    (hKb : 0 ≤ Kb) (hKv : 0 ≤ Kv) (hLb : ∀ x y, |b x - b y| ≤ Kb * |x - y|)
    (hLv : ∀ x y, |v x - v y| ≤ Kv * |x - y|) (hZ : {x | b x = 0}.Countable) {α : ℝ}
    {L : ℕ} (hL : 1 ≤ L) {S : ℝ} (hS : 0 < S)
    (hSall : ∀ θ : ℝ, (∀ k : ℤ, b (θ + k * α) ≠ 0) → ∀ m : ℤ, S ≤ Splus (bw b α θ) L m)
    {E : ℝ} (hE : E ∈ sigmaM v b α) (β : ℝ) :
    Metric.infDist E (sigmaM v b β) ≤ (2 * Kb + Kv) * L * |α - β| + 4 * √2 / S := by
  refine le_of_forall_pos_lt_add (fun η hη => ?_)
  obtain ⟨E₀, hE₀, hdE⟩ := Metric.mem_closure_iff.1 hE (η / 4) (by positivity)
  obtain ⟨θ₀, hθ₀⟩ := Set.mem_iUnion.1 hE₀
  obtain ⟨θ, hθ, hgood⟩ := exists_good_phase hZ α θ₀ (η := η / (8 * ((2 * Kb + Kv) + 1)))
    (by positivity)
  obtain ⟨E₁, hE₁, hd1⟩ := exists_mem_spectrum_phase hv hb hKb hKv hLb hLv hθ₀
    (θ := θ) (η := η / 8) (by positivity)
  obtain ⟨θ', E', hE', hd2⟩ := ams_estimate hv hb hKb hKv hLb hLv hgood hE₁ hL hS
    (hSall θ hgood) β (ε := η / 4) (by positivity)
  have hmem : E' ∈ sigmaM v b β := subset_closure (Set.mem_iUnion.2 ⟨θ', hE'⟩)
  have hK1 : (2 * Kb + Kv) * |θ - θ₀| ≤ η / 8 := by
    have hK0 : 0 ≤ 2 * Kb + Kv := by positivity
    calc (2 * Kb + Kv) * |θ - θ₀| ≤ ((2 * Kb + Kv) + 1) * (η / (8 * ((2 * Kb + Kv) + 1))) := by
          apply mul_le_mul (by linarith) hθ.le (abs_nonneg _) (by linarith)
      _ = η / 8 := by field_simp
  calc Metric.infDist E (sigmaM v b β) ≤ dist E E' := Metric.infDist_le_dist_of_mem hmem
    _ ≤ |E - E₀| + |E₀ - E₁| + |E₁ - E'| := by
        rw [Real.dist_eq]
        calc |E - E'| = |(E - E₀) + (E₀ - E₁) + (E₁ - E')| := by ring_nf
          _ ≤ _ := abs_add_three _ _ _
    _ < η / 4 + (η / 8 + η / 8) + ((2 * Kb + Kv) * L * |α - β| + 4 * √2 / S + η / 4) := by
        rw [Real.dist_eq] at hdE
        linarith
    _ = (2 * Kb + Kv) * L * |α - β| + 4 * √2 / S + (3 / 4) * η := by ring
    _ < _ := by linarith

/-- `σ(M_{v,b,β})` is nonempty (the fibre operators are self-adjoint on a nonzero space). -/
lemma sigmaM_nonempty {v b : ℝ → ℝ} (hv : BddFun v) (hb : BddFun b) (β : ℝ) :
    (sigmaM v b β).Nonempty := by
  obtain ⟨E, hE⟩ := AMO.spectrum_real_nonempty (jacobi_isSelfAdjoint hv hb β 0)
  exact ⟨E, subset_closure (Set.mem_iUnion.2 ⟨0, hE⟩)⟩

/-- If `infDist E σ(M_{v,b,β}) ≤ r`, then there is `E' ∈ σ(M_{v,b,β})` with `|E - E'| ≤ r`. -/
lemma exists_mem_sigmaM_of_infDist_le {v b : ℝ → ℝ} (hv : BddFun v) (hb : BddFun b)
    {β E r : ℝ} (h : Metric.infDist E (sigmaM v b β) ≤ r) :
    ∃ E' ∈ sigmaM v b β, |E - E'| ≤ r := by
  obtain ⟨E', hE', hd⟩ := (isClosed_closure : IsClosed (sigmaM v b β)).exists_infDist_eq_dist
    (sigmaM_nonempty hv hb β) E
  exact ⟨E', hE', by rw [← Real.dist_eq, ← hd]; exact h⟩

end CAH
