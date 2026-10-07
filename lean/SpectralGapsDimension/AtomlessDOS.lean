/-
# The density of states has no atoms  (Paper I, Lemma 2.8, atomlessness half)

Let `x ↦ H_x` be a norm-continuous, `1`-periodic, covariant (`H_{x+α} = U H_x U^*`) family of
self-adjoint operators on `ℓ²(ℤ)`, and let `ν` be its density-of-states measure.  If for every
phase the eigenspace `ker (H_x - E)` is finite-dimensional of dimension `≤ d` (uniformly in `x`),
then `ν {E} = 0`.

The proof only uses the continuous functional calculus.  With the bumps
`b_k(t) = max 0 (1 - (k+1)|t - E|)`:

1. for one self-adjoint `T` and one vector `φ`, the decreasing limit of `⟪φ, b_k(T) φ⟫` is at most
   `‖P φ‖²`, where `P` is the orthogonal projection onto `ker (T - E)` (the vectors `b_k(T) φ`
   form a Cauchy sequence whose limit lies in the kernel);
2. Bessel: `∑_{n ∈ s} ‖P δ_n‖² ≤ dim ker (T - E)`;
3. covariance moves `δ₀` to `δ_n`, so `∫ b_k dν = ∫₀¹ (1/N) ∑_{n<N} ⟪δ_n, b_k(H_x) δ_n⟫ dx`;
4. dominated convergence in `k` gives `ν {E} ≤ d / N` for all `N ≥ 1`.
-/
import AnalyticPerturbationsAMO.IDSSupport
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section

open scoped ENNReal InnerProductSpace ComplexConjugate Topology BoundedContinuousFunction
open MeasureTheory Set Filter AMO

namespace SGD

/-! ### The bumps `b_k` -/

/-- The bump `b_k(t) = max 0 (1 - (k+1)|t - E|)` around `E`
(Paper I, Lemma 2.8 (atomlessness half)). -/
def atomBump (E : ℝ) (k : ℕ) (t : ℝ) : ℝ := max 0 (1 - ((k : ℝ) + 1) * |t - E|)

lemma atomBump_continuous (E : ℝ) (k : ℕ) : Continuous (atomBump E k) :=
  continuous_const.max (continuous_const.sub
    (continuous_const.mul ((continuous_id.sub continuous_const).abs)))

lemma atomBump_nonneg (E : ℝ) (k : ℕ) (t : ℝ) : 0 ≤ atomBump E k t := le_max_left _ _

lemma atomBump_le_one (E : ℝ) (k : ℕ) (t : ℝ) : atomBump E k t ≤ 1 := by
  refine max_le zero_le_one ?_
  have : 0 ≤ ((k : ℝ) + 1) * |t - E| := by positivity
  linarith

lemma atomBump_self (E : ℝ) (k : ℕ) : atomBump E k E = 1 := by
  simp [atomBump]

lemma atomBump_antitone (E t : ℝ) : Antitone fun k => atomBump E k t := by
  intro k l hkl
  have hkl' : (k : ℝ) ≤ l := by exact_mod_cast hkl
  have := abs_nonneg (t - E)
  refine max_le_max le_rfl ?_
  nlinarith

lemma abs_sub_mul_atomBump_le (E : ℝ) (k : ℕ) (t : ℝ) :
    |t - E| * atomBump E k t ≤ 1 / ((k : ℝ) + 1) := by
  have ha : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hs := abs_nonneg (t - E)
  unfold atomBump
  rcases le_total (1 - ((k : ℝ) + 1) * |t - E|) 0 with h | h
  · rw [max_eq_left h, mul_zero]; positivity
  · rw [max_eq_right h, le_div_iff₀ ha]
    nlinarith

lemma indicator_le_atomBump (E : ℝ) (k : ℕ) (t : ℝ) :
    ({E} : Set ℝ).indicator 1 t ≤ atomBump E k t := by
  by_cases ht : t = E
  · subst ht; simp [atomBump_self]
  · rw [indicator_of_notMem (by simpa using ht)]
    exact atomBump_nonneg E k t

/-- The bump `b_k` as a bounded continuous function. -/
def atomBumpBCF (E : ℝ) (k : ℕ) : ℝ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (atomBump E k) (atomBump_continuous E k) 1
    (fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (atomBump_nonneg E k t)]
      exact atomBump_le_one E k t)

lemma atomBumpBCF_apply (E : ℝ) (k : ℕ) (t : ℝ) : atomBumpBCF E k t = atomBump E k t := rfl

/-! ### Elementary functional-calculus facts for one self-adjoint operator

We only use the complex continuous functional calculus, applied to real-valued functions
`z ↦ f (re z)`, exactly as in `AMO.IsDOSMeasure`. -/

lemma inner_delta_left' (n : ℤ) (u : L2 ℤ) : ⟪delta n, u⟫_ℂ = u n := by
  rw [delta, lp.inner_single_left]
  simp

/-- `f(T)` for a real function `f`, through the complex functional calculus. -/
def rcfc (f : ℝ → ℝ) (T : Op ℤ) : Op ℤ := cfc (fun z : ℂ => ((f z.re : ℝ) : ℂ)) T

lemma continuous_ofReal_comp_re {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous fun z : ℂ => ((f z.re : ℝ) : ℂ) :=
  Complex.continuous_ofReal.comp (hf.comp Complex.continuous_re)

lemma rcfc_isSelfAdjoint (f : ℝ → ℝ) (T : Op ℤ) : IsSelfAdjoint (rcfc f T) := by
  show star (rcfc f T) = rcfc f T
  unfold rcfc
  rw [← cfc_star]
  congr 1
  funext z
  simp

lemma rcfc_mul {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (T : Op ℤ) :
    rcfc (fun t => f t * g t) T = rcfc f T * rcfc g T := by
  unfold rcfc
  rw [← cfc_mul (fun z : ℂ => ((f z.re : ℝ) : ℂ)) (fun z : ℂ => ((g z.re : ℝ) : ℂ)) T
    (continuous_ofReal_comp_re hf).continuousOn (continuous_ofReal_comp_re hg).continuousOn]
  congr 1
  funext z
  simp only [Complex.ofReal_mul]

lemma rcfc_sub {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) (T : Op ℤ) :
    rcfc (fun t => f t - g t) T = rcfc f T - rcfc g T := by
  unfold rcfc
  rw [← cfc_sub (fun z : ℂ => ((f z.re : ℝ) : ℂ)) (fun z : ℂ => ((g z.re : ℝ) : ℂ)) T
    (continuous_ofReal_comp_re hf).continuousOn (continuous_ofReal_comp_re hg).continuousOn]
  congr 1
  funext z
  simp only [Complex.ofReal_sub]

lemma norm_sq_apply_eq_re_inner {A : Op ℤ} (hA : IsSelfAdjoint A) (φ : L2 ℤ) :
    ‖A φ‖ ^ 2 = RCLike.re ⟪φ, (A * A) φ⟫_ℂ := by
  have : ⟪φ, A (A φ)⟫_ℂ = ⟪A φ, A φ⟫_ℂ := by
    rw [← ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.star_eq_adjoint,
      hA.star_eq]
  rw [ContinuousLinearMap.mul_apply, this, inner_self_eq_norm_sq]

/-- `⟪φ, f²(T) φ⟫ = ‖f(T) φ‖²`. -/
lemma re_inner_rcfc_mul_self {f : ℝ → ℝ} (hf : Continuous f) (T : Op ℤ) (φ : L2 ℤ) :
    RCLike.re ⟪φ, rcfc (fun t => f t * f t) T φ⟫_ℂ = ‖rcfc f T φ‖ ^ 2 := by
  rw [rcfc_mul hf hf, norm_sq_apply_eq_re_inner (rcfc_isSelfAdjoint f T)]

lemma re_inner_rcfc_nonneg {T : Op ℤ} {f : ℝ → ℝ} (hf : Continuous f) (h0 : ∀ t, 0 ≤ f t)
    (φ : L2 ℤ) : 0 ≤ RCLike.re ⟪φ, rcfc f T φ⟫_ℂ := by
  have hf' : f = fun t => Real.sqrt (f t) * Real.sqrt (f t) := by
    funext t; rw [Real.mul_self_sqrt (h0 t)]
  rw [hf', re_inner_rcfc_mul_self (f := fun t => Real.sqrt (f t)) (Real.continuous_sqrt.comp hf)]
  positivity

/-- Order on real functions turns into order on the quadratic forms. -/
lemma re_inner_rcfc_mono {T : Op ℤ} {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ t, f t ≤ g t) (φ : L2 ℤ) :
    RCLike.re ⟪φ, rcfc f T φ⟫_ℂ ≤ RCLike.re ⟪φ, rcfc g T φ⟫_ℂ := by
  have h := re_inner_rcfc_nonneg (T := T) (f := fun t => g t - f t) (hg.sub hf) (fun t => sub_nonneg.2 (hfg t)) φ
  rw [rcfc_sub hg hf, ContinuousLinearMap.sub_apply, inner_sub_right, map_sub] at h
  linarith

/-- For `0 ≤ f ≤ 1`: `‖f(T) φ‖² ≤ ⟪φ, f(T) φ⟫`. -/
lemma norm_sq_rcfc_le {T : Op ℤ} {f : ℝ → ℝ} (hf : Continuous f) (h0 : ∀ t, 0 ≤ f t)
    (h1 : ∀ t, f t ≤ 1) (φ : L2 ℤ) :
    ‖rcfc f T φ‖ ^ 2 ≤ RCLike.re ⟪φ, rcfc f T φ⟫_ℂ := by
  rw [← re_inner_rcfc_mul_self hf]
  exact re_inner_rcfc_mono (f := fun t => f t * f t) (hf.mul hf) hf (fun t => by nlinarith [h0 t, h1 t]) φ

lemma sub_smul_one_eq_cfc {T : Op ℤ} (hT : IsSelfAdjoint T) (E : ℝ) :
    (T - (E : ℂ) • 1 : Op ℤ) = cfc (fun z : ℂ => z - (E : ℂ)) T := by
  have hn : IsStarNormal T := hT.isStarNormal
  rw [cfc_sub (fun z : ℂ => z) (fun _ => (E : ℂ)) T, cfc_id' ℂ T hn, cfc_const (E : ℂ) T hn,
    Algebra.algebraMap_eq_smul_one]

lemma norm_sub_smul_mul_rcfc_atomBump_le {T : Op ℤ} (hT : IsSelfAdjoint T) (E : ℝ) (k : ℕ) :
    ‖(T - (E : ℂ) • 1 : Op ℤ) * rcfc (atomBump E k) T‖ ≤ 1 / ((k : ℝ) + 1) := by
  rw [sub_smul_one_eq_cfc hT E, rcfc, ← cfc_mul (fun z : ℂ => z - (E : ℂ))
    (fun z : ℂ => ((atomBump E k z.re : ℝ) : ℂ)) T (by fun_prop)
    (continuous_ofReal_comp_re (atomBump_continuous E k)).continuousOn]
  refine norm_cfc_le (by positivity) (fun z hz => ?_)
  have hzre : z = (z.re : ℂ) := hT.mem_spectrum_eq_re hz
  rw [hzre, Complex.ofReal_re, ← Complex.ofReal_sub, ← Complex.ofReal_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_mul, abs_of_nonneg (atomBump_nonneg E k _)]
  exact abs_sub_mul_atomBump_le E k _

/-! ### Step 1: the limit of `⟪φ, b_k(T) φ⟫` is controlled by the eigenprojection -/

/-- The eigenspace `ker (T - E)`. -/
abbrev eigKer (T : Op ℤ) (E : ℝ) : Submodule ℂ (L2 ℤ) :=
  LinearMap.ker ((T - (E : ℂ) • 1 : Op ℤ) : L2 ℤ →ₗ[ℂ] L2 ℤ)

instance hasOrthogonalProjection_of_finiteDimensional (K : Submodule ℂ (L2 ℤ))
    [FiniteDimensional ℂ K] : K.HasOrthogonalProjection :=
  haveI : CompleteSpace K := FiniteDimensional.complete ℂ K
  inferInstance

/-- **Step 1 (Paper I, Lemma 2.8 (atomlessness half)).**  For a self-adjoint `T` with
finite-dimensional eigenspace `K = ker (T - E)`, the decreasing limit of `⟪φ, b_k(T) φ⟫` is at
most `‖P_K φ‖²`. -/
theorem iInf_re_inner_atomBump_le {T : Op ℤ} (hT : IsSelfAdjoint T) (E : ℝ)
    [FiniteDimensional ℂ (eigKer T E)] (φ : L2 ℤ) :
    ⨅ k, RCLike.re ⟪φ, rcfc (atomBump E k) T φ⟫_ℂ ≤ ‖(eigKer T E).starProjection φ‖ ^ 2 := by
  set G : ℕ → Op ℤ := fun k => rcfc (atomBump E k) T with hG
  set a : ℕ → ℝ := fun k => RCLike.re ⟪φ, G k φ⟫_ℂ with ha
  set μ := ⨅ k, a k with hμdef
  change μ ≤ _
  have ha_anti : Antitone a := fun k l hkl =>
    re_inner_rcfc_mono (atomBump_continuous E l) (atomBump_continuous E k)
      (fun t => atomBump_antitone E t hkl) φ
  have ha_nonneg : ∀ k, 0 ≤ a k := fun k =>
    re_inner_rcfc_nonneg (atomBump_continuous E k) (atomBump_nonneg E k) φ
  have hbdd : BddBelow (range a) := ⟨0, by rintro _ ⟨k, rfl⟩; exact ha_nonneg k⟩
  have hμ : Tendsto a atTop (𝓝 μ) := tendsto_atTop_ciInf ha_anti hbdd
  have hμle : ∀ k, μ ≤ a k := fun k => ciInf_le hbdd k
  have hμ0 : 0 ≤ μ := le_ciInf ha_nonneg
  -- the Cauchy estimate
  have hdiff : ∀ k l, k ≤ l → ‖G k φ - G l φ‖ ^ 2 ≤ a k - a l := by
    intro k l hkl
    have hcont : Continuous fun t => atomBump E k t - atomBump E l t :=
      (atomBump_continuous E k).sub (atomBump_continuous E l)
    have hsub : G k - G l = rcfc (fun t => atomBump E k t - atomBump E l t) T :=
      (rcfc_sub (atomBump_continuous E k) (atomBump_continuous E l) T).symm
    have h := norm_sq_rcfc_le (T := T) hcont
      (fun t => sub_nonneg.2 (atomBump_antitone E t hkl))
      (fun t => by linarith [atomBump_le_one E k t, atomBump_nonneg E l t]) φ
    rw [← hsub, ContinuousLinearMap.sub_apply, inner_sub_right, map_sub] at h
    exact h
  have hcs : CauchySeq fun k => G k φ := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hev := (hμ.eventually (gt_mem_nhds (show μ < μ + ε ^ 2 from lt_add_of_pos_right _ (by positivity))))
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hdiff N n hn
    have h2 := hN N le_rfl
    have h3 := hμle n
    rw [dist_eq_norm, ← norm_neg, neg_sub]
    have hd : ‖G N φ - G n φ‖ ^ 2 < ε ^ 2 := by linarith
    have hn0 := norm_nonneg (G N φ - G n φ)
    nlinarith
  obtain ⟨v, hv⟩ := cauchySeq_tendsto_of_complete hcs
  -- the limit lies in the eigenspace
  set A : Op ℤ := (T - (E : ℂ) • 1 : Op ℤ) with hA
  have hAv : A v = 0 := by
    have h1 : Tendsto (fun k => A (G k φ)) atTop (𝓝 (A v)) :=
      (A.continuous.tendsto v).comp hv
    have h2 : Tendsto (fun k => A (G k φ)) atTop (𝓝 0) := by
      refine squeeze_zero_norm (a := fun k : ℕ => 1 / ((k : ℝ) + 1) * ‖φ‖) (fun k => ?_) ?_
      · rw [← ContinuousLinearMap.mul_apply]
        exact (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right
          (norm_sub_smul_mul_rcfc_atomBump_le hT E k) (norm_nonneg _))
      · simpa using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const ‖φ‖
    exact tendsto_nhds_unique h1 h2
  have hvK : v ∈ eigKer T E := by
    rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
    exact hAv
  -- `μ = re ⟪φ, v⟫` and `‖v‖² ≤ μ`
  have hμv : μ = RCLike.re ⟪φ, v⟫_ℂ := by
    have h : Tendsto a atTop (𝓝 (RCLike.re ⟪φ, v⟫_ℂ)) :=
      (RCLike.continuous_re.tendsto _).comp (tendsto_const_nhds.inner hv)
    exact tendsto_nhds_unique hμ h
  have hvμ : ‖v‖ ^ 2 ≤ μ := by
    refine le_of_tendsto_of_tendsto' ((hv.norm).pow 2) hμ (fun k => ?_)
    exact norm_sq_rcfc_le (atomBump_continuous E k) (atomBump_nonneg E k) (atomBump_le_one E k) φ
  -- replace `φ` by its projection
  set P := (eigKer T E).starProjection with hP
  have hinner : ⟪φ, v⟫_ℂ = ⟪P φ, v⟫_ℂ := by
    have h := (eigKer T E).starProjection_inner_eq_zero φ v hvK
    rw [inner_sub_left, sub_eq_zero] at h
    exact h
  have hle : μ ≤ ‖P φ‖ * ‖v‖ := by
    rw [hμv, hinner]
    exact re_inner_le_norm _ _
  have hp0 := norm_nonneg (P φ)
  have hw0 := norm_nonneg v
  have h1 : μ ^ 2 ≤ (‖P φ‖ * ‖v‖) ^ 2 := pow_le_pow_left₀ hμ0 hle 2
  have h3 : ‖P φ‖ ^ 2 * ‖v‖ ^ 2 ≤ ‖P φ‖ ^ 2 * μ := mul_le_mul_of_nonneg_left hvμ (sq_nonneg _)
  rcases hμ0.eq_or_lt with h | h
  · rw [← h]; positivity
  · nlinarith

/-! ### Step 2: Bessel's inequality for the eigenprojection -/

/-- **Step 2 (Paper I, Lemma 2.8 (atomlessness half)).**  `∑_{n ∈ s} ‖P_K δ_n‖² ≤ dim K` for a
finite-dimensional subspace `K ⊆ ℓ²(ℤ)`. -/
theorem sum_norm_sq_starProjection_delta_le (K : Submodule ℂ (L2 ℤ)) [FiniteDimensional ℂ K]
    (s : Finset ℤ) :
    ∑ n ∈ s, ‖K.starProjection (delta n)‖ ^ 2 ≤ Module.finrank ℂ K := by
  set e := stdOrthonormalBasis ℂ K with he
  have hPφ : ∀ φ : L2 ℤ, ‖K.starProjection φ‖ ^ 2 = ∑ j, ‖⟪(e j : L2 ℤ), φ⟫_ℂ‖ ^ 2 := by
    intro φ
    have h := e.sum_sq_norm_inner_right (K.orthogonalProjectionOnto φ)
    rw [K.starProjection_apply, Submodule.norm_coe, ← h]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 2
    rw [Submodule.coe_inner, ← K.starProjection_apply]
    have h0 := K.starProjection_inner_eq_zero φ (e j) (e j).2
    rw [inner_eq_zero_symm, inner_sub_right, sub_eq_zero] at h0
    exact h0.symm
  have hrow : ∀ j, ∑ n ∈ s, ‖⟪(e j : L2 ℤ), delta n⟫_ℂ‖ ^ 2 ≤ 1 := by
    intro j
    have hterm : ∀ n, ‖⟪(e j : L2 ℤ), delta n⟫_ℂ‖ = ‖(e j : L2 ℤ) n‖ := by
      intro n
      rw [norm_inner_symm, inner_delta_left']
    simp only [hterm]
    calc ∑ n ∈ s, ‖(e j : L2 ℤ) n‖ ^ 2 ≤ ∑' n, ‖(e j : L2 ℤ) n‖ ^ 2 :=
          (L2.summable_norm_sq _).sum_le_tsum s (fun _ _ => by positivity)
      _ = ‖(e j : L2 ℤ)‖ ^ 2 := (L2.norm_sq_eq_tsum _).symm
      _ = 1 := by rw [Submodule.norm_coe, e.orthonormal.1 j, one_pow]
  calc ∑ n ∈ s, ‖K.starProjection (delta n)‖ ^ 2
      = ∑ j, ∑ n ∈ s, ‖⟪(e j : L2 ℤ), delta n⟫_ℂ‖ ^ 2 := by
        simp only [hPφ]; exact Finset.sum_comm
    _ ≤ ∑ _j : Fin (Module.finrank ℂ K), (1 : ℝ) := Finset.sum_le_sum fun j _ => hrow j
    _ = Module.finrank ℂ K := by simp

/-! ### Step 3: covariance -/

/-- Covariance of the functional calculus `f ↦ f(H_x)` for real `f`. -/
lemma cfc_conj_U {α : ℝ} {Hx : ℝ → Op ℤ} (hsa : ∀ x, IsSelfAdjoint (Hx x))
    (hcov : ∀ x, Hx (x + α) = U α x * Hx x * star (U α x)) {f : ℝ → ℝ} (hf : Continuous f)
    (x : ℝ) : rcfc f (Hx (x + α)) = U α x * rcfc f (Hx x) * star (U α x) := by
  unfold rcfc
  have hu := U_mem_unitary α x
  have hG : Continuous fun z : ℂ => ((f z.re : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (hf.comp Complex.continuous_re)
  have h := StarAlgHomClass.map_cfc (Unitary.conjStarAlgAut ℂ (Op ℤ) ⟨U α x, hu⟩)
    (fun z : ℂ => ((f z.re : ℝ) : ℂ)) (Hx x) hG.continuousOn (by
      change Continuous fun T : Op ℤ => U α x * T * star (U α x)
      fun_prop) (hsa x).isStarNormal (by
      simp only [Unitary.conjStarAlgAut_apply]
      rw [← hcov]; exact (hsa _).isStarNormal)
  simp only [Unitary.conjStarAlgAut_apply] at h
  rw [hcov, ← h]

/-- The diagonal matrix element `x ↦ re ⟪δ_n, f(H_x) δ_n⟫`. -/
def diagElt (Hx : ℝ → Op ℤ) (f : ℝ → ℝ) (n : ℤ) (x : ℝ) : ℝ :=
  RCLike.re ⟪delta n, rcfc f (Hx x) (delta n)⟫_ℂ

lemma diagElt_shift {α : ℝ} {Hx : ℝ → Op ℤ} (hsa : ∀ x, IsSelfAdjoint (Hx x))
    (hcov : ∀ x, Hx (x + α) = U α x * Hx x * star (U α x)) {f : ℝ → ℝ} (hf : Continuous f)
    (n : ℤ) (x : ℝ) : diagElt Hx f n (x + α) = diagElt Hx f (n + 1) x := by
  have hs : star (U α x) = W α x (-1) 0 := by rw [U, star_W]; rfl
  unfold diagElt
  rw [cfc_conj_U hsa hcov hf x, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply, hs,
    Uinv_delta, inner_delta_left', U_apply, ← inner_delta_left' (n + 1)]

lemma diagElt_zero_add_nat {α : ℝ} {Hx : ℝ → Op ℤ} (hsa : ∀ x, IsSelfAdjoint (Hx x))
    (hcov : ∀ x, Hx (x + α) = U α x * Hx x * star (U α x)) {f : ℝ → ℝ} (hf : Continuous f)
    (m : ℕ) : ∀ x, diagElt Hx f 0 (x + m * α) = diagElt Hx f m x := by
  induction m with
  | zero => intro x; simp
  | succ m ih =>
    intro x
    rw [show x + ((m + 1 : ℕ) : ℝ) * α = (x + α) + (m : ℝ) * α by push_cast; ring, ih,
      diagElt_shift hsa hcov hf]
    push_cast; rfl

lemma diagElt_continuous {Hx : ℝ → Op ℤ} (hsa : ∀ x, IsSelfAdjoint (Hx x))
    (hcont : Continuous Hx) {f : ℝ → ℝ} (hf : Continuous f) (n : ℤ) :
    Continuous (diagElt Hx f n) := by
  have hc : Continuous fun x => rcfc f (Hx x) :=
    Continuous.cfc_of_mem_nhdsSet _ (s := univ) univ_mem hcont (fun x => (hsa x).isStarNormal)
      (continuous_ofReal_comp_re hf).continuousOn
  exact RCLike.continuous_re.comp (continuous_const.inner (hc.clm_apply continuous_const))

lemma integral_diagElt_eq {α : ℝ} {Hx : ℝ → Op ℤ} (hsa : ∀ x, IsSelfAdjoint (Hx x))
    (hper : ∀ x, Hx (x + 1) = Hx x)
    (hcov : ∀ x, Hx (x + α) = U α x * Hx x * star (U α x)) {f : ℝ → ℝ} (hf : Continuous f)
    (m : ℕ) :
    ∫ x in (0 : ℝ)..1, diagElt Hx f m x = ∫ x in (0 : ℝ)..1, diagElt Hx f 0 x := by
  have hperiodic : Function.Periodic (diagElt Hx f 0) 1 := fun x => by
    simp only [diagElt, hper]
  simp_rw [← diagElt_zero_add_nat hsa hcov hf m]
  rw [intervalIntegral.integral_comp_add_right (diagElt Hx f 0) ((m : ℝ) * α), zero_add,
    add_comm 1, hperiodic.intervalIntegral_add_eq ((m : ℝ) * α) 0, zero_add]

/-! ### Step 4: the atom -/

/-- **Paper I, Lemma 2.8 (atomlessness half).**  If every eigenspace `ker (H_x - E)` is
finite-dimensional of dimension `≤ d` (uniformly in the phase), then the density-of-states
measure has no atom at `E`. -/
theorem dos_measure_singleton_eq_zero {α : ℝ} {Hx : ℝ → Op ℤ} {ν : Measure ℝ}
    (hν : IsDOSMeasure Hx ν) (hsa : ∀ x, IsSelfAdjoint (Hx x)) (hcont : Continuous Hx)
    (hper : ∀ x, Hx (x + 1) = Hx x)
    (hcov : ∀ x, Hx (x + α) = U α x * Hx x * star (U α x))
    {E : ℝ} {d : ℕ}
    (hfin : ∀ x, FiniteDimensional ℂ
      (LinearMap.ker ((Hx x - (E : ℂ) • 1 : Op ℤ) : L2 ℤ →ₗ[ℂ] L2 ℤ)))
    (hdim : ∀ x, Module.finrank ℂ
      (LinearMap.ker ((Hx x - (E : ℂ) • 1 : Op ℤ) : L2 ℤ →ₗ[ℂ] L2 ℤ)) ≤ d) :
    ν {E} = 0 := by
  have := hν.1
  set g : ℕ → ℤ → ℝ → ℝ := fun k n x => diagElt Hx (atomBump E k) n x with hg
  have hgc : ∀ k n, Continuous (g k n) := fun k n =>
    diagElt_continuous hsa hcont (atomBump_continuous E k) n
  have hg_anti : ∀ n x, Antitone fun k => g k n x := fun n x k l hkl =>
    re_inner_rcfc_mono (atomBump_continuous E l) (atomBump_continuous E k)
      (fun t => atomBump_antitone E t hkl) _
  have hg_nonneg : ∀ k n x, 0 ≤ g k n x := fun k n x =>
    re_inner_rcfc_nonneg (atomBump_continuous E k) (atomBump_nonneg E k) _
  -- `ν {E} ≤ ∫ b_k dν = ∫₀¹ g_k 0`
  have hatom : ∀ k, (ν {E}).toReal ≤ ∫ x in (0 : ℝ)..1, g k 0 x := by
    intro k
    have h := hν.2 (atomBumpBCF E k)
    have hint : ∫ t, atomBumpBCF E k t ∂ν = ∫ x in (0 : ℝ)..1, g k 0 x := by
      rw [h]
      refine intervalIntegral.integral_congr (fun x _ => ?_)
      rfl
    rw [← hint, ← measureReal_def, ← integral_indicator_one (measurableSet_singleton E)]
    refine integral_mono ((integrable_const (μ := ν) (1 : ℝ)).indicator (measurableSet_singleton E))
      ((atomBumpBCF E k).integrable ν) (fun t => ?_)
    rw [atomBumpBCF_apply]
    exact indicator_le_atomBump E k t
  have key : ∀ N : ℕ, 0 < N → (ν {E}).toReal ≤ d / N := by
    intro N hN
    have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    set F : ℕ → ℝ → ℝ := fun k x => (1 / (N : ℝ)) * ∑ m ∈ Finset.range N, g k m x with hF
    set L : ℝ → ℝ := fun x => (1 / (N : ℝ)) * ∑ m ∈ Finset.range N, ⨅ k, g k m x with hL
    have hFc : ∀ k, Continuous (F k) := fun k =>
      continuous_const.mul (continuous_finsetSum _ fun m _ => hgc k m)
    -- `∫₀¹ g_k 0 = ∫₀¹ F_k`
    have hFint : ∀ k, ∫ x in (0 : ℝ)..1, g k 0 x = ∫ x in (0 : ℝ)..1, F k x := by
      intro k
      simp only [hF]
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum (f := fun (m : ℕ) x => g k (m : ℤ) x)
        (fun m _ => (hgc k m).intervalIntegrable 0 1)]
      rw [Finset.sum_congr rfl (fun m _ =>
        integral_diagElt_eq hsa hper hcov (atomBump_continuous E k) m)]
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
      rfl
    -- pointwise limit
    have hbdd : ∀ m x, BddBelow (range fun k => g k m x) := fun m x =>
      ⟨0, by rintro _ ⟨k, rfl⟩; exact hg_nonneg k m x⟩
    have hlim : ∀ x, Tendsto (fun k => F k x) atTop (𝓝 (L x)) := by
      intro x
      show Tendsto (fun k => (1 / (N : ℝ)) * ∑ m ∈ Finset.range N, g k m x) atTop
        (𝓝 ((1 / (N : ℝ)) * ∑ m ∈ Finset.range N, ⨅ k, g k m x))
      exact (tendsto_finsetSum (f := fun (m : ℕ) k => g k (m : ℤ) x) (Finset.range N)
        fun (m : ℕ) _ => tendsto_atTop_ciInf (hg_anti (m : ℤ) x) (hbdd (m : ℤ) x)).const_mul _
    have hF_nonneg : ∀ k x, 0 ≤ F k x := fun k x =>
      mul_nonneg (by positivity) (Finset.sum_nonneg fun m _ => hg_nonneg k m x)
    have hF_le : ∀ k x, F k x ≤ F 0 x := fun k x =>
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun m _ => hg_anti m x (Nat.zero_le k))
        (by positivity)
    have hDCT : Tendsto (fun k => ∫ x in (0 : ℝ)..1, F k x) atTop
        (𝓝 (∫ x in (0 : ℝ)..1, L x)) := by
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (F 0)
        (Eventually.of_forall fun k => (hFc k).aestronglyMeasurable)
        (Eventually.of_forall fun k => Eventually.of_forall fun x _ => ?_)
        ((hFc 0).intervalIntegrable 0 1) (Eventually.of_forall fun x _ => hlim x)
      rw [Real.norm_eq_abs, abs_of_nonneg (hF_nonneg k x)]
      exact hF_le k x
    have hstep : (ν {E}).toReal ≤ ∫ x in (0 : ℝ)..1, L x :=
      ge_of_tendsto hDCT (Eventually.of_forall fun k => (hatom k).trans_eq (hFint k))
    -- the pointwise bound `L x ≤ d / N`
    have hL_le : ∀ x, L x ≤ d / N := by
      intro x
      have : FiniteDimensional ℂ (eigKer (Hx x) E) := hfin x
      have h1 : ∀ m : ℕ, ⨅ k, g k m x ≤ ‖(eigKer (Hx x) E).starProjection (delta m)‖ ^ 2 :=
        fun m => iInf_re_inner_atomBump_le (hsa x) E (delta m)
      have h2 : ∑ m ∈ Finset.range N, ‖(eigKer (Hx x) E).starProjection (delta m)‖ ^ 2 ≤ d := by
        have hb := sum_norm_sq_starProjection_delta_le (eigKer (Hx x) E)
          ((Finset.range N).image (fun m : ℕ => (m : ℤ)))
        rw [Finset.sum_image (fun a _ b _ h => by exact_mod_cast h)] at hb
        exact hb.trans (by exact_mod_cast hdim x)
      have h3 := (Finset.sum_le_sum fun m (_ : m ∈ Finset.range N) => h1 m).trans h2
      simp only [hL]
      rw [one_div_mul_eq_div]
      exact div_le_div_of_nonneg_right h3 hN'.le
    have hL_nonneg : ∀ x, 0 ≤ L x := fun x =>
      mul_nonneg (by positivity) (Finset.sum_nonneg fun m _ => le_ciInf fun k => hg_nonneg k m x)
    have hLint : ∫ x in (0 : ℝ)..1, L x ≤ d / N := by
      have h : ∫ x in (0 : ℝ)..1, L x ≤ ∫ x in (0 : ℝ)..1, ((d : ℝ) / N) := by
        rw [intervalIntegral.integral_of_le zero_le_one, intervalIntegral.integral_of_le zero_le_one]
        exact integral_mono_of_nonneg (Eventually.of_forall hL_nonneg) (integrable_const _)
          (Eventually.of_forall hL_le)
      simpa using h
    exact hstep.trans hLint
  have hlim : Tendsto (fun N : ℕ => (d : ℝ) / N) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (d : ℝ)
  have h0 : (ν {E}).toReal ≤ 0 :=
    ge_of_tendsto hlim (eventually_atTop.2 ⟨1, fun N hN => key N hN⟩)
  have htr : (ν {E}).toReal = 0 := le_antisymm h0 ENNReal.toReal_nonneg
  rcases (ENNReal.toReal_eq_zero_iff _).1 htr with h | h
  · exact h
  · exact absurd h (measure_ne_top ν _)

/-- **Paper I, Lemma 2.8 (atomlessness half), global form.**  If all eigenspaces of all `H_x`
are finite-dimensional of dimension `≤ d`, the density-of-states measure is atomless. -/
theorem dos_measure_atomless {α : ℝ} {Hx : ℝ → Op ℤ} {ν : Measure ℝ}
    (hν : IsDOSMeasure Hx ν) (hsa : ∀ x, IsSelfAdjoint (Hx x)) (hcont : Continuous Hx)
    (hper : ∀ x, Hx (x + 1) = Hx x)
    (hcov : ∀ x, Hx (x + α) = U α x * Hx x * star (U α x)) {d : ℕ}
    (hfin : ∀ x (E : ℝ), FiniteDimensional ℂ
      (LinearMap.ker ((Hx x - (E : ℂ) • 1 : Op ℤ) : L2 ℤ →ₗ[ℂ] L2 ℤ)))
    (hdim : ∀ x (E : ℝ), Module.finrank ℂ
      (LinearMap.ker ((Hx x - (E : ℂ) • 1 : Op ℤ) : L2 ℤ →ₗ[ℂ] L2 ℤ)) ≤ d) :
    ∀ E, ν {E} = 0 := fun E =>
  dos_measure_singleton_eq_zero hν hsa hcont hper hcov (fun x => hfin x E) (fun x => hdim x E)

end SGD

