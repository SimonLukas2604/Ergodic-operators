import ContinuumMagnetic.RegularRep.MaximalType
import ContinuumMagnetic.RegularRep.SpectralMeasureExists

/-!
# Atoms of spectral measures are eigenprojections

For a self-adjoint `T` on a complex Hilbert space `H` and `E : ℝ`, let
`K = ker (T - E)` (`CMS.eigenspaceH T E`, a closed subspace) and `P_K` its orthogonal projection.

Main results:
* `CMS.cfc_apply_of_apply_eq_smul`: if `T u = E u` then `G(T) u = G(E) u` for every `G`
  continuous on the spectrum (proved by the Stone–Weierstrass induction principle
  `ContinuousMap.induction_on_of_compact` applied to `cfcHom`);
* `CMS.IsSpectralMeasureH.measureReal_singleton_eq`: if `μ` is a spectral measure of `v` then
  `μ {E} = ‖P_K v‖²`. Proof: with `g_n` the thickened indicators of `{E}`, `g_n(T) v` is Cauchy
  (`‖g_n(T) v - g_m(T) v‖² = ∫ (g_n - g_m)² dμ ≤ (∫ g_n² dμ - μ{E}) + (∫ g_m² dμ - μ{E})`), its
  limit `u` lies in `K` (`‖(T - E) g_n(T)‖ ≤ 1/(n+1)`), and `v - u ⊥ K` (`g_n(T)` is self-adjoint
  and fixes `K`); hence `u = P_K v` and `‖P_K v‖² = lim ∫ g_n² dμ = μ{E}`;
* `CMS.sum_measureReal_singleton_le_finrank`: trace bound `∑_{i ∈ F} μ_i {E} ≤ dim K` for an
  orthonormal family `(e i)` with spectral measures `μ_i`, when `K` is finite-dimensional.
-/

noncomputable section

open scoped ComplexConjugate InnerProductSpace ENNReal NNReal
open MeasureTheory Set Filter Topology BoundedContinuousFunction

namespace CMS

set_option linter.unusedSectionVars false

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The eigenspace `ker (T - E)`. -/
def eigenspaceH (T : H →L[ℂ] H) (E : ℝ) : Submodule ℂ H :=
  LinearMap.ker ((T - algebraMap ℂ (H →L[ℂ] H) E : H →L[ℂ] H) : H →ₗ[ℂ] H)

/-- Membership in the eigenspace. -/
lemma mem_eigenspaceH {T : H →L[ℂ] H} {E : ℝ} {u : H} :
    u ∈ eigenspaceH T E ↔ T u = (E : ℂ) • u := by
  simp [eigenspaceH, sub_eq_zero, Algebra.algebraMap_eq_smul_one]

/-- The eigenspace is closed. -/
lemma isClosed_eigenspaceH (T : H →L[ℂ] H) (E : ℝ) : IsClosed (eigenspaceH T E : Set H) :=
  ContinuousLinearMap.isClosed_ker _

instance (T : H →L[ℂ] H) (E : ℝ) : (eigenspaceH T E).HasOrthogonalProjection := by
  have : CompleteSpace (eigenspaceH T E) := (isClosed_eigenspaceH T E).completeSpace_coe
  infer_instance

/-- An eigenvalue (with nonzero eigenvector) lies in the spectrum. -/
lemma mem_spectrum_of_apply_eq_smul {T : H →L[ℂ] H} {E : ℂ} {u : H} (hu : T u = E • u)
    (hu0 : u ≠ 0) : E ∈ spectrum ℂ T := by
  rw [spectrum.mem_iff]
  intro h
  apply hu0
  have h0 : (algebraMap ℂ (H →L[ℂ] H) E - T) u = 0 := by
    simp [hu, Algebra.algebraMap_eq_smul_one]
  have := congrArg (fun A : H →L[ℂ] H => A u) h.unit.inv_mul
  simp only [mul_apply_eq_comp, IsUnit.unit_spec, h0, map_zero, one_apply_eq_self] at this
  exact this.symm

variable {T : H →L[ℂ] H}

/-- On an eigenvector `T u = E u` of a self-adjoint `T`, `cfcHom F` acts as the scalar `F E`. -/
theorem cfcHom_apply_of_apply_eq_smul (hT : IsSelfAdjoint T) {E : ℝ} {u : H}
    (hu : T u = (E : ℂ) • u) (hE : (E : ℂ) ∈ spectrum ℂ T) (F : C(spectrum ℂ T, ℂ)) :
    cfcHom hT.isStarNormal F u = F ⟨E, hE⟩ • u := by
  induction F using ContinuousMap.induction_on_of_compact with
  | const r =>
    show cfcHom hT.isStarNormal (algebraMap ℂ C(spectrum ℂ T, ℂ) r) u = _
    rw [AlgHomClass.commutes]
    simp [Algebra.algebraMap_eq_smul_one]
  | id => simp [cfcHom_id, hu]
  | star_id => rw [map_star, cfcHom_id, hT.star_eq]; simp [hu]
  | add f g hf hg => simp [map_add, hf, hg, add_smul]
  | mul f g hf hg =>
    rw [map_mul, mul_apply_eq_comp, hg, map_smul, hf, smul_smul]
    simp [mul_comm]
  | frequently f hf =>
    have hcl : IsClosed {F : C(spectrum ℂ T, ℂ) |
        cfcHom hT.isStarNormal F u = F ⟨E, hE⟩ • u} :=
      isClosed_eq ((cfcHom_continuous hT.isStarNormal).clm_apply continuous_const)
        ((continuous_eval_const _).smul continuous_const)
    exact hcl.mem_of_frequently_of_tendsto hf tendsto_id

/-- On an eigenvector `T u = E u` of a self-adjoint `T`, the functional calculus acts as the
scalar `G E`. -/
theorem cfc_apply_of_apply_eq_smul (hT : IsSelfAdjoint T) {E : ℝ} {u : H}
    (hu : T u = (E : ℂ) • u) (G : ℂ → ℂ) (hG : ContinuousOn G (spectrum ℂ T)) :
    cfc G T u = G E • u := by
  by_cases hu0 : u = 0
  · simp [hu0]
  have hE := mem_spectrum_of_apply_eq_smul hu hu0
  rw [cfc_apply G T hT.isStarNormal hG]
  exact cfcHom_apply_of_apply_eq_smul hT hu hE _


/-! ### Auxiliary facts on `realCFC` -/

/-- `g(T)` is self-adjoint for real `g`. -/
lemma star_realCFC (g : ℝ →ᵇ ℝ) (T : H →L[ℂ] H) : star (realCFC g T) = realCFC g T := by
  rw [realCFC, ← cfc_star]
  congr 1
  funext z
  simp

/-- `⟪g(T) x, y⟫ = ⟪x, g(T) y⟫`. -/
lemma inner_realCFC_left (g : ℝ →ᵇ ℝ) (T : H →L[ℂ] H) (x y : H) :
    ⟪realCFC g T x, y⟫_ℂ = ⟪x, realCFC g T y⟫_ℂ := by
  conv_lhs => rw [← star_realCFC g T]
  rw [ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

/-- `(g - h)(T) = g(T) - h(T)`. -/
lemma realCFC_sub (g h : ℝ →ᵇ ℝ) (T : H →L[ℂ] H) :
    realCFC (g - h) T = realCFC g T - realCFC h T := by
  rw [realCFC, realCFC, realCFC, ← cfc_sub _ _ T (continuous_realFun g).continuousOn
    (continuous_realFun h).continuousOn]
  congr 1
  funext z
  simp

/-- `|t - E| g_n(t) ≤ 1/(n+1)` for the thickened indicators `g_n` of `{E}`. -/
lemma abs_sub_mul_thickInd_le (E t : ℝ) (n : ℕ) :
    |t - E| * thickInd {E} n t ≤ 1 / ((n : ℝ) + 1) := by
  by_cases ht : t ∈ Metric.thickening (1 / ((n : ℝ) + 1)) ({E} : Set ℝ)
  · rw [Metric.thickening_singleton, Metric.mem_ball, Real.dist_eq] at ht
    calc |t - E| * thickInd {E} n t ≤ |t - E| * 1 :=
          mul_le_mul_of_nonneg_left (thickInd_le_one _ _ _) (abs_nonneg _)
      _ ≤ _ := by rw [mul_one]; exact ht.le
  · rw [thickInd_apply, thickenedIndicator_zero _ _ ht]
    simp only [NNReal.coe_zero, mul_zero]
    positivity

/-- `‖(T - E) g_n(T)‖ ≤ 1/(n+1)` for the thickened indicators `g_n` of `{E}`. -/
lemma norm_sub_mul_realCFC_thickInd_le (hT : IsSelfAdjoint T) (E : ℝ) (n : ℕ) :
    ‖(T - algebraMap ℂ (H →L[ℂ] H) E) * realCFC (thickInd {E} n) T‖ ≤ 1 / ((n : ℝ) + 1) := by
  have h1 : cfc (fun z : ℂ => z - (E : ℂ)) T = T - algebraMap ℂ (H →L[ℂ] H) E := by
    rw [cfc_sub (fun z : ℂ => z) (fun _ => (E : ℂ)) T, cfc_id' ℂ T, cfc_const (E : ℂ) T]
  have hrw : (T - algebraMap ℂ (H →L[ℂ] H) E) * realCFC (thickInd {E} n) T =
      cfc (fun z : ℂ => (z - E) * ((thickInd {E} n z.re : ℝ) : ℂ)) T := by
    rw [cfc_mul (fun z : ℂ => z - E) _ T, h1, realCFC]
  rw [hrw]
  refine norm_cfc_le (by positivity) fun x hx => ?_
  rw [hT.mem_spectrum_eq_re hx]
  simp only [Complex.ofReal_re]
  rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg (thickInd_nonneg _ _ _)]
  exact abs_sub_mul_thickInd_le E x.re n

/-! ### Atoms of spectral measures -/

/-- **Atoms are eigenprojections.** For self-adjoint `T` and a spectral measure `μ` of `v`, the
mass of `μ` at `E` is `‖P_E v‖²`, where `P_E` is the orthogonal projection onto `ker (T - E)`. -/
theorem IsSpectralMeasureH.measureReal_singleton_eq (hT : IsSelfAdjoint T) {v : H}
    {μ : Measure ℝ} (hμ : IsSpectralMeasureH T v μ) (E : ℝ) :
    μ.real {E} = ‖(eigenspaceH T E).starProjection v‖ ^ 2 := by
  have := hμ.1
  -- `g_n(T)` acts as the identity on the eigenspace
  have hAK : ∀ n : ℕ, ∀ k ∈ eigenspaceH T E, realCFC (thickInd {E} n) T k = k := by
    intro n k hk
    have := cfc_apply_of_apply_eq_smul hT (mem_eigenspaceH.1 hk)
      (fun z : ℂ => ((thickInd {E} n z.re : ℝ) : ℂ)) (continuous_realFun _).continuousOn
    rw [realCFC, this]
    simp [thickInd_eq_one {E} n (mem_singleton E)]
  -- Cauchy property of `g_n(T) v`
  set a : ℕ → ℝ := fun n => ∫ t, (thickInd {E} n * thickInd {E} n) t ∂μ - μ.real {E} with ha
  have ha0 : Tendsto a atTop (𝓝 0) := by
    have := (tendsto_integral_sq μ (isClosed_singleton (x := E))).sub_const (μ.real {E})
    simpa [ha, sub_self] using this
  have hpt : ∀ n m : ℕ, ∀ t,
      ((thickInd {E} n - thickInd {E} m) * (thickInd {E} n - thickInd {E} m)) t
        + 2 * Set.indicator {E} (1 : ℝ → ℝ) t ≤
      (thickInd {E} n * thickInd {E} n) t + (thickInd {E} m * thickInd {E} m) t := by
    intro n m t
    by_cases ht : t = E
    · subst ht
      simp [thickInd_eq_one _ _ (mem_singleton t)]
      norm_num
    · simp only [coe_sub, coe_mul, Pi.mul_apply, Pi.sub_apply,
        indicator_of_notMem (show t ∉ ({E} : Set ℝ) from ht)]
      nlinarith [thickInd_nonneg {E} n t, thickInd_nonneg {E} m t]
  have hdist : ∀ n m : ℕ,
      ‖realCFC (thickInd {E} n) T v - realCFC (thickInd {E} m) T v‖ ^ 2 ≤ a n + a m := by
    intro n m
    rw [← _root_.sub_apply, ← realCFC_sub, norm_realCFC_sq_eq_integral hμ]
    have hind : Integrable (fun t => 2 * Set.indicator {E} (1 : ℝ → ℝ) t) μ :=
      ((integrable_const (1 : ℝ)).indicator (measurableSet_singleton E)).const_mul 2
    have h2 : 2 * μ.real {E} = ∫ t, 2 * Set.indicator {E} (1 : ℝ → ℝ) t ∂μ := by
      rw [integral_const_mul, integral_indicator_one (measurableSet_singleton E)]
    have hint : ∫ t, ((thickInd {E} n - thickInd {E} m) * (thickInd {E} n - thickInd {E} m)) t ∂μ
        + 2 * μ.real {E} ≤
        ∫ t, (thickInd {E} n * thickInd {E} n) t ∂μ
          + ∫ t, (thickInd {E} m * thickInd {E} m) t ∂μ := by
      rw [← integral_add (BoundedContinuousFunction.integrable _ _)
        (BoundedContinuousFunction.integrable _ _), h2,
        ← integral_add (BoundedContinuousFunction.integrable _ _) hind]
      exact integral_mono ((BoundedContinuousFunction.integrable _ _).add hind)
        ((BoundedContinuousFunction.integrable _ _).add (BoundedContinuousFunction.integrable _ _))
        (hpt n m)
    simp only [ha]
    linarith
  have hcauchy : CauchySeq (fun n : ℕ => realCFC (thickInd {E} n) T v) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.1
      (ha0.eventually (gt_mem_nhds (show (0 : ℝ) < ε ^ 2 / 2 by positivity)))
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    have h := hdist m n
    have h1 := hN m hm
    have h2 := hN n hn
    by_contra hc
    push Not at hc
    nlinarith [norm_nonneg (realCFC (thickInd {E} m) T v - realCFC (thickInd {E} n) T v)]
  obtain ⟨u, hu⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- the limit is an eigenvector
  have huK : u ∈ eigenspaceH T E := by
    set S : H →L[ℂ] H := T - algebraMap ℂ (H →L[ℂ] H) E with hS
    have h1 : Tendsto (fun n : ℕ => S (realCFC (thickInd {E} n) T v)) atTop (𝓝 (S u)) :=
      (S.continuous.tendsto u).comp hu
    have h2 : Tendsto (fun n : ℕ => S (realCFC (thickInd {E} n) T v)) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have hlim : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1) * ‖v‖) atTop (𝓝 0) := by
        simpa using tendsto_one_div_add_atTop_nhds_zero_nat.mul_const ‖v‖
      refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hlim
      calc ‖S (realCFC (thickInd {E} n) T v)‖ = ‖(S * realCFC (thickInd {E} n) T) v‖ := rfl
        _ ≤ ‖S * realCFC (thickInd {E} n) T‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
        _ ≤ 1 / ((n : ℝ) + 1) * ‖v‖ :=
          mul_le_mul_of_nonneg_right (norm_sub_mul_realCFC_thickInd_le hT E n) (norm_nonneg _)
    exact LinearMap.mem_ker.2 (tendsto_nhds_unique h1 h2)
  -- `v - u ⊥ ker (T - E)`
  have hinner : ∀ k ∈ eigenspaceH T E, ⟪v - u, k⟫_ℂ = 0 := by
    intro k hk
    have h1 : Tendsto (fun n : ℕ => ⟪realCFC (thickInd {E} n) T v, k⟫_ℂ) atTop (𝓝 ⟪u, k⟫_ℂ) :=
      hu.inner tendsto_const_nhds
    have h2 : (fun n : ℕ => ⟪realCFC (thickInd {E} n) T v, k⟫_ℂ) = fun _ => ⟪v, k⟫_ℂ := by
      funext n
      rw [inner_realCFC_left, hAK n k hk]
    rw [h2] at h1
    rw [inner_sub_left, tendsto_nhds_unique h1 tendsto_const_nhds, sub_self]
  have hPu : (eigenspaceH T E).starProjection v = u :=
    Submodule.eq_starProjection_of_mem_of_inner_eq_zero huK hinner
  rw [hPu]
  have h1 : Tendsto (fun n : ℕ => ‖realCFC (thickInd {E} n) T v‖ ^ 2) atTop (𝓝 (‖u‖ ^ 2)) :=
    hu.norm.pow 2
  have h2 : (fun n : ℕ => ‖realCFC (thickInd {E} n) T v‖ ^ 2) =
      fun n => ∫ t, (thickInd {E} n * thickInd {E} n) t ∂μ :=
    funext fun n => norm_realCFC_sq_eq_integral hμ _
  rw [h2] at h1
  exact tendsto_nhds_unique (tendsto_integral_sq μ isClosed_singleton) h1

/-- For a finite-dimensional closed subspace `K` and an orthonormal family `e`,
`∑_{i ∈ F} ‖P_K e_i‖² ≤ dim K`. -/
lemma sum_norm_starProjection_sq_le_finrank (K : Submodule ℂ H) [K.HasOrthogonalProjection]
    [FiniteDimensional ℂ K] {ι : Type*} {e : ι → H} (he : Orthonormal ℂ e) (F : Finset ι) :
    ∑ i ∈ F, ‖K.starProjection (e i)‖ ^ 2 ≤ Module.finrank ℂ K := by
  set b := stdOrthonormalBasis ℂ K
  have hexp : ∀ x : H, ‖K.starProjection x‖ ^ 2 = ∑ j, ‖⟪x, (b j : H)⟫_ℂ‖ ^ 2 := by
    intro x
    rw [Submodule.starProjection_apply, Submodule.norm_coe,
      ← b.sum_sq_norm_inner_left (K.orthogonalProjectionOnto x)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_inner, ← Submodule.starProjection_apply]
    have h0 := Submodule.starProjection_inner_eq_zero x (b j : H) (b j).2
    rw [inner_sub_left, sub_eq_zero] at h0
    rw [← h0]
  simp_rw [hexp]
  rw [Finset.sum_comm]
  calc ∑ j, ∑ i ∈ F, ‖⟪e i, (b j : H)⟫_ℂ‖ ^ 2 ≤ ∑ j : Fin (Module.finrank ℂ K), (1 : ℝ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hb : ‖(b j : H)‖ = 1 := by
          rw [Submodule.norm_coe]; exact b.orthonormal.1 j
        have := he.sum_inner_products_le (x := (b j : H)) (s := F)
        simp_rw [hb, one_pow] at this
        exact this
    _ = Module.finrank ℂ K := by simp

/-- **Trace bound for atoms.** If `ker (T - E)` is finite-dimensional and `(e i)_{i ∈ F}` is part
of an orthonormal family with spectral measures `μ i`, then `∑_{i ∈ F} μ_i {E} ≤ dim ker (T - E)`. -/
theorem sum_measureReal_singleton_le_finrank (hT : IsSelfAdjoint T) (E : ℝ)
    [FiniteDimensional ℂ (eigenspaceH T E)] {ι : Type*} {e : ι → H} (he : Orthonormal ℂ e)
    (F : Finset ι) {μ : ι → Measure ℝ} (hμ : ∀ i, IsSpectralMeasureH T (e i) (μ i)) :
    ∑ i ∈ F, (μ i).real {E} ≤ Module.finrank ℂ (eigenspaceH T E) := by
  simp_rw [fun i => (hμ i).measureReal_singleton_eq hT E]
  exact sum_norm_starProjection_sq_le_finrank _ he F

end CMS
