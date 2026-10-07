import ErgodicShared.TraceIdentity
import ErgodicShared.SpectralMeasureExists
import ErgodicShared.MaximalType

/-!
# The density of states: existence, covariance and averaging

For a summable self-adjoint symbol `K` and the covariant family `H_x = op α K x` on `ℓ²(ℤ)`:

* `CMS.exists_isDOSMeasure`: the density of states measure exists; it is the spectral measure
  of the two-dimensional realization `op2 α K` at `δ₀` (trace identity `inner_delta_cfc_op2`).
* `CMS.inner_delta_cfc_op_covariant`: covariance of diagonal matrix elements,
  `⟪δ_n, g(H_x) δ_n⟫ = ⟪δ₀, g(H_{x+nα}) δ₀⟫` (shift unitary + `cfc` commutes with unitary
  conjugation).
* `CMS.integral_inner_delta_cfc_op_average`: averaging identity
  `∫₀¹ ⟪δ₀, g(H_x) δ₀⟫ dx = (1/N) ∫₀¹ ∑_{n<N} ⟪δ_n, g(H_x) δ_n⟫ dx`.
* `CMS.dos_measure_singleton_eq_zero`: abstract atom bound — if for every `x` and every finite
  set `F ⊆ ℤ` the masses `∑_{n∈F} μ_{x,n}{E}` of the spectral measures at `δ_n` are bounded by a
  constant `C` (e.g. `C = 2`), then the DOS measure has no atom at `E`.
-/

noncomputable section

open scoped ComplexConjugate InnerProductSpace
open MeasureTheory Set Filter Topology BoundedContinuousFunction AMO L2

namespace CMS

set_option linter.unusedSectionVars false

/-! ### Existence of the density of states measure -/

/-- **Existence of the DOS measure.** For a summable self-adjoint symbol `K`, the spectral
measure of `op2 α K` at `δ₀` is a density of states measure of `x ↦ op α K x`. -/
theorem exists_isDOSMeasure (α : ℝ) {K : Symbol} (hK : SymbolSummable K)
    (hsa : SymbolSelfAdjoint K) : ∃ ν, IsDOSMeasure (op α K) ν := by
  have hT := isSelfAdjoint_op2 (α := α) hK hsa
  have hμ := isSpectralMeasureH_spectralMeasureH hT (delta (0 : ℤ × ℤ))
  refine ⟨spectralMeasureH (op2 α K) (delta (0 : ℤ × ℤ)), ⟨?_⟩, fun f => ?_⟩
  · rw [hμ.measure_univ hT, norm_delta]; simp
  · obtain ⟨hc, heq⟩ := inner_delta_cfc_op2 α hK hsa f.continuous
    rw [hμ.2 f, heq 0, intervalIntegral.intervalIntegral_re (hc.intervalIntegrable _ _)]

/-! ### Covariance -/

/-- The shift `U` as a unitary. -/
def shiftUnitary (α x : ℝ) : unitary (Op ℤ) :=
  ⟨U α x, by
    have hs : star (U α x) = W α x (-1) 0 := by
      rw [U, star_W]; simp
    refine ⟨?_, ?_⟩
    · rw [hs]; exact Uinv_comp_U α x
    · rw [hs]; exact U_comp_Uinv α x⟩

lemma W_neg_one_delta (α x : ℝ) (m : ℤ) : W α x (-1) 0 (delta m) = delta (m + 1) := by
  ext n
  rw [W_apply]
  simp only [delta, lp.single_apply, Int.cast_zero, zero_mul, mul_zero, zero_div, add_zero,
    e_zero, one_mul]
  by_cases h : n = m + 1
  · subst h; simp
  · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne (by omega)]

/-- One step of covariance: `⟪δ_{m+1}, g(H_x) δ_{m+1}⟫ = ⟪δ_m, g(H_{x+α}) δ_m⟫`. -/
lemma inner_delta_cfc_op_succ (α : ℝ) {K : Symbol} (hK : SymbolSummable K) (G : ℂ → ℂ)
    (x : ℝ) (m : ℤ) :
    ⟪delta (m + 1), cfc G (op α K x) (delta (m + 1))⟫_ℂ =
      ⟪delta m, cfc G (op α K (x + α)) (delta m)⟫_ℂ := by
  set u := Unitary.linearIsometryEquiv (shiftUnitary α x)
  have hu : ∀ v, u v = U α x v := fun v => rfl
  have hsymm' : ∀ v, u.symm v = W α x (-1) 0 v := by
    intro v
    rw [LinearIsometryEquiv.symm_apply_eq, hu, ← ContinuousLinearMap.comp_apply, U_comp_Uinv]
    rfl
  have hconj : u.conjStarAlgEquiv (op α K x) = op α K (x + α) := by
    ext1 v
    rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, op_conj_U hK x, hsymm', hu]
    rfl
  have hsymm : u.symm (delta m) = delta (m + 1) := by rw [hsymm']; exact W_neg_one_delta α x m
  have hδ : u (delta (m + 1)) = delta m := by
    rw [← hsymm, LinearIsometryEquiv.apply_symm_apply]
  rw [← hconj, ← conjStarAlgEquiv_cfc, LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, hsymm,
    ← hδ, u.inner_map_map]

/-- **Covariance of diagonal matrix elements.** For any `G` (in particular `G z = g(Re z)` with
`g` continuous) and every `n ∈ ℤ`, `⟪δ_n, G(H_x) δ_n⟫ = ⟪δ₀, G(H_{x+nα}) δ₀⟫`. -/
theorem inner_delta_cfc_op_covariant (α : ℝ) {K : Symbol} (hK : SymbolSummable K)
    (G : ℂ → ℂ) (x : ℝ) (n : ℤ) :
    ⟪delta n, cfc G (op α K x) (delta n)⟫_ℂ =
      ⟪delta 0, cfc G (op α K (x + n * α)) (delta 0)⟫_ℂ := by
  induction n using Int.induction_on generalizing x with
  | zero => simp
  | succ m ih =>
    rw [inner_delta_cfc_op_succ α hK G x, ih,
      show x + α + ((m : ℤ) : ℝ) * α = x + (((m : ℤ) + 1 : ℤ) : ℝ) * α by push_cast; ring]
  | pred m ih =>
    have h := inner_delta_cfc_op_succ α hK G (x - α) (-(m : ℤ) - 1)
    have e1 : (-(m : ℤ) - 1 + 1) = -(m : ℤ) := by ring
    simp only [e1, sub_add_cancel] at h
    rw [← h, ih, show x - α + ((-(m : ℤ) : ℤ) : ℝ) * α = x + ((-(m : ℤ) - 1 : ℤ) : ℝ) * α by
      push_cast; ring]

/-- Real-part form of covariance, for `G z = g(Re z)`. -/
theorem re_inner_delta_cfc_op_covariant (α : ℝ) {K : Symbol} (hK : SymbolSummable K)
    (g : ℝ → ℝ) (x : ℝ) (n : ℤ) :
    RCLike.re ⟪delta n, cfc (fun z : ℂ => ((g z.re : ℝ) : ℂ)) (op α K x) (delta n)⟫_ℂ =
      RCLike.re ⟪delta 0, cfc (fun z : ℂ => ((g z.re : ℝ) : ℂ)) (op α K (x + n * α))
        (delta 0)⟫_ℂ := by
  rw [inner_delta_cfc_op_covariant α hK]

/-! ### Averaging -/

/-- Averaging a continuous `1`-periodic function along `x ↦ x + nα`:
`∫₀¹ φ = N⁻¹ • ∫₀¹ ∑_{n<N} φ(x + nα)`. -/
lemma integral_periodic_average {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {φ : ℝ → E} (hφ : Continuous φ) (hper : Function.Periodic φ 1)
    (α : ℝ) {N : ℕ} (hN : 1 ≤ N) :
    ∫ x in (0 : ℝ)..1, φ x =
      (N : ℝ)⁻¹ • ∫ x in (0 : ℝ)..1, ∑ n ∈ Finset.range N, φ (x + n * α) := by
  rw [intervalIntegral.integral_finsetSum (f := fun (n : ℕ) x => φ (x + n * α)) fun n _ =>
    (show Continuous fun x => φ (x + n * α) by fun_prop).intervalIntegrable _ _]
  have hconst : ∀ n ∈ Finset.range N, ∫ x in (0 : ℝ)..1, φ (x + n * α) =
      ∫ x in (0 : ℝ)..1, φ x := by
    intro n _
    rw [intervalIntegral.integral_comp_add_right, zero_add, add_comm 1,
      hper.intervalIntegral_add_eq (n * α) 0, zero_add]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ,
    smul_smul, inv_mul_cancel₀ (by exact_mod_cast (show N ≠ 0 by omega)), one_smul]

/-- The diagonal element `x ↦ ⟪δ₀, G(H_x) δ₀⟫` is `1`-periodic. -/
lemma periodic_inner_delta_cfc_op (α : ℝ) (K : Symbol) (G : ℂ → ℂ) :
    Function.Periodic (fun x => ⟪delta 0, cfc G (op α K x) (delta 0)⟫_ℂ) 1 := by
  intro x
  have h := op_add_int α K x 1
  rw [Int.cast_one] at h
  dsimp only
  rw [h]

/-- **Averaging identity.** For continuous `g` and `N ≥ 1`,
`∫₀¹ ⟪δ₀, g(H_x) δ₀⟫ dx = (1/N) ∫₀¹ ∑_{n<N} ⟪δ_n, g(H_x) δ_n⟫ dx`. -/
theorem integral_inner_delta_cfc_op_average (α : ℝ) {K : Symbol} (hK : SymbolSummable K)
    (hsa : SymbolSelfAdjoint K) {g : ℝ → ℝ} (hg : Continuous g) {N : ℕ} (hN : 1 ≤ N) :
    ∫ x in (0 : ℝ)..1, ⟪delta 0, cfc (fun z : ℂ => ((g z.re : ℝ) : ℂ)) (op α K x) (delta 0)⟫_ℂ =
      (1 / (N : ℂ)) * ∫ x in (0 : ℝ)..1, ∑ n ∈ Finset.range N,
        ⟪delta (n : ℤ), cfc (fun z : ℂ => ((g z.re : ℝ) : ℂ)) (op α K x) (delta (n : ℤ))⟫_ℂ := by
  rw [integral_periodic_average (inner_delta_cfc_op2 α hK hsa hg).1
    (periodic_inner_delta_cfc_op α K _) α hN]
  have hs : ∀ x, ∑ n ∈ Finset.range N,
      ⟪delta (n : ℤ), cfc (fun z : ℂ => ((g z.re : ℝ) : ℂ)) (op α K x) (delta (n : ℤ))⟫_ℂ =
      ∑ n ∈ Finset.range N,
        ⟪delta 0, cfc (fun z : ℂ => ((g z.re : ℝ) : ℂ)) (op α K (x + n * α)) (delta 0)⟫_ℂ :=
    fun x => Finset.sum_congr rfl fun n _ => by
      rw [inner_delta_cfc_op_covariant α hK _ x n, Int.cast_natCast]
  simp only [hs]
  rw [Complex.real_smul]
  push_cast
  ring

/-- Real-part form of the averaging identity. -/
theorem integral_re_inner_delta_cfc_op_average (α : ℝ) {K : Symbol} (hK : SymbolSummable K)
    (hsa : SymbolSelfAdjoint K) {g : ℝ → ℝ} (hg : Continuous g) {N : ℕ} (hN : 1 ≤ N) :
    ∫ x in (0 : ℝ)..1,
        RCLike.re ⟪delta 0, cfc (fun z : ℂ => ((g z.re : ℝ) : ℂ)) (op α K x) (delta 0)⟫_ℂ =
      (N : ℝ)⁻¹ * ∫ x in (0 : ℝ)..1, ∑ n ∈ Finset.range N,
        RCLike.re ⟪delta (n : ℤ), cfc (fun z : ℂ => ((g z.re : ℝ) : ℂ)) (op α K x)
          (delta (n : ℤ))⟫_ℂ := by
  have hc := (inner_delta_cfc_op2 α hK hsa hg).1
  rw [integral_periodic_average
    (φ := fun x => RCLike.re ⟪delta 0, cfc (fun z : ℂ => ((g z.re : ℝ) : ℂ)) (op α K x)
      (delta 0)⟫_ℂ) (RCLike.continuous_re.comp hc)
    (fun x => by
      have h := op_add_int α K x 1
      rw [Int.cast_one] at h
      dsimp only
      rw [h]) α hN]
  have hs : ∀ x, ∑ n ∈ Finset.range N,
      RCLike.re ⟪delta (n : ℤ), cfc (fun z : ℂ => ((g z.re : ℝ) : ℂ)) (op α K x)
        (delta (n : ℤ))⟫_ℂ =
      ∑ n ∈ Finset.range N, RCLike.re
        ⟪delta 0, cfc (fun z : ℂ => ((g z.re : ℝ) : ℂ)) (op α K (x + n * α)) (delta 0)⟫_ℂ :=
    fun x => Finset.sum_congr rfl fun n _ => by
      rw [inner_delta_cfc_op_covariant α hK _ x n, Int.cast_natCast]
  simp only [hs]
  rfl

/-! ### The abstract atom bound -/

/-- **Abstract atom bound for the DOS measure.** Let `ν` be a DOS measure of `x ↦ H_x`, and
suppose that for every phase `x` and every finite set `F ⊆ ℤ`, the spectral measures `μ_n` of
`H_x` at `δ_n` satisfy `∑_{n∈F} μ_n{E} ≤ C`. Then `ν{E} = 0`.

(Proof: `ν{E} ≤ ∫ g_k dν = (1/N) ∫₀¹ ∑_{n<N} ⟪δ_n, g_k(H_x) δ_n⟫ dx` for thickened indicators
`g_k ↓ 1_{E}`; letting `k → ∞` by dominated convergence gives `ν{E} ≤ C/N` for all `N`.) -/
theorem dos_measure_singleton_eq_zero {α : ℝ} {K : Symbol} (hK : SymbolSummable K)
    (hsa : SymbolSelfAdjoint K) {ν : Measure ℝ} (hν : IsDOSMeasure (op α K) ν) (E C : ℝ)
    (hbound : ∀ (x : ℝ) (F : Finset ℤ) (μ : ℤ → Measure ℝ),
      (∀ n ∈ F, IsSpectralMeasure (op α K x) (delta n) (μ n)) →
        ∑ n ∈ F, (μ n).real {E} ≤ C) :
    ν {E} = 0 := by
  have := hν.1
  set h : ℕ → ℝ →ᵇ ℝ := fun k => thickInd {E} k * thickInd {E} k
  have hT : ∀ x, IsSelfAdjoint (op α K x) := isSelfAdjoint_op hK hsa
  set μ : ℝ → ℤ → Measure ℝ := fun x n => spectralMeasureH (op α K x) (delta n)
  have hμ : ∀ x n, IsSpectralMeasureH (op α K x) (delta n) (μ x n) := fun x n =>
    isSpectralMeasureH_spectralMeasureH (hT x) _
  have hC0 : 0 ≤ C := by simpa using hbound 0 ∅ (fun _ => 0) (by simp)
  -- the integrands
  set F : ℕ → ℕ → ℝ → ℝ := fun N k x => ∑ n ∈ Finset.range N,
    RCLike.re ⟪delta (n : ℤ), cfc (fun z : ℂ => ((h k z.re : ℝ) : ℂ)) (op α K x)
      (delta (n : ℤ))⟫_ℂ
  have hF_eq : ∀ N k x, F N k x = ∑ n ∈ Finset.range N, ∫ t, h k t ∂(μ x n) := by
    intro N k x
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [(hμ x n).2 (h k)]
  have hbound_k : ∀ k x (n : ℤ), ‖∫ t, h k t ∂(μ x n)‖ ≤ 1 := by
    intro k x n
    have := (hμ x n).1
    have h1 := norm_integral_le_of_norm_le_const (μ := μ x n) (f := fun t => h k t) (C := 1)
      (Eventually.of_forall fun t => by
        have h0 := thickInd_nonneg {E} k t
        have h1 := thickInd_le_one {E} k t
        simp only [h, BoundedContinuousFunction.coe_mul, Pi.mul_apply, Real.norm_eq_abs]
        rw [abs_of_nonneg (mul_nonneg h0 h0)]
        nlinarith)
    rwa [(hμ x n).measureReal_univ (hT x), norm_delta, one_pow, mul_one] at h1
  -- key estimate for each `N ≥ 1`
  have key : ∀ N : ℕ, 1 ≤ N → ν.real {E} ≤ (N : ℝ)⁻¹ * C := by
    intro N hN
    set L : ℝ → ℝ := fun x => ∑ n ∈ Finset.range N, (μ x n).real {E}
    have hlim : Tendsto (fun k => ∫ x in (0 : ℝ)..1, F N k x) atTop
        (𝓝 (∫ x in (0 : ℝ)..1, L x)) := by
      refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (N : ℝ))
        (Eventually.of_forall fun k => ?_) (Eventually.of_forall fun k => ?_)
        intervalIntegrable_const ?_
      · refine Continuous.aestronglyMeasurable ?_
        refine continuous_finsetSum _ fun n _ => ?_
        have hc := (inner_delta_cfc_op2 α hK hsa (h k).continuous).1
        simp_rw [re_inner_delta_cfc_op_covariant α hK _ _ (n : ℤ)]
        exact RCLike.continuous_re.comp (hc.comp (continuous_id.add continuous_const))
      · refine ae_of_all _ fun x _ => ?_
        rw [hF_eq]
        refine (norm_sum_le _ _).trans ?_
        refine (Finset.sum_le_sum (s := Finset.range N)
          (g := fun _ => (1 : ℝ)) fun n _ => hbound_k k x (n : ℤ)).trans ?_
        simp
      · refine ae_of_all _ fun x _ => ?_
        simp_rw [hF_eq]
        refine tendsto_finsetSum _ fun n _ => ?_
        have := (hμ x n).1
        exact tendsto_integral_sq (μ x n) isClosed_singleton
    have hLC : ‖∫ x in (0 : ℝ)..1, L x‖ ≤ C := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1) (C := C)
        (f := L) fun x _ => by
          have hnn : 0 ≤ L x := Finset.sum_nonneg fun n _ => measureReal_nonneg
          rw [Real.norm_eq_abs, abs_of_nonneg hnn]
          exact (Finset.sum_image (f := fun n : ℤ => (μ x n).real {E}) (s := Finset.range N)
            (g := fun n : ℕ => (n : ℤ))
            (fun a _ b _ hab => Nat.cast_injective hab)).symm.trans_le
            (hbound x ((Finset.range N).image (fun n : ℕ => (n : ℤ))) (μ x)
              fun n _ => hμ x n)
      simpa using this
    have hle : ∀ k, ν.real {E} ≤ (N : ℝ)⁻¹ * ∫ x in (0 : ℝ)..1, F N k x := by
      intro k
      refine (measureReal_le_integral_sq ν isClosed_singleton k).trans_eq ?_
      rw [hν.2 (h k), integral_re_inner_delta_cfc_op_average α hK hsa (h k).continuous hN]
    have hlim' := hlim.const_mul (N : ℝ)⁻¹
    refine (ge_of_tendsto hlim' (Eventually.of_forall hle)).trans ?_
    gcongr
    exact (le_abs_self _).trans hLC
  -- conclude
  have hle0 : ν.real {E} ≤ 0 := by
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨N, hN⟩ := exists_nat_gt (C / ε)
    have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg hC0 hε.le) hN
    have hN1 : 1 ≤ N := by exact_mod_cast hNpos
    refine (key N hN1).trans_lt ?_
    rw [zero_add, inv_mul_lt_iff₀ hNpos]
    rwa [div_lt_iff₀ hε] at hN
  have h0 : ν.real {E} = 0 := le_antisymm hle0 measureReal_nonneg
  rwa [measureReal_eq_zero_iff] at h0

/-- **Atom bound with constant `2`.** -/
theorem dos_measure_singleton_eq_zero_of_two {α : ℝ} {K : Symbol} (hK : SymbolSummable K)
    (hsa : SymbolSelfAdjoint K) {ν : Measure ℝ} (hν : IsDOSMeasure (op α K) ν) (E : ℝ)
    (hbound : ∀ (x : ℝ) (F : Finset ℤ) (μ : ℤ → Measure ℝ),
      (∀ n ∈ F, IsSpectralMeasure (op α K x) (delta n) (μ n)) →
        ∑ n ∈ F, (μ n).real {E} ≤ 2) :
    ν {E} = 0 :=
  dos_measure_singleton_eq_zero hK hsa hν E 2 hbound

end CMS
