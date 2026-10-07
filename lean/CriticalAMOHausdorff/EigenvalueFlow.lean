/-
Copyright (c) 2026. Formalization of
  S. Becker, S. Jitomirskaya, I. Krasovsky, "Critical almost Mathieu operator: hidden
  singularity, gap continuity, and the Hausdorff dimension of the spectrum"
  (arXiv:1909.04429v2).

# Variation of eigenvalues along a flow, and the abstract spectral cover

* **Lemma `lemma-flow`** (`.tex` l. 1352–1409, eq. `flowbound`): for a `C¹` Hermitian path
  `H : [a,b] → M_N(ℂ)` with `H' = [K, H] + 𝓔`, `K^* = -K` constant,
  `∑_j Var_{[a,b]} λ_j ≤ ∫_a^b ‖𝓔(x)‖_{S_1} dx` (`flow_bound`).  This is the *integral* form
  of the paper.  Variation is Mathlib's `eVariationOn` on `Set.Icc a b` (an `ℝ≥0∞`), so the
  statement also asserts that each `λ_j` has bounded variation.  The `C¹` hypothesis is
  formalised as: `H` has one-sided derivative `K H - H K + 𝓔` within `[a,b]` at every point
  and `𝓔` is continuous on `[a,b]`.  The Hermitian property of `𝓔` is derived, not assumed.
* **Proposition `prop-cover1`** (l. 1676–1772), abstract core (`cover_core`, `cover_bdry`):
  given Hermitian paths `H^±(x) = B(x) ± c P` (`P ≥ 0`, `c ≥ 0`) on `J = [a,b]` whose ordered
  eigenvalues have total variation `≤ V`, there are intervals `Ĩ_j = [lo_j, hi_j]`
  independent of `x ∈ J` and of `W` with `-cP ≤ W ≤ cP`, such that
  `σ(B(x) + W) ⊆ ⋃_j Ĩ_j` and `∑_j |Ĩ_j| ≤ 2c tr P + V` (`= 4c + V` for the boundary
  projection `P_N`, `tr P_N = 2`).  We take `Ĩ_j = [λ_j^-(a) - Var λ_j^-, λ_j^+(a) + Var λ_j^+]`,
  which contains the paper's `[min_J λ_j^-, max_J λ_j^+]` and satisfies the same length bound
  (this is exactly the estimate in the paper's proof).
* The boundary map `bdry N : M_{2×N}(ℂ)`, `u ↦ (u_0, u_{N-1})` (eq. `bp`, l. 1271) is defined
  locally as `CAH.Flow.bdry` with *the same definition* as `CAH.bdry` in
  `BoundaryResolvent.lean` (to be unified later; we do not import that file).  For Hermitian
  `V ∈ M_2(ℂ)` with `‖V‖ ≤ c` (equivalently: all eigenvalues in `[-c, c]`), we prove
  `-c P_N ≤ Γ^* V Γ ≤ c P_N` (`bdry_conj_bounds`).

## Proof of the flow bound

`H̃(t) = e^{-tK} H(t) e^{tK}` has the same ordered eigenvalues as `H(t)` and derivative
`e^{-tK} 𝓔(t) e^{tK}`.  For `x ≤ y` Lidskii gives `∑_j |λ_j(y) - λ_j(x)| ≤ ‖H̃(y) - H̃(x)‖_{S_1}`,
and with `S = sgn(H̃(y) - H̃(x))`, `‖H̃(y) - H̃(x)‖_{S_1} = Re tr(S(H̃(y) - H̃(x))) =
∫_x^y Re tr(S H̃'(t)) dt ≤ ∫_x^y ‖𝓔(t)‖_{S_1} dt` (duality + unitary invariance; only scalar
integrals occur).  The passage from the two-point bound to the sum of variations
(the paper's common-refinement argument) is `sum_eVariationOn_le`, proved by induction on the
number of functions, peeling off one variation function at a time.

No `sorry`s and no extra hypotheses in this file.
-/
import CriticalAMOHausdorff.OrderedEigenvalues

noncomputable section

open Matrix Set
open scoped ComplexOrder Topology

namespace CAH
namespace Flow

/-! ## 1. Variation bounds from two-point bounds -/

/-- If `|φ t - φ s| ≤ G t - G s` for `s ≤ t` in `[x,y]`, then `Var_{[x,y]} φ ≤ G y - G x`. -/
lemma eVariationOn_le_of_abs_sub_le {φ G : ℝ → ℝ} {x y : ℝ}
    (h : ∀ s ∈ Icc x y, ∀ t ∈ Icc x y, s ≤ t → |φ t - φ s| ≤ G t - G s) :
    eVariationOn φ (Icc x y) ≤ ENNReal.ofReal (G y - G x) := by
  unfold eVariationOn
  refine iSup_le fun p => ?_
  obtain ⟨n, u, hu, hus⟩ := p
  dsimp only
  have hstep : ∀ i, |φ (u (i + 1)) - φ (u i)| ≤ G (u (i + 1)) - G (u i) := fun i =>
    h _ (hus i) _ (hus (i + 1)) (hu (Nat.le_succ i))
  calc ∑ i ∈ Finset.range n, edist (φ (u (i + 1))) (φ (u i))
      ≤ ∑ i ∈ Finset.range n, ENNReal.ofReal (G (u (i + 1)) - G (u i)) :=
        Finset.sum_le_sum fun i _ => by
          rw [edist_dist, Real.dist_eq]
          exact ENNReal.ofReal_le_ofReal (hstep i)
    _ = ENNReal.ofReal (∑ i ∈ Finset.range n, (G (u (i + 1)) - G (u i))) :=
        (ENNReal.ofReal_sum_of_nonneg fun i _ => (abs_nonneg _).trans (hstep i)).symm
    _ = ENNReal.ofReal (G (u n) - G (u 0)) := by
        rw [Finset.sum_range_sub (fun i => G (u i))]
    _ ≤ ENNReal.ofReal (G y - G x) := by
        apply ENNReal.ofReal_le_ofReal
        have hx : x ∈ Icc x y := ⟨le_rfl, (hus 0).1.trans (hus 0).2⟩
        have hy : y ∈ Icc x y := ⟨(hus 0).1.trans (hus 0).2, le_rfl⟩
        have h1 := h _ (hus n) _ hy (hus n).2
        have h2 := h _ hx _ (hus 0) (hus 0).1
        linarith [abs_nonneg (φ y - φ (u n)), abs_nonneg (φ (u 0) - φ x)]

/-- **Sum of variations from a two-point bound** (the common-refinement step in the proof of
Lemma `lemma-flow`, l. 1393–1407): if `∑_{j∈T} |f_j y - f_j x| ≤ F y - F x` for all
`x ≤ y` in `[a,b]`, then `∑_{j∈T} Var_{[a,b]} f_j ≤ F b - F a`. -/
theorem sum_eVariationOn_le {ι : Type*} (T : Finset ι) (f : ι → ℝ → ℝ) {a b : ℝ}
    (hab : a ≤ b) :
    ∀ F : ℝ → ℝ, (∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → ∑ j ∈ T, |f j y - f j x| ≤ F y - F x) →
      ∑ j ∈ T, eVariationOn (f j) (Icc a b) ≤ ENNReal.ofReal (F b - F a) := by
  classical
  refine Finset.induction_on T ?_ ?_
  · intro F _
    simp
  intro k T hk ih F hF
  have hFk : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y →
      |f k y - f k x| + ∑ j ∈ T, |f j y - f j x| ≤ F y - F x := by
    intro x hx y hy hxy
    have := hF x hx y hy hxy
    rwa [Finset.sum_insert hk] at this
  -- variation of `f k` on subintervals
  have hVsub : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y →
      eVariationOn (f k) (Icc x y) ≤
        ENNReal.ofReal ((F y - F x) - ∑ j ∈ T, |f j y - f j x|) := by
    intro x hx y hy hxy
    have key := eVariationOn_le_of_abs_sub_le (φ := f k)
      (G := fun t => F t - ∑ j ∈ T, |f j t - f j x|) (x := x) (y := y) (by
        intro s hs t ht hst
        have hs' : s ∈ Icc a b := ⟨hx.1.trans hs.1, hs.2.trans hy.2⟩
        have ht' : t ∈ Icc a b := ⟨hx.1.trans ht.1, ht.2.trans hy.2⟩
        have h1 := hFk s hs' t ht' hst
        have h2 : ∑ j ∈ T, |f j t - f j x| - ∑ j ∈ T, |f j s - f j x| ≤
            ∑ j ∈ T, |f j t - f j s| := by
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_le_sum fun j _ => ?_
          have := abs_sub_abs_le_abs_sub (f j t - f j x) (f j s - f j x)
          rwa [sub_sub_sub_cancel_right] at this
        linarith)
    have e : (F y - ∑ j ∈ T, |f j y - f j x|) - (F x - ∑ j ∈ T, |f j x - f j x|) =
        (F y - F x) - ∑ j ∈ T, |f j y - f j x| := by
      simp only [sub_self, abs_zero, Finset.sum_const_zero, sub_zero]
      ring
    rw [← e]
    exact key
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hfin : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y → eVariationOn (f k) (Icc x y) ≠ ⊤ :=
    fun x hx y hy hxy => ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hVsub x hx y hy hxy)
  let v : ℝ → ℝ := fun t => (eVariationOn (f k) (Icc a t)).toReal
  have hadd : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y →
      v y - v x = (eVariationOn (f k) (Icc x y)).toReal := by
    intro x hx y hy hxy
    have := eVariationOn.Icc_add_Icc (f k) (s := Set.univ) hx.1 hxy (Set.mem_univ x)
    simp only [Set.univ_inter] at this
    simp only [v]
    rw [← this, ENNReal.toReal_add (hfin a ha x hx hx.1) (hfin x hx y hy hxy)]
    ring
  have hF' : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b, x ≤ y →
      ∑ j ∈ T, |f j y - f j x| ≤ (F y - v y) - (F x - v x) := by
    intro x hx y hy hxy
    have hnn : 0 ≤ (F y - F x) - ∑ j ∈ T, |f j y - f j x| := by
      have := hFk x hx y hy hxy
      linarith [abs_nonneg (f k y - f k x)]
    have h2 := ENNReal.toReal_le_of_le_ofReal hnn (hVsub x hx y hy hxy)
    have := hadd x hx y hy hxy
    linarith
  have ih' : ∑ j ∈ T, eVariationOn (f j) (Icc a b) ≤
      ENNReal.ofReal ((F b - v b) - (F a - v a)) := ih (fun t => F t - v t) hF'
  have hva : v a = 0 := by
    simp only [v]
    rw [eVariationOn.subsingleton (f k) (s := Icc a a)
      (by rw [Set.Icc_self]; exact Set.subsingleton_singleton)]
    exact ENNReal.toReal_zero
  rw [Finset.sum_insert hk]
  have hvb : eVariationOn (f k) (Icc a b) = ENNReal.ofReal (v b) :=
    (ENNReal.ofReal_toReal (hfin a ha b hb hab)).symm
  rw [hvb]
  have hnn2 : 0 ≤ (F b - v b) - (F a - v a) :=
    le_trans (Finset.sum_nonneg fun j _ => abs_nonneg _) (hF' a ha b hb hab)
  calc ENNReal.ofReal (v b) + ∑ j ∈ T, eVariationOn (f j) (Icc a b)
      ≤ ENNReal.ofReal (v b) + ENNReal.ofReal ((F b - v b) - (F a - v a)) := by gcongr
    _ = ENNReal.ofReal (F b - F a) := by
        rw [← ENNReal.ofReal_add ENNReal.toReal_nonneg hnn2, hva]
        congr 1
        ring

/-- `|f x - f y| ≤ Var_s f` for `x, y ∈ s`, `f` of bounded variation. -/
lemma abs_sub_le_variation {f : ℝ → ℝ} {s : Set ℝ} (hf : eVariationOn f s ≠ ⊤) {x y : ℝ}
    (hx : x ∈ s) (hy : y ∈ s) : |f x - f y| ≤ (eVariationOn f s).toReal := by
  have h := eVariationOn.edist_le f hx hy
  rw [edist_dist, Real.dist_eq] at h
  have := ENNReal.toReal_mono hf h
  rwa [ENNReal.toReal_ofReal (abs_nonneg _)] at this

/-! ## 2. Linear functionals and derivatives -/

variable {N : ℕ}

/-- `X ↦ Re tr(S X)` as an `ℝ`-linear map. -/
def trLin (S : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ →ₗ[ℝ] ℝ where
  toFun X := (trace (S * X)).re
  map_add' X Y := by simp [Matrix.mul_add, trace_add]
  map_smul' c X := by simp [Matrix.mul_smul, trace_smul]

/-- `X ↦ Xᴴ` as an `ℝ`-linear map. -/
def ctLin : Matrix (Fin N) (Fin N) ℂ →ₗ[ℝ] Matrix (Fin N) (Fin N) ℂ where
  toFun X := Xᴴ
  map_add' X Y := conjTranspose_add X Y
  map_smul' c X := by simp [conjTranspose_smul]

section Deriv

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma hasDerivWithinAt_conj {H : ℝ → Matrix (Fin N) (Fin N) ℂ} {K E : Matrix (Fin N) (Fin N) ℂ}
    {s : Set ℝ} {t : ℝ} (hd : HasDerivWithinAt H (K * H t - H t * K + E) s t) :
    HasDerivWithinAt (fun x => NormedSpace.exp (x • -K) * H x * NormedSpace.exp (x • K))
      (NormedSpace.exp (t • -K) * E * NormedSpace.exp (t • K)) s t := by
  have h1 := (hasDerivAt_exp_smul_const (-K) t).hasDerivWithinAt (s := s)
  have h2 := (hasDerivAt_exp_smul_const' K t).hasDerivWithinAt (s := s)
  have h := (h1.mul hd).mul h2
  have e : (NormedSpace.exp (t • -K) * -K * H t +
      NormedSpace.exp (t • -K) * (K * H t - H t * K + E)) * NormedSpace.exp (t • K) +
      NormedSpace.exp (t • -K) * H t * (K * NormedSpace.exp (t • K)) =
      NormedSpace.exp (t • -K) * E * NormedSpace.exp (t • K) := by noncomm_ring
  exact h.congr_deriv e

lemma hasDerivWithinAt_trace_conj {H : ℝ → Matrix (Fin N) (Fin N) ℂ}
    {K E S : Matrix (Fin N) (Fin N) ℂ} {s : Set ℝ} {t : ℝ}
    (hd : HasDerivWithinAt H (K * H t - H t * K + E) s t) :
    HasDerivWithinAt
      (fun x => (trace (S * (NormedSpace.exp (x • -K) * H x * NormedSpace.exp (x • K)))).re)
      ((trace (S * (NormedSpace.exp (t • -K) * E * NormedSpace.exp (t • K)))).re) s t := by
  have h := hasDerivWithinAt_conj hd
  exact (ContinuousLinearMap.mk (trLin S)
    (trLin S).continuous_of_finiteDimensional).hasFDerivAt.comp_hasDerivWithinAt t h

lemma hasDerivWithinAt_conjTranspose {H : ℝ → Matrix (Fin N) (Fin N) ℂ}
    {D : Matrix (Fin N) (Fin N) ℂ} {s : Set ℝ} {t : ℝ} (h : HasDerivWithinAt H D s t) :
    HasDerivWithinAt (fun x => (H x)ᴴ) Dᴴ s t := by
  exact (ContinuousLinearMap.mk (ctLin (N := N))
    (ctLin (N := N)).continuous_of_finiteDimensional).hasFDerivAt.comp_hasDerivWithinAt t h

/-- The derivative of a Hermitian path (within a nondegenerate interval) is Hermitian. -/
lemma deriv_isHermitian {H : ℝ → Matrix (Fin N) (Fin N) ℂ} {D : Matrix (Fin N) (Fin N) ℂ}
    {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b) (hH : ∀ x ∈ Icc a b, (H x).IsHermitian)
    (h : HasDerivWithinAt H D (Icc a b) t) : D.IsHermitian := by
  have h1 := hasDerivWithinAt_conjTranspose h
  have h2 : HasDerivWithinAt H Dᴴ (Icc a b) t :=
    h1.congr (fun x hx => (hH x hx).eq.symm) (hH t ht).eq.symm
  exact (uniqueDiffOn_Icc hab t ht).eq_deriv _ h2 h

lemma continuous_exp_smul (K : Matrix (Fin N) (Fin N) ℂ) :
    Continuous (fun t : ℝ => NormedSpace.exp (t • K)) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_exp_smul_const' K t).continuousAt

end Deriv

/-! ## 3. Exponentials of a skew-Hermitian matrix -/

lemma exp_neg_mul_exp (K : Matrix (Fin N) (Fin N) ℂ) (t : ℝ) :
    NormedSpace.exp (t • -K) * NormedSpace.exp (t • K) = 1 := by
  have hc : Commute (t • -K) (t • K) := ((Commute.refl K).neg_left.smul_left t).smul_right t
  rw [← Matrix.exp_add_of_commute _ _ hc, smul_neg, neg_add_cancel, NormedSpace.exp_zero]

lemma exp_mul_exp_neg (K : Matrix (Fin N) (Fin N) ℂ) (t : ℝ) :
    NormedSpace.exp (t • K) * NormedSpace.exp (t • -K) = 1 := by
  have hc : Commute (t • K) (t • -K) := ((Commute.refl K).neg_right.smul_left t).smul_right t
  rw [← Matrix.exp_add_of_commute _ _ hc, smul_neg, add_neg_cancel, NormedSpace.exp_zero]

lemma exp_neg_conjTranspose {K : Matrix (Fin N) (Fin N) ℂ} (hK : Kᴴ = -K) (t : ℝ) :
    (NormedSpace.exp (t • -K))ᴴ = NormedSpace.exp (t • K) := by
  rw [← Matrix.exp_conjTranspose, conjTranspose_smul, conjTranspose_neg, hK, neg_neg,
    star_trivial]

/-! ## 4. The flow bound (Lemma `lemma-flow`) -/

lemma isHermitian_of_flow {H K E D : Matrix (Fin N) (Fin N) ℂ} (hH : H.IsHermitian)
    (hK : Kᴴ = -K) (hD : D.IsHermitian) (hDe : D = K * H - H * K + E) : E.IsHermitian := by
  have e : E = D - (K * H - H * K) := by rw [hDe]; abel
  rw [e]
  unfold IsHermitian
  rw [conjTranspose_sub, hD.eq, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, hK,
    hH.eq]
  noncomm_ring

lemma continuousOn_traceNorm {E : ℝ → Matrix (Fin N) (Fin N) ℂ} {s : Set ℝ}
    (hE : ContinuousOn E s) (hEh : ∀ x ∈ s, (E x).IsHermitian) :
    ContinuousOn (fun x => traceNorm (E x)) s := by
  intro x₀ hx₀
  have hlim : Filter.Tendsto (fun x => hsNorm (E x - E x₀)) (𝓝[s] x₀) (𝓝 0) := by
    have := (continuous_hsNorm.tendsto (E x₀ - E x₀)).comp
      (Filter.Tendsto.sub (hE x₀ hx₀) tendsto_const_nhds)
    simpa [Function.comp_def, hsNorm_zero] using this
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Filter.Eventually.of_forall fun x => norm_nonneg _) ?_
    (by simpa using hlim.const_mul (Real.sqrt N))
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [Real.norm_eq_abs]
  exact abs_traceNorm_sub_le (hEh x hx) (hEh x₀ hx₀)

/-- The two-point bound (eq. `partitionbound`, l. 1386–1391):
`∑_j |λ_j(y) - λ_j(x)| ≤ ∫_x^y ‖𝓔(t)‖_{S_1} dt` for `a ≤ x ≤ y ≤ b`. -/
theorem flow_twoPoint {a b : ℝ} {H E : ℝ → Matrix (Fin N) (Fin N) ℂ}
    {K : Matrix (Fin N) (Fin N) ℂ} (hK : Kᴴ = -K)
    (hH : ∀ x ∈ Icc a b, (H x).IsHermitian)
    (hd : ∀ x ∈ Icc a b, HasDerivWithinAt H (K * H x - H x * K + E x) (Icc a b) x)
    (hE : ContinuousOn E (Icc a b)) (hEh : ∀ x ∈ Icc a b, (E x).IsHermitian)
    {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) (hxy : x ≤ y) :
    ∑ j, |eig (H y) j - eig (H x) j| ≤ ∫ t in x..y, traceNorm (E t) := by
  let G : ℝ → Matrix (Fin N) (Fin N) ℂ := fun t => NormedSpace.exp (t • K)
  let Gs : ℝ → Matrix (Fin N) (Fin N) ℂ := fun t => NormedSpace.exp (t • -K)
  let Ht : ℝ → Matrix (Fin N) (Fin N) ℂ := fun t => Gs t * H t * G t
  have hG1 : ∀ t, (Gs t)ᴴ * Gs t = 1 := fun t => by
    simp only [Gs]; rw [exp_neg_conjTranspose hK]; exact exp_mul_exp_neg K t
  have hG2 : ∀ t, Gs t * (Gs t)ᴴ = 1 := fun t => by
    simp only [Gs]; rw [exp_neg_conjTranspose hK]; exact exp_neg_mul_exp K t
  have hHtdef : ∀ t, Ht t = Gs t * H t * (Gs t)ᴴ := fun t => by
    simp only [Ht, Gs, G]; rw [exp_neg_conjTranspose hK]
  have hHt : ∀ t ∈ Icc a b, (Ht t).IsHermitian := fun t ht => by
    rw [hHtdef]; exact isHermitian_conj (hH t ht) _
  have heig : ∀ t ∈ Icc a b, eig (Ht t) = eig (H t) := fun t ht => by
    rw [hHtdef]; exact eig_unitary_conj (hH t ht) (hG1 t) (hG2 t)
  have hD := (hHt y hy).sub (hHt x hx)
  set S := fnH hD sgnR with hS
  let f : ℝ → ℝ := fun t => (trace (S * Ht t)).re
  let f' : ℝ → ℝ := fun t => (trace (S * (Gs t * E t * G t))).re
  have hsub : Icc x y ⊆ Icc a b := Set.Icc_subset_Icc hx.1 hy.2
  have hderiv : ∀ t ∈ Icc a b, HasDerivWithinAt f (f' t) (Icc a b) t := fun t ht =>
    hasDerivWithinAt_trace_conj (S := S) (hd t ht)
  -- continuity of `f'` and of `‖𝓔‖₁`
  have hcont' : ContinuousOn f' (Icc x y) := by
    have ctr : Continuous (fun X : Matrix (Fin N) (Fin N) ℂ => (trace (S * X)).re) :=
      Complex.continuous_re.comp ((continuous_const.mul continuous_id).matrix_trace)
    have inner : ContinuousOn (fun t => Gs t * E t * G t) (Icc x y) :=
      ((continuous_exp_smul (-K)).continuousOn.mul (hE.mono hsub)).mul
        (continuous_exp_smul K).continuousOn
    exact ctr.comp_continuousOn inner
  have hint' : IntervalIntegrable f' MeasureTheory.volume x y :=
    ContinuousOn.intervalIntegrable (by rwa [Set.uIcc_of_le hxy])
  have hintE : IntervalIntegrable (fun t => traceNorm (E t)) MeasureTheory.volume x y :=
    ContinuousOn.intervalIntegrable (by
      rw [Set.uIcc_of_le hxy]
      exact continuousOn_traceNorm (hE.mono hsub) (fun t ht => hEh t (hsub ht)))
  have hFTC : ∫ t in x..y, f' t = f y - f x := by
    apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hxy
    · exact fun t ht => ((hderiv t (hsub ht)).continuousWithinAt).mono hsub
    · intro t ht
      have ht' : t ∈ Ioo a b := ⟨lt_of_le_of_lt hx.1 ht.1, lt_of_lt_of_le ht.2 hy.2⟩
      exact ((hderiv t (Ioo_subset_Icc_self ht')).hasDerivAt
        (Icc_mem_nhds ht'.1 ht'.2)).hasDerivWithinAt
    · exact hint'
  have hmono : ∫ t in x..y, f' t ≤ ∫ t in x..y, traceNorm (E t) := by
    refine intervalIntegral.integral_mono_on hxy hint' hintE fun t ht => ?_
    have ht' := hsub ht
    have hX : (Gs t * E t * G t).IsHermitian := by
      have := isHermitian_conj (hEh t ht') (Gs t)
      simp only [Gs, G] at this ⊢
      rwa [exp_neg_conjTranspose hK] at this
    have h1 := re_trace_mul_le_traceNorm hD hX
    have h2 : traceNorm (Gs t * E t * G t) = traceNorm (E t) := by
      have := traceNorm_unitary_conj (hEh t ht') (hG1 t) (hG2 t)
      simp only [Gs, G] at this ⊢
      rwa [exp_neg_conjTranspose hK] at this
    simp only [f']
    rw [← h2]
    exact h1
  have hlid := lidskii (hHt y hy) (hHt x hx)
  rw [heig y hy, heig x hx] at hlid
  have hdual : traceNorm (Ht y - Ht x) = f y - f x := by
    show traceNorm (Ht y - Ht x) = (trace (S * Ht y)).re - (trace (S * Ht x)).re
    rw [← re_trace_sgn_mul_self hD, ← hS, Matrix.mul_sub, trace_sub, Complex.sub_re]
  linarith

/-- **Lemma `lemma-flow`** (eq. `flowbound`, l. 1352–1371): for a `C¹` Hermitian path
`H : [a,b] → M_N(ℂ)` with `H' = [K, H] + 𝓔`, `K^* = -K` constant, the ordered eigenvalues
satisfy `∑_j Var_{[a,b]} λ_j ≤ ∫_a^b ‖𝓔(x)‖_{S_1} dx`. -/
theorem flow_bound {a b : ℝ} (hab : a ≤ b) {H E : ℝ → Matrix (Fin N) (Fin N) ℂ}
    {K : Matrix (Fin N) (Fin N) ℂ} (hK : Kᴴ = -K)
    (hH : ∀ x ∈ Icc a b, (H x).IsHermitian)
    (hd : ∀ x ∈ Icc a b, HasDerivWithinAt H (K * H x - H x * K + E x) (Icc a b) x)
    (hE : ContinuousOn E (Icc a b)) :
    ∑ j, eVariationOn (fun x => eig (H x) j) (Icc a b) ≤
      ENNReal.ofReal (∫ x in a..b, traceNorm (E x)) := by
  by_cases hab' : a = b
  · subst hab'
    have : ∀ j, eVariationOn (fun x => eig (H x) j) (Icc a a) = 0 := fun j =>
      eVariationOn.subsingleton _ (by rw [Set.Icc_self]; exact Set.subsingleton_singleton)
    simp [this]
  have hlt : a < b := lt_of_le_of_ne hab hab'
  have hEh : ∀ x ∈ Icc a b, (E x).IsHermitian := fun x hx =>
    isHermitian_of_flow (hH x hx) hK (deriv_isHermitian hlt hx hH (hd x hx)) rfl
  have hint : ∀ x ∈ Icc a b, ∀ y ∈ Icc a b,
      IntervalIntegrable (fun t => traceNorm (E t)) MeasureTheory.volume x y := by
    intro x hx y hy
    apply ContinuousOn.intervalIntegrable
    have : Set.uIcc x y ⊆ Icc a b := Set.uIcc_subset_Icc hx hy
    exact continuousOn_traceNorm (hE.mono this) (fun t ht => hEh t (this ht))
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have key := sum_eVariationOn_le Finset.univ (fun j x => eig (H x) j) hab
    (fun x => ∫ t in a..x, traceNorm (E t)) (fun x hx y hy hxy => by
      have h := flow_twoPoint hK hH hd hE hEh hx hy hxy
      show ∑ j, |eig (H y) j - eig (H x) j| ≤
        (∫ t in a..y, traceNorm (E t)) - ∫ t in a..x, traceNorm (E t)
      rw [intervalIntegral.integral_interval_sub_left (hint a ha y hy) (hint a ha x hx)]
      exact h)
  simpa only [intervalIntegral.integral_same, sub_zero] using key

/-! ## 5. The abstract spectral cover (Proposition `prop-cover1`) -/

lemma isHermitian_real_smul {P : Matrix (Fin N) (Fin N) ℂ} (hP : P.IsHermitian) (c : ℝ) :
    ((c : ℂ) • P).IsHermitian := by
  unfold IsHermitian
  rw [conjTranspose_smul, hP.eq, Complex.star_def, Complex.conj_ofReal]

/-- **Proposition `prop-cover1`**, abstract core (l. 1700–1772).  Let `H^±(x) = B(x) ± cP` with
`P ≥ 0`, `c ≥ 0`, and suppose the ordered eigenvalues `λ_j^±` of `H^±` have total variation
`∑_j Var_J λ_j^+ + ∑_j Var_J λ_j^- ≤ V` on `J = [a,b]`.  Then there are intervals
`[lo_j, hi_j]`, independent of `x ∈ J` and of the perturbation `W` (`-cP ≤ W ≤ cP`), with
`σ(B(x) + W) ⊆ ⋃_j [lo_j, hi_j]` and `∑_j (hi_j - lo_j) ≤ 2c·tr P + V`. -/
theorem cover_core {a b : ℝ} (hab : a ≤ b) (B : ℝ → Matrix (Fin N) (Fin N) ℂ)
    {P : Matrix (Fin N) (Fin N) ℂ} {c V : ℝ} (hc : 0 ≤ c) (hV0 : 0 ≤ V)
    (hB : ∀ x ∈ Icc a b, (B x).IsHermitian) (hP : P.PosSemidef)
    (hV : ∑ j, eVariationOn (fun x => eig (B x + (c : ℂ) • P) j) (Icc a b) +
        ∑ j, eVariationOn (fun x => eig (B x - (c : ℂ) • P) j) (Icc a b) ≤ ENNReal.ofReal V) :
    ∃ lo hi : Fin N → ℝ, (∀ j, lo j ≤ hi j) ∧
      ∑ j, (hi j - lo j) ≤ 2 * c * (trace P).re + V ∧
      ∀ x ∈ Icc a b, ∀ W : Matrix (Fin N) (Fin N) ℂ, W.IsHermitian →
        ((c : ℂ) • P - W).PosSemidef → (W + (c : ℂ) • P).PosSemidef →
        spectrum ℝ (B x + W) ⊆ ⋃ j, Icc (lo j) (hi j) := by
  set vp : Fin N → ENNReal := fun j => eVariationOn (fun x => eig (B x + (c : ℂ) • P) j) (Icc a b)
  set vm : Fin N → ENNReal := fun j => eVariationOn (fun x => eig (B x - (c : ℂ) • P) j) (Icc a b)
  have hVfin : ∑ j, vp j + ∑ j, vm j ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hV
  have hpfin : ∀ j, vp j ≠ ⊤ := fun j => ne_top_of_le_ne_top (ENNReal.add_ne_top.1 hVfin).1
    (Finset.single_le_sum (fun i _ => zero_le) (Finset.mem_univ j))
  have hmfin : ∀ j, vm j ≠ ⊤ := fun j => ne_top_of_le_ne_top (ENNReal.add_ne_top.1 hVfin).2
    (Finset.single_le_sum (fun i _ => zero_le) (Finset.mem_univ j))
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hcP : ((c : ℂ) • P).PosSemidef := hP.smul (Complex.zero_le_real.2 hc)
  have hcPh := hcP.isHermitian
  refine ⟨fun j => eig (B a - (c : ℂ) • P) j - (vm j).toReal,
    fun j => eig (B a + (c : ℂ) • P) j + (vp j).toReal, ?_, ?_, ?_⟩
  · intro j
    dsimp only
    have := eig_mono ((hB a ha).sub hcPh) ((hB a ha).add hcPh)
      (by rw [show B a + (c : ℂ) • P - (B a - (c : ℂ) • P) = (c : ℂ) • P + (c : ℂ) • P by abel]
          exact hcP.add hcP) j
    linarith [ENNReal.toReal_nonneg (a := vp j), ENNReal.toReal_nonneg (a := vm j)]
  · have htr : ∑ j, (eig (B a + (c : ℂ) • P) j - eig (B a - (c : ℂ) • P) j) =
        2 * c * (trace P).re := by
      rw [Finset.sum_sub_distrib, sum_eig_eq_trace ((hB a ha).add hcPh),
        sum_eig_eq_trace ((hB a ha).sub hcPh), ← Complex.sub_re, ← trace_sub,
        show B a + (c : ℂ) • P - (B a - (c : ℂ) • P) = (c : ℂ) • P + (c : ℂ) • P by abel,
        trace_add, trace_smul, smul_eq_mul, Complex.add_re, Complex.re_ofReal_mul]
      ring
    have hvar : ∑ j, (vp j).toReal + ∑ j, (vm j).toReal ≤ V := by
      rw [← ENNReal.toReal_sum (fun j _ => hpfin j), ← ENNReal.toReal_sum (fun j _ => hmfin j),
        ← ENNReal.toReal_add (ENNReal.add_ne_top.1 hVfin).1 (ENNReal.add_ne_top.1 hVfin).2]
      exact ENNReal.toReal_le_of_le_ofReal hV0 hV
    have e : ∑ j, ((eig (B a + (c : ℂ) • P) j + (vp j).toReal) -
        (eig (B a - (c : ℂ) • P) j - (vm j).toReal)) =
        ∑ j, (eig (B a + (c : ℂ) • P) j - eig (B a - (c : ℂ) • P) j) +
          (∑ j, (vp j).toReal + ∑ j, (vm j).toReal) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    dsimp only
    rw [e, htr]
    linarith
  · intro x hx W hW hW1 hW2 μ hμ
    have hBW := (hB x hx).add hW
    rw [spectrum_eq_range_eig hBW] at hμ
    obtain ⟨j, rfl⟩ := hμ
    refine Set.mem_iUnion.2 ⟨j, ?_, ?_⟩
    · have h1 := eig_mono ((hB x hx).sub hcPh) hBW
        (by rw [show B x + W - (B x - (c : ℂ) • P) = W + (c : ℂ) • P by abel]; exact hW2) j
      have h2 : |eig (B x - (c : ℂ) • P) j - eig (B a - (c : ℂ) • P) j| ≤ (vm j).toReal :=
        abs_sub_le_variation (f := fun x => eig (B x - (c : ℂ) • P) j) (hmfin j) hx ha
      dsimp only
      linarith [(abs_le.1 h2).1]
    · have h1 := eig_mono hBW ((hB x hx).add hcPh)
        (by rw [show B x + (c : ℂ) • P - (B x + W) = (c : ℂ) • P - W by abel]; exact hW1) j
      have h2 : |eig (B x + (c : ℂ) • P) j - eig (B a + (c : ℂ) • P) j| ≤ (vp j).toReal :=
        abs_sub_le_variation (f := fun x => eig (B x + (c : ℂ) • P) j) (hpfin j) hx ha
      dsimp only
      linarith [(abs_le.1 h2).2]

/-! ## 6. The boundary map -/

/-- The boundary map `Γ̂_N : ℂ^N → ℂ^2`, `u ↦ (u_0, u_{N-1})` (eq. `bp`, l. 1271).  Same
definition as `CAH.bdry` in `BoundaryResolvent.lean`. -/
def bdry (N : ℕ) : Matrix (Fin 2) (Fin N) ℂ :=
  Matrix.of fun i j =>
    if ((i : ℕ) = 0 ∧ (j : ℕ) = 0) ∨ ((i : ℕ) = 1 ∧ (j : ℕ) + 1 = N) then 1 else 0

/-- The boundary projection `P_N = Γ̂_N^* Γ̂_N`. -/
def bdryProj (N : ℕ) : Matrix (Fin N) (Fin N) ℂ := (bdry N)ᴴ * bdry N

lemma bdryProj_posSemidef (N : ℕ) : (bdryProj N).PosSemidef :=
  posSemidef_conjTranspose_mul_self _

lemma sum_fin_ite_val_eq (k : ℕ) (hk : k < N) :
    ∑ j : Fin N, (if (j : ℕ) = k then (1 : ℂ) else 0) = 1 := by
  rw [Finset.sum_eq_single ⟨k, hk⟩]
  · simp
  · intro j _ hj
    rw [if_neg]
    intro h
    exact hj (Fin.ext h)
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- `tr P_N = 2` for `N ≥ 1`. -/
lemma trace_bdryProj (hN : 1 ≤ N) : (trace (bdryProj N)).re = 2 := by
  have e : trace (bdryProj N) = ∑ i : Fin 2, ∑ j : Fin N, bdry N i j * star (bdry N i j) := by
    rw [bdryProj, trace_mul_comm]
    simp only [Matrix.trace, Matrix.diag_apply, mul_apply, conjTranspose_apply]
  have hb : ∀ i j, bdry N i j * star (bdry N i j) = bdry N i j := by
    intro i j
    simp only [bdry, of_apply]
    split_ifs <;> simp
  simp only [hb] at e
  rw [e, Fin.sum_univ_two]
  have h0 : ∑ j : Fin N, bdry N 0 j = 1 := by
    rw [← sum_fin_ite_val_eq (N := N) 0 (by omega)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [bdry, of_apply]
    by_cases hj : (j : ℕ) = 0
    · rw [if_pos hj, if_pos (Or.inl ⟨rfl, hj⟩)]
    · rw [if_neg hj, if_neg]
      rintro (⟨_, h⟩ | ⟨h, _⟩)
      · exact hj h
      · exact absurd h (by decide)
  have h1 : ∑ j : Fin N, bdry N 1 j = 1 := by
    rw [← sum_fin_ite_val_eq (N := N) (N - 1) (by omega)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [bdry, of_apply]
    by_cases hj : (j : ℕ) = N - 1
    · rw [if_pos hj, if_pos (Or.inr ⟨rfl, by omega⟩)]
    · rw [if_neg hj, if_neg]
      rintro (⟨h, _⟩ | ⟨_, h⟩)
      · exact absurd h (by decide)
      · omega
  rw [h0, h1]
  norm_num

lemma fnH_const {M : ℕ} {C : Matrix (Fin M) (Fin M) ℂ} (hC : C.IsHermitian) (c : ℝ) :
    fnH hC (fun _ => c) = (c : ℂ) • 1 := by
  simp only [fnH]
  rw [← smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, eigU_mul_star]

/-- For Hermitian `V ∈ M_2(ℂ)` with eigenvalues in `[-c, c]` (i.e. `‖V‖ ≤ c`), we have
`-c ≤ V ≤ c`. -/
lemma le_of_abs_eigenvalues_le {V : Matrix (Fin 2) (Fin 2) ℂ} (hV : V.IsHermitian) {c : ℝ}
    (h : ∀ i, |hV.eigenvalues i| ≤ c) :
    ((c : ℂ) • 1 - V).PosSemidef ∧ (V + (c : ℂ) • 1).PosSemidef := by
  have e1 : (c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - V = fnH hV (fun x => c - x) := by
    calc (c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) - V
        = fnH hV (fun _ => c) - fnH hV (fun x => x) := by rw [fnH_id, fnH_const]
      _ = fnH hV (fun x => c - x) := (fnH_sub hV (fun _ => c) (fun x => x)).symm
  have e2 : V + (c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) = fnH hV (fun x => x + c) := by
    calc V + (c : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
        = fnH hV (fun x => x) + fnH hV (fun _ => c) := by rw [fnH_id, fnH_const]
      _ = fnH hV (fun x => x + c) := (fnH_add hV (fun x => x) (fun _ => c)).symm
  rw [e1, e2]
  exact ⟨fnH_posSemidef hV fun i => by
      show 0 ≤ c - hV.eigenvalues i; linarith [(abs_le.1 (h i)).2],
    fnH_posSemidef hV fun i => by
      show 0 ≤ hV.eigenvalues i + c; linarith [(abs_le.1 (h i)).1]⟩

/-- Proof of Proposition `prop-cover1`, first display (l. 1700–1705): if `-c ≤ V ≤ c` then
`-c P_N ≤ Γ̂_N^* V Γ̂_N ≤ c P_N`. -/
theorem bdry_conj_bounds {V : Matrix (Fin 2) (Fin 2) ℂ} {c : ℝ}
    (h1 : ((c : ℂ) • 1 - V).PosSemidef) (h2 : (V + (c : ℂ) • 1).PosSemidef) :
    ((c : ℂ) • bdryProj N - (bdry N)ᴴ * V * bdry N).PosSemidef ∧
      ((bdry N)ᴴ * V * bdry N + (c : ℂ) • bdryProj N).PosSemidef := by
  have k1 := h1.conjTranspose_mul_mul_same (bdry N)
  have k2 := h2.conjTranspose_mul_mul_same (bdry N)
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] at k1
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one] at k2
  exact ⟨k1, k2⟩

/-- **Proposition `prop-cover1`** for boundary perturbations (l. 1676–1772, with
`P = P_N`, `tr P_N = 2`): with `H^±(x) = B(x) ± c P_N` whose ordered eigenvalues have total
variation `≤ V` on `J = [a,b]`, there are `N` intervals of total length `≤ 4c + V`,
independent of `x ∈ J` and of `V₂` (Hermitian `2×2` with eigenvalues in `[-c,c]`, i.e.
`‖V₂‖ ≤ c`), covering `σ(B(x) + Γ̂_N^* V₂ Γ̂_N)`. -/
theorem cover_bdry {a b : ℝ} (hab : a ≤ b) (hN : 1 ≤ N) (B : ℝ → Matrix (Fin N) (Fin N) ℂ)
    {c V : ℝ} (hc : 0 ≤ c) (hV0 : 0 ≤ V) (hB : ∀ x ∈ Icc a b, (B x).IsHermitian)
    (hV : ∑ j, eVariationOn (fun x => eig (B x + (c : ℂ) • bdryProj N) j) (Icc a b) +
        ∑ j, eVariationOn (fun x => eig (B x - (c : ℂ) • bdryProj N) j) (Icc a b) ≤
          ENNReal.ofReal V) :
    ∃ lo hi : Fin N → ℝ, (∀ j, lo j ≤ hi j) ∧ ∑ j, (hi j - lo j) ≤ 4 * c + V ∧
      ∀ x ∈ Icc a b, ∀ V₂ : Matrix (Fin 2) (Fin 2) ℂ, ∀ hV₂ : V₂.IsHermitian,
        (∀ i, |hV₂.eigenvalues i| ≤ c) →
        spectrum ℝ (B x + (bdry N)ᴴ * V₂ * bdry N) ⊆ ⋃ j, Icc (lo j) (hi j) := by
  obtain ⟨lo, hi, hle, hlen, hcov⟩ := cover_core hab B hc hV0 hB (bdryProj_posSemidef N) hV
  refine ⟨lo, hi, hle, ?_, ?_⟩
  · rw [trace_bdryProj hN] at hlen
    linarith
  · intro x hx V₂ hV₂ hc₂
    obtain ⟨k1, k2⟩ := le_of_abs_eigenvalues_le hV₂ hc₂
    obtain ⟨b1, b2⟩ := bdry_conj_bounds (N := N) k1 k2
    exact hcov x hx _ (isHermitian_conjTranspose_mul_mul _ hV₂) b1 b2

end Flow
end CAH
