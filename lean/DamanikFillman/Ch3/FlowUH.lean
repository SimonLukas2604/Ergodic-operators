/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §3.9.1: uniform hyperbolicity of cocycles over flows (Theorem 3.9.5)

Main results:
* `DF.iterZ_flow` — the time-one cocycle `(ϕ₁, Φ₁)` has iterates `Φ_n`, `n ∈ ℤ`;
* `DF.flowUH` — **Theorem 3.9.5** (items (a), (c), (d)): for a continuous `SL(2, ℝ)` cocycle over a
  continuous flow on a compact metric space, uniform exponential growth, absence of bounded
  orbits, and uniform hyperbolicity of the time-one cocycle are equivalent. This proves
  `DF.FlowUHStatement`.

The proof interpolates between integer times (using compactness of `Ω × [0, 1]`) and uses the
discrete Theorem 3.8.2 ((a) ⟺ (c), `DF.Cocycle.uniformExpGrowth_iff_not_boundedOrbit`) together
with the one-sided growth of every vector for uniformly hyperbolic cocycles.
-/
import DamanikFillman.Ch3.UHOpen
import DamanikFillman.Ch3.Flows

noncomputable section

set_option linter.unusedSectionVars false

open Filter Set Function Topology Matrix
open scoped Matrix.Norms.L2Operator

namespace DF

open Cocycle

variable {X : Type*} [TopologicalSpace X] {ϕ : Flow ℝ X}

lemma tpow_flow (n : ℤ) (ω : X) : tpow (ϕ.toHomeomorph 1).toEquiv n ω = ϕ n ω := by
  induction n using Int.induction_on generalizing ω with
  | zero => rw [tpow_zero]; simp [Flow.map_zero_apply]
  | succ i ih =>
    rw [tpow_add_one, ih]
    show ϕ 1 (ϕ i ω) = ϕ ((i : ℤ) + 1 : ℤ) ω
    rw [← Flow.map_add]; push_cast; ring_nf
  | pred i ih =>
    rw [tpow_sub_one, ih]
    show ϕ (-1) (ϕ (-(i : ℤ) : ℤ) ω) = ϕ ((-(i : ℤ) - 1 : ℤ)) ω
    rw [← Flow.map_add]; push_cast; ring_nf

/-- The iterates of the time-one cocycle are the values of the flow cocycle at integer times. -/
lemma iterZ_flow (Φ : FlowCocycle ϕ) (n : ℤ) (ω : X) :
    iterZ (ϕ.toHomeomorph 1).toEquiv (fun ω => Φ.toFun ω 1) n ω = Φ.toFun ω n := by
  induction n using Int.induction_on generalizing ω with
  | zero => rw [iterZ_zero]; simp [Φ.map_zero]
  | succ i ih =>
    rw [iterZ_succ, ih, tpow_flow]
    have := Φ.map_add ω (i : ℤ) 1
    push_cast at this ⊢
    rw [this]
  | pred i ih =>
    rw [iterZ_pred, ih, tpow_flow]
    have := Φ.map_add ω ((-(i : ℤ) - 1 : ℤ) : ℝ) 1
    rw [show ((-(i : ℤ) - 1 : ℤ) : ℝ) + 1 = ((-(i : ℤ) : ℤ) : ℝ) by push_cast; ring] at this
    rw [this, ← mul_assoc, inv_mul_cancel, one_mul]

variable [MetricSpace X] [CompactSpace X]

/-- **Theorem 3.9.5**: `DF.FlowUHStatement` holds. -/
theorem flowUH : FlowUHStatement := by
  intro X _ _ ϕ Φ hΦ
  classical
  set A : X → SL2R := fun ω => Φ.toFun ω 1
  set T := ϕ.toHomeomorph 1
  have hA : Continuous fun ω => (A ω : M2R) := hΦ.comp (continuous_id.prodMk continuous_const)
  have hit : ∀ (n : ℤ) ω, iterZ T.toEquiv A n ω = Φ.toFun ω n := fun n ω => iterZ_flow Φ n ω
  -- bounds on `[0, 1]`
  have hΦinv : Continuous fun p : X × ℝ => (((Φ.toFun p.1 p.2)⁻¹ : SL2R) : M2R) := by
    simp_rw [Matrix.SpecialLinearGroup.coe_inv, adjugate_eq_trace]
    exact (hΦ.matrix_trace.smul continuous_const).sub hΦ
  have hKc : IsCompact (univ ×ˢ Icc (0 : ℝ) 1 : Set (X × ℝ)) := isCompact_univ.prod isCompact_Icc
  obtain ⟨K1, hK1⟩ := hKc.exists_bound_of_continuousOn hΦ.continuousOn
  obtain ⟨K2, hK2⟩ := hKc.exists_bound_of_continuousOn hΦinv.continuousOn
  set K := max (max K1 K2) 1
  have hK : 1 ≤ K := le_max_right _ _
  have hKΦ : ∀ ω (s : ℝ), 0 ≤ s → s ≤ 1 → ‖((Φ.toFun ω s : SL2R) : M2R)‖ ≤ K := fun ω s h0 h1 =>
    (hK1 (ω, s) ⟨mem_univ _, h0, h1⟩).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hKΦi : ∀ ω (s : ℝ), 0 ≤ s → s ≤ 1 → ‖(((Φ.toFun ω s)⁻¹ : SL2R) : M2R)‖ ≤ K :=
    fun ω s h0 h1 =>
      (hK2 (ω, s) ⟨mem_univ _, h0, h1⟩).trans ((le_max_right _ _).trans (le_max_left _ _))
  -- decomposition `t = ⌊t⌋ + s`
  have hdec : ∀ ω (t : ℝ), Φ.toFun ω t =
      Φ.toFun (ϕ (⌊t⌋ : ℝ) ω) (t - ⌊t⌋) * Φ.toFun ω (⌊t⌋ : ℝ) := by
    intro ω t
    rw [← Φ.map_add]; congr 1; ring
  have hs0 : ∀ t : ℝ, 0 ≤ t - ⌊t⌋ := fun t => sub_nonneg.2 (Int.floor_le t)
  have hs1 : ∀ t : ℝ, t - ⌊t⌋ ≤ 1 := fun t => by linarith [Int.lt_floor_add_one t]
  -- vectors: lower and upper comparison with integer times
  have hvlow : ∀ ω (t : ℝ) v, ‖act ((Φ.toFun ω (⌊t⌋ : ℝ) : SL2R) : M2R) v‖ ≤
      K * ‖act ((Φ.toFun ω t : SL2R) : M2R) v‖ := by
    intro ω t v
    rw [hdec ω t, Matrix.SpecialLinearGroup.coe_mul, act_mul]
    exact (norm_le_inv_mul_act _ _).trans
      (mul_le_mul_of_nonneg_right (hKΦi _ _ (hs0 t) (hs1 t)) (norm_nonneg _))
  have hvup : ∀ ω (t : ℝ) v, ‖act ((Φ.toFun ω t : SL2R) : M2R) v‖ ≤
      K * ‖act ((Φ.toFun ω (⌊t⌋ : ℝ) : SL2R) : M2R) v‖ := by
    intro ω t v
    rw [hdec ω t, Matrix.SpecialLinearGroup.coe_mul, act_mul]
    exact (norm_act_le _ _).trans
      (mul_le_mul_of_nonneg_right (hKΦ _ _ (hs0 t) (hs1 t)) (norm_nonneg _))
  have hmlow : ∀ ω (t : ℝ), ‖((Φ.toFun ω (⌊t⌋ : ℝ) : SL2R) : M2R)‖ ≤
      K * ‖((Φ.toFun ω t : SL2R) : M2R)‖ := by
    intro ω t
    have e : ((Φ.toFun ω (⌊t⌋ : ℝ) : SL2R) : M2R) =
        (((Φ.toFun (ϕ (⌊t⌋ : ℝ) ω) (t - ⌊t⌋))⁻¹ : SL2R) : M2R) * ((Φ.toFun ω t : SL2R) : M2R) := by
      rw [hdec ω t, ← Matrix.SpecialLinearGroup.coe_mul, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [e]
    exact (norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (hKΦi _ _ (hs0 t) (hs1 t)) (norm_nonneg _))
  -- (a) for the flow ⟺ (a) for the time-one map
  have hAD : FlowUniformExpGrowth Φ ↔ UniformExpGrowth T A := by
    constructor
    · rintro ⟨C, hC, l, hl, h⟩
      refine ⟨C, hC, l, hl, fun n ω => ?_⟩
      rw [hit]
      have := h n ω
      rwa [show |(n : ℝ)| = ((n.natAbs : ℕ) : ℝ) by rw [Nat.cast_natAbs, Int.cast_abs], Real.rpow_natCast] at this
    · rintro ⟨C, hC, l, hl, h⟩
      refine ⟨C / (K * l), by positivity, l, hl, fun t ω => ?_⟩
      have h1 := h ⌊t⌋ ω
      rw [hit] at h1
      have h2 := hmlow ω t
      have hl0 : 0 < l := by linarith
      have h3 : l ^ |t| ≤ l ^ (⌊t⌋.natAbs : ℕ) * l := by
        rw [← Real.rpow_natCast, ← Real.rpow_add_one hl0.ne']
        apply Real.rpow_le_rpow_of_exponent_le hl.le
        have : |t| ≤ |(⌊t⌋ : ℝ)| + 1 := by
          have := abs_sub_abs_le_abs_sub t ⌊t⌋
          rw [abs_of_nonneg (hs0 t)] at this
          linarith [hs1 t]
        rw [Nat.cast_natAbs, Int.cast_abs]
        exact this
      have hK0 : 0 < K := by linarith
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      calc C * l ^ |t| ≤ C * (l ^ (⌊t⌋.natAbs : ℕ) * l) := by gcongr
        _ = (C * l ^ (⌊t⌋.natAbs : ℕ)) * l := by ring
        _ ≤ (K * ‖((Φ.toFun ω t : SL2R) : M2R)‖) * l :=
            mul_le_mul_of_nonneg_right (h1.trans h2) hl0.le
        _ = _ := by ring
  -- discrete bounded orbits give flow bounded orbits
  have hBO : BoundedOrbit T A → FlowBoundedOrbit Φ := by
    rintro ⟨ω, v, hv, hb⟩
    refine ⟨ω, v, hv, K, ?_⟩
    rintro _ ⟨t, rfl⟩
    have h1 := hvup ω t v
    have h2 := hb ⌊t⌋
    rw [hit] at h2
    nlinarith [norm_nonneg (act ((Φ.toFun ω (⌊t⌋ : ℝ) : SL2R) : M2R) v)]
  -- flow bounded orbits exclude uniform hyperbolicity
  have hFBO : FlowBoundedOrbit Φ → ¬ UniformExpGrowth T A := by
    rintro ⟨ω, v, hv, M, hM⟩ hU
    obtain ⟨C0, hC0, l, hl, M0, hg⟩ := one_sided_growth_of_uniformExpGrowth T A hA hU
    have hbd : ∀ t : ℝ, ‖act ((Φ.toFun ω t : SL2R) : M2R) v‖ ≤ M := fun t => hM ⟨t, rfl⟩
    obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (M / C0) hl
    set m' := max m M0
    have hm' : M / C0 < l ^ m' := hm.trans_le (pow_le_pow_right₀ hl.le (le_max_left _ _))
    rw [div_lt_iff₀ hC0] at hm'
    rcases hg ω v with h | h
    · have e1 := h m' (le_max_right _ _)
      rw [hv, mul_one, hit] at e1
      have e2 := hbd (((m' : ℤ) : ℤ) : ℝ)
      exact absurd (hm'.trans_le (e1.trans e2)) (lt_irrefl _)
    · have e1 := h m' (le_max_right _ _)
      rw [hv, mul_one, hit] at e1
      have e2 := hbd ((-(m' : ℤ) : ℤ) : ℝ)
      exact absurd (hm'.trans_le (e1.trans e2)) (lt_irrefl _)
  refine ⟨⟨fun hU hB => hFBO hB (hAD.1 hU), fun hnB => hAD.2 ?_⟩, hAD⟩
  exact uniformExpGrowth_of_not_boundedOrbit T A hA fun hB => hnB (hBO hB)

end DF
