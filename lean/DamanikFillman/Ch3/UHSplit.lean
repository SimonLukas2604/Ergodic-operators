/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §3.8.1: an invariant exponential splitting gives uniform growth (Theorem 3.8.2, (b) ⇒ (a))

Main results:
* `DF.Cocycle.exists_ne_zero_mem_lineOf` — the line of a line projection is nontrivial;
* `DF.Cocycle.mem_lineOf_iterZ` — invariance of a line field under the iterates `A_n`, `n ≥ 0`;
* `DF.Cocycle.uniformExpGrowth_of_invExpSplitting` — **Theorem 3.8.2, (b) ⇒ (a)**: vectors in
  `Λᵘ(ω)` are expanded by `A_n(ω)` at rate `c⁻¹ Lⁿ` (they decay in backward time), and vectors
  in `Λˢ(T⁻ⁿω)` are mapped by `A_{-n}(ω) = A_n(T⁻ⁿω)⁻¹` with the same expansion;
* `DF.Cocycle.not_boundedOrbit_of_invExpSplitting` — **Theorem 3.8.2, (b) ⇒ (c)**;
* `DF.Cocycle.uniformHyperbolicityCharacterization_of` — the remaining implication
  (a) ⇒ (b) suffices for `DF.Cocycle.UniformHyperbolicityCharacterizationStatement`.
-/
import DamanikFillman.Ch3.UH2

noncomputable section

set_option linter.unusedSectionVars false

open Filter Set Function Topology Matrix
open scoped Matrix.Norms.L2Operator

namespace DF

namespace Cocycle

lemma exists_ne_zero_mem_lineOf {P : M2R} (hP : IsLineProj P) :
    ∃ v : EuclideanSpace ℝ (Fin 2), v ≠ 0 ∧ v ∈ lineOf P := by
  have htr : P 0 0 + P 1 1 = 1 := by
    have := hP.2.2; rwa [Matrix.trace_fin_two] at this
  obtain ⟨j, hj⟩ : ∃ j : Fin 2, P j j ≠ 0 := by
    by_contra h
    push_neg at h
    rw [h 0, h 1] at htr
    norm_num at htr
  refine ⟨act P (EuclideanSpace.single j 1), ?_, ?_⟩
  · intro h0
    have := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w j) h0
    simp only [act_apply, EuclideanSpace.single_apply, PiLp.zero_apply] at this
    fin_cases j <;> simp_all
  · show act P (act P _) = act P _
    rw [← act_mul, hP.1]

variable {X : Type*} [TopologicalSpace X]

lemma mem_lineOf_iterZ {T : X ≃ₜ X} {A : X → SL2R} {P : X → M2R}
    (hinv : ∀ ω, ∀ v ∈ lineOf (P ω), act (A ω : M2R) v ∈ lineOf (P (T ω)))
    (k : ℕ) (ω : X) {v : EuclideanSpace ℝ (Fin 2)} (hv : v ∈ lineOf (P ω)) :
    act ((iterZ T.toEquiv A k ω : SL2R) : M2R) v ∈ lineOf (P (tpow T.toEquiv k ω)) := by
  induction k with
  | zero =>
    rw [Nat.cast_zero, iterZ_zero, tpow_zero, Matrix.SpecialLinearGroup.coe_one, act_one]
    exact hv
  | succ k ih =>
    rw [Nat.cast_succ, iterZ_succ, tpow_add_one, Matrix.SpecialLinearGroup.coe_mul, act_mul]
    exact hinv _ _ ih

lemma le_norm_of_contract {N c L x y : ℝ} (hc : 0 < c) (hL : 1 < L) (k : ℕ)
    (hv0 : 0 < x) (h1 : x ≤ c * L⁻¹ ^ k * y) (h2 : y ≤ N * x) : c⁻¹ * L ^ k ≤ N := by
  have hLk : 0 < L ^ k := pow_pos (by linarith) k
  have h3 : x ≤ c * L⁻¹ ^ k * N * x := by
    calc x ≤ c * L⁻¹ ^ k * y := h1
      _ ≤ c * L⁻¹ ^ k * (N * x) := by gcongr
      _ = _ := by ring
  have h4 : 1 ≤ c * L⁻¹ ^ k * N := by
    by_contra h
    push_neg at h
    have := mul_lt_mul_of_pos_right h hv0
    linarith
  rw [inv_pow] at h4
  rw [inv_mul_le_iff₀ hc]
  have h5 : c * (L ^ k)⁻¹ * N * L ^ k = c * N := by field_simp
  calc L ^ k = 1 * L ^ k := (one_mul _).symm
    _ ≤ c * (L ^ k)⁻¹ * N * L ^ k := by gcongr
    _ = c * N := h5

/-- **Theorem 3.8.2, (b) ⇒ (a)**: an invariant exponential splitting implies uniform exponential
growth. -/
theorem uniformExpGrowth_of_invExpSplitting (T : X ≃ₜ X) (A : X → SL2R)
    (h : InvExpSplitting T A) : UniformExpGrowth T A := by
  obtain ⟨c, hc, L, hL, Ps, Pu, -, -, hPs, hPu, hinvs, hinvu, hs, hu⟩ := h
  refine ⟨c⁻¹, inv_pos.2 hc, L, hL, fun n ω => ?_⟩
  rcases Int.eq_nat_or_neg n with ⟨k, rfl | rfl⟩
  · -- forward time: use the unstable line at `ω`
    rw [Int.natAbs_natCast]
    obtain ⟨v, hv0, hv⟩ := exists_ne_zero_mem_lineOf (hPu ω)
    set w := act ((iterZ T.toEquiv A k ω : SL2R) : M2R) v with hwdef
    have hw : w ∈ lineOf (Pu (tpow T.toEquiv k ω)) := mem_lineOf_iterZ hinvu k ω hv
    have hback := hu k _ w hw
    have hid : act ((iterZ T.toEquiv A (-(k : ℤ)) (tpow T.toEquiv k ω) : SL2R) : M2R) w = v := by
      rw [hwdef]
      rw [← act_mul, ← Matrix.SpecialLinearGroup.coe_mul, ← iterZ_add, add_neg_cancel,
        iterZ_zero, Matrix.SpecialLinearGroup.coe_one, act_one]
    rw [hid] at hback
    exact le_norm_of_contract hc hL k (norm_pos_iff.2 hv0) hback (norm_act_le _ _)
  · -- backward time: use the stable line at `T⁻ᵏω`
    rw [Int.natAbs_neg, Int.natAbs_natCast]
    set ω' := tpow T.toEquiv (-(k : ℤ)) ω with hω'def
    have hω : tpow T.toEquiv k ω' = ω := by
      rw [hω'def, ← tpow_add, neg_add_cancel, tpow_zero]
    obtain ⟨v, hv0, hv⟩ := exists_ne_zero_mem_lineOf (hPs ω')
    set w := act ((iterZ T.toEquiv A k ω' : SL2R) : M2R) v with hwdef
    have hfwd := hs k ω' v hv
    have hid : act ((iterZ T.toEquiv A (-(k : ℤ)) ω : SL2R) : M2R) w = v := by
      rw [hwdef]
      rw [← hω, ← act_mul, ← Matrix.SpecialLinearGroup.coe_mul, ← iterZ_add, add_neg_cancel,
        iterZ_zero, Matrix.SpecialLinearGroup.coe_one, act_one]
    -- `‖v‖ ≤ ‖A_{-k}(ω)‖ ‖w‖ ≤ ‖A_{-k}(ω)‖ c L⁻ᵏ ‖v‖`
    have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv0
    set N := ‖((iterZ T.toEquiv A (-(k : ℤ)) ω : SL2R) : M2R)‖
    have h1 : ‖v‖ ≤ N * ‖w‖ := by
      calc ‖v‖ = ‖act ((iterZ T.toEquiv A (-(k : ℤ)) ω : SL2R) : M2R) w‖ := by rw [hid]
        _ ≤ N * ‖w‖ := norm_act_le _ _
    have h2 : ‖v‖ ≤ c * L⁻¹ ^ k * (N * ‖v‖) := by
      calc ‖v‖ ≤ N * ‖w‖ := h1
        _ ≤ N * (c * L⁻¹ ^ k * ‖v‖) := by gcongr
        _ = _ := by ring
    exact le_norm_of_contract hc hL k hv' h2 le_rfl

end Cocycle

namespace Cocycle

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- **Theorem 3.8.2, (b) ⇒ (c)**. -/
theorem not_boundedOrbit_of_invExpSplitting (T : X ≃ₜ X) (A : X → SL2R)
    (hA : Continuous fun ω => (A ω : M2R)) (h : InvExpSplitting T A) : ¬ BoundedOrbit T A :=
  not_boundedOrbit_of_uniformExpGrowth T A hA (uniformExpGrowth_of_invExpSplitting T A h)

/-- Theorem 3.8.2 reduces to the implication (a) ⇒ (b). -/
theorem uniformHyperbolicityCharacterization_of
    (h : ∀ (X : Type) [MetricSpace X] [CompactSpace X] (T : X ≃ₜ X) (A : X → SL2R),
      Continuous (fun ω => (A ω : M2R)) → UniformExpGrowth T A → InvExpSplitting T A) :
    UniformHyperbolicityCharacterizationStatement := fun X _ _ T A hA =>
  ⟨⟨h X T A hA, uniformExpGrowth_of_invExpSplitting T A⟩,
    uniformExpGrowth_iff_not_boundedOrbit T A hA⟩

end Cocycle

end DF
