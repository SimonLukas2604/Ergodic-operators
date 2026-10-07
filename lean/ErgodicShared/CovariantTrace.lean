import ErgodicShared.IDSAveraging
import ErgodicShared.UnitaryTransfer

/-!
# The trace property of the covariant trace

For a family `x ↦ A_x` of operators on `ℓ²(ℤ)` let `τ(A) = ∫₀¹ ⟪δ₀, A_x δ₀⟫ dx` (for `A_x = g(H_x)`
this is `∫ g dν`, `ν` the density of states). We call `A` a **covariant family** (`IsCovFam α A`) if
it is norm continuous, `1`-periodic, and covariant under the shift `(Su)_n = u_{n+1}`:
`A_{x+α} S = S A_x`.

* `CMS.tau_mul_comm`: **trace property** `τ(AB) = τ(BA)` for covariant families. Proof: by
  Parseval `⟪δ₀, A_x B_x δ₀⟫ = ∑ₙ ⟪δ₀, A_x δₙ⟫⟪δₙ, B_x δ₀⟫`; Cauchy–Schwarz and Bessel make the
  series absolutely summable after integration, so sum and integral commute; covariance turns the
  `n`-th term into the `(-n)`-th term of `BA`, evaluated at `x + nα`, and periodicity removes the
  shift.
* `CMS.tau_conj`: `τ(V Q V⁻¹) = τ(Q)` for covariant `V, V⁻¹, Q`.
* `CMS.exists_conj_of_norm_sub_lt_one`: two projections at distance `< 1` are similar,
  `P = V Q V⁻¹` with `V = 1 + (P - Q)(2Q - 1)`.
* `CMS.tau_eq_of_norm_sub_lt_one`: **covariant projection families at uniform distance `< 1` have
  the same trace.** This is the elementary replacement for the K-theoretic statement "nearby
  spectral projections are equivalent, hence have the same trace".
-/

noncomputable section

open scoped ComplexConjugate InnerProductSpace
open MeasureTheory Set Filter Topology AMO L2

namespace CMS

set_option linter.unusedSectionVars false

/-! ### Covariant families -/

/-- The shift `(Su)_n = u_{n+1}` as a linear isometry equivalence of `ℓ²(ℤ)`. -/
def shiftU (α : ℝ) : L2 ℤ ≃ₗᵢ[ℂ] L2 ℤ := Unitary.linearIsometryEquiv (shiftUnitary α 0)

lemma shiftU_apply (α : ℝ) (v : L2 ℤ) (n : ℤ) : shiftU α v n = v (n + 1) := U_apply α 0 v n

lemma shiftU_delta (α : ℝ) (n : ℤ) : shiftU α (delta (n + 1)) = delta n := by
  ext k
  rw [shiftU_apply]
  simp only [delta, lp.single_apply, Pi.single_apply]
  by_cases h : k = n
  · subst h; simp
  · rw [if_neg (by omega), if_neg h]

/-- A covariant family: norm continuous, `1`-periodic and `A_{x+α} S = S A_x`. -/
structure IsCovFam (α : ℝ) (A : ℝ → Op ℤ) : Prop where
  cont : Continuous A
  periodic : Function.Periodic A 1
  cov : ∀ x, Intertwines (shiftU α) (A x) (A (x + α))

/-- The covariant trace `τ(A) = ∫₀¹ ⟪δ₀, A_x δ₀⟫ dx`. -/
def tau (A : ℝ → Op ℤ) : ℂ := ∫ x in (0 : ℝ)..1, ⟪delta 0, A x (delta 0)⟫_ℂ

namespace IsCovFam

variable {α : ℝ} {A B : ℝ → Op ℤ}

lemma bdd (hA : IsCovFam α A) : ∃ M, ∀ x, ‖A x‖ ≤ M := by
  obtain ⟨M, hM⟩ := (hA.periodic.compact_of_continuous one_ne_zero hA.cont).isBounded.exists_norm_le
  exact ⟨M, fun x => hM _ (mem_range_self x)⟩

theorem mul (hA : IsCovFam α A) (hB : IsCovFam α B) : IsCovFam α (fun x => A x * B x) where
  cont := hA.cont.mul hB.cont
  periodic x := by simp only [hA.periodic x, hB.periodic x]
  cov x v := by
    simp only [ContinuousLinearMap.mul_apply]
    rw [hB.cov x v, hA.cov x]

theorem add (hA : IsCovFam α A) (hB : IsCovFam α B) : IsCovFam α (fun x => A x + B x) where
  cont := hA.cont.add hB.cont
  periodic x := by simp only [hA.periodic x, hB.periodic x]
  cov x v := by
    simp only [ContinuousLinearMap.add_apply]
    rw [hB.cov x v, hA.cov x, map_add]

theorem sub (hA : IsCovFam α A) (hB : IsCovFam α B) : IsCovFam α (fun x => A x - B x) where
  cont := hA.cont.sub hB.cont
  periodic x := by simp only [hA.periodic x, hB.periodic x]
  cov x v := by
    simp only [ContinuousLinearMap.sub_apply]
    rw [hB.cov x v, hA.cov x, map_sub]

theorem const_one : IsCovFam α (fun _ => (1 : Op ℤ)) where
  cont := continuous_const
  periodic _ := rfl
  cov _ _ := rfl

/-- Pointwise inverses of a covariant family of units form a covariant family. -/
theorem inverse (hA : IsCovFam α A) (hu : ∀ x, IsUnit (A x)) :
    IsCovFam α (fun x => Ring.inverse (A x)) where
  cont := continuous_iff_continuousAt.2 fun x => by
    have h1 : ContinuousAt Ring.inverse (A x) := by
      have := NormedRing.inverse_continuousAt (hu x).unit
      rwa [IsUnit.unit_spec] at this
    exact h1.comp (f := A) hA.cont.continuousAt
  periodic x := by simp only [hA.periodic x]
  cov x v := by
    have hl : ∀ y w, Ring.inverse (A y) (A y w) = w := fun y w => by
      change (Ring.inverse (A y) * A y) w = w
      rw [Ring.inverse_mul_cancel _ (hu y)]; rfl
    have hr : ∀ y w, A y (Ring.inverse (A y) w) = w := fun y w => by
      change (A y * Ring.inverse (A y)) w = w
      rw [Ring.mul_inverse_cancel _ (hu y)]; rfl
    calc Ring.inverse (A (x + α)) (shiftU α v)
        = Ring.inverse (A (x + α)) (shiftU α (A x (Ring.inverse (A x) v))) := by rw [hr]
      _ = Ring.inverse (A (x + α)) (A (x + α) (shiftU α (Ring.inverse (A x) v))) := by
          rw [hA.cov x]
      _ = shiftU α (Ring.inverse (A x) v) := hl _ _

/-! ### Matrix elements -/

/-- One step of covariance on matrix elements: `⟪δ_{m+1}, A_x δ_{n+1}⟫ = ⟪δ_m, A_{x+α} δ_n⟫`. -/
lemma inner_succ (hA : IsCovFam α A) (x : ℝ) (m n : ℤ) :
    ⟪delta (m + 1), A x (delta (n + 1))⟫_ℂ = ⟪delta m, A (x + α) (delta n)⟫_ℂ := by
  rw [← shiftU_delta α n, hA.cov x, inner_delta_left2, inner_delta_left2, shiftU_apply]

/-- Covariance of matrix elements: `⟪δ_{m+k}, A_x δ_{n+k}⟫ = ⟪δ_m, A_{x+kα} δ_n⟫`. -/
lemma inner_add (hA : IsCovFam α A) (x : ℝ) (m n k : ℤ) :
    ⟪delta (m + k), A x (delta (n + k))⟫_ℂ = ⟪delta m, A (x + k * α) (delta n)⟫_ℂ := by
  induction k using Int.induction_on generalizing x with
  | zero => simp
  | succ j ih =>
    rw [show m + (j + 1) = m + j + 1 by ring, show n + (j + 1) = n + j + 1 by ring,
      hA.inner_succ, ih]
    congr 3; push_cast; ring
  | pred j ih =>
    have h := hA.inner_succ (x - α) (m + (-(j : ℤ) - 1)) (n + (-(j : ℤ) - 1))
    rw [show m + (-(j : ℤ) - 1) + 1 = m + -(j : ℤ) by ring,
      show n + (-(j : ℤ) - 1) + 1 = n + -(j : ℤ) by ring, sub_add_cancel, ih] at h
    rw [← h]
    congr 3; push_cast; ring

lemma continuous_inner (hA : IsCovFam α A) (u v : L2 ℤ) :
    Continuous fun x => ⟪u, A x v⟫_ℂ :=
  continuous_const.inner (hA.cont.clm_apply continuous_const)

end IsCovFam

/-! ### Parseval and the interchange of sum and integral -/

/-- The standard Hilbert basis `(δₙ)` of `ℓ²(ℤ)`. -/
def deltaBasis : HilbertBasis ℤ ℂ (L2 ℤ) := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

lemma deltaBasis_apply (n : ℤ) : deltaBasis n = delta n := by
  rw [← HilbertBasis.repr_symm_single]; rfl

/-- Parseval: `⟪δ₀, A B δ₀⟫ = ∑ₙ ⟪δ₀, A δₙ⟫ ⟪δₙ, B δ₀⟫`. -/
lemma hasSum_inner_mul (A B : Op ℤ) :
    HasSum (fun n : ℤ => ⟪delta 0, A (delta n)⟫_ℂ * ⟪delta n, B (delta 0)⟫_ℂ)
      ⟪delta 0, (A * B) (delta 0)⟫_ℂ := by
  have h := deltaBasis.hasSum_inner_mul_inner (ContinuousLinearMap.adjoint A (delta 0))
    (B (delta 0))
  simp only [deltaBasis_apply, ContinuousLinearMap.adjoint_inner_left] at h
  exact h

/-- Bessel: `∑_{n ∈ F} ‖⟪δₙ, v⟫‖² ≤ ‖v‖²`. -/
lemma sum_sq_le_norm_sq (v : L2 ℤ) (F : Finset ℤ) :
    ∑ n ∈ F, ‖⟪delta n, v⟫_ℂ‖ ^ 2 ≤ ‖v‖ ^ 2 := by
  have h := deltaBasis.orthonormal.sum_inner_products_le (s := F) v
  simpa only [deltaBasis_apply] using h

/-- The `n`-th Parseval term `x ↦ ⟪δ₀, A_x δₙ⟫ ⟪δₙ, B_x δ₀⟫`. -/
def parTerm (A B : ℝ → Op ℤ) (n : ℤ) (x : ℝ) : ℂ :=
  ⟪delta 0, A x (delta n)⟫_ℂ * ⟪delta n, B x (delta 0)⟫_ℂ

lemma continuous_parTerm {α : ℝ} {A B : ℝ → Op ℤ} (hA : IsCovFam α A) (hB : IsCovFam α B)
    (n : ℤ) : Continuous (parTerm A B n) :=
  (hA.continuous_inner _ _).mul (hB.continuous_inner _ _)

/-- `‖⟪δ₀, A δₙ⟫‖ = ‖⟪δₙ, A* δ₀⟫‖`. -/
lemma norm_inner_delta_left (A : Op ℤ) (n : ℤ) :
    ‖⟪delta 0, A (delta n)⟫_ℂ‖ = ‖⟪delta n, ContinuousLinearMap.adjoint A (delta 0)⟫_ℂ‖ := by
  rw [← ContinuousLinearMap.adjoint_inner_left, norm_inner_symm]

/-- Pointwise bound `‖aₙbₙ‖ ≤ (‖aₙ‖² + ‖bₙ‖²)/2`. -/
lemma norm_parTerm_le (A B : ℝ → Op ℤ) (n : ℤ) (x : ℝ) :
    ‖parTerm A B n x‖ ≤
      (‖⟪delta 0, A x (delta n)⟫_ℂ‖ ^ 2 + ‖⟪delta n, B x (delta 0)⟫_ℂ‖ ^ 2) / 2 := by
  rw [parTerm, norm_mul]
  nlinarith [sq_nonneg (‖⟪delta 0, A x (delta n)⟫_ℂ‖ - ‖⟪delta n, B x (delta 0)⟫_ℂ‖)]

/-- Summability of `n ↦ ∫₀¹ f_n` for nonnegative continuous `f_n` whose finite sums are bounded
by `M` pointwise. -/
lemma summable_integral_of_sum_le {f : ℤ → ℝ → ℝ} (hc : ∀ n, Continuous (f n))
    (h0 : ∀ n x, 0 ≤ f n x) {M : ℝ} (hM : ∀ (F : Finset ℤ) x, ∑ n ∈ F, f n x ≤ M) :
    Summable fun n => ∫ x in Ioc (0 : ℝ) 1, f n x := by
  refine summable_of_sum_le (c := M) (fun n => setIntegral_nonneg measurableSet_Ioc
    fun x _ => h0 n x) fun F => ?_
  rw [← integral_finsetSum F fun n _ => (hc n).integrableOn_Ioc]
  calc ∫ x in Ioc (0 : ℝ) 1, ∑ n ∈ F, f n x ≤ ∫ _ in Ioc (0 : ℝ) 1, M :=
        setIntegral_mono_on (continuous_finsetSum F fun n _ => hc n).integrableOn_Ioc
          (continuous_const.integrableOn_Ioc) measurableSet_Ioc fun x _ => hM F x
    _ = M := by simp

/-- **Sum and integral commute**: `τ(AB) = ∑ₙ ∫₀¹ ⟪δ₀, A_x δₙ⟫⟪δₙ, B_x δ₀⟫ dx`. -/
theorem tau_mul_eq_tsum {α : ℝ} {A B : ℝ → Op ℤ} (hA : IsCovFam α A) (hB : IsCovFam α B) :
    tau (fun x => A x * B x) = ∑' n, ∫ x in (0 : ℝ)..1, parTerm A B n x := by
  obtain ⟨MA, hMA⟩ := hA.bdd
  obtain ⟨MB, hMB⟩ := hB.bdd
  have hpt : ∀ x, ⟪delta 0, (A x * B x) (delta 0)⟫_ℂ = ∑' n, parTerm A B n x := fun x =>
    (hasSum_inner_mul (A x) (B x)).tsum_eq.symm
  have hcA : ∀ n, Continuous fun x => ‖⟪delta 0, A x (delta n)⟫_ℂ‖ ^ 2 := fun n =>
    ((hA.continuous_inner _ _).norm).pow 2
  have hcB : ∀ n, Continuous fun x => ‖⟪delta n, B x (delta 0)⟫_ℂ‖ ^ 2 := fun n =>
    ((hB.continuous_inner _ _).norm).pow 2
  unfold tau
  simp only [intervalIntegral.integral_of_le zero_le_one, hpt]
  refine (integral_tsum_of_summable_integral_norm
    (fun n => (continuous_parTerm hA hB n).integrableOn_Ioc) ?_).symm
  -- summability of the integrated norms
  have hsA := summable_integral_of_sum_le hcA (fun _ _ => by positivity)
    (M := MA ^ 2) fun F x => by
      simp only [norm_inner_delta_left]
      refine (sum_sq_le_norm_sq _ F).trans ?_
      have h1 : ‖ContinuousLinearMap.adjoint (A x) (delta 0)‖ ≤ MA := by
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        rw [norm_delta, mul_one, LinearIsometryEquiv.norm_map]
        exact hMA x
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  have hsB := summable_integral_of_sum_le hcB (fun _ _ => by positivity)
    (M := MB ^ 2) fun F x => by
      refine (sum_sq_le_norm_sq _ F).trans ?_
      have h1 : ‖B x (delta 0)‖ ≤ MB := by
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        rw [norm_delta, mul_one]
        exact hMB x
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  refine Summable.of_nonneg_of_le (fun n => setIntegral_nonneg measurableSet_Ioc
    fun x _ => norm_nonneg _) (fun n => ?_) ((hsA.add hsB).div_const 2)
  rw [← integral_add (hcA n).integrableOn_Ioc (hcB n).integrableOn_Ioc, ← integral_div]
  exact setIntegral_mono_on (continuous_parTerm hA hB n).norm.integrableOn_Ioc
    (((hcA n).add (hcB n)).div_const 2).integrableOn_Ioc
    measurableSet_Ioc fun x _ => norm_parTerm_le A B n x

/-- Covariance moves the `n`-th term of `AB` to the `(-n)`-th term of `BA`. -/
lemma integral_parTerm_swap {α : ℝ} {A B : ℝ → Op ℤ} (hA : IsCovFam α A) (hB : IsCovFam α B)
    (n : ℤ) : ∫ x in (0 : ℝ)..1, parTerm A B n x = ∫ x in (0 : ℝ)..1, parTerm B A (-n) x := by
  have hpt : ∀ x, parTerm A B n x = parTerm B A (-n) (x + n * α) := by
    intro x
    have h1 := hA.inner_add x (-n) 0 n
    have h2 := hB.inner_add x 0 (-n) n
    simp only [neg_add_cancel, zero_add] at h1 h2
    rw [parTerm, parTerm, h1, h2, mul_comm]
  simp only [hpt]
  have hper : Function.Periodic (parTerm B A (-n)) 1 := fun x => by
    simp only [parTerm, hA.periodic x, hB.periodic x]
  rw [intervalIntegral.integral_comp_add_right, zero_add, add_comm 1,
    hper.intervalIntegral_add_eq (n * α) 0, zero_add]

/-- **Trace property** of the covariant trace: `τ(AB) = τ(BA)`. -/
theorem tau_mul_comm {α : ℝ} {A B : ℝ → Op ℤ} (hA : IsCovFam α A) (hB : IsCovFam α B) :
    tau (fun x => A x * B x) = tau (fun x => B x * A x) := by
  rw [tau_mul_eq_tsum hA hB, tau_mul_eq_tsum hB hA]
  simp only [integral_parTerm_swap hA hB]
  exact (Equiv.neg ℤ).tsum_eq (fun m => ∫ x in (0 : ℝ)..1, parTerm B A m x)

/-- Similar covariant families have the same trace: if `W_x V_x = 1`, then
`τ(V Q W) = τ(Q)`. -/
theorem tau_conj {α : ℝ} {V W Q : ℝ → Op ℤ} (hV : IsCovFam α V) (hW : IsCovFam α W)
    (hQ : IsCovFam α Q) (hWV : ∀ x, W x * V x = 1) :
    tau (fun x => V x * Q x * W x) = tau Q := by
  rw [tau_mul_comm (hV.mul hQ) hW]
  congr 1
  funext x
  rw [← mul_assoc, hWV, one_mul]

/-! ### Nearby projections -/

/-- A self-adjoint involution has norm `≤ 1`. -/
lemma norm_le_one_of_involution {S : Op ℤ} (hS : IsSelfAdjoint S) (h2 : S * S = 1) : ‖S‖ ≤ 1 := by
  have h := CStarRing.norm_star_mul_self (x := S)
  rw [hS.star_eq, h2] at h
  have h1 : ‖(1 : Op ℤ)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  nlinarith [norm_nonneg S]

/-- **Nearby projections are similar.** If `P, Q` are projections with `‖P - Q‖ < 1`, then
`V = 1 + (P - Q)(2Q - 1)` is invertible and `P V = V Q` (both equal `P Q`). -/
theorem exists_conj_of_norm_sub_lt_one {P Q : Op ℤ} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) (h : ‖P - Q‖ < 1) :
    IsUnit (1 + (P - Q) * (Q + Q - 1)) ∧
      P * (1 + (P - Q) * (Q + Q - 1)) = (1 + (P - Q) * (Q + Q - 1)) * Q := by
  have hPP : P * P = P := hP.isIdempotentElem.eq
  have hQQ : Q * Q = Q := hQ.isIdempotentElem.eq
  have hPP' : ∀ X : Op ℤ, P * (P * X) = P * X := fun X => by rw [← mul_assoc, hPP]
  have hQQ' : ∀ X : Op ℤ, Q * (Q * X) = Q * X := fun X => by rw [← mul_assoc, hQQ]
  constructor
  · have hS : ‖(Q + Q - 1 : Op ℤ)‖ ≤ 1 := by
      refine norm_le_one_of_involution ?_ ?_
      · have hQs : star Q = Q := hQ.isSelfAdjoint.star_eq
        show star (Q + Q - 1) = Q + Q - 1
        simp [hQs]
      · simp only [add_mul, mul_add, sub_mul, mul_sub, mul_one, one_mul, hQQ]
        abel
    have ht : ‖(Q - P) * (Q + Q - 1)‖ < 1 := by
      calc ‖(Q - P) * (Q + Q - 1)‖ ≤ ‖Q - P‖ * ‖(Q + Q - 1 : Op ℤ)‖ := norm_mul_le _ _
        _ ≤ ‖Q - P‖ * 1 := by gcongr
        _ < 1 := by rw [mul_one, norm_sub_rev]; exact h
    have := (Units.oneSub _ ht).isUnit
    rw [Units.val_oneSub] at this
    convert this using 1
    have e : (P - Q) * (Q + Q - 1) = -((Q - P) * (Q + Q - 1)) := by rw [← neg_mul, neg_sub]
    rw [e, ← sub_eq_add_neg]
  · have e1 : P * (1 + (P - Q) * (Q + Q - 1)) = P * Q := by
      simp only [add_mul, mul_add, sub_mul, mul_sub, mul_one, one_mul, mul_assoc, hPP, hQQ,
        hPP', hQQ']
      abel
    have e2 : (1 + (P - Q) * (Q + Q - 1)) * Q = P * Q := by
      simp only [add_mul, mul_add, sub_mul, mul_sub, mul_one, one_mul, mul_assoc, hPP, hQQ,
        hPP', hQQ']
      abel
    rw [e1, e2]

/-- **Covariant projection families at uniform distance `< 1` have the same trace.** -/
theorem tau_eq_of_norm_sub_lt_one {α : ℝ} {P Q : ℝ → Op ℤ} (hPc : IsCovFam α P)
    (hQc : IsCovFam α Q) (hP : ∀ x, IsStarProjection (P x)) (hQ : ∀ x, IsStarProjection (Q x))
    (h : ∀ x, ‖P x - Q x‖ < 1) : tau P = tau Q := by
  set V : ℝ → Op ℤ := fun x => 1 + (P x - Q x) * (Q x + Q x - 1) with hVdef
  have hV : IsCovFam α V :=
    IsCovFam.const_one.add ((hPc.sub hQc).mul ((hQc.add hQc).sub IsCovFam.const_one))
  have hu : ∀ x, IsUnit (V x) := fun x => (exists_conj_of_norm_sub_lt_one (hP x) (hQ x) (h x)).1
  have hW := hV.inverse hu
  have hconj : ∀ x, P x = V x * Q x * Ring.inverse (V x) := by
    intro x
    have h1 := (exists_conj_of_norm_sub_lt_one (hP x) (hQ x) (h x)).2
    rw [← h1, mul_assoc, Ring.mul_inverse_cancel _ (hu x), mul_one]
  have : P = fun x => V x * Q x * Ring.inverse (V x) := funext hconj
  rw [this]
  exact tau_conj hV hW hQc fun x => Ring.inverse_mul_cancel _ (hu x)

end CMS
