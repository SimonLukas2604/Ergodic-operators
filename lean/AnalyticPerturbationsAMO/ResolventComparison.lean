/-
# Weighted resolvent comparison  (paper Lemma 3.2, `t-lem:weight`)

Let `J = J^*` and `0 < m ≤ W ≤ M` in a unital C⋆-algebra.  Then `J - isW` is invertible for
every `s ≠ 0`, with the exact identity (no commutativity needed)
  `Im (J - isW)^{-1} = s (J W^{-1} J + s² W)^{-1}`,
and there is `C = C(m, M)` such that for every `s > 0`
  `C^{-1} Im (J - is)^{-1} ≤ Im (J - isW)^{-1} ≤ C Im (J - is)^{-1}`.
Everything here is proved.
-/
import Mathlib

noncomputable section

open Complex

namespace AMO

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The imaginary part `Im X = (X - X^*) / (2i)`. -/
def imPart (X : A) : A := (2 * I)⁻¹ • (X - star X)

omit [PartialOrder A] [StarOrderedRing A] in
lemma star_units_inv_of_isSelfAdjoint (P : Aˣ) (hP : IsSelfAdjoint (P : A)) :
    star (↑P⁻¹ : A) = ↑P⁻¹ := by
  calc star (↑P⁻¹ : A) = star (↑P⁻¹ : A) * ((P : A) * ↑P⁻¹) := by simp
    _ = star ((P : A) * ↑P⁻¹) * ↑P⁻¹ := by
        rw [star_mul, hP.star_eq, mul_assoc]
    _ = ↑P⁻¹ := by simp

omit [PartialOrder A] [StarOrderedRing A] in
/-- **Exact identity.**  If `P = J W^{-1} J + s² W` is invertible, then `J - isW` is
invertible and `Im (J - isW)^{-1} = s P^{-1}`. -/
theorem imPart_inverse_eq {J : A} (hJ : IsSelfAdjoint J) (W : Aˣ) (hW : IsSelfAdjoint (W : A))
    (s : ℝ) (P : Aˣ) (hP : (P : A) = J * ↑W⁻¹ * J + ((s : ℂ) ^ 2) • (W : A)) :
    IsUnit (J - ((s : ℂ) * I) • (W : A)) ∧
      imPart (Ring.inverse (J - ((s : ℂ) * I) • (W : A))) = (s : ℂ) • (↑P⁻¹ : A) := by
  set a : ℂ := (s : ℂ) * I with ha
  have haa : a * a = -((s : ℂ) ^ 2) := by
    rw [ha]; ring_nf; rw [I_sq]; ring
  have hWw : (W : A) * ↑W⁻¹ = 1 := W.mul_inv
  have hwW : (↑W⁻¹ : A) * W = 1 := W.inv_mul
  -- `X W⁻¹ Y = P = Y W⁻¹ X`
  have hXY : (J - a • (W : A)) * ↑W⁻¹ * (J + a • (W : A)) = P := by
    calc (J - a • (W : A)) * ↑W⁻¹ * (J + a • (W : A))
        = (J * ↑W⁻¹ - a • 1) * (J + a • (W : A)) := by rw [sub_mul, smul_mul_assoc, hWw]
      _ = J * ↑W⁻¹ * J + a • J - a • J - (a * a) • (W : A) := by
        rw [sub_mul, mul_add, mul_add, smul_mul_assoc, one_mul, mul_smul_comm,
          mul_assoc J (↑W⁻¹ : A) (W : A), hwW, mul_one, smul_mul_assoc, one_mul, smul_smul]
        abel
      _ = P := by rw [hP, haa, neg_smul]; abel
  have hYX : (J + a • (W : A)) * ↑W⁻¹ * (J - a • (W : A)) = P := by
    calc (J + a • (W : A)) * ↑W⁻¹ * (J - a • (W : A))
        = (J * ↑W⁻¹ + a • 1) * (J - a • (W : A)) := by rw [add_mul, smul_mul_assoc, hWw]
      _ = J * ↑W⁻¹ * J - a • J + a • J - (a * a) • (W : A) := by
        rw [add_mul, mul_sub, mul_sub, smul_mul_assoc, one_mul, mul_smul_comm,
          mul_assoc J (↑W⁻¹ : A) (W : A), hwW, mul_one, smul_mul_assoc, one_mul, smul_smul]
        abel
      _ = P := by rw [hP, haa, neg_smul]; abel
  clear_value a
  generalize hX : J - a • (W : A) = X at hXY hYX ⊢
  generalize hY : J + a • (W : A) = Y at hXY hYX
  set Rr : A := ↑W⁻¹ * Y * ↑P⁻¹
  set Ll : A := ↑P⁻¹ * Y * ↑W⁻¹
  have hright : X * Rr = 1 := by
    have : X * Rr = (X * ↑W⁻¹ * Y) * ↑P⁻¹ := by simp only [Rr, mul_assoc]
    rw [this, hXY, P.mul_inv]
  have hleft : Ll * X = 1 := by
    have : Ll * X = ↑P⁻¹ * (Y * ↑W⁻¹ * X) := by simp only [Ll, mul_assoc]
    rw [this, hYX, P.inv_mul]
  have hLR : Ll = Rr := by
    calc Ll = Ll * (X * Rr) := by rw [hright, mul_one]
      _ = (Ll * X) * Rr := (mul_assoc Ll X Rr).symm
      _ = Rr := by rw [hleft, one_mul]
  let Xu : Aˣ := ⟨X, Rr, hright, hLR ▸ hleft⟩
  have hXu : IsUnit X := ⟨Xu, rfl⟩
  refine ⟨hXu, ?_⟩
  have hinv : Ring.inverse X = Rr := by
    rw [show X = (Xu : A) from rfl, Ring.inverse_unit]
    rfl
  -- adjoints
  have hPsa : IsSelfAdjoint (P : A) := by
    rw [hP]
    refine IsSelfAdjoint.add ?_ ?_
    · have hw : IsSelfAdjoint (↑W⁻¹ : A) := star_units_inv_of_isSelfAdjoint W hW
      unfold IsSelfAdjoint
      rw [star_mul, star_mul, hJ.star_eq, hw.star_eq, mul_assoc]
    · unfold IsSelfAdjoint
      rw [star_smul, hW.star_eq]
      congr 1
      simp
  have hstarY : star Y = X := by
    rw [← hY, ← hX, star_add, hJ.star_eq, star_smul, hW.star_eq, ha]
    simp [sub_eq_add_neg]
  have hstarLl : star Ll = ↑W⁻¹ * X * ↑P⁻¹ := by
    simp only [Ll, star_mul, star_units_inv_of_isSelfAdjoint W hW,
      star_units_inv_of_isSelfAdjoint P hPsa, hstarY, mul_assoc]
  unfold imPart
  rw [hinv, ← hLR]
  conv_lhs => rw [hstarLl]
  rw [hLR]
  simp only [Rr]
  have hdiff : (↑W⁻¹ : A) * Y * ↑P⁻¹ - ↑W⁻¹ * X * ↑P⁻¹ = (2 * a) • (↑P⁻¹ : A) := by
    rw [← sub_mul, ← mul_sub, ← hY, ← hX]
    rw [show J + a • (W : A) - (J - a • (W : A)) = (2 * a) • (W : A) by
      rw [two_mul, add_smul]; abel]
    rw [mul_smul_comm, hwW, smul_mul_assoc, one_mul]
  rw [hdiff, smul_smul, ha]
  congr 1
  field_simp

/-! ### The order comparison -/

/-- `c • P` as a unit. -/
def smulUnit (c : ℝ) (hc : c ≠ 0) (P : Aˣ) : Aˣ where
  val := c • (P : A)
  inv := c⁻¹ • (↑P⁻¹ : A)
  val_inv := by rw [smul_mul_smul_comm, mul_inv_cancel₀ hc, P.mul_inv, one_smul]
  inv_val := by rw [smul_mul_smul_comm, inv_mul_cancel₀ hc, P.inv_mul, one_smul]

lemma isStrictlyPositive_unit_inv_nonneg (P : Aˣ) (hP : 0 ≤ (P : A)) : 0 ≤ (↑P⁻¹ : A) :=
  CFC.inv_nonneg_of_nonneg P hP

omit [PartialOrder A] [StarOrderedRing A] in
lemma algebraMap_unit_inv {r : ℝ} (hr : r ≠ 0) (U : Aˣ) (hU : (U : A) = algebraMap ℝ A r) :
    (↑U⁻¹ : A) = algebraMap ℝ A r⁻¹ := by
  apply Units.inv_eq_of_mul_eq_one_right
  rw [hU, ← map_mul, mul_inv_cancel₀ hr, map_one]

/-- `M^{-1} J² ≤ J W^{-1} J ≤ m^{-1} J²` for `0 < m ≤ W ≤ M`. -/
lemma conj_inv_bounds {J : A} (hJ : IsSelfAdjoint J) (W : Aˣ) {m M : ℝ} (hm : 0 < m)
    (hmM : m ≤ M) (hmW : algebraMap ℝ A m ≤ W) (hWM : (W : A) ≤ algebraMap ℝ A M) :
    M⁻¹ • (J * J) ≤ J * ↑W⁻¹ * J ∧ J * ↑W⁻¹ * J ≤ m⁻¹ • (J * J) := by
  have hM : 0 < M := hm.trans_le hmM
  have hW0 : 0 ≤ (W : A) := (isStrictlyPositive_algebraMap hm).nonneg.trans hmW
  have hconj : ∀ r : ℝ, J * algebraMap ℝ A r * J = r • (J * J) := fun r => by
    rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc]
  let Mu : Aˣ := (isStrictlyPositive_algebraMap (A := A) hM).isUnit.unit
  let mu : Aˣ := (isStrictlyPositive_algebraMap (A := A) hm).isUnit.unit
  have hMu : (↑Mu⁻¹ : A) = algebraMap ℝ A M⁻¹ := algebraMap_unit_inv hM.ne' Mu rfl
  have hmu : (↑mu⁻¹ : A) = algebraMap ℝ A m⁻¹ := algebraMap_unit_inv hm.ne' mu rfl
  have h1 : (↑Mu⁻¹ : A) ≤ ↑W⁻¹ := CStarAlgebra.inv_le_inv hW0 hWM
  have h2 : (↑W⁻¹ : A) ≤ ↑mu⁻¹ :=
    CStarAlgebra.inv_le_inv (isStrictlyPositive_algebraMap hm).nonneg hmW
  rw [hMu] at h1
  rw [hmu] at h2
  constructor
  · rw [← hconj]; exact hJ.conjugate_le_conjugate h1
  · rw [← hconj]; exact hJ.conjugate_le_conjugate h2

/-- **Lemma 3.2 (weighted resolvent comparison).**  For `0 < m ≤ M` there is `C = C(m, M) > 0`
such that, whenever `J = J^*` and `m ≤ W ≤ M`, for every `s > 0` both `J - isW` and `J - is`
are invertible and, as positive quadratic forms,
`C^{-1} Im (J - is)^{-1} ≤ Im (J - isW)^{-1} ≤ C Im (J - is)^{-1}`. -/
theorem resolvent_comparison {m M : ℝ} (hm : 0 < m) (hmM : m ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (J W : A), IsSelfAdjoint J → algebraMap ℝ A m ≤ W →
      W ≤ algebraMap ℝ A M → ∀ s : ℝ, 0 < s →
        IsUnit (J - ((s : ℂ) * I) • W) ∧ IsUnit (J - ((s : ℂ) * I) • (1 : A)) ∧
        C⁻¹ • imPart (Ring.inverse (J - ((s : ℂ) * I) • (1 : A))) ≤
          imPart (Ring.inverse (J - ((s : ℂ) * I) • W)) ∧
        imPart (Ring.inverse (J - ((s : ℂ) * I) • W)) ≤
          C • imPart (Ring.inverse (J - ((s : ℂ) * I) • (1 : A))) := by
  have hM : 0 < M := hm.trans_le hmM
  set cp : ℝ := max m⁻¹ M with hcp
  set cm : ℝ := min M⁻¹ m with hcm
  have hcm0 : 0 < cm := lt_min (inv_pos.2 hM) hm
  have hcp0 : 0 < cp := lt_max_of_lt_right hM
  refine ⟨max cp cm⁻¹, lt_max_of_lt_left hcp0, ?_⟩
  intro J W hJ hmW hWM s hs
  have hmsp := isStrictlyPositive_algebraMap (A := A) hm
  have hW0 : 0 ≤ W := hmsp.nonneg.trans hmW
  let Wu : Aˣ := (CStarAlgebra.isUnit_of_le (algebraMap ℝ A m) hmW hmsp).unit
  have hWu : (Wu : A) = W := rfl
  have hWsa : IsSelfAdjoint (Wu : A) := IsSelfAdjoint.of_nonneg hW0
  obtain ⟨hlo, hhi⟩ := conj_inv_bounds hJ Wu hm hmM hmW hWM
  have hJJ : 0 ≤ J * J := by
    simpa [hJ.star_eq] using star_mul_self_nonneg J
  have h10 : (0 : A) ≤ 1 := zero_le_one
  set P1 : A := J * J + (s ^ 2) • (1 : A) with hP1
  set PW : A := J * ↑Wu⁻¹ * J + (s ^ 2) • W with hPW
  have hs2 : 0 < s ^ 2 := by positivity
  -- `cm P1 ≤ PW ≤ cp P1`
  have hmW' : m • (1 : A) ≤ W := by rwa [← Algebra.algebraMap_eq_smul_one]
  have hWM' : W ≤ M • (1 : A) := by rwa [← Algebra.algebraMap_eq_smul_one]
  have hlower : cm • P1 ≤ PW := by
    rw [hP1, hPW, smul_add, smul_comm cm (s ^ 2)]
    refine add_le_add ?_ ?_
    · exact (smul_le_smul_of_nonneg_right (min_le_left _ _) hJJ).trans hlo
    · refine smul_le_smul_of_nonneg_left ?_ hs2.le
      exact (smul_le_smul_of_nonneg_right (min_le_right _ _) h10).trans hmW'
  have hupper : PW ≤ cp • P1 := by
    rw [hP1, hPW, smul_add, smul_comm cp (s ^ 2)]
    refine add_le_add ?_ ?_
    · exact hhi.trans (smul_le_smul_of_nonneg_right (le_max_left _ _) hJJ)
    · refine smul_le_smul_of_nonneg_left ?_ hs2.le
      exact hWM'.trans (smul_le_smul_of_nonneg_right (le_max_right _ _) h10)
  -- strict positivity and units
  have hP1sp : IsStrictlyPositive P1 := by
    rw [hP1, ← Algebra.algebraMap_eq_smul_one]
    exact IsStrictlyPositive.nonneg_add hJJ (isStrictlyPositive_algebraMap hs2)
  have hcmP1sp : IsStrictlyPositive (cm • P1) := by
    rw [hP1, smul_add, smul_smul, ← Algebra.algebraMap_eq_smul_one]
    exact IsStrictlyPositive.nonneg_add (smul_nonneg hcm0.le hJJ)
      (isStrictlyPositive_algebraMap (mul_pos hcm0 hs2))
  have hPWsp : IsStrictlyPositive PW := hcmP1sp.of_le hlower
  let P1u : Aˣ := hP1sp.isUnit.unit
  let PWu : Aˣ := hPWsp.isUnit.unit
  -- the exact identities
  have hPWc : (PWu : A) = J * ↑Wu⁻¹ * J + ((s : ℂ) ^ 2) • (Wu : A) := by
    show PW = _
    rw [hPW, ← Complex.coe_smul]
    push_cast
    rfl
  have hP1c : (P1u : A) = J * ↑(1 : Aˣ)⁻¹ * J + ((s : ℂ) ^ 2) • ((1 : Aˣ) : A) := by
    show P1 = _
    rw [hP1, ← Complex.coe_smul]
    push_cast
    simp
  obtain ⟨hXW, hImW⟩ := imPart_inverse_eq hJ Wu hWsa s PWu hPWc
  obtain ⟨hX1, hIm1⟩ := imPart_inverse_eq hJ (1 : Aˣ) (by simp [IsSelfAdjoint]) s P1u hP1c
  simp only [Units.val_one] at hX1 hIm1
  rw [hWu] at hXW hImW
  -- invert the comparisons
  have hcm_inv : (↑PWu⁻¹ : A) ≤ cm⁻¹ • ↑P1u⁻¹ :=
    CStarAlgebra.inv_le_inv (a := smulUnit cm hcm0.ne' P1u) hcmP1sp.nonneg hlower
  have hcp_inv : cp⁻¹ • (↑P1u⁻¹ : A) ≤ ↑PWu⁻¹ :=
    CStarAlgebra.inv_le_inv (b := smulUnit cp hcp0.ne' P1u) hPWsp.nonneg hupper
  have hP1inv0 : 0 ≤ (↑P1u⁻¹ : A) := CFC.inv_nonneg_of_nonneg P1u hP1sp.nonneg
  refine ⟨hXW, hX1, ?_, ?_⟩
  all_goals rw [hImW, hIm1, Complex.coe_smul, Complex.coe_smul]
  · rw [smul_comm _ s]
    refine smul_le_smul_of_nonneg_left ?_ hs.le
    refine le_trans (smul_le_smul_of_nonneg_right ?_ hP1inv0) hcp_inv
    exact inv_anti₀ hcp0 (le_max_left _ _)
  · rw [smul_comm (max cp cm⁻¹) s]
    refine smul_le_smul_of_nonneg_left ?_ hs.le
    exact hcm_inv.trans (smul_le_smul_of_nonneg_right (le_max_right _ _) hP1inv0)

end AMO
