/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §2.2.3  Half-line operators  (book pp. 148–152)

We realize the half-line operators through the *decoupled* operator
`H₊ ⊕ H₋ = H - ⟨δ₁, ·⟩ δ₀ - ⟨δ₀, ·⟩ δ₁` on `ℓ²(ℤ)` (`DF.schrDec`, cf. the proof of
Theorem 2.2.15): it acts as the Dirichlet half-line operator (2.2.43) on `ℓ²(ℕ) = ℓ²({1,2,…})`
and as `H₋` on `ℓ²(ℤ₋)`.  In particular the half-line `m`-function is
`m(z) = ⟨δ₁, (H₊ ⊕ H₋ - z)⁻¹ δ₁⟩` (`DF.mHalf`), and the spectral measure of `(H₊, δ₁)` is
the spectral measure of `δ₁` for the decoupled operator.

## Main results
* `DF.schrDec_apply`, `DF.isSelfAdjoint_schrDec`.
* **Proposition 2.2.12**: `DF.mHalf_eq_integral` ((2.2.45), `m` is the Stieltjes transform of
  the spectral measure) and `DF.mHalf_eq_mPlus` ((2.2.46), `m = m₊`).
* **Theorem 2.2.13** (coefficient stripping): `DF.mPlus_stripping` and `DF.mHalf_stripping`:
  `m(z) = 1 / (V(1) - z - m₁(z))` (2.2.52).

## Not formalized
Proposition 2.2.11 (contour integral formula), Proposition 2.2.14 (continuity of `m` in `V`),
Theorem 2.2.15 (essential spectrum; this would need Weyl's theorem on finite-rank
perturbations), and the general boundary conditions of Definition 2.2.16.
-/
import DamanikFillman.Ch2.Green

noncomputable section

open scoped InnerProductSpace ComplexConjugate
open L2 MeasureTheory

namespace DF

variable {V : ℤ → ℝ} {z : ℂ}

/-- The decoupled operator `H₊ ⊕ H₋ = H - ⟨δ₁, ·⟩ δ₀ - ⟨δ₀, ·⟩ δ₁`. -/
def schrDec (V : ℤ → ℝ) : Op :=
  schr V - (innerSL ℂ (dlt 1)).smulRight (dlt 0) - (innerSL ℂ (dlt 0)).smulRight (dlt 1)

lemma schrDec_apply (hV : BddPot V) (ψ : L2 ℤ) (n : ℤ) :
    schrDec V ψ n = ψ (n + 1) + ψ (n - 1) + (V n : ℂ) * ψ n -
      (if n = 0 then ψ 1 else 0) - (if n = 1 then ψ 0 else 0) := by
  simp only [schrDec, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, inner_dlt, lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, schr_apply hV, dlt_apply]
  split_ifs <;> ring

theorem isSelfAdjoint_schrDec (hV : BddPot V) : IsSelfAdjoint (schrDec V) := by
  have hH := isSelfAdjoint_schr hV
  have hR : IsSelfAdjoint ((innerSL ℂ (dlt 1)).smulRight (dlt 0) +
      (innerSL ℂ (dlt 0)).smulRight (dlt 1)) := by
    rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
    intro x y
    simp only [ContinuousLinearMap.coe_add, LinearMap.add_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_add_left, inner_add_right,
      inner_smul_left, inner_smul_right, inner_dlt]
    have r0 : ⟪x, dlt 0⟫_ℂ = conj (x 0) := by rw [← inner_conj_symm, inner_dlt]
    have r1 : ⟪x, dlt 1⟫_ℂ = conj (x 1) := by rw [← inner_conj_symm, inner_dlt]
    rw [r0, r1]
    ring
  have : schrDec V = schr V - ((innerSL ℂ (dlt 1)).smulRight (dlt 0) +
      (innerSL ℂ (dlt 0)).smulRight (dlt 1)) := by
    rw [schrDec]; abel
  rw [this]
  exact hH.sub hR

/-- The half-line Weyl–Titchmarsh function `m(z) = ⟨δ₁, (H₊ - z)⁻¹ δ₁⟩` (2.2.5). -/
def mHalf (V : ℤ → ℝ) (z : ℂ) : ℂ := ⟪dlt 1, res (schrDec V) z (dlt 1)⟫_ℂ

/-- **Proposition 2.2.12**, (2.2.45): `m(z) = ∫ dμ(E) / (E - z)`, `μ` the spectral measure of
`(H₊, δ₁)`. -/
theorem mHalf_eq_integral (hV : BddPot V) (hz : z.im ≠ 0) :
    mHalf V z = ∫ x : ℝ, ((x : ℂ) - z)⁻¹ ∂(spectralMeasure (schrDec V) (isSelfAdjoint_schrDec hV)
      (dlt 1)) :=
  inner_resolvent_eq_integral (schrDec V) (isSelfAdjoint_schrDec hV) (dlt 1) hz

lemma mem_resolventSet_dec (hV : BddPot V) (hz : z.im ≠ 0) :
    z ∈ resolventSet ℂ (schrDec V) := by
  rw [mem_resolventSet_iff_notMem]
  intro h
  have := (isSelfAdjoint_schrDec hV).mem_spectrum_eq_re h
  apply hz; rw [this]; simp

/-- **Proposition 2.2.12**, (2.2.46): the half-line `m`-function coincides with the whole-line
`m₊` of (2.2.26). -/
theorem mHalf_eq_mPlus (hV : BddPot V) (hz : z.im ≠ 0) : mHalf V z = mPlus V z := by
  have hzr := mem_resolventSet_dec hV hz
  set ψ := res (schrDec V) z (dlt 1)
  -- `(H₊ ⊕ H₋ - z) ψ = δ₁`
  have heq : ∀ n : ℤ, ψ (n + 1) + ψ (n - 1) + (V n : ℂ) * ψ n -
      (if n = 0 then ψ 1 else 0) - (if n = 1 then ψ 0 else 0) - z * ψ n =
        if n = 1 then 1 else 0 := by
    intro n
    have h := congrArg (fun T : Op => T (dlt 1)) (sub_mul_res hzr)
    simp only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.one_apply] at h
    have h' := congrArg (fun f : L2 ℤ => f n) h
    simp only [lp.coeFn_sub, Pi.sub_apply, schrDec_apply hV, dlt_apply] at h'
    rw [show (algebraMap ℂ Op z) ψ = z • ψ by simp [Algebra.algebraMap_eq_smul_one]] at h'
    simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] at h'
    rw [← h']
  set w : ℤ → ℂ := fun n => if n = 0 then -1 else ψ n
  have hw : ∀ n, 0 < n → w (n - 1) + w (n + 1) + (V n : ℂ) * w n = z * w n := by
    intro n hn
    have h := heq n
    rw [if_neg (show n ≠ 0 by omega)] at h
    simp only [w]
    rw [if_neg (show n ≠ 0 by omega), if_neg (show n + 1 ≠ 0 by omega)]
    by_cases h1 : n = 1
    · subst h1
      rw [if_pos rfl, if_pos rfl] at h
      rw [show (1 : ℤ) + 1 = 2 by norm_num, show (1 : ℤ) - 1 = 0 by norm_num] at h
      norm_num
      linear_combination h
    · rw [if_neg h1, if_neg h1] at h
      rw [if_neg (show n - 1 ≠ 0 by omega)]
      linear_combination h
  set up := solAt V z 0 (-1) (ψ 1)
  have hup : IsSolution V z up := isSolution_solAt _ _ _
  have hagree : ∀ n, 0 ≤ n → up n = w n :=
    agree_up hw hup (by simp [up, w]) (by
      have := solAt_succ (V := V) (z := z) 0 (-1) (ψ 1)
      simp only [zero_add] at this
      simp [up, w, this])
  have hsq : SqSumTop up := by
    rw [sqSumTop_iff_of_eventually (N := 1) (v := fun n => ψ n) (fun n hn => by
      rw [hagree n (by omega)]; simp only [w]; rw [if_neg (by omega)])]
    exact sqSumTop_of_memℓp ψ.2
  have hne : up ≠ 0 := by
    intro h; have := congrFun h 0; simp [up] at this
  obtain ⟨-, hm, -⟩ := mPlus_eq hz hup hne hsq
  rw [hm, hagree 0 le_rfl, hagree 1 (by norm_num)]
  simp only [w, if_pos rfl, if_neg one_ne_zero]
  rw [mHalf, inner_dlt]
  field_simp
  try rfl

/-- **Theorem 2.2.13** (coefficient stripping), whole-line form:
`m₊(z) = 1 / (V(1) - z - m₊⁽¹⁾(z))` where `m₊⁽¹⁾` belongs to the shifted potential
`V₁(n) = V(n+1)` (2.2.52). -/
theorem mPlus_stripping (hV : BddPot V) (hz : z.im ≠ 0) :
    mPlus V z = 1 / ((V 1 : ℂ) - z - mPlus (fun n => V (n + 1)) z) := by
  obtain ⟨u, hu, hu0, hu2⟩ := exists_weyl_top hV (mem_resolventSet_of_im hV hz)
  set w : ℤ → ℂ := fun n => u (n + 1)
  have hw : IsSolution (fun n => V (n + 1)) z w := by
    intro n
    have := hu (n + 1)
    simp only [w]
    rw [show n - 1 + 1 = n + 1 - 1 by ring]
    linear_combination this
  have hw2 : SqSumTop w := ((sqSumTop_shift hu2 1).congr fun n => by simp [w])
  have hwne : w ≠ 0 := by
    intro h; apply hu0
    have h0 : u 0 = 0 := by
      have := congrFun h (-1); simpa [w] using this
    have h1 : u 1 = 0 := by
      have := congrFun h 0; simpa [w] using this
    exact eq_zero_of_isSolution hu h0 h1
  obtain ⟨hu0', hm, -⟩ := mPlus_eq hz hu hu0 hu2
  obtain ⟨hw0', hm1, -⟩ := mPlus_eq hz hw hwne hw2
  have hu1 : u 1 ≠ 0 := weyl_top_ne_zero hz hu hu2 hu0 1
  rw [hm, hm1]
  simp only [w] at hw0' ⊢
  norm_num
  have h := hu 1
  norm_num at h
  have hden : (V 1 : ℂ) - z + u 2 / u 1 = -(u 0 / u 1) := by
    field_simp
    linear_combination h
  rw [show (V 1 : ℂ) - z - -u 2 / u 1 = (V 1 : ℂ) - z + u 2 / u 1 by ring, hden]
  field_simp

/-- **Theorem 2.2.13** for the half-line `m`-function, (2.2.52). -/
theorem mHalf_stripping (hV : BddPot V) (hz : z.im ≠ 0) :
    mHalf V z = 1 / ((V 1 : ℂ) - z - mHalf (fun n => V (n + 1)) z) := by
  have hV1 : BddPot (fun n => V (n + 1)) := by
    obtain ⟨M, hM⟩ := hV; exact ⟨M, fun n => hM (n + 1)⟩
  rw [mHalf_eq_mPlus hV hz, mHalf_eq_mPlus hV1 hz, mPlus_stripping hV hz]

end DF
