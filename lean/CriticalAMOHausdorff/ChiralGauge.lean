/-
Copyright (c) 2026. Formalization of
  S. Becker, S. Jitomirskaya, I. Krasovsky, "Critical almost Mathieu operator: hidden
  singularity, gap continuity, and the Hausdorff dimension of the spectrum"
  (arXiv:1909.04429v2).

# Chiral gauge  (paper §3, eqs. (3.1)–(3.4), Theorem 3.1 `chiralrepresentthm`)

TeX references (`Arxiv_version-5.tex`, lines ~549–692):
* `H̃_{α,θ} = Ĥ_{α,1/4+α/2+θ}` (line ~551);
* the operators `T`, `S`, `U_x` (3.2)–(3.3) `(SandT)`, `(Q)`, the operator `R` (3.4) `(R)`, and
  `S^x` (line ~572);
* the fibre representations `H_{α,θ} = T + T⁻¹ + S + S⁻¹`,
  `H̃_{α,θ} = e^{iπα}(ST + S⁻¹T⁻¹) + e^{-iπα}(ST⁻¹ + S⁻¹T)` (lines ~578–582);
* the even/odd splitting of `T² + T⁻² + S + S⁻¹` into `H_{2α,θ} ⊕ H_{2α,θ+α}` (lines ~591–604);
* the commutation relations `(RS)`, `(RS-1)`, `(RTpm1)`, `(TU)`, `(UT)` and the `S^xT`,
  `U_xS^y` relations (lines ~628–672);
* the relations `(QS)`, `(QS-1)`, `QT^{±2}` and the intertwining identity
  `Q(T²+T⁻²+S+S⁻¹) = M̃_α Q` (lines ~674–690), i.e. Theorem 3.1.

## Formalization choices

We let all operators act on the space `Fn = ℤ → ℝ → ℂ` of *all* functions `φ(n, θ)`
(the paper's `L²(𝕋; ℓ²(ℤ))` with `θ` represented by its value; for the non-periodic operators
`S^x`, `U_x` the paper's convention "θ ∈ [0,1)" is just the restriction of our pointwise
formulas to `θ ∈ [0,1)`).  `T`, `T⁻¹`, `S^x`, `U_x` are the pointwise formulas (3.2)–(3.3).
The operator `R` (3.4) is defined literally,
`(Rφ)(n,θ) = ∑'_{k∈ℤ} e^{-2πik(θ+nα)} ∫_0^1 e^{-2πinβ} φ(k,β) dβ`,
using Mathlib's `tsum` and interval integral.

* All the commutation relations `RS = T⁻¹R`, `RS⁻¹ = TR`, `RT = SR`, `RT⁻¹ = S⁻¹R`,
  `TU_x = e^{iπxα} S^x U_x T`, ..., hold as *literal identities of functions for every `φ`*
  (the summands / integrands agree pointwise up to a reindexing of `k` and constant factors),
  so no convergence hypotheses are needed for them.
* The four relations `QS = e^{-iπα} S T⁻¹ Q`, `QS⁻¹ = e^{-iπα} S⁻¹ T Q`,
  `QT² = e^{iπα} S T Q`, `QT⁻² = e^{iπα} S⁻¹ T⁻¹ Q` are derived from these exactly as in the
  paper, again for every `φ`.
* To add the four relations up (Theorem 3.1) one needs additivity of `R`, which for `tsum`s and
  Bochner integrals requires summability/integrability.  We prove the intertwining identity
  `Q (T² + T⁻² + S + S⁻¹) φ = M̃_α (Q φ)` for all `φ` in the class `Good`: finitely many
  `k` with `φ(k, ·) ≠ 0`, and each `φ(k, ·)` interval-integrable on `[0,1]`.  This class is
  dense in `L²(𝕋; ℓ²(ℤ))` and is preserved by `T^{±1}, S^x, U_x`.
* The unitarity of `R` (a Fourier–Plancherel statement) is *not* formalized; the content of the
  paper's proof of Theorem 3.1 is the intertwining identity, which is fully proved here.

## Main results
* `T_U`, `U_T`, `U_Tinv`, `S_T`, `Tinv_S`, `U_S`, `R_S`, `R_Sinv`, `R_T`, `R_Tinv`:
  the commutation relations (3.5)–(3.9);
* `Q_S`, `Q_Sinv`, `Q_T2`, `Q_Tinv2`: (3.10)–(3.12);
* `chiral_representation` — **Theorem 3.1** (intertwining form);
* `amoOp_fibre`, `chiralOp_fibre` — the fibre representations of `H_{α,θ}` (matching
  `CAH.amo`) and of `H̃_{α,θ} = Ĥ_{α,1/4+α/2+θ}` (matching `CAH.chiral`);
* `doubled_even`, `doubled_odd` — the even/odd splitting into `H_{2α,θ}` and `H_{2α,θ+α}`.

There are no `sorry`s in this file.
-/
import CriticalAMOHausdorff.Basic

noncomputable section

open Real Complex MeasureTheory

namespace CAH

namespace ChiralGauge

/-- The function space on which the operators act: `φ(n, θ)`, `n ∈ ℤ`, `θ ∈ ℝ`. -/
abbrev Fn := ℤ → ℝ → ℂ

variable (α : ℝ)

/-- `(Tφ)(n,θ) = φ(n+1,θ)` (3.2). -/
def opT (φ : Fn) : Fn := fun n θ => φ (n + 1) θ

/-- `(T⁻¹φ)(n,θ) = φ(n-1,θ)`. -/
def opTinv (φ : Fn) : Fn := fun n θ => φ (n - 1) θ

/-- `(S^xφ)(n,θ) = e^{2πix(θ+nα)} φ(n,θ)`; `S = S^1`, `S⁻¹ = S^{-1}` (3.2). -/
def opS (x : ℝ) (φ : Fn) : Fn := fun n θ => cexp (2 * π * I * x * ((θ + n * α : ℝ) : ℂ)) * φ n θ

/-- `(U_xφ)(n,θ) = e^{2πinx(θ+nα/2)} φ(n,θ)` (3.3). -/
def opU (x : ℝ) (φ : Fn) : Fn :=
  fun n θ => cexp (2 * π * I * n * x * ((θ + n * α / 2 : ℝ) : ℂ)) * φ n θ

/-- `(Rφ)(n,θ) = ∑_{k∈ℤ} e^{-2πik(θ+nα)} ∫_𝕋 e^{-2πinβ} φ(k,β) dβ` (3.4). -/
def opR (φ : Fn) : Fn := fun n θ =>
  ∑' k : ℤ, cexp (-(2 * π * I * k * ((θ + n * α : ℝ) : ℂ))) *
    ∫ β in (0 : ℝ)..1, cexp (-(2 * π * I * n * β)) * φ k β

/-- `Q = U_1 R U_{1/2}` (Theorem 3.1). -/
def opQ (φ : Fn) : Fn := opU α 1 (opR α (opU α (1 / 2) φ))

/-- `T² + T⁻² + S + S⁻¹`. -/
def opDoubled (φ : Fn) : Fn := opT (opT φ) + opTinv (opTinv φ) + opS α 1 φ + opS α (-1) φ

/-- `H_{α,θ} = T + T⁻¹ + S + S⁻¹` (fibrewise AMO). -/
def opH (φ : Fn) : Fn := opT φ + opTinv φ + opS α 1 φ + opS α (-1) φ

/-- `H̃ = e^{iπα}(ST + S⁻¹T⁻¹) + e^{-iπα}(ST⁻¹ + S⁻¹T)` (fibrewise `H̃_{α,θ}`). -/
def opHt (φ : Fn) : Fn :=
  cexp (π * I * α) • (opS α 1 (opT φ) + opS α (-1) (opTinv φ)) +
    cexp (-(π * I * α)) • (opS α 1 (opTinv φ) + opS α (-1) (opT φ))

/-! ### Elementary algebra -/

variable {α}

lemma opT_opTinv (φ : Fn) : opT (opTinv φ) = φ := by
  funext n θ; simp [opT, opTinv]

lemma opTinv_opT (φ : Fn) : opTinv (opT φ) = φ := by
  funext n θ; simp [opT, opTinv]

lemma opT_smul (c : ℂ) (φ : Fn) : opT (c • φ) = c • opT φ := rfl
lemma opTinv_smul (c : ℂ) (φ : Fn) : opTinv (c • φ) = c • opTinv φ := rfl

lemma opS_smul (x : ℝ) (c : ℂ) (φ : Fn) : opS α x (c • φ) = c • opS α x φ := by
  funext n θ; simp only [opS, Pi.smul_apply, smul_eq_mul]; ring

lemma opU_smul (x : ℝ) (c : ℂ) (φ : Fn) : opU α x (c • φ) = c • opU α x φ := by
  funext n θ; simp only [opU, Pi.smul_apply, smul_eq_mul]; ring

lemma opR_smul (c : ℂ) (φ : Fn) : opR α (c • φ) = c • opR α φ := by
  funext n θ
  simp only [opR, Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  congr 1; funext k
  have h : ∀ β : ℝ, cexp (-(2 * π * I * n * β)) * (c * φ k β) =
      c * (cexp (-(2 * π * I * n * β)) * φ k β) := fun β => by ring
  simp_rw [h, intervalIntegral.integral_const_mul]
  ring

lemma opS_opS (x y : ℝ) (φ : Fn) : opS α x (opS α y φ) = opS α (x + y) φ := by
  funext n θ
  simp only [opS]
  rw [← mul_assoc, ← Complex.exp_add]; congr 2; push_cast; ring

lemma opS_zero (φ : Fn) : opS α 0 φ = φ := by
  funext n θ; simp [opS]

/-! ### Commutation relations (3.5)–(3.9) -/

/-- `(TU)`: `T U_x = e^{iπxα} S^x U_x T`. -/
theorem T_U (x : ℝ) (φ : Fn) :
    opT (opU α x φ) = cexp (π * I * x * α) • opS α x (opU α x (opT φ)) := by
  funext n θ
  simp only [opT, opU, opS, Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2; push_cast; ring

/-- `(UT)`, first relation: `U_x T = e^{-iπxα} S^{-x} T U_x`. -/
theorem U_T (x : ℝ) (φ : Fn) :
    opU α x (opT φ) = cexp (-(π * I * x * α)) • opS α (-x) (opT (opU α x φ)) := by
  rw [T_U, opS_smul, opS_opS, neg_add_cancel, opS_zero, smul_smul, ← Complex.exp_add,
    neg_add_cancel, Complex.exp_zero, one_smul]

/-- `(UT)`, second relation: `U_x T⁻¹ = e^{iπxα} T⁻¹ S^x U_x`. -/
theorem U_Tinv (x : ℝ) (φ : Fn) :
    opU α x (opTinv φ) = cexp (π * I * x * α) • opTinv (opS α x (opU α x φ)) := by
  have := T_U (α := α) x (opTinv φ)
  rw [opT_opTinv] at this
  rw [← opTinv_smul, ← this, opTinv_opT]

/-- `S^x T = e^{-2πixα} T S^x`. -/
theorem S_T (x : ℝ) (φ : Fn) :
    opS α x (opT φ) = cexp (-(2 * π * I * x * α)) • opT (opS α x φ) := by
  funext n θ
  simp only [opT, opS, Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2; push_cast; ring

/-- `T S^x = e^{2πixα} S^x T`. -/
theorem T_S (x : ℝ) (φ : Fn) :
    opT (opS α x φ) = cexp (2 * π * I * x * α) • opS α x (opT φ) := by
  rw [S_T, smul_smul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_smul]

/-- `T⁻¹ S^x = e^{-2πixα} S^x T⁻¹`. -/
theorem Tinv_S (x : ℝ) (φ : Fn) :
    opTinv (opS α x φ) = cexp (-(2 * π * I * x * α)) • opS α x (opTinv φ) := by
  funext n θ
  simp only [opTinv, opS, Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2; push_cast; ring

/-- The paper's form: `T⁻¹ S^{-x} = e^{2πixα} S^{-x} T⁻¹`. -/
theorem Tinv_Sneg (x : ℝ) (φ : Fn) :
    opTinv (opS α (-x) φ) = cexp (2 * π * I * x * α) • opS α (-x) (opTinv φ) := by
  rw [Tinv_S]; congr 2; push_cast; ring

/-- `S^x T⁻¹ = e^{2πixα} T⁻¹ S^x`. -/
theorem S_Tinv (x : ℝ) (φ : Fn) :
    opS α x (opTinv φ) = cexp (2 * π * I * x * α) • opTinv (opS α x φ) := by
  rw [Tinv_S, smul_smul, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_smul]

/-- `U_x S^y = S^y U_x`. -/
theorem U_S (x y : ℝ) (φ : Fn) : opU α x (opS α y φ) = opS α y (opU α x φ) := by
  funext n θ; simp only [opU, opS]; ring

/-- `(RS)`: `R S = T⁻¹ R`. -/
theorem R_S (φ : Fn) : opR α (opS α 1 φ) = opTinv (opR α φ) := by
  funext n θ
  simp only [opR, opS, opTinv]
  congr 1; funext k
  have : ∀ β : ℝ, cexp (-(2 * π * I * n * β)) *
      (cexp (2 * π * I * ((1 : ℝ) : ℂ) * ((β + k * α : ℝ) : ℂ)) * φ k β) =
      cexp (2 * π * I * k * α) * (cexp (-(2 * π * I * ((n - 1 : ℤ) : ℂ) * β)) * φ k β) := by
    intro β
    rw [← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    congr 2; push_cast; ring
  simp_rw [this, intervalIntegral.integral_const_mul, ← mul_assoc, ← Complex.exp_add]
  congr 2; push_cast; ring

/-- `(RS-1)`: `R S⁻¹ = T R`. -/
theorem R_Sinv (φ : Fn) : opR α (opS α (-1) φ) = opT (opR α φ) := by
  funext n θ
  simp only [opR, opS, opT]
  congr 1; funext k
  have : ∀ β : ℝ, cexp (-(2 * π * I * n * β)) *
      (cexp (2 * π * I * ((-1 : ℝ) : ℂ) * ((β + k * α : ℝ) : ℂ)) * φ k β) =
      cexp (-(2 * π * I * k * α)) * (cexp (-(2 * π * I * ((n + 1 : ℤ) : ℂ) * β)) * φ k β) := by
    intro β
    rw [← mul_assoc, ← mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
    congr 2; push_cast; ring
  simp_rw [this, intervalIntegral.integral_const_mul, ← mul_assoc, ← Complex.exp_add]
  congr 2; push_cast; ring

/-- `(RTpm1)`, first relation: `R T = S R`. -/
theorem R_T (φ : Fn) : opR α (opT φ) = opS α 1 (opR α φ) := by
  funext n θ
  simp only [opR, opS, opT]
  set Ik : ℤ → ℂ := fun k => ∫ β in (0 : ℝ)..1, cexp (-(2 * π * I * n * β)) * φ k β
  have h := (Equiv.addRight (1 : ℤ)).tsum_eq
    (fun k => cexp (-(2 * π * I * ((k - 1 : ℤ) : ℂ) * ((θ + n * α : ℝ) : ℂ))) * Ik k)
  simp only [Equiv.coe_addRight, add_sub_cancel_right] at h
  refine h.trans ?_
  rw [← tsum_mul_left]
  congr 1; funext k
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2; push_cast; ring

/-- `(RTpm1)`, second relation: `R T⁻¹ = S⁻¹ R`. -/
theorem R_Tinv (φ : Fn) : opR α (opTinv φ) = opS α (-1) (opR α φ) := by
  funext n θ
  simp only [opR, opS, opTinv]
  set Ik : ℤ → ℂ := fun k => ∫ β in (0 : ℝ)..1, cexp (-(2 * π * I * n * β)) * φ k β
  have h := (Equiv.subRight (1 : ℤ)).tsum_eq
    (fun k => cexp (-(2 * π * I * ((k + 1 : ℤ) : ℂ) * ((θ + n * α : ℝ) : ℂ))) * Ik k)
  simp only [Equiv.subRight_apply, sub_add_cancel] at h
  refine h.trans ?_
  rw [← tsum_mul_left]
  congr 1; funext k
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2; push_cast; ring

/-! ### The relations for `Q = U_1 R U_{1/2}` (3.10)–(3.12) -/

/-- `(QS)`: `Q S = e^{-iπα} S T⁻¹ Q`. -/
theorem Q_S (φ : Fn) :
    opQ α (opS α 1 φ) = cexp (-(π * I * α)) • opS α 1 (opTinv (opQ α φ)) := by
  simp only [opQ]
  rw [U_S, R_S, U_Tinv, Tinv_S, smul_smul, ← Complex.exp_add]
  congr 2; push_cast; ring

/-- `(QS-1)`: `Q S⁻¹ = e^{-iπα} S⁻¹ T Q`. -/
theorem Q_Sinv (φ : Fn) :
    opQ α (opS α (-1) φ) = cexp (-(π * I * α)) • opS α (-1) (opT (opQ α φ)) := by
  simp only [opQ]
  rw [U_S, R_Sinv, U_T]
  congr 2; push_cast; ring

/-- `Q T² = e^{iπα} S T Q`. -/
theorem Q_T2 (φ : Fn) :
    opQ α (opT (opT φ)) = cexp (π * I * α) • opS α 1 (opT (opQ α φ)) := by
  simp only [opQ]
  -- `U_{1/2} T² = e^{-2πiα} S⁻¹ T² U_{1/2}`
  have h1 : opU α (1 / 2) (opT (opT φ)) =
      cexp (-(2 * π * I * α)) • opS α (-1) (opT (opT (opU α (1 / 2) φ))) := by
    rw [U_T, U_T, opT_smul, opS_smul, T_S, opS_smul, opS_opS, smul_smul, smul_smul,
      ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    · congr 1; push_cast; ring
    · norm_num
  -- `R S⁻¹ T² = T S² R`
  have h2 : ∀ ψ : Fn, opR α (opS α (-1) (opT (opT ψ))) =
      opT (opS α 1 (opS α 1 (opR α ψ))) := by
    intro ψ; rw [R_Sinv, R_T, R_T]
  rw [h1, opR_smul, h2, opU_smul, U_T, U_S, U_S, T_S, T_S, opS_smul, opS_smul, opS_smul,
    opS_opS, opS_opS, smul_smul, smul_smul, smul_smul, ← Complex.exp_add, ← Complex.exp_add,
    ← Complex.exp_add]
  congr 1
  · congr 1; push_cast; ring
  · norm_num

/-- `Q T⁻² = e^{iπα} S⁻¹ T⁻¹ Q`. -/
theorem Q_Tinv2 (φ : Fn) :
    opQ α (opTinv (opTinv φ)) = cexp (π * I * α) • opS α (-1) (opTinv (opQ α φ)) := by
  simp only [opQ]
  -- `U_{1/2} T⁻² = e^{2πiα} T⁻² S U_{1/2}`
  have h1 : opU α (1 / 2) (opTinv (opTinv φ)) =
      cexp (2 * π * I * α) • opTinv (opTinv (opS α 1 (opU α (1 / 2) φ))) := by
    rw [U_Tinv, U_Tinv, opS_smul, opTinv_smul, S_Tinv, opTinv_smul, opS_opS, smul_smul,
      smul_smul, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    · congr 1; push_cast; ring
    · norm_num
  -- `R T⁻² S = S⁻² T⁻¹ R`
  have h2 : ∀ ψ : Fn, opR α (opTinv (opTinv (opS α 1 ψ))) =
      opS α (-1) (opS α (-1) (opTinv (opR α ψ))) := by
    intro ψ; rw [R_Tinv, R_Tinv, R_S]
  rw [h1, opR_smul, h2, opU_smul, U_S, U_S, U_Tinv, opS_smul, opS_smul, Tinv_S, opS_smul,
    opS_smul, opS_opS, opS_opS, smul_smul, smul_smul, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  · congr 1; push_cast; ring
  · norm_num

/-! ### Theorem 3.1 -/

/-- The class of functions on which `R` is additive: finitely many nonzero fibres `φ(k,·)`,
each interval-integrable on `[0,1]`. -/
def Good (φ : Fn) : Prop :=
  (∃ F : Finset ℤ, ∀ k ∉ F, φ k = 0) ∧ ∀ k, IntervalIntegrable (φ k) volume 0 1

lemma good_add {φ ψ : Fn} (hφ : Good φ) (hψ : Good ψ) : Good (φ + ψ) := by
  obtain ⟨⟨F, hF⟩, hφi⟩ := hφ
  obtain ⟨⟨G, hG⟩, hψi⟩ := hψ
  refine ⟨⟨F ∪ G, fun k hk => ?_⟩, fun k => (hφi k).add (hψi k)⟩
  simp only [Finset.mem_union, not_or] at hk
  funext θ; simp [hF k hk.1, hG k hk.2]

lemma good_opT {φ : Fn} (hφ : Good φ) : Good (opT φ) := by
  obtain ⟨⟨F, hF⟩, hφi⟩ := hφ
  refine ⟨⟨F.image (fun k => k - 1), fun k hk => ?_⟩, fun k => hφi (k + 1)⟩
  have : k + 1 ∉ F := fun h => hk (Finset.mem_image.2 ⟨k + 1, h, by ring⟩)
  funext θ; simp [opT, hF _ this]

lemma good_opTinv {φ : Fn} (hφ : Good φ) : Good (opTinv φ) := by
  obtain ⟨⟨F, hF⟩, hφi⟩ := hφ
  refine ⟨⟨F.image (fun k => k + 1), fun k hk => ?_⟩, fun k => hφi (k - 1)⟩
  have : k - 1 ∉ F := fun h => hk (Finset.mem_image.2 ⟨k - 1, h, by ring⟩)
  funext θ; simp [opTinv, hF _ this]

lemma good_mul {φ : Fn} (hφ : Good φ) (g : ℤ → ℝ → ℂ) (hg : ∀ k, Continuous (g k)) :
    Good (fun k θ => g k θ * φ k θ) := by
  obtain ⟨⟨F, hF⟩, hφi⟩ := hφ
  refine ⟨⟨F, fun k hk => ?_⟩, fun k => ?_⟩
  · funext θ; simp [hF k hk]
  · have := (hφi k).mul_continuousOn (hg k).continuousOn
    simpa [mul_comm] using this

lemma good_opS {φ : Fn} (hφ : Good φ) (x : ℝ) : Good (opS α x φ) :=
  good_mul hφ _ (fun k => by fun_prop)

lemma good_opU {φ : Fn} (hφ : Good φ) (x : ℝ) : Good (opU α x φ) :=
  good_mul hφ _ (fun k => by fun_prop)

lemma opU_add (x : ℝ) (φ ψ : Fn) : opU α x (φ + ψ) = opU α x φ + opU α x ψ := by
  funext n θ; simp only [opU, Pi.add_apply]; ring

/-- `R` is additive on `Good` functions. -/
lemma opR_add {φ ψ : Fn} (hφ : Good φ) (hψ : Good ψ) :
    opR α (φ + ψ) = opR α φ + opR α ψ := by
  obtain ⟨⟨F, hF⟩, hφi⟩ := hφ
  obtain ⟨⟨G, hG⟩, hψi⟩ := hψ
  funext n θ
  simp only [opR, Pi.add_apply, mul_add]
  have hint : ∀ (χ : Fn), (∀ k, IntervalIntegrable (χ k) volume 0 1) → ∀ k,
      IntervalIntegrable (fun β => cexp (-(2 * π * I * n * β)) * χ k β) volume 0 1 := by
    intro χ hχ k
    have := (hχ k).mul_continuousOn
      (by fun_prop : Continuous fun β : ℝ => cexp (-(2 * π * I * n * β))).continuousOn
    simpa [mul_comm] using this
  have hk : ∀ k : ℤ, (∫ β in (0 : ℝ)..1,
      (cexp (-(2 * π * I * n * β)) * φ k β + cexp (-(2 * π * I * n * β)) * ψ k β)) =
      (∫ β in (0 : ℝ)..1, cexp (-(2 * π * I * n * β)) * φ k β) +
        ∫ β in (0 : ℝ)..1, cexp (-(2 * π * I * n * β)) * ψ k β :=
    fun k => intervalIntegral.integral_add (hint φ hφi k) (hint ψ hψi k)
  simp_rw [hk, mul_add]
  refine Summable.tsum_add ?_ ?_
  · refine summable_of_ne_finset_zero (s := F) (fun k hk => ?_)
    simp [hF k hk]
  · refine summable_of_ne_finset_zero (s := G) (fun k hk => ?_)
    simp [hG k hk]

lemma opQ_add {φ ψ : Fn} (hφ : Good φ) (hψ : Good ψ) :
    opQ α (φ + ψ) = opQ α φ + opQ α ψ := by
  simp only [opQ]
  rw [opU_add, opR_add (good_opU hφ _) (good_opU hψ _), opU_add]

/-- **Theorem 3.1 (`chiralrepresentthm`), intertwining form.**  With `Q = U_1 R U_{1/2}`,
`Q (T² + T⁻² + S + S⁻¹) = M̃_α Q`, where `M̃_α = e^{iπα}(ST + S⁻¹T⁻¹) + e^{-iπα}(ST⁻¹ + S⁻¹T)`
acts fibrewise as `H̃_{α,θ}` (see `chiralOp_fibre`).  Proved on the class `Good`. -/
theorem chiral_representation {φ : Fn} (hφ : Good φ) :
    opQ α (opDoubled α φ) = opHt α (opQ α φ) := by
  have h1 := good_opT (good_opT hφ)
  have h2 := good_opTinv (good_opTinv hφ)
  have h3 := good_opS (α := α) hφ 1
  have h4 := good_opS (α := α) hφ (-1)
  simp only [opDoubled]
  rw [opQ_add (good_add (good_add h1 h2) h3) h4, opQ_add (good_add h1 h2) h3, opQ_add h1 h2, Q_T2, Q_Tinv2,
    Q_S, Q_Sinv, opHt, smul_add, smul_add]
  abel

/-! ### Fibre representations -/

lemma cexp_pair (y : ℝ) :
    cexp (2 * π * I * ((1 : ℝ) : ℂ) * ((y : ℝ) : ℂ)) +
        cexp (2 * π * I * ((-1 : ℝ) : ℂ) * ((y : ℝ) : ℂ)) =
      ((2 * Real.cos (2 * π * y) : ℝ) : ℂ) := by
  push_cast
  rw [Complex.two_cos]
  ring_nf

/-- **Fibre representation of `H_{α,θ}`.**  If `φ(·,θ) = u`, then
`((T + T⁻¹ + S + S⁻¹) φ)(n,θ) = (H_{α,θ} u)(n)` with `H_{α,θ} = CAH.amo α θ`. -/
theorem amoOp_fibre (θ : ℝ) (u : L2 ℤ) (φ : Fn) (hφ : ∀ m, φ m θ = u m) (n : ℤ) :
    opH α φ n θ = amo α θ u n := by
  rw [amo, jacobi_apply bddFun_two_cos (bddFun_const 1)]
  simp only [opH, Pi.add_apply, opT, opTinv, opS, hφ]
  rw [← cexp_pair]
  simp only [Complex.ofReal_one, one_mul]
  ring

/-- **Fibre representation of `H̃_{α,θ}`.**  If `φ(·,θ) = u`, then `(M̃_α φ)(n,θ)` equals
`(Ĥ_{α,1/4+α/2+θ} u)(n)`, i.e. `H̃_{α,θ} = Ĥ_{α,1/4+α/2+θ}` with `Ĥ = CAH.chiral` (1.2):
`2 sin 2π(αn+1/4+α/2+θ) = e^{iπα}e^{2πi(θ+nα)} + e^{-iπα}e^{-2πi(θ+nα)}` and
`2 sin 2π(α(n-1)+1/4+α/2+θ) = e^{iπα}e^{-2πi(θ+nα)} + e^{-iπα}e^{2πi(θ+nα)}`. -/
theorem chiralOp_fibre (θ : ℝ) (u : L2 ℤ) (φ : Fn) (hφ : ∀ m, φ m θ = u m) (n : ℤ) :
    opHt α φ n θ = chiral α (1 / 4 + α / 2 + θ) u n := by
  rw [chiral, jacobi_apply (bddFun_const 0) (bddFun_two_sin _)]
  simp only [opHt, Pi.add_apply, Pi.smul_apply, smul_eq_mul, opT, opTinv, opS, hφ]
  have c1 : ((2 * Real.sin (2 * π * (1 / 4 + α / 2 + θ + n * α)) : ℝ) : ℂ) =
      cexp (π * I * α) * cexp (2 * π * I * ((1 : ℝ) : ℂ) * ((θ + n * α : ℝ) : ℂ)) +
      cexp (-(π * I * α)) * cexp (2 * π * I * ((-1 : ℝ) : ℂ) * ((θ + n * α : ℝ) : ℂ)) := by
    rw [show 2 * π * (1 / 4 + α / 2 + θ + n * α) = (2 * π * (θ + n * α) + π * α) + π / 2 by
      ring, Real.sin_add_pi_div_two]
    push_cast
    rw [Complex.two_cos]
    simp only [← Complex.exp_add]
    ring_nf
  have c2 : ((2 * Real.sin (2 * π * (1 / 4 + α / 2 + θ + (n - 1) * α)) : ℝ) : ℂ) =
      cexp (π * I * α) * cexp (2 * π * I * ((-1 : ℝ) : ℂ) * ((θ + n * α : ℝ) : ℂ)) +
      cexp (-(π * I * α)) * cexp (2 * π * I * ((1 : ℝ) : ℂ) * ((θ + n * α : ℝ) : ℂ)) := by
    rw [show 2 * π * (1 / 4 + α / 2 + θ + (n - 1) * α) =
      (2 * π * (θ + n * α) - π * α) + π / 2 by ring, Real.sin_add_pi_div_two]
    push_cast
    rw [Complex.two_cos]
    simp only [← Complex.exp_add]
    ring_nf
  rw [c1, c2]
  simp only [Complex.ofReal_zero, zero_mul, add_zero]
  ring

/-- **Even sites.**  If `φ(2m,θ) = u(m)` then `((T² + T⁻² + S + S⁻¹)φ)(2n,θ) = (H_{2α,θ} u)(n)`. -/
theorem doubled_even (θ : ℝ) (u : L2 ℤ) (φ : Fn) (hφ : ∀ m, φ (2 * m) θ = u m) (n : ℤ) :
    opDoubled α φ (2 * n) θ = amo (2 * α) θ u n := by
  rw [amo, jacobi_apply bddFun_two_cos (bddFun_const 1)]
  simp only [opDoubled, Pi.add_apply, opT, opTinv, opS]
  rw [show 2 * n + 1 + 1 = 2 * (n + 1) by ring, show 2 * n - 1 - 1 = 2 * (n - 1) by ring, hφ, hφ,
    hφ, show θ + (n : ℝ) * (2 * α) = θ + ((2 * n : ℤ) : ℝ) * α by push_cast; ring, ← cexp_pair]
  simp only [Complex.ofReal_one, one_mul]
  ring

/-- **Odd sites.**  If `φ(2m+1,θ) = u(m)` then
`((T² + T⁻² + S + S⁻¹)φ)(2n+1,θ) = (H_{2α,θ+α} u)(n)`. -/
theorem doubled_odd (θ : ℝ) (u : L2 ℤ) (φ : Fn) (hφ : ∀ m, φ (2 * m + 1) θ = u m) (n : ℤ) :
    opDoubled α φ (2 * n + 1) θ = amo (2 * α) (θ + α) u n := by
  rw [amo, jacobi_apply bddFun_two_cos (bddFun_const 1)]
  simp only [opDoubled, Pi.add_apply, opT, opTinv, opS]
  rw [show 2 * n + 1 + 1 + 1 = 2 * (n + 1) + 1 by ring,
    show 2 * n + 1 - 1 - 1 = 2 * (n - 1) + 1 by ring, hφ, hφ, hφ,
    show θ + α + (n : ℝ) * (2 * α) = θ + ((2 * n + 1 : ℤ) : ℝ) * α by push_cast; ring,
    ← cexp_pair]
  simp only [Complex.ofReal_one, one_mul]
  ring

end ChiralGauge

end CAH
