/-
# Characterization of uniform hyperbolicity  (paper §3, Theorem `uniformly hyperbolic`)

* `per` — **Lemma `per`**: if `(α, A)` is regular with `L(α, A) > 0`, then periodic
  approximants `(p/q, Ã)` with `p/q` close to `α` and `Ã` close to `A` are uniformly hyperbolic.
* `ulc`, `derivCoeffs` — the upper left coefficient and the coefficients `q₁, q₂, q₃` of the
  derivative of the Lyapunov exponent; `derivCoeffs_sum_eq_ulc`:
  `q₁w₁ + q₂w₂ + q₃w₃ = u.l.c.(B⁻¹ w B)`, and `ulc_diag_conj`: conjugation by a diagonal
  matrix does not change the u.l.c.  (Both proved.)
* `deriv_formula` — **Lemma (derivative of `L` at `𝒰ℋ`)**:
  `d/dt L(α, A e^{tw})|_{t=0} = Re ∫ Σ qᵢ wᵢ`.
* `ang` — **Lemma `ang`** in quantitative form (proved): if `ad - bc = 1` and `|ab|, |cd| ≤ K`
  then `(|a|² + |c|²)(|b|² + |d|²) ≤ 3K² + (1 + K)²`, i.e. the sine of the angle between the
  complex lines through `(a, c)` and `(b, d)` is bounded below.
* The hard direction of the **Theorem** (regular with `L > 0` ⇒ uniformly hyperbolic) is proved
  in `RegularUH.lean` (`regular_pos_imp_uh`); the theorem itself (`uh_iff_regular`) is assembled
  in `Stratified.lean`.
-/
import AvilaGlobal.Quantization

noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology Complex Set

namespace AvilaGlobal

open AMO

/-! ### Uniform hyperbolicity of periodic approximants -/

/-- **Lemma `per`** (stated, not proved here).  Let `α` be irrational and let `(α, A)` be regular with positive Lyapunov
exponent.  If `pₙ/qₙ → α` and `Aₙ → A` uniformly on the strip, then `(pₙ/qₙ, Aₙ)` is
uniformly hyperbolic for all large `n`. -/
def PerClaim : Prop :=
  ∀ {δ : ℝ} {A : ℂ → M2}, IsAnalyticCocycle δ A → ∀ {α : ℝ}, Irrational α → IsRegular α A →
    0 < L α A 0 → ∀ {r : ℕ → ℚ}, Tendsto (fun n => (r n : ℝ)) atTop (𝓝 α) →
      ∀ {As : ℕ → ℂ → M2}, (∀ n, IsAnalyticCocycle δ (As n)) →
        TendstoUniformlyOn As A atTop (strip δ) → ∀ᶠ n in atTop, UH (r n) (As n)

/-! ### The derivative of the Lyapunov exponent on `𝒰ℋ` -/

/-- The upper left coefficient. -/
def ulc (M : M2) : ℂ := M 0 0

/-- Conjugating by a diagonal invertible matrix does not change the u.l.c. -/
theorem ulc_diag_conj (M : M2) {l₁ l₂ : ℂ} (h₁ : l₁ ≠ 0) (h₂ : l₂ ≠ 0) :
    ulc ((!![l₁⁻¹, 0; 0, l₂⁻¹] : M2) * M * !![l₁, 0; 0, l₂]) = ulc M := by
  simp [ulc, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  field_simp

/-- The coefficients `(q₁, q₂, q₃) = (ad + bc, cd, -ba)` of the derivative of the Lyapunov
exponent, for `B = [[a, b], [c, d]]`. -/
def derivCoeffs (B : M2) : Fin 3 → ℂ :=
  ![B 0 0 * B 1 1 + B 0 1 * B 1 0, B 1 0 * B 1 1, -(B 0 1 * B 0 0)]

/-- `q₁w₁ + q₂w₂ + q₃w₃ = u.l.c.(B⁻¹ w B)` for `B ∈ SL(2,ℂ)` and `w = [[w₁, w₂], [w₃, -w₁]]`. -/
theorem derivCoeffs_sum_eq_ulc {B : M2} (hB : B.det = 1) (w₁ w₂ w₃ : ℂ) :
    derivCoeffs B 0 * w₁ + derivCoeffs B 1 * w₂ + derivCoeffs B 2 * w₃ =
      ulc (B⁻¹ * !![w₁, w₂; w₃, -w₁] * B) := by
  rw [Matrix.inv_def, hB, Ring.inverse_one, one_smul, Matrix.adjugate_fin_two]
  simp [derivCoeffs, ulc, Matrix.mul_apply, Fin.sum_univ_two]
  ring

/-- **Lemma (derivative of the Lyapunov exponent at uniformly hyperbolic cocycles)**, proved in
`DerivFormula.lean` (`derivFormula_proof`).
Let `(α, A) ∈ 𝒰ℋ` and let `B : ℝ → SL(2,ℂ)` be continuous, `1`-periodic, with first column
along the unstable and second along the stable direction (the first column is expanded), so that `B(x+α)⁻¹ A(x) B(x)` is diagonal.  Then for every
continuous `1`-periodic `w : ℝ → sl(2,ℂ)`,
`d/dt L(α, A e^{tw})|_{t=0} = Re ∫_𝕋 Σᵢ qᵢ(x) wᵢ(x) dx`. -/
def DerivFormulaClaim : Prop :=
  ∀ {α : ℝ} {A : ℝ → M2}, IsSLCocycle A → IsUH α A →
    ∀ {B : ℝ → M2}, Continuous B → Function.Periodic B 1 → (∀ x, (B x).det = 1) →
      (∀ x, ((B (x + α))⁻¹ * A x * B x) 0 1 = 0 ∧ ((B (x + α))⁻¹ * A x * B x) 1 0 = 0) →
      (∃ n : ℕ, 1 ≤ n ∧ ∀ x, ‖B x *ᵥ ![1, 0]‖ < ‖iter α A n x *ᵥ (B x *ᵥ ![1, 0])‖) →
      ∀ {w : ℝ → M2}, Continuous w → Function.Periodic w 1 → (∀ x, (w x).trace = 0) →
        HasDerivAt (fun t : ℝ => lyapunov α fun x => A x * NormedSpace.exp ((t : ℂ) • w x))
          (∫ x in (0 : ℝ)..1, (derivCoeffs (B x) 0 * w x 0 0 + derivCoeffs (B x) 1 * w x 0 1 +
            derivCoeffs (B x) 2 * w x 1 0).re) 0

/-! ### The angle lemma -/

/-- **Lemma `ang`** (quantitative form).  If `ad - bc = 1` and `|ab|, |cd| ≤ K`, then
`(|a|² + |c|²)(|b|² + |d|²) ≤ 3K² + (1 + K)²`.  Since the sine of the angle between the complex
lines through `(a, c)` and `(b, d)` is `|ad - bc| / (‖(a,c)‖ ‖(b,d)‖)`, a small angle forces
`max(|ab|, |cd|)` to be large. -/
theorem ang {a b c d : ℂ} (h : a * d - b * c = 1) {K : ℝ} (hab : ‖a * b‖ ≤ K)
    (hcd : ‖c * d‖ ≤ K) :
    (‖a‖ ^ 2 + ‖c‖ ^ 2) * (‖b‖ ^ 2 + ‖d‖ ^ 2) ≤ 3 * K ^ 2 + (1 + K) ^ 2 := by
  have h1 : |‖a * d‖ - ‖b * c‖| ≤ 1 := by
    have := abs_norm_sub_norm_le (a * d) (b * c)
    rwa [h, norm_one] at this
  simp only [norm_mul] at hab hcd h1
  have hK : 0 ≤ K := (mul_nonneg (norm_nonneg a) (norm_nonneg b)).trans hab
  have h2 : (‖a‖ * ‖d‖ - ‖b‖ * ‖c‖) ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (‖a‖ * ‖d‖ - ‖b‖ * ‖c‖)]
  have h3 : (‖a‖ * ‖b‖) ^ 2 ≤ K ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hab 2
  have h4 : (‖c‖ * ‖d‖) ^ 2 ≤ K ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hcd 2
  have h5 : (‖a‖ * ‖b‖) * (‖c‖ * ‖d‖) ≤ K * K :=
    mul_le_mul hab hcd (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hK
  have hid : (‖a‖ ^ 2 + ‖c‖ ^ 2) * (‖b‖ ^ 2 + ‖d‖ ^ 2) =
      (‖a‖ * ‖b‖) ^ 2 + (‖c‖ * ‖d‖) ^ 2 + (‖a‖ * ‖d‖ - ‖b‖ * ‖c‖) ^ 2 +
        2 * ((‖a‖ * ‖b‖) * (‖c‖ * ‖d‖)) := by ring
  rw [hid]
  nlinarith

end AvilaGlobal
