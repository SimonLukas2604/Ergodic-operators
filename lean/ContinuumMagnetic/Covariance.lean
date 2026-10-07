/-
# Paper III: magnetic covariance and coefficient symmetries

*Periodic magnetic Schrödinger operators: Dry Ten Martini and spectral transitions*,
§2.1 (eq. `c-eq:translations`), §3 "Covariance of the Gram construction",
§3 "Covariance of the exact interaction" (eqs. `c-eq:magnetic-cocycle`,
`c-eq:twisted-adjoint`), Corollary `c-cor:critical`, §4.1 "Normalization and the choice of
fibre direction" (eq. `eq:continuum-oriented`), and the guiding-centre orientation of §5.
-/
import ContinuumMagnetic.Basic

noncomputable section

open AMO
open scoped ComplexConjugate
open Complex L2

namespace CMS

/-! ### 1. Magnetic translations  (paper (2.4), `c-eq:translations`) -/

/-- `T₁ u(x) = e^{i μ 𝓑 x₂ / h} u(x - (μ,0))`. -/
def T1 (μ B h : ℝ) (u : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  fun x => Complex.exp (((μ * B / h * x.2 : ℝ) : ℂ) * I) * u (x.1 - μ, x.2)

/-- `T₂ u(x) = u(x - (0,1))`. -/
def T2 (u : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ := fun x => u (x.1, x.2 - 1)

/-- Along the field path `μ𝓑/h = 2πγ`, `T₁ u(x) = e(γ x₂) u(x - (μ,0))`. -/
lemma T1_fieldPath {μ h : ℝ} (hμ : μ ≠ 0) (hh : h ≠ 0) (γ : ℝ) (u : ℝ × ℝ → ℂ)
    (x : ℝ × ℝ) : T1 μ (fieldPath μ γ h) h u x = e (γ * x.2) * u (x.1 - μ, x.2) := by
  have hk : μ * fieldPath μ γ h / h * x.2 = 2 * Real.pi * (γ * x.2) := by
    unfold fieldPath
    field_simp
  unfold T1 e
  rw [hk]

/-- **Magnetic commutation relation** `T₁T₂ = e^{2πiγ} T₂T₁` along the field path
(paper `c-eq:translations`). -/
theorem T1_T2 {μ h : ℝ} (hμ : μ ≠ 0) (hh : h ≠ 0) (γ : ℝ) (u : ℝ × ℝ → ℂ) :
    T1 μ (fieldPath μ γ h) h (T2 u) = e γ • T2 (T1 μ (fieldPath μ γ h) h u) := by
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, T1_fieldPath hμ hh, T2]
  rw [← mul_assoc, ← e_add]
  congr 2
  ring

/-- `T₁` is a pointwise isometry composed with a shift: `|T₁u(x)| = |u(x - (μ,0))|`. -/
lemma norm_T1 (μ B h : ℝ) (u : ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    ‖T1 μ B h u x‖ = ‖u (x - (μ, 0))‖ := by
  rw [show x - (μ, 0) = (x.1 - μ, x.2) from Prod.ext (by simp) (by simp)]
  simp only [T1, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

lemma norm_T2 (u : ℝ × ℝ → ℂ) (x : ℝ × ℝ) : ‖T2 u x‖ = ‖u (x - (0, 1))‖ := by
  rw [show x - (0, 1) = (x.1, x.2 - 1) from Prod.ext (by simp) (by simp)]
  rfl

/-- The magnetic translations `S_m = T₂^{m₂} T₁^{m₁}` along the field path, in closed form:
`S_m u(x) = e(γ m₁ (x₂ - m₂)) u(x - (m₁μ, m₂))`. -/
def S (γ μ : ℝ) (m : ℤ × ℤ) (u : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  fun x => e (γ * m.1 * (x.2 - m.2)) * u (x.1 - m.1 * μ, x.2 - m.2)

@[simp] lemma S_zero (γ μ : ℝ) (u : ℝ × ℝ → ℂ) : S γ μ 0 u = u := by
  funext x
  simp [S]

lemma S_one_zero {μ h : ℝ} (hμ : μ ≠ 0) (hh : h ≠ 0) (γ : ℝ) (u : ℝ × ℝ → ℂ) :
    S γ μ (1, 0) u = T1 μ (fieldPath μ γ h) h u := by
  funext x
  simp [S, T1_fieldPath hμ hh]

lemma S_zero_one (γ μ : ℝ) (u : ℝ × ℝ → ℂ) : S γ μ (0, 1) u = T2 u := by
  funext x
  simp [S, T2]

/-- `S_{(k+1,0)} = T₁ S_{(k,0)}` for every `k ∈ ℤ`, so `S_{(k,0)} = T₁^k`. -/
lemma S_succ_fst {μ h : ℝ} (hμ : μ ≠ 0) (hh : h ≠ 0) (γ : ℝ) (k : ℤ) (u : ℝ × ℝ → ℂ) :
    S γ μ (k + 1, 0) u = T1 μ (fieldPath μ γ h) h (S γ μ (k, 0) u) := by
  funext x
  simp only [S, T1_fieldPath hμ hh]
  rw [← mul_assoc, ← e_add]
  push_cast
  congr 2
  · ring
  · congr 1; ring

/-- `S_{(0,l+1)} = T₂ S_{(0,l)}` for every `l ∈ ℤ`, so `S_{(0,l)} = T₂^l`. -/
lemma S_succ_snd (γ μ : ℝ) (l : ℤ) (u : ℝ × ℝ → ℂ) :
    S γ μ (0, l + 1) u = T2 (S γ μ (0, l) u) := by
  funext x
  simp only [S, T2]
  push_cast
  simp only [zero_mul, mul_zero, e_zero, one_mul, sub_zero]
  congr 2
  ring

/-- `S_m = T₂^{m₂} T₁^{m₁}`: `S_{(m₁,m₂)} = S_{(0,m₂)} S_{(m₁,0)}`. -/
lemma S_eq_comp (γ μ : ℝ) (m : ℤ × ℤ) (u : ℝ × ℝ → ℂ) :
    S γ μ m u = S γ μ (0, m.2) (S γ μ (m.1, 0) u) := by
  funext x
  simp [S]

lemma S_fst_nat {μ h : ℝ} (hμ : μ ≠ 0) (hh : h ≠ 0) (γ : ℝ) (n : ℕ) (u : ℝ × ℝ → ℂ) :
    S γ μ (n, 0) u = (T1 μ (fieldPath μ γ h) h)^[n] u := by
  induction n with
  | zero => exact S_zero γ μ u
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← ih, ← S_succ_fst hμ hh]
    push_cast; rfl

lemma S_snd_nat (γ μ : ℝ) (n : ℕ) (u : ℝ × ℝ → ℂ) : S γ μ (0, n) u = T2^[n] u := by
  induction n with
  | zero => exact S_zero γ μ u
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← ih, ← S_succ_snd]
    push_cast; rfl

/-- **Composition law** `S_j S_l = e^{2πiγ j₁ l₂} S_{j+l}` (paper §3, "Covariance of the
exact interaction"). -/
theorem S_comp (γ μ : ℝ) (j l : ℤ × ℤ) (u : ℝ × ℝ → ℂ) :
    S γ μ j (S γ μ l u) = e (γ * j.1 * l.2) • S γ μ (j + l) u := by
  funext x
  simp only [S, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← mul_assoc, ← e_add, ← e_add]
  push_cast
  congr 2
  · ring
  · congr 1 <;> ring

/-- `S_j^{-1} = e^{2πiγ j₁j₂} S_{-j}`. -/
theorem S_inv (γ μ : ℝ) (j : ℤ × ℤ) (u : ℝ × ℝ → ℂ) :
    S γ μ j (e (γ * j.1 * j.2) • S γ μ (-j) u) = u ∧
      e (γ * j.1 * j.2) • S γ μ (-j) (S γ μ j u) = u := by
  constructor
  · funext x
    simp only [S, Pi.smul_apply, smul_eq_mul, Prod.fst_neg, Prod.snd_neg, Int.cast_neg,
      ← mul_assoc, ← e_add]
    rw [← one_mul (u x)]
    congr 1
    · rw [← e_zero]; congr 1; ring
    · congr 1; ext <;> simp
  · funext x
    simp only [S, Pi.smul_apply, smul_eq_mul, Prod.fst_neg, Prod.snd_neg, Int.cast_neg,
      ← mul_assoc, ← e_add]
    rw [← one_mul (u x)]
    congr 1
    · rw [← e_zero]; congr 1; ring
    · congr 1; ext <;> simp

/-- Pointwise unitarity: `|S_m u(x)| = |u(x - (m₁μ, m₂))|`. -/
lemma norm_S (γ μ : ℝ) (m : ℤ × ℤ) (u : ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    ‖S γ μ m u x‖ = ‖u (x - ((m.1 : ℝ) * μ, (m.2 : ℝ)))‖ := by
  rw [show x - ((m.1 : ℝ) * μ, (m.2 : ℝ)) = (x.1 - m.1 * μ, x.2 - m.2) from
    Prod.ext (by simp) (by simp)]
  simp only [S, norm_mul, norm_e, one_mul]

/-- `S_m` preserves `∫ |u|²` (unitarity on `L²(ℝ²)`). -/
theorem integral_norm_sq_S (γ μ : ℝ) (m : ℤ × ℤ) (u : ℝ × ℝ → ℂ) :
    ∫ x, ‖S γ μ m u x‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 := by
  simp_rw [norm_S]
  exact MeasureTheory.integral_sub_right_eq_self (fun x => ‖u x‖ ^ 2) _

/-! ### Commutation with the magnetic Schrödinger expression

`H = (hD₁)² + (hD₂ - 𝓑x₁)² + V`, `D = -i∂`, written with the partial derivatives
`∂₁, ∂₂` of the partial maps and the kinetic momentum `π₂ = hD₂ - 𝓑x₁`. -/

/-- `∂₁ u`. -/
def d1 (u : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ := fun x => deriv (fun t : ℝ => u (t, x.2)) x.1

/-- `∂₂ u`. -/
def d2 (u : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ := fun x => deriv (fun t : ℝ => u (x.1, t)) x.2

/-- The kinetic momentum `π₂ u = -ih ∂₂u - 𝓑x₁u`. -/
def pi2 (B h : ℝ) (u : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  fun x => -I * h * d2 u x - B * x.1 * u x

/-- The magnetic Schrödinger expression `-h²∂₁²u + π₂²u + Vu`. -/
def schr (B h : ℝ) (V : ℝ × ℝ → ℝ) (u : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  fun x => -(h : ℂ) ^ 2 * d1 (d1 u) x + pi2 B h (pi2 B h u) x + V x * u x

lemma d1_T1 (μ B h : ℝ) (u : ℝ × ℝ → ℂ) : d1 (T1 μ B h u) = T1 μ B h (d1 u) := by
  funext x
  show deriv (fun t : ℝ => Complex.exp (((μ * B / h * x.2 : ℝ) : ℂ) * I) * u (t - μ, x.2)) x.1 =
    Complex.exp (((μ * B / h * x.2 : ℝ) : ℂ) * I) * deriv (fun t : ℝ => u (t, x.2)) (x.1 - μ)
  rw [deriv_const_mul_field']
  beta_reduce
  congr 1
  exact deriv_comp_sub_const (f := fun t : ℝ => u (t, x.2)) (a := μ) (x := x.1)

lemma hasDerivAt_T1_snd (μ B h : ℝ) (u : ℝ × ℝ → ℂ) (x : ℝ × ℝ)
    (hu : DifferentiableAt ℝ (fun t : ℝ => u (x.1 - μ, t)) x.2) :
    HasDerivAt (fun t : ℝ => T1 μ B h u (x.1, t))
      (((μ * B / h : ℝ) : ℂ) * I * T1 μ B h u x + T1 μ B h (d2 u) x) x.2 := by
  have h1 := ((((hasDerivAt_id' x.2).const_mul (μ * B / h)).ofReal_comp).mul_const I).cexp
  have h2 := h1.mul hu.hasDerivAt
  show HasDerivAt (fun t : ℝ => Complex.exp (((μ * B / h * t : ℝ) : ℂ) * I) * u (x.1 - μ, t)) _ x.2
  refine h2.congr_deriv ?_
  simp only [T1, d2, mul_one]
  ring

lemma d2_T1 (μ B h : ℝ) (u : ℝ × ℝ → ℂ) (x : ℝ × ℝ)
    (hu : DifferentiableAt ℝ (fun t : ℝ => u (x.1 - μ, t)) x.2) :
    d2 (T1 μ B h u) x = ((μ * B / h : ℝ) : ℂ) * I * T1 μ B h u x + T1 μ B h (d2 u) x :=
  (hasDerivAt_T1_snd μ B h u x hu).deriv

/-- `π₂ T₁ = T₁ π₂` (the gauge phase of `T₁` exactly compensates the shift of `𝓑x₁`). -/
theorem pi2_T1 {μ B h : ℝ} (hh : h ≠ 0) (u : ℝ × ℝ → ℂ)
    (hu : ∀ x : ℝ × ℝ, DifferentiableAt ℝ (fun t : ℝ => u (x.1, t)) x.2) :
    pi2 B h (T1 μ B h u) = T1 μ B h (pi2 B h u) := by
  funext x
  have hd := d2_T1 μ B h u x (hu (x.1 - μ, x.2))
  simp only [pi2]
  rw [hd]
  simp only [T1]
  simp only [pi2]
  have hh' : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh
  have hc : (h : ℂ) * ((μ * B / h : ℝ) : ℂ) = μ * B := by
    push_cast
    field_simp
  have hx : (((x.1 - μ : ℝ)) : ℂ) = x.1 - μ := by push_cast; ring
  rw [hx]
  linear_combination
    (Complex.exp (((μ * B / h * x.2 : ℝ) : ℂ) * I) * u (x.1 - μ, x.2)) * hc -
      ((h : ℂ) * ((μ * B / h : ℝ) : ℂ) * Complex.exp (((μ * B / h * x.2 : ℝ) : ℂ) * I) *
        u (x.1 - μ, x.2)) * I_sq

/-- **`T₁` commutes with the magnetic Schrödinger expression** when `V` is `μ`-periodic in
`x₁` and `u` is twice differentiable in `x₂` (the `x₁` part needs no regularity). -/
theorem schr_T1 {μ B h : ℝ} (hh : h ≠ 0) (V : ℝ × ℝ → ℝ)
    (hV : ∀ x : ℝ × ℝ, V (x.1 - μ, x.2) = V x) (u : ℝ × ℝ → ℂ)
    (hu : ∀ x : ℝ × ℝ, DifferentiableAt ℝ (fun t : ℝ => u (x.1, t)) x.2)
    (hu2 : ∀ x : ℝ × ℝ, DifferentiableAt ℝ (fun t : ℝ => d2 u (x.1, t)) x.2) :
    schr B h V (T1 μ B h u) = T1 μ B h (schr B h V u) := by
  have hp : ∀ x : ℝ × ℝ, DifferentiableAt ℝ (fun t : ℝ => pi2 B h u (x.1, t)) x.2 :=
    fun x => ((hu2 x).const_mul (-I * h)).sub ((hu x).const_mul ((B : ℂ) * x.1))
  funext x
  simp only [schr]
  rw [d1_T1, d1_T1, pi2_T1 hh u hu, pi2_T1 hh _ hp]
  simp only [T1]
  simp only [schr]
  rw [hV x]
  ring

lemma d1_T2 (u : ℝ × ℝ → ℂ) : d1 (T2 u) = T2 (d1 u) := rfl

lemma d2_T2 (u : ℝ × ℝ → ℂ) : d2 (T2 u) = T2 (d2 u) := by
  funext x
  exact deriv_comp_sub_const (f := fun t : ℝ => u (x.1, t)) (a := 1) (x := x.2)

lemma pi2_T2 (B h : ℝ) (u : ℝ × ℝ → ℂ) : pi2 B h (T2 u) = T2 (pi2 B h u) := by
  funext x
  show -I * h * d2 (T2 u) x - B * x.1 * T2 u x =
    -I * h * d2 u (x.1, x.2 - 1) - B * x.1 * u (x.1, x.2 - 1)
  rw [d2_T2]
  rfl

/-- **`T₂` commutes with the magnetic Schrödinger expression** when `V` is `1`-periodic in
`x₂` (no regularity needed). -/
theorem schr_T2 (B h : ℝ) (V : ℝ × ℝ → ℝ) (hV : ∀ x : ℝ × ℝ, V (x.1, x.2 - 1) = V x)
    (u : ℝ × ℝ → ℂ) : schr B h V (T2 u) = T2 (schr B h V u) := by
  funext x
  simp only [schr]
  rw [d1_T2, d1_T2, pi2_T2, pi2_T2]
  simp only [T2]
  simp only [schr]
  rw [hV x]

/-! ### 2. Covariance of the exact interaction  (`c-eq:magnetic-cocycle`, `c-eq:twisted-adjoint`)

Abstract setting: a complex inner product space `E` (the range of the island projection), a
projective representation `S : ℤ² → E` by isometries with `S_j S_l = e(γ j₁ l₂) S_{j+l}`
(proved above for the concrete translations), an operator `H` commuting with it, and the
equivariant basis `φ_m = S_m φ₀`.  The paper's `f_m = ⟨H φ_m, φ₀⟩` (linear in the first
slot) is Mathlib's `⟪φ₀, H φ_m⟫` (linear in the second slot). -/

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The exact interaction coefficient `f_m = ⟨H φ_m, φ₀⟩`, `φ_m = S_m φ₀`. -/
def coeff (Hop : E →ₗ[ℂ] E) (Sop : ℤ × ℤ → E →ₗᵢ[ℂ] E) (φ₀ : E) (m : ℤ × ℤ) : ℂ :=
  inner ℂ φ₀ (Hop (Sop m φ₀))

/-- **Magnetic cocycle** (paper `c-eq:magnetic-cocycle`):
`w_{jl} = ⟨Hφ_l, φ_j⟩ = e^{-2πiγ j₁(l₂-j₂)} f_{l-j}`. -/
theorem magnetic_cocycle (γ : ℝ) (Sop : ℤ × ℤ → E →ₗᵢ[ℂ] E) (Hop : E →ₗ[ℂ] E)
    (hS : ∀ j l v, Sop j (Sop l v) = e (γ * j.1 * l.2) • Sop (j + l) v)
    (hH : ∀ j v, Hop (Sop j v) = Sop j (Hop v)) (φ₀ : E) (j l : ℤ × ℤ) :
    inner ℂ (Sop j φ₀) (Hop (Sop l φ₀)) =
      e (-(γ * j.1 * (l.2 - j.2))) * coeff Hop Sop φ₀ (l - j) := by
  have h1 : Sop l φ₀ = e (-(γ * j.1 * (l.2 - j.2))) • Sop j (Sop (l - j) φ₀) := by
    rw [hS, smul_smul, ← e_add, add_sub_cancel]
    have : -(γ * j.1 * (l.2 - j.2)) + γ * j.1 * ((l - j).2 : ℤ) = 0 := by
      simp only [Prod.snd_sub, Int.cast_sub]; ring
    rw [this, e_zero, one_smul]
  rw [h1, map_smul, hH, inner_smul_right, LinearIsometry.inner_map_map]
  rfl

lemma S_zero_eq (γ : ℝ) (Sop : ℤ × ℤ → E →ₗᵢ[ℂ] E)
    (hS : ∀ j l v, Sop j (Sop l v) = e (γ * j.1 * l.2) • Sop (j + l) v) (v : E) :
    Sop 0 v = v := by
  apply (Sop 0).injective
  rw [hS]
  simp

/-- **Twisted adjoint relation** (paper `c-eq:twisted-adjoint`):
`f_{-r,-q} = e^{-2πiγrq} \overline{f_{r,q}}` for a symmetric `H`. -/
theorem twisted_adjoint (γ : ℝ) (Sop : ℤ × ℤ → E →ₗᵢ[ℂ] E) (Hop : E →ₗ[ℂ] E)
    (hS : ∀ j l v, Sop j (Sop l v) = e (γ * j.1 * l.2) • Sop (j + l) v)
    (hH : ∀ j v, Hop (Sop j v) = Sop j (Hop v))
    (hsym : ∀ a b, inner ℂ (Hop a) b = inner ℂ a (Hop b)) (φ₀ : E) (j : ℤ × ℤ) :
    coeff Hop Sop φ₀ (-j) = e (-(γ * j.1 * j.2)) * conj (coeff Hop Sop φ₀ j) := by
  have hc := magnetic_cocycle γ Sop Hop hS hH φ₀ j 0
  rw [S_zero_eq γ Sop hS, ← hsym, ← inner_conj_symm, zero_sub] at hc
  unfold coeff
  rw [hc, ← mul_assoc, ← e_add]
  simp only [Prod.snd_zero, Int.cast_zero, zero_sub]
  rw [show -(γ * j.1 * j.2) + -(γ * j.1 * -(j.2 : ℝ)) = 0 by ring, e_zero, one_mul]
  rfl

/-- **Rotation covariance of the coefficients** (Corollary `c-cor:critical`, first identity):
if the magnetic rotation `𝓡` commutes with `H`, satisfies
`𝓡 S_{(r,q)} = e^{-2πiγrq} S_{(q,-r)} 𝓡` (`c-eq:rotation-covariance`) and `𝓡φ₀ = cφ₀` with
`|c| = 1`, then `f_{r,q} = e^{-2πiγrq} f_{q,-r}`. -/
theorem rotation_coefficients (γ : ℝ) (Sop : ℤ × ℤ → E →ₗᵢ[ℂ] E) (Hop : E →ₗ[ℂ] E)
    (Rot : E →ₗᵢ[ℂ] E) (hRH : ∀ v, Rot (Hop v) = Hop (Rot v))
    (hRS : ∀ (r q : ℤ) v, Rot (Sop (r, q) v) = e (-(γ * r * q)) • Sop (q, -r) (Rot v))
    (φ₀ : E) (c : ℂ) (hc : ‖c‖ = 1) (hRφ : Rot φ₀ = c • φ₀) (r q : ℤ) :
    coeff Hop Sop φ₀ (r, q) = e (-(γ * r * q)) * coeff Hop Sop φ₀ (q, -r) := by
  have hcc : conj c * c = 1 := by rw [Complex.conj_mul', hc]; simp
  unfold coeff
  rw [← LinearIsometry.inner_map_map Rot, hRH, hRS, hRφ, map_smul, map_smul, map_smul,
    inner_smul_left, inner_smul_right, inner_smul_right]
  rw [show ∀ a b : ℂ, conj c * (a * (c * b)) = (conj c * c) * (a * b) from fun a b => by ring,
    hcc, one_mul]

end Abstract

/-! ### Coefficient symmetries at the symbol level -/

/-- The twisted adjoint relation `f_{-p} = e^{-2πiγ p₁p₂} \overline{f_p}` on a coefficient
function (paper `c-eq:twisted-adjoint`). -/
def TwistedAdjoint (γ : ℝ) (f : Symbol) : Prop :=
  ∀ p : ℤ × ℤ, f (-p) = e (-(γ * p.1 * p.2)) * conj (f p)

/-- The rotation relation `f_{r,q} = e^{-2πiγrq} f_{q,-r}` (paper
`c-eq:rotation-coefficients`). -/
def RotationCovariant (γ : ℝ) (f : Symbol) : Prop :=
  ∀ r q : ℤ, f (r, q) = e (-(γ * r * q)) * f (q, -r)

lemma norm_weylSymbol (γ : ℝ) (f : Symbol) (p : ℤ × ℤ) : ‖weylSymbol γ f p‖ = ‖f p‖ := by
  simp [weylSymbol]

lemma wnorm_weylSymbol (γ s ℓ : ℝ) (f : Symbol) : wnorm s ℓ (weylSymbol γ f) = wnorm s ℓ f := by
  simp only [wnorm, norm_weylSymbol]

lemma summable_weylSymbol {f : Symbol} (hf : SymbolSummable f) (γ : ℝ) :
    SymbolSummable (weylSymbol γ f) :=
  (hf : Summable fun p => ‖f p‖).congr fun p => (norm_weylSymbol γ f p).symm

/-- **Hermiticity of the Weyl symbol**: the twisted adjoint relation for the exact
coefficients is exactly self-adjointness `c_{-p} = \overline{c_p}` of
`c_{r,q} = e^{πiγrq} f_{r,q}`. -/
theorem weylSymbol_selfAdjoint {γ : ℝ} {f : Symbol} (h : TwistedAdjoint γ f) :
    SymbolSelfAdjoint (weylSymbol γ f) := by
  intro p
  simp only [weylSymbol, Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
  rw [h p, map_mul, conj_e, ← mul_assoc, ← e_add]
  congr 2
  ring

/-- The converse: self-adjointness of the Weyl symbol gives the twisted adjoint relation. -/
theorem twistedAdjoint_of_selfAdjoint {γ : ℝ} {f : Symbol}
    (h : SymbolSelfAdjoint (weylSymbol γ f)) : TwistedAdjoint γ f := by
  intro p
  have hp := h p
  simp only [weylSymbol, Prod.fst_neg, Prod.snd_neg, Int.cast_neg, map_mul, conj_e] at hp
  have : f (-p) = e (-(γ * -(p.1 : ℝ) * -(p.2 : ℝ) / 2)) * (e (-(γ * p.1 * p.2 / 2)) * conj (f p)) := by
    rw [← hp, ← mul_assoc, ← e_add, neg_add_cancel, e_zero, one_mul]
  rw [this, ← mul_assoc, ← e_add]
  congr 2
  ring

/-- Axial consequences of the twisted adjoint relation: `f_{-1,0} = \overline{f_{1,0}}`,
`f_{0,-1} = \overline{f_{0,1}}`, `f_{0,0} ∈ ℝ`. -/
lemma TwistedAdjoint.axial {γ : ℝ} {f : Symbol} (h : TwistedAdjoint γ f) :
    f (-1, 0) = conj (f (1, 0)) ∧ f (0, -1) = conj (f (0, 1)) ∧ conj (f 0) = f 0 := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using h (1, 0)
  · simpa using h (0, 1)
  · have := h 0
    simp only [neg_zero, Prod.fst_zero, Prod.snd_zero, Int.cast_zero, mul_zero,
      e_zero, one_mul] at this
    exact this.symm

/-- In Weyl normalization the rotation identity reads `c_{r,q} = c_{q,-r}`. -/
lemma weylSymbol_rot {γ : ℝ} {f : Symbol} (h : RotationCovariant γ f) (r q : ℤ) :
    weylSymbol γ f (r, q) = weylSymbol γ f (q, -r) := by
  simp only [weylSymbol]
  rw [h r q, ← mul_assoc, ← e_add]
  congr 2
  push_cast
  ring

/-- **Corollary `c-cor:critical` (Fourier self-duality).** If
`f(r,q) = e(-γrq) f(q,-r)`, then the Weyl symbol is invariant under the Fourier automorphism
`𝓕(W_{r,q}) = W_{q,-r}`, i.e. `(𝓕c)_{r',q'} = c_{-q',r'}` equals `c`. -/
theorem fourier_weylSymbol {γ : ℝ} {f : Symbol} (h : RotationCovariant γ f) :
    AMO.fourier (weylSymbol γ f) = weylSymbol γ f := by
  funext p
  obtain ⟨a, b⟩ := p
  show weylSymbol γ f (-b, a) = weylSymbol γ f (a, b)
  rw [weylSymbol_rot h (-b) a, neg_neg]

/-- **Corollary `c-cor:critical` (axial values).** `f_{1,0} = f_{0,1}`. -/
theorem axial_eq {γ : ℝ} {f : Symbol} (h : RotationCovariant γ f) : f (1, 0) = f (0, 1) := by
  have := h 0 1
  simp only [Int.cast_zero, Int.cast_one, mul_zero, zero_mul, neg_zero, e_zero, one_mul] at this
  exact this.symm

/-- **Corollary `c-cor:critical` (reality).** With the twisted adjoint relation, every Weyl
coefficient is real, `f_{1,0} = f_{0,1} ∈ ℝ`, and hence `t₁ = t₂`. -/
theorem critical_real {γ : ℝ} {f : Symbol} (h : RotationCovariant γ f)
    (hsa : TwistedAdjoint γ f) :
    (∀ p, conj (weylSymbol γ f p) = weylSymbol γ f p) ∧ conj (f (1, 0)) = f (1, 0) ∧
      ‖f (1, 0)‖ = ‖f (0, 1)‖ := by
  have hF := fourier_weylSymbol h
  refine ⟨fun p => ?_, ?_, by rw [axial_eq h]⟩
  · rw [← weylSymbol_selfAdjoint hsa p]
    have := congrFun (congrArg AMO.fourier hF) p
    rw [AMO.fourier_fourier, hF] at this
    exact this
  · have h1 : f (1, 0) = f (0, -1) := by
      have := h 1 0
      simpa using this
    have h2 : f (1, 0) = conj (f (0, 1)) := h1.trans hsa.axial.2.1
    rw [← axial_eq h] at h2
    exact h2.symm

/-! ### 3. Normalization and orientation  (paper (2.9)–(2.10), §4.1, `eq:continuum-oriented`) -/

/-- A symbol with on-site energy `E₀`, axial hoppings `t₁, t₂` and remainder `R`:
`c = E₀δ₀ + t₁(δ_{e₁} + δ_{-e₁}) + t₂(δ_{e₂} + δ_{-e₂}) + R`. -/
def axialSymbol (E₀ t₁ t₂ : ℝ) (R : Symbol) : Symbol :=
  Pi.single 0 (E₀ : ℂ) + (t₁ : ℂ) • (Pi.single (1, 0) 1 + Pi.single (-1, 0) 1) +
    (t₂ : ℂ) • (Pi.single (0, 1) 1 + Pi.single (0, -1) 1) + R

lemma single_apply_eq_mul (q p : ℤ × ℤ) (a : ℂ) :
    (Pi.single q a : Symbol) p = a * (Pi.single q 1 : Symbol) p := by
  by_cases h : p = q
  · subst h; simp
  · simp [Pi.single_eq_of_ne h]

lemma axialSymbol_eq {E₀ t₁ t₂ : ℝ} (ht₁ : t₁ ≠ 0) (R : Symbol) :
    axialSymbol E₀ t₁ t₂ R =
      Pi.single 0 (E₀ : ℂ) + (t₁ : ℂ) • (amo ((t₂ / t₁ : ℝ) : ℂ) + ((1 / t₁ : ℝ) : ℂ) • R) := by
  have h1 : (t₁ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht₁
  funext p
  simp only [axialSymbol, amo, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [single_apply_eq_mul (0, 1) p ((t₂ / t₁ : ℝ) : ℂ),
    single_apply_eq_mul (0, -1) p ((t₂ / t₁ : ℝ) : ℂ)]
  push_cast
  field_simp
  ring

/-- **Subcritical normalization** (`t₁ > t₂`): `(c - E₀δ₀)/t₁ = H_{t₂/t₁} + R/t₁`. -/
theorem normalized_sub {E₀ t₁ t₂ : ℝ} (ht₁ : t₁ ≠ 0) (R : Symbol) :
    ((1 / t₁ : ℝ) : ℂ) • (axialSymbol E₀ t₁ t₂ R - Pi.single 0 (E₀ : ℂ)) =
      amo ((t₂ / t₁ : ℝ) : ℂ) + ((1 / t₁ : ℝ) : ℂ) • R := by
  rw [axialSymbol_eq ht₁, add_sub_cancel_left, smul_smul, ← Complex.ofReal_mul,
    one_div_mul_cancel ht₁, Complex.ofReal_one, one_smul]

/-- The inverse Fourier automorphism `𝓕⁻¹ = 𝓕³`, `(𝓕⁻¹R)_{r,q} = R_{q,-r}`. -/
def fourierInv (R : Symbol) : Symbol := AMO.fourier (AMO.fourier (AMO.fourier R))

lemma fourierInv_eq_iterate (R : Symbol) : fourierInv R = AMO.fourier^[3] R := rfl

lemma fourierInv_apply (R : Symbol) (p : ℤ × ℤ) : fourierInv R p = R (p.2, -p.1) := by
  simp [fourierInv, AMO.fourier]

lemma fourierSym_smul (a : ℂ) (R : Symbol) : AMO.fourier (a • R) = a • AMO.fourier R := rfl

lemma fourierInv_fourier (R : Symbol) : fourierInv (AMO.fourier R) = R := AMO.fourier_four R

lemma fourierSym_fourierInv (R : Symbol) : AMO.fourier (fourierInv R) = R := AMO.fourier_four R

/-- `‖𝓕⁻¹R‖_{s,ℓ} = ‖R‖_{ℓ,s}`. -/
lemma wnorm_fourierInv (s ℓ : ℝ) (R : Symbol) : wnorm s ℓ (fourierInv R) = wnorm ℓ s R := by
  unfold fourierInv
  rw [wnorm_fourier, wnorm_fourier, wnorm_fourier]

lemma wnorm_smul (s ℓ : ℝ) (a : ℂ) (R : Symbol) : wnorm s ℓ (a • R) = ‖a‖ * wnorm s ℓ R := by
  unfold wnorm
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
  exact tsum_mul_left

lemma axialSymbol_eq' {E₀ t₁ t₂ : ℝ} (ht₁ : t₁ ≠ 0) (ht₂ : t₂ ≠ 0) (R : Symbol) :
    axialSymbol E₀ t₁ t₂ R =
      Pi.single 0 (E₀ : ℂ) +
        (t₂ : ℂ) • (AMO.fourier (amo ((t₁ / t₂ : ℝ) : ℂ)) + ((1 / t₂ : ℝ) : ℂ) • R) := by
  have h1 : (t₁ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht₁
  have h2 : (t₂ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht₂
  have hη : ((t₁ / t₂ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (div_ne_zero ht₁ ht₂)
  rw [AMO.fourier_amo hη]
  funext p
  simp only [axialSymbol, amo, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [single_apply_eq_mul (0, 1) p ((t₁ / t₂ : ℝ) : ℂ)⁻¹,
    single_apply_eq_mul (0, -1) p ((t₁ / t₂ : ℝ) : ℂ)⁻¹]
  push_cast
  field_simp
  ring

/-- **Supercritical orientation** (`t₂ > t₁`, paper `eq:continuum-oriented`):
`𝓕⁻¹((c - E₀δ₀)/t₂) = H_{t₁/t₂} + 𝓕⁻¹(R)/t₂`. -/
theorem normalized_super {E₀ t₁ t₂ : ℝ} (ht₁ : t₁ ≠ 0) (ht₂ : t₂ ≠ 0) (R : Symbol) :
    fourierInv (((1 / t₂ : ℝ) : ℂ) • (axialSymbol E₀ t₁ t₂ R - Pi.single 0 (E₀ : ℂ))) =
      amo ((t₁ / t₂ : ℝ) : ℂ) + ((1 / t₂ : ℝ) : ℂ) • fourierInv R := by
  rw [axialSymbol_eq' ht₁ ht₂, add_sub_cancel_left, smul_smul, ← Complex.ofReal_mul,
    one_div_mul_cancel ht₂, Complex.ofReal_one, one_smul]
  unfold fourierInv
  rw [AMO.fourier_add, AMO.fourier_add, AMO.fourier_add, AMO.fourier_four, fourierSym_smul,
    fourierSym_smul, fourierSym_smul]

/-- The physical normalized family is the Fourier dual of the subcritical one:
`(c - E₀δ₀)/t₂ = 𝓕(K^{sub})`, `K^{sub} = H_{t₁/t₂} + 𝓕⁻¹(R)/t₂`. -/
theorem normalized_phys_eq_fourier {E₀ t₁ t₂ : ℝ} (ht₁ : t₁ ≠ 0) (ht₂ : t₂ ≠ 0) (R : Symbol) :
    axialSymbol E₀ t₁ t₂ R = Pi.single 0 (E₀ : ℂ) +
      (t₂ : ℂ) • AMO.fourier (amo ((t₁ / t₂ : ℝ) : ℂ) + ((1 / t₂ : ℝ) : ℂ) • fourierInv R) := by
  rw [axialSymbol_eq' ht₁ ht₂, AMO.fourier_add, fourierSym_smul, fourierSym_fourierInv]

/-- The weighted norm of the oriented remainder (paper §4.1):
`‖t₂⁻¹𝓕⁻¹R‖_{s,ℓ} = t₂⁻¹‖R‖_{ℓ,s}`. -/
lemma wnorm_oriented (s ℓ : ℝ) {t₂ : ℝ} (ht₂ : 0 < t₂) (R : Symbol) :
    wnorm s ℓ (((1 / t₂ : ℝ) : ℂ) • fourierInv R) = (1 / t₂) * wnorm ℓ s R := by
  rw [wnorm_smul, wnorm_fourierInv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity)]

/-! #### Operator level -/

lemma W_zero_zero (α x : ℝ) : W α x 0 0 = 1 := by
  ext u n
  simp [W_apply]

lemma summable_smul {R : Symbol} (h : SymbolSummable R) (a : ℂ) :
    SymbolSummable (a • R) := by
  unfold SymbolSummable
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
  exact h.mul_left _

lemma op_smul (α : ℝ) (a : ℂ) (R : Symbol) (x : ℝ) : op α (a • R) x = a • op α R x := by
  unfold op
  simp_rw [Pi.smul_apply, smul_eq_mul, mul_smul]
  exact tsum_const_smul'' a

lemma op_single_add {α : ℝ} (E₀ : ℂ) {K : Symbol} (hK : SymbolSummable K) (t : ℂ) (x : ℝ) :
    op α (Pi.single 0 E₀ + t • K) x = E₀ • 1 + t • op α K x := by
  rw [op_add (symbolSummable_single _ _) (summable_smul hK t), op_single, op_smul, Prod.fst_zero,
    Prod.snd_zero, W_zero_zero]

/-- **Operator form of the subcritical normalization**:
`op c = E₀ + t₁ · op(H_{t₂/t₁} + R/t₁)`. -/
theorem op_axial_sub (α : ℝ) {E₀ t₁ t₂ : ℝ} (ht₁ : t₁ ≠ 0) {R : Symbol} (hR : SymbolSummable R)
    (x : ℝ) :
    op α (axialSymbol E₀ t₁ t₂ R) x =
      (E₀ : ℂ) • 1 + (t₁ : ℂ) • op α (amo ((t₂ / t₁ : ℝ) : ℂ) + ((1 / t₁ : ℝ) : ℂ) • R) x := by
  rw [axialSymbol_eq ht₁]
  exact op_single_add _ ((amo_summable _).add (summable_smul hR _)) _ x

/-- **Operator form of the supercritical orientation**:
`op c = E₀ + t₂ · op(𝓕(H_{t₁/t₂} + 𝓕⁻¹R/t₂))`. -/
theorem op_axial_super (α : ℝ) {E₀ t₁ t₂ : ℝ} (ht₁ : t₁ ≠ 0) (ht₂ : t₂ ≠ 0) {R : Symbol}
    (hR : SymbolSummable R) (x : ℝ) :
    op α (axialSymbol E₀ t₁ t₂ R) x =
      (E₀ : ℂ) • 1 + (t₂ : ℂ) •
        op α (AMO.fourier (amo ((t₁ / t₂ : ℝ) : ℂ) + ((1 / t₂ : ℝ) : ℂ) • fourierInv R)) x := by
  rw [normalized_phys_eq_fourier ht₁ ht₂]
  refine op_single_add _ (SymbolSummable.fourier ?_) _ x
  exact (amo_summable _).add (summable_smul hR.fourier.fourier.fourier _)

/-- The spectrum of `E₀ + tA` is the affine image `E₀ + t·σ(A)`. -/
theorem spectrum_affine (A : L2 ℤ →L[ℂ] L2 ℤ) (E₀ t : ℝ) (ht : t ≠ 0) :
    spectrum ℂ ((E₀ : ℂ) • (1 : L2 ℤ →L[ℂ] L2 ℤ) + (t : ℂ) • A) =
      (fun z => (E₀ : ℂ) + t * z) '' spectrum ℂ A := by
  have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht
  rw [← Algebra.algebraMap_eq_smul_one, ← spectrum.singleton_add_eq,
    show (t : ℂ) • A = (Units.mk0 (t : ℂ) ht') • A from rfl, spectrum.unit_smul_eq_smul,
    Set.singleton_add, ← Set.image_smul, Set.image_image]
  congr 1

/-- **The island spectrum is the affine image `E₀ + t_max Σ_norm`** (subcritical orientation). -/
theorem spectrum_op_axial_sub (α : ℝ) {E₀ t₁ t₂ : ℝ} (ht₁ : t₁ ≠ 0) {R : Symbol}
    (hR : SymbolSummable R) (x : ℝ) :
    spectrum ℂ (op α (axialSymbol E₀ t₁ t₂ R) x) = (fun z => (E₀ : ℂ) + t₁ * z) ''
      spectrum ℂ (op α (amo ((t₂ / t₁ : ℝ) : ℂ) + ((1 / t₁ : ℝ) : ℂ) • R) x) := by
  rw [op_axial_sub α ht₁ hR, spectrum_affine _ _ _ ht₁]

/-- **The island spectrum is the affine image `E₀ + t_max Σ_norm`** (supercritical orientation,
the normalized operator being the Fourier dual of the subcritical one). -/
theorem spectrum_op_axial_super (α : ℝ) {E₀ t₁ t₂ : ℝ} (ht₁ : t₁ ≠ 0) (ht₂ : t₂ ≠ 0)
    {R : Symbol} (hR : SymbolSummable R) (x : ℝ) :
    spectrum ℂ (op α (axialSymbol E₀ t₁ t₂ R) x) = (fun z => (E₀ : ℂ) + t₂ * z) ''
      spectrum ℂ (op α (AMO.fourier (amo ((t₁ / t₂ : ℝ) : ℂ) + ((1 / t₂ : ℝ) : ℂ) • fourierInv R))
        x) := by
  rw [op_axial_super α ht₁ ht₂ hR, spectrum_affine _ _ _ ht₂]

/-! ### 4. Gauge of the axial phases  (paper §4.1) -/

/-- Multiplication of a symbol by the character `p ↦ e(θ₁p₁ + θ₂p₂)`. -/
def modulate (θ₁ θ₂ : ℝ) (c : Symbol) : Symbol := fun p => e (θ₁ * p.1 + θ₂ * p.2) * c p

lemma norm_modulate (θ₁ θ₂ : ℝ) (c : Symbol) (p : ℤ × ℤ) : ‖modulate θ₁ θ₂ c p‖ = ‖c p‖ := by
  simp [modulate]

/-- The character preserves the analytic norms. -/
lemma wnorm_modulate (θ₁ θ₂ s ℓ : ℝ) (c : Symbol) :
    wnorm s ℓ (modulate θ₁ θ₂ c) = wnorm s ℓ c := by
  simp only [wnorm, norm_modulate]

lemma summable_modulate {c : Symbol} (h : SymbolSummable c) (θ₁ θ₂ : ℝ) :
    SymbolSummable (modulate θ₁ θ₂ c) :=
  (h : Summable fun p => ‖c p‖).congr fun p => (norm_modulate θ₁ θ₂ c p).symm

/-- The character preserves self-adjointness (real `θ`). -/
lemma selfAdjoint_modulate {c : Symbol} (h : SymbolSelfAdjoint c) (θ₁ θ₂ : ℝ) :
    SymbolSelfAdjoint (modulate θ₁ θ₂ c) := by
  intro p
  simp only [modulate, Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
  rw [h p, map_mul, conj_e]
  congr 2
  ring

lemma weylSymbol_modulate (γ θ₁ θ₂ : ℝ) (f : Symbol) :
    weylSymbol γ (modulate θ₁ θ₂ f) = modulate θ₁ θ₂ (weylSymbol γ f) := by
  funext p
  simp only [weylSymbol, modulate]
  ring

/-- Removing the axial phases: if `f(1,0) = t₁e(φ₁)`, `f(0,1) = t₂e(φ₂)`, the gauged
coefficients `f' = e(-φ₁r - φ₂q) f` have `f'(1,0) = t₁`, `f'(0,1) = t₂`. -/
lemma modulate_axial {f : Symbol} {t₁ t₂ φ₁ φ₂ : ℝ} (h₁ : f (1, 0) = t₁ * e φ₁)
    (h₂ : f (0, 1) = t₂ * e φ₂) :
    modulate (-φ₁) (-φ₂) f (1, 0) = t₁ ∧ modulate (-φ₁) (-φ₂) f (0, 1) = t₂ := by
  constructor
  · simp only [modulate, h₁, Int.cast_one, Int.cast_zero, mul_one, mul_zero, add_zero]
    rw [mul_left_comm, ← e_add, neg_add_cancel, e_zero, mul_one]
  · simp only [modulate, h₂, Int.cast_one, Int.cast_zero, mul_one, mul_zero, zero_add]
    rw [mul_left_comm, ← e_add, neg_add_cancel, e_zero, mul_one]

/-- The diagonal unitary `(D_θ u)_n = e(-θn) u_n` (a weighted shift with the identity
permutation). -/
def gaugeD (θ : ℝ) : L2 ℤ →L[ℂ] L2 ℤ := diagOp (fun n : ℤ => e (-(θ * n)))

lemma gaugeD_apply (θ : ℝ) (u : L2 ℤ) (n : ℤ) : gaugeD θ u n = e (-(θ * n)) * u n :=
  diagOp_apply (bdd_e _) u n

lemma gaugeD_comp_gaugeD_neg (θ : ℝ) : gaugeD θ ∘L gaugeD (-θ) = 1 := by
  ext u n
  rw [ContinuousLinearMap.comp_apply, gaugeD_apply, gaugeD_apply, ← mul_assoc, ← e_add,
    show -(θ * n) + -(-θ * n) = 0 by ring, e_zero, one_mul]
  rfl

lemma star_gaugeD (θ : ℝ) : star (gaugeD θ) = gaugeD (-θ) := by
  rw [gaugeD, star_diagOp (bdd_e _)]
  unfold gaugeD diagOp
  exact weightedShift_congr (fun n => by rw [conj_e]; congr 1; ring) (fun n => rfl)

/-- The gauge unitary is unitary. -/
lemma gaugeD_mem_unitary (θ : ℝ) : gaugeD θ ∈ unitary (L2 ℤ →L[ℂ] L2 ℤ) := by
  rw [Unitary.mem_iff, star_gaugeD]
  refine ⟨?_, ?_⟩
  · have := gaugeD_comp_gaugeD_neg (-θ)
    rw [neg_neg] at this
    exact this
  · exact gaugeD_comp_gaugeD_neg θ

/-- Single generator: `D_{θ₁} W_{r,q}(x+θ₂) D_{θ₁}^{-1} = e(θ₁r + θ₂q) W_{r,q}(x)`. -/
theorem gauge_W (α x θ₁ θ₂ : ℝ) (r q : ℤ) :
    gaugeD θ₁ ∘L W α (x + θ₂) r q ∘L gaugeD (-θ₁) = e (θ₁ * r + θ₂ * q) • W α x r q := by
  ext u n
  simp only [ContinuousLinearMap.comp_apply, gaugeD_apply, W_apply,
    smul_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  simp only [← mul_assoc, ← e_add]
  congr 2
  push_cast
  ring

/-- **Gauge covariance of Weyl series**: multiplying the symbol by the character
`e(θ₁r + θ₂q)` is the unitary conjugation by `D_{θ₁}` combined with the phase translation
`x ↦ x + θ₂`: `op(e(θ·)c)(x) = D_{θ₁} op(c)(x+θ₂) D_{θ₁}^{-1}`. -/
theorem op_modulate (α : ℝ) {c : Symbol} (hc : SymbolSummable c) (θ₁ θ₂ x : ℝ) :
    op α (modulate θ₁ θ₂ c) x = gaugeD θ₁ ∘L op α c (x + θ₂) ∘L gaugeD (-θ₁) := by
  refine ContinuousLinearMap.ext fun u => ?_
  have key : ∀ p : ℤ × ℤ, gaugeD θ₁ (W α (x + θ₂) p.1 p.2 (gaugeD (-θ₁) u)) =
      e (θ₁ * p.1 + θ₂ * p.2) • W α x p.1 p.2 u := fun p => by
    have := DFunLike.congr_fun (gauge_W α x θ₁ θ₂ p.1 p.2) u
    exact this
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    op_apply (summable_modulate hc _ _), op_apply hc,
    (gaugeD θ₁).map_tsum (summable_op_apply hc _ _)]
  congr 1
  funext p
  rw [map_smul, key, smul_smul, mul_comm]
  rfl

/-! ### 5. Guiding-centre orientation  (paper §5, lines 256–268) -/

/-- `(U,V) = (G_{e₁}, G_{e₂})` obeys `UV = e(α) VU`. -/
theorem guiding_UV_e1 (α : ℝ) :
    W2 α 1 0 ∘L W2 α 0 1 = e α • (W2 α 0 1 ∘L W2 α 1 0) := by
  rw [W2_mul, W2_mul, smul_smul, ← e_add]
  have h1 : ((1 : ℤ) + 0) = 0 + 1 := by norm_num
  have h2 : ((0 : ℤ) + 1) = 1 + 0 := by norm_num
  rw [h1, h2]
  congr 2
  push_cast
  ring

/-- The rotated orientation `(U,V) = (G_{e₂}, G_{-e₁})` (used when `a_y > a_x`) obeys the same
relation `UV = e(α) VU`. -/
theorem guiding_UV_e2 (α : ℝ) :
    W2 α 0 1 ∘L W2 α (-1) 0 = e α • (W2 α (-1) 0 ∘L W2 α 0 1) := by
  rw [W2_mul, W2_mul, smul_smul, ← e_add]
  have h1 : ((0 : ℤ) + -1) = -1 + 0 := by norm_num
  have h2 : ((1 : ℤ) + 0) = 0 + 1 := by norm_num
  rw [h1, h2]
  congr 2
  push_cast
  ring

/-- The Fourier series `W(x,y) = Σ ŵ(m) e^{2πi(m₁x + m₂y)}` (pointwise `tsum`). -/
def fseries (w : ℤ × ℤ → ℂ) (x y : ℝ) : ℂ := ∑' m : ℤ × ℤ, w m * e (m.1 * x + m.2 * y)

/-- Rotation invariance of the coefficients, `ŵ(m₂,-m₁) = ŵ(m₁,m₂)`, is exactly
`𝓕`-invariance of the coefficient symbol. -/
theorem rot_invariant_iff (w : ℤ × ℤ → ℂ) :
    (∀ m : ℤ × ℤ, w (m.2, -m.1) = w m) ↔ AMO.fourier w = w := by
  constructor
  · intro hw
    funext p
    show w (-p.2, p.1) = w p
    simpa using (hw (-p.2, p.1)).symm
  · intro h m
    simpa [AMO.fourier] using (congrFun h (m.2, -m.1)).symm

/-- Rotation-invariant coefficients give a rotation-invariant series `W(-y,x) = W(x,y)`
(no summability needed: the reindexing is a bijection of `ℤ²`). -/
theorem fseries_rot {w : ℤ × ℤ → ℂ} (hw : ∀ m : ℤ × ℤ, w (m.2, -m.1) = w m) (x y : ℝ) :
    fseries w (-y) x = fseries w x y := by
  let σ : ℤ × ℤ ≃ ℤ × ℤ :=
    { toFun := fun p => (-p.2, p.1), invFun := fun p => (p.2, -p.1),
      left_inv := fun p => by simp, right_inv := fun p => by simp }
  unfold fseries
  rw [← σ.tsum_eq]
  congr 1
  funext m
  obtain ⟨a, b⟩ := m
  simp only [σ, Equiv.coe_fn_mk]
  rw [show w (-b, a) = w (a, b) from (by simpa using hw (-b, a) : w (a, b) = w (-b, a)).symm]
  congr 2
  push_cast
  ring

end CMS
