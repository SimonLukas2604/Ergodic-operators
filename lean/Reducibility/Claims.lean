/-
# Reducibility of analytic one-frequency cocycles: definitions and the cited theorems

(Paper I, §"Rotations reducibility for every irrational frequency", Lemmas `t-lem:reducibility`
and `t-lem:arithmetic-reducibility`.)

This file defines

* analytic `SL(2,ℝ)` cocycles on a strip `|Im z| < h` (`AnalyticCocycle`), their restrictions to
  horizontal lines, and **subcriticality** `L(α, A(· + iy)) = 0` for `|y| < h`;
* the **fibered rotation number** through a continuous lift of the projective action
  (`IsRotationNumber`);
* **almost reducibility**, **rotations reducibility** and **reducibility to a constant rotation**,

and states, as named propositions (never asserted), the three cocycle theorems that Paper I cites:

* `AlmostReducibilityClaim` — Avila, *Almost reducibility and absolute continuity I*, Thm 1
  (the almost reducibility conjecture): subcritical ⇒ almost reducible;
* `RotationsReducibilityClaim` — Avila, Corollary 1.5 and Theorem 1.4 of the ARAC paper, with
  Avila–Fayad–Krikorian Theorem 1.3: an almost reducible cocycle whose rotation number lies in a
  full-measure set is analytically conjugate, by a degree-zero map, to a variable rotation;
* `ArithmeticReducibilityClaim` — Ge–Jitomirskaya, Theorem 9.2, Remark 9.1, Appendix B:
  subcritical on `|y| < h` with `2πh > β(α)` and `ρ ∈ Θ_α` ⇒ analytically reducible to a
  constant rotation.
-/
import AnalyticPerturbationsAMO.Spectral
import Reducibility.Basic
import Reducibility.Diophantine

noncomputable section

open scoped Matrix.Norms.Operator
open MeasureTheory Set Filter AMO

namespace Red

/-! ### Analytic cocycles -/

/-- An analytic `SL(2,ℝ)` cocycle on the strip `|Im z| < h`: holomorphic, `1`-periodic, real on
the real axis, with determinant one. -/
structure AnalyticCocycle (h : ℝ) where
  A : ℂ → M2
  analytic : ∀ i j, AnalyticOnNhd ℂ (fun z => A z i j) (strip h)
  periodic : ∀ z, A (z + 1) = A z
  real : ∀ (x : ℝ) i j, (starRingEnd ℂ) (A x i j) = A x i j
  det_eq_one : ∀ z ∈ strip h, (A z).det = 1

namespace AnalyticCocycle

variable {h : ℝ}

/-- The cocycle on the horizontal line `Im z = y`: `x ↦ A(x + iy)`. -/
def line (C : AnalyticCocycle h) (y : ℝ) : ℝ → M2 := fun x => C.A (x + y * Complex.I)

/-- The cocycle on the real axis. -/
def real' (C : AnalyticCocycle h) : ℝ → M2 := C.line 0

end AnalyticCocycle

/-- **Subcriticality** on the strip `|Im z| < h`: `L(α, A(· + iy)) = 0` for every `|y| < h`. -/
def SubcriticalOn (α : ℝ) {w : ℝ} (C : AnalyticCocycle w) (h : ℝ) : Prop :=
  h ≤ w ∧ ∀ y : ℝ, |y| < h → lyapunov α (C.line y) = 0

/-! ### The fibered rotation number -/

/-- The unit vector of angle `θ` turns. -/
def unitVec (θ : ℝ) : Fin 2 → ℂ := ![Real.cos (2 * Real.pi * θ), Real.sin (2 * Real.pi * θ)]

/-- `F` is a continuous lift of the projective action of `A` homotopic to the identity:
`A(x) (cos 2πθ, sin 2πθ)` is a positive multiple of `(cos 2πF(x,θ), sin 2πF(x,θ))`,
`F(x, θ + 1) = F(x, θ) + 1`, and `F` is `1`-periodic in `x`. -/
structure IsProjectiveLift (A : ℝ → M2) (F : ℝ → ℝ → ℝ) : Prop where
  continuous : Continuous fun p : ℝ × ℝ => F p.1 p.2
  equivariant : ∀ x θ, F x (θ + 1) = F x θ + 1
  periodic : ∀ x θ, F (x + 1) θ = F x θ
  lift : ∀ x θ, ∃ c : ℝ, 0 < c ∧ (A x).mulVec (unitVec θ) = (c : ℂ) • unitVec (F x θ)

/-- The iterated lift `F_n(x, ·) = F(x + (n-1)α, ·) ∘ ⋯ ∘ F(x, ·)`. -/
def liftIter (α : ℝ) (F : ℝ → ℝ → ℝ) : ℕ → ℝ → ℝ → ℝ
  | 0, _, θ => θ
  | n + 1, x, θ => F (x + n * α) (liftIter α F n x θ)

/-- `ρ` is a **fibered rotation number** of `(α, A)`: for some continuous lift of the projective
action, `(F_n(x,θ) - θ)/n → ρ` uniformly in `(x, θ)`. -/
def IsRotationNumber (α : ℝ) (A : ℝ → M2) (ρ : ℝ) : Prop :=
  ∃ F, IsProjectiveLift A F ∧
    TendstoUniformly (fun (n : ℕ) (p : ℝ × ℝ) => (liftIter α F n p.1 p.2 - p.2) / n)
      (fun _ => ρ) atTop

/-! ### Reducibility notions -/

/-- A real-analytic, `1`-periodic `SL(2,ℝ)`-valued conjugacy, analytic on `|Im z| < h`. -/
structure AnalyticConj (h : ℝ) where
  Z : ℂ → M2
  analytic : ∀ i j, AnalyticOnNhd ℂ (fun z => Z z i j) (strip h)
  periodic : ∀ z, Z (z + 1) = Z z
  real : ∀ (x : ℝ) i j, (starRingEnd ℂ) (Z x i j) = Z x i j
  det_eq_one : ∀ z ∈ strip h, (Z z).det = 1

/-- `Z` has **degree zero**: it is homotopic to a constant through continuous periodic maps
into `SL(2,ℝ)` (equivalently, the angle of its first column has winding number zero). -/
def DegreeZero {h : ℝ} (Z : AnalyticConj h) : Prop :=
  ∃ H : ℝ → ℝ → M2, Continuous (fun p : ℝ × ℝ => H p.1 p.2) ∧
    (∀ x, H 0 x = Z.Z x) ∧ (∀ x, H 1 x = H 1 0) ∧
    (∀ s x, H s (x + 1) = H s x) ∧ (∀ s x, (H s x).det = 1)

/-- **Almost reducibility**: for every `ε > 0` there are an analytic conjugacy on some strip and a
constant matrix `C₀` with `Z(z+α)⁻¹ A(z) Z(z)` within `ε` of `C₀` on that strip. -/
def AlmostReducible (α : ℝ) {w : ℝ} (C : AnalyticCocycle w) : Prop :=
  ∀ ε > (0 : ℝ), ∃ h' > (0 : ℝ), ∃ (Z : AnalyticConj h') (B : ℂ → M2) (C₀ : M2),
    (∀ z ∈ strip h', C.A z * Z.Z z = Z.Z (z + α) * B z) ∧ ∀ z ∈ strip h', ‖B z - C₀‖ < ε

/-- **Analytic rotations reducibility** by a degree-zero conjugacy (paper (t-eq:rotations-reducibility)):
`Z(x+α)⁻¹ A(x) Z(x) = R_{φ(x)}` with `Z` real analytic, `φ` real analytic and real. -/
def RotationsReducible (α : ℝ) {w : ℝ} (C : AnalyticCocycle w) : Prop :=
  ∃ h' > (0 : ℝ), ∃ (Z : AnalyticConj h') (φ : ℝ → ℝ),
    DegreeZero Z ∧ AnalyticOnNhd ℝ φ univ ∧ Function.Periodic φ 1 ∧
    Conj α C.real' (fun x => rot (φ x)) (fun x => Z.Z x)

/-- **Analytic reducibility to a constant rotation**: `Z(x+α)⁻¹ A(x) Z(x) = R_r`. -/
def ReducibleToRotation (α : ℝ) {w : ℝ} (C : AnalyticCocycle w) (r : ℝ) : Prop :=
  ∃ h' > (0 : ℝ), ∃ Z : AnalyticConj h', Conj α C.real' (fun _ => rot r) (fun x => Z.Z x)

/-! ### The cited theorems, as claims -/

/-- **Avila's almost reducibility theorem** ([AvilaARC, Theorem 1]): a subcritical analytic
cocycle over an irrational rotation is almost reducible. -/
def AlmostReducibilityClaim : Prop :=
  ∀ {α : ℝ}, Irrational α → ∀ {w : ℝ} (C : AnalyticCocycle w) {h : ℝ}, 0 < h →
    SubcriticalOn α C h → AlmostReducible α C

/-- **Analytic rotations reducibility** ([AvilaARAC, §1.2, Thm 1.4, Cor 1.5] and [AFK, Thm 1.3]):
for each irrational `α` there is a set `𝓡_α ⊆ ℝ` of full Lebesgue measure, invariant under
integer translation, such that every almost reducible analytic cocycle whose fibered rotation
number lies in `𝓡_α` is analytically rotations reducible by a degree-zero conjugacy. -/
def RotationsReducibilityClaim : Prop :=
  ∀ {α : ℝ}, Irrational α → ∃ 𝓡 : Set ℝ, volume 𝓡ᶜ = 0 ∧ (∀ r : ℝ, ∀ k : ℤ, r ∈ 𝓡 → r + k ∈ 𝓡) ∧
    ∀ {w : ℝ} (C : AnalyticCocycle w) {ρ : ℝ}, AlmostReducible α C →
      IsRotationNumber α C.real' ρ → ρ ∈ 𝓡 → RotationsReducible α C

/-- **Arithmetic reducibility** ([GJArithmetic, Theorem 9.2, Remark 9.1, Appendix B]): if
`L(α, A(· + iy)) = 0` for `|y| < h` with `2πh > β(α)` and `ρ(α, A) ∈ Θ_α`, then `(α, A)` is
analytically reducible to a constant rotation. -/
def ArithmeticReducibilityClaim : Prop :=
  ∀ {α : ℝ}, Irrational α → ∀ {w : ℝ} (C : AnalyticCocycle w) {h : ℝ}, 0 < h →
    ENNReal.ofReal (2 * Real.pi * h) > beta α → SubcriticalOn α C h →
    ∀ {ρ : ℝ}, IsRotationNumber α C.real' ρ → ρ ∈ ThetaSet α → ∃ r, ReducibleToRotation α C r

/-- All cited reducibility theorems. -/
structure ReducibilityInputs : Prop where
  almost : AlmostReducibilityClaim
  rotations : RotationsReducibilityClaim
  arithmetic : ArithmeticReducibilityClaim

end Red
