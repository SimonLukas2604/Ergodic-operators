/-
# Paper III: basic conventions  (paper §1.1–§1.3, §2.1)

*Periodic magnetic Schrödinger operators: Dry Ten Martini and spectral transitions.*

This file fixes the parameters of the continuum model
`H_h = (-i h ∇ - A_𝓑)² + V`, `A_𝓑(x) = (0, 𝓑 x₁)`, on the lattice `Λ_μ = ℤ(μ,0) ⊕ ℤ(0,1)`,
along the field path `𝓑(h) = 2πhγ/μ`, `α = -γ`, and the dictionary between the exact
interaction coefficients `f_{r,q} = ⟨H_h φ_{(r,q)}, φ_0⟩` and the Weyl symbols of Paper I
(`AnalyticPerturbationsAMO`), `c_{r,q} = e^{πiγrq} f_{r,q}`.
-/
import AnalyticPerturbationsAMO

noncomputable section

open AMO

namespace CMS

/-- The field path `𝓑(h) = 2πhγ/μ` (paper (1.2)). -/
def fieldPath (μ γ h : ℝ) : ℝ := 2 * Real.pi * h * γ / μ

/-- The frequency `α = -γ` of the reduced magnetic interaction. -/
def freq (γ : ℝ) : ℝ := -γ

/-- Along the field path the magnetic flux through a cell in units of `h` is `2πγ`. -/
lemma fieldPath_flux {μ h : ℝ} (hμ : μ ≠ 0) (hh : h ≠ 0) (γ : ℝ) :
    μ * fieldPath μ γ h / h = 2 * Real.pi * γ := by
  unfold fieldPath; field_simp

/-- The rectangular cosine potential `V_μ(x) = 2 - cos(2πx₁/μ) - cos(2πx₂)` (paper (1.3)). -/
def cosinePotential (μ : ℝ) (x : ℝ × ℝ) : ℝ :=
  2 - Real.cos (2 * Real.pi * x.1 / μ) - Real.cos (2 * Real.pi * x.2)

lemma cosinePotential_nonneg (μ : ℝ) (x : ℝ × ℝ) : 0 ≤ cosinePotential μ x := by
  unfold cosinePotential
  linarith [Real.cos_le_one (2 * Real.pi * x.1 / μ), Real.cos_le_one (2 * Real.pi * x.2)]

/-- The harmonic levels `λ_𝐧 = √2 π ((2n₁+1)/μ + 2n₂ + 1)` of the cosine well. -/
def harmonicLevel (μ : ℝ) (n : ℕ × ℕ) : ℝ :=
  Real.sqrt 2 * Real.pi * ((2 * n.1 + 1) / μ + 2 * n.2 + 1)

/-- The tunneling action `S_cos = 2√2/π`. -/
def Scos : ℝ := 2 * Real.sqrt 2 / Real.pi

/-- From exact coefficients `f_{r,q}` to the Weyl symbol `c_{r,q} = e^{πiγrq} f_{r,q}`
(paper (2.5)); `e t = e^{2πit}`. -/
def weylSymbol (γ : ℝ) (f : Symbol) : Symbol := fun p => e (γ * p.1 * p.2 / 2) * f p

/-- The axial neighbours `𝒩 = {(0,0), (±1,0), (0,±1)}`. -/
def axialNbhd : Set (ℤ × ℤ) := {(0, 0), (1, 0), (-1, 0), (0, 1), (0, -1)}

/-- `|m|₁`. -/
def l1 (m : ℤ × ℤ) : ℝ := |(m.1 : ℝ)| + |(m.2 : ℝ)|

/-- A lattice distance as in paper (2.6). -/
structure IsLatticeDistance (D : ℤ × ℤ → ℝ) : Prop where
  zero : D 0 = 0
  symm : ∀ m, D (-m) = D m
  pos : ∀ m, m ≠ 0 → 0 < D m
  triangle : ∀ m n, D (m + n) ≤ D m + D n
  coercive : ∃ c C : ℝ, 0 < c ∧ ∀ m, c * l1 m - C ≤ D m

end CMS
