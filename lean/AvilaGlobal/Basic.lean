/-
# Basic objects  (Avila, *Global theory of one-frequency Schrödinger operators I*, §1)

* Analytic one-frequency `SL(2,ℂ)` cocycles on a strip `|Im z| < δ`, encoded as functions
  `A : ℂ → M₂(ℂ)` which are holomorphic, `1`-periodic and of determinant one on the strip.
* The complexified cocycle `A_ε(x) = A(x + iε)` and the function `ε ↦ L(α, A_ε)`.
* The acceleration `ω(α, A) = lim_{ε → 0+} (L(α, A_ε) - L(α, A)) / (2πε)`.
* Regularity, uniform hyperbolicity, nonuniform hyperbolicity, criticality.
* Schrödinger cocycles `A^{(v)} = [[v, -1], [1, 0]]` and the spectrum `Σ_{α,v}`.
* Stratifications and `C^r`-stratified functions.

Proved here: for `|ε| < δ`, `A_ε` is a continuous `1`-periodic `SL(2,ℂ)` cocycle (so
`L(α, A_ε)` is a genuine limit and is `≥ 0`); the Schrödinger cocycle is an analytic cocycle
on the strip of analyticity of `v`.

Conventions.  As in `AnalyticPerturbationsAMO.Cocycle`, the Lyapunov exponent uses the `ℓ^∞`
operator norm on `M₂(ℂ)`; `AMO.IsSLCocycle.tendsto_lyapunov_euclid` shows that the Euclidean
norm of the paper gives the same number.  Uniform hyperbolicity is stated with continuous
invariant directions (the paper writes "analytic"; for analytic cocycles the invariant
directions of a uniformly hyperbolic cocycle are automatically analytic, and the continuous
definition is the standard one).
-/
import AnalyticPerturbationsAMO.LyapunovNorm
import AnalyticPerturbationsAMO.Equidistribution

noncomputable section

open scoped Matrix.Norms.Operator ComplexConjugate ContDiff
open Matrix Filter Topology Complex

namespace AvilaGlobal

open AMO

/-! ### Strips and analytic cocycles -/

/-- The open strip `{|Im z| < δ}`. -/
def strip (δ : ℝ) : Set ℂ := {z | |z.im| < δ}

lemma isOpen_strip (δ : ℝ) : IsOpen (strip δ) :=
  isOpen_lt (continuous_abs.comp continuous_im) continuous_const

lemma mem_strip_shift {δ ε : ℝ} (hε : |ε| < δ) (x : ℝ) : (x : ℂ) + ε * I ∈ strip δ := by
  simpa [strip] using hε

/-- `A ∈ C^ω_δ(ℝ/ℤ, SL(2,ℂ))`: `A` is holomorphic, `1`-periodic and of determinant one on the
strip `|Im z| < δ`.  (Values off the strip are irrelevant.) -/
structure IsAnalyticCocycle (δ : ℝ) (A : ℂ → M2) : Prop where
  pos : 0 < δ
  holo : DifferentiableOn ℂ A (strip δ)
  periodic : ∀ z, A (z + 1) = A z
  det_eq_one : ∀ z ∈ strip δ, (A z).det = 1

/-- `A ∈ C^ω(ℝ/ℤ, SL(2,ℂ))`: analytic on some strip. -/
def IsAnalytic (A : ℂ → M2) : Prop := ∃ δ, IsAnalyticCocycle δ A

/-- `A` takes values in `SL(2,ℝ)` on the real line, in the holomorphic form
`A(z̄) = conj A(z)`. -/
def IsRealSymmetric (A : ℂ → M2) : Prop := ∀ z, A (conj z) = (A z).map conj

/-- The complexified cocycle restricted to the real line, `x ↦ A_ε(x) = A(x + iε)`. -/
def shift (A : ℂ → M2) (ε : ℝ) : ℝ → M2 := fun x => A (x + ε * I)

/-- The Lyapunov exponent of the complexified cocycle, `L(α, A_ε)`. -/
def L (α : ℝ) (A : ℂ → M2) (ε : ℝ) : ℝ := lyapunov α (shift A ε)

/-- The acceleration `ω(α, A) = lim_{ε → 0+} (L(α, A_ε) - L(α, A)) / (2πε)`. -/
def accel (α : ℝ) (A : ℂ → M2) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε => (L α A ε - L α A 0) / (2 * Real.pi * ε)

/-- The `ε`-shift of a complex cocycle, as a complex cocycle: `z ↦ A(z + iε)`. -/
def cshift (A : ℂ → M2) (ε : ℝ) : ℂ → M2 := fun z => A (z + ε * I)

/-- `(α, A)` is *regular*: `ε ↦ L(α, A_ε)` is affine near `0`. -/
def IsRegular (α : ℝ) (A : ℂ → M2) : Prop :=
  ∃ η > 0, ∃ a b : ℝ, ∀ ε : ℝ, |ε| < η → L α A ε = a + b * ε

/-! ### Uniform hyperbolicity -/

/-- `(α, A)` (a cocycle on the real line) is *uniformly hyperbolic*: there are continuous
`1`-periodic nowhere-vanishing vector fields `u, s : ℝ → ℂ²` spanning invariant lines,
`A(x) u(x) ∥ u(x+α)`, `A(x) s(x) ∥ s(x+α)`, and an `n ≥ 1` such that `A_n` expands along
`u` and contracts along `s`. -/
def IsUH (α : ℝ) (A : ℝ → M2) : Prop :=
  ∃ u s : ℝ → (Fin 2 → ℂ), Continuous u ∧ Continuous s ∧
    Function.Periodic u 1 ∧ Function.Periodic s 1 ∧ (∀ x, u x ≠ 0) ∧ (∀ x, s x ≠ 0) ∧
    (∀ x, ∃ c : ℂ, A x *ᵥ u x = c • u (x + α)) ∧
    (∀ x, ∃ c : ℂ, A x *ᵥ s x = c • s (x + α)) ∧
    ∃ n : ℕ, 1 ≤ n ∧ ∀ x, ‖iter α A n x *ᵥ s x‖ < ‖s x‖ ∧ ‖u x‖ < ‖iter α A n x *ᵥ u x‖

/-- `(α, A) ∈ 𝒰ℋ` for a complex cocycle: its restriction to the real line is uniformly
hyperbolic. -/
def UH (α : ℝ) (A : ℂ → M2) : Prop := IsUH α (shift A 0)

/-- Nonuniformly hyperbolic: positive exponent but not uniformly hyperbolic. -/
def IsNUH (α : ℝ) (A : ℂ → M2) : Prop := 0 < L α A 0 ∧ ¬ UH α A

/-- *Critical*: not regular, with zero Lyapunov exponent. -/
def IsCritical (α : ℝ) (A : ℂ → M2) : Prop := ¬ IsRegular α A ∧ L α A 0 = 0

/-! ### Schrödinger cocycles and operators -/

/-- The Schrödinger cocycle `A^{(v)} = [[v, -1], [1, 0]]`. -/
def schr (v : ℂ → ℂ) : ℂ → M2 := fun z => !![v z, -1; 1, 0]

/-- `v ∈ C^ω_δ(ℝ/ℤ, ℝ)` in holomorphic form: holomorphic on the strip, `1`-periodic, and real on
the real line. -/
structure IsRealAnalyticPotential (δ : ℝ) (v : ℂ → ℂ) : Prop where
  pos : 0 < δ
  holo : DifferentiableOn ℂ v (strip δ)
  periodic : ∀ z, v (z + 1) = v z
  real : ∀ x : ℝ, (v x).im = 0

/-- The energy-shifted potential `E - v`. -/
def eShift (E : ℝ) (v : ℂ → ℂ) : ℂ → ℂ := fun z => E - v z

/-- The Schrödinger operator `(Hu)_n = u_{n+1} + u_{n-1} + v(x + nα) u_n` on `ℓ²(ℤ)`. -/
def schrOp (α : ℝ) (v : ℂ → ℂ) (x : ℝ) := jacobi α (fun _ => 1) v x

/-- The spectrum `Σ_{α,v}` of `H_{α,v}` (at phase `0`; for irrational `α` it does not depend on
the phase, `AMO.spectrum_indep_phase`-type statement). -/
def Sigma (α : ℝ) (v : ℂ → ℂ) : Set ℝ := {E | (E : ℂ) ∈ spectrum ℂ (schrOp α v 0)}

/-- The Lyapunov exponent at energy `E`, `L(E) = L(α, A^{(E - v)})`. -/
def LE (α : ℝ) (v : ℂ → ℂ) (E : ℝ) : ℝ := L α (schr (eShift E v)) 0

/-- `E` is a critical energy of `H_{α,v}`. -/
def IsCriticalEnergy (α : ℝ) (v : ℂ → ℂ) (E : ℝ) : Prop := IsCritical α (schr (eShift E v))

/-! ### Stratifications -/

/-- A stratification of a set `X` (in a topological space `T`): a sequence of relatively closed
sets `X = X₀ ⊇ X₁ ⊇ ⋯`, strictly decreasing until it becomes empty, with empty intersection. -/
structure IsStratification {T : Type*} [TopologicalSpace T] (X : Set T) (S : ℕ → Set T) :
    Prop where
  zero : S 0 = X
  subset : ∀ i, S i ⊆ X
  closed : ∀ i, ∃ F : Set T, IsClosed F ∧ S i = F ∩ X
  anti : ∀ i, S (i + 1) ⊆ S i
  strict : ∀ i, S i ≠ ∅ → S (i + 1) ≠ S i
  inter : ⋂ i, S i = ∅

/-- The `i`-th stratum `S i \ S (i+1)`. -/
def stratum {T : Type*} (S : ℕ → Set T) (i : ℕ) : Set T := S i \ S (i + 1)

/-- `f : X → ℝ` (defined on `X ⊆ E`, `E` a real normed space) is `C^ω` on a set `Y ⊆ X`: near
every point of `Y` it agrees on `Y` with a real-analytic function defined on a neighbourhood
in `E`. -/
def AnalyticOnSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ)
    (Y : Set E) : Prop :=
  ∀ p ∈ Y, ∃ U ∈ 𝓝 p, ∃ g : E → ℝ, AnalyticOnNhd ℝ g U ∧ ∀ y ∈ Y ∩ U, f y = g y

/-- `f` is `C^∞` on `Y` in the same sense. -/
def SmoothOnSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ)
    (Y : Set E) : Prop :=
  ∀ p ∈ Y, ∃ U ∈ 𝓝 p, ∃ g : E → ℝ, ContDiffOn ℝ ∞ g U ∧ ∀ y ∈ Y ∩ U, f y = g y

/-- `f` is continuous and `C^ω`-stratified on `X`. -/
def IsAnalyticStratified {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ)
    (X : Set E) : Prop :=
  ContinuousOn f X ∧ ∃ S, IsStratification X S ∧ ∀ i, AnalyticOnSet f (stratum S i)

/-- `f` is continuous and `C^∞`-stratified on `X`. -/
def IsSmoothStratified {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ℝ)
    (X : Set E) : Prop :=
  ContinuousOn f X ∧ ∃ S, IsStratification X S ∧ ∀ i, SmoothOnSet f (stratum S i)

/-! ### Basic facts -/

section Basic

variable {δ : ℝ} {A : ℂ → M2}

lemma IsAnalyticCocycle.continuousOn (hA : IsAnalyticCocycle δ A) : ContinuousOn A (strip δ) :=
  hA.holo.continuousOn

/-- For `|ε| < δ`, `A_ε` is a continuous `1`-periodic `SL(2,ℂ)` cocycle. -/
theorem IsAnalyticCocycle.isSLCocycle_shift (hA : IsAnalyticCocycle δ A) {ε : ℝ}
    (hε : |ε| < δ) : IsSLCocycle (shift A ε) := by
  have hpath : Continuous fun x : ℝ => (x : ℂ) + ε * I := by fun_prop
  refine ⟨hA.continuousOn.comp_continuous hpath (mem_strip_shift hε), ?_, ?_⟩
  · intro x
    simp only [shift]
    push_cast
    rw [add_right_comm, hA.periodic]
  · intro x
    exact hA.det_eq_one _ (mem_strip_shift hε x)

/-- `L(α, A_ε) ≥ 0`. -/
theorem IsAnalyticCocycle.L_nonneg (hA : IsAnalyticCocycle δ A) (α : ℝ) {ε : ℝ}
    (hε : |ε| < δ) : 0 ≤ L α A ε :=
  (hA.isSLCocycle_shift hε).lyapunov_nonneg

/-- `L(α, A_ε)` is the limit of `(1/n) ∫ log ‖A_n(x + iε)‖ dx`. -/
theorem IsAnalyticCocycle.tendsto_L (hA : IsAnalyticCocycle δ A) (α : ℝ) {ε : ℝ}
    (hε : |ε| < δ) :
    Tendsto (fun n : ℕ => lyapSeq α (shift A ε) n / n) atTop (𝓝 (L α A ε)) :=
  (hA.isSLCocycle_shift hε).tendsto_lyapunov

lemma shift_cshift (A : ℂ → M2) (ε ε' : ℝ) : shift (cshift A ε) ε' = shift A (ε' + ε) := by
  funext x
  simp only [shift, cshift]
  push_cast
  ring_nf

lemma L_cshift (α : ℝ) (A : ℂ → M2) (ε ε' : ℝ) : L α (cshift A ε) ε' = L α A (ε' + ε) := by
  simp [L, shift_cshift]

/-- A shifted analytic cocycle is analytic on a smaller strip. -/
theorem IsAnalyticCocycle.cshift (hA : IsAnalyticCocycle δ A) {ε : ℝ} (hε : |ε| < δ) :
    IsAnalyticCocycle (δ - |ε|) (cshift A ε) := by
  have hmaps : Set.MapsTo (fun z : ℂ => z + ε * I) (strip (δ - |ε|)) (strip δ) := by
    intro z hz
    simp only [strip, Set.mem_ofPred_eq, add_im, mul_im, ofReal_re, I_im, mul_one, ofReal_im,
      I_re, mul_zero, add_zero] at hz ⊢
    calc |z.im + ε| ≤ |z.im| + |ε| := abs_add_le _ _
      _ < δ := by linarith
  refine ⟨by linarith, ?_, ?_, ?_⟩
  · exact hA.holo.comp (differentiableOn_id.add_const _) hmaps
  · intro z
    simp only [AvilaGlobal.cshift]
    rw [add_right_comm, hA.periodic]
  · intro z hz
    exact hA.det_eq_one _ (hmaps hz)

lemma det_schr (v : ℂ → ℂ) (z : ℂ) : (schr v z).det = 1 := by
  simp [schr, det_fin_two]

/-- The Schrödinger cocycle of an analytic potential is an analytic `SL(2,ℂ)` cocycle. -/
theorem IsRealAnalyticPotential.schr {v : ℂ → ℂ} (hv : IsRealAnalyticPotential δ v) (E : ℝ) :
    IsAnalyticCocycle δ (AvilaGlobal.schr (eShift E v)) := by
  refine ⟨hv.pos, ?_, ?_, fun z _ => det_schr _ z⟩
  · have hE : DifferentiableOn ℂ (eShift E v) (strip δ) :=
      (differentiableOn_const _).sub hv.holo
    have hform : AvilaGlobal.schr (eShift E v) =
        fun z => eShift E v z • (!![1, 0; 0, 0] : M2) + !![0, -1; 1, 0] := by
      funext z
      ext i j
      fin_cases i <;> fin_cases j <;> simp [AvilaGlobal.schr]
    rw [hform]
    exact (hE.smul_const _).add_const _
  · intro z
    simp [AvilaGlobal.schr, eShift, hv.periodic]

end Basic

end AvilaGlobal
