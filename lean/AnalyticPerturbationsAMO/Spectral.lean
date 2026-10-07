/-
# Spectral-theoretic vocabulary  (paper §1)

Definitions used in the main statements:
* spectral measures of a bounded self-adjoint operator, characterised through the continuous
  functional calculus (`∫ f dμ_ψ = ⟪ψ, f(T) ψ⟫` for bounded continuous `f`), and with them
  *purely absolutely continuous*, *purely singular continuous (on a set)*, *no a.c. component*;
* Anderson localization on a spectral set;
* the density of states measure `dN` and the IDS `N(E)`;
* Cantor sets, open gaps with prescribed IDS labels, the arithmetic exponent `β(α)`;
* exact exponentially local Jacobi preparations `H_x - E = Q_x^* J_x Q_x`, their complexified
  transfer cocycles `C_E(· + iy)`, and subcriticality;
* the two-dimensional magnetic realization `H̃` on `ℓ²(ℤ²)`.

Spectral measures exist and are unique by the spectral theorem and Riesz–Markov; we do not
need this, because every statement below asserts *existence* of the relevant measures.

Proved here: the complexified transfer cocycle of a preparation is a continuous `1`-periodic
`SL(2,ℂ)` cocycle on the preparation strip, so its Lyapunov exponent `L(E, y)` is a genuine
limit (by `AMO.IsSLCocycle.tendsto_lyapunov`); and Fourier self-duality of the critical
almost Mathieu symbol.
-/
import AnalyticPerturbationsAMO.Cocycle

noncomputable section

open scoped ComplexConjugate InnerProductSpace ENNReal
open MeasureTheory Set Filter L2 BoundedContinuousFunction

namespace AMO

/-- Bounded operators on `ℓ²(ι)`. -/
abbrev Op (ι : Type*) := L2 ι →L[ℂ] L2 ι

variable {ι : Type*}

/-! ### Spectral measures and spectral types -/

/-- `μ` is the spectral measure of the self-adjoint operator `T` at the vector `ψ`.
(For self-adjoint `T`, `z ↦ f(Re z)` agrees with `f` on `spec T ⊆ ℝ`, so this is `f(T)`.) -/
def IsSpectralMeasure (T : Op ι) (ψ : L2 ι) (μ : Measure ℝ) : Prop :=
  IsFiniteMeasure μ ∧
    ∀ f : ℝ →ᵇ ℝ, ∫ t, f t ∂μ = RCLike.re ⟪ψ, cfc (fun z : ℂ => ((f z.re : ℝ) : ℂ)) T ψ⟫_ℂ

/-- Purely absolutely continuous spectrum: every spectral measure is a.c. -/
def PurelyAC (T : Op ι) : Prop :=
  ∀ ψ, ∃ μ, IsSpectralMeasure T ψ μ ∧ μ ≪ volume

/-- The spectral restriction of `T` to `S` is purely singular continuous. -/
def PurelySCOn (T : Op ι) (S : Set ℝ) : Prop :=
  ∀ ψ, ∃ μ, IsSpectralMeasure T ψ μ ∧ μ.restrict S ⟂ₘ volume ∧ ∀ E ∈ S, μ {E} = 0

/-- Purely singular continuous spectrum. -/
def PurelySC (T : Op ι) : Prop := PurelySCOn T univ

/-- `T` has no absolutely continuous component. -/
def NoACComponent (T : Op ι) : Prop :=
  ∀ ψ, ∃ μ, IsSpectralMeasure T ψ μ ∧ μ ⟂ₘ volume

/-- `T` has no eigenvalues in `S`. -/
def NoEigenvaluesIn (T : Op ι) (S : Set ℝ) : Prop :=
  ∀ E ∈ S, ∀ u : L2 ι, T u = algebraMap ℂ (Op ι) E u → u = 0

/-- The standard basis vector `δ_n`. -/
def delta [DecidableEq ι] (n : ι) : L2 ι := lp.single 2 n 1

/-- **Anderson localization on a spectral set `S`.**  There is an orthonormal family of
exponentially decaying eigenvectors with eigenvalues in `S` whose closed span contains
`Ran 1_S(T)`, i.e. every vector whose spectral measure is carried by `S`. -/
def AndersonLocalizedOn (T : Op ℤ) (S : Set ℝ) : Prop :=
  ∃ (J : Type) (u : J → L2 ℤ) (E : J → ℝ),
    Orthonormal ℂ u ∧
    (∀ j, E j ∈ S ∧ T (u j) = algebraMap ℂ (Op ℤ) (E j) (u j)) ∧
    (∀ j, ∃ C m : ℝ, 0 < C ∧ 0 < m ∧ ∃ nj : ℤ,
      ∀ n : ℤ, ‖u j n‖ ≤ C * Real.exp (-m * |((n - nj : ℤ) : ℝ)|)) ∧
    (∀ ψ, (∃ μ, IsSpectralMeasure T ψ μ ∧ μ Sᶜ = 0) →
      ψ ∈ (Submodule.span ℂ (range u)).topologicalClosure)

lemma AndersonLocalizedOn.mono {T : Op ℤ} {S S' : Set ℝ} (h : AndersonLocalizedOn T S)
    (hS : S = S') : AndersonLocalizedOn T S' := hS ▸ h

/-! ### Density of states and gaps -/

/-- `ν` is the density of states measure of the covariant family `x ↦ H_x`:
`∫ f dν = ∫_𝕋 ⟪δ₀, f(H_x) δ₀⟫ dx`. -/
def IsDOSMeasure (Hx : ℝ → Op ℤ) (ν : Measure ℝ) : Prop :=
  IsProbabilityMeasure ν ∧
    ∀ f : ℝ →ᵇ ℝ, ∫ t, f t ∂ν =
      ∫ x in (0 : ℝ)..1,
        RCLike.re ⟪delta 0, cfc (fun z : ℂ => ((f z.re : ℝ) : ℂ)) (Hx x) (delta 0)⟫_ℂ

/-- The integrated density of states `N(E) = ν((-∞, E])`. -/
def IDS (ν : Measure ℝ) (E : ℝ) : ℝ := (ν (Iic E)).toReal

/-- A Cantor set: nonempty, compact, without isolated points and without intervals. -/
def IsCantor (K : Set ℝ) : Prop :=
  K.Nonempty ∧ IsCompact K ∧ Perfect K ∧ interior K = ∅

/-- The gap with label `{nα}` is open: there are `a < b` in `Σ` with `(a,b) ∩ Σ = ∅` and
`N ≡ {nα}` on `[a,b]`. -/
def GapOpen (Sig : Set ℝ) (ν : Measure ℝ) (α : ℝ) (n : ℤ) : Prop :=
  ∃ a b : ℝ, a < b ∧ a ∈ Sig ∧ b ∈ Sig ∧ Ioo a b ∩ Sig = ∅ ∧
    ∀ E ∈ Icc a b, IDS ν E = Int.fract (n * α)

/-- Dry Ten Martini: every allowed internal gap label `{nα}`, `n ≠ 0`, is an open gap. -/
def AllGapsOpen (Sig : Set ℝ) (ν : Measure ℝ) (α : ℝ) : Prop :=
  ∀ n : ℤ, n ≠ 0 → GapOpen Sig ν α n

/-! ### Arithmetic of the frequency -/

/-- The continued-fraction denominators `q_j` of `α`. -/
def cfDen (α : ℝ) (j : ℕ) : ℝ := (GenContFract.of α).dens j

/-- `β(α) = limsup_j (log q_{j+1}) / q_j ∈ [0, ∞]`. -/
def beta (α : ℝ) : ℝ≥0∞ :=
  limsup (fun j : ℕ => ENNReal.ofReal (Real.log (cfDen α (j + 1)) / cfDen α j)) atTop

/-- Diophantine condition `‖nα‖_𝕋 ≥ κ |n|^{-τ}`. -/
def Diophantine (α : ℝ) : Prop :=
  ∃ κ τ : ℝ, 0 < κ ∧ ∀ n : ℤ, n ≠ 0 → κ * |(n : ℝ)| ^ (-τ) ≤ |n * α - round (n * α)|

/-! ### Exact Jacobi preparations -/

/-- The strip `|Im z| < w`. -/
def strip (w : ℝ) : Set ℂ := {z | |z.im| < w}

/-- An exact, analytic, exponentially local Jacobi preparation of `H_x - E`:
`H_x - E = Q_x^* J_x Q_x`, `J = a U + a^♯(· - α) U^{-1} + b` with `b` real and `a ≠ 0` on `𝕋`,
and `c = (a a^♯)^{1/2}` the analytic square root with `c = |a|` on `𝕋`. -/
structure JacobiPrep (α : ℝ) (Hx : ℝ → Op ℤ) (E : ℝ) where
  /-- The (invertible) change of unknown. -/
  Q : ℝ → (Op ℤ)ˣ
  /-- Prepared hopping. -/
  a : ℂ → ℂ
  /-- Prepared potential. -/
  b : ℂ → ℂ
  /-- Analytic square root of `a a^♯`. -/
  c : ℂ → ℂ
  /-- Width of the analyticity strip. -/
  w : ℝ
  w_pos : 0 < w
  a_analytic : AnalyticOnNhd ℂ a (strip w)
  b_analytic : AnalyticOnNhd ℂ b (strip w)
  c_analytic : AnalyticOnNhd ℂ c (strip w)
  a_periodic : ∀ z, a (z + 1) = a z
  b_periodic : ∀ z, b (z + 1) = b z
  c_periodic : ∀ z, c (z + 1) = c z
  b_real : ∀ t : ℝ, conj (b t) = b t
  a_ne : ∀ t : ℝ, a t ≠ 0
  c_sq : ∀ z ∈ strip w, c z ^ 2 = a z * conj (a (conj z))
  c_eq_norm : ∀ t : ℝ, c t = ‖a t‖
  c_ne : ∀ z ∈ strip w, c z ≠ 0
  /-- The exact factorization. -/
  factor : ∀ x : ℝ, Hx x - algebraMap ℂ (Op ℤ) E = star (Q x : Op ℤ) * jacobi α a b x * Q x
  /-- Exponential locality of `Q` and `Q⁻¹`, uniformly in the phase. -/
  exp_local : ∃ C κ : ℝ, 0 < C ∧ 0 < κ ∧ ∀ (x : ℝ) (m n : ℤ),
    ‖⟪delta m, (Q x : Op ℤ) (delta n)⟫_ℂ‖ ≤ C * Real.exp (-κ * |((n - m : ℤ) : ℝ)|) ∧
    ‖⟪delta m, ((Q x)⁻¹ : (Op ℤ)ˣ).1 (delta n)⟫_ℂ‖ ≤ C * Real.exp (-κ * |((n - m : ℤ) : ℝ)|)

namespace JacobiPrep

variable {α : ℝ} {Hx : ℝ → Op ℤ} {E : ℝ} (P : JacobiPrep α Hx E)

/-- The complexified prepared transfer cocycle `x ↦ C_E(x + iy)`. -/
def C (y : ℝ) : ℝ → M2 := fun x => transferMatrix (P.b (x + y * Complex.I)) (P.c (x + y * Complex.I))

/-- The complexified Lyapunov exponent `L(E, y) = L(α, C_E(· + iy))`. -/
def L (y : ℝ) : ℝ := lyapunov α (P.C y)

/-- `∫_𝕋 log |a_E|`. -/
def logMean : ℝ := ∫ x in (0 : ℝ)..1, Real.log ‖P.a x‖

/-- Subcriticality of the prepared equation: `L(E, y) = 0` for `|y| < h`, some `h > 0`. -/
def Subcritical : Prop := ∃ h : ℝ, 0 < h ∧ h ≤ P.w ∧ ∀ y : ℝ, |y| < h → P.L y = 0

lemma mem_strip {y : ℝ} (hy : |y| < P.w) (x : ℝ) : (x : ℂ) + y * Complex.I ∈ strip P.w := by
  simpa [strip] using hy

/-- On the preparation strip, `C_E(· + iy)` is a continuous `1`-periodic `SL(2, ℂ)` cocycle;
in particular `L(E, y)` is a limit and is nonnegative. -/
theorem isSLCocycle_C {y : ℝ} (hy : |y| < P.w) : IsSLCocycle (P.C y) := by
  have hpath : Continuous fun x : ℝ => (x : ℂ) + y * Complex.I := by fun_prop
  have hb : Continuous fun x : ℝ => P.b (x + y * Complex.I) :=
    P.b_analytic.continuousOn.comp_continuous hpath (P.mem_strip hy)
  have hc : Continuous fun x : ℝ => P.c (x + y * Complex.I) :=
    P.c_analytic.continuousOn.comp_continuous hpath (P.mem_strip hy)
  have hc0 : ∀ x : ℝ, P.c (x + y * Complex.I) ≠ 0 := fun x => P.c_ne _ (P.mem_strip hy x)
  refine ⟨?_, ?_, ?_⟩
  · unfold C transferMatrix
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp
    all_goals first
      | exact continuous_const
      | exact hc
      | exact hb.neg.div hc hc0
      | exact continuous_const.div hc hc0
  · intro x
    simp only [C]
    push_cast
    rw [add_right_comm, P.b_periodic, P.c_periodic]
  · intro x
    exact det_transferMatrix _ (hc0 x)

theorem L_nonneg {y : ℝ} (hy : |y| < P.w) : 0 ≤ P.L y := (P.isSLCocycle_C hy).lyapunov_nonneg

end JacobiPrep

/-! ### The two-dimensional realization on `ℓ²(ℤ²)` -/

/-- `W̃_{r,q} = e^{πiαrq} Ṽ^q Ũ^r`, i.e. `(W̃_{r,q} u)(n,m) = e^{2πi(αrq/2 + αqn)} u(n+r, m+q)`. -/
def W2 (α : ℝ) (r q : ℤ) : Op (ℤ × ℤ) :=
  weightedShift (fun p : ℤ × ℤ => e (α * r * q / 2 + q * p.1 * α)) (Equiv.addRight (r, q))

/-- The two-dimensional operator `H̃ = ∑ R_{r,q} W̃_{r,q}`. -/
def op2 (α : ℝ) (R : Symbol) : Op (ℤ × ℤ) := ∑' p : ℤ × ℤ, R p • W2 α p.1 p.2

/-- The two-dimensional magnetic Weyl relation `W̃_{r,q} W̃_{r',q'} = e^{πiα(rq'-r'q)} W̃_{r+r',q+q'}`. -/
lemma W2_apply (α : ℝ) (r q : ℤ) (u : L2 (ℤ × ℤ)) (p : ℤ × ℤ) :
    W2 α r q u p = e (α * r * q / 2 + q * p.1 * α) * u (p + (r, q)) := by
  rw [W2, weightedShift_apply (bdd_e _)]
  rfl

theorem W2_mul (α : ℝ) (r q r' q' : ℤ) :
    W2 α r q ∘L W2 α r' q' = e (α * (r * q' - r' * q) / 2) • W2 α (r + r') (q + q') := by
  ext u p
  obtain ⟨n, m⟩ := p
  simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply, lp.coeFn_smul, Pi.smul_apply,
    smul_eq_mul, W2_apply]
  simp only [← mul_assoc, ← e_add, Prod.mk_add_mk, add_assoc]
  congr 2
  push_cast
  ring

/-! ### Self-duality at criticality -/

lemma fourier_add (R R' : Symbol) : fourier (R + R') = fourier R + fourier R' := rfl

/-- The critical almost Mathieu symbol is Fourier self-dual. -/
lemma fourier_amo_one : fourier (amo 1) = amo 1 := by
  rw [fourier_amo one_ne_zero, inv_one, one_smul]

/-- A Fourier self-dual perturbation of the critical operator gives a self-dual `H`. -/
theorem fourier_critical {R : Symbol} (hR : fourier R = R) :
    fourier (amo 1 + R) = amo 1 + R := by
  rw [fourier_add, fourier_amo_one, hR]

/-- Hence `Ĥ_x = H_x` at criticality. -/
theorem Hdual_eq_H_critical (α : ℝ) {R : Symbol} (hR : fourier R = R) (x : ℝ) :
    Hdual α 1 R x = H α 1 R x := by
  unfold Hdual H
  have : ((1 : ℝ) : ℂ) = 1 := by norm_num
  rw [this, fourier_critical hR]

end AMO
