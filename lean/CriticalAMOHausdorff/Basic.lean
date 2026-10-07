/-
Copyright (c) 2026. Formalization of
  S. Becker, S. Jitomirskaya, I. Krasovsky, "Critical almost Mathieu operator: hidden
  singularity, gap continuity, and the Hausdorff dimension of the spectrum"
  (arXiv:1909.04429v2).

# Basic objects  (paper §1, eqs. (1.1), (1.2), (1.3), (1.4))

* `jacobi v b α θ`: the quasiperiodic Jacobi matrix (1.3)
  `(Hφ)(n) = b(θ+(n-1)α) φ(n-1) + b(θ+nα) φ(n+1) + v(θ+nα) φ(n)` on `ℓ²(ℤ)`;
* `amo α θ`: the critical almost Mathieu operator (1.1) with `λ = 1`;
* `chiral α θ`: the chiral-gauge operator `Ĥ_{α,θ}` of (1.2), i.e. `v = 0`, `b = 2 sin 2π·`;
* `sigmaM v b α`: the spectrum of the direct integral `M_{v,b,α} = ∫^⊕ H_{v,b,α,θ} dθ` (1.4).

For coefficients depending continuously on `θ` (norm-continuous fibres), the spectrum of the
direct integral over `𝕋` is the closure of the union of the fibre spectra; we take this as the
definition of `sigmaM`.  (For irrational `α` all fibre spectra coincide, and `sigmaM` is the
common fibre spectrum; for rational `α` it is the union of the band spectra.)
-/
import AnalyticPerturbationsAMO.Spectral

noncomputable section

open Real Set

namespace CAH

open L2

/-- Bounded operators on `ℓ²(ℤ)`. -/
abbrev Op := AMO.Op ℤ

/-- The quasiperiodic Jacobi matrix (1.3):
`(H φ)(n) = b(θ+(n-1)α) φ(n-1) + b(θ+nα) φ(n+1) + v(θ+nα) φ(n)`. -/
def jacobi (v b : ℝ → ℝ) (α θ : ℝ) : Op :=
  weightedShift (fun n : ℤ => ((b (θ + (n - 1) * α) : ℝ) : ℂ)) (Equiv.addRight (-1)) +
  weightedShift (fun n : ℤ => ((b (θ + n * α) : ℝ) : ℂ)) (Equiv.addRight 1) +
  weightedShift (fun n : ℤ => ((v (θ + n * α) : ℝ) : ℂ)) (Equiv.refl ℤ)

/-- A function `f : ℝ → ℝ` is bounded. -/
def BddFun (f : ℝ → ℝ) : Prop := ∃ M, ∀ x, |f x| ≤ M

lemma bdd_comp {f : ℝ → ℝ} (hf : BddFun f) (g : ℤ → ℝ) :
    Bdd (fun n : ℤ => ((f (g n) : ℝ) : ℂ)) := by
  obtain ⟨M, hM⟩ := hf
  exact ⟨M, fun n => by simpa [Complex.norm_real] using hM (g n)⟩

/-- Matrix elements of `jacobi`. -/
lemma jacobi_apply {v b : ℝ → ℝ} (hv : BddFun v) (hb : BddFun b) (α θ : ℝ) (u : L2 ℤ)
    (n : ℤ) :
    jacobi v b α θ u n =
      (b (θ + (n - 1) * α) : ℂ) * u (n - 1) + (b (θ + n * α) : ℂ) * u (n + 1) +
        (v (θ + n * α) : ℂ) * u n := by
  simp only [jacobi, add_apply, lp.coeFn_add, Pi.add_apply]
  rw [weightedShift_apply (bdd_comp hb _), weightedShift_apply (bdd_comp hb _),
    weightedShift_apply (bdd_comp hv _)]
  simp [sub_eq_add_neg]

/-- The critical almost Mathieu operator (1.1), `λ = 1`:
`(H φ)(n) = φ(n-1) + φ(n+1) + 2 cos 2π(αn+θ) φ(n)`. -/
def amo (α θ : ℝ) : Op := jacobi (fun x => 2 * cos (2 * π * x)) (fun _ => 1) α θ

/-- The chiral-gauge operator (1.2):
`(Ĥ φ)(n) = 2 sin 2π(α(n-1)+θ) φ(n-1) + 2 sin 2π(αn+θ) φ(n+1)`. -/
def chiral (α θ : ℝ) : Op := jacobi (fun _ => 0) (fun x => 2 * sin (2 * π * x)) α θ

/-- The spectrum of the direct integral `M_{v,b,α} = ∫^⊕_𝕋 H_{v,b,α,θ} dθ` (1.4). -/
def sigmaM (v b : ℝ → ℝ) (α : ℝ) : Set ℝ :=
  closure (⋃ θ : ℝ, spectrum ℝ (jacobi v b α θ))

/-- The spectrum of the critical almost Mathieu direct integral `M_α`. -/
def sigmaAMO (α : ℝ) : Set ℝ := closure (⋃ θ : ℝ, spectrum ℝ (amo α θ))

/-- The continued-fraction denominators `q_n` (shared with the other libraries). -/
abbrev q (α : ℝ) (n : ℕ) : ℝ := AMO.cfDen α n

/-- The continued-fraction numerators `p_n`. -/
def p (α : ℝ) (n : ℕ) : ℝ := (GenContFract.of α).nums n

lemma bddFun_two_cos : BddFun (fun x => 2 * cos (2 * π * x)) :=
  ⟨2, fun x => by
    rw [abs_mul, show |(2 : ℝ)| = 2 from abs_two]; nlinarith [abs_cos_le_one (2 * π * x)]⟩

lemma bddFun_two_sin (c : ℝ) : BddFun (fun x => 2 * sin (c * x)) :=
  ⟨2, fun x => by
    rw [abs_mul, show |(2 : ℝ)| = 2 from abs_two]; nlinarith [abs_sin_le_one (c * x)]⟩

lemma bddFun_const (c : ℝ) : BddFun (fun _ => c) := ⟨|c|, fun _ => le_rfl⟩

end CAH
