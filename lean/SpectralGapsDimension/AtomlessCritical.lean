/-
Copyright (c) 2026. Formalization of
  S. Becker, "Self-dual perturbations of the critical almost Mathieu operator:
  Dry Ten Martini and Hausdorff dimension" (Paper II).

# The atomless IDS of the perturbed critical operators, from an eigenspace bound

Paper II gets atomlessness of the IDS (used for the Cantor assertions and for the label at the
gap edges) from Theorem 2.4 (`dim:thm:center`) and Paper I, Lemma 2.8: within the radius of
Theorem 2.4 every eigenspace of `H_{α,x} - E` is congruent to the kernel of a Jacobi operator with
nonvanishing hopping, so `dim ker (H_{α,x} - E) ≤ 2`, and Lemma 2.8 turns this into an atomless IDS.

Here the second step is **proved**: `dos_H_atomless` applies `SGD.dos_measure_atomless` (Paper I,
Lemma 2.8, atomless half; `AtomlessDOS.lean`) to the covariant family `x ↦ H_{α,η}(R)_x`.  So
`AtomlessIDSClaim` follows from the smaller input `EigenspaceBoundClaim` together with the existence
of the DOS measure (`DOSExistsClaim`; `atomlessIDS_of_eigenspaceBound`).

`DOSExistsClaim` is a theorem of Paper III's library (`CMS.exists_isDOSMeasure`, via the spectral
measure of the two-dimensional realization).  It is kept as a separate input here so that this library
does not depend on a module of `ContinuumMagnetic` that is still under development; the Paper III
bridge can discharge it.
-/
import ErgodicShared.AtomlessDOS
import SpectralGapsDimension.MainTheorems

noncomputable section

open MeasureTheory

namespace SGD

open AMO

/-- **Atomless DOS for `H_{α,η}(R)`** (Paper I, Lemma 2.8, atomless half): if every eigenspace of
every `H_{α,η}(R)_x` is finite-dimensional of dimension `≤ d`, the DOS measure has no atoms. -/
theorem dos_H_atomless {α η : ℝ} {R : Symbol} (hR : SymbolSummable R)
    (hsa : SymbolSelfAdjoint R) {ν : Measure ℝ} (hν : IsDOSMeasure (H α η R) ν) {d : ℕ}
    (hfin : ∀ x (E : ℝ), FiniteDimensional ℂ
      (LinearMap.ker ((H α η R x - (E : ℂ) • 1 : Op ℤ) : L2 ℤ →ₗ[ℂ] L2 ℤ)))
    (hdim : ∀ x (E : ℝ), Module.finrank ℂ
      (LinearMap.ker ((H α η R x - (E : ℂ) • 1 : Op ℤ) : L2 ℤ →ₗ[ℂ] L2 ℤ)) ≤ d) :
    ∀ E, ν {E} = 0 := by
  have hs : SymbolSummable (amo η + R) := (amo_summable η).add hR
  refine dos_measure_atomless (α := α) hν (isSelfAdjoint_H α η hR hsa) (continuous_op hs)
    (fun x => ?_) (fun x => ?_) hfin hdim
  · have := op_add_int α (amo (η : ℂ) + R) x 1
    simp only [Int.cast_one] at this
    exact this
  · have hst : star (U α x) = W α x (-1) 0 := by rw [U, star_W]; rfl
    rw [hst]
    exact op_conj_U hs x

/-- **Eigenspace bound** (consequence of Theorem 2.4 `dim:thm:center`: the exact, boundedly
invertible Jacobi congruence `H_{α,x} - E = Q^♯ J Q` with nonvanishing hopping): for irrational `α`
and `S > 0`, small admissible perturbations have `dim ker (H_{α,x} - E) ≤ 2` at every phase and
every energy. -/
def EigenspaceBoundClaim : Prop :=
  ∀ {α : ℝ} (hα : Irrational α) {S : ℝ} (hS : 0 < S),
    ∃ ε > 0, ∀ R : Symbol, SelfDual R → WSmall S S R ε → ∀ x (E : ℝ),
      FiniteDimensional ℂ (LinearMap.ker ((H α 1 R x - (E : ℂ) • 1 : Op ℤ) : L2 ℤ →ₗ[ℂ] L2 ℤ)) ∧
      Module.finrank ℂ (LinearMap.ker ((H α 1 R x - (E : ℂ) • 1 : Op ℤ) : L2 ℤ →ₗ[ℂ] L2 ℤ)) ≤ 2

/-- **Existence of the DOS measure** for the critical family with a summable self-adjoint
perturbation (proved in Paper III's library as `CMS.exists_isDOSMeasure`). -/
def DOSExistsClaim : Prop :=
  ∀ (α : ℝ) (R : Symbol), SymbolSummable R → SymbolSelfAdjoint R →
    ∃ ν : Measure ℝ, IsDOSMeasure (H α 1 R) ν

/-- `AtomlessIDSClaim` follows from the eigenspace bound: the DOS measure exists and has no atoms
(`dos_H_atomless`). -/
theorem atomlessIDS_of_eigenspaceBound (hD : DOSExistsClaim) (h : EigenspaceBoundClaim) :
    AtomlessIDSClaim := by
  intro α hα S hS
  obtain ⟨ε, hε, hR⟩ := h hα hS
  refine ⟨ε, hε, fun R hRsd hRS => ?_⟩
  have hRs : SymbolSummable R := WSmall.summable hS.le hS.le hRS
  obtain ⟨ν, hν⟩ := hD α R hRs hRsd.1
  exact ⟨ν, hν, dos_H_atomless hRs hRsd.1 hν (fun x E => (hR R hRsd hRS x E).1)
    (fun x E => (hR R hRsd hRS x E).2)⟩

end SGD
