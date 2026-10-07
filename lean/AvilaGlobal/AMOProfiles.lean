/-
# Bridge: the AMO Lyapunov profiles from the global theory

The sharp-width preparation of *Analytic perturbations of the AMO* (Proposition 2.4,
`AnalyticPerturbationsAMO/SharpWidth.lean`) takes as hypothesis the **AMO profiles**
(`AMO.AMOProfiles`, paper `ext-eq:AMO-profiles`):
  `L_E(y) = max(0, 2π|y| - c)`,   `L̂_E(y) = c + 2π|y|`,   `c = log(1/η)`,
for the direct and the dual transfer cocycles, at energies of the AMO spectrum.  Here they are
derived from Avila's global theory as formalized in this library:

* the direct cocycle `AMO.amoCoc η (E, y)` **is** the shifted Schrödinger cocycle of
  `E - η·2cos(2π·)`, so `am1` (+ evenness `L_neg`) and `am2` give the first profile on the AMO
  spectrum;
* the dual cocycle `AMO.dualCoc η (E, y)` is conjugate, by the constant `diag(√η, 1/√η)`, to the
  Schrödinger cocycle of `E/η - η^{-1}·2cos(2π·)`; with `Hdual = η · H_{η^{-1}}` (Aubry), `am1`,
  `am2` give the second profile on the dual spectrum.

`amoProfiles` gives the profiles on `Σ₀ ∩ Σ̂₀`; `amoProfiles_of_duality` on `Σ₀` itself, given
the spectral form of Aubry duality `Σ̂₀ = Σ₀` (`AubryDualityClaim`, recorded, not asserted).
Like the rest of this library, everything depends only on `[Hypotheses]` ([JKS]).
-/
import AvilaGlobal.AlmostMathieu
import AvilaGlobal.Codimension
import AnalyticPerturbationsAMO.SharpWidth
import AnalyticPerturbationsAMO.Supercritical
import AnalyticPerturbationsAMO.FirstPreparation

noncomputable section

open Complex Matrix

namespace AvilaGlobal

namespace Bridge

variable [Hypotheses]

/-! ### The cocycles -/

/-- The direct AMO transfer cocycle is the shifted Schrödinger cocycle. -/
lemma amoCoc_eq (η E y : ℝ) :
    AMO.amoCoc η ((E : ℂ), y) = shift (schr (eShift E (amPotScaled η))) y := by
  funext x
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [AMO.amoCoc, AMO.transferMatrix, shift, schr, eShift, amPotScaled, amPot] <;> ring

/-- The constant conjugacy `diag(√η, 1/√η)`. -/
def Bη (η : ℝ) : AMO.M2 := !![((Real.sqrt η : ℝ) : ℂ), 0; 0, ((Real.sqrt η : ℝ) : ℂ)⁻¹]

lemma Bη_inv {η : ℝ} (hη : 0 < η) :
    (Bη η)⁻¹ = !![((Real.sqrt η : ℝ) : ℂ)⁻¹, 0; 0, ((Real.sqrt η : ℝ) : ℂ)] := by
  have hs : ((Real.sqrt η : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hη).ne'
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Bη, Matrix.mul_apply, hs]

lemma Bη_det {η : ℝ} (hη : 0 < η) : (Bη η).det = 1 := by
  have hs : ((Real.sqrt η : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hη).ne'
  simp [Bη, Matrix.det_fin_two, hs]

/-- The dual cocycle is conjugate to a Schrödinger cocycle with coupling `η^{-1}`. -/
lemma dualCoc_conj {η : ℝ} (hη : 0 < η) (E y : ℝ) :
    (fun x => Bη η * AMO.dualCoc η ((E : ℂ), y) x * (Bη η)⁻¹) =
      shift (schr (eShift (E / η) (amPotScaled η⁻¹))) y := by
  have hs : ((Real.sqrt η : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hη).ne'
  have hη' : (η : ℂ) ≠ 0 := by exact_mod_cast hη.ne'
  have hsq : ((Real.sqrt η : ℝ) : ℂ) ^ 2 = η := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt hη.le]
  funext x
  rw [Bη_inv hη]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Bη, AMO.dualCoc, AMO.transferMatrix, shift, schr, eShift, amPotScaled, amPot,
      Matrix.mul_apply, Fin.sum_univ_two] <;>
    rw [← hsq] <;> field_simp <;> ring

/-! ### The AMO operator is the Schrödinger operator of `amPotScaled η` -/

lemma coefFn_amo_one (α η t : ℝ) : AMO.coefFn α (AMO.amo η) 1 t = 1 := by
  rw [AMO.coefFn_ofReal, tsum_eq_single 0]
  · simp [AMO.amo, Pi.single_apply]
  · intro q hq; simp [AMO.amo, Pi.single_apply, hq]

lemma coefFn_amo_zero (α η t : ℝ) : AMO.coefFn α (AMO.amo η) 0 t = amPotScaled η t := by
  rw [AMO.coefFn_ofReal, tsum_eq_sum (s := {1, -1}) (fun q hq => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hq
    simp [AMO.amo, Pi.single_apply, hq.1, hq.2]), Finset.sum_pair (by norm_num)]
  simp only [AMO.amo, Pi.add_apply, Pi.single_apply, Prod.mk.injEq, amPotScaled, amPot, AMO.e]
  simp
  rw [Complex.cos]
  push_cast
  ring_nf

lemma amo_wsum (η : ℝ) : AMO.WSum 0 0 (AMO.amo η) := by
  unfold AMO.amo
  exact AMO.WSum.add' (AMO.WSum.add' (AMO.WSum.add' (AMO.single_wsum _ _) (AMO.single_wsum _ _))
    (AMO.single_wsum _ _)) (AMO.single_wsum _ _)

lemma amo_hop (η : ℝ) : AMO.HopGE (AMO.amo η) (-1) ∧ AMO.HopLE (AMO.amo η) 1 := by
  constructor <;> intro p hp <;> obtain ⟨a, b⟩ := p <;> simp only at hp <;>
    simp only [AMO.amo, Pi.add_apply, Pi.single_apply, Prod.mk.injEq] <;>
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)] <;> simp

lemma H_zero_eq (α η : ℝ) : AMO.H α η 0 0 = schrOp α (amPotScaled η) 0 := by
  unfold AMO.H schrOp
  rw [add_zero, AMO.op_eq_jacobi le_rfl le_rfl (amo_wsum η) (AMO.amo_selfAdjoint η)
    (amo_hop η).1 (amo_hop η).2 0]
  simp only [AMO.jacobi, coefFn_amo_one, coefFn_amo_zero, map_one]

lemma mem_Sigma {α η E : ℝ} (hE : E ∈ AMO.Sigma α η 0) : E ∈ Sigma α (amPotScaled η) := by
  unfold AMO.Sigma at hE
  rw [← spectrum.preimage_algebraMap ℂ] at hE
  show (E : ℂ) ∈ spectrum ℂ (schrOp α (amPotScaled η) 0)
  rw [← H_zero_eq]
  exact hE

lemma Hdual_zero_eq {η : ℝ} (hη : 0 < η) (α : ℝ) :
    AMO.Hdual α η 0 0 = ((η : ℝ) : ℂ) • AMO.H α η⁻¹ 0 0 := by
  have h := AMO.Hdual_supercritical (α := α) (inv_pos.2 hη) (T := 0)
    (by simpa [AMO.SymbolSummable] using (summable_zero : Summable fun _ : ℤ × ℤ => (0 : ℝ))) 0
  have hf : AMO.fourier (0 : AMO.Symbol) = 0 := rfl
  rw [hf, hf, hf, smul_zero, inv_inv] at h
  exact h

lemma mem_Sigma_dual {α η E : ℝ} (hη : 0 < η) (hE : E ∈ AMO.SigmaDual α η 0) :
    E / η ∈ Sigma α (amPotScaled η⁻¹) := by
  unfold AMO.SigmaDual at hE
  rw [Hdual_zero_eq hη, AMO.spectrum_real_smul hη.ne'] at hE
  obtain ⟨E', hE', rfl⟩ := hE
  rw [mul_div_cancel_left₀ _ hη.ne']
  exact mem_Sigma hE'

/-! ### The profiles -/

lemma L_abs {A : ℂ → AMO.M2} (hsym : IsRealSymmetric A) (α y : ℝ) : L α A y = L α A |y| := by
  rcases le_or_gt 0 y with hy | hy
  · rw [abs_of_nonneg hy]
  · rw [abs_of_neg hy, L_neg hsym]

/-- **The AMO profiles** (`ext-eq:AMO-profiles`) on `Σ₀ ∩ Σ̂₀`, from `am1`, `am2`. -/
theorem amoProfiles {α η : ℝ} (hα : Irrational α) (hη0 : 0 < η) (hη1 : η < 1) :
    AMO.AMOProfiles α η ((fun E : ℝ => (E : ℂ)) '' (AMO.Sigma α η 0 ∩ AMO.SigmaDual α η 0)) := by
  rintro _ ⟨E, ⟨hE, hEd⟩, rfl⟩ y
  have hlog : Real.log (1 / η) = -Real.log η := by rw [one_div, Real.log_inv]
  constructor
  · rw [amoCoc_eq]
    show L α (schr (eShift E (amPotScaled η))) y = _
    have hsym := schr_isRealSymmetric (amPotScaled_conj η) E
    rw [L_abs hsym, am1 hα hη0 E (abs_nonneg y)]
    have h0 : L α (schr (eShift E (amPotScaled η))) 0 = 0 := by
      have h := (am2 hα hη0 E).2.2 (mem_Sigma hE)
      unfold LE at h
      rw [h]
      exact max_eq_left (Real.log_nonpos hη0.le hη1.le)
    rw [h0, hlog]
    congr 1
    ring
  · have hconj := lyapunov_conj (α := α) (AMO.isSLCocycle_dualCoc hη0.ne' ((E : ℂ), y))
      (continuous_const : Continuous fun _ : ℝ => Bη η) (fun _ => rfl) (fun _ => Bη_det hη0)
    rw [← hconj, dualCoc_conj hη0]
    show L α (schr (eShift (E / η) (amPotScaled η⁻¹))) y = _
    have hsym := schr_isRealSymmetric (amPotScaled_conj η⁻¹) (E / η)
    have hη' : 0 < η⁻¹ := inv_pos.2 hη0
    rw [L_abs hsym, am1 hα hη' (E / η) (abs_nonneg y)]
    have hpos : 0 < Real.log η⁻¹ := by
      rw [Real.log_inv]; linarith [Real.log_neg hη0 hη1]
    have h0 : L α (schr (eShift (E / η) (amPotScaled η⁻¹))) 0 = Real.log η⁻¹ := by
      have h := (am2 hα hη' (E / η)).2.2 (mem_Sigma_dual hη0 hEd)
      unfold LE at h
      rw [h]
      exact max_eq_right hpos.le
    have hy0 : 0 ≤ 2 * Real.pi * |y| := by positivity
    rw [h0, one_div]
    exact max_eq_right (by linarith)

/-- The spectral form of Aubry duality for the unperturbed AMO, `Σ̂₀ = Σ₀` (recorded, not
asserted; it is not used elsewhere). -/
def AubryDualityClaim (α η : ℝ) : Prop := AMO.SigmaDual α η 0 = AMO.Sigma α η 0

/-- **The AMO profiles on the AMO spectrum**, given spectral Aubry duality. -/
theorem amoProfiles_of_duality {α η : ℝ} (hα : Irrational α) (hη0 : 0 < η) (hη1 : η < 1)
    (hD : AubryDualityClaim α η) :
    AMO.AMOProfiles α η ((fun E : ℝ => (E : ℂ)) '' AMO.Sigma α η 0) := by
  have h := amoProfiles hα hη0 hη1
  rwa [show AMO.SigmaDual α η 0 = AMO.Sigma α η 0 from hD, Set.inter_self] at h

end Bridge

end AvilaGlobal
