/-
# Covariance and the common spectrum  (paper §2.1)

We prove, without `sorry`:
* the spectral stability estimate for a normal element `a` of a C⋆-algebra:
  every point of `spec b` lies within `‖a - b‖` of `spec a`; hence
  `d_H(spec A, spec B) ≤ ‖A - B‖` for normal (e.g. self-adjoint) `A, B`;
* **phase independence**: for irrational `α` and an absolutely summable self-adjoint
  Weyl symbol, the spectrum of `R_x` does not depend on the phase `x`.
  The proof is the one in the paper: covariance under `U`, `1`-periodicity, norm
  continuity, and density of `ℤ + αℤ`.
-/
import AnalyticPerturbationsAMO.Weyl

noncomputable section

open scoped ComplexConjugate
open L2

namespace AMO

section Stability

variable {A : Type*} [CStarAlgebra A]

/-- **Spectral stability.** If `a` is normal, every `z ∈ spec b` lies within `‖a - b‖`
of `spec a`. -/
theorem exists_mem_spectrum_dist_le {a b : A} [IsStarNormal a] {z : ℂ}
    (hz : z ∈ spectrum ℂ b) : ∃ w ∈ spectrum ℂ a, ‖z - w‖ ≤ ‖a - b‖ := by
  rcases subsingleton_or_nontrivial A with hA | hA
  · simp [spectrum.of_subsingleton] at hz
  obtain ⟨w₀, hw₀, hmin⟩ := (spectrum.isCompact a).exists_isMinOn (spectrum.nonempty a)
    (f := fun w : ℂ => ‖z - w‖) (by fun_prop)
  refine ⟨w₀, hw₀, ?_⟩
  by_contra! hlt
  set d := ‖z - w₀‖ with hd_def
  have hd : ∀ w ∈ spectrum ℂ a, d ≤ ‖z - w‖ := fun w hw => hmin hw
  have hd0 : 0 < d := lt_of_le_of_lt (norm_nonneg _) hlt
  have hne : ∀ w ∈ spectrum ℂ a, z - w ≠ 0 := fun w hw h => by
    have := hd w hw
    rw [h, norm_zero] at this
    linarith
  have hcont : ContinuousOn (fun w : ℂ => (z - w)⁻¹) (spectrum ℂ a) :=
    (continuousOn_const.sub continuousOn_id).inv₀ hne
  set r := cfc (fun w : ℂ => (z - w)⁻¹) a with hr_def
  have hza : algebraMap ℂ A z - a = cfc (fun w : ℂ => z - w) a := by
    rw [cfc_sub (fun _ : ℂ => z) (fun w : ℂ => w) a continuousOn_const continuousOn_id,
      cfc_const z a, cfc_id' ℂ a]
  have h1 : (algebraMap ℂ A z - a) * r = 1 := by
    rw [hza, hr_def, ← cfc_mul (fun w : ℂ => z - w) (fun w : ℂ => (z - w)⁻¹) a
        (continuousOn_const.sub continuousOn_id) hcont,
      cfc_congr (g := fun _ => (1 : ℂ)) (fun w hw => mul_inv_cancel₀ (hne w hw)),
      cfc_const_one ℂ a]
  have h2 : r * (algebraMap ℂ A z - a) = 1 := by
    rw [hza, hr_def, ← cfc_mul (fun w : ℂ => (z - w)⁻¹) (fun w : ℂ => z - w) a
        hcont (continuousOn_const.sub continuousOn_id),
      cfc_congr (g := fun _ => (1 : ℂ)) (fun w hw => inv_mul_cancel₀ (hne w hw)),
      cfc_const_one ℂ a]
  have hr : ‖r‖ ≤ d⁻¹ := by
    refine norm_cfc_le (inv_nonneg.2 hd0.le) (fun w hw => ?_)
    rw [norm_inv]
    exact inv_anti₀ hd0 (hd w hw)
  have hsmall : ‖-(r * (a - b))‖ < 1 := by
    rw [norm_neg]
    calc ‖r * (a - b)‖ ≤ ‖r‖ * ‖a - b‖ := norm_mul_le _ _
      _ ≤ d⁻¹ * ‖a - b‖ := by gcongr
      _ < d⁻¹ * d := by gcongr
      _ = 1 := inv_mul_cancel₀ hd0.ne'
  have hfac : algebraMap ℂ A z - b = (algebraMap ℂ A z - a) * (1 - -(r * (a - b))) := by
    rw [sub_neg_eq_add, mul_add, mul_one, ← mul_assoc, h1, one_mul]
    abel
  apply spectrum.mem_iff.1 hz
  rw [hfac]
  exact (IsUnit.mul ⟨⟨_, r, h1, h2⟩, rfl⟩ (Units.oneSub _ hsmall).isUnit)

/-- `d_H(spec a, spec b) ≤ ‖a - b‖` for normal `a, b`. -/
theorem hausdorffDist_spectrum_le {a b : A} [IsStarNormal a] [IsStarNormal b] :
    Metric.hausdorffDist (spectrum ℂ a) (spectrum ℂ b) ≤ ‖a - b‖ := by
  refine Metric.hausdorffDist_le_of_mem_dist (norm_nonneg _) (fun z hz => ?_) (fun z hz => ?_)
  · obtain ⟨w, hw, h⟩ := exists_mem_spectrum_dist_le (a := b) (b := a) hz
    exact ⟨w, hw, by rw [dist_eq_norm]; simpa [norm_sub_rev] using h⟩
  · obtain ⟨w, hw, h⟩ := exists_mem_spectrum_dist_le (a := a) (b := b) hz
    exact ⟨w, hw, by rw [dist_eq_norm]; exact h⟩

end Stability

/-! ### Phase independence of the spectrum -/

/-- `U` as a unit of the operator algebra. -/
def Uunit (α x : ℝ) : (L2 ℤ →L[ℂ] L2 ℤ)ˣ where
  val := U α x
  inv := W α x (-1) 0
  val_inv := U_comp_Uinv α x
  inv_val := Uinv_comp_U α x

variable {α : ℝ} {R : Symbol}

lemma spectrum_op_add_alpha (hR : SymbolSummable R) (x : ℝ) :
    spectrum ℂ (op α R (x + α)) = spectrum ℂ (op α R x) := by
  rw [op_conj_U hR x]
  exact spectrum.units_conjugate (u := Uunit α x)

lemma spectrum_op_add_mem_closure (hR : SymbolSummable R) {g : ℝ}
    (hg : g ∈ AddSubgroup.closure ({α, 1} : Set ℝ)) (x : ℝ) :
    spectrum ℂ (op α R (x + g)) = spectrum ℂ (op α R x) := by
  induction hg using AddSubgroup.closure_induction generalizing x with
  | mem g hg =>
    rcases hg with rfl | rfl
    · exact spectrum_op_add_alpha hR x
    · have := op_add_int α R x 1
      simp only [Int.cast_one] at this
      rw [this]
  | zero => simp
  | add g h _ _ ihg ihh => rw [← add_assoc, ihh, ihg]
  | neg g _ ih =>
    have := ih (x + -g)
    rw [neg_add_cancel_right] at this
    exact this.symm

/-- **Phase independence.** For irrational `α`, the spectrum of `R_x` is independent of `x`
(for an absolutely summable self-adjoint symbol). -/
theorem spectrum_op_eq (hα : Irrational α) (hR : SymbolSummable R)
    (hsa : SymbolSelfAdjoint R) (x y : ℝ) :
    spectrum ℂ (op α R y) = spectrum ℂ (op α R x) := by
  have hdense : Dense (AddSubgroup.closure ({α, 1} : Set ℝ) : Set ℝ) :=
    dense_addSubgroupClosure_pair_iff.2 (by simpa using hα)
  have key : ∀ x y : ℝ, spectrum ℂ (op α R y) ⊆ spectrum ℂ (op α R x) := by
    intro x y z hz
    rw [← (spectrum.isClosed (op α R x)).closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨δ, hδ, hcont⟩ := Metric.continuous_iff.1 (continuous_op (α := α) hR) y ε hε
    obtain ⟨g, hg1, hg2⟩ := Metric.dense_iff.1 hdense (y - x) δ hδ
    have hxg : dist (x + g) y < δ := by
      rw [Metric.mem_ball, Real.dist_eq] at hg1
      rw [Real.dist_eq]
      calc |x + g - y| = |g - (y - x)| := by ring_nf
        _ < δ := hg1
    have : IsStarNormal (op α R (x + g)) := (isSelfAdjoint_op hR hsa (x + g)).isStarNormal
    obtain ⟨w, hw, hzw⟩ := exists_mem_spectrum_dist_le (a := op α R (x + g)) hz
    rw [spectrum_op_add_mem_closure hR hg2 x] at hw
    refine ⟨w, hw, ?_⟩
    rw [dist_eq_norm]
    calc ‖z - w‖ ≤ ‖op α R (x + g) - op α R y‖ := hzw
      _ = dist (op α R (x + g)) (op α R y) := (dist_eq_norm _ _).symm
      _ < ε := hcont _ hxg
  exact (key x y).antisymm (key y x)

/-- The real spectrum is phase independent as well. -/
theorem spectrum_real_op_eq (hα : Irrational α) (hR : SymbolSummable R)
    (hsa : SymbolSelfAdjoint R) (x y : ℝ) :
    spectrum ℝ (op α R y) = spectrum ℝ (op α R x) := by
  rw [← spectrum.preimage_algebraMap ℂ (R := ℝ) (a := op α R y),
    ← spectrum.preimage_algebraMap ℂ (R := ℝ) (a := op α R x), spectrum_op_eq hα hR hsa x y]

/-- The common spectrum `Σ` of `H_x = U + U^{-1} + η(V_x + V_x^{-1}) + R_x`. -/
def Sigma (α η : ℝ) (R : Symbol) : Set ℝ := spectrum ℝ (H α η R 0)

theorem spectrum_H_eq_Sigma {η : ℝ} (hα : Irrational α) (hR : SymbolSummable R)
    (hsa : SymbolSelfAdjoint R) (x : ℝ) : spectrum ℝ (H α η R x) = Sigma α η R := by
  unfold Sigma H
  refine spectrum_real_op_eq hα ((amo_summable η).add hR) ?_ 0 x
  intro p
  simp [amo_selfAdjoint η p, hsa p]

/-- The common spectrum of the Fourier dual family `Ĥ_x`. -/
def SigmaDual (α η : ℝ) (R : Symbol) : Set ℝ := spectrum ℝ (Hdual α η R 0)

theorem spectrum_Hdual_eq_SigmaDual {η : ℝ} (hα : Irrational α) (hR : SymbolSummable R)
    (hsa : SymbolSelfAdjoint R) (x : ℝ) : spectrum ℝ (Hdual α η R x) = SigmaDual α η R := by
  unfold SigmaDual Hdual
  have hs : SymbolSelfAdjoint (amo η + R) := by
    intro p
    simp [amo_selfAdjoint η p, hsa p]
  exact spectrum_real_op_eq hα ((amo_summable η).add hR).fourier hs.fourier 0 x

end AMO
