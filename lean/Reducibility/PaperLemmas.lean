/-
# Paper I, Lemmas `t-lem:reducibility` and `t-lem:arithmetic-reducibility`

Both lemmas are proved here from the cited cocycle theorems (`ReducibilityInputs`, stated as
claims in `Reducibility.Claims`) and the parts of the argument that Paper I carries out itself:

* the conversion from rotation numbers to energies through the probability integral transform
  `N_*(dN) = dt` and `ρ = (1 - N)/2` (`Reducibility.Diophantine`);
* the full-measure Diophantine set `Θ_α` (Borel–Cantelli) and the removal of the resonances
  `4ρ ∈ 2αℤ + ℤ` (`Reducibility.Diophantine`);
* telescoping of the conjugacy, giving the uniform bounds (t-eq:all-irr-bounded)
  (`Reducibility.Basic`);
* the exponential small-divisor estimate and the analytic cohomological equation giving the
  hopping coboundary (t-eq:hopping-coboundary) (`Reducibility.SmallDivisors`).

The spectral setting is abstract: `ν` is the IDS measure (a probability measure with continuous
distribution function `N`), `Σ` a Borel set carrying the energies under consideration, and
`C E` the prepared analytic cocycle at energy `E`, whose fibered rotation number is
`ρ(E) = (1 - N(E))/2`.
-/
import Reducibility.Claims
import Reducibility.SmallDivisors

noncomputable section

open scoped Matrix.Norms.Operator ComplexConjugate
open MeasureTheory Set Filter AMO

namespace Red

/-- The rotation number read off the IDS: `ρ(E) = (1 - N(E))/2`. -/
def rhoOf (ν : Measure ℝ) (E : ℝ) : ℝ := (1 - (ν (Iic E)).toReal) / 2

lemma continuous_rhoOf {ν : Measure ℝ} (hF : Continuous fun t => (ν (Iic t)).toReal) :
    Continuous (rhoOf ν) :=
  (continuous_const.sub hF).div_const 2

/-- The real-axis restriction of an analytic conjugacy is continuous, `1`-periodic and has
determinant one. -/
lemma AnalyticConj.real_props {h : ℝ} (hh : 0 < h) (Z : AnalyticConj h) :
    Continuous (fun x : ℝ => Z.Z x) ∧ Function.Periodic (fun x : ℝ => Z.Z x) 1 ∧
      ∀ x : ℝ, (Z.Z x).det = 1 := by
  have hmem : ∀ x : ℝ, (x : ℂ) ∈ strip h := fun x => by simpa [strip] using hh
  refine ⟨?_, fun x => ?_, fun x => Z.det_eq_one _ (hmem x)⟩
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (Z.analytic i j).continuousOn.comp_continuous Complex.continuous_ofReal hmem
  · simp only
    push_cast
    exact Z.periodic _

/-- A rotations-reducible cocycle has uniformly bounded iterates (paper (t-eq:all-irr-bounded)). -/
theorem RotationsReducible.bounded {α w : ℝ} {C : AnalyticCocycle w}
    (h : RotationsReducible α C) : ∃ K : ℝ, ∀ (n : ℕ) (x : ℝ), ‖iter α C.real' n x‖ ≤ K := by
  obtain ⟨h', hh', Z, φ, -, -, -, hconj⟩ := h
  obtain ⟨hc, hp, hdet⟩ := Z.real_props hh'
  obtain ⟨K, hK⟩ := exists_bound_of_periodic hc hp
  exact ⟨4 * K ^ 2, fun n x => norm_iter_le_of_rotReducible' hconj hdet hK n x⟩

/-- A measurable null set containing the complement of a co-null set, pulled back along `ρ`,
has `ν`-measure zero; its complement gives a Borel full-measure set of good energies. -/
lemma exists_good_set {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hF : Continuous fun t => (ν (Iic t)).toReal) {Sig B : Set ℝ} (hSig : MeasurableSet Sig)
    (hB : volume B = 0) :
    ∃ G ⊆ Sig, MeasurableSet G ∧ ν (Sig \ G) = 0 ∧ ∀ E ∈ G, rhoOf ν E ∉ B := by
  obtain ⟨N, hBN, hNmeas, hN0⟩ := exists_measurable_superset_of_null hB
  refine ⟨Sig ∩ rhoOf ν ⁻¹' Nᶜ, inter_subset_left,
    hSig.inter ((continuous_rhoOf hF).measurable hNmeas.compl), ?_,
    fun E hE hEB => hE.2 (hBN hEB)⟩
  refine measure_mono_null (fun E hE => ?_) (measure_rho_preimage_null ν hF hN0)
  simp only [mem_diff, mem_inter_iff, mem_preimage, mem_compl_iff, not_and, not_not] at hE
  exact hE.2 hE.1

/-- **Lemma `t-lem:reducibility` (rotations reducibility for every irrational frequency).**
If every cocycle in `Σ` is subcritical and has fibered rotation number `ρ(E) = (1-N(E))/2`, then
there is a Borel set `G ⊆ Σ` of full `dN` measure on which `C_E` is analytically rotations
reducible by a degree-zero conjugacy, and the cocycle products are uniformly bounded. -/
theorem rotations_reducibility (I : ReducibilityInputs) {α : ℝ} (hα : Irrational α)
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (hF : Continuous fun t => (ν (Iic t)).toReal)
    {Sig : Set ℝ} (hSig : MeasurableSet Sig) {w : ℝ} (C : ℝ → AnalyticCocycle w)
    (hsub : ∀ E ∈ Sig, ∃ h > (0 : ℝ), SubcriticalOn α (C E) h)
    (hrot : ∀ E ∈ Sig, IsRotationNumber α (C E).real' (rhoOf ν E)) :
    ∃ G ⊆ Sig, MeasurableSet G ∧ ν (Sig \ G) = 0 ∧ ∀ E ∈ G,
      RotationsReducible α (C E) ∧ ∃ K : ℝ, ∀ (n : ℕ) (x : ℝ), ‖iter α (C E).real' n x‖ ≤ K := by
  obtain ⟨𝓡, h𝓡, -, hR⟩ := I.rotations hα
  obtain ⟨G, hGS, hGm, hG0, hGgood⟩ := exists_good_set hF hSig h𝓡
  refine ⟨G, hGS, hGm, hG0, fun E hE => ?_⟩
  obtain ⟨h, hh, hs⟩ := hsub E (hGS hE)
  have hAR := I.almost hα (C E) hh hs
  have hRR := hR (C E) hAR (hrot E (hGS hE)) (by simpa using hGgood E hE)
  exact ⟨hRR, hRR.bounded⟩

/-- Membership in `Θ_α` excludes the resonances `2ρ + kα ∈ ℤ` (the first condition in
(t-eq:arithmetic-nonresonance)). -/
lemma nonresonant_of_mem_ThetaSet {α r : ℝ} (hr : r ∈ ThetaSet α) (k m : ℤ) :
    2 * r + k * α ≠ m := by
  intro h
  simp only [ThetaSet, mem_iUnion] at hr
  obtain ⟨τ, -, κ, hκ, hbound⟩ := hr
  have h1 := hbound k
  rw [h, torusDist, round_intCast, sub_self, abs_zero] at h1
  have : 0 < κ * (1 + |(k : ℝ)|) ^ (-τ) := mul_pos hκ (Real.rpow_pos_of_pos (by positivity) _)
  linarith

/-- **Lemma `t-lem:arithmetic-reducibility`.**  Suppose every cocycle `C_E`, `E ∈ Σ_loc`, is
subcritical on a strip of width `h_E` with `2πh_E > β(α)`, has fibered rotation number
`ρ(E) = (1-N(E))/2`, and its hopping phase `p_E = (2πi)⁻¹ log q_E` has Fourier coefficients
`p̂_E` with `|p̂_E(k)| ≤ C_E e^{-2πh_E|k|}` and `β(α) + δ_E < 2πh_E`.  Then there is a Borel set
`G ⊆ Σ_loc` of full `dN` measure such that for `E ∈ G`:

* `C_E` is analytically reducible to a constant rotation;
* `ρ(E) ∈ Θ_α`, `2ρ(E) ∉ αℤ + ℤ` and `4ρ(E) ∉ 2αℤ + ℤ` (t-eq:arithmetic-nonresonance);

and for every `E ∈ Σ_loc` the scalar equation `χ_E(x + α) - χ_E(x) = p_E(x) - ψ(E)` has the
analytic solution `χ_E = ∑ p̂_E(k)/(e(kα) - 1) e(kx)`, real when `p_E` is real
(t-eq:hopping-coboundary). -/
theorem arithmetic_reducibility (I : ReducibilityInputs) {α : ℝ} (hα : Irrational α)
    (hβ : beta α ≠ ⊤) {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hF : Continuous fun t => (ν (Iic t)).toReal) {Sig : Set ℝ} (hSig : MeasurableSet Sig)
    {w : ℝ} (C : ℝ → AnalyticCocycle w)
    (hsub : ∀ E ∈ Sig, ∃ h > (0 : ℝ), ENNReal.ofReal (2 * Real.pi * h) > beta α ∧
      SubcriticalOn α (C E) h)
    (hrot : ∀ E ∈ Sig, IsRotationNumber α (C E).real' (rhoOf ν E))
    (p : ℝ → ℤ → ℂ)
    (hp : ∀ E ∈ Sig, ∃ Cst h δ : ℝ, 0 < δ ∧ (beta α).toReal + δ < 2 * Real.pi * h ∧
      (∀ k : ℤ, ‖p E k‖ ≤ Cst * Real.exp (-(2 * Real.pi * h) * |(k : ℝ)|)) ∧
      ∀ k, p E (-k) = conj (p E k)) :
    (∃ G ⊆ Sig, MeasurableSet G ∧ ν (Sig \ G) = 0 ∧ ∀ E ∈ G,
      (∃ r, ReducibleToRotation α (C E) r) ∧ rhoOf ν E ∈ ThetaSet α ∧
      (∀ k m : ℤ, 2 * rhoOf ν E + k * α ≠ m) ∧
      ¬ ∃ j m : ℤ, 4 * rhoOf ν E = 2 * α * j + m) ∧
    ∀ E ∈ Sig, ∀ x : ℝ,
      fourierSum (chiHat α (p E)) (x + α) - fourierSum (chiHat α (p E)) x =
        fourierSum (p E) x - p E 0 ∧
      (fourierSum (chiHat α (p E)) x).im = 0 := by
  refine ⟨?_, fun E hE x => ?_⟩
  · set B : Set ℝ := (ThetaSet α)ᶜ ∪ {r | ∃ j m : ℤ, 4 * r = 2 * α * j + m}
    have hB : volume B = 0 :=
      measure_union_null (volume_compl_ThetaSet α) (volume_resonant4 α)
    obtain ⟨G, hGS, hGm, hG0, hGgood⟩ := exists_good_set hF hSig hB
    refine ⟨G, hGS, hGm, hG0, fun E hE => ?_⟩
    have hgood := hGgood E hE
    have hΘ : rhoOf ν E ∈ ThetaSet α := by
      by_contra h; exact hgood (Or.inl h)
    have hres : ¬ ∃ j m : ℤ, 4 * rhoOf ν E = 2 * α * j + m := fun h => hgood (Or.inr h)
    obtain ⟨h, hh, hβh, hs⟩ := hsub E (hGS hE)
    exact ⟨I.arithmetic hα (C E) hh hβh hs (hrot E (hGS hE)) hΘ, hΘ,
      nonresonant_of_mem_ThetaSet hΘ, hres⟩
  · obtain ⟨Cst, h, δ, hδ, hh, hbound, hsym⟩ := hp E hE
    exact ⟨cohomological_eq hα hβ hδ hbound hh x, chi_im_eq_zero hsym x⟩

end Red
