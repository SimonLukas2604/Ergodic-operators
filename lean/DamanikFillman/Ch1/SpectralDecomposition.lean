/-
Formalization of Damanik–Fillman, *One-Dimensional Ergodic Schrödinger Operators I*, Chapter 1.

# Spectral decompositions  (book §1.6.1, pp. 46–50)

For a bounded self-adjoint operator `A` we define the spectral subspaces (Definition 1.6.1)
* `DF.ppSubspace A hA` — `H_pp`: vectors whose spectral measure is pure point;
* `DF.acSubspace A hA` — `H_ac`: spectral measure absolutely continuous;
* `DF.cSubspace A hA` — `H_c`: spectral measure continuous (no atoms);
* `DF.sSubspace A hA` — `H_s`: spectral measure singular;
* `DF.scSubspace A hA` — `H_sc = H_c ⊓ H_s`.

Main results
* Theorem 1.6.2(a): the subspaces are closed (`DF.isClosed_ppSubspace`, …) and `A`-invariant
  (`DF.apply_mem_ppSubspace`, …);
* Theorem 1.6.2(b): pairwise orthogonality (`DF.acSubspace_orthogonal_sSubspace`,
  `DF.cSubspace_orthogonal_ppSubspace`, and consequences);
* Theorem 1.6.2(c): every vector decomposes as `φ = φ_ac + φ_sc + φ_pp`
  (`DF.exists_decomposition`);
* Proposition 1.6.5(a),(c): eigenvectors lie in `H_pp` and have spectral measure
  `‖ψ‖² δ_E` (`DF.spectralMeasure_eigenvector`), and `Aψ = Eψ ↔ χ_{E}(A) ψ = ψ`
  (`DF.eigen_iff_specProj_singleton`);
* Proposition 1.6.5(d): `H_pp` is contained in the closed span of the eigenvectors
  (`DF.ppSubspace_le_closure_span_eigenvectors`).

Deviations
* The spectra `σ_•(A) = σ(A|_{H_•})` (Definition 1.6.3), Proposition 1.6.5(e) and
  Theorem 1.6.6 (cyclic vectors) are not formalized.

No `Statement` props are introduced in this file.
-/
import DamanikFillman.Ch1.BorelCalculus

noncomputable section

open scoped InnerProductSpace ComplexConjugate NNReal ENNReal Topology
open MeasureTheory Set Filter

namespace DF

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A : H →L[ℂ] H} {hA : IsSelfAdjoint A}

/-! ### Null sets of spectral measures -/

lemma specProj_apply_eq_zero_iff {S : Set ℝ} (hS : MeasurableSet S) (φ : H) :
    specProj A hA S φ = 0 ↔ spectralMeasure A hA φ S = 0 := by
  rw [← norm_eq_zero, ← pow_eq_zero_iff two_ne_zero, norm_specProj_apply_sq hS,
    measureReal_eq_zero_iff]

lemma specProj_add_compl {S : Set ℝ} (hS : MeasurableSet S) :
    specProj A hA S + specProj A hA Sᶜ = 1 := by
  rw [specProj, specProj, ← borelCalc_add (isBddBorel_indicator hS)
    (isBddBorel_indicator hS.compl), indicator_self_add_compl]
  exact borelCalc_one

lemma specProj_commute_apply (S : Set ℝ) (hS : MeasurableSet S) (φ : H) :
    specProj A hA S (A φ) = A (specProj A hA S φ) := by
  have := congrArg (fun T : H →L[ℂ] H => T φ) (borelCalc_commute (A := A) (hA := hA)
    (isBddBorel_indicator hS))
  exact this

lemma spec_null_add {S : Set ℝ} (hS : MeasurableSet S) {φ ψ : H}
    (hφ : spectralMeasure A hA φ S = 0) (hψ : spectralMeasure A hA ψ S = 0) :
    spectralMeasure A hA (φ + ψ) S = 0 := by
  rw [← specProj_apply_eq_zero_iff hS] at hφ hψ ⊢
  rw [map_add, hφ, hψ, add_zero]

lemma spec_null_smul {S : Set ℝ} (c : ℂ) {φ : H} (hφ : spectralMeasure A hA φ S = 0) :
    spectralMeasure A hA (c • φ) S = 0 := by
  rw [spectralMeasure_smul, Measure.smul_apply, hφ, smul_zero]

lemma spec_null_zero (S : Set ℝ) : spectralMeasure A hA (0 : H) S = 0 := by
  have := spectralMeasure_univ A hA (0 : H)
  rw [norm_zero, zero_pow two_ne_zero, ENNReal.ofReal_zero] at this
  exact measure_mono_null (subset_univ S) this

lemma spec_null_apply {S : Set ℝ} (hS : MeasurableSet S) {φ : H}
    (hφ : spectralMeasure A hA φ S = 0) : spectralMeasure A hA (A φ) S = 0 := by
  rw [← specProj_apply_eq_zero_iff hS] at hφ ⊢
  rw [specProj_commute_apply S hS, hφ, map_zero]

lemma spec_null_of_tendsto {S : Set ℝ} (hS : MeasurableSet S) {φ : ℕ → H} {ψ : H}
    (hlim : Tendsto φ atTop (𝓝 ψ)) (hφ : ∀ n, spectralMeasure A hA (φ n) S = 0) :
    spectralMeasure A hA ψ S = 0 := by
  rw [← specProj_apply_eq_zero_iff hS]
  have h1 : Tendsto (fun n => specProj A hA S (φ n)) atTop (𝓝 (specProj A hA S ψ)) :=
    ((specProj A hA S).continuous.tendsto ψ).comp hlim
  have h2 : (fun n => specProj A hA S (φ n)) = fun _ => 0 :=
    funext fun n => (specProj_apply_eq_zero_iff hS _).2 (hφ n)
  rw [h2] at h1
  exact tendsto_nhds_unique h1 tendsto_const_nhds

/-- If `μ_φ(S) = 0` and `μ_ψ(Sᶜ) = 0` then `φ ⊥ ψ`. -/
lemma inner_eq_zero_of_spec_null {S : Set ℝ} (hS : MeasurableSet S) {φ ψ : H}
    (hφ : spectralMeasure A hA φ S = 0) (hψ : spectralMeasure A hA ψ Sᶜ = 0) :
    ⟪φ, ψ⟫_ℂ = 0 := by
  rw [← specProj_apply_eq_zero_iff hS] at hφ
  rw [← specProj_apply_eq_zero_iff hS.compl] at hψ
  have hψ' : ψ = specProj A hA S ψ := by
    have := congrArg (fun T : H →L[ℂ] H => T ψ) (specProj_add_compl (A := A) (hA := hA) hS)
    simp only [_root_.add_apply, one_apply_eq_self, hψ, add_zero] at this
    exact this.symm
  have hsym := (isSelfAdjoint_specProj (A := A) (hA := hA) hS).isSymmetric φ ψ
  simp only [ContinuousLinearMap.coe_coe] at hsym
  rw [hψ', ← hsym, hφ, inner_zero_left]

/-! ### The spectral subspaces (Definition 1.6.1) -/

variable (A hA)

/-- `H_pp`: vectors with pure point spectral measure (supported on a countable set). -/
def ppSubspace : Submodule ℂ H where
  carrier := {φ | ∃ C : Set ℝ, C.Countable ∧ spectralMeasure A hA φ Cᶜ = 0}
  add_mem' := by
    rintro φ ψ ⟨C, hC, hφ⟩ ⟨D, hD, hψ⟩
    refine ⟨C ∪ D, hC.union hD, spec_null_add (hC.union hD).measurableSet.compl ?_ ?_⟩
    · exact measure_mono_null (compl_subset_compl.2 subset_union_left) hφ
    · exact measure_mono_null (compl_subset_compl.2 subset_union_right) hψ
  zero_mem' := ⟨∅, countable_empty, spec_null_zero _⟩
  smul_mem' := by
    rintro c φ ⟨C, hC, hφ⟩
    exact ⟨C, hC, spec_null_smul c hφ⟩

/-- `H_s`: vectors with singular spectral measure. -/
def sSubspace : Submodule ℂ H where
  carrier := {φ | ∃ N : Set ℝ, MeasurableSet N ∧ volume N = 0 ∧ spectralMeasure A hA φ Nᶜ = 0}
  add_mem' := by
    rintro φ ψ ⟨N, hN, hN0, hφ⟩ ⟨M, hM, hM0, hψ⟩
    refine ⟨N ∪ M, hN.union hM, measure_union_null hN0 hM0,
      spec_null_add (hN.union hM).compl ?_ ?_⟩
    · exact measure_mono_null (compl_subset_compl.2 subset_union_left) hφ
    · exact measure_mono_null (compl_subset_compl.2 subset_union_right) hψ
  zero_mem' := ⟨∅, MeasurableSet.empty, measure_empty, spec_null_zero _⟩
  smul_mem' := by
    rintro c φ ⟨N, hN, hN0, hφ⟩
    exact ⟨N, hN, hN0, spec_null_smul c hφ⟩

/-- `H_ac`: vectors with absolutely continuous spectral measure. -/
def acSubspace : Submodule ℂ H where
  carrier := {φ | ∀ N : Set ℝ, MeasurableSet N → volume N = 0 → spectralMeasure A hA φ N = 0}
  add_mem' := fun hφ hψ N hN hN0 => spec_null_add hN (hφ N hN hN0) (hψ N hN hN0)
  zero_mem' := fun N _ _ => spec_null_zero N
  smul_mem' := fun c _ hφ N hN hN0 => spec_null_smul c (hφ N hN hN0)

/-- `H_c`: vectors with continuous (atomless) spectral measure. -/
def cSubspace : Submodule ℂ H where
  carrier := {φ | ∀ E : ℝ, spectralMeasure A hA φ {E} = 0}
  add_mem' := fun hφ hψ E => spec_null_add (measurableSet_singleton E) (hφ E) (hψ E)
  zero_mem' := fun E => spec_null_zero {E}
  smul_mem' := fun c _ hφ E => spec_null_smul c (hφ E)

/-- `H_sc = H_c ∩ H_s`: singular continuous spectral measure. -/
def scSubspace : Submodule ℂ H := cSubspace A hA ⊓ sSubspace A hA

variable {A hA}

lemma mem_acSubspace_iff (φ : H) : φ ∈ acSubspace A hA ↔ spectralMeasure A hA φ ≪ volume :=
  ⟨fun h => Measure.AbsolutelyContinuous.mk fun N hN hN0 => h N hN hN0,
    fun h N _ hN0 => h hN0⟩

lemma mem_sSubspace_iff (φ : H) : φ ∈ sSubspace A hA ↔ spectralMeasure A hA φ ⟂ₘ volume := by
  constructor
  · rintro ⟨N, hN, hN0, hφ⟩
    exact ⟨Nᶜ, hN.compl, hφ, by rwa [compl_compl]⟩
  · rintro ⟨S, hS, hφ, hS0⟩
    exact ⟨Sᶜ, hS.compl, hS0, by rwa [compl_compl]⟩

lemma mem_cSubspace_iff (φ : H) : φ ∈ cSubspace A hA ↔ ∀ E, spectralMeasure A hA φ {E} = 0 :=
  Iff.rfl

lemma mem_ppSubspace_iff (φ : H) :
    φ ∈ ppSubspace A hA ↔ ∃ C : Set ℝ, C.Countable ∧ spectralMeasure A hA φ Cᶜ = 0 := Iff.rfl

lemma scSubspace_le_cSubspace : scSubspace A hA ≤ cSubspace A hA := inf_le_left

lemma scSubspace_le_sSubspace : scSubspace A hA ≤ sSubspace A hA := inf_le_right

lemma ppSubspace_le_sSubspace : ppSubspace A hA ≤ sSubspace A hA := by
  rintro φ ⟨C, hC, hφ⟩
  exact ⟨C, hC.measurableSet, hC.measure_zero _, hφ⟩

lemma acSubspace_le_cSubspace : acSubspace A hA ≤ cSubspace A hA := fun _ hφ E =>
  hφ {E} (measurableSet_singleton E) Real.volume_singleton

/-! ### Theorem 1.6.2(a): closed and invariant -/

theorem isClosed_acSubspace : IsClosed (acSubspace A hA : Set H) := by
  refine isSeqClosed_iff_isClosed.1 fun φ ψ hφ hlim N hN hN0 =>
    spec_null_of_tendsto hN hlim fun n => hφ n N hN hN0

theorem isClosed_cSubspace : IsClosed (cSubspace A hA : Set H) := by
  refine isSeqClosed_iff_isClosed.1 fun φ ψ hφ hlim E =>
    spec_null_of_tendsto (measurableSet_singleton E) hlim fun n => hφ n E

theorem isClosed_ppSubspace : IsClosed (ppSubspace A hA : Set H) := by
  refine isSeqClosed_iff_isClosed.1 fun φ ψ hφ hlim => ?_
  choose C hC hφC using hφ
  refine ⟨⋃ n, C n, countable_iUnion hC, ?_⟩
  refine spec_null_of_tendsto (MeasurableSet.iUnion fun n => (hC n).measurableSet).compl hlim
    fun n => measure_mono_null (compl_subset_compl.2 (subset_iUnion C n)) (hφC n)

theorem isClosed_sSubspace : IsClosed (sSubspace A hA : Set H) := by
  refine isSeqClosed_iff_isClosed.1 fun φ ψ hφ hlim => ?_
  choose N hN hN0 hφN using hφ
  refine ⟨⋃ n, N n, MeasurableSet.iUnion hN, measure_iUnion_null hN0, ?_⟩
  exact spec_null_of_tendsto (MeasurableSet.iUnion hN).compl hlim
    fun n => measure_mono_null (compl_subset_compl.2 (subset_iUnion N n)) (hφN n)

theorem isClosed_scSubspace : IsClosed (scSubspace A hA : Set H) :=
  isClosed_cSubspace.inter isClosed_sSubspace

theorem apply_mem_acSubspace {φ : H} (hφ : φ ∈ acSubspace A hA) : A φ ∈ acSubspace A hA :=
  fun N hN hN0 => spec_null_apply hN (hφ N hN hN0)

theorem apply_mem_cSubspace {φ : H} (hφ : φ ∈ cSubspace A hA) : A φ ∈ cSubspace A hA :=
  fun E => spec_null_apply (measurableSet_singleton E) (hφ E)

theorem apply_mem_ppSubspace {φ : H} (hφ : φ ∈ ppSubspace A hA) : A φ ∈ ppSubspace A hA := by
  obtain ⟨C, hC, h⟩ := hφ
  exact ⟨C, hC, spec_null_apply hC.measurableSet.compl h⟩

theorem apply_mem_sSubspace {φ : H} (hφ : φ ∈ sSubspace A hA) : A φ ∈ sSubspace A hA := by
  obtain ⟨N, hN, hN0, h⟩ := hφ
  exact ⟨N, hN, hN0, spec_null_apply hN.compl h⟩

theorem apply_mem_scSubspace {φ : H} (hφ : φ ∈ scSubspace A hA) : A φ ∈ scSubspace A hA :=
  ⟨apply_mem_cSubspace hφ.1, apply_mem_sSubspace hφ.2⟩

/-! ### Theorem 1.6.2(b): orthogonality -/

theorem acSubspace_orthogonal_sSubspace {φ ψ : H} (hφ : φ ∈ acSubspace A hA)
    (hψ : ψ ∈ sSubspace A hA) : ⟪φ, ψ⟫_ℂ = 0 := by
  obtain ⟨N, hN, hN0, hψN⟩ := hψ
  exact inner_eq_zero_of_spec_null hN (hφ N hN hN0) hψN

theorem cSubspace_orthogonal_ppSubspace {φ ψ : H} (hφ : φ ∈ cSubspace A hA)
    (hψ : ψ ∈ ppSubspace A hA) : ⟪φ, ψ⟫_ℂ = 0 := by
  obtain ⟨C, hC, hψC⟩ := hψ
  refine inner_eq_zero_of_spec_null hC.measurableSet ?_ hψC
  rw [← biUnion_of_singleton C]
  exact (measure_biUnion_null_iff hC).2 fun E _ => hφ E

theorem acSubspace_orthogonal_scSubspace {φ ψ : H} (hφ : φ ∈ acSubspace A hA)
    (hψ : ψ ∈ scSubspace A hA) : ⟪φ, ψ⟫_ℂ = 0 :=
  acSubspace_orthogonal_sSubspace hφ hψ.2

theorem acSubspace_orthogonal_ppSubspace {φ ψ : H} (hφ : φ ∈ acSubspace A hA)
    (hψ : ψ ∈ ppSubspace A hA) : ⟪φ, ψ⟫_ℂ = 0 :=
  acSubspace_orthogonal_sSubspace hφ (ppSubspace_le_sSubspace hψ)

theorem scSubspace_orthogonal_ppSubspace {φ ψ : H} (hφ : φ ∈ scSubspace A hA)
    (hψ : ψ ∈ ppSubspace A hA) : ⟪φ, ψ⟫_ℂ = 0 :=
  cSubspace_orthogonal_ppSubspace hφ.1 hψ

/-! ### Theorem 1.6.2(c): the decomposition -/

lemma spectralMeasure_specProj {S : Set ℝ} (hS : MeasurableSet S) (φ : H) :
    spectralMeasure A hA (specProj A hA S φ) = (spectralMeasure A hA φ).restrict S := by
  rw [specProj, spectralMeasure_borelCalc (isBddBorel_indicator hS)]
  have : (fun x => ((‖S.indicator (fun _ => (1 : ℂ)) x‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞)) =
      S.indicator fun _ => 1 := by
    funext x; by_cases h : x ∈ S <;> simp [h]
  rw [this, withDensity_indicator hS]
  exact withDensity_one

lemma specProj_union {S T : Set ℝ} (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hST : Disjoint S T) : specProj A hA (S ∪ T) = specProj A hA S + specProj A hA T := by
  rw [specProj, specProj, specProj, ← borelCalc_add (isBddBorel_indicator hS)
    (isBddBorel_indicator hT), indicator_union_of_disjoint hST]
  rfl

/-- **Theorem 1.6.2(c)**: `H = H_ac ⊕ H_sc ⊕ H_pp` (existence of the decomposition; the
summands are pairwise orthogonal by part (b)). -/
theorem exists_decomposition (φ : H) :
    ∃ a ∈ acSubspace A hA, ∃ s ∈ scSubspace A hA, ∃ p ∈ ppSubspace A hA, φ = a + s + p := by
  set μ := spectralMeasure A hA φ
  -- atoms
  set C : Set ℝ := {E | 0 < μ {E}}
  have hC : C.Countable := Measure.countable_meas_pos_of_disjoint_iUnion
    (As := fun E : ℝ => ({E} : Set ℝ)) (fun E => measurableSet_singleton E)
    (fun E F hEF => disjoint_singleton.2 hEF)
  have hCm : MeasurableSet C := hC.measurableSet
  -- singular part carried by a null set
  obtain ⟨T, hT, hTs, hTv⟩ := Measure.mutuallySingular_singularPart μ volume
  set N : Set ℝ := Tᶜ
  have hN : MeasurableSet N := hT.compl
  refine ⟨specProj A hA (Nᶜ \ C) φ, ?_, specProj A hA (N \ C) φ, ⟨?_, ?_⟩,
    specProj A hA C φ, ?_, ?_⟩
  · -- absolutely continuous part
    intro M hM hM0
    rw [spectralMeasure_specProj (hN.compl.diff hCm), Measure.restrict_apply hM]
    have hdec : spectralMeasure A hA φ = μ.singularPart volume + volume.withDensity
        (μ.rnDeriv volume) := Measure.haveLebesgueDecomposition_add μ volume
    rw [hdec, Measure.add_apply]
    refine add_eq_zero.2 ⟨measure_mono_null (fun x hx => ?_) hTs, ?_⟩
    · exact by simpa [N] using hx.2.1
    · exact withDensity_absolutelyContinuous _ _ (measure_mono_null inter_subset_left hM0)
  · -- continuous
    intro E
    rw [spectralMeasure_specProj (hN.diff hCm), Measure.restrict_apply (measurableSet_singleton E)]
    by_cases hE : E ∈ C
    · rw [show {E} ∩ (N \ C) = ∅ by
        ext x
        simp only [mem_inter_iff, mem_singleton_iff, mem_diff, mem_empty_iff_false, iff_false]
        rintro ⟨rfl, _, hx⟩
        exact hx hE]
      exact measure_empty
    · exact measure_mono_null inter_subset_left (by simpa [C] using hE)
  · -- singular
    refine ⟨N, hN, hTv, ?_⟩
    rw [spectralMeasure_specProj (hN.diff hCm), Measure.restrict_apply hN.compl]
    exact measure_mono_null (fun x hx => absurd hx.2.1 hx.1) measure_empty
  · -- pure point
    refine ⟨C, hC, ?_⟩
    rw [spectralMeasure_specProj hCm, Measure.restrict_apply hCm.compl]
    simp
  · -- the sum
    have h1 := specProj_union (A := A) (hA := hA) (hN.compl.diff hCm) (hN.diff hCm)
      (by rw [disjoint_iff]; ext x; simp; tauto)
    have h2 := specProj_union (A := A) (hA := hA) ((hN.compl.diff hCm).union (hN.diff hCm)) hCm
      (by rw [disjoint_iff]; ext x; simp; tauto)
    have h3 : ((Nᶜ \ C) ∪ (N \ C)) ∪ C = univ := by ext x; simp; tauto
    rw [h3, specProj_univ, h1] at h2
    have := congrArg (fun T : H →L[ℂ] H => T φ) h2
    simpa using this

/-! ### Eigenvectors (Proposition 1.6.5) -/

/-- If `Aψ = Eψ` then `μ_ψ` is concentrated at `E`, i.e. `μ_ψ = ‖ψ‖² δ_E`. -/
theorem spectralMeasure_eigenvector {ψ : H} {E : ℝ} (h : A ψ = (E : ℂ) • ψ) :
    spectralMeasure A hA ψ {E}ᶜ = 0 := by
  have hcont : Continuous fun x : ℝ => (x - E) ^ 2 := by fun_prop
  have hint := integral_spectralMeasure_re A hA ψ hcont
  have hcfc : cfc (fun x : ℝ => (x - E) ^ 2) A = (A - algebraMap ℝ (H →L[ℂ] H) E) ^ 2 := by
    rw [cfc_pow (fun x : ℝ => x - E) 2 A, cfc_sub (fun x : ℝ => x) (fun _ => E) A, cfc_id' ℝ A,
      cfc_const E A]
  have hker : (A - algebraMap ℝ (H →L[ℂ] H) E) ψ = 0 := by
    rw [ContinuousLinearMap.sub_apply, Algebra.algebraMap_eq_smul_one,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, h, Complex.coe_smul, sub_self]
  rw [hcfc, pow_two, ContinuousLinearMap.mul_apply, hker, map_zero, inner_zero_right,
    map_zero] at hint
  have hae := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg (x - E))
    (integrable_spectralMeasure A hA ψ hcont)).1 hint
  rw [Filter.EventuallyEq, ae_iff] at hae
  refine measure_mono_null (fun x hx => ?_) hae
  simp only [mem_compl_iff, mem_singleton_iff] at hx
  simp only [mem_setOf_eq, Pi.zero_apply, pow_eq_zero_iff two_ne_zero, sub_eq_zero]
  exact hx

/-- **Proposition 1.6.5(a)**: every eigenvector lies in `H_pp`. -/
theorem eigenvector_mem_ppSubspace {ψ : H} {E : ℝ} (h : A ψ = (E : ℂ) • ψ) :
    ψ ∈ ppSubspace A hA :=
  ⟨{E}, countable_singleton E, spectralMeasure_eigenvector h⟩

lemma specProj_apply_eq_self_iff {S : Set ℝ} (hS : MeasurableSet S) (ψ : H) :
    specProj A hA S ψ = ψ ↔ spectralMeasure A hA ψ Sᶜ = 0 := by
  have hsum := congrArg (fun T : H →L[ℂ] H => T ψ) (specProj_add_compl (A := A) (hA := hA) hS)
  simp only [_root_.add_apply, one_apply_eq_self] at hsum
  rw [← specProj_apply_eq_zero_iff hS.compl]
  constructor
  · intro h; rw [h] at hsum
    have := congrArg (fun v => v - ψ) hsum
    simpa using this
  · intro h; rw [h, add_zero] at hsum; exact hsum

lemma abs_le_norm_of_mem_spectrum {x : ℝ} (hx : x ∈ spectrum ℝ A) : |x| ≤ ‖A‖ := by
  have := spectrum.subset_closedBall_norm_mul (𝕜 := ℝ) A hx
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this
  exact this.trans (mul_le_of_le_one_right (norm_nonneg _)
    (by exact ContinuousLinearMap.norm_id_le))

/-- `A χ_{E}(A) = E χ_{E}(A)`. -/
theorem mul_specProj_singleton (E : ℝ) :
    A * specProj A hA {E} = (E : ℂ) • specProj A hA {E} := by
  have hi := isBddBorel_indicator (measurableSet_singleton E)
  have e := borelCalc_truncId (hA := hA)
  refine (congrArg (· * specProj A hA {E}) e.symm).trans ?_
  rw [specProj, ← borelCalc_mul isBddBorel_truncId hi, ← borelCalc_const_mul hi]
  refine borelCalc_congr_spectrum (isBddBorel_truncId.mul hi) (hi.const_mul _) fun x hx => ?_
  have hx' := abs_le_norm_of_mem_spectrum hx
  by_cases hxE : x = E
  · subst hxE
    simp only [Pi.mul_apply, truncId, indicator_of_mem (mem_singleton x), mul_one]
    rw [min_eq_left (abs_le.1 hx').2, max_eq_right (abs_le.1 hx').1]
  · simp only [Pi.mul_apply, indicator_of_notMem (show x ∉ ({E} : Set ℝ) from hxE), mul_zero]

theorem apply_specProj_singleton (E : ℝ) (φ : H) :
    A (specProj A hA {E} φ) = (E : ℂ) • specProj A hA {E} φ := by
  have := congrArg (fun T : H →L[ℂ] H => T φ) (mul_specProj_singleton (A := A) (hA := hA) E)
  simpa using this

/-- **Proposition 1.6.5(c)**: `Aψ = Eψ` iff `ψ ∈ Ran χ_{E}(A)`. -/
theorem eigen_iff_specProj_singleton (ψ : H) (E : ℝ) :
    A ψ = (E : ℂ) • ψ ↔ specProj A hA {E} ψ = ψ := by
  constructor
  · intro h
    exact (specProj_apply_eq_self_iff (measurableSet_singleton E) ψ).2
      (spectralMeasure_eigenvector h)
  · intro h
    rw [← h]
    exact apply_specProj_singleton E ψ

lemma specProj_finset (F : Finset ℝ) :
    specProj A hA (F : Set ℝ) = ∑ E ∈ F, specProj A hA {E} := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [specProj_empty]
  | insert a F ha ih =>
    rw [Finset.coe_insert, insert_eq, specProj_union (measurableSet_singleton a)
      F.finite_toSet.measurableSet (disjoint_singleton_left.2 ha), ih, Finset.sum_insert ha]

/-- **Proposition 1.6.5(d)**: `H_pp` is contained in the closed linear span of the
eigenvectors of `A` (the reverse inclusion follows from part (a) and closedness). -/
theorem ppSubspace_le_closure_span_eigenvectors :
    ppSubspace A hA ≤
      (Submodule.span ℂ {v : H | ∃ E : ℝ, A v = (E : ℂ) • v}).topologicalClosure := by
  rintro ψ ⟨C, hC, hψC⟩
  set V := (Submodule.span ℂ {v : H | ∃ E : ℝ, A v = (E : ℂ) • v})
  have hψ : specProj A hA C ψ = ψ := (specProj_apply_eq_self_iff hC.measurableSet ψ).2 hψC
  rcases C.eq_empty_or_nonempty with hCe | hCne
  · rw [hCe, specProj_empty] at hψ
    rw [← hψ]
    exact V.topologicalClosure.zero_mem
  obtain ⟨e, he⟩ := hC.exists_eq_range hCne
  let S : ℕ → Finset ℝ := fun n => (Finset.range n).image e
  have hmem : ∀ n, specProj A hA (S n : Set ℝ) ψ ∈ V := by
    intro n
    rw [specProj_finset, _root_.sum_apply]
    refine Submodule.sum_mem _ fun E _ => Submodule.subset_span ⟨E, ?_⟩
    exact apply_specProj_singleton E ψ
  have hlim : Tendsto (fun n => specProj A hA (S n : Set ℝ) ψ) atTop
      (𝓝 (specProj A hA C ψ)) := by
    refine tendsto_borelCalc_apply (C := 1)
      (fun n => measurable_const.indicator (S n).finite_toSet.measurableSet)
      (measurable_const.indicator hC.measurableSet)
      (fun n x => by by_cases h : x ∈ (S n : Set ℝ) <;> simp [h])
      (fun x => by by_cases h : x ∈ C <;> simp [h]) (fun x => ?_) ψ
    by_cases hx : x ∈ C
    · rw [he] at hx
      obtain ⟨k, rfl⟩ := hx
      rw [indicator_of_mem (by rw [he]; exact mem_range_self k)]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop k] with n hn
      rw [indicator_of_mem]
      simp only [S, Finset.coe_image, Finset.coe_range]
      exact mem_image_of_mem e (mem_Iio.2 hn)
    · rw [indicator_of_notMem hx]
      refine tendsto_const_nhds.congr' (Eventually.of_forall fun n =>
        (indicator_of_notMem ?_ _).symm)
      intro hxS
      simp only [S, Finset.coe_image, Finset.coe_range] at hxS
      obtain ⟨k, -, rfl⟩ := hxS
      exact hx (he ▸ mem_range_self k)
  rw [hψ] at hlim
  exact mem_closure_of_tendsto hlim (Eventually.of_forall hmem)

end DF
