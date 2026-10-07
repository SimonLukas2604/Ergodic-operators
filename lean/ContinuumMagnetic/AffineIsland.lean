/-
# Affine transport of island spectra, IDS and gap labels  (paper §4.1 and §4.4)

In the proofs of Theorems `thm:noncritical-continuum` and `thm:critical-continuum` the physical
island is `Σ_h = Φ_h(spec K)`, `Φ_h(E) = E_h^0 + aE`, and the normalized IDS is
`N_h(Φ_h E) = N_K(E)`.  For `a > 0` the gap labels are kept; for `a = a_h < 0` (the critical
case, either sign of the axial coefficient) a label `r` becomes `1 - r`, and
`1 - {nα} = {-nα}`, so every allowed label still occurs.

This file proves these transports at the level of Paper I's vocabulary
(`IsCantor`, `IsDOSMeasure`, `GapOpen`, `AllGapsOpen`), and the operator identities
`op_α(E₀δ₀ + aK)_x = E₀ + a K_x` and `op2_α(E₀δ₀ + aK) = E₀ + a K̃`.
-/
import ContinuumMagnetic.Affine

noncomputable section

open scoped ComplexConjugate ENNReal
open MeasureTheory Set Filter BoundedContinuousFunction AMO

namespace CMS

/-! ### Cantor sets -/

lemma _root_.AMO.IsCantor.image_homeomorph {K : Set ℝ} (hK : IsCantor K) (h : ℝ ≃ₜ ℝ) :
    IsCantor (h '' K) := by
  obtain ⟨hne, hcpt, hperf, hint⟩ := hK
  refine ⟨hne.image _, hcpt.image h.continuous, ⟨h.isClosedMap _ hperf.closed, ?_⟩, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have := (hperf.acc x hx).map h.continuous.continuousAt h.injective
    rwa [Filter.map_principal] at this
  · rw [← h.image_interior, hint, image_empty]

lemma _root_.AMO.IsCantor.image_affine {K : Set ℝ} (hK : IsCantor K) (E₀ : ℝ) {a : ℝ} (ha : a ≠ 0) :
    IsCantor (affine E₀ a '' K) :=
  hK.image_homeomorph (affineHomeomorph E₀ a ha)

/-! ### Density of states -/

/-- If `H'_x = E₀ + a H_x` and `ν` is the DOS measure of `H`, then `Φ_* ν` is that of `H'`. -/
theorem _root_.AMO.IsDOSMeasure.map_affine {Hx : ℝ → Op ℤ} {ν : Measure ℝ} (hν : IsDOSMeasure Hx ν)
    (hsa : ∀ x, IsSelfAdjoint (Hx x)) (E₀ a : ℝ) :
    IsDOSMeasure (fun x => affineOp E₀ a (Hx x)) (ν.map (affine E₀ a)) := by
  have := hν.1
  refine ⟨⟨by rw [Measure.map_apply (measurable_affine E₀ a) MeasurableSet.univ, preimage_univ,
    measure_univ]⟩, fun f => ?_⟩
  rw [integral_map (measurable_affine E₀ a).aemeasurable f.continuous.aestronglyMeasurable]
  set g : ℝ →ᵇ ℝ := f.compContinuous ⟨affine E₀ a, continuous_affine E₀ a⟩
  rw [show (∫ t, f (affine E₀ a t) ∂ν) = ∫ t, g t ∂ν from rfl, hν.2 g]
  congr 1
  funext x
  have hn : IsStarNormal (Hx x) := (hsa x).isStarNormal
  rw [show (fun z : ℂ => ((g z.re : ℝ) : ℂ)) = fun z => ((f (affine E₀ a z.re) : ℝ) : ℂ) from rfl,
    cfc_affine_re E₀ a (Hx x) f f.continuous]
  rfl

/-! ### Gap labels -/

lemma affine_lt_affine {E₀ a : ℝ} (ha : 0 < a) {s t : ℝ} : affine E₀ a s < affine E₀ a t ↔ s < t := by
  unfold affine; constructor <;> intro h <;> nlinarith

lemma affine_le_affine {E₀ a : ℝ} (ha : 0 < a) {s t : ℝ} :
    affine E₀ a s ≤ affine E₀ a t ↔ s ≤ t := by
  unfold affine; constructor <;> intro h <;> nlinarith

lemma affine_lt_affine_neg {E₀ a : ℝ} (ha : a < 0) {s t : ℝ} :
    affine E₀ a s < affine E₀ a t ↔ t < s := by
  unfold affine; constructor <;> intro h <;> nlinarith

lemma affine_le_affine_neg {E₀ a : ℝ} (ha : a < 0) {s t : ℝ} :
    affine E₀ a s ≤ affine E₀ a t ↔ t ≤ s := by
  unfold affine; constructor <;> intro h <;> nlinarith

/-- A gap with label `{nα}` is carried to a gap with the same label when `a > 0`. -/
theorem _root_.AMO.GapOpen.map_affine {S : Set ℝ} {ν : Measure ℝ} {α : ℝ} {n : ℤ} (h : GapOpen S ν α n)
    (E₀ : ℝ) {a : ℝ} (ha : 0 < a) :
    GapOpen (affine E₀ a '' S) (ν.map (affine E₀ a)) α n := by
  obtain ⟨s, t, hst, hs, ht, hgap, hids⟩ := h
  refine ⟨affine E₀ a s, affine E₀ a t, (affine_lt_affine ha).2 hst, ⟨s, hs, rfl⟩, ⟨t, ht, rfl⟩,
    ?_, ?_⟩
  · ext E
    simp only [mem_inter_iff, mem_Ioo, mem_image, mem_empty_iff_false, iff_false, not_and]
    rintro ⟨h1, h2⟩ ⟨u, hu, rfl⟩
    have : u ∈ Ioo s t ∩ S := ⟨⟨(affine_lt_affine ha).1 h1, (affine_lt_affine ha).1 h2⟩, hu⟩
    rw [hgap] at this
    exact this
  · intro E hE
    obtain ⟨u, rfl⟩ : ∃ u, affine E₀ a u = E := ⟨_, affine_inv' ha.ne' E⟩
    unfold IDS
    rw [Measure.map_apply (measurable_affine E₀ a) measurableSet_Iic]
    have hpre : affine E₀ a ⁻¹' Iic (affine E₀ a u) = Iic u := by
      ext v; simp [affine_le_affine ha]
    rw [hpre]
    exact hids u ⟨(affine_le_affine ha).1 hE.1, (affine_le_affine ha).1 hE.2⟩

theorem _root_.AMO.AllGapsOpen.map_affine {S : Set ℝ} {ν : Measure ℝ} {α : ℝ} (h : AllGapsOpen S ν α)
    (E₀ : ℝ) {a : ℝ} (ha : 0 < a) :
    AllGapsOpen (affine E₀ a '' S) (ν.map (affine E₀ a)) α :=
  fun n hn => (h n hn).map_affine E₀ ha

/-- `1 - {nα} = {-nα}` for irrational `α` and `n ≠ 0`. -/
lemma one_sub_fract {α : ℝ} (hα : Irrational α) {n : ℤ} (hn : n ≠ 0) :
    1 - Int.fract ((n : ℝ) * α) = Int.fract (((-n : ℤ) : ℝ) * α) := by
  have hnz : Int.fract ((n : ℝ) * α) ≠ 0 := by
    intro h0
    have h1 := Int.floor_add_fract ((n : ℝ) * α)
    rw [h0, add_zero] at h1
    exact (hα.intCast_mul hn).ne_int _ h1.symm
  push_cast
  rw [neg_mul, Int.fract_neg hnz]

/-- A gap with label `{nα}` is carried to a gap with label `{-nα}` when `a < 0`, provided the
IDS measure has no atoms (paper §4.4: "Atomlessness gives the physical IDS label"). -/
theorem _root_.AMO.GapOpen.map_affine_neg {S : Set ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hat : ∀ t, ν {t} = 0) {α : ℝ} (hα : Irrational α) {n : ℤ} (hn : n ≠ 0)
    (h : GapOpen S ν α n) (E₀ : ℝ) {a : ℝ} (ha : a < 0) :
    GapOpen (affine E₀ a '' S) (ν.map (affine E₀ a)) α (-n) := by
  obtain ⟨s, t, hst, hs, ht, hgap, hids⟩ := h
  refine ⟨affine E₀ a t, affine E₀ a s, (affine_lt_affine_neg ha).2 hst, ⟨t, ht, rfl⟩,
    ⟨s, hs, rfl⟩, ?_, ?_⟩
  · ext E
    simp only [mem_inter_iff, mem_Ioo, mem_image, mem_empty_iff_false, iff_false, not_and]
    rintro ⟨h1, h2⟩ ⟨u, hu, rfl⟩
    have : u ∈ Ioo s t ∩ S :=
      ⟨⟨(affine_lt_affine_neg ha).1 h2, (affine_lt_affine_neg ha).1 h1⟩, hu⟩
    rw [hgap] at this
    exact this
  · intro E hE
    obtain ⟨u, rfl⟩ : ∃ u, affine E₀ a u = E := ⟨_, affine_inv' ha.ne E⟩
    have hu : u ∈ Icc s t :=
      ⟨(affine_le_affine_neg ha).1 hE.2, (affine_le_affine_neg ha).1 hE.1⟩
    unfold IDS
    rw [Measure.map_apply (measurable_affine E₀ a) measurableSet_Iic]
    have hpre : affine E₀ a ⁻¹' Iic (affine E₀ a u) = Ici u := by
      ext v; simp [affine_le_affine_neg ha]
    rw [hpre, ← compl_Iio, prob_compl_eq_one_sub measurableSet_Iio]
    have hIio : ν (Iio u) = ν (Iic u) := by
      rw [← Iio_union_right, measure_union (by simp) (measurableSet_singleton u), hat, add_zero]
    have hfin : ν (Iic u) ≠ ⊤ := measure_ne_top ν _
    rw [hIio, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one]
    have := hids u hu
    unfold IDS at this
    rw [this]
    exact one_sub_fract hα hn

theorem _root_.AMO.AllGapsOpen.map_affine_neg {S : Set ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hat : ∀ t, ν {t} = 0) {α : ℝ} (hα : Irrational α) (h : AllGapsOpen S ν α)
    (E₀ : ℝ) {a : ℝ} (ha : a < 0) :
    AllGapsOpen (affine E₀ a '' S) (ν.map (affine E₀ a)) α := by
  intro n hn
  have := (h (-n) (neg_ne_zero.2 hn)).map_affine_neg hat hα (neg_ne_zero.2 hn) E₀ ha
  rwa [neg_neg] at this

/-- Gap labels for either sign of `a ≠ 0`. -/
theorem _root_.AMO.AllGapsOpen.map_affine_ne {S : Set ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    (hat : ∀ t, ν {t} = 0) {α : ℝ} (hα : Irrational α) (h : AllGapsOpen S ν α)
    (E₀ : ℝ) {a : ℝ} (ha : a ≠ 0) :
    AllGapsOpen (affine E₀ a '' S) (ν.map (affine E₀ a)) α := by
  rcases ha.lt_or_gt with ha | ha
  · exact h.map_affine_neg hat hα E₀ ha
  · exact h.map_affine E₀ ha

/-! ### Symbols and operators -/

/-- The symbol `E₀ δ₀ + a K`. -/
def affineSym (E₀ a : ℝ) (K : Symbol) : Symbol := Pi.single 0 (E₀ : ℂ) + (a : ℂ) • K

lemma _root_.AMO.SymbolSummable.smul {K : Symbol} (hK : SymbolSummable K) (c : ℂ) :
    SymbolSummable (c • K) := by
  unfold SymbolSummable at *
  simpa [norm_smul] using hK.mul_left ‖c‖

lemma _root_.AMO.SymbolSummable.affineSym {K : Symbol} (hK : SymbolSummable K) (E₀ a : ℝ) :
    SymbolSummable (affineSym E₀ a K) :=
  (symbolSummable_single _ _).add (hK.smul _)

lemma _root_.AMO.SymbolSelfAdjoint.affineSym {K : Symbol} (hK : SymbolSelfAdjoint K) (E₀ a : ℝ) :
    SymbolSelfAdjoint (affineSym E₀ a K) := by
  intro p
  simp only [CMS.affineSym, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul,
    Complex.conj_ofReal, hK p, Pi.single_apply, neg_eq_zero]
  split_ifs <;> simp

/-- `op_α(E₀δ₀ + aK)_x = E₀ + a K_x`. -/
theorem op_affineSym (α : ℝ) {K : Symbol} (hK : SymbolSummable K) (E₀ a : ℝ) (x : ℝ) :
    op α (affineSym E₀ a K) x = affineOp E₀ a (op α K x) := by
  unfold affineSym affineOp
  rw [op_add (symbolSummable_single _ _) (hK.smul _), op_single, op_smul' α _ hK]
  congr 1
  rw [show ((0 : ℤ × ℤ).1) = 0 from rfl, show ((0 : ℤ × ℤ).2) = 0 from rfl, AMO.W_zero,
    Algebra.algebraMap_eq_smul_one]

/-! ### The two-dimensional realization -/

lemma norm_W2_le (α : ℝ) (r q : ℤ) : ‖W2 α r q‖ ≤ 1 :=
  L2.norm_weightedShift_le zero_le_one (fun _ => (norm_e _).le)

lemma W2_zero (α : ℝ) : W2 α 0 0 = 1 := by
  ext u p
  rw [W2_apply]
  simp [e, Prod.mk_zero_zero]

lemma summable_op2 (α : ℝ) {R : Symbol} (hR : SymbolSummable R) :
    Summable fun p : ℤ × ℤ => R p • W2 α p.1 p.2 := by
  refine Summable.of_norm_bounded hR (fun p => ?_)
  rw [norm_smul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_W2_le _ _ _)

lemma op2_add (α : ℝ) {R R' : Symbol} (hR : SymbolSummable R) (hR' : SymbolSummable R') :
    op2 α (R + R') = op2 α R + op2 α R' := by
  unfold op2
  rw [← (summable_op2 α hR).tsum_add (summable_op2 α hR')]
  congr 1
  funext p
  exact add_smul (R p) (R' p) (W2 α p.1 p.2)

lemma op2_smul (α : ℝ) (c : ℂ) {R : Symbol} (hR : SymbolSummable R) :
    op2 α (c • R) = c • op2 α R := by
  unfold op2
  rw [← ((summable_op2 α hR).hasSum.const_smul c).tsum_eq]
  congr 1
  funext p
  exact (smul_smul c (R p) _).symm

lemma op2_single (α : ℝ) (p : ℤ × ℤ) (c : ℂ) : op2 α (Pi.single p c) = c • W2 α p.1 p.2 := by
  unfold op2
  rw [tsum_eq_single p]
  · simp
  · intro q hq
    rw [Pi.single_eq_of_ne hq]
    exact zero_smul ℂ (W2 α q.1 q.2)


/-- `W̃_{r,q}^* = W̃_{-r,-q}`. -/
theorem star_W2 (α : ℝ) (r q : ℤ) : star (W2 α r q) = W2 α (-r) (-q) := by
  unfold W2
  rw [L2.star_weightedShift (bdd_e fun p : ℤ × ℤ => α * r * q / 2 + q * p.1 * α)]
  apply L2.weightedShift_congr
  · rintro ⟨n₁, n₂⟩
    rw [conj_e]
    congr 1
    have key : (((n₁, n₂) - (r, q) : ℤ × ℤ).1 : ℤ) = n₁ - r := rfl
    simp only [Equiv.addRight_symm_apply]
    erw [key]
    push_cast
    ring
  · intro n
    simp [sub_eq_add_neg]

/-- A self-adjoint summable symbol gives a self-adjoint two-dimensional operator. -/
theorem isSelfAdjoint_op2 {α : ℝ} {R : Symbol} (hR : SymbolSummable R)
    (hsa : SymbolSelfAdjoint R) : IsSelfAdjoint (op2 α R) := by
  have h1 := (summable_op2 α hR).hasSum.star
  have h2 := ((Equiv.neg (ℤ × ℤ)).hasSum_iff).2 (summable_op2 α hR).hasSum
  unfold IsSelfAdjoint op2
  refine h1.unique ?_
  convert h2 using 1
  funext p
  simp [star_W2, hsa p]

/-- `op2_α(E₀δ₀ + aK) = E₀ + a K̃`. -/
theorem op2_affineSym (α : ℝ) {K : Symbol} (hK : SymbolSummable K) (E₀ a : ℝ) :
    op2 α (affineSym E₀ a K) = affineOp E₀ a (op2 α K) := by
  unfold affineSym affineOp
  rw [op2_add α (symbolSummable_single _ _) (hK.smul _), op2_single, op2_smul α _ hK]
  congr 1
  rw [show ((0 : ℤ × ℤ).1) = 0 from rfl, show ((0 : ℤ × ℤ).2) = 0 from rfl, W2_zero,
    Algebra.algebraMap_eq_smul_one]

end CMS
