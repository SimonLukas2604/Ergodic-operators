/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §3.9.2: the suspension of an invariant measure (Lemma 3.9.7, book pp. 295–296)

Main result:
* `DF.suspension_ergodic` — **Lemma 3.9.7**: the suspension `μ̄` (push-forward of
  `μ × Leb|_{[0,1)}` to `S(Ω, T)`) of a `T`-invariant (resp. ergodic) measure is invariant
  (resp. ergodic) for the suspension flow; this proves `DF.SuspensionErgodicStatement`.

The proof follows the book: sections `E_s = {ω : [ω, s] ∈ E}` of a flow-invariant set do not
depend on `s` and are `T`-invariant; for invariance, `s ↦ μ(W_s)` is `1`-periodic and its
integral over a period is translation invariant.
-/
import DamanikFillman.Ch3.Flows

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Set Function Topology

namespace DF

section

variable {X : Type*} [TopologicalSpace X] (S : X ≃ₜ X)

lemma suspMk_add_one (ω : X) (s : ℝ) : suspMk S ω (s + 1) = suspMk S (S ω) s := by
  rw [← suspFlow_mk, suspFlow_one]

lemma suspMk_eq_flow (ω : X) (s : ℝ) : suspMk S ω s = suspFlow S s (suspMk S ω 0) := by
  rw [suspFlow_mk, zero_add]

lemma continuous_suspMk : Continuous fun p : X × ℝ => suspMk S p.1 p.2 :=
  continuous_quotient_mk'

lemma continuous_suspFlow (t : ℝ) : Continuous (suspFlow S t) := by
  exact (isQuotientMap_quotient_mk' (s := suspSetoid S)).continuous_iff.2
    (continuous_quotient_mk'.comp (continuous_fst.prodMk (continuous_snd.add continuous_const)))

end

/-- **Lemma 3.9.7**: suspensions of invariant (resp. ergodic) measures are invariant (resp.
ergodic) for the suspension flow. -/
theorem suspension_ergodic : SuspensionErgodicStatement := by
  intro X _ _ _ _ S μ _
  let _ : MeasurableSpace (Suspension S) := borel _
  have : BorelSpace (Suspension S) := ⟨rfl⟩
  set q : X × ℝ → Suspension S := fun p => suspMk S p.1 p.2 with hqdef
  have hqm : Measurable q := (continuous_suspMk S).measurable
  set ν : Measure (X × ℝ) := μ.prod (volume.restrict (Ico (0 : ℝ) 1))
  have hμbar : ∀ E, MeasurableSet E → ((ν.map q) E) = ν (q ⁻¹' E) := fun E hE =>
    Measure.map_apply hqm hE
  refine ⟨fun hS t => ?_, fun hS E hE hinv => ?_⟩
  · -- invariance
    -- the section formula
    have hsec : ∀ W : Set (X × ℝ), MeasurableSet W →
        ν W = ENNReal.ofReal (∫ s in (0 : ℝ)..1, (μ ((fun ω => (ω, s)) ⁻¹' W)).toReal) := by
      intro W hW
      have hm : Measurable fun s : ℝ => μ ((fun ω => (ω, s)) ⁻¹' W) :=
        measurable_measure_prodMk_right hW
      rw [Measure.prod_apply_symm hW, intervalIntegral.integral_of_le zero_le_one,
        integral_Ioc_eq_integral_Ioo, ← integral_Ico_eq_integral_Ioo,
        ofReal_integral_eq_lintegral_ofReal]
      · refine lintegral_congr fun s => ?_
        rw [ENNReal.ofReal_toReal (measure_ne_top _ _)]
      · refine (integrable_const (1 : ℝ)).mono' hm.ennreal_toReal.aestronglyMeasurable
          (Eventually.of_forall fun s => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
        exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
      · exact Eventually.of_forall fun s => ENNReal.toReal_nonneg
    have hflow_m : Measurable (suspFlow S t) := (continuous_suspFlow S t).measurable
    refine ⟨hflow_m, ?_⟩
    ext E hE
    rw [Measure.map_apply hflow_m hE, hμbar _ (hflow_m hE), hμbar _ hE]
    set W := q ⁻¹' E
    have hW : MeasurableSet W := hqm hE
    have hW1 : ∀ ω s, (ω, s + 1) ∈ W ↔ (S ω, s) ∈ W := by
      intro ω s
      show suspMk S ω (s + 1) ∈ E ↔ suspMk S (S ω) s ∈ E
      rw [suspMk_add_one]
    have hpre : q ⁻¹' (suspFlow S t ⁻¹' E) = (fun p : X × ℝ => (p.1, p.2 + t)) ⁻¹' W := by
      ext ⟨ω, s⟩; rfl
    have hWt : MeasurableSet ((fun p : X × ℝ => (p.1, p.2 + t)) ⁻¹' W) :=
      (measurable_fst.prodMk (measurable_snd.add_const t)) hW
    rw [hpre, hsec _ hWt, hsec _ hW]
    set f : ℝ → ℝ := fun s => (μ ((fun ω => (ω, s)) ⁻¹' W)).toReal
    have hper : Periodic f 1 := by
      intro s
      simp only [f]
      have : (fun ω => (ω, s + 1)) ⁻¹' W = S ⁻¹' ((fun ω => (ω, s)) ⁻¹' W) := by
        ext ω; simp only [mem_preimage]; exact hW1 ω s
      rw [this, hS.measure_preimage (measurable_prodMk_right hW).nullMeasurableSet]
    have hshift : ∫ s in (0 : ℝ)..1, (μ ((fun ω => (ω, s)) ⁻¹'
        ((fun p : X × ℝ => (p.1, p.2 + t)) ⁻¹' W))).toReal = ∫ s in (0 : ℝ)..1, f (s + t) := rfl
    rw [hshift, intervalIntegral.integral_comp_add_right f t, zero_add,
      add_comm 1 t, hper.intervalIntegral_add_eq t 0, zero_add]
  · -- ergodicity
    set E0 := {ω : X | suspMk S ω 0 ∈ E}
    have hE0 : MeasurableSet E0 :=
      ((continuous_suspMk S).comp (continuous_id.prodMk continuous_const)).measurable hE
    have hsect : q ⁻¹' E = E0 ×ˢ univ := by
      ext ⟨ω, s⟩
      simp only [mem_preimage, mem_prod, mem_univ, and_true, E0, q]
      rw [suspMk_eq_flow, ← mem_preimage, hinv s]
      exact Iff.rfl
    have hinv0 : S ⁻¹' E0 = E0 := by
      ext ω
      simp only [E0, mem_preimage, mem_setOf_eq]
      rw [← suspMk_add_one, suspMk_eq_flow, ← mem_preimage, hinv]
    have hvol : (volume.restrict (Ico (0 : ℝ) 1)) univ = 1 := by
      rw [Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ico]; simp
    rcases hS.toPreErgodic.measure_self_or_compl_eq_zero hE0.nullMeasurableSet
      (Eq.eventuallyEq hinv0) with h0 | h0
    · left
      rw [hμbar _ hE, hsect, Measure.prod_prod, h0, zero_mul]
    · right
      have hc : q ⁻¹' Eᶜ = E0ᶜ ×ˢ univ := by
        rw [preimage_compl, hsect]; ext p; simp
      rw [hμbar _ hE.compl, hc, Measure.prod_prod, h0, zero_mul]

end DF
