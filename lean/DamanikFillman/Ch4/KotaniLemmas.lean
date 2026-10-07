/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §4.7–§4.8: deterministic ingredients of Kotani theory   (book pp. 343–362, 365–377)

This file collects the parts of Kotani theory that do not refer to an ergodic family: the
measure-theoretic notions of §4.7 (essential closure, weak homogeneity), the elementary
inequalities and algebraic identities for `m`-functions used in Propositions 4.7.4–4.7.6,
Theorem 4.7.9, Proposition 4.8.4, the measure estimate of Corollary 4.7.17 (as a consequence of
Theorem 4.7.16), and the topological arguments behind Theorem 4.8.10(b) and Theorem 4.8.17.

## Main definitions
* `DF.essClosure A` — the (Lebesgue) essential closure (4.7.1);
* `DF.IsWeaklyHomogeneous A` — Definition 4.7.11.

## Main results
* `DF.isClosed_essClosure`, `DF.essClosure_subset_closure`, `DF.essClosure_mono`,
  `DF.essClosure_congr_ae`;
* `DF.volume_diff_essClosure` — `Leb(A \ A^ess) = 0`;
* `DF.essClosure_eq_empty_iff` — **Exercise 4.7.1**: `A^ess = ∅ ↔ Leb(A) = 0`;
* `DF.volume_le_volume_essClosure` — **Exercise 4.7.2** (first part): `Leb(A) ≤ Leb(A^ess)`;
* `DF.IsOpen.isWeaklyHomogeneous` — open sets are weakly homogeneous (used in Corollary 4.7.12);
  `DF.IsWeaklyHomogeneous.subset_essClosure`;
* `DF.inv_add_half_le_log` — inequality (4.7.25) in the form used in the proof of (4.7.22);
* `DF.im_riccati` — the imaginary part of the Riccati equation (4.7.15);
* `DF.log_one_add_im_div` — the pointwise identity in the proof of Proposition 4.7.4;
* `DF.kotani_identity` — the algebraic identity in the proof of (4.7.23);
* `DF.im_inv_inv_sub` — the formula for `Im G(0,0)` in terms of `m±` (proof of Theorem 4.7.1);
* `DF.green00_of_reflectionless`, `DF.green11_of_reflectionless` — (4.8.6), (4.8.7) in the proof
  of Proposition 4.8.4;
* `DF.volume_le_four_of_varEstimate` — **Corollary 4.7.17** from the estimate of
  Theorem 4.7.16 and (4.7.62);
* `DF.tendsto_of_tendsto_restrict` — the topological core of Lemma 4.8.5(e) and
  Theorem 4.8.10(b): on a compact set of sequences on which the left half-line determines the
  sequence, convergence of left halves forces convergence of the whole sequences;
* `DF.isGδ_dense_setOf_eq_zero` — the Baire category argument of Theorem 4.8.17.

No `Statement` props are introduced in this file.
-/
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Analysis.Complex.Basic

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal NNReal Real ComplexConjugate

namespace DF

/-! ### Essential closure (4.7.1) -/

/-- The (Lebesgue) essential closure of `A ⊆ ℝ` (4.7.1): the points `E` all of whose
neighbourhoods meet `A` in a set of positive Lebesgue measure. -/
def essClosure (A : Set ℝ) : Set ℝ := {E | ∀ ε > 0, 0 < volume (Ioo (E - ε) (E + ε) ∩ A)}

lemma not_mem_essClosure_iff {A : Set ℝ} {E : ℝ} :
    E ∉ essClosure A ↔ ∃ ε > 0, volume (Ioo (E - ε) (E + ε) ∩ A) = 0 := by
  simp only [essClosure, mem_ofPred_eq, not_forall, not_lt, nonpos_iff_eq_zero, exists_prop]

theorem isClosed_essClosure (A : Set ℝ) : IsClosed (essClosure A) := by
  rw [← isOpen_compl_iff, Metric.isOpen_iff]
  intro E hE
  obtain ⟨ε, hε, h0⟩ := not_mem_essClosure_iff.1 hE
  refine ⟨ε / 2, by positivity, fun E' hE' => ?_⟩
  rw [mem_ball, Real.dist_eq, abs_lt] at hE'
  refine not_mem_essClosure_iff.2 ⟨ε / 2, by positivity, measure_mono_null ?_ h0⟩
  refine inter_subset_inter_left _ (Ioo_subset_Ioo ?_ ?_) <;> linarith

theorem essClosure_subset_closure (A : Set ℝ) : essClosure A ⊆ closure A := by
  intro E hE
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨x, hx⟩ := nonempty_of_measure_ne_zero (hE ε hε).ne'
  refine ⟨x, hx.2, ?_⟩
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith [hx.1.1, hx.1.2]

theorem essClosure_mono {A B : Set ℝ} (h : A ⊆ B) : essClosure A ⊆ essClosure B :=
  fun _ hE ε hε => lt_of_lt_of_le (hE ε hε) (measure_mono (inter_subset_inter_right _ h))

/-- The essential closure only depends on the Lebesgue class of `A`. -/
theorem essClosure_congr_ae {A B : Set ℝ} (h : A =ᵐ[volume] B) : essClosure A = essClosure B := by
  ext E
  simp only [essClosure, mem_ofPred_eq]
  have : ∀ ε, volume (Ioo (E - ε) (E + ε) ∩ A) = volume (Ioo (E - ε) (E + ε) ∩ B) :=
    fun ε => measure_congr (ae_eq_set_inter (ae_eq_refl _) h)
  simp_rw [this]

/-- `Leb(A \ A^ess) = 0`. -/
theorem volume_diff_essClosure (A : Set ℝ) : volume (A \ essClosure A) = 0 := by
  set s : ℚ × ℚ → Set ℝ := fun pq =>
    Ioo (pq.1 : ℝ) pq.2 ∩ A ∩ {_x | volume (Ioo (pq.1 : ℝ) pq.2 ∩ A) = 0}
  have hs : ∀ pq, volume (s pq) = 0 := by
    intro pq
    by_cases h : volume (Ioo (pq.1 : ℝ) pq.2 ∩ A) = 0
    · exact measure_mono_null inter_subset_left h
    · have : s pq = ∅ := by
        ext x; simp only [s, mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        exact fun h' => h h'.2
      rw [this, measure_empty]
  refine measure_mono_null ?_ (measure_iUnion_null hs)
  intro E ⟨hEA, hE⟩
  obtain ⟨ε, hε, h0⟩ := not_mem_essClosure_iff.1 hE
  obtain ⟨p, hp1, hp2⟩ := exists_rat_btwn (show E - ε < E by linarith)
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show E < E + ε by linarith)
  refine mem_iUnion.2 ⟨(p, q), ⟨⟨⟨hp2, hq1⟩, hEA⟩, ?_⟩⟩
  exact measure_mono_null (inter_subset_inter_left _ (Ioo_subset_Ioo hp1.le hq2.le)) h0

/-- **Exercise 4.7.2** (first part): `Leb(A) ≤ Leb(A^ess)`. -/
theorem volume_le_volume_essClosure (A : Set ℝ) : volume A ≤ volume (essClosure A) := by
  calc volume A ≤ volume ((A \ essClosure A) ∪ essClosure A) :=
        measure_mono (fun x hx => by by_cases h : x ∈ essClosure A <;> simp [h, hx])
    _ ≤ volume (A \ essClosure A) + volume (essClosure A) := measure_union_le _ _
    _ = volume (essClosure A) := by rw [volume_diff_essClosure, zero_add]

/-- **Exercise 4.7.1**: `A^ess = ∅` if and only if `Leb(A) = 0`. -/
theorem essClosure_eq_empty_iff {A : Set ℝ} : essClosure A = ∅ ↔ volume A = 0 := by
  constructor
  · intro h
    have := volume_le_volume_essClosure A
    rw [h, measure_empty] at this
    exact le_antisymm this zero_le
  · intro h
    ext E
    simp only [mem_empty_iff_false, iff_false]
    exact not_mem_essClosure_iff.2 ⟨1, one_pos, measure_mono_null inter_subset_right h⟩

/-! ### Weak homogeneity (Definition 4.7.11) -/

/-- `A ⊆ ℝ` is weakly homogeneous (Definition 4.7.11) if
`limsup_{δ ↓ 0} Leb(A ∩ (E - δ, E + δ)) / (2δ) > 0` for every `E ∈ A`. -/
def IsWeaklyHomogeneous (A : Set ℝ) : Prop :=
  ∀ E ∈ A, 0 < limsup (fun δ : ℝ => volume (A ∩ Ioo (E - δ) (E + δ)) / ENNReal.ofReal (2 * δ))
    (𝓝[>] 0)

/-- Open sets are weakly homogeneous (used in Corollary 4.7.12). -/
theorem IsOpen.isWeaklyHomogeneous {A : Set ℝ} (hA : IsOpen A) : IsWeaklyHomogeneous A := by
  intro E hE
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hA E hE
  have hev : (fun δ : ℝ => volume (A ∩ Ioo (E - δ) (E + δ)) / ENNReal.ofReal (2 * δ)) =ᶠ[𝓝[>] 0]
      fun _ => 1 := by
    filter_upwards [Ioo_mem_nhdsGT hε] with δ hδ
    have hsub : Ioo (E - δ) (E + δ) ⊆ A := by
      intro x hx
      apply hball
      rw [mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hx.1, hx.2, hδ.2]
    rw [inter_eq_right.2 hsub, Real.volume_Ioo, show E + δ - (E - δ) = 2 * δ by ring]
    exact ENNReal.div_self (by simp [hδ.1]) ENNReal.ofReal_ne_top
  rw [limsup_congr hev, limsup_const]
  exact one_pos

/-- A weakly homogeneous set is contained in its essential closure. -/
theorem IsWeaklyHomogeneous.subset_essClosure {A : Set ℝ} (hA : IsWeaklyHomogeneous A) :
    A ⊆ essClosure A := by
  intro E hE
  by_contra hne
  obtain ⟨ε, hε, h0⟩ := not_mem_essClosure_iff.1 hne
  have hev : (fun δ : ℝ => volume (A ∩ Ioo (E - δ) (E + δ)) / ENNReal.ofReal (2 * δ)) =ᶠ[𝓝[>] 0]
      fun _ => 0 := by
    filter_upwards [Ioo_mem_nhdsGT hε] with δ hδ
    have : volume (A ∩ Ioo (E - δ) (E + δ)) = 0 := by
      refine measure_mono_null ?_ h0
      rw [inter_comm]
      exact inter_subset_inter_left _ (Ioo_subset_Ioo (by linarith [hδ.2]) (by linarith [hδ.2]))
    rw [this, ENNReal.zero_div]
  have := hA E hE
  rw [limsup_congr hev, limsup_const] at this
  exact lt_irrefl _ this

/-! ### Elementary inequalities and identities for `m`-functions -/

/-- Inequality (4.7.25), in the form used for (4.7.22): for `a, y > 0`,
`1 / (a + y/2) ≤ (1/y) log (1 + y/a)`. -/
theorem inv_add_half_le_log {a y : ℝ} (ha : 0 < a) (hy : 0 < y) :
    1 / (a + y / 2) ≤ Real.log (1 + y / a) / y := by
  have h := Real.le_log_one_add_of_nonneg (x := y / a) (by positivity)
  rw [le_div_iff₀ hy]
  calc 1 / (a + y / 2) * y = 2 * (y / a) / (y / a + 2) := by field_simp; ring
    _ ≤ _ := h

/-- `log (1 + x) ≤ x` for `x ≥ 0` (used in the proof of Theorem 4.7.13). -/
theorem log_one_add_le_self {x : ℝ} (hx : 0 ≤ x) : Real.log (1 + x) ≤ x := by
  have := Real.log_le_sub_one_of_pos (show 0 < 1 + x by linarith)
  linarith

/-- The imaginary part of the Riccati equation (4.7.14)–(4.7.15): if
`m' = v - z - m⁻¹` with `v` real, then `Im m' = -Im z + Im m / |m|²`. -/
theorem im_riccati {m m' z : ℂ} {v : ℝ} (h : m' = v - z - m⁻¹) :
    m'.im = -z.im + m.im / Complex.normSq m := by
  rw [h]; simp [Complex.inv_im]; ring

/-- The pointwise identity in the proof of Proposition 4.7.4: if `Im m > 0`, `Im m' > 0`,
`Im z > 0` and `m' = v - z - m⁻¹`, then
`log (1 + Im z / Im m') = log (Im m / |m|²) - log (Im m')`. -/
theorem log_one_add_im_div {m m' z : ℂ} {v : ℝ} (h : m' = v - z - m⁻¹) (hm : 0 < m.im)
    (hm' : 0 < m'.im) (hz : 0 < z.im) :
    Real.log (1 + z.im / m'.im) = Real.log (m.im / Complex.normSq m) - Real.log m'.im := by
  have hR := im_riccati h
  have hnm : 0 < Complex.normSq m := by
    rw [Complex.normSq_pos]; intro h0; rw [h0] at hm; simp at hm
  rw [← Real.log_div (by positivity) hm'.ne']
  congr 1
  have h2 : m.im / Complex.normSq m = m'.im + z.im := by linarith
  rw [h2]
  field_simp

/-- The algebraic identity in the proof of (4.7.23): if `n₊, n₋ > 0` and `Im b = n₊ + n₋`,
`b ≠ 0`, then
`(1/n₊ + 1/n₋) ((n₊ - n₋)² + (Re b)²) / |b|² = 1/n₊ + 1/n₋ + 4 Im (1/b)`. -/
theorem kotani_identity {np nm : ℝ} {b : ℂ} (hp : 0 < np) (hm : 0 < nm) (hb : b.im = np + nm) :
    (1 / np + 1 / nm) * ((np - nm) ^ 2 + b.re ^ 2) / Complex.normSq b =
      1 / np + 1 / nm + 4 * (1 / b).im := by
  have hb0 : 0 < Complex.normSq b := by
    rw [Complex.normSq_apply]; nlinarith [sq_nonneg b.re]
  have hnorm : Complex.normSq b = b.re ^ 2 + b.im ^ 2 := by rw [Complex.normSq_apply]; ring
  have hinv : (1 / b).im = -b.im / Complex.normSq b := by rw [one_div, Complex.inv_im]
  rw [hinv]
  field_simp
  rw [hnorm, hb]
  ring

/-- The formula for `Im G(0,0)` in the proof of Theorem 4.7.1 (after (4.7.32)): with
`G = (m₋⁻¹ - m₊)⁻¹` one has `Im G = (Im m₋ + |m₋|² Im m₊) / |1 - m₋ m₊|²`. -/
theorem im_inv_inv_sub {mm mp : ℂ} (hmm : mm ≠ 0) (hne : 1 - mm * mp ≠ 0) :
    ((mm⁻¹ - mp)⁻¹).im = (mm.im + Complex.normSq mm * mp.im) / Complex.normSq (1 - mm * mp) := by
  have h1 : (mm⁻¹ - mp)⁻¹ = mm / (1 - mm * mp) := by
    field_simp
  rw [h1, Complex.div_im]
  have hn : Complex.normSq (1 - mm * mp) ≠ 0 := by rwa [Ne, Complex.normSq_eq_zero]
  field_simp
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re,
    Complex.mul_im, Complex.one_re, Complex.one_im]
  ring

/-- (4.8.5)–(4.8.6): if `m₊ = (conj m₋)⁻¹` (identity (4.8.2)), then the diagonal Green function
`M₀ = m₋ / (1 - m₋ m₊)` is purely imaginary, `M₀ = 2 i Im m₋ / |1 - m₋ m₊|²`. -/
theorem green00_of_reflectionless {mm mp : ℂ} (hmm : mm ≠ 0) (h : mp = (conj mm)⁻¹) :
    mm / (1 - mm * mp) = 2 * Complex.I * mm.im / Complex.normSq (1 - mm * mp) := by
  have hc : conj mm ≠ 0 := by simpa using hmm
  have h1 : 1 - mm * mp = (conj mm - mm) / conj mm := by rw [h]; field_simp
  have h2 : conj mm - mm = -(2 * Complex.I * mm.im) := by
    apply Complex.ext <;> simp; ring
  by_cases him : mm.im = 0
  · have : conj mm = mm := Complex.conj_eq_iff_im.2 him
    rw [h1, this, sub_self, zero_div, div_zero, him]; simp
  have hn : Complex.normSq (1 - mm * mp) = 4 * mm.im ^ 2 / Complex.normSq mm := by
    rw [h1, h2, Complex.normSq_div, Complex.normSq_conj, Complex.normSq_neg]
    simp [Complex.normSq_mul, Complex.normSq_I]
    ring
  rw [hn, h1, h2]
  have hnm' : (Complex.normSq mm : ℂ) = mm * conj mm := (Complex.mul_conj mm).symm
  have him' : (mm.im : ℂ) ≠ 0 := by exact_mod_cast him
  push_cast
  rw [hnm']
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- (4.8.7): under (4.8.2), `M₁ = m₊ / (1 - m₋ m₊) = 2 i Im m₊ / |1 - m₋ m₊|²`. -/
theorem green11_of_reflectionless {mm mp : ℂ} (hmm : mm ≠ 0) (h : mp = (conj mm)⁻¹) :
    mp / (1 - mm * mp) = 2 * Complex.I * mp.im / Complex.normSq (1 - mm * mp) := by
  have hmp : mp ≠ 0 := by rw [h]; simpa using hmm
  have h' : mm = (conj mp)⁻¹ := by rw [h]; simp
  have := green00_of_reflectionless hmp h'
  rwa [mul_comm mp mm] at this

/-! ### Corollary 4.7.17 from Theorem 4.7.16 -/

/-- **Corollary 4.7.17** as a consequence of Theorem 4.7.16 and (4.7.62): let
`Z ⊆ Σ ⊆ [a, b]` be measurable, `G = [a, b] \ Σ` (the union of the bounded gaps when
`a = min Σ`, `b = max Σ`), `b - a ≤ 4 + v` (this is (4.7.62) with `v = Var V`) and
`v ≤ Leb(Σ \ Z) + Leb(G)` (Theorem 4.7.16).  Then `Leb(Z) ≤ 4`. -/
theorem volume_le_four_of_varEstimate {Z S : Set ℝ} {a b v : ℝ} (hZ : MeasurableSet Z)
    (hS : MeasurableSet S) (hZS : Z ⊆ S) (hSab : S ⊆ Icc a b) (hab : b - a ≤ 4 + v)
    (hvar : ENNReal.ofReal v ≤ volume (S \ Z) + volume (Icc a b \ S)) (hv : 0 ≤ v) :
    volume Z ≤ 4 := by
  have hsplit : volume (Icc a b) = volume S + volume (Icc a b \ S) := by
    rw [← measure_union disjoint_sdiff_right (measurableSet_Icc.diff hS), union_sdiff_cancel hSab]
  have hIcc : volume (Icc a b) ≤ ENNReal.ofReal (4 + v) := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_le_ofReal (by linarith)
  have hfinI : volume (Icc a b) ≠ ⊤ := by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  have hfin : volume (Icc a b \ S) ≠ ⊤ := ne_top_of_le_ne_top hfinI (measure_mono sdiff_subset)
  have hfin' : volume (S \ Z) ≠ ⊤ :=
    ne_top_of_le_ne_top hfinI (measure_mono (sdiff_subset.trans hSab))
  have h1 : volume S + volume (Icc a b \ S) ≤
      4 + volume (S \ Z) + volume (Icc a b \ S) := by
    rw [← hsplit]
    refine hIcc.trans ?_
    rw [ENNReal.ofReal_add (by norm_num) hv, add_assoc]
    simpa using add_le_add_left hvar 4
  have h2 : volume S ≤ 4 + volume (S \ Z) := (ENNReal.add_le_add_iff_right hfin).1 h1
  have h3 : volume Z + volume (S \ Z) = volume S := by
    have := measure_inter_add_sdiff (μ := volume) S hZ
    rwa [inter_eq_right.2 hZS] at this
  rw [← h3] at h2
  exact (ENNReal.add_le_add_iff_right hfin').1 h2

/-! ### Topology of sequence spaces (Lemma 4.8.5(e), Theorem 4.8.10(b)) -/

/-- The topological core of Lemma 4.8.5(e) / Theorem 4.8.10(b): let `S` be a compact set in a
topological space `X` and `p : X → Y` continuous into a Hausdorff space, injective on `S`
(e.g. `p` = restriction of a sequence to the left half-line).  If `xₘ, x ∈ S` and
`p xₘ → p x`, then `xₘ → x`. -/
theorem tendsto_of_tendsto_restrict {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [T2Space Y] {S : Set X} (hS : IsCompact S) {p : X → Y} (hp : Continuous p)
    (hinj : InjOn p S) {ι : Type*} {l : Filter ι} {x : ι → X} {x₀ : X} (hx : ∀ i, x i ∈ S)
    (hx₀ : x₀ ∈ S) (h : Tendsto (fun i => p (x i)) l (𝓝 (p x₀))) : Tendsto x l (𝓝 x₀) := by
  have : CompactSpace S := isCompact_iff_compactSpace.1 hS
  have hemb : Topology.IsClosedEmbedding (S.domRestrict p) :=
    (hp.comp continuous_subtype_val).isClosedEmbedding
      (fun a b hab => Subtype.ext (hinj a.2 b.2 hab))
  have h' : Tendsto (fun i => (⟨x i, hx i⟩ : S)) l (𝓝 ⟨x₀, hx₀⟩) := by
    rw [hemb.isEmbedding.tendsto_nhds_iff]
    exact h
  exact (continuous_subtype_val.tendsto _).comp h'

/-! ### Baire category (Theorem 4.8.17) -/

/-- The Baire category argument of Theorem 4.8.17: if `M ≥ 0` is upper semicontinuous on a
Baire space and every sublevel set `{M < δ}`, `δ > 0`, is dense, then `{M = 0}` is a dense
`G_δ`. -/
theorem isGδ_dense_setOf_eq_zero {X : Type*} [TopologicalSpace X] [BaireSpace X] {M : X → ℝ}
    (hM : UpperSemicontinuous M) (h0 : ∀ x, 0 ≤ M x) (hdense : ∀ δ > 0, Dense {x | M x < δ}) :
    IsGδ {x | M x = 0} ∧ Dense {x | M x = 0} := by
  have heq : {x | M x = 0} = ⋂ n : ℕ, {x | M x < 1 / (n + 1)} := by
    ext x
    simp only [mem_ofPred_eq, mem_iInter]
    constructor
    · intro hx n; rw [hx]; positivity
    · intro hx
      refine le_antisymm ?_ (h0 x)
      refine le_of_forall_pos_lt_add fun ε hε => ?_
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
      linarith [hx n]
  have hopen : ∀ n : ℕ, IsOpen {x | M x < 1 / (n + 1)} := fun n =>
    upperSemicontinuous_iff_isOpen_preimage.1 hM _
  rw [heq]
  exact ⟨IsGδ.iInter_of_isOpen hopen,
    dense_iInter_of_isOpen hopen fun n => hdense _ (by positivity)⟩

end DF
