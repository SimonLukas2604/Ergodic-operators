/-
Copyright (c) 2026. Formalization of
  S. Becker, "Self-dual perturbations of the critical almost Mathieu operator:
  Dry Ten Martini and Hausdorff dimension" (Paper II).

# The integrated density of states as a distribution function

Facts about `IDS ν E = ν((-∞, E])` for a probability measure `ν` used in the reductions:
monotonicity, `ν(a,b] = N(b) - N(a)`, continuity for atomless `ν`, the level-set dichotomy
behind Prop 3.9, uniqueness of the DOS measure, perfectness of `Σ` from an atomless IDS, and the
paper's notion of an open gap (`GapOpenWeak`: the IDS equals the label on the open gap, i.e. on
`[a, b)` by right continuity) together with its upgrade to `AMO.GapOpen` (`[a, b]`) for atomless
IDS.
-/
import AnalyticPerturbationsAMO.IDSSupport

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace SGD

open AMO

/-! ### The IDS as a distribution function -/

section IDS

variable {ν : Measure ℝ} [IsProbabilityMeasure ν]

lemma IDS_eq_cdf (E : ℝ) : IDS ν E = cdf ν E := by
  rw [cdf_eq_real]; rfl

lemma IDS_mono : Monotone (IDS ν) := fun x y h => by
  rw [IDS_eq_cdf, IDS_eq_cdf]; exact monotone_cdf ν h

lemma measure_Ioc_eq_IDS (x y : ℝ) : ν (Ioc x y) = ENNReal.ofReal (IDS ν y - IDS ν x) := by
  rw [IDS_eq_cdf, IDS_eq_cdf, ← (cdf ν).measure_Ioc, measure_cdf]

lemma tendsto_IDS_atBot : Tendsto (IDS ν) atBot (𝓝 0) := by
  simpa [funext (IDS_eq_cdf (ν := ν))] using tendsto_cdf_atBot ν

lemma tendsto_IDS_atTop : Tendsto (IDS ν) atTop (𝓝 1) := by
  simpa [funext (IDS_eq_cdf (ν := ν))] using tendsto_cdf_atTop ν

/-- An atomless distribution function is continuous. -/
lemma continuous_IDS (hat : ∀ E, ν {E} = 0) : Continuous (IDS ν) := by
  have hF : IDS ν = cdf ν := funext IDS_eq_cdf
  rw [hF, continuous_iff_continuousAt]
  intro x
  have h1 := (cdf ν).measure_singleton x
  rw [measure_cdf, hat x] at h1
  have hle : Function.leftLim (cdf ν) x ≤ cdf ν x := (cdf ν).mono.leftLim_le le_rfl
  have hge : cdf ν x ≤ Function.leftLim (cdf ν) x := by
    have := ENNReal.ofReal_eq_zero.1 h1.symm
    linarith
  have hleft : Function.leftLim (cdf ν) x = cdf ν x := le_antisymm hle hge
  refine continuousAt_iff_continuous_left_right.2 ⟨?_, (cdf ν).right_continuous x⟩
  exact continuousWithinAt_Iio_iff_Iic.1
    ((cdf ν).mono.continuousWithinAt_Iio_iff_leftLim_eq.2 hleft)

/-- Positive increase of an atomless IDS forces a point of any full-measure set in between. -/
lemma Ioo_inter_nonempty {S : Set ℝ} (hSc : ν Sᶜ = 0) (hat : ∀ E, ν {E} = 0) {x y : ℝ}
    (hlt : IDS ν x < IDS ν y) : (Ioo x y ∩ S).Nonempty := by
  by_contra h
  have hsub : Ioo x y ⊆ Sᶜ := fun z hz hzS => h ⟨z, hz, hzS⟩
  have h0 : ν (Ioc x y) = 0 := by
    refine measure_mono_null (fun z hz => ?_) (measure_union_null hSc (hat y))
    rcases hz.2.lt_or_eq with hzy | rfl
    · exact Or.inl (hsub ⟨hz.1, hzy⟩)
    · exact Or.inr rfl
  rw [measure_Ioc_eq_IDS] at h0
  have := ENNReal.ofReal_eq_zero.1 h0
  linarith

/-- **Level sets of the IDS** (proof of Prop 3.9).  For an atomless IDS carried by a closed set
`S` on which it has full support, and `0 < ℓ < 1`, the level set `N^{-1}(ℓ)` is either a
nondegenerate interval whose interior is a gap of `S` with endpoints in `S`, or a single point
`E₀ ∈ S` with `N < ℓ` to its left and `N > ℓ` to its right. -/
theorem level_set_dichotomy {S : Set ℝ} (hS : IsClosed S) (hSc : ν Sᶜ = 0)
    (hat : ∀ E, ν {E} = 0) (hsupp : ∀ E ∈ S, ∀ ε > 0, 0 < ν (Ioo (E - ε) (E + ε)))
    {ℓ : ℝ} (hℓ0 : 0 < ℓ) (hℓ1 : ℓ < 1) :
    (∃ a b, a < b ∧ a ∈ S ∧ b ∈ S ∧ Ioo a b ∩ S = ∅ ∧ ∀ E ∈ Icc a b, IDS ν E = ℓ) ∨
    (∃ E₀ ∈ S, IDS ν E₀ = ℓ ∧ (∀ E < E₀, IDS ν E < ℓ) ∧ (∀ E, E₀ < E → ℓ < IDS ν E)) := by
  have hFc : Continuous (IDS ν) := continuous_IDS hat
  have hFm : Monotone (IDS ν) := IDS_mono
  obtain ⟨E1, hE1⟩ : ∃ E1, IDS ν E1 < ℓ :=
    (tendsto_IDS_atBot.eventually (gt_mem_nhds hℓ0)).exists
  obtain ⟨E2, hE2⟩ : ∃ E2, ℓ < IDS ν E2 :=
    (tendsto_IDS_atTop.eventually (lt_mem_nhds hℓ1)).exists
  have h12 : E1 ≤ E2 := (hFm.reflect_lt (hE1.trans hE2)).le
  set L := {E | IDS ν E = ℓ} with hLdef
  have hLne : L.Nonempty := by
    obtain ⟨E, -, hFE⟩ := intermediate_value_Icc h12 hFc.continuousOn ⟨hE1.le, hE2.le⟩
    exact ⟨E, hFE⟩
  have hLcl : IsClosed L := isClosed_eq hFc continuous_const
  have hLbb : BddBelow L := ⟨E1, fun E (hE : IDS ν E = ℓ) => le_of_not_gt fun h => by
    have := hFm h.le; linarith⟩
  have hLba : BddAbove L := ⟨E2, fun E (hE : IDS ν E = ℓ) => le_of_not_gt fun h => by
    have := hFm h.le; linarith⟩
  have hu : IDS ν (sInf L) = ℓ := hLcl.csInf_mem hLne hLbb
  have hv : IDS ν (sSup L) = ℓ := hLcl.csSup_mem hLne hLba
  have huv : sInf L ≤ sSup L :=
    (csInf_le hLbb hLne.some_mem).trans (le_csSup hLba hLne.some_mem)
  have hbelow : ∀ E < sInf L, IDS ν E < ℓ := fun E hE =>
    lt_of_le_of_ne ((hFm hE.le).trans_eq hu) fun h => (not_le.2 hE) (csInf_le hLbb h)
  have habove : ∀ E, sSup L < E → ℓ < IDS ν E := fun E hE =>
    lt_of_le_of_ne (hv.symm.trans_le (hFm hE.le)) fun h => (not_le.2 hE) (le_csSup hLba h.symm)
  -- both ends lie in `S`
  have hend : ∀ E, IDS ν E = ℓ → (∀ x < E, IDS ν x < ℓ) ∨ (∀ x, E < x → ℓ < IDS ν x) →
      E ∈ S := by
    intro E hE hside
    by_contra hES
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hS.isOpen_compl E hES
    rcases hside with h | h
    · obtain ⟨z, hz, hzS⟩ := Ioo_inter_nonempty hSc hat
        (x := E - ε / 2) (y := E) (by rw [hE]; exact h _ (by linarith))
      exact hball (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;>
        linarith [hz.1, hz.2]) hzS
    · obtain ⟨z, hz, hzS⟩ := Ioo_inter_nonempty hSc hat
        (x := E) (y := E + ε / 2) (by rw [hE]; exact h _ (by linarith))
      exact hball (by rw [Metric.mem_ball, Real.dist_eq, abs_lt]; constructor <;>
        linarith [hz.1, hz.2]) hzS
  have huS : sInf L ∈ S := hend _ hu (Or.inl hbelow)
  have hvS : sSup L ∈ S := hend _ hv (Or.inr habove)
  rcases huv.lt_or_eq with h | h
  · left
    refine ⟨sInf L, sSup L, h, huS, hvS, ?_, fun E hE => le_antisymm ?_ ?_⟩
    · refine eq_empty_iff_forall_notMem.2 fun E ⟨hE, hES⟩ => ?_
      set δ := min (E - sInf L) (sSup L - E)
      have hδ : 0 < δ := lt_min (by linarith [hE.1]) (by linarith [hE.2])
      have hpos := hsupp E hES δ hδ
      have hsub : Ioo (E - δ) (E + δ) ⊆ Ioc (sInf L) (sSup L) := fun z hz =>
        ⟨by linarith [hz.1, min_le_left (E - sInf L) (sSup L - E)],
          by linarith [hz.2, min_le_right (E - sInf L) (sSup L - E)]⟩
      have h0 : ν (Ioc (sInf L) (sSup L)) = 0 := by
        rw [measure_Ioc_eq_IDS, hu, hv, sub_self, ENNReal.ofReal_zero]
      exact (measure_mono_null hsub h0 ▸ hpos).ne rfl
    · exact (hFm hE.2).trans_eq hv
    · exact hu.symm.trans_le (hFm hE.1)
  · right
    exact ⟨sInf L, huS, hu, hbelow, fun E hE => habove E (h ▸ hE)⟩

/-- Approximating sequences in `S` from both sides of an isolated level point. -/
lemma exists_seq_sides {S : Set ℝ} (hSc : ν Sᶜ = 0) (hat : ∀ E, ν {E} = 0) {E₀ ℓ : ℝ}
    (hE₀ : IDS ν E₀ = ℓ) (hbel : ∀ E < E₀, IDS ν E < ℓ) (habo : ∀ E, E₀ < E → ℓ < IDS ν E) :
    ∃ Em Ep : ℕ → ℝ, (∀ j, Em j ∈ S) ∧ (∀ j, Ep j ∈ S) ∧ Tendsto Em atTop (𝓝 E₀) ∧
      Tendsto Ep atTop (𝓝 E₀) ∧ (∀ j, IDS ν (Em j) < ℓ) ∧ (∀ j, ℓ < IDS ν (Ep j)) := by
  have hm : ∀ j : ℕ, ∃ e, e ∈ Ioo (E₀ - 1 / ((j : ℝ) + 1)) E₀ ∩ S := fun j =>
    Ioo_inter_nonempty hSc hat (by rw [hE₀]; exact hbel _ (by
      have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
      linarith))
  have hp : ∀ j : ℕ, ∃ e, e ∈ Ioo E₀ (E₀ + 1 / ((j : ℝ) + 1)) ∩ S := fun j =>
    Ioo_inter_nonempty hSc hat (by rw [hE₀]; exact habo _ (by
      have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
      linarith))
  choose Em hEm using hm
  choose Ep hEp using hp
  have hlim : Tendsto (fun j : ℕ => 1 / ((j : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨Em, Ep, fun j => (hEm j).2, fun j => (hEp j).2, ?_, ?_,
    fun j => hbel _ (hEm j).1.2, fun j => habo _ (hEp j).1.1⟩
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds
      (fun j => (hEm j).1.1.le) (fun j => (hEm j).1.2.le)
    simpa using (tendsto_const_nhds (x := E₀)).sub hlim
  · refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun j => (hEp j).1.1.le) (fun j => (hEp j).1.2.le)
    simpa using (tendsto_const_nhds (x := E₀)).add hlim

end IDS

/-! ### Perfectness from atomlessness -/

/-- An isolated point of `Σ` would be an atom of the DOS measure, because the DOS measure has
full support on `Σ` (Paper I, `AMO.dos_support`). -/
theorem perfect_of_atomless {α : ℝ} (hα : Irrational α) {R : Symbol} (hRs : SymbolSummable R)
    (hsa : SymbolSelfAdjoint R) {ν : Measure ℝ} (hν : IsDOSMeasure (H α 1 R) ν)
    (hat : ∀ E, ν {E} = 0) : Perfect (Sigma α 1 R) := by
  refine ⟨spectrum_real_isClosed _, preperfect_iff_nhds.2 fun E hE U hU => ?_⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
  by_contra h
  push_neg at h
  have hsupp := dos_support hα hRs hsa hν hE hε
  have hsub : Ioo (E - ε) (E + ε) ⊆ {E} ∪ (Sigma α 1 R)ᶜ := by
    intro y hy
    by_cases hyS : y ∈ Sigma α 1 R
    · left
      exact h y ⟨hball (by rw [Real.ball_eq_Ioo]; exact hy), hyS⟩
    · exact Or.inr hyS
  have h0 : ν (Ioo (E - ε) (E + ε)) = 0 :=
    measure_mono_null hsub (measure_union_null (hat E) hsupp.2)
  exact hsupp.1.ne' h0

/-! ### Uniqueness of the DOS measure -/

/-- The density of states measure of a family is unique (bounded continuous functions determine
finite Borel measures on `ℝ`). -/
theorem IsDOSMeasure.unique {Hx : ℝ → Op ℤ} {ν ν' : Measure ℝ} (h : IsDOSMeasure Hx ν)
    (h' : IsDOSMeasure Hx ν') : ν = ν' := by
  haveI := h.1
  haveI := h'.1
  exact ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => (h.2 f).trans (h'.2 f).symm

/-! ### Open gaps in the paper's sense -/

/-- The paper's notion of an open gap with label `{nα}` (§1): a nonempty bounded component
`(a, b)` of `ℝ ∖ Σ` (endpoints in `Σ`) on which `N` is constant equal to the label; by right
continuity of `N` this is `N = {nα}` on `[a, b)`. -/
def GapOpenWeak (Sig : Set ℝ) (ν : Measure ℝ) (α : ℝ) (n : ℤ) : Prop :=
  ∃ a b : ℝ, a < b ∧ a ∈ Sig ∧ b ∈ Sig ∧ Ioo a b ∩ Sig = ∅ ∧
    ∀ E ∈ Ico a b, IDS ν E = Int.fract (n * α)

/-- Every allowed internal label is realized by an open gap, in the paper's sense. -/
def AllGapsOpenWeak (Sig : Set ℝ) (ν : Measure ℝ) (α : ℝ) : Prop :=
  ∀ n : ℤ, n ≠ 0 → GapOpenWeak Sig ν α n

lemma AllGapsOpen.weak {Sig : Set ℝ} {ν : Measure ℝ} {α : ℝ} (h : AllGapsOpen Sig ν α) :
    AllGapsOpenWeak Sig ν α := fun n hn => by
  obtain ⟨a, b, hab, ha, hb, hgap, hIDS⟩ := h n hn
  exact ⟨a, b, hab, ha, hb, hgap, fun E hE => hIDS E ⟨hE.1, hE.2.le⟩⟩

/-- For an atomless DOS carried by `Sig`, the paper's notion of open gap gives `AMO.GapOpen`
(the label also holds at the right endpoint). -/
theorem AllGapsOpenWeak.toAllGapsOpen {Sig : Set ℝ} {ν : Measure ℝ} [IsProbabilityMeasure ν]
    {α : ℝ} (h : AllGapsOpenWeak Sig ν α) (hSc : ν Sigᶜ = 0) (hat : ∀ E, ν {E} = 0) :
    AllGapsOpen Sig ν α := fun n hn => by
  obtain ⟨a, b, hab, ha, hb, hgap, hIDS⟩ := h n hn
  refine ⟨a, b, hab, ha, hb, hgap, fun E hE => ?_⟩
  rcases hE.2.lt_or_eq with hlt | rfl
  · exact hIDS E ⟨hE.1, hlt⟩
  · have hsub : Ioc a E ⊆ Sigᶜ ∪ {E} := by
      intro x hx
      rcases hx.2.lt_or_eq with hxl | rfl
      · left
        intro hxS
        have : x ∈ Ioo a E ∩ Sig := ⟨⟨hx.1, hxl⟩, hxS⟩
        rw [hgap] at this
        exact this
      · exact Or.inr rfl
    have h0 : ν (Ioc a E) = 0 := measure_mono_null hsub (measure_union_null hSc (hat E))
    rw [measure_Ioc_eq_IDS] at h0
    have h1 := ENNReal.ofReal_eq_zero.1 h0
    have h2 := IDS_mono (ν := ν) hab.le
    have h3 := hIDS a ⟨le_rfl, hab⟩
    linarith

end SGD
