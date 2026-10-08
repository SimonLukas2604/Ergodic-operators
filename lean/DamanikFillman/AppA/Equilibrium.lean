/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Appendix A.2: lower semicontinuity of the energy and existence of equilibrium measures
(book pp. 412–415)

## Main results

* `DF.continuous_dblInt` — for a compact metric space `X` and `f ∈ C(X × X)`, the map
  `ν ↦ ∫∫ f dν dν` is weak-* continuous on probability measures (the Stone–Weierstrass
  argument from the proof of Lemma A.2.4).
* `DF.lowerSemicontinuous_energy` — **Lemma A.2.4**: on `M1(K)` (realised as
  `ProbabilityMeasure K`, with the weak-* topology) the energy is lower semicontinuous.
* `DF.exists_isEquilibriumMeasure` — **Theorem A.2.6, existence**: a compact set of positive
  capacity carries an energy minimizing probability measure.  Together with
  `DF.IsEquilibriumMeasure.unique'` (from Prop. A.2.5, proved in `EnergyConvexity.lean`)
  this gives Theorem A.2.6.
* `DF.equilibriumExistenceStatement_holds` — the statement recorded in `Potential.lean` holds.
* **Proposition A.2.2(e)**: `tendsto_capCompact_antitone`, `tendsto_capacity_antitone`,
  `tendsto_capacity_monotone`, and `capacity_eq_capCompact` (the capacities (A.2.1) and
  (A.2.2)–(A.2.3) agree on compact sets); hence `capacityRegularityStatement_holds`.
-/
import DamanikFillman.AppA.Potential
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

noncomputable section

open Real Complex Metric Set Filter Topology MeasureTheory
open scoped ENNReal BoundedContinuousFunction

namespace DF

section DoubleIntegral

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The double integral `∫∫ f(a, b) dν(b) dν(a)`. -/
def dblInt (f : C(X × X, ℝ)) (ν : ProbabilityMeasure X) : ℝ :=
  ∫ a, ∫ b, f (a, b) ∂(ν : Measure X) ∂(ν : Measure X)

lemma integrable_of_continuous_compact {g : X → ℝ} (hg : Continuous g) (ν : Measure X)
    [IsFiniteMeasure ν] : Integrable g ν :=
  integrableOn_univ.1 (hg.continuousOn.integrableOn_compact isCompact_univ)

lemma continuous_innerInt (f : C(X × X, ℝ)) (ν : Measure X) [IsFiniteMeasure ν] :
    Continuous (fun a => ∫ b, f (a, b) ∂ν) := by
  have := continuous_parametric_integral_of_continuous (μ := ν) (f := fun a b => f (a, b))
    (by exact f.continuous) isCompact_univ
  simpa [Measure.restrict_univ] using this

lemma integrable_innerInt (f : C(X × X, ℝ)) (ν : Measure X) [IsFiniteMeasure ν] (a : X) :
    Integrable (fun b => f (a, b)) ν :=
  integrable_of_continuous_compact (by fun_prop) ν

lemma dblInt_add (f g : C(X × X, ℝ)) (ν : ProbabilityMeasure X) :
    dblInt (f + g) ν = dblInt f ν + dblInt g ν := by
  unfold dblInt
  rw [← integral_add (integrable_of_continuous_compact (continuous_innerInt f _) _)
    (integrable_of_continuous_compact (continuous_innerInt g _) _)]
  congr 1; funext a
  simp only [ContinuousMap.add_apply]
  exact integral_add (integrable_innerInt f _ a) (integrable_innerInt g _ a)

omit [CompactSpace X] [BorelSpace X] in
lemma dblInt_smul (c : ℝ) (f : C(X × X, ℝ)) (ν : ProbabilityMeasure X) :
    dblInt (c • f) ν = c * dblInt f ν := by
  unfold dblInt
  simp only [ContinuousMap.smul_apply, smul_eq_mul, integral_const_mul]

omit [CompactSpace X] [BorelSpace X] in
lemma dblInt_zero (ν : ProbabilityMeasure X) : dblInt (0 : C(X × X, ℝ)) ν = 0 := by
  simp [dblInt]

omit [BorelSpace X] in
lemma abs_dblInt_le (f : C(X × X, ℝ)) (ν : ProbabilityMeasure X) : |dblInt f ν| ≤ ‖f‖ := by
  unfold dblInt
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le_const (C := ‖f‖) (Eventually.of_forall fun a => ?_)).trans
    (by simp)
  refine (norm_integral_le_of_norm_le_const (C := ‖f‖)
    (Eventually.of_forall fun b => f.norm_coe_le_norm (a, b))).trans (by simp)

/-- Products `g(a) h(b)` form a submonoid of `C(X × X)`. -/
def tensorSubmonoid (X : Type*) [TopologicalSpace X] : Submonoid C(X × X, ℝ) where
  carrier := {f | ∃ g h : C(X, ℝ), f = g.comp ContinuousMap.fst * h.comp ContinuousMap.snd}
  mul_mem' := by
    rintro _ _ ⟨g1, h1, rfl⟩ ⟨g2, h2, rfl⟩
    exact ⟨g1 * g2, h1 * h2, by ext; simp; ring⟩
  one_mem' := ⟨1, 1, by ext; simp⟩

lemma continuous_dblInt_tensor (g h : C(X, ℝ)) :
    Continuous (dblInt (g.comp ContinuousMap.fst * h.comp ContinuousMap.snd)) := by
  have e : ∀ ν : ProbabilityMeasure X,
      dblInt (g.comp ContinuousMap.fst * h.comp ContinuousMap.snd) ν =
        (∫ a, g a ∂(ν : Measure X)) * ∫ b, h b ∂(ν : Measure X) := by
    intro ν
    unfold dblInt
    simp only [ContinuousMap.mul_apply, ContinuousMap.comp_apply, ContinuousMap.fst_apply,
      ContinuousMap.snd_apply, integral_const_mul, integral_mul_const]
  rw [show dblInt (g.comp ContinuousMap.fst * h.comp ContinuousMap.snd) = _ from funext e]
  exact (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
    (BoundedContinuousFunction.mkOfCompact g)).mul
    (ProbabilityMeasure.continuous_integral_boundedContinuousFunction
      (BoundedContinuousFunction.mkOfCompact h))

/-- The weak-* continuity of `ν ↦ ∫∫ f dν dν` for every `f ∈ C(X × X)`, via Stone–Weierstrass
(proof of Lemma A.2.4). -/
theorem continuous_dblInt (f : C(X × X, ℝ)) : Continuous (dblInt f) := by
  set S := Algebra.adjoin ℝ ((tensorSubmonoid X : Submonoid C(X × X, ℝ)) : Set C(X × X, ℝ))
  have hS : ∀ f ∈ S, Continuous (dblInt f) := by
    intro f hf
    have hf' : f ∈ Subalgebra.toSubmodule S := hf
    rw [Algebra.adjoin_eq_span, Submonoid.closure_eq] at hf'
    clear hf
    induction hf' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, h, rfl⟩ := hx
      exact continuous_dblInt_tensor g h
    | zero => rw [show dblInt (0 : C(X × X, ℝ)) = fun _ => 0 from funext dblInt_zero]
              exact continuous_const
    | add x y _ _ hx hy =>
      rw [show dblInt (x + y) = fun ν => dblInt x ν + dblInt y ν from funext (dblInt_add x y)]
      exact hx.add hy
    | smul a x _ hx =>
      rw [show dblInt (a • x) = fun ν => a * dblInt x ν from funext (dblInt_smul a x)]
      exact continuous_const.mul hx
  have hsep : S.SeparatesPoints := by
    intro p q hpq
    have hmem : ∀ g h : C(X, ℝ), g.comp ContinuousMap.fst * h.comp ContinuousMap.snd ∈ S :=
      fun g h => Algebra.subset_adjoin ⟨g, h, rfl⟩
    by_cases h1 : p.1 = q.1
    · have h2 : p.2 ≠ q.2 := fun h2 => hpq (Prod.ext h1 h2)
      refine ⟨_, ⟨_, hmem 1 ⟨fun b => dist b p.2, by fun_prop⟩, rfl⟩, ?_⟩
      simp [dist_comm]
      exact h2
    · refine ⟨_, ⟨_, hmem ⟨fun a => dist a p.1, by fun_prop⟩ 1, rfl⟩, ?_⟩
      simp [dist_comm]
      exact h1
  have hdense := ContinuousMap.subalgebra_topologicalClosure_eq_top_of_separatesPoints S hsep
  have hf : f ∈ closure (S : Set C(X × X, ℝ)) := by
    rw [← Subalgebra.topologicalClosure_coe, hdense]; trivial
  have happrox : ∀ n : ℕ, ∃ g ∈ S, dist f g < 1 / (n + 1) := fun n =>
    Metric.mem_closure_iff.1 hf _ (by positivity)
  choose g hgS hgf using happrox
  refine TendstoUniformly.continuous (F := fun n => dblInt (g n)) (p := atTop) ?_
    (Eventually.of_forall fun n => hS _ (hgS n)).frequently
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  filter_upwards [eventually_ge_atTop N] with n hn ν
  rw [Real.dist_eq]
  have e : dblInt f ν - dblInt (g n) ν = dblInt (f - g n) ν := by
    rw [sub_eq_add_neg, sub_eq_add_neg, dblInt_add, show -g n = (-1 : ℝ) • g n by simp,
      dblInt_smul]; ring
  rw [e]
  refine lt_of_le_of_lt (abs_dblInt_le _ _) ?_
  rw [← dist_eq_norm]
  refine (hgf n).trans (lt_of_le_of_lt ?_ hN)
  gcongr

end DoubleIntegral

/-! ### Lemma A.2.4 and Theorem A.2.6 -/

section Energy

variable {K : Set ℂ}

/-- The truncated kernel on `K × K`, as a continuous function. -/
def logKerK (K : Set ℂ) (N : ℕ) : C(K × K, ℝ) :=
  ⟨fun p => logKer N ((p.1 : ℂ) - p.2),
    (continuous_logKer N).comp (continuous_subtype_val.comp continuous_fst |>.sub
      (continuous_subtype_val.comp continuous_snd))⟩

lemma map_val_compl_eq_zero (hK : IsCompact K) (ν : Measure K) :
    (ν.map ((↑) : K → ℂ)) Kᶜ = 0 := by
  rw [Measure.map_apply measurable_subtype_coe hK.isClosed.measurableSet.compl]
  convert measure_empty (μ := ν)
  ext x; simp

lemma energy_map_val (hK : IsCompact K) (ν : ProbabilityMeasure K) :
    energy ((ν : Measure K).map ((↑) : K → ℂ)) = ⨆ N : ℕ, ((dblInt (logKerK K N) ν : ℝ) : EReal) := by
  set μ := (ν : Measure K).map ((↑) : K → ℂ)
  have : IsProbabilityMeasure μ := inferInstance
  have hμ := integrable_norm_of_compact hK (map_val_compl_eq_zero hK ν)
  unfold energy mutualEnergy
  congr 1; funext N; congr 1
  unfold dblInt
  rw [integral_map measurable_subtype_coe.aemeasurable
    (continuous_potTrunc hμ N).aestronglyMeasurable]
  congr 1; funext a
  rw [integral_map measurable_subtype_coe.aemeasurable
    (by exact ((continuous_logKer N).comp (continuous_const.sub continuous_id)).aestronglyMeasurable :
      AEStronglyMeasurable (fun w => logKer N ((a : ℂ) - w)) _)]
  rfl

/-- **Lemma A.2.4**: the logarithmic energy is weak-* lower semicontinuous on `M1(K)`, realised
as the space `ProbabilityMeasure K` of probability measures on the compact set `K`. -/
theorem lowerSemicontinuous_energy (hK : IsCompact K) :
    LowerSemicontinuous (fun ν : ProbabilityMeasure K =>
      energy ((ν : Measure K).map ((↑) : K → ℂ))) := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  simp_rw [energy_map_val hK]
  exact lowerSemicontinuous_iSup fun N =>
    (continuous_coe_real_ereal.comp (continuous_dblInt (logKerK K N))).lowerSemicontinuous

lemma map_val_mem_M1 (hK : IsCompact K) (ν : ProbabilityMeasure K) :
    (ν : Measure K).map ((↑) : K → ℂ) ∈ M1 K :=
  ⟨inferInstance, map_val_compl_eq_zero hK ν⟩

lemma exists_map_val_eq (hK : IsCompact K) {μ : Measure ℂ} (hμ : μ ∈ M1 K) :
    ∃ ν : ProbabilityMeasure K, (ν : Measure K).map ((↑) : K → ℂ) = μ := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have := hμ.1
  have hmap : (μ.comap ((↑) : K → ℂ)).map ((↑) : K → ℂ) = μ := by
    rw [map_comap_subtype_coe hKm]
    refine Measure.restrict_eq_self_of_ae_mem ?_
    exact measure_eq_zero_iff_ae_notMem.1 hμ.2 |>.mono fun w hw => by simpa using hw
  have hprob : IsProbabilityMeasure (μ.comap ((↑) : K → ℂ)) := by
    constructor
    have h1 := congrArg (fun m : Measure ℂ => m univ) hmap
    simp only [Measure.map_apply measurable_subtype_coe MeasurableSet.univ, preimage_univ,
      measure_univ] at h1
    exact h1
  exact ⟨⟨_, hprob⟩, hmap⟩

/-- **Theorem A.2.6, existence**: a compact set of positive capacity admits an equilibrium
measure. -/
theorem exists_isEquilibriumMeasure (hK : IsCompact K) (hcap : capCompact K ≠ 0) :
    ∃ ρ, IsEquilibriumMeasure K ρ := by
  have : CompactSpace K := isCompact_iff_compactSpace.1 hK
  -- `K` is nonempty, since otherwise `M1 K = ∅` and the capacity vanishes
  have hne : Nonempty K := by
    by_contra h
    rw [not_nonempty_iff, isEmpty_coe_sort] at h
    apply hcap
    rw [capCompact_eq_zero_iff]
    intro μ hμ
    have := hμ.1
    have h2 := hμ.2
    rw [h, compl_empty, measure_univ] at h2
    exact absurd h2 one_ne_zero
  obtain ⟨x⟩ := hne
  have : Nonempty (ProbabilityMeasure K) := ⟨⟨Measure.dirac x, inferInstance⟩⟩
  obtain ⟨ν₀, -, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn univ_nonempty
    isCompact_univ ((lowerSemicontinuous_energy hK).lowerSemicontinuousOn univ)
  refine ⟨_, map_val_mem_M1 hK ν₀, fun μ hμ => ?_⟩
  obtain ⟨ν, rfl⟩ := exists_map_val_eq hK hμ
  exact isMinOn_iff.1 hmin ν (mem_univ ν)

/-- The existence half of Theorem A.2.6 recorded in `Potential.lean` holds. -/
theorem equilibriumExistenceStatement_holds : EquilibriumExistenceStatement :=
  fun _ hK hcap => exists_isEquilibriumMeasure hK hcap

end Energy

/-! ### Proposition A.2.2(e): regularity of the capacity -/

section Regularity

lemma expNeg_eq_exp_neg (x : EReal) : expNeg x = EReal.exp (-x) := by
  induction x using EReal.rec with
  | bot => simp
  | top => simp
  | coe x => rw [expNeg_coe, ← EReal.coe_neg, EReal.exp_coe]

/-- `x ↦ e^{-x}` turns suprema into infima. -/
lemma expNeg_iSup {ι : Sort*} (e : ι → EReal) : expNeg (⨆ i, e i) = ⨅ i, expNeg (e i) := by
  simp_rw [expNeg_eq_exp_neg, ereal_neg_iSup]
  exact EReal.expOrderIso.map_iInf _

/-- Capacity is continuous along decreasing sequences of compact sets (Prop. A.2.2(e), for the
capacity (A.2.1) of compact sets).  The proof extracts a weak-* limit of the equilibrium
measures and uses Lemma A.2.4. -/
theorem tendsto_capCompact_antitone {K : ℕ → Set ℂ} (hK : ∀ n, IsCompact (K n))
    (hanti : Antitone K) :
    Tendsto (fun n => capCompact (K n)) atTop (𝓝 (capCompact (⋂ n, K n))) := by
  have hmono : Antitone (fun n => capCompact (K n)) := fun m n h => capCompact_mono (hanti h)
  have hlim := tendsto_atTop_iInf hmono
  suffices h : ⨅ n, capCompact (K n) = capCompact (⋂ n, K n) by rwa [h] at hlim
  refine le_antisymm ?_ (le_iInf fun n => capCompact_mono (iInter_subset _ n))
  by_cases hzero : ∃ n, capCompact (K n) = 0
  · obtain ⟨n, hn⟩ := hzero
    exact (iInf_le _ n).trans (hn.symm ▸ zero_le)
  push Not at hzero
  choose ρ hρ using fun n => exists_isEquilibriumMeasure (hK n) (hzero n)
  have : CompactSpace (K 0) := isCompact_iff_compactSpace.1 (hK 0)
  have hρ0 : ∀ n, ρ n ∈ M1 (K 0) := fun n => M1_mono (hanti (Nat.zero_le n)) (hρ n).1
  choose ν hν using fun n => exists_map_val_eq (hK 0) (hρ0 n)
  obtain ⟨νlim, -, φ, hφ, hlimν⟩ :=
    (isCompact_univ (X := ProbabilityMeasure (K 0))).tendsto_subseq (x := ν) (fun _ => mem_univ _)
  set ρlim := (νlim : Measure (K 0)).map ((↑) : K 0 → ℂ) with hρlim
  -- the limit is carried by `⋂ Kₙ`
  have hsupp : ρlim ∈ M1 (⋂ n, K n) := by
    refine ⟨inferInstance, ?_⟩
    rw [compl_iInter]
    refine measure_iUnion_null fun m => ?_
    rw [hρlim, Measure.map_apply measurable_subtype_coe (hK m).isClosed.measurableSet.compl]
    have hopen : IsOpen (((↑) : K 0 → ℂ) ⁻¹' (K m)ᶜ) :=
      (hK m).isClosed.isOpen_compl.preimage continuous_subtype_val
    have h1 := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlimν hopen
    have h2 : ∀ᶠ n in atTop,
        ((ν ∘ φ) n : Measure (K 0)) (((↑) : K 0 → ℂ) ⁻¹' (K m)ᶜ) = 0 := by
      filter_upwards [eventually_ge_atTop m] with n hn
      have h3 := (hρ (φ n)).1.2
      rw [← hν (φ n), Measure.map_apply measurable_subtype_coe
        (hK _).isClosed.measurableSet.compl] at h3
      exact measure_mono_null (preimage_mono (compl_subset_compl.2
        (hanti (hn.trans (hφ.id_le n))))) h3
    have h4 : liminf (fun n => ((ν ∘ φ) n : Measure (K 0)) (((↑) : K 0 → ℂ) ⁻¹' (K m)ᶜ))
        atTop = 0 := by
      rw [liminf_congr h2, liminf_const]
    exact le_antisymm (h1.trans h4.le) zero_le
  -- lower semicontinuity of the energy
  have hEle : energy ρlim ≤ ⨆ n, energy (ρ n) := by
    refine le_of_forall_lt fun y hy => ?_
    have hev := hlimν.eventually ((lowerSemicontinuous_energy (hK 0)) νlim y hy)
    obtain ⟨n, hn⟩ := hev.exists
    simp only [Function.comp, hν] at hn
    exact hn.trans_le (le_iSup (fun n => energy (ρ n)) (φ n))
  calc ⨅ n, capCompact (K n) = ⨅ n, expNeg (energy (ρ n)) := by
        congr 1; funext n; exact (hρ n).capCompact_eq
    _ = expNeg (⨆ n, energy (ρ n)) := (expNeg_iSup _).symm
    _ ≤ expNeg (energy ρlim) := expNeg_antitone hEle
    _ ≤ capCompact (⋂ n, K n) := expNeg_energy_le_capCompact hsupp

/-- For compact sets the capacity defined via (A.2.2)–(A.2.3) agrees with (A.2.1). -/
theorem capacity_eq_capCompact {K : Set ℂ} (hK : IsCompact K) : capacity K = capCompact K := by
  refine le_antisymm ?_ (capCompact_le_capacity hK)
  set Kn : ℕ → Set ℂ := fun n => cthickening (1 / ((n : ℝ) + 1)) K with hKn_def
  have hKn : ∀ n, IsCompact (Kn n) := fun n => hK.cthickening
  have hanti : Antitone Kn := fun m n h => cthickening_mono
    (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right h 1)) K
  have hinter : ⋂ n, Kn n = K := by
    apply subset_antisymm
    · intro x hx
      rw [← hK.isClosed.closure_eq, closure_eq_iInter_cthickening]
      simp only [mem_iInter]
      intro δ hδ
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
      exact cthickening_mono hn.le K (mem_iInter.1 hx n)
    · exact subset_iInter fun n => self_subset_cthickening K
  have hlim := tendsto_capCompact_antitone hKn hanti
  rw [hinter] at hlim
  have hle : ∀ n, capacity K ≤ capCompact (Kn n) := by
    intro n
    unfold capacity
    refine iInf_le_of_le (thickening (1 / ((n : ℝ) + 1)) K) (iInf_le_of_le isOpen_thickening
      (iInf_le_of_le hK.isBounded.thickening
        (iInf_le_of_le (self_subset_thickening (by positivity) K) ?_)))
    exact iSup₂_le fun K' _ => iSup_le fun hK'O =>
      capCompact_mono (hK'O.trans (thickening_subset_cthickening _ _))
  exact ge_of_tendsto hlim (Eventually.of_forall hle)

/-- Prop. A.2.2(e), first half. -/
theorem tendsto_capacity_antitone {K : ℕ → Set ℂ} (hK : ∀ n, IsCompact (K n))
    (hanti : Antitone K) :
    Tendsto (fun n => capacity (K n)) atTop (𝓝 (capacity (⋂ n, K n))) := by
  have hI : IsCompact (⋂ n, K n) :=
    (hK 0).of_isClosed_subset (isClosed_iInter fun n => (hK n).isClosed) (iInter_subset _ 0)
  simp_rw [capacity_eq_capCompact (hK _), capacity_eq_capCompact hI]
  exact tendsto_capCompact_antitone hK hanti

lemma capacity_open_eq {O : Set ℂ} (hO : IsOpen O) (hb : Bornology.IsBounded O) :
    capacity O = ⨆ (K : Set ℂ) (_ : IsCompact K) (_ : K ⊆ O), capCompact K := by
  apply le_antisymm
  · exact iInf_le_of_le O (iInf_le_of_le hO (iInf_le_of_le hb (iInf_le_of_le subset_rfl le_rfl)))
  · exact le_iInf fun O' => le_iInf fun _ => le_iInf fun _ => le_iInf fun hOO' =>
      iSup₂_le fun K hK => iSup_le fun hKO =>
        le_iSup_of_le K (le_iSup_of_le hK (le_iSup_of_le (hKO.trans hOO') le_rfl))

/-- Prop. A.2.2(e), second half: continuity along increasing sequences of bounded open sets. -/
theorem tendsto_capacity_monotone {O : ℕ → Set ℂ} (hO : ∀ n, IsOpen (O n)) (hmono : Monotone O)
    (hb : Bornology.IsBounded (⋃ n, O n)) :
    Tendsto (fun n => capacity (O n)) atTop (𝓝 (capacity (⋃ n, O n))) := by
  have hbn : ∀ n, Bornology.IsBounded (O n) := fun n => hb.subset (subset_iUnion _ n)
  have hcm : Monotone (fun n => capacity (O n)) := fun m n h => capacity_mono (hmono h)
  have hlim := tendsto_atTop_iSup hcm
  suffices h : ⨆ n, capacity (O n) = capacity (⋃ n, O n) by rwa [h] at hlim
  refine le_antisymm (iSup_le fun n => capacity_mono (subset_iUnion _ n)) ?_
  rw [capacity_open_eq (isOpen_iUnion hO) hb]
  refine iSup₂_le fun K hK => iSup_le fun hKO => ?_
  obtain ⟨n, hn⟩ := hK.elim_directed_cover O hO hKO hmono.directed_le
  refine le_iSup_of_le n ?_
  rw [capacity_open_eq (hO n) (hbn n)]
  exact le_iSup_of_le K (le_iSup_of_le hK (le_iSup_of_le hn le_rfl))

/-- `CapacityRegularityStatement` (Prop. A.2.2(e) and the consistency of (A.2.1) with
(A.2.2)–(A.2.3)) holds. -/
theorem capacityRegularityStatement_holds : CapacityRegularityStatement :=
  ⟨fun _ hK => capacity_eq_capCompact hK, fun _ hK hanti => tendsto_capacity_antitone hK hanti,
    fun _ hO hmono hb => tendsto_capacity_monotone hO hmono hb⟩

end Regularity

end DF
