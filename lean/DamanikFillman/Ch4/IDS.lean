/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §4.3 The integrated density of states   (book pp. 315–322)

## Main definitions (namespace `DF.ErgodicFamily`)
* `E.dosm` — the **density of states measure** `dk` (Definition 4.3.1): the `μ`-average of the
  spectral measures `η_{ω,0}`, i.e. the Giry-monad bind `μ.bind (ω ↦ η_{ω,0})`;
* `E.ids` — the **integrated density of states** `k(E) = dk((-∞, E])` (4.3.2);
* `E.dkN ω N` — the measures `dk_{ω,N}`, `∫ g dk_{ω,N} = N⁻¹ Tr(g(H_ω) χ_{[1,N]})`
  (Definition 4.3.3).

## Main results
* `E.integral_dosm`, `E.integral_dosm_real` — the defining property (4.3.1):
  `∫ g dk = E⟨δ₀, g(H_ω) δ₀⟩` for bounded Borel `g`; `E.integral_dosm_dlt` — (4.3.3) for any
  `δₙ`; `E.integral_dosm_canonical` — (4.3.4): `∫ g dk = ½ E(∫ g dη_ω)`;
* `E.support_dosm` — **Theorem 4.3.2**: `supp(dk) = Σ`;
* `E.tendsto_integral_dkN` — **Lemma 4.3.4**: `∫ g dk_{ω,N} → ∫ g dk` a.s., for each bounded
  measurable `g`;
* `E.ae_tendsto_dkN` — **Corollary 4.3.5**: almost surely, `dk_{ω,N} → dk` weakly;
* `E.dosm_singleton`, `E.continuous_ids` — **Theorem 4.3.6**: `dk` has no atoms and `k` is
  continuous.

Theorems 4.3.8 and 4.3.9 (Dirichlet truncations, rotation number) are in
`DamanikFillman/Ch4/IDSTruncation.lean`.

No `Statement` props are introduced in this file.
-/
import DamanikFillman.Ch4.Nonrandom
import DamanikFillman.Ch3.Birkhoff

noncomputable section

open scoped InnerProductSpace ComplexConjugate NNReal ENNReal Topology
open MeasureTheory Set Filter L2

namespace DF

/-! ### Integrals against a bind of measures -/

section Bind

variable {X : Type*} [MeasurableSpace X]

lemma isProbabilityMeasure_bind (m : Measure X) [IsProbabilityMeasure m] {ν : X → Measure ℝ}
    [∀ x, IsProbabilityMeasure (ν x)] (hν : Measurable ν) : IsProbabilityMeasure (m.bind ν) :=
  ⟨by rw [Measure.bind_apply MeasurableSet.univ hν.aemeasurable]; simp⟩

lemma lintegral_ofReal_le_of_bdd {ν : Measure ℝ} [IsProbabilityMeasure ν] {g : ℝ → ℝ} {C : ℝ}
    (hC : ∀ x, |g x| ≤ C) : ∫⁻ y, ENNReal.ofReal (g y) ∂ν ≤ ENNReal.ofReal C := by
  calc ∫⁻ y, ENNReal.ofReal (g y) ∂ν ≤ ∫⁻ _, ENNReal.ofReal C ∂ν :=
        lintegral_mono fun y => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hC y))
    _ = ENNReal.ofReal C := by simp

/-- `∫ g d(m.bind ν) = ∫ (∫ g dν_x) dm` for bounded measurable real `g`. -/
theorem integral_bind_of_bdd (m : Measure X) [IsProbabilityMeasure m] {ν : X → Measure ℝ}
    [∀ x, IsProbabilityMeasure (ν x)] (hν : Measurable ν) {g : ℝ → ℝ} (hg : Measurable g)
    {C : ℝ} (hC : ∀ x, |g x| ≤ C) :
    ∫ y, g y ∂(m.bind ν) = ∫ x, (∫ y, g y ∂(ν x)) ∂m := by
  have := isProbabilityMeasure_bind m hν
  have hintg : ∀ μ' : Measure ℝ, IsFiniteMeasure μ' → Integrable g μ' := fun μ' _ =>
    (integrable_const C).mono' hg.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x)
  have hCn : ∀ x, |(-g) x| ≤ C := fun x => by simpa using hC x
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hintg _ inferInstance),
    Measure.lintegral_bind hν.aemeasurable hg.ennreal_ofReal.aemeasurable,
    Measure.lintegral_bind (f := fun a => ENNReal.ofReal (-g a)) hν.aemeasurable hg.neg.ennreal_ofReal.aemeasurable]
  simp_rw [fun x => integral_eq_lintegral_pos_part_sub_lintegral_neg_part
    (hintg (ν x) inferInstance)]
  have hm1 : Measurable fun x => ∫⁻ y, ENNReal.ofReal (g y) ∂(ν x) :=
    (Measure.measurable_lintegral hg.ennreal_ofReal).comp hν
  have hm2 : Measurable fun x => ∫⁻ y, ENNReal.ofReal (-g y) ∂(ν x) :=
    (Measure.measurable_lintegral hg.neg.ennreal_ofReal).comp hν
  have hb1 : ∀ x, ∫⁻ y, ENNReal.ofReal (g y) ∂(ν x) ≤ ENNReal.ofReal C := fun x =>
    lintegral_ofReal_le_of_bdd hC
  have hb2 : ∀ x, ∫⁻ y, ENNReal.ofReal (-g y) ∂(ν x) ≤ ENNReal.ofReal C := fun x =>
    lintegral_ofReal_le_of_bdd (g := -g) hCn
  have hfin1 : ∀ᵐ x ∂m, ∫⁻ y, ENNReal.ofReal (g y) ∂(ν x) < ⊤ :=
    ae_of_all _ fun x => (hb1 x).trans_lt ENNReal.ofReal_lt_top
  have hfin2 : ∀ᵐ x ∂m, ∫⁻ y, ENNReal.ofReal (-g y) ∂(ν x) < ⊤ :=
    ae_of_all _ fun x => (hb2 x).trans_lt ENNReal.ofReal_lt_top
  have hi : ∀ (F : X → ℝ≥0∞), Measurable F → (∀ x, F x ≤ ENNReal.ofReal C) →
      Integrable (fun x => (F x).toReal) m := fun F hF hb =>
    (integrable_const C).mono' hF.ennreal_toReal.aestronglyMeasurable (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
      have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC 0)
      calc (F x).toReal ≤ (ENNReal.ofReal C).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top (hb x)
        _ = C := ENNReal.toReal_ofReal hC0)
  rw [integral_sub (hi _ hm1 hb1) (hi _ hm2 hb2), integral_toReal hm1.aemeasurable hfin1,
    integral_toReal hm2.aemeasurable hfin2]

/-- Complex version of `integral_bind_of_bdd`. -/
theorem integral_bind_complex (m : Measure X) [IsProbabilityMeasure m] {ν : X → Measure ℝ}
    [∀ x, IsProbabilityMeasure (ν x)] (hν : Measurable ν) {g : ℝ → ℂ} (hg : IsBddBorel g) :
    ∫ y, g y ∂(m.bind ν) = ∫ x, (∫ y, g y ∂(ν x)) ∂m := by
  have := isProbabilityMeasure_bind m hν
  obtain ⟨C, hC⟩ := hg.bdd
  have hre : ∀ x, |(g x).re| ≤ C := fun x => (Complex.abs_re_le_norm _).trans (hC x)
  have him : ∀ x, |(g x).im| ≤ C := fun x => (Complex.abs_im_le_norm _).trans (hC x)
  have hmre : Measurable fun x => (g x).re := Complex.measurable_re.comp hg.meas
  have hmim : Measurable fun x => (g x).im := Complex.measurable_im.comp hg.meas
  have h1 := integral_bind_of_bdd m hν hmre hre
  have h2 := integral_bind_of_bdd m hν hmim him
  have hsplit : ∀ μ' : Measure ℝ, IsFiniteMeasure μ' →
      ∫ y, g y ∂μ' = ((∫ y, (g y).re ∂μ' : ℝ) : ℂ) + ((∫ y, (g y).im ∂μ' : ℝ) : ℂ) * Complex.I :=
    fun μ' _ => (integral_re_add_im (hg.integrable μ')).symm
  rw [hsplit _ inferInstance]
  simp_rw [fun x => hsplit (ν x) inferInstance]
  have hint : ∀ (F : ℝ → ℝ), Measurable F → (∀ x, |F x| ≤ C) →
      Integrable (fun x => ∫ y, F y ∂(ν x)) m := by
    intro F hF hFC
    refine (integrable_const C).mono' (measurable_integral_of_bdd hν hF hFC).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ y, |F y| ∂(ν x) ≤ ∫ _, C ∂(ν x) :=
          integral_mono_of_nonneg (ae_of_all _ fun y => abs_nonneg _) (integrable_const C)
            (ae_of_all _ hFC)
      _ = C := by simp
  rw [integral_add ((hint _ hmre hre).ofReal) (((hint _ hmim him).ofReal).mul_const _),
    integral_mul_const, integral_complex_ofReal, integral_complex_ofReal, h1, h2]

end Bind

/-! ### Weak convergence from convergence of moments -/

section Moments

lemma integrable_of_ae_bdd {ν : Measure ℝ} [IsFiniteMeasure ν] {f : ℝ → ℝ} (hf : Measurable f)
    {K : ℝ} (hK : ∀ᵐ x ∂ν, |f x| ≤ K) : Integrable f ν :=
  (integrable_const K).mono' hf.aestronglyMeasurable
    (by filter_upwards [hK] with x hx; rwa [Real.norm_eq_abs])

lemma integrable_cont_of_supp {ν : Measure ℝ} [IsFiniteMeasure ν] {R : ℝ}
    (hs : ∀ᵐ x ∂ν, x ∈ Icc (-R) R) {f : ℝ → ℝ} (hf : Continuous f) : Integrable f ν := by
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := -R) (b := R)).exists_bound_of_continuousOn
    hf.continuousOn
  exact integrable_of_ae_bdd hf.measurable (by
    filter_upwards [hs] with x hx; rw [← Real.norm_eq_abs]; exact hK x hx)

/-- If finite measures `ν_N`, `ν` (of mass `≤ 1`) are all concentrated on `[-R, R]` and all
moments converge, then `∫ g dν_N → ∫ g dν` for every continuous `g` (Weierstrass). -/
theorem tendsto_integral_of_moments {ν : ℕ → Measure ℝ} {ν₀ : Measure ℝ}
    [∀ N, IsFiniteMeasure (ν N)] [IsFiniteMeasure ν₀] {R : ℝ}
    (hs : ∀ N, ∀ᵐ x ∂(ν N), x ∈ Icc (-R) R) (hs₀ : ∀ᵐ x ∂ν₀, x ∈ Icc (-R) R)
    (hm : ∀ N, (ν N).real univ ≤ 1) (hm₀ : ν₀.real univ ≤ 1)
    (hmom : ∀ k : ℕ, Tendsto (fun N => ∫ x, x ^ k ∂(ν N)) atTop (𝓝 (∫ x, x ^ k ∂ν₀)))
    {g : ℝ → ℝ} (hg : Continuous g) :
    Tendsto (fun N => ∫ x, g x ∂(ν N)) atTop (𝓝 (∫ x, g x ∂ν₀)) := by
  -- polynomials
  have hpoly : ∀ p : Polynomial ℝ, Tendsto (fun N => ∫ x, p.eval x ∂(ν N)) atTop
      (𝓝 (∫ x, p.eval x ∂ν₀)) := by
    intro p
    have hint : ∀ (μ' : Measure ℝ) [IsFiniteMeasure μ'], (∀ᵐ x ∂μ', x ∈ Icc (-R) R) →
        ∫ x, p.eval x ∂μ' = ∑ i ∈ Finset.range (p.natDegree + 1), p.coeff i * ∫ x, x ^ i ∂μ' := by
      intro μ' _ hs'
      simp_rw [Polynomial.eval_eq_sum_range]
      rw [integral_finsetSum _ fun i _ =>
        (integrable_cont_of_supp hs' (continuous_pow i)).const_mul _]
      simp_rw [integral_const_mul]
    simp_rw [hint _ (hs _), hint ν₀ hs₀]
    exact tendsto_finsetSum _ fun i _ => (hmom i).const_mul _
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-R) R g hg.continuousOn (ε / 4)
    (by positivity)
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.1 (hpoly p) (ε / 4) (by positivity)
  refine ⟨N₀, fun N hN => ?_⟩
  have hbd : ∀ (μ' : Measure ℝ) [IsFiniteMeasure μ'], (∀ᵐ x ∂μ', x ∈ Icc (-R) R) →
      μ'.real univ ≤ 1 → |∫ x, g x ∂μ' - ∫ x, p.eval x ∂μ'| ≤ ε / 4 := by
    intro μ' _ hs' hm'
    rw [← integral_sub (integrable_cont_of_supp hs' hg)
      (integrable_cont_of_supp hs' (Polynomial.continuous p)), ← Real.norm_eq_abs]
    refine (norm_integral_le_of_norm_le_const (C := ε / 4) ?_).trans ?_
    · filter_upwards [hs'] with x hx
      rw [Real.norm_eq_abs, abs_sub_comm]; exact (hp x hx).le
    · calc ε / 4 * μ'.real univ ≤ ε / 4 * 1 := by gcongr
        _ = ε / 4 := mul_one _
  have h1 := hbd (ν N) (hs N) (hm N)
  have h2 := hbd ν₀ hs₀ hm₀
  have h3 := hN₀ N hN
  rw [Real.dist_eq] at h3 ⊢
  calc |∫ x, g x ∂(ν N) - ∫ x, g x ∂ν₀|
      = |(∫ x, g x ∂(ν N) - ∫ x, p.eval x ∂(ν N)) + (∫ x, p.eval x ∂(ν N) - ∫ x, p.eval x ∂ν₀)
          - (∫ x, g x ∂ν₀ - ∫ x, p.eval x ∂ν₀)| := by ring_nf
    _ ≤ |∫ x, g x ∂(ν N) - ∫ x, p.eval x ∂(ν N)| + |∫ x, p.eval x ∂(ν N) - ∫ x, p.eval x ∂ν₀|
          + |∫ x, g x ∂ν₀ - ∫ x, p.eval x ∂ν₀| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ < ε := by linarith

end Moments

namespace ErgodicFamily

variable {Ω : Type*} [MeasurableSpace Ω] (E : ErgodicFamily Ω)

/-! ### Definition 4.3.1 -/

/-- The **density of states measure** `dk` (Definition 4.3.1): `dk = E(η_{ω,0})`. -/
def dosm : Measure ℝ := E.μ.bind fun ω => E.spec ω (dlt 0)

instance : IsProbabilityMeasure E.dosm := isProbabilityMeasure_bind E.μ (E.measurable_spec _)

lemma dosm_apply {S : Set ℝ} (hS : MeasurableSet S) :
    E.dosm S = ∫⁻ ω, E.spec ω (dlt 0) S ∂E.μ :=
  Measure.bind_apply hS (E.measurable_spec _).aemeasurable

/-- `dk = E(η_{ω,n})` for every `n` (4.3.3). -/
lemma dosm_apply_dlt {S : Set ℝ} (hS : MeasurableSet S) (n : ℤ) :
    E.dosm S = ∫⁻ ω, E.spec ω (dlt n) S ∂E.μ := by
  rw [dosm_apply E hS]
  simp_rw [E.spec_dlt_eq _ n]
  exact ((E.measurePreserving_Tz n).lintegral_comp (E.measurable_spec_apply _ hS)).symm

/-- **(4.3.1)/(4.3.3)**: `∫ g dk = E(∫ g dη_{ω,0})` for bounded measurable real `g`. -/
theorem integral_dosm_real {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, |g x| ≤ C) :
    ∫ x, g x ∂E.dosm = ∫ ω, (∫ x, g x ∂(E.spec ω (dlt 0))) ∂E.μ :=
  integral_bind_of_bdd E.μ (E.measurable_spec _) hg hC

/-- **(4.3.1)**: `∫ g dk = E⟨δ₀, g(H_ω) δ₀⟩` for bounded Borel `g`. -/
theorem integral_dosm {g : ℝ → ℂ} (hg : IsBddBorel g) :
    ∫ x, g x ∂E.dosm = ∫ ω, ⟪dlt 0, E.fc ω g (dlt 0)⟫_ℂ ∂E.μ := by
  rw [dosm, integral_bind_complex E.μ (E.measurable_spec _) hg]
  simp_rw [E.inner_fc_self hg]

lemma integral_spec_Tz {g : ℝ → ℂ} (hg : IsBddBorel g) (n : ℤ) :
    ∫ ω, (∫ x, g x ∂(E.spec ω (dlt n))) ∂E.μ = ∫ ω, (∫ x, g x ∂(E.spec ω (dlt 0))) ∂E.μ := by
  simp_rw [E.spec_dlt_eq _ n]
  have hmp := E.measurePreserving_Tz n
  have := integral_map (μ := E.μ) hmp.measurable.aemeasurable
    (f := fun ω => ∫ x, g x ∂(E.spec ω (dlt 0)))
    (E.measurable_integral_spec hg _).aestronglyMeasurable
  rw [hmp.map_eq] at this
  exact this.symm

/-- **(4.3.3)**: `∫ g dk = E(∫ g dη_{ω,n})` for every `n`. -/
theorem integral_dosm_dlt {g : ℝ → ℂ} (hg : IsBddBorel g) (n : ℤ) :
    ∫ x, g x ∂E.dosm = ∫ ω, (∫ x, g x ∂(E.spec ω (dlt n))) ∂E.μ := by
  rw [E.integral_spec_Tz hg n, dosm, integral_bind_complex E.μ (E.measurable_spec _) hg]

/-- **(4.3.4)**: `∫ g dk = ½ E(∫ g dη_ω)` with `η_ω = η_{ω,0} + η_{ω,1}` the canonical
spectral measure. -/
theorem integral_dosm_canonical {g : ℝ → ℂ} (hg : IsBddBorel g) :
    ∫ x, g x ∂E.dosm = (1 / 2 : ℂ) * ∫ ω, (∫ x, g x ∂(E.canonical ω)) ∂E.μ := by
  have hint : ∀ n, Integrable (fun ω => ∫ x, g x ∂(E.spec ω (dlt n))) E.μ := by
    intro n
    obtain ⟨C, hC⟩ := hg.bdd
    refine (integrable_const C).mono' (E.measurable_integral_spec hg _).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    refine (norm_integral_le_integral_norm _).trans ?_
    calc ∫ x, ‖g x‖ ∂(E.spec ω (dlt n)) ≤ ∫ _, C ∂(E.spec ω (dlt n)) :=
          integral_mono_of_nonneg (ae_of_all _ fun y => norm_nonneg _) (integrable_const C)
            (ae_of_all _ hC)
      _ = C := by simp
  simp only [canonical]
  simp_rw [fun ω => integral_add_measure (hg.integrable (E.spec ω (dlt 0)))
    (hg.integrable (E.spec ω (dlt 1)))]
  rw [integral_add (hint 0) (hint 1), ← E.integral_dosm_dlt hg 0, ← E.integral_dosm_dlt hg 1]
  ring

/-! ### Theorem 4.3.2: `supp(dk) = Σ` -/

/-- `dk(S) = 0` iff `P_ω(S) = 0` almost surely. -/
theorem dosm_eq_zero_iff {S : Set ℝ} (hS : MeasurableSet S) :
    E.dosm S = 0 ↔ ∀ᵐ ω ∂E.μ, E.proj ω S = 0 := by
  rw [E.dosm_apply hS, lintegral_eq_zero_iff (E.measurable_spec_apply _ hS)]
  constructor
  · intro h
    have hn : ∀ n : ℤ, ∀ᵐ ω ∂E.μ, E.spec ω (dlt n) S = 0 := by
      intro n
      have := (E.measurePreserving_Tz n).quasiMeasurePreserving.ae h
      filter_upwards [this] with ω hω
      rw [E.spec_dlt_eq ω n]; exact hω
    filter_upwards [ae_all_iff.2 hn] with ω hω
    exact (E.proj_eq_zero_iff hS ω).2 hω
  · intro h
    filter_upwards [h] with ω hω
    exact (E.proj_eq_zero_iff hS ω).1 hω 0

/-- **Theorem 4.3.2**: the almost sure spectrum is the topological support of the density of
states measure, i.e. the set of points of increase of `k`. -/
theorem support_dosm : E.dosm.support = E.asSpectrum := by
  ext x
  rw [Measure.mem_support_iff_forall]
  simp only [asSpectrum, mem_setOf_eq]
  constructor
  · intro h a b ha hb hae
    have := h (Ioo a b) (Ioo_mem_nhds ha hb)
    rw [(E.dosm_eq_zero_iff measurableSet_Ioo).2 hae] at this
    exact lt_irrefl _ this
  · intro h U hU
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hU
    obtain ⟨a, ha1, ha2⟩ := exists_rat_btwn (show x - ε < x by linarith)
    obtain ⟨b, hb1, hb2⟩ := exists_rat_btwn (show x < x + ε by linarith)
    have hsub : Ioo (a : ℝ) b ⊆ U := fun y hy => hball (by
      rw [Real.ball_eq_Ioo]; exact ⟨by linarith [hy.1], by linarith [hy.2]⟩)
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [pos_iff_ne_zero, Ne, E.dosm_eq_zero_iff measurableSet_Ioo]
    exact h a b ha2 hb1

/-! ### Theorem 4.3.6: continuity -/

/-- **Theorem 4.3.6**: the density of states measure has no atoms. -/
theorem dosm_singleton (x : ℝ) : E.dosm {x} = 0 := by
  rw [E.dosm_apply (measurableSet_singleton x)]
  refine (lintegral_eq_zero_iff (E.measurable_spec_apply _ (measurableSet_singleton x))).2 ?_
  filter_upwards [E.ae_tr_singleton_eq_zero x] with ω hω
  exact le_antisymm ((ENNReal.le_tsum 0).trans (le_of_eq hω)) zero_le

/-- The **integrated density of states** `k(E) = dk((-∞, E])` (4.3.2). -/
def ids (x : ℝ) : ℝ := ProbabilityTheory.cdf E.dosm x

lemma ids_eq (x : ℝ) : E.ids x = E.dosm.real (Iic x) := ProbabilityTheory.cdf_eq_real _ x

lemma monotone_ids : Monotone E.ids := (ProbabilityTheory.cdf E.dosm).mono

/-- **Theorem 4.3.6**: the integrated density of states is continuous. -/
theorem continuous_ids : Continuous E.ids := by
  rw [continuous_iff_continuousAt]
  intro x
  set F := ProbabilityTheory.cdf E.dosm
  have h1 : F.measure {x} = 0 := by rw [ProbabilityTheory.measure_cdf, E.dosm_singleton]
  rw [StieltjesFunction.measure_singleton, ENNReal.ofReal_eq_zero] at h1
  have h2 : Function.leftLim F x ≤ F x := F.mono.leftLim_le le_rfl
  have hl : Function.leftLim F x = F x := le_antisymm h2 (by linarith)
  show ContinuousAt F x
  rw [F.mono.continuousAt_iff_leftLim_eq_rightLim, hl, F.rightLim_eq]

/-! ### Definition 4.3.3 and Lemma 4.3.4 -/

/-- The measures `dk_{ω,N} = N⁻¹ ∑_{n=1}^N η_{ω,n}`, so that
`∫ g dk_{ω,N} = N⁻¹ ∑_{n=1}^N ⟨δₙ, g(H_ω) δₙ⟩ = N⁻¹ Tr(g(H_ω) χ_{[1,N]})` (Definition 4.3.3). -/
def dkN (ω : Ω) (N : ℕ) : Measure ℝ :=
  (N : ℝ≥0∞)⁻¹ • ∑ k ∈ Finset.range N, E.spec ω (dlt ((k : ℤ) + 1))

instance (ω : Ω) (N : ℕ) : IsFiniteMeasure (E.dkN ω N) := by
  unfold dkN
  rcases N.eq_zero_or_pos with rfl | hN
  · simp only [Finset.range_zero, Finset.sum_empty, smul_zero]; infer_instance
  · exact Measure.smul_finite _ (ENNReal.inv_ne_top.2 (by exact_mod_cast hN.ne'))

lemma integral_dkN {g : ℝ → ℂ} (hg : IsBddBorel g) (ω : Ω) (N : ℕ) :
    ∫ x, g x ∂(E.dkN ω N) =
      (N : ℂ)⁻¹ * ∑ k ∈ Finset.range N, ⟪dlt ((k : ℤ) + 1), E.fc ω g (dlt ((k : ℤ) + 1))⟫_ℂ := by
  rw [dkN, integral_smul_measure, integral_finsetSum_measure fun i _ => hg.integrable _]
  simp_rw [E.inner_fc_self hg]
  rw [ENNReal.toReal_inv, ENNReal.toReal_natCast, Complex.real_smul]
  push_cast; rfl

lemma integral_dkN_real {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, |g x| ≤ C)
    (ω : Ω) (N : ℕ) :
    ∫ x, g x ∂(E.dkN ω N) =
      (N : ℝ)⁻¹ * ∑ k ∈ Finset.range N, ∫ x, g x ∂(E.spec ω (dlt ((k : ℤ) + 1))) := by
  have hint : ∀ μ' : Measure ℝ, IsFiniteMeasure μ' → Integrable g μ' := fun μ' _ =>
    (integrable_const C).mono' hg.aestronglyMeasurable
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hC x)
  rw [dkN, integral_smul_measure, integral_finsetSum_measure fun i _ => hint _ inferInstance,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, smul_eq_mul]

/-- **Lemma 4.3.4.** For every bounded measurable `g`, `∫ g dk_{ω,N} → ∫ g dk` for `μ`-a.e.
`ω` (Birkhoff's ergodic theorem applied to `ω ↦ ⟨δ₀, g(H_ω) δ₀⟩`). -/
theorem tendsto_integral_dkN {g : ℝ → ℝ} (hg : Measurable g) {C : ℝ} (hC : ∀ x, |g x| ≤ C) :
    ∀ᵐ ω ∂E.μ, Tendsto (fun N : ℕ => ∫ x, g x ∂(E.dkN ω N)) atTop (𝓝 (∫ x, g x ∂E.dosm)) := by
  set G : Ω → ℝ := fun ω => ∫ x, g x ∂(E.spec ω (dlt 0))
  have hGm : Measurable G := measurable_integral_of_bdd (E.measurable_spec _) hg hC
  have hGb : ∀ ω, |G ω| ≤ C := fun ω => by
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ y, |g y| ∂(E.spec ω (dlt 0)) ≤ ∫ _, C ∂(E.spec ω (dlt 0)) :=
          integral_mono_of_nonneg (ae_of_all _ fun y => abs_nonneg _) (integrable_const C)
            (ae_of_all _ hC)
      _ = C := by simp
  have hGi : Integrable G E.μ :=
    (integrable_const C).mono' hGm.aestronglyMeasurable
      (ae_of_all _ fun ω => by rw [Real.norm_eq_abs]; exact hGb ω)
  have hB := birkhoff_ergodic_tendsto E.ergodic hGi
  have hB' := E.measurePreserving_T.quasiMeasurePreserving.ae hB
  filter_upwards [hB'] with ω hω
  rw [E.integral_dosm_real hg hC]
  have key : ∀ N : ℕ, birkhoffAverage ℝ (⇑E.T) G N (E.T ω) = ∫ x, g x ∂(E.dkN ω N) := by
    intro N
    rw [E.integral_dkN_real hg hC, birkhoffAverage, birkhoffSum, smul_eq_mul]
    refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
    show ∫ x, g x ∂(E.spec ((⇑E.T)^[k] (E.T ω)) (dlt 0)) = _
    rw [← Function.iterate_succ_apply, ← Tz_natCast, E.spec_Tz, zero_add]
    push_cast; rfl
  exact hω.congr key

/-! ### Corollary 4.3.5 -/

lemma ae_mem_Icc_spec (ω : Ω) (φ : L2 ℤ) :
    ∀ᵐ x ∂(E.spec ω φ), x ∈ Icc (-(2 + E.fBound)) (2 + E.fBound) :=
  ae_mem_Icc_spectralMeasure E.H E.isSelfAdjoint_H E.norm_H_le φ ω

lemma ae_mem_Icc_dkN (ω : Ω) (N : ℕ) :
    ∀ᵐ x ∂(E.dkN ω N), x ∈ Icc (-(2 + E.fBound)) (2 + E.fBound) := by
  rw [ae_iff]
  unfold dkN
  rw [Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply]
  have : ∀ k ∈ Finset.range N, E.spec ω (dlt ((k : ℤ) + 1))
      {x | ¬ x ∈ Icc (-(2 + E.fBound)) (2 + E.fBound)} = 0 := fun k _ =>
    ae_iff.1 (E.ae_mem_Icc_spec ω _)
  rw [Finset.sum_eq_zero this, smul_zero]

lemma ae_mem_Icc_dosm : ∀ᵐ x ∂E.dosm, x ∈ Icc (-(2 + E.fBound)) (2 + E.fBound) := by
  rw [ae_iff]
  have hc : {a | a ∉ Icc (-(2 + E.fBound)) (2 + E.fBound)} = (Icc (-(2 + E.fBound)) (2 + E.fBound))ᶜ :=
    rfl
  rw [hc, E.dosm_apply (measurableSet_Icc.compl)]
  · simp only [lintegral_eq_zero_iff (E.measurable_spec_apply _ measurableSet_Icc.compl)]
    exact ae_of_all _ fun ω => ae_iff.1 (E.ae_mem_Icc_spec ω _)

lemma dkN_real_univ_le (ω : Ω) (N : ℕ) : (E.dkN ω N).real univ ≤ 1 := by
  have h : E.dkN ω N univ ≤ 1 := by
    unfold dkN
    rw [Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply]
    simp only [measure_univ, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
      smul_eq_mul]
    exact ENNReal.inv_mul_le_one _
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using h)

/-- The clamped monomials, bounded measurable functions agreeing with `x ↦ xᵏ` on `[-R, R]`. -/
def clampPow (R : ℝ) (k : ℕ) (x : ℝ) : ℝ := (max (-R) (min x R)) ^ k

lemma continuous_clampPow (R : ℝ) (k : ℕ) : Continuous (clampPow R k) := by
  unfold clampPow; fun_prop

lemma abs_clampPow_le {R : ℝ} (hR : 0 ≤ R) (k : ℕ) (x : ℝ) : |clampPow R k x| ≤ R ^ k := by
  unfold clampPow
  rw [abs_pow]
  gcongr
  exact abs_le.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

lemma clampPow_eq {R : ℝ} {k : ℕ} {x : ℝ} (hx : x ∈ Icc (-R) R) : clampPow R k x = x ^ k := by
  unfold clampPow; rw [min_eq_left hx.2, max_eq_right hx.1]

lemma integral_clampPow {ν : Measure ℝ} {R : ℝ} (hs : ∀ᵐ x ∂ν, x ∈ Icc (-R) R) (k : ℕ) :
    ∫ x, clampPow R k x ∂ν = ∫ x, x ^ k ∂ν :=
  integral_congr_ae (by filter_upwards [hs] with x hx; exact clampPow_eq hx)

/-- **Corollary 4.3.5.** Almost surely, `dk_{ω,N} → dk` weakly: there is a full-measure set of
`ω` on which `∫ g dk_{ω,N} → ∫ g dk` for *all* continuous `g`. -/
theorem ae_tendsto_dkN :
    ∀ᵐ ω ∂E.μ, ∀ g : ℝ → ℝ, Continuous g →
      Tendsto (fun N : ℕ => ∫ x, g x ∂(E.dkN ω N)) atTop (𝓝 (∫ x, g x ∂E.dosm)) := by
  set R := 2 + E.fBound
  have hR : 0 ≤ R := by have := E.fBound_nonneg; positivity
  have hmom := ae_all_iff.2 fun k : ℕ =>
    E.tendsto_integral_dkN (continuous_clampPow R k).measurable (abs_clampPow_le hR k)
  filter_upwards [hmom] with ω hω g hg
  refine tendsto_integral_of_moments (E.ae_mem_Icc_dkN ω) E.ae_mem_Icc_dosm
    (E.dkN_real_univ_le ω) (by simp) (fun k => ?_) hg
  have := hω k
  rw [integral_clampPow E.ae_mem_Icc_dosm] at this
  exact this.congr fun N => integral_clampPow (E.ae_mem_Icc_dkN ω N) k

end ErgodicFamily

end DF
