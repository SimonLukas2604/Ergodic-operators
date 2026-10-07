/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §3.6 Minimality (book pp. 263–266)

Setting: `Ω` a compact metric space, `T : Ω ≃ₜ Ω` a homeomorphism.

Main definitions (Definition 3.6.1):
* `DF.orbit T ω` — the two-sided orbit `{Tᵏω : k ∈ ℤ}`;
* `DF.TopTransitive T`, `DF.IsMinimalSys T`, `DF.StrictlyErgodic T`.

Main results:
* `DF.minimal_tfae` — **Proposition 3.6.2**: minimality ⟺ the only closed invariant sets are
  `∅` and `Ω` ⟺ `⋃_{k ∈ ℤ} Tᵏ U = Ω` for every nonempty open `U`;
* `DF.minimal_iff_forward_dense` — **Lemma 3.6.3** ((a) ⟺ (c)): minimality is equivalent to
  density of all forward orbits;
* `DF.minimal_iff_fullSupport` — **Proposition 3.6.5**: a uniquely ergodic homeomorphism is
  minimal iff its invariant measure gives positive mass to every nonempty open set.

Invariance of a set `K` is phrased as `T ⁻¹' K = K`, which for a bijection is equivalent to the
book's `T K = K` (`DF.image_eq_iff_preimage_eq`).
-/
import DamanikFillman.Ch3.TopErgodic

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Set Function Topology

namespace DF

variable {Ω : Type*} [MetricSpace Ω] [CompactSpace Ω]

/-- The `T`-orbit `orb(ω) = {Tᵏω : k ∈ ℤ}` (Definition 3.6.1), written as the union of the forward
and the backward orbit. -/
def orbit (T : Ω ≃ₜ Ω) (ω : Ω) : Set Ω :=
  range (fun n : ℕ => T^[n] ω) ∪ range (fun n : ℕ => T.symm^[n] ω)

/-- Definition 3.6.1: `T` is *topologically transitive* if some orbit is dense. -/
def TopTransitive (T : Ω ≃ₜ Ω) : Prop := ∃ ω, Dense (orbit T ω)

/-- Definition 3.6.1: `T` is *minimal* if every orbit is dense. -/
def IsMinimalSys (T : Ω ≃ₜ Ω) : Prop := ∀ ω, Dense (orbit T ω)

lemma image_eq_iff_preimage_eq (T : Ω ≃ₜ Ω) (K : Set Ω) : T '' K = K ↔ T ⁻¹' K = K := by
  constructor
  · intro h
    conv_lhs => rw [← h]
    exact T.injective.preimage_image K
  · intro h
    conv_lhs => rw [← h]
    exact T.surjective.image_preimage K

/-- The set of points whose orbit meets `U`, i.e. `⋃_{k ∈ ℤ} Tᵏ U`. -/
def orbitSat (T : Ω ≃ₜ Ω) (U : Set Ω) : Set Ω :=
  ⋃ n : ℕ, (T^[n] ⁻¹' U ∪ T.symm^[n] ⁻¹' U)

lemma isOpen_orbitSat (T : Ω ≃ₜ Ω) {U : Set Ω} (hU : IsOpen U) : IsOpen (orbitSat T U) :=
  isOpen_iUnion fun n => ((T.continuous.iterate n).isOpen_preimage U hU).union
    ((T.symm.continuous.iterate n).isOpen_preimage U hU)

lemma preimage_orbitSat (T : Ω ≃ₜ Ω) (U : Set Ω) : T ⁻¹' orbitSat T U = orbitSat T U := by
  ext x
  simp only [orbitSat, mem_preimage, mem_iUnion, mem_union]
  constructor
  · rintro ⟨n, h | h⟩
    · exact ⟨n + 1, Or.inl (by rwa [iterate_succ_apply])⟩
    · rcases n with _ | m
      · exact ⟨1, Or.inl (by simpa using h)⟩
      · refine ⟨m, Or.inr ?_⟩
        rwa [iterate_succ_apply, Homeomorph.symm_apply_apply] at h
  · rintro ⟨n, h | h⟩
    · rcases n with _ | m
      · refine ⟨1, Or.inr ?_⟩
        simpa using h
      · exact ⟨m, Or.inl (by rwa [iterate_succ_apply] at h)⟩
    · refine ⟨n + 1, Or.inr ?_⟩
      rwa [iterate_succ_apply, Homeomorph.symm_apply_apply]

lemma iterate_symm_iterate' (T : Ω ≃ₜ Ω) (n : ℕ) (x : Ω) : T.symm^[n] (T^[n] x) = x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply, iterate_succ_apply', Homeomorph.symm_apply_apply, ih]

lemma iterate_iterate_symm' (T : Ω ≃ₜ Ω) (n : ℕ) (x : Ω) : T^[n] (T.symm^[n] x) = x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply, iterate_succ_apply', Homeomorph.apply_symm_apply, ih]

lemma orbit_subset_of_invariant (T : Ω ≃ₜ Ω) {K : Set Ω} (hK : T ⁻¹' K = K) {ω : Ω}
    (hω : ω ∈ K) : orbit T ω ⊆ K := by
  have hfw : ∀ n x, x ∈ K → T^[n] x ∈ K := by
    intro n
    induction n with
    | zero => exact fun x hx => hx
    | succ n ih =>
      intro x hx
      rw [iterate_succ_apply']
      have : T^[n] x ∈ T ⁻¹' K := by rw [hK]; exact ih x hx
      exact this
  have hbw : ∀ n x, x ∈ K → T.symm^[n] x ∈ K := by
    intro n
    induction n with
    | zero => exact fun x hx => hx
    | succ n ih =>
      intro x hx
      rw [iterate_succ_apply']
      have h1 := ih x hx
      have h2 : T.symm (T.symm^[n] x) ∈ T ⁻¹' K := by
        rw [mem_preimage, Homeomorph.apply_symm_apply]; exact h1
      rwa [hK] at h2
  rintro _ (⟨n, rfl⟩ | ⟨n, rfl⟩)
  · exact hfw n ω hω
  · exact hbw n ω hω

/-- **Proposition 3.6.2**: for a topological dynamical system the following are equivalent:
(a) `T` is minimal; (b) the only closed `T`-invariant sets are `∅` and `Ω`;
(c) `⋃_{k ∈ ℤ} Tᵏ U = Ω` for every nonempty open `U`. -/
theorem minimal_tfae (T : Ω ≃ₜ Ω) :
    [IsMinimalSys T,
      ∀ K : Set Ω, IsClosed K → T ⁻¹' K = K → K = ∅ ∨ K = univ,
      ∀ U : Set Ω, IsOpen U → U.Nonempty → orbitSat T U = univ].TFAE := by
  tfae_have 1 → 2 := by
    intro hmin K hKc hK
    rcases K.eq_empty_or_nonempty with h | ⟨ω, hω⟩
    · exact Or.inl h
    · right
      have h1 : closure (orbit T ω) ⊆ K := hKc.closure_subset_iff.2 (orbit_subset_of_invariant T hK hω)
      rw [(hmin ω).closure_eq] at h1
      exact eq_univ_of_univ_subset h1
  tfae_have 2 → 3 := by
    intro h U hU ⟨y, hy⟩
    have hc := h (orbitSat T U)ᶜ (isOpen_orbitSat T hU).isClosed_compl
      (by rw [preimage_compl, preimage_orbitSat])
    rcases hc with hc | hc
    · exact compl_empty_iff.1 hc
    · exfalso
      have : y ∈ orbitSat T U := mem_iUnion.2 ⟨0, Or.inl hy⟩
      have h2 : y ∈ (orbitSat T U)ᶜ := by rw [hc]; trivial
      exact h2 this
  tfae_have 3 → 1 := by
    intro h ω
    rw [dense_iff_inter_open]
    intro U hU hne
    have : ω ∈ orbitSat T U := by rw [h U hU hne]; trivial
    obtain ⟨n, hn | hn⟩ := mem_iUnion.1 this
    · exact ⟨_, hn, Or.inl ⟨n, rfl⟩⟩
    · exact ⟨_, hn, Or.inr ⟨n, rfl⟩⟩
  tfae_finish

/-- **Lemma 3.6.3** ((a) ⟺ (c)): `T` is minimal iff every forward orbit is dense. -/
theorem minimal_iff_forward_dense (T : Ω ≃ₜ Ω) :
    IsMinimalSys T ↔ ∀ ω, Dense (range fun n : ℕ => T^[n] ω) := by
  constructor
  · intro hmin ω
    -- the ω-limit set
    set Kn : ℕ → Set Ω := fun N => closure (range fun n : ℕ => T^[n + N] ω)
    set K := ⋂ N, Kn N
    have hKc : IsClosed K := isClosed_iInter fun N => isClosed_closure
    have hmono : ∀ N, Kn (N + 1) ⊆ Kn N := by
      intro N
      apply closure_mono
      rintro _ ⟨n, rfl⟩
      refine ⟨n + 1, ?_⟩
      show T^[n + 1 + N] ω = T^[n + (N + 1)] ω
      rw [show n + 1 + N = n + (N + 1) by ring]
    have hKne : K.Nonempty := by
      apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed Kn hmono
      · intro N; exact ⟨_, subset_closure ⟨0, rfl⟩⟩
      · exact isClosed_closure.isCompact
      · intro N; exact isClosed_closure
    have himage : ∀ N, T '' Kn N = Kn (N + 1) := by
      intro N
      simp only [Kn]
      rw [T.image_closure, ← range_comp]
      congr 2
      funext n
      simp only [comp_apply]
      rw [← iterate_succ_apply' T, show (n + N).succ = n + (N + 1) by omega]
    have hTK : T '' K = K := by
      rw [image_iInter T.bijective]
      apply Subset.antisymm
      · intro x hx
        refine mem_iInter.2 fun N => ?_
        have := mem_iInter.1 hx N
        rw [himage] at this
        exact hmono N this
      · intro x hx
        refine mem_iInter.2 fun N => ?_
        rw [himage]
        exact mem_iInter.1 hx (N + 1)
    have hK : T ⁻¹' K = K := (image_eq_iff_preimage_eq T K).1 hTK
    have hb : ∀ K : Set Ω, IsClosed K → T ⁻¹' K = K → K = ∅ ∨ K = univ :=
      ((minimal_tfae T).out 1 2).1 hmin
    rcases hb K hKc hK with h | h
    · rw [h] at hKne; exact absurd hKne (by simp)
    · have h1 : K ⊆ closure (range fun n : ℕ => T^[n] ω) := by
        intro x hx
        have := mem_iInter.1 hx 0
        simp only [Kn, add_zero] at this
        exact this
      rw [h] at h1
      exact dense_iff_closure_eq.2 (eq_univ_of_univ_subset h1)
  · intro h ω
    exact (h ω).mono subset_union_left

variable [MeasurableSpace Ω] [BorelSpace Ω]

/-- Definition 3.6.1: `T` is *strictly ergodic* if it is minimal and uniquely ergodic. -/
def StrictlyErgodic (T : Ω ≃ₜ Ω) : Prop := IsMinimalSys T ∧ UniquelyErgodic T

/-- **Proposition 3.6.5**: if `T` is uniquely ergodic with `M₁(Ω, T) = {μ}`, then `T` is minimal
iff `μ(U) > 0` for every nonempty open `U`. -/
theorem minimal_iff_fullSupport (T : Ω ≃ₜ Ω) {μ : Measure Ω} (hμ : invMeasures T = {μ}) :
    IsMinimalSys T ↔ ∀ U : Set Ω, IsOpen U → U.Nonempty → 0 < μ U := by
  have hμmem : μ ∈ invMeasures T := by rw [hμ]; rfl
  have := hμmem.2
  have hmp : MeasurePreserving T μ μ := hμmem.1
  constructor
  · intro hmin U hU hne
    by_contra h0
    push Not at h0
    have h0 : μ U = 0 := nonpos_iff_eq_zero.1 h0
    have hc : ∀ U : Set Ω, IsOpen U → U.Nonempty → orbitSat T U = univ :=
      ((minimal_tfae T).out 1 3).1 hmin
    have hsat := hc U hU hne
    have hmpe : MeasurePreserving T.toMeasurableEquiv μ μ := hmp
    have hsymm : MeasurePreserving T.symm μ μ := hmpe.symm
    have : μ (orbitSat T U) = 0 := by
      apply measure_iUnion_null
      intro n
      apply measure_union_null
      · rw [(hmp.iterate n).measure_preimage hU.measurableSet.nullMeasurableSet]; exact h0
      · rw [(hsymm.iterate n).measure_preimage hU.measurableSet.nullMeasurableSet]; exact h0
    rw [hsat, measure_univ] at this
    exact one_ne_zero this
  · intro hpos
    by_contra hmin
    have h2 : ¬ ∀ K : Set Ω, IsClosed K → T ⁻¹' K = K → K = ∅ ∨ K = univ := fun h =>
      hmin (((minimal_tfae T).out 1 2).2 h)
    push Not at h2
    obtain ⟨K, hKc, hK, hne, huniv⟩ := h2
    obtain ⟨ν, hν, -, hνp, hsupp⟩ := exists_measurePreserving_probabilityMeasure_of_compact_forwardInvariant
      hKc.isCompact hne T.continuous.continuousOn
      (fun x hx => by
        have : x ∈ T ⁻¹' K := by rw [hK]; exact hx
        exact this) T.continuous.measurable
    have hνmem : ν ∈ invMeasures T := ⟨hν, hνp⟩
    rw [hμ] at hνmem
    have hνμ : ν = μ := hνmem
    have hKcpos : 0 < μ Kᶜ := hpos _ hKc.isOpen_compl
      (by rw [nonempty_compl]; exact huniv)
    have hνK : ν Kᶜ = 0 := measure_mono_null (compl_subset_compl.2 hsupp) Measure.measure_compl_support
    rw [hνμ] at hνK
    exact hKcpos.ne' hνK

end DF
