/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# Theorem 3.2.17: Bernoulli shifts are ergodic

Main results:
* `DF.measurePreserving_shiftN`, `DF.measurePreserving_shiftZ` — the shifts preserve the product
  measures `ν^ℕ`, `ν^ℤ`;
* `DF.ergodic_shiftZ` — **Theorem 3.2.17(a)**, by the book's argument: approximate an invariant set
  by a cylinder `C` and use independence of `C` and `T^{-N} C` to get `μ(E) = μ(E)²`;
* `DF.ergodic_shiftN` — **Theorem 3.2.17(b)**, via Kolmogorov's zero-one law (a strictly
  invariant set is a tail event);
* `DF.bernoulliShiftErgodic` — proof of `DF.BernoulliShiftErgodicStatement`.
-/
import DamanikFillman.Ch3.Examples

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped symmDiff

namespace DF

variable {A : Type*} [mA : MeasurableSpace A] (ν : Measure A) [IsProbabilityMeasure ν]

lemma measurable_shiftN : Measurable (shiftN (A := A)) :=
  measurable_pi_iff.2 fun n => measurable_pi_apply (n + 1)

lemma iIndepFun_coord :
    iIndepFun (fun (i : ℕ) (ω : ℕ → A) => ω i) (Measure.infinitePi fun _ : ℕ => ν) := by
  have := iIndepFun_infinitePi (P := fun _ : ℕ => ν) (X := fun _ => (id : A → A))
    (fun _ => measurable_id)
  simpa using this

/-- The unilateral shift preserves the product measure. -/
theorem measurePreserving_shiftN :
    MeasurePreserving (shiftN (A := A)) (Measure.infinitePi fun _ : ℕ => ν)
      (Measure.infinitePi fun _ : ℕ => ν) := by
  refine ⟨measurable_shiftN, ?_⟩
  have hind := (iIndepFun_coord ν).precomp (g := fun i : ℕ => i + 1) (add_left_injective 1)
  have h := hind.map_fun_eq_infinitePi_map (fun i => measurable_pi_apply (i + 1))
  have hs : (fun (ω : ℕ → A) (i : ℕ) => ω (i + 1)) = shiftN := rfl
  rw [hs] at h
  rw [h]
  congr 1
  funext i
  exact Measure.infinitePi_map_eval (fun _ : ℕ => ν) (i + 1)

lemma shiftN_iterate_apply (n j : ℕ) (ω : ℕ → A) : (shiftN^[n] ω) j = ω (n + j) := by
  induction n generalizing ω with
  | zero => simp
  | succ n ih => rw [iterate_succ_apply, ih]; simp only [shiftN]; congr 1; ring

/-- **Theorem 3.2.17(b)**: the unilateral shift is ergodic for the product measure `ν^ℕ`. -/
theorem ergodic_shiftN : Ergodic (shiftN (A := A)) (Measure.infinitePi fun _ : ℕ => ν) := by
  refine Ergodic.of_preimage_eq (measurePreserving_shiftN ν) fun s hs hinv => ?_
  set m : ℕ → MeasurableSpace (ℕ → A) := fun n => MeasurableSpace.comap (fun ω => ω n) mA
  have hle : ∀ n, m n ≤ MeasurableSpace.pi := fun n => (measurable_pi_apply n).comap_le
  have hind : iIndep m (Measure.infinitePi fun _ : ℕ => ν) :=
    (iIndepFun_iff_iIndep (fun _ => mA) _ _).1 (iIndepFun_coord ν)
  have htail : MeasurableSet[limsup m atTop] s := by
    rw [limsup_eq_iInf_iSup_of_nat, MeasurableSpace.measurableSet_iInf]
    intro n
    have hit : (shiftN^[n]) ⁻¹' s = s := by
      induction n with
      | zero => rfl
      | succ n ih => rw [iterate_succ', preimage_comp, hinv, ih]
    rw [← hit]
    have hmeas : Measurable[⨆ i ≥ n, m i, MeasurableSpace.pi] (shiftN^[n]) := by
      refine @measurable_pi_lambda (ℕ → A) ℕ (fun _ => A) (⨆ i ≥ n, m i) (fun _ => mA) _
        fun j => ?_
      have e : (fun ω : ℕ → A => (shiftN^[n] ω) j) = fun ω => ω (n + j) := by
        funext ω; exact shiftN_iterate_apply n j ω
      rw [e]
      exact (comap_measurable (fun ω : ℕ → A => ω (n + j))).mono
        (le_iSup₂ (f := fun i (_ : i ≥ n) => m i) (n + j) (by omega)) le_rfl
    exact hmeas hs
  rw [eventuallyEmptyOrUniv_iff]
  rcases measure_zero_or_one_of_measurableSet_limsup_atTop hle hind htail with h0 | h1
  · exact Or.inr (measure_eq_zero_iff_ae_notMem.1 h0)
  · refine Or.inl ?_
    have : (Measure.infinitePi fun _ : ℕ => ν) sᶜ = 0 := by
      rw [prob_compl_eq_zero_iff hs]; exact h1
    exact (measure_eq_zero_iff_ae_notMem.1 this).mono fun x hx => by simpa using hx

/-! ### The bilateral shift (Theorem 3.2.17(a)) -/

lemma measurable_shiftZ : Measurable (shiftZ (A := A)) :=
  measurable_pi_iff.2 fun n => measurable_pi_apply (n + 1)

lemma iIndepFun_coordZ :
    iIndepFun (fun (i : ℤ) (ω : ℤ → A) => ω i) (Measure.infinitePi fun _ : ℤ => ν) := by
  have := iIndepFun_infinitePi (P := fun _ : ℤ => ν) (X := fun _ => (id : A → A))
    (fun _ => measurable_id)
  simpa using this

/-- The bilateral shift preserves the product measure. -/
theorem measurePreserving_shiftZ :
    MeasurePreserving (shiftZ (A := A)) (Measure.infinitePi fun _ : ℤ => ν)
      (Measure.infinitePi fun _ : ℤ => ν) := by
  refine ⟨measurable_shiftZ, ?_⟩
  have hind := (iIndepFun_coordZ ν).precomp (g := fun i : ℤ => i + 1) (add_left_injective 1)
  have h := hind.map_fun_eq_infinitePi_map (fun i => measurable_pi_apply (i + 1))
  have hs : (fun (ω : ℤ → A) (i : ℤ) => ω (i + 1)) = shiftZ := rfl
  rw [hs] at h
  rw [h]
  congr 1
  funext i
  exact Measure.infinitePi_map_eval (fun _ : ℤ => ν) (i + 1)

lemma shiftZ_iterate_apply (n : ℕ) (j : ℤ) (ω : ℤ → A) : (shiftZ^[n] ω) j = ω (j + n) := by
  induction n generalizing ω with
  | zero => simp
  | succ n ih => rw [iterate_succ_apply, ih]; simp only [shiftZ]; congr 1; push_cast; ring

/-- **Theorem 3.2.17(a)**: the bilateral shift is ergodic for the product measure `ν^ℤ`. -/
theorem ergodic_shiftZ : Ergodic (shiftZ (A := A)) (Measure.infinitePi fun _ : ℤ => ν) := by
  classical
  have hmp := measurePreserving_shiftZ ν
  refine Ergodic.of_preimage_eq hmp fun E hE hinv => ?_
  set μ := Measure.infinitePi fun _ : ℤ => ν with hμ
  set m : ℤ → MeasurableSpace (ℤ → A) := fun n => MeasurableSpace.comap (fun ω => ω n) mA
  have hle : ∀ n, m n ≤ MeasurableSpace.pi := fun n => (measurable_pi_apply n).comap_le
  have hind : iIndep m μ := (iIndepFun_iff_iIndep (fun _ => mA) _ _).1 (iIndepFun_coordZ ν)
  have hinvN : ∀ N : ℕ, (shiftZ^[N]) ⁻¹' E = E := by
    intro N
    induction N with
    | zero => rfl
    | succ N ih => rw [iterate_succ', preimage_comp, hinv, ih]
  -- the key estimate `|μ E - μ E ^ 2| ≤ 4 ε`
  have hkey : ∀ ε > (0 : ℝ), |μ.real E - μ.real E ^ 2| ≤ 4 * ε := by
    intro ε hε
    obtain ⟨C, hC, hCE⟩ := exists_measure_symmDiff_lt_of_generateFrom_isSetRing (μ := μ)
      (isSetRing_measurableCylinders (α := fun _ : ℤ => A))
      ⟨{univ}, countable_singleton _, by simpa using univ_mem_measurableCylinders (fun _ : ℤ => A), by simp⟩
      generateFrom_measurableCylinders.symm hE (ε := ENNReal.ofReal ε) (by simpa using hε)
    obtain ⟨I, S, hS, rfl⟩ := (mem_measurableCylinders _).1 hC
    set C := MeasureTheory.cylinder (α := fun _ : ℤ => A) I S
    set M : ℕ := I.sup fun i => i.natAbs
    set N : ℕ := 2 * M + 1
    set D := (shiftZ^[N]) ⁻¹' C
    have hCm : MeasurableSet[cylinderEvents (I : Set ℤ)] C := by
      have : Measurable[cylinderEvents (I : Set ℤ), MeasurableSpace.pi] (I.restrict (π := fun _ => A)) :=
        @measurable_pi_lambda (ℤ → A) I (fun _ => A) (cylinderEvents (I : Set ℤ)) _ _
          fun i => measurable_cylinderEvent_apply (X := fun _ : ℤ => A) i.2
      exact this hS
    set J : Set ℤ := (fun i => i + (N : ℤ)) '' (I : Set ℤ)
    have hDm : MeasurableSet[cylinderEvents J] D := by
      have : Measurable[cylinderEvents J, MeasurableSpace.pi]
          (fun ω : ℤ → A => I.restrict (π := fun _ => A) (shiftZ^[N] ω)) := by
        refine @measurable_pi_lambda (ℤ → A) I (fun _ => A) (cylinderEvents J) _ _ fun i => ?_
        have e : (fun ω : ℤ → A => I.restrict (π := fun _ => A) (shiftZ^[N] ω) i) =
            fun ω => ω (i + N) := by
          funext ω; simp [Finset.restrict, shiftZ_iterate_apply]
        rw [e]
        exact measurable_cylinderEvent_apply (X := fun _ : ℤ => A) ⟨i, i.2, rfl⟩
      exact this hS
    have hdisj : Disjoint (I : Set ℤ) J := by
      rw [Set.disjoint_left]
      rintro i hi ⟨j, hj, rfl⟩
      have h1 : (j + (N : ℤ)).natAbs ≤ M := Finset.le_sup (f := fun i : ℤ => i.natAbs) hi
      have h2 : j.natAbs ≤ M := Finset.le_sup (f := fun i : ℤ => i.natAbs) hj
      omega
    have hindep := indep_iSup_of_disjoint hle hind hdisj
    have hCD : μ (C ∩ D) = μ C * μ D := (Indep_iff _ _ μ).1 hindep C D hCm hDm
    have hCmeas : MeasurableSet C := MeasurableSet.cylinder I hS
    have hDmeas : MeasurableSet D := (measurable_shiftZ.iterate N) hCmeas
    have hDμ : μ D = μ C := (hmp.iterate N).measure_preimage hCmeas.nullMeasurableSet
    have hCDr : μ.real (C ∩ D) = μ.real C * μ.real C := by
      simp only [measureReal_def]; rw [hCD, hDμ, ENNReal.toReal_mul]
    have he : μ.real (C ∆ E) < ε := by
      rw [measureReal_def]
      exact (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).2 hCE
        |>.trans_eq (ENNReal.toReal_ofReal hε.le)
    have hsd : (C ∩ D) ∆ (E ∩ (shiftZ^[N]) ⁻¹' E) ⊆ (C ∆ E) ∪ (shiftZ^[N]) ⁻¹' (C ∆ E) := by
      intro x hx
      simp only [Set.mem_symmDiff, Set.mem_inter_iff, Set.mem_union, Set.mem_preimage, D] at hx ⊢
      tauto
    have he2 : μ.real ((shiftZ^[N]) ⁻¹' (C ∆ E)) = μ.real (C ∆ E) := by
      simp only [measureReal_def]
      rw [(hmp.iterate N).measure_preimage (hCmeas.symmDiff hE).nullMeasurableSet]
    have h1 : |μ.real (C ∩ D) - μ.real (E ∩ (shiftZ^[N]) ⁻¹' E)| ≤ 2 * ε := by
      refine (abs_measureReal_sub_le_measureReal_symmDiff (hCmeas.inter hDmeas).nullMeasurableSet
        (hE.inter ((measurable_shiftZ.iterate N) hE)).nullMeasurableSet).trans ?_
      refine (measureReal_mono hsd).trans ((measureReal_union_le _ _).trans ?_)
      rw [he2]; linarith
    rw [hinvN, inter_self, hCDr] at h1
    have h2 : |μ.real C - μ.real E| ≤ ε :=
      (abs_measureReal_sub_le_measureReal_symmDiff hCmeas.nullMeasurableSet
        hE.nullMeasurableSet).trans he.le
    have hc0 : 0 ≤ μ.real C := measureReal_nonneg
    have hc1 : μ.real C ≤ 1 := measureReal_le_one
    have ha0 : 0 ≤ μ.real E := measureReal_nonneg
    have ha1 : μ.real E ≤ 1 := measureReal_le_one
    have h3 : |μ.real C * μ.real C - μ.real E ^ 2| ≤ 2 * ε := by
      rw [show μ.real C * μ.real C - μ.real E ^ 2 = (μ.real C - μ.real E) * (μ.real C + μ.real E)
        by ring, abs_mul]
      have : |μ.real C + μ.real E| ≤ 2 := by rw [abs_of_nonneg (by linarith)]; linarith
      nlinarith [abs_nonneg (μ.real C - μ.real E), abs_nonneg (μ.real C + μ.real E)]
    calc |μ.real E - μ.real E ^ 2|
        = |(μ.real E - μ.real C * μ.real C) + (μ.real C * μ.real C - μ.real E ^ 2)| := by ring_nf
      _ ≤ |μ.real E - μ.real C * μ.real C| + |μ.real C * μ.real C - μ.real E ^ 2| := abs_add_le _ _
      _ ≤ 2 * ε + 2 * ε := by rw [abs_sub_comm] at h1; exact add_le_add h1 h3
      _ = 4 * ε := by ring
  have hsq : μ.real E = μ.real E ^ 2 := by
    by_contra hne
    have hpos : 0 < |μ.real E - μ.real E ^ 2| := abs_pos.2 (sub_ne_zero.2 hne)
    have := hkey (|μ.real E - μ.real E ^ 2| / 8) (by positivity)
    linarith
  rw [eventuallyEmptyOrUniv_iff]
  have h01 : μ.real E = 0 ∨ μ.real E = 1 := by
    have : μ.real E * (1 - μ.real E) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rcases h01 with h0 | h1
  · refine Or.inr (measure_eq_zero_iff_ae_notMem.1 ?_)
    rwa [measureReal_eq_zero_iff] at h0
  · refine Or.inl ?_
    have hE1 : μ E = 1 := by
      rw [measureReal_def, ENNReal.toReal_eq_one_iff] at h1; exact h1
    have : μ Eᶜ = 0 := (prob_compl_eq_zero_iff hE).2 hE1
    exact (measure_eq_zero_iff_ae_notMem.1 this).mono fun x hx => by simpa using hx

/-- **Theorem 3.2.17**: `DF.BernoulliShiftErgodicStatement` holds. -/
theorem bernoulliShiftErgodic : BernoulliShiftErgodicStatement :=
  fun _ _ ν _ => ⟨ergodic_shiftZ ν, ergodic_shiftN ν⟩

end DF
