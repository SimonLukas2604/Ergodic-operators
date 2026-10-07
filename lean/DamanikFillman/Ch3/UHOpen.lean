/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §3.8.1: robustness of uniform hyperbolicity (Corollary 3.8.5, fixed base dynamics)

Main results:
* `DF.Cocycle.exists_escape` — the compactness step in the proof of Theorem 3.8.2: without
  bounded orbits there are `N` and `ε > 0` such that every unit vector is expanded by a factor
  `1 + ε` by some `A_n(ω)` with `|n| ≤ N`;
* `DF.Cocycle.uniformExpGrowth_open` — **Corollary 3.8.5** for a fixed homeomorphism `T`:
  uniform hyperbolicity of `(T, A)` persists under uniformly small continuous perturbations
  of `A`. (The book also perturbs `T`; that part is not formalized.)
* `DF.Cocycle.one_sided_growth_of_uniformExpGrowth` — for a uniformly hyperbolic cocycle every
  nonzero vector grows exponentially (uniformly) on at least one half-line.
-/
import DamanikFillman.Ch3.UH2

noncomputable section

set_option linter.unusedSectionVars false

open Filter Set Function Topology Matrix
open scoped Matrix.Norms.L2Operator

namespace DF

namespace Cocycle

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- The compactness step of Theorem 3.8.2 ((c) ⇒ (a)). -/
theorem exists_escape (T : X ≃ₜ X) (A : X → SL2R) (hA : Continuous fun ω => (A ω : M2R))
    (h : ¬ BoundedOrbit T A) : ∃ N : ℕ, ∃ ε > (0 : ℝ), ∀ ω (w : EuclideanSpace ℝ (Fin 2)),
      ∃ m : ℤ, |m| ≤ N ∧ (w ≠ 0 →
        (1 + ε) * ‖w‖ ≤ ‖act ((iterZ T.toEquiv A m ω : SL2R) : M2R) w‖) := by
  classical
  set B : ℤ → X → SL2R := fun n ω => iterZ T.toEquiv A n ω with hBdef
  set tp := tpow T.toEquiv
  have hBadd : ∀ (n m : ℤ) ω, B (n + m) ω = B m (tp n ω) * B n ω := fun n m ω => iterZ_add n m ω
  have hB0 : ∀ ω, B 0 ω = 1 := fun ω => rfl
  -- continuity
  have htp : ∀ n, Continuous (tp n) := by
    intro n
    induction n using Int.induction_on with
    | zero => exact continuous_id.congr fun x => (tpow_zero x).symm
    | succ i ih => exact (T.continuous.comp ih).congr fun x => (tpow_add_one (i : ℤ) x).symm
    | pred i ih => exact (T.symm.continuous.comp ih).congr fun x => (tpow_sub_one (-(i : ℤ)) x).symm
  have hAinv : Continuous fun ω => (((A ω)⁻¹ : SL2R) : M2R) := by
    simp_rw [Matrix.SpecialLinearGroup.coe_inv, adjugate_eq_trace]
    exact (hA.matrix_trace.smul continuous_const).sub hA
  have hBc : ∀ n, Continuous fun ω => (B n ω : M2R) := by
    intro n
    induction n using Int.induction_on with
    | zero => exact continuous_const.congr fun ω => by rw [hB0, Matrix.SpecialLinearGroup.coe_one]
    | succ i ih =>
      refine ((hA.comp (htp i)).mul ih).congr fun ω => ?_
      show (A (tp i ω) : M2R) * (B i ω : M2R) = (B (i + 1) ω : M2R)
      rw [show B (i + 1) ω = A (tp i ω) * B i ω from iterZ_succ _ _, Matrix.SpecialLinearGroup.coe_mul]
    | pred i ih =>
      refine ((hAinv.comp (htp (-(i : ℤ) - 1))).mul ih).congr fun ω => ?_
      show (((A (tp (-(i : ℤ) - 1) ω))⁻¹ : SL2R) : M2R) * (B (-(i : ℤ)) ω : M2R) =
        (B (-(i : ℤ) - 1) ω : M2R)
      rw [show B (-(i : ℤ) - 1) ω = (A (tp (-(i : ℤ) - 1) ω))⁻¹ * B (-(i : ℤ)) ω from
        iterZ_pred _ _, Matrix.SpecialLinearGroup.coe_mul]
  -- the bound `Q`
  obtain ⟨Q1, hQ1⟩ := (isCompact_range hA).isBounded.exists_norm_le
  obtain ⟨Q2, hQ2⟩ := (isCompact_range hAinv).isBounded.exists_norm_le
  set Q := max (max Q1 Q2) 1
  have hQ : 1 ≤ Q := le_max_right _ _
  have hQA : ∀ ω, ‖(A ω : M2R)‖ ≤ Q := fun ω =>
    (hQ1 _ ⟨ω, rfl⟩).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hQAi : ∀ ω, ‖(((A ω)⁻¹ : SL2R) : M2R)‖ ≤ Q := fun ω =>
    (hQ2 _ ⟨ω, rfl⟩).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hBn : ∀ n ω, ‖(B n ω : M2R)‖ ≤ Q ^ n.natAbs := by
    intro n
    induction n using Int.induction_on with
    | zero => intro ω; rw [hB0, Matrix.SpecialLinearGroup.coe_one, norm_one]; simp
    | succ i ih =>
      intro ω
      rw [show B (i + 1) ω = A (tp i ω) * B i ω from iterZ_succ _ _, Matrix.SpecialLinearGroup.coe_mul,
        show ((i : ℤ) + 1).natAbs = i + 1 by omega, pow_succ']
      refine (norm_mul_le _ _).trans (mul_le_mul (hQA _) ?_ (norm_nonneg _) (by positivity))
      simpa using ih ω
    | pred i ih =>
      intro ω
      rw [show B (-(i : ℤ) - 1) ω = (A (tp (-(i : ℤ) - 1) ω))⁻¹ * B (-(i : ℤ)) ω from
        iterZ_pred _ _, Matrix.SpecialLinearGroup.coe_mul,
        show (-(i : ℤ) - 1).natAbs = i + 1 by omega, pow_succ']
      refine (norm_mul_le _ _).trans (mul_le_mul (hQAi _) ?_ (norm_nonneg _) (by positivity))
      simpa using ih ω
  have hBinv : ∀ m y, ‖(((B m y)⁻¹ : SL2R) : M2R)‖ ≤ Q ^ m.natAbs := by
    intro m y
    rw [show (B m y)⁻¹ = B (-m) (tp m y) from iterZ_inv m y]
    exact (hBn _ _).trans_eq (by rw [Int.natAbs_neg])
  -- Step 1: compactness
  set K : Set (X × EuclideanSpace ℝ (Fin 2)) := univ ×ˢ Metric.sphere 0 1
  have hK : IsCompact K := isCompact_univ.prod (isCompact_sphere 0 1)
  set U : ℤ × ℕ → Set (X × EuclideanSpace ℝ (Fin 2)) :=
    fun q => {p | 1 + 1 / ((q.2 : ℝ) + 1) < ‖act (B q.1 p.1 : M2R) p.2‖}
  have hUo : ∀ q, IsOpen (U q) := fun q =>
    isOpen_lt continuous_const (continuous_act ((hBc q.1).comp continuous_fst) continuous_snd).norm
  have hcov : K ⊆ ⋃ q, U q := by
    rintro ⟨ω, v⟩ ⟨-, hv⟩
    have hv1 : ‖v‖ = 1 := by simpa using hv
    have : ∃ n : ℤ, 1 < ‖act (B n ω : M2R) v‖ := by
      by_contra hc
      push Not at hc
      exact h ⟨ω, v, hv1, hc⟩
    obtain ⟨n, hn⟩ := this
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt (sub_pos.2 hn)
    exact mem_iUnion.2 ⟨(n, j), by simp only [U, mem_setOf_eq]; linarith⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hUo hcov
  set N : ℕ := t.sup (fun q => q.1.natAbs) + 1
  set J : ℕ := t.sup (fun q => q.2)
  set ε : ℝ := 1 / ((J : ℝ) + 1)
  have hε : 0 < ε := by positivity
  have hN1 : 1 ≤ N := by omega
  have hstep1 : ∀ ω (w : EuclideanSpace ℝ (Fin 2)), ∃ m : ℤ, |m| ≤ N ∧
      (w ≠ 0 → (1 + ε) * ‖w‖ ≤ ‖act (B m ω : M2R) w‖) := by
    intro ω w
    by_cases hw : w = 0
    · exact ⟨0, by simp, fun h => absurd hw h⟩
    have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
    set u := ‖w‖⁻¹ • w
    have hu : (ω, u) ∈ K := ⟨mem_univ _, by simp [u, norm_smul, hwpos.ne']⟩
    obtain ⟨q, hq, hpq⟩ := mem_iUnion₂.1 (ht hu)
    refine ⟨q.1, ?_, fun _ => ?_⟩
    · have h1 : q.1.natAbs ≤ t.sup (fun q : ℤ × ℕ => q.1.natAbs) :=
        Finset.le_sup (f := fun q : ℤ × ℕ => q.1.natAbs) hq
      rw [Int.abs_eq_natAbs]
      have : q.1.natAbs ≤ N := by omega
      exact_mod_cast this
    · have hJ : ε ≤ 1 / ((q.2 : ℝ) + 1) := by
        have h1 : q.2 ≤ J := Finset.le_sup (f := fun q : ℤ × ℕ => q.2) hq
        have h2 : (q.2 : ℝ) ≤ J := by exact_mod_cast h1
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      simp only [U, mem_setOf_eq] at hpq
      rw [act_smul, norm_smul, norm_inv, norm_norm] at hpq
      have h3 : ‖w‖ * (1 + 1 / ((q.2 : ℝ) + 1)) < ‖act (B q.1 ω : M2R) w‖ := by
        rw [lt_inv_mul_iff₀ hwpos] at hpq; exact hpq
      nlinarith
  exact ⟨N, ε, hε, hstep1⟩

lemma norm_adjugate_le_R (M : M2R) : ‖adjugate M‖ ≤ 4 * ‖M‖ := by
  calc ‖adjugate M‖ ≤ ‖cplx (adjugate M)‖ := norm_le_norm_cplx _
    _ = ‖adjugate (cplx M)‖ := by rw [cplx_adjugate]
    _ ≤ 2 * ‖cplx M‖ := norm_adjugate_le _
    _ ≤ 2 * (2 * ‖M‖) := by gcongr; exact norm_cplx_le _
    _ = 4 * ‖M‖ := by ring

lemma adjugate_sub_two (M N : M2R) : adjugate M - adjugate N = adjugate (M - N) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [adjugate_fin_two] <;> ring

/-- **Corollary 3.8.5** (for fixed `T`): if `(T, A)` is uniformly hyperbolic, then so is `(T, A')`
for every continuous `A'` uniformly close to `A`. -/
theorem uniformExpGrowth_open (T : X ≃ₜ X) (A : X → SL2R) (hA : Continuous fun ω => (A ω : M2R))
    (h : UniformExpGrowth T A) : ∃ δ > (0 : ℝ), ∀ A' : X → SL2R,
      Continuous (fun ω => (A' ω : M2R)) → (∀ ω, ‖(A' ω : M2R) - A ω‖ < δ) →
        UniformExpGrowth T A' := by
  classical
  have hnb := not_boundedOrbit_of_uniformExpGrowth T A hA h
  obtain ⟨N, ε, hε, hesc⟩ := exists_escape T A hA hnb
  set B : ℤ → X → SL2R := fun n ω => iterZ T.toEquiv A n ω with hBdef
  set tp := tpow T.toEquiv
  have hB0 : ∀ ω, B 0 ω = 1 := fun ω => rfl
  have hAinv : Continuous fun ω => (((A ω)⁻¹ : SL2R) : M2R) := by
    simp_rw [Matrix.SpecialLinearGroup.coe_inv, adjugate_eq_trace]
    exact (hA.matrix_trace.smul continuous_const).sub hA
  obtain ⟨Q1, hQ1⟩ := (isCompact_range hA).isBounded.exists_norm_le
  obtain ⟨Q2, hQ2⟩ := (isCompact_range hAinv).isBounded.exists_norm_le
  set Q := max (max Q1 Q2) 1
  have hQ : 1 ≤ Q := le_max_right _ _
  have hQA : ∀ ω, ‖(A ω : M2R)‖ ≤ Q := fun ω =>
    (hQ1 _ ⟨ω, rfl⟩).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hQAi : ∀ ω, ‖(((A ω)⁻¹ : SL2R) : M2R)‖ ≤ Q := fun ω =>
    (hQ2 _ ⟨ω, rfl⟩).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hBn : ∀ n ω, ‖(B n ω : M2R)‖ ≤ Q ^ n.natAbs := by
    intro n
    induction n using Int.induction_on with
    | zero => intro ω; rw [hB0, Matrix.SpecialLinearGroup.coe_one, norm_one]; simp
    | succ i ih =>
      intro ω
      rw [show B (i + 1) ω = A (tp i ω) * B i ω from iterZ_succ _ _, Matrix.SpecialLinearGroup.coe_mul,
        show ((i : ℤ) + 1).natAbs = i + 1 by omega, pow_succ']
      refine (norm_mul_le _ _).trans (mul_le_mul (hQA _) ?_ (norm_nonneg _) (by positivity))
      simpa using ih ω
    | pred i ih =>
      intro ω
      rw [show B (-(i : ℤ) - 1) ω = (A (tp (-(i : ℤ) - 1) ω))⁻¹ * B (-(i : ℤ)) ω from
        iterZ_pred _ _, Matrix.SpecialLinearGroup.coe_mul,
        show (-(i : ℤ) - 1).natAbs = i + 1 by omega, pow_succ']
      refine (norm_mul_le _ _).trans (mul_le_mul (hQAi _) ?_ (norm_nonneg _) (by positivity))
      simpa using ih ω
  set K : ℝ := 8 * (N + 1) * (Q + 4) ^ N
  have hK : 0 < K := by positivity
  set δ := min 1 (ε / K)
  have hδ : 0 < δ := lt_min one_pos (div_pos hε hK)
  refine ⟨δ, hδ, fun A' hA' hclose => ?_⟩
  refine uniformExpGrowth_of_not_boundedOrbit T A' hA' ?_
  set B' : ℤ → X → SL2R := fun n ω => iterZ T.toEquiv A' n ω
  have hB'0 : ∀ ω, B' 0 ω = 1 := fun ω => rfl
  have hδ1 : δ ≤ 1 := min_le_left _ _
  -- one-step estimates
  have hA'Q : ∀ ω, ‖(A' ω : M2R)‖ ≤ Q + 4 := fun ω => by
    have h1 := hclose ω
    have h2 := hQA ω
    have h3 : ‖(A' ω : M2R)‖ ≤ ‖(A ω : M2R)‖ + ‖(A' ω : M2R) - A ω‖ := norm_le_norm_add_norm_sub' _ _
    linarith
  have hinvdiff : ∀ ω, ‖(((A' ω)⁻¹ : SL2R) : M2R) - (((A ω)⁻¹ : SL2R) : M2R)‖ ≤ 4 * δ := fun ω => by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.SpecialLinearGroup.coe_inv, adjugate_sub_two]
    exact (norm_adjugate_le_R _).trans (by linarith [hclose ω])
  have hA'iQ : ∀ ω, ‖(((A' ω)⁻¹ : SL2R) : M2R)‖ ≤ Q + 4 := fun ω => by
    have h1 := hinvdiff ω
    have h2 := hQAi ω
    have h3 := norm_le_norm_add_norm_sub' (((A' ω)⁻¹ : SL2R) : M2R) (((A ω)⁻¹ : SL2R) : M2R)
    nlinarith
  -- the perturbation estimate
  have hdiff : ∀ n ω, ‖(B' n ω : M2R)‖ ≤ (Q + 4) ^ n.natAbs ∧
      ‖(B' n ω : M2R) - B n ω‖ ≤ n.natAbs * (Q + 4) ^ n.natAbs * (4 * δ) := by
    intro n
    induction n using Int.induction_on with
    | zero => intro ω; simp [hB0, hB'0]
    | succ i ih =>
      intro ω
      obtain ⟨ih1, ih2⟩ := ih ω
      simp only [Int.natAbs_natCast] at ih1 ih2
      rw [show ((i : ℤ) + 1).natAbs = i + 1 by omega]
      have e1 : (B' ((i : ℤ) + 1) ω : M2R) = A' (tp i ω) * B' i ω := by
        rw [show B' ((i : ℤ) + 1) ω = A' (tp i ω) * B' i ω from iterZ_succ _ _,
          Matrix.SpecialLinearGroup.coe_mul]
      have e2 : (B ((i : ℤ) + 1) ω : M2R) = A (tp i ω) * B i ω := by
        rw [show B ((i : ℤ) + 1) ω = A (tp i ω) * B i ω from iterZ_succ _ _,
          Matrix.SpecialLinearGroup.coe_mul]
      have hQ4 : 1 ≤ Q + 4 := by linarith
      constructor
      · rw [e1, pow_succ']
        exact (norm_mul_le _ _).trans (mul_le_mul (hA'Q _) ih1 (norm_nonneg _) (by positivity))
      · rw [e1, e2]
        have : (A' (tp i ω) : M2R) * B' i ω - A (tp i ω) * B i ω =
            ((A' (tp i ω) : M2R) - A (tp i ω)) * B' i ω + (A (tp i ω) : M2R) * (B' i ω - B i ω) := by
          noncomm_ring
        rw [this]
        refine (norm_add_le _ _).trans ?_
        have f1 := (norm_mul_le ((A' (tp i ω) : M2R) - A (tp i ω)) (B' i ω : M2R)).trans
          (mul_le_mul (hclose (tp i ω)).le ih1 (norm_nonneg _) hδ.le)
        have f2 := (norm_mul_le (A (tp i ω) : M2R) ((B' i ω : M2R) - B i ω)).trans
          (mul_le_mul (hQA (tp i ω)) ih2 (norm_nonneg _) (by linarith))
        have hp : (Q + 4) ^ i ≤ (Q + 4) ^ (i + 1) := pow_le_pow_right₀ hQ4 (by omega)
        have hp0 : 0 ≤ (Q + 4) ^ i := by positivity
        push_cast
        rw [pow_succ]
        have P0 : 0 ≤ δ * (Q + 4) ^ i := by positivity
        have hQ0 : 0 ≤ Q := by linarith
        nlinarith [mul_nonneg P0 (Nat.cast_nonneg (α := ℝ) i), mul_nonneg P0 hQ0]
    | pred i ih =>
      intro ω
      obtain ⟨ih1, ih2⟩ := ih ω
      simp only [Int.natAbs_neg, Int.natAbs_natCast] at ih1 ih2
      rw [show (-(i : ℤ) - 1).natAbs = i + 1 by omega]
      have e1 : (B' (-(i : ℤ) - 1) ω : M2R) = (((A' (tp (-(i : ℤ) - 1) ω))⁻¹ : SL2R) : M2R) *
          B' (-(i : ℤ)) ω := by
        rw [show B' (-(i : ℤ) - 1) ω = (A' (tp (-(i : ℤ) - 1) ω))⁻¹ * B' (-(i : ℤ)) ω from
          iterZ_pred _ _, Matrix.SpecialLinearGroup.coe_mul]
      have e2 : (B (-(i : ℤ) - 1) ω : M2R) = (((A (tp (-(i : ℤ) - 1) ω))⁻¹ : SL2R) : M2R) *
          B (-(i : ℤ)) ω := by
        rw [show B (-(i : ℤ) - 1) ω = (A (tp (-(i : ℤ) - 1) ω))⁻¹ * B (-(i : ℤ)) ω from
          iterZ_pred _ _, Matrix.SpecialLinearGroup.coe_mul]
      have hQ4 : 1 ≤ Q + 4 := by linarith
      constructor
      · rw [e1, pow_succ']
        exact (norm_mul_le _ _).trans (mul_le_mul (hA'iQ _) ih1 (norm_nonneg _) (by positivity))
      · rw [e1, e2]
        set y := tp (-(i : ℤ) - 1) ω
        have : (((A' y)⁻¹ : SL2R) : M2R) * B' (-(i : ℤ)) ω - (((A y)⁻¹ : SL2R) : M2R) * B (-(i : ℤ)) ω =
            ((((A' y)⁻¹ : SL2R) : M2R) - (((A y)⁻¹ : SL2R) : M2R)) * B' (-(i : ℤ)) ω +
              (((A y)⁻¹ : SL2R) : M2R) * (B' (-(i : ℤ)) ω - B (-(i : ℤ)) ω) := by
          noncomm_ring
        rw [this]
        refine (norm_add_le _ _).trans ?_
        have f1 := (norm_mul_le ((((A' y)⁻¹ : SL2R) : M2R) - (((A y)⁻¹ : SL2R) : M2R))
          (B' (-(i : ℤ)) ω : M2R)).trans (mul_le_mul (hinvdiff y) ih1 (norm_nonneg _) (by positivity))
        have f2 := (norm_mul_le (((A y)⁻¹ : SL2R) : M2R) ((B' (-(i : ℤ)) ω : M2R) - B (-(i : ℤ)) ω)).trans
          (mul_le_mul (hQAi y) ih2 (norm_nonneg _) (by linarith))
        have hp : (Q + 4) ^ i ≤ (Q + 4) ^ (i + 1) := pow_le_pow_right₀ hQ4 (by omega)
        have hp0 : 0 ≤ (Q + 4) ^ i := by positivity
        push_cast
        rw [pow_succ]
        have P0 : 0 ≤ δ * (Q + 4) ^ i := by positivity
        have hQ0 : 0 ≤ Q := by linarith
        nlinarith [mul_nonneg P0 (Nat.cast_nonneg (α := ℝ) i), mul_nonneg P0 hQ0]
  -- no bounded orbit for the perturbed cocycle
  rintro ⟨ω, v, hv1, hb⟩
  have hv0 : v ≠ 0 := by intro h0; rw [h0, norm_zero] at hv1; norm_num at hv1
  obtain ⟨m, hm, hesc'⟩ := hesc ω v
  have h1 : (1 + ε) * ‖v‖ ≤ ‖act ((B m ω : SL2R) : M2R) v‖ := hesc' hv0
  rw [hv1, mul_one] at h1
  have hmN : m.natAbs ≤ N := by
    have := hm; rw [Int.abs_eq_natAbs] at this; exact_mod_cast this
  have h2 := (hdiff m ω).2
  have h3 : (m.natAbs : ℝ) * (Q + 4) ^ m.natAbs * (4 * δ) ≤ ε / 2 := by
    have hQ4 : 1 ≤ Q + 4 := by linarith
    have e1 : (m.natAbs : ℝ) * (Q + 4) ^ m.natAbs ≤ (N + 1) * (Q + 4) ^ N := by
      apply mul_le_mul (by exact_mod_cast (hmN.trans (Nat.le_succ N))) (pow_le_pow_right₀ hQ4 hmN)
        (by positivity) (by positivity)
    have e2 : δ ≤ ε / K := min_le_right _ _
    have e3 : K * δ ≤ ε := by rw [le_div_iff₀ hK] at e2; linarith
    have e4 : (m.natAbs : ℝ) * (Q + 4) ^ m.natAbs * (4 * δ) ≤ K * δ / 2 := by
      simp only [K]; nlinarith
    linarith
  have h4 : ‖act ((B' m ω : SL2R) : M2R) v‖ ≥ ‖act ((B m ω : SL2R) : M2R) v‖ - ε / 2 := by
    have : act ((B m ω : SL2R) : M2R) v =
        act ((B' m ω : SL2R) : M2R) v - act ((B' m ω : M2R) - B m ω) v := by
      simp [act, map_sub]
    have e := norm_act_le ((B' m ω : M2R) - B m ω) v
    rw [hv1, mul_one] at e
    rw [this] at *
    have := norm_sub_le (act ((B' m ω : SL2R) : M2R) v) (act ((B' m ω : M2R) - B m ω) v)
    linarith
  have h5 := hb m
  linarith

/-- From the proof of Theorem 3.8.2 ((c) ⇒ (a)): without bounded orbits, every unit vector grows
exponentially, with uniform constants, in forward or in backward time. -/
theorem one_sided_growth_of_not_boundedOrbit (T : X ≃ₜ X) (A : X → SL2R)
    (hA : Continuous fun ω => (A ω : M2R)) (h : ¬ BoundedOrbit T A) :
    ∃ C0 > (0 : ℝ), ∃ l > (1 : ℝ), ∃ M0 : ℕ, ∀ ω (v : EuclideanSpace ℝ (Fin 2)), ‖v‖ = 1 →
      (∀ m : ℕ, M0 ≤ m → l ^ m * C0 ≤ ‖act ((iterZ T.toEquiv A m ω : SL2R) : M2R) v‖) ∨
      (∀ m : ℕ, M0 ≤ m → l ^ m * C0 ≤ ‖act ((iterZ T.toEquiv A (-(m : ℤ)) ω : SL2R) : M2R) v‖) := by
  classical
  set B : ℤ → X → SL2R := fun n ω => iterZ T.toEquiv A n ω with hBdef
  set tp := tpow T.toEquiv
  have hBadd : ∀ (n m : ℤ) ω, B (n + m) ω = B m (tp n ω) * B n ω := fun n m ω => iterZ_add n m ω
  have hB0 : ∀ ω, B 0 ω = 1 := fun ω => rfl
  -- continuity
  have htp : ∀ n, Continuous (tp n) := by
    intro n
    induction n using Int.induction_on with
    | zero => exact continuous_id.congr fun x => (tpow_zero x).symm
    | succ i ih => exact (T.continuous.comp ih).congr fun x => (tpow_add_one (i : ℤ) x).symm
    | pred i ih => exact (T.symm.continuous.comp ih).congr fun x => (tpow_sub_one (-(i : ℤ)) x).symm
  have hAinv : Continuous fun ω => (((A ω)⁻¹ : SL2R) : M2R) := by
    simp_rw [Matrix.SpecialLinearGroup.coe_inv, adjugate_eq_trace]
    exact (hA.matrix_trace.smul continuous_const).sub hA
  have hBc : ∀ n, Continuous fun ω => (B n ω : M2R) := by
    intro n
    induction n using Int.induction_on with
    | zero => exact continuous_const.congr fun ω => by rw [hB0, Matrix.SpecialLinearGroup.coe_one]
    | succ i ih =>
      refine ((hA.comp (htp i)).mul ih).congr fun ω => ?_
      show (A (tp i ω) : M2R) * (B i ω : M2R) = (B (i + 1) ω : M2R)
      rw [show B (i + 1) ω = A (tp i ω) * B i ω from iterZ_succ _ _, Matrix.SpecialLinearGroup.coe_mul]
    | pred i ih =>
      refine ((hAinv.comp (htp (-(i : ℤ) - 1))).mul ih).congr fun ω => ?_
      show (((A (tp (-(i : ℤ) - 1) ω))⁻¹ : SL2R) : M2R) * (B (-(i : ℤ)) ω : M2R) =
        (B (-(i : ℤ) - 1) ω : M2R)
      rw [show B (-(i : ℤ) - 1) ω = (A (tp (-(i : ℤ) - 1) ω))⁻¹ * B (-(i : ℤ)) ω from
        iterZ_pred _ _, Matrix.SpecialLinearGroup.coe_mul]
  -- the bound `Q`
  obtain ⟨Q1, hQ1⟩ := (isCompact_range hA).isBounded.exists_norm_le
  obtain ⟨Q2, hQ2⟩ := (isCompact_range hAinv).isBounded.exists_norm_le
  set Q := max (max Q1 Q2) 1
  have hQ : 1 ≤ Q := le_max_right _ _
  have hQA : ∀ ω, ‖(A ω : M2R)‖ ≤ Q := fun ω =>
    (hQ1 _ ⟨ω, rfl⟩).trans ((le_max_left _ _).trans (le_max_left _ _))
  have hQAi : ∀ ω, ‖(((A ω)⁻¹ : SL2R) : M2R)‖ ≤ Q := fun ω =>
    (hQ2 _ ⟨ω, rfl⟩).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hBn : ∀ n ω, ‖(B n ω : M2R)‖ ≤ Q ^ n.natAbs := by
    intro n
    induction n using Int.induction_on with
    | zero => intro ω; rw [hB0, Matrix.SpecialLinearGroup.coe_one, norm_one]; simp
    | succ i ih =>
      intro ω
      rw [show B (i + 1) ω = A (tp i ω) * B i ω from iterZ_succ _ _, Matrix.SpecialLinearGroup.coe_mul,
        show ((i : ℤ) + 1).natAbs = i + 1 by omega, pow_succ']
      refine (norm_mul_le _ _).trans (mul_le_mul (hQA _) ?_ (norm_nonneg _) (by positivity))
      simpa using ih ω
    | pred i ih =>
      intro ω
      rw [show B (-(i : ℤ) - 1) ω = (A (tp (-(i : ℤ) - 1) ω))⁻¹ * B (-(i : ℤ)) ω from
        iterZ_pred _ _, Matrix.SpecialLinearGroup.coe_mul,
        show (-(i : ℤ) - 1).natAbs = i + 1 by omega, pow_succ']
      refine (norm_mul_le _ _).trans (mul_le_mul (hQAi _) ?_ (norm_nonneg _) (by positivity))
      simpa using ih ω
  have hBinv : ∀ m y, ‖(((B m y)⁻¹ : SL2R) : M2R)‖ ≤ Q ^ m.natAbs := by
    intro m y
    rw [show (B m y)⁻¹ = B (-m) (tp m y) from iterZ_inv m y]
    exact (hBn _ _).trans_eq (by rw [Int.natAbs_neg])
  -- Step 1: compactness
  set K : Set (X × EuclideanSpace ℝ (Fin 2)) := univ ×ˢ Metric.sphere 0 1
  have hK : IsCompact K := isCompact_univ.prod (isCompact_sphere 0 1)
  set U : ℤ × ℕ → Set (X × EuclideanSpace ℝ (Fin 2)) :=
    fun q => {p | 1 + 1 / ((q.2 : ℝ) + 1) < ‖act (B q.1 p.1 : M2R) p.2‖}
  have hUo : ∀ q, IsOpen (U q) := fun q =>
    isOpen_lt continuous_const (continuous_act ((hBc q.1).comp continuous_fst) continuous_snd).norm
  have hcov : K ⊆ ⋃ q, U q := by
    rintro ⟨ω, v⟩ ⟨-, hv⟩
    have hv1 : ‖v‖ = 1 := by simpa using hv
    have : ∃ n : ℤ, 1 < ‖act (B n ω : M2R) v‖ := by
      by_contra hc
      push Not at hc
      exact h ⟨ω, v, hv1, hc⟩
    obtain ⟨n, hn⟩ := this
    obtain ⟨j, hj⟩ := exists_nat_one_div_lt (sub_pos.2 hn)
    exact mem_iUnion.2 ⟨(n, j), by simp only [U, mem_setOf_eq]; linarith⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hUo hcov
  set N : ℕ := t.sup (fun q => q.1.natAbs) + 1
  set J : ℕ := t.sup (fun q => q.2)
  set ε : ℝ := 1 / ((J : ℝ) + 1)
  have hε : 0 < ε := by positivity
  have hN1 : 1 ≤ N := by omega
  have hstep1 : ∀ ω (w : EuclideanSpace ℝ (Fin 2)), ∃ m : ℤ, |m| ≤ N ∧
      (w ≠ 0 → (1 + ε) * ‖w‖ ≤ ‖act (B m ω : M2R) w‖) := by
    intro ω w
    by_cases hw : w = 0
    · exact ⟨0, by simp, fun h => absurd hw h⟩
    have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw
    set u := ‖w‖⁻¹ • w
    have hu : (ω, u) ∈ K := ⟨mem_univ _, by simp [u, norm_smul, hwpos.ne']⟩
    obtain ⟨q, hq, hpq⟩ := mem_iUnion₂.1 (ht hu)
    refine ⟨q.1, ?_, fun _ => ?_⟩
    · have h1 : q.1.natAbs ≤ t.sup (fun q : ℤ × ℕ => q.1.natAbs) :=
        Finset.le_sup (f := fun q : ℤ × ℕ => q.1.natAbs) hq
      rw [Int.abs_eq_natAbs]
      have : q.1.natAbs ≤ N := by omega
      exact_mod_cast this
    · have hJ : ε ≤ 1 / ((q.2 : ℝ) + 1) := by
        have h1 : q.2 ≤ J := Finset.le_sup (f := fun q : ℤ × ℕ => q.2) hq
        have h2 : (q.2 : ℝ) ≤ J := by exact_mod_cast h1
        exact one_div_le_one_div_of_le (by positivity) (by linarith)
      simp only [U, mem_setOf_eq] at hpq
      rw [act_smul, norm_smul, norm_inv, norm_norm] at hpq
      have h3 : ‖w‖ * (1 + 1 / ((q.2 : ℝ) + 1)) < ‖act (B q.1 ω : M2R) w‖ := by
        rw [lt_inv_mul_iff₀ hwpos] at hpq; exact hpq
      nlinarith
  choose mstep hmstep using hstep1
  -- Claim 1: the sequences
  set seq : X → EuclideanSpace ℝ (Fin 2) → ℕ → ℤ := fun ω v k =>
    Nat.rec (motive := fun _ => ℤ) 0 (fun _ sk => sk + mstep (tp sk ω) (act (B sk ω : M2R) v)) k
  have hseq0 : ∀ ω v, seq ω v 0 = 0 := fun _ _ => rfl
  have hseqs : ∀ ω v k, seq ω v (k + 1) =
      seq ω v k + mstep (tp (seq ω v k) ω) (act (B (seq ω v k) ω : M2R) v) := fun _ _ _ => rfl
  have hseq_step : ∀ ω v k, |seq ω v (k + 1) - seq ω v k| ≤ N := by
    intro ω v k
    rw [hseqs, add_sub_cancel_left]
    exact (hmstep _ _).1
  have hseq_grow : ∀ ω v, v ≠ 0 → ∀ k,
      (1 + ε) ^ k * ‖v‖ ≤ ‖act (B (seq ω v k) ω : M2R) v‖ := by
    intro ω v hv k
    induction k with
    | zero => rw [hseq0, hB0, Matrix.SpecialLinearGroup.coe_one, act_one]; simp
    | succ k ih =>
      set sk := seq ω v k
      set w := act (B sk ω : M2R) v
      have hw : w ≠ 0 := by
        intro h0
        rw [h0, norm_zero] at ih
        have : 0 < (1 + ε) ^ k * ‖v‖ := by have := norm_pos_iff.2 hv; positivity
        linarith
      rw [hseqs, hBadd, Matrix.SpecialLinearGroup.coe_mul, act_mul]
      have := (hmstep (tp sk ω) w).2 hw
      calc (1 + ε) ^ (k + 1) * ‖v‖ = (1 + ε) * ((1 + ε) ^ k * ‖v‖) := by ring
        _ ≤ (1 + ε) * ‖w‖ := by gcongr
        _ ≤ _ := this
  have hP : ∀ ω v (p d : ℤ), ‖act (B p ω : M2R) v‖ * (Q ^ d.natAbs)⁻¹ ≤
      ‖act (B (p + d) ω : M2R) v‖ := by
    intro ω v p d
    rw [hBadd, Matrix.SpecialLinearGroup.coe_mul, act_mul]
    have h1 := norm_le_inv_mul_act (B d (tp p ω)) (act (B p ω : M2R) v)
    have h2 := hBinv d (tp p ω)
    have hQpos : 0 < Q ^ d.natAbs := by positivity
    rw [mul_inv_le_iff₀ hQpos]
    calc ‖act (B p ω : M2R) v‖
        ≤ ‖(((B d (tp p ω))⁻¹ : SL2R) : M2R)‖ * ‖act (B d (tp p ω) : M2R) (act (B p ω : M2R) v)‖ :=
          h1
      _ ≤ Q ^ d.natAbs * ‖act (B d (tp p ω) : M2R) (act (B p ω : M2R) v)‖ :=
          mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ = _ := mul_comm _ _
  have hup : ∀ ω v (n : ℤ), ‖act (B n ω : M2R) v‖ ≤ Q ^ n.natAbs * ‖v‖ := fun ω v n =>
    (norm_act_le _ _).trans (mul_le_mul_of_nonneg_right (hBn n ω) (norm_nonneg _))
  -- uniform sign change time
  obtain ⟨K0', hK0'⟩ := pow_unbounded_of_one_lt (Q ^ N) (by linarith : 1 < 1 + ε)
  set K0 := K0' + 1
  have hK0 : Q ^ N < (1 + ε) ^ K0 :=
    hK0'.trans_le (pow_le_pow_right₀ (by linarith) (by omega))
  have hsign : ∀ ω (v : EuclideanSpace ℝ (Fin 2)), ‖v‖ = 1 →
      (∀ k, K0 ≤ k → 0 < seq ω v k) ∨ (∀ k, K0 ≤ k → seq ω v k < 0) := by
    intro ω v hv
    have hv0 : v ≠ 0 := by intro h; rw [h, norm_zero] at hv; norm_num at hv
    have hbig : ∀ k, K0 ≤ k → (N : ℤ) < |seq ω v k| := by
      intro k hk
      by_contra hc
      push Not at hc
      have h1 := hseq_grow ω v hv0 k
      have h2 := hup ω v (seq ω v k)
      rw [hv, mul_one] at h1 h2
      rw [Int.abs_eq_natAbs] at hc
      have h3 : Q ^ (seq ω v k).natAbs ≤ Q ^ N := pow_le_pow_right₀ hQ (by exact_mod_cast hc)
      have h4 : (1 + ε) ^ K0 ≤ (1 + ε) ^ k := pow_le_pow_right₀ (by linarith) hk
      linarith
    by_cases hp : 0 < seq ω v K0
    · left
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => exact hp
      | succ k hk ih =>
        have hk' : (N : ℤ) < seq ω v k := by
          have := hbig k hk; rwa [abs_of_pos ih] at this
        have h2 := (abs_le.1 (hseq_step ω v k)).1
        linarith
    · right
      have hneg : seq ω v K0 < 0 := by
        have := hbig K0 le_rfl
        rcases lt_abs.1 this with h1 | h1
        · exfalso; exact hp (by linarith)
        · linarith
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => exact hneg
      | succ k hk ih =>
        have hk' : seq ω v k < -(N : ℤ) := by
          have := hbig k hk; rw [abs_of_neg ih] at this; linarith
        have h2 := (abs_le.1 (hseq_step ω v k)).2
        linarith
  -- the growth rate `λ`
  set l : ℝ := (1 + ε) ^ ((1 : ℝ) / N)
  have hl1 : 1 ≤ l := Real.one_le_rpow (by linarith) (by positivity)
  have hlN : l ^ N = 1 + ε := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), one_div_mul_cancel (by positivity),
      Real.rpow_one]
  have hlgt : 1 < l := by
    rcases eq_or_lt_of_le hl1 with h1 | h1
    · rw [← h1, one_pow] at hlN; linarith
    · exact h1
  set C0 := ((1 + ε) * Q ^ N)⁻¹
  have hC0 : 0 < C0 := by positivity
  have hC01 : C0 ≤ 1 := by
    apply inv_le_one_of_one_le₀
    have : 1 ≤ Q ^ N := one_le_pow₀ hQ
    nlinarith
  -- forward and backward estimates for unit vectors
  have hfwd : ∀ ω (v : EuclideanSpace ℝ (Fin 2)), ‖v‖ = 1 → (∀ k, K0 ≤ k → 0 < seq ω v k) →
      ∀ m : ℕ, K0 * N ≤ m → l ^ m * C0 ≤ ‖act (B m ω : M2R) v‖ := by
    intro ω v hv hpos m hm
    have hv0 : v ≠ 0 := by intro h; rw [h, norm_zero] at hv; norm_num at hv
    have ha0 : ‖act (B 0 ω : M2R) v‖ = 1 := by
      rw [hB0, Matrix.SpecialLinearGroup.coe_one, act_one, hv]
    have hg : ∀ k, (1 + ε) ^ k * ‖act (B 0 ω : M2R) v‖ ≤ ‖act (B (seq ω v k) ω : M2R) v‖ := by
      intro k; rw [ha0]; simpa [hv] using hseq_grow ω v hv0 k
    have hp1 : ∀ (p : ℤ) (j : ℕ), j ≤ N →
        ‖act (B p ω : M2R) v‖ * (Q ^ N)⁻¹ ≤ ‖act (B (p + j) ω : M2R) v‖ := by
      intro p j hj
      have h1 := hP ω v p j
      rw [Int.natAbs_natCast] at h1
      refine le_trans ?_ h1
      gcongr
    have hu : ∀ n : ℤ, ‖act (B n ω : M2R) v‖ ≤ Q ^ n.natAbs * ‖act (B 0 ω : M2R) v‖ := by
      intro n; rw [ha0, mul_one]; simpa [hv] using hup ω v n
    have := interp (fun n => ‖act (B n ω : M2R) v‖) hQ hε hl1 hlN (seq ω v) K0 (hseq0 ω v)
      (hseq_step ω v) hg hp1 hu hpos (by rw [ha0]; norm_num) m hm
    beta_reduce at this
    rw [ha0, mul_one] at this
    exact this
  have hbwd : ∀ ω (v : EuclideanSpace ℝ (Fin 2)), ‖v‖ = 1 → (∀ k, K0 ≤ k → seq ω v k < 0) →
      ∀ m : ℕ, K0 * N ≤ m → l ^ m * C0 ≤ ‖act (B (-(m : ℤ)) ω : M2R) v‖ := by
    intro ω v hv hneg m hm
    have hv0 : v ≠ 0 := by intro h; rw [h, norm_zero] at hv; norm_num at hv
    have ha0 : ‖act (B (-0) ω : M2R) v‖ = 1 := by
      rw [neg_zero, hB0, Matrix.SpecialLinearGroup.coe_one, act_one, hv]
    have hst : ∀ k, |(-seq ω v (k + 1)) - (-seq ω v k)| ≤ N := by
      intro k
      rw [show -seq ω v (k + 1) - -seq ω v k = -(seq ω v (k + 1) - seq ω v k) by ring, abs_neg]
      exact hseq_step ω v k
    have hg : ∀ k, (1 + ε) ^ k * ‖act (B (-0) ω : M2R) v‖ ≤
        ‖act (B (-(-seq ω v k)) ω : M2R) v‖ := by
      intro k; rw [ha0, neg_neg]; simpa [hv] using hseq_grow ω v hv0 k
    have hp1 : ∀ (p : ℤ) (j : ℕ), j ≤ N →
        ‖act (B (-p) ω : M2R) v‖ * (Q ^ N)⁻¹ ≤ ‖act (B (-(p + j)) ω : M2R) v‖ := by
      intro p j hj
      have h1 := hP ω v (-p) (-(j : ℤ))
      rw [Int.natAbs_neg, Int.natAbs_natCast] at h1
      rw [show -(p + (j : ℤ)) = -p + -(j : ℤ) by ring]
      refine le_trans ?_ h1
      gcongr
    have hu : ∀ n : ℤ, ‖act (B (-n) ω : M2R) v‖ ≤ Q ^ n.natAbs * ‖act (B (-0) ω : M2R) v‖ := by
      intro n; rw [ha0, mul_one]
      have := hup ω v (-n)
      rw [Int.natAbs_neg, hv, mul_one] at this
      exact this
    have := interp (fun n => ‖act (B (-n) ω : M2R) v‖) hQ hε hl1 hlN (fun k => -seq ω v k) K0
      (by simp [hseq0]) hst hg hp1 hu (fun k hk => by linarith [hneg k hk])
      (by rw [ha0]; norm_num) m hm
    beta_reduce at this
    rw [ha0, mul_one] at this
    exact this
  refine ⟨C0, hC0, l, hlgt, K0 * N, fun ω v hv => ?_⟩
  rcases hsign ω v hv with hpos | hneg
  · exact Or.inl fun m hm => hfwd ω v hv hpos m hm
  · exact Or.inr fun m hm => hbwd ω v hv hneg m hm

/-- A uniformly hyperbolic cocycle expands every nonzero vector exponentially in forward or in
backward time, with uniform constants (used in the proof of Johnson's theorem, Theorem 4.9.3). -/
theorem one_sided_growth_of_uniformExpGrowth (T : X ≃ₜ X) (A : X → SL2R)
    (hA : Continuous fun ω => (A ω : M2R)) (h : UniformExpGrowth T A) :
    ∃ C0 > (0 : ℝ), ∃ l > (1 : ℝ), ∃ M0 : ℕ, ∀ ω (v : EuclideanSpace ℝ (Fin 2)),
      (∀ m : ℕ, M0 ≤ m → l ^ m * C0 * ‖v‖ ≤ ‖act ((iterZ T.toEquiv A m ω : SL2R) : M2R) v‖) ∨
      (∀ m : ℕ, M0 ≤ m →
        l ^ m * C0 * ‖v‖ ≤ ‖act ((iterZ T.toEquiv A (-(m : ℤ)) ω : SL2R) : M2R) v‖) := by
  obtain ⟨C0, hC0, l, hl, M0, hg⟩ :=
    one_sided_growth_of_not_boundedOrbit T A hA (not_boundedOrbit_of_uniformExpGrowth T A hA h)
  refine ⟨C0, hC0, l, hl, M0, fun ω v => ?_⟩
  by_cases hv : v = 0
  · left; intro m _; simp [hv, act]
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hu : ‖‖v‖⁻¹ • v‖ = 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvpos.ne']
  rcases hg ω (‖v‖⁻¹ • v) hu with h1 | h1
  · left; intro m hm
    have := h1 m hm
    rw [act_smul, norm_smul, norm_inv, norm_norm, le_inv_mul_iff₀ hvpos] at this
    linarith [mul_comm (l ^ m * C0) ‖v‖]
  · right; intro m hm
    have := h1 m hm
    rw [act_smul, norm_smul, norm_inv, norm_norm, le_inv_mul_iff₀ hvpos] at this
    linarith [mul_comm (l ^ m * C0) ‖v‖]

end Cocycle

end DF
