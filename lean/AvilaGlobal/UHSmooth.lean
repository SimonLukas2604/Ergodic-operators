import AvilaGlobal.DerivFormula
import AvilaGlobal.UHAnalytic

/-!
# `C^∞` dependence of the Lyapunov exponent on `𝒰ℋ`, jointly in frequency and parameters

`uhSmooth_proof` proves the field `Hypotheses.uhSmooth` (Avila, *Global theory I*, §1.2).

Strategy.  Near a uniformly hyperbolic `(α₀, A_{p₀})` we fix an adapted frame `F` and an entire
`1`-periodic approximation `Ft` of it.  The approximants
`v_n(q, x) = A_p(x-α) ⋯ A_p(x-nα) Ft(x-nα) e₁` converge projectively (cone contraction), and the
multipliers `R_n = cr(A_p(x) v_n, Ft(x+α)e₂) / cr(v_n, Ft(x)e₂)` give
`L(α, A_p) = ∫₀¹ (log |R_{n₀}| + Σ_k Re log (R_{n₀+k+1}/R_{n₀+k})) dx`.
Each term extends holomorphically along every real line of `(α, p, x)`-space to a complex disc of
radius `≍ 1/n` with bound `≍ θⁿ` (the shift `x - jα` only uses the analyticity of `A` in a
strip; the `p`-dependence is complexified along lines through the power series of `A`), so by
Cauchy estimates and polarization all derivatives of the terms are summable.
-/

noncomputable section

open scoped Matrix.Norms.Operator Topology ContDiff Interval
open Matrix Set Filter Metric

namespace AvilaGlobal

open AMO UHOpenAux

namespace UHSmoothAux

/-! ### Generic analysis -/

section Tsum

variable {Q G : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- A local version of `contDiff_tsum`. -/
theorem contDiffOn_tsum_of_bounds {s : Set Q} (hs : IsOpen s) (hs' : IsPreconnected s)
    (f : ℕ → Q → G) (hf : ∀ n, ContDiffOn ℝ ∞ (f n) s) (v : ℕ → ℕ → ℝ)
    (hv : ∀ k, Summable (v k)) (hfv : ∀ k n, ∀ q ∈ s, ‖iteratedFDeriv ℝ k (f n) q‖ ≤ v k n) :
    ContDiffOn ℝ ∞ (fun q => ∑' n, f n q) s := by
  rw [contDiffOn_infty]
  intro N
  induction N generalizing G v with
  | zero =>
    rw [Nat.cast_zero, contDiffOn_zero]
    refine continuousOn_tsum (fun n => (hf n).continuousOn) (hv 0) (fun n q hq => ?_)
    simpa [norm_iteratedFDeriv_zero] using hfv 0 n q hq
  | succ N ih =>
    rcases s.eq_empty_or_nonempty with h0 | ⟨q₀, hq₀⟩
    · simp [h0]
    have hderiv : ∀ q ∈ s, HasFDerivAt (fun q => ∑' n, f n q) (∑' n, fderiv ℝ (f n) q) q := by
      intro q hq
      refine hasFDerivAt_tsum_of_isPreconnected (hv 1) hs hs'
        (f' := fun n q => fderiv ℝ (f n) q)
        (fun n q hq => (((hf n).differentiableOn (by simp)) q hq).differentiableAt
          (hs.mem_nhds hq) |>.hasFDerivAt)
        (fun n q hq => by rw [← norm_iteratedFDeriv_one]; exact hfv 1 n q hq) hq₀ ?_ hq
      exact (hv 0).of_norm_bounded (fun n => by simpa using hfv 0 n q₀ hq₀)
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hs]
    refine ⟨fun q hq => (hderiv q hq).differentiableAt.differentiableWithinAt,
      fun h => by simp at h, ?_⟩
    have hfv' : ∀ k n, ∀ q ∈ s, ‖iteratedFDeriv ℝ k (fderiv ℝ (f n)) q‖ ≤ v (k + 1) n :=
      fun k n q hq => by rw [norm_iteratedFDeriv_fderiv]; exact hfv (k + 1) n q hq
    have := ih (G := Q →L[ℝ] G) (f := fun n => fderiv ℝ (f n))
      (hf := fun n => (hf n).fderiv_of_isOpen hs (by simp)) (v := fun k n => v (k + 1) n)
      (hv := fun k => hv (k + 1)) (hfv := hfv')
    exact this.congr (fun q hq => (hderiv q hq).fderiv)

end Tsum

section Param

variable {Q : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

omit [NormedSpace ℝ Q] in
lemma exists_bound_near {H : Type*} [NormedAddCommGroup H] {W : Set Q} (hW : IsOpen W)
    {Φ : Q × ℝ → H} (hΦ : ContinuousOn Φ (W ×ˢ univ)) {q₀ : Q} (hq₀ : q₀ ∈ W) :
    ∃ C, ∀ᶠ q in 𝓝 q₀, ∀ x ∈ Icc (0 : ℝ) 1, ‖Φ (q, x)‖ ≤ C := by
  have hcont : ∀ x, ContinuousAt Φ (q₀, x) := fun x =>
    hΦ.continuousAt ((hW.prod isOpen_univ).mem_nhds ⟨hq₀, mem_univ x⟩)
  obtain ⟨C₀, hC₀⟩ : ∃ C₀, ∀ x ∈ Icc (0 : ℝ) 1, ‖Φ (q₀, x)‖ ≤ C₀ := by
    have : ContinuousOn (fun x => Φ (q₀, x)) (Icc 0 1) := fun x _ =>
      ((hcont x).comp (continuous_const.prodMk continuous_id).continuousAt).continuousWithinAt
    exact isCompact_Icc.exists_bound_of_continuousOn this
  refine ⟨C₀ + 1, ?_⟩
  refine isCompact_Icc.eventually_forall_of_forall_eventually
    (P := fun q x => ‖Φ (q, x)‖ ≤ C₀ + 1) ?_
  intro x hx
  have h1 : Tendsto (fun z : Q × ℝ => ‖Φ z‖) (𝓝 (q₀, x)) (𝓝 ‖Φ (q₀, x)‖) := (hcont x).norm
  have : ‖Φ (q₀, x)‖ < C₀ + 1 := by linarith [hC₀ x hx]
  filter_upwards [h1.eventually (gt_mem_nhds this)] with z hz
  exact hz.le

lemma mem_Icc_of_uIoc {x : ℝ} (hx : x ∈ Ι (0 : ℝ) 1) : x ∈ Icc (0 : ℝ) 1 := by
  rw [uIoc_of_le zero_le_one] at hx
  exact Ioc_subset_Icc_self hx

/-- `C^∞` dependence of `∫₀¹ F(q, x) dx` on the parameter. -/
theorem contDiffOn_intervalIntegral_param {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] {W : Set Q} (hW : IsOpen W) (F : Q × ℝ → G)
    (hF : ContDiffOn ℝ ∞ F (W ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun q => ∫ x in (0 : ℝ)..1, F (q, x)) W := by
  rw [contDiffOn_infty]
  intro N
  induction N generalizing G with
  | zero =>
    rw [Nat.cast_zero, contDiffOn_zero]
    intro q₀ hq₀
    obtain ⟨C, hC⟩ := exists_bound_near hW hF.continuousOn hq₀
    refine ContinuousAt.continuousWithinAt ?_
    refine intervalIntegral.continuousAt_of_dominated_interval (bound := fun _ => C) ?_ ?_
      intervalIntegrable_const ?_
    · filter_upwards [hW.mem_nhds hq₀] with q hq
      exact (hF.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
        (fun x => ⟨hq, mem_univ x⟩)).aestronglyMeasurable
    · filter_upwards [hC] with q hq
      exact Filter.Eventually.of_forall (fun x hx => hq x (mem_Icc_of_uIoc hx))
    · refine Filter.Eventually.of_forall (fun x _ => ?_)
      exact (hF.continuousOn.continuousAt ((hW.prod isOpen_univ).mem_nhds
        ⟨hq₀, mem_univ x⟩)).comp (continuous_id.prodMk continuous_const).continuousAt
  | succ N ih =>
    have hWo : IsOpen (W ×ˢ (univ : Set ℝ)) := hW.prod isOpen_univ
    set F' : Q × ℝ → Q →L[ℝ] G := fun z => (fderiv ℝ F z).comp (ContinuousLinearMap.inl ℝ Q ℝ)
      with hF'def
    have hF' : ContDiffOn ℝ ∞ F' (W ×ˢ univ) :=
      (hF.fderiv_of_isOpen hWo (by simp)).clm_comp contDiffOn_const
    have hFd : ∀ q ∈ W, ∀ x : ℝ, HasFDerivAt (fun q => F (q, x)) (F' (q, x)) q := by
      intro q hq x
      have h1 : HasFDerivAt F (fderiv ℝ F (q, x)) (q, x) :=
        ((hF.differentiableOn (by simp)) (q, x) ⟨hq, mem_univ x⟩).differentiableAt
          (hWo.mem_nhds ⟨hq, mem_univ x⟩) |>.hasFDerivAt
      exact h1.comp q (hasFDerivAt_prodMk_left q x)
    have hcontq : ∀ q ∈ W, Continuous fun x => F (q, x) := fun q hq =>
      hF.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
        (fun x => ⟨hq, mem_univ x⟩)
    have hcontq' : ∀ q ∈ W, Continuous fun x => F' (q, x) := fun q hq =>
      hF'.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
        (fun x => ⟨hq, mem_univ x⟩)
    have hderiv : ∀ q₀ ∈ W, HasFDerivAt (fun q => ∫ x in (0 : ℝ)..1, F (q, x))
        (∫ x in (0 : ℝ)..1, F' (q₀, x)) q₀ := by
      intro q₀ hq₀
      obtain ⟨C, hC⟩ := exists_bound_near hW hF'.continuousOn hq₀
      set s := {q | q ∈ W ∧ ∀ x ∈ Icc (0 : ℝ) 1, ‖F' (q, x)‖ ≤ C}
      have hs : s ∈ 𝓝 q₀ := Filter.inter_mem (hW.mem_nhds hq₀) hC
      refine hasFDerivAt_integral_of_dominated_of_fderiv_le'' (bound := fun _ => C)
        (F := fun q x => F (q, x)) (F' := fun q x => F' (q, x))
        hs ?_ ((hcontq q₀ hq₀).intervalIntegrable _ _)
        (hcontq' q₀ hq₀).aestronglyMeasurable ?_ intervalIntegrable_const ?_
      · filter_upwards [hW.mem_nhds hq₀] with q hq
        exact (hcontq q hq).aestronglyMeasurable
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc (fun x hx q hq => ?_)
        exact hq.2 x (mem_Icc_of_uIoc hx)
      · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_uIoc (fun x _ q hq => ?_)
        exact hFd q hq.1 x
    rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hW]
    refine ⟨fun q hq => (hderiv q hq).differentiableAt.differentiableWithinAt,
      fun h => by simp at h, ?_⟩
    exact (ih F' hF').congr (fun q hq => (hderiv q hq).fderiv)

end Param

section Polar

variable {Q G : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma sign_sum_surj {k : ℕ} (r : Fin k → Fin k) :
    ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
      (if ∀ j, r j ∈ S then (-1 : ℝ) ^ (Finset.univ \ S).card else 0) =
      if Function.Surjective r then 1 else 0 := by
  classical
  set g : Fin k → ℝ := fun i => if ∃ j, r j = i then 0 else -1 with hg
  have h1 := Finset.prod_add (s := (Finset.univ : Finset (Fin k))) (fun _ => (1 : ℝ)) g
  simp only [Finset.prod_const_one, one_mul] at h1
  have h2 : ∀ S : Finset (Fin k), ∏ i ∈ Finset.univ \ S, g i =
      if ∀ j, r j ∈ S then (-1 : ℝ) ^ (Finset.univ \ S).card else 0 := by
    intro S
    split_ifs with hTS
    · rw [Finset.prod_congr rfl (g := fun _ => (-1 : ℝ))]
      · simp
      · intro i hi
        have : ¬ ∃ j, r j = i := by
          rintro ⟨j, rfl⟩
          exact (Finset.mem_sdiff.1 hi).2 (hTS j)
        simp only [hg, this, if_false]
    · push_neg at hTS
      obtain ⟨j, hj⟩ := hTS
      exact Finset.prod_eq_zero (Finset.mem_sdiff.2 ⟨Finset.mem_univ (r j), hj⟩)
        (by simp only [hg]; rw [if_pos ⟨j, rfl⟩])
  rw [← Finset.sum_congr rfl (fun S _ => h2 S), ← h1]
  split_ifs with hT
  · apply Finset.prod_eq_one
    intro i _
    simp only [hg]
    rw [if_pos (hT i)]
    ring
  · obtain ⟨i, hi⟩ : ∃ i, ¬ ∃ j, r j = i := by
      by_contra h
      push_neg at h
      exact hT h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp only [hg]; rw [if_neg hi]; ring)

/-- The polarization identity. -/
lemma polarization {k : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin k => Q) G)
    (hsymm : ∀ (σ : Equiv.Perm (Fin k)) (v : Fin k → Q), M (v ∘ σ) = M v) (v : Fin k → Q) :
    ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
      (-1 : ℝ) ^ (Finset.univ \ S).card • M (fun _ => ∑ i ∈ S, v i) =
      (k.factorial : ℝ) • M v := by
  classical
  have hexp : ∀ S : Finset (Fin k), M (fun _ => ∑ i ∈ S, v i) =
      ∑ r : Fin k → Fin k, if ∀ j, r j ∈ S then M (fun j => v (r j)) else 0 := by
    intro S
    rw [M.map_sum_finset (fun _ i => v i) (fun _ => S), ← Finset.sum_filter]
    congr 1
    ext r
    simp [Fintype.mem_piFinset]
  simp_rw [hexp, Finset.smul_sum]
  rw [Finset.sum_comm]
  have hin : ∀ r : Fin k → Fin k, ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
      (-1 : ℝ) ^ (Finset.univ \ S).card • (if ∀ j, r j ∈ S then M (fun j => v (r j)) else 0) =
      (if Function.Surjective r then (1 : ℝ) else 0) • M (fun j => v (r j)) := by
    intro r
    rw [← sign_sum_surj r, Finset.sum_smul]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    split_ifs <;> simp
  simp_rw [hin, ite_smul, one_smul, zero_smul]
  rw [← Finset.sum_filter]
  have hperm : ∑ σ : Equiv.Perm (Fin k), M (v ∘ σ) =
      ∑ r ∈ Finset.univ.filter (fun r : Fin k → Fin k => Function.Surjective r),
        M (fun j => v (r j)) := by
    refine Finset.sum_bij (fun σ _ => ⇑σ) (fun σ _ => ?_) (fun σ₁ _ σ₂ _ h => ?_)
      (fun r hr => ?_) (fun σ _ => rfl)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact σ.surjective
    · exact Equiv.coe_fn_injective h
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
      exact ⟨Equiv.ofBijective r ⟨Finite.injective_iff_surjective.2 hr, hr⟩, Finset.mem_univ _,
        rfl⟩
  rw [← hperm]
  simp_rw [hsymm]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    Nat.cast_smul_eq_nsmul]

lemma norm_le_of_symm {k : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin k => Q) G)
    (hsymm : ∀ (σ : Equiv.Perm (Fin k)) (v : Fin k → Q), M (v ∘ σ) = M v) {c : ℝ}
    (hc : 0 ≤ c) (hdiag : ∀ h : Q, ‖h‖ ≤ 1 → ‖M (fun _ => h)‖ ≤ c) :
    ‖M‖ ≤ (2 * k) ^ k * c := by
  classical
  -- diagonal values scale
  have hdiag' : ∀ h : Q, ‖M (fun _ => h)‖ ≤ ‖h‖ ^ k * c := by
    intro h
    rcases eq_or_ne h 0 with rfl | h0
    · rcases Nat.eq_zero_or_pos k with rfl | hk
      · simpa using hdiag 0 (by simp)
      · have : M (fun _ => (0 : Q)) = 0 := M.map_coord_zero ⟨0, hk⟩ rfl
        rw [this, norm_zero]
        positivity
    · have hn : 0 < ‖h‖ := norm_pos_iff.2 h0
      have e : (fun _ : Fin k => h) = fun _ => ‖h‖ • (‖h‖⁻¹ • h) := by
        funext _; rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
      rw [e, M.map_smul_univ (fun _ => ‖h‖) (fun _ => ‖h‖⁻¹ • h), norm_smul]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, norm_pow, Real.norm_eq_abs,
        abs_of_pos hn]
      gcongr
      apply hdiag
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  -- unit vectors
  have hunit : ∀ v : Fin k → Q, (∀ i, ‖v i‖ ≤ 1) → ‖M v‖ ≤ (2 * k) ^ k * c := by
    intro v hv
    have hp := polarization M hsymm v
    have hfact : (1 : ℝ) ≤ k.factorial := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hle : ‖(k.factorial : ℝ) • M v‖ ≤ ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
        (k : ℝ) ^ k * c := by
      rw [← hp]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun S _ => ?_))
      rw [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      refine (hdiag' _).trans ?_
      gcongr
      calc ‖∑ i ∈ S, v i‖ ≤ ∑ i ∈ S, ‖v i‖ := norm_sum_le _ _
        _ ≤ ∑ i ∈ S, (1 : ℝ) := Finset.sum_le_sum (fun i _ => hv i)
        _ ≤ k := by
          simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
          exact_mod_cast (Finset.card_le_univ S).trans (by simp)
    rw [Finset.sum_const, Finset.card_powerset, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, norm_smul, Real.norm_natCast] at hle
    have hMv : ‖M v‖ ≤ (2 : ℝ) ^ k * (k ^ k * c) :=
      le_trans (le_mul_of_one_le_left (norm_nonneg _) hfact) (by exact_mod_cast hle)
    calc ‖M v‖ ≤ (2 : ℝ) ^ k * (k ^ k * c) := hMv
      _ = (2 * k) ^ k * c := by ring
  refine M.opNorm_le_bound (by positivity) (fun v => ?_)
  by_cases hz : ∃ i, v i = 0
  · obtain ⟨i, hi⟩ := hz
    rw [M.map_coord_zero i hi, norm_zero]
    positivity
  · push_neg at hz
    have hn : ∀ i, 0 < ‖v i‖ := fun i => norm_pos_iff.2 (hz i)
    have e : v = fun i => ‖v i‖ • (‖v i‖⁻¹ • v i) := by
      funext i; rw [smul_smul, mul_inv_cancel₀ (hn i).ne', one_smul]
    have hu : ∀ i, ‖‖v i‖⁻¹ • v i‖ ≤ 1 := fun i => by
      rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (hn i).ne']
    conv_lhs => rw [e, M.map_smul_univ]
    rw [norm_smul]
    have hprod : ‖∏ i, ‖v i‖‖ = ∏ i, ‖v i‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg (fun i _ => norm_nonneg _))]
    rw [hprod, mul_comm]
    gcongr
    exact hunit _ hu

end Polar

section Line

variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℝ Q]

lemma iteratedDeriv_re_eq {g : ℂ → ℂ} {r : ℝ} (hg : DifferentiableOn ℂ g (ball 0 r))
    {φ : ℝ → ℝ} (hφ : ∀ s : ℝ, |s| < r → φ s = (g s).re) (k : ℕ) :
    ∀ s : ℝ, |s| < r → iteratedDeriv k φ s = (iteratedDeriv k g s).re := by
  induction k with
  | zero => intro s hs; simpa using hφ s hs
  | succ k ih =>
    intro s hs
    have hopen : IsOpen {s : ℝ | |s| < r} := isOpen_lt continuous_abs continuous_const
    have heq : iteratedDeriv k φ =ᶠ[𝓝 s] fun s' : ℝ => (iteratedDeriv k g s').re := by
      filter_upwards [hopen.mem_nhds hs] with s' hs'
      exact ih s' hs'
    rw [iteratedDeriv_succ, heq.deriv_eq]
    have hball : (s : ℂ) ∈ ball (0 : ℂ) r := by simpa using hs
    have hcd : ContDiffOn ℂ ⊤ g (ball 0 r) := hg.contDiffOn isOpen_ball
    have hdiff : DifferentiableOn ℂ (iteratedDerivWithin k g (ball 0 r)) (ball 0 r) :=
      hcd.differentiableOn_iteratedDerivWithin (by simp) (isOpen_ball.uniqueDiffOn)
    have hdiff' : DifferentiableOn ℂ (iteratedDeriv k g) (ball 0 r) :=
      hdiff.congr (fun z hz => (iteratedDerivWithin_of_isOpen isOpen_ball hz).symm)
    have hda : HasDerivAt (iteratedDeriv k g) (deriv (iteratedDeriv k g) s) s :=
      ((hdiff' _ hball).differentiableAt (isOpen_ball.mem_nhds hball)).hasDerivAt
    rw [(hda.real_of_complex).deriv, iteratedDeriv_succ]

/-- The diagonal of the `k`-th derivative along a line equals the `k`-th derivative of the
restriction. -/
lemma iteratedFDeriv_diag_eq {f : Q → ℝ} {V : Set Q} (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f V)
    {q : Q} (hq : q ∈ V) (h : Q) (k : ℕ) :
    iteratedFDeriv ℝ k f q (fun _ => h) = iteratedDeriv k (fun s : ℝ => f (q + s • h)) 0 := by
  set g : ℝ →L[ℝ] Q := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) h with hgdef
  set f₁ : Q → ℝ := fun y => f (q + y) with hf₁
  set V₁ : Set Q := (fun y => q + y) ⁻¹' V with hV₁
  have hV₁o : IsOpen V₁ := hV.preimage (continuous_const.add continuous_id)
  have hf₁c : ContDiffOn ℝ ∞ f₁ V₁ :=
    hf.comp (contDiff_const.add contDiff_id).contDiffOn (fun y hy => hy)
  have h0 : (0 : Q) ∈ V₁ := by simpa [hV₁] using hq
  have hpre : IsOpen (g ⁻¹' V₁) := hV₁o.preimage g.continuous
  have h0' : (0 : ℝ) ∈ g ⁻¹' V₁ := by simpa using h0
  have key := g.iteratedFDerivWithin_comp_right hf₁c hV₁o.uniqueDiffOn hpre.uniqueDiffOn
    (x := 0) (by simpa using h0) (i := k) (by exact_mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen k hpre h0', iteratedFDerivWithin_of_isOpen k hV₁o
    (by simpa using h0)] at key
  rw [iteratedDeriv_eq_iteratedFDeriv]
  have e1 : (fun s : ℝ => f (q + s • h)) = f₁ ∘ g := by
    funext s; simp [hf₁, hgdef]
  rw [e1, key]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero]
  rw [hf₁, iteratedFDeriv_comp_add_left, add_zero]
  simp [hgdef]

/-- **Cauchy estimate along a line**. -/
lemma norm_iteratedFDeriv_diag_le {f : Q → ℝ} {V : Set Q} (hV : IsOpen V)
    (hf : ContDiffOn ℝ ∞ f V) {q : Q} (hq : q ∈ V) (h : Q) {r M : ℝ} (hr : 0 < r)
    {g : ℂ → ℂ} (hg : DifferentiableOn ℂ g (ball 0 r)) (hgM : ∀ t ∈ ball (0 : ℂ) r, ‖g t‖ ≤ M)
    (hfg : ∀ s : ℝ, |s| < r → f (q + s • h) = (g s).re) (k : ℕ) :
    ‖iteratedFDeriv ℝ k f q (fun _ => h)‖ ≤ k.factorial * M / (r / 2) ^ k := by
  rw [iteratedFDeriv_diag_eq hV hf hq h k,
    iteratedDeriv_re_eq hg hfg k 0 (by simpa using hr)]
  have hr2 : 0 < r / 2 := by linarith
  have hdc : DiffContOnCl ℂ g (ball (0 : ℂ) (r / 2)) := by
    exact hg.diffContOnCl_ball (closedBall_subset_ball (by linarith))
  have := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr2 hdc
    (C := M) (fun z hz => hgM z (sphere_subset_closedBall.trans
      (closedBall_subset_ball (by linarith)) hz))
  rw [Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm _).trans (by simpa using this)

/-- Bound on the full `k`-th derivative from bounds along all lines. -/
lemma norm_iteratedFDeriv_le_of_lines {f : Q → ℝ} {V : Set Q} (hV : IsOpen V)
    (hfa : ∀ q ∈ V, AnalyticAt ℝ f q) {q : Q} (hq : q ∈ V) {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hline : ∀ h : Q, ‖h‖ ≤ 1 → ∃ g : ℂ → ℂ, DifferentiableOn ℂ g (ball 0 r) ∧
      (∀ t ∈ ball (0 : ℂ) r, ‖g t‖ ≤ M) ∧ ∀ s : ℝ, |s| < r → f (q + s • h) = (g s).re)
    (k : ℕ) :
    ‖iteratedFDeriv ℝ k f q‖ ≤ (2 * k) ^ k * (k.factorial * M / (r / 2) ^ k) := by
  have hf : ContDiffOn ℝ ∞ f V := fun y hy => (hfa y hy).contDiffAt.contDiffWithinAt
  refine norm_le_of_symm _ (fun σ v => ?_) (by positivity) (fun h hh => ?_)
  · exact ((hfa q hq).contDiffAt (n := ω)).iteratedFDeriv_comp_perm v σ
  · obtain ⟨g, hg, hgM, hfg⟩ := hline h hh
    exact norm_iteratedFDeriv_diag_le hV hf hq h hr hg hgM hfg k

end Line

section Tube

/-- Tube lemma for periodic functions. -/
lemma tube_periodic {Z : Type*} [TopologicalSpace Z] {g : ℝ → Z → ℝ}
    (hg : Continuous (fun p : ℝ × Z => g p.1 p.2)) (hper : ∀ y z, g (y + 1) z = g y z)
    {z₀ : Z} {c : ℝ} (h0 : ∀ y, g y z₀ < c) : ∀ᶠ z in 𝓝 z₀, ∀ y, g y z < c := by
  have hK := isCompact_Icc.eventually_forall_of_forall_eventually (x₀ := z₀)
    (K := Icc (0 : ℝ) 1) (P := fun z y => g y z < c) (fun y _ => by
      have : Tendsto (fun p : Z × ℝ => g p.2 p.1) (𝓝 (z₀, y)) (𝓝 (g y z₀)) :=
        (hg.comp continuous_swap).tendsto (z₀, y)
      exact this.eventually (gt_mem_nhds (h0 y)))
  filter_upwards [hK] with z hz y
  have hp : Function.Periodic (fun y => g y z) 1 := fun y => hper y z
  have e : g y z = g (Int.fract y) z := by
    have := hp.sub_int_mul_eq (n := ⌊y⌋) (x := y)
    simp only [mul_one] at this
    rw [Int.fract, this]
  rw [e]
  exact hz _ ⟨Int.fract_nonneg y, (Int.fract_lt_one y).le⟩

end Tube



section Cpoly

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℂ G] [NormedSpace ℝ G] [IsScalarTower ℝ ℂ G]

/-- The complexification of `t ↦ p_m(w + t d, …, w + t d)`. -/
def cpoly (pser : FormalMultilinearSeries ℝ E G) (m : ℕ) (w d : E) (t : ℂ) : G :=
  ∑ S : Finset (Fin m), t ^ S.card • pser m (S.piecewise (fun _ => d) (fun _ => w))

lemma cpoly_real (pser : FormalMultilinearSeries ℝ E G) (m : ℕ)
    (w d : E) (s : ℝ) : cpoly pser m w d s = pser m (fun _ => w + s • d) := by
  classical
  have e : (fun _ : Fin m => w + s • d) = (fun _ : Fin m => s • d) + (fun _ => w) := by
    funext i; simp [add_comm]
  rw [e, (pser m).map_add_univ]
  unfold cpoly
  refine Finset.sum_congr rfl (fun S _ => ?_)
  have hpw : S.piecewise (fun _ => s • d) (fun _ => w) =
      S.piecewise (fun i => s • (S.piecewise (fun _ => d) (fun _ => w)) i)
        (S.piecewise (fun _ => d) (fun _ => w)) := by
    funext i; by_cases hi : i ∈ S <;> simp [hi]
  rw [hpw, (pser m).map_piecewise_smul (fun _ => s) (S.piecewise (fun _ => d) (fun _ => w)) S,
    Finset.prod_const]
  rw [← Complex.ofReal_pow]
  exact algebraMap_smul ℂ (s ^ S.card) _

lemma norm_cpoly_le (pser : FormalMultilinearSeries ℝ E G) (m : ℕ)
    (w d : E) (t : ℂ) : ‖cpoly pser m w d t‖ ≤ ‖pser m‖ * (‖w‖ + ‖t‖ * ‖d‖) ^ m := by
  classical
  unfold cpoly
  refine (norm_sum_le _ _).trans ?_
  have hS : ∀ S : Finset (Fin m), ‖t ^ S.card • pser m (S.piecewise (fun _ => d) (fun _ => w))‖ ≤
      ‖pser m‖ * ((‖t‖ * ‖d‖) ^ S.card * ‖w‖ ^ (m - S.card)) := by
    intro S
    rw [norm_smul, norm_pow]
    have h1 := (pser m).le_opNorm (S.piecewise (fun _ => d) (fun _ => w))
    have h2 : ∏ i, ‖S.piecewise (fun _ => d) (fun _ => w) i‖ =
        ‖d‖ ^ S.card * ‖w‖ ^ (m - S.card) := by
      rw [show (fun i => ‖S.piecewise (fun _ => d) (fun _ => w) i‖) =
          S.piecewise (fun _ => ‖d‖) (fun _ => ‖w‖) from by
        funext i; by_cases hi : i ∈ S <;> simp [hi] ]
      rw [Finset.prod_piecewise, Finset.prod_const, Finset.prod_const, Finset.univ_inter,
        ← Finset.compl_eq_univ_sdiff, Finset.card_compl, Fintype.card_fin]
    rw [h2] at h1
    calc ‖t‖ ^ S.card * ‖pser m (S.piecewise (fun _ => d) (fun _ => w))‖
        ≤ ‖t‖ ^ S.card * (‖pser m‖ * (‖d‖ ^ S.card * ‖w‖ ^ (m - S.card))) := by gcongr
      _ = ‖pser m‖ * ((‖t‖ * ‖d‖) ^ S.card * ‖w‖ ^ (m - S.card)) := by rw [mul_pow]; ring
  refine (Finset.sum_le_sum (fun S _ => hS S)).trans (le_of_eq ?_)
  rw [← Finset.mul_sum]
  congr 1
  have := Finset.sum_pow_mul_eq_add_pow (‖t‖ * ‖d‖) ‖w‖ (Finset.univ : Finset (Fin m))
  rw [Finset.powerset_univ, Finset.card_univ, Fintype.card_fin] at this
  rw [this, add_comm]

lemma differentiable_cpoly (pser : FormalMultilinearSeries ℝ E G) (m : ℕ)
    (w d : E) : Differentiable ℂ (cpoly pser m w d) := by
  unfold cpoly
  exact Differentiable.fun_sum (fun S _ => (differentiable_id.pow _).smul_const _)

end Cpoly

section LineExt

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- **Uniform complex extension along real lines** of a real-analytic family. -/
theorem line_ext {δ : ℝ} {U : Set P} {A : P → ℂ → M2} (hA : IsAnalyticCocycleFamily δ U A)
    {p₀ : P} (hp₀ : p₀ ∈ U) :
    ∃ ρ > 0, ∃ M ≥ 0, ball p₀ ρ ⊆ U ∧ ∀ p ∈ ball p₀ ρ, ∀ y : ℝ, ∀ b : P, ∀ c : ℂ,
      ‖b‖ ≤ 1 → ‖c‖ ≤ 1 → ∃ G : ℂ → M2, DifferentiableOn ℂ G (ball 0 ρ) ∧
        (∀ t ∈ ball (0 : ℂ) ρ, ‖G t‖ ≤ M) ∧
        ∀ s : ℝ, |s| < ρ → G s = A (p + s • b) ((y : ℂ) + s * c) := by
  classical
  set F : P × ℂ → M2 := fun q => A q.1 q.2 with hF
  have hδ : 0 < δ := (hA.cocycle p₀ hp₀).pos
  have hloc : ∀ y₀ : ℝ, ∃ r' : ℝ, 0 < r' ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∃ pser, ∃ r, HasFPowerSeriesOnBall (𝕜 := ℝ) F pser (p₀, (y₀ : ℂ)) r ∧ (∀ m, ‖pser m‖ * r' ^ m ≤ C) ∧
      ∀ v : P × ℂ, ‖v‖ < r' → HasSum (fun m => pser m (fun _ => v)) (F ((p₀, (y₀ : ℂ)) + v)) := by
    intro y₀
    have hmem : (p₀, (y₀ : ℂ)) ∈ U ×ˢ strip δ := ⟨hp₀, by simp [strip, hδ]⟩
    obtain ⟨pser, r, hpr⟩ := hA.analytic _ hmem
    obtain ⟨r', hr'0, hr'r⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hpr.r_pos
    obtain ⟨C, hCpos, hC⟩ := pser.norm_mul_pow_le_of_lt_radius (hr'r.trans_le hpr.r_le)
    refine ⟨r', by exact_mod_cast hr'0, C, hCpos.le, pser, r, hpr, fun m => by exact_mod_cast hC m,
      fun v hv => ?_⟩
    apply hpr.hasSum
    rw [Metric.mem_eball, edist_zero_right]
    refine lt_trans ?_ hr'r
    exact_mod_cast hv
  choose r' hr'0 C hC0 pser rr _hpr hpserC hpsum using hloc
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hA.isOpen p₀ hp₀
  obtain ⟨T, hT⟩ := isCompact_Icc.elim_finite_subcover
    (fun i : Icc (0 : ℝ) 1 => ball (i : ℝ) (r' i / 8)) (fun _ => isOpen_ball)
    (fun y hy => mem_iUnion.2 ⟨⟨y, hy⟩, mem_ball_self (by have := hr'0 y; positivity)⟩)
  have hTne : T.Nonempty := by
    obtain ⟨i, hi, -⟩ := mem_iUnion₂.1 (hT ⟨le_refl (0 : ℝ), zero_le_one⟩)
    exact ⟨i, hi⟩
  set ρ₀ := T.inf' hTne (fun i : Icc (0 : ℝ) 1 => r' i / 8) with hρ₀def
  have hρ₀ : 0 < ρ₀ := (Finset.lt_inf'_iff hTne).2 (fun i _ => by have := hr'0 i; positivity)
  set ρ := min ρ₀ (ε / 2) with hρdef
  have hρ : 0 < ρ := lt_min hρ₀ (by linarith)
  set M := T.sup' hTne (fun i : Icc (0 : ℝ) 1 => 2 * C i) with hMdef
  have hM : 0 ≤ M := by
    obtain ⟨i, hi⟩ := hTne
    exact le_trans (show (0 : ℝ) ≤ 2 * C i by have := hC0 i; positivity)
      (Finset.le_sup' (f := fun i : Icc (0 : ℝ) 1 => 2 * C i) hi)
  refine ⟨ρ, hρ, M, hM, (ball_subset_ball (min_le_right _ _)).trans
    ((ball_subset_ball (by linarith)).trans hεU), ?_⟩
  intro p hp y b c hb hc
  set y' : ℝ := Int.fract y with hy'
  obtain ⟨i, hiT, hiy⟩ := mem_iUnion₂.1 (hT ⟨Int.fract_nonneg y, (Int.fract_lt_one y).le⟩)
  have hρi : ρ ≤ r' i / 8 :=
    (min_le_left _ _).trans (Finset.inf'_le (f := fun i : Icc (0 : ℝ) 1 => r' i / 8) hiT)
  have hCi : 2 * C i ≤ M := Finset.le_sup' (f := fun i : Icc (0 : ℝ) 1 => 2 * C i) hiT
  have hr'i := hr'0 i
  set w : P × ℂ := (p - p₀, ((y' : ℂ) - ((i : ℝ) : ℂ))) with hw
  set d : P × ℂ := (b, c) with hd
  have hpp : ‖p - p₀‖ < ρ := by rw [← dist_eq_norm]; exact hp
  have hwn : ‖w‖ < r' i / 8 := by
    rw [hw, Prod.norm_def, max_lt_iff]
    refine ⟨hpp.trans_le hρi, ?_⟩
    have : ‖(y' : ℂ) - ((i : ℝ) : ℂ)‖ = |y' - i| := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    rw [this]
    have := hiy
    rw [mem_ball, Real.dist_eq] at this
    exact this
  have hdn : ‖d‖ ≤ 1 := by rw [hd, Prod.norm_def]; exact max_le hb hc
  have hgeom : Summable (fun m : ℕ => C i * (1 / 4 : ℝ) ^ m) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
  have hterm : ∀ m, ∀ t ∈ ball (0 : ℂ) ρ, ‖cpoly (pser i) m w d t‖ ≤ C i * (1 / 4 : ℝ) ^ m := by
    intro m t ht
    have ht' : ‖t‖ < ρ := by simpa using ht
    refine (norm_cpoly_le _ _ _ _ _).trans ?_
    have h1 : ‖w‖ + ‖t‖ * ‖d‖ ≤ r' i / 4 := by
      have : ‖t‖ * ‖d‖ ≤ ‖t‖ := mul_le_of_le_one_right (norm_nonneg _) hdn
      linarith
    calc ‖pser i m‖ * (‖w‖ + ‖t‖ * ‖d‖) ^ m ≤ ‖pser i m‖ * (r' i / 4) ^ m := by
          gcongr
      _ = (‖pser i m‖ * r' i ^ m) * (1 / 4) ^ m := by rw [div_pow, _root_.one_div_pow]; ring
      _ ≤ C i * (1 / 4) ^ m := by gcongr; exact hpserC i m
  refine ⟨fun t => ∑' m, cpoly (pser i) m w d t, ?_, ?_, ?_⟩
  · exact Complex.differentiableOn_tsum_of_summable_norm hgeom
      (fun m => (differentiable_cpoly _ _ _ _).differentiableOn) isOpen_ball hterm
  · intro t ht
    calc ‖∑' m, cpoly (pser i) m w d t‖ ≤ ∑' m, C i * (1 / 4 : ℝ) ^ m :=
          tsum_of_norm_bounded hgeom.hasSum (fun m => hterm m t ht)
      _ = C i * (4 / 3) := by
          rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
      _ ≤ 2 * C i := by have := hC0 i; nlinarith
      _ ≤ M := hCi
  · intro s hs
    have hv : ‖w + s • d‖ < r' i := by
      have : ‖s • d‖ ≤ |s| := by
        rw [norm_smul, Real.norm_eq_abs]; exact mul_le_of_le_one_right (abs_nonneg _) hdn
      calc ‖w + s • d‖ ≤ ‖w‖ + ‖s • d‖ := norm_add_le _ _
        _ < r' i := by linarith
    have hsum := hpsum i (w + s • d) hv
    simp_rw [cpoly_real]
    rw [hsum.tsum_eq]
    have hpU : p + s • b ∈ U := by
      apply hεU
      rw [mem_ball, dist_eq_norm]
      have : ‖s • b‖ ≤ |s| := by
        rw [norm_smul, Real.norm_eq_abs]; exact mul_le_of_le_one_right (abs_nonneg _) hb
      calc ‖p + s • b - p₀‖ = ‖(p - p₀) + s • b‖ := by congr 1; abel
        _ ≤ ‖p - p₀‖ + ‖s • b‖ := norm_add_le _ _
        _ < ε := by
          have := min_le_right ρ₀ (ε / 2)
          linarith
    have hper : Function.Periodic (A (p + s • b)) 1 := (hA.cocycle _ hpU).periodic
    simp only [hF, hw, hd, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
    have e1 : p₀ + (p - p₀ + s • b) = p + s • b := by abel
    have e2 : ((i : ℝ) : ℂ) + ((y' : ℂ) - ((i : ℝ) : ℂ) + s • c) =
        ((y : ℂ) + s * c) - ((⌊y⌋ : ℤ) : ℂ) * 1 := by
      rw [hy', Int.fract, Complex.real_smul]; push_cast; ring
    rw [e1, e2, hper.sub_int_mul_eq]

/-- Normalised extension along an arbitrary direction (radius `ρ / (1 + ‖b‖ + ‖c‖)`). -/
theorem line_ext' {δ : ℝ} {U : Set P} {A : P → ℂ → M2} (hA : IsAnalyticCocycleFamily δ U A)
    {p₀ : P} (hp₀ : p₀ ∈ U) :
    ∃ ρ > 0, ∃ M ≥ 0, ball p₀ ρ ⊆ U ∧ ∃ Ext : P → ℝ → P → ℂ → ℂ → M2,
      ∀ p ∈ ball p₀ ρ, ∀ y : ℝ, ∀ b : P, ∀ c : ℂ,
        DifferentiableOn ℂ (Ext p y b c) (ball 0 (ρ / (1 + ‖b‖ + ‖c‖))) ∧
        (∀ t ∈ ball (0 : ℂ) (ρ / (1 + ‖b‖ + ‖c‖)),
          ‖Ext p y b c t - A p y‖ ≤ 2 * M * (1 + ‖b‖ + ‖c‖) / ρ * ‖t‖) ∧
        ∀ s : ℝ, |s| < ρ / (1 + ‖b‖ + ‖c‖) → Ext p y b c s = A (p + s • b) ((y : ℂ) + s * c) := by
  obtain ⟨ρ, hρ, M, hM, hU, hG⟩ := line_ext hA hp₀
  have hG' : ∀ (p : P) (y : ℝ) (b : P) (c : ℂ), ∃ G : ℂ → M2, p ∈ ball p₀ ρ → ‖b‖ ≤ 1 → ‖c‖ ≤ 1 →
      DifferentiableOn ℂ G (ball 0 ρ) ∧ (∀ t ∈ ball (0 : ℂ) ρ, ‖G t‖ ≤ M) ∧
        ∀ s : ℝ, |s| < ρ → G s = A (p + s • b) ((y : ℂ) + s * c) := by
    intro p y b c
    by_cases h : p ∈ ball p₀ ρ ∧ ‖b‖ ≤ 1 ∧ ‖c‖ ≤ 1
    · obtain ⟨G, hG1⟩ := hG p h.1 y b c h.2.1 h.2.2
      exact ⟨G, fun _ _ _ => hG1⟩
    · exact ⟨0, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩
  choose G hGp using hG'
  refine ⟨ρ, hρ, M, hM, hU, fun p y b c t =>
    G p y ((1 + ‖b‖ + ‖c‖)⁻¹ • b) (((1 + ‖b‖ + ‖c‖ : ℝ) : ℂ)⁻¹ * c)
      (((1 + ‖b‖ + ‖c‖ : ℝ) : ℂ) * t), ?_⟩
  intro p hp y b c
  simp only
  set lam : ℝ := 1 + ‖b‖ + ‖c‖ with hlam
  have hlam0 : 0 < lam := by positivity
  have hb : ‖lam⁻¹ • b‖ ≤ 1 := by
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hlam0, inv_mul_le_iff₀ hlam0]
    linarith [norm_nonneg c]
  have hc : ‖(lam : ℂ)⁻¹ * c‖ ≤ 1 := by
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam0,
      inv_mul_le_iff₀ hlam0]
    linarith [norm_nonneg b]
  obtain ⟨hd, hbd, hval⟩ := hGp p y _ _ hp hb hc
  have hmaps : ∀ t ∈ ball (0 : ℂ) (ρ / lam), (lam : ℂ) * t ∈ ball (0 : ℂ) ρ := by
    intro t ht
    rw [mem_ball_zero_iff] at ht ⊢
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlam0]
    rw [lt_div_iff₀ hlam0] at ht
    linarith
  refine ⟨?_, ?_, ?_⟩
  · exact hd.comp (f := fun t : ℂ => (lam : ℂ) * t)
      (differentiable_id.const_mul (lam : ℂ)).differentiableOn hmaps
  · intro t ht
    have h0 : G p y (lam⁻¹ • b) ((lam : ℂ)⁻¹ * c) 0 = A p y := by
      have := hval 0 (by simpa using hρ)
      simpa using this
    have hsch := Complex.dist_le_div_mul_dist_of_mapsTo_ball hd
      (R₂ := 2 * M) (fun z hz => by
        rw [mem_closedBall, dist_eq_norm]
        calc ‖G p y _ _ z - G p y _ _ 0‖ ≤ ‖G p y _ _ z‖ + ‖G p y _ _ 0‖ := norm_sub_le _ _
          _ ≤ M + M := add_le_add (hbd z hz) (hbd 0 (by simpa using hρ))
          _ = 2 * M := by ring) (hmaps t ht)
    rw [dist_eq_norm, dist_eq_norm, sub_zero, h0, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hlam0] at hsch
    calc _ ≤ 2 * M / ρ * (lam * ‖t‖) := hsch
      _ = 2 * M * lam / ρ * ‖t‖ := by ring
  · intro s hs
    have hs' : |lam * s| < ρ := by
      rw [abs_mul, abs_of_pos hlam0]
      rw [lt_div_iff₀ hlam0] at hs
      linarith
    have := hval (lam * s) hs'
    rw [show (lam : ℂ) * (s : ℂ) = ((lam * s : ℝ) : ℂ) by push_cast; ring, this]
    congr 1
    · rw [smul_smul, mul_comm lam s, mul_assoc, mul_inv_cancel₀ hlam0.ne', mul_one]
    · have hl : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam0.ne'
      push_cast
      field_simp

end LineExt

section Trig

/-- Uniform approximation of a continuous `1`-periodic function by an entire `1`-periodic
function (a trigonometric polynomial). -/
lemma exists_entire_approx {g : ℝ → ℂ} (hg : Continuous g) (hp : Function.Periodic g 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ (∀ z, G (z + 1) = G z) ∧ ∀ y : ℝ, ‖G y - g y‖ < ε := by
  haveI : Fact ((0 : ℝ) < 1) := ⟨zero_lt_one⟩
  have hc : Continuous (hp.lift : AddCircle (1 : ℝ) → ℂ) := by
    rw [(QuotientAddGroup.isQuotientMap_mk _).continuous_iff]
    have : hp.lift ∘ (QuotientAddGroup.mk : ℝ → AddCircle (1 : ℝ)) = g := by
      funext x; exact hp.lift_coe x
    rw [this]; exact hg
  let gc : C(AddCircle (1 : ℝ), ℂ) := ⟨hp.lift, hc⟩
  have hmem : gc ∈ closure (Submodule.span ℂ (Set.range (fourier (T := (1 : ℝ)))) :
      Set C(AddCircle (1 : ℝ), ℂ)) := by
    rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top]; trivial
  obtain ⟨φ, hφ1, hφ2⟩ := Metric.mem_closure_iff.1 hmem ε hε
  obtain ⟨c, hcφ⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hφ1
  refine ⟨fun z => ∑ n ∈ c.support, c n * Complex.exp (2 * Real.pi * Complex.I * n * z), ?_, ?_,
    ?_⟩
  · fun_prop
  · intro z
    refine Finset.sum_congr rfl (fun n _ => ?_)
    congr 1
    rw [show 2 * (Real.pi : ℂ) * Complex.I * n * (z + 1) =
      2 * Real.pi * Complex.I * n * z + (n : ℂ) * (2 * Real.pi * Complex.I) by ring,
      Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  · intro y
    have h1 : ‖φ y - gc y‖ < ε := by
      calc ‖φ y - gc y‖ = dist (φ y) (gc y) := (dist_eq_norm _ _).symm
        _ ≤ dist φ gc := ContinuousMap.dist_apply_le_dist _
        _ = dist gc φ := dist_comm _ _
        _ < ε := hφ2
    have h2 : φ y = ∑ n ∈ c.support, c n * Complex.exp (2 * Real.pi * Complex.I * n * y) := by
      rw [← hcφ]
      simp only [Finsupp.sum, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.smul_apply,
        fourier_coe_apply, smul_eq_mul, Complex.ofReal_one, div_one]
    have h3 : gc y = g y := hp.lift_coe y
    show ‖∑ n ∈ c.support, c n * Complex.exp (2 * Real.pi * Complex.I * n * y) - g y‖ < ε
    rw [← h2, ← h3]
    exact h1

end Trig



/-! ### Cones and Möbius contraction -/

/-- The one-step cone condition (in projective coordinates). -/
def Good (θ : ℝ) (N : M2) : Prop :=
  ‖N 0 1‖ + ‖N 1 0‖ + ‖N 1 1‖ < ‖N 0 0‖ ∧ ‖N.det‖ ≤ θ * (‖N 0 0‖ - ‖N 0 1‖) ^ 2

/-- The unstable cone. -/
def InCone (w : Fin 2 → ℂ) : Prop := ‖w 1‖ ≤ ‖w 0‖ ∧ w 0 ≠ 0

/-- Projective coordinate. -/
def ph (w : Fin 2 → ℂ) : ℂ := w 1 / w 0

lemma mulVec_apply0 (N : M2) (w : Fin 2 → ℂ) : (N *ᵥ w) 0 = N 0 0 * w 0 + N 0 1 * w 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma mulVec_apply1 (N : M2) (w : Fin 2 → ℂ) : (N *ᵥ w) 1 = N 1 0 * w 0 + N 1 1 * w 1 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

lemma InCone.norm_ph_le {w : Fin 2 → ℂ} (h : InCone w) : ‖ph w‖ ≤ 1 := by
  rw [ph, norm_div, div_le_one (norm_pos_iff.2 h.2)]; exact h.1

lemma good_cone {θ : ℝ} {N : M2} (hN : Good θ N) {w : Fin 2 → ℂ} (hw : InCone w) :
    InCone (N *ᵥ w) ∧ (‖N 0 0‖ - ‖N 0 1‖) * ‖w 0‖ ≤ ‖(N *ᵥ w) 0‖ := by
  have hw0 : 0 < ‖w 0‖ := norm_pos_iff.2 hw.2
  have hm : 0 < ‖N 0 0‖ - ‖N 0 1‖ := by
    have := hN.1; linarith [norm_nonneg (N 1 0), norm_nonneg (N 1 1)]
  have h0 : (‖N 0 0‖ - ‖N 0 1‖) * ‖w 0‖ ≤ ‖(N *ᵥ w) 0‖ := by
    rw [mulVec_apply0]
    have h1 : ‖N 0 1‖ * ‖w 1‖ ≤ ‖N 0 1‖ * ‖w 0‖ := mul_le_mul_of_nonneg_left hw.1 (norm_nonneg _)
    calc (‖N 0 0‖ - ‖N 0 1‖) * ‖w 0‖ ≤ ‖N 0 0 * w 0‖ - ‖N 0 1 * w 1‖ := by
          rw [norm_mul, norm_mul]; nlinarith
      _ ≤ ‖N 0 0 * w 0 + N 0 1 * w 1‖ := norm_add_ge _ _
  have h1 : ‖(N *ᵥ w) 1‖ ≤ (‖N 1 0‖ + ‖N 1 1‖) * ‖w 0‖ := by
    rw [mulVec_apply1]
    calc ‖N 1 0 * w 0 + N 1 1 * w 1‖ ≤ ‖N 1 0 * w 0‖ + ‖N 1 1 * w 1‖ := norm_add_le _ _
      _ = ‖N 1 0‖ * ‖w 0‖ + ‖N 1 1‖ * ‖w 1‖ := by rw [norm_mul, norm_mul]
      _ ≤ (‖N 1 0‖ + ‖N 1 1‖) * ‖w 0‖ := by
          have := mul_le_mul_of_nonneg_left hw.1 (norm_nonneg (N 1 1)); nlinarith
  have hlt : (‖N 1 0‖ + ‖N 1 1‖) * ‖w 0‖ < (‖N 0 0‖ - ‖N 0 1‖) * ‖w 0‖ := by
    apply mul_lt_mul_of_pos_right _ hw0
    linarith [hN.1]
  refine ⟨⟨by linarith, fun h => ?_⟩, h0⟩
  have : ‖(N *ᵥ w) 0‖ = 0 := by rw [h]; simp
  nlinarith

lemma mob_diff (n00 n01 n10 n11 w0 w1 v0 v1 : ℂ) (h1 : n00 * w0 + n01 * w1 ≠ 0)
    (h2 : n00 * v0 + n01 * v1 ≠ 0) (hw : w0 ≠ 0) (hv : v0 ≠ 0) :
    (n10 * w0 + n11 * w1) / (n00 * w0 + n01 * w1) - (n10 * v0 + n11 * v1) / (n00 * v0 + n01 * v1)
      = (n00 * n11 - n01 * n10) * (w1 / w0 - v1 / v0) * (w0 * v0) /
        ((n00 * w0 + n01 * w1) * (n00 * v0 + n01 * v1)) := by
  rw [div_sub_div _ _ hw hv, mul_assoc, div_mul_cancel₀ _ (mul_ne_zero hw hv),
    div_sub_div _ _ h1 h2]
  congr 1
  ring

lemma ph_sub_ph {w w' : Fin 2 → ℂ} (h0 : w 0 ≠ 0) (h0' : w' 0 ≠ 0) :
    ph w - ph w' = (w 1 * w' 0 - w' 1 * w 0) / (w 0 * w' 0) := by
  unfold ph; field_simp

lemma good_lip {θ : ℝ} {N : M2} (hN : Good θ N) {w w' : Fin 2 → ℂ} (hw : InCone w)
    (hw' : InCone w') : ‖ph (N *ᵥ w) - ph (N *ᵥ w')‖ ≤ θ * ‖ph w - ph w'‖ := by
  obtain ⟨hc, h0⟩ := good_cone hN hw
  obtain ⟨hc', h0'⟩ := good_cone hN hw'
  have hm : 0 < ‖N 0 0‖ - ‖N 0 1‖ := by
    have := hN.1; linarith [norm_nonneg (N 1 0), norm_nonneg (N 1 1)]
  have hw0 : 0 < ‖w 0‖ := norm_pos_iff.2 hw.2
  have hw0' : 0 < ‖w' 0‖ := norm_pos_iff.2 hw'.2
  have key : ph (N *ᵥ w) - ph (N *ᵥ w') = N.det * (ph w - ph w') * (w 0 * w' 0) /
      ((N *ᵥ w) 0 * (N *ᵥ w') 0) := by
    have e1 := hc.2
    have e2 := hc'.2
    rw [mulVec_apply0] at e1 e2
    unfold ph
    rw [mulVec_apply0, mulVec_apply0, mulVec_apply1, mulVec_apply1, det_fin_two]
    exact mob_diff _ _ _ _ _ _ _ _ e1 e2 hw.2 hw'.2
  rw [key, norm_div, norm_mul, norm_mul, norm_mul, norm_mul]
  set m := ‖N 0 0‖ - ‖N 0 1‖
  have hden : m * ‖w 0‖ * (m * ‖w' 0‖) ≤ ‖(N *ᵥ w) 0‖ * ‖(N *ᵥ w') 0‖ :=
    mul_le_mul h0 h0' (by positivity) (norm_nonneg _)
  have hpos : 0 < m * ‖w 0‖ * (m * ‖w' 0‖) := by positivity
  rw [div_le_iff₀ (hpos.trans_le hden)]
  calc ‖N.det‖ * ‖ph w - ph w'‖ * (‖w 0‖ * ‖w' 0‖)
      ≤ θ * m ^ 2 * ‖ph w - ph w'‖ * (‖w 0‖ * ‖w' 0‖) := by gcongr; exact hN.2
    _ = θ * ‖ph w - ph w'‖ * (m * ‖w 0‖ * (m * ‖w' 0‖)) := by ring
    _ ≤ θ * ‖ph w - ph w'‖ * (‖(N *ᵥ w) 0‖ * ‖(N *ᵥ w') 0‖) := by
        have hθ : 0 ≤ θ := by
          by_contra h
          push_neg at h
          have := hN.2
          have : θ * m ^ 2 < 0 := mul_neg_of_neg_of_pos h (by positivity)
          linarith [norm_nonneg N.det]
        gcongr

/-- Ordered products `M 1 * M 2 * ⋯ * M n`. -/
def pmat (M : ℕ → M2) : ℕ → M2
  | 0 => 1
  | n + 1 => pmat M n * M (n + 1)

lemma chain {θ : ℝ} (hθ : 0 ≤ θ) {N : ℕ → M2} (n : ℕ) (hN : ∀ j, 1 ≤ j → j ≤ n → Good θ (N j)) :
    ∀ w w' : Fin 2 → ℂ, InCone w → InCone w' → InCone (pmat N n *ᵥ w) ∧
      ‖ph (pmat N n *ᵥ w) - ph (pmat N n *ᵥ w')‖ ≤ θ ^ n * ‖ph w - ph w'‖ := by
  induction n with
  | zero => intro w w' hw _; simp [pmat, hw]
  | succ n ih =>
    intro w w' hw hw'
    have hg := hN (n + 1) (by omega) le_rfl
    have ih' := ih (fun j h1 h2 => hN j h1 (by omega))
    have e : ∀ u, pmat N (n + 1) *ᵥ u = pmat N n *ᵥ (N (n + 1) *ᵥ u) := by
      intro u; rw [pmat, ← Matrix.mulVec_mulVec]
    obtain ⟨h1, h2⟩ := ih' _ _ (good_cone hg hw).1 (good_cone hg hw').1
    refine ⟨by rw [e]; exact h1, ?_⟩
    rw [e, e]
    calc _ ≤ θ ^ n * ‖ph (N (n + 1) *ᵥ w) - ph (N (n + 1) *ᵥ w')‖ := h2
      _ ≤ θ ^ n * (θ * ‖ph w - ph w'‖) := by gcongr; exact good_lip hg hw hw'
      _ = θ ^ (n + 1) * ‖ph w - ph w'‖ := by ring

lemma proj_identity_aux (X M : ℕ → M2) (n : ℕ) :
    (∏ j ∈ Finset.range n, (X j).det) • (pmat M n * X n) =
      X 0 * pmat (fun j => (X (j - 1)).adjugate * M j * X j) n := by
  induction n with
  | zero => simp [pmat]
  | succ n ih =>
    simp only [pmat, Finset.prod_range_succ, Nat.add_sub_cancel]
    have h1 : (X n).det • (M (n + 1) * X (n + 1)) =
        X n * ((X n).adjugate * M (n + 1) * X (n + 1)) := by
      rw [show X n * ((X n).adjugate * M (n + 1) * X (n + 1)) =
          (X n * (X n).adjugate) * (M (n + 1) * X (n + 1)) by simp only [Matrix.mul_assoc],
        Matrix.mul_adjugate, Matrix.smul_mul, Matrix.one_mul]
    calc ((∏ j ∈ Finset.range n, (X j).det) * (X n).det) • (pmat M n * M (n + 1) * X (n + 1))
        = (∏ j ∈ Finset.range n, (X j).det) •
            (pmat M n * ((X n).det • (M (n + 1) * X (n + 1)))) := by
          simp only [Matrix.mul_smul, mul_smul, Matrix.mul_assoc]
      _ = (∏ j ∈ Finset.range n, (X j).det) • (pmat M n * X n) *
            ((X n).adjugate * M (n + 1) * X (n + 1)) := by
          rw [h1]; simp only [Matrix.smul_mul, Matrix.mul_assoc]
      _ = _ := by rw [ih, Matrix.mul_assoc]

/-- Frame change along a chain: the product `M_1 ⋯ M_n` is conjugated to the product of
`adj(X_{j-1}) M_j X_j`. -/
lemma proj_identity (X M : ℕ → M2) (n : ℕ) (e : Fin 2 → ℂ) :
    (∏ j ∈ Finset.range (n + 1), (X j).det) • (pmat M n *ᵥ e) =
      X 0 *ᵥ (pmat (fun j => (X (j - 1)).adjugate * M j * X j) n *ᵥ ((X n).adjugate *ᵥ e)) := by
  have h := proj_identity_aux X M n
  have he : (X n).det • e = X n *ᵥ ((X n).adjugate *ᵥ e) := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
  symm
  calc X 0 *ᵥ (pmat (fun j => (X (j - 1)).adjugate * M j * X j) n *ᵥ ((X n).adjugate *ᵥ e))
      = (X 0 * pmat (fun j => (X (j - 1)).adjugate * M j * X j) n) *ᵥ
          ((X n).adjugate *ᵥ e) := by
        rw [Matrix.mulVec_mulVec]
    _ = ((∏ j ∈ Finset.range n, (X j).det) • (pmat M n * X n)) *ᵥ ((X n).adjugate *ᵥ e) := by
        rw [h]
    _ = (∏ j ∈ Finset.range n, (X j).det) • (pmat M n *ᵥ (X n *ᵥ ((X n).adjugate *ᵥ e))) := by
        rw [Matrix.smul_mulVec, ← Matrix.mulVec_mulVec]
    _ = _ := by rw [← he, Matrix.mulVec_smul, smul_smul, Finset.prod_range_succ]

/-! ### The multiplier functional -/

lemma cr_add_left (u u' w : Fin 2 → ℂ) : cr (u + u') w = cr u w + cr u' w := by
  simp [cr]; ring

/-- `R(v) = cr(M₀ v, W) / cr(v, W₀)`. -/
def Rv (M0 : M2) (v W W₀ : Fin 2 → ℂ) : ℂ := cr (M0 *ᵥ v) W / cr v W₀

lemma Rv_smul (M0 : M2) {κ : ℂ} (hκ : κ ≠ 0) (v W W₀ : Fin 2 → ℂ) :
    Rv M0 (κ • v) W W₀ = Rv M0 v W W₀ := by
  unfold Rv
  rw [Matrix.mulVec_smul, cr_smul_left, cr_smul_left]
  by_cases h : cr v W₀ = 0
  · simp [h]
  · field_simp

/-- The Möbius form of `R` in a frame `X`. -/
lemma Rv_frame (M0 X : M2) (W W₀ : Fin 2 → ℂ) {κ : ℂ} (hκ : κ ≠ 0) {v U : Fin 2 → ℂ}
    (hv : κ • v = X *ᵥ U) (hU : U 0 ≠ 0) :
    Rv M0 v W W₀ = (cr (M0 *ᵥ (X *ᵥ ![1, 0])) W + cr (M0 *ᵥ (X *ᵥ ![0, 1])) W * ph U) /
      (cr (X *ᵥ ![1, 0]) W₀ + cr (X *ᵥ ![0, 1]) W₀ * ph U) := by
  rw [← Rv_smul M0 hκ, hv]
  have hXU : X *ᵥ U = U 0 • (X *ᵥ ![1, 0] + ph U • X *ᵥ ![0, 1]) := by
    rw [← Matrix.mulVec_smul, ← Matrix.mulVec_add, ← Matrix.mulVec_smul]
    congr 1
    ext i; fin_cases i <;> simp [ph]; field_simp
  rw [hXU, Rv_smul M0 hU, Rv]
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, cr_add_left, cr_add_left, cr_smul_left,
    cr_smul_left]
  ring

lemma rf_est {a b c d φ φ' : ℂ} {K : ℝ} (hc : ‖c - 1‖ < 1 / 4) (hd : ‖d‖ < 1 / 4)
    (ha : 3 / 4 < ‖a‖) (ha' : ‖a‖ < K) (hb : ‖b‖ < 1 / 4) (hφ : ‖φ‖ ≤ 1) (hφ' : ‖φ'‖ ≤ 1) :
    (a + b * φ') / (c + d * φ') ≠ 0 ∧ c + d * φ ≠ 0 ∧
      ‖(a + b * φ) / (c + d * φ) / ((a + b * φ') / (c + d * φ')) - 1‖ ≤ 4 * K * ‖φ - φ'‖ := by
  have hc' : 3 / 4 < ‖c‖ := by
    have := norm_sub_norm_le (1 : ℂ) (1 - c)
    rw [sub_sub_cancel, norm_one, norm_sub_rev] at this
    linarith
  have hden : ∀ ψ : ℂ, ‖ψ‖ ≤ 1 → 1 / 2 ≤ ‖c + d * ψ‖ := by
    intro ψ hψ
    have h1 : ‖d * ψ‖ ≤ 1 / 4 := by
      rw [norm_mul]; nlinarith [norm_nonneg d, norm_nonneg ψ]
    have := norm_add_ge c (d * ψ)
    linarith
  have hnum : ∀ ψ : ℂ, ‖ψ‖ ≤ 1 → 1 / 2 ≤ ‖a + b * ψ‖ := by
    intro ψ hψ
    have h1 : ‖b * ψ‖ ≤ 1 / 4 := by
      rw [norm_mul]; nlinarith [norm_nonneg b, norm_nonneg ψ]
    have := norm_add_ge a (b * ψ)
    linarith
  have hD := hden φ hφ
  have hD' := hden φ' hφ'
  have hN' := hnum φ' hφ'
  have hD0 : c + d * φ ≠ 0 := fun h => by rw [h, norm_zero] at hD; linarith
  have hD0' : c + d * φ' ≠ 0 := fun h => by rw [h, norm_zero] at hD'; linarith
  have hN0' : a + b * φ' ≠ 0 := fun h => by rw [h, norm_zero] at hN'; linarith
  refine ⟨div_ne_zero hN0' hD0', hD0, ?_⟩
  have key : (a + b * φ) / (c + d * φ) / ((a + b * φ') / (c + d * φ')) - 1 =
      (a * d - b * c) * (φ' - φ) / ((c + d * φ) * (a + b * φ')) := by
    rw [div_div_div_eq, div_sub_one (mul_ne_zero hD0 hN0')]
    congr 1
    ring
  rw [key, norm_div, norm_mul, norm_mul, norm_sub_rev φ' φ]
  have hK : 3 / 4 < K := ha.trans ha'
  have hadbc : ‖a * d - b * c‖ ≤ K := by
    have h1 : ‖a * d‖ ≤ K * (1 / 4) := by
      rw [norm_mul]; exact mul_le_mul ha'.le hd.le (norm_nonneg _) (by linarith)
    have h2 : ‖b * c‖ ≤ (1 / 4) * (5 / 4) := by
      rw [norm_mul]
      have : ‖c‖ ≤ 5 / 4 := by
        have := norm_le_norm_add_norm_sub' c 1
        rw [norm_one] at this
        linarith
      exact mul_le_mul hb.le this (norm_nonneg _) (by norm_num)
    calc ‖a * d - b * c‖ ≤ ‖a * d‖ + ‖b * c‖ := norm_sub_le _ _
      _ ≤ K := by linarith
  rw [div_le_iff₀ (by positivity)]
  calc ‖a * d - b * c‖ * ‖φ - φ'‖ ≤ K * ‖φ - φ'‖ := by gcongr
    _ = 4 * K * ‖φ - φ'‖ * (1 / 2 * (1 / 2)) := by ring
    _ ≤ 4 * K * ‖φ - φ'‖ * (‖c + d * φ‖ * ‖a + b * φ'‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hD hN' (by norm_num) (norm_nonneg _))
          (by have := norm_nonneg (φ - φ'); positivity)




/-- Tube lemma for periodic families (set version). -/
lemma tube_periodic_set {Z T : Type*} [TopologicalSpace Z] [TopologicalSpace T] {Φ : ℝ → Z → T}
    (hΦ : Continuous (fun p : ℝ × Z => Φ p.1 p.2)) (hper : ∀ y z, Φ (y + 1) z = Φ y z)
    {O : Set T} (hO : IsOpen O) {z₀ : Z} (h0 : ∀ y, Φ y z₀ ∈ O) :
    ∀ᶠ z in 𝓝 z₀, ∀ y, Φ y z ∈ O := by
  have hK := isCompact_Icc.eventually_forall_of_forall_eventually (x₀ := z₀)
    (K := Icc (0 : ℝ) 1) (P := fun z y => Φ y z ∈ O) (fun y _ => by
      have : Tendsto (fun p : Z × ℝ => Φ p.2 p.1) (𝓝 (z₀, y)) (𝓝 (Φ y z₀)) :=
        (hΦ.comp continuous_swap).tendsto (z₀, y)
      exact this.eventually (hO.mem_nhds (h0 y)))
  filter_upwards [hK] with z hz y
  have hp : Function.Periodic (fun y => Φ y z) 1 := fun y => hper y z
  have e : Φ y z = Φ (Int.fract y) z := by
    have := hp.sub_int_mul_eq (n := ⌊y⌋) (x := y)
    simp only [mul_one] at this
    rw [Int.fract, this]
  rw [e]
  exact hz _ ⟨Int.fract_nonneg y, (Int.fract_lt_one y).le⟩

/-- All the open conditions used in the perturbative analysis, at a point `y`. -/
structure Conds (θ K : ℝ) (N Bm Nm : M2) (a b c d : ℂ) : Prop where
  good1 : ‖N 0 1‖ + ‖N 1 0‖ + ‖N 1 1‖ < ‖N 0 0‖
  good2 : ‖N.det‖ < θ * (‖N 0 0‖ - ‖N 0 1‖) ^ 2
  bm : ‖Bm - 1‖ < 1 / 8
  hU : 1 / 2 * ‖Nm 0 1‖ + ‖Nm 1 0‖ / (1 / 2) + ‖Nm 1 1‖ < ‖Nm 0 0‖
  hS : 1 / 2 * ‖Nm 1 0‖ + ‖Nm 0 1‖ / (1 / 2) + ‖Nm 1 1‖ < ‖Nm 0 0‖
  hU2 : ‖Nm.det‖ < (‖Nm 0 0‖ - 1 / 2 * ‖Nm 0 1‖) ^ 2
  hS2 : ‖Nm.det‖ < (‖Nm 0 0‖ - 1 / 2 * ‖Nm 1 0‖) ^ 2
  h1 : 1 < ‖Nm 0 0‖ - ‖Nm 0 1‖ / 2
  ca : 3 / 4 < ‖a‖
  ca' : ‖a‖ < K
  cb : ‖b‖ < 1 / 4
  cc : ‖c - 1‖ < 1 / 4
  cd : ‖d‖ < 1 / 4

lemma isOpen_conds (θ K : ℝ) :
    IsOpen {t : M2 × M2 × M2 × ℂ × ℂ × ℂ × ℂ |
      Conds θ K t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2} := by
  have e : {t : M2 × M2 × M2 × ℂ × ℂ × ℂ × ℂ |
      Conds θ K t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2} =
      {t : M2 × M2 × M2 × ℂ × ℂ × ℂ × ℂ |
        (‖t.1 0 1‖ + ‖t.1 1 0‖ + ‖t.1 1 1‖ < ‖t.1 0 0‖ ∧
        ‖t.1.det‖ < θ * (‖t.1 0 0‖ - ‖t.1 0 1‖) ^ 2) ∧
        ‖t.2.1 - 1‖ < 1 / 8 ∧
        (1 / 2 * ‖t.2.2.1 0 1‖ + ‖t.2.2.1 1 0‖ / (1 / 2) + ‖t.2.2.1 1 1‖ < ‖t.2.2.1 0 0‖ ∧
        1 / 2 * ‖t.2.2.1 1 0‖ + ‖t.2.2.1 0 1‖ / (1 / 2) + ‖t.2.2.1 1 1‖ < ‖t.2.2.1 0 0‖ ∧
        ‖t.2.2.1.det‖ < (‖t.2.2.1 0 0‖ - 1 / 2 * ‖t.2.2.1 0 1‖) ^ 2 ∧
        ‖t.2.2.1.det‖ < (‖t.2.2.1 0 0‖ - 1 / 2 * ‖t.2.2.1 1 0‖) ^ 2 ∧
        1 < ‖t.2.2.1 0 0‖ - ‖t.2.2.1 0 1‖ / 2) ∧
        (3 / 4 < ‖t.2.2.2.1‖ ∧ ‖t.2.2.2.1‖ < K ∧ ‖t.2.2.2.2.1‖ < 1 / 4 ∧
        ‖t.2.2.2.2.2.1 - 1‖ < 1 / 4 ∧ ‖t.2.2.2.2.2.2‖ < 1 / 4)} := by
    ext t
    simp only [mem_setOf_eq]
    constructor
    · intro h
      exact ⟨⟨h.good1, h.good2⟩, h.bm, ⟨h.hU, h.hS, h.hU2, h.hS2, h.h1⟩, ⟨h.ca, h.ca', h.cb, h.cc,
        h.cd⟩⟩
    · rintro ⟨⟨h1, h2⟩, h3, ⟨h4, h5, h6, h7, h8⟩, ⟨h9, h10, h11, h12, h13⟩⟩
      exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13⟩
  rw [e]
  have c1 : Continuous fun t : M2 × M2 × M2 × ℂ × ℂ × ℂ × ℂ => t.1 := continuous_fst
  have c2 : Continuous fun t : M2 × M2 × M2 × ℂ × ℂ × ℂ × ℂ => t.2.1 :=
    continuous_fst.comp continuous_snd
  have c3 : Continuous fun t : M2 × M2 × M2 × ℂ × ℂ × ℂ × ℂ => t.2.2.1 :=
    continuous_fst.comp (continuous_snd.comp continuous_snd)
  have c4 : Continuous fun t : M2 × M2 × M2 × ℂ × ℂ × ℂ × ℂ => t.2.2.2 :=
    continuous_snd.comp (continuous_snd.comp continuous_snd)
  have e1 : ∀ i j, Continuous fun t : M2 × M2 × M2 × ℂ × ℂ × ℂ × ℂ => ‖t.1 i j‖ :=
    fun i j => (c1.matrix_elem i j).norm
  have e3 : ∀ i j, Continuous fun t : M2 × M2 × M2 × ℂ × ℂ × ℂ × ℂ => ‖t.2.2.1 i j‖ :=
    fun i j => (c3.matrix_elem i j).norm
  have d1 : Continuous fun t : M2 × M2 × M2 × ℂ × ℂ × ℂ × ℂ => ‖t.1.det‖ := c1.matrix_det.norm
  have d3 : Continuous fun t : M2 × M2 × M2 × ℂ × ℂ × ℂ × ℂ => ‖t.2.2.1.det‖ := c3.matrix_det.norm
  have b2 : Continuous fun t : M2 × M2 × M2 × ℂ × ℂ × ℂ × ℂ => ‖t.2.1 - 1‖ :=
    (c2.sub continuous_const).norm
  have k1 : Continuous fun t : M2 × M2 × M2 × ℂ × ℂ × ℂ × ℂ => t.2.2.2.1 := continuous_fst.comp c4
  have k2 : Continuous fun t : M2 × M2 × M2 × ℂ × ℂ × ℂ × ℂ => t.2.2.2.2.1 :=
    continuous_fst.comp (continuous_snd.comp c4)
  have k3 : Continuous fun t : M2 × M2 × M2 × ℂ × ℂ × ℂ × ℂ => t.2.2.2.2.2.1 :=
    continuous_fst.comp (continuous_snd.comp (continuous_snd.comp c4))
  have k4 : Continuous fun t : M2 × M2 × M2 × ℂ × ℂ × ℂ × ℂ => t.2.2.2.2.2.2 :=
    continuous_snd.comp (continuous_snd.comp (continuous_snd.comp c4))
  simp only [Set.setOf_and]
  refine ((isOpen_lt ?_ ?_).inter (isOpen_lt ?_ ?_)).inter ((isOpen_lt ?_ ?_).inter
    (((isOpen_lt ?_ ?_).inter ((isOpen_lt ?_ ?_).inter ((isOpen_lt ?_ ?_).inter
    ((isOpen_lt ?_ ?_).inter (isOpen_lt ?_ ?_))))).inter
    ((isOpen_lt ?_ ?_).inter ((isOpen_lt ?_ ?_).inter ((isOpen_lt ?_ ?_).inter
    ((isOpen_lt ?_ ?_).inter (isOpen_lt ?_ ?_)))))))
  all_goals first
    | exact continuous_const
    | exact b2
    | exact d1
    | exact d3
    | exact k1.norm
    | exact k2.norm
    | exact (k3.sub continuous_const).norm
    | exact k4.norm
    | exact ((e1 0 1).add (e1 1 0)).add (e1 1 1)
    | exact e1 0 0
    | exact e3 0 0
    | exact continuous_const.mul (((e1 0 0).sub (e1 0 1)).pow 2)
    | exact (((continuous_const.mul (e3 0 1)).add ((e3 1 0).div_const _)).add (e3 1 1))
    | exact (((continuous_const.mul (e3 1 0)).add ((e3 0 1).div_const _)).add (e3 1 1))
    | exact ((e3 0 0).sub (continuous_const.mul (e3 0 1))).pow 2
    | exact ((e3 0 0).sub (continuous_const.mul (e3 1 0))).pow 2
    | exact (e3 0 0).sub ((e3 0 1).div_const _)

/-- The data map at `y`, for parameter `α'` and perturbations `E = (Δ, E₀, …, E₄)`. -/
def condMap (F : ℝ → M2) (A₀ : ℝ → M2) (y : ℝ) (z : ℝ × (Fin 6 → M2)) :
    M2 × M2 × M2 × ℂ × ℂ × ℂ × ℂ :=
  ((F (y + z.1) + z.2 2).adjugate * (A₀ y + z.2 0) * (F y + z.2 1),
   (F y + z.2 1).adjugate * (F y + z.2 3),
   (F (y + z.1)).adjugate * (A₀ y + z.2 0) * F y,
   cr ((A₀ y + z.2 0) *ᵥ ((F y + z.2 1) *ᵥ ![1, 0])) ((F (y + z.1) + z.2 4) *ᵥ ![0, 1]),
   cr ((A₀ y + z.2 0) *ᵥ ((F y + z.2 1) *ᵥ ![0, 1])) ((F (y + z.1) + z.2 4) *ᵥ ![0, 1]),
   cr ((F y + z.2 1) *ᵥ ![1, 0]) ((F y + z.2 5) *ᵥ ![0, 1]),
   cr ((F y + z.2 1) *ᵥ ![0, 1]) ((F y + z.2 5) *ᵥ ![0, 1]))

lemma cr_e0_e1 : cr (![1, 0] : Fin 2 → ℂ) ![0, 1] = 1 := by simp [cr]

lemma cr_e1_e1 : cr (![0, 1] : Fin 2 → ℂ) ![0, 1] = 0 := by simp [cr]

lemma adjugate_eq_inv {X : M2} (h : X.det = 1) : X.adjugate = X⁻¹ := by
  rw [Matrix.inv_def, h]; simp

/-- **Stage 1**: all conditions hold for small perturbations, uniformly in `y`. -/
theorem stage1 {F A₀ : ℝ → M2} {l : ℝ → ℂ} {α₀ ρ₁ θ K : ℝ} (hFc : Continuous F)
    (hFp : Function.Periodic F 1) (hFd : ∀ y, (F y).det = 1) (hAc : Continuous A₀)
    (hAp : Function.Periodic A₀ 1) (hρ₁ : 1 < ρ₁) (hl : ∀ y, ρ₁ ≤ ‖l y‖) (hlK : ∀ y, ‖l y‖ < K)
    (hθ : 1 < θ * ρ₁ ^ 2) (hθ0 : 0 ≤ θ)
    (hD : ∀ y, (F (y + α₀))⁻¹ * A₀ y * F y = !![l y, 0; 0, (l y)⁻¹]) :
    ∃ η > 0, ∀ y α' : ℝ, ∀ E : Fin 6 → M2, |α' - α₀| < η → (∀ i, ‖E i‖ < η) →
      Conds θ K (condMap F A₀ y (α', E)).1 (condMap F A₀ y (α', E)).2.1
        (condMap F A₀ y (α', E)).2.2.1 (condMap F A₀ y (α', E)).2.2.2.1
        (condMap F A₀ y (α', E)).2.2.2.2.1 (condMap F A₀ y (α', E)).2.2.2.2.2.1
        (condMap F A₀ y (α', E)).2.2.2.2.2.2 := by
  set O := {t : M2 × M2 × M2 × ℂ × ℂ × ℂ × ℂ |
      Conds θ K t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2} with hO
  have hcont : Continuous (fun p : ℝ × (ℝ × (Fin 6 → M2)) => condMap F A₀ p.1 p.2) := by
    have hy : Continuous fun p : ℝ × (ℝ × (Fin 6 → M2)) => p.1 := continuous_fst
    have hα : Continuous fun p : ℝ × (ℝ × (Fin 6 → M2)) => p.2.1 :=
      continuous_fst.comp continuous_snd
    have hE : ∀ i, Continuous fun p : ℝ × (ℝ × (Fin 6 → M2)) => p.2.2 i := fun i =>
      (continuous_apply i).comp (continuous_snd.comp continuous_snd)
    have hF0 : Continuous fun p : ℝ × (ℝ × (Fin 6 → M2)) => F p.1 := hFc.comp hy
    have hF1 : Continuous fun p : ℝ × (ℝ × (Fin 6 → M2)) => F (p.1 + p.2.1) :=
      hFc.comp (hy.add hα)
    have hA : Continuous fun p : ℝ × (ℝ × (Fin 6 → M2)) => A₀ p.1 := hAc.comp hy
    have hcr : ∀ {u v : ℝ × (ℝ × (Fin 6 → M2)) → Fin 2 → ℂ}, Continuous u → Continuous v →
        Continuous fun p => cr (u p) (v p) := fun hu hv => continuous_cr.comp (hu.prodMk hv)
    unfold condMap
    refine Continuous.prodMk ?_ (Continuous.prodMk ?_ (Continuous.prodMk ?_
      (Continuous.prodMk ?_ (Continuous.prodMk ?_ (Continuous.prodMk ?_ ?_)))))
    · exact ((hF1.add (hE 2)).matrix_adjugate.mul (hA.add (hE 0))).mul (hF0.add (hE 1))
    · exact (hF0.add (hE 1)).matrix_adjugate.mul (hF0.add (hE 3))
    · exact (hF1.matrix_adjugate.mul (hA.add (hE 0))).mul hF0
    · exact hcr ((hA.add (hE 0)).matrix_mulVec ((hF0.add (hE 1)).matrix_mulVec continuous_const))
        ((hF1.add (hE 4)).matrix_mulVec continuous_const)
    · exact hcr ((hA.add (hE 0)).matrix_mulVec ((hF0.add (hE 1)).matrix_mulVec continuous_const))
        ((hF1.add (hE 4)).matrix_mulVec continuous_const)
    · exact hcr ((hF0.add (hE 1)).matrix_mulVec continuous_const)
        ((hF0.add (hE 5)).matrix_mulVec continuous_const)
    · exact hcr ((hF0.add (hE 1)).matrix_mulVec continuous_const)
        ((hF0.add (hE 5)).matrix_mulVec continuous_const)
  have hper : ∀ y z, condMap F A₀ (y + 1) z = condMap F A₀ y z := by
    intro y z
    unfold condMap
    rw [show y + 1 + z.1 = y + z.1 + 1 by ring, hFp, hFp, hAp]
  -- the model point
  have hmodel : ∀ y, condMap F A₀ y (α₀, 0) ∈ O := by
    intro y
    have hF1 := hFd (y + α₀)
    have hF0 := hFd y
    have hl0 : l y ≠ 0 := fun h => by have := hl y; rw [h, norm_zero] at this; linarith
    have hl1 : 1 < ‖l y‖ := hρ₁.trans_le (hl y)
    have hND : (F (y + α₀)).adjugate * A₀ y * F y = !![l y, 0; 0, (l y)⁻¹] := by
      rw [adjugate_eq_inv hF1]; exact hD y
    have hAF : A₀ y * F y = F (y + α₀) * !![l y, 0; 0, (l y)⁻¹] := by
      rw [← hND, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_adjugate, hF1, one_smul,
        Matrix.one_mul]
    have hlinv : ‖(l y)⁻¹‖ < 1 := by
      rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hl1
    have ha : cr (A₀ y *ᵥ (F y *ᵥ ![1, 0])) (F (y + α₀) *ᵥ ![0, 1]) = l y := by
      rw [Matrix.mulVec_mulVec, hAF, ← Matrix.mulVec_mulVec, cr_mulVec, hF1, one_mul]
      simp [cr, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have hb : cr (A₀ y *ᵥ (F y *ᵥ ![0, 1])) (F (y + α₀) *ᵥ ![0, 1]) = 0 := by
      rw [Matrix.mulVec_mulVec, hAF, ← Matrix.mulVec_mulVec, cr_mulVec, hF1, one_mul]
      simp [cr, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    have hc : cr (F y *ᵥ ![1, 0]) (F y *ᵥ ![0, 1]) = 1 := by
      rw [cr_mulVec, hF0, one_mul, cr_e0_e1]
    have hd : cr (F y *ᵥ ![0, 1]) (F y *ᵥ ![0, 1]) = 0 := by
      rw [cr_mulVec, cr_e1_e1, mul_zero]
    have hBm : (F y).adjugate * F y = 1 := by rw [Matrix.adjugate_mul, hF0, one_smul]
    have hdet : (!![l y, 0; 0, (l y)⁻¹] : M2).det = 1 := by
      rw [det_fin_two_of, mul_inv_cancel₀ hl0]; ring
    simp only [hO, mem_setOf_eq, condMap, Pi.zero_apply, add_zero]
    rw [hND, hBm, ha, hb, hc, hd]
    have e00 : (!![l y, 0; 0, (l y)⁻¹] : M2) 0 0 = l y := by simp
    have e01 : (!![l y, 0; 0, (l y)⁻¹] : M2) 0 1 = 0 := by simp
    have e10 : (!![l y, 0; 0, (l y)⁻¹] : M2) 1 0 = 0 := by simp
    have e11 : (!![l y, 0; 0, (l y)⁻¹] : M2) 1 1 = (l y)⁻¹ := by simp
    have hsq : 1 < θ * ‖l y‖ ^ 2 := by
      have : ρ₁ ^ 2 ≤ ‖l y‖ ^ 2 := pow_le_pow_left₀ (by linarith) (hl y) 2
      nlinarith
    have hl2 : 1 < ‖l y‖ ^ 2 := by nlinarith
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hlK y, ?_, ?_, ?_⟩
    · rw [e01, e10, e11, e00, norm_zero]; linarith
    · rw [hdet, norm_one, e00, e01, norm_zero, sub_zero]; exact hsq
    · rw [sub_self, norm_zero]; norm_num
    · rw [e01, e10, e11, e00, norm_zero]; linarith
    · rw [e01, e10, e11, e00, norm_zero]; linarith
    · rw [hdet, norm_one, e00, e01, norm_zero, mul_zero, sub_zero]; exact hl2
    · rw [hdet, norm_one, e00, e10, norm_zero, mul_zero, sub_zero]; exact hl2
    · rw [e00, e01, norm_zero]; linarith
    · linarith
    · rw [norm_zero]; norm_num
    · rw [sub_self, norm_zero]; norm_num
    · rw [norm_zero]; norm_num
  have hev := tube_periodic_set hcont hper (isOpen_conds θ K) hmodel
  obtain ⟨η, hη, hball⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨η, hη, fun y α' E hα hE => ?_⟩
  have hdist : dist (α', E) (α₀, (0 : Fin 6 → M2)) < η := by
    rw [Prod.dist_eq, max_lt_iff]
    refine ⟨by rw [Real.dist_eq]; exact hα, ?_⟩
    rw [dist_zero_right]
    exact (pi_norm_lt_iff hη).2 hE
  exact hball hdist y




/-! ### Entrywise analyticity / holomorphy -/

section AnM

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Entrywise real-analyticity of a matrix-valued map. -/
def AnM (f : E → M2) (x : E) : Prop := ∀ i j, AnalyticAt ℝ (fun y => f y i j) x

/-- Entrywise real-analyticity of a vector-valued map. -/
def AnV (f : E → Fin 2 → ℂ) (x : E) : Prop := ∀ i, AnalyticAt ℝ (fun y => f y i) x

lemma AnM.mul {f g : E → M2} {x : E} (hf : AnM f x) (hg : AnM g x) :
    AnM (fun y => f y * g y) x := by
  intro i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  exact ((hf i 0).mul (hg 0 j)).add ((hf i 1).mul (hg 1 j))

lemma AnM.const (M : M2) (x : E) : AnM (fun _ => M) x := fun _ _ => analyticAt_const

lemma AnM.pmat {M : ℕ → E → M2} {x : E} (h : ∀ j, AnM (M j) x) (n : ℕ) :
    AnM (fun y => pmat (fun j => M j y) n) x := by
  induction n with
  | zero => exact AnM.const 1 x
  | succ n ih => exact ih.mul (h (n + 1))

lemma AnM.mulVec {f : E → M2} {v : E → Fin 2 → ℂ} {x : E} (hf : AnM f x) (hv : AnV v x) :
    AnV (fun y => f y *ᵥ v y) x := by
  intro i
  have e : (fun y => (f y *ᵥ v y) i) = fun y => f y i 0 * v y 0 + f y i 1 * v y 1 := by
    funext y; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [e]
  exact ((hf i 0).mul (hv 0)).add ((hf i 1).mul (hv 1))

lemma AnV.const (v : Fin 2 → ℂ) (x : E) : AnV (fun _ => v) x := fun _ => analyticAt_const

lemma AnV.cr {u v : E → Fin 2 → ℂ} {x : E} (hu : AnV u x) (hv : AnV v x) :
    AnalyticAt ℝ (fun y => cr (u y) (v y)) x := by
  show AnalyticAt ℝ (fun y => u y 0 * v y 1 - u y 1 * v y 0) x
  exact ((hu 0).mul (hv 1)).sub ((hu 1).mul (hv 0))

lemma AnM.of_analyticAt {f : E → M2} {x : E} (hf : AnalyticAt ℝ f x) : AnM f x := by
  intro i j
  have := (((entryCLM i j).restrictScalars ℝ).analyticAt (f x)).comp hf
  exact this

lemma AnM.of_entire {Ft : ℂ → M2} (hFt : Differentiable ℂ Ft) {g : E → ℝ} {x : E}
    (hg : AnalyticAt ℝ g x) : AnM (fun y => Ft (g y : ℂ)) x := by
  intro i j
  have h1 : Differentiable ℂ (fun z => Ft z i j) := fun z =>
    ((entryCLM i j).differentiableAt).comp z (hFt z)
  have h2 : AnalyticAt ℝ (fun z => Ft z i j) (g x : ℂ) :=
    (h1.analyticAt (g x : ℂ)).restrictScalars
  have h3 : AnalyticAt ℝ (fun y => ((g y : ℝ) : ℂ)) x :=
    (Complex.ofRealCLM.analyticAt (g x)).comp hg
  exact h2.comp (f := fun y => ((g y : ℝ) : ℂ)) h3

end AnM

section DiM

variable {S : Set ℂ}

/-- Entrywise holomorphy. -/
def DiM (f : ℂ → M2) (S : Set ℂ) : Prop := ∀ i j, DifferentiableOn ℂ (fun t => f t i j) S

def DiV (f : ℂ → Fin 2 → ℂ) (S : Set ℂ) : Prop := ∀ i, DifferentiableOn ℂ (fun t => f t i) S

lemma DiM.mul {f g : ℂ → M2} (hf : DiM f S) (hg : DiM g S) : DiM (fun t => f t * g t) S := by
  intro i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  exact ((hf i 0).mul (hg 0 j)).add ((hf i 1).mul (hg 1 j))

lemma DiM.pmat {M : ℕ → ℂ → M2} {n : ℕ} (h : ∀ j, 1 ≤ j → j ≤ n → DiM (M j) S) :
    DiM (fun t => pmat (fun j => M j t) n) S := by
  induction n with
  | zero => intro i j; exact differentiableOn_const _
  | succ n ih =>
    exact (ih (fun j h1 h2 => h j h1 (by omega))).mul (h (n + 1) (by omega) le_rfl)

lemma DiM.mulVec {f : ℂ → M2} {v : ℂ → Fin 2 → ℂ} (hf : DiM f S) (hv : DiV v S) :
    DiV (fun t => f t *ᵥ v t) S := by
  intro i
  have e : (fun t => (f t *ᵥ v t) i) = fun t => f t i 0 * v t 0 + f t i 1 * v t 1 := by
    funext t; simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [e]
  exact ((hf i 0).mul (hv 0)).add ((hf i 1).mul (hv 1))

lemma DiV.const (v : Fin 2 → ℂ) : DiV (fun _ => v) S := fun _ => differentiableOn_const _

lemma DiV.cr {u v : ℂ → Fin 2 → ℂ} (hu : DiV u S) (hv : DiV v S) :
    DifferentiableOn ℂ (fun t => cr (u t) (v t)) S := by
  show DifferentiableOn ℂ (fun t => u t 0 * v t 1 - u t 1 * v t 0) S
  exact ((hu 0).mul (hv 1)).sub ((hu 1).mul (hv 0))

lemma DiM.of_diff {f : ℂ → M2} (hf : DifferentiableOn ℂ f S) : DiM f S := by
  intro i j
  exact ((entryCLM i j).differentiable.comp_differentiableOn hf)

lemma DiM.of_entire {Ft : ℂ → M2} (hFt : Differentiable ℂ Ft) (z₀ c : ℂ) :
    DiM (fun t => Ft (z₀ + t * c)) S :=
  DiM.of_diff (hFt.comp ((differentiable_const _).add (differentiable_id.mul
    (differentiable_const _)))).differentiableOn

end DiM

lemma Rv_an {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {M0 : E → M2}
    {v W W₀ : E → Fin 2 → ℂ} {x : E} (hM : AnM M0 x) (hv : AnV v x) (hW : AnV W x)
    (hW₀ : AnV W₀ x) (h0 : cr (v x) (W₀ x) ≠ 0) :
    AnalyticAt ℝ (fun y => Rv (M0 y) (v y) (W y) (W₀ y)) x :=
  ((hM.mulVec hv).cr hW).div (hv.cr hW₀) h0

lemma Rv_di {S : Set ℂ} {M0 : ℂ → M2} {v W W₀ : ℂ → Fin 2 → ℂ} (hM : DiM M0 S) (hv : DiV v S)
    (hW : DiV W S) (hW₀ : DiV W₀ S) (h0 : ∀ t ∈ S, cr (v t) (W₀ t) ≠ 0) :
    DifferentiableOn ℂ (fun t => Rv (M0 t) (v t) (W t) (W₀ t)) S :=
  ((hM.mulVec hv).cr hW).div (hv.cr hW₀) h0



/-- Shorthand: the conditions hold at `y` for `(α', E)`. -/
def CondsAt (θ K : ℝ) (F A₀ : ℝ → M2) (y α' : ℝ) (E : Fin 6 → M2) : Prop :=
  Conds θ K (condMap F A₀ y (α', E)).1 (condMap F A₀ y (α', E)).2.1
    (condMap F A₀ y (α', E)).2.2.1 (condMap F A₀ y (α', E)).2.2.2.1
    (condMap F A₀ y (α', E)).2.2.2.2.1 (condMap F A₀ y (α', E)).2.2.2.2.2.1
    (condMap F A₀ y (α', E)).2.2.2.2.2.2

/-! ### Small lemmas -/

lemma pmat_congr {M M' : ℕ → M2} {n : ℕ} (h : ∀ j, 1 ≤ j → j ≤ n → M j = M' j) :
    pmat M n = pmat M' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [pmat]
    rw [ih (fun j h1 h2 => h j h1 (by omega)), h (n + 1) (by omega) le_rfl]

lemma one_le_norm_neg_one : 1 ≤ ‖(-1 : M2)‖ := by
  have := DerivFormulaAux.entry_le_norm (-1 : M2) 0 0
  simpa using this

lemma det_ne_zero_of_near {X : M2} (h : ‖X.adjugate * X - 1‖ < 1 / 8) : X.det ≠ 0 := by
  intro h0
  rw [Matrix.adjugate_mul, h0, zero_smul, zero_sub] at h
  linarith [one_le_norm_neg_one]

lemma cone_of_near_one {B : M2} (hB : ‖B - 1‖ < 1 / 8) {v : Fin 2 → ℂ} (hv0 : v 0 = 1)
    (hv1 : ‖v 1‖ ≤ 1 / 2) : InCone (B *ᵥ v) := by
  have hv : ‖v‖ ≤ 1 := by
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 (fun i => ?_)
    fin_cases i
    · simp [hv0]
    · simp only [Fin.mk_one]; linarith
  have he : B *ᵥ v = v + (B - 1) *ᵥ v := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  have herr : ‖(B - 1) *ᵥ v‖ ≤ 1 / 8 :=
    (Matrix.linfty_opNorm_mulVec _ _).trans
      (by nlinarith [norm_nonneg (B - 1), norm_nonneg v])
  have h0 : ‖((B - 1) *ᵥ v) 0‖ ≤ 1 / 8 := (norm_le_pi_norm _ 0).trans herr
  have h1 : ‖((B - 1) *ᵥ v) 1‖ ≤ 1 / 8 := (norm_le_pi_norm _ 1).trans herr
  have a0 : 7 / 8 ≤ ‖1 + ((B - 1) *ᵥ v) 0‖ := by
    have := norm_add_ge (1 : ℂ) (((B - 1) *ᵥ v) 0)
    rw [norm_one] at this; linarith
  have a1 : ‖v 1 + ((B - 1) *ᵥ v) 1‖ ≤ 5 / 8 :=
    (norm_add_le _ _).trans (by linarith)
  rw [he]
  refine ⟨?_, fun h => ?_⟩
  · show ‖v 1 + ((B - 1) *ᵥ v) 1‖ ≤ ‖v 0 + ((B - 1) *ᵥ v) 0‖
    rw [hv0]; linarith
  · change v 0 + ((B - 1) *ᵥ v) 0 = 0 at h
    rw [hv0] at h
    rw [h, norm_zero] at a0; linarith

lemma cr_frame_ne {X : M2} {W₀ : Fin 2 → ℂ} {κ : ℂ} (hκ : κ ≠ 0) {v U : Fin 2 → ℂ}
    (hv : κ • v = X *ᵥ U) (hU : U 0 ≠ 0)
    (hden : cr (X *ᵥ ![1, 0]) W₀ + cr (X *ᵥ ![0, 1]) W₀ * ph U ≠ 0) : cr v W₀ ≠ 0 := by
  intro h0
  have h1 : cr (κ • v) W₀ = 0 := by rw [cr_smul_left, h0, mul_zero]
  have hU' : U = U 0 • ![1, 0] + U 1 • ![0, 1] := by
    ext i; fin_cases i <;> simp
  rw [hv, hU', Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul] at h1
  have e : cr (U 0 • (X *ᵥ ![1, 0]) + U 1 • (X *ᵥ ![0, 1])) W₀ =
      U 0 * (cr (X *ᵥ ![1, 0]) W₀ + cr (X *ᵥ ![0, 1]) W₀ * ph U) := by
    simp only [cr, ph, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp
    ring
  rw [e] at h1
  exact mul_ne_zero hU hden h1

/-! ### The approximants -/

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- Real chain matrices `A_p(x - jα)`. -/
def Mr (A : P → ℂ → M2) (q : (ℝ × P) × ℝ) (j : ℕ) : M2 :=
  A q.1.2 (((q.2 - j * q.1.1 : ℝ)) : ℂ)

/-- `v_n = A_p(x-α) ⋯ A_p(x-nα) e(x - nα)`. -/
def vr (A : P → ℂ → M2) (Ft : ℂ → M2) (n : ℕ) (q : (ℝ × P) × ℝ) : Fin 2 → ℂ :=
  pmat (Mr A q) n *ᵥ (Ft ((q.2 - n * q.1.1 : ℝ) : ℂ) *ᵥ ![1, 0])

/-- The approximate multiplier. -/
def Rr (A : P → ℂ → M2) (Ft : ℂ → M2) (n : ℕ) (q : (ℝ × P) × ℝ) : ℂ :=
  Rv (Mr A q 0) (vr A Ft n q) (Ft ((q.2 + q.1.1 : ℝ) : ℂ) *ᵥ ![0, 1])
    (Ft ((q.2 : ℝ) : ℂ) *ᵥ ![0, 1])

/-- Complexified chain matrices along the line `q + t h`. -/
def Ml (Ext : P → ℝ → P → ℂ → ℂ → M2) (q h : (ℝ × P) × ℝ) (j : ℕ) (t : ℂ) : M2 :=
  Ext q.1.2 (q.2 - j * q.1.1) h.1.2 (((h.2 - j * h.1.1 : ℝ)) : ℂ) t

def El (Ft : ℂ → M2) (q h : (ℝ × P) × ℝ) (n : ℕ) (t : ℂ) : M2 :=
  Ft (((q.2 - n * q.1.1 : ℝ) : ℂ) + t * ((h.2 - n * h.1.1 : ℝ) : ℂ))

def vl (Ext : P → ℝ → P → ℂ → ℂ → M2) (Ft : ℂ → M2) (n : ℕ) (q h : (ℝ × P) × ℝ) (t : ℂ) :
    Fin 2 → ℂ :=
  pmat (fun j => Ml Ext q h j t) n *ᵥ (El Ft q h n t *ᵥ ![1, 0])

def Wl (Ft : ℂ → M2) (q h : (ℝ × P) × ℝ) (t : ℂ) : Fin 2 → ℂ :=
  Ft (((q.2 + q.1.1 : ℝ) : ℂ) + t * ((h.2 + h.1.1 : ℝ) : ℂ)) *ᵥ ![0, 1]

def W0l (Ft : ℂ → M2) (q h : (ℝ × P) × ℝ) (t : ℂ) : Fin 2 → ℂ :=
  Ft (((q.2 : ℝ) : ℂ) + t * ((h.2 : ℝ) : ℂ)) *ᵥ ![0, 1]

def Rl (Ext : P → ℝ → P → ℂ → ℂ → M2) (Ft : ℂ → M2) (n : ℕ) (q h : (ℝ × P) × ℝ) (t : ℂ) : ℂ :=
  Rv (Ml Ext q h 0 t) (vl Ext Ft n q h t) (Wl Ft q h t) (W0l Ft q h t)

lemma norm_dir2 {h : (ℝ × P) × ℝ} (hh : ‖h‖ ≤ 1) (j : ℕ) :
    ‖(((h.2 - j * h.1.1 : ℝ)) : ℂ)‖ ≤ j + 1 := by
  have h2 : |h.2| ≤ 1 := by
    have := (norm_snd_le h).trans hh; rwa [Real.norm_eq_abs] at this
  have h3 : |h.1.1| ≤ 1 := by
    have := (norm_fst_le h.1).trans ((norm_fst_le h).trans hh); rwa [Real.norm_eq_abs] at this
  rw [Complex.norm_real, Real.norm_eq_abs]
  calc |h.2 - j * h.1.1| ≤ |h.2| + |j * h.1.1| := abs_sub _ _
    _ = |h.2| + j * |h.1.1| := by rw [abs_mul, Nat.abs_cast]
    _ ≤ 1 + j * 1 := by gcongr
    _ = j + 1 := by ring

lemma norm_dir_le {h : (ℝ × P) × ℝ} (hh : ‖h‖ ≤ 1) (j : ℕ) :
    1 + ‖h.1.2‖ + ‖(((h.2 - j * h.1.1 : ℝ)) : ℂ)‖ ≤ j + 3 := by
  have h1 : ‖h.1.2‖ ≤ 1 := (norm_snd_le h.1).trans ((norm_fst_le h).trans hh)
  have h2 : |h.2| ≤ 1 := by
    have := (norm_snd_le h).trans hh; rwa [Real.norm_eq_abs] at this
  have h3 : |h.1.1| ≤ 1 := by
    have := (norm_fst_le h.1).trans ((norm_fst_le h).trans hh); rwa [Real.norm_eq_abs] at this
  rw [Complex.norm_real, Real.norm_eq_abs]
  have : |h.2 - j * h.1.1| ≤ 1 + j := by
    calc |h.2 - j * h.1.1| ≤ |h.2| + |j * h.1.1| := abs_sub _ _
      _ = |h.2| + j * |h.1.1| := by rw [abs_mul, Nat.abs_cast]
      _ ≤ 1 + j * 1 := by gcongr
      _ = 1 + j := by ring
  linarith

/-- On real points of the line, the complexified approximant is the real one. -/
lemma Rl_real {A : P → ℂ → M2} {Ext : P → ℝ → P → ℂ → ℂ → M2} {Ft : ℂ → M2} {p₀ : P} {ρ : ℝ}
    (hρ : 0 < ρ)
    (hExt : ∀ p ∈ ball p₀ ρ, ∀ (y : ℝ) (b : P) (c : ℂ) (s : ℝ),
      |s| < ρ / (1 + ‖b‖ + ‖c‖) → Ext p y b c s = A (p + s • b) ((y : ℂ) + s * c))
    {q h : (ℝ × P) × ℝ} (hq : q.1.2 ∈ ball p₀ ρ) (hh : ‖h‖ ≤ 1) {n : ℕ} {s : ℝ}
    (hs : |s| < ρ / (n + 3)) :
    Rl Ext Ft n q h s = Rr A Ft n (q + s • h) := by
  have hM : ∀ j, j ≤ n → Ml Ext q h j s = Mr A (q + s • h) j := by
    intro j hj
    unfold Ml Mr
    rw [hExt _ hq _ _ _ _ ?_]
    · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      congr 1
      push_cast; ring
    · refine hs.trans_le (div_le_div_of_nonneg_left hρ.le (by positivity) ?_)
      have := norm_dir_le hh j
      have : (j : ℝ) ≤ n := by exact_mod_cast hj
      linarith
  unfold Rl Rr vl vr El Wl W0l
  rw [hM 0 (Nat.zero_le _), pmat_congr (M := fun j => Ml Ext q h j s)
    (fun j _ h2 => hM j h2)]
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  congr 3 <;> push_cast <;> ring_nf

/-! ### The main perturbative estimate -/

section Est

variable {A : P → ℂ → M2} {Ext : P → ℝ → P → ℂ → ℂ → M2} {Ft : ℂ → M2} {F A₀ : ℝ → M2}
  {p₀ : P} {α₀ θ K η ρ MA δ₁ τ τ₀ : ℝ}

/-- All frame data for the line through `q` in direction `h`, at the complex time `t`. -/
theorem line_est (hθ0 : 0 ≤ θ)
    (hcond : ∀ y α' (E : Fin 6 → M2), |α' - α₀| < η → (∀ i, ‖E i‖ < η) →
      CondsAt θ K F A₀ y α' E)
    (hFt : ∀ y : ℝ, ‖Ft y - F y‖ < η / 2)
    (hFtζ : ∀ (y : ℝ) (ζ : ℂ), ‖ζ‖ < τ₀ → ‖Ft (y + ζ) - Ft y‖ < η / 2)
    (hExtB : ∀ p ∈ ball p₀ ρ, ∀ (y : ℝ) (b : P) (c : ℂ), ∀ t ∈ ball (0 : ℂ) (ρ / (1 + ‖b‖ + ‖c‖)),
      ‖Ext p y b c t - A p y‖ ≤ 2 * MA * (1 + ‖b‖ + ‖c‖) / ρ * ‖t‖)
    (hAp : ∀ p ∈ ball p₀ δ₁, ∀ y : ℝ, ‖A p y - A₀ y‖ < η / 2)
    (hMA : 0 ≤ MA) (hρ : 0 < ρ) (hδη : δ₁ ≤ η) (hδρ : δ₁ ≤ ρ) (hτ0 : 0 < τ) (hτρ : τ ≤ ρ)
    (hτ : 2 * MA * τ / ρ < η / 2) (hττ₀ : τ ≤ τ₀)
    {q h : (ℝ × P) × ℝ} (hq : q.1 ∈ ball (α₀, p₀) δ₁) (hh : ‖h‖ ≤ 1) {t : ℂ} :
    (∀ n : ℕ, ‖t‖ < τ / (n + 3) → cr (vl Ext Ft n q h t) (W0l Ft q h t) ≠ 0 ∧
        Rl Ext Ft n q h t ≠ 0) ∧
      (∀ n : ℕ, ‖t‖ < τ / (n + 4) →
        ‖Rl Ext Ft (n + 1) q h t / Rl Ext Ft n q h t - 1‖ ≤ 8 * K * θ ^ n) := by
  have hqd : dist q.1 (α₀, p₀) < δ₁ := hq
  rw [Prod.dist_eq, max_lt_iff] at hqd
  have hα : |q.1.1 - α₀| < δ₁ := by rw [← Real.dist_eq]; exact hqd.1
  have hp : q.1.2 ∈ ball p₀ δ₁ := hqd.2
  have hpρ : q.1.2 ∈ ball p₀ ρ := ball_subset_ball hδρ hp
  have hαη : |q.1.1 - α₀| < η := hα.trans_le hδη
  have hη : 0 < η := by
    have := hFt 0
    linarith [norm_nonneg (Ft ((0 : ℝ) : ℂ) - F 0)]
  have hh1 : |h.1.1| ≤ 1 := by
    have := (norm_fst_le h.1).trans ((norm_fst_le h).trans hh); rwa [Real.norm_eq_abs] at this
  have hh2 : |h.2| ≤ 1 := by
    have := (norm_snd_le h).trans hh; rwa [Real.norm_eq_abs] at this
  set y : ℕ → ℝ := fun j => q.2 - j * q.1.1 with hy
  set X : ℕ → M2 := fun j => Ft ((y j : ℝ) : ℂ) with hX
  have hXF : ∀ j, ‖X j - F (y j)‖ < η / 2 := fun j => hFt _
  -- the perturbation of the chain matrices
  have hMl : ∀ (m j : ℕ), j ≤ m → ‖t‖ < τ / (m + 3) → ‖Ml Ext q h j t - A₀ (y j)‖ < η := by
    intro m j hj ht
    have hlam := norm_dir_le hh j
    have hlampos : 0 < 1 + ‖h.1.2‖ + ‖(((h.2 - j * h.1.1 : ℝ)) : ℂ)‖ := by positivity
    have hjm : (j : ℝ) ≤ m := by exact_mod_cast hj
    have ht' : t ∈ ball (0 : ℂ) (ρ / (1 + ‖h.1.2‖ + ‖(((h.2 - j * h.1.1 : ℝ)) : ℂ)‖)) := by
      rw [mem_ball_zero_iff]
      calc ‖t‖ < τ / (m + 3) := ht
        _ ≤ ρ / (m + 3) := by gcongr
        _ ≤ ρ / (1 + ‖h.1.2‖ + ‖(((h.2 - j * h.1.1 : ℝ)) : ℂ)‖) :=
          div_le_div_of_nonneg_left hρ.le hlampos (by linarith)
    have h1 := hExtB q.1.2 hpρ (y j) h.1.2 _ t ht'
    have h1' : ‖Ml Ext q h j t - A q.1.2 ((y j : ℝ) : ℂ)‖ < η / 2 := by
      refine h1.trans_lt ?_
      have hA1 : 2 * MA * (1 + ‖h.1.2‖ + ‖(((h.2 - j * h.1.1 : ℝ)) : ℂ)‖) / ρ ≤
          2 * MA * (m + 3) / ρ := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hρ.le
      calc 2 * MA * (1 + ‖h.1.2‖ + ‖(((h.2 - j * h.1.1 : ℝ)) : ℂ)‖) / ρ * ‖t‖
          ≤ 2 * MA * (m + 3) / ρ * (τ / (m + 3)) :=
            mul_le_mul hA1 ht.le (norm_nonneg _) (by positivity)
        _ = 2 * MA * τ / ρ := by field_simp
        _ < η / 2 := hτ
    have h2 := hAp q.1.2 hp (y j)
    calc ‖Ml Ext q h j t - A₀ (y j)‖
        = ‖(Ml Ext q h j t - A q.1.2 ((y j : ℝ) : ℂ)) + (A q.1.2 ((y j : ℝ) : ℂ) - A₀ (y j))‖ := by
          congr 1; abel
      _ ≤ _ := norm_add_le _ _
      _ < η / 2 + η / 2 := add_lt_add h1' h2
      _ = η := by ring
  -- one-step cone conditions
  have hgood : ∀ (m j : ℕ), 1 ≤ j → j ≤ m → ‖t‖ < τ / (m + 3) →
      Good θ ((X (j - 1)).adjugate * Ml Ext q h j t * X j) := by
    intro m j hj1 hjm ht
    have hXj1 : X (j - 1) = Ft (((y j + q.1.1 : ℝ)) : ℂ) := by
      simp only [hX, hy]; congr 2; rw [Nat.cast_sub hj1]; push_cast; ring
    set E : Fin 6 → M2 := ![Ml Ext q h j t - A₀ (y j), X j - F (y j),
      X (j - 1) - F (y j + q.1.1), 0, 0, 0] with hE
    have hEb : ∀ i, ‖E i‖ < η := by
      intro i; fin_cases i
      · exact hMl m j hjm ht
      · exact (hXF j).trans (by linarith)
      · show ‖X (j - 1) - F (y j + q.1.1)‖ < η
        rw [hXj1]; exact (hFt _).trans (by linarith)
      all_goals simp [hE, hη]
    have hc := hcond (y j) q.1.1 E hαη hEb
    have hN : (condMap F A₀ (y j) (q.1.1, E)).1 = (X (j - 1)).adjugate * Ml Ext q h j t * X j := by
      simp [condMap, E]
    have g1 := hc.good1
    have g2 := hc.good2
    rw [hN] at g1 g2
    exact ⟨g1, g2.le⟩
  -- determinants
  have hdet : ∀ j, (X j).det ≠ 0 := by
    intro j
    set E : Fin 6 → M2 := ![0, X j - F (y j), 0, X j - F (y j), 0, 0] with hE
    have hEb : ∀ i, ‖E i‖ < η := by
      intro i; fin_cases i
      all_goals first | simp [hE, hη]; done | exact (hXF j).trans (by linarith)
    have hc := (hcond (y j) q.1.1 E hαη hEb).bm
    have hB : (condMap F A₀ (y j) (q.1.1, E)).2.1 = (X j).adjugate * X j := by
      simp [condMap, E]
    rw [hB] at hc
    exact det_ne_zero_of_near hc
  -- initial vectors
  have hinit : ∀ m : ℕ, ‖t‖ < τ / (m + 3) →
      InCone ((X m).adjugate *ᵥ (El Ft q h m t *ᵥ ![1, 0])) := by
    intro m ht
    have hζ : ‖t * (((h.2 - m * h.1.1 : ℝ)) : ℂ)‖ < τ₀ := by
      have hlam := norm_dir_le hh m
      rw [norm_mul]
      have hb : ‖(((h.2 - m * h.1.1 : ℝ)) : ℂ)‖ ≤ m + 1 := by
        have := norm_dir2 hh m; linarith
      calc ‖t‖ * ‖(((h.2 - m * h.1.1 : ℝ)) : ℂ)‖ ≤ τ / (m + 3) * (m + 1) :=
            mul_le_mul ht.le hb (norm_nonneg _) (by positivity)
        _ < τ := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]; nlinarith
        _ ≤ τ₀ := hττ₀
    set E : Fin 6 → M2 := ![0, X m - F (y m), 0, El Ft q h m t - F (y m), 0, 0] with hE
    have hEb : ∀ i, ‖E i‖ < η := by
      intro i; fin_cases i
      · simp [hE, hη]
      · exact (hXF m).trans (by linarith)
      · simp [hE, hη]
      · show ‖El Ft q h m t - F (y m)‖ < η
        have e1 : El Ft q h m t - F (y m) = (Ft (((y m : ℝ) : ℂ) + t * (((h.2 - m * h.1.1 : ℝ)) : ℂ))
            - Ft ((y m : ℝ) : ℂ)) + (Ft ((y m : ℝ) : ℂ) - F (y m)) := by
          simp only [El, hy]; abel
        rw [e1]
        calc _ ≤ _ := norm_add_le _ _
          _ < η / 2 + η / 2 := add_lt_add (hFtζ _ _ hζ) (hFt _)
          _ = η := by ring
      all_goals simp [hE, hη]
    have hc := (hcond (y m) q.1.1 E hαη hEb).bm
    have hB : (condMap F A₀ (y m) (q.1.1, E)).2.1 = (X m).adjugate * El Ft q h m t := by
      simp [condMap, E]
    rw [hB] at hc
    rw [Matrix.mulVec_mulVec]
    exact cone_of_near_one hc (by simp) (by simp)
  -- the coefficients of the multiplier
  have hX0 : X 0 = Ft ((q.2 : ℝ) : ℂ) := by simp [hX, hy]
  have hcoef : ‖t‖ < τ / 3 →
      CondsAt θ K F A₀ q.2 q.1.1 ![Ml Ext q h 0 t - A₀ q.2, X 0 - F q.2, 0, 0,
        Ft (((q.2 + q.1.1 : ℝ) : ℂ) + t * ((h.2 + h.1.1 : ℝ) : ℂ)) - F (q.2 + q.1.1),
        Ft (((q.2 : ℝ) : ℂ) + t * ((h.2 : ℝ) : ℂ)) - F q.2] := by
    intro ht
    have ht3 : ‖t‖ < τ / ((0 : ℕ) + 3) := by simpa using ht
    refine hcond _ _ _ hαη (fun i => ?_)
    fin_cases i
    · have := hMl 0 0 le_rfl ht3
      simpa [hy] using this
    · rw [hX0] at *; simpa using (hFt q.2).trans (by linarith)
    · simpa using hη
    · simpa using hη
    · show ‖Ft (((q.2 + q.1.1 : ℝ) : ℂ) + t * ((h.2 + h.1.1 : ℝ) : ℂ)) - F (q.2 + q.1.1)‖ < η
      have hz : ‖t * ((h.2 + h.1.1 : ℝ) : ℂ)‖ < τ₀ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have : |h.2 + h.1.1| ≤ 2 := (abs_add_le _ _).trans (by linarith)
        calc ‖t‖ * |h.2 + h.1.1| ≤ τ / 3 * 2 := mul_le_mul ht.le this (abs_nonneg _) (by positivity)
          _ < τ := by linarith
          _ ≤ τ₀ := hττ₀
      calc _ = ‖(Ft (((q.2 + q.1.1 : ℝ) : ℂ) + t * ((h.2 + h.1.1 : ℝ) : ℂ)) -
            Ft ((q.2 + q.1.1 : ℝ) : ℂ)) + (Ft ((q.2 + q.1.1 : ℝ) : ℂ) - F (q.2 + q.1.1))‖ := by
            congr 1; abel
        _ ≤ _ := norm_add_le _ _
        _ < η / 2 + η / 2 := add_lt_add (hFtζ _ _ hz) (hFt _)
        _ = η := by ring
    · show ‖Ft (((q.2 : ℝ) : ℂ) + t * ((h.2 : ℝ) : ℂ)) - F q.2‖ < η
      have hz : ‖t * ((h.2 : ℝ) : ℂ)‖ < τ₀ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        calc ‖t‖ * |h.2| ≤ τ / 3 * 1 := mul_le_mul ht.le hh2 (abs_nonneg _) (by positivity)
          _ < τ := by linarith
          _ ≤ τ₀ := hττ₀
      calc _ = ‖(Ft (((q.2 : ℝ) : ℂ) + t * ((h.2 : ℝ) : ℂ)) - Ft ((q.2 : ℝ) : ℂ)) +
            (Ft ((q.2 : ℝ) : ℂ) - F q.2)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
        _ < η / 2 + η / 2 := add_lt_add (hFtζ _ _ hz) (hFt _)
        _ = η := by ring
  -- the coefficients
  set a := cr (Ml Ext q h 0 t *ᵥ (X 0 *ᵥ ![1, 0])) (Wl Ft q h t) with ha
  set b := cr (Ml Ext q h 0 t *ᵥ (X 0 *ᵥ ![0, 1])) (Wl Ft q h t) with hb
  set c := cr (X 0 *ᵥ ![1, 0]) (W0l Ft q h t) with hc
  set d := cr (X 0 *ᵥ ![0, 1]) (W0l Ft q h t) with hd
  have hcoef' : ‖t‖ < τ / 3 → 3 / 4 < ‖a‖ ∧ ‖a‖ < K ∧ ‖b‖ < 1 / 4 ∧ ‖c - 1‖ < 1 / 4 ∧
      ‖d‖ < 1 / 4 := by
    intro ht
    have H := hcoef ht
    have e : (condMap F A₀ q.2 (q.1.1, ![Ml Ext q h 0 t - A₀ q.2, X 0 - F q.2, 0, 0,
        Ft (((q.2 + q.1.1 : ℝ) : ℂ) + t * ((h.2 + h.1.1 : ℝ) : ℂ)) - F (q.2 + q.1.1),
        Ft (((q.2 : ℝ) : ℂ) + t * ((h.2 : ℝ) : ℂ)) - F q.2])).2.2.2 = (a, b, c, d) := by
      simp [condMap, ha, hb, hc, hd, Wl, W0l]
    have h1 := H.ca; have h2 := H.ca'; have h3 := H.cb; have h4 := H.cc; have h5 := H.cd
    simp only [e] at h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  -- frame identity
  set U : ℕ → Fin 2 → ℂ := fun n =>
    pmat (fun j => (X (j - 1)).adjugate * Ml Ext q h j t * X j) n *ᵥ
      ((X n).adjugate *ᵥ (El Ft q h n t *ᵥ ![1, 0])) with hU
  have hκ : ∀ n : ℕ, (∏ j ∈ Finset.range (n + 1), (X j).det) ≠ 0 := fun n =>
    Finset.prod_ne_zero_iff.2 (fun j _ => hdet j)
  have hframe : ∀ n : ℕ, (∏ j ∈ Finset.range (n + 1), (X j).det) • vl Ext Ft n q h t =
      X 0 *ᵥ U n := fun n => proj_identity X (fun j => Ml Ext q h j t) n _
  have hUc : ∀ n : ℕ, ‖t‖ < τ / (n + 3) → InCone (U n) := fun n ht =>
    (chain hθ0 n (fun j h1 h2 => hgood n j h1 h2 ht) _ _ (hinit n ht) (hinit n ht)).1
  have h3 : ∀ n : ℕ, τ / (n + 3) ≤ τ / 3 := fun n =>
    div_le_div_of_nonneg_left hτ0.le (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hR : ∀ n : ℕ, ‖t‖ < τ / (n + 3) →
      Rl Ext Ft n q h t = (a + b * ph (U n)) / (c + d * ph (U n)) := by
    intro n ht
    exact Rv_frame _ _ _ _ (hκ n) (hframe n) (hUc n ht).2
  refine ⟨fun n ht => ?_, fun n ht => ?_⟩
  · obtain ⟨ha1, ha2, hb1, hc1, hd1⟩ := hcoef' (ht.trans_le (h3 n))
    have hφ := (hUc n ht).norm_ph_le
    have hrf := rf_est (φ := ph (U n)) (φ' := ph (U n)) hc1 hd1 ha1 ha2 hb1 hφ hφ
    refine ⟨cr_frame_ne (hκ n) (hframe n) (hUc n ht).2 hrf.2.1, ?_⟩
    rw [hR n ht]; exact hrf.1
  · have ht3 : ‖t‖ < τ / (n + 3) :=
      ht.trans_le (div_le_div_of_nonneg_left hτ0.le (by positivity) (by linarith))
    have ht4 : ‖t‖ < τ / ((n + 1 : ℕ) + 3) := by push_cast; linarith [ht, show τ / (n + 4) = τ / (n + 1 + 3) by ring_nf]
    obtain ⟨ha1, ha2, hb1, hc1, hd1⟩ := hcoef' (ht3.trans_le (h3 n))
    have hK : 0 ≤ K := by linarith [norm_nonneg a]
    have hUn := hUc n ht3
    have hUn1 := hUc (n + 1) ht4
    -- `U (n+1) = pmat N n *ᵥ (N (n+1) *ᵥ w_{n+1})`
    have hgN := hgood (n + 1) (n + 1) le_add_self le_rfl ht4
    have hw1 := hinit (n + 1) ht4
    have hsplit : U (n + 1) = pmat (fun j => (X (j - 1)).adjugate * Ml Ext q h j t * X j) n *ᵥ
        (((X (n + 1 - 1)).adjugate * Ml Ext q h (n + 1) t * X (n + 1)) *ᵥ
          ((X (n + 1)).adjugate *ᵥ (El Ft q h (n + 1) t *ᵥ ![1, 0]))) := by
      rw [hU]; beta_reduce; rw [pmat, ← Matrix.mulVec_mulVec]
    have hch := chain hθ0 n (fun j h1 h2 => hgood n j h1 h2 ht3) _ _ (good_cone hgN hw1).1
      (hinit n ht3)
    have hdiff : ‖ph (U (n + 1)) - ph (U n)‖ ≤ θ ^ n * 2 := by
      rw [hsplit]
      refine hch.2.trans ?_
      gcongr
      calc _ ≤ ‖ph _‖ + ‖ph _‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := add_le_add (good_cone hgN hw1).1.norm_ph_le (hinit n ht3).norm_ph_le
        _ = 2 := by norm_num
    have hrf := rf_est (φ := ph (U (n + 1))) (φ' := ph (U n)) hc1 hd1 ha1 ha2 hb1
      hUn1.norm_ph_le hUn.norm_ph_le
    rw [hR (n + 1) (by exact_mod_cast ht4), hR n ht3]
    calc _ ≤ 4 * K * ‖ph (U (n + 1)) - ph (U n)‖ := hrf.2.2
      _ ≤ 4 * K * (θ ^ n * 2) := by gcongr
      _ = 8 * K * θ ^ n := by ring

end Est


/-! ### Consistency at real points -/

section Cons

variable {A : P → ℂ → M2} {Ext : P → ℝ → P → ℂ → ℂ → M2} {Ft : ℂ → M2} {p₀ : P} {ρ : ℝ}

lemma Ml_real (hρ : 0 < ρ)
    (hExt : ∀ p ∈ ball p₀ ρ, ∀ (y : ℝ) (b : P) (c : ℂ) (s : ℝ),
      |s| < ρ / (1 + ‖b‖ + ‖c‖) → Ext p y b c s = A (p + s • b) ((y : ℂ) + s * c))
    {q h : (ℝ × P) × ℝ} (hq : q.1.2 ∈ ball p₀ ρ) (hh : ‖h‖ ≤ 1) {n : ℕ} {s : ℝ}
    (hs : |s| < ρ / (n + 3)) {j : ℕ} (hj : j ≤ n) :
    Ml Ext q h j s = Mr A (q + s • h) j := by
  unfold Ml Mr
  rw [hExt _ hq _ _ _ _ ?_]
  · simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    congr 1
    push_cast; ring
  · refine hs.trans_le (div_le_div_of_nonneg_left hρ.le (by positivity) ?_)
    have := norm_dir_le hh j
    have : (j : ℝ) ≤ n := by exact_mod_cast hj
    linarith

lemma vl_real (hρ : 0 < ρ)
    (hExt : ∀ p ∈ ball p₀ ρ, ∀ (y : ℝ) (b : P) (c : ℂ) (s : ℝ),
      |s| < ρ / (1 + ‖b‖ + ‖c‖) → Ext p y b c s = A (p + s • b) ((y : ℂ) + s * c))
    {q h : (ℝ × P) × ℝ} (hq : q.1.2 ∈ ball p₀ ρ) (hh : ‖h‖ ≤ 1) {n : ℕ} {s : ℝ}
    (hs : |s| < ρ / (n + 3)) :
    vl Ext Ft n q h s = vr A Ft n (q + s • h) ∧
      W0l Ft q h s = Ft (((q + s • h).2 : ℝ) : ℂ) *ᵥ ![0, 1] := by
  constructor
  · unfold vl vr El
    rw [pmat_congr (M := fun j => Ml Ext q h j s) (fun j _ h2 => Ml_real hρ hExt hq hh hs h2)]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    congr 3
    push_cast; ring
  · unfold W0l
    simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    congr 2
    push_cast; ring

end Cons

/-! ### The real limit -/

section Real

variable {A : P → ℂ → M2} {Ext : P → ℝ → P → ℂ → ℂ → M2} {Ft : ℂ → M2} {F A₀ : ℝ → M2}
  {p₀ : P} {α₀ θ K η ρ MA δ₁ τ τ₀ : ℝ}

lemma pmat_invariant {M : ℕ → M2} {u : ℕ → Fin 2 → ℂ} {ℓ : ℕ → ℂ}
    (h : ∀ j, M (j + 1) *ᵥ u (j + 1) = ℓ (j + 1) • u j) (n : ℕ) :
    pmat M n *ᵥ u n = (∏ j ∈ Finset.range n, ℓ (j + 1)) • u 0 := by
  induction n with
  | zero => simp [pmat]
  | succ n ih =>
    rw [pmat, ← Matrix.mulVec_mulVec, h n, Matrix.mulVec_smul, ih, smul_smul,
      Finset.prod_range_succ, mul_comm]

/-- Convergence of the real approximants to the multiplier of the invariant section. -/
theorem real_conv (hθ0 : 0 ≤ θ)
    (hcond : ∀ y α' (E : Fin 6 → M2), |α' - α₀| < η → (∀ i, ‖E i‖ < η) →
      CondsAt θ K F A₀ y α' E)
    (hFt : ∀ y : ℝ, ‖Ft y - F y‖ < η / 2)
    (hAp : ∀ p ∈ ball p₀ δ₁, ∀ y : ℝ, ‖A p y - A₀ y‖ < η / 2) (hδη : δ₁ ≤ η)
    {q : (ℝ × P) × ℝ} (hq : q.1 ∈ ball (α₀, p₀) δ₁)
    {u : ℝ → Fin 2 → ℂ} {ℓ : ℝ → ℂ}
    (hinv : ∀ y : ℝ, A q.1.2 (y : ℂ) *ᵥ u y = ℓ y • u (y + q.1.1)) (hℓ : ∀ y, ℓ y ≠ 0)
    (hu : ∀ y, ∃ z : ℂ, ‖z‖ ≤ 1 / 2 ∧ u y = F y *ᵥ ![1, z]) :
    Rv (Mr A q 0) (u q.2) (Ft ((q.2 + q.1.1 : ℝ) : ℂ) *ᵥ ![0, 1]) (Ft ((q.2 : ℝ) : ℂ) *ᵥ ![0, 1])
        ≠ 0 ∧
      cr (u q.2) (Ft ((q.2 : ℝ) : ℂ) *ᵥ ![0, 1]) ≠ 0 ∧
      ∀ n : ℕ, Rr A Ft n q ≠ 0 ∧
        ‖Rr A Ft n q / Rv (Mr A q 0) (u q.2) (Ft ((q.2 + q.1.1 : ℝ) : ℂ) *ᵥ ![0, 1])
          (Ft ((q.2 : ℝ) : ℂ) *ᵥ ![0, 1]) - 1‖ ≤ 8 * K * θ ^ n := by
  have hqd : dist q.1 (α₀, p₀) < δ₁ := hq
  rw [Prod.dist_eq, max_lt_iff] at hqd
  have hα : |q.1.1 - α₀| < δ₁ := by rw [← Real.dist_eq]; exact hqd.1
  have hp : q.1.2 ∈ ball p₀ δ₁ := hqd.2
  have hαη : |q.1.1 - α₀| < η := hα.trans_le hδη
  have hη : 0 < η := by
    have := hFt 0
    linarith [norm_nonneg (Ft ((0 : ℝ) : ℂ) - F 0)]
  set y : ℕ → ℝ := fun j => q.2 - j * q.1.1 with hy
  set X : ℕ → M2 := fun j => Ft ((y j : ℝ) : ℂ) with hX
  have hXF : ∀ j, ‖X j - F (y j)‖ < η / 2 := fun j => hFt _
  have hMl : ∀ j, ‖Mr A q j - A₀ (y j)‖ < η := by
    intro j
    have := hAp q.1.2 hp (y j)
    exact this.trans (by linarith)
  have hgood : ∀ j, 1 ≤ j → Good θ ((X (j - 1)).adjugate * Mr A q j * X j) := by
    intro j hj1
    have hXj1 : X (j - 1) = Ft (((y j + q.1.1 : ℝ)) : ℂ) := by
      simp only [hX, hy]; congr 2; rw [Nat.cast_sub hj1]; push_cast; ring
    set E : Fin 6 → M2 := ![Mr A q j - A₀ (y j), X j - F (y j),
      X (j - 1) - F (y j + q.1.1), 0, 0, 0] with hE
    have hEb : ∀ i, ‖E i‖ < η := by
      intro i; fin_cases i
      · exact hMl j
      · exact (hXF j).trans (by linarith)
      · show ‖X (j - 1) - F (y j + q.1.1)‖ < η
        rw [hXj1]; exact (hFt _).trans (by linarith)
      all_goals simp [hE, hη]
    have hc := hcond (y j) q.1.1 E hαη hEb
    have hN : (condMap F A₀ (y j) (q.1.1, E)).1 = (X (j - 1)).adjugate * Mr A q j * X j := by
      simp [condMap, E]
    have g1 := hc.good1
    have g2 := hc.good2
    rw [hN] at g1 g2
    exact ⟨g1, g2.le⟩
  have hdet : ∀ j, (X j).det ≠ 0 := by
    intro j
    set E : Fin 6 → M2 := ![0, X j - F (y j), 0, X j - F (y j), 0, 0] with hE
    have hEb : ∀ i, ‖E i‖ < η := by
      intro i; fin_cases i
      all_goals first | simp [hE, hη]; done | exact (hXF j).trans (by linarith)
    have hc := (hcond (y j) q.1.1 E hαη hEb).bm
    have hB : (condMap F A₀ (y j) (q.1.1, E)).2.1 = (X j).adjugate * X j := by
      simp [condMap, E]
    rw [hB] at hc
    exact det_ne_zero_of_near hc
  have hnear : ∀ (j : ℕ) (v : Fin 2 → ℂ), v 0 = 1 → ‖v 1‖ ≤ 1 / 2 →
      InCone ((X j).adjugate *ᵥ (F (y j) *ᵥ v)) := by
    intro j v hv0 hv1
    set E : Fin 6 → M2 := ![0, X j - F (y j), 0, 0, 0, 0] with hE
    have hEb : ∀ i, ‖E i‖ < η := by
      intro i; fin_cases i
      all_goals first | simp [hE, hη]; done | exact (hXF j).trans (by linarith)
    have hc := (hcond (y j) q.1.1 E hαη hEb).bm
    have hB : (condMap F A₀ (y j) (q.1.1, E)).2.1 = (X j).adjugate * F (y j) := by
      simp [condMap, E]
    rw [hB] at hc
    rw [Matrix.mulVec_mulVec]
    exact cone_of_near_one hc hv0 hv1
  have hinitR : ∀ m, InCone ((X m).adjugate *ᵥ (Ft ((y m : ℝ) : ℂ) *ᵥ ![1, 0])) := by
    intro m
    set E : Fin 6 → M2 := ![0, X m - F (y m), 0, X m - F (y m), 0, 0] with hE
    have hEb : ∀ i, ‖E i‖ < η := by
      intro i; fin_cases i
      all_goals first | simp [hE, hη]; done | exact (hXF m).trans (by linarith)
    have hc := (hcond (y m) q.1.1 E hαη hEb).bm
    have hB : (condMap F A₀ (y m) (q.1.1, E)).2.1 = (X m).adjugate * Ft ((y m : ℝ) : ℂ) := by
      simp [condMap, E, hX]
    rw [hB] at hc
    rw [Matrix.mulVec_mulVec]
    exact cone_of_near_one hc (by simp) (by simp)
  -- coefficients
  have hX0 : X 0 = Ft ((q.2 : ℝ) : ℂ) := by simp [hX, hy]
  set a := cr (Mr A q 0 *ᵥ (X 0 *ᵥ ![1, 0])) (Ft ((q.2 + q.1.1 : ℝ) : ℂ) *ᵥ ![0, 1]) with ha
  set b := cr (Mr A q 0 *ᵥ (X 0 *ᵥ ![0, 1])) (Ft ((q.2 + q.1.1 : ℝ) : ℂ) *ᵥ ![0, 1]) with hb
  set c := cr (X 0 *ᵥ ![1, 0]) (Ft ((q.2 : ℝ) : ℂ) *ᵥ ![0, 1]) with hc
  set d := cr (X 0 *ᵥ ![0, 1]) (Ft ((q.2 : ℝ) : ℂ) *ᵥ ![0, 1]) with hd
  have hcoef : 3 / 4 < ‖a‖ ∧ ‖a‖ < K ∧ ‖b‖ < 1 / 4 ∧ ‖c - 1‖ < 1 / 4 ∧ ‖d‖ < 1 / 4 := by
    set E : Fin 6 → M2 := ![Mr A q 0 - A₀ q.2, X 0 - F q.2, 0, 0,
      Ft ((q.2 + q.1.1 : ℝ) : ℂ) - F (q.2 + q.1.1), Ft ((q.2 : ℝ) : ℂ) - F q.2] with hE
    have hEb : ∀ i, ‖E i‖ < η := by
      intro i; fin_cases i
      · rw [hE]; simpa [hy] using hMl 0
      · rw [hE]; simpa [hX0] using (hFt q.2).trans (by linarith)
      · simp [hE, hη]
      · simp [hE, hη]
      · rw [hE]; simpa using (hFt (q.2 + q.1.1)).trans (by linarith)
      · rw [hE]; simpa using (hFt q.2).trans (by linarith)
    have H := hcond q.2 q.1.1 E hαη hEb
    have e : (condMap F A₀ q.2 (q.1.1, E)).2.2.2 = (a, b, c, d) := by
      simp [condMap, ha, hb, hc, hd, E]
    have h1 := H.ca; have h2 := H.ca'; have h3 := H.cb; have h4 := H.cc; have h5 := H.cd
    simp only [e] at h1 h2 h3 h4 h5
    exact ⟨h1, h2, h3, h4, h5⟩
  obtain ⟨ha1, ha2, hb1, hc1, hd1⟩ := hcoef
  have hK : 0 ≤ K := by linarith [norm_nonneg a]
  set Np : ℕ → M2 := fun j => (X (j - 1)).adjugate * Mr A q j * X j with hNp
  -- the true section
  have huv : ∀ m, ∃ v : Fin 2 → ℂ, v 0 = 1 ∧ ‖v 1‖ ≤ 1 / 2 ∧ u (y m) = F (y m) *ᵥ v := by
    intro m
    obtain ⟨z, hz, hz'⟩ := hu (y m)
    exact ⟨![1, z], by simp, by simpa using hz, hz'⟩
  have hwu : ∀ m, InCone ((X m).adjugate *ᵥ u (y m)) := by
    intro m
    obtain ⟨v, hv0, hv1, hv⟩ := huv m
    rw [hv]; exact hnear m v hv0 hv1
  have hinv' : ∀ j, Mr A q (j + 1) *ᵥ u (y (j + 1)) = ℓ (y (j + 1)) • u (y j) := by
    intro j
    have := hinv (y (j + 1))
    have e : y (j + 1) + q.1.1 = y j := by simp only [hy]; push_cast; ring
    rw [e] at this
    simpa [Mr, hy] using this
  have hpinv := pmat_invariant (M := Mr A q) (u := fun j => u (y j)) (ℓ := fun j => ℓ (y j)) hinv'
  have hy0 : y 0 = q.2 := by simp [hy]
  set Uu : ℕ → Fin 2 → ℂ := fun n => pmat Np n *ᵥ ((X n).adjugate *ᵥ u (y n)) with hUu
  set Ur : ℕ → Fin 2 → ℂ := fun n => pmat Np n *ᵥ ((X n).adjugate *ᵥ (Ft ((y n : ℝ) : ℂ) *ᵥ ![1, 0]))
    with hUr
  have hcone : ∀ n, InCone (Uu n) ∧ InCone (Ur n) ∧ ‖ph (Ur n) - ph (Uu n)‖ ≤ θ ^ n * 2 := by
    intro n
    have hch := chain hθ0 n (fun j h1 _ => hgood j h1) _ _ (hinitR n) (hwu n)
    refine ⟨(chain hθ0 n (fun j h1 _ => hgood j h1) _ _ (hwu n) (hwu n)).1, hch.1, ?_⟩
    refine hch.2.trans ?_
    gcongr
    calc _ ≤ ‖ph _‖ + ‖ph _‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := add_le_add (hinitR n).norm_ph_le (hwu n).norm_ph_le
      _ = 2 := by norm_num
  have hκ : ∀ n : ℕ, (∏ j ∈ Finset.range (n + 1), (X j).det) ≠ 0 := fun n =>
    Finset.prod_ne_zero_iff.2 (fun j _ => hdet j)
  have hℓp : ∀ n : ℕ, (∏ j ∈ Finset.range n, ℓ (y (j + 1))) ≠ 0 := fun n =>
    Finset.prod_ne_zero_iff.2 (fun j _ => hℓ _)
  have hframeU : ∀ n : ℕ, ((∏ j ∈ Finset.range (n + 1), (X j).det) *
      (∏ j ∈ Finset.range n, ℓ (y (j + 1)))) • u q.2 = X 0 *ᵥ Uu n := by
    intro n
    have := proj_identity X (Mr A q) n (u (y n))
    rw [hpinv n] at this
    rw [mul_smul, ← hy0]
    exact this
  have hframeR : ∀ n : ℕ, (∏ j ∈ Finset.range (n + 1), (X j).det) • vr A Ft n q =
      X 0 *ᵥ Ur n := fun n => proj_identity X (Mr A q) n _
  have hRinf : ∀ n, Rv (Mr A q 0) (u q.2) (Ft ((q.2 + q.1.1 : ℝ) : ℂ) *ᵥ ![0, 1])
      (Ft ((q.2 : ℝ) : ℂ) *ᵥ ![0, 1]) = (a + b * ph (Uu n)) / (c + d * ph (Uu n)) := fun n =>
    Rv_frame _ _ _ _ (mul_ne_zero (hκ n) (hℓp n)) (hframeU n) (hcone n).1.2
  have hRr : ∀ n, Rr A Ft n q = (a + b * ph (Ur n)) / (c + d * ph (Ur n)) := fun n =>
    Rv_frame _ _ _ _ (hκ n) (hframeR n) (hcone n).2.1.2
  have hrf0 := rf_est (φ := ph (Uu 0)) (φ' := ph (Uu 0)) hc1 hd1 ha1 ha2 hb1
    (hcone 0).1.norm_ph_le (hcone 0).1.norm_ph_le
  refine ⟨by rw [hRinf 0]; exact hrf0.1, ?_, fun n => ⟨?_, ?_⟩⟩
  · exact cr_frame_ne (mul_ne_zero (hκ 0) (hℓp 0)) (hframeU 0) (hcone 0).1.2 hrf0.2.1
  · have hr := rf_est (φ := ph (Ur n)) (φ' := ph (Ur n)) hc1 hd1 ha1 ha2 hb1
      (hcone n).2.1.norm_ph_le (hcone n).2.1.norm_ph_le
    rw [hRr n]; exact hr.1
  · have hr := rf_est (φ := ph (Ur n)) (φ' := ph (Uu n)) hc1 hd1 ha1 ha2 hb1
      (hcone n).2.1.norm_ph_le (hcone n).1.norm_ph_le
    rw [hRr n, hRinf n]
    calc _ ≤ 4 * K * ‖ph (Ur n) - ph (Uu n)‖ := hr.2.2
      _ ≤ 4 * K * (θ ^ n * 2) := by gcongr; exact (hcone n).2.2
      _ = 8 * K * θ ^ n := by ring

end Real

/-! ### Smoothness of the limit -/

/-- The `k`-th term of the series. -/
def fterm (A : P → ℂ → M2) (Ft : ℂ → M2) (n₀ k : ℕ) (q : (ℝ × P) × ℝ) : ℝ :=
  (Complex.log (Rr A Ft (n₀ + k + 1) q / Rr A Ft (n₀ + k) q)).re

lemma mem_slit_of_near {z : ℂ} (h : ‖z - 1‖ ≤ 1 / 2) : z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff]; left
  have h1 := Complex.abs_re_le_norm (z - 1)
  rw [Complex.sub_re, Complex.one_re] at h1
  have := abs_le.1 (h1.trans h); linarith

lemma norm_log_le_of_near {z : ℂ} (h : ‖z - 1‖ ≤ 1 / 2) :
    ‖Complex.log z‖ ≤ 3 / 2 * ‖z - 1‖ := by
  have := Complex.norm_log_one_add_half_le_self h
  rwa [add_sub_cancel] at this

lemma mem_ball_snd' {a c : ℝ × P} {r : ℝ} (h : a ∈ ball c r) : a.2 ∈ ball c.2 r := by
  rw [mem_ball, Prod.dist_eq] at h; exact lt_of_le_of_lt (le_max_right _ _) h

lemma mem_ball_fst' {a c : ℝ × P} {r : ℝ} (h : a ∈ ball c r) : |a.1 - c.1| < r := by
  rw [mem_ball, Prod.dist_eq] at h; rw [← Real.dist_eq]; exact lt_of_le_of_lt (le_max_left _ _) h

section Smooth

variable {A : P → ℂ → M2} {Ext : P → ℝ → P → ℂ → ℂ → M2} {Ft : ℂ → M2} {F A₀ : ℝ → M2}
  {p₀ : P} {α₀ θ K η ρ MA δ₁ τ τ₀ : ℝ}

lemma Rl_diff (hFtd : Differentiable ℂ Ft) (hρ : 0 < ρ) (hτρ : τ ≤ ρ)
    (hExtD : ∀ p ∈ ball p₀ ρ, ∀ (y : ℝ) (b : P) (c : ℂ),
      DifferentiableOn ℂ (Ext p y b c) (ball 0 (ρ / (1 + ‖b‖ + ‖c‖))))
    {q h : (ℝ × P) × ℝ} (hq : q.1.2 ∈ ball p₀ ρ) (hh : ‖h‖ ≤ 1) (m : ℕ)
    (h0 : ∀ t ∈ ball (0 : ℂ) (τ / (m + 3)), cr (vl Ext Ft m q h t) (W0l Ft q h t) ≠ 0) :
    DifferentiableOn ℂ (Rl Ext Ft m q h) (ball 0 (τ / (m + 3))) := by
  have hMl : ∀ j, j ≤ m → DiM (fun t => Ml Ext q h j t) (ball 0 (τ / (m + 3))) := by
    intro j hj
    refine DiM.of_diff ((hExtD _ hq _ _ _).mono (ball_subset_ball ?_))
    have hlam := norm_dir_le hh j
    have : (j : ℝ) ≤ m := by exact_mod_cast hj
    calc τ / (m + 3) ≤ ρ / (m + 3) := by gcongr
      _ ≤ ρ / (1 + ‖h.1.2‖ + ‖(((h.2 - j * h.1.1 : ℝ)) : ℂ)‖) :=
        div_le_div_of_nonneg_left hρ.le (by positivity) (by linarith)
  unfold Rl
  refine Rv_di (hMl 0 (Nat.zero_le _)) ?_ ?_ ?_ h0
  · unfold vl El
    exact (DiM.pmat (M := fun j t => Ml Ext q h j t) (fun j _ hj => hMl j hj)).mulVec
      ((DiM.of_entire hFtd _ _).mulVec (DiV.const _))
  · unfold Wl; exact (DiM.of_entire hFtd _ _).mulVec (DiV.const _)
  · unfold W0l; exact (DiM.of_entire hFtd _ _).mulVec (DiV.const _)

set_option maxHeartbeats 2000000 in
theorem smooth_Phi (hθ0 : 0 < θ) (hθ1 : θ < 1) (hK : 0 ≤ K)
    (hcond : ∀ y α' (E : Fin 6 → M2), |α' - α₀| < η → (∀ i, ‖E i‖ < η) →
      CondsAt θ K F A₀ y α' E)
    (hFt : ∀ y : ℝ, ‖Ft y - F y‖ < η / 2)
    (hFtζ : ∀ (y : ℝ) (ζ : ℂ), ‖ζ‖ < τ₀ → ‖Ft (y + ζ) - Ft y‖ < η / 2)
    (hExtB : ∀ p ∈ ball p₀ ρ, ∀ (y : ℝ) (b : P) (c : ℂ), ∀ t ∈ ball (0 : ℂ) (ρ / (1 + ‖b‖ + ‖c‖)),
      ‖Ext p y b c t - A p y‖ ≤ 2 * MA * (1 + ‖b‖ + ‖c‖) / ρ * ‖t‖)
    (hExtD : ∀ p ∈ ball p₀ ρ, ∀ (y : ℝ) (b : P) (c : ℂ),
      DifferentiableOn ℂ (Ext p y b c) (ball 0 (ρ / (1 + ‖b‖ + ‖c‖))))
    (hExtV : ∀ p ∈ ball p₀ ρ, ∀ (y : ℝ) (b : P) (c : ℂ) (s : ℝ),
      |s| < ρ / (1 + ‖b‖ + ‖c‖) → Ext p y b c s = A (p + s • b) ((y : ℂ) + s * c))
    (hAp : ∀ p ∈ ball p₀ δ₁, ∀ y : ℝ, ‖A p y - A₀ y‖ < η / 2)
    (hMA : 0 ≤ MA) (hρ : 0 < ρ) (hδη : δ₁ ≤ η) (hδρ : δ₁ ≤ ρ) (hτ0 : 0 < τ) (hτρ : τ ≤ ρ)
    (hτ : 2 * MA * τ / ρ < η / 2) (hττ₀ : τ ≤ τ₀)
    (hFtd : Differentiable ℂ Ft) {δ : ℝ} {U : Set P} (hA : IsAnalyticCocycleFamily δ U A)
    (hδ : 0 < δ)
    (hU : ball p₀ δ₁ ⊆ U) {n₀ : ℕ} (hn₀ : 8 * K * θ ^ n₀ ≤ 1 / 2) :
    ContDiffOn ℝ ∞ (fun q => Real.log ‖Rr A Ft n₀ q‖ + ∑' k, fterm A Ft n₀ k q)
      (ball (α₀, p₀) δ₁ ×ˢ univ) := by
  set V := ball (α₀, p₀) δ₁ ×ˢ (univ : Set ℝ) with hVdef
  have hVo : IsOpen V := isOpen_ball.prod isOpen_univ
  have hVc : IsPreconnected V := ((convex_ball _ _).prod convex_univ).isPreconnected
  have hθn : ∀ n, n₀ ≤ n → 8 * K * θ ^ n ≤ 1 / 2 := fun n hn =>
    le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hθ0.le hθ1.le hn) (by positivity))
      hn₀
  have hpV : ∀ q ∈ V, q.1.2 ∈ ball p₀ ρ := fun q hq =>
    ball_subset_ball hδρ (mem_ball_snd' hq.1)
  have hlin := fun (q h : (ℝ × P) × ℝ) (hq : q.1 ∈ ball (α₀, p₀) δ₁) (hh : ‖h‖ ≤ 1) (t : ℂ) =>
    line_est (A := A) (Ext := Ext) (Ft := Ft) hθ0.le hcond hFt hFtζ hExtB hAp hMA hρ hδη hδρ
      hτ0 hτρ hτ hττ₀ hq hh (t := t)
  -- real facts
  have hreal : ∀ q ∈ V, ∀ n : ℕ, Rr A Ft n q ≠ 0 ∧
      cr (vr A Ft n q) (Ft ((q.2 : ℝ) : ℂ) *ᵥ ![0, 1]) ≠ 0 ∧
      ‖Rr A Ft (n + 1) q / Rr A Ft n q - 1‖ ≤ 8 * K * θ ^ n := by
    intro q hq n
    have h0 := hlin q 0 hq.1 (by simp) 0
    have hs : ∀ m : ℕ, |(0 : ℝ)| < ρ / (m + 3) := fun m => by rw [abs_zero]; positivity
    have hR : ∀ m : ℕ, Rl Ext Ft m q 0 0 = Rr A Ft m q := fun m => by
      have := Rl_real (A := A) (Ext := Ext) (Ft := Ft) hρ hExtV (hpV q hq) (h := 0) (by simp)
        (n := m) (hs m)
      simpa using this
    have hv : ∀ m : ℕ, vl Ext Ft m q 0 0 = vr A Ft m q ∧
        W0l Ft q 0 0 = Ft ((q.2 : ℝ) : ℂ) *ᵥ ![0, 1] := fun m => by
      have := vl_real (A := A) (Ext := Ext) (Ft := Ft) hρ hExtV (hpV q hq) (h := 0) (by simp)
        (n := m) (hs m)
      simpa using this
    have hn3 : ‖(0 : ℂ)‖ < τ / (n + 3) := by rw [norm_zero]; positivity
    have hn4 : ‖(0 : ℂ)‖ < τ / (n + 4) := by rw [norm_zero]; positivity
    obtain ⟨hc1, hc2⟩ := h0.1 n hn3
    refine ⟨by rw [← hR n]; exact hc2, by rw [← (hv n).1, ← (hv n).2]; exact hc1, ?_⟩
    have := h0.2 n hn4
    rwa [hR, hR] at this
  -- analyticity of the approximants
  have hAnRr : ∀ q ∈ V, ∀ n, AnalyticAt ℝ (Rr A Ft n) q := by
    intro q hq n
    have hpU : q.1.2 ∈ U := hU (mem_ball_snd' hq.1)
    have hMr : ∀ j, AnM (fun q => Mr A q j) q := by
      intro j
      apply AnM.of_analyticAt
      have hmem : (q.1.2, (((q.2 - j * q.1.1 : ℝ)) : ℂ)) ∈ U ×ˢ strip δ :=
        ⟨hpU, by simp [strip, hδ]⟩
      have hg : AnalyticAt ℝ (fun q : (ℝ × P) × ℝ => (q.1.2, (((q.2 - j * q.1.1 : ℝ)) : ℂ))) q := by
        refine AnalyticAt.prod (analyticAt_snd.comp analyticAt_fst) ?_
        exact (Complex.ofRealCLM.analyticAt _).comp
          (analyticAt_snd.sub (analyticAt_const.mul (analyticAt_fst.comp analyticAt_fst)))
      exact (hA.analytic _ hmem).comp
        (f := fun q : (ℝ × P) × ℝ => (q.1.2, (((q.2 - j * q.1.1 : ℝ)) : ℂ))) hg
    have han : ∀ g : (ℝ × P) × ℝ → ℝ, AnalyticAt ℝ g q → AnV (fun q => Ft ((g q : ℝ) : ℂ) *ᵥ ![0, 1]) q :=
      fun g hg => (AnM.of_entire hFtd hg).mulVec (AnV.const _ _)
    have hv : AnV (fun q => vr A Ft n q) q := by
      unfold vr
      exact (AnM.pmat (M := fun j q => Mr A q j) hMr n).mulVec ((AnM.of_entire hFtd
        (g := fun q : (ℝ × P) × ℝ => q.2 - n * q.1.1)
        (analyticAt_snd.sub (analyticAt_const.mul (analyticAt_fst.comp analyticAt_fst)))).mulVec
        (AnV.const _ _))
    unfold Rr
    exact Rv_an (hMr 0) hv (han (fun q => q.2 + q.1.1) (analyticAt_snd.add
      (analyticAt_fst.comp analyticAt_fst))) (han (fun q => q.2) analyticAt_snd)
      (hreal q hq n).2.1
  -- analyticity of the terms
  have hAnF : ∀ k, ∀ q ∈ V, AnalyticAt ℝ (fterm A Ft n₀ k) q := by
    intro k q hq
    have hr := hreal q hq (n₀ + k)
    have hsl := mem_slit_of_near (hr.2.2.trans (hθn _ (by omega)))
    have hdiv : AnalyticAt ℝ (fun q => Rr A Ft (n₀ + k + 1) q / Rr A Ft (n₀ + k) q) q :=
      (hAnRr q hq _).div (hAnRr q hq _) hr.1
    have hlog : AnalyticAt ℝ (fun q => Complex.log (Rr A Ft (n₀ + k + 1) q / Rr A Ft (n₀ + k) q)) q :=
      ((analyticAt_clog hsl).restrictScalars (𝕜 := ℝ)).comp
        (f := fun q => Rr A Ft (n₀ + k + 1) q / Rr A Ft (n₀ + k) q) hdiv
    exact (Complex.reCLM.analyticAt _).comp hlog
  -- line extensions of the terms
  have hline : ∀ k, ∀ q ∈ V, ∀ h : (ℝ × P) × ℝ, ‖h‖ ≤ 1 → ∃ g : ℂ → ℂ,
      DifferentiableOn ℂ g (ball 0 (τ / ((n₀ + k : ℕ) + 4))) ∧
      (∀ t ∈ ball (0 : ℂ) (τ / ((n₀ + k : ℕ) + 4)), ‖g t‖ ≤ 12 * K * θ ^ (n₀ + k)) ∧
      ∀ s : ℝ, |s| < τ / ((n₀ + k : ℕ) + 4) → fterm A Ft n₀ k (q + s • h) = (g s).re := by
    intro k q hq h hh
    set n := n₀ + k with hn
    have hpq := hpV q hq
    have hl := fun t => hlin q h hq.1 hh t
    have hr34 : τ / ((n : ℕ) + 4 : ℝ) ≤ τ / ((n : ℕ) + 3 : ℝ) :=
      div_le_div_of_nonneg_left hτ0.le (by positivity) (by linarith)
    have hr4 : τ / ((n : ℕ) + 4 : ℝ) = τ / (((n + 1 : ℕ) : ℝ) + 3) := by push_cast; ring_nf
    have hD1 : DifferentiableOn ℂ (Rl Ext Ft (n + 1) q h) (ball 0 (τ / ((n : ℕ) + 4))) := by
      rw [hr4]
      exact Rl_diff hFtd hρ hτρ hExtD hpq hh (n + 1) (fun t ht => ((hl t).1 (n + 1)
        (by simpa using ht)).1)
    have hD0 : DifferentiableOn ℂ (Rl Ext Ft n q h) (ball 0 (τ / ((n : ℕ) + 4))) :=
      (Rl_diff hFtd hρ hτρ hExtD hpq hh n (fun t ht => ((hl t).1 n (by simpa using ht)).1)).mono
        (ball_subset_ball hr34)
    have hest : ∀ t ∈ ball (0 : ℂ) (τ / ((n : ℕ) + 4)),
        ‖Rl Ext Ft (n + 1) q h t / Rl Ext Ft n q h t - 1‖ ≤ 1 / 2 ∧
        ‖Rl Ext Ft (n + 1) q h t / Rl Ext Ft n q h t - 1‖ ≤ 8 * K * θ ^ n ∧
        Rl Ext Ft n q h t ≠ 0 := by
      intro t ht
      have ht' : ‖t‖ < τ / (n + 4) := by simpa using ht
      have h2 := (hl t).2 n ht'
      exact ⟨h2.trans (hθn n (by omega)), h2,
        ((hl t).1 n (ht'.trans_le (by simpa using hr34))).2⟩
    refine ⟨fun t => Complex.log (Rl Ext Ft (n + 1) q h t / Rl Ext Ft n q h t), ?_, ?_, ?_⟩
    · exact (hD1.div hD0 (fun t ht => (hest t ht).2.2)).clog
        (fun t ht => mem_slit_of_near (hest t ht).1)
    · intro t ht
      calc _ ≤ 3 / 2 * ‖Rl Ext Ft (n + 1) q h t / Rl Ext Ft n q h t - 1‖ :=
            norm_log_le_of_near (hest t ht).1
        _ ≤ 3 / 2 * (8 * K * θ ^ n) := by gcongr; exact (hest t ht).2.1
        _ = 12 * K * θ ^ n := by ring
    · intro s hs
      have hs' : ∀ m, m ≤ n + 1 → |s| < ρ / (m + 3) := by
        intro m hm
        refine hs.trans_le ?_
        calc τ / ((n : ℕ) + 4 : ℝ) ≤ ρ / ((n : ℕ) + 4) := by gcongr
          _ ≤ ρ / (m + 3) := div_le_div_of_nonneg_left hρ.le (by positivity)
              (by have : (m : ℝ) ≤ n + 1 := by exact_mod_cast hm
                  push_cast; linarith)
      have e1 := Rl_real (A := A) (Ext := Ext) (Ft := Ft) hρ hExtV hpq hh (n := n + 1)
        (hs' (n + 1) le_rfl)
      have e0 := Rl_real (A := A) (Ext := Ext) (Ft := Ft) hρ hExtV hpq hh (n := n)
        (hs' n (by omega))
      simp only [fterm]
      rw [← e1, ← e0]
  -- the bounds on derivatives
  set v : ℕ → ℕ → ℝ := fun i k => (2 * i) ^ i * (i.factorial * (12 * K * θ ^ (n₀ + k)) /
    (τ / ((n₀ + k : ℕ) + 4) / 2) ^ i) with hv
  have hbound : ∀ i k, ∀ q ∈ V, ‖iteratedFDeriv ℝ i (fterm A Ft n₀ k) q‖ ≤ v i k := by
    intro i k q hq
    exact norm_iteratedFDeriv_le_of_lines hVo (hAnF k) hq (by positivity) (by positivity)
      (hline k q hq) i
  have hsum : ∀ i, Summable (v i) := by
    intro i
    have hθn' : ‖θ‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_pos hθ0]
    have h1 := ((summable_pow_mul_geometric_of_norm_lt_one i hθn').comp_injective
      (add_left_injective (n₀ + 4))).mul_left
      ((2 * i) ^ i * (i.factorial * (12 * K)) * (2 / τ) ^ i / θ ^ 4)
    refine h1.congr (fun k => ?_)
    simp only [hv, Function.comp_apply]
    have hθ4 : θ ^ 4 ≠ 0 := by positivity
    have hτne : τ ≠ 0 := hτ0.ne'
    have hn4 : ((n₀ : ℝ) + k + 4) ≠ 0 := by positivity
    push_cast
    rw [show k + (n₀ + 4) = (n₀ + k) + 4 by ring, pow_add]
    field_simp
    have h8 : (8 + (k : ℝ) * 2 + (n₀ : ℝ) * 2) ≠ 0 := by positivity
    have e : (8 + (k : ℝ) * 2 + (n₀ : ℝ) * 2)⁻¹ * 2 * (4 + (k : ℝ) + (n₀ : ℝ)) = 1 := by
      field_simp; ring
    calc _ = K * ((τ * τ⁻¹) ^ i * ((8 + (k : ℝ) * 2 + (n₀ : ℝ) * 2)⁻¹ * 2 *
          (4 + (k : ℝ) + (n₀ : ℝ))) ^ i) := by rw [mul_pow, mul_pow, mul_pow]; ring
      _ = K := by rw [mul_inv_cancel₀ hτne, e]; simp
  have hT := contDiffOn_tsum_of_bounds hVo hVc (fterm A Ft n₀)
    (fun k q hq => (hAnF k q hq).contDiffAt.contDiffWithinAt) v hsum hbound
  have hL : ContDiffOn ℝ ∞ (fun q => Real.log ‖Rr A Ft n₀ q‖) V := by
    intro q hq
    have h1 := (hAnRr q hq n₀).contDiffAt (n := ∞)
    have h2 := h1.norm ℝ (hreal q hq n₀).1
    exact (h2.log (by simpa using (hreal q hq n₀).1)).contDiffWithinAt
  exact hL.add hT

end Smooth

/-! ### Identification of the limit with the Lyapunov exponent -/

section Ident

variable {A : P → ℂ → M2} {Ft : ℂ → M2} {F A₀ : ℝ → M2}
  {p₀ : P} {α₀ θ K η δ₁ : ℝ}

set_option maxHeartbeats 2000000 in
theorem ident (hθ0 : 0 < θ) (hθ1 : θ < 1) (hK : 0 ≤ K)
    (hcond : ∀ y α' (E : Fin 6 → M2), |α' - α₀| < η → (∀ i, ‖E i‖ < η) →
      CondsAt θ K F A₀ y α' E)
    (hFt : ∀ y : ℝ, ‖Ft y - F y‖ < η / 2)
    (hAp : ∀ p ∈ ball p₀ δ₁, ∀ y : ℝ, ‖A p y - A₀ y‖ < η / 2) (hδη : δ₁ ≤ η)
    (hFtd : Differentiable ℂ Ft) (hFtp : ∀ z, Ft (z + 1) = Ft z)
    (hFc : Continuous F) (hFp : Function.Periodic F 1) (hFd : ∀ y, (F y).det = 1)
    {δ : ℝ} {U : Set P} (hA : IsAnalyticCocycleFamily δ U A) (hδ : 0 < δ)
    (hU : ball p₀ δ₁ ⊆ U) {n₀ : ℕ} (hn₀ : 32 * K * θ ^ n₀ ≤ 1 / 2)
    {q₁ : ℝ × P} (hq₁ : q₁ ∈ ball (α₀, p₀) δ₁) :
    L q₁.1 (A q₁.2) 0 =
      ∫ x in (0 : ℝ)..1, (Real.log ‖Rr A Ft n₀ (q₁, x)‖ + ∑' k, fterm A Ft n₀ k (q₁, x)) := by
  obtain ⟨α, p⟩ := q₁
  have hpδ : p ∈ ball p₀ δ₁ := mem_ball_snd' hq₁
  have hpU : p ∈ U := hU hpδ
  have hαη : |α - α₀| < η := (mem_ball_fst' hq₁).trans_le hδη
  have hη : 0 < η := by
    have := hFt 0
    linarith [norm_nonneg (Ft ((0 : ℝ) : ℂ) - F 0)]
  have hSL : IsSLCocycle (fun y : ℝ => A p (y : ℂ)) := by
    have := (hA.cocycle p hpU).isSLCocycle_shift (ε := 0) (by simpa using hδ)
    have e : shift (A p) 0 = fun y : ℝ => A p (y : ℂ) := by funext y; simp [shift]
    rwa [e] at this
  have hLdef : L α (A p) 0 = lyapunov α (fun y : ℝ => A p (y : ℂ)) := by
    have e : shift (A p) 0 = fun y : ℝ => A p (y : ℂ) := by funext y; simp [shift]
    simp only [L, e]
  -- the conjugated cocycle
  set Nm : ℝ → M2 := fun x => (F (x + α))⁻¹ * A p (x : ℂ) * F x with hNm
  have hNmc : ∀ x, Conds θ K
      (condMap F A₀ x (α, ![A p (x : ℂ) - A₀ x, 0, 0, 0, 0, 0])).1
      (condMap F A₀ x (α, ![A p (x : ℂ) - A₀ x, 0, 0, 0, 0, 0])).2.1 (Nm x)
      (condMap F A₀ x (α, ![A p (x : ℂ) - A₀ x, 0, 0, 0, 0, 0])).2.2.2.1
      (condMap F A₀ x (α, ![A p (x : ℂ) - A₀ x, 0, 0, 0, 0, 0])).2.2.2.2.1
      (condMap F A₀ x (α, ![A p (x : ℂ) - A₀ x, 0, 0, 0, 0, 0])).2.2.2.2.2.1
      (condMap F A₀ x (α, ![A p (x : ℂ) - A₀ x, 0, 0, 0, 0, 0])).2.2.2.2.2.2 := by
    intro x
    have H := hcond x α ![A p (x : ℂ) - A₀ x, 0, 0, 0, 0, 0] hαη (fun i => by
      fin_cases i
      · simpa using (hAp p hpδ x).trans (by linarith)
      all_goals simp [hη])
    have e : (condMap F A₀ x (α, ![A p (x : ℂ) - A₀ x, 0, 0, 0, 0, 0])).2.2.1 = Nm x := by
      simp [condMap, hNm, adjugate_eq_inv (hFd _)]
    unfold CondsAt at H
    rw [e] at H
    exact H
  have hNc : Continuous Nm :=
    ((DerivFormulaAux.continuous_inv_of_det (hFc.comp (continuous_id.add continuous_const))
      (fun x => hFd _)).mul hSL.continuous).mul hFc
  have hNp : Function.Periodic Nm 1 := by
    intro x
    simp only [hNm]
    rw [show x + 1 + α = x + α + 1 by ring, hFp, hFp]
    push_cast
    rw [(hA.cocycle p hpU).periodic]
  obtain ⟨hg, gg, hgc, hgp, ggc, ggp, hgb, ggb, hgeq, ggeq⟩ :=
    DerivFormulaAux.graphs_exist (α := α) hNc hNp (r := 1 / 2) (by norm_num)
      (fun x => (hNmc x).hU) (fun x => (hNmc x).hS)
      (fun x => (hNmc x).hU2) (fun x => (hNmc x).hS2)
  have hXB : ∀ x : ℝ, A p (x : ℂ) * F x = F (x + α) * Nm x := by
    intro x
    simp only [hNm]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (by rw [hFd]; exact isUnit_one),
      Matrix.one_mul]
  have hℓ1 : ∀ x, 1 ≤ ‖Nm x 0 0 + Nm x 0 1 * hg x‖ := by
    intro x
    have h1 := (hNmc x).h1
    have h2 : ‖Nm x 0 1 * hg x‖ ≤ ‖Nm x 0 1‖ / 2 := by
      rw [norm_mul]; nlinarith [hgb x, norm_nonneg (Nm x 0 1)]
    have := norm_add_ge (Nm x 0 0) (Nm x 0 1 * hg x)
    linarith
  have hhg : ∀ x, hg x * gg x ≠ 1 := by
    intro x h
    have : ‖hg x * gg x‖ ≤ 1 / 4 := by
      rw [norm_mul]; nlinarith [hgb x, ggb x, norm_nonneg (hg x), norm_nonneg (gg x)]
    rw [h, norm_one] at this; linarith
  have hL := DerivFormulaAux.lyap_of_graphs hSL hFc hFp hFd hNc hNp hXB hgc hgp ggc ggp hhg hgeq
    ggeq hℓ1
  -- the invariant section
  set u : ℝ → Fin 2 → ℂ := fun x => F x *ᵥ ![1, hg x] with hu
  set ℓ : ℝ → ℂ := fun x => Nm x 0 0 + Nm x 0 1 * hg x with hℓ
  have hℓ0 : ∀ x, ℓ x ≠ 0 := fun x h => by
    have := hℓ1 x; simp only [hℓ] at h; rw [h, norm_zero] at this; linarith
  have hinv : ∀ y : ℝ, A p (y : ℂ) *ᵥ u y = ℓ y • u (y + α) := by
    intro y
    simp only [hu, hℓ]
    rw [Matrix.mulVec_mulVec, hXB, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_smul]
    congr 1
    ext i; fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      rw [← hgeq y]; ring
  have hu' : ∀ y, ∃ z : ℂ, ‖z‖ ≤ 1 / 2 ∧ u y = F y *ᵥ ![1, z] := fun y => ⟨hg y, hgb y, rfl⟩
  have hRC := fun x : ℝ => real_conv (A := A) (Ft := Ft) (q := ((α, p), x)) hθ0.le hcond hFt hAp
    hδη hq₁ (u := u) (ℓ := ℓ) hinv hℓ0 hu'
  -- the limit of the series
  set Rinf : ℝ → ℂ := fun x => Rv (Mr A ((α, p), x) 0) (u x)
    (Ft ((x + α : ℝ) : ℂ) *ᵥ ![0, 1]) (Ft ((x : ℝ) : ℂ) *ᵥ ![0, 1]) with hRinf
  have hPhi : ∀ x : ℝ, Real.log ‖Rr A Ft n₀ ((α, p), x)‖ + ∑' k, fterm A Ft n₀ k ((α, p), x) =
      Real.log ‖Rinf x‖ := by
    intro x
    obtain ⟨hR0, -, hRn⟩ := hRC x
    set a : ℕ → ℝ := fun k => Real.log ‖Rr A Ft (n₀ + k) ((α, p), x)‖ with ha
    have hft : ∀ k, fterm A Ft n₀ k ((α, p), x) = a (k + 1) - a k := by
      intro k
      simp only [fterm, ha, Complex.log_re, norm_div]
      rw [Real.log_div (by simpa using (hRn _).1) (by simpa using (hRn _).1)]
      ring_nf
    have hlim : Tendsto a atTop (𝓝 (Real.log ‖Rinf x‖)) := by
      have h1 : Tendsto (fun k => Rr A Ft (n₀ + k) ((α, p), x) / Rinf x) atTop (𝓝 1) := by
        rw [tendsto_iff_norm_sub_tendsto_zero]
        refine squeeze_zero (fun _ => norm_nonneg _) (fun k => (hRn (n₀ + k)).2) ?_
        have : Tendsto (fun k : ℕ => θ ^ (n₀ + k)) atTop (𝓝 0) := by
          simpa [pow_add] using
            (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0.le hθ1).const_mul (θ ^ n₀)
        simpa using this.const_mul (8 * K)
      have h2 : Tendsto (fun k => Rr A Ft (n₀ + k) ((α, p), x)) atTop (𝓝 (Rinf x)) := by
        have := h1.mul_const (Rinf x)
        rw [one_mul] at this
        exact this.congr (fun k => div_mul_cancel₀ _ hR0)
      have h3 : ContinuousAt (fun z : ℂ => Real.log ‖z‖) (Rinf x) :=
        (Real.continuousAt_log (norm_ne_zero_iff.2 hR0)).comp continuous_norm.continuousAt
      exact h3.tendsto.comp h2
    have hsumm : Summable (fun k => fterm A Ft n₀ k ((α, p), x)) := by
      refine ((summable_geometric_of_lt_one hθ0.le hθ1).mul_left
        (48 * K * θ ^ n₀)).of_norm_bounded (fun k => ?_)
      set r1 := Rr A Ft (n₀ + k + 1) ((α, p), x)
      set r0 := Rr A Ft (n₀ + k) ((α, p), x)
      have h1 := (hRn (n₀ + k + 1)).2
      have h2 := (hRn (n₀ + k)).2
      have hθk : θ ^ (n₀ + k + 1) ≤ θ ^ (n₀ + k) :=
        pow_le_pow_of_le_one hθ0.le hθ1.le (by omega)
      have hθk0 : θ ^ (n₀ + k) ≤ θ ^ n₀ := pow_le_pow_of_le_one hθ0.le hθ1.le (by omega)
      have hsmall : 32 * K * θ ^ (n₀ + k) ≤ 1 / 2 :=
        le_trans (mul_le_mul_of_nonneg_left hθk0 (by positivity)) hn₀
      have hden : 1 / 2 ≤ ‖r0 / Rinf x‖ := by
        have := norm_add_ge (1 : ℂ) (r0 / Rinf x - 1)
        rw [norm_one, add_sub_cancel] at this
        have : 8 * K * θ ^ (n₀ + k) ≤ 1 / 4 := by linarith
        linarith
      have hr0 : r0 ≠ 0 := (hRn (n₀ + k)).1
      have hRi : Rinf x ≠ 0 := hR0
      have e : r1 / r0 - 1 = ((r1 / Rinf x - 1) - (r0 / Rinf x - 1)) / (r0 / Rinf x) := by
        field_simp
        ring
      have hratio : ‖r1 / r0 - 1‖ ≤ 32 * K * θ ^ (n₀ + k) := by
        rw [e, norm_div, div_le_iff₀ (by linarith)]
        calc ‖r1 / Rinf x - 1 - (r0 / Rinf x - 1)‖ ≤ ‖r1 / Rinf x - 1‖ + ‖r0 / Rinf x - 1‖ :=
              norm_sub_le _ _
          _ ≤ 8 * K * θ ^ (n₀ + k) + 8 * K * θ ^ (n₀ + k) := by
              gcongr
              exact h1.trans (mul_le_mul_of_nonneg_left hθk (by positivity))
          _ = 32 * K * θ ^ (n₀ + k) * (1 / 2) := by ring
          _ ≤ 32 * K * θ ^ (n₀ + k) * ‖r0 / Rinf x‖ := by gcongr
      rw [Real.norm_eq_abs]
      calc |fterm A Ft n₀ k ((α, p), x)| ≤ ‖Complex.log (r1 / r0)‖ := Complex.abs_re_le_norm _
        _ ≤ 3 / 2 * ‖r1 / r0 - 1‖ := norm_log_le_of_near (hratio.trans hsmall)
        _ ≤ 3 / 2 * (32 * K * θ ^ (n₀ + k)) := by gcongr
        _ = 48 * K * θ ^ n₀ * θ ^ k := by rw [pow_add]; ring
    have hts := hsumm.hasSum.tendsto_sum_nat
    have htel : ∀ N, ∑ k ∈ Finset.range N, fterm A Ft n₀ k ((α, p), x) = a N - a 0 := by
      intro N
      simp_rw [hft]
      exact Finset.sum_range_sub a N
    have h2 : Tendsto (fun N => a N - a 0) atTop (𝓝 (Real.log ‖Rinf x‖ - a 0)) :=
      hlim.sub_const _
    have heq := tendsto_nhds_unique (hts.congr htel) h2
    rw [heq]
    simp [ha]
  -- integrate
  have hGc : ∀ x : ℝ, cr (u x) (Ft ((x : ℝ) : ℂ) *ᵥ ![0, 1]) ≠ 0 := fun x => (hRC x).2.1
  set Gf : ℝ → ℝ := fun x => Real.log ‖cr (u x) (Ft ((x : ℝ) : ℂ) *ᵥ ![0, 1])‖ with hGf
  have hRinf' : ∀ x, Real.log ‖Rinf x‖ = Real.log ‖ℓ x‖ + (Gf (x + α) - Gf x) := by
    intro x
    have e : Rinf x = ℓ x * cr (u (x + α)) (Ft (((x + α : ℝ)) : ℂ) *ᵥ ![0, 1]) /
        cr (u x) (Ft ((x : ℝ) : ℂ) *ᵥ ![0, 1]) := by
      simp only [hRinf, Rv, Mr]
      rw [show (((x - ((0 : ℕ) : ℝ) * α : ℝ)) : ℂ) = (x : ℂ) by push_cast; ring, hinv x,
        cr_smul_left]
    rw [e, norm_div, norm_mul, Real.log_div (by simpa using mul_ne_zero (hℓ0 x) (hGc (x + α)))
      (by simpa using hGc x), Real.log_mul (by simpa using hℓ0 x) (by simpa using hGc (x + α))]
    simp only [hGf]
    ring
  have hucont : Continuous u := by
    refine hFc.matrix_mulVec (continuous_pi (fun i => ?_))
    fin_cases i
    · simpa using continuous_const
    · simpa using hgc
  have hcontG : Continuous Gf := by
    have hW : Continuous fun x : ℝ => Ft ((x : ℝ) : ℂ) *ᵥ ![0, 1] :=
      (hFtd.continuous.comp Complex.continuous_ofReal).matrix_mulVec continuous_const
    exact (continuous_cr.comp (hucont.prodMk hW)).norm.log
      (fun x => norm_ne_zero_iff.2 (hGc x))
  have hperG : Function.Periodic Gf 1 := by
    intro x
    simp only [hGf, hu]
    rw [hFp, hgp]
    push_cast
    rw [hFtp]
  have hcontℓ : Continuous fun x => Real.log ‖ℓ x‖ :=
    ((hNc.matrix_elem 0 0).add ((hNc.matrix_elem 0 1).mul hgc)).norm.log
      (fun x => norm_ne_zero_iff.2 (hℓ0 x))
  rw [hLdef, hL]
  symm
  rw [intervalIntegral.integral_congr (g := fun x => Real.log ‖ℓ x‖ + (Gf (x + α) - Gf x))
    (fun x _ => by simp only; rw [hPhi x, hRinf' x])]
  have hc3 : Continuous fun x => Gf (x + α) := hcontG.comp (continuous_id.add continuous_const)
  have hc2 : Continuous fun x => Gf (x + α) - Gf x := hc3.sub hcontG
  rw [intervalIntegral.integral_add (hcontℓ.intervalIntegrable 0 1) (hc2.intervalIntegrable 0 1),
    intervalIntegral.integral_sub (hc3.intervalIntegrable 0 1) (hcontG.intervalIntegrable 0 1),
    DerivFormulaAux.integral_shift_per hperG, sub_self, add_zero]

end Ident

end UHSmoothAux

open UHSmoothAux in
/-- **`C^∞` dependence on `𝒰ℋ`, jointly in the frequency and the parameters** (the field
`Hypotheses.uhSmooth`). -/
theorem uhSmooth_proof : ∀ {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {δ : ℝ} {U : Set P}
    {A : P → ℂ → M2}, IsAnalyticCocycleFamily δ U A → ∀ {α₀ : ℝ} {p₀ : P}, p₀ ∈ U →
      UH α₀ (A p₀) →
        ∃ W ∈ 𝓝 (α₀, p₀), ContDiffOn ℝ ∞ (fun q : ℝ × P => L q.1 (A q.2) 0) W := by
  intro P _ _ δ U A hA α₀ p₀ hp₀ hUH
  have hδ : 0 < δ := (hA.cocycle p₀ hp₀).pos
  set A₀ : ℝ → M2 := fun y => A p₀ (y : ℂ) with hA₀
  have hshift : ∀ p, shift (A p) 0 = fun y : ℝ => A p (y : ℂ) := fun p => by
    funext y; simp [shift]
  have hSL0 : IsSLCocycle A₀ := by
    have := (hA.cocycle p₀ hp₀).isSLCocycle_shift (ε := 0) (by simpa using hδ)
    rwa [hshift] at this
  have hUH' : IsUH α₀ A₀ := by
    have := hUH; unfold UH at this; rwa [hshift] at this
  -- an adapted frame at the base point
  obtain ⟨B, hBc, hBp, hBd, hdiag, hexp⟩ := UHAnalyticAux.frame_of_isUH hUH'
  obtain ⟨F, l, ρ₁, hFc, hFp, hFd, hlc, hlp, hρ₁, hlρ, hD, -⟩ :=
    DerivFormulaAux.adapt_frame hSL0 hBc hBp hBd hdiag hexp
  obtain ⟨Kl, hKl⟩ := UHOpenAux.per_bound hlc hlp
  set K : ℝ := Kl + 1 with hKdef
  have hlK : ∀ y, ‖l y‖ < K := fun y => by linarith [hKl y]
  have hK1 : 1 < K := by linarith [hKl 0, hlρ 0]
  set θ : ℝ := 2 / (1 + ρ₁ ^ 2) with hθdef
  have hθ0 : 0 < θ := by positivity
  have hθ1 : θ < 1 := by rw [hθdef, div_lt_one (by positivity)]; nlinarith
  have hθρ : 1 < θ * ρ₁ ^ 2 := by
    rw [hθdef, div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]; nlinarith
  -- stage 1
  obtain ⟨η, hη, hcond0⟩ := stage1 hFc hFp hFd hSL0.continuous hSL0.periodic hρ₁ hlρ hlK hθρ
    hθ0.le hD
  have hcond : ∀ y α' (E : Fin 6 → M2), |α' - α₀| < η → (∀ i, ‖E i‖ < η) →
      CondsAt θ K F A₀ y α' E := hcond0
  -- stage 2: an entire frame
  have hent : ∀ i j : Fin 2, ∃ G : ℂ → ℂ, Differentiable ℂ G ∧ (∀ z, G (z + 1) = G z) ∧
      ∀ y : ℝ, ‖G y - F y i j‖ < η / 8 := fun i j =>
    exists_entire_approx (hFc.matrix_elem i j) (fun y => by simp only [hFp y]) (by positivity)
  choose G hGd hGp hGa using hent
  set Ft : ℂ → M2 := fun z => G 0 0 z • !![1, 0; 0, 0] + G 0 1 z • !![0, 1; 0, 0] +
    G 1 0 z • !![0, 0; 1, 0] + G 1 1 z • !![0, 0; 0, 1] with hFtdef
  have hFt_apply : ∀ z i j, Ft z i j = G i j z := by
    intro z i j; fin_cases i <;> fin_cases j <;> simp [hFtdef]
  have hFtd : Differentiable ℂ Ft :=
    ((((hGd 0 0).smul_const _).add ((hGd 0 1).smul_const _)).add
      ((hGd 1 0).smul_const _)).add ((hGd 1 1).smul_const _)
  have hFtp : ∀ z, Ft (z + 1) = Ft z := by intro z; simp only [hFtdef, hGp]
  have hFt : ∀ y : ℝ, ‖Ft y - F y‖ < η / 2 := by
    intro y
    refine (DerivFormulaAux.norm_M2_le_entries _ (by positivity : 0 ≤ η / 8) (fun i j => ?_)).trans_lt
      (by linarith)
    rw [Matrix.sub_apply, hFt_apply]
    exact (hGa i j y).le
  -- stage 3: uniform continuity of the entire frame near the real axis
  have hτev := tube_periodic_set (Z := ℂ) (Φ := fun (y : ℝ) (ζ : ℂ) => Ft (y + ζ) - Ft y)
    (by
      have h1 : Continuous fun p : ℝ × ℂ => Ft ((p.1 : ℂ) + p.2) :=
        hFtd.continuous.comp ((Complex.continuous_ofReal.comp continuous_fst).add continuous_snd)
      have h2 : Continuous fun p : ℝ × ℂ => Ft (p.1 : ℂ) :=
        hFtd.continuous.comp (Complex.continuous_ofReal.comp continuous_fst)
      exact h1.sub h2)
    (fun y ζ => by
      beta_reduce
      push_cast
      rw [show (y : ℂ) + 1 + ζ = (y + ζ) + 1 by ring, hFtp, hFtp])
    (O := ball 0 (η / 2)) isOpen_ball (z₀ := 0) (fun y => by simp [hη])
  obtain ⟨τ₀, hτ₀, hτ₀b⟩ := Metric.eventually_nhds_iff.1 hτev
  have hFtζ : ∀ (y : ℝ) (ζ : ℂ), ‖ζ‖ < τ₀ → ‖Ft (y + ζ) - Ft y‖ < η / 2 := by
    intro y ζ hζ
    have := hτ₀b (by simpa [dist_zero_right] using hζ) y
    simpa [mem_ball, dist_zero_right] using this
  -- stage 4: complexification along lines
  obtain ⟨ρ, hρ, MA, hMA, hballU, Ext, hExt⟩ := line_ext' hA hp₀
  have hExtD : ∀ p ∈ ball p₀ ρ, ∀ (y : ℝ) (b : P) (c : ℂ),
      DifferentiableOn ℂ (Ext p y b c) (ball 0 (ρ / (1 + ‖b‖ + ‖c‖))) :=
    fun p hp y b c => (hExt p hp y b c).1
  have hExtB : ∀ p ∈ ball p₀ ρ, ∀ (y : ℝ) (b : P) (c : ℂ),
      ∀ t ∈ ball (0 : ℂ) (ρ / (1 + ‖b‖ + ‖c‖)),
      ‖Ext p y b c t - A p y‖ ≤ 2 * MA * (1 + ‖b‖ + ‖c‖) / ρ * ‖t‖ :=
    fun p hp y b c => (hExt p hp y b c).2.1
  have hExtV : ∀ p ∈ ball p₀ ρ, ∀ (y : ℝ) (b : P) (c : ℂ) (s : ℝ),
      |s| < ρ / (1 + ‖b‖ + ‖c‖) → Ext p y b c s = A (p + s • b) ((y : ℂ) + s * c) :=
    fun p hp y b c => (hExt p hp y b c).2.2
  -- stage 5: radii
  set δ₁ : ℝ := min (min η (ρ / 4)) (η * ρ / (8 * (MA + 1))) with hδ₁def
  have hδ₁0 : 0 < δ₁ := lt_min (lt_min hη (by positivity)) (by positivity)
  have hδη : δ₁ ≤ η := (min_le_left _ _).trans (min_le_left _ _)
  have hδρ4 : δ₁ ≤ ρ / 4 := (min_le_left _ _).trans (min_le_right _ _)
  have hδρ : δ₁ ≤ ρ := hδρ4.trans (by linarith)
  have hδ3 : δ₁ ≤ η * ρ / (8 * (MA + 1)) := min_le_right _ _
  have hU : ball p₀ δ₁ ⊆ U := (ball_subset_ball hδρ).trans hballU
  have hAp : ∀ p ∈ ball p₀ δ₁, ∀ y : ℝ, ‖A p y - A₀ y‖ < η / 2 := by
    intro p hp y
    rcases eq_or_ne p p₀ with rfl | hne
    · simp [hA₀, hη]
    have hs0 : 0 < ‖p - p₀‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
    have hs : ‖p - p₀‖ < δ₁ := by rw [← dist_eq_norm]; exact hp
    set b : P := ‖p - p₀‖⁻¹ • (p - p₀) with hb
    have hbn : ‖b‖ = 1 := by
      rw [hb, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hs0.ne']
    have hlam : (1 + ‖b‖ + ‖(0 : ℂ)‖) = 2 := by rw [hbn, norm_zero]; ring
    have hsρ : |‖p - p₀‖| < ρ / (1 + ‖b‖ + ‖(0 : ℂ)‖) := by
      rw [hlam, abs_of_pos hs0]; linarith
    have hval := hExtV p₀ (mem_ball_self hρ) y b 0 ‖p - p₀‖ hsρ
    have hpb : p₀ + ‖p - p₀‖ • b = p := by
      rw [hb, smul_smul, mul_inv_cancel₀ hs0.ne', one_smul]; abel
    rw [hpb, mul_zero, add_zero] at hval
    have hbd := hExtB p₀ (mem_ball_self hρ) y b 0 (‖p - p₀‖ : ℂ)
      (by rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs]; exact hsρ)
    rw [hval, hlam, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs0] at hbd
    calc ‖A p ↑y - A₀ y‖ = ‖A p ↑y - A p₀ ↑y‖ := by simp [hA₀]
      _ ≤ 2 * MA * 2 / ρ * ‖p - p₀‖ := hbd
      _ ≤ 2 * MA * 2 / ρ * (η * ρ / (8 * (MA + 1))) := by gcongr; linarith
      _ < η / 2 := by
          rw [div_mul_div_comm, div_lt_div_iff₀ (by positivity) (by norm_num)]
          nlinarith [mul_pos hη hρ]
  set τ : ℝ := min (min ρ τ₀) (η * ρ / (8 * (MA + 1))) with hτdef
  have hτ0 : 0 < τ := lt_min (lt_min hρ hτ₀) (by positivity)
  have hτρ : τ ≤ ρ := (min_le_left _ _).trans (min_le_left _ _)
  have hττ₀ : τ ≤ τ₀ := (min_le_left _ _).trans (min_le_right _ _)
  have hτ : 2 * MA * τ / ρ < η / 2 := by
    have h1 : τ ≤ η * ρ / (8 * (MA + 1)) := min_le_right _ _
    calc 2 * MA * τ / ρ ≤ 2 * MA * (η * ρ / (8 * (MA + 1))) / ρ := by gcongr
      _ < η / 2 := by
          rw [div_lt_div_iff₀ hρ (by norm_num), mul_div_assoc', div_mul_eq_mul_div,
            div_lt_iff₀ (by positivity)]
          nlinarith [mul_pos hη hρ]
  -- stage 6: the number of skipped terms
  obtain ⟨n₀, hn₀⟩ := exists_pow_lt_of_lt_one (show 0 < 1 / (64 * K) by positivity) hθ1
  have hn₀' : 32 * K * θ ^ n₀ ≤ 1 / 2 := by
    have := mul_lt_mul_of_pos_left hn₀ (show 0 < 32 * K by positivity)
    rw [show 32 * K * (1 / (64 * K)) = 1 / 2 by field_simp; ring] at this
    linarith
  have hn₀8 : 8 * K * θ ^ n₀ ≤ 1 / 2 := by nlinarith [pow_pos hθ0 n₀]
  -- smoothness of the integrand and identification
  have hsm := smooth_Phi (A := A) (Ext := Ext) (Ft := Ft) hθ0 hθ1 (by linarith) hcond hFt hFtζ
    hExtB hExtD hExtV hAp hMA hρ hδη hδρ hτ0 hτρ hτ hττ₀ hFtd hA hδ hU hn₀8
  have hint := contDiffOn_intervalIntegral_param (isOpen_ball (x := (α₀, p₀)) (ε := δ₁))
    (fun z => Real.log ‖Rr A Ft n₀ z‖ + ∑' k, fterm A Ft n₀ k z) hsm
  refine ⟨ball (α₀, p₀) δ₁, ball_mem_nhds _ hδ₁0, hint.congr (fun q₁ hq₁ => ?_)⟩
  exact ident (A := A) (Ft := Ft) hθ0 hθ1 (by linarith) hcond hFt hAp hδη hFtd hFtp hFc hFp hFd
    hA hδ hU hn₀' hq₁

/-- `C^∞` dependence on `𝒰ℋ`, jointly in the frequency and the parameters. -/
theorem uh_smooth_family {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] {δ : ℝ}
    {U : Set P} {A : P → ℂ → M2} (hA : IsAnalyticCocycleFamily δ U A) {α₀ : ℝ} {p₀ : P}
    (hp₀ : p₀ ∈ U) (hUH : UH α₀ (A p₀)) :
    ∃ W ∈ 𝓝 (α₀, p₀), ContDiffOn ℝ ∞ (fun q : ℝ × P => L q.1 (A q.2) 0) W :=
  uhSmooth_proof hA hp₀ hUH

end AvilaGlobal
