/-
Formalization of D. Damanik, J. Fillman, *One-Dimensional Ergodic Schrödinger Operators,
I. General Theory*, GSM 221, AMS 2022.

# §2.7 (second part)  Subordinacy and boundary values of `m`-functions  (book pp. 182–188)

## Main definitions
* `DF.IsSubordinate V E u` — **Definition 2.7.2**: `u` is a nonzero solution of (2.7.10) with
  `‖u‖_L / ‖v‖_L → 0` for every solution `v` that is not a multiple of `u` (subordinacy at `+∞`).
* `DF.IsSubordinateBot V E u` — subordinacy at `-∞`, defined through the reflection
  `[Rψ](n) = ψ(1 - n)` (`DF.reflV`, `DF.reflS`) used in the proof of Corollary 2.7.9(b).

## Main results
* **Exercise 2.7.5**: `DF.isSubordinate_of_one` — one linearly independent comparison solution
  suffices.
* `DF.isSubordinate_smul_iff` — subordinacy is invariant under nonzero scaling.
* Consequence of the Jitomirskaya–Last inequality (p. 186): `DF.isSubordinate_solAB_iff` —
  `solAB a b` (`a² + b² = 1`) is subordinate iff `|m_{(a,b)}(E + iε)| → ∞`; in particular
  `DF.isSubordinate_u₁_iff` (`u₁` subordinate iff `|m₊(E + i0)| = ∞`).
* **Corollary 2.7.9**:
  (a) `DF.isSubordinate_theta_iff` (`u_{1,θ}` subordinate at `+∞` iff `m₊(E + i0) = cot θ`,
  for `sin θ ≠ 0`) and `DF.isSubordinate_u₁_iff` (`θ = 0`);
  (b) `DF.isSubordinateBot_theta_iff`, `DF.isSubordinateBot_u₂_iff`;
  (c) `DF.exists_subordinate_iff`, `DF.exists_subordinateBot_iff`;
  (d) `DF.exists_subordinate_both_iff`.
* `DF.mMinus_eq_mPlus_reflV` — `m₋ = m₊` of the reflected potential.

## Deviations
* "Linearly independent of `u`" is expressed as "not a scalar multiple of `u`" (equivalent
  since `u ≠ 0`).
* Limits `ε ↓ 0` are taken along `𝓝[>] 0`; "`m(E + i0) = ∞`" means `‖m(E + iε)‖ → ∞`.
-/
import DamanikFillman.Ch2.JitomirskayaLast

noncomputable section

open scoped ComplexConjugate
open Filter Topology Complex

namespace DF

variable {V : ℤ → ℝ}

/-- **Definition 2.7.2**: `u` is subordinate at `+∞` (for energy `E`). -/
def IsSubordinate (V : ℤ → ℝ) (E : ℝ) (u : ℤ → ℂ) : Prop :=
  IsSolution V E u ∧ u ≠ 0 ∧
    ∀ v : ℤ → ℂ, IsSolution V E v → (∀ c : ℂ, v ≠ fun n => c * u n) →
      Tendsto (fun L => normL u L / normL v L) atTop (𝓝 0)

/-! ### Linear algebra of the solution space -/

lemma normL_comb_le (u v : ℤ → ℂ) (c d : ℂ) (L : ℝ) :
    normL (fun n => c * u n + d * v n) L ≤ ‖c‖ * normL u L + ‖d‖ * normL v L := by
  rw [← norm_lvec _ L (M := ⌊L⌋₊ + 1) le_rfl, lvec_add_smul, ← norm_lvec u L le_rfl,
    ← norm_lvec v L le_rfl, ← norm_smul, ← norm_smul]
  exact norm_add_le _ _

lemma isSolution_comb {z : ℂ} {u v : ℤ → ℂ} (hu : IsSolution V z u) (hv : IsSolution V z v)
    (α β : ℂ) : IsSolution V z (fun n => α * u n + β * v n) := by
  intro n
  have a := hu n; have b := hv n
  simp only
  linear_combination α * a + β * b

lemma isSolution_smul {z : ℂ} {u : ℤ → ℂ} (hu : IsSolution V z u) (c : ℂ) :
    IsSolution V z (fun n => c * u n) := by
  intro n; have a := hu n; simp only; linear_combination c * a

/-- Every solution is a combination of two solutions with nonzero Wronskian. -/
lemma exists_comb {z : ℂ} {u v w : ℤ → ℂ} (hu : IsSolution V z u) (hv : IsSolution V z v)
    (hw : IsSolution V z w) (hW : wronskian u v 0 ≠ 0) :
    ∃ α β : ℂ, w = fun n => α * u n + β * v n := by
  simp only [wronskian, zero_add] at hW
  refine ⟨(w 0 * v 1 - v 0 * w 1) / (u 0 * v 1 - v 0 * u 1),
    (u 0 * w 1 - w 0 * u 1) / (u 0 * v 1 - v 0 * u 1), ?_⟩
  apply eq_of_isSolution hw (isSolution_comb hu hv _ _)
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hW]; ring
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hW]; ring

/-- Two solutions, the second not a multiple of the nonzero first, have nonzero Wronskian. -/
lemma wronskian_ne_zero_of_indep {z : ℂ} {u v : ℤ → ℂ} (hu : IsSolution V z u)
    (hv : IsSolution V z v) (hne : u ≠ 0) (hind : ∀ c : ℂ, v ≠ fun n => c * u n) :
    wronskian u v 0 ≠ 0 := by
  intro h0
  obtain ⟨a, b, hab, h⟩ := (wronskian_eq_zero_iff hu hv).1 h0
  by_cases hb : b = 0
  · subst hb
    have ha : a ≠ 0 := hab.resolve_right (by simp)
    apply hne; funext n
    have := h n; simp at this
    exact this.resolve_left ha
  · apply hind (-a / b); funext n
    have := h n
    field_simp
    linear_combination this

lemma eventually_normL_pos {z : ℂ} {u : ℤ → ℂ} (hu : IsSolution V z u) (hne : u ≠ 0) :
    ∀ᶠ L in atTop, 0 < normL u L := by
  filter_upwards [eventually_ge_atTop 2] with L hL using normL_pos hu hne hL

/-- **Exercise 2.7.5**: if `‖u‖_L / ‖v‖_L → 0` for a single solution `v` that is not a multiple
of `u`, then `u` is subordinate. -/
theorem isSubordinate_of_one {E : ℝ} {u v : ℤ → ℂ} (hu : IsSolution V E u) (hne : u ≠ 0)
    (hv : IsSolution V E v) (hind : ∀ c : ℂ, v ≠ fun n => c * u n)
    (hlim : Tendsto (fun L => normL u L / normL v L) atTop (𝓝 0)) : IsSubordinate V E u := by
  refine ⟨hu, hne, fun w hw hwind => ?_⟩
  have hW := wronskian_ne_zero_of_indep hu hv hne hind
  obtain ⟨α, β, rfl⟩ := exists_comb hu hv hw hW
  have hβ : β ≠ 0 := by
    rintro rfl; apply hwind α; funext n; simp
  have hβpos : 0 < ‖β‖ := norm_pos_iff.2 hβ
  have hvne : v ≠ 0 := by rintro rfl; simp [wronskian] at hW
  -- eventually `‖α‖ r ≤ ‖β‖/2`
  have hsmall : ∀ᶠ L in atTop, ‖α‖ * (normL u L / normL v L) ≤ ‖β‖ / 2 := by
    have : Tendsto (fun L => ‖α‖ * (normL u L / normL v L)) atTop (𝓝 (‖α‖ * 0)) :=
      hlim.const_mul _
    rw [mul_zero] at this
    exact this.eventually (eventually_le_nhds (half_pos hβpos))
  have hbound : ∀ᶠ L in atTop,
      normL u L / normL (fun n => α * u n + β * v n) L ≤ (2 / ‖β‖) * (normL u L / normL v L) := by
    filter_upwards [hsmall, eventually_normL_pos hv hvne] with L hs hvpos
    -- `‖β‖ ‖v‖ ≤ ‖w‖ + ‖α‖ ‖u‖`
    have htri := normL_comb_le (fun n => α * u n + β * v n) u 1 (-α) L
    have hcomb : (fun n => (1 : ℂ) * (α * u n + β * v n) + -α * u n) = fun n => β * v n := by
      funext n; ring
    rw [hcomb, normL_smul] at htri
    simp only [norm_one, one_mul, norm_neg] at htri
    have hr : normL u L = (normL u L / normL v L) * normL v L := by field_simp
    have hw_lb : ‖β‖ / 2 * normL v L ≤ normL (fun n => α * u n + β * v n) L := by
      have : ‖α‖ * normL u L ≤ ‖β‖ / 2 * normL v L := by
        rw [hr, ← mul_assoc]; exact mul_le_mul_of_nonneg_right hs (normL_nonneg _ _)
      nlinarith
    have hwpos : 0 < normL (fun n => α * u n + β * v n) L :=
      lt_of_lt_of_le (mul_pos (half_pos hβpos) hvpos) hw_lb
    rw [div_le_iff₀ hwpos]
    calc normL u L = (normL u L / normL v L) * normL v L := hr
      _ = (2 / ‖β‖) * (normL u L / normL v L) * (‖β‖ / 2 * normL v L) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hw_lb
          (mul_nonneg (by positivity) (div_nonneg (normL_nonneg _ _) (normL_nonneg _ _)))
  have hlim' : Tendsto (fun L => (2 / ‖β‖) * (normL u L / normL v L)) atTop (𝓝 0) := by
    simpa using hlim.const_mul (2 / ‖β‖)
  exact squeeze_zero' (Eventually.of_forall fun L => div_nonneg (normL_nonneg _ _)
    (normL_nonneg _ _)) hbound hlim'

/-- Subordinacy is invariant under multiplication by nonzero scalars. -/
theorem IsSubordinate.smul {E : ℝ} {u : ℤ → ℂ} (h : IsSubordinate V E u) {c : ℂ} (hc : c ≠ 0) :
    IsSubordinate V E (fun n => c * u n) := by
  obtain ⟨hu, hne, hsub⟩ := h
  refine ⟨isSolution_smul hu c, ?_, fun v hv hind => ?_⟩
  · intro h0; apply hne; funext n
    have := congrFun h0 n; simpa [hc] using this
  · have hind' : ∀ k : ℂ, v ≠ fun n => k * u n := fun k hk =>
      hind (k / c) (by rw [hk]; funext n; field_simp)
    have := (hsub v hv hind').const_mul ‖c‖
    rw [mul_zero] at this
    refine this.congr fun L => ?_
    rw [normL_smul]; ring

theorem isSubordinate_smul_iff {E : ℝ} {u : ℤ → ℂ} {c : ℂ} (hc : c ≠ 0) :
    IsSubordinate V E (fun n => c * u n) ↔ IsSubordinate V E u := by
  refine ⟨fun h => ?_, fun h => h.smul hc⟩
  have := h.smul (inv_ne_zero hc)
  convert this using 1
  funext n; field_simp

/-! ### Subordinacy and boundary values of `m` -/

lemma sqrt24_lt_five : √24 < 5 := by
  rw [Real.sqrt_lt' (by norm_num)]; norm_num

lemma mAB_ne_zero (hV : BddPot V) {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) {E ε : ℝ} (hε : 0 < ε) :
    mAB V a b (E + ε * I) ≠ 0 := by
  have hne := add_mul_mPlus_ne_zero hV hab (E := E) hε
  have hpos := im_mPlus_pos hV (E := E) hε
  unfold mAB
  refine div_ne_zero ?_ hne
  intro h
  have him := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    add_zero, sub_zero, Complex.zero_im] at him
  have ha : a = 0 := by
    rcases mul_eq_zero.1 him with h' | h'
    · exact h'
    · linarith
  subst ha
  have hre := congrArg Complex.re h
  simp at hre
  subst hre; norm_num at hab

lemma solAB_indep {E a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) :
    ∀ c : ℂ, solAB V E (-b) a ≠ fun n => c * solAB V E a b n := by
  intro c h
  have hW := wronskian_solAB (V := V) E a b
  rw [h] at hW
  simp only [wronskian, zero_add] at hW
  have hab' : (a : ℂ) ^ 2 + (b : ℂ) ^ 2 = 1 := by exact_mod_cast hab
  rw [hab'] at hW
  have : (-1 : ℂ) = 0 := by rw [← hW]; ring
  norm_num at this

lemma solAB_ne_zero {E a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) : solAB V E a b ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [solAB_zero, solAB_one, Pi.zero_apply, Complex.ofReal_eq_zero] at h0 h1
  subst h0; subst h1; norm_num at hab

/-- Consequence of Theorem 2.7.8 (p. 186): for `a² + b² = 1`, the solution `solAB a b`
(`u(1) = a`, `u(0) = b`) is subordinate at `+∞` iff `|m_{(a,b)}(E + iε)| → ∞` as `ε ↓ 0`. -/
theorem isSubordinate_solAB_iff (hV : BddPot V) {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) (E : ℝ) :
    IsSubordinate V E (solAB V E a b) ↔
      Tendsto (fun ε : ℝ => ‖mAB V a b (E + ε * I)‖) (𝓝[>] 0) atTop := by
  set φ₁ := solAB V E a b
  set φ₂ := solAB V E (-b) a
  have h₁ : IsSolution V E φ₁ := isSolution_solAB E a b
  have h₂ : IsSolution V E φ₂ := isSolution_solAB E (-b) a
  have hW : wronskian φ₁ φ₂ 0 ≠ 0 := by
    rw [wronskian_solAB]
    have hab' : (a : ℂ) ^ 2 + (b : ℂ) ^ 2 = 1 := by exact_mod_cast hab
    rw [hab']; norm_num
  have hP := tendsto_normL_mul_atTop h₁ h₂ hW
  have hPc : Continuous fun L => normL φ₁ L * normL φ₂ L :=
    (continuous_normL _).mul (continuous_normL _)
  have hc5 : 0 < 5 - √24 := by linarith [sqrt24_lt_five]
  have hsub : IsSubordinate V E φ₁ ↔
      Tendsto (fun L => normL φ₁ L / normL φ₂ L) atTop (𝓝 0) :=
    ⟨fun h => h.2.2 φ₂ h₂ (solAB_indep hab),
      fun h => isSubordinate_of_one h₁ (solAB_ne_zero hab) h₂ (solAB_indep hab) h⟩
  rw [hsub]
  constructor
  · intro hr
    rw [tendsto_atTop]
    intro K
    set K' := max K 1
    have hK' : 0 < K' := lt_of_lt_of_le one_pos (le_max_right _ _)
    obtain ⟨R, hR⟩ := (eventually_atTop.1 (hr.eventually (gt_mem_nhds (div_pos hc5 hK'))))
    filter_upwards [exists_jlLength hPc hP R, self_mem_nhdsWithin] with ε ⟨L, hRL, hL⟩
      (hε : 0 < ε)
    have hJL := (jitomirskaya_last_ab hV hab hε hL).1
    have hm0 : 0 < ‖mAB V a b (E + ε * I)‖ := norm_pos_iff.2 (mAB_ne_zero hV hab hε)
    have h1 : (5 - √24) / ‖mAB V a b (E + ε * I)‖ < (5 - √24) / K' :=
      hJL.trans (hR L hRL.le)
    have := (div_lt_div_iff_of_pos_left hc5 hm0 hK').1 h1
    exact (le_max_left _ _).trans this.le
  · intro hm
    have hε := tendsto_jlEps hP
    have hcomp := hm.comp hε
    have hbound : Tendsto (fun L => (5 + √24) /
        ‖mAB V a b (E + (2 * (normL φ₁ L * normL φ₂ L))⁻¹ * I)‖) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hcomp
    refine squeeze_zero' (Eventually.of_forall fun L => div_nonneg (normL_nonneg _ _)
      (normL_nonneg _ _)) ?_ hbound
    filter_upwards [hP.eventually (eventually_gt_atTop 0)] with L hL
    have hεL : 0 < (2 * (normL φ₁ L * normL φ₂ L))⁻¹ := by positivity
    have := (jitomirskaya_last_ab hV hab (E := E) hεL (L := L)
      (by change 2 * _ * (normL φ₁ L * normL φ₂ L) = 1; field_simp; exact div_self hL.ne')).2
    exact this.le

/-- `u₁` is subordinate at `+∞` iff `|m₊(E + iε)| → ∞` (Corollary 2.7.9(a), `θ = 0`). -/
theorem isSubordinate_u₁_iff (hV : BddPot V) (E : ℝ) :
    IsSubordinate V E (u₁ V E) ↔
      Tendsto (fun ε : ℝ => ‖mPlus V (E + ε * I)‖) (𝓝[>] 0) atTop := by
  rw [u₁_eq_solAB, isSubordinate_solAB_iff hV (by norm_num) E]
  simp

/-- `|m_{(a,b)}| → ∞` iff `m₊ → -a/b` (for `b ≠ 0`); this is the computation behind (2.7.31). -/
theorem tendsto_mAB_iff (hV : BddPot V) {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1) (hb : b ≠ 0)
    (E : ℝ) :
    Tendsto (fun ε : ℝ => ‖mAB V a b (E + ε * I)‖) (𝓝[>] 0) atTop ↔
      Tendsto (fun ε : ℝ => mPlus V (E + ε * I)) (𝓝[>] 0) (𝓝 ((-a / b : ℝ) : ℂ)) := by
  have hb' : (b : ℂ) ≠ 0 := by exact_mod_cast hb
  have hab' : (a : ℂ) ^ 2 + (b : ℂ) ^ 2 = 1 := by exact_mod_cast hab
  constructor
  · intro h
    -- `w = 1 / m_{(a,b)} → 0`
    have hw : Tendsto (fun ε : ℝ => (mAB V a b (E + ε * I))⁻¹) (𝓝[>] 0) (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine h.inv_tendsto_atTop.congr fun ε => ?_
      simp [norm_inv]
    have hden : Tendsto (fun ε : ℝ => (a : ℂ) * (mAB V a b (E + ε * I))⁻¹ - b) (𝓝[>] 0)
        (𝓝 (a * 0 - b)) := (hw.const_mul _).sub_const _
    have hnum : Tendsto (fun ε : ℝ => (a : ℂ) + b * (mAB V a b (E + ε * I))⁻¹) (𝓝[>] 0)
        (𝓝 (a + b * 0)) := (hw.const_mul _).const_add _
    have hq := hnum.div hden (by rw [mul_zero, zero_sub, neg_ne_zero]; exact hb')
    have hval : ((a : ℂ) + b * 0) / (a * 0 - b) = ((-a / b : ℝ) : ℂ) := by
      push_cast; simp only [mul_zero, add_zero, zero_sub, div_neg, neg_div]
    rw [hval] at hq
    refine hq.congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      hden.eventually (compl_singleton_mem_nhds
        (by rw [mul_zero, zero_sub, neg_ne_zero]; exact hb'))] with ε (hε : 0 < ε) hd
    have hne := add_mul_mPlus_ne_zero hV hab (E := E) hε
    have hm0 := mAB_ne_zero hV hab (E := E) hε
    have hm : mAB V a b (E + ε * I) * (a + b * mPlus V (E + ε * I)) =
        a * mPlus V (E + ε * I) - b := div_mul_cancel₀ _ hne
    rw [Set.mem_singleton_iff] at hd
    simp only [Pi.div_apply]
    rw [div_eq_iff hd]
    field_simp
    linear_combination hm
  · intro h
    have hnum : Tendsto (fun ε : ℝ => ‖(a : ℂ) * mPlus V (E + ε * I) - b‖) (𝓝[>] 0)
        (𝓝 ‖(a : ℂ) * ((-a / b : ℝ) : ℂ) - b‖) := ((h.const_mul _).sub_const _).norm
    have hden : Tendsto (fun ε : ℝ => ‖(a : ℂ) + b * mPlus V (E + ε * I)‖) (𝓝[>] 0)
        (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have := ((h.const_mul (b : ℂ)).const_add (a : ℂ)).norm
        have hv : ‖(a : ℂ) + b * ((-a / b : ℝ) : ℂ)‖ = 0 := by
          push_cast; rw [norm_eq_zero]; field_simp; ring
        rwa [hv] at this
      · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
        exact norm_pos_iff.2 (add_mul_mPlus_ne_zero hV hab hε)
    have hC : 0 < ‖(a : ℂ) * ((-a / b : ℝ) : ℂ) - b‖ := by
      apply norm_pos_iff.2
      push_cast
      intro h0
      field_simp at h0
      have : (a : ℂ) ^ 2 + (b : ℂ) ^ 2 = 0 := by linear_combination -h0
      rw [hab'] at this; norm_num at this
    have := Tendsto.pos_mul_atTop hC hnum (tendsto_inv_nhdsGT_zero.comp hden)
    refine this.congr fun ε => ?_
    simp only [Function.comp, mAB, norm_div]
    ring

/-- **Corollary 2.7.9(a)**: for `sin θ ≠ 0`, `u_{1,θ}` (initial data `u(1) = cos θ`,
`u(0) = -sin θ`, (2.7.26)) is subordinate at `+∞` iff `m₊(E + iε) → cot θ`. -/
theorem isSubordinate_theta_iff (hV : BddPot V) {θ : ℝ} (hθ : Real.sin θ ≠ 0) (E : ℝ) :
    IsSubordinate V E (solAB V E (Real.cos θ) (-Real.sin θ)) ↔
      Tendsto (fun ε : ℝ => mPlus V (E + ε * I)) (𝓝[>] 0) (𝓝 (Real.cot θ : ℂ)) := by
  have hab : Real.cos θ ^ 2 + (-Real.sin θ) ^ 2 = 1 := by
    rw [neg_sq]; exact Real.cos_sq_add_sin_sq θ
  rw [isSubordinate_solAB_iff hV hab E, tendsto_mAB_iff hV hab (neg_ne_zero.2 hθ) E,
    Real.cot_eq_cos_div_sin, neg_div_neg_eq]

/-- `u₂` is subordinate at `+∞` iff `m₊(E + iε) → 0` (p. 186). -/
theorem isSubordinate_u₂_iff (hV : BddPot V) (E : ℝ) :
    IsSubordinate V E (u₂ V E) ↔
      Tendsto (fun ε : ℝ => mPlus V (E + ε * I)) (𝓝[>] 0) (𝓝 0) := by
  rw [u₂_eq_solAB, isSubordinate_solAB_iff hV (by norm_num) E,
    tendsto_mAB_iff hV (by norm_num) one_ne_zero E]
  simp

lemma isSubordinate_solAB_iff_lim (hV : BddPot V) {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1)
    (hb : b ≠ 0) (E : ℝ) :
    IsSubordinate V E (solAB V E a b) ↔
      Tendsto (fun ε : ℝ => mPlus V (E + ε * I)) (𝓝[>] 0) (𝓝 ((-a / b : ℝ) : ℂ)) :=
  (isSubordinate_solAB_iff hV hab E).trans (tendsto_mAB_iff hV hab hb E)

lemma isSubordinate_solAB_iff_norm (hV : BddPot V) {a : ℝ} (ha : a ^ 2 = 1) (E : ℝ) :
    IsSubordinate V E (solAB V E a 0) ↔
      Tendsto (fun ε : ℝ => ‖mPlus V (E + ε * I)‖) (𝓝[>] 0) atTop := by
  have ha0 : (a : ℂ) ≠ 0 := by
    intro h; have : a = 0 := by exact_mod_cast h
    subst this; norm_num at ha
  rw [isSubordinate_solAB_iff hV (by simpa using ha) E]
  have : ∀ z, mAB V a 0 z = mPlus V z := fun z => by
    simp only [mAB, Complex.ofReal_zero, zero_mul, add_zero, sub_zero]; field_simp
  simp only [this]

/-! ### Real subordinate solutions -/

lemma isSolution_conj {E : ℝ} {u : ℤ → ℂ} (hu : IsSolution V E u) :
    IsSolution V E (fun n => conj (u n)) := by
  intro n
  have h := congrArg conj (hu n)
  simp only [map_add, map_mul, Complex.conj_ofReal] at h
  exact h

/-- A subordinate solution is a (nonzero) multiple of a real solution `solAB a b` with
`a² + b² = 1` (cf. Exercise 2.7.7 and the proof of Corollary 2.7.9(c)). -/
theorem IsSubordinate.exists_solAB {E : ℝ} {u : ℤ → ℂ} (h : IsSubordinate V E u) :
    ∃ (c : ℂ) (a b : ℝ), c ≠ 0 ∧ a ^ 2 + b ^ 2 = 1 ∧ u = fun n => c * solAB V E a b n := by
  obtain ⟨hu, hne, hsub⟩ := h
  have hc := isSolution_conj hu
  -- `conj u` is a multiple of `u`
  have hdep : ∃ k : ℂ, (fun n => conj (u n)) = fun n => k * u n := by
    by_contra hk
    push Not at hk
    have hlim := hsub _ hc hk
    have h1 : Tendsto (fun L => normL u L / normL (fun n => conj (u n)) L) atTop (𝓝 1) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_normL_pos hu hne] with L hL
      have : normL (fun n => conj (u n)) L = normL u L := by
        unfold normL; rw [normSqL_congr (v := u) (fun n _ => by simp)]
      rw [this, div_self hL.ne']
    have := tendsto_nhds_unique hlim h1
    norm_num at this
  obtain ⟨k, hk⟩ := hdep
  -- a nonzero real multiple `ρ = κ u`
  have hreal : ∃ κ : ℂ, κ ≠ 0 ∧ ∀ n, (κ * u n).im = 0 := by
    by_cases h1k : 1 + k = 0
    · refine ⟨2 * I, by simp, fun n => ?_⟩
      have hkn := congrFun hk n
      have hk' : k = -1 := by linear_combination h1k
      rw [hk'] at hkn
      have him : (u n).re = 0 := by
        have := congrArg Complex.re hkn
        simp at this; linarith
      simp [Complex.mul_im, him]
    · refine ⟨1 + k, h1k, fun n => ?_⟩
      have hkn := congrFun hk n
      have : (1 + k) * u n = u n + conj (u n) := by rw [hkn]; ring
      rw [this, Complex.add_conj]; simp
  obtain ⟨κ, hκ, hρ⟩ := hreal
  set ρ : ℤ → ℂ := fun n => κ * u n
  have hρs : IsSolution V E ρ := isSolution_smul hu κ
  have hρval : ∀ n, ρ n = ((ρ n).re : ℂ) := fun n => by
    apply Complex.ext <;> simp [ρ, hρ n]
  set a₀ := (ρ 1).re
  set b₀ := (ρ 0).re
  have hρeq : ρ = solAB V E a₀ b₀ := by
    apply eq_of_isSolution hρs (isSolution_solAB E a₀ b₀)
    · rw [solAB_zero]; exact hρval 0
    · rw [solAB_one]; exact hρval 1
  have hN : 0 < a₀ ^ 2 + b₀ ^ 2 := by
    by_contra hcon
    push Not at hcon
    have ha : a₀ = 0 := by nlinarith [sq_nonneg a₀, sq_nonneg b₀]
    have hb : b₀ = 0 := by nlinarith [sq_nonneg a₀, sq_nonneg b₀]
    have h0 : ρ = 0 := by rw [hρeq, ha, hb]; funext n; simp [solAB, solFrom]
    apply hne; funext n
    have := congrFun h0 n
    simpa [ρ, hκ] using this
  set N := √(a₀ ^ 2 + b₀ ^ 2)
  have hNpos : 0 < N := Real.sqrt_pos.2 hN
  have hNsq : N ^ 2 = a₀ ^ 2 + b₀ ^ 2 := Real.sq_sqrt hN.le
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hNpos.ne'
  have hscale : solAB V E a₀ b₀ = fun n => (N : ℂ) * solAB V E (a₀ / N) (b₀ / N) n := by
    apply eq_of_isSolution (isSolution_solAB E a₀ b₀) (isSolution_smul (isSolution_solAB E _ _) _)
    · simp only [solAB_zero]; push_cast; field_simp
    · simp only [solAB_one]; push_cast; field_simp
  refine ⟨κ⁻¹ * N, a₀ / N, b₀ / N, mul_ne_zero (inv_ne_zero hκ) (by exact_mod_cast hNpos.ne'),
    ?_, ?_⟩
  · rw [div_pow, div_pow, ← add_div, ← hNsq, div_self (by positivity)]
  · funext n
    have h1 := congrFun hρeq n
    rw [hscale] at h1
    simp only [ρ] at h1
    rw [mul_assoc, ← h1]; field_simp

/-- **Corollary 2.7.9(c)** (at `+∞`): (2.7.10) has a solution subordinate at `+∞` iff
`m₊(E + i0) ∈ ℝ ∪ {∞}`. -/
theorem exists_subordinate_iff (hV : BddPot V) (E : ℝ) :
    (∃ u, IsSubordinate V E u) ↔
      Tendsto (fun ε : ℝ => ‖mPlus V (E + ε * I)‖) (𝓝[>] 0) atTop ∨
        ∃ x : ℝ, Tendsto (fun ε : ℝ => mPlus V (E + ε * I)) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
  constructor
  · rintro ⟨u, hu⟩
    obtain ⟨c, a, b, hc, hab, rfl⟩ := hu.exists_solAB
    rw [isSubordinate_smul_iff hc] at hu
    by_cases hb : b = 0
    · subst hb
      left
      exact (isSubordinate_solAB_iff_norm hV (by simpa using hab) E).1 hu
    · right
      exact ⟨_, (isSubordinate_solAB_iff_lim hV hab hb E).1 hu⟩
  · rintro (h | ⟨x, hx⟩)
    · exact ⟨_, (isSubordinate_u₁_iff hV E).2 h⟩
    · set N := √(x ^ 2 + 1)
      have hN : 0 < N := Real.sqrt_pos.2 (by positivity)
      have hNsq : N ^ 2 = x ^ 2 + 1 := Real.sq_sqrt (by positivity)
      have hab : (-x / N) ^ 2 + (1 / N) ^ 2 = 1 := by
        rw [div_pow, div_pow, ← add_div, neg_sq, one_pow, ← hNsq, div_self (by positivity)]
      refine ⟨_, (isSubordinate_solAB_iff_lim hV hab (by positivity) E).2 ?_⟩
      have : -(-x / N) / (1 / N) = x := by field_simp
      rwa [this]

/-! ### The left half-line: reflection -/

/-- The reflected potential `n ↦ V(1 - n)`. -/
def reflV (V : ℤ → ℝ) : ℤ → ℝ := fun n => V (1 - n)

/-- The reflection `[Rψ](n) = ψ(1 - n)` (proof of Corollary 2.7.9(b)). -/
def reflS (u : ℤ → ℂ) : ℤ → ℂ := fun n => u (1 - n)

lemma bddPot_reflV (hV : BddPot V) : BddPot (reflV V) := by
  obtain ⟨M, hM⟩ := hV; exact ⟨M, fun n => hM _⟩

@[simp] lemma reflS_reflS (u : ℤ → ℂ) : reflS (reflS u) = u := by
  funext n; simp [reflS]

@[simp] lemma reflV_reflV (V : ℤ → ℝ) : reflV (reflV V) = V := by
  funext n; simp [reflV]

lemma isSolution_reflS {z : ℂ} {u : ℤ → ℂ} (hu : IsSolution V z u) :
    IsSolution (reflV V) z (reflS u) := by
  intro n
  have := hu (1 - n)
  simp only [reflS, reflV]
  rw [show 1 - (n - 1) = 1 - n + 1 by ring, show 1 - (n + 1) = 1 - n - 1 by ring]
  linear_combination this

lemma reflS_smul (c : ℂ) (u : ℤ → ℂ) : reflS (fun n => c * u n) = fun n => c * reflS u n := rfl

lemma reflS_solAB (E a b : ℝ) : reflS (solAB V E a b) = solAB (reflV V) E b a := by
  apply eq_of_isSolution (isSolution_reflS (isSolution_solAB E a b)) (isSolution_solAB E b a)
  · simp [reflS]
  · simp [reflS]

/-- `m₋(z) = m₊(z)` for the reflected potential (`Im z ≠ 0`). -/
theorem mMinus_eq_mPlus_reflV (hV : BddPot V) {z : ℂ} (hz : z.im ≠ 0) :
    mMinus V z = mPlus (reflV V) z := by
  obtain ⟨um, hum, hum0, hum2⟩ := exists_weyl_bot hV (mem_resolventSet_of_im hV hz)
  have h1 := mMinus_eq hz hum hum0 hum2
  have hs := isSolution_reflS hum
  have hne : reflS um ≠ 0 := by
    intro h; apply hum0; rw [← reflS_reflS um, h]; funext n; simp [reflS]
  have hsq : SqSumTop (reflS um) := by
    unfold SqSumTop
    rw [← summable_nat_add_iff 1]
    refine hum2.congr fun n => ?_
    simp only [reflS]; push_cast; ring_nf
  have h2 := mPlus_eq hz hs hne hsq
  rw [h1.2.1, h2.2.1]
  simp [reflS]

/-- Subordinacy at `-∞`: subordinacy at `+∞` after the reflection `n ↦ 1 - n`. -/
def IsSubordinateBot (V : ℤ → ℝ) (E : ℝ) (u : ℤ → ℂ) : Prop :=
  IsSubordinate (reflV V) E (reflS u)

lemma mMinus_eventuallyEq (hV : BddPot V) (E : ℝ) :
    (fun ε : ℝ => mPlus (reflV V) (E + ε * I)) =ᶠ[𝓝[>] 0] fun ε => mMinus V (E + ε * I) := by
  filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
  exact (mMinus_eq_mPlus_reflV hV (by simp [hε.ne'])).symm

/-- **Corollary 2.7.9(b)**: for `cos θ ≠ 0`, `u_{1,θ}` is subordinate at `-∞` iff
`m₋(E + iε) → tan θ`. -/
theorem isSubordinateBot_theta_iff (hV : BddPot V) {θ : ℝ} (hθ : Real.cos θ ≠ 0) (E : ℝ) :
    IsSubordinateBot V E (solAB V E (Real.cos θ) (-Real.sin θ)) ↔
      Tendsto (fun ε : ℝ => mMinus V (E + ε * I)) (𝓝[>] 0) (𝓝 (Real.tan θ : ℂ)) := by
  have hab : (-Real.sin θ) ^ 2 + Real.cos θ ^ 2 = 1 := by
    rw [neg_sq, add_comm]; exact Real.cos_sq_add_sin_sq θ
  rw [IsSubordinateBot, reflS_solAB, isSubordinate_solAB_iff_lim (bddPot_reflV hV) hab hθ E,
    tendsto_congr' (mMinus_eventuallyEq hV E), neg_neg, Real.tan_eq_sin_div_cos]

/-- Corollary 2.7.9(b), `θ = π/2`: `u₂` is subordinate at `-∞` iff `|m₋(E + iε)| → ∞`. -/
theorem isSubordinateBot_u₂_iff (hV : BddPot V) (E : ℝ) :
    IsSubordinateBot V E (u₂ V E) ↔
      Tendsto (fun ε : ℝ => ‖mMinus V (E + ε * I)‖) (𝓝[>] 0) atTop := by
  rw [IsSubordinateBot, u₂_eq_solAB, reflS_solAB,
    isSubordinate_solAB_iff_norm (bddPot_reflV hV) (by norm_num) E]
  exact tendsto_congr' ((mMinus_eventuallyEq hV E).fun_comp _)

lemma exists_subordinateBot_iff' (E : ℝ) :
    (∃ u, IsSubordinateBot V E u) ↔ ∃ w, IsSubordinate (reflV V) E w :=
  ⟨fun ⟨u, hu⟩ => ⟨_, hu⟩, fun ⟨w, hw⟩ => ⟨reflS w, by rwa [IsSubordinateBot, reflS_reflS]⟩⟩

/-- **Corollary 2.7.9(c)** (at `-∞`). -/
theorem exists_subordinateBot_iff (hV : BddPot V) (E : ℝ) :
    (∃ u, IsSubordinateBot V E u) ↔
      Tendsto (fun ε : ℝ => ‖mMinus V (E + ε * I)‖) (𝓝[>] 0) atTop ∨
        ∃ x : ℝ, Tendsto (fun ε : ℝ => mMinus V (E + ε * I)) (𝓝[>] 0) (𝓝 (x : ℂ)) := by
  rw [exists_subordinateBot_iff', exists_subordinate_iff (bddPot_reflV hV) E]
  have hM := mMinus_eventuallyEq hV E
  have h1 : (fun ε : ℝ => ‖mPlus (reflV V) (E + ε * I)‖) =ᶠ[𝓝[>] 0]
      fun ε => ‖mMinus V (E + ε * I)‖ := hM.fun_comp _
  exact or_congr (tendsto_congr' h1) (exists_congr fun x => tendsto_congr' hM)

/-- **Corollary 2.7.9(d)**: (2.7.10) has a solution subordinate at both `±∞` iff
`m₊(E + i0) = m₋(E + i0)⁻¹` (with `0⁻¹ = ∞`, `∞⁻¹ = 0`; such limits are automatically
real). -/
theorem exists_subordinate_both_iff (hV : BddPot V) (E : ℝ) :
    (∃ u, IsSubordinate V E u ∧ IsSubordinateBot V E u) ↔
      (Tendsto (fun ε : ℝ => ‖mPlus V (E + ε * I)‖) (𝓝[>] 0) atTop ∧
          Tendsto (fun ε : ℝ => mMinus V (E + ε * I)) (𝓝[>] 0) (𝓝 0)) ∨
        (Tendsto (fun ε : ℝ => mPlus V (E + ε * I)) (𝓝[>] 0) (𝓝 0) ∧
          Tendsto (fun ε : ℝ => ‖mMinus V (E + ε * I)‖) (𝓝[>] 0) atTop) ∨
        ∃ x : ℝ, x ≠ 0 ∧ Tendsto (fun ε : ℝ => mPlus V (E + ε * I)) (𝓝[>] 0) (𝓝 (x : ℂ)) ∧
          Tendsto (fun ε : ℝ => mMinus V (E + ε * I)) (𝓝[>] 0) (𝓝 ((x⁻¹ : ℝ) : ℂ)) := by
  have hV' := bddPot_reflV hV
  have hM := mMinus_eventuallyEq hV E
  constructor
  · rintro ⟨u, hu, hub⟩
    obtain ⟨c, a, b, hc, hab, rfl⟩ := hu.exists_solAB
    rw [isSubordinate_smul_iff hc] at hu
    rw [IsSubordinateBot, reflS_smul, isSubordinate_smul_iff hc, reflS_solAB] at hub
    have hab' : b ^ 2 + a ^ 2 = 1 := by linarith
    by_cases hb : b = 0
    · subst hb
      have ha : a ≠ 0 := by rintro rfl; norm_num at hab
      left
      refine ⟨(isSubordinate_solAB_iff_norm hV (by simpa using hab) E).1 hu, ?_⟩
      have := (isSubordinate_solAB_iff_lim hV' hab' ha E).1 hub
      rw [tendsto_congr' hM] at this
      simpa using this
    · by_cases ha : a = 0
      · subst ha
        right; left
        refine ⟨?_, ?_⟩
        · have := (isSubordinate_solAB_iff_lim hV hab hb E).1 hu
          simpa using this
        · have := (isSubordinate_solAB_iff_norm hV' (by simpa using hab) E).1 hub
          exact (tendsto_congr' (hM.fun_comp _)).1 this
      · right; right
        refine ⟨-a / b, neg_div b a ▸ neg_ne_zero.2 (div_ne_zero ha hb), (isSubordinate_solAB_iff_lim hV hab hb E).1 hu, ?_⟩
        have := (isSubordinate_solAB_iff_lim hV' hab' ha E).1 hub
        rw [tendsto_congr' hM] at this
        convert this using 3
        field_simp
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨x, hx, h1, h2⟩)
    · refine ⟨u₁ V E, (isSubordinate_u₁_iff hV E).2 h1, ?_⟩
      rw [IsSubordinateBot, u₁_eq_solAB, reflS_solAB,
        isSubordinate_solAB_iff_lim hV' (by norm_num) one_ne_zero E, tendsto_congr' hM]
      simpa using h2
    · refine ⟨u₂ V E, (isSubordinate_u₂_iff hV E).2 h1, (isSubordinateBot_u₂_iff hV E).2 h2⟩
    · set N := √(x ^ 2 + 1)
      have hN : 0 < N := Real.sqrt_pos.2 (by positivity)
      have hNsq : N ^ 2 = x ^ 2 + 1 := Real.sq_sqrt (by positivity)
      have hab : (-x / N) ^ 2 + (1 / N) ^ 2 = 1 := by
        rw [div_pow, div_pow, ← add_div, neg_sq, one_pow, ← hNsq, div_self (by positivity)]
      have hab' : (1 / N) ^ 2 + (-x / N) ^ 2 = 1 := by linarith
      refine ⟨solAB V E (-x / N) (1 / N), ?_, ?_⟩
      · rw [isSubordinate_solAB_iff_lim hV hab (by positivity) E]
        have : -(-x / N) / (1 / N) = x := by field_simp
        rwa [this]
      · rw [IsSubordinateBot, reflS_solAB,
          isSubordinate_solAB_iff_lim hV' hab' (by rw [neg_div]; exact neg_ne_zero.2 (div_ne_zero hx hN.ne')) E, tendsto_congr' hM]
        have : -(1 / N) / (-x / N) = x⁻¹ := by field_simp
        rwa [this]

end DF
