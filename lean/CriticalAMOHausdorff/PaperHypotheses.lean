/-
Copyright (c) 2026. Formalization of
  S. Becker, S. Jitomirskaya, I. Krasovsky, "Critical almost Mathieu operator: hidden
  singularity, gap continuity, and the Hausdorff dimension of the spectrum"
  (arXiv:1909.04429v2).

# The paper's literal hypotheses  (§1 after (1.3), §2.3, Lemma 5.1, Theorem 5.2, Theorem 1.3)

The rest of the library works with convenient variants of three hypotheses of the paper.
This file proves the bridges and restates the results with the literal hypotheses.

Paper references (`Arxiv_version-5.tex`):
* hypotheses after (1.3) (tex l. 245–251): `b, v ∈ C¹(ℝ;ℝ)`, both `1`-periodic, and the
  number of zeros of `b` on a period is at most finite.  Bundled as `PaperCoeffs v b`.
  Bridges: `bddFun_of_continuous_periodic`, `lipschitz_of_contDiff_periodic`,
  `countable_zeros_of_finite`, and `PaperCoeffs.bddFun_v`, … ;
* bounded type (footnote on tex l. 202, used in Lemma 5.1, (5.8)): the continued-fraction
  coefficients `a_n` of `α` are bounded.  Defined as `BoundedPartialQuotients α` via
  Mathlib's `GenContFract.of α` (its `partDens` are `a_1, a_2, …`).  Bridges:
  `boundedPartialQuotients_iff_ratio` (`a_n` bounded ⇔ `q_{n+1}/q_n` bounded, from
  `q_{n+1} = a_{n+1} q_n + q_{n-1}`, §2.3), and `boundedType_iff`
  (`BoundedType α ↔ Irrational α ∧ BoundedPartialQuotients α`, both directions; the
  Diophantine `BoundedType` is the form used in `GapContinuity.lean`);
* Lemma 5.1 (`lemma-S`): `lemma_S_paper`;
* Theorem 5.2 (`continuitylemma1`): (5.7) `cgeneral_paper`, (5.8) `cbounded_paper` (all
  `n ≥ 1`; also for all `β` with `0 < |α - β| ≤ 1/2`: `cbounded_paper_real`), (5.9)
  `csingular_paper` (as `r_n = o(|α - p_n/q_n|^{1/2})`, with `r_n` = `rn v b α n`), and
  the combined statement `continuitylemma1_paper` (one constant `C` for (5.7) and (5.8));
* Theorem 1.3 (`measure`), (1.5): `measure_convergence_paper`.

## Remaining conventions
* "singular" (`b` has a zero on a period) is `∃ x₀, b x₀ = 0` (equivalent by periodicity).
* `1/0 = ∞` in Lemma 5.1: as in `GapContinuity.lean`, the sum is only considered for phases
  whose orbit avoids the zeros of `b` (otherwise the left side of (5.1) is `+∞`).
* `|ln δ|^{-1/2}` in (5.8) is written `1 / √|log δ|`.

Everything in this file is proved completely (no `sorry`, no axioms, no extra hypotheses).
-/
import CriticalAMOHausdorff.RationalBands

noncomputable section

open Real Filter Topology GenContFract Asymptotics

namespace CAH

/-! ### `C¹` periodic coefficients -/

/-- The derivative of a `c`-periodic function is `c`-periodic. -/
lemma periodic_deriv {f : ℝ → ℝ} {c : ℝ} (h : Function.Periodic f c) :
    Function.Periodic (deriv f) c := fun x => by
  have e : (fun y => f (y + c)) = f := funext h
  rw [← deriv_comp_add_const f c x, e]

/-- A continuous `1`-periodic function is bounded (compactness of `[0,1]`). -/
lemma bddFun_of_continuous_periodic {f : ℝ → ℝ} (hf : Continuous f)
    (hp : Function.Periodic f 1) : BddFun f := by
  obtain ⟨M, hM⟩ := (hp.isBounded_of_continuous one_ne_zero hf).exists_norm_le
  exact ⟨M, fun x => by simpa [Real.norm_eq_abs] using hM (f x) ⟨x, rfl⟩⟩

/-- A `C¹` `1`-periodic function is Lipschitz: its derivative is continuous and periodic,
hence bounded, and the mean value theorem applies. -/
lemma lipschitz_of_contDiff_periodic {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hp : Function.Periodic f 1) : ∃ K, 0 ≤ K ∧ ∀ x y, |f x - f y| ≤ K * |x - y| := by
  obtain ⟨M, hM⟩ := bddFun_of_continuous_periodic (hf.continuous_deriv le_rfl)
    (periodic_deriv hp)
  have hdiff : Differentiable ℝ f := hf.differentiable one_ne_zero
  refine ⟨max M 0, le_max_right _ _, fun x y => ?_⟩
  have := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ) (C := max M 0)
    (fun z _ => hdiff z)
    (fun z _ => by rw [Real.norm_eq_abs]; exact (hM z).trans (le_max_left M 0)) convex_univ
    (Set.mem_univ y) (Set.mem_univ x)
  simpa [Real.norm_eq_abs] using this

/-- Finitely many zeros on a period and `1`-periodicity give a countable zero set. -/
lemma countable_zeros_of_finite {b : ℝ → ℝ} (hper : Function.Periodic b 1)
    (hfin : {x ∈ Set.Ico (0 : ℝ) 1 | b x = 0}.Finite) : {x | b x = 0}.Countable := by
  have hsub : {x | b x = 0} ⊆
      ⋃ k : ℤ, (fun y => y + (k : ℝ)) '' {x ∈ Set.Ico (0 : ℝ) 1 | b x = 0} := by
    intro x hx
    refine Set.mem_iUnion.2 ⟨⌊x⌋, Int.fract x,
      ⟨⟨Int.fract_nonneg x, Int.fract_lt_one x⟩, ?_⟩, Int.fract_add_floor x⟩
    have e : Int.fract x = x - ((⌊x⌋ : ℤ) : ℝ) * 1 := by rw [mul_one]; rfl
    show b (Int.fract x) = 0
    rw [e, hper.sub_int_mul_eq]
    exact hx
  exact (Set.countable_iUnion fun k => (hfin.image _).countable).mono hsub

/-- **The hypotheses of the paper after (1.3)** (tex l. 245–251): `b, v ∈ C¹(ℝ;ℝ)`, both
periodic with period `1`, and `b` has at most finitely many zeros on a period. -/
structure PaperCoeffs (v b : ℝ → ℝ) : Prop where
  contDiff_v : ContDiff ℝ 1 v
  contDiff_b : ContDiff ℝ 1 b
  periodic_v : Function.Periodic v 1
  periodic_b : Function.Periodic b 1
  finite_zeros : {x ∈ Set.Ico (0 : ℝ) 1 | b x = 0}.Finite

namespace PaperCoeffs

variable {v b : ℝ → ℝ}

lemma bddFun_v (h : PaperCoeffs v b) : BddFun v :=
  bddFun_of_continuous_periodic h.contDiff_v.continuous h.periodic_v

lemma bddFun_b (h : PaperCoeffs v b) : BddFun b :=
  bddFun_of_continuous_periodic h.contDiff_b.continuous h.periodic_b

lemma lip_v (h : PaperCoeffs v b) : ∃ K, 0 ≤ K ∧ ∀ x y, |v x - v y| ≤ K * |x - y| :=
  lipschitz_of_contDiff_periodic h.contDiff_v h.periodic_v

lemma lip_b (h : PaperCoeffs v b) : ∃ K, 0 ≤ K ∧ ∀ x y, |b x - b y| ≤ K * |x - y| :=
  lipschitz_of_contDiff_periodic h.contDiff_b h.periodic_b

lemma countable_zeros (h : PaperCoeffs v b) : {x | b x = 0}.Countable :=
  countable_zeros_of_finite h.periodic_b h.finite_zeros

end PaperCoeffs

/-! ### Bounded type -/

/-- **`α` has bounded partial quotients** (the paper's "bounded type", footnote on
tex l. 202): the coefficients `a_1, a_2, …` of the continued fraction expansion of `α`
(Mathlib's `(GenContFract.of α).partDens`) are bounded. -/
def BoundedPartialQuotients (α : ℝ) : Prop :=
  ∃ A : ℝ, ∀ n : ℕ, ∀ a : ℝ, (GenContFract.of α).partDens.get? n = some a → a ≤ A

/-- The ratios `q_{n+1}/q_n` of consecutive continued-fraction denominators are bounded. -/
def BoundedDenRatio (α : ℝ) : Prop :=
  ∃ B : ℝ, ∀ n : ℕ, q α (n + 1) ≤ B * q α n

lemma q_zero (α : ℝ) : q α 0 = 1 := rfl

/-- `q_{n+2} = a_{n+2} q_{n+1} + q_n`, with `a_{n+2}` the Mathlib partial denominator
of index `n + 1`. -/
lemma exists_partDen_succ {α : ℝ} (hα : Irrational α) (n : ℕ) :
    ∃ a : ℝ, (GenContFract.of α).partDens.get? (n + 1) = some a ∧ 1 ≤ a ∧
      q α (n + 2) = a * q α (n + 1) + q α n := by
  obtain ⟨gp, hgp⟩ : ∃ gp, (GenContFract.of α).s.get? (n + 1) = some gp :=
    Option.ne_none_iff_exists'.1 (SGD.not_terminatedAt hα (n + 1))
  have ha : gp.a = 1 := (of_partNum_eq_one_and_exists_int_partDen_eq hgp).1
  refine ⟨gp.b, partDen_eq_s_b hgp, of_one_le_get?_partDen (partDen_eq_s_b hgp), ?_⟩
  simp only [q, AMO.cfDen]
  rw [dens_recurrence hgp rfl rfl, ha]
  ring

/-- **Bounded partial quotients ⇔ bounded `q_{n+1}/q_n`** (via
`q_{n+1} = a_{n+1} q_n + q_{n-1}`). -/
theorem boundedPartialQuotients_iff_ratio {α : ℝ} (hα : Irrational α) :
    BoundedPartialQuotients α ↔ BoundedDenRatio α := by
  constructor
  · rintro ⟨A, hA⟩
    refine ⟨max (A + 1) (q α 1), fun n => ?_⟩
    rcases n with _ | m
    · rw [q_zero, mul_one]; exact le_max_right _ _
    · obtain ⟨a, ha, -, hq⟩ := exists_partDen_succ hα m
      have haA := hA _ a ha
      have h1 := q_pos hα (m + 1)
      have h2 := q_le_succ hα m
      have h3 : A + 1 ≤ max (A + 1) (q α 1) := le_max_left _ _
      show q α (m + 2) ≤ _
      rw [hq]
      nlinarith [mul_le_mul_of_nonneg_right haA h1.le, mul_le_mul_of_nonneg_right h3 h1.le]
  · rintro ⟨B, hB⟩
    refine ⟨max B (((GenContFract.of α).partDens.get? 0).getD 0), fun n a ha => ?_⟩
    rcases n with _ | m
    · have : ((GenContFract.of α).partDens.get? 0).getD 0 = a := by rw [ha]; rfl
      rw [this]; exact le_max_right _ _
    · obtain ⟨a', ha', -, hq⟩ := exists_partDen_succ hα m
      rw [ha'] at ha
      have hae : a' = a := Option.some.inj ha
      subst hae
      have h1 := q_pos hα (m + 1)
      have h0 := q_pos hα m
      have h2 : q α (m + 2) ≤ B * q α (m + 1) := hB (m + 1)
      have h3 : a' * q α (m + 1) ≤ B * q α (m + 1) := by rw [hq] at h2; linarith
      exact (le_of_mul_le_mul_right h3 h1).trans (le_max_left _ _)

/-- A Diophantine-bounded-type number is irrational. -/
lemma irrational_of_boundedType {α : ℝ} (h : BoundedType α) : Irrational α := by
  obtain ⟨c, hc, h⟩ := h
  rintro ⟨r, rfl⟩
  have h1 := h r.den r.den_pos r.num
  have e : (r.den : ℝ) * (r : ℝ) - r.num = 0 := by
    rw [Rat.cast_def]
    have : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_pos.ne'
    field_simp
    ring
  rw [e, abs_zero] at h1
  have : 0 < c / (r.den : ℝ) := div_pos hc (by exact_mod_cast r.den_pos)
  linarith

/-- Bounded `q_{n+1}/q_n` implies the Diophantine bounded-type condition: for
`q_n ≤ k < q_{n+1}`, best approximation gives `|kα - m| ≥ |δ_n| > 1/(q_{n+1} + q_n)`. -/
theorem boundedType_of_ratio {α : ℝ} (hα : Irrational α) (h : BoundedDenRatio α) :
    BoundedType α := by
  classical
  obtain ⟨B, hB⟩ := h
  set B' := max B 1
  have hB'1 : 1 ≤ B' := le_max_right _ _
  refine ⟨1 / (B' + 1), by positivity, fun k hk m => ?_⟩
  have hex : ∃ n, k < qN α (n + 1) := by
    obtain ⟨n, hn⟩ := ((SGD.cfGrowth hα).tendsto_atTop.eventually_gt_atTop (k : ℝ)).exists
    refine ⟨n, ?_⟩
    have : (k : ℝ) < qN α (n + 1) := by rw [qN_cast hα]; exact hn.trans_le (q_le_succ hα n)
    exact_mod_cast this
  set n := Nat.find hex
  have hn : k < qN α (n + 1) := Nat.find_spec hex
  have hqk : q α n ≤ k := by
    rcases hn0 : n with _ | j
    · rw [q_zero]; exact_mod_cast hk
    · have hmin := Nat.find_min hex (show j < n by omega)
      rw [not_lt] at hmin
      rw [← qN_cast hα]; exact_mod_cast hmin
  have hδ := abs_delta_le_abs_mul_sub hα n (k : ℤ) m (by exact_mod_cast hk)
    (by exact_mod_cast hn)
  push_cast at hδ
  have hlow := (abs_delta_bounds hα n).1
  have hq0 := q_pos hα n
  have hq1 := q_pos hα (n + 1)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hsum : q α (n + 1) + q α n ≤ (B' + 1) * k := by
    have := hB n
    have hb : B * q α n ≤ B' * q α n := mul_le_mul_of_nonneg_right (le_max_left _ _) hq0.le
    nlinarith
  calc 1 / (B' + 1) / (k : ℝ) = 1 / ((B' + 1) * k) := by rw [div_div]
    _ ≤ 1 / (q α (n + 1) + q α n) := one_div_le_one_div_of_le (by positivity) hsum
    _ ≤ |delta α n| := hlow.le
    _ ≤ _ := hδ

/-- The Diophantine bounded-type condition implies bounded `q_{n+1}/q_n`:
`c/q_n ≤ |δ_n| < 1/q_{n+1}`. -/
theorem ratio_of_boundedType {α : ℝ} (h : BoundedType α) : BoundedDenRatio α := by
  have hα := irrational_of_boundedType h
  obtain ⟨c, hc, h⟩ := h
  refine ⟨1 / c, fun n => ?_⟩
  have h1 := h (qN α n) (one_le_qN hα n) (pZ α n)
  rw [qN_cast hα, pZ_cast] at h1
  have h2 := (abs_delta_bounds hα n).2
  have h3 : c / q α n < 1 / q α (n + 1) := h1.trans_lt (by simpa [delta] using h2)
  have hq0 := q_pos hα n
  have hq1 := q_pos hα (n + 1)
  rw [div_lt_div_iff₀ hq0 hq1] at h3
  rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hc]
  linarith

/-- **Bounded type: the Diophantine form used in `GapContinuity.lean` is equivalent to
irrationality plus bounded continued-fraction coefficients.** -/
theorem boundedType_iff (α : ℝ) :
    BoundedType α ↔ Irrational α ∧ BoundedPartialQuotients α := by
  constructor
  · intro h
    have hα := irrational_of_boundedType h
    exact ⟨hα, (boundedPartialQuotients_iff_ratio hα).2 (ratio_of_boundedType h)⟩
  · rintro ⟨hα, h⟩
    exact boundedType_of_ratio hα ((boundedPartialQuotients_iff_ratio hα).1 h)

/-! ### Lemma 5.1 -/

/-- **Lemma 5.1 (`lemma-S`), (5.1), with the paper's hypotheses.** Let `b ∈ C¹(ℝ)` be
`1`-periodic with `b(0) = 0`, and `α` irrational of bounded type (bounded partial
quotients).  Then there is `C > 0` such that for all `θ` and integers `L > 1`,
`∑_{k<L} 1/|b(αk+θ)| ≥ C L ln L` (for phases whose orbit avoids the zeros of `b`; otherwise
the left side is `+∞`). -/
theorem lemma_S_paper {b : ℝ → ℝ} (hb : ContDiff ℝ 1 b) (hper : Function.Periodic b 1)
    (h0 : b 0 = 0) {α : ℝ} (hα : Irrational α) (hbt : BoundedPartialQuotients α) :
    ∃ C > 0, ∀ θ : ℝ, ∀ L : ℕ, 2 ≤ L → (∀ k < L, b (θ + k * α) ≠ 0) →
      C * L * Real.log L ≤ ∑ k ∈ Finset.range L, 1 / |b (θ + k * α)| := by
  obtain ⟨K, -, hK⟩ := lipschitz_of_contDiff_periodic hb hper
  exact lemma_S hper h0 hK ((boundedType_iff α).2 ⟨hα, hbt⟩)

/-! ### Theorem 5.2 -/

/-- `|α - p_n/q_n| ≤ 1/2` for `n ≥ 1`. -/
lemma abs_sub_conv_le_half {α : ℝ} (hα : Irrational α) {n : ℕ} (hn : 1 ≤ n) :
    |α - p α n / q α n| ≤ 1 / 2 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 := abs_sub_lt hα (m + 1)
  have h2 : q α m + q α (m + 1) ≤ q α (m + 1 + 1) := q_add_le hα m
  have h3 := q_one_le hα m
  have h4 := q_one_le hα (m + 1)
  have h5 : 2 ≤ q α (m + 1) * q α (m + 1 + 1) := by nlinarith
  refine h1.le.trans ?_
  rw [div_le_div_iff₀ (by linarith) (by norm_num)]
  linarith

/-- `0 < |α - p_n/q_n|`. -/
lemma abs_sub_conv_pos {α : ℝ} (hα : Irrational α) (n : ℕ) : 0 < |α - p α n / q α n| :=
  (div_pos one_pos (mul_pos (q_pos hα n) (add_pos (q_pos hα n) (q_pos hα (n + 1))))).trans
    (lt_abs_sub hα n)

/-- **Theorem 5.2, (5.7) (`cgeneral`), with the paper's hypotheses.** There is `C > 0` such
that for every `E ∈ σ(M_{v,b,α})` and `n = 1, 2, …` there is `E' ∈ σ(M_{v,b,p_n/q_n})` with
`|E - E'| ≤ C |α - p_n/q_n|^{1/2}`. -/
theorem cgeneral_paper {v b : ℝ → ℝ} (hc : PaperCoeffs v b) {α : ℝ} (hα : Irrational α) :
    ∃ C > 0, ∀ n : ℕ, 1 ≤ n → ∀ E ∈ sigmaM v b α, ∃ E' ∈ sigmaM v b (p α n / q α n),
      |E - E'| ≤ C * √|α - p α n / q α n| := by
  obtain ⟨Kb, hKb, hLb⟩ := hc.lip_b
  obtain ⟨Kv, hKv, hLv⟩ := hc.lip_v
  obtain ⟨C, hC⟩ := cgeneral_convergents hc.bddFun_v hc.bddFun_b hKb hKv hLb hLv
    hc.countable_zeros hα
  refine ⟨max C 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun n _ E hE => ?_⟩
  obtain ⟨E', hE', h⟩ := hC n E hE
  exact ⟨E', hE', h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _))⟩

/-- **(5.8) for all `β` near `α`, with the paper's hypotheses.** If `b` has a zero and `α`
is irrational of bounded type, there is `C > 0` with
`dist(E, σ(M_{v,b,β})) ≤ C |α-β|^{1/2} |ln|α-β||^{-1/2}` for all `0 < |α - β| ≤ 1/2`
(the small-`|α - β|` estimate `cbounded`, combined with (5.7) on `δ₀ ≤ |α - β| ≤ 1/2`). -/
theorem cbounded_paper_real {v b : ℝ → ℝ} (hc : PaperCoeffs v b) (hsing : ∃ x₀, b x₀ = 0)
    {α : ℝ} (hα : Irrational α) (hbt : BoundedPartialQuotients α) :
    ∃ C > 0, ∀ β : ℝ, 0 < |α - β| → |α - β| ≤ 1 / 2 → ∀ E ∈ sigmaM v b α,
      Metric.infDist E (sigmaM v b β) ≤ C * √|α - β| / √(abs (Real.log |α - β|)) := by
  obtain ⟨Kb, hKb, hLb⟩ := hc.lip_b
  obtain ⟨Kv, hKv, hLv⟩ := hc.lip_v
  obtain ⟨C₁, hC₁, δ₀, hδ₀, h1⟩ := cbounded hc.bddFun_v hc.bddFun_b hKb hKv hLb hLv
    hc.countable_zeros hc.periodic_b hsing ((boundedType_iff α).2 ⟨hα, hbt⟩)
  obtain ⟨C₂, hC₂, h2⟩ := cgeneral hc.bddFun_v hc.bddFun_b hKb hKv hLb hLv hc.countable_zeros
  have hs0 : 0 ≤ √|Real.log δ₀| := Real.sqrt_nonneg _
  refine ⟨C₁ + C₂ * √|Real.log δ₀|, by positivity, fun β hpos hhalf E hE => ?_⟩
  have hlogneg : Real.log |α - β| < 0 := Real.log_neg hpos (by linarith)
  have hlog : 0 < (abs (Real.log |α - β|)) := abs_pos.2 hlogneg.ne
  have hw : 0 < √(abs (Real.log |α - β|)) := Real.sqrt_pos.2 hlog
  have hs : 0 ≤ √|α - β| := Real.sqrt_nonneg _
  rcases lt_or_ge |α - β| δ₀ with hlt | hge
  · refine (h1 β hpos hlt E hE).trans ?_
    have : C₁ ≤ C₁ + C₂ * √|Real.log δ₀| := le_add_of_nonneg_right (mul_nonneg hC₂ hs0)
    gcongr
  · refine (h2 α β (by linarith) E hE).trans ?_
    have hlogle : (abs (Real.log |α - β|)) ≤ |Real.log δ₀| := by
      rw [abs_of_neg hlogneg]
      have : Real.log δ₀ ≤ Real.log |α - β| := Real.log_le_log hδ₀ hge
      have := neg_abs_le (Real.log δ₀)
      linarith
    have hsq : √(abs (Real.log |α - β|)) ≤ √|Real.log δ₀| := Real.sqrt_le_sqrt hlogle
    rw [le_div_iff₀ hw]
    nlinarith [mul_le_mul_of_nonneg_left hsq (mul_nonneg hC₂ hs), mul_nonneg hC₁.le hs]

/-- **Theorem 5.2, (5.8) (`cbounded`), with the paper's hypotheses.** If `b` has a zero on a
period and `α` is irrational of bounded type, there is `C > 0` such that for every
`E ∈ σ(M_{v,b,α})` and `n = 1, 2, …` there is `E' ∈ σ(M_{v,b,p_n/q_n})` with
`|E - E'| ≤ C |α - p_n/q_n|^{1/2} |ln|α - p_n/q_n||^{-1/2}`. -/
theorem cbounded_paper {v b : ℝ → ℝ} (hc : PaperCoeffs v b) (hsing : ∃ x₀, b x₀ = 0)
    {α : ℝ} (hα : Irrational α) (hbt : BoundedPartialQuotients α) :
    ∃ C > 0, ∀ n : ℕ, 1 ≤ n → ∀ E ∈ sigmaM v b α, ∃ E' ∈ sigmaM v b (p α n / q α n),
      |E - E'| ≤ C * √|α - p α n / q α n| / √(abs (Real.log |α - p α n / q α n|)) := by
  obtain ⟨C, hC, h⟩ := cbounded_paper_real hc hsing hα hbt
  exact ⟨C, hC, fun n hn E hE => exists_mem_sigmaM_of_infDist_le hc.bddFun_v hc.bddFun_b
    (h _ (abs_sub_conv_pos hα n) (abs_sub_conv_le_half hα hn) E hE)⟩

/-- The quantity `r_n = sup_{E ∈ σ(M_{v,b,α})} dist(E, σ(M_{v,b,p_n/q_n}))` of (5.9). -/
def rn (v b : ℝ → ℝ) (α : ℝ) (n : ℕ) : ℝ :=
  sSup ((fun E => Metric.infDist E (sigmaM v b (p α n / q α n))) '' sigmaM v b α)

/-- **Theorem 5.2, (5.9) (`csingular`), with the paper's hypotheses.** If `b` has a zero on a
period, then for every irrational `α`, `r_n = o(|α - p_n/q_n|^{1/2})` as `n → ∞`. -/
theorem csingular_paper {v b : ℝ → ℝ} (hc : PaperCoeffs v b) (hsing : ∃ x₀, b x₀ = 0)
    {α : ℝ} (hα : Irrational α) :
    (fun n => rn v b α n) =o[atTop] (fun n => √|α - p α n / q α n|) := by
  obtain ⟨Kb, hKb, hLb⟩ := hc.lip_b
  obtain ⟨Kv, hKv, hLv⟩ := hc.lip_v
  have h := csingular_convergents hc.bddFun_v hc.bddFun_b hKb hKv hLb hLv hc.countable_zeros
    hc.periodic_b hsing hα
  refine Asymptotics.IsLittleO.of_bound fun η hη => ?_
  filter_upwards [h η hη] with n hn
  have hr0 : 0 ≤ rn v b α n := Real.sSup_nonneg (by
    rintro _ ⟨E, -, rfl⟩; exact Metric.infDist_nonneg)
  rw [Real.norm_of_nonneg hr0, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sSup_le (by rintro _ ⟨E, hE, rfl⟩; exact hn E hE) (by positivity)

/-- **Theorem 5.2 (`continuitylemma1`), with the paper's hypotheses.** Let `v, b ∈ C¹(ℝ;ℝ)`
be `1`-periodic, `b` with finitely many zeros on a period, and `α` irrational with
convergents `p_n/q_n`.  Then there is `C > 0` such that
* (5.7) for every `E ∈ σ(M_{v,b,α})` and `n ≥ 1` there is `E' ∈ σ(M_{v,b,p_n/q_n})` with
  `|E - E'| ≤ C |α - p_n/q_n|^{1/2}`;
* (5.8) if `b` has a zero on a period and `α` is of bounded type, then moreover `E'` can be
  chosen with `|E - E'| ≤ C |α - p_n/q_n|^{1/2} |ln|α - p_n/q_n||^{-1/2}`, `n ≥ 1`;
* (5.9) if `b` has a zero on a period, `r_n = o(|α - p_n/q_n|^{1/2})`. -/
theorem continuitylemma1_paper {v b : ℝ → ℝ} (hc : PaperCoeffs v b) {α : ℝ}
    (hα : Irrational α) :
    ∃ C > 0,
      (∀ n : ℕ, 1 ≤ n → ∀ E ∈ sigmaM v b α, ∃ E' ∈ sigmaM v b (p α n / q α n),
        |E - E'| ≤ C * √|α - p α n / q α n|) ∧
      ((∃ x₀, b x₀ = 0) → BoundedPartialQuotients α →
        ∀ n : ℕ, 1 ≤ n → ∀ E ∈ sigmaM v b α, ∃ E' ∈ sigmaM v b (p α n / q α n),
          |E - E'| ≤ C * √|α - p α n / q α n| / √(abs (Real.log |α - p α n / q α n|))) ∧
      ((∃ x₀, b x₀ = 0) →
        (fun n => rn v b α n) =o[atTop] (fun n => √|α - p α n / q α n|)) := by
  obtain ⟨C₁, hC₁, h1⟩ := cgeneral_paper hc hα
  have h3 : (∃ x₀, b x₀ = 0) →
      (fun n => rn v b α n) =o[atTop] (fun n => √|α - p α n / q α n|) :=
    fun hs => csingular_paper hc hs hα
  by_cases hcase : (∃ x₀, b x₀ = 0) ∧ BoundedPartialQuotients α
  · obtain ⟨C₂, hC₂, h2⟩ := cbounded_paper hc hcase.1 hα hcase.2
    refine ⟨max C₁ C₂, lt_of_lt_of_le hC₁ (le_max_left _ _), ?_, ?_, h3⟩
    · intro n hn E hE
      obtain ⟨E', hE', h⟩ := h1 n hn E hE
      exact ⟨E', hE', h.trans (by gcongr; exact le_max_left _ _)⟩
    · intro _ _ n hn E hE
      obtain ⟨E', hE', h⟩ := h2 n hn E hE
      exact ⟨E', hE', h.trans (by gcongr; exact le_max_right _ _)⟩
  · exact ⟨C₁, hC₁, h1, fun hs hb => absurd ⟨hs, hb⟩ hcase, h3⟩

/-! ### Theorem 1.3 -/

/-- **Theorem 1.3 (`measure`), (1.5), with the paper's hypotheses.** Let `v, b ∈ C¹(ℝ;ℝ)`
be `1`-periodic, `b` with finitely many zeros on a period and at least one zero (singular
`H_{v,b,α,θ}`), and `α` irrational with convergents `p_n/q_n`.  Then
`|σ(M_{v,b,α})| = lim_{n→∞} |σ(M_{v,b,p_n/q_n})|`. -/
theorem measure_convergence_paper {v b : ℝ → ℝ} (hc : PaperCoeffs v b)
    (hsing : ∃ θ₀, b θ₀ = 0) {α : ℝ} (hα : Irrational α) :
    Tendsto (fun n => MeasureTheory.volume (sigmaM v b (p α n / q α n))) atTop
      (𝓝 (MeasureTheory.volume (sigmaM v b α))) := by
  obtain ⟨Kb, hKb, hLb⟩ := hc.lip_b
  obtain ⟨Kv, hKv, hLv⟩ := hc.lip_v
  exact measure_convergence' hc.bddFun_v hc.bddFun_b hKb hKv hLb hLv hc.countable_zeros
    hc.periodic_b hc.periodic_v hsing hα

end CAH
